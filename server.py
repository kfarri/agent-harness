#!/usr/bin/env python3
"""에이전트 하네스 GUI 서버 v3 (파이썬 표준 라이브러리만 사용)

구조: 프로젝트 > (에이전트, 단계 파이프라인, 작업)
- 프로젝트마다 폴더가 분리된다. 'default' 프로젝트는 기존 ~/agents 폴더를 그대로 쓴다(자동 이전).
- 단계는 '작업'(결과 파일 생성)과 '검토'(VERDICT: APPROVE/REVISE)로 구성되고,
  검토가 REVISE이면 대상 단계로 돌아가 다시 수행한다(프로젝트별 최대 반복 횟수).
- 마지막에는 항상 사용자의 최종 승인을 받는다.
"""
import base64
import copy
import fnmatch
import http.cookies
import ipaddress
import hmac
import json
import os
import re
import secrets
import shlex
import shutil
import signal
import subprocess
import sys
import threading
import time
import traceback
import queue
import urllib.error
import urllib.request
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlparse

BASE = Path(os.environ.get("AGENTS_DIR", "~/agents")).expanduser().resolve()


def load_env(path):
    if not path.exists():
        return
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        k, v = line.split("=", 1)
        os.environ.setdefault(k.strip(), v.strip().strip('"').strip("'"))


load_env(BASE / ".env")

HOST = os.environ.get("GUI_HOST", "127.0.0.1")
PORT = int(os.environ.get("GUI_PORT", "8080"))
USER = os.environ.get("GUI_USER", "admin")
PASSWORD = os.environ.get("GUI_PASSWORD", "")
AGENT_CMD = os.environ.get("AGENT_CMD", "claude")
STEP_TIMEOUT = int(os.environ.get("STEP_TIMEOUT", "900"))
BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "")
TG_BASE = os.environ.get("TELEGRAM_API_BASE", "https://api.telegram.org").rstrip("/")
TG_POLL = int(os.environ.get("TELEGRAM_POLL", "25"))
PAIR_CODE = secrets.token_hex(3)
TRUST_PROXY = os.environ.get("TRUST_PROXY", "") not in ("", "0", "false", "no")
TRUST_PROXY_IPS = {x.strip() for x in os.environ.get("TRUST_PROXY_IPS", "").split(",") if x.strip()}  # 비우면 사설 IP 전부
PUBLIC_HTTPS = os.environ.get("PUBLIC_HTTPS", "") not in ("", "0", "false", "no")
PUBLIC_HOST = os.environ.get("PUBLIC_HOST", "")
SESS_TTL = max(1, int(os.environ.get("SESSION_DAYS", "7"))) * 86400
MAX_FAILS = max(3, int(os.environ.get("MAX_LOGIN_FAILS", "5")))

CONFIG_FILE = BASE / "projects.json"
LEGACY_FILE = BASE / "agents.json"
CLAUDE_JSON = Path.home() / ".claude.json"

ID_RE = re.compile(r"^[A-Za-z0-9_-]{1,40}$")
MODEL_RE = re.compile(r"^[A-Za-z0-9._:\-\[\]]{0,60}$")
RESERVED_STAGE = {"request", "final", "approved"}
RESERVED_DIR = {"shared", "logs", "scripts", "projects"}
DEFAULT_SETTINGS = {"parallel": 1, "job_token_limit": 0, "planner_model": "sonnet",
                    "telegram": {"chats": [], "notify": True, "cur": {}}}
TG_HELP = ("사용법\n"
           "/projects  프로젝트 목록 (버튼으로 바로 전환)\n"
           "/use 번호  작업할 프로젝트 고르기\n"
           "/newproject 이름  새 프로젝트 만들기\n"
           "/jobs  최근 작업 5건 보기\n"
           "/status  지금 실행 중인 작업\n"
           "/sched  예약 목록\n"
           "/cancel  입력 대기 취소\n"
           "/release  테스트에서 확인한 변경을 운영에 반영\n"
           "/security  차단 현황 · /unban IP  차단 해제 · /unlock  외부 로그인 잠금 해제\n\n"
           "명령 없이 그냥 메시지를 보내면 고른 프로젝트에 새 작업으로 요청됩니다.\n"
           "작업이 끝나면 승인/반려 버튼이 도착합니다.")
DEFAULT_TURNS = {"work": 15, "review": 8}
KIND_LABEL = {"work": "작업", "review": "검토"}

LOCK = threading.RLock()
NOTIFY = queue.Queue()
TG_WAIT = {}
SESSIONS = {}     # 토큰 -> {ip, exp}
FAILS = {}        # IP -> {n, until}
LOGINS = []       # 최근 로그인 기록
COND = threading.Condition(LOCK)
PROCS = {}
JOBS = {}
QUEUE = queue.Queue()
RUNNING = 0
CFG = {}
FLAGS = {}
PENDING_TRUST = set()
PLAN_LOCK = threading.Lock()
OPT_FLAGS = ("--tools", "--strict-mcp-config", "--disable-slash-commands", "--no-session-persistence")


class ApiError(Exception):
    def __init__(self, code, msg):
        super().__init__(msg)
        self.code, self.msg = code, msg


class Cancelled(Exception):
    pass


def now():
    return time.strftime("%Y-%m-%d %H:%M:%S")


def read_text(path, limit=200_000):
    try:
        return path.read_text(errors="replace")[:limit]
    except (FileNotFoundError, IsADirectoryError):
        return None


def write_json(path, obj):
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(obj, ensure_ascii=False, indent=2))
    tmp.replace(path)


# ---------------------------------------------------------------- 기본값 · 프리셋

def A(key, name, role, web=False, model=""):
    return {"key": key, "name": name, "role": role, "web": web, "model": model}


def S(name, agent, kind, instruction, inputs=(), target="", polish=False):
    return {"name": name, "agent": agent, "kind": kind, "instruction": instruction,
            "inputs": list(inputs), "target": target, "polish": polish}


_RESEARCH = "요청 주제를 조사한다. 사실만 정리하고 출처를 함께 적으며, 자료가 엇갈리면 불일치로 표시한다. 글 작성은 하지 않는다."
_CHECK = "요청과 조사 결과를 읽고, 이 조사 결과만으로 요청에 맞는 글을 쓸 수 있는지 판단한다. 기준: 요청 충족 / 근거·출처 / 모순·누락."
_DRAFT = "조사 결과에 있는 내용만 사용해 읽기 쉬운 한국어 글(제목, 소제목 포함)로 작성한다. 없는 사실은 지어내지 않고 불일치 표시는 그대로 밝힌다."
_REVIEW = "초안을 조사 결과와 대조해 검수한다 (없는 사실, 오탈자, 어색한 문장, 요청 누락)."

# 기본으로 생성되는 에이전트의 역할 설명. 프로젝트를 새로 만들거나 'AI 추천' 대신 프리셋을 쓸 때 CLAUDE.md에
# 그대로 들어가므로, 한 줄짜리 요약이 아니라 전문 분야·접근 방식·판단 기준·하지 않는 일까지 담아 전문적으로 적는다.
_ROLE_RESEARCHER = (
    "조사와 사실 확인을 전문으로 하는 리서치 에이전트다. 주제에 대해 신뢰할 수 있는 자료를 찾아 핵심 사실·수치·날짜를 "
    "정리하고, 항목마다 출처를 명시한다. 여러 출처의 내용이 서로 다르면 임의로 하나를 골라 통일하지 않고 '불일치'로 "
    "표시해 다음 단계가 직접 판단할 수 있게 남겨 둔다. 확인된 사실과 추측·의견을 분명히 구분해서 적고, 확인하지 못한 "
    "부분은 숨기지 않고 모른다고 밝힌다. 글의 문장력이나 구성은 신경 쓰지 않는다 — 그건 작성자의 몫이다."
)
_ROLE_WRITER = (
    "조사 자료를 바탕으로 읽기 쉬운 글을 쓰는 전문 작가다. 받은 조사 결과에 있는 사실만 사용하며, 매끄럽게 풀어 쓰더라도 "
    "없는 내용을 지어내거나 과장하지 않는다. 독자가 한 번에 핵심을 파악할 수 있도록 제목과 소제목으로 글의 구조를 "
    "잡고, 조사 결과에 불일치로 표시된 부분이 있으면 얼버무리지 않고 글에도 그대로 드러낸다."
)
_ROLE_REVIEWER = (
    "출고 전 마지막 검수를 맡는 교정·사실 확인 전문가다. 초안을 조사 결과와 한 줄씩 대조해 (1) 조사에 없는 사실이 "
    "끼어들지 않았는지, (2) 오탈자나 어색한 문장이 없는지, (3) 요청한 내용이 빠지지 않았는지 확인한다. 문제를 발견하면 "
    "어디가 왜 문제인지 구체적으로 짚어 지적한다. 통과(APPROVE) 기준은 '조사 결과로 뒷받침되는가'이지 개인 취향이 아니다."
)

PRESETS_RAW = [
    {"key": "content_lite", "label": "콘텐츠 제작 · 절약형 (조사 → 작성 → 검수)",
     "desc": "단계가 가장 적어 토큰을 아낍니다. 처음 시작할 때 권장합니다.",
     "agents": [A("researcher", "리서처", _ROLE_RESEARCHER, web=True),
                A("writer", "작성자", _ROLE_WRITER),
                A("reviewer", "리뷰어", _ROLE_REVIEWER, model="haiku")],
     "stages": [S("리서치", "researcher", "work", _RESEARCH),
                S("초안 작성", "writer", "work", _DRAFT, ["리서치"]),
                S("검수", "reviewer", "review", _REVIEW, ["리서치"], "초안 작성", True)]},
    {"key": "content_full", "label": "콘텐츠 제작 · 교차검토 포함 (조사 → 검토 → 작성 → 검수)",
     "desc": "조사 결과를 먼저 검토해 품질을 높입니다. 호출이 1회 더 늘어납니다.",
     "agents": [A("researcher", "리서처", _ROLE_RESEARCHER, web=True),
                A("writer", "작성자", _ROLE_WRITER),
                A("reviewer", "리뷰어", _ROLE_REVIEWER, model="haiku")],
     "stages": [S("리서치", "researcher", "work", _RESEARCH),
                S("교차검토", "reviewer", "review", _CHECK, [], "리서치"),
                S("초안 작성", "writer", "work", _DRAFT, ["리서치"]),
                S("검수", "reviewer", "review", _REVIEW, ["리서치"], "초안 작성", True)]},
    {"key": "blog", "label": "블로그·SNS 글 (기획 → 초안 → 편집)",
     "desc": "주제 기획부터 편집까지. 웹 자료가 필요 없으면 가장 가볍습니다.",
     "agents": [A("planner", "기획자",
                 "콘텐츠 기획 전문가다. 요청을 받으면 이 글을 읽을 독자가 누구이고 무엇을 얻어가야 하는지부터 정의한다. "
                 "그다음 주목을 끌 제목 후보 3개를 제시하고, 글의 흐름을 목차로 설계하며, 전체를 관통할 핵심 메시지를 "
                 "한 줄로 정한다. 이 단계에서는 실제 문장을 쓰지 않고 구조와 방향만 정한다.", web=True),
                A("writer", "작성자",
                 "매력적인 글을 쓰는 전문 작가다. 기획자가 세운 목차와 핵심 메시지를 따라가되, 딱딱한 나열이 아니라 "
                 "독자가 끝까지 읽고 싶어지는 문체로 쓴다. 분량은 요청에 맞추고, 기획 의도에서 벗어나지 않는다."),
                A("editor", "편집자",
                 "출고 전 편집을 담당하는 전문 에디터다. 초안이 기획 의도(목차·핵심 메시지)에서 벗어나지 않았는지, "
                 "문장이 매끄러운지, 톤이 일관적인지, 사실관계에 오류가 없는지 점검한다. 고친 내용은 검수 메모로 남겨 "
                 "무엇을 왜 바꿨는지 알 수 있게 한다.", model="haiku")],
     "stages": [S("기획", "planner", "work", "요청을 분석해 독자, 목적, 제목 후보 3개, 목차, 핵심 메시지를 간결하게 정리한다."),
                S("초안 작성", "writer", "work", "기획안에 따라 글을 작성한다. 분량은 요청에 맞춘다.", ["기획"]),
                S("편집", "editor", "review", "초안을 기획안과 대조해 구조, 문장, 톤을 점검한다.", ["기획"], "초안 작성", True)]},
    {"key": "code", "label": "코드 개발 (설계 → 구현 → 코드리뷰)",
     "desc": "결과는 마크다운 코드 블록으로 저장됩니다. 실제 파일 생성·실행은 하지 않습니다.",
     "agents": [A("architect", "설계자",
                 "소프트웨어 아키텍트다. 요구사항을 분석해 꼭 필요한 구조만 설계한다. 어떤 모듈·함수·클래스가 "
                 "필요한지, 서로 어떻게 연결되는지, 예외 상황은 어떻게 처리할지를 명확히 정의하되 과도한 설계는 "
                 "피한다. 실제 코드는 쓰지 않고 구현자가 그대로 따라갈 수 있는 설계만 남긴다."),
                A("developer", "개발자",
                 "실용적인 소프트웨어 엔지니어다. 설계를 받아 읽기 쉽고 단순한 코드로 구현한다. 영리한 트릭보다 "
                 "명확함을 우선하고, 설계에서 정한 예외 처리와 인터페이스를 그대로 따른다. 핵심적인 부분에는 짧은 "
                 "주석을 남겨 다음 사람이 바로 이해할 수 있게 한다."),
                A("codereviewer", "코드리뷰어",
                 "코드 리뷰를 전문으로 하는 시니어 엔지니어다. 설계 의도와 실제 구현을 대조해 버그, 보안 취약점, "
                 "가독성 문제를 찾아낸다. 지적할 때는 어느 부분이 무엇이 문제이고 왜 문제인지, 가능하면 어떻게 고치면 "
                 "좋을지까지 구체적으로 적는다.", model="haiku")],
     "stages": [S("설계", "architect", "work", "요구사항을 분석해 구조, 주요 함수·클래스, 예외 처리 방침을 간결하게 설계한다."),
                S("구현", "developer", "work", "설계에 따라 코드를 작성해 마크다운 코드 블록으로 출력한다.", ["설계"]),
                S("코드리뷰", "codereviewer", "review", "코드를 설계와 대조해 버그, 보안, 가독성을 점검한다.", ["설계"], "구현", True)]},
    {"key": "repo", "label": "코드 저장소 수정 (구현 → 코드리뷰 → 승인 시 GitHub 반영)",
     "desc": "설정 > 코드 저장소에서 GitHub 저장소를 연결하면 실제 코드 파일을 고치고, 빌드 확인 후 승인하면 푸시합니다.",
     "agents": [A("developer", "개발자",
                 "실무 경험이 많은 소프트웨어 엔지니어다. 연결된 저장소의 기존 코드 스타일·구조·라이브러리를 먼저 파악하고 "
                 "그 방식을 그대로 따라 요청을 구현한다. 변경은 요청 범위로 최소화하고, 관련 없는 파일은 건드리지 않는다. "
                 "필요한 파일만 Grep/Glob으로 찾아 읽어 탐색 비용을 줄이며, 빌드가 깨지지 않도록 문법과 참조를 꼼꼼히 확인한다. "
                 "작업이 끝나면 바꾼 파일과 이유, 사용자가 확인할 점을 짧게 정리한다."),
                A("codereviewer", "코드리뷰어",
                 "코드 리뷰를 전문으로 하는 시니어 엔지니어다. 변경 내용(diff)을 요청과 대조해 요구사항 누락, 버그, 보안 "
                 "취약점, 기존 기능 회귀, 불필요한 변경을 찾아낸다. 지적할 때는 파일과 위치, 문제와 이유, 고치는 방법을 "
                 "구체적으로 적는다. 사소한 취향 차이로 반려하지 않고, 실제로 문제가 되는 것만 수정요청한다. "
                 "저장소 파일은 읽기만 하고 직접 고치지 않는다.")],
     "stages": [S("구현", "developer", "work", "요청을 연결된 저장소 코드에 직접 반영하고, 출력 파일에는 변경 요약만 적는다."),
                S("코드리뷰", "codereviewer", "review", "변경 내용(diff)을 요청과 대조해 버그, 보안, 회귀, 불필요한 변경을 점검한다.", [], "구현")]},
    {"key": "translate", "label": "번역·현지화 (번역 → 감수)",
     "desc": "두 단계뿐이라 토큰이 적게 듭니다.",
     "agents": [A("translator", "번역가",
                 "전문 번역가다. 원문의 의미, 어조, 뉘앙스를 최대한 보존하면서 대상 언어로 자연스럽게 옮긴다. 직역하면 "
                 "어색해지는 표현은 그 언어의 관용적인 표현으로 바꾸되, 원문에 없는 내용을 더하거나 빼지 않는다. "
                 "고유명사와 숫자는 원문 그대로 정확하게 옮긴다."),
                A("proofreader", "감수자",
                 "번역 감수(QA)를 전문으로 하는 바이링구얼 에디터다. 원문과 번역문을 한 문장씩 대조해 오역, 누락, "
                 "어색한 표현을 찾아낸다. 사소한 어투 차이보다 의미가 달라지는 오류를 우선 지적하고, 왜 틀렸는지와 "
                 "더 나은 번역을 함께 제시한다.", model="haiku")],
     "stages": [S("번역", "translator", "work", "요청에 적힌 원문을 지정된 언어로 번역한다. 의미를 더하거나 빼지 않는다."),
                S("감수", "proofreader", "review", "원문과 번역을 대조해 오역, 누락, 어색한 표현을 점검한다.", [], "번역", True)]},
    {"key": "report", "label": "데이터·보고서 (분석 → 보고서 → 검수)",
     "desc": "자료를 분석하고 보고서로 정리합니다.",
     "agents": [A("analyst", "분석가",
                 "데이터·리서치 분석 전문가다. 주제와 관련된 자료를 조사하고 핵심 수치, 추세, 근거를 표와 목록으로 "
                 "정리한다. 수치를 인용할 때는 출처와 기준 시점을 함께 밝히고, 원자료(사실)와 해석(시사점)을 분명히 "
                 "구분해서 적는다.", web=True),
                A("writer", "작성자",
                 "비즈니스·기술 보고서 작성 전문가다. 분석 결과만 근거로 삼아 요약(핵심만 먼저)-본문(근거와 세부사항)"
                 "-결론(그래서 어떻게 해야 하는지) 순서로 보고서를 쓴다. 분석에 없는 숫자나 주장을 만들어내지 않는다."),
                A("reviewer", "리뷰어",
                 "보고서 품질 검수를 전문으로 하는 에디터다. 보고서에 등장하는 모든 수치와 주장이 분석 결과로 "
                 "뒷받침되는지 하나씩 대조하고, 근거 없이 과장된 표현이나 분석과 다른 숫자가 있으면 구체적으로 "
                 "지적한다.", model="haiku")],
     "stages": [S("분석", "analyst", "work", "요청 주제의 자료를 조사·분석해 핵심 수치, 근거, 시사점을 표와 목록으로 정리한다."),
                S("보고서 작성", "writer", "work", "분석 결과만 사용해 요약, 본문, 결론 순서의 보고서를 쓴다.", ["분석"]),
                S("검수", "reviewer", "review", "보고서의 수치와 주장을 분석 결과와 대조해 오류를 점검한다.", ["분석"], "보고서 작성", True)]},
]

DEFAULT_ROLE_TEXT = {"researcher": _ROLE_RESEARCHER, "writer": _ROLE_WRITER, "reviewer": _ROLE_REVIEWER}


def norm_plan(p, max_stages=8, max_agents=6):
    """AI 또는 프리셋이 만든 구성안을 검증·정규화한다. (서버는 클라이언트가 보낸 구성안을 믿지 않는다)"""
    if not isinstance(p, dict):
        raise ValueError("구성안 형식이 올바르지 않습니다")
    agents, keys = [], set()
    for a in (p.get("agents") or [])[:max(1, min(6, max_agents))]:
        if not isinstance(a, dict):
            continue
        key = re.sub(r"[^a-z0-9_]", "", str(a.get("key") or "").lower())[:20] or "a%d" % (len(agents) + 1)
        while key in keys:
            key += "x"
        model = str(a.get("model") or "").strip()
        agents.append({"key": key, "name": (str(a.get("name") or key).strip()[:30] or key),
                       "role": str(a.get("role") or "").strip()[:1500], "web": bool(a.get("web")),
                       "model": model if MODEL_RE.match(model) else ""})
        keys.add(key)
    if not agents:
        raise ValueError("에이전트가 없습니다")
    stages, ref = [], {}
    raw, lim = (p.get("stages") or []), max(1, min(8, max_stages))
    if len(raw) > lim:   # 앞쪽을 줄이고 마지막(보통 최종 검토) 단계는 남긴다
        raw = raw[:1] if lim == 1 else raw[:lim - 1] + raw[-1:]
    for i, s in enumerate(raw):
        if not isinstance(s, dict):
            continue
        name = (str(s.get("name") or "").strip()[:30]) or "단계%d" % (i + 1)
        kind = "review" if (s.get("kind") == "review" and stages) else "work"
        agent = s.get("agent") if s.get("agent") in keys else agents[0]["key"]
        sid = "s%d" % (len(stages) + 1)
        target = ""
        if kind == "review":
            target = ref.get(str(s.get("target") or ""), "")
            if not target:
                works = [x for x in stages if x["kind"] == "work"]
                if works:
                    target = works[-1]["id"]
                else:
                    kind = "work"
        inputs = []
        for x in (s.get("inputs") or []):
            r = ref.get(str(x))
            if r and r not in inputs and r != target:
                inputs.append(r)
        stages.append({"id": sid, "name": name, "kind": kind, "agent": agent, "target": target, "inputs": inputs,
                       "instruction": str(s.get("instruction") or "").strip()[:3000], "enabled": True,
                       "max_turns": 0, "polish": bool(s.get("polish")) and kind == "review"})
        ref[name] = sid
        ref[sid] = sid
    if not any(s["kind"] == "work" for s in stages):
        raise ValueError("'작업' 단계가 하나 이상 필요합니다")
    if stages[-1]["kind"] == "review" and not any(s["polish"] for s in stages):
        stages[-1]["polish"] = True
    return {"agents": agents, "stages": stages}


PRESETS = []
for _p in PRESETS_RAW:
    _n = norm_plan(_p)
    PRESETS.append({"key": _p["key"], "label": _p["label"], "desc": _p["desc"], "plan": _n})


# ---------------------------------------------------------------- 설정 저장 · 프로젝트 조회

def S_():
    return CFG["settings"]


def save_cfg():
    write_json(CONFIG_FILE, CFG)


def proj_dirs(proj):
    root = BASE if proj["root"] == "." else (BASE / proj["root"]).resolve()
    sh = root / "shared"
    return {"root": root, "shared": sh, "inbox": sh / "inbox", "handoff": sh / "handoff", "outbox": sh / "outbox",
            "jobs": sh / "jobs", "hist": sh / "history", "sources": sh / "sources",
            "logs": BASE / "logs" / proj["id"]}


def ensure_dirs(proj):
    for k in ("inbox", "handoff", "outbox", "jobs", "hist", "sources", "logs"):
        proj_dirs(proj)[k].mkdir(parents=True, exist_ok=True)


def proj_of(pid):
    if not ID_RE.match(pid or ""):
        raise ApiError(400, "잘못된 프로젝트 ID")
    p = next((x for x in CFG["projects"] if x["id"] == pid), None)
    if not p:
        raise ApiError(404, "프로젝트를 찾을 수 없음")
    return p


def agent_of(proj, aid):
    a = next((x for x in proj["agents"] if x["id"] == aid), None)
    if not a:
        raise ApiError(404, "에이전트를 찾을 수 없음")
    return a


def agent_name(proj, aid):
    a = next((x for x in proj["agents"] if x["id"] == aid), None)
    return a["name"] if a else "(없음)"


def active_stages(proj):
    return [s for s in proj["stages"] if s.get("enabled", True)]


def migrate():
    """기존(v2) agents.json 이 있으면 그 에이전트와 단계 담당을 default 프로젝트로 이전한다."""
    agents = [{"id": "researcher", "name": "리서처", "workspace": "workspace_1", "model": ""},
              {"id": "writer", "name": "작성자", "workspace": "workspace_2", "model": ""},
              {"id": "reviewer", "name": "리뷰어", "workspace": "workspace_3", "model": ""}]
    who = {"research": "researcher", "check_research": "writer", "draft": "writer", "review": "reviewer"}
    try:
        old = json.loads(LEGACY_FILE.read_text())
        if old.get("agents"):
            agents = old["agents"]
            who.update(old.get("stages") or {})
    except (OSError, ValueError):
        pass

    def st(i, name, kind, agent, instr, inputs=(), target="", polish=False):
        return {"id": i, "name": name, "kind": kind, "agent": agent, "target": target, "inputs": list(inputs),
                "instruction": instr, "enabled": True, "max_turns": 0, "polish": polish}
    stages = [st("research", "리서치", "work", who["research"], _RESEARCH),
              st("check_research", "교차검토", "review", who["check_research"], _CHECK, [], "research"),
              st("draft", "초안 작성", "work", who["draft"], _DRAFT, ["research"]),
              st("review", "리뷰", "review", who["review"], _REVIEW, ["research"], "draft", True)]
    return {"settings": copy.deepcopy(DEFAULT_SETTINGS),
            "projects": [{"id": "default", "name": "기본 프로젝트", "description": "기존에 쓰던 작업 공간", "root": ".",
                          "agents": agents, "stages": stages, "max_rounds": 2, "schedules": [],
                          "stage_mode": "fixed", "created": now()}]}


def load_cfg():
    global CFG
    try:
        CFG = json.loads(CONFIG_FILE.read_text())
    except FileNotFoundError:
        CFG = migrate()
    except ValueError:
        sys.exit("projects.json 형식이 깨져 있습니다: %s" % CONFIG_FILE)
    CFG.setdefault("settings", {})
    for k, v in DEFAULT_SETTINGS.items():
        CFG["settings"].setdefault(k, copy.deepcopy(v))
    for k, v in DEFAULT_SETTINGS["telegram"].items():
        CFG["settings"]["telegram"].setdefault(k, copy.deepcopy(v))
    for p in CFG["projects"]:
        p.setdefault("max_rounds", 1)
        p.setdefault("description", "")
        p.setdefault("schedules", [])
        p.setdefault("stage_mode", "fixed")
        p.setdefault("use_sources", "prefer")
    if any(p.get("repo") for p in CFG["projects"]) and CONFIG_FILE.exists():
        # 저장소 설정 형식이 바뀌기 전 원본을 남겨 둔다(문제가 생기면 이 파일로 되돌릴 수 있게)
        shutil.copy2(CONFIG_FILE, CONFIG_FILE.with_name("projects.json.before-multirepo"))
    for p in CFG["projects"]:
        migrate_repo_cfg(p)
    save_cfg()


# ---------------------------------------------------------------- 에이전트 설정 파일 · 신뢰 등록

def build_settings(proj, perms):
    allow = ["Read", "Write", "Edit"]
    src = proj_dirs(proj)["sources"]
    deny = ["Bash(sudo:*)", "Bash(rm:*)", "Read(/%s)" % (BASE / ".env"),
            "Bash(mariadb:*)", "Bash(mysql:*)", "Bash(mariadb-dump:*)", "Bash(mysqldump:*)",
            "Write(/%s/**)" % src, "Edit(/%s/**)" % src]   # 참고 자료는 읽기만 허용
    if perms.get("web"):
        allow += ["WebSearch", "WebFetch"]
    else:
        deny += ["WebSearch", "WebFetch"]
    if perms.get("bash"):
        allow.append("Bash")
    dirs = [str(proj_dirs(proj)["shared"])]
    deny.append("Read(/%s/**)" % (Path.home() / ".ssh"))   # 저장소 접근 키는 에이전트가 읽지 못한다
    if repo_on(proj):
        allow += ["Glob", "Grep"]
        deny += ["Bash(git push:*)", "Bash(git commit:*)"]
        for r in repos_of(proj):
            rd = str(Path(r["path"]))
            dirs.append(rd)
            deny += ["Write(/%s/.git/**)" % rd, "Edit(/%s/.git/**)" % rd]
    return {"permissions": {"additionalDirectories": dirs, "allow": allow, "deny": deny}}


def refresh_agent_settings(proj):
    """저장소 연결이 바뀌면 각 에이전트의 접근 폴더·권한을 다시 쓴다(기존 웹/Bash 권한은 유지)."""
    root = proj_dirs(proj)["root"]
    for a in proj["agents"]:
        sp = root / a["workspace"] / ".claude" / "settings.json"
        if sp.parent.is_dir():
            sp.write_text(json.dumps(build_settings(proj, parse_perms(sp)), ensure_ascii=False, indent=2))


def read_allow(path):
    try:
        return json.loads(path.read_text()).get("permissions", {}).get("allow", [])
    except (OSError, ValueError):
        return None


def parse_perms(path):
    allow = read_allow(path) or []
    return {"web": "WebSearch" in allow or "WebFetch" in allow, "bash": "Bash" in allow}


def agent_tools(ws):
    """에이전트가 쓸 수 있는 기본 도구만 모델에 노출한다(도구 정의가 줄어 토큰이 절약된다)."""
    allow = read_allow(ws / ".claude" / "settings.json")
    tools = [t for t in (allow or []) if re.match(r"^[A-Za-z]+$", t)]
    for need in ("Read", "Write", "Edit"):
        if need not in tools:
            tools.append(need)
    return tools


def md_template(name, desc):
    desc = (desc or "").strip()
    body = desc or (
        "이 에이전트가 맡을 전문 분야와 접근 방식을 적어주세요. 예:\n"
        "- 어떤 주제·업무를 전문으로 다루는가\n"
        "- 어떤 방식·순서로 작업하는가\n"
        "- 결과물을 어떤 기준으로 판단하는가 (정확성, 근거, 분량, 톤 등)\n"
        "- 하지 않는 일이 있다면 무엇인가"
    )
    return ("# 역할: %s\n\n%s\n\n"
            "## 작업 원칙\n"
            "- 확인된 사실과 추측·의견을 분명히 구분해서 적는다\n"
            "- 모르거나 확인하지 못한 부분은 숨기지 않고 그대로 알린다\n"
            "- 불필요하게 분량을 늘리지 않고 핵심부터 전달한다\n\n"
            "## 공통 규칙\n"
            "- 작업 지시에 적힌 입력 파일(과 참고 자료)만 읽는다\n"
            "- 지정된 출력 파일에 Write 도구로 반드시 저장한다\n"
            "- 저장을 마치면 한 줄로 결과를 보고하고 종료한다\n" % (name, body))


def is_trusted(ws):
    try:
        d = json.loads(CLAUDE_JSON.read_text())
        return bool(d.get("projects", {}).get(str(ws.resolve()), {}).get("hasTrustDialogAccepted"))
    except (OSError, ValueError):
        return False


def flush_trust():
    """claude 설정 파일(~/.claude.json)은 에이전트가 실행 중일 때 건드리면 충돌할 수 있어, 유휴 시에만 쓴다."""
    with LOCK:
        if PROCS or not PENDING_TRUST:
            return
        try:
            d = json.loads(CLAUDE_JSON.read_text())
        except FileNotFoundError:
            d = {}
        except ValueError:
            return
        for p in PENDING_TRUST:
            d.setdefault("projects", {}).setdefault(p, {})["hasTrustDialogAccepted"] = True
        tmp = CLAUDE_JSON.with_suffix(".tmp")
        tmp.write_text(json.dumps(d, indent=2))
        os.chmod(tmp, 0o600)
        tmp.replace(CLAUDE_JSON)
        PENDING_TRUST.clear()


def trust(ws):
    if is_trusted(ws):
        return True
    PENDING_TRUST.add(str(ws.resolve()))
    flush_trust()
    return is_trusted(ws)


def agent_problems(proj, a):
    ws = proj_dirs(proj)["root"] / a["workspace"]
    if not ws.is_dir():
        return ["워크스페이스 폴더가 없습니다: %s" % a["workspace"]]
    out = []
    if not (ws / ".claude" / "settings.json").exists():
        out.append("권한 설정(settings.json)이 없어 공유 폴더에 결과를 쓰지 못합니다")
    if not (ws / "CLAUDE.md").exists():
        out.append("역할 설명(CLAUDE.md)이 없습니다")
    if not is_trusted(ws):
        out.append("폴더 신뢰 등록이 안 되어 권한 설정이 무시됩니다")
    return out


def backup_file(proj, path):
    if path.exists():
        d = proj_dirs(proj)["hist"] / "_agents" / path.parent.name
        d.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, d / ("%s.%s" % (path.name, time.strftime("%Y%m%d-%H%M%S"))))


def agent_info(proj, a, full=False):
    ws = proj_dirs(proj)["root"] / a["workspace"]
    info = {"id": a["id"], "name": a["name"], "workspace": a["workspace"], "model": a.get("model", ""),
            "problems": agent_problems(proj, a),
            "stages": [s["name"] for s in proj["stages"] if s["agent"] == a["id"]]}
    if full:
        md = read_text(ws / "CLAUDE.md")
        info["claude_md"] = md if md is not None else md_template(a["name"], DEFAULT_ROLE_TEXT.get(a["id"], ""))
        info["has_md"] = md is not None
        sp = ws / ".claude" / "settings.json"
        info["perms"] = parse_perms(sp) if sp.exists() else {"web": a["id"] == "researcher", "bash": False}
    return info


def ws_slug(name):
    """에이전트 이름을 폴더 이름으로 쓸 수 있게 다듬는다. 한글은 그대로 두고(리눅스는 UTF-8 파일명을 지원한다),
    경로에 문제가 될 문자만 없앤다."""
    s = re.sub(r"[^\w가-힣 ()\-]", "", name or "").strip()
    s = re.sub(r"\s+", " ", s)[:40]
    return s


def free_ws_name(root, base, used, keep=""):
    name, i = base, 1
    while name in used or name in RESERVED_DIR or (name != keep and (root / name).exists()):
        i += 1
        name = "%s %d" % (base, i)
    return name


def create_agent_in(proj, name, desc, perms, model="", existing=""):
    root = proj_dirs(proj)["root"]
    used = {a["workspace"] for a in proj["agents"]}
    if existing:
        if not ID_RE.match(existing) or existing in RESERVED_DIR:
            raise ApiError(400, "폴더 이름이 올바르지 않습니다")
        if existing in used:
            raise ApiError(409, "이미 등록된 폴더입니다")
        if not (root / existing).is_dir():
            raise ApiError(404, "그 이름의 폴더가 없습니다: %s" % existing)
        ws_name = existing
    else:
        ws_name = free_ws_name(root, ws_slug(name) or "agent", used)
    ws = root / ws_name
    (ws / ".claude").mkdir(parents=True, exist_ok=True)
    if not (ws / "CLAUDE.md").exists():
        (ws / "CLAUDE.md").write_text(md_template(name, desc))
    sp = ws / ".claude" / "settings.json"
    if not sp.exists():
        sp.write_text(json.dumps(build_settings(proj, perms), ensure_ascii=False, indent=2))
    nums = [int(re.sub(r"\D", "", a["id"]) or 0) for a in proj["agents"]]
    a = {"id": "agent%d" % (max(nums + [0]) + 1), "name": name, "workspace": ws_name, "model": model}
    proj["agents"].append(a)
    trust(ws)
    return a


def validate_stages(proj, raw):
    if not isinstance(raw, list) or not 1 <= len(raw) <= 10:
        raise ApiError(400, "단계는 1~10개여야 합니다")
    out, ids = [], []
    for s in raw:
        if not isinstance(s, dict):
            raise ApiError(400, "단계 형식 오류")
        sid = str(s.get("id") or "").strip()
        if not ID_RE.match(sid) or sid in RESERVED_STAGE or sid in ids:
            raise ApiError(400, "단계 ID가 올바르지 않거나 중복입니다: %s" % sid)
        name = str(s.get("name") or "").strip()[:30]
        if not name:
            raise ApiError(400, "단계 이름을 입력하세요")
        kind = "review" if s.get("kind") == "review" else "work"
        agent = str(s.get("agent") or "")
        if not any(a["id"] == agent for a in proj["agents"]):
            raise ApiError(400, "'%s' 단계의 담당 에이전트가 올바르지 않습니다" % name)
        target = ""
        if kind == "review":
            target = str(s.get("target") or "")
            if target not in ids:
                if not ids:
                    raise ApiError(400, "첫 단계는 '검토'가 될 수 없습니다")
                target = ids[-1]
        try:
            mt = max(0, min(60, int(s.get("max_turns") or 0)))
        except (TypeError, ValueError):
            mt = 0
        out.append({"id": sid, "name": name, "kind": kind, "agent": agent, "target": target,
                    "inputs": [x for x in (s.get("inputs") or []) if x in ids and x != target],
                    "instruction": str(s.get("instruction") or "").strip()[:3000],
                    "enabled": bool(s.get("enabled", True)), "max_turns": mt,
                    "polish": bool(s.get("polish")) and kind == "review"})
        ids.append(sid)
    en = [s for s in out if s["enabled"]]
    if not en or en[0]["kind"] != "work":
        raise ApiError(400, "사용 중인 첫 단계는 '작업'이어야 합니다")
    return out


def apply_plan(proj, plan):
    """구성안을 프로젝트에 적용: 에이전트를 새로 만들고 단계를 교체한다. 기존 에이전트는 그대로 둔다."""
    kmap = {}
    for a in plan["agents"]:
        ag = create_agent_in(proj, a["name"], a["role"], {"web": a["web"], "bash": False}, a["model"])
        kmap[a["key"]] = ag["id"]
    proj["stages"] = [dict(s, agent=kmap[s["agent"]]) for s in plan["stages"]]


# ---------------------------------------------------------------- 파일 경로 · 작업 상태

def fpath(proj, kind, jid):
    d = proj_dirs(proj)
    if kind == "request":
        return d["inbox"] / ("%s.md" % jid)
    if kind == "final":
        return d["outbox"] / ("final_%s.md" % jid)
    if kind == "approved":
        return d["outbox"] / ("approved_%s.md" % jid)
    return d["handoff"] / ("%s_%s.md" % (kind, jid))


def rel(proj, kind, jid):
    p = fpath(proj, kind, jid)
    return "../shared/%s/%s" % (p.parent.name, p.name)


def jsave(job):
    write_json(proj_dirs(proj_of(job["pid"]))["jobs"] / ("%s.json" % job["id"]), job)


def event(job, agent, msg, kind="info"):
    with LOCK:
        job["events"].append({"ts": now(), "agent": agent, "msg": msg, "kind": kind})
        job["updated"] = now()
        jsave(job)


def set_state(job, **kw):
    with LOCK:
        job.update(kw)
        job["updated"] = now()
        jsave(job)


def archive(proj, jid, path):
    if path.exists():
        d = proj_dirs(proj)["hist"] / jid
        d.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, d / ("%s.%s" % (path.name, time.strftime("%H%M%S"))))


def new_tokens(u):
    return int(u.get("input", 0)) + int(u.get("output", 0)) + int(u.get("cache_write", 0))


def _acc(t, inp, out, cw, cr, cost):
    t["input"] = t.get("input", 0) + inp
    t["output"] = t.get("output", 0) + out
    t["cache_write"] = t.get("cache_write", 0) + cw
    t["cache_read"] = t.get("cache_read", 0) + cr
    t["cost"] = round(t.get("cost", 0.0) + cost, 6)
    t["calls"] = t.get("calls", 0) + 1


def add_usage(job, stage_id, data):
    u = data.get("usage") or {}
    vals = [int(u.get(k) or 0) for k in ("input_tokens", "output_tokens", "cache_creation_input_tokens", "cache_read_input_tokens")]
    try:
        cost = float(data.get("total_cost_usd") or 0)
    except (TypeError, ValueError):
        cost = 0.0
    with LOCK:
        tot = job.setdefault("usage", {})
        _acc(tot, *vals, cost)
        _acc(tot.setdefault("by_stage", {}).setdefault(stage_id, {}), *vals, cost)
        jsave(job)


# ---------------------------------------------------------------- 에이전트 실행

def child_env():
    e = dict(os.environ)
    for k in list(e):   # 에이전트에게 비밀번호·토큰을 넘기지 않는다 (DB 비밀번호 포함)
        if re.search(r"PASSWORD|SECRET|_PWD$", k) or k == "TELEGRAM_BOT_TOKEN":
            e.pop(k, None)
    e.setdefault("DISABLE_AUTOUPDATER", "1")
    e.setdefault("CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC", "1")
    return e


def probe_flags():
    """설치된 claude가 지원하는 토큰 절감 옵션만 쓰도록 --help 로 확인한다."""
    global FLAGS
    mode = os.environ.get("AGENT_FLAGS", "auto")
    if mode == "none":
        FLAGS = {f: False for f in OPT_FLAGS}
        return
    if mode == "all":
        FLAGS = {f: True for f in OPT_FLAGS}
        return
    try:
        out = subprocess.run(shlex.split(AGENT_CMD) + ["--help"], capture_output=True, text=True,
                             timeout=60, env=child_env()).stdout
    except Exception:  # noqa: BLE001
        out = ""
    FLAGS = {f: (f in out) for f in OPT_FLAGS}


def build_cmd(prompt, model="", turns=10, tools=None):
    cmd = shlex.split(AGENT_CMD) + ["-p", prompt, "--output-format", "json", "--max-turns", str(turns),
                                    "--permission-mode", "acceptEdits"]
    if model:
        cmd += ["--model", model]
    if tools is not None and FLAGS.get("--tools"):
        cmd += ["--tools", ",".join(tools)]
    for f in ("--strict-mcp-config", "--disable-slash-commands", "--no-session-persistence"):
        if FLAGS.get(f):
            cmd.append(f)
    return cmd


def parse_result(text):
    t = (text or "").strip()
    cands = [t]
    if "\n{" in t:
        cands.append(t[t.rfind("\n{"):].strip())
    for c in cands:
        try:
            d = json.loads(c)
        except ValueError:
            continue
        if isinstance(d, list):
            d = next((x for x in reversed(d) if isinstance(x, dict) and x.get("type") == "result"), None)
        if isinstance(d, dict):
            return d
    return None


def kill_proc(p):
    try:
        os.killpg(p.pid, signal.SIGTERM)
        time.sleep(1)
        os.killpg(p.pid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        pass


def run_agent(job, proj, agent, stage, prompt):
    d = proj_dirs(proj)
    ws = d["root"] / agent["workspace"]
    if not ws.is_dir():
        raise RuntimeError("워크스페이스가 없음: %s" % ws)
    d["logs"].mkdir(parents=True, exist_ok=True)
    log = d["logs"] / ("%s_%s_%s.log" % (job["id"], stage["id"], time.strftime("%H%M%S")))
    turns = stage.get("max_turns") or DEFAULT_TURNS[stage["kind"]]
    cmd = build_cmd(prompt, agent.get("model", ""), turns, agent_tools(ws))
    key = (proj["id"], job["id"])
    with open(log, "wb") as lf:
        p = subprocess.Popen(cmd, cwd=ws, env=child_env(), stdout=lf, stderr=subprocess.STDOUT,
                             start_new_session=True)
        PROCS[key] = p
        try:
            rc = p.wait(timeout=STEP_TIMEOUT)
        except subprocess.TimeoutExpired:
            kill_proc(p)
            raise RuntimeError("시간 초과(%d초)" % STEP_TIMEOUT)
        finally:
            PROCS.pop(key, None)
    text = read_text(log) or ""
    data = parse_result(text)
    if data:
        add_usage(job, stage["id"], data)
    if job.get("cancel"):
        raise Cancelled()
    if data:
        sub = str(data.get("subtype") or "")
        if data.get("is_error") or sub.startswith("error"):
            hint = "최대 턴(%d)을 초과했습니다. 단계의 '최대 턴'을 늘려보세요. " % turns if "max_turns" in sub else ""
            raise RuntimeError("에이전트 오류(%s): %s%s" % (sub or "error", hint, str(data.get("result") or "")[:300]))
        reply = str(data.get("result") or "")
    elif rc != 0:
        raise RuntimeError("에이전트 종료 코드 %s: %s" % (rc, text[-300:].strip()))
    else:
        reply = text
    check_budget(job)
    return reply


def check_budget(job):
    limit = int(S_().get("job_token_limit") or 0)
    if limit and new_tokens(job.get("usage") or {}) > limit:
        raise RuntimeError("작업 토큰 한도(%s) 초과: 현재 %s. 설정에서 한도를 조정하세요" %
                           (limit, new_tokens(job["usage"])))


def run_step(job, proj, stage, prompt, remove_kinds=()):
    jid = job["id"]
    if job.get("cancel"):
        raise Cancelled()
    agent = next((a for a in proj["agents"] if a["id"] == stage["agent"]), None)
    if not agent:
        raise RuntimeError("'%s' 단계의 담당 에이전트가 없습니다 (단계 탭에서 지정하세요)" % stage["name"])
    who = agent["name"]
    set_state(job, step=stage["id"])
    event(job, who, "%s 시작" % stage["name"])
    for pr in agent_problems(proj, agent):
        event(job, who, "설정 확인 필요: %s" % pr, "warn")
    for k in remove_kinds:
        archive(proj, jid, fpath(proj, k, jid))
        fpath(proj, k, jid).unlink(missing_ok=True)
    out = fpath(proj, stage["id"], jid)
    archive(proj, jid, out)
    reply = ""
    for attempt in range(2):
        if job.get("cancel"):
            raise Cancelled()
        started = time.time() - 1
        reply = run_agent(job, proj, agent, stage, prompt if attempt == 0 else prompt + RETRY_SUFFIX)
        if out.exists() and out.stat().st_mtime >= started:
            event(job, who, "%s 완료" % stage["name"], "ok")
            return
        if attempt == 0:
            event(job, who, "%s: 파일 저장이 확인되지 않아 한 번 더 지시합니다" % stage["name"], "warn")
    raise RuntimeError("%s 결과 파일이 두 번 시도에도 저장되지 않음 (담당: %s, 폴더: %s)\n에이전트 응답: %s"
                       % (stage["name"], who, agent["workspace"], reply.strip()[-500:] or "(응답 없음)"))


# ---------------------------------------------------------------- 코드 저장소 연동 (git·빌드는 하네스가 직접 실행해 토큰을 쓰지 않는다)
# 프로젝트 하나에 저장소 여러 개(예: 프론트·API)를 연결할 수 있다. 저장소 설정은 proj["repos"] 목록에 들어 있다.

REPO_URL_RE = re.compile(r"^(git@[\w.-]+:[\w./-]+|https://[\w.-]+/[\w./-]+|ssh://[\w@.:/-]+)$")
REPO_PATH_RE = re.compile(r"^/[\w./-]+$")
BRANCH_RE = re.compile(r"^[\w][\w./-]{0,59}$")
RID_RE = re.compile(r"^[a-z0-9_]{1,20}$")
KEY_DIR = Path.home() / ".ssh"
BUILD_TIMEOUT = int(os.environ.get("BUILD_TIMEOUT", "900"))
BUILD_FIX_TRIES = int(os.environ.get("BUILD_FIX_TRIES", "2"))
REPO_LOCKS = {}
GIT_ID = ["-c", "user.name=agent-harness", "-c", "user.email=agent-harness@localhost"]


def migrate_repo_cfg(proj):
    """예전 단일 저장소 설정(proj["repo"])을 목록 형식(proj["repos"])으로 옮긴다."""
    old = proj.pop("repo", None)
    if old and old.get("url") and not proj.get("repos"):
        rs = old.pop("releases", [])
        r = dict(old, id="main", name=old.get("name") or "저장소", key=str(KEY_DIR / ("harness_%s" % proj["id"])))
        proj["repos"] = [r]
        proj["releases"] = [{"ts": x.get("ts", ""), "by": x.get("by", ""), "n": x.get("n", 0), "msgs": x.get("msgs", []),
                             "rollback": x.get("rollback", False),
                             "heads": {"main": x.get("sha", "")}, "before": {"main": x.get("prev", "")}} for x in rs]
        return True
    return False


def repos_of(proj):
    return [r for r in (proj.get("repos") or []) if r.get("url") and r.get("path")]


def repo_by(proj, rid):
    for r in proj.get("repos") or []:
        if r.get("id") == rid:
            return r
    raise ApiError(404, "저장소를 찾을 수 없습니다: %s" % rid)


def repo_on(proj):
    return bool(repos_of(proj))


def repo_release(proj):
    """테스트→운영 단계를 쓰는지(저장소 중 하나라도 운영 브랜치가 있으면)."""
    return any(r.get("release") for r in repos_of(proj))


def repo_base(proj):
    rs = repos_of(proj)
    return (rs[0].get("branch") or "main") if rs else "main"


def repo_test_url(proj):
    return next((r["test_url"] for r in repos_of(proj) if r.get("test_url")), "")


def rbase(r):
    return r.get("branch") or "main"


def rkey(proj, r):
    return Path(r["key"]) if r.get("key") else KEY_DIR / ("harness_%s_%s" % (proj["id"], r["id"]))


def job_branch(jid):
    return "harness/" + jid


def repo_lock(pid):
    with LOCK:
        return REPO_LOCKS.setdefault(pid, threading.Lock())


def git_env(keyfile=None):
    e = child_env()
    e["GIT_TERMINAL_PROMPT"] = "0"
    key = "-i %s -o IdentitiesOnly=yes " % shlex.quote(str(keyfile)) if keyfile and Path(keyfile).exists() else ""
    e["GIT_SSH_COMMAND"] = "ssh %s-o StrictHostKeyChecking=accept-new -o BatchMode=yes" % key
    return e


def git(cwd, *args, timeout=120, check=True, key=None):
    try:
        r = subprocess.run(["git", *GIT_ID, *args], cwd=str(cwd), env=git_env(key), capture_output=True, text=True,
                           timeout=timeout)
    except subprocess.TimeoutExpired:
        raise RuntimeError("git %s 시간 초과" % args[0])
    if check and r.returncode:
        raise RuntimeError("git %s 실패: %s" % (args[0], (r.stderr or r.stdout).strip()[-500:]))
    return r.stdout if check else r


def G(proj, r, *args, **kw):
    """저장소 r 에서 git 실행(그 저장소의 배포 키 사용)."""
    return git(r["path"], *args, key=rkey(proj, r), **kw)


def web_url(url):
    m = re.match(r"^(?:git@([\w.-]+):|https://([\w.-]+)/|ssh://git@([\w.-]+)/)([\w.-]+/[\w.-]+?)(?:\.git)?/?$", url or "")
    return "https://%s/%s" % (m.group(1) or m.group(2) or m.group(3), m.group(4)) if m else ""


def one_status(proj, r):
    out = {"cfg": {k: r.get(k, "") for k in ("id", "name", "url", "path", "branch", "release", "merge", "build", "deploy",
                                           "test_url")},
           "cloned": False, "key": "", "web": web_url(r.get("url")), "pending": []}
    pub = rkey(proj, r).with_suffix(".pub")
    if pub.exists():
        out["key"] = pub.read_text().strip()
    if r.get("path") and (Path(r["path"]) / ".git").is_dir():
        out["cloned"] = True
        res = G(proj, r, "log", "-1", "--format=%h %s (%cr)", check=False)
        out["head"] = res.stdout.strip() if res.returncode == 0 else ""
        rel = r.get("release")
        if rel:
            res = G(proj, r, "log", "--no-merges", "--format=%h\t%s\t%cr", "origin/%s..origin/%s" % (rel, rbase(r)), check=False)
            if res.returncode == 0:
                out["pending"] = [dict(zip(("sha", "msg", "when"), l.split("\t", 2))) for l in res.stdout.splitlines()[:30]]
            res = G(proj, r, "log", "-1", "--format=%h %s (%cr)", "origin/" + rel, check=False)
            out["release_head"] = res.stdout.strip() if res.returncode == 0 else ""
    return out


def repo_status(proj):
    names = {r["id"]: r.get("name", r["id"]) for r in proj.get("repos") or []}
    return {"repos": [one_status(proj, r) for r in proj.get("repos") or []], "releases": (proj.get("releases") or [])[:15],
            "names": names, "default_path": str(BASE / "repos" / ("%s_%s" % (proj["id"], "r%d" % (len(proj.get("repos") or []) + 1))))}


# ---- 작업별 반영 기록: j["merges"] = {저장소id: 테스트 브랜치 병합 커밋}
def job_merges(j):
    m = dict(j.get("merges") or {})
    if not m and j.get("merge_sha"):
        m["main"] = j["merge_sha"]
    return m


def is_anc(proj, r, a, b):
    return G(proj, r, "merge-base", "--is-ancestor", a, b, check=False).returncode == 0


def job_released(proj, j):
    for rid, sha in job_merges(j).items():
        try:
            r = repo_by(proj, rid)
        except ApiError:
            continue
        if r.get("release") and not is_anc(proj, r, sha, "origin/" + r["release"]):
            return False
    return True


def sync_release_states(proj):
    """운영 브랜치에 들어간 작업은 '운영 반영', 아직이면(되돌리기 포함) '운영 대기'로 맞춘다."""
    if not repo_release(proj):
        return
    for (pid, _), j in list(JOBS.items()):
        if pid != proj["id"] or not job_merges(j) or j.get("status") != "approved":
            continue
        inside = job_released(proj, j)
        if inside and j.get("release_state") != "released":
            set_state(j, release_state="released", released_at=now())
            event(j, "system", "운영 반영 완료", "ok")
        elif not inside and j.get("release_state") == "released":
            set_state(j, release_state="pending", released_at="")
            event(j, "system", "운영이 이전 버전으로 되돌려져 다시 운영 대기", "warn")


def backfill_release(proj, j):
    """운영 대기 기능이 생기기 전에 승인한 작업: 테스트 브랜치의 병합 커밋을 찾아 상태를 채운다."""
    try:
        merges = {}
        for r in repos_of(proj):
            res = G(proj, r, "log", "--merges", "--fixed-strings", "--format=%H", "--grep=Merge %s:" % job_branch(j["id"]),
                    "origin/" + rbase(r), check=False)
            sha = (res.stdout.split() or [""])[0] if res.returncode == 0 else ""
            if sha:
                merges[r["id"]] = sha
        if not merges:
            set_state(j, release_state="none")
            return
        set_state(j, merges=merges, merge_sha="")
        set_state(j, release_state="released" if job_released(proj, j) else "pending")
    except Exception:  # noqa: BLE001
        pass


def _aorder(j):
    return j.get("approved_at") or j.get("updated") or ""


def pending_jobs(proj, upto=None):
    """운영 대기 작업 목록(승인 순). upto(작업)를 주면 그 작업을 운영에 올릴 때 함께 올라가는 작업,
    즉 upto 와 그보다 먼저 승인된 운영 대기 작업 전부(저장소가 여러 개여도 한 작업의 일부만 올라가지 않게)."""
    js = sorted([j for (pid, _), j in JOBS.items() if pid == proj["id"] and j.get("release_state") == "pending"
                 and j.get("status") == "approved" and job_merges(j)], key=_aorder)
    if upto:
        js = [j for j in js if _aorder(j) <= _aorder(upto)]
        if upto not in js and upto.get("release_state") == "pending":
            js.append(upto)
    return js


def _push_release(proj, r, target):
    """운영 브랜치를 target 으로 올린다(빨리감기가 안 되면 병합 커밋)."""
    rel, base = r["release"], rbase(r)
    G(proj, r, "reset", "--hard", "-q")
    if is_anc(proj, r, "origin/" + rel, target):
        G(proj, r, "push", "-q", "origin", "%s:refs/heads/%s" % (G(proj, r, "rev-parse", target).strip(), rel), timeout=300)
    else:   # 운영 브랜치에 직접 들어간 수정이 있으면 병합 커밋을 만든다
        G(proj, r, "checkout", "-q", "-B", "_release", "origin/" + rel)
        res = G(proj, r, "merge", "--no-ff", "-m", "운영 반영: %s → %s" % (base, rel), target, check=False)
        if res.returncode:
            G(proj, r, "merge", "--abort", check=False)
            raise ApiError(409, "%s: 운영 브랜치와 충돌이 나서 자동으로 올릴 수 없습니다. GitHub에서 직접 병합하세요" % r.get("name"))
        G(proj, r, "push", "-q", "origin", "HEAD:refs/heads/" + rel, timeout=300)
    G(proj, r, "fetch", "origin", rel, timeout=300)


def _heads(proj):
    out = {}
    for r in repos_of(proj):
        if r.get("release"):
            res = G(proj, r, "rev-parse", "origin/" + r["release"], check=False)
            if res.returncode == 0:
                out[r["id"]] = res.stdout.strip()[:12]
    return out


def _record_release(proj, entry):
    with LOCK:
        rs = proj.setdefault("releases", [])
        rs.insert(0, entry)
        del rs[30:]
        sync_release_states(proj)
        save_cfg()


def repo_promote(proj, who="GUI", job=None):
    """테스트 브랜치에서 확인된 변경을 운영 브랜치로 올린다. job 을 주면 그 작업(과 그 전에 승인된 작업)까지만.
    NAS 운영 서버는 1분 안에 이를 받아 재배포한다."""
    if not repo_release(proj):
        raise ApiError(400, "운영 브랜치가 설정되지 않았습니다")
    pushed, msgs, n_all, err = [], [], 0, None
    with repo_lock(proj["id"]):
        try:
            rs = [r for r in repos_of(proj) if r.get("release")]
            for r in rs:
                G(proj, r, "fetch", "origin", rbase(r), r["release"], timeout=300)
            before = _heads(proj)
            targets = {}
            if job is not None:
                if not job_merges(job):
                    raise ApiError(409, "이 작업은 테스트 브랜치에 반영된 기록이 없습니다")
                if job_released(proj, job):
                    sync_release_states(proj)
                    raise ApiError(409, "이미 운영에 반영된 작업입니다")
                # 이 작업과 그보다 먼저 승인된 대기 작업을 모두 온전히 올린다: 저장소별로 그중 가장 나중 병합까지
                for jj in pending_jobs(proj, job):
                    for rid, sha in job_merges(jj).items():
                        targets[rid] = sha
                for r in rs:
                    if r["id"] in targets and not is_anc(proj, r, targets[r["id"]], "origin/" + rbase(r)):
                        raise ApiError(409, "%s: 작업 변경이 테스트 브랜치에서 사라졌습니다 (다시 작업이 필요합니다)" % r.get("name"))
            else:
                targets = {r["id"]: "origin/" + rbase(r) for r in rs}
            plan = []
            for r in rs:
                t = targets.get(r["id"])
                if not t:
                    continue
                n = int(G(proj, r, "rev-list", "--count", "--no-merges", "origin/%s..%s" % (r["release"], t)).strip() or 0)
                if n:
                    plan.append((r, t, n))
            if not plan:
                raise ApiError(409, "운영에 올릴 새 변경이 없습니다")
            for r, t, n in plan:
                prev = G(proj, r, "rev-parse", "origin/" + r["release"]).strip()
                _push_release(proj, r, t)
                new = G(proj, r, "rev-parse", "origin/" + r["release"]).strip()
                pushed.append(r.get("name", r["id"]))
                n_all += n
                msgs += ["[%s] %s" % (r.get("name", r["id"]), m) if len(rs) > 1 else m
                         for m in G(proj, r, "log", "--no-merges", "--format=%s", "%s..%s" % (prev, new)).splitlines()]
        except ApiError as e:
            err = e
        except RuntimeError as e:
            err = ApiError(502, "운영 반영 실패: %s" % e)
        if pushed or err is None:
            msgs = list(dict.fromkeys(msgs))
            _record_release(proj, {"ts": now(), "by": who, "n": n_all, "msgs": msgs[:12], "before": before,
                                   "heads": _heads(proj), "partial": bool(err)})
    if err:
        if pushed:
            notify("[%s] 운영 반영 일부 실패: %s 는 올라갔지만 나머지에서 오류가 났습니다.\n%s" % (proj["name"], ", ".join(pushed), err.msg))
            raise ApiError(err.code, "%s 는 운영에 올라갔지만 나머지에서 실패했습니다: %s" % (", ".join(pushed), err.msg))
        raise err
    msgs = list(dict.fromkeys(msgs))
    notify("[%s] 운영 반영 완료 (%s · 변경 %d개) - 1분 안에 운영 서버에 배포됩니다.\n%s"
           % (proj["name"], ", ".join(pushed), n_all, "\n".join("- " + m[:60] for m in msgs[:8])))
    return repo_status(proj)


def repo_rollback(proj, idx, which="heads", who="GUI"):
    """운영 브랜치들을 이력의 한 시점으로 되돌린다. which='heads'면 그 반영 직후, 'before'면 반영 직전 상태로."""
    hist = proj.get("releases") or []
    try:
        ent = hist[int(idx)]
    except (ValueError, IndexError, TypeError):
        raise ApiError(400, "되돌릴 이력을 찾을 수 없습니다")
    snap = ent.get("before" if which == "before" else "heads") or {}
    if not snap:
        raise ApiError(400, "이 이력에는 되돌릴 버전 정보가 없습니다")
    changed = []
    with repo_lock(proj["id"]):
        try:
            before = {}
            for r in repos_of(proj):
                rel, sha = r.get("release"), snap.get(r["id"])
                if not rel or not sha:
                    continue
                G(proj, r, "fetch", "origin", rel, timeout=300)
                cur = G(proj, r, "rev-parse", "origin/" + rel).strip()
                before[r["id"]] = cur[:12]
                full = G(proj, r, "rev-parse", sha).strip()
                if full == cur:
                    continue
                G(proj, r, "push", "-q", "--force-with-lease=%s:%s" % (rel, cur), "origin", "%s:refs/heads/%s" % (full, rel),
                  timeout=300)
                G(proj, r, "fetch", "origin", rel, timeout=300)
                changed.append("%s → %s" % (r.get("name", r["id"]), full[:7]))
        except RuntimeError as e:
            raise ApiError(502, "되돌리기 실패: %s" % e)
        if not changed:
            raise ApiError(409, "운영이 이미 그 버전입니다")
        _record_release(proj, {"ts": now(), "by": who, "n": 0, "msgs": changed, "rollback": True, "before": before,
                               "heads": _heads(proj)})
    notify("[%s] 운영을 이전 버전으로 되돌렸습니다 (%s) - 1분 안에 운영 서버에 배포됩니다.\n"
           "테스트 브랜치에는 문제의 변경이 남아 있으니, 고친 뒤 다시 운영 반영하세요." % (proj["name"], ", ".join(changed)))
    return repo_status(proj)


def repo_save(proj, b):
    """저장소 하나를 추가하거나 고친다. b['id'] 가 없으면 새 저장소."""
    if any(j["status"] in ("queued", "running", "deploying") for (pid, _), j in JOBS.items() if pid == proj["id"]):
        raise ApiError(409, "진행 중인 작업이 끝난 뒤 바꿔주세요")
    repos = proj.setdefault("repos", [])
    rid = str(b.get("id") or "").strip()
    url = str(b.get("url") or "").strip()
    if b.get("remove"):
        proj["repos"] = [r for r in repos if r.get("id") != rid]
        save_cfg()
        refresh_agent_settings(proj)
        return repo_status(proj)
    if not REPO_URL_RE.match(url):
        raise ApiError(400, "저장소 주소 형식이 올바르지 않습니다 (예: git@github.com:아이디/저장소.git)")
    if not rid:
        n = 1
        while any(r.get("id") == "r%d" % n for r in repos):
            n += 1
        rid = "r%d" % n
    if not RID_RE.match(rid):
        raise ApiError(400, "저장소 id가 올바르지 않습니다")
    path = str(b.get("path") or "").strip() or str(BASE / "repos" / ("%s_%s" % (proj["id"], rid)))
    if not REPO_PATH_RE.match(path) or ".." in path:
        raise ApiError(400, "로컬 폴더 경로는 /로 시작하는 절대 경로여야 합니다")
    if Path(path).resolve() in (BASE.resolve(), Path.home().resolve()):
        raise ApiError(400, "작업 폴더 전체가 아니라 저장소 전용 폴더를 지정하세요")
    if any(r.get("id") != rid and Path(r.get("path", "")).resolve() == Path(path).resolve() for r in repos):
        raise ApiError(400, "다른 저장소와 같은 폴더입니다")
    branch = str(b.get("branch") or "main").strip()
    if not BRANCH_RE.match(branch) or ".." in branch:
        raise ApiError(400, "브랜치 이름이 올바르지 않습니다")
    mode = b.get("merge") if b.get("merge") in ("merge", "branch") else "merge"
    release = str(b.get("release") or "").strip()
    if release and (not BRANCH_RE.match(release) or ".." in release):
        raise ApiError(400, "운영 브랜치 이름이 올바르지 않습니다")
    if release and release == branch:
        raise ApiError(400, "테스트 브랜치와 운영 브랜치는 달라야 합니다 (예: develop / main)")
    test_url = str(b.get("test_url") or "").strip()[:200]
    if test_url and not re.match(r"^https?://[\w.:\-]+(/[\w./\-]*)?$", test_url):
        raise ApiError(400, "테스트 서버 주소 형식이 올바르지 않습니다 (예: http://192.168.0.16:38080)")
    name = re.sub(r"\s+", " ", str(b.get("name") or "")).strip()[:20] or rid
    new = {"id": rid, "name": name, "url": url, "path": path, "branch": branch, "merge": mode, "release": release,
           "test_url": test_url, "build": str(b.get("build") or "").strip()[:500], "deploy": str(b.get("deploy") or "").strip()[:500]}
    for r in repos:
        if r.get("id") == rid:
            if r.get("key"):
                new["key"] = r["key"]
            r.clear()
            r.update(new)
            break
    else:
        repos.append(new)
    save_cfg()
    refresh_agent_settings(proj)
    return repo_status(proj)


def repo_clone(proj, rid):
    r = repo_by(proj, rid)
    d, url = Path(r["path"]), r["url"]
    with repo_lock(proj["id"]):
        try:
            if (d / ".git").is_dir():
                G(proj, r, "remote", "set-url", "origin", url)
                G(proj, r, "fetch", "origin", timeout=300)
                msg = "%s: 최신 내용을 가져왔습니다" % r.get("name", rid)
            else:
                if d.exists() and any(d.iterdir()):
                    raise ApiError(409, "폴더가 비어 있지 않습니다: %s" % d)
                d.parent.mkdir(parents=True, exist_ok=True)
                git(d.parent, "clone", url, str(d), timeout=600, key=rkey(proj, r))
                msg = "%s: 저장소를 내려받았습니다" % r.get("name", rid)
            rel, base = r.get("release"), rbase(r)
            if rel:
                G(proj, r, "rev-parse", "--verify", "origin/" + rel)
                if G(proj, r, "rev-parse", "--verify", "--quiet", "origin/" + base, check=False).returncode:
                    # 테스트 브랜치가 아직 없으면 운영 브랜치에서 만들어 올린다
                    G(proj, r, "push", "-q", "origin", "refs/remotes/origin/%s:refs/heads/%s" % (rel, base), timeout=300)
                    G(proj, r, "fetch", "origin", timeout=300)
                    msg += " · 운영(%s)에서 테스트 브랜치 %s를 만들었습니다" % (rel, base)
            G(proj, r, "rev-parse", "--verify", "origin/" + base)
        except RuntimeError as e:
            raise ApiError(502, "%s\n(GitHub에 배포 키를 등록했는지, 쓰기 권한을 켰는지 확인하세요)" % e)
    refresh_agent_settings(proj)
    return dict(repo_status(proj), msg=msg)


def repo_key(proj, rid):
    k = rkey(proj, repo_by(proj, rid))
    if not k.exists():
        k.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
        subprocess.run(["ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-C", "agent-harness-%s-%s" % (proj["id"], rid),
                        "-f", str(k)], check=True, capture_output=True, timeout=30)
    return {"key": k.with_suffix(".pub").read_text().strip()}


def repo_prepare(job, proj):
    """작업마다 저장소별로 기준 브랜치에서 harness/<작업ID> 브랜치를 만든다. 다시 작업할 때는 이어서 쓴다."""
    br = job_branch(job["id"])
    fresh = job.get("fresh_branch")
    for r in repos_of(proj):
        name, base = r.get("name", r["id"]), rbase(r)
        if not (Path(r["path"]) / ".git").is_dir():
            raise RuntimeError("%s 저장소를 아직 내려받지 않았습니다. 설정 > 코드 저장소에서 '내려받기'를 누르세요" % name)
        G(proj, r, "fetch", "origin", base, timeout=300)
        G(proj, r, "reset", "--hard", "-q")
        G(proj, r, "clean", "-fdq")
        if fresh:
            G(proj, r, "checkout", "-q", "--detach", "origin/" + base)
            G(proj, r, "branch", "-D", br, check=False)
        if G(proj, r, "rev-parse", "--verify", "--quiet", "refs/heads/" + br, check=False).returncode == 0:
            G(proj, r, "checkout", "-q", br)
            if G(proj, r, "rebase", "-q", "origin/" + base, check=False).returncode:
                G(proj, r, "rebase", "--abort", check=False)
                G(proj, r, "checkout", "-q", "-B", br, "origin/" + base)
                event(job, "system", "%s: %s 이 그사이 바뀌어 충돌이 나서, 최신 %s 기준으로 새로 작업합니다" % (name, base, base), "warn")
        else:
            G(proj, r, "checkout", "-q", "-B", br, "origin/" + base)
    if fresh:
        set_state(job, fresh_branch=False)
        event(job, "system", "요청이 바뀌어 예전 코드 변경은 버리고 테스트 브랜치 기준으로 새로 시작")
    names = ", ".join(r.get("name", r["id"]) for r in repos_of(proj))
    event(job, "system", "저장소 준비: %s (작업 브랜치 %s)" % (names, br))
    set_state(job, branch=br)


def repo_files(proj, r, limit=250):
    try:
        names = G(proj, r, "ls-files").splitlines()
    except RuntimeError:
        return ""
    head = names[:limit]
    more = "\n... 외 %d개 (필요하면 Glob으로 찾는다)" % (len(names) - limit) if len(names) > limit else ""
    return "\n".join(head) + more


def repo_block(proj, jid, kind):
    rs = repos_of(proj)
    if not rs:
        return ""
    if kind == "work":
        multi = len(rs) > 1
        head = ("[코드 저장소] %s\n"
                "이 저장소의 파일을 Edit/Write로 직접 수정해 요청을 구현한다. git(커밋·푸시·브랜치)과 빌드는 하네스가 "
                "처리하므로 하지 않는다. 아래 파일 목록을 보고 필요한 파일만 Grep/Glob/Read로 확인하고, 관련 없는 파일은 "
                "열지 않는다. 변경은 요청 범위로 최소화하고 기존 코드 스타일을 따른다.\n"
                % ("저장소가 %d개다. 요청을 처리하는 데 필요한 저장소만 고친다(예: 화면만 바뀌면 프론트만). "
                   "한쪽을 바꾸면 다른 쪽과 맞물리는 부분(API 주소·요청/응답 필드 이름 등)이 서로 맞는지 확인한다." % len(rs)
                   if multi else ""))
        body = "".join("\n[저장소: %s] 경로: %s (작업 브랜치 %s, 기준 %s)\n[파일 목록]\n%s\n"
                       % (r.get("name", r["id"]), r["path"], job_branch(jid), rbase(r), repo_files(proj, r)) for r in rs)
        return head + "출력 파일에는 변경 요약만 적는다: 저장소별로 바꾼 파일, 무엇을 왜 바꿨는지, 사용자가 확인할 점.\n" + body
    paths = ", ".join("%s(%s)" % (r.get("name", r["id"]), r["path"]) for r in rs)
    return ("[코드 저장소] %s\n변경 내용(diff): %s\n이 diff를 기준으로 검토하고, 필요할 때만 저장소 파일을 읽어 "
            "확인한다. 저장소 파일은 절대 수정하지 않는다.\n" % (paths, rel(proj, "diff", jid)))


def run_shell(job, proj, r, cmd, what):
    d = proj_dirs(proj)
    d["logs"].mkdir(parents=True, exist_ok=True)
    log = d["logs"] / ("%s_%s_%s_%s.log" % (job["id"], what, r["id"], time.strftime("%H%M%S")))
    key = (proj["id"], job["id"])
    with open(log, "wb") as lf:
        p = subprocess.Popen(["bash", "-lc", cmd], cwd=str(r["path"]), env=git_env(rkey(proj, r)), stdout=lf,
                             stderr=subprocess.STDOUT, start_new_session=True)
        PROCS[key] = p
        try:
            rc = p.wait(timeout=BUILD_TIMEOUT)
        except subprocess.TimeoutExpired:
            kill_proc(p)
            rc = -1
        finally:
            PROCS.pop(key, None)
    if job.get("cancel"):
        raise Cancelled()
    return rc == 0, (read_text(log) or "")[-3000:]


def r_changed(proj, r):
    return bool(G(proj, r, "status", "--porcelain").strip())


def repo_after_work(job, proj, stages, st):
    """작업 단계가 끝나면: 바뀐 저장소만 빌드 확인(실패 시 오류를 돌려줘 자동 수정) → 커밋 → diff 저장."""
    jid = job["id"]
    tries = 0
    while True:
        changed = [r for r in repos_of(proj) if r_changed(proj, r)]
        if not changed:
            event(job, "system", "%s: 저장소에 바뀐 파일이 없습니다" % st["name"], "warn")
            write_diff(proj, jid)
            return
        failed = None
        for r in changed:
            cmd = r.get("build")
            if not cmd:
                continue
            event(job, "system", "빌드 확인 (%s): %s" % (r.get("name", r["id"]), cmd))
            ok, tail = run_shell(job, proj, r, cmd, "build")
            if not ok:
                failed = (r, cmd, tail)
                break
            event(job, "system", "빌드 통과 (%s)" % r.get("name", r["id"]), "ok")
        if not failed:
            break
        r, cmd, tail = failed
        if tries >= BUILD_FIX_TRIES:
            raise RuntimeError("%s 빌드 실패 (자동 수정 %d회 후에도 실패)\n%s" % (r.get("name", r["id"]), tries, tail[-800:]))
        tries += 1
        event(job, "system", "%s 빌드 실패 - 오류 내용을 %s 단계로 돌려보내 자동 수정 (%d/%d)"
              % (r.get("name", r["id"]), st["name"], tries, BUILD_FIX_TRIES), "warn")
        fb = ("%s 저장소(%s)의 빌드 명령 `%s` 이 실패했다. 아래 오류의 원인을 찾아 코드를 고친다. 요청과 관계없는 부분은 "
              "건드리지 않는다.\n```\n%s\n```" % (r.get("name", r["id"]), r["path"], cmd, tail[-2500:]))
        run_step(job, proj, st, prompt_work(proj, stages, st, jid, fb))
    title = re.sub(r"\s+", " ", job["title"])[:60]
    if job.get("followups") and job.get("feedback"):
        title = "%s (추가 요청 %d: %s)" % (title[:40], job["followups"], re.sub(r"\s+", " ", job["feedback"])[:50])
    done = []
    for r in changed:
        G(proj, r, "add", "-A")
        G(proj, r, "commit", "-q", "-m", "%s\n\nagent-harness 작업 %s · %s 단계" % (title, jid, st["name"]))
        done.append("%s %s" % (r.get("name", r["id"]), G(proj, r, "log", "-1", "--format=%h").strip()))
    write_diff(proj, jid)
    event(job, "system", "커밋 완료: %s" % ", ".join(done), "ok")


def write_diff(proj, jid, limit=40000):
    parts, rs = [], repos_of(proj)
    each = limit // max(1, len(rs))
    for r in rs:
        base = "origin/" + rbase(r)
        stat = G(proj, r, "diff", "--stat", base + "...HEAD")
        if not stat.strip():
            continue
        diff = G(proj, r, "diff", base + "...HEAD")
        cut = "\n... (diff가 길어 %d자에서 잘림)" % each if len(diff) > each else ""
        title = "# %s 저장소\n\n" % r.get("name", r["id"]) if len(rs) > 1 else ""
        parts.append("%s## 변경 파일\n```\n%s```\n\n## 변경 내용\n```diff\n%s%s\n```\n" % (title, stat, diff[:each], cut))
    f = fpath(proj, "diff", jid)
    if parts:
        f.write_text("\n".join(parts))
    elif f.exists():
        f.unlink()


def repo_discard(proj):
    """검토 단계에서 에이전트가 실수로 고친 파일은 되돌린다(커밋된 작업 결과만 남긴다)."""
    hit = False
    for r in repos_of(proj):
        if r_changed(proj, r):
            G(proj, r, "reset", "--hard", "-q")
            G(proj, r, "clean", "-fdq")
            hit = True
    return hit


def repo_deliver(proj, j, summary_src):
    """최종 승인 후: 바뀐 저장소마다 기준 브랜치에 병합해 푸시(또는 작업 브랜치만 푸시) → 배포 명령 실행."""
    jid, br = j["id"], job_branch(j["id"])
    lines, merges = [], job_merges(j)
    multi = len(repos_of(proj)) > 1
    try:
        with repo_lock(proj["id"]):
            todo = []
            for r in repos_of(proj):
                base = rbase(r)
                G(proj, r, "fetch", "origin", base, timeout=300)
                G(proj, r, "reset", "--hard", "-q")
                if G(proj, r, "rev-parse", "--verify", "--quiet", "refs/heads/" + br, check=False).returncode:
                    continue
                G(proj, r, "checkout", "-q", br)
                ahead = int(G(proj, r, "rev-list", "--count", "origin/%s..%s" % (base, br)).strip() or 0)
                if ahead:
                    todo.append((r, ahead))
            if not todo:
                lines.append("- 바뀐 코드가 없어 저장소에는 반영하지 않았습니다")
                if repo_release(proj) and not merges:
                    set_state(j, release_state="none")
            # 먼저 모든 저장소에서 병합이 되는지 확인한 뒤 푸시한다(한쪽만 올라가는 일을 줄인다)
            for r, ahead in todo:
                if r.get("merge", "merge") == "branch":
                    continue
                base = rbase(r)
                G(proj, r, "checkout", "-q", "-B", base, "origin/" + base)
                res = G(proj, r, "merge", "--no-ff", "-m", "Merge %s: %s" % (br, j["title"][:60]), br, check=False)
                if res.returncode:
                    G(proj, r, "merge", "--abort", check=False)
                    G(proj, r, "checkout", "-q", br)
                    raise RuntimeError("%s: %s 에 그사이 다른 변경이 있어 자동 병합 중 충돌이 났습니다. "
                                       "반려하고 다시 작업하면 최신 %s 기준으로 다시 맞춥니다" % (r.get("name", r["id"]), base, base))
            for r, ahead in todo:
                name, base, web = r.get("name", r["id"]), rbase(r), web_url(r.get("url"))
                pre = "**%s**: " % name if multi else ""
                if r.get("merge", "merge") == "branch":
                    G(proj, r, "push", "-q", "-f", "origin", "%s:%s" % (br, br), timeout=300)
                    lines.append("- %s`%s` 브랜치로 푸시했습니다 (커밋 %d개)" % (pre, br, ahead))
                    if web:
                        lines.append("- PR 만들기: %s/compare/%s...%s?expand=1" % (web, base, br))
                    continue
                G(proj, r, "push", "-q", "origin", "%s:%s" % (base, base), timeout=300)
                sha = G(proj, r, "log", "-1", "--format=%h").strip()
                if r.get("release"):
                    merges[r["id"]] = G(proj, r, "rev-parse", "HEAD").strip()
                    set_state(j, merges=dict(merges), merge_sha="", release_state="pending", approved_at=now())
                lines.append("- %s`%s`에 병합하고 푸시했습니다 (커밋 %s, 변경 커밋 %d개)" % (pre, base, sha, ahead))
                if web:
                    lines.append("  - 커밋: %s/commit/%s" % (web, sha))
                dep = r.get("deploy")
                if dep:
                    event(j, "system", "배포 명령 실행 (%s): %s" % (name, dep))
                    ok, tail = run_shell(j, proj, r, dep, "deploy")
                    lines.append("  - 배포 명령 %s" % ("성공" if ok else "실패"))
                    if not ok:
                        lines.append("```\n%s\n```" % tail[-1500:])
                        event(j, "system", "배포 명령 실패 (%s, 코드는 이미 푸시됨)" % name, "err")
            if any(r.get("release") for r, _ in todo):
                tu = repo_test_url(proj)
                lines.append("- **테스트 서버**%s에 1~3분 안에 배포됩니다. 확인한 뒤 이 작업 화면의 '운영 반영'을 누르면 운영으로 올라갑니다"
                             % (" (%s)" % tu if tu else ""))
    except Exception as e:  # noqa: BLE001
        set_state(j, status="awaiting_user", error="저장소 반영 실패: %s" % e)
        event(j, "system", "저장소 반영 실패: %s" % e, "err")
        notify("[%s] %s\n저장소 반영 실패: %s" % (proj["name"], j["title"], str(e)[:300]),
               [[("다시 승인", "ap:%s:%s" % (proj["id"], jid))]], j.get("chat") or None)
        return
    body = (read_text(summary_src) or "").rstrip()
    fpath(proj, "approved", jid).write_text(body + "\n\n## 저장소 반영\n" + "\n".join(lines) + "\n")
    set_state(j, status="approved", error="")
    event(j, "user", "최종 승인 · 저장소 반영 완료", "ok")
    notify_job(j, "approved")



def repo_revert(proj, j):
    """승인해 테스트 서버(기준 브랜치)에 올라간 작업을 되돌린다. 운영에는 아직 안 올라간 작업만.
    이 작업의 병합 커밋(이어서 수정한 것 포함)을 최신 것부터 git revert 해서 푸시한다(강제 푸시 없음)."""
    jid, br = j["id"], job_branch(j["id"])
    done, lines = [], []
    with repo_lock(proj["id"]):
        if j.get("status") != "approved" or j.get("release_state") != "pending" or not job_merges(j):
            raise ApiError(409, "테스트 서버에만 반영되고 아직 운영에 올리지 않은 작업만 되돌릴 수 있습니다")
        try:
            for r in repos_of(proj):
                if r["id"] not in job_merges(j):
                    continue
                base, name = rbase(r), r.get("name", r["id"])
                G(proj, r, "fetch", "origin", base, timeout=300)
                if r.get("release"):
                    G(proj, r, "fetch", "origin", r["release"], timeout=300)
                G(proj, r, "reset", "--hard", "-q")
                G(proj, r, "checkout", "-q", "-B", base, "origin/" + base)
                done.append(r)
                shas = G(proj, r, "log", "origin/" + base, "--merges", "--format=%H",
                         "--grep=^Merge %s:" % br).split()
                gone = set(re.findall(r"This reverts commit ([0-9a-f]{40})", G(proj, r, "log", "origin/" + base,
                           "--format=%b", "--grep=^Revert \"Merge %s:" % br)))
                shas = [x for x in shas if x not in gone]   # 예전에 이미 되돌린 병합은 빼고
                if r.get("release") and any(is_anc(proj, r, x, "origin/" + r["release"]) for x in shas):
                    raise ApiError(409, "%s: 이 작업의 일부가 이미 운영에 올라가 있습니다. 운영 반영 이력에서 먼저 되돌리세요" % name)
                for x in shas:
                    res = G(proj, r, "revert", "-m", "1", "--no-edit", x, check=False)
                    if res.returncode:
                        G(proj, r, "revert", "--abort", check=False)
                        raise ApiError(409, "%s: 이 작업 뒤에 승인된 다른 작업이 같은 부분을 고쳐서 자동으로 되돌릴 수 없습니다. "
                                            "나중 작업을 먼저 되돌리거나, 되돌리는 내용을 새 작업으로 요청하세요" % name)
                lines.append("- %s: 병합 %d건 되돌림" % (name, len(shas)))
            for r in done:   # 모든 저장소에서 되돌리기가 되는 걸 확인한 뒤에 푸시
                base = rbase(r)
                G(proj, r, "push", "-q", "origin", "%s:%s" % (base, base), timeout=300)
                if r.get("deploy"):
                    run_shell(j, proj, r, r["deploy"], "deploy")
        except Exception:
            for r in done:
                G(proj, r, "reset", "--hard", "-q", "origin/" + rbase(r), check=False)
            raise
    set_state(j, status="reverted", release_state="none", merges={}, merge_sha="", reverted_at=now())
    event(j, "user", "테스트 서버에서 되돌림\n" + "\n".join(lines), "warn")
    ap = fpath(proj, "approved", jid)
    if ap.exists():
        ap.write_text((read_text(ap) or "").rstrip() + "\n\n## 되돌림 (%s)\n%s\n- 테스트 서버에 1~3분 안에 이전 상태로 배포됩니다\n"
                      % (now()[:16], "\n".join(lines)))
    return job_summary(j)


def repo_drop_branch(proj, jid):
    with repo_lock(proj["id"]):
        br = job_branch(jid)
        for r in repos_of(proj):
            try:
                if not (Path(r["path"]) / ".git").is_dir():
                    continue
                if G(proj, r, "rev-parse", "--abbrev-ref", "HEAD").strip() == br:
                    G(proj, r, "checkout", "-q", "--detach", "origin/" + rbase(r))
                G(proj, r, "branch", "-D", br, check=False)
            except RuntimeError:
                pass


def merge_projects(b):
    """저장소가 연결된 프로젝트 여러 개를 한 프로젝트로 묶는다. 저장소 폴더·배포 키·에이전트·단계를 그대로 가져오고,
    원래 프로젝트들은 작업 기록만 남기고 저장소 연결을 푼다(같은 폴더를 두 프로젝트가 동시에 쓰지 않게)."""
    ids = [str(x) for x in (b.get("sources") or [])]
    if len(ids) < 2:
        raise ApiError(400, "합칠 프로젝트를 2개 이상 고르세요")
    srcs = [proj_of(i) for i in ids]
    for p in srcs:
        if not repos_of(p):
            raise ApiError(400, "%s 에는 코드 저장소가 연결되어 있지 않습니다" % p["name"])
        if any(j["status"] in ("queued", "running", "deploying") for (pid, _), j in JOBS.items() if pid == p["id"]):
            raise ApiError(409, "%s 에 진행 중인 작업이 있습니다. 끝난 뒤 합치세요" % p["name"])
    names = [p["name"] for p in srcs]
    common = os.path.commonprefix(names).strip()
    name = re.sub(r"\s+", " ", str(b.get("name") or "")).strip()[:40] or common or "합친 프로젝트"
    nums = [int(re.sub(r"\D", "", p["id"]) or 0) for p in CFG["projects"]]
    pid = "p%d" % (max(nums + [0]) + 1)
    proj = {"id": pid, "name": name, "description": (" + ".join(names) + " 저장소를 합친 프로젝트")[:2000],
            "root": "projects/%s" % pid, "agents": [], "stages": [], "max_rounds": 1, "schedules": [],
            "stage_mode": "fixed", "use_sources": "prefer", "created": now()}
    (BASE / proj["root"]).mkdir(parents=True, exist_ok=True)
    ensure_dirs(proj)
    CFG["projects"].append(proj)
    # 에이전트·단계는 첫 프로젝트 것을 그대로 가져온다
    first = srcs[0]
    amap = {}
    for a in first["agents"]:
        amap[a["id"]] = import_agent(proj, first, a)["id"]
    proj["stages"] = [dict(s, agent=amap.get(s.get("agent"), s.get("agent"))) for s in first["stages"]]
    for k in ("max_rounds", "stage_mode", "use_sources"):
        if k in first:
            proj[k] = first[k]
    repos, used = [], set()
    for i, p in enumerate(srcs, 1):
        for r in repos_of(p):
            short = p["name"][len(common):].strip() if common and p["name"].startswith(common) else p["name"]
            short = short or r.get("name") or "저장소%d" % i
            while short in used:
                short += "2"
            used.add(short)
            nr = {k: r.get(k, "") for k in ("url", "path", "branch", "release", "merge", "build", "deploy", "test_url")}
            nr.update(id="r%d" % (len(repos) + 1), name=short[:20], key=str(rkey(p, r)))
            repos.append(nr)
    proj["repos"] = repos
    for p in srcs:
        p["repos"] = []
        p["description"] = ((p.get("description") or "") + " (저장소는 '%s' 프로젝트로 옮겨짐)" % name).strip()
        refresh_agent_settings(p)
    save_cfg()
    refresh_agent_settings(proj)
    return {"id": proj["id"], "name": proj["name"], "repos": [r["name"] for r in repos]}


# ---------------------------------------------------------------- 파이프라인

CONCISE = ("위에 적힌 입력 파일과 참고 자료 외에는 폴더를 탐색하지 않는다. 그런 다음 반드시 Write 도구로 출력 파일 경로에 결과를 저장한다. "
           "파일로 저장하기 전에는 작업이 끝난 것이 아니며, 채팅으로 결과를 답하는 것만으로는 완료되지 않는다. "
           "설명이나 요약을 덧붙이지 말고, 저장을 마친 뒤 한 줄로만 보고하고 종료한다.")
RETRY_SUFFIX = ("\n\n[중요] 방금 전 시도에서 지정된 출력 파일이 저장되지 않았습니다. 이유를 설명하지 말고, "
                "다른 어떤 도구도 쓰지 말고, 지금 바로 Write 도구로 위에 적힌 출력 파일 경로에 저장하세요. "
                "저장하지 않으면 이 작업은 실패로 처리됩니다.")


SRC_NAME = re.compile(r"^[\w가-힣 .()\-]{1,60}$")
SRC_MAX = 50


def src_dir(proj):
    d = proj_dirs(proj)["sources"]
    d.mkdir(parents=True, exist_ok=True)
    return d


def src_path(proj, name):
    name = str(name or "").strip()
    if not SRC_NAME.match(name) or "/" in name or ".." in name:
        raise ApiError(400, "파일 이름에 쓸 수 없는 문자가 있습니다")
    if not name.lower().endswith((".md", ".txt")):
        name += ".md"
    return src_dir(proj) / name


def src_list(proj):
    out = []
    d = proj_dirs(proj)["sources"]
    if d.is_dir():
        for p in sorted(d.iterdir()):
            if p.is_file() and p.suffix.lower() in (".md", ".txt"):
                out.append({"name": p.name, "size": p.stat().st_size,
                            "preview": (read_text(p, 300) or "").strip()[:200]})
    return out


def sources_block(proj):
    """사용자가 직접 넣어둔 자료를 에이전트가 근거로 쓰도록 프롬프트에 붙인다."""
    mode = proj.get("use_sources", "prefer")
    if mode == "off":
        return ""
    items = src_list(proj)
    db = db_block(proj)
    if not items:
        return db
    lines = ["[참고 자료] 사용자가 직접 제공한 자료다. 관련 있는 파일을 읽어 근거로 삼는다."]
    lines += ["- ../shared/sources/%s" % s["name"] for s in items[:SRC_MAX]]
    if mode == "only":
        lines.append("답변은 이 자료에 있는 내용만 근거로 작성한다. 자료에 없는 것은 '제공된 자료에 없음'이라고 밝히고 추측하지 않는다.")
    else:
        lines.append("이 자료를 우선 근거로 삼고, 부족한 부분만 다른 방법으로 보완한다.")
    return "\n".join(lines) + "\n" + db


# ---------------------------------------------------------------- DB 구조 자료 (읽기 전용 계정으로 추출)

DB_AUTO_AT = os.environ.get("DB_EXPORT_AT", "03:40")   # 매일 자동 갱신 시각
DB_RUN = {}            # pid -> True (추출 중)
DB_ROW_MAX = 3000      # 코드 테이블 한 개당 최대 행 수
DB_ROW_SKIP = 20000    # 이보다 큰 테이블은 코드 테이블로 보지 않는다
DB_PREFIX_RE = re.compile(r"^[A-Z][A-Z0-9_]{0,30}$")


def db_cfg(proj):
    return proj.get("db") or {}


def db_dir(proj):
    return proj_dirs(proj)["sources"] / "db"


def db_conn(proj):
    pre = db_cfg(proj).get("prefix") or ""
    if not DB_PREFIX_RE.match(pre):
        return None, []
    keys = ["HOST", "PORT", "USER", "PASSWORD", "NAME"]
    c = {k.lower(): os.environ.get("%s_%s" % (pre, k), "") for k in keys}
    missing = ["%s_%s" % (pre, k) for k in keys if not c[k.lower()] and k != "PORT"]
    return c, missing


def _db_unesc(v):
    if v == "NULL":
        return None
    return re.sub(r"\\(.)", lambda m: {"n": "\n", "t": "\t", "0": "\0", "\\": "\\"}.get(m[1], m[1]), v)


def db_query(c, sql, header=False, timeout=90):
    exe = shutil.which("mariadb") or shutil.which("mysql")
    if not exe:
        raise RuntimeError("파이에 mariadb 클라이언트가 없습니다 (sudo apt install mariadb-client)")
    cmd = [exe, "-h", c["host"], "-P", c["port"] or "3306", "-u", c["user"], c["name"],
           "--batch", "--connect-timeout=10", "--default-character-set=utf8mb4", "-e", "SET SESSION group_concat_max_len=4000000; " + sql]
    if not header:
        cmd.insert(-2, "-N")
    env = dict(os.environ, MYSQL_PWD=c["password"])   # 비밀번호는 명령줄에 남기지 않는다
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, env=env)
    if r.returncode != 0:
        err = "\n".join(x for x in r.stderr.splitlines() if not x.startswith("WARNING"))
        raise RuntimeError((err or "DB 조회 실패").strip()[:300])
    rows = [[_db_unesc(v) for v in ln.split("\t")] for ln in r.stdout.split("\n") if ln != ""]
    return rows


def _md(v):
    return ("" if v is None else str(v)).replace("|", "\\|").replace("\n", " ").replace("\t", " ").strip()


def _fname(n):
    return re.sub(r"[^\w가-힣.\-]", "_", n)[:80]


def db_export(proj):
    c, missing = db_conn(proj)
    if c is None:
        raise RuntimeError("환경 변수 이름(접두어)을 먼저 설정하세요")
    if missing:
        raise RuntimeError("파이 .env에 없음: " + ", ".join(missing))
    cfg = db_cfg(proj)
    pats = [x.strip() for x in str(cfg.get("code_tables") or "CM*").split(",") if x.strip()]
    tabs = db_query(c, "SELECT TABLE_NAME, TABLE_TYPE, TABLE_ROWS, TABLE_COMMENT FROM information_schema.TABLES "
                       "WHERE TABLE_SCHEMA=database() ORDER BY TABLE_NAME")
    cols = db_query(c, "SELECT TABLE_NAME, COLUMN_NAME, COLUMN_TYPE, IS_NULLABLE, COLUMN_KEY, COLUMN_DEFAULT, EXTRA, "
                       "COLUMN_COMMENT FROM information_schema.COLUMNS WHERE TABLE_SCHEMA=database() "
                       "ORDER BY TABLE_NAME, ORDINAL_POSITION")
    idx = db_query(c, "SELECT TABLE_NAME, INDEX_NAME, NON_UNIQUE, GROUP_CONCAT(COLUMN_NAME ORDER BY SEQ_IN_INDEX) "
                      "FROM information_schema.STATISTICS WHERE TABLE_SCHEMA=database() "
                      "GROUP BY TABLE_NAME, INDEX_NAME, NON_UNIQUE ORDER BY TABLE_NAME, INDEX_NAME")
    fks = db_query(c, "SELECT TABLE_NAME, COLUMN_NAME, REFERENCED_TABLE_NAME, REFERENCED_COLUMN_NAME "
                      "FROM information_schema.KEY_COLUMN_USAGE WHERE TABLE_SCHEMA=database() "
                      "AND REFERENCED_TABLE_NAME IS NOT NULL")
    rts = db_query(c, "SELECT ROUTINE_NAME, ROUTINE_TYPE, ROUTINE_DEFINITION, ROUTINE_COMMENT, DTD_IDENTIFIER "
                      "FROM information_schema.ROUTINES WHERE ROUTINE_SCHEMA=database() ORDER BY ROUTINE_NAME")
    prm = db_query(c, "SELECT SPECIFIC_NAME, GROUP_CONCAT(CONCAT_WS(' ', PARAMETER_MODE, PARAMETER_NAME, DTD_IDENTIFIER) "
                      "ORDER BY ORDINAL_POSITION SEPARATOR ', ') FROM information_schema.PARAMETERS "
                      "WHERE SPECIFIC_SCHEMA=database() AND ORDINAL_POSITION>0 GROUP BY SPECIFIC_NAME")
    vws = db_query(c, "SELECT TABLE_NAME, VIEW_DEFINITION FROM information_schema.VIEWS "
                      "WHERE TABLE_SCHEMA=database() ORDER BY TABLE_NAME")
    trg = db_query(c, "SELECT TRIGGER_NAME, ACTION_TIMING, EVENT_MANIPULATION, EVENT_OBJECT_TABLE, ACTION_STATEMENT "
                      "FROM information_schema.TRIGGERS WHERE TRIGGER_SCHEMA=database() ORDER BY TRIGGER_NAME")
    if any(r[2] is None for r in rts):
        raise RuntimeError("프로시저 내용을 볼 권한이 없습니다 (GRANT SHOW CREATE ROUTINE 필요)")

    out = db_dir(proj)
    tmp = out.with_name("db.tmp")
    shutil.rmtree(tmp, ignore_errors=True)
    for d in ("tables", "routines", "views", "codes"):
        (tmp / d).mkdir(parents=True)
    bycol, byidx, byfk = {}, {}, {}
    for r in cols:
        bycol.setdefault(r[0], []).append(r)
    for r in idx:
        byidx.setdefault(r[0], []).append(r)
    for r in fks:
        byfk.setdefault(r[0], []).append(r)
    params = {r[0]: r[1] for r in prm}
    stamp = now()

    base_tabs = [t for t in tabs if t[1] != "VIEW"]
    for t in base_tabs:
        name = t[0]
        L = ["# %s" % name, "", "설명: %s · 대략 행 수: %s" % (_md(t[3]) or "-", t[2] or "0"), "",
             "| 컬럼 | 타입 | NULL | 키 | 기본값 | 기타 | 설명 |", "|---|---|---|---|---|---|---|"]
        L += ["| %s |" % " | ".join(_md(x) for x in r[1:]) for r in bycol.get(name, [])]
        if byidx.get(name):
            L += ["", "## 인덱스", ""] + ["- %s%s: %s" % (r[1], "" if r[2] == "1" else " (UNIQUE)", r[3])
                                         for r in byidx[name]]
        if byfk.get(name):
            L += ["", "## 참조 (FK)", ""] + ["- %s → %s.%s" % (r[1], r[2], r[3]) for r in byfk[name]]
        rel = [x for x in trg if x[3] == name]
        if rel:
            L += ["", "## 트리거", ""] + ["- %s (%s %s) → triggers 항목 참고" % (x[0], x[1], x[2]) for x in rel]
        (tmp / "tables" / (_fname(name) + ".md")).write_text("\n".join(L) + "\n")
    for r in rts:
        head = "-- %s %s(%s)%s\n" % (r[1], r[0], params.get(r[0], ""), (" RETURNS " + r[4]) if r[1] == "FUNCTION" and r[4] else "")
        if r[3]:
            head += "-- 설명: %s\n" % _md(r[3])
        (tmp / "routines" / (_fname(r[0]) + ".sql")).write_text(head + (r[2] or "") + "\n")
    for r in vws:
        (tmp / "views" / (_fname(r[0]) + ".sql")).write_text("-- VIEW %s\n%s\n" % (r[0], r[1] or ""))
    if trg:
        (tmp / "triggers.sql").write_text("\n\n".join("-- TRIGGER %s %s %s ON %s\n%s" % (x[0], x[1], x[2], x[3], x[4] or "")
                                                     for x in trg) + "\n")
    codes = []
    for t in base_tabs:
        if not any(fnmatch.fnmatchcase(t[0], p) for p in pats) or int(t[2] or 0) > DB_ROW_SKIP:
            continue
        rows = db_query(c, "SELECT * FROM `%s` LIMIT %d" % (t[0].replace("`", ""), DB_ROW_MAX + 1), header=True)
        if not rows:
            continue
        hdr, data = rows[0], rows[1:]
        L = ["# %s 데이터 (%s 기준%s)" % (t[0], stamp, ", 앞 %d행만" % DB_ROW_MAX if len(data) > DB_ROW_MAX else ""),
             "", "| %s |" % " | ".join(_md(h) for h in hdr), "|%s" % ("---|" * len(hdr))]
        L += ["| %s |" % " | ".join(_md(v) for v in r) for r in data[:DB_ROW_MAX]]
        (tmp / "codes" / (_fname(t[0]) + ".md")).write_text("\n".join(L) + "\n")
        codes.append((t[0], len(data[:DB_ROW_MAX])))

    R = ["# DB 구조 목차 (%s)" % c["name"], "",
         "%s 기준, 운영 DB에서 읽기 전용 계정으로 자동 추출한 자료다. 이 목차에서 필요한 항목만 골라 해당 파일을 읽는다." % stamp,
         "", "- 테이블: tables/<이름>.md (컬럼·인덱스·FK)",
         "- 프로시저·함수: routines/<이름>.sql", "- 뷰: views/<이름>.sql",
         "- 코드 테이블 실제 값: codes/<이름>.md" + (" · 트리거: triggers.sql" if trg else ""), "",
         "## 테이블 (%d)" % len(base_tabs), "", "| 테이블 | 대략 행 수 | 컬럼 수 | 설명 |", "|---|---|---|---|"]
    R += ["| %s | %s | %d | %s |" % (t[0], t[2] or "0", len(bycol.get(t[0], [])), _md(t[3])) for t in base_tabs]
    R += ["", "## 프로시저·함수 (%d)" % len(rts), ""]
    R += ["- %s%s(%s)%s" % ("" if r[1] == "PROCEDURE" else "[함수] ", r[0], params.get(r[0], ""),
                            (" — " + _md(r[3])) if r[3] else "") for r in rts]
    R += ["", "## 뷰 (%d)" % len(vws), ""] + ["- %s" % r[0] for r in vws]
    R += ["", "## 코드 테이블 데이터 (%d)" % len(codes), ""] + ["- %s: %d행" % x for x in codes]
    (tmp / "README.md").write_text("\n".join(R) + "\n")

    old = out.with_name("db.old")
    shutil.rmtree(old, ignore_errors=True)
    if out.exists():
        out.rename(old)
    tmp.rename(out)
    shutil.rmtree(old, ignore_errors=True)
    return {"tables": len(base_tabs), "routines": len(rts), "views": len(vws), "codes": len(codes), "triggers": len(trg)}


def db_refresh(proj, who="수동"):
    pid = proj["id"]
    with LOCK:
        if DB_RUN.get(pid):
            raise ApiError(409, "이미 DB 구조를 가져오는 중입니다")
        DB_RUN[pid] = True
    try:
        try:
            counts = db_export(proj)
            last = {"at": now(), "ok": True, "who": who, "counts": counts,
                    "msg": "테이블 %(tables)d · 프로시저 %(routines)d · 뷰 %(views)d · 코드 테이블 %(codes)d" % counts}
            if not counts["routines"]:
                last["msg"] += " (프로시저가 0개면 계정에 SHOW CREATE ROUTINE 권한이 있는지 확인)"
        except Exception as e:  # noqa: BLE001
            shutil.rmtree(db_dir(proj).with_name("db.tmp"), ignore_errors=True)
            last = {"at": now(), "ok": False, "who": who, "msg": str(e)[:300]}
            notify("[%s] DB 구조 자료 갱신 실패: %s" % (proj["name"], last["msg"]))
        with LOCK:
            proj.setdefault("db", {})["last"] = last
            save_cfg()
        return last
    finally:
        DB_RUN.pop(pid, None)


def db_status(proj):
    cfg = db_cfg(proj)
    c, missing = db_conn(proj)
    readme = db_dir(proj) / "README.md"
    return {"prefix": cfg.get("prefix", ""), "code_tables": cfg.get("code_tables", "CM*"),
            "auto": bool(cfg.get("auto", True)), "last": cfg.get("last"), "running": bool(DB_RUN.get(proj["id"])),
            "ready": c is not None and not missing, "missing": missing,
            "target": ("%s:%s / %s (%s)" % (c["host"], c["port"] or "3306", c["name"], c["user"])) if c and not missing else "",
            "has": readme.exists()}


def db_block(proj):
    """DB 구조 자료가 있으면 에이전트에게 목차부터 보게 한다."""
    if proj.get("use_sources", "prefer") == "off" or not (db_dir(proj) / "README.md").exists():
        return ""
    at = (db_cfg(proj).get("last") or {}).get("at", "")
    return ("[DB 구조] 운영 DB의 실제 구조(테이블·컬럼·프로시저·뷰·코드값)를 %s 기준으로 뽑아 둔 자료가 "
            "../shared/sources/db/ 에 있다. DB 관련 판단이 필요하면 먼저 ../shared/sources/db/README.md 목차를 보고, "
            "필요한 테이블·프로시저 파일만 골라 읽는다. 전부 읽지 않는다. DB에 직접 접속하지 않는다.\n" % (at or "최근"))


def feedback_block(fb):
    fb = (fb or "").strip()[:2000]
    if not fb:
        return ""
    return ("\n[수정 요청 - 반드시 반영할 것]\n%s\n기존 결과 파일이 있으면 먼저 읽고, 같은 경로에 덮어써서 수정본을 저장한다.\n" % fb)


def inputs_block(proj, stages, stage, jid):
    lines = ["요청 파일: %s" % rel(proj, "request", jid)]
    ab = att_block(proj, jid)
    if ab:
        lines.append(ab.rstrip())
    by_id = {s["id"]: s for s in stages}
    for i in stage.get("inputs", []):
        if i in by_id:
            lines.append("%s: %s" % (by_id[i]["name"], rel(proj, i, jid)))
    return "\n".join(lines)


CLARIFY_RULE = (
    "요청이 모호하거나, 범위·분량·대상·날짜처럼 결과를 크게 좌우할 정보가 빠져 있어 추측하면 엉뚱한 결과가 나올 수 있을 때만 "
    "그렇게 한다: 멋대로 추측해서 진행하지 말고, 출력 파일 첫 줄에 정확히 `NEEDS_INPUT: <한 줄 질문>` 을 쓰고 "
    "둘째 줄부터 왜 필요한지와 선택지를 짧게 적어 그대로 저장한다. 사소하게 빠진 정보는 합리적으로 판단해 평소대로 작업을 "
    "끝까지 완료한다. NEEDS_INPUT은 정말 진행할 수 없을 때만 쓰는 예외다.\n"
)


def prompt_work(proj, stages, stage, jid, fb):
    return ("STEP: %s\n작업ID: %s\n%s\n%s%s지시: %s\n출력 파일: %s\n%s%s%s"
            % (stage["id"], jid, inputs_block(proj, stages, stage, jid), sources_block(proj), repo_block(proj, jid, "work"),
               stage["instruction"] or "요청을 수행한다.",
               rel(proj, stage["id"], jid), feedback_block(fb), CLARIFY_RULE, CONCISE))


def prompt_review(proj, stages, stage, jid):
    by_id = {s["id"]: s for s in stages}
    tgt = by_id[stage["target"]]
    p = ("STEP: %s\n작업ID: %s\n%s\n%s%s검토 대상(%s): %s\n지시: %s\n검수 결과 파일: %s\n"
         "형식: 첫 줄은 정확히 `VERDICT: APPROVE` 또는 `VERDICT: REVISE` 한 줄만 쓴다. 둘째 줄부터 이유를 적고, "
         "REVISE이면 대상 단계에 줄 구체적인 수정 요청을 적는다.\n"
         % (stage["id"], jid, inputs_block(proj, stages, stage, jid), sources_block(proj),
            repo_block(proj, jid, "review") if fpath(proj, "diff", jid).exists() else "",
            tgt["name"], rel(proj, tgt["id"], jid),
            stage["instruction"] or "검토 대상이 요청에 맞는지 판단한다.", rel(proj, stage["id"], jid)))
    if stage.get("polish"):
        p += ("VERDICT가 APPROVE일 때만 오탈자와 문장을 다듬은 최종본을 %s 에 저장하고 맨 아래에 '검수 메모'로 "
              "고친 내용을 짧게 적는다. REVISE이면 최종본은 만들지 않는다.\n" % rel(proj, "final", jid))
    return p + "검토 대상 외 다른 파일은 수정하지 않는다. " + CONCISE


def read_question(proj, stage, jid):
    t = read_text(fpath(proj, stage["id"], jid), 4000) or ""
    m = re.match(r"^\s*NEEDS_INPUT:\s*(.+)", t, re.S)
    return m.group(1).strip() if m else None


def verdict(proj, stage, jid):
    text = read_text(fpath(proj, stage["id"], jid)) or ""
    m = re.search(r"VERDICT:\s*(APPROVE|REVISE)", text[:600], re.I)
    return (m.group(1).upper() if m else "REVISE"), text


def pipeline(job, start):
    proj = proj_of(job["pid"])
    jid = job["id"]
    stages = [dict(s) for s in job_stage_src(proj, job)]
    max_rounds = int(proj.get("max_rounds", 1))
    idx = next((i for i, s in enumerate(stages) if s["id"] == start and s["kind"] == "work"), 0)
    pending = {stages[idx]["id"]: job.get("feedback") or ""}
    rounds = {}
    try:
        i = idx
        while i < len(stages):
            st = stages[i]
            who = agent_name(proj, st["agent"])
            if st["kind"] == "work":
                run_step(job, proj, st, prompt_work(proj, stages, st, jid, pending.pop(st["id"], "")))
                q = read_question(proj, st, jid)
                if q:
                    set_state(job, status="awaiting_user", step=st["id"], needs_input=True, question=q)
                    event(job, who, "%s: 질문 - %s" % (st["name"], q.splitlines()[0][:200]), "warn")
                    notify_job(job, "question")
                    return
                if repo_on(proj):
                    repo_after_work(job, proj, stages, st)
                i += 1
                continue
            run_step(job, proj, st, prompt_review(proj, stages, st, jid),
                     remove_kinds=("final",) if st.get("polish") else ())
            if repo_on(proj) and repo_discard(proj):
                event(job, "system", "%s: 검토 중 바뀐 저장소 파일은 되돌렸습니다" % st["name"], "warn")
            v, text = verdict(proj, st, jid)
            if v == "APPROVE":
                event(job, who, "%s: 승인" % st["name"], "ok")
                i += 1
                continue
            r = rounds.get(st["id"], 0)
            tpos = next((k for k, s in enumerate(stages) if s["id"] == st["target"]), None)
            if r >= max_rounds or tpos is None or tpos >= i:
                event(job, who, "%s: 수정요청이 남았지만 반복 한도(%d회)라 다음으로 진행" % (st["name"], max_rounds), "warn")
                i += 1
                continue
            rounds[st["id"]] = r + 1
            pending[stages[tpos]["id"]] = text
            event(job, who, "%s: 수정요청 (%d/%d회) - %s 단계로 돌려보냄" % (st["name"], r + 1, max_rounds,
                                                                      stages[tpos]["name"]), "warn")
            i = tpos
        set_state(job, status="awaiting_user")
        if job.get("auto_approve"):
            event(job, "system", "자동 승인 설정에 따라 바로 승인합니다", "ok")
            with LOCK:
                try:
                    job_approve(proj, job)
                except ApiError as e:
                    set_state(job, status="failed", error=e.msg)
                    event(job, "system", "자동 승인 실패: %s" % e.msg, "err")
        else:
            event(job, "system", "사용자 최종 승인을 기다리는 중", "ok")
            notify_job(job, "awaiting")
    except Cancelled:
        set_state(job, status="cancelled")
        event(job, "system", "중단됨", "warn")
    except Exception as e:  # noqa: BLE001
        set_state(job, status="failed", error=str(e))
        event(job, "system", "실패: %s" % e, "err")
        notify_job(job, "failed")


def worker():
    global RUNNING
    while True:
        pid, jid, start = QUEUE.get()
        job = JOBS.get((pid, jid))
        if not job:
            continue
        with COND:
            while RUNNING >= int(S_()["parallel"]):
                COND.wait(2)
            RUNNING += 1
        try:
            if job.get("cancel"):
                set_state(job, status="cancelled")
                event(job, "system", "대기 중 중단됨", "warn")
            else:
                set_state(job, status="running", error="")
                proj = next((p for p in CFG["projects"] if p["id"] == pid), None)
                if proj and start == "first" and not job.get("stages") and proj.get("stage_mode") == "auto":
                    plan_job(proj, job)
                if proj and repo_on(proj):
                    with repo_lock(pid):   # 같은 저장소를 쓰는 작업은 한 번에 하나씩
                        repo_prepare(job, proj)
                        pipeline(job, start)
                else:
                    pipeline(job, start)
        except Exception as e:  # noqa: BLE001
            set_state(job, status="failed", error=str(e))
            event(job, "system", "실패: %s" % e, "err")
            notify_job(job, "failed")
        finally:
            with COND:
                RUNNING -= 1
                COND.notify_all()
            try:
                flush_trust()
            except Exception:  # noqa: BLE001
                pass


# ---------------------------------------------------------------- AI 단계 추천

def ai_plan(name, desc, want_stages=0, want_agents=0):
    ns = "에이전트 %d개" % want_agents if want_agents else "에이전트 2~4개"
    st = ("단계는 정확히 %d개로 만든다." % want_stages) if want_stages else "단계 2~5개로 꼭 필요한 것만 둔다."
    prompt = (
        "STEP: plan\n너는 멀티 에이전트 파이프라인 설계자다. 아래 프로젝트에 맞는 에이전트와 단계를 설계해 JSON 하나만 출력한다. "
        "설명, 코드블록, 머리말은 쓰지 않는다.\n프로젝트: %s\n설명: %s\n\n규칙:\n"
        "- 토큰을 아끼려면 단계가 적어야 한다. %s. %s\n"
        "- agents:[{\"key\":\"영문소문자\",\"name\":\"한글 이름\",\"role\":\"전문적인 역할 설명 3~5문장. 전문 분야, 접근 방식(어떤 순서·기준으로 "
        "일하는지), 결과물의 판단 기준, 하지 않는 일을 포함한다. '~전문 에이전트다' 한 줄로 끝내지 말 것\",\"web\":true|false,"
        "\"model\":\"haiku|sonnet|\"}]\n"
        "- stages: [{\"name\":\"한글 단계 이름\",\"agent\":\"agents의 key\",\"kind\":\"work|review\",\"target\":\"review일 때 검토할 앞 단계의 name\","
        "\"instruction\":\"이 단계 지시 1~2문장\",\"inputs\":[\"참고할 앞 단계의 name\"],\"polish\":false}]\n"
        "- 첫 단계는 work. review 단계는 앞의 work 단계를 target으로 하며, 마지막 단계는 review로 두고 polish를 true로 한다.\n"
        "- 점검·검수 같은 단순 단계의 에이전트는 model을 haiku로, 글쓰기·추론은 빈 문자열(기본)로 한다. web은 인터넷 자료가 필요한 에이전트만 true.\n"
        "출력 형식: {\"agents\":[...],\"stages\":[...]}") % (name, desc, ns, st)
    if not PLAN_LOCK.acquire(blocking=False):
        raise ApiError(409, "이미 추천을 생성하는 중입니다. 잠시 후 다시 시도하세요")
    try:
        cwd = BASE / ".planner"
        cwd.mkdir(exist_ok=True)
        model = S_().get("planner_model") or ""
        try:
            r = subprocess.run(build_cmd(prompt, model, 3, []), cwd=cwd, env=child_env(), capture_output=True,
                               text=True, timeout=180)
        except subprocess.TimeoutExpired:
            raise ApiError(504, "추천 생성이 시간 초과되었습니다")
        data = parse_result(r.stdout)
        if not data or data.get("is_error"):
            raise ApiError(502, "추천 생성에 실패했습니다: %s" % ((data or {}).get("result") or r.stderr or r.stdout)[:200])
        txt = str(data.get("result") or "")
        a, b = txt.find("{"), txt.rfind("}")
        try:
            plan = norm_plan(json.loads(txt[a:b + 1]), want_stages or 8, want_agents or 6)
        except (ValueError, TypeError) as e:
            raise ApiError(502, "추천 결과를 해석하지 못했습니다(%s). 프리셋을 사용하거나 다시 시도하세요" % e)
        u = data.get("usage") or {}
        return {"plan": plan, "usage": {"input": u.get("input_tokens", 0), "output": u.get("output_tokens", 0),
                                        "cache_write": u.get("cache_creation_input_tokens", 0),
                                        "cache_read": u.get("cache_read_input_tokens", 0),
                                        "cost": data.get("total_cost_usd", 0)}}
    finally:
        PLAN_LOCK.release()


def role_text(md):
    """CLAUDE.md 에서 역할 설명만 남긴다 (제목 줄과 '## 공통 규칙' 이후는 뺀다)."""
    t = re.sub(r"^#[^\n]*\n", "", md or "", count=1)
    return re.split(r"\n##\s", t)[0].strip()


def agent_brief(proj, a):
    ws = proj_dirs(proj)["root"] / a["workspace"]
    role = role_text(read_text(ws / "CLAUDE.md", 1500)).replace("\n", " ")[:200]
    web = parse_perms(ws / ".claude" / "settings.json").get("web")
    return "%s (key=%s)%s: %s" % (a["name"], a["id"], " [웹 가능]" if web else "", role or "(설명 없음)")


def norm_job_stages(proj, raw):
    """요청 1건에 맞춘 단계 설계안을 검증한다. 기존 에이전트만 참조할 수 있고, 모르는 에이전트가 있으면 None(전체 무효)을 돌려준다."""
    if not isinstance(raw, list) or not raw:
        return None
    by_id = {a["id"] for a in proj["agents"]}
    name_to_id = {a["name"]: a["id"] for a in proj["agents"]}
    out, ref = [], {}
    for i, s in enumerate(raw[:5]):
        if not isinstance(s, dict):
            continue
        name = str(s.get("name") or "").strip()[:30] or ("단계%d" % (i + 1))
        kind = "review" if (s.get("kind") == "review" and out) else "work"
        key = str(s.get("agent") or "")
        agent_id = key if key in by_id else name_to_id.get(key)
        if not agent_id:
            return None
        sid = "j%d" % (len(out) + 1)
        target = ""
        if kind == "review":
            target = ref.get(str(s.get("target") or ""), "")
            if not target:
                works = [x for x in out if x["kind"] == "work"]
                target = works[-1]["id"] if works else ""
                if not target:
                    kind = "work"
        inputs = [ref[x] for x in (s.get("inputs") or []) if ref.get(x) and ref[x] != target]
        out.append({"id": sid, "name": name, "kind": kind, "agent": agent_id, "target": target, "inputs": inputs,
                    "instruction": str(s.get("instruction") or "").strip()[:3000], "enabled": True,
                    "max_turns": 0, "polish": bool(s.get("polish")) and kind == "review"})
        ref[name] = sid
    if not out or out[0]["kind"] != "work":
        return None
    return out


def ai_job_plan(proj, request_text):
    """요청 1건을 보고 그 작업에만 쓸 단계를 설계한다. 실패하면 (None, 사용량)을 돌려줘 호출자가 고정 파이프라인으로 대체하게 한다."""
    if not proj["agents"]:
        return None, None
    brief = "\n".join("- " + agent_brief(proj, a) for a in proj["agents"])
    prompt = (
        "STEP: jobplan\n이 요청 하나를 처리할 단계를 설계한다. 아래 '사용 가능한 에이전트' 중에서만 골라야 하며 "
        "새 에이전트를 만들 수 없다.\n\n요청:\n%s\n\n사용 가능한 에이전트:\n%s\n\n규칙:\n"
        "- 토큰을 아끼는 것이 최우선이다. 요청이 간단하면 work 단계 1개만 써도 된다. review 단계는 꼭 필요할 때만 추가한다.\n"
        "- 단계는 최대 5개로 제한한다. 첫 단계는 반드시 kind가 work여야 한다.\n"
        "- stages: [{\"name\":\"한글 단계 이름\",\"agent\":\"위 목록의 key\",\"kind\":\"work|review\","
        "\"target\":\"review일 때 검토할 앞 단계의 name\",\"instruction\":\"이 단계 지시 1~2문장\","
        "\"inputs\":[\"참고할 앞 단계의 name\"],\"polish\":false}]\n"
        "출력 형식: {\"stages\":[...]}  다른 설명 없이 이 JSON만 출력한다." % (request_text[:3000], brief))
    with PLAN_LOCK:
        cwd = BASE / ".planner"
        cwd.mkdir(exist_ok=True)
        try:
            r = subprocess.run(build_cmd(prompt, S_().get("planner_model") or "", 3, []), cwd=cwd, env=child_env(),
                               capture_output=True, text=True, timeout=120)
        except subprocess.TimeoutExpired:
            return None, None
    data = parse_result(r.stdout)
    if not data or data.get("is_error"):
        return None, data
    txt = str(data.get("result") or "")
    a, b = txt.find("{"), txt.rfind("}")
    try:
        raw = json.loads(txt[a:b + 1])
    except (ValueError, TypeError):
        return None, data
    return norm_job_stages(proj, raw.get("stages")), data


def job_stage_src(proj, job):
    return job.get("stages") or active_stages(proj)


def plan_job(proj, job):
    stages, data = ai_job_plan(proj, read_text(fpath(proj, "request", job["id"])) or job["title"])
    if data:
        add_usage(job, "plan", data)
    if stages:
        job["stages"] = stages
        set_state(job, step=stages[0]["id"])
        event(job, "system", "자동 구성: %d단계 (%s)" % (len(stages), " → ".join(s["name"] for s in stages)), "ok")
    else:
        event(job, "system", "자동 구성 실패 - 기본 파이프라인으로 진행", "warn")
    check_budget(job)


# ---------------------------------------------------------------- API 로직

def psummary(p):
    js = [j for (pid, _), j in JOBS.items() if pid == p["id"]]
    return {"id": p["id"], "name": p["name"], "description": p.get("description", ""),
            "active": sum(1 for j in js if j["status"] in ("queued", "running", "deploying")),
            "awaiting": sum(1 for j in js if j["status"] == "awaiting_user"),
            "jobs": len(js), "tokens": sum(new_tokens(j.get("usage") or {}) for j in js),
            "cost": round(sum((j.get("usage") or {}).get("cost", 0) for j in js), 4),
            "agents": len(p["agents"]), "stages": len(active_stages(p)),
            "schedules": sum(1 for s in p.get("schedules", []) if s.get("enabled", True)),
            "repo": {"on": True, "release": repo_release(p), "branch": repo_base(p), "test_url": repo_test_url(p),
                     "names": [r.get("name", r["id"]) for r in repos_of(p)]} if repo_on(p) else None}


def project_detail(proj):
    flush_trust()
    return {"id": proj["id"], "name": proj["name"], "description": proj.get("description", ""),
            "max_rounds": proj.get("max_rounds", 1), "root": proj["root"],
            "stage_mode": proj.get("stage_mode", "fixed"), "use_sources": proj.get("use_sources", "prefer"),
            "sources": len(src_list(proj)), "repo": {"on": True, "release": repo_release(proj), "branch": repo_base(proj),
                                                   "test_url": repo_test_url(proj)} if repo_on(proj) else None,
            "agents": [agent_info(proj, a) for a in proj["agents"]], "stages": proj["stages"],
            "schedules": proj.get("schedules", []), "summary": psummary(proj)}


def job_summary(j):
    return {k: j[k] for k in ("id", "title", "status", "step", "created", "updated")} | \
        {"tokens": new_tokens(j.get("usage") or {}), "needs_input": bool(j.get("needs_input")),
         "release_state": j.get("release_state", ""), "released_at": j.get("released_at", ""),
         "reverted_at": j.get("reverted_at", "")}


def job_detail(proj, j):
    src = j.get("stages") or proj["stages"]
    files = {"request": read_text(fpath(proj, "request", j["id"])),
             "final": read_text(fpath(proj, "final", j["id"])),
             "approved": read_text(fpath(proj, "approved", j["id"]))}
    for s in src:
        files[s["id"]] = read_text(fpath(proj, s["id"], j["id"]))
    files["diff"] = read_text(fpath(proj, "diff", j["id"]))
    files_att = att_list(proj, j["id"])
    rs_ = repos_of(proj)
    rp = {"on": True, "mode": rs_[0].get("merge", "merge") if rs_ else "merge", "base": repo_base(proj),
          "release": repo_release(proj), "test_url": repo_test_url(proj),
          "names": [r.get("name", r["id"]) for r in rs_]} if rs_ else None
    if rp and rp["release"] and j["status"] == "approved" and not j.get("release_state"):
        backfill_release(proj, j)
    if rp and j.get("release_state") == "pending":
        try:
            rp["with"] = [{"id": x["id"], "title": x["title"]} for x in pending_jobs(proj, j) if x["id"] != j["id"]]
        except Exception:  # noqa: BLE001
            rp["with"] = []
    return {"job": j, "files": files, "repo": rp, "attachments": files_att, "limit": S_().get("job_token_limit", 0), "max_rounds": proj.get("max_rounds", 1),
            "auto_planned": bool(j.get("stages")),
            "stages": [{"id": s["id"], "name": s["name"], "kind": s["kind"], "enabled": s.get("enabled", True),
                        "agent": agent_name(proj, s["agent"])} for s in src]}


def job_of(proj, jid):
    if not ID_RE.match(jid or ""):
        raise ApiError(400, "잘못된 작업 ID")
    j = JOBS.get((proj["id"], jid))
    if not j:
        raise ApiError(404, "작업을 찾을 수 없음")
    return j


ATT_EXT = {"png", "jpg", "jpeg", "gif", "webp", "pdf", "txt", "md", "csv", "json", "log", "yaml", "yml", "html", "css",
           "js", "ts", "vue", "py", "sql", "xml", "har"}
ATT_IMG = {"png", "jpg", "jpeg", "gif", "webp"}
ATT_MAX, ATT_TOTAL, ATT_COUNT = 10 * 1024 * 1024, 20 * 1024 * 1024, 10


def att_dir(proj, jid):
    return proj_dirs(proj)["inbox"] / ("%s_files" % jid)


def att_name(name, used):
    base = re.sub(r"[^\w.가-힣-]+", "_", Path(str(name or "file")).name).strip("._")[:80] or "file"
    ext = base.rsplit(".", 1)[-1].lower() if "." in base else ""
    if ext not in ATT_EXT:
        raise ApiError(400, "올릴 수 없는 파일 형식입니다: %s (이미지·PDF·텍스트·코드 파일만)" % base[:40])
    stem, n, out = base[: -len(ext) - 1], 1, base
    while out in used:
        n += 1
        out = "%s_%d.%s" % (stem, n, ext)
    used.add(out)
    return out


def save_attachments(proj, jid, files, keep=()):
    """GUI에서 올린 파일(base64)을 inbox/<작업ID>_files/ 에 저장한다. 에이전트는 필요할 때 Read로 연다."""
    if not files:
        return []
    if not isinstance(files, list) or len(files) > ATT_COUNT:
        raise ApiError(400, "첨부는 최대 %d개까지입니다" % ATT_COUNT)
    out, used, total = [], set(keep), 0
    blobs = []
    for f in files:
        try:
            data = base64.b64decode(str(f.get("data") or ""), validate=True)
        except (ValueError, AttributeError):
            raise ApiError(400, "첨부 파일을 읽지 못했습니다")
        if len(data) > ATT_MAX:
            raise ApiError(400, "파일 하나는 10MB까지입니다: %s" % str(f.get("name"))[:40])
        total += len(data)
        if total > ATT_TOTAL:
            raise ApiError(400, "첨부 전체는 20MB까지입니다")
        blobs.append((att_name(f.get("name"), used), data))
    d = att_dir(proj, jid)
    d.mkdir(parents=True, exist_ok=True)
    for name, data in blobs:
        (d / name).write_bytes(data)
        out.append({"name": name, "size": len(data)})
    return out


def att_list(proj, jid):
    d = att_dir(proj, jid)
    if not d.is_dir():
        return []
    return [{"name": x.name, "size": x.stat().st_size, "img": x.suffix.lower().lstrip(".") in ATT_IMG}
            for x in sorted(d.iterdir()) if x.is_file()]


def att_block(proj, jid):
    files = att_list(proj, jid)
    if not files:
        return ""
    return ("[첨부 파일] 요청에 함께 올라온 파일이다. 작업에 필요한 것만 Read로 열어 확인한다(이미지는 화면 캡처일 수 있음).\n"
            + "\n".join("- ../shared/inbox/%s_files/%s" % (jid, f["name"]) for f in files) + "\n")


def create_job(proj, text, source="gui", auto_approve=False, chat=None, title=None, files=None):
    text = (text or "").strip()
    if not text:
        raise ApiError(400, "요청 내용을 입력하세요")
    if len(text) > 20000:
        raise ApiError(400, "요청이 너무 깁니다")
    if not active_stages(proj):
        raise ApiError(400, "사용 중인 단계가 없습니다")
    ensure_dirs(proj)
    jid = time.strftime("%m%d-%H%M%S") + "-" + secrets.token_hex(1)
    saved = save_attachments(proj, jid, files)
    fpath(proj, "request", jid).write_text(text + "\n")
    auto = proj.get("stage_mode") == "auto"
    job = {"id": jid, "pid": proj["id"], "title": (title or text.splitlines()[0])[:60], "status": "queued",
           "step": ("" if auto else active_stages(proj)[0]["id"]), "created": now(), "updated": now(),
           "feedback": "", "error": "", "cancel": False, "usage": {}, "events": [], "source": source,
           "auto_approve": bool(auto_approve), "chat": str(chat) if chat else "",
           "needs_input": False, "question": ""}
    JOBS[(proj["id"], jid)] = job
    jsave(job)
    event(job, "system", "작업 등록" + {"telegram": " (텔레그램)", "schedule": " (예약 실행)"}.get(source, "")
          + (" · 첨부 %d개" % len(saved) if saved else ""))
    QUEUE.put((proj["id"], jid, "first"))
    return job


def job_restart(proj, j, b):
    if j["status"] not in ("awaiting_user", "failed", "cancelled"):
        raise ApiError(409, "지금은 다시 시작할 수 없는 상태입니다")
    start = str(b.get("start") or "first")
    act = job_stage_src(proj, j)
    if start != "first" and not any(s["id"] == start and s["kind"] == "work" for s in act):
        raise ApiError(400, "시작 단계가 올바르지 않습니다")
    fb = (b.get("feedback") or "").strip()[:5000]
    first = act[0]["id"] if act else ""
    if fb:   # 수정 요청·답변도 요청 탭에 차례대로 남긴다
        answer = bool(j.get("needs_input"))
        n = int(j.get("revisions") or 0) + (0 if answer else 1)
        rq = fpath(proj, "request", j["id"])
        rq.write_text((read_text(rq) or "").rstrip() + "\n\n## %s (%s)\n%s\n"
                      % ("질문에 대한 답변" if answer else "수정 요청 %d" % n, now()[:16], fb))
        if not answer:
            j["revisions"] = n
    set_state(j, status="queued", step=first if start == "first" else start, feedback=fb, error="", cancel=False,
              needs_input=False, question="")
    label = "처음" if start == "first" else next(s["name"] for s in act if s["id"] == start)
    event(j, "user", "수정 요청으로 %s 단계부터 다시 시작%s" % (label, (": " + fb[:120]) if fb else ""))
    QUEUE.put((proj["id"], j["id"], start))
    return job_summary(j)


def job_edit(proj, j, b):
    """중단·실패한 작업의 요청 내용(과 첨부)을 고쳐서 처음부터 다시 시작한다."""
    if j["status"] not in ("failed", "cancelled", "reverted"):
        raise ApiError(409, "진행 중이거나 끝난 작업은 고칠 수 없습니다. 먼저 작업을 중단하세요")
    text = str(b.get("request") or "").strip()
    if not text:
        raise ApiError(400, "요청 내용을 입력하세요")
    if len(text) > 20000:
        raise ApiError(400, "요청이 너무 깁니다")
    jid, d = j["id"], att_dir(proj, j["id"])
    for name in b.get("remove") or []:
        f = d / Path(str(name)).name
        if f.is_file() and f.resolve().parent == d.resolve():
            f.unlink()
    keep = [x["name"] for x in att_list(proj, jid)]
    if len(keep) + len(b.get("files") or []) > ATT_COUNT:
        raise ApiError(400, "첨부는 최대 %d개까지입니다" % ATT_COUNT)
    added = save_attachments(proj, jid, b.get("files"), keep)
    fpath(proj, "request", jid).write_text(text + "\n")
    # 예전 요청으로 만든 중간 결과는 지워서 에이전트가 섞어 읽지 않게 한다
    for f in proj_dirs(proj)["handoff"].glob("*_%s.md" % jid):
        try:
            f.unlink()
        except OSError:
            pass
    for k in ("final", "diff"):
        try:
            fpath(proj, k, jid).unlink()
        except OSError:
            pass
    upd = {"title": text.splitlines()[0][:60], "status": "queued", "feedback": "", "error": "", "cancel": False,
           "needs_input": False, "question": "", "fresh_branch": bool(repo_on(proj))}
    if proj.get("stage_mode") == "auto":
        upd["stages"] = None
    act = job_stage_src(proj, j)
    upd["step"] = act[0]["id"] if act else ""
    set_state(j, **upd)
    event(j, "user", "요청 수정 후 처음부터 다시 시작" + (" · 첨부 %d개 추가" % len(added) if added else ""))
    QUEUE.put((proj["id"], jid, "first"))
    return job_summary(j)


def job_followup(proj, j, b):
    """승인한 작업을 다시 열어, 앞선 결과(코드 저장소면 테스트 브랜치의 최신 코드) 위에서 이어서 수정한다."""
    if j["status"] != "approved":
        raise ApiError(409, "승인 완료된 작업만 이어서 요청할 수 있습니다")
    text = str(b.get("request") or "").strip()
    if not text:
        raise ApiError(400, "추가 요청 내용을 입력하세요")
    if len(text) > 20000:
        raise ApiError(400, "요청이 너무 깁니다")
    jid = j["id"]
    keep = [x["name"] for x in att_list(proj, jid)]
    if len(keep) + len(b.get("files") or []) > ATT_COUNT:
        raise ApiError(400, "첨부는 최대 %d개까지입니다 (지금 %d개)" % (ATT_COUNT, len(keep)))
    added = save_attachments(proj, jid, b.get("files"), keep)
    n = int(j.get("followups") or 0) + 1
    rq = fpath(proj, "request", jid)
    rq.write_text((read_text(rq) or "").rstrip() + "\n\n## 추가 요청 %d (%s)\n%s\n" % (n, now()[:16], text))
    try:
        fpath(proj, "diff", jid).unlink()
    except OSError:
        pass
    act = job_stage_src(proj, j)
    set_state(j, status="queued", step=act[0]["id"] if act else "", feedback=text[:5000], error="", cancel=False,
              needs_input=False, question="", followups=n)
    event(j, "user", "이어서 수정 요청 (%d차)%s: %s" % (n, " · 첨부 %d개" % len(added) if added else "", text[:120]))
    QUEUE.put((proj["id"], jid, "first"))
    return job_summary(j)


def job_approve(proj, j):
    if j["status"] != "awaiting_user":
        raise ApiError(409, "승인 대기 상태가 아닙니다")
    if j.get("needs_input"):
        raise ApiError(409, "에이전트의 질문에 먼저 답해주세요")
    src = fpath(proj, "final", j["id"])
    if not src.exists():
        works = [s for s in job_stage_src(proj, j) if s["kind"] == "work"]
        src = fpath(proj, works[-1]["id"], j["id"]) if works else src
    if not src.exists():
        raise ApiError(409, "승인할 결과 파일이 없습니다")
    proj_dirs(proj)["outbox"].mkdir(parents=True, exist_ok=True)
    if repo_on(proj):
        set_state(j, status="deploying", error="")
        event(j, "user", "최종 승인 - 저장소에 반영하는 중")
        threading.Thread(target=repo_deliver, args=(proj, j, src), daemon=True).start()
        return job_summary(j)
    shutil.copy2(src, fpath(proj, "approved", j["id"]))
    set_state(j, status="approved")
    event(j, "user", "최종 승인 -> outbox/approved_%s.md" % j["id"], "ok")
    notify_job(j, "approved")
    return job_summary(j)


def job_cancel(proj, j):
    if j["status"] not in ("queued", "running"):
        raise ApiError(409, "진행 중인 작업이 아닙니다")
    set_state(j, cancel=True)
    p = PROCS.get((proj["id"], j["id"]))
    if p:
        kill_proc(p)
    return job_summary(j)


DELETABLE = ("awaiting_user", "approved", "failed", "cancelled", "reverted")


def job_delete(proj, j):
    """작업 기록과 그 작업이 만든 파일(요청·중간 결과·최종본·이력·로그·로컬 작업 브랜치)을 지운다."""
    jid = j["id"]
    if j["status"] not in DELETABLE:
        raise ApiError(409, "진행 중인 작업은 먼저 중지한 뒤 삭제하세요")
    d = proj_dirs(proj)
    targets = [d["jobs"] / ("%s.json" % jid), fpath(proj, "request", jid), fpath(proj, "final", jid),
               fpath(proj, "approved", jid)]
    shutil.rmtree(att_dir(proj, jid), ignore_errors=True)
    targets += list(d["handoff"].glob("*_%s.md" % jid)) + [x for x in d["inbox"].glob("%s*" % jid) if x.is_file()]
    if d["logs"].is_dir():
        targets += list(d["logs"].glob("%s_*" % jid))
    for t in targets:
        try:
            t.unlink()
        except OSError:
            pass
    shutil.rmtree(d["hist"] / jid, ignore_errors=True)
    if repo_on(proj):
        threading.Thread(target=repo_drop_branch, args=(proj, jid), daemon=True).start()
    JOBS.pop((proj["id"], jid), None)
    for chat, v in list(TG_WAIT.items()):
        if v == (proj["id"], jid):
            TG_WAIT.pop(chat, None)
    return {"deleted": jid}


def job_delete_many(proj, b):
    sts = [x for x in (b.get("status") or []) if x in DELETABLE] or ["approved", "failed", "cancelled", "reverted"]
    days = max(0, int(b.get("older_days") or 0))
    cut = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(time.time() - days * 86400))
    n = 0
    for (pid, _), j in list(JOBS.items()):
        if pid == proj["id"] and j["status"] in sts and (not days or j["created"] < cut):
            job_delete(proj, j)
            n += 1
    return {"deleted": n}


def project_create(b):
    name = str(b.get("name") or "").strip()[:40]
    if not name:
        raise ApiError(400, "프로젝트 이름을 입력하세요")
    try:
        plan = norm_plan(b["plan"], 10, 8) if b.get("plan") else copy.deepcopy(PRESETS[0]["plan"])
    except ValueError as e:
        raise ApiError(400, str(e))
    nums = [int(re.sub(r"\D", "", p["id"]) or 0) for p in CFG["projects"]]
    pid = "p%d" % (max(nums + [0]) + 1)
    sm = "auto" if b.get("stage_mode") == "auto" else "fixed"
    proj = {"id": pid, "name": name, "description": str(b.get("description") or "").strip()[:2000],
            "root": "projects/%s" % pid, "agents": [], "stages": [], "max_rounds": 1, "schedules": [],
            "stage_mode": sm, "use_sources": "prefer", "created": now()}
    (BASE / proj["root"]).mkdir(parents=True, exist_ok=True)
    ensure_dirs(proj)
    apply_plan(proj, plan)
    CFG["projects"].append(proj)
    save_cfg()
    return project_detail(proj)


def project_update(proj, b):
    name = str(b.get("name") or proj["name"]).strip()[:40]
    if not name:
        raise ApiError(400, "이름을 입력하세요")
    try:
        mr = max(0, min(3, int(b.get("max_rounds", proj.get("max_rounds", 1)))))
    except (TypeError, ValueError):
        raise ApiError(400, "반복 횟수가 올바르지 않습니다")
    proj["name"], proj["max_rounds"] = name, mr
    proj["description"] = str(b.get("description") or "").strip()[:2000]
    if "stage_mode" in b:
        proj["stage_mode"] = "auto" if b["stage_mode"] == "auto" else "fixed"
    save_cfg()
    return project_detail(proj)


def project_delete(proj):
    if len(CFG["projects"]) <= 1:
        raise ApiError(409, "마지막 프로젝트는 제거할 수 없습니다")
    if any(j["status"] in ("queued", "running") for (pid, _), j in JOBS.items() if pid == proj["id"]):
        raise ApiError(409, "진행 중인 작업이 있어 제거할 수 없습니다")
    CFG["projects"].remove(proj)
    save_cfg()
    return {"ok": True, "note": "목록에서만 제거했고 폴더와 파일은 그대로 남아 있습니다"}


def agent_create(proj, b):
    name = str(b.get("name") or "").strip()[:30]
    if not name:
        raise ApiError(400, "이름을 입력하세요")
    model = str(b.get("model") or "").strip()
    if not MODEL_RE.match(model):
        raise ApiError(400, "모델 이름이 올바르지 않습니다")
    a = create_agent_in(proj, name, str(b.get("description") or "").strip()[:5000], b.get("perms") or {}, model,
                        str(b.get("workspace") or "").strip())
    save_cfg()
    return {"agent": agent_info(proj, a), "warning": None if is_trusted(proj_dirs(proj)["root"] / a["workspace"]) else
            "폴더 신뢰 등록이 보류되었습니다(작업 실행 중). 작업이 끝나면 자동으로 등록됩니다."}


def agent_save(proj, a, b):
    name = str(b.get("name") or a["name"]).strip()[:30]
    if not name:
        raise ApiError(400, "이름을 입력하세요")
    model = str(b.get("model") or "").strip()
    if not MODEL_RE.match(model):
        raise ApiError(400, "모델 이름이 올바르지 않습니다")
    md = b.get("claude_md")
    if md is not None and (not isinstance(md, str) or len(md) > 50000):
        raise ApiError(400, "역할 설명(CLAUDE.md)이 너무 깁니다")
    ws = proj_dirs(proj)["root"] / a["workspace"]
    if not ws.is_dir():
        raise ApiError(404, "워크스페이스 폴더가 없습니다")
    (ws / ".claude").mkdir(parents=True, exist_ok=True)
    if md is not None:
        backup_file(proj, ws / "CLAUDE.md")
        (ws / "CLAUDE.md").write_text(md.rstrip() + "\n")
    sp = ws / ".claude" / "settings.json"
    backup_file(proj, sp)
    sp.write_text(json.dumps(build_settings(proj, b.get("perms") or {}), ensure_ascii=False, indent=2))
    a["name"], a["model"] = name, model
    save_cfg()
    ok = trust(ws)
    return {"agent": agent_info(proj, a, True), "warning": None if ok else
            "폴더 신뢰 등록이 보류되었습니다(작업 실행 중). 작업이 끝나면 자동으로 등록됩니다."}


def rename_agent_folder(proj, a):
    if PROCS:
        raise ApiError(409, "작업이 실행 중일 때는 폴더 이름을 정리할 수 없습니다. 잠시 후 다시 시도하세요")
    root = proj_dirs(proj)["root"]
    old_ws = root / a["workspace"]
    if not old_ws.is_dir():
        raise ApiError(404, "워크스페이스 폴더가 없습니다")
    used = {x["workspace"] for x in proj["agents"] if x["id"] != a["id"]}
    new_name = free_ws_name(root, ws_slug(a["name"]) or "agent", used, keep=a["workspace"])
    if new_name == a["workspace"]:
        return {"changed": False, "workspace": a["workspace"]}
    new_ws = root / new_name
    old_ws.rename(new_ws)
    a["workspace"] = new_name
    save_cfg()
    trust(new_ws)
    return {"changed": True, "workspace": new_name}


def agent_remove(proj, a):
    used = [s["name"] for s in proj["stages"] if s["agent"] == a["id"]]
    if used:
        raise ApiError(409, "단계 담당으로 지정되어 있어 제거할 수 없습니다: %s" % ", ".join(used))
    proj["agents"].remove(a)
    save_cfg()
    return {"ok": True, "note": "목록에서만 제거했고 폴더와 파일은 그대로 남아 있습니다"}


def settings_update(b):
    s = S_()
    try:
        if "parallel" in b:
            s["parallel"] = max(1, min(3, int(b["parallel"])))
        if "job_token_limit" in b:
            s["job_token_limit"] = max(0, int(b["job_token_limit"]))
    except (TypeError, ValueError):
        raise ApiError(400, "숫자 형식이 올바르지 않습니다")
    if "planner_model" in b:
        m = str(b["planner_model"] or "").strip()
        if not MODEL_RE.match(m):
            raise ApiError(400, "모델 이름이 올바르지 않습니다")
        s["planner_model"] = m
    save_cfg()
    with COND:
        COND.notify_all()
    return s


# ---------------------------------------------------------------- 텔레그램

def tg_cfg():
    return CFG["settings"]["telegram"]


def tg_call(method, payload=None, timeout=35):
    if not BOT_TOKEN:
        raise RuntimeError("TELEGRAM_BOT_TOKEN 이 설정되지 않았습니다")
    req = urllib.request.Request("%s/bot%s/%s" % (TG_BASE, BOT_TOKEN, method),
                                 data=json.dumps(payload or {}).encode(),
                                 headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        d = json.loads(r.read().decode())
    if not d.get("ok"):
        raise RuntimeError(str(d.get("description") or d)[:200])
    return d.get("result")


def tg_send(chat, text, buttons=None):
    body = {"chat_id": int(chat), "text": text[:3900], "disable_web_page_preview": True}
    if buttons:
        body["reply_markup"] = {"inline_keyboard": [[{"text": t, "callback_data": d} for t, d in row]
                                                    for row in buttons]}
    return tg_call("sendMessage", body, 25)


def tg_allowed(chat):
    return str(chat) in tg_cfg()["chats"]


def notify(text, buttons=None, chat=None):
    """네트워크 호출은 전송 스레드에 맡긴다(파이프라인을 막지 않기 위해)."""
    if not BOT_TOKEN:
        return
    with LOCK:
        if chat and tg_allowed(chat):
            targets = [str(chat)]
        elif chat:
            targets = []
        else:
            targets = list(tg_cfg()["chats"]) if tg_cfg().get("notify", True) else []
    for t in targets:
        NOTIFY.put((t, text, buttons))


def notify_job(job, kind):
    if not BOT_TOKEN:
        return
    with LOCK:
        proj = next((p for p in CFG["projects"] if p["id"] == job["pid"]), None)
        if not proj:
            return
        pname, tok = proj["name"], new_tokens(job.get("usage") or {})
        chat = job.get("chat") or None
        ref = "%s:%s" % (job["pid"], job["id"])
        if kind == "approved":
            src = fpath(proj, "approved", job["id"])
            body = read_text(src, 3000) or "(결과 파일을 읽지 못했습니다)"
    if kind == "awaiting":
        notify("[%s] %s\n검토가 끝나 승인을 기다립니다. (새 토큰 %s)" % (pname, job["title"], tok),
               [[("승인", "ap:" + ref), ("반려", "rj:" + ref)], [("결과 보기", "rs:" + ref)]], chat)
    elif kind == "failed":
        notify("[%s] %s\n실패: %s" % (pname, job["title"], str(job.get("error"))[:300]),
               [[("다시 시도", "rt:" + ref)]], chat)
    elif kind == "approved":
        rb = [[("운영 반영", "rl:%s:%s" % (job["pid"], job["id"]))]] if job.get("release_state") == "pending" else None
        notify("[%s] %s · 완료 (새 토큰 %s)\n\n%s" % (pname, job["title"], tok, body), rb, chat)
    elif kind == "question":
        notify("[%s] %s\n에이전트가 질문이 있습니다:\n\n%s" % (pname, job["title"], str(job.get("question"))[:1500]),
               [[("답변하기", "aw:" + ref)]], chat)


def tg_projects(chat):
    cur = tg_cur(chat)
    lines, btns = ["프로젝트 목록"], []
    for i, p in enumerate(CFG["projects"], 1):
        now_using = cur and p["id"] == cur["id"]
        mode = "자동 구성" if p.get("stage_mode") == "auto" else "%d단계" % len(active_stages(p))
        lines.append("%d. %s (%s, 에이전트 %d, 작업 %d)%s"
                     % (i, p["name"], mode, len(p["agents"]), psummary(p)["jobs"],
                        " ← 지금 사용 중" if now_using else ""))
        btns.append([(("✓ " if now_using else "") + p["name"][:28], "pu:%s:0" % p["id"])])
    lines.append("\n버튼을 누르면 바로 전환됩니다. 새로 만들려면 /newproject 이름")
    return "\n".join(lines), btns


def tg_project_card(proj):
    ags = ", ".join(a["name"] for a in proj["agents"]) or "없음"
    mode = "요청마다 자동 구성" if proj.get("stage_mode") == "auto" else "고정 %d단계" % len(active_stages(proj))
    src = len(src_list(proj))
    return ("'%s' 프로젝트를 사용합니다.\n에이전트: %s\n처리 방식: %s%s\n\n이제 그냥 메시지를 보내면 이 프로젝트로 작업이 등록됩니다."
            % (proj["name"], ags, mode, ("\n참고 자료: %d개" % src) if src else ""))


def tg_cur(chat):
    cur = tg_cfg()["cur"].get(str(chat))
    p = next((x for x in CFG["projects"] if x["id"] == cur), None)
    return p or (CFG["projects"][0] if CFG["projects"] else None)


def tg_jobs_text(proj):
    js = sorted((j for (pid, _), j in JOBS.items() if pid == proj["id"]), key=lambda j: j["created"], reverse=True)[:5]
    if not js:
        return "아직 작업이 없습니다.", None
    st = {"queued": "대기", "running": "진행 중", "awaiting_user": "승인 대기", "approved": "완료", "deploying": "반영 중",
          "failed": "실패", "cancelled": "중단", "reverted": "되돌림"}
    lines, btns = ["[%s] 최근 작업" % proj["name"]], []
    for j in js:
        lines.append("· %s — %s (%s)" % (j["title"][:40], st.get(j["status"], j["status"]), j["created"][5:16]))
        btns.append([("결과: " + j["title"][:18], "rs:%s:%s" % (j["pid"], j["id"]))])
    return "\n".join(lines), btns


def tg_result(proj, job):
    for kind in ("approved", "final"):
        t = read_text(fpath(proj, kind, job["id"]), 3000)
        if t:
            return t
    works = [x for x in job_stage_src(proj, job) if x["kind"] == "work"]
    for st in reversed(works):
        t = read_text(fpath(proj, st["id"], job["id"]), 3000)
        if t:
            return t
    return "아직 결과가 없습니다."


def cheap_start(proj, job):
    """토큰을 아끼려고, 처음이 아니라 다시 할 필요가 있는 가장 뒤쪽 '작업' 단계부터 시작한다."""
    act = job_stage_src(proj, job)
    works = [s["id"] for s in act if s["kind"] == "work"]
    if not works:
        return "first"
    if job.get("status") == "failed":
        cur = next((s for s in act if s["id"] == job.get("step")), None)
        if cur:
            sid = cur["id"] if cur["kind"] == "work" else cur.get("target")
            if sid in works:
                return sid
        return "first"
    return works[-1]


def tg_button(chat, data):
    try:
        act, pid, jid = data.split(":", 2)
    except ValueError:
        return
    with LOCK:
        try:
            proj = proj_of(pid)
        except ApiError as e:
            return notify(e.msg, None, chat)
        if act == "rl":
            if not repo_on(proj):
                return notify("[%s] 코드 저장소가 연결되지 않았습니다." % proj["name"], None, chat)
            jb = JOBS.get((pid, jid)) if jid != "-" else None
            js = pending_jobs(proj, jb) if jb and job_merges(jb) else pending_jobs(proj)
            if not js:
                return notify("[%s] 운영 대기 중인 작업이 없습니다." % proj["name"], None, chat)
            return notify("[%s] 테스트 서버에서 확인을 마쳤나요? 아래 작업 %d개를 운영에 올립니다.\n%s"
                          % (proj["name"], len(js), "\n".join("- " + x["title"][:50] for x in js[:10])),
                          [[("예, 운영 반영", "rly:%s:%s" % (pid, jid))]], chat)
        if act == "rly":
            jb = JOBS.get((pid, jid)) if jid != "-" else None
            def go():
                try:
                    repo_promote(proj, "텔레그램", job=jb)
                except ApiError as e:
                    notify("[%s] %s" % (proj["name"], e.msg), None, chat)
            threading.Thread(target=go, daemon=True).start()
            return notify("운영 반영을 시작합니다…", None, chat)
        if act == "pu":
            tg_cfg()["cur"][str(chat)] = proj["id"]
            save_cfg()
            return notify(tg_project_card(proj), None, chat)
        try:
            job = job_of(proj, jid)
        except ApiError as e:
            return notify(e.msg, None, chat)
        if act == "rs":
            return notify("[%s] %s\n\n%s" % (proj["name"], job["title"], tg_result(proj, job)), None, chat)
        if act == "rj":
            TG_WAIT[str(chat)] = (pid, jid)
            st = cheap_start(proj, job)
            name = next((s["name"] for s in job_stage_src(proj, job) if s["id"] == st), "처음")
            return notify("수정 요청 내용을 메시지로 보내주세요. '%s' 단계부터 다시 합니다. (취소: /cancel)" % name, None, chat)
        if act == "aw":
            TG_WAIT[str(chat)] = (pid, jid)
            return notify("질문에 대한 답변을 메시지로 보내주세요. (취소: /cancel)\n\n%s" % str(job.get("question"))[:1000],
                          None, chat)
        try:
            if act == "ap":
                job_approve(proj, job)
                notify("승인했습니다: %s%s" % (job["title"], " (저장소에 반영하는 중)" if repo_on(proj) else ""), None, chat)
            elif act == "rt":
                job_restart(proj, job, {"start": cheap_start(proj, job)})
                notify("다시 시작합니다: %s" % job["title"], None, chat)
        except ApiError as e:
            notify(e.msg, None, chat)


def tg_message(chat, text):
    with LOCK:
        if str(chat) in TG_WAIT:
            pid, jid = TG_WAIT.pop(str(chat))
            if text.strip() == "/cancel":
                return notify("취소했습니다.", None, chat)
            try:
                proj = proj_of(pid)
                job = job_of(proj, jid)
                answering = bool(job.get("needs_input"))
                start = job["step"] if answering else cheap_start(proj, job)
                job_restart(proj, job, {"start": start, "feedback": text})
                return notify("답변을 반영해 이어서 진행합니다." if answering else "수정 요청을 반영해 다시 작업합니다.", None, chat)
            except ApiError as e:
                return notify(e.msg, None, chat)
        cmd = text.split()[0].lower() if text.startswith("/") else ""
        arg = text[len(cmd):].strip()
        if cmd == "/security":
            st = security_state()
            lines = ["보안 상태", "차단 중 IP %d개%s" % (st["blocked_total"], " · 외부 로그인 잠김 %d분" % (st["lockdown"] // 60 + 1) if st["lockdown"] else "")]
            lines += ["- %s (%s)" % (b["ip"], b["reason"][:40]) for b in st["blocked"][:10]]
            lines.append("\n해제: /unban IP   잠금 해제: /unlock")
            return notify("\n".join(lines), None, chat)
        if cmd == "/unban":
            if not arg or not ip_ok(arg):
                return notify("IP를 함께 보내주세요. 예: /unban 211.234.1.2  (목록은 /security)", None, chat)
            unban(arg)
            return notify("%s 차단을 해제했습니다." % arg, None, chat)
        if cmd == "/unlock":
            SEC["lockdown_until"] = 0
            sec_event("-", "외부 로그인 잠금 해제(텔레그램)", "ok")
            sec_save()
            return notify("외부 로그인 잠금을 해제했습니다.", None, chat)
        proj = tg_cur(chat)
        if not proj:
            return notify("프로젝트가 없습니다. GUI에서 먼저 만들어주세요.", None, chat)
        if cmd in ("/start", "/help"):
            _, btns = tg_projects(chat)
            return notify("지금 사용 중: %s\n\n%s\n\n아래 버튼으로 프로젝트를 바꿀 수 있습니다."
                          % (proj["name"], TG_HELP), btns[:8], chat)
        if cmd == "/cancel":
            return notify("대기 중인 입력이 없습니다.", None, chat)
        if cmd == "/release":
            return tg_button(chat, "rl:%s:-" % proj["id"])
        if cmd == "/projects":
            t, btns = tg_projects(chat)
            return notify(t, btns, chat)
        if cmd == "/use":
            try:
                assert int(arg) >= 1
                p = CFG["projects"][int(arg) - 1]
            except (ValueError, IndexError, AssertionError):
                return notify("번호가 올바르지 않습니다. /projects 로 확인하세요.", None, chat)
            tg_cfg()["cur"][str(chat)] = p["id"]
            save_cfg()
            return notify(tg_project_card(p), None, chat)
        if cmd in ("/newproject", "/np"):
            if not arg:
                return notify("프로젝트 이름을 함께 보내주세요. 예: /newproject 뉴스봇", None, chat)
            try:
                d = project_create({"name": arg, "description": arg,
                                    "plan": copy.deepcopy(PRESETS[0]["plan"]), "stage_mode": "auto"})
            except ApiError as e:
                return notify(e.msg, None, chat)
            tg_cfg()["cur"][str(chat)] = d["id"]
            save_cfg()
            return notify("새 프로젝트를 만들었습니다.\n\n%s\n\n에이전트와 참고 자료는 웹 화면에서 더 자세히 고칠 수 있습니다."
                          % tg_project_card(proj_of(d["id"])), None, chat)
        if cmd == "/jobs":
            t, b = tg_jobs_text(proj)
            return notify(t, b, chat)
        if cmd == "/status":
            act = [j for (pid, _), j in JOBS.items() if j["status"] in ("queued", "running")]
            if not act:
                return notify("실행 중인 작업이 없습니다.", None, chat)
            return notify("실행 중\n" + "\n".join("· [%s] %s — %s" % (agent_name_safe(j["pid"]), j["title"][:40],
                                                                    j["status"]) for j in act), None, chat)
        if cmd == "/sched":
            sc = proj.get("schedules", [])
            if not sc:
                return notify("[%s] 예약이 없습니다. GUI의 '예약' 화면에서 추가하세요." % proj["name"], None, chat)
            return notify("[%s] 예약\n" % proj["name"] + "\n".join(
                "· %s %s %s%s" % (x["time"], x["name"], "사용" if x.get("enabled", True) else "꺼짐",
                                  " · 자동승인" if x.get("auto_approve") else "") for x in sc), None, chat)
        if cmd and cmd not in ("/new",):
            return notify("모르는 명령입니다.\n\n" + TG_HELP, None, chat)
        req = arg if cmd == "/new" else text
        if not req.strip():
            return notify("요청 내용을 함께 보내주세요.", None, chat)
        try:
            job = create_job(proj, req, source="telegram", chat=chat)
        except ApiError as e:
            return notify(e.msg, None, chat)
        notify("[%s] 작업을 시작했습니다: %s\n끝나면 알려드릴게요." % (proj["name"], job["title"]), None, chat)


def agent_name_safe(pid):
    p = next((x for x in CFG["projects"] if x["id"] == pid), None)
    return p["name"] if p else pid


def tg_handle(u):
    cb = u.get("callback_query")
    if cb:
        chat = str(((cb.get("message") or {}).get("chat") or {}).get("id") or "")
        try:
            tg_call("answerCallbackQuery", {"callback_query_id": cb.get("id")}, 15)
        except Exception:  # noqa: BLE001
            pass
        if chat and tg_allowed(chat):
            tg_button(chat, str(cb.get("data") or ""))
        return
    msg = u.get("message") or u.get("edited_message") or {}
    chat = str(((msg.get("chat") or {}).get("id")) or "")
    text = (msg.get("text") or "").strip()
    if not chat or not text:
        return
    if text.split()[0].lower() == "/pair":
        code = text.split()[1].strip() if len(text.split()) > 1 else ""
        with LOCK:
            ok = hmac.compare_digest(code, PAIR_CODE)
            if ok and chat not in tg_cfg()["chats"]:
                tg_cfg()["chats"].append(chat)
                save_cfg()
        if ok:
            return notify("연결되었습니다.\n\n" + TG_HELP, None, chat)
        print("텔레그램: 잘못된 연결 코드 (chat %s)" % chat, flush=True)
        return
    if not tg_allowed(chat):
        print("텔레그램: 허용되지 않은 chat %s 의 메시지를 무시했습니다" % chat, flush=True)
        return
    tg_message(chat, text)


def tg_sender():
    while True:
        chat, text, buttons = NOTIFY.get()
        try:
            tg_send(chat, text, buttons)
        except Exception as e:  # noqa: BLE001
            print("텔레그램 전송 실패(chat %s): %s" % (chat, e), flush=True)


def tg_loop():
    offset, wait = 0, 1
    try:
        me = tg_call("getMe", {}, 20)
        print("텔레그램 봇 연결: @%s (연결 코드: %s)" % (me.get("username", "?"), PAIR_CODE), flush=True)
    except Exception as e:  # noqa: BLE001
        print("텔레그램 봇 확인 실패: %s" % e, flush=True)
    while True:
        try:
            ups = tg_call("getUpdates", {"offset": offset, "timeout": TG_POLL,
                                         "allowed_updates": ["message", "callback_query"]}, TG_POLL + 15) or []
            wait = 1
            for u in ups:
                offset = max(offset, int(u.get("update_id", 0)) + 1)
                try:
                    tg_handle(u)
                except Exception:  # noqa: BLE001
                    traceback.print_exc()
        except Exception as e:  # noqa: BLE001
            print("텔레그램 수신 오류: %s (%d초 후 재시도)" % (str(e)[:120], wait), flush=True)
            time.sleep(wait)
            wait = min(wait * 2, 60)


# ---------------------------------------------------------------- 예약 작업

def validate_schedules(raw):
    if not isinstance(raw, list) or len(raw) > 20:
        raise ApiError(400, "예약은 20개까지 등록할 수 있습니다")
    out, ids = [], set()
    for x in raw:
        if not isinstance(x, dict):
            raise ApiError(400, "예약 형식 오류")
        name = str(x.get("name") or "").strip()[:30]
        req = str(x.get("request") or "").strip()[:5000]
        if not name or not req:
            raise ApiError(400, "예약 이름과 요청 내용을 입력하세요")
        t = str(x.get("time") or "").strip()
        if not re.match(r"^([01]\d|2[0-3]):([0-5]\d)$", t):
            raise ApiError(400, "시각은 HH:MM 형식이어야 합니다 (예: 07:30)")
        days = sorted({int(d) for d in (x.get("days") or []) if str(d).isdigit() and 0 <= int(d) <= 6})
        if not days:
            raise ApiError(400, "'%s' 예약의 요일을 하나 이상 선택하세요" % name)
        sid = str(x.get("id") or "")
        if not ID_RE.match(sid) or sid in ids:
            sid = secrets.token_hex(3)
        ids.add(sid)
        out.append({"id": sid, "name": name, "time": t, "days": days, "request": req,
                    "auto_approve": bool(x.get("auto_approve", True)), "enabled": bool(x.get("enabled", True)),
                    "last_run": str(x.get("last_run") or "")[:20]})
    return out


def sched_loop():
    while True:
        time.sleep(20)
        try:
            due = []
            with LOCK:
                lt = time.localtime()
                stamp = time.strftime("%Y-%m-%d %H:%M", lt)
                for proj in CFG["projects"]:
                    for sc in proj.get("schedules", []):
                        if (not sc.get("enabled", True) or sc.get("time") != stamp[11:]
                                or lt.tm_wday not in sc.get("days", []) or sc.get("last_run") == stamp):
                            continue
                        sc["last_run"] = stamp
                        due.append((proj, sc))
                dbdue = [p for p in CFG["projects"] if stamp[11:] == DB_AUTO_AT and db_cfg(p).get("prefix")
                         and db_cfg(p).get("auto", True) and db_cfg(p).get("auto_day") != stamp[:10]]
                for p in dbdue:
                    p["db"]["auto_day"] = stamp[:10]
                if due or dbdue:
                    save_cfg()
                for p in dbdue:
                    threading.Thread(target=db_refresh, args=(p, "자동"), daemon=True).start()
                for proj, sc in due:
                    try:
                        job = create_job(proj, sc["request"], source="schedule",
                                         auto_approve=sc.get("auto_approve", True),
                                         title="%s (%s)" % (sc["name"], stamp[5:16]))
                        print("예약 실행: [%s] %s -> %s" % (proj["name"], sc["name"], job["id"]), flush=True)
                    except ApiError as e:
                        print("예약 실행 실패: [%s] %s: %s" % (proj["name"], sc["name"], e.msg), flush=True)
                        notify("[%s] 예약 '%s' 실행 실패: %s" % (proj["name"], sc["name"], e.msg))
        except Exception:  # noqa: BLE001
            traceback.print_exc()


# ---------------------------------------------------------------- 로그인 · 세션 · 접근 제한

def is_local(ip):
    try:
        a = ipaddress.ip_address(ip)
    except ValueError:
        return False
    return a.is_loopback or a.is_private


def prune_sessions():
    t = time.time()
    for k, v in list(SESSIONS.items()):
        if v["exp"] < t:
            SESSIONS.pop(k, None)


def new_session(ip, ext=False):
    prune_sessions()
    tok = secrets.token_urlsafe(32)
    ttl = min(SESS_TTL, sec_cfg()["ext_session_hours"] * 3600) if ext else SESS_TTL
    SESSIONS[tok] = {"ip": ip, "exp": time.time() + ttl, "since": now(), "ext": ext, "ttl": ttl}
    return tok


# ---------------------------------------------------------------- 보안: 차단·스캐너 탐지·2단계 인증
# 외부 요청은 모두 NAS 리버스 프록시를 거쳐 오므로 NAS 방화벽이 아니라 여기서 실제 IP(X-Forwarded-For) 기준으로 막는다.

SEC_FILE = BASE / "security.json"
BAN_STEPS = [86400, 7 * 86400, 0]          # 1일 → 7일 → 영구(0)
LAN_BAN = 900                              # 내부망 기기는 15분만 막는다(본인 기기일 가능성)
SCAN_RE = re.compile(r"(\.php|\.asp|\.jsp|\.cgi|/\.env|/\.git|/\.aws|/\.ssh|wp-|wordpress|phpmyadmin|/admin|/actuator|"
                     r"/cgi-bin|/boaform|/vendor/|/console|/manager/|/solr|/HNAP1|/owa/|/autodiscover|/\.well-known/security|"
                     r"/config\.|/backup|\.sql|\.zip|\.tar|/shell|/setup|/install|/xmlrpc|/server-status|/debug)", re.I)
OPEN_PATHS = {"/", "/login", "/logout", "/favicon.ico", "/robots.txt"}
RATE = {}          # ip -> [시각...] (최근 60초)
MISS = {}          # ip -> [시각...] (비로그인 잘못된 요청, 최근 10분)
FAILS = {}         # ip -> {n, first}
GFAILS = {}        # "all" -> 외부 로그인 실패 시각들 (전체 잠금 판단)
PENDING = {}       # 2단계 인증 대기 토큰 -> {ip, code, exp, tries, ext}
SEC = {"bans": {}, "events": [], "lockdown_until": 0, "proxy_seen": {}}
_SEC_NOTE = {"t": 0, "n": 0}


def sec_load():
    try:
        d = json.loads(SEC_FILE.read_text())
        SEC.update({k: d[k] for k in ("bans", "events", "lockdown_until") if k in d})
    except (OSError, ValueError):
        pass


SEC_LOCK = threading.Lock()


def sec_save():
    with SEC_LOCK:
        try:
            snap = json.loads(json.dumps({k: SEC[k] for k in ("bans", "events", "lockdown_until")}))
            write_json(SEC_FILE, snap)
        except (OSError, RuntimeError, ValueError):
            pass


def send_code(text):
    """2단계 인증 코드는 알림 끄기 설정과 무관하게 연결된 모든 텔레그램 대화로 보낸다."""
    for t in list(tg_cfg()["chats"]):
        NOTIFY.put((t, text, None))


def sec_cfg():
    s = CFG["settings"].setdefault("security", {})
    s.setdefault("two_factor", True)
    s.setdefault("allow", [])
    s.setdefault("ext_session_hours", 12)
    return s


def sec_event(ip, msg, kind="warn"):
    SEC["events"].insert(0, {"ts": now(), "ip": ip, "msg": msg, "kind": kind})
    del SEC["events"][200:]
    print("보안: %s %s" % (ip, msg), flush=True)


def sec_alert(text):
    """텔레그램 경고는 10분에 한 번으로 묶는다(공격이 몰려도 알림 폭탄이 되지 않게)."""
    t = time.time()
    _SEC_NOTE["n"] += 1
    if t - _SEC_NOTE["t"] > 600:
        extra = " (최근 10분간 보안 이벤트 %d건)" % _SEC_NOTE["n"] if _SEC_NOTE["n"] > 1 else ""
        _SEC_NOTE.update(t=t, n=0)
        notify("[보안] " + text + extra)


def ip_ok(ip):
    try:
        ipaddress.ip_address(ip)
        return True
    except ValueError:
        return False


def banned_for(ip):
    """남은 차단 시간(초). 영구 차단은 -1."""
    b = SEC["bans"].get(ip)
    if not b:
        return 0
    if b["until"] == 0:
        return -1
    left = int(b["until"] - time.time())
    if left <= 0:
        return 0
    return left


def ban(ip, reason, lan=False, step=None):
    if not ip_ok(ip):
        return
    b = SEC["bans"].get(ip) or {"n": 0}
    if banned_for(ip):
        return
    if lan:
        until = time.time() + LAN_BAN
    else:
        k = min(len(BAN_STEPS) - 1, max(b["n"], step or 0))
        until = 0 if BAN_STEPS[k] == 0 else time.time() + BAN_STEPS[k]
    b.update(until=until, reason=reason, ts=now(), n=b["n"] + (0 if lan else 1))
    SEC["bans"][ip] = b
    dur = "15분" if lan else ("영구" if until == 0 else "%d일" % round((until - time.time()) / 86400))
    sec_event(ip, "차단(%s): %s" % (dur, reason), "err")
    sec_save()
    if not lan:
        sec_alert("%s 차단(%s): %s\n본인이라면 /unban %s" % (ip, dur, reason, ip))


def unban(ip):
    SEC["bans"].pop(ip, None)
    FAILS.pop(ip, None)
    MISS.pop(ip, None)
    sec_event(ip, "차단 해제(수동)", "ok")
    sec_save()


def recent(store, ip, window):
    t = time.time()
    lst = [x for x in store.get(ip, []) if t - x < window]
    lst.append(t)
    store[ip] = lst
    if len(store) > 5000:          # 메모리 보호
        for k in list(store)[:1000]:
            store.pop(k, None)
    return len(lst)


def allowed_external(ip):
    allow = sec_cfg()["allow"]
    if not allow:
        return True
    try:
        a = ipaddress.ip_address(ip)
        return any(a in ipaddress.ip_network(c, strict=False) for c in allow)
    except ValueError:
        return False


def lockdown_left():
    return max(0, int(SEC.get("lockdown_until", 0) - time.time()))


def blocked_for(ip):
    left = banned_for(ip)
    return 10 ** 9 if left < 0 else left


def note_fail(ip, where, ext=True):
    if not ip_ok(ip):
        return
    t = time.time()
    f = FAILS.get(ip)
    if not f or t - f["first"] > 86400:
        f = FAILS[ip] = {"n": 0, "first": t}
    f["n"] += 1
    LOGINS.insert(0, {"ts": now(), "ip": ip, "ok": False})
    del LOGINS[30:]
    sec_event(ip, "로그인 실패 %d/%d (%s)" % (f["n"], MAX_FAILS, where))
    if f["n"] >= MAX_FAILS:
        FAILS.pop(ip, None)
        ban(ip, "로그인 %d회 실패" % MAX_FAILS, lan=not ext)
    if ext:   # 여러 IP에서 동시에 무차별 대입 → 외부 로그인 전체를 1시간 잠근다
        n = recent(GFAILS, "all", 3600)
        if n >= 20 and not lockdown_left():
            SEC["lockdown_until"] = t + 3600
            sec_event("-", "외부 로그인 1시간 잠금 (1시간 내 실패 %d회)" % n, "err")
            sec_save()
            notify("[보안] 1시간 동안 로그인 실패가 %d회라 외부 로그인을 1시간 잠갔습니다. 내부망 접속은 가능합니다." % n)


def note_ok(ip):
    known = any(x["ok"] and x["ip"] == ip for x in LOGINS)
    FAILS.pop(ip, None)
    LOGINS.insert(0, {"ts": now(), "ip": ip, "ok": True})
    del LOGINS[30:]
    sec_event(ip, "로그인 성공", "ok")
    if not known and not is_local(ip):
        notify("새로운 곳에서 하네스에 로그인했습니다: %s" % ip)


def two_factor_ready():
    return bool(BOT_TOKEN and tg_cfg().get("chats"))


def check_pw(user, pw):
    return (hmac.compare_digest(user.encode(), USER.encode())
            and hmac.compare_digest(pw.encode(), PASSWORD.encode()))


def security_state():
    prune_sessions()
    c = sec_cfg()
    bans = [{"ip": k, "left": banned_for(k), "reason": v.get("reason", ""), "ts": v.get("ts", ""), "n": v.get("n", 0)}
            for k, v in SEC["bans"].items() if banned_for(k)]
    bans.sort(key=lambda x: x["ts"], reverse=True)
    return {"https": PUBLIC_HTTPS, "proxy": TRUST_PROXY, "host": HOST, "public_host": PUBLIC_HOST,
            "sessions": len(SESSIONS), "weak_password": len(PASSWORD) < 12, "max_fails": MAX_FAILS,
            "blocked": bans[:100], "blocked_total": len(bans), "events": SEC["events"][:40],
            "recent": LOGINS[:10], "two_factor": c["two_factor"], "two_factor_ready": two_factor_ready(),
            "allow": c["allow"], "ext_session_hours": c["ext_session_hours"], "lockdown": lockdown_left(),
            "proxy_seen": SEC["proxy_seen"]}


def security_update(b):
    c = sec_cfg()
    if "two_factor" in b:
        c["two_factor"] = bool(b["two_factor"])
    if "allow" in b:
        out = []
        for x in re.split(r"[\s,]+", str(b["allow"] or "")):
            if not x:
                continue
            try:
                out.append(str(ipaddress.ip_network(x, strict=False)))
            except ValueError:
                raise ApiError(400, "IP/대역 형식이 올바르지 않습니다: %s" % x[:40])
        c["allow"] = out[:50]
    if "ext_session_hours" in b:
        try:
            c["ext_session_hours"] = max(1, min(24 * 30, int(b["ext_session_hours"])))
        except (TypeError, ValueError):
            raise ApiError(400, "숫자를 입력하세요")
    if b.get("unban"):
        unban(str(b["unban"])[:45])
    if b.get("unban_all"):
        SEC["bans"].clear()
        sec_event("-", "전체 차단 해제(수동)", "ok")
        sec_save()
    if b.get("unlock"):
        SEC["lockdown_until"] = 0
        sec_event("-", "외부 로그인 잠금 해제(수동)", "ok")
        sec_save()
    save_cfg()
    return security_state()


LOGIN_HTML = """<!doctype html><html lang="ko"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>에이전트 하네스 로그인</title><style>
:root{color-scheme:light dark;--bg:#f6f5f2;--panel:#fff;--ink:#1d1d1b;--mute:#6b6a65;--line:#e4e2dc;--accent:#2f5d50;--accent-ink:#fff;--err:#b83232}
@media (prefers-color-scheme:dark){:root{--bg:#171715;--panel:#201f1d;--ink:#ecebe6;--mute:#9a988f;--line:#34332f;--accent:#7fb7a4;--accent-ink:#10201a;--err:#ef7a7a}}
body{margin:0;min-height:100vh;display:flex;align-items:center;justify-content:center;background:var(--bg);color:var(--ink);
font:15px/1.6 -apple-system,"Apple SD Gothic Neo","Noto Sans KR",system-ui,sans-serif}
form{background:var(--panel);border:1px solid var(--line);border-radius:14px;padding:26px;width:min(360px,92vw)}
h1{font-size:17px;margin:0 0 4px}p.s{color:var(--mute);font-size:13px;margin:0 0 18px}
label{display:block;font-size:13px;color:var(--mute);margin-bottom:12px}
input{width:100%;box-sizing:border-box;font:inherit;color:var(--ink);background:var(--bg);border:1px solid var(--line);border-radius:8px;padding:10px;margin-top:4px}
button{width:100%;font:inherit;font-weight:600;cursor:pointer;border:0;border-radius:8px;padding:11px;background:var(--accent);color:var(--accent-ink);margin-top:6px}
.e{color:var(--err);font-size:13px;margin:0 0 12px}
</style></head><body><form method="post" action="/login" autocomplete="on">
<h1>에이전트 하네스</h1><p class="s">@SUB@</p>@ERR@
@FIELDS@</form></body></html>"""
LOGIN_FIELDS = """<label>아이디<input name="user" autocomplete="username" autofocus></label>
<label>비밀번호<input name="password" type="password" autocomplete="current-password"></label>
<button type="submit">로그인</button>"""
CODE_FIELDS = """<label>텔레그램으로 받은 6자리 확인 코드<input name="code" inputmode="numeric" pattern="[0-9]{6}" maxlength="6"
autocomplete="one-time-code" autofocus></label><button type="submit">확인</button>
<p class="s" style="margin-top:12px"><a href="/login" style="color:inherit">처음부터 다시</a></p>"""

# ---------------------------------------------------------------- HTTP

ROUTES = []


def route(method, pattern, lock=True):
    def deco(fn):
        ROUTES.append((method, re.compile("^" + pattern + "$"), fn, lock))
        return fn
    return deco


@route("GET", r"/api/projects")
def r_projects(m, b):
    return {"projects": [psummary(p) for p in CFG["projects"]], "settings": CFG["settings"], "flags": FLAGS,
            "queue": {"waiting": QUEUE.qsize(), "running": RUNNING}}


# ---------------------------------------------------------------- Claude 구독 사용량 (Claude Code /usage 와 같은 값)
# 공식 문서에 없는 내부 주소라 바뀔 수 있다. 실패하면 화면에서 조용히 숨긴다(하네스 동작과 무관).
USAGE_URL = os.environ.get("CLAUDE_USAGE_URL", "https://api.anthropic.com/api/oauth/usage")
USAGE_CACHE = {"t": 0, "v": None}


def _usage_window(d):
    if not isinstance(d, dict):
        return None
    pct = d.get("utilization", d.get("used_percentage"))
    if pct is None:
        return None
    r = d.get("resets_at") or d.get("reset_at")
    ts = None
    if isinstance(r, (int, float)):
        ts = r / 1000 if r > 1e12 else r
    elif isinstance(r, str) and r:
        try:
            from datetime import datetime
            ts = datetime.fromisoformat(r.replace("Z", "+00:00")).timestamp()
        except ValueError:
            ts = None
    return {"pct": round(float(pct)), "reset": int(ts) if ts else None}


def claude_usage(force=False):
    if not force and time.time() - USAGE_CACHE["t"] < 300:
        return USAGE_CACHE["v"]
    USAGE_CACHE["t"] = time.time()
    out = None
    try:
        cred = json.loads((Path.home() / ".claude" / ".credentials.json").read_text())
        oa = cred.get("claudeAiOauth") or {}
        tok = oa.get("accessToken")
        if tok and (not oa.get("expiresAt") or oa["expiresAt"] / 1000 > time.time()):
            req = urllib.request.Request(USAGE_URL, headers={
                "Authorization": "Bearer " + tok, "anthropic-beta": "oauth-2025-04-20",
                "Accept": "application/json", "User-Agent": "agent-harness"})
            with urllib.request.urlopen(req, timeout=10) as r:
                d = json.loads(r.read().decode("utf-8"))
            five = _usage_window(d.get("five_hour") or (d.get("rate_limits") or {}).get("five_hour"))
            week = _usage_window(d.get("seven_day") or (d.get("rate_limits") or {}).get("seven_day"))
            if five or week:
                out = {"session": five, "week": week, "ts": now()}
    except Exception:  # noqa: BLE001 - 표시용 부가 기능이라 실패해도 무시
        out = None
    if out or not USAGE_CACHE["v"]:
        USAGE_CACHE["v"] = out
    return USAGE_CACHE["v"]


@route("GET", r"/api/usage", lock=False)
def r_usage(m, b):
    return {"usage": claude_usage()}


@route("GET", r"/api/presets")
def r_presets(m, b):
    return {"presets": PRESETS}


@route("POST", r"/api/projects")
def r_project_create(m, b):
    return project_create(b)


@route("GET", r"/api/projects/([^/]+)")
def r_project_get(m, b):
    return project_detail(proj_of(m[1]))


@route("POST", r"/api/projects/([^/]+)/update")
def r_project_update(m, b):
    return project_update(proj_of(m[1]), b)


@route("POST", r"/api/projects/([^/]+)/delete")
def r_project_delete(m, b):
    return project_delete(proj_of(m[1]))


@route("POST", r"/api/projects/([^/]+)/stages")
def r_stages(m, b):
    proj = proj_of(m[1])
    proj["stages"] = validate_stages(proj, b.get("stages"))
    save_cfg()
    return project_detail(proj)


@route("POST", r"/api/projects/([^/]+)/apply-plan")
def r_apply(m, b):
    proj = proj_of(m[1])
    try:
        plan = norm_plan(b.get("plan"), 10, 8)
    except ValueError as e:
        raise ApiError(400, str(e))
    apply_plan(proj, plan)
    save_cfg()
    return project_detail(proj)


@route("POST", r"/api/projects/([^/]+)/agents")
def r_agent_create(m, b):
    return agent_create(proj_of(m[1]), b)


@route("GET", r"/api/projects/([^/]+)/agents/([^/]+)")
def r_agent_get(m, b):
    proj = proj_of(m[1])
    return agent_info(proj, agent_of(proj, m[2]), True)


@route("POST", r"/api/projects/([^/]+)/agents/([^/]+)/save")
def r_agent_save(m, b):
    proj = proj_of(m[1])
    return agent_save(proj, agent_of(proj, m[2]), b)


@route("POST", r"/api/projects/([^/]+)/agents/([^/]+)/remove")
def r_agent_remove(m, b):
    proj = proj_of(m[1])
    return agent_remove(proj, agent_of(proj, m[2]))


@route("POST", r"/api/projects/([^/]+)/agents/([^/]+)/rename-folder")
def r_agent_rename(m, b):
    proj = proj_of(m[1])
    return rename_agent_folder(proj, agent_of(proj, m[2]))


@route("POST", r"/api/projects/([^/]+)/agents/rename-all")
def r_agents_rename_all(m, b):
    proj = proj_of(m[1])
    return {"results": [{"name": a["name"]} | rename_agent_folder(proj, a) for a in proj["agents"]]}


@route("GET", r"/api/projects/([^/]+)/jobs")
def r_jobs(m, b):
    proj = proj_of(m[1])
    js = sorted((j for (pid, _), j in JOBS.items() if pid == proj["id"]), key=lambda j: j["created"], reverse=True)
    return {"jobs": [job_summary(j) for j in js[:80]]}


@route("POST", r"/api/projects/([^/]+)/jobs")
def r_job_create(m, b):
    return job_summary(create_job(proj_of(m[1]), b.get("request"), files=b.get("files")))


@route("GET", r"/api/projects/([^/]+)/jobs/([^/]+)")
def r_job_get(m, b):
    proj = proj_of(m[1])
    return job_detail(proj, job_of(proj, m[2]))


@route("POST", r"/api/projects/([^/]+)/jobs/delete-many")
def r_job_delete_many(m, b):
    return job_delete_many(proj_of(m[1]), b)


@route("POST", r"/api/projects/([^/]+)/jobs/([^/]+)/(approve|restart|cancel|delete|edit|followup|revert)", lock=False)
def r_job_action(m, b):
    proj = proj_of(m[1])
    j = job_of(proj, m[2])
    fn = {"approve": lambda: job_approve(proj, j), "restart": lambda: job_restart(proj, j, b),
            "cancel": lambda: job_cancel(proj, j), "delete": lambda: job_delete(proj, j),
            "edit": lambda: job_edit(proj, j, b), "followup": lambda: job_followup(proj, j, b),
           "revert": lambda: repo_revert(proj, j)}[m[3]]
    if m[3] == "revert":   # git 작업이라 오래 걸릴 수 있어 전체 잠금 없이 실행
        return fn()
    with LOCK:
        return fn()


@route("POST", r"/api/plan", lock=False)
def r_plan(m, b):
    name = str(b.get("name") or "").strip()[:40]
    desc = str(b.get("description") or "").strip()[:2000]
    if not desc and not name:
        raise ApiError(400, "프로젝트 이름이나 설명을 입력하세요")
    try:
        ws = max(0, min(8, int(b.get("stages") or 0)))
        wa = max(0, min(6, int(b.get("agents") or 0)))
    except (TypeError, ValueError):
        raise ApiError(400, "단계 수가 올바르지 않습니다")
    return ai_plan(name or "(이름 없음)", desc or "(설명 없음)", ws, wa)


@route("GET", r"/api/projects/([^/]+)/sources")
def r_sources(m, b):
    proj = proj_of(m[1])
    return {"sources": src_list(proj), "mode": proj.get("use_sources", "prefer"),
            "dir": str(proj_dirs(proj)["sources"])}


@route("POST", r"/api/projects/([^/]+)/sources")
def r_source_save(m, b):
    proj = proj_of(m[1])
    content = b.get("content")
    if not isinstance(content, str) or not content.strip():
        raise ApiError(400, "자료 내용을 입력하세요")
    if len(content) > 300_000:
        raise ApiError(400, "자료가 너무 깁니다 (30만 자 제한)")
    p = src_path(proj, b.get("name"))
    if not p.exists() and len(src_list(proj)) >= SRC_MAX:
        raise ApiError(400, "자료는 %d개까지 등록할 수 있습니다" % SRC_MAX)
    p.write_text(content.rstrip() + "\n")
    return {"sources": src_list(proj)}


@route("POST", r"/api/projects/([^/]+)/sources/read")
def r_source_read(m, b):
    proj = proj_of(m[1])
    p = src_path(proj, b.get("name"))
    t = read_text(p, 300_000)
    if t is None:
        raise ApiError(404, "자료를 찾을 수 없습니다")
    return {"name": p.name, "content": t}


@route("POST", r"/api/projects/([^/]+)/sources/delete")
def r_source_delete(m, b):
    proj = proj_of(m[1])
    src_path(proj, b.get("name")).unlink(missing_ok=True)
    return {"sources": src_list(proj)}


@route("POST", r"/api/projects/([^/]+)/sources/mode")
def r_source_mode(m, b):
    proj = proj_of(m[1])
    mode = str(b.get("mode") or "")
    if mode not in ("off", "prefer", "only"):
        raise ApiError(400, "자료 사용 방식이 올바르지 않습니다")
    proj["use_sources"] = mode
    save_cfg()
    return {"mode": mode}


@route("GET", r"/api/projects/([^/]+)/db")
def r_db(m, b):
    return db_status(proj_of(m[1]))


@route("POST", r"/api/projects/([^/]+)/db")
def r_db_save(m, b):
    proj = proj_of(m[1])
    pre = str(b.get("prefix") or "").strip().upper()
    if pre and not DB_PREFIX_RE.match(pre):
        raise ApiError(400, "환경 변수 접두어는 영문 대문자·숫자·밑줄만 쓸 수 있습니다 (예: MYMA_DB)")
    ct = str(b.get("code_tables") or "").strip()[:200]
    if not re.match(r"^[\w*?, ]*$", ct):
        raise ApiError(400, "코드 테이블은 이름이나 패턴을 쉼표로 구분해 적으세요 (예: CM*, ZZ_CODE)")
    with LOCK:
        d = proj.setdefault("db", {})
        d.update({"prefix": pre, "code_tables": ct or "CM*", "auto": bool(b.get("auto", True))})
        save_cfg()
    return db_status(proj)


@route("POST", r"/api/projects/([^/]+)/db/refresh", lock=False)  # 수 초 걸리므로 전체 잠금 없이
def r_db_refresh(m, b):
    proj = proj_of(m[1])
    db_refresh(proj)
    return db_status(proj)


@route("GET", r"/api/projects/([^/]+)/db/readme")
def r_db_readme(m, b):
    t = read_text(db_dir(proj_of(m[1])) / "README.md", 300_000)
    if t is None:
        raise ApiError(404, "아직 가져온 DB 구조 자료가 없습니다")
    return {"content": t}


@route("GET", r"/api/all-agents")
def r_all_agents(m, b):
    out = []
    for p in CFG["projects"]:
        for a in p["agents"]:
            ws = proj_dirs(p)["root"] / a["workspace"]
            role = role_text(read_text(ws / "CLAUDE.md", 3000))
            out.append({"pid": p["id"], "pname": p["name"], "id": a["id"], "name": a["name"],
                        "model": a.get("model", ""), "role": role[:1500],
                        "web": parse_perms(ws / ".claude" / "settings.json").get("web", False)})
    return {"agents": out}


def import_agent(proj, src, a, name=None):
    ws = proj_dirs(src)["root"] / a["workspace"]
    role = read_text(ws / "CLAUDE.md", 50000) or ""
    perms = parse_perms(ws / ".claude" / "settings.json")
    new = create_agent_in(proj, name or a["name"], "", perms, a.get("model", ""))
    if role.strip():
        (proj_dirs(proj)["root"] / new["workspace"] / "CLAUDE.md").write_text(role.rstrip() + "\n")
    return new


@route("POST", r"/api/projects/([^/]+)/agents/import")
def r_agent_import(m, b):
    proj = proj_of(m[1])
    src = proj_of(str(b.get("from") or ""))
    a = agent_of(src, str(b.get("agent") or ""))
    name = str(b.get("name") or a["name"]).strip()[:30] or a["name"]
    new = import_agent(proj, src, a, name)
    save_cfg()
    return {"agent": agent_info(proj, new),
            "note": "'%s' 프로젝트의 %s 를 복사해 왔습니다. 여기서 고쳐도 원본에는 영향이 없습니다." % (src["name"], a["name"])}


@route("POST", r"/api/projects/([^/]+)/schedules")
def r_schedules(m, b):
    proj = proj_of(m[1])
    proj["schedules"] = validate_schedules(b.get("schedules"))
    save_cfg()
    return project_detail(proj)


@route("GET", r"/api/security")
def r_security(m, b):
    return security_state()


@route("POST", r"/api/security")
def r_security_update(m, b):
    return security_update(b)


@route("POST", r"/api/security/logout-all")
def r_logout_all(m, b):
    SESSIONS.clear()
    return {"ok": True}


@route("GET", r"/api/telegram")
def r_tg(m, b):
    t = tg_cfg()
    return {"configured": bool(BOT_TOKEN), "pair_code": PAIR_CODE if BOT_TOKEN else "",
            "chats": t["chats"], "notify": t.get("notify", True),
            "cur": {k: agent_name_safe(v) for k, v in t["cur"].items()}}


@route("POST", r"/api/telegram/update")
def r_tg_update(m, b):
    t = tg_cfg()
    if "notify" in b:
        t["notify"] = bool(b["notify"])
    if b.get("unpair"):
        c = str(b["unpair"])
        t["chats"] = [x for x in t["chats"] if x != c]
        t["cur"].pop(c, None)
    save_cfg()
    return r_tg(m, b)


@route("POST", r"/api/telegram/test", lock=False)
def r_tg_test(m, b):
    if not BOT_TOKEN:
        raise ApiError(400, "TELEGRAM_BOT_TOKEN 이 설정되지 않았습니다")
    with LOCK:
        chats = list(tg_cfg()["chats"])
    if not chats:
        raise ApiError(400, "연결된 대화가 없습니다. 봇에게 /pair 코드 를 보내 연결하세요")
    try:
        for c in chats:
            tg_send(c, "에이전트 하네스 테스트 메시지입니다.")
    except Exception as e:  # noqa: BLE001
        raise ApiError(502, "전송 실패: %s" % str(e)[:200])
    return {"sent": len(chats)}


@route("GET", r"/api/projects/([^/]+)/repo")
def r_repo(m, b):
    return repo_status(proj_of(m[1]))


@route("POST", r"/api/projects/([^/]+)/repo")
def r_repo_save(m, b):
    return repo_save(proj_of(m[1]), b)


@route("POST", r"/api/projects/([^/]+)/repo/clone", lock=False)
def r_repo_clone(m, b):
    with LOCK:
        proj = proj_of(m[1])
    return repo_clone(proj, str(b.get("id") or ""))


@route("POST", r"/api/projects/([^/]+)/repo/release", lock=False)
def r_repo_release(m, b):
    with LOCK:
        proj = proj_of(m[1])
        job = job_of(proj, str(b["job"])) if b.get("job") else None
    return repo_promote(proj, job=job)


@route("POST", r"/api/projects/([^/]+)/repo/rollback", lock=False)
def r_repo_rollback(m, b):
    with LOCK:
        proj = proj_of(m[1])
    return repo_rollback(proj, b.get("idx"), "before" if b.get("which") == "before" else "heads")


@route("POST", r"/api/projects/([^/]+)/repo/key", lock=False)
def r_repo_key(m, b):
    with LOCK:
        proj = proj_of(m[1])
    try:
        return repo_key(proj, str(b.get("id") or ""))
    except ApiError:
        raise
    except Exception as e:  # noqa: BLE001
        raise ApiError(500, "키 생성 실패: %s" % str(e)[:200])


@route("POST", r"/api/merge-projects")
def r_projects_merge(m, b):
    return merge_projects(b)


@route("POST", r"/api/settings")
def r_settings(m, b):
    return settings_update(b)


class Handler(BaseHTTPRequestHandler):
    server_version = "-"     # 서버 종류·버전을 드러내지 않는다
    sys_version = ""
    timeout = 20             # 느리게 보내며 연결을 붙잡는 공격(slowloris) 방지

    def log_message(self, *a):
        pass

    auth = None

    def ip(self):
        peer = self.client_address[0]
        if TRUST_PROXY and is_local(peer) and (not TRUST_PROXY_IPS or peer in TRUST_PROXY_IPS):
            xff = self.headers.get("X-Forwarded-For")
            if xff:
                return xff.split(",")[-1].strip()[:45]   # 프록시가 마지막에 붙인 값이 실제 접속 IP
        return peer

    def is_ext(self):
        """공개 도메인으로 들어왔거나 사설망 밖 IP면 외부 접속으로 본다."""
        host = (self.headers.get("Host") or "").split(":")[0]
        return bool(PUBLIC_HOST and host == PUBLIC_HOST) or not is_local(self.ip())

    def shield(self):
        """모든 요청의 첫 관문: 차단 IP, 허용 목록, 요청 폭주, 취약점 스캔 경로."""
        ip, ext, path = self.ip(), self.is_ext(), urlparse(self.path).path
        host = (self.headers.get("Host") or "").split(":")[0]
        if PUBLIC_HOST and host == PUBLIC_HOST:
            SEC["proxy_seen"] = {"ts": now(), "xff": bool(self.headers.get("X-Forwarded-For")), "ip": ip}
        if ext and is_local(ip):
            # 프록시가 실제 IP를 넘겨주지 않음: NAS를 막으면 전부 막히므로 차단 대신 경고만
            self.can_ban = False
        else:
            self.can_ban = True
        if self.can_ban and banned_for(ip):
            self.close_connection = True
            self.send_response(403)
            self.send_header("Content-Length", "0")
            self.send_header("Connection", "close")
            self.end_headers()
            return False
        if ext and not allowed_external(ip):
            self.send(403, "접속이 허용되지 않은 위치입니다.", "text/plain; charset=utf-8")
            return False
        n = recent(RATE, ip, 60)
        if n > 600 and self.can_ban:
            ban(ip, "요청 폭주 (1분에 %d회)" % n, lan=not ext)
            return False
        if n > 300:
            self.send(429, json.dumps({"error": "요청이 너무 많습니다. 잠시 후 다시 시도하세요"}))
            return False
        if SCAN_RE.search(path) and not self.has_session():
            if self.can_ban:
                ban(ip, "취약점 스캔 경로 접근: %s" % path[:60], lan=not ext, step=1)
            self.send(404, "", "text/plain; charset=utf-8")
            return False
        return True

    def has_session(self):
        sess = SESSIONS.get(self.cookie("ah_sess") or "")
        return bool(sess and sess["exp"] > time.time())

    def miss(self):
        """로그인 안 된 상태로 없는 경로를 계속 찌르면 스캐너로 보고 차단한다."""
        ip, ext = self.ip(), self.is_ext()
        n = recent(MISS, ip, 600)
        if n >= 8 and self.can_ban:
            ban(ip, "없는 경로를 반복 요청 (10분에 %d회)" % n, lan=not ext)
        self.send(404, "", "text/plain; charset=utf-8")

    def cookie(self, name):
        raw = self.headers.get("Cookie")
        if not raw:
            return None
        try:
            c = http.cookies.SimpleCookie(raw)
        except http.cookies.CookieError:
            return None
        return c[name].value if name in c else None

    def send(self, code, body, ctype="application/json; charset=utf-8", extra=None):
        data = body if isinstance(body, bytes) else body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("X-Frame-Options", "DENY")
        self.send_header("Referrer-Policy", "same-origin")   # no-referrer 는 Origin 을 null 로 만들어 POST 가 막힌다
        if PUBLIC_HTTPS:
            self.send_header("Strict-Transport-Security", "max-age=31536000")
        for k, v in (extra or {}).items():
            for x in (v if isinstance(v, list) else [v]):
                self.send_header(k, x)
        self.end_headers()
        self.wfile.write(data)

    def js(self, code, obj):
        self.send(code, json.dumps(obj, ensure_ascii=False))

    def gate(self):
        """세션 쿠키 또는 기본 인증(내부망만). 실패는 횟수 제한으로 막는다."""
        ip = self.ip()
        tok = self.cookie("ah_sess")
        if tok:
            sess = SESSIONS.get(tok)
            if sess and sess["exp"] > time.time():
                self.auth = "cookie"
                return True
        a = self.headers.get("Authorization", "")
        if a.startswith("Basic ") and self.is_ext():
            # 기본 인증은 2단계 인증을 우회하므로 외부에서는 받지 않는다
            note_fail(ip, "외부 기본 인증 시도", True)
            self.send(401, json.dumps({"error": "외부에서는 로그인 화면으로만 접속할 수 있습니다"}))
            return False
        if a.startswith("Basic "):
            try:
                u, p = base64.b64decode(a[6:]).decode("utf-8").split(":", 1)
            except Exception:  # noqa: BLE001
                u = p = ""
            if check_pw(u, p):
                self.auth = "basic"
                return True
            note_fail(ip, "기본 인증", self.is_ext())
            self.send(401, json.dumps({"error": "아이디 또는 비밀번호가 올바르지 않습니다"}))
            return False
        path = urlparse(self.path).path
        if path.startswith("/api/"):
            self.send(401, json.dumps({"error": "로그인이 필요합니다"}))
        elif path in OPEN_PATHS:
            self.send(303, "", "text/plain; charset=utf-8", {"Location": "/login"})
        else:
            self.miss()
        return False

    def login_page(self, err="", code=False):
        ip = self.ip()
        if self.is_ext() and lockdown_left():
            err = "외부 로그인이 일시적으로 잠겨 있습니다 (%d분 남음)." % (lockdown_left() // 60 + 1)
        sub = "이 서버는 에이전트를 실행합니다. 본인만 로그인하세요."
        if code:
            sub = "2단계 인증: 텔레그램으로 보낸 확인 코드를 입력하세요. (5분 안에)"
        html = LOGIN_HTML.replace("@SUB@", sub).replace("@FIELDS@", CODE_FIELDS if code else LOGIN_FIELDS).replace(
            "@ERR@", ('<p class="e">%s</p>' % err.replace("<", "&lt;")) if err else "")
        self.send(200, html,
                  "text/html; charset=utf-8",
                  {"Content-Security-Policy": "default-src 'none'; style-src 'unsafe-inline'; form-action 'self'; frame-ancestors 'none'"})

    def finish_login(self, ip, ext):
        note_ok(ip)
        tok = new_session(ip, ext)
        # 공개 도메인(https)으로 들어왔을 때만 Secure 쿠키를 쓴다. 내부 IP(http)에 Secure를 붙이면
        # 브라우저가 쿠키 저장을 거부해 로그인이 계속 풀린다.
        req_host = (self.headers.get("Host") or "").split(":")[0]
        flags = "; Secure" if (PUBLIC_HTTPS and PUBLIC_HOST and req_host == PUBLIC_HOST) else ""
        self.send(303, "", "text/plain; charset=utf-8",
                  {"Location": "/", "Set-Cookie": ["ah_sess=%s; Path=/; HttpOnly; SameSite=Lax; Max-Age=%d%s"
                                                   % (tok, SESSIONS[tok]["ttl"], flags),
                                                   "ah_pend=; Path=/login; HttpOnly; Max-Age=0"]})

    def do_login(self):
        ip, ext = self.ip(), self.is_ext()
        if ext and lockdown_left():
            return self.login_page()
        origin = self.headers.get("Origin")
        if origin and urlparse(origin).netloc not in {self.headers.get("Host"), PUBLIC_HOST}:
            return self.send(403, "허용되지 않은 출처", "text/plain; charset=utf-8")
        n = int(self.headers.get("Content-Length") or 0)
        if n > 4000:
            return self.login_page("입력이 너무 깁니다.")
        from urllib.parse import parse_qs
        f = parse_qs(self.rfile.read(n).decode("utf-8", "replace"))
        if "code" in f:                                   # 2단계: 텔레그램 코드 확인
            pt = self.cookie("ah_pend") or ""
            pend = PENDING.get(pt)
            if not pend or pend["exp"] < time.time() or pend["ip"] != ip:
                PENDING.pop(pt, None)
                return self.login_page("확인이 만료됐거나 접속 위치가 바뀌었습니다. 처음부터 다시 로그인하세요.")
            if not hmac.compare_digest((f.get("code") or [""])[0].strip(), pend["code"]):
                pend["tries"] += 1
                if pend["tries"] >= 3:
                    PENDING.pop(pt, None)
                    note_fail(ip, "2단계 코드 3회 오류", ext)
                    return self.login_page("코드가 3번 틀렸습니다. 처음부터 다시 로그인하세요.")
                return self.login_page("코드가 올바르지 않습니다. (%d/3)" % pend["tries"], code=True)
            PENDING.pop(pt, None)
            return self.finish_login(ip, ext)
        if not check_pw((f.get("user") or [""])[0], (f.get("password") or [""])[0]):
            note_fail(ip, "로그인 화면", ext)
            if banned_for(ip):
                self.close_connection = True
                return self.send(403, "", "text/plain; charset=utf-8")
            left = MAX_FAILS - (FAILS.get(ip) or {"n": 0})["n"]
            return self.login_page("아이디 또는 비밀번호가 올바르지 않습니다. (%d번 더 틀리면 차단)" % left)
        if ext and sec_cfg()["two_factor"] and two_factor_ready():
            for k in [k for k, v in PENDING.items() if v["exp"] < time.time()]:
                PENDING.pop(k, None)
            pt, code = secrets.token_urlsafe(24), "%06d" % secrets.randbelow(10 ** 6)
            PENDING[pt] = {"ip": ip, "code": code, "exp": time.time() + 300, "tries": 0}
            send_code("[하네스 로그인 확인] 코드: %s\n접속 IP: %s\n본인이 아니면 무시하고 비밀번호를 바꾸세요. (5분간 유효)" % (code, ip))
            sec_event(ip, "비밀번호 확인, 2단계 코드 발송")
            self.send(303, "", "text/plain; charset=utf-8",
                      {"Location": "/login?step=2",
                       "Set-Cookie": "ah_pend=%s; Path=/login; HttpOnly; SameSite=Strict; Max-Age=300%s"
                                     % (pt, "; Secure" if PUBLIC_HTTPS else "")})
            return
        self.finish_login(ip, ext)

    def dispatch(self, method, body):
        path = urlparse(self.path).path
        for meth, rx, fn, lock in ROUTES:
            if meth != method:
                continue
            m = rx.match(path)
            if not m:
                continue
            try:
                if lock:
                    with LOCK:
                        res = fn((None,) + m.groups(), body)
                else:
                    res = fn((None,) + m.groups(), body)
                return self.js(200, res)
            except ApiError as e:
                return self.js(e.code, {"error": e.msg})
            except Exception:  # noqa: BLE001
                traceback.print_exc()
                return self.js(500, {"error": "서버 내부 오류 (서버 터미널 로그를 확인하세요)"})
        self.js(404, {"error": "없는 경로"})

    def do_GET(self):
        if not self.shield():
            return
        path = urlparse(self.path).path
        if path == "/login":
            q = urlparse(self.path).query
            return self.login_page(code=(q == "step=2" and bool(self.cookie("ah_pend"))))
        if path in ("/favicon.ico", "/robots.txt"):
            return self.send(200 if path == "/robots.txt" else 204, "User-agent: *\nDisallow: /\n" if path == "/robots.txt" else "",
                             "text/plain; charset=utf-8")
        if path == "/logout":
            SESSIONS.pop(self.cookie("ah_sess") or "", None)
            return self.send(303, "", "text/plain; charset=utf-8",
                             {"Location": "/login", "Set-Cookie": "ah_sess=; Path=/; HttpOnly; SameSite=Strict; Max-Age=0"})
        if not self.gate():
            return
        m = re.match(r"^/api/projects/([^/]+)/jobs/([^/]+)/files/([^/]+)$", path)
        if m:
            return self.send_attachment(*m.groups())
        if path == "/":
            return self.send(200, INDEX_HTML, "text/html; charset=utf-8",
                             {"Content-Security-Policy": "default-src 'self'; img-src 'self' blob:; style-src 'unsafe-inline'; script-src 'unsafe-inline'; frame-ancestors 'none'"})
        self.dispatch("GET", {})

    def send_attachment(self, pid, jid, name):
        from urllib.parse import unquote
        name = unquote(name)
        try:
            with LOCK:
                proj = proj_of(pid)
                job_of(proj, jid)
        except ApiError as e:
            return self.js(e.code, {"error": e.msg})
        f = att_dir(proj, jid) / Path(name).name
        if not f.is_file() or f.resolve().parent != att_dir(proj, jid).resolve():
            return self.js(404, {"error": "파일 없음"})
        ext = f.suffix.lower().lstrip(".")
        ctype = {"png": "image/png", "jpg": "image/jpeg", "jpeg": "image/jpeg", "gif": "image/gif", "webp": "image/webp",
                 "pdf": "application/pdf"}.get(ext, "text/plain; charset=utf-8")
        disp = "inline" if ext in ATT_IMG or ext == "pdf" else "attachment"
        from urllib.parse import quote
        self.send(200, f.read_bytes(), ctype, {"Content-Disposition": "%s; filename*=UTF-8''%s" % (disp, quote(f.name)),
                                               "Content-Security-Policy": "default-src 'none'; img-src 'self'; style-src 'unsafe-inline'; sandbox"})

    def do_HEAD(self):
        if self.shield():
            self.send(405, "", "text/plain; charset=utf-8")

    def do_POST(self):
        if not self.shield():
            return
        if urlparse(self.path).path == "/login":
            return self.do_login()
        if not self.gate():
            return
        origin = self.headers.get("Origin")
        ok_hosts = {self.headers.get("Host"), self.headers.get("X-Forwarded-Host"), PUBLIC_HOST}
        if self.auth == "cookie" and not origin:
            return self.js(403, {"error": "출처 헤더가 없는 요청은 거부합니다"})
        if origin and urlparse(origin).netloc not in ok_hosts:
            return self.js(403, {"error": "허용되지 않은 출처"})
        if "application/json" not in (self.headers.get("Content-Type") or ""):
            return self.js(415, {"error": "JSON만 허용"})
        try:
            n = int(self.headers.get("Content-Length") or 0)
            big = re.match(r"^/api/projects/[^/]+/jobs(/[^/]+/(edit|followup))?$", urlparse(self.path).path)
            if n > (30_000_000 if big else 300_000):
                return self.js(413, {"error": "요청이 너무 큼"})
            body = json.loads(self.rfile.read(n) or b"{}")
            if not isinstance(body, dict):
                raise ValueError
        except Exception:  # noqa: BLE001
            return self.js(400, {"error": "JSON 형식 오류"})
        self.dispatch("POST", body)


def recover():
    for proj in CFG["projects"]:
        ensure_dirs(proj)
        for p in sorted(proj_dirs(proj)["jobs"].glob("*.json")):
            try:
                j = json.loads(p.read_text())
            except ValueError:
                continue
            j["pid"] = proj["id"]
            j.setdefault("usage", {})
            j.setdefault("needs_input", False)
            j.setdefault("question", "")
            if j.get("status") == "deploying":
                j["status"], j["error"] = "awaiting_user", "서버 재시작으로 저장소 반영이 중단됨. 다시 승인하세요"
                write_json(p, j)
            if j.get("status") in ("queued", "running"):
                j["status"] = "failed"
                j["error"] = "서버가 재시작되어 중단됨"
                j["events"].append({"ts": now(), "agent": "system", "msg": "서버 재시작으로 중단됨. 다시 시작하세요", "kind": "err"})
                write_json(p, j)
            JOBS[(proj["id"], j["id"])] = j


def main():
    if not PASSWORD:
        sys.exit("GUI_PASSWORD 가 설정되지 않았습니다. %s/.env 에 GUI_PASSWORD=원하는비밀번호 를 추가하세요." % BASE)
    load_cfg()
    for pj in CFG["projects"]:   # 권한 규칙이 바뀐 버전으로 올라와도 기존 에이전트 설정에 반영
        try:
            refresh_agent_settings(pj)
        except Exception:  # noqa: BLE001
            traceback.print_exc()
    sec_load()
    recover()
    probe_flags()
    for _ in range(3):
        threading.Thread(target=worker, daemon=True).start()
    threading.Thread(target=sched_loop, daemon=True).start()
    if BOT_TOKEN:
        threading.Thread(target=tg_sender, daemon=True).start()
        threading.Thread(target=tg_loop, daemon=True).start()
    else:
        print("텔레그램: TELEGRAM_BOT_TOKEN 이 없어 봇 기능은 꺼져 있습니다", flush=True)
    srv = ThreadingHTTPServer((HOST, PORT), Handler)
    signal.signal(signal.SIGTERM, lambda *a: (_ for _ in ()).throw(SystemExit(0)))
    on = [k for k, v in FLAGS.items() if v]
    print("에이전트 하네스 GUI: http://%s:%d  (사용자: %s)" % (HOST, PORT, USER), flush=True)
    if PUBLIC_HOST:
        print("공개 주소: https://%s" % PUBLIC_HOST, flush=True)
    if len(PASSWORD) < 12:
        print("경고: GUI_PASSWORD 가 %d자입니다. 인터넷에 공개한다면 12자 이상으로 바꾸세요." % len(PASSWORD), flush=True)
    if HOST not in ("127.0.0.1", "localhost", "::1") and not PUBLIC_HTTPS:
        print("경고: 암호화 없이 외부에 열려 있습니다. 리버스 프록시(HTTPS)를 두고 GUI_HOST=127.0.0.1 로 되돌리세요.",
              flush=True)
    print("토큰 절감 옵션 감지: %s" % (", ".join(on) or "없음"), flush=True)
    try:
        srv.serve_forever()
    except (KeyboardInterrupt, SystemExit):
        pass
    finally:
        for p in list(PROCS.values()):
            kill_proc(p)


INDEX_HTML = r"""<!doctype html>
<html lang="ko">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>에이전트 하네스</title>
<style>
:root{--bg:#f6f5f2;--panel:#fff;--ink:#1d1d1b;--mute:#6b6a65;--line:#e4e2dc;--accent:#2f5d50;--accent-ink:#fff;--ok:#2f7d4f;--warn:#b7791f;--err:#b83232;--chip:#eeece6}
@media (prefers-color-scheme:dark){:root{--bg:#171715;--panel:#201f1d;--ink:#ecebe6;--mute:#9a988f;--line:#34332f;--accent:#7fb7a4;--accent-ink:#10201a;--ok:#6fcf97;--warn:#e0b050;--err:#ef7a7a;--chip:#2a2926}}
*{box-sizing:border-box}
[hidden]{display:none!important}
body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.6 -apple-system,"Apple SD Gothic Neo","Noto Sans KR","Malgun Gothic",system-ui,sans-serif}
header{display:flex;align-items:center;gap:14px;padding:10px 20px;border-bottom:1px solid var(--line);background:var(--panel)}
header h1{font-size:16px;margin:0;font-weight:700;white-space:nowrap}
header .sp{flex:1}
header .q{color:var(--mute);font-size:13px;white-space:nowrap}
.ptabs{display:flex;gap:6px;overflow:auto;padding:2px}
.ptab{white-space:nowrap;border:1px solid var(--line);background:var(--bg);color:var(--ink);padding:6px 14px;border-radius:99px;font-weight:600;font-size:14px}
.ptab.on{background:var(--accent);color:var(--accent-ink);border-color:var(--accent)}
.ptab i{font-style:normal;font-size:11px;margin-left:6px;padding:0 6px;border-radius:99px;background:color-mix(in srgb,var(--ink) 14%,transparent)}
.ptab i.w{background:var(--warn);color:#fff}
.ptab.add{border-style:dashed;color:var(--mute);background:none}
.subnav{display:flex;align-items:center;gap:4px;padding:6px 20px;border-bottom:1px solid var(--line);background:var(--panel);overflow-x:auto}
.nv{border:0;background:none;color:var(--mute);padding:6px 14px;border-radius:8px;font-weight:600;white-space:nowrap;flex:none}
.nv.on{background:var(--chip);color:var(--ink)}
.pdesc{margin-left:12px;color:var(--mute);font-size:13px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.wrap{display:grid;grid-template-columns:320px minmax(0,1fr);gap:16px;padding:16px 20px;max-width:1280px;margin:0 auto}
.page{padding:16px 20px;max-width:900px;margin:0 auto}
@media (max-width:860px){.wrap{grid-template-columns:minmax(0,1fr);padding:12px}.page{padding:12px}header{padding:10px 12px}.subnav{padding:6px 12px}.pdesc{display:none}header h1{font-size:14px}}
.card{background:var(--panel);border:1px solid var(--line);border-radius:12px;padding:14px}
.card+.card{margin-top:12px}
.card h2{font-size:13px;margin:0 0 10px;color:var(--mute);font-weight:600;letter-spacing:.02em}
textarea,select,input[type=text]{width:100%;font:inherit;color:var(--ink);background:var(--bg);border:1px solid var(--line);border-radius:8px;padding:8px 10px}
textarea{min-height:92px;resize:vertical}
button{font:inherit;cursor:pointer;border-radius:8px;border:1px solid var(--line);background:var(--panel);color:var(--ink);padding:8px 14px}
button.pri{background:var(--accent);color:var(--accent-ink);border-color:var(--accent);font-weight:600}
button.dng{color:var(--err);border-color:var(--err)}
button:disabled{opacity:.5;cursor:default}
.row{display:flex;gap:8px;align-items:center;flex-wrap:wrap}
.jobs{display:flex;flex-direction:column;gap:6px;margin-top:12px;max-height:60vh;overflow:auto}
.job{padding:10px 11px;border:1px solid var(--line);border-radius:10px;cursor:pointer;background:var(--panel)}
.job:hover{border-color:var(--accent)}
.job.sel{border-color:var(--accent);box-shadow:0 0 0 1px var(--accent) inset}
.job .t{font-weight:600;font-size:14px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.job .m{display:flex;gap:8px;align-items:center;color:var(--mute);font-size:12px;margin-top:3px;flex-wrap:wrap}
.chip{display:inline-block;padding:1px 9px;border-radius:99px;font-size:12px;background:var(--chip);color:var(--mute);font-weight:600}
.chip.running{background:color-mix(in srgb,var(--accent) 18%,transparent);color:var(--accent)}
.chip.awaiting_user{background:color-mix(in srgb,var(--warn) 22%,transparent);color:var(--warn)}
.chip.deploying{background:color-mix(in srgb,var(--accent) 18%,transparent);color:var(--accent)}
.attl{display:flex;flex-wrap:wrap;gap:6px;margin-top:6px}.attl:empty{display:none}
.attc{display:flex;align-items:center;gap:6px;font-size:12px;border:1px solid var(--line);border-radius:8px;padding:3px 6px;max-width:100%}
.attc img{width:34px;height:34px;object-fit:cover;border-radius:4px}.attc b{font-weight:500;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;max-width:140px}
.attc button{border:0;background:none;cursor:pointer;color:var(--mute);padding:0 2px;font-size:14px}
.attb{font-size:13px;cursor:pointer;border:1px solid var(--line);border-radius:8px;padding:7px 12px;color:var(--ink)}
.req.drag{outline:2px dashed var(--accent)}
.atts{display:flex;flex-wrap:wrap;gap:8px;margin:8px 0}.atts a{font-size:12px;color:var(--ink);text-decoration:none;border:1px solid var(--line);border-radius:8px;padding:4px 8px;display:flex;align-items:center;gap:6px}
.atts img{max-width:160px;max-height:110px;border-radius:6px;display:block}
.usagebar{position:fixed;right:10px;bottom:6px;font-size:11px;color:var(--mute);background:var(--panel);border:1px solid var(--line);border-radius:8px;padding:3px 8px;opacity:.9;z-index:5}
.usagebar b{color:var(--ink);font-weight:600}.usagebar .hi{color:var(--err)}
@media (max-width:700px){.usagebar{left:10px;right:auto}}
.chip.relwait{background:color-mix(in srgb,#d08a1c 20%,transparent);color:#b0700a}
.chip.approved{background:color-mix(in srgb,var(--ok) 20%,transparent);color:var(--ok)}
.chip.failed,.chip.cancelled,.chip.reverted{background:color-mix(in srgb,var(--err) 18%,transparent);color:var(--err)}
.empty{color:var(--mute);text-align:center;padding:60px 10px}
.title{display:flex;gap:10px;align-items:center;flex-wrap:wrap;margin-bottom:4px}
.title h2{font-size:18px;margin:0;color:var(--ink)}
.usage{font-size:12px;color:var(--mute);margin:2px 0 4px}
.steps{display:flex;gap:6px;margin:12px 0;flex-wrap:wrap}
.step{flex:1;min-width:92px;padding:8px 10px;border-radius:10px;border:1px solid var(--line);font-size:13px;background:var(--bg)}
.step b{display:block;font-size:13px}
.step span{color:var(--mute);font-size:12px}
.step.done{border-color:var(--ok)}.step.done b::before{content:"✓ ";color:var(--ok)}
.step.active{border-color:var(--accent);background:color-mix(in srgb,var(--accent) 10%,var(--panel))}
.step.active b::before{content:"● ";color:var(--accent);animation:p 1.2s infinite}
.step.err{border-color:var(--err)}.step.err b::before{content:"✕ ";color:var(--err)}
@keyframes p{50%{opacity:.3}}
.approve{border:1px solid var(--warn);background:color-mix(in srgb,var(--warn) 8%,var(--panel));margin:10px 0}
.approve h3{margin:0 0 6px;font-size:15px}
.approve .sub{color:var(--mute);font-size:13px;margin-bottom:10px}
.tabs{display:flex;gap:4px;border-bottom:1px solid var(--line);margin-top:14px;overflow:auto}
.tab{padding:8px 12px;border:0;border-bottom:2px solid transparent;border-radius:0;background:none;color:var(--mute);white-space:nowrap}
.tab.on{color:var(--ink);border-bottom-color:var(--accent);font-weight:600}
.tab.none{opacity:.4}
.doc{padding:14px 4px;max-height:58vh;overflow:auto}
.doc h2,.doc h3,.doc h4,.doc h5{margin:1.1em 0 .4em;line-height:1.35;color:var(--ink);letter-spacing:0}
.doc h2{font-size:20px}.doc h3{font-size:17px}.doc h4{font-size:15px}
.doc p{margin:.5em 0}.doc ul{padding-left:20px}
.doc code{background:var(--chip);padding:1px 5px;border-radius:4px;font-size:.92em}
.doc pre{background:var(--chip);padding:10px;border-radius:8px;overflow:auto}
.doc blockquote{margin:.6em 0;padding:2px 12px;border-left:3px solid var(--line);color:var(--mute)}
.doc table{border-collapse:collapse;margin:.6em 0;font-size:14px}.doc td,.doc th{border:1px solid var(--line);padding:5px 9px}
.doc a{color:var(--accent)}
.doc hr{border:0;border-top:1px solid var(--line);margin:1em 0}
.vd{font-size:13px;margin:4px 0;color:var(--mute)}
.ev{margin-top:14px}
.ev div{display:flex;gap:10px;font-size:13px;padding:3px 0;color:var(--mute)}
.ev .ts{font-variant-numeric:tabular-nums;flex:none}
.ev .ag{flex:none;min-width:48px;font-weight:600;color:var(--ink)}
.ev .ok .mg{color:var(--ok)}.ev .warn .mg{color:var(--warn)}.ev .err .mg{color:var(--err)}
.err-box{color:var(--err);font-size:13px;margin:6px 0;white-space:pre-wrap}
label.lb{display:block;font-size:13px;color:var(--mute);margin:0 0 10px}
label.lb select,label.lb input,label.lb textarea{display:block;margin-top:4px}
.mono{font-family:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;font-size:13px;min-height:260px;line-height:1.55}
.warnbox{border:1px solid var(--warn);background:color-mix(in srgb,var(--warn) 9%,var(--panel));border-radius:10px;padding:10px 14px;margin:10px 0;font-size:13px}
.warnbox ul{margin:6px 0;padding-left:18px}
.chk{display:flex;gap:8px;align-items:flex-start;margin:8px 0;font-size:14px}
.chk input{margin-top:5px}
.chk small{display:block;color:var(--mute);font-size:12px}
.badges{display:flex;gap:6px;flex-wrap:wrap;margin:6px 0 12px}
.tag{display:inline-block;font-size:11px;padding:0 7px;border-radius:6px;background:var(--chip);color:var(--mute);font-weight:600}
.plan{border:1px solid var(--line);border-radius:10px;padding:10px 14px;margin:10px 0;background:var(--bg)}
.plan .ph{font-size:12px;font-weight:700;color:var(--mute);margin:8px 0 4px}
.plan .pa{margin:4px 0}
.pst{margin:4px 0;padding-left:20px}.pst li{margin:6px 0}
.sc{border:1px solid var(--line);border-radius:10px;margin:10px 0;background:var(--bg)}
.sc.off{opacity:.6}
.sch{display:flex;gap:8px;align-items:center;padding:8px 10px;border-bottom:1px solid var(--line);flex-wrap:wrap}
.sch input[type=text]{flex:1;min-width:120px;width:auto}
.sch select{width:auto}
.sch button{padding:4px 10px}
.sch b{width:22px;height:22px;border-radius:50%;background:var(--accent);color:var(--accent-ink);display:inline-flex;align-items:center;justify-content:center;font-size:12px}
.inl{display:flex;gap:5px;align-items:center;font-size:13px;color:var(--mute);white-space:nowrap}
.scb{padding:10px 12px}
.g2{display:grid;grid-template-columns:1fr 1fr;gap:10px}
@media (max-width:600px){.g2{grid-template-columns:1fr}}
.ins{display:flex;gap:12px;flex-wrap:wrap;margin:0 0 10px;font-size:13px}
table.ut{border-collapse:collapse;width:100%;font-size:13px}.ut td,.ut th{padding:6px 8px;border-bottom:1px solid var(--line);text-align:left}
.tip{font-size:13px;color:var(--mute)}.tip li{margin:4px 0}
#toast{position:fixed;bottom:18px;left:50%;transform:translateX(-50%);background:var(--ink);color:var(--bg);padding:9px 16px;border-radius:99px;font-size:13px;opacity:0;transition:.2s;pointer-events:none;max-width:90vw}
#toast.show{opacity:1}
/* ---- 화면 개편 (2026-11) ---- */
:root{--radius:14px;--shadow:0 1px 2px rgba(20,20,10,.05),0 4px 14px rgba(20,20,10,.04)}
header{position:sticky;top:0;z-index:20;padding:10px 24px;gap:16px}
header h1{font-size:17px;letter-spacing:-.01em}
.subnav{position:sticky;top:52px;z-index:19;padding:6px 24px}
.wrap{grid-template-columns:400px minmax(0,1fr);gap:20px;padding:20px 24px;max-width:1520px}
.wrap>aside{position:sticky;top:112px;align-self:start}
.card{border-radius:var(--radius);padding:18px;box-shadow:var(--shadow)}
.card h2{font-size:14px;color:var(--ink);margin-bottom:12px}
#req{min-height:230px;font-size:15px;line-height:1.65;padding:12px 14px;background:var(--panel)}
#req:focus,textarea:focus,input[type=text]:focus,select:focus{outline:2px solid color-mix(in srgb,var(--accent) 45%,transparent);outline-offset:0;border-color:var(--accent)}
#go{padding:9px 22px}
.jobs{max-height:calc(100vh - 560px);min-height:180px;gap:8px}
.job{padding:11px 13px;border-radius:12px}
main.card#main{padding:24px 28px;min-height:calc(100vh - 160px)}
.title h2{font-size:21px;letter-spacing:-.01em}
.steps{gap:8px}
.step{border-radius:12px;padding:9px 12px}
.tabs{position:sticky;top:104px;background:var(--panel);z-index:3;margin-top:18px}
.tab{padding:10px 14px;font-size:14px}
.doc{max-height:none;font-size:15.5px;line-height:1.8;padding:20px 4px 8px}
.doc h2{font-size:21px}.doc h3{font-size:18px}
.doc pre{font-size:13px;line-height:1.55}
.doc .ev{margin-top:0}.doc .ev div{font-size:13.5px;padding:5px 0;border-bottom:1px dashed var(--line)}
.approve{border-radius:var(--radius);padding:16px 18px}
@media (max-width:1100px){.wrap{grid-template-columns:340px minmax(0,1fr)}}
@media (max-width:860px){.wrap{grid-template-columns:minmax(0,1fr);padding:12px}.wrap>aside{position:static}
  .jobs{max-height:45vh}main.card#main{padding:16px;min-height:0}.tabs{top:96px}#req{min-height:160px}header,.subnav{padding-left:12px;padding-right:12px}}
</style>
</head>
<body>
<header><h1>에이전트 하네스</h1><div class="ptabs" id="ptabs"></div><div class="sp"></div><div class="q" id="qinfo"></div><a class="q" href="/logout" style="color:var(--mute);margin-left:12px">로그아웃</a></header>
<div class="subnav" id="subnav" hidden>
  <button class="nv on" data-v="jobs">작업</button><button class="nv" data-v="agents">에이전트</button><button class="nv" data-v="sources">자료</button><button class="nv" data-v="stages">단계</button><button class="nv" data-v="sched">예약</button><button class="nv" data-v="settings">설정</button>
  <span class="pdesc" id="pdesc"></span>
</div>

<div class="wrap" id="v-jobs">
  <aside>
    <div class="card">
      <h2>새 작업 요청</h2>
      <textarea id="req" placeholder="무엇을 해야 하는지 자세히 적어주세요.&#10;&#10;예) 마필 목록 화면에서 검색창이 모바일에서 잘려 보여요. 한 줄로 보이게 고쳐주세요.&#10;&#10;· 스크린샷은 Ctrl+V로 붙여넣거나 끌어다 놓기&#10;· Ctrl+Enter로 바로 시작"></textarea>
      <div id="attl" class="attl"></div>
      <div class="row" style="margin-top:8px"><button class="pri" id="go">작업 시작</button><label class="attb">파일 첨부<input type="file" id="attf" multiple hidden accept="image/*,.pdf,.txt,.md,.csv,.json,.log,.yaml,.yml,.html,.css,.js,.ts,.vue,.py,.sql,.xml,.har"></label></div>
    </div>
    <div class="jobs" id="jobs"></div>
    <div class="row" style="margin-top:8px;justify-content:center"><button id="jclean" style="font-size:12px;padding:5px 10px">끝난 작업 정리</button></div>
  </aside>
  <main class="card" id="main"><div class="empty">왼쪽에서 작업을 선택하거나 새 요청을 시작하세요.</div></main>
</div>

<div class="wrap" id="v-agents" hidden>
  <aside>
    <div class="card">
      <h2>이 프로젝트의 에이전트</h2>
      <div class="jobs" id="alist" style="margin-top:0;max-height:none"></div>
      <div class="row" style="margin-top:10px"><button class="pri" id="anew">+ 새 에이전트</button><button id="aimp">가져오기</button></div>
      <div class="row" style="margin-top:6px"><button id="arenall">전체 폴더 이름 정리</button></div>
    </div>
  </aside>
  <main><div class="card" id="aedit"><div class="empty">왼쪽에서 에이전트를 선택하세요.</div></div><div id="imppanel2"></div></main>
</div>

<div class="page" id="v-sources" hidden></div>
<div class="page" id="v-stages" hidden></div>
<div class="page" id="v-sched" hidden></div>
<div class="page" id="v-settings" hidden></div>
<div class="page" id="v-newproj" hidden></div>
<div id="toast"></div>

<script>
const $=s=>document.querySelector(s);
const esc=s=>String(s==null?'':s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const STATUS={queued:'대기',running:'진행 중',awaiting_user:'승인 대기',approved:'승인 완료',deploying:'반영 중',failed:'실패',cancelled:'중단',reverted:'되돌림'};
const AG={system:'시스템',user:'나'};
let P=[],cur=null,view='jobs',settings={},flags={},presets=[],pj=null;
let sel=null,tab=null,tabPinned=false,last={},busy=false,tickN=0;

function toast(m){const t=$('#toast');t.textContent=m;t.classList.add('show');clearTimeout(toast.t);toast.t=setTimeout(()=>t.classList.remove('show'),2600)}
async function api(path,opt){
  const r=await fetch(path,Object.assign({headers:{'Content-Type':'application/json'},credentials:'same-origin'},opt||{}));
  if(r.status===401){location.href='/login';throw new Error('로그인이 필요합니다')}
  let d={};try{d=await r.json()}catch(e){}
  if(!r.ok)throw new Error(d.error||r.statusText);
  return d;
}
const post=(path,obj)=>api(path,{method:'POST',body:JSON.stringify(obj||{})});
const base=()=>'/api/projects/'+encodeURIComponent(cur);
const fmtN=n=>{n=+n||0;return n>=1e6?(n/1e6).toFixed(1)+'M':n>=1e3?(n/1e3).toFixed(1)+'k':String(n)};
const newTok=u=>(+u.input||0)+(+u.output||0)+(+u.cache_write||0);
function usageLine(u){
  if(!u||!u.calls)return '아직 사용량 없음';
  return '호출 '+u.calls+'회 · 입력 '+fmtN(u.input)+' · 출력 '+fmtN(u.output)+' · 캐시 쓰기 '+fmtN(u.cache_write)+' · 캐시 읽기 '+fmtN(u.cache_read)+(u.cost?' · 추정 $'+(+u.cost).toFixed(3):'');
}

/* ---------- 마크다운 ---------- */
function md(src){
  const lines=esc(src).split('\n');let out='',code=false,list=false,para=[],tbl=[];
  const inl=t=>t.replace(/`([^`]+)`/g,'<code>$1</code>').replace(/\*\*([^*]+)\*\*/g,'<b>$1</b>').replace(/\[([^\]]+)\]\((https?:\/\/[^)\s]+)\)/g,'<a href="$2" target="_blank" rel="noopener noreferrer">$1</a>');
  const fp=()=>{if(para.length){out+='<p>'+inl(para.join(' '))+'</p>';para=[]}};
  const fl=()=>{if(list){out+='</ul>';list=false}};
  const ft=()=>{if(tbl.length){const rows=tbl.filter(r=>!/^\s*\|?\s*:?-{2,}/.test(r));out+='<table>'+rows.map((r,i)=>'<tr>'+r.replace(/^\s*\||\|\s*$/g,'').split('|').map(c=>(i?'<td>':'<th>')+inl(c.trim())+(i?'</td>':'</th>')).join('')+'</tr>').join('')+'</table>';tbl=[]}};
  for(const l of lines){
    if(l.startsWith('```')){fp();fl();ft();out+=code?'</pre>':'<pre>';code=!code;continue}
    if(code){out+=l+'\n';continue}
    let m;
    if(/^\s*\|/.test(l)){fp();fl();tbl.push(l);continue}else ft();
    if(/^\s*(-{3,}|\*{3,})\s*$/.test(l)){fp();fl();out+='<hr>';continue}
    if(m=l.match(/^(#{1,4})\s+(.*)$/)){fp();fl();const n=Math.min(m[1].length+1,5);out+='<h'+n+'>'+inl(m[2])+'</h'+n+'>'}
    else if(m=l.match(/^\s*[-*]\s+(.*)$/)){fp();if(!list){out+='<ul>';list=true}out+='<li>'+inl(m[1])+'</li>'}
    else if(m=l.match(/^&gt;\s?(.*)$/)){fp();fl();out+='<blockquote>'+inl(m[1])+'</blockquote>'}
    else if(!l.trim()){fp();fl()}
    else{fl();para.push(l)}
  }
  fp();fl();ft();if(code)out+='</pre>';return out;
}
const verdictOf=t=>{const m=(t||'').slice(0,600).match(/VERDICT:\s*(APPROVE|REVISE)/i);return m?m[1].toUpperCase():null};
const stripV=t=>(t||'').replace(/^\s*VERDICT:.*\n?/i,'');

/* ---------- 프로젝트 / 화면 전환 ---------- */
async function loadProjects(){
  const d=await api('/api/projects');
  P=d.projects;settings=d.settings;flags=d.flags;
  if(!cur||!P.find(p=>p.id===cur)){let s=null;try{s=localStorage.getItem('cur')}catch(e){}cur=(P.find(p=>p.id===s)||P[0]||{}).id||null}
  const q=d.queue;$('#qinfo').textContent=[q.running?'실행 '+q.running:'',q.waiting?'대기 '+q.waiting:''].filter(Boolean).join(' · ');
  $('#ptabs').innerHTML=P.map(p=>'<button class="ptab'+(p.id===cur?' on':'')+'" data-id="'+esc(p.id)+'">'+esc(p.name)+(p.active?'<i>'+p.active+'</i>':'')+(p.awaiting?'<i class="w">승인 '+p.awaiting+'</i>':'')+'</button>').join('')+'<button class="ptab add" id="padd">+ 프로젝트</button>';
  const c=P.find(p=>p.id===cur);$('#pdesc').textContent=c?(c.description||''):'';
}
function setView(v){
  view=v;
  document.querySelectorAll('#subnav .nv').forEach(b=>b.classList.toggle('on',b.dataset.v===v));
  ['jobs','agents','sources','stages','sched','settings','newproj'].forEach(x=>{$('#v-'+x).hidden=x!==v});
  $('#subnav').hidden=v==='newproj'||!cur;
  last={};
  if(v==='jobs'){loadList().then(()=>sel&&loadDetail(true)).catch(()=>{})}
  if(v==='agents')loadAgents().catch(e=>toast(e.message));
  if(v==='sources')loadSources().catch(e=>toast(e.message));
  if(v==='stages')loadStages().catch(e=>toast(e.message));
  if(v==='sched')loadSched().catch(e=>toast(e.message));
  if(v==='settings')loadSettings().catch(e=>toast(e.message));
  if(v==='newproj')initNewProj().catch(e=>toast(e.message));
}
function switchProject(id){
  cur=id;try{localStorage.setItem('cur',id)}catch(e){}
  sel=null;last={};selAgent=null;
  $('#main').innerHTML='<div class="empty">왼쪽에서 작업을 선택하거나 새 요청을 시작하세요.</div>';
  $('#aedit').innerHTML='<div class="empty">왼쪽에서 에이전트를 선택하세요.</div>';
  loadProjects().then(()=>setView(view==='newproj'?'jobs':view));
}
$('#ptabs').onclick=e=>{
  if(e.target.closest('#padd')){setView('newproj');return}
  const b=e.target.closest('.ptab');if(b)switchProject(b.dataset.id);
};
document.querySelectorAll('#subnav .nv').forEach(b=>b.onclick=()=>setView(b.dataset.v));

/* ---------- 작업 ---------- */
const chipC=j=>j.release_state==='pending'?'relwait':j.status;
const chipL=j=>j.needs_input?'질문 대기':j.release_state==='pending'?'운영 대기':j.release_state==='released'?'운영 반영':STATUS[j.status];
async function loadList(){
  if(!cur)return;
  const d=await api(base()+'/jobs');
  const h=d.jobs.map(j=>'<div class="job'+(j.id===sel?' sel':'')+'" data-id="'+esc(j.id)+'"><div class="t">'+esc(j.title)+'</div><div class="m"><span class="chip '+chipC(j)+'">'+chipL(j)+'</span><span>'+esc(j.created.slice(5,16))+'</span>'+(j.tokens?'<span>토큰 '+fmtN(j.tokens)+'</span>':'')+'</div></div>').join('');
  if(h!==last.list){last.list=h;$('#jobs').innerHTML=h||'<div class="empty" style="padding:20px">아직 작업이 없습니다</div>'}
}
async function loadDetail(force){
  if(!sel||!cur||view!=='jobs')return;
  let d;try{d=await api(base()+'/jobs/'+encodeURIComponent(sel))}catch(e){return}
  const j=d.job,f=d.files,stg=d.stages.filter(s=>s.enabled);
  const steps=stg.map(s=>[s.id,s.name,s.agent]).concat([['user','최종 승인','나']]);
  const keys=steps.map(s=>s[0]);
  if(!tabPinned&&f.approved!=null&&d.repo){tab='approved'}else if(!tabPinned){const w=d.stages.slice().reverse().find(s=>s.kind==='work'&&f[s.id]!=null);tab=f.final?'final':(w?w.id:((j.status==='running'||j.status==='queued')?'log':'request'))}
  const nS=stg.length;
  const ci=j.needs_input?Math.max(0,keys.indexOf(j.step)):(j.status==='awaiting_user'||j.status==='deploying')?nS:(j.status==='approved'||j.status==='reverted')?nS+1:Math.max(0,keys.indexOf(j.step));
  const st=i=>i<ci?'done':i===ci?((j.status==='failed'||j.status==='cancelled')?'err':(j.status==='running'||j.status==='awaiting_user'||j.status==='deploying')?'active':'wait'):'wait';
  const u=j.usage||{};
  const bys=Object.entries(u.by_stage||{}).map(([k,v])=>{const s=d.stages.find(x=>x.id===k);return esc(s?s.name:(k==='plan'?'자동 구성':k))+' '+fmtN(newTok(v))}).join(' · ');
  const srcL={telegram:'텔레그램',schedule:'예약 실행'}[j.source];
  const head='<div class="title"><h2>'+esc(j.title)+'</h2><span class="chip '+chipC(j)+'">'+chipL(j)+'</span>'+(srcL?'<span class="chip">'+srcL+'</span>':'')+(j.auto_approve?'<span class="chip">자동 승인</span>':'')+(d.auto_planned?'<span class="chip approved">자동 구성</span>':'')+'</div>'
    +(j.branch?'<div class="usage">브랜치: '+esc(j.branch)+'</div>':'')+'<div class="usage">'+esc(usageLine(u))+(d.limit?' · 작업 한도 '+fmtN(d.limit)+' 중 새 토큰 '+fmtN(newTok(u)):'')+'</div>'
    +(bys?'<div class="usage">단계별 새 토큰: '+bys+'</div>':'')
    +'<div class="steps">'+steps.map((s,i)=>'<div class="step '+st(i)+'"><b>'+esc(s[1])+'</b><span>'+esc(s[2])+'</span></div>').join('')+'</div>'
    +(j.error?'<div class="err-box">'+esc(j.error)+'</div>':'');
  const evh='<div class="ev">'+j.events.slice().reverse().map(e=>'<div class="'+e.kind+'"><span class="ts">'+esc((e.ts||'').slice(11,19))+'</span><span class="ag">'+esc(AG[e.agent]||e.agent)+'</span><span class="mg">'+esc(e.msg)+'</span></div>').join('')+'</div>';
  const actKey=j.id+'|'+j.status+'|'+(j.release_state||'')+'|'+(EDIT===j.id?'e':'')+(FOLLOW===j.id?'f':'');
  if(last.act!==actKey||force){
    last.act=actKey;
    const works=stg.filter(s=>s.kind==='work');
    const opts='<option value="first">처음부터</option>'+works.map((s,i)=>'<option value="'+esc(s.id)+'"'+(i===works.length-1&&works.length>1?' selected':'')+'>'+esc(s.name)+'부터</option>').join('');
    let act='';
    if(j.status==='awaiting_user'&&j.needs_input){
      act='<div class="card approve"><h3>에이전트가 질문이 있습니다</h3>'
        +'<div class="sub" style="white-space:pre-wrap">'+esc(j.question||'')+'</div>'
        +'<textarea id="qa" placeholder="답변을 적어주세요"></textarea>'
        +'<div class="row" style="margin-top:8px"><button class="pri" id="qago">답변 보내기</button></div></div>';
    }else if(j.status==='awaiting_user'){
      const lastRev=stg.slice().reverse().find(s=>s.kind==='review'&&f[s.id]!=null);
      const rv=lastRev?verdictOf(f[lastRev.id]):'APPROVE';
      act='<div class="card approve"><h3>최종 승인이 필요합니다</h3><div class="sub">'+(rv==='APPROVE'?'검토를 통과한 결과물입니다.':'검토 단계의 수정요청이 남은 상태입니다. 해당 탭에서 내용을 확인하세요.')+(d.repo&&d.repo.release?' 승인하면 테스트 서버('+esc(d.repo.base)+')에만 반영됩니다. 운영은 테스트 서버에서 확인한 뒤 이 화면의 \'운영 반영\'으로 따로 올립니다.':d.repo?(d.repo.mode==='branch'?' 승인하면 작업 브랜치를 GitHub에 푸시합니다(PR은 직접 병합).':' 승인하면 '+esc(d.repo.base)+'에 병합해 GitHub에 푸시합니다. 푸시되면 GitHub Actions 빌드가 시작됩니다.')+' \'변경 내용\' 탭에서 diff를 먼저 확인하세요.':' 승인하면 outbox에 approved 파일로 저장됩니다.')+'</div>'
        +'<div class="row"><button class="pri" id="ap">'+(d.repo&&d.repo.release?'승인 · 테스트 서버 반영':'최종 승인')+'</button></div><hr style="border:0;border-top:1px solid var(--line);margin:12px 0">'
        +'<textarea id="fb" placeholder="수정이 필요하면 요청 내용을 적어주세요"></textarea>'
        +'<div class="row" style="margin-top:8px"><select id="st" style="width:auto">'+opts+'</select><button id="rj">반려하고 다시 작업</button></div></div>';
    }else if(j.status==='running'||j.status==='queued'){
      act='<div class="row" style="margin:10px 0"><button class="dng" id="cn">작업 중단</button><button id="cne">중단하고 요청 수정</button></div>';
    }else if((j.status==='failed'||j.status==='cancelled'||j.status==='reverted')&&EDIT===j.id){
      const at=d.attachments||[];
      act='<div class="card approve"><h3>요청 수정</h3><div class="sub">고친 요청으로 처음부터 다시 작업합니다. 이전 시도의 중간 결과'+(d.repo?'와 코드 변경':'')+'은 버립니다.</div>'
        +'<textarea id="edtx" style="min-height:140px">'+esc((f.request||'').replace(/\n$/,''))+'</textarea>'
        +'<div class="attl" id="edatt">'+at.map(a=>'<span class="attc" data-keep="'+esc(a.name)+'">'+(a.img?'🖼':'📄')+' <b>'+esc(a.name)+'</b><button data-drop="'+esc(a.name)+'" title="빼기">×</button></span>').join('')+'</div>'
        +'<div class="attl" id="ednew"></div>'
        +'<div class="row" style="margin-top:8px"><button class="pri" id="edgo">수정하고 다시 시작</button><label class="attb">파일 추가<input type="file" id="edf" multiple hidden></label><button id="edno">취소</button></div></div>';
    }else if(j.status==='reverted'){
      act='<div class="card"><h3 style="margin:0 0 6px">테스트 서버에서 되돌린 작업</h3><div class="sub">'+(j.reverted_at?esc(j.reverted_at.slice(5,16))+'에 ':'')+'이 작업의 코드 변경을 되돌렸습니다. 테스트 서버는 1~3분 안에 이전 상태로 다시 배포됩니다. 다시 하고 싶으면 요청을 고쳐서 새로 작업하세요.</div>'
        +'<div class="row"><button class="pri" id="ed">요청 수정해서 다시 작업</button></div></div>';
    }else if(j.status==='failed'||j.status==='cancelled'){
      act='<div class="row" style="margin:10px 0"><button class="pri" id="ed">요청 수정</button><select id="st" style="width:auto">'+opts.replace(' selected','')+'</select><button id="rt">그대로 다시 시도</button></div>';
    }else if(j.status==='deploying'){
      act='<div class="vd">승인됨 - GitHub 저장소에 반영하는 중입니다…</div>';
    }else if(j.status==='approved'&&j.release_state==='pending'){
      const w=(d.repo&&d.repo.with)||[];
      act='<div class="card approve"><h3>테스트 서버에 반영됨 · 운영 반영 대기</h3>'
        +'<div class="sub">테스트 서버에서 확인을 마쳤으면 운영에 올리세요. 바로 올리지 않아도 됩니다. 이 작업은 운영 대기 상태로 남아 있다가 원할 때 반영할 수 있습니다.'
        +(w.length?'<br><b>먼저 승인된 운영 대기 작업 '+w.length+'개도 함께 반영됩니다:</b> '+w.map(x=>esc(x.title)).join(', '):'')+'</div>'
        +'<div class="row">'+(d.repo&&d.repo.test_url?'<a class="attb" style="text-decoration:none" href="'+esc(d.repo.test_url)+'" target="_blank" rel="noopener">테스트 서버 열기 ↗</a>':'')
        +'<button class="pri" id="rel">운영 반영</button><button class="dng" id="rvt">테스트 서버에서 되돌리기</button></div>'
        +'<div class="vd" style="margin-top:6px">마음에 안 들면 \'되돌리기\'로 테스트 서버를 이 작업 이전 상태로 돌립니다. 조금만 고치면 되는 경우엔 아래 \'이어서 수정 요청\'이 더 편합니다.</div></div>';
    }else if(j.status==='approved'&&j.release_state==='none'){
      act='<div class="vd">이 작업은 바뀐 코드가 없어 테스트·운영 서버에 올라간 것이 없습니다 (분석·설계 요청 등). 운영 반영할 내용이 없습니다.</div>';
    }else if(j.status==='approved'&&j.release_state==='released'){
      act='<div class="vd">운영 반영 완료'+(j.released_at?' ('+esc(j.released_at.slice(5,16))+')':'')+' · 문제가 있으면 설정 → 코드 저장소 → 운영 반영 이력에서 되돌릴 수 있습니다.</div>';
    }else if(j.status==='approved'){
      act='<div class="vd">승인 완료: shared/outbox/approved_'+esc(j.id)+'.md'+(d.repo?' · 반영 결과는 \'승인본\' 탭에서 확인':'')+'</div>';
    }
    if(['awaiting_user','approved','failed','cancelled','reverted'].includes(j.status))act+='<div class="row" style="margin:6px 0 10px;justify-content:flex-end"><button class="dng" id="jdel" style="font-size:12px;padding:5px 10px">작업 삭제</button></div>';
    const at=d.attachments||[];
    if(at.length)act='<div class="atts">'+at.map(a=>{const u=base()+'/jobs/'+encodeURIComponent(j.id)+'/files/'+encodeURIComponent(a.name);return '<a href="'+u+'" target="_blank" rel="noopener">'+(a.img?'<img src="'+u+'" alt="'+esc(a.name)+'">':'📄 '+esc(a.name)+' <span style="color:var(--mute)">'+fmtB(a.size)+'</span>')+'</a>'}).join('')+'</div>'+act;
    if(j.status==='approved'){
      act+=FOLLOW===j.id
        ?'<div class="card" style="margin-top:10px"><h3 style="margin:0 0 6px">이어서 수정 요청</h3><div class="sub">이 작업의 결과'+(d.repo?'(테스트 서버에 올라간 최신 코드)':'')+' 위에서 이어서 고칩니다. 마음에 안 드는 부분만 적어주세요.</div>'
          +'<textarea id="futx" style="min-height:110px" placeholder="예: 버튼 색을 회색으로, 목록 정렬은 최신순으로 바꿔줘 (스크린샷은 Ctrl+V)"></textarea><div class="attl" id="funew"></div>'
          +'<div class="row" style="margin-top:8px"><button class="pri" id="fugo">이어서 작업 시작</button><label class="attb">파일 첨부<input type="file" id="fuf" multiple hidden></label><button id="funo">취소</button></div></div>'
        :'<div class="row" style="margin:8px 0"><button id="fu">이어서 수정 요청</button>'+(j.followups?'<span style="font-size:12px;color:var(--mute)">추가 요청 '+j.followups+'회</span>':'')+'</div>';
    }
    $('#act').innerHTML=act;bindJob(j);
  }
  const tdef=(f.approved!=null&&d.repo?[['approved','승인본']]:[]).concat(f.diff!=null?[['diff','변경 내용']]:[]).concat([['final','최종본']]).concat(d.stages.slice().reverse().map(s=>[s.id,s.name+(s.kind==='review'?' (검토)':'')+(s.enabled?'':' ·꺼짐')])).concat([['request','요청'],['log','진행 기록 ('+j.events.length+')']]);
  const tabsH='<div class="tabs">'+tdef.map(t=>'<button class="tab'+(tab===t[0]?' on':'')+(f[t[0]]!=null||t[0]==='log'?'':' none')+'" data-t="'+esc(t[0])+'">'+esc(t[1])+'</button>').join('')+'</div>';
  const txt=tab==='log'?'':f[tab];const ts=d.stages.find(s=>s.id===tab);const isRev=ts&&ts.kind==='review';
  let vd='';if(isRev){const v=verdictOf(txt);if(v)vd='<div class="vd">판정: <b>'+(v==='APPROVE'?'승인':'수정요청')+'</b></div>'}
  const docH=tab==='log'?evh:txt==null?'<div class="empty" style="padding:30px">아직 만들어지지 않았습니다</div>':vd+md(isRev?stripV(txt):txt);
  const sig=JSON.stringify([head,evh,tabsH,docH]);
  if(last.sig!==sig||force){
    const keep=$('.doc')?$('.doc').scrollTop:0;
    $('#hd').innerHTML=head;$('#tb').innerHTML=tabsH;
    const dc=$('.doc');dc.innerHTML=docH;if(last.sel===sel&&last.tab===tab)dc.scrollTop=keep;
    last.sig=sig;last.sel=sel;last.tab=tab;
  }
}
function bindJob(j){
  const q=s=>$(s);
  const run=async(fn,msg)=>{if(busy)return;busy=true;try{await fn();toast(msg);last.act=null;await tick(true)}catch(e){toast(e.message)}busy=false};
  const url=base()+'/jobs/'+j.id;
  if(q('#ap'))q('#ap').onclick=()=>{if(confirm('이 결과물을 최종 승인할까요?'))run(()=>post(url+'/approve'),'승인되었습니다')};
  if(q('#rj'))q('#rj').onclick=()=>{const fb=q('#fb').value.trim();if(!fb){toast('수정 요청 내용을 적어주세요');return}run(()=>post(url+'/restart',{feedback:fb,start:q('#st').value}),'다시 작업을 시작합니다')};
  if(q('#rt'))q('#rt').onclick=()=>run(()=>post(url+'/restart',{start:q('#st').value}),'다시 시작합니다');
  if(q('#cn'))q('#cn').onclick=()=>{if(confirm('작업을 중단할까요?'))run(()=>post(url+'/cancel'),'중단 요청')};
  if(q('#fu'))q('#fu').onclick=()=>{FOLLOW=j.id;FUNEW=[];last={};tick(false)};
  if(q('#funo'))q('#funo').onclick=()=>{FOLLOW=null;last={};tick(false)};
  const fuAdd=fs=>{for(const f of fs){if(f.size>10*1024*1024){toast(f.name+': 10MB를 넘습니다');continue}
    FUNEW.push({file:f,name:f.name&&f.name!=='image.png'?f.name:'screenshot-'+new Date().toTimeString().slice(0,8).replace(/:/g,'')+'.png'})}
    q('#funew').innerHTML=FUNEW.map((a,i)=>'<span class="attc">➕ <b>'+esc(a.name)+'</b><span style="color:var(--mute)">'+fmtB(a.file.size)+'</span><button data-fr="'+i+'">×</button></span>').join('');
    q('#funew').querySelectorAll('[data-fr]').forEach(b=>b.onclick=()=>{FUNEW.splice(+b.dataset.fr,1);fuAdd([])})};
  if(q('#fuf'))q('#fuf').onchange=e=>{fuAdd(e.target.files);e.target.value=''};
  if(q('#futx')){q('#futx').addEventListener('paste',e=>{const fs=[...(e.clipboardData||{}).items||[]].filter(x=>x.kind==='file').map(x=>x.getAsFile()).filter(Boolean);if(fs.length){e.preventDefault();fuAdd(fs)}});q('#futx').focus()}
  if(q('#fugo'))q('#fugo').onclick=async e=>{const t=q('#futx').value.trim();if(!t){toast('추가 요청 내용을 입력하세요');return}
    e.target.disabled=true;
    try{const files=await Promise.all(FUNEW.map(async a=>({name:a.name,data:await b64(a.file)})));
      await post(url+'/followup',{request:t,files});FOLLOW=null;toast('이어서 작업을 시작합니다');last={};await loadList();tick(false)}
    catch(err){toast(err.message);e.target.disabled=false}};
  if(q('#ed'))q('#ed').onclick=()=>{EDIT=j.id;EDNEW=[];EDDROP=[];last={};tick(false)};
  if(q('#edno'))q('#edno').onclick=()=>{EDIT=null;last={};tick(false)};
  if(q('#cne'))q('#cne').onclick=async()=>{try{await post(url+'/cancel');EDIT=j.id;EDNEW=[];EDDROP=[];toast('중단했습니다. 요청을 고쳐 다시 시작하세요');last={};tick(false)}catch(e){toast(e.message)}};
  if(q('#edatt'))q('#edatt').querySelectorAll('[data-drop]').forEach(b=>b.onclick=()=>{EDDROP.push(b.dataset.drop);b.closest('.attc').remove()});
  if(q('#edf'))q('#edf').onchange=e=>{for(const f of e.target.files){if(f.size>10*1024*1024){toast(f.name+': 10MB를 넘습니다');continue}EDNEW.push(f)}e.target.value='';
    q('#ednew').innerHTML=EDNEW.map(f=>'<span class="attc">➕ <b>'+esc(f.name)+'</b><span style="color:var(--mute)">'+fmtB(f.size)+'</span></span>').join('')};
  if(q('#edgo'))q('#edgo').onclick=async e=>{const t=q('#edtx').value.trim();if(!t){toast('요청 내용을 입력하세요');return}
    e.target.disabled=true;
    try{const files=await Promise.all(EDNEW.map(async f=>({name:f.name,data:await b64(f)})));
      await post(url+'/edit',{request:t,remove:EDDROP,files});EDIT=null;toast('수정한 요청으로 다시 시작합니다');last={};await loadList();tick(false)}
    catch(err){toast(err.message);e.target.disabled=false}};
  if(q('#rvt'))q('#rvt').onclick=()=>{if(confirm('이 작업의 코드 변경을 테스트 서버에서 되돌릴까요?\n(운영 서버에는 영향 없음, 1~3분 안에 테스트 서버가 이전 상태로 배포됩니다)'))run(()=>post(url+'/revert',{}),'되돌렸습니다 - 1~3분 안에 테스트 서버에 반영됩니다')};
  if(q('#rel'))q('#rel').onclick=()=>{if(confirm('테스트 서버에서 확인을 마쳤나요?\n운영에 반영하면 1~3분 안에 실서버에 배포됩니다.'))run(()=>post(base()+'/repo/release',{job:j.id}),'운영 반영 완료 - 1~3분 안에 실서버에 배포됩니다')};
  if(q('#jdel'))q('#jdel').onclick=async()=>{if(!confirm('이 작업을 삭제할까요?\n요청·중간 결과·최종본·로그가 모두 지워지고 되돌릴 수 없습니다.'+(j.status==='approved'?'\n(이미 GitHub에 반영된 코드는 그대로 남습니다)':'')))return;try{await post(url+'/delete');toast('삭제했습니다');sel=null;last={};$('#main').innerHTML='<div class="empty">왼쪽에서 작업을 선택하거나 새 요청을 시작하세요.</div>';await loadList()}catch(e){toast(e.message)}};
  if(q('#qago'))q('#qago').onclick=()=>{const a=q('#qa').value.trim();if(!a){toast('답변을 적어주세요');return}run(()=>post(url+'/restart',{feedback:a,start:j.step}),'답변을 반영해 이어서 진행합니다')};
}
function selectJob(id){
  sel=id;tab=null;tabPinned=false;last={list:last.list};
  $('#main').innerHTML='<div id="hd"></div><div id="act"></div><div id="tb"></div><div class="doc"></div>';
  $('#tb').onclick=e=>{const b=e.target.closest('.tab');if(b){tab=b.dataset.t;tabPinned=true;loadDetail(true)}};
  tick(true);
}
$('#jclean').onclick=async()=>{const d=prompt('승인 완료·실패·중단된 작업을 삭제합니다.\n며칠 지난 작업만 지울까요? (0 = 전부)','7');if(d===null)return;const n=parseInt(d);if(isNaN(n)||n<0){toast('숫자를 입력하세요');return}try{const r=await post(base()+'/jobs/delete-many',{older_days:n});toast(r.deleted+'개 작업을 삭제했습니다');if(sel&&!(await api(base()+'/jobs')).jobs.some(x=>x.id===sel)){sel=null;$('#main').innerHTML='<div class="empty">왼쪽에서 작업을 선택하거나 새 요청을 시작하세요.</div>'}last={};await loadList()}catch(e){toast(e.message)}};
$('#jobs').onclick=e=>{const j=e.target.closest('.job');if(j)selectJob(j.dataset.id)};
let ATT=[],EDIT=null,EDNEW=[],EDDROP=[],FOLLOW=null,FUNEW=[];
const fmtB=n=>n>1048576?(n/1048576).toFixed(1)+'MB':Math.ceil(n/1024)+'KB';
function addFiles(list){
  for(const f of list){
    if(ATT.length>=10){toast('첨부는 최대 10개까지입니다');break}
    if(f.size>10*1024*1024){toast(f.name+': 10MB를 넘습니다');continue}
    const name=f.name&&f.name!=='image.png'?f.name:'screenshot-'+new Date().toTimeString().slice(0,8).replace(/:/g,'')+'.png';
    ATT.push({file:f,name,url:f.type.startsWith('image/')?URL.createObjectURL(f):''});
  }
  drawAtt();
}
function drawAtt(){
  $('#attl').innerHTML=ATT.map((a,i)=>'<span class="attc">'+(a.url?'<img src="'+a.url+'" alt="">':'📄')+'<b title="'+esc(a.name)+'">'+esc(a.name)+'</b><span style="color:var(--mute)">'+fmtB(a.file.size)+'</span><button data-rm="'+i+'" title="빼기">×</button></span>').join('');
  $('#attl').querySelectorAll('[data-rm]').forEach(b=>b.onclick=()=>{const a=ATT.splice(+b.dataset.rm,1)[0];if(a&&a.url)URL.revokeObjectURL(a.url);drawAtt()});
}
const b64=f=>new Promise((ok,no)=>{const r=new FileReader();r.onload=()=>ok(String(r.result).split(',')[1]||'');r.onerror=no;r.readAsDataURL(f)});
$('#req').addEventListener('keydown',e=>{if(e.key==='Enter'&&(e.ctrlKey||e.metaKey)){e.preventDefault();$('#go').click()}});
$('#attf').onchange=e=>{addFiles(e.target.files);e.target.value=''};
$('#req').addEventListener('paste',e=>{const fs=[...(e.clipboardData||{}).items||[]].filter(x=>x.kind==='file').map(x=>x.getAsFile()).filter(Boolean);if(fs.length){e.preventDefault();addFiles(fs)}});
{const box=$('#req').closest('.card');box.classList.add('req');
 box.addEventListener('dragover',e=>{e.preventDefault();box.classList.add('drag')});
 box.addEventListener('dragleave',()=>box.classList.remove('drag'));
 box.addEventListener('drop',e=>{e.preventDefault();box.classList.remove('drag');if(e.dataTransfer.files.length)addFiles(e.dataTransfer.files)});}
$('#go').onclick=async()=>{
  const t=$('#req').value.trim();if(!t){toast('요청 내용을 입력하세요');return}
  let files=[];
  if(ATT.length){$('#go').disabled=true;toast('첨부 파일을 올리는 중…');
    try{files=await Promise.all(ATT.map(async a=>({name:a.name,data:await b64(a.file)})))}catch(e){toast('파일을 읽지 못했습니다');$('#go').disabled=false;return}}
  try{const j=await post(base()+'/jobs',{request:t,files});$('#req').value='';ATT.forEach(a=>a.url&&URL.revokeObjectURL(a.url));ATT=[];drawAtt();await loadList();selectJob(j.id)}catch(e){toast(e.message)}
  $('#go').disabled=false;
};

/* ---------- 에이전트 ---------- */
let selAgent=null;
async function loadAgents(){
  pj=await api(base());
  $('#alist').innerHTML=pj.agents.map(a=>'<div class="job'+(a.id===selAgent?' sel':'')+'" data-id="'+esc(a.id)+'"><div class="t">'+esc(a.name)+'</div><div class="m"><span>'+esc(a.workspace)+'</span>'+(a.problems.length?'<span class="chip failed">설정 확인</span>':'<span class="chip approved">정상</span>')+'</div></div>').join('')||'<div class="empty" style="padding:16px">에이전트가 없습니다</div>';
}
function permsHtml(p){
  return '<label class="chk"><input type="checkbox" id="pweb"'+(p.web?' checked':'')+'><span>웹 검색·페이지 읽기 허용<small>인터넷 자료가 필요한 역할만 켜세요</small></span></label>'
    +'<label class="chk"><input type="checkbox" id="pbash"'+(p.bash?' checked':'')+'><span>셸 명령 실행 허용 (Bash)<small>주의: 켜면 에이전트가 파이에서 명령을 실행할 수 있습니다. sudo와 rm은 계속 막힙니다</small></span></label>';
}
async function openAgent(id){
  selAgent=id;
  const a=await api(base()+'/agents/'+encodeURIComponent(id));
  const warn=a.problems.length?'<div class="warnbox"><b>확인이 필요합니다</b><ul>'+a.problems.map(p=>'<li>'+esc(p)+'</li>').join('')+'</ul>아래 [저장]을 누르면 기본 권한 설정을 만들고 폴더 신뢰도 등록합니다.</div>':'';
  const st=a.stages.length?a.stages.map(s=>'<span class="chip running">'+esc(s)+'</span>').join(''):'<span class="chip">담당 단계 없음</span>';
  $('#aedit').innerHTML='<div class="title"><h2>'+esc(a.name)+'</h2></div><div class="badges"><span class="chip">'+esc(a.workspace)+'</span>'+st+'</div>'+warn
    +'<div class="g2"><label class="lb">이름<input type="text" id="an" maxlength="30" value="'+esc(a.name)+'"></label>'
    +'<label class="lb">모델 (비우면 기본값. 예: haiku, sonnet, opus)<input type="text" id="am" value="'+esc(a.model)+'" placeholder="기본값"></label></div>'
    +permsHtml(a.perms)
    +'<label class="lb" style="margin-top:10px">역할 설명 (CLAUDE.md)'+(a.has_md?'':' - 아직 없어서 기본 틀을 채웠습니다')+'<textarea id="amd" class="mono" spellcheck="false">'+esc(a.claude_md)+'</textarea></label>'
    +'<div class="vd">저장하면 이전 내용은 shared/history/_agents 에 백업됩니다. 권한 설정(settings.json)은 위 체크박스 기준으로 다시 만들어집니다.</div>'
    +'<div class="row" style="margin-top:10px"><button class="pri" id="asave">저장</button><button id="aren">폴더 이름 정리</button><button class="dng" id="adel">목록에서 제거</button></div>';
  $('#aren').onclick=async()=>{
    try{const r=await post(base()+'/agents/'+id+'/rename-folder');
      toast(r.changed?('폴더 이름을 "'+r.workspace+'"로 바꿨습니다'):'이미 정리되어 있습니다');
      await loadAgents();await openAgent(id)}catch(e){toast(e.message)}
  };
  $('#asave').onclick=async()=>{
    try{const r=await post(base()+'/agents/'+id+'/save',{name:$('#an').value,model:$('#am').value,claude_md:$('#amd').value,perms:{web:$('#pweb').checked,bash:$('#pbash').checked}});
      toast(r.warning||'저장했습니다');await loadAgents();await openAgent(id)}catch(e){toast(e.message)}
  };
  $('#adel').onclick=async()=>{
    if(!confirm('이 에이전트를 목록에서 제거할까요? 폴더와 파일은 지워지지 않습니다.'))return;
    try{await post(base()+'/agents/'+id+'/remove');selAgent=null;$('#aedit').innerHTML='<div class="empty">제거했습니다.</div>';toast('목록에서 제거했습니다');await loadAgents()}catch(e){toast(e.message)}
  };
  loadAgents();
}
function newAgentForm(){
  selAgent=null;
  $('#aedit').innerHTML='<div class="title"><h2>새 에이전트</h2></div>'
    +'<div class="g2"><label class="lb">이름<input type="text" id="nn" maxlength="30" placeholder="예: 번역가"></label>'
    +'<label class="lb">모델 (선택)<input type="text" id="nm" placeholder="기본값"></label></div>'
    +'<label class="lb">역할 설명 (나중에 자유롭게 고칠 수 있습니다. 비워 두면 기본 틀만 채워집니다)<textarea id="nd" placeholder="예: 전문 번역가다. 원문의 의미와 어조를 보존하며 자연스럽게 옮기고, 고유명사·숫자는 그대로 둔다. 직역으로 어색해지는 표현은 관용구로 바꾸되 내용을 더하거나 빼지 않는다."></textarea></label>'
    +permsHtml({web:false,bash:false})
    +'<label class="lb">이미 만들어 둔 폴더를 연결하려면 폴더 이름 입력 (선택)<input type="text" id="nw" placeholder="비워 두면 새 폴더를 자동으로 만듭니다"></label>'
    +'<div class="row"><button class="pri" id="ncreate">에이전트 만들기</button></div>';
  $('#ncreate').onclick=async()=>{
    try{const r=await post(base()+'/agents',{name:$('#nn').value,model:$('#nm').value,description:$('#nd').value,workspace:$('#nw').value,perms:{web:$('#pweb').checked,bash:$('#pbash').checked}});
      toast(r.warning||'만들었습니다');await loadAgents();await openAgent(r.agent.id)}catch(e){toast(e.message)}
  };
  loadAgents();
}
$('#alist').onclick=e=>{const j=e.target.closest('.job');if(j)openAgent(j.dataset.id).catch(x=>toast(x.message))};
$('#anew').onclick=newAgentForm;
$('#arenall').onclick=async()=>{
  if(!confirm('이 프로젝트의 모든 에이전트 폴더 이름을 정리할까요? 실행 중인 작업이 없을 때만 됩니다.'))return;
  try{const r=await post(base()+'/agents/rename-all');
    const n=r.results.filter(x=>x.changed).length;
    toast(n?n+'개 폴더 이름을 정리했습니다':'이미 전부 정리되어 있습니다');
    await loadAgents();if(selAgent)await openAgent(selAgent)}catch(e){toast(e.message)}
};
$('#aimp').onclick=async()=>{
  const host=$('#imppanel2');
  host.innerHTML='<div class="card"><h2>기존 에이전트 가져오기</h2><div class="vd">불러오는 중...</div></div>';
  let d;try{d=await api('/api/all-agents')}catch(e){toast(e.message);host.innerHTML='';return}
  const list=d.agents.filter(a=>a.pid!==cur);
  if(!list.length){host.innerHTML='<div class="card"><h2>기존 에이전트 가져오기</h2><div class="empty" style="padding:16px">다른 프로젝트에 가져올 에이전트가 없습니다</div></div>';return}
  host.innerHTML='<div class="card"><h2>기존 에이전트 가져오기</h2>'
    +'<div class="vd" style="margin-bottom:8px">선택하면 이 프로젝트로 복사됩니다. 복사본이라 고쳐도 원본에는 영향이 없습니다.</div>'
    +'<div class="jobs" style="margin-top:0;max-height:50vh">'+list.map((a,i)=>'<div class="job" data-i="'+i+'"><div class="t">'+esc(a.name)+' <span class="tag">'+esc(a.pname)+'</span>'+(a.web?' <span class="tag">웹</span>':'')+(a.model?' <span class="tag">'+esc(a.model)+'</span>':'')+'</div><div class="m">'+esc((a.role||'').slice(0,90))+'</div></div>').join('')+'</div>'
    +'<div class="row" style="margin-top:10px"><button id="imp2close">닫기</button></div></div>';
  host.querySelectorAll('.job').forEach(el=>el.onclick=async()=>{
    const a=list[+el.dataset.i];
    try{const r=await post(base()+'/agents/import',{from:a.pid,agent:a.id});toast(r.note||'가져왔습니다');host.innerHTML='';await loadAgents();await openAgent(r.agent.id)}catch(e){toast(e.message)}});
  $('#imp2close').onclick=()=>{host.innerHTML=''};
};

/* ---------- 구성 추천 (프리셋 / AI) ---------- */
function planHtml(p){
  const an={},sn={};p.agents.forEach(a=>an[a.key]=a.name);p.stages.forEach(s=>sn[s.id]=s.name);
  return '<div class="plan"><div class="ph">에이전트 '+p.agents.length+'명</div>'
    +p.agents.map(a=>'<div class="pa"><b>'+esc(a.name)+'</b>'+(a.web?' <span class="tag">웹</span>':'')+(a.model?' <span class="tag">'+esc(a.model)+'</span>':'')+'<div class="vd">'+esc(a.role)+'</div></div>').join('')
    +'<div class="ph">단계 '+p.stages.length+'개 (호출 최소 '+p.stages.length+'회/작업)</div><ol class="pst">'
    +p.stages.map(s=>'<li><b>'+esc(s.name)+'</b> <span class="tag">'+(s.kind==='review'?'검토':'작업')+'</span> '+esc(an[s.agent]||s.agent)+(s.kind==='review'?' → '+esc(sn[s.target]||'')+' 검토':'')+'<div class="vd">'+esc(s.instruction)+'</div></li>').join('')+'</ol></div>';
}
const presetOpts=()=>presets.map((p,i)=>'<option value="'+i+'">'+esc(p.label)+'</option>').join('');
function countSel(sid,aid){
  const o=(n,lab)=>'<option value="'+n+'">'+lab+'</option>';
  return '<label class="inl">단계 수<select id="'+sid+'" style="width:auto">'+o(0,'자동')+[2,3,4,5,6,7,8].map(n=>o(n,n+'개')).join('')+'</select></label>'
    +'<label class="inl">에이전트 수<select id="'+aid+'" style="width:auto">'+o(0,'자동')+[2,3,4,5,6].map(n=>o(n,n+'명')).join('')+'</select></label>';
}

/* ---------- 단계 ---------- */
let ES=[],planCur=null;
async function loadStages(){
  pj=await api(base());
  if(!presets.length)presets=(await api('/api/presets')).presets;
  ES=JSON.parse(JSON.stringify(pj.stages));planCur=null;
  const autoNote=pj.stage_mode==='auto'?'<div class="warnbox">이 프로젝트는 <b>요청별 자동 구성</b>으로 설정되어 있습니다. 실제 작업은 매번 AI가 새로 설계한 단계로 실행되고, 아래 구성은 설계가 실패했을 때만 쓰이는 대체용입니다. 고정 구성으로 되돌리려면 설정 화면에서 바꾸세요.</div>':'';
  $('#v-stages').innerHTML=autoNote+'<div class="card"><h2>단계 추천</h2>'
    +'<div class="vd" style="margin:0 0 8px">프리셋은 토큰이 들지 않습니다. AI 추천은 1회 호출(토큰 소량 사용)로 프로젝트 설명에 맞는 구성을 제안합니다. 적용 전에 미리보기로 확인하세요.</div>'
    +'<div class="row"><select id="prs" style="flex:1"><option value="">프리셋 선택...</option>'+presetOpts()+'</select></div>'
    +'<label class="lb" style="margin-top:10px">AI 추천용 프로젝트 설명<textarea id="pd2" placeholder="어떤 작업을 하는 프로젝트인지 적어주세요">'+esc(pj.description)+'</textarea></label>'
    +'<div class="row">'+countSel('pcs','pca')+'<button id="paib">AI 추천 받기</button></div><div id="pprev"></div>'
    +'<div class="row" id="papply" hidden><button class="pri" id="papplyb">이 구성으로 교체</button><span class="vd">기존 단계는 대체되고, 추천 에이전트가 새로 만들어집니다. 기존 에이전트는 그대로 남습니다.</span></div></div>'
    +'<div class="card"><h2>단계 파이프라인 (위에서 아래로 실행)</h2>'
    +'<div class="vd" style="margin:0 0 6px">검토 단계가 수정요청(REVISE)을 내면 대상 단계로 돌아가 다시 수행합니다 (프로젝트 설정의 반복 횟수까지). 불필요한 단계는 \'사용\'을 꺼서 토큰을 아낄 수 있습니다.</div>'
    +'<div id="stlist"></div><div class="row"><button id="stadd">+ 단계 추가</button><button class="pri" id="stsave">저장</button></div></div>';
  $('#prs').onchange=e=>{const v=e.target.value;if(v===''){return}planCur=presets[+v].plan;showPlan(presets[+v].desc)};
  $('#paib').onclick=async()=>{
    const d=$('#pd2').value.trim();if(!d){toast('프로젝트 설명을 적어주세요');return}
    $('#paib').disabled=true;$('#paib').textContent='추천 생성 중...';
    try{const r=await post('/api/plan',{name:pj.name,description:d,stages:+$('#pcs').value,agents:+$('#pca').value});planCur=r.plan;showPlan('AI 추천 사용량: 입력 '+fmtN(r.usage.input)+' · 출력 '+fmtN(r.usage.output)+' · 캐시 '+fmtN((+r.usage.cache_write||0)+(+r.usage.cache_read||0)))}catch(e){toast(e.message)}
    $('#paib').disabled=false;$('#paib').textContent='AI 추천 받기';
  };
  $('#papplyb').onclick=async()=>{
    if(!planCur||!confirm('현재 단계를 이 구성으로 교체할까요?'))return;
    try{await post(base()+'/apply-plan',{plan:planCur});toast('적용했습니다');await loadProjects();await loadStages()}catch(e){toast(e.message)}
  };
  const L=$('#stlist');
  L.addEventListener('input',e=>{
    const c=e.target.closest('.sc');if(!c)return;const f=e.target.dataset.f;if(!f||e.target.type==='checkbox')return;
    if(f==='name'||f==='instruction')ES[+c.dataset.i][f]=e.target.value;
    else if(f==='max_turns')ES[+c.dataset.i][f]=parseInt(e.target.value)||0;
  });
  L.addEventListener('change',e=>{
    const c=e.target.closest('.sc');if(!c)return;const i=+c.dataset.i,f=e.target.dataset.f;if(!f)return;const s=ES[i];
    if(f==='enabled'||f==='polish')s[f]=e.target.checked;
    else if(f==='inputs'){const v=e.target.dataset.v;s.inputs=s.inputs.filter(x=>x!==v);if(e.target.checked)s.inputs.push(v)}
    else if(f==='kind'){s.kind=e.target.value;if(s.kind==='review'&&!s.target&&i>0)s.target=ES[i-1].id;if(s.kind==='work'){s.target='';s.polish=false}}
    else if(f==='name'){s.name=e.target.value}
    else if(f==='max_turns'){s.max_turns=parseInt(e.target.value)||0;return}
    else s[f]=e.target.value;
    if(['enabled','kind','name','target'].includes(f))renderStages();
  });
  L.addEventListener('click',e=>{
    const b=e.target.closest('button[data-a]');if(!b)return;const i=+b.closest('.sc').dataset.i,a=b.dataset.a;
    if(a==='up'&&i>0)[ES[i-1],ES[i]]=[ES[i],ES[i-1]];
    else if(a==='down'&&i<ES.length-1)[ES[i+1],ES[i]]=[ES[i],ES[i+1]];
    else if(a==='del'){
      if(ES.length<=1){toast('단계는 최소 1개가 필요합니다');return}
      const id=ES[i].id;ES.splice(i,1);
      ES.forEach((s,k)=>{s.inputs=s.inputs.filter(x=>x!==id);if(s.target===id){s.target=k>0?ES[k-1].id:'';if(!s.target)s.kind='work'}});
    }
    renderStages();
  });
  $('#stadd').onclick=()=>{
    const ids=new Set(ES.map(s=>s.id));let n=1;while(ids.has('s'+n))n++;
    ES.push({id:'s'+n,name:'새 단계',kind:'work',agent:pj.agents[0]?pj.agents[0].id:'',target:'',inputs:[],instruction:'',enabled:true,max_turns:0,polish:false});
    renderStages();
  };
  $('#stsave').onclick=async()=>{
    try{await post(base()+'/stages',{stages:ES});toast('단계를 저장했습니다');await loadProjects();await loadStages()}catch(e){toast(e.message)}
  };
  renderStages();
}
function showPlan(note){$('#pprev').innerHTML=(note?'<div class="vd">'+esc(note)+'</div>':'')+planHtml(planCur);$('#papply').hidden=false}
function renderStages(){
  const ao=sel_=>pj.agents.map(a=>'<option value="'+esc(a.id)+'"'+(a.id===sel_?' selected':'')+'>'+esc(a.name)+'</option>').join('');
  $('#stlist').innerHTML=ES.map((s,i)=>{
    const prev=ES.slice(0,i);
    return '<div class="sc'+(s.enabled?'':' off')+'" data-i="'+i+'"><div class="sch"><b>'+(i+1)+'</b>'
      +'<label class="inl"><input type="checkbox" data-f="enabled"'+(s.enabled?' checked':'')+'> 사용</label>'
      +'<input type="text" data-f="name" value="'+esc(s.name)+'" maxlength="30">'
      +'<select data-f="kind"><option value="work"'+(s.kind==='work'?' selected':'')+'>작업</option><option value="review"'+(s.kind==='review'?' selected':'')+(i?'':' disabled')+'>검토</option></select>'
      +'<button data-a="up"'+(i?'':' disabled')+'>↑</button><button data-a="down"'+(i<ES.length-1?'':' disabled')+'>↓</button><button class="dng" data-a="del">삭제</button></div>'
      +'<div class="scb"><div class="g2"><label class="lb">담당 에이전트<select data-f="agent">'+ao(s.agent)+'</select></label>'
      +(s.kind==='review'?'<label class="lb">검토 대상 단계<select data-f="target">'+prev.map(p=>'<option value="'+esc(p.id)+'"'+(p.id===s.target?' selected':'')+'>'+esc(p.name)+'</option>').join('')+'</select></label>'
        :'<label class="lb">최대 턴 (0=기본 '+15+')<input type="text" data-f="max_turns" value="'+(s.max_turns||0)+'"></label>')+'</div>'
      +(s.kind==='review'?'<label class="lb">최대 턴 (0=기본 8)<input type="text" data-f="max_turns" value="'+(s.max_turns||0)+'" style="width:100px"></label>':'')
      +(prev.length?'<div class="vd">함께 읽을 이전 단계 결과 (요청 파일은 항상 포함)</div><div class="row" style="margin-bottom:8px">'+prev.filter(p=>p.id!==s.target).map(p=>'<label class="inl"><input type="checkbox" data-f="inputs" data-v="'+esc(p.id)+'"'+(s.inputs.includes(p.id)?' checked':'')+'> '+esc(p.name)+'</label>').join('')+'</div>':'')
      +'<label class="lb">지시<textarea data-f="instruction" rows="3" style="min-height:64px">'+esc(s.instruction)+'</textarea></label>'
      +(s.kind==='review'?'<label class="chk"><input type="checkbox" data-f="polish"'+(s.polish?' checked':'')+'><span>승인 시 다듬은 최종본 작성<small>켜면 이 검토 단계가 최종본(final)을 만듭니다. 끄면 마지막 작업 단계의 결과가 최종본이 됩니다</small></span></label>':'')
      +'</div></div>';
  }).join('');
}

/* ---------- 참고 자료 ---------- */
const SRCMODE={off:['사용 안 함','자료를 프롬프트에 넣지 않습니다'],
  prefer:['우선 참고 (권장)','이 자료를 먼저 근거로 삼고, 부족하면 다른 방법으로 보완합니다'],
  only:['이 자료만 사용','자료에 없는 내용은 추측하지 않고 「제공된 자료에 없음」이라고 밝힙니다']};
let srcEdit=null;
async function loadSources(){
  const d=await api(base()+'/sources');
  const list=d.sources.length?d.sources.map(s=>'<div class="sc"><div class="sch"><b>자</b><input type="text" value="'+esc(s.name)+'" readonly style="flex:1;border:0;background:none">'
    +'<span class="vd">'+fmtN(s.size)+'B</span><button data-edit="'+esc(s.name)+'">편집</button><button class="dng" data-del="'+esc(s.name)+'">삭제</button></div>'
    +'<div class="scb"><div class="vd" style="white-space:pre-wrap">'+esc(s.preview)+(s.size>200?' …':'')+'</div></div></div>').join(''):'<div class="empty" style="padding:20px">등록된 자료가 없습니다</div>';
  $('#v-sources').innerHTML='<div class="card"><h2>참고 자료 (내가 제공하는 근거)</h2>'
    +'<div class="vd" style="margin:0 0 8px">여기에 넣은 자료를 에이전트가 읽고 근거로 씁니다. 서비스 설명, 내부 규정, 가격표, 자주 묻는 질문처럼 답변의 바탕이 될 내용을 넣으세요.</div>'
    +'<label class="lb">자료 사용 방식<select id="smd" style="width:auto">'+Object.keys(SRCMODE).map(k=>'<option value="'+k+'"'+(d.mode===k?' selected':'')+'>'+SRCMODE[k][0]+'</option>').join('')+'</select></label>'
    +'<div class="vd">'+esc(SRCMODE[d.mode][1])+'</div></div>'
    +'<div class="card"><h2>자료 목록 ('+d.sources.length+')</h2>'+list
    +'<div class="row" style="margin-top:10px"><button class="pri" id="srcnew">+ 자료 추가</button></div>'
    +'<div class="vd" style="margin-top:8px">파일을 직접 넣어도 됩니다: <code>'+esc(d.dir)+'</code> 폴더에 .md 또는 .txt 파일을 복사하면 여기에 나타납니다.</div></div>'
    +'<div id="dbcard"></div><div id="srcform"></div>';
  loadDb().catch(()=>{});
  $('#smd').onchange=async e=>{try{await post(base()+'/sources/mode',{mode:e.target.value});toast('저장했습니다');await loadSources()}catch(err){toast(err.message)}};
  $('#srcnew').onclick=()=>srcForm('','');
  document.querySelectorAll('[data-del]').forEach(b=>b.onclick=async()=>{
    if(!confirm(b.dataset.del+' 자료를 삭제할까요?'))return;
    try{await post(base()+'/sources/delete',{name:b.dataset.del});toast('삭제했습니다');await loadSources()}catch(e){toast(e.message)}});
  document.querySelectorAll('[data-edit]').forEach(b=>b.onclick=async()=>{
    try{const full=await post(base()+'/sources/read',{name:b.dataset.edit});srcForm(full.name,full.content)}catch(e){toast(e.message)}});
  if(srcEdit){srcForm(srcEdit.name,srcEdit.content);srcEdit=null}
}
async function loadDb(){
  const d=await api(base()+'/db');
  const L=d.last;
  const st=L?(L.ok?'<span class="chip approved">성공</span> ':'<span class="chip failed">실패</span> ')+esc(L.at)+' ('+esc(L.who||'')+') · '+esc(L.msg):'아직 가져온 적 없음';
  $('#dbcard').innerHTML='<div class="card"><h2>DB 구조 자료 (자동)</h2>'
    +'<div class="vd" style="margin:0 0 8px">파이 .env에 넣어 둔 <b>읽기 전용</b> DB 계정으로 테이블·컬럼·프로시저·뷰·코드값을 뽑아 에이전트 자료로 넣습니다. 에이전트는 목차를 먼저 보고 필요한 것만 읽으며, DB 비밀번호는 에이전트에게 전달되지 않습니다.</div>'
    +'<label class="lb">환경 변수 접두어<input type="text" id="dbpre" value="'+esc(d.prefix)+'" placeholder="예: MYMA_DB → MYMA_DB_HOST, _PORT, _USER, _PASSWORD, _NAME"></label>'
    +'<label class="lb">실제 값까지 넣을 코드 테이블 (쉼표로 구분, * 사용 가능)<input type="text" id="dbct" value="'+esc(d.code_tables)+'"></label>'
    +'<label class="lb" style="display:flex;gap:6px;align-items:center"><input type="checkbox" id="dbauto"'+(d.auto?' checked':'')+' style="width:auto"> 매일 새벽 3시 40분에 자동으로 다시 가져오기</label>'
    +'<div class="vd">연결: '+(d.prefix?(d.ready?esc(d.target):'<span class="chip failed">.env에 없음</span> '+esc(d.missing.join(', '))):'접두어를 입력하고 저장하세요')+'</div>'
    +'<div class="vd">마지막: '+st+'</div>'
    +'<div class="row" style="margin-top:10px"><button id="dbsave">저장</button><button class="pri" id="dbrun"'+(d.ready&&!d.running?'':' disabled')+'>'+(d.running?'가져오는 중…':'지금 가져오기')+'</button>'
    +(d.has?'<button id="dbview">목차 보기</button>':'')+'</div><div id="dbtoc"></div></div>';
  $('#dbsave').onclick=async()=>{try{await post(base()+'/db',{prefix:$('#dbpre').value.trim(),code_tables:$('#dbct').value.trim(),auto:$('#dbauto').checked});toast('저장했습니다');await loadDb()}catch(e){toast(e.message)}};
  $('#dbrun').onclick=async()=>{const b=$('#dbrun');b.disabled=true;b.textContent='가져오는 중…';
    try{const r=await post(base()+'/db/refresh',{});toast(r.last&&r.last.ok?'가져왔습니다':'실패: '+(r.last?r.last.msg:''))}catch(e){toast(e.message)}await loadDb()};
  if($('#dbview'))$('#dbview').onclick=async()=>{const t=$('#dbtoc');if(t.innerHTML){t.innerHTML='';return}
    try{const r=await api(base()+'/db/readme');t.innerHTML='<pre class="mono" style="max-height:420px;overflow:auto;white-space:pre-wrap;margin-top:10px">'+esc(r.content)+'</pre>'}catch(e){toast(e.message)}};
}
function srcForm(name,content){
  $('#srcform').innerHTML='<div class="card"><h2>'+(name?'자료 편집: '+esc(name):'새 자료')+'</h2>'
    +'<label class="lb">제목 (파일 이름)<input type="text" id="srcn" maxlength="60" value="'+esc(name)+'" placeholder="예: 서비스 소개.md"'+(name?' readonly':'')+'></label>'
    +'<label class="lb">내용<textarea id="srcc" class="mono" placeholder="답변의 근거가 될 내용을 붙여넣으세요">'+esc(content)+'</textarea></label>'
    +'<div class="row"><button class="pri" id="srcsave">저장</button><button id="srccancel">취소</button></div></div>';
  $('#srcsave').onclick=async()=>{
    const n=$('#srcn').value.trim(),c=$('#srcc').value;
    if(!n){toast('제목을 입력하세요');return}
    if(!c.trim()){toast('내용을 입력하세요');return}
    try{await post(base()+'/sources',{name:n,content:c});toast('저장했습니다');await loadSources()}catch(e){toast(e.message)}
  };
  $('#srccancel').onclick=()=>{$('#srcform').innerHTML=''};
  $('#srcform').scrollIntoView({behavior:'smooth',block:'nearest'});
}

/* ---------- 예약 ---------- */
const DAYS=['월','화','수','목','금','토','일'];
let SC=[];
async function loadSched(){
  pj=await api(base());
  SC=JSON.parse(JSON.stringify(pj.schedules||[]));
  $('#v-sched').innerHTML='<div class="card"><h2>예약 작업</h2>'
    +'<div class="vd" style="margin:0 0 6px">정한 시각에 요청이 자동으로 실행됩니다. 자동 승인을 켜두면 사람 확인 없이 완료되고, 텔레그램이 연결돼 있으면 결과가 바로 전송됩니다. 뉴스 봇처럼 매일 받아보는 용도에 쓰세요.</div>'
    +'<div class="vd" style="margin:0 0 10px">실행마다 이 프로젝트의 단계 수만큼 호출이 일어납니다. 매일 돌리는 예약은 단계를 적게 두는 편이 좋습니다. 서버가 꺼져 있던 시각의 예약은 건너뜁니다.</div>'
    +'<div id="sclist"></div><div class="row"><button id="scadd">+ 예약 추가</button><button class="pri" id="scsave">저장</button></div></div>';
  const L=$('#sclist');
  L.addEventListener('input',e=>{const c=e.target.closest('.sc');if(!c)return;const f=e.target.dataset.f;if(f&&e.target.type!=='checkbox')SC[+c.dataset.i][f]=e.target.value});
  L.addEventListener('change',e=>{
    const c=e.target.closest('.sc');if(!c)return;const i=+c.dataset.i,f=e.target.dataset.f;if(!f)return;const x=SC[i];
    if(f==='days'){const v=+e.target.dataset.v;x.days=x.days.filter(d=>d!==v);if(e.target.checked)x.days.push(v)}
    else if(e.target.type==='checkbox'){x[f]=e.target.checked;if(f==='enabled')renderSched()}
    else x[f]=e.target.value;
  });
  L.addEventListener('click',e=>{
    const b=e.target.closest('button[data-a]');if(!b)return;
    if(b.dataset.a==='del'){SC.splice(+b.closest('.sc').dataset.i,1);renderSched()}
  });
  $('#scadd').onclick=()=>{SC.push({id:'',name:'새 예약',time:'07:30',days:[0,1,2,3,4],request:'',auto_approve:true,enabled:true,last_run:''});renderSched()};
  $('#scsave').onclick=async()=>{
    try{await post(base()+'/schedules',{schedules:SC});toast('예약을 저장했습니다');await loadProjects();await loadSched()}catch(e){toast(e.message)}
  };
  renderSched();
}
function renderSched(){
  $('#sclist').innerHTML=SC.length?SC.map((x,i)=>'<div class="sc'+(x.enabled?'':' off')+'" data-i="'+i+'"><div class="sch">'
    +'<label class="inl"><input type="checkbox" data-f="enabled"'+(x.enabled?' checked':'')+'> 사용</label>'
    +'<input type="text" data-f="name" value="'+esc(x.name)+'" maxlength="30">'
    +'<label class="inl">시각<input type="text" data-f="time" value="'+esc(x.time)+'" placeholder="07:30" style="width:70px"></label>'
    +'<button class="dng" data-a="del">삭제</button></div>'
    +'<div class="scb"><div class="row" style="margin-bottom:8px">'+DAYS.map((d,n)=>'<label class="inl"><input type="checkbox" data-f="days" data-v="'+n+'"'+(x.days.includes(n)?' checked':'')+'> '+d+'</label>').join('')+'</div>'
    +'<label class="lb">요청 내용 (작업 화면에 입력하는 것과 같습니다)<textarea data-f="request" rows="3" style="min-height:64px" placeholder="예: 오늘 국내 IT 뉴스 중 중요한 5건을 요약해줘">'+esc(x.request)+'</textarea></label>'
    +'<label class="chk"><input type="checkbox" data-f="auto_approve"'+(x.auto_approve?' checked':'')+'><span>자동 승인<small>끄면 완료 후 텔레그램으로 승인 버튼이 오고, 승인해야 결과가 전송됩니다</small></span></label>'
    +(x.last_run?'<div class="vd">마지막 실행: '+esc(x.last_run)+'</div>':'')
    +'</div></div>').join(''):'<div class="empty" style="padding:20px">등록된 예약이 없습니다</div>';
}

/* ---------- 설정 ---------- */
function tgCard(t){
  if(!t.configured)return '<div class="card"><h2>텔레그램 (모바일에서 사용)</h2>'
    +'<div class="vd">아직 봇 토큰이 없습니다. 텔레그램에서 <b>@BotFather</b> 에게 <b>/newbot</b> 으로 봇을 만든 뒤, 받은 토큰을 파이의 <b>~/agents/.env</b> 에 아래처럼 추가하고 서버를 다시 켜세요.</div>'
    +'<pre style="background:var(--chip);padding:10px;border-radius:8px;font-size:13px;overflow:auto">TELEGRAM_BOT_TOKEN=받은토큰</pre>'
    +'<div class="vd">연결하면 휴대폰에서 작업을 요청하고, 완료 알림과 승인 버튼을 받을 수 있습니다. 예약 작업 결과도 여기로 옵니다.</div></div>';
  return '<div class="card"><h2>텔레그램 (모바일에서 사용)</h2>'
    +'<div class="vd">봇과의 대화창에서 아래 명령을 한 번 보내면 연결됩니다. 연결된 대화만 작업을 요청할 수 있습니다.</div>'
    +'<pre style="background:var(--chip);padding:10px;border-radius:8px;font-size:14px">/pair '+esc(t.pair_code)+'</pre>'
    +'<div class="vd">연결 코드는 서버를 다시 켤 때마다 새로 만들어집니다. 이미 연결된 대화는 그대로 유지됩니다.</div>'
    +'<div style="margin:10px 0">연결된 대화: '+(t.chats.length?t.chats.map(c=>'<span class="chip approved">'+esc(c)+(t.cur[c]?' · '+esc(t.cur[c]):'')+'</span> <button data-unpair="'+esc(c)+'" style="padding:2px 8px">해제</button>').join(' '):'<span class="chip">없음</span>')+'</div>'
    +'<label class="chk"><input type="checkbox" id="tgn"'+(t.notify?' checked':'')+'><span>완료·실패 알림 보내기<small>GUI에서 시작한 작업의 알림도 연결된 모든 대화로 보냅니다</small></span></label>'
    +'<div class="row" style="margin-top:8px"><button class="pri" id="tgsave">저장</button><button id="tgtest">테스트 메시지 보내기</button></div></div>';
}
function fmtLeft(x){if(x<0)return '영구';if(x>=86400)return Math.ceil(x/86400)+'일';if(x>=3600)return Math.ceil(x/3600)+'시간';return Math.ceil(x/60)+'분'}
function secCard(s){
  const bad=[];
  if(s.weak_password)bad.push('비밀번호가 12자 미만입니다. 외부에 열려 있으니 16자 이상으로 바꾸세요 (.env의 GUI_PASSWORD).');
  if(s.host!=='127.0.0.1'&&!s.https)bad.push('암호화 없이 외부에 열려 있습니다. HTTPS 리버스 프록시를 두세요.');
  if(s.https&&!s.proxy)bad.push('TRUST_PROXY가 꺼져 있어 실제 접속 IP를 알 수 없습니다. 차단이 동작하지 않습니다.');
  if(s.proxy_seen&&s.proxy_seen.ts&&!s.proxy_seen.xff)bad.push('NAS 리버스 프록시가 실제 접속 IP(X-Forwarded-For)를 넘겨주지 않습니다. 이 상태에서는 IP 차단을 하지 않습니다(NAS 전체가 막히므로).');
  if(s.two_factor&&!s.two_factor_ready)bad.push('2단계 인증이 켜져 있지만 텔레그램이 연결되지 않아 적용되지 않고 있습니다.');
  const ev=s.events||[];
  return '<div class="card"><h2>보안</h2>'
    +'<div class="row" style="margin-bottom:8px"><span class="chip '+(s.https?'approved':'failed')+'">HTTPS '+(s.https?'사용':'미설정')+'</span>'
    +'<span class="chip '+(s.proxy_seen&&s.proxy_seen.xff?'approved':'')+'">실제 IP 인식 '+(s.proxy_seen&&s.proxy_seen.ts?(s.proxy_seen.xff?'정상':'안 됨'):'확인 전')+'</span>'
    +'<span class="chip '+(s.two_factor&&s.two_factor_ready?'approved':'failed')+'">외부 로그인 2단계 인증 '+(s.two_factor&&s.two_factor_ready?'적용':'미적용')+'</span>'
    +'<span class="chip">차단 중 IP '+s.blocked_total+'</span><span class="chip">로그인 세션 '+s.sessions+'</span>'
    +(s.lockdown?'<span class="chip failed">외부 로그인 잠김 '+fmtLeft(s.lockdown)+'</span>':'')+'</div>'
    +(bad.length?'<div class="warnbox"><b>확인이 필요합니다</b><ul>'+bad.map(x=>'<li>'+esc(x)+'</li>').join('')+'</ul></div>':'')
    +'<ul class="tip"><li>비밀번호 '+s.max_fails+'회 실패 → 1일 차단, 다시 걸리면 7일, 세 번째는 영구 차단</li><li>.env·.git·wp-admin·phpmyadmin 같은 해킹 경로 접근 → 즉시 7일 이상 차단</li><li>로그인 없이 없는 주소를 10분에 8번 이상 요청 → 차단 · 1분에 600회 넘는 요청 → 차단</li><li>1시간에 로그인 실패가 20번을 넘으면(여러 IP 동시 공격) 외부 로그인 전체를 1시간 잠금. 내부망은 계속 가능</li><li>외부에서는 기본 인증(Authorization 헤더)을 받지 않고, 차단된 IP에는 화면 없이 연결을 끊습니다</li></ul>'
    +'<label class="lb"><input type="checkbox" id="s2fa"'+(s.two_factor?' checked':'')+'> 외부 로그인 시 텔레그램 확인 코드 요구 (2단계 인증)</label>'
    +'<div class="g2"><label class="lb">외부 로그인 유지 시간 (시간)<input type="number" id="sexh" min="1" max="720" value="'+s.ext_session_hours+'"></label><span></span></div>'
    +'<label class="lb">외부 접속 허용 IP/대역 (비우면 모두 허용 · 쉼표나 줄바꿈으로 구분 · 넣으면 목록 밖은 전부 거부)<textarea id="sallow" style="min-height:48px" placeholder="예: 211.234.0.0/16, 58.228.63.106">'+esc((s.allow||[]).join('\n'))+'</textarea></label>'
    +'<div class="row" style="margin-top:4px"><button class="pri" id="ssec">보안 설정 저장</button>'+(s.lockdown?'<button id="sunlock">외부 로그인 잠금 해제</button>':'')+'<button class="dng" id="slog">모든 기기에서 로그아웃</button></div>'
    +'<div class="vd" style="margin-top:12px">차단 중인 IP</div><table class="ut"><tr><th>IP</th><th>남은 시간</th><th>이유</th><th></th></tr>'
    +(s.blocked.length?s.blocked.map(b=>'<tr><td>'+esc(b.ip)+'</td><td>'+fmtLeft(b.left)+'</td><td>'+esc(b.reason)+'</td><td><button data-unban="'+esc(b.ip)+'" style="font-size:12px;padding:3px 8px">해제</button></td></tr>').join(''):'<tr><td colspan="4">없음</td></tr>')
    +'</table>'+(s.blocked.length>1?'<div class="row" style="margin-top:6px"><button id="sunall" style="font-size:12px">전체 해제</button></div>':'')
    +'<div class="vd" style="margin-top:12px">최근 보안 기록</div><table class="ut"><tr><th>시각</th><th>IP</th><th>내용</th></tr>'
    +(ev.length?ev.slice(0,15).map(e=>'<tr><td>'+esc(e.ts.slice(5,16))+'</td><td>'+esc(e.ip)+'</td><td'+(e.kind==='err'?' style="color:var(--err)"':'')+'>'+esc(e.msg)+'</td></tr>').join(''):'<tr><td colspan="3">기록 없음</td></tr>')
    +'</table></div>';
}
function bindSec(){
  const p=async(b,msg)=>{try{await post('/api/security',b);toast(msg);await loadSettings()}catch(e){toast(e.message)}};
  $('#ssec').onclick=()=>p({two_factor:$('#s2fa').checked,ext_session_hours:+$('#sexh').value,allow:$('#sallow').value},'저장했습니다');
  if($('#sunlock'))$('#sunlock').onclick=()=>p({unlock:true},'잠금을 해제했습니다');
  if($('#sunall'))$('#sunall').onclick=()=>{if(confirm('차단을 모두 해제할까요?'))p({unban_all:true},'모두 해제했습니다')};
  document.querySelectorAll('[data-unban]').forEach(b=>b.onclick=()=>{if(confirm(b.dataset.unban+' 차단을 해제할까요?'))p({unban:b.dataset.unban},'해제했습니다')});
}
async function loadSettings(){
  pj=await api(base());
  const tg=await api('/api/telegram');
  const sec=await api('/api/security');
  const rp=await api(base()+'/repo');
  const fl=Object.keys(flags).map(k=>'<span class="chip '+(flags[k]?'approved':'')+'">'+esc(k)+' '+(flags[k]?'사용':'미지원')+'</span>').join(' ');
  $('#v-settings').innerHTML='<div class="card"><h2>프로젝트 설정</h2>'
    +'<label class="lb">이름<input type="text" id="sn" maxlength="40" value="'+esc(pj.name)+'"></label>'
    +'<label class="lb">설명<textarea id="sd" style="min-height:64px">'+esc(pj.description)+'</textarea></label>'
    +'<label class="lb">검토 단계의 수정요청 최대 반복 횟수<select id="sr" style="width:auto">'+[0,1,2,3].map(n=>'<option value="'+n+'"'+(pj.max_rounds===n?' selected':'')+'>'+n+'회'+(n===1?' (권장)':n===0?' (반복 안 함, 최저 비용)':'')+'</option>').join('')+'</select></label>'
    +'<div class="vd">반복 1회마다 2~3번의 호출이 추가됩니다. 비용을 줄이려면 1회 이하를 권장합니다.</div>'
    +'<label class="lb" style="margin-top:12px">요청 처리 방식<select id="smode" style="width:auto">'
    +'<option value="fixed"'+(pj.stage_mode!=='auto'?' selected':'')+'>고정 파이프라인 (아래 \'단계\'에서 정한 구성을 항상 그대로 실행)</option>'
    +'<option value="auto"'+(pj.stage_mode==='auto'?' selected':'')+'>요청별 자동 구성 (AI가 요청마다 에이전트·단계 수를 다시 설계)</option>'
    +'</select></label>'
    +'<div class="vd">자동 구성은 매 요청마다 설계 호출이 1회 추가됩니다. 대신 간단한 요청은 단계를 줄이고, 복잡한 요청만 단계를 늘려 전체적으로는 토큰을 아낄 수 있습니다. \'단계\' 화면의 구성은 자동 설계가 실패했을 때 쓰이는 대체 파이프라인으로 남습니다.</div>'
    +'<div class="row" style="margin-top:8px"><button class="pri" id="ssave">저장</button><button class="dng" id="sdel">프로젝트 제거</button></div>'
    +'<div class="vd">작업 폴더: '+esc(pj.root==='.'?'~/agents (기존 작업 공간)':'~/agents/'+pj.root)+'</div></div>'
    +'<div class="card"><h2>전체 설정 (모든 프로젝트 공통)</h2>'
    +'<div class="g2"><label class="lb">동시에 실행할 작업 수<select id="gp">'+[1,2,3].map(n=>'<option value="'+n+'"'+(settings.parallel===n?' selected':'')+'>'+n+'개'+(n===1?' (라즈베리파이 권장)':'')+'</option>').join('')+'</select></label>'
    +'<label class="lb">작업당 토큰 한도 (0=무제한, 새 토큰 기준)<input type="text" id="gt" value="'+(settings.job_token_limit||0)+'"></label></div>'
    +'<label class="lb">단계 추천(AI)에 쓸 모델<input type="text" id="gm" value="'+esc(settings.planner_model||'')+'" placeholder="sonnet"></label>'
    +'<div class="vd">동시 실행은 프로젝트가 달라도 합산됩니다. 한 번에 에이전트 1개가 메모리를 약 300~500MB 쓰므로 4GB 파이는 1~2개를 권장합니다.</div>'
    +'<div class="row" style="margin-top:8px"><button class="pri" id="gsave">저장</button></div></div>'
    +'<div class="card"><h2>토큰 절감 옵션 (설치된 claude가 지원하면 자동 적용)</h2><div class="row">'+fl+'</div>'
    +'<ul class="tip"><li><b>--tools</b>: 에이전트가 쓰는 도구만 모델에 알려 매 호출의 고정 토큰을 줄입니다.</li><li><b>--strict-mcp-config, --disable-slash-commands, --no-session-persistence</b>: 불필요한 도구·스킬 목록과 세션 파일 저장을 끕니다.</li><li>단계마다 최대 턴이 제한되고, 에이전트에게 설명 없이 파일만 저장하도록 지시합니다.</li></ul></div>'
    +repoCard(rp)+tgCard(tg)+secCard(sec)
    +'<div class="card"><h2>프로젝트별 사용량 (새 토큰 = 입력 + 출력 + 캐시 쓰기)</h2><table class="ut"><tr><th>프로젝트</th><th>작업</th><th>새 토큰</th><th>추정 비용</th></tr>'
    +P.map(p=>'<tr><td>'+esc(p.name)+'</td><td>'+p.jobs+'</td><td>'+fmtN(p.tokens)+'</td><td>'+(p.cost?'$'+p.cost.toFixed(3):'-')+'</td></tr>').join('')+'</table></div>'
    +'<div class="card"><h2>토큰 아끼는 방법</h2><ul class="tip"><li>꼭 필요한 단계만 두세요. 단계 1개 = 호출 1회입니다. 필요 없는 단계는 \'사용\'을 끄세요.</li>'
    +'<li>검토·검수처럼 단순한 단계의 에이전트는 모델을 <b>haiku</b>로 지정하세요.</li><li>수정요청 반복 횟수를 1회 이하로 두세요.</li>'
    +'<li>요청에 분량과 범위를 구체적으로 적으면 불필요한 장문 생성을 줄입니다.</li><li>작업 상세 화면의 단계별 새 토큰 수치로 가장 비싼 단계를 찾아 조정하세요.</li></ul></div>';
  $('#ssave').onclick=async()=>{try{await post(base()+'/update',{name:$('#sn').value,description:$('#sd').value,max_rounds:+$('#sr').value,stage_mode:$('#smode').value});toast('저장했습니다');await loadProjects();await loadSettings()}catch(e){toast(e.message)}};
  $('#sdel').onclick=async()=>{if(!confirm('이 프로젝트를 목록에서 제거할까요? 폴더와 파일은 지워지지 않습니다.'))return;try{await post(base()+'/delete');toast('제거했습니다');cur=null;await loadProjects();setView('jobs')}catch(e){toast(e.message)}};
  bindRepo();bindSec();
  $('#gsave').onclick=async()=>{try{await post('/api/settings',{parallel:+$('#gp').value,job_token_limit:parseInt($('#gt').value)||0,planner_model:$('#gm').value});toast('저장했습니다');await loadProjects()}catch(e){toast(e.message)}};
  $('#slog').onclick=async()=>{if(!confirm('모든 기기의 로그인을 끊을까요? 이 화면도 다시 로그인해야 합니다.'))return;
    try{await post('/api/security/logout-all');location.href='/login'}catch(e){toast(e.message)}};
  if($('#tgsave'))$('#tgsave').onclick=async()=>{try{await post('/api/telegram/update',{notify:$('#tgn').checked});toast('저장했습니다')}catch(e){toast(e.message)}};
  if($('#tgtest'))$('#tgtest').onclick=async()=>{try{const r=await post('/api/telegram/test');toast(r.sent+'개 대화로 보냈습니다')}catch(e){toast(e.message)}};
  document.querySelectorAll('[data-unpair]').forEach(b=>b.onclick=async()=>{
    if(!confirm('이 대화의 연결을 해제할까요?'))return;
    try{await post('/api/telegram/update',{unpair:b.dataset.unpair});toast('해제했습니다');await loadSettings()}catch(e){toast(e.message)}});
}

function repoForm(st,i){
  const r=st?st.cfg:{};const k=st?r.id:'new';const on=!!st;
  const f=(id,lab,val,ph)=>'<label class="lb">'+lab+'<input type="text" data-f="'+id+'" value="'+esc(val||'')+'" placeholder="'+esc(ph||'')+'"></label>';
  return '<div class="sc" data-repo="'+esc(k)+'"><div class="sch"><b>'+(on?i+1:'+')+'</b><strong style="flex:1">'+(on?esc(r.name||r.id)+' 저장소':'저장소 추가')+'</strong>'
    +(on?'<span class="chip '+(st.cloned?'approved':'')+'">'+(st.cloned?'내려받음':'내려받기 전')+'</span>':'')+'</div><div class="scb">'
    +'<div class="g2">'+f('name','이름 (화면·커밋에 표시)',r.name,'예: 프론트, API')+f('url','저장소 주소 (SSH)',r.url,'git@github.com:아이디/저장소.git')+'</div>'
    +'<div class="g2">'+f('path','로컬 폴더',r.path||(on?'':'(비우면 자동)'),'')+f('branch','기준(테스트) 브랜치',r.branch||'main','develop')+'</div>'
    +'<div class="g2">'+f('release','운영 브랜치 (비우면 승인 즉시 운영)',r.release,'main')+f('test_url','테스트 서버 주소 (선택)',r.test_url,'http://192.168.0.16:38080')+'</div>'
    +f('build','빌드 확인 명령 (이 저장소가 바뀐 작업에서만 실행 · 비우면 생략)',r.build,'예: npm ci && npm run build')
    +'<div class="g2"><label class="lb">승인 시 반영 방식<select data-f="merge"><option value="merge"'+(r.merge!=='branch'?' selected':'')+'>기준 브랜치에 병합 후 푸시</option><option value="branch"'+(r.merge==='branch'?' selected':'')+'>작업 브랜치만 푸시 (PR)</option></select></label>'
    +f('deploy','푸시 후 실행할 배포 명령 (선택)',r.deploy,'')+'</div>'
    +'<div class="row"><button class="pri" data-act="save">저장</button>'
    +(on?'<button data-act="clone">'+(st.cloned?'최신 내용 가져오기':'내려받기')+'</button><button data-act="key">배포 키 보기</button><button class="dng" data-act="remove">연결 해제</button>':'')+'</div>'
    +(on?'<div class="vd">'+(st.cloned?'최근 커밋 '+esc(st.head||'-'):'아직 내려받지 않음')+(st.release_head?' · 운영: '+esc(st.release_head):'')+(st.web?' · <a href="'+esc(st.web)+'" target="_blank" rel="noopener">GitHub 열기</a>':'')+'</div>'
      +'<pre class="vd keyv" style="white-space:pre-wrap;word-break:break-all'+(st.key?'':';display:none')+'">'+esc(st.key||'')+'</pre>':'')
    +'</div></div>';
}
function repoCard(st){
  const rs=st.repos||[],nm=st.names||{};
  const hist=st.releases||[];
  const verS=o=>Object.keys(o||{}).map(k=>(rs.length>1?esc(nm[k]||k)+' ':'')+esc(String(o[k]).slice(0,7))).join(' · ');
  return '<div class="card"><h2>코드 저장소 (GitHub 연동)</h2>'
    +'<div class="vd">연결한 저장소의 실제 코드를 에이전트가 고칩니다. 저장소를 여러 개(예: 프론트·API) 연결하면 요청 하나로 필요한 쪽을 함께 고치고, 승인·운영 반영도 한 번에 처리합니다. 빌드 확인과 커밋은 하네스가 대신 합니다(토큰 사용 없음).</div>'
    +rs.map((x,i)=>repoForm(x,i)).join('')
    +'<details style="margin-top:6px"'+(rs.length?'':' open')+'><summary class="vd" style="cursor:pointer">+ 저장소 '+(rs.length?'더 ':'')+'연결하기</summary>'+repoForm(null,rs.length)+'</details>'
    +(hist.length?'<div class="vd" style="margin-top:12px">운영 반영 이력</div><table class="ut"><tr><th>시각</th><th>운영 버전</th><th>내용</th><th></th></tr>'
      +hist.map((x,i)=>'<tr><td>'+esc((x.ts||'').slice(5,16))+'</td><td>'+verS(x.heads)+'</td><td>'+(x.rollback?'<b>되돌리기</b> '+esc((x.msgs||[]).join(', ')):'변경 '+x.n+'개 · '+esc((x.msgs||[]).slice(0,2).join(', ')))+(x.partial?' <b style="color:var(--err)">(일부만 반영)</b>':'')+' <span style="color:var(--mute)">('+esc(x.by||'')+')</span></td><td>'
        +(i===0?'<span class="chip approved">현재 운영</span>':'<button data-rbi="'+i+'" style="font-size:12px;padding:3px 8px">이 시점으로 되돌리기</button>')+'</td></tr>').join('')
      +(hist[0].before&&Object.keys(hist[0].before).length&&!hist[0].rollback?'<tr><td colspan="3">마지막 반영 직전 ('+verS(hist[0].before)+')</td><td><button data-rbi="0" data-which="before" class="dng" style="font-size:12px;padding:3px 8px">직전 버전으로 되돌리기</button></td></tr>':'')+'</table>':'')
    +'<ul class="tip"><li>저장소마다 배포 키가 따로 있습니다. 배포 키 보기 → GitHub 그 저장소의 Settings → Deploy keys 에 붙여넣고 <b>Allow write access</b>를 켜세요.</li><li>빌드 산출물 폴더(dist, node_modules 등)는 저장소의 .gitignore에 있어야 커밋에 섞이지 않습니다.</li></ul></div>';
}
function bindRepo(){
  document.querySelectorAll('[data-repo]').forEach(box=>{
    const k=box.dataset.repo,id=k==='new'?'':k;
    const val=()=>{const o={id};box.querySelectorAll('[data-f]').forEach(e=>o[e.dataset.f]=e.value.trim());if(o.path==='(비우면 자동)')o.path='';return o};
    box.querySelectorAll('[data-act]').forEach(b=>b.onclick=async()=>{
      const a=b.dataset.act;
      try{
        if(a==='save'){await post(base()+'/repo',val());toast('저장했습니다');await loadSettings()}
        else if(a==='clone'){b.disabled=true;toast('저장소와 통신 중…');const r=await post(base()+'/repo/clone',{id});toast(r.msg);await loadSettings()}
        else if(a==='key'){const r=await post(base()+'/repo/key',{id});const p=box.querySelector('.keyv');p.textContent=r.key;p.style.display='';try{await navigator.clipboard.writeText(r.key);toast('공개 키를 복사했습니다')}catch(_){toast('아래 공개 키를 복사하세요')}}
        else if(a==='remove'){if(!confirm('이 저장소 연결을 해제할까요? 로컬 폴더와 GitHub는 그대로입니다.'))return;await post(base()+'/repo',{id,remove:true});toast('해제했습니다');await loadSettings()}
      }catch(e){alert(e.message);b.disabled=false}});
  });
  document.querySelectorAll('[data-rbi]').forEach(b=>b.onclick=async()=>{
    if(!confirm((b.dataset.which==='before'?'운영을 마지막 반영 직전 버전으로':'운영을 이 시점 버전으로')+' 되돌릴까요?\n1분 안에 실서버가 이 버전으로 다시 배포됩니다. 테스트 브랜치는 그대로입니다.'))return;
    b.disabled=true;try{await post(base()+'/repo/rollback',{idx:+b.dataset.rbi,which:b.dataset.which||'heads'});toast('되돌렸습니다 - 1분 안에 실서버에 배포됩니다');await loadSettings()}catch(e){alert(e.message);b.disabled=false}});
}

/* ---------- 새 프로젝트 ---------- */
let newPlan=null,manual=[],allAgents=null;
function manualPlan(){
  const ag=manual.filter(a=>a.name.trim()).map((a,i)=>({key:'m'+(i+1),name:a.name.trim(),role:a.role.trim(),web:!!a.web,model:a.model||''}));
  if(!ag.length)return null;
  const st=ag.map((a,i)=>({name:a.name,agent:a.key,kind:'work',instruction:a.role||'요청을 수행한다.',inputs:i?[ag[0].name]:[]}));
  if(st.length>1){const l=st[st.length-1];l.kind='review';l.target=st[st.length-2].name;l.polish=true}
  return {agents:ag,stages:st};
}
function manualRows(){
  return manual.map((a,i)=>'<div class="sc" data-i="'+i+'"><div class="sch"><b>'+(i+1)+'</b>'
    +'<input type="text" data-f="name" value="'+esc(a.name)+'" maxlength="30" placeholder="이름 (예: 리서처)">'
    +'<label class="inl"><input type="checkbox" data-f="web"'+(a.web?' checked':'')+'> 웹</label>'
    +'<input type="text" data-f="model" value="'+esc(a.model||'')+'" placeholder="모델(선택)" style="width:110px">'
    +'<button class="dng" data-a="del">삭제</button></div>'
    +'<div class="scb"><label class="lb">이 에이전트가 할 일<textarea data-f="role" rows="2" style="min-height:52px" placeholder="예: 자료를 조사해 사실만 정리하고 출처를 적는다">'+esc(a.role)+'</textarea></label></div></div>').join('')
    ||'<div class="empty" style="padding:16px">아직 에이전트가 없습니다. 아래에서 추가하세요.</div>';
}
function renderManual(){
  $('#mlist').innerHTML=manualRows();
  const p=manualPlan();
  $('#npprev').innerHTML=p?planHtml(p):'<div class="vd">에이전트를 1명 이상 추가하면 미리보기가 나옵니다.</div>';
}
function mergeCard(){
  const rp=(P||[]).filter(p=>p.repo);
  if(rp.length<2)return '';
  const common=(()=>{let c=rp[0].name;for(const p of rp)while(c&&!p.name.startsWith(c))c=c.slice(0,-1);return c.trim()})();
  return '<div class="card" style="margin-top:12px"><h2>코드 저장소 프로젝트 합치기</h2>'
    +'<div class="vd">저장소가 연결된 프로젝트들을 하나로 묶습니다. 요청 한 번으로 여러 저장소(예: 프론트·API)를 함께 고치고, 승인·운영 반영도 한 번에 됩니다. 저장소 폴더·배포 키·에이전트·단계를 그대로 가져오므로 GitHub에 키를 다시 등록할 필요가 없습니다.</div>'
    +rp.map((p,i)=>'<label class="chk"><input type="checkbox" class="mgp" value="'+esc(p.id)+'"'+(i<2?' checked':'')+'><span>'+esc(p.name)+'<small>'+esc((p.repo.names||[]).join(', '))+' · '+(p.repo.release?'테스트→운영':'바로 운영')+'</small></span></label>').join('')
    +'<label class="lb">새 프로젝트 이름<input type="text" id="mgname" maxlength="40" value="'+esc(common)+'"></label>'
    +'<ul class="tip"><li>원래 프로젝트들은 작업 기록 보관용으로 남고, 저장소 연결만 새 프로젝트로 옮겨집니다.</li><li>에이전트와 단계는 처음 체크한 프로젝트 것을 복사합니다.</li><li>진행 중인 작업이 없을 때만 합칠 수 있습니다.</li></ul>'
    +'<div class="row"><button class="pri" id="mggo">합쳐서 새 프로젝트 만들기</button></div></div>';
}
function bindMerge(){
  if(!$('#mggo'))return;
  $('#mggo').onclick=async e=>{
    const ids=[...document.querySelectorAll('.mgp:checked')].map(x=>x.value);
    if(ids.length<2){toast('2개 이상 고르세요');return}
    if(!confirm('선택한 프로젝트의 저장소를 새 프로젝트로 옮깁니다. 계속할까요?'))return;
    e.target.disabled=true;
    try{const r=await post('/api/merge-projects',{sources:ids,name:$('#mgname').value.trim()});toast('"'+r.name+'" 프로젝트를 만들었습니다 ('+r.repos.join(', ')+')');await loadProjects();switchProject(r.id)}
    catch(err){alert(err.message);e.target.disabled=false}};
}
async function initNewProj(){
  if(!presets.length)presets=(await api('/api/presets')).presets;
  newPlan=presets[0].plan;manual=[];
  $('#v-newproj').innerHTML='<div class="card"><h2>새 프로젝트</h2>'
    +'<label class="lb">프로젝트 이름<input type="text" id="npn" maxlength="40" placeholder="예: 블로그 자동화"></label>'
    +'<label class="lb">설명<textarea id="npd" placeholder="어떤 작업을 하는 프로젝트인지 적어주세요"></textarea></label>'
    +'<label class="lb">에이전트 구성 방법<select id="npmode">'
    +'<option value="preset">프리셋에서 고르기 (토큰 안 듦)</option>'
    +'<option value="ai">AI 추천 받기 (호출 1회)</option>'
    +'<option value="manual">직접 만들기 (내가 역할을 정함)</option></select></label>'
    +'<div id="npbody"></div><div id="npprev"></div>'
    +'<label class="chk" style="margin-top:12px"><input type="checkbox" id="npauto"><span>요청마다 AI가 단계를 다시 설계<small>등록한 에이전트 중에서 요청에 맞게 골라 씁니다. 위 구성은 설계 실패 시 쓰는 대체용이 됩니다.</small></span></label>'
    +'<div class="row" style="margin-top:12px"><button class="pri" id="npgo">프로젝트 만들기</button><button id="npcancel">취소</button></div></div>'
    +'<div id="imppanel"></div>'+mergeCard();
  bindMerge();
  $('#npmode').onchange=e=>npBody(e.target.value);
  npBody('preset');
  $('#npgo').onclick=async()=>{
    const mode=$('#npmode').value;
    let plan=mode==='manual'?manualPlan():newPlan;
    if(!plan){toast('에이전트를 1명 이상 추가하세요');return}
    try{const r=await post('/api/projects',{name:$('#npn').value,description:$('#npd').value,plan:plan,stage_mode:$('#npauto').checked?'auto':'fixed'});
      toast('프로젝트를 만들었습니다');cur=r.id;try{localStorage.setItem('cur',r.id)}catch(e){}await loadProjects();view='agents';setView('agents')}catch(e){toast(e.message)}
  };
  $('#npcancel').onclick=()=>setView('jobs');
}
function npBody(mode){
  const show=note=>{$('#npprev').innerHTML=(note?'<div class="vd">'+esc(note)+'</div>':'')+planHtml(newPlan)};
  if(mode==='preset'){
    $('#npbody').innerHTML='<label class="lb">프리셋<select id="nps">'+presetOpts()+'</select></label>';
    $('#nps').onchange=e=>{newPlan=presets[+e.target.value].plan;show(presets[+e.target.value].desc)};
    newPlan=presets[0].plan;show(presets[0].desc);
  }else if(mode==='ai'){
    $('#npbody').innerHTML='<div class="row">'+countSel('ncs','nca')+'<button id="npai">AI 추천 받기</button></div>'
      +'<div class="vd">설명을 자세히 적을수록 원하는 에이전트가 나옵니다. 마음에 안 들면 다시 받거나, 만든 뒤 에이전트 화면에서 고치면 됩니다.</div>';
    $('#npprev').innerHTML='';
    $('#npai').onclick=async()=>{
      const d=$('#npd').value.trim();if(!d){toast('설명을 먼저 적어주세요');return}
      $('#npai').disabled=true;$('#npai').textContent='추천 생성 중...';
      try{const r=await post('/api/plan',{name:$('#npn').value,description:d,stages:+$('#ncs').value,agents:+$('#nca').value});
        newPlan=r.plan;show('AI 추천 결과 (사용량: 입력 '+fmtN(r.usage.input)+' · 출력 '+fmtN(r.usage.output)+')')}catch(e){toast(e.message)}
      $('#npai').disabled=false;$('#npai').textContent='AI 추천 받기';
    };
  }else{
    $('#npbody').innerHTML='<div id="mlist"></div>'
      +'<div class="row" style="margin-top:8px"><button id="madd">+ 에이전트 추가</button><button id="mimp">기존 에이전트 가져오기</button></div>'
      +'<div class="vd">맨 아래 에이전트는 앞 결과를 검토하는 역할이 됩니다(2명 이상일 때). 만든 뒤 단계 화면에서 자유롭게 바꿀 수 있습니다.</div>';
    renderManual();
    const L=$('#mlist');
    L.addEventListener('input',e=>{const c=e.target.closest('.sc');if(!c)return;const f=e.target.dataset.f;
      if(f&&e.target.type!=='checkbox'){manual[+c.dataset.i][f]=e.target.value;if(f==='name'||f==='role')$('#npprev').innerHTML=manualPlan()?planHtml(manualPlan()):''}});
    L.addEventListener('change',e=>{const c=e.target.closest('.sc');if(!c)return;
      if(e.target.dataset.f==='web')manual[+c.dataset.i].web=e.target.checked});
    L.addEventListener('click',e=>{const b=e.target.closest('button[data-a="del"]');if(b){manual.splice(+b.closest('.sc').dataset.i,1);renderManual()}});
    $('#madd').onclick=()=>{manual.push({name:'',role:'',web:false,model:''});renderManual()};
    $('#mimp').onclick=()=>importPanel(a=>{manual.push({name:a.name,role:a.role,web:a.web,model:a.model});renderManual();$('#imppanel').innerHTML=''});
  }
}
async function importPanel(onPick){
  $('#imppanel').innerHTML='<div class="card"><h2>기존 에이전트 가져오기</h2><div class="vd">불러오는 중...</div></div>';
  let d;try{d=await api('/api/all-agents')}catch(e){toast(e.message);$('#imppanel').innerHTML='';return}
  if(!d.agents.length){$('#imppanel').innerHTML='<div class="card"><h2>기존 에이전트 가져오기</h2><div class="empty" style="padding:16px">가져올 에이전트가 없습니다</div></div>';return}
  $('#imppanel').innerHTML='<div class="card"><h2>기존 에이전트 가져오기</h2>'
    +'<div class="vd" style="margin-bottom:8px">다른 프로젝트의 에이전트를 복사해 옵니다. 복사본이라 고쳐도 원본에는 영향이 없습니다.</div>'
    +'<div class="jobs" style="margin-top:0;max-height:50vh">'+d.agents.map((a,i)=>'<div class="job" data-i="'+i+'"><div class="t">'+esc(a.name)+' <span class="tag">'+esc(a.pname)+'</span>'+(a.web?' <span class="tag">웹</span>':'')+(a.model?' <span class="tag">'+esc(a.model)+'</span>':'')+'</div><div class="m">'+esc((a.role||'').slice(0,90))+'</div></div>').join('')+'</div>'
    +'<div class="row" style="margin-top:10px"><button id="impclose">닫기</button></div></div>';
  $('#imppanel').querySelectorAll('.job').forEach(el=>el.onclick=()=>onPick(d.agents[+el.dataset.i]));
  $('#impclose').onclick=()=>{$('#imppanel').innerHTML=''};
  $('#imppanel').scrollIntoView({behavior:'smooth',block:'nearest'});
}

/* ---------- 폴링 ---------- */
async function tick(force){
  if(document.hidden&&!force)return;
  try{await loadProjects();if(view==='jobs'){await loadList();await loadDetail(force)}}catch(e){}
}
const WD=['일','월','화','수','목','금','토'];
function fmtReset(t){if(!t)return '';const d=new Date(t*1000),h=d.getHours(),m=String(d.getMinutes()).padStart(2,'0');return WD[d.getDay()]+' '+(h<12?'오전 ':'오후 ')+((h%12)||12)+':'+m}
async function loadUsage(){try{const u=(await api('/api/usage')).usage;const el=$('#usagebar');if(!u){el.hidden=true;return}
  const seg=(n,w)=>w?n+' <b class="'+(w.pct>=80?'hi':'')+'">'+w.pct+'%</b>'+(w.reset?' · '+fmtReset(w.reset)+' 초기화':''):'';
  el.innerHTML=[seg('현재 세션',u.session),seg('이번 주',u.week)].filter(Boolean).join(' &nbsp;|&nbsp; ');el.title='Claude 구독 사용량 (확인 '+u.ts+')';el.hidden=false}catch(e){}}
loadUsage();setInterval(loadUsage,300000);
setInterval(()=>{tickN++;if(P.some(p=>p.active>0)||tickN%3===0)tick(false)},3000);
loadProjects().then(()=>setView(cur?'jobs':'newproj')).catch(e=>toast(e.message));
</script>
<div id="usagebar" class="usagebar" hidden></div>
</body>
</html>
"""

if __name__ == "__main__":
    main()

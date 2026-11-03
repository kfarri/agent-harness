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
           "/cancel  입력 대기 취소\n\n"
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

PRESETS_RAW = [
    {"key": "content_lite", "label": "콘텐츠 제작 · 절약형 (조사 → 작성 → 검수)",
     "desc": "단계가 가장 적어 토큰을 아낍니다. 처음 시작할 때 권장합니다.",
     "agents": [A("researcher", "리서처", "자료 조사 전문 에이전트다. 사실만 정리하고 출처를 적는다.", web=True),
                A("writer", "작성자", "글 작성 전문 에이전트다. 조사 결과에 있는 내용만 사용해 글을 쓴다."),
                A("reviewer", "리뷰어", "검수 전문 에이전트다. 없는 사실, 오탈자, 어색한 문장을 고친다.", model="haiku")],
     "stages": [S("리서치", "researcher", "work", _RESEARCH),
                S("초안 작성", "writer", "work", _DRAFT, ["리서치"]),
                S("검수", "reviewer", "review", _REVIEW, ["리서치"], "초안 작성", True)]},
    {"key": "content_full", "label": "콘텐츠 제작 · 교차검토 포함 (조사 → 검토 → 작성 → 검수)",
     "desc": "조사 결과를 먼저 검토해 품질을 높입니다. 호출이 1회 더 늘어납니다.",
     "agents": [A("researcher", "리서처", "자료 조사 전문 에이전트다. 사실만 정리하고 출처를 적는다.", web=True),
                A("writer", "작성자", "글 작성 전문 에이전트다. 조사 결과에 있는 내용만 사용해 글을 쓴다."),
                A("reviewer", "리뷰어", "검수 전문 에이전트다. 없는 사실, 오탈자, 어색한 문장을 고친다.", model="haiku")],
     "stages": [S("리서치", "researcher", "work", _RESEARCH),
                S("교차검토", "reviewer", "review", _CHECK, [], "리서치"),
                S("초안 작성", "writer", "work", _DRAFT, ["리서치"]),
                S("검수", "reviewer", "review", _REVIEW, ["리서치"], "초안 작성", True)]},
    {"key": "blog", "label": "블로그·SNS 글 (기획 → 초안 → 편집)",
     "desc": "주제 기획부터 편집까지. 웹 자료가 필요 없으면 가장 가볍습니다.",
     "agents": [A("planner", "기획자", "독자와 목적을 분석해 글의 구조(제목 후보, 목차, 핵심 메시지)를 설계한다.", web=True),
                A("writer", "작성자", "기획안에 따라 매력적인 한국어 글을 쓴다."),
                A("editor", "편집자", "문장을 다듬고 톤을 통일하며 사실 오류를 점검한다.", model="haiku")],
     "stages": [S("기획", "planner", "work", "요청을 분석해 독자, 목적, 제목 후보 3개, 목차, 핵심 메시지를 간결하게 정리한다."),
                S("초안 작성", "writer", "work", "기획안에 따라 글을 작성한다. 분량은 요청에 맞춘다.", ["기획"]),
                S("편집", "editor", "review", "초안을 기획안과 대조해 구조, 문장, 톤을 점검한다.", ["기획"], "초안 작성", True)]},
    {"key": "code", "label": "코드 개발 (설계 → 구현 → 코드리뷰)",
     "desc": "결과는 마크다운 코드 블록으로 저장됩니다. 실제 파일 생성·실행은 하지 않습니다.",
     "agents": [A("architect", "설계자", "요구사항을 분석해 구조와 인터페이스를 설계한다."),
                A("developer", "개발자", "설계에 따라 읽기 쉽고 단순한 코드를 작성한다."),
                A("codereviewer", "코드리뷰어", "버그, 보안, 가독성 문제를 찾아 지적한다.", model="haiku")],
     "stages": [S("설계", "architect", "work", "요구사항을 분석해 구조, 주요 함수·클래스, 예외 처리 방침을 간결하게 설계한다."),
                S("구현", "developer", "work", "설계에 따라 코드를 작성해 마크다운 코드 블록으로 출력한다.", ["설계"]),
                S("코드리뷰", "codereviewer", "review", "코드를 설계와 대조해 버그, 보안, 가독성을 점검한다.", ["설계"], "구현", True)]},
    {"key": "translate", "label": "번역·현지화 (번역 → 감수)",
     "desc": "두 단계뿐이라 토큰이 적게 듭니다.",
     "agents": [A("translator", "번역가", "원문의 의미와 어조를 유지해 자연스럽게 번역한다."),
                A("proofreader", "감수자", "번역의 오역, 누락, 어색한 표현을 점검한다.", model="haiku")],
     "stages": [S("번역", "translator", "work", "요청에 적힌 원문을 지정된 언어로 번역한다. 의미를 더하거나 빼지 않는다."),
                S("감수", "proofreader", "review", "원문과 번역을 대조해 오역, 누락, 어색한 표현을 점검한다.", [], "번역", True)]},
    {"key": "report", "label": "데이터·보고서 (분석 → 보고서 → 검수)",
     "desc": "자료를 분석하고 보고서로 정리합니다.",
     "agents": [A("analyst", "분석가", "자료를 분석해 핵심 수치와 시사점을 정리한다.", web=True),
                A("writer", "작성자", "분석 결과로 읽기 쉬운 보고서를 쓴다."),
                A("reviewer", "리뷰어", "수치와 주장이 분석 결과와 일치하는지 검수한다.", model="haiku")],
     "stages": [S("분석", "analyst", "work", "요청 주제의 자료를 조사·분석해 핵심 수치, 근거, 시사점을 표와 목록으로 정리한다."),
                S("보고서 작성", "writer", "work", "분석 결과만 사용해 요약, 본문, 결론 순서의 보고서를 쓴다.", ["분석"]),
                S("검수", "reviewer", "review", "보고서의 수치와 주장을 분석 결과와 대조해 오류를 점검한다.", ["분석"], "보고서 작성", True)]},
]

DEFAULT_ROLE_TEXT = {
    "researcher": "자료 조사 전문 에이전트다. 사실만 정리하고 출처를 함께 적는다. 자료가 서로 엇갈리면 불일치로 표시한다. 최종 글 작성은 하지 않는다.",
    "writer": "글 작성 전문 에이전트다. 조사 결과에 있는 내용만 사용해 읽기 쉬운 한국어 글로 작성하고, 없는 사실은 지어내지 않는다.",
    "reviewer": "검수 전문 에이전트다. 초안을 조사 결과와 대조해 없는 사실, 오탈자, 어색한 문장을 찾아 고치고, 고친 내용은 검수 메모로 남긴다.",
}


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
    save_cfg()


# ---------------------------------------------------------------- 에이전트 설정 파일 · 신뢰 등록

def build_settings(proj, perms):
    allow = ["Read", "Write", "Edit"]
    src = proj_dirs(proj)["sources"]
    deny = ["Bash(sudo:*)", "Bash(rm:*)", "Read(/%s)" % (BASE / ".env"),
            "Write(/%s/**)" % src, "Edit(/%s/**)" % src]   # 참고 자료는 읽기만 허용
    if perms.get("web"):
        allow += ["WebSearch", "WebFetch"]
    else:
        deny += ["WebSearch", "WebFetch"]
    if perms.get("bash"):
        allow.append("Bash")
    return {"permissions": {"additionalDirectories": [str(proj_dirs(proj)["shared"])], "allow": allow, "deny": deny}}


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
    body = (desc or "").strip() or "(여기에 이 에이전트가 맡을 역할을 적어주세요)"
    return ("# 역할: %s\n%s\n\n## 공통 규칙\n- 작업 지시에 적힌 입력 파일만 읽고, 지정된 출력 파일에만 저장한다\n"
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
    e.pop("GUI_PASSWORD", None)  # 에이전트가 GUI 비밀번호를 읽지 못하게 한다
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
    if not items:
        return ""
    lines = ["[참고 자료] 사용자가 직접 제공한 자료다. 관련 있는 파일을 읽어 근거로 삼는다."]
    lines += ["- ../shared/sources/%s" % s["name"] for s in items[:SRC_MAX]]
    if mode == "only":
        lines.append("답변은 이 자료에 있는 내용만 근거로 작성한다. 자료에 없는 것은 '제공된 자료에 없음'이라고 밝히고 추측하지 않는다.")
    else:
        lines.append("이 자료를 우선 근거로 삼고, 부족한 부분만 다른 방법으로 보완한다.")
    return "\n".join(lines) + "\n"


def feedback_block(fb):
    fb = (fb or "").strip()[:2000]
    if not fb:
        return ""
    return ("\n[수정 요청 - 반드시 반영할 것]\n%s\n기존 결과 파일이 있으면 먼저 읽고, 같은 경로에 덮어써서 수정본을 저장한다.\n" % fb)


def inputs_block(proj, stages, stage, jid):
    lines = ["요청 파일: %s" % rel(proj, "request", jid)]
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
    return ("STEP: %s\n작업ID: %s\n%s\n%s지시: %s\n출력 파일: %s\n%s%s%s"
            % (stage["id"], jid, inputs_block(proj, stages, stage, jid), sources_block(proj),
               stage["instruction"] or "요청을 수행한다.",
               rel(proj, stage["id"], jid), feedback_block(fb), CLARIFY_RULE, CONCISE))


def prompt_review(proj, stages, stage, jid):
    by_id = {s["id"]: s for s in stages}
    tgt = by_id[stage["target"]]
    p = ("STEP: %s\n작업ID: %s\n%s\n%s검토 대상(%s): %s\n지시: %s\n검수 결과 파일: %s\n"
         "형식: 첫 줄은 정확히 `VERDICT: APPROVE` 또는 `VERDICT: REVISE` 한 줄만 쓴다. 둘째 줄부터 이유를 적고, "
         "REVISE이면 대상 단계에 줄 구체적인 수정 요청을 적는다.\n"
         % (stage["id"], jid, inputs_block(proj, stages, stage, jid), sources_block(proj),
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
                i += 1
                continue
            run_step(job, proj, st, prompt_review(proj, stages, st, jid),
                     remove_kinds=("final",) if st.get("polish") else ())
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
        "- agents:[{\"key\":\"영문소문자\",\"name\":\"한글 이름\",\"role\":\"역할 설명 1~2문장\",\"web\":true|false,\"model\":\"haiku|sonnet|\"}]\n"
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
            "active": sum(1 for j in js if j["status"] in ("queued", "running")),
            "awaiting": sum(1 for j in js if j["status"] == "awaiting_user"),
            "jobs": len(js), "tokens": sum(new_tokens(j.get("usage") or {}) for j in js),
            "cost": round(sum((j.get("usage") or {}).get("cost", 0) for j in js), 4),
            "agents": len(p["agents"]), "stages": len(active_stages(p)),
            "schedules": sum(1 for s in p.get("schedules", []) if s.get("enabled", True))}


def project_detail(proj):
    flush_trust()
    return {"id": proj["id"], "name": proj["name"], "description": proj.get("description", ""),
            "max_rounds": proj.get("max_rounds", 1), "root": proj["root"],
            "stage_mode": proj.get("stage_mode", "fixed"), "use_sources": proj.get("use_sources", "prefer"),
            "sources": len(src_list(proj)),
            "agents": [agent_info(proj, a) for a in proj["agents"]], "stages": proj["stages"],
            "schedules": proj.get("schedules", []), "summary": psummary(proj)}


def job_summary(j):
    return {k: j[k] for k in ("id", "title", "status", "step", "created", "updated")} | \
        {"tokens": new_tokens(j.get("usage") or {}), "needs_input": bool(j.get("needs_input"))}


def job_detail(proj, j):
    src = j.get("stages") or proj["stages"]
    files = {"request": read_text(fpath(proj, "request", j["id"])),
             "final": read_text(fpath(proj, "final", j["id"])),
             "approved": read_text(fpath(proj, "approved", j["id"]))}
    for s in src:
        files[s["id"]] = read_text(fpath(proj, s["id"], j["id"]))
    return {"job": j, "files": files, "limit": S_().get("job_token_limit", 0), "max_rounds": proj.get("max_rounds", 1),
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


def create_job(proj, text, source="gui", auto_approve=False, chat=None, title=None):
    text = (text or "").strip()
    if not text:
        raise ApiError(400, "요청 내용을 입력하세요")
    if len(text) > 20000:
        raise ApiError(400, "요청이 너무 깁니다")
    if not active_stages(proj):
        raise ApiError(400, "사용 중인 단계가 없습니다")
    ensure_dirs(proj)
    jid = time.strftime("%m%d-%H%M%S") + "-" + secrets.token_hex(1)
    fpath(proj, "request", jid).write_text(text + "\n")
    auto = proj.get("stage_mode") == "auto"
    job = {"id": jid, "pid": proj["id"], "title": (title or text.splitlines()[0])[:60], "status": "queued",
           "step": ("" if auto else active_stages(proj)[0]["id"]), "created": now(), "updated": now(),
           "feedback": "", "error": "", "cancel": False, "usage": {}, "events": [], "source": source,
           "auto_approve": bool(auto_approve), "chat": str(chat) if chat else "",
           "needs_input": False, "question": ""}
    JOBS[(proj["id"], jid)] = job
    jsave(job)
    event(job, "system", "작업 등록" + {"telegram": " (텔레그램)", "schedule": " (예약 실행)"}.get(source, ""))
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
    set_state(j, status="queued", step=first if start == "first" else start, feedback=fb, error="", cancel=False,
              needs_input=False, question="")
    label = "처음" if start == "first" else next(s["name"] for s in act if s["id"] == start)
    event(j, "user", "수정 요청으로 %s 단계부터 다시 시작%s" % (label, (": " + fb[:120]) if fb else ""))
    QUEUE.put((proj["id"], j["id"], start))
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
        notify("[%s] %s · 완료 (새 토큰 %s)\n\n%s" % (pname, job["title"], tok, body), None, chat)
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
    st = {"queued": "대기", "running": "진행 중", "awaiting_user": "승인 대기", "approved": "완료",
          "failed": "실패", "cancelled": "중단"}
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
                notify("승인했습니다: %s" % job["title"], None, chat)
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
        proj = tg_cur(chat)
        if not proj:
            return notify("프로젝트가 없습니다. GUI에서 먼저 만들어주세요.", None, chat)
        if cmd in ("/start", "/help"):
            _, btns = tg_projects(chat)
            return notify("지금 사용 중: %s\n\n%s\n\n아래 버튼으로 프로젝트를 바꿀 수 있습니다."
                          % (proj["name"], TG_HELP), btns[:8], chat)
        if cmd == "/cancel":
            return notify("대기 중인 입력이 없습니다.", None, chat)
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
                if due:
                    save_cfg()
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


def new_session(ip):
    prune_sessions()
    tok = secrets.token_urlsafe(32)
    SESSIONS[tok] = {"ip": ip, "exp": time.time() + SESS_TTL, "since": now()}
    return tok


def blocked_for(ip):
    f = FAILS.get(ip)
    return max(0, int(f["until"] - time.time())) if f else 0


def note_fail(ip, where):
    f = FAILS.setdefault(ip, {"n": 0, "until": 0})
    f["n"] += 1
    if f["n"] >= MAX_FAILS:
        wait = min(3600, 60 * 2 ** (f["n"] - MAX_FAILS))
        f["until"] = time.time() + wait
        print("로그인 차단: %s (%d회 실패, %d초)" % (ip, f["n"], wait), flush=True)
        if f["n"] == MAX_FAILS or f["n"] % 10 == 0:
            notify("경고: %s 에서 로그인 %d회 실패해 %d초 차단했습니다. (%s)" % (ip, f["n"], wait, where))
    LOGINS.insert(0, {"ts": now(), "ip": ip, "ok": False})
    del LOGINS[30:]


def note_ok(ip):
    known = any(x["ok"] and x["ip"] == ip for x in LOGINS)
    FAILS.pop(ip, None)
    LOGINS.insert(0, {"ts": now(), "ip": ip, "ok": True})
    del LOGINS[30:]
    if not known and not is_local(ip):
        notify("새로운 곳에서 하네스에 로그인했습니다: %s" % ip)


def check_pw(user, pw):
    return (hmac.compare_digest(user.encode(), USER.encode())
            and hmac.compare_digest(pw.encode(), PASSWORD.encode()))


def security_state():
    prune_sessions()
    return {"https": PUBLIC_HTTPS, "proxy": TRUST_PROXY, "host": HOST, "public_host": PUBLIC_HOST,
            "sessions": len(SESSIONS), "weak_password": len(PASSWORD) < 12,
            "blocked": [{"ip": k, "left": blocked_for(k), "fails": v["n"]}
                        for k, v in FAILS.items() if blocked_for(k) > 0],
            "recent": LOGINS[:10]}


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
<label>아이디<input name="user" autocomplete="username" autofocus></label>
<label>비밀번호<input name="password" type="password" autocomplete="current-password"></label>
<button type="submit">로그인</button></form></body></html>"""

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
    return job_summary(create_job(proj_of(m[1]), b.get("request")))


@route("GET", r"/api/projects/([^/]+)/jobs/([^/]+)")
def r_job_get(m, b):
    proj = proj_of(m[1])
    return job_detail(proj, job_of(proj, m[2]))


@route("POST", r"/api/projects/([^/]+)/jobs/([^/]+)/(approve|restart|cancel)")
def r_job_action(m, b):
    proj = proj_of(m[1])
    j = job_of(proj, m[2])
    return {"approve": lambda: job_approve(proj, j), "restart": lambda: job_restart(proj, j, b),
            "cancel": lambda: job_cancel(proj, j)}[m[3]]()


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


@route("POST", r"/api/projects/([^/]+)/agents/import")
def r_agent_import(m, b):
    proj = proj_of(m[1])
    src = proj_of(str(b.get("from") or ""))
    a = agent_of(src, str(b.get("agent") or ""))
    ws = proj_dirs(src)["root"] / a["workspace"]
    role = read_text(ws / "CLAUDE.md", 50000) or ""
    perms = parse_perms(ws / ".claude" / "settings.json")
    name = str(b.get("name") or a["name"]).strip()[:30] or a["name"]
    new = create_agent_in(proj, name, "", perms, a.get("model", ""))
    if role.strip():
        (proj_dirs(proj)["root"] / new["workspace"] / "CLAUDE.md").write_text(role.rstrip() + "\n")
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


@route("POST", r"/api/settings")
def r_settings(m, b):
    return settings_update(b)


class Handler(BaseHTTPRequestHandler):
    server_version = "AgentHarness"

    def log_message(self, *a):
        pass

    auth = None

    def ip(self):
        peer = self.client_address[0]
        if TRUST_PROXY and is_local(peer):
            xff = self.headers.get("X-Forwarded-For")
            if xff:
                return xff.split(",")[0].strip()[:45]
        return peer

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
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(data)

    def js(self, code, obj):
        self.send(code, json.dumps(obj, ensure_ascii=False))

    def gate(self):
        """세션 쿠키 또는 기본 인증. 공개 호스팅을 고려해 실패는 횟수 제한으로 막는다."""
        ip = self.ip()
        left = blocked_for(ip)
        if left:
            self.send(429, json.dumps({"error": "로그인 시도가 많아 %d초 동안 차단되었습니다" % left}))
            return False
        tok = self.cookie("ah_sess")
        if tok:
            sess = SESSIONS.get(tok)
            if sess and sess["exp"] > time.time():
                self.auth = "cookie"
                return True
        a = self.headers.get("Authorization", "")
        if a.startswith("Basic "):
            try:
                u, p = base64.b64decode(a[6:]).decode("utf-8").split(":", 1)
            except Exception:  # noqa: BLE001
                u = p = ""
            if check_pw(u, p):
                self.auth = "basic"
                return True
            note_fail(ip, "기본 인증")
            self.send(401, json.dumps({"error": "아이디 또는 비밀번호가 올바르지 않습니다"}))
            return False
        if urlparse(self.path).path.startswith("/api/"):
            self.send(401, json.dumps({"error": "로그인이 필요합니다"}))
        else:
            self.send(303, "", "text/plain; charset=utf-8", {"Location": "/login"})
        return False

    def login_page(self, err=""):
        left = blocked_for(self.ip())
        if left:
            err = "로그인 시도가 많아 %d초 동안 차단되었습니다." % left
        sub = "이 서버는 에이전트를 실행합니다. 본인만 로그인하세요."
        html = LOGIN_HTML.replace("@SUB@", sub).replace(
            "@ERR@", ('<p class="e">%s</p>' % err.replace("<", "&lt;")) if err else "")
        self.send(200, html,
                  "text/html; charset=utf-8",
                  {"Content-Security-Policy": "default-src 'none'; style-src 'unsafe-inline'; form-action 'self'; frame-ancestors 'none'"})

    def do_login(self):
        ip = self.ip()
        if blocked_for(ip):
            return self.login_page()
        origin = self.headers.get("Origin")
        if origin and urlparse(origin).netloc not in {self.headers.get("Host"), PUBLIC_HOST}:
            return self.send(403, "허용되지 않은 출처", "text/plain; charset=utf-8")
        n = int(self.headers.get("Content-Length") or 0)
        if n > 4000:
            return self.login_page("입력이 너무 깁니다.")
        from urllib.parse import parse_qs
        f = parse_qs(self.rfile.read(n).decode("utf-8", "replace"))
        if not check_pw((f.get("user") or [""])[0], (f.get("password") or [""])[0]):
            note_fail(ip, "로그인 화면")
            return self.login_page("아이디 또는 비밀번호가 올바르지 않습니다.")
        note_ok(ip)
        tok = new_session(ip)
        # 공개 도메인(https)으로 들어왔을 때만 Secure 쿠키를 쓴다. 내부 IP(http)에 Secure를 붙이면
        # 브라우저가 쿠키 저장을 거부해 로그인이 계속 풀린다.
        req_host = (self.headers.get("Host") or "").split(":")[0]
        flags = "; Secure" if (PUBLIC_HTTPS and PUBLIC_HOST and req_host == PUBLIC_HOST) else ""
        self.send(303, "", "text/plain; charset=utf-8",
                  {"Location": "/", "Set-Cookie": "ah_sess=%s; Path=/; HttpOnly; SameSite=Lax; Max-Age=%d%s"
                                                  % (tok, SESS_TTL, flags)})

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
        path = urlparse(self.path).path
        if path == "/login":
            return self.login_page()
        if path == "/logout":
            SESSIONS.pop(self.cookie("ah_sess") or "", None)
            return self.send(303, "", "text/plain; charset=utf-8",
                             {"Location": "/login", "Set-Cookie": "ah_sess=; Path=/; HttpOnly; Max-Age=0"})
        if not self.gate():
            return
        if path == "/":
            return self.send(200, INDEX_HTML, "text/html; charset=utf-8",
                             {"Content-Security-Policy": "default-src 'self'; style-src 'unsafe-inline'; script-src 'unsafe-inline'; frame-ancestors 'none'"})
        self.dispatch("GET", {})

    def do_POST(self):
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
            if n > 300_000:
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


INDEX_HTML = r"""@@INDEX_HTML@@"""

if __name__ == "__main__":
    main()

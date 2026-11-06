#!/usr/bin/env bash
# 하네스 설정·데이터·키를 NAS 공유 폴더에 백업한다.
#   처음 한 번:  sudo /opt/agent-harness-src/backup.sh --setup   (NAS 주소·계정 입력 → 매일 자동 백업 예약)
#   지금 바로:   sudo /opt/agent-harness-src/backup.sh
# 백업에는 비밀번호·토큰·키가 들어 있으므로 NAS 폴더는 관리자만 접근하게 두세요.
set -euo pipefail

CONF=/etc/harness-backup.conf
CRED=/root/.harness-nas-cred
[ -f "$CONF" ] && . "$CONF"
AGENT_HOME=${AGENT_HOME:-/home/agent}
MNT=${MNT:-/mnt/harness-backup}
KEEP=${KEEP:-14}
SHARE=${SHARE:-}
DEST=${DEST:-}            # 지정하면 NAS 마운트 없이 이 폴더에 저장 (테스트·USB용)

tg() {   # 실패 시 텔레그램으로 알린다 (하네스에 연결된 대화로)
  python3 - "$1" "$AGENT_HOME/agents" <<'PY' 2>/dev/null || true
import json, sys, urllib.request, urllib.parse, pathlib
msg, base = sys.argv[1], pathlib.Path(sys.argv[2])
tok = ""
for l in (base / ".env").read_text().splitlines():
    if l.startswith("TELEGRAM_BOT_TOKEN="):
        tok = l.split("=", 1)[1].strip().strip('"').strip("'")
chats = json.loads((base / "projects.json").read_text())["settings"]["telegram"]["chats"]
for c in chats:
    urllib.request.urlopen("https://api.telegram.org/bot%s/sendMessage" % tok,
                           urllib.parse.urlencode({"chat_id": c, "text": msg}).encode(), timeout=15)
PY
}

if [ "${1:-}" = "--setup" ]; then
  [ "$(id -u)" = 0 ] || { echo "root로 실행하세요 (sudo)"; exit 1; }
  command -v mount.cifs >/dev/null || { echo "NAS 연결 도구 설치 중..."; apt-get install -y -qq cifs-utils >/dev/null; }
  read -rp "NAS 공유 폴더 (예: //192.168.0.16/harness_backup): " SHARE
  read -rp "NAS 계정 아이디: " U
  read -rsp "NAS 계정 비밀번호 (화면에 안 보임): " P; echo
  umask 077
  printf 'username=%s\npassword=%s\n' "$U" "$P" > "$CRED"
  printf 'SHARE=%q\nKEEP=%q\n' "$SHARE" "$KEEP" > "$CONF"
  cat > /etc/systemd/system/harness-backup.service <<EOF
[Unit]
Description=Agent harness backup to NAS
After=network-online.target
[Service]
Type=oneshot
ExecStart=$(readlink -f "$0")
EOF
  cat > /etc/systemd/system/harness-backup.timer <<'EOF'
[Unit]
Description=Daily agent harness backup
[Timer]
OnCalendar=*-*-* 04:17
Persistent=true
RandomizedDelaySec=300
[Install]
WantedBy=timers.target
EOF
  systemctl daemon-reload
  systemctl enable --now harness-backup.timer >/dev/null
  echo "설정 완료. 지금 한 번 백업해 봅니다..."
  exec "$0"
fi

[ "$(id -u)" = 0 ] || { echo "root로 실행하세요 (sudo)"; exit 1; }
mounted=""
cleanup() { [ -n "$mounted" ] && umount "$MNT" 2>/dev/null || true; }
fail() { echo "백업 실패: $1"; tg "[하네스] 백업 실패: $1"; cleanup; exit 1; }
trap 'fail "명령 오류 (줄 $LINENO)"' ERR

if [ -z "$DEST" ]; then
  [ -n "$SHARE" ] || fail "NAS 공유 폴더가 설정되지 않았습니다. 먼저 --setup 을 실행하세요"
  mkdir -p "$MNT"
  if ! mountpoint -q "$MNT"; then
    mount -t cifs "$SHARE" "$MNT" -o "credentials=$CRED,uid=0,gid=0,file_mode=0600,dir_mode=0700,vers=3.0" \
      || fail "NAS 폴더 연결 실패 ($SHARE)"
    mounted=1
  fi
  DEST="$MNT"
fi

TS=$(date +%Y%m%d-%H%M%S)
OUT="$DEST/harness-backup-$TS.tar.gz"
cd /
# 있는 것만 담는다. 코드 저장소(repos)와 로그는 GitHub·재생성으로 복구되므로 뺀다.
items=()
for p in "${AGENT_HOME#/}/agents" "${AGENT_HOME#/}/.ssh" "${AGENT_HOME#/}/.claude.json" \
         "${AGENT_HOME#/}/.claude/.credentials.json" "${AGENT_HOME#/}/.claude/settings.json" \
         etc/systemd/system/agent-harness.service; do
  [ -e "/$p" ] && items+=("$p")
done
[ ${#items[@]} -gt 0 ] || fail "백업할 파일이 없습니다 ($AGENT_HOME)"
trap - ERR
tar czpf "$OUT.part" --exclude="${AGENT_HOME#/}/agents/repos" --exclude="${AGENT_HOME#/}/agents/logs" \
    --exclude='node_modules' --exclude='.cache' "${items[@]}" || fail "압축 실패"
trap 'fail "명령 오류 (줄 $LINENO)"' ERR
mv "$OUT.part" "$OUT"
chmod 600 "$OUT"
# 오래된 백업 정리 (최근 KEEP개만)
ls -1t "$DEST"/harness-backup-*.tar.gz 2>/dev/null | tail -n +$((KEEP + 1)) | while read -r f; do rm -f "$f"; done
echo "백업 완료: $(basename "$OUT") ($(du -h "$OUT" | cut -f1)), 보관 $(ls -1 "$DEST"/harness-backup-*.tar.gz | wc -l)개"
cleanup

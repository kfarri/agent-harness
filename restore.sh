#!/usr/bin/env bash
# 새 라즈베리파이(Raspberry Pi OS 64비트)에 하네스를 백업 그대로 되살린다.
#   사용법:  sudo bash restore.sh harness-backup-YYYYMMDD-HHMM.tar.gz
set -euo pipefail
B=${1:-}
REPO_URL=${REPO_URL:-https://github.com/kfarri/agent-harness.git}
[ "$(id -u)" = 0 ] || { echo "root로 실행하세요: sudo bash restore.sh 백업파일"; exit 1; }
[ -f "$B" ] || { echo "백업 파일을 지정하세요: sudo bash restore.sh harness-backup-....tar.gz"; exit 1; }
tar tzf "$B" >/dev/null || { echo "백업 파일이 손상됐습니다: $B"; exit 1; }

echo "[1/7] 필요한 프로그램 설치..."
apt-get update -qq
apt-get install -y -qq git python3 curl ca-certificates openssh-client cifs-utils >/dev/null
nv=$(node -v 2>/dev/null | sed 's/^v//; s/\..*//' || echo 0)
if [ "${nv:-0}" -lt 20 ]; then
  curl -fsSL https://deb.nodesource.com/setup_20.x | bash - >/dev/null
  apt-get install -y -qq nodejs >/dev/null
fi
echo "      node $(node -v)"

echo "[2/7] agent 사용자 준비..."
id agent >/dev/null 2>&1 || adduser --disabled-password --gecos "" agent >/dev/null

echo "[3/7] 백업 파일 복원..."
systemctl stop agent-harness 2>/dev/null || true
tar xzpf "$B" -C /
mkdir -p /home/agent/agents/scripts /home/agent/agents/logs /home/agent/agents/repos
chown -R agent:agent /home/agent
[ -d /home/agent/.ssh ] && { chmod 700 /home/agent/.ssh; find /home/agent/.ssh -type f ! -name '*.pub' -exec chmod 600 {} +; }
[ -f /home/agent/agents/.env ] && chmod 600 /home/agent/agents/.env

echo "[4/7] Claude CLI 설치 확인..."
if ! sudo -u agent bash -lc 'command -v claude' >/dev/null 2>&1 && ! command -v claude >/dev/null 2>&1; then
  npm install -g @anthropic-ai/claude-code >/dev/null
fi
echo "      $(claude --version 2>/dev/null || sudo -u agent bash -lc 'claude --version')"

echo "[5/7] 하네스 프로그램 받기..."
if [ ! -d /opt/agent-harness-src/.git ]; then
  git clone -q --depth 1 "$REPO_URL" /opt/agent-harness-src
fi
chmod +x /opt/agent-harness-src/*.sh
if [ ! -f /etc/systemd/system/agent-harness.service ]; then
  cat > /etc/systemd/system/agent-harness.service <<'EOF'
[Unit]
Description=Agent harness GUI
After=network-online.target
[Service]
User=agent
WorkingDirectory=/home/agent/agents
EnvironmentFile=/home/agent/agents/.env
Environment=GUI_HOST=0.0.0.0
ExecStart=/usr/bin/python3 /home/agent/agents/scripts/gui_server.py
Restart=on-failure
StandardOutput=append:/home/agent/agents/logs/gui.log
StandardError=append:/home/agent/agents/logs/gui.log
[Install]
WantedBy=multi-user.target
EOF
fi
systemctl daemon-reload
systemctl enable agent-harness >/dev/null 2>&1

echo "[6/7] 코드 저장소 다시 받기 (GitHub)..."
python3 - <<'PY' | while IFS='|' read -r pid url path; do
import json
for p in json.load(open("/home/agent/agents/projects.json"))["projects"]:
    r = p.get("repo") or {}
    if r.get("url") and r.get("path"):
        print("%s|%s|%s" % (p["id"], r["url"], r["path"]))
PY
  if [ -d "$path/.git" ]; then echo "      $pid: 이미 있음 ($path)"; continue; fi
  key=/home/agent/.ssh/harness_$pid
  mkdir -p "$(dirname "$path")"; chown agent:agent "$(dirname "$path")"
  if sudo -u agent env GIT_SSH_COMMAND="ssh -i $key -o IdentitiesOnly=yes -o StrictHostKeyChecking=accept-new -o BatchMode=yes" \
       git clone -q "$url" "$path"; then echo "      $pid: 받음 ($url)"; else echo "      $pid: 실패 - 화면에서 '내려받기'를 다시 누르세요"; fi
done

echo "[7/7] 하네스 시작..."
/opt/agent-harness-src/update.sh

cat <<'EOF'

==== 복원 완료. 아래를 확인하세요 ====
1. Claude 로그인:  sudo -u agent claude   (로그인 화면이 나오면 다시 로그인)
2. 이 파이의 내부 IP가 예전과 같은지 확인하세요 (NAS 리버스 프록시·TRUST_PROXY_IPS 가 이 주소를 씁니다)
   지금 IP:  hostname -I
3. 매일 백업 다시 켜기:  sudo /opt/agent-harness-src/backup.sh --setup
4. 브라우저에서 하네스에 로그인해 프로젝트·작업 기록이 보이는지 확인
EOF

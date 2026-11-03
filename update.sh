#!/usr/bin/env bash
# 파이에서 최신 server.py 받아서 서비스 재시작
set -euo pipefail
REPO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TARGET="/home/agent/agents/scripts/gui_server.py"

echo "[1/4] 최신 코드 받는 중..."
git -C "$REPO_DIR" fetch --depth 1 origin main
git -C "$REPO_DIR" reset --hard origin/main

echo "[2/4] 문법 확인..."
python3 -c "import ast; ast.parse(open('$REPO_DIR/server.py').read())"

echo "[3/4] 적용..."
cp "$REPO_DIR/server.py" "$TARGET"
chown agent:agent "$TARGET"

echo "[4/4] 서비스 재시작..."
systemctl restart agent-harness
sleep 2
systemctl is-active --quiet agent-harness && echo "정상 실행 중" || { echo "실행 실패, 로그 확인:"; tail -20 /home/agent/agents/logs/gui.log; exit 1; }
wc -c "$TARGET"

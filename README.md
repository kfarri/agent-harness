# agent-harness

라즈베리파이 에이전트 하네스 GUI 서버 배포용 저장소.

## 파이에서 최초 1회 설정

```bash
git clone https://github.com/kfarri/agent-harness.git /opt/agent-harness-src
chmod +x /opt/agent-harness-src/update.sh
```

## 이후 업데이트 (root 셸)

```bash
/opt/agent-harness-src/update.sh
```

## 코드 저장소 연동 (예: 마이마)
1. 새 프로젝트 → 프리셋 "코드 저장소 수정" 선택
2. 설정 → 코드 저장소: `배포 키 보기` → GitHub 저장소 Settings → Deploy keys 에 붙여넣기 (Allow write access 체크)
3. 저장소 주소(`git@github.com:아이디/저장소.git`), 빌드 명령 입력 후 저장 → `내려받기`
4. 작업 요청 → 에이전트가 `harness/작업ID` 브랜치에서 코드 수정 → 하네스가 빌드 확인·커밋 → 코드리뷰 → 최종 승인 시 main 병합·푸시 (GitHub Actions 빌드)

## 백업·복원 (파이 고장 대비)
- 처음 한 번: `sudo /opt/agent-harness-src/backup.sh --setup` → NAS 공유 폴더·계정 입력 → 매일 04:17 자동 백업(최근 14개 보관)
- 백업 내용: ~/agents(설정·.env·프로젝트·작업 기록·참고 자료·보안 차단 목록), ~/.ssh(GitHub 배포 키), Claude 로그인 정보, systemd 서비스
- 빼는 것: 코드 저장소(repos, GitHub에서 다시 받음), 로그, node_modules
- 새 파이에서 복원: 백업 파일을 새 파이로 복사 → `sudo bash restore.sh harness-backup-YYYYMMDD-HHMMSS.tar.gz`

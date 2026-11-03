"""backend.py 의 @@INDEX_HTML@@ 자리에 index.html 을 넣어 단일 파일 server.py 를 만든다."""
from pathlib import Path

src = Path(__file__).parent
html = (src / "index.html").read_text()
assert '"""' not in html, "index.html 에 삼중 따옴표가 있으면 안 됩니다"
code = (src / "backend.py").read_text()
assert code.count("@@INDEX_HTML@@") == 1
out = src.parent / "server.py"
out.write_text(code.replace("@@INDEX_HTML@@", html))
print("생성:", out, out.stat().st_size, "bytes")

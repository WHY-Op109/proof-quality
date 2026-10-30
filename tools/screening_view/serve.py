#!/usr/bin/env python3
"""Browse screened proof pairs: earlier (rejected) and final (chosen) side by side.

python3 tools/screening_view/serve.py                 # http://127.0.0.1:8740/
python3 tools/screening_view/serve.py --port 8740 --no-open
python3 tools/screening_view/serve.py --data-dir data/mathlibpr/screening/2026-10-30

The page opens on pairs with a meaningful quality difference. Other views: hard cases,
unresolved, and no meaningful difference. Pairs keep their historical orientation; the
preferred side comes from the screening record and is never produced by swapping proofs.
"""

from __future__ import annotations

import argparse
import json
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlsplit

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
DEFAULT_DATA = REPO / "data" / "mathlibpr" / "screening" / "2026-10-30"
DEFAULT_DOCS = REPO / "docs" / "screening" / "2026-10-30"
EXPORTS = {"retain": "fast-retained.pairs.jsonl", "unresolved": "fast-unresolved.pairs.jsonl", "exclude": "fast-excluded.pairs.jsonl"}
DIMENSIONS = ["argument_abstraction", "reuse_modularity", "automation_fit", "explanatory_clarity", "robustness_maintenance", "library_integration"]
MATHLIB = "https://github.com/leanprover-community/mathlib4/blob/"


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def statement_of(prompt: str) -> str:
    marker = "following declaration.\n\n"
    at = prompt.find(marker)
    return (prompt[at + len(marker):] if at >= 0 else prompt).rstrip()


def basis(s: dict) -> str | None:
    """Describe agent cross-checks; None falls back to the single-reading label."""
    check = s.get("stage_a")
    if not check:
        return None
    return {
        "two_screens_agree": "two independent readings agree",
        "adjudicated": "two readings disagreed; a third agent adjudicated",
    }.get(check["outcome"], check["outcome"])


def build_data(data_dir: Path) -> dict:
    records = read_jsonl(data_dir / "FAST-SCREENING.jsonl")
    original = {}
    for decision, name in EXPORTS.items():
        rows = read_jsonl(data_dir / name)
        subset = [s for s in records if s["decision"] == decision]
        if len(rows) != len(subset):
            raise SystemExit(f"{name}: {len(rows)} rows but {len(subset)} screening records")
        for s, r in zip(subset, rows):
            original[s["source_line_1based"]] = r
    out = []
    for s in records:
        r = original[s["source_line_1based"]]
        sk = s["source_key"]
        out.append({
            "row": s["source_line_1based"], "decl": r["metadata"]["declaration_name"], "pr": r["metadata"]["pr_number"],
            "statement": statement_of(r["prompt"]), "earlier": r["rejected"], "final": r["chosen"],
            "decision": s["decision"], "direction": s["preference_direction"], "reason": s["reason"],
            "dims": [d for d in s.get("dimensions") or [] if d in DIMENSIONS], "assessor": s.get("assessor") or s["assessment_method"],
            "check": basis(s), "human": s["human_verbatim"], "discussion": s.get("discussion"), "cluster": s.get("cluster"),
            "spencer": s["spencer_retained"], "spencer_class": s["spencer_class"], "flags": s["usability_flags"],
            "earlier_url": MATHLIB + sk["earlier_snapshot_commit_sha"] + "/" + sk["earlier_file_path"],
            "final_url": MATHLIB + sk["final_snapshot_commit_sha"] + "/" + sk["file_path"],
        })
    return {
        "rows": out,
        "dimensions": DIMENSIONS,
        "subtitle": f"{len(out):,} declaration pairs from Mathlib PRs · screened against rubric v0.3",
        "footer": "Left is the earlier revision (the dataset's rejected field); right is the final, historically accepted revision (chosen). "
        "Acceptance is history, not a quality label: the outlined card is the side the screening prefers. Highlighting marks textual "
        "differences only. No Lean compilation, timing or historical lemma-availability check was run. "
        f"Data: {data_dir.name}. Report and discussion notes: /report and /discussion.md on this server.",
    }


def build_page(data: dict) -> bytes:
    template = (HERE / "site_template.html").read_text()
    payload = json.dumps(data, ensure_ascii=False).replace("</", "<\\/")
    body = template.replace("/*__DATA__*/", payload)
    return ("<!doctype html>\n<html lang=\"en\"><head><meta charset=\"utf-8\">"
            "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1, viewport-fit=cover\"></head><body>\n"
            + body + "\n</body></html>\n").encode()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--data-dir", type=Path, default=DEFAULT_DATA)
    parser.add_argument("--docs-dir", type=Path, default=DEFAULT_DOCS)
    parser.add_argument("--port", type=int, default=8740)
    parser.add_argument("--no-open", action="store_true")
    args = parser.parse_args()
    data_dir = args.data_dir.expanduser().resolve()
    docs_dir = args.docs_dir.expanduser().resolve()
    data = build_data(data_dir)
    page = build_page(data)
    routes = {
        "/": (lambda: page, "text/html; charset=utf-8"),
        "/index.html": (lambda: page, "text/html; charset=utf-8"),
        "/report": (lambda: (docs_dir / "FAST-SCREENING.md").read_bytes(), "text/plain; charset=utf-8"),
        "/discussion.md": (lambda: (docs_dir / "FAST-DISCUSSION.md").read_bytes(), "text/plain; charset=utf-8"),
    }

    class Handler(BaseHTTPRequestHandler):
        def do_GET(self) -> None:
            route = routes.get(urlsplit(self.path).path)
            if route is None:
                self.send_error(404)
                return
            body, kind = route[0](), route[1]
            self.send_response(200)
            self.send_header("Content-Type", kind)
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(body)

        def log_message(self, *_args) -> None:
            pass

    server = None
    for port in range(args.port, args.port + 20):
        try:
            server = ThreadingHTTPServer(("127.0.0.1", port), Handler)
            break
        except OSError:
            continue
    if server is None:
        raise SystemExit(f"Could not bind a port starting at {args.port}")
    url = f"http://127.0.0.1:{port}/"
    counts = {d: sum(r["decision"] == d for r in data["rows"]) for d in EXPORTS}
    print(f"Serving {data_dir}\nmeaningful difference {counts['retain']}, unresolved {counts['unresolved']}, "
          f"no meaningful difference {counts['exclude']}\n{url}", flush=True)
    if not args.no_open:
        webbrowser.open(url)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Browse proof-pair screening results with the existing triplet viewer.

python3 tools/screening_view/serve.py                # retained pairs (default view)
python3 tools/screening_view/serve.py --port 8740 --no-open
python3 tools/screening_view/serve.py --data-dir data/mathlibpr/screening/2026-10-30

Views: /  retained · /unresolved/ · /exclude/ · /discussion/ (cases flagged for the user)
Each pair keeps its historical orientation: left = earlier revision (`rejected` field),
right = final revision (`chosen` field). The preferred side comes from the screening record,
never from swapping the proofs.
"""

from __future__ import annotations

import argparse
import html
import json
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlsplit

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
TRIPLET_HTML = REPO / "tools" / "triplet_view" / "index.html"
DEFAULT_DATA = REPO / "data" / "mathlibpr" / "screening" / "2026-10-30"
DEFAULT_DOCS = REPO / "docs" / "screening" / "2026-10-30"
VIEWS = {"retain": "Retained", "unresolved": "Unresolved", "exclude": "Excluded", "discussion": "Discussion"}
EXPORTS = {"retain": "fast-retained.pairs.jsonl", "unresolved": "fast-unresolved.pairs.jsonl", "exclude": "fast-excluded.pairs.jsonl"}

PANEL_CSS = """
<style>
  .screen { margin: 1rem 0 0; padding: 0.9rem 1rem; border: 1px solid var(--line); border-radius: 10px; background: #f6f8fa; }
  .screen nav a { margin-right: 0.8rem; }
  .screen nav a[aria-current="page"] { font-weight: 700; color: var(--ink); text-decoration: none; }
  .screen .verdict { font-weight: 600; margin: 0.5rem 0 0.25rem; }
  .screen .human { border-left: 3px solid #8250df; padding-left: 0.6rem; margin: 0.5rem 0; }
  .screen .note { color: var(--muted); font-size: 0.85rem; margin: 0.4rem 0 0; }
  .badge { display: inline-block; margin-left: 0.5rem; padding: 0 0.45rem; border-radius: 999px; font-size: 0.75rem; background: #1f883d; color: #fff; }
  .card.preferred { border: 2px solid #1f883d; }
</style>
"""


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def build_page(view: str) -> bytes:
    page = TRIPLET_HTML.read_text()
    page = page.replace("<title>Proof triples</title>", f"<title>Screening · {VIEWS[view]}</title>" + PANEL_CSS)
    page = page.replace(
        "<h2>Rejected</h2>",
        '<h2 id="left-title">Earlier revision <small>(historically superseded · <code>rejected</code>)</small></h2>',
    ).replace(
        "<h2>Accepted</h2>",
        '<h2 id="right-title">Final revision <small>(historically accepted · <code>chosen</code>)</small></h2>',
    )
    links = " ".join(
        f'<a href="{"/" if v == "retain" else "/" + v + "/"}"{" aria-current=page" if v == view else ""}>{label}</a>'
        for v, label in VIEWS.items()
    )
    panel = (
        f'<section class="screen" aria-live="polite"><nav>{links} · <a href="/report">Report</a> · '
        f'<a href="/discussion.md">Discussion notes</a></nav>'
        '<div id="screen-body">Loading screening record…</div>'
        '<p class="note">Left/right are historical roles, not quality labels. No Lean compilation or '
        "profiling was run. Highlighting marks textual differences only.</p></section>"
    )
    page = page.replace('<pre class="statement" id="statement"></pre>', panel + '\n    <pre class="statement" id="statement"></pre>')
    page = page.replace('["/pairs.jsonl", "../../data/mathlibpr/pairs.jsonl"]', f'["/data/{view}.jsonl"]')
    helper = """
    const VIEW = __VIEW__;
    const screening = fetch('/data/' + VIEW + '.screening.json').then((r) => r.json());
    const PREF = {
      final_better: 'Preferred: FINAL revision (right)',
      earlier_better: 'Preferred: EARLIER revision (left)',
      no_material_preference: 'No material preference',
      unresolved: 'Unresolved: no preference established',
      insufficient_evidence: 'Unresolved: insufficient evidence',
    };
    function para(cls, text) { const p = document.createElement('p'); if (cls) p.className = cls; p.textContent = text; return p; }
    async function renderScreening(pos) {
      const s = (await screening)[pos];
      const body = $('screen-body');
      body.replaceChildren();
      for (const id of ['left-title', 'right-title']) {
        $(id).querySelector('.badge')?.remove();
        $(id).parentElement.classList.remove('preferred');
      }
      if (!s) { body.append(para('', 'No screening record for this row.')); return; }
      const side = s.preference_direction === 'final_better' ? 'right-title' : s.preference_direction === 'earlier_better' ? 'left-title' : null;
      if (side) {
        const b = document.createElement('span'); b.className = 'badge'; b.textContent = 'preferred';
        $(side).append(b); $(side).parentElement.classList.add('preferred');
      }
      body.append(para('verdict', `${s.decision.toUpperCase()} · ${PREF[s.preference_direction] || s.preference_direction}`));
      body.append(para('', s.reason));
      if (s.human_verbatim) {
        const h = para('human', `Your verdict (${s.human_decision_id}): “${s.human_verbatim}”` + (s.decision === 'unresolved' ? ' — deferred for discussion.' : ''));
        body.append(h);
      }
      if (s.discussion) body.append(para('human', `Discussion (${s.discussion.source}): ${s.discussion.why}` + (s.discussion.question ? ` Question: ${s.discussion.question}` : '')));
      if (s.agent_disagreements && s.agent_disagreements.length) body.append(para('note', 'Agent disagreements: ' + s.agent_disagreements.map((d) => `${d.agent}: ${d.view}`).join('; ')));
      const meta = para('note', `Original row ${s.source_line_1based} · Spencer: ${s.spencer_retained ? 'retained' : 'excluded'} (${s.spencer_class}) · Basis: ${s.assessment_method}` + (s.assessor ? ` by ${s.assessor}` : '') + (s.usability_flags.length ? ` · Usability: ${s.usability_flags.join(', ')}` : '') + ' · ');
      const a = document.createElement('a'); a.href = '/explanation/' + s.source_line_1based; a.textContent = 'full record and historical sources';
      meta.append(a); body.append(meta);
    }
"""
    page = page.replace("    const $ =", helper.replace("__VIEW__", json.dumps(view)) + "\n    const $ =")
    page = page.replace("      window.scrollTo(0, 0);", "      window.scrollTo(0, 0);\n      renderScreening(index);")
    page = page.replace("let highlight = false;", "let highlight = true;").replace(
        'id="diff-toggle" aria-pressed="false"', 'id="diff-toggle" aria-pressed="true"'
    )
    page = page.replace("Run python3 tools/triplet_view/serve.py from the repo.", "This view is empty.")
    return page.encode()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--data-dir", type=Path, default=DEFAULT_DATA)
    parser.add_argument("--docs-dir", type=Path, default=DEFAULT_DOCS)
    parser.add_argument("--port", type=int, default=8740)
    parser.add_argument("--no-open", action="store_true")
    args = parser.parse_args()
    data_dir = args.data_dir.expanduser().resolve()
    docs_dir = args.docs_dir.expanduser().resolve()
    records = read_jsonl(data_dir / "FAST-SCREENING.jsonl")
    original = {}
    for view, name in EXPORTS.items():
        rows = read_jsonl(data_dir / name)
        subset = [s for s in records if s["decision"] == view]
        if len(rows) != len(subset):
            raise SystemExit(f"{name}: {len(rows)} rows but {len(subset)} screening records")
        for s, r in zip(subset, rows):
            original[s["source_line_1based"]] = r
    by_view = {v: [s for s in records if s["decision"] == v] for v in EXPORTS}
    by_view["discussion"] = [s for s in records if s.get("discussion")]

    def payload(path: str) -> tuple[bytes, str] | None:
        if path in ("/", "/index.html") or path.rstrip("/") in [f"/{v}" for v in VIEWS if v != "retain"]:
            view = path.strip("/").split("/")[0] or "retain"
            return build_page("retain" if view == "index.html" else view), "text/html; charset=utf-8"
        for view, subset in by_view.items():
            if path == f"/data/{view}.jsonl":
                text = "".join(json.dumps(original[s["source_line_1based"]], ensure_ascii=False) + "\n" for s in subset)
                return text.encode(), "application/x-ndjson; charset=utf-8"
            if path == f"/data/{view}.screening.json":
                return json.dumps(subset, ensure_ascii=False).encode(), "application/json; charset=utf-8"
        if path == "/report":
            return (docs_dir / "FAST-SCREENING.md").read_bytes(), "text/plain; charset=utf-8"
        if path == "/discussion.md":
            return (docs_dir / "FAST-DISCUSSION.md").read_bytes(), "text/plain; charset=utf-8"
        if path.startswith("/explanation/") and path.rsplit("/", 1)[-1].isdigit():
            row = int(path.rsplit("/", 1)[-1])
            if not 1 <= row <= len(records):
                return None
            s = records[row - 1]
            sk = s["source_key"]
            links = "".join(
                f'<p><a href="{html.escape("https://github.com/leanprover-community/mathlib4/blob/" + sk[side + "_snapshot_commit_sha"] + "/" + sk[path_key])}">{side} historical source</a></p>'
                for side, path_key in (("earlier", "earlier_file_path"), ("final", "file_path"))
            )
            body = f'<!doctype html><meta charset="utf-8"><title>Row {row}</title><p><a href="/">Viewer</a> · <a href="/report">Report</a></p>{links}<pre style="white-space:pre-wrap">{html.escape(json.dumps(s, ensure_ascii=False, indent=2))}</pre>'
            return body.encode(), "text/html; charset=utf-8"
        return None

    class Handler(BaseHTTPRequestHandler):
        def do_GET(self) -> None:
            result = payload(urlsplit(self.path).path)
            if result is None:
                self.send_error(404)
                return
            data, kind = result
            self.send_response(200)
            self.send_header("Content-Type", kind)
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(data)

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
    counts = ", ".join(f"{VIEWS[v]} {len(s)}" for v, s in by_view.items())
    print(f"Serving {data_dir}\n{counts}\n{url}", flush=True)
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

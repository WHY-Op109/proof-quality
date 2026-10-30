# Proof-pair screening, 2026-10-30

- `FAST-SCREENING.md`: coverage, comparison with Spencer's 539/2,379, examples, reformulated research question, proposed proof-term experiment.
- `FAST-DISCUSSION.md`: cases you flagged (Part A) and agent suggestions with grouped questions (Part B).
- `RUBRIC.md`, `APPROVAL.json`: the approved rubric v0.3 and its approval record (unchanged copies).
- `human-records/`: verbatim copies of `human-decisions.jsonl` and `meeting-flags.jsonl` (originals unchanged).
- `run.py`, `discussion.py`, `rules.json`, `manifest.json`, `continuation-assessments.json`, `round2/`: merge policy and inputs. In the review directory these sit under `fast-screen/`, which is where `run.py` expects them.
- `agent-disagreements.jsonl`: checkpoint rows where independent agent records differ.
- Data: `data/mathlibpr/screening/2026-10-30/` (screening records and exact original-row exports).

View: `python3 tools/screening_view/serve.py`, which serves retained pairs by default, plus `/unresolved/`, `/exclude/`, `/discussion/` and `/report`.

# Stage A3: adjudication brief

Two independent screeners read the same proof pair and disagreed. You decide. Read `round2/BRIEF.md` (one directory up) first: its rubric, classification rules and human calibration all apply.

Each row shows Screen X and Screen Y, presented in random order. Neither one is the "first" or the more authoritative screen. Read the diff yourself, then pick the better-supported view, or your own.

Calibration from a blind test against the user's real verdicts:
- The screeners **under-weight small but real clarity gains**. Examples: "clearer use of the general fact", "simpler presentation". The user retains these as `final_better`. Retain when the gain is concrete and visible (a named general fact or characterisation replaces a detour; a clearly simpler structure), even if it is small.
- Cases the user **deferred as hard** look like convention changes on the surface but alter how much of the argument is explicit. Examples: split_ifs/rw→`by_cases <;> simp`; simp-set visibility inside a grind witness; explicit witness transport→`cat_disch`. If the dispute is about this, choose `unresolved`; do not exclude it.
- Pure convention (`simp only`→`simp` closing a goal, `field_simp`→`field`, comment moves or removals, `by rfl`→`rfl`) stays excluded.

## Output
A JSON object keyed by row number (string):
```json
{"123": {"decision": "...", "direction": "...", "category": "...", "dimensions": [...],
         "reason": "one or two sentences: the concrete change and why", "chose": "X|Y|own",
         "open_question": "only if unresolved: the specific question that would settle it"}}
```
The consistency rules are the same as in BRIEF.md.

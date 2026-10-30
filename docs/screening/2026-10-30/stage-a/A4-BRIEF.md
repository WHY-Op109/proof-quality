# Stage A4: clustering brief

You receive the rows that remain **unresolved** after two screens and adjudication. Each row comes with its reasons and open question. Group them by the **question a user would have to answer** to settle them. Group by the type of decision, not by mathematical topic.

Rules:
- At most 12 clusters. A row that fits no cluster goes to `"singleton"` clusters; keep these to at most 5. Rows that are blocked by data defects (truncated or empty bodies) or need historical context no user answer could supply go to the cluster `"needs_context"`. That cluster gets no question.
- For each cluster, write:
  - `question`: one sentence, answerable as *final better / earlier better / no difference / depends*.
  - `summary`: what the rows have in common.
  - `representative`: the single row whose diff shows the question most clearly and briefly.
  - `members`: every row in the cluster.
- Do not decide any row yourself.

## Output
Write one JSON object:
```json
{"clusters": [{"cluster_id": "automation-main-step", "question": "...", "summary": "...", "representative": 1762, "members": [1762, 1344]}]}
```
Every input row must appear in exactly one cluster.

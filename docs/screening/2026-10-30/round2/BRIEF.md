# Round-2 individual screening brief (Claude Code, 2026-10-30)

You screen Lean/Mathlib proof pairs. Each pair has an **earlier** revision (historically rejected) and a **final** revision (historically accepted) of the same declaration. These are historical roles: the final is not automatically better. Acceptance, shorter length, or a structural edit alone does **not** establish improvement. The earlier proof may be better.

Approved rubric: `../../RUBRIC.md`, v0.3, especially §3–§4. Dimensions: argument_abstraction, reuse_modularity, automation_fit, explanatory_clarity, robustness_maintenance, library_integration. Materiality means a specific consequence for understanding, abstraction, reuse, automation or maintenance beyond conformity. Support levels: observed / mechanism_documented / speculative. Convention conformity has no automatic quality direction.

## Classification (per row)
- `retain` + `final_better` or `earlier_better`: a specific, material, source-visible quality difference. Examples: a general library theorem or characterisation replaces a bespoke derivation; duplicated construction removed; the argument is reorganised so the main idea is exposed; an explicit proof replaces opaque automation in a way that clearly aids understanding, or the reverse. Retain with `earlier_better` when the earlier proof is better (e.g. the final hides a meaningful explicit argument, or adds needless detours).
- `exclude` + `no_material_preference`: you positively inspected the difference and it has little apparent quality effect. Examples: renames or API migrations of lemma names, simp-set tweaks, `simp only`↔`simp` or `field_simp`→`field` conventions, comment placement/removal/capitalisation, `by rfl`/`rfl`, `@`/explicit args, layout, `fun`/`intro`, `exact`/term mode, `<;>` combination, deprecated-alias replacement, small reordering.
- `unresolved` + `unresolved`: you looked but cannot decide. Examples: automation versus explicit steps where both expose the same mathematics; hidden detail versus brevity; changed definitions/API whose effect needs historical context; a new comment whose explanatory value is unclear; truncated or unclear diff. Give the **specific** open question.

## Human calibration (pair-specific; do NOT turn into blanket rules)
User verdicts. **No difference**: comment placement or removal (rows 947, 1063, 2250); `simp only`→`simp` closing a goal is just convention (1162); `field_simp`→`field` is convention (1203); `aesop` replacing an explicit finiteness side-condition proof (1381); 760, 815, 1119. **Final better**: "clearer use of the general fact" (2095); "uses the right general abstraction" (1935); "reuses the characterization" (1759); "useful general-lemma reuse" (817, 445); "reusable library setup exposes the main argument" (572); "simpler presentation" (2124). **Deferred as hard**: 1574 (`simp only [...]`→`simp [...]` before grind); 1617 (explicit witness transport→`cat_disch`, "I don't know how cat_disch works"); 1587 (split_ifs/rw→`by_cases <;> simp`, "no math significance, hard to see quality from code"); 1128 (more calc steps, small presentation gain, no clear meaningful difference). The user has **not** settled a general automation-versus-explicit preference.

Also consider: reuse; organisation; automation versus explicit proof; convention/maintenance changes, which are usually exclude unless a concrete consequence is visible.

## Output
Write ONLY a JSON object to the output path given to you, keyed by row number (string). Every row in your packet must appear:
```json
{"123": {"decision": "retain|exclude|unresolved",
         "direction": "final_better|earlier_better|no_material_preference|unresolved",
         "category": "clear_quality_difference|little_apparent_mathematical_effect|difficult_preference|mixed_changes",
         "dimensions": ["reuse_modularity", "..."],
         "reason": "one or two concise rubric-based sentences naming the concrete change and why it does/doesn't matter",
         "difficult_for_user": false}}
```
Consistency: retain ⇒ final_better/earlier_better + clear_quality_difference; exclude ⇒ no_material_preference + little_apparent_mathematical_effect; unresolved ⇒ unresolved + difficult_preference or mixed_changes. Set `difficult_for_user: true` only for a genuinely hard, discussion-worthy case where quality is truly ambiguous and a user question would settle a class of cases. Add `"question": "..."` in that case. Use it sparingly, at most about 3 per packet.
Use `earlier_better` honestly when warranted. Do not retain because of length. Earlier-side lemma availability is not verified, so say "earlier availability unverified" when a reuse claim depends on it.
If a diff is truncated and you need the full bodies, read line N of `/Users/why/Documents/Projects/Research_Project/AI4Maths/proof-quality/data/mathlibpr/pairs.jsonl` (`rejected` = earlier, `chosen` = final). Do not modify any other file.

# Round-2 individual screening brief (Claude Code, 2026-10-30)

You screen Lean/Mathlib proof pairs. Each pair has an **earlier** revision (historically rejected) and a **final** revision (historically accepted) of the same declaration. These are historical roles: the final is not automatically better. Acceptance, shorter length, or a structural edit alone does **not** establish improvement. The earlier proof may be better.

Approved rubric: `../../RUBRIC.md`, v0.3, especially §3–§4. Dimensions: argument_abstraction, reuse_modularity, automation_fit, explanatory_clarity, robustness_maintenance, library_integration. Materiality means a specific consequence for understanding, abstraction, reuse, automation or maintenance beyond conformity. Support levels: observed / mechanism_documented / speculative. Convention conformity has no automatic quality direction.

## Classification (per row)
- `retain` + `final_better` or `earlier_better`: a specific, material, source-visible quality difference. Examples: a general library theorem or characterisation replaces a bespoke derivation; duplicated construction removed; the argument is reorganised so the main idea is exposed; an explicit proof replaces opaque automation in a way that clearly aids understanding, or the reverse. Retain with `earlier_better` when the earlier proof is better (e.g. the final hides a meaningful explicit argument, or adds needless detours).
- `exclude` + `no_material_preference`: you positively inspected the difference and it has little apparent quality effect. Examples: renames or API migrations of lemma names, simp-set tweaks, `simp only`↔`simp` or `field_simp`→`field` conventions, comment placement/removal/capitalisation, `by rfl`/`rfl`, `@`/explicit args, layout, `fun`/`intro`, `exact`/term mode, `<;>` combination, deprecated-alias replacement, small reordering.
- `unresolved` + `unresolved`: you looked but cannot decide. Examples: automation versus explicit steps where both expose the same mathematics; hidden detail versus brevity; changed definitions/API whose effect needs historical context; a new comment whose explanatory value is unclear; truncated or unclear diff. Give the **specific** open question.

## Human calibration (pair-specific; do NOT turn into blanket rules)
The user's verdicts on other pairs:
- `PartialOrder.mem_nerve_nonDegenerate_iff_strictMono`: final_better. User: "Final is better: useful general-lemma reuse"
- `IsGaloisGroup.card_fixingSubgroup_eq_finrank`: no_material_preference. User: "No meaningful quality difference"
- `Cycle.chain_map`: no_material_preference. User: "Mathlib Convention (check if some goal can be closed using simp then without use simp only, if so, just convention, no significan proof quality difference"
- `Vitali.exists_disjoint_subfamily_covering_enlargement`: no_material_preference. User: "Is this just a mathlib transfering or mathlib convention, that if something can be solved by field_simp or field prefer field tactic? Check this, if so, no proof quality difference, just convention"
- `EReal.toReal_pos`: no_material_preference. User: "No meaningful quality difference"
- `MeasureTheory.stoppedProcess_indicator_comm`: DEFERRED as hard to judge. User: "defer and add this for meeting discussion. That, there is no math siginificance of this, this is hard to see the proof quality just from the code"
- `ModuleCat.uliftFunctor_map_exact`: DEFERRED as hard to judge. User: "Defer，similar as case 13 for discussion"
- `ClosedSubmodule.closure_toSubmodule_eq`: final_better. User: "Final is better: clearer use of the general fact"
- `diam_stdSimplex_le`: final_better. User: "Final is better: simpler presentation"
- `PowerSeries.exp_unique_of_derivative_eq_self`: no_material_preference. User: "No quality difference, this is the second similar one, this is just delete the comments no quality difference"
The user has **not** settled a general automation-versus-explicit preference. Cases the user found hard were deferred; mark comparable cases `unresolved`.

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
Consistency: retain ⇒ final_better/earlier_better + clear_quality_difference; exclude ⇒ no_material_preference + little_apparent_mathematical_effect; unresolved ⇒ unresolved + difficult_preference or mixed_changes. Set `difficult_for_user: true` only for a genuinely hard, discussion-worthy case where quality is truly ambiguous and a user question would settle a class of cases. Add `"question": "..."` in that case. Use it sparingly.
Use `earlier_better` honestly when warranted. Do not retain because of length. Earlier-side lemma availability is not verified, so say "earlier availability unverified" when a reuse claim depends on it.
If a diff is truncated and you need the full bodies, read line N of `/Users/why/Documents/Projects/Research_Project/AI4Maths/proof-quality/data/mathlibpr/pairs.jsonl` (`rejected` = earlier, `chosen` = final). Do not modify any other file.

## Blind-test rules
Rows are labelled C.. and bodies are given in full. Do **not** open any other file (no pairs.jsonl, human-decisions, FAST-*, reports or earlier outputs). This is a held-out calibration test.

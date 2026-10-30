# Proposed proof-change review rubric

Version: **0.3.0-proposed**, 2026-10-30. **Awaiting user approval; not screening instructions in force.** Consolidates [Codex research](RESEARCH.md), [the original draft](RUBRIC-DRAFT.md) and [Claude's independent review](CLAUDE-REVIEW.md). Operational scope and approval choices: [REVIEW-PLAN.md](REVIEW-PLAN.md). This revision incorporates B1–B4 and O3–O4 explicitly proposed in [Claude’s follow-up](CLAUDE-FOLLOWUP-REVIEW.md). Reviewed source versions, current hashes and the response to every concern are recorded in [REVIEW-PLAN.md §8](REVIEW-PLAN.md#8-follow-up-reconciliation-and-version-coverage) and [reconciliation manifest](reconciliation/2026-10-30/manifest.json). Claude assessed the predecessor and proposed these amendments; it has not reread this assembled revision. Any amendment requires a new version and hash.

## 1. Question and boundaries

For each historical pair, describe **what changed**, **which quality effects have evidence**, and **what remains unknown**. This round does not decide training inclusion, assign rewards or implement a filter. Mathlib acceptance is a PR-history proxy, not a local proof-quality judgment. Earlier/final are historical roles; neither is inherently worse/better.

The population consists of 2,379 extracted declaration pairs with matching normalized source signatures. Extraction omits many statement changes, renamed/unmatched declarations and final-only edits. Its earlier-side selection is asymmetric. Conclusions apply to this stored extraction, not all Mathlib proof improvements. Matching signature text does not establish identical elaborated statements or environments.

Proposed policy: report relative effects without numeric scores, weighted averages or a compulsory pair ordering. Pure convention conformity is descriptive. A small but supported readability gain may be recorded; it need not qualify as a material argument improvement. The user decides later which effects matter for any downstream task. No paper's metric is adopted by this rubric.

## 2. Check usability before judging quality

Record the following for every pair. Unknown values remain explicit; an absent check never means success.

| Field | Required distinction |
| --- | --- |
| Identity | Existing `sample_id`, dataset hash, source line, PR, declaration, both paths and snapshot SHAs; preserve source metadata |
| Role | `ordinary_proof`, `test_fixture`, `expected_error`, `example_or_counterexample`, `other`, `unknown`; path is a clue, not a verdict |
| Extraction | `plausible`, `problem_found`, `not_checked`, with missing surrounding definitions/binders noted |
| Completion | `no_admission_observed`, `admission_observed`, `intentional_failure`, `unknown`; source inspection is not a transitive axiom check |
| Verification | Each endpoint separately: `not_run`, `passed`, `failed`, `blocked`; exact historical context, command and evidence if run |
| Environment | Both diff-base SHAs; `diff_bases_differ`; base distance and definition of distance if checked; changed imports/definitions/instances relevant to this proof |
| Provenance flags | `proof_reverted`, `file_path_changed`, `path_role`, test-split membership, historical filter class/action, exposure history |
| Comparability | Per assessed dimension: `adequate_for_claim`, `conditional_on_environment`, `blocked`, `unresolved`, with a claim-specific explanation. Pair-level `comparability_overall` summarizes the worst assessed claim: blocked, then unresolved, then conditional, then adequate; use unresolved if none is assessed. This summary does not invalidate otherwise assessable dimensions. |

Different bases are common, so record drift for everyone; do not mark every drifting pair incomparable. Equal bases would not rule out PR-internal context changes either. A build-passing repository can contain intentional failures and admitted dependencies. Keep fixtures in the audit as usability findings, but do not give them an ordinary complete-proof preference.

For `proof_reverted=true`, explain that the final restores the pre-PR proof. Record whether the abandoned edit later landed elsewhere: `yes`, `no_evidence_found_in_stated_search`, `not_checked`, or `unknown`. Reversion does not establish inferiority.

### Closed fields for comparison (B1)

- `path_role` is mechanically derived from the path: `Mathlib`, `MathlibTest`, `Archive`, `Counterexamples`, `other`. It is separate from the judged `role` above.
- `convention_conformity.change`: `final_more_conforming`, `earlier_more_conforming`, `mixed`, `no_change`, `unknown`; also record `rule_source`, `rule_date_known` (boolean), applicability and explanation.
- `non_quality_acceptance_factors[].code`: `pr_scope`, `ci_or_conflict`, `naming_policy`, `deprecation_policy`, `abandonment`, `review_logistics`, `import_or_api_integration`, `unknown`; each entry has `status: observed / hypothesis` and evidence. These codes do not imply that the factor has no possible quality effect.
- Availability `unresolved_reason`: `not_attempted`, `ambiguous_result`, `access_failed`, `budget_exhausted`; explain the limitation.
- `exposure`: `anchor`, `listed_in_saved_report`, `content_seen_in_prior_session`, `none_recorded`, `exposure_unknown`. Keep agent/person and source-specific exposure entries when more than one applies. `none_recorded` does not certify that content was unseen. Claude's Appendix A supplies additional exposure evidence.

## 3. Describe each change, allowing multiple labels

| Category | What to describe |
| --- | --- |
| `argument_strategy` | A different mathematical route or intermediate propositions, not just tactic names |
| `library_reuse` | Delegating an argument to a reusable theorem or abstraction |
| `automation` | Different solver, search, simplification or direct construction |
| `local_facts_and_rewrites` | Intermediate facts, dependencies, rewrite organization and lemma choices |
| `presentation_structure` | Ordering, grouping, tactic/term form or explicit intermediate reasoning |
| `explanatory_comment` | Added, removed or changed mathematical explanation |
| `naming_or_notation` | Names, notation and accessors; describe any explanatory effect separately |
| `syntax_or_layout` | Wrappers, formatting and syntactic variants |
| `api_or_migration` | Compatibility, deprecation and changed library interfaces |
| `statement_or_environment` | Relevant context/type changes; flag possible extraction limitations |
| `draft_cleanup` | TODOs, abandoned commented code and other work-in-progress cleanup |

Attach exact fragments and a plain-language explanation to each label. Track `motivation` per change as `required_for_compatibility`, `migration_adoption_not_shown_required`, `voluntary_supported`, or `unknown`, with the evidence. Distinguish PR-internal from upstream causes. A deprecated alias still working means a naming update is not proven compulsory. Required compatibility work may also have a quality effect; assess that separately instead of automatically declaring it good, bad or inapplicable.

Record `non_quality_acceptance_factors` as evidence-backed observations or explicitly marked hypotheses: PR scope, conflict/CI resolution, naming policy, deprecation policy, abandonment, review logistics, or unknown. Import placement and API integration can also carry quality information; do not classify them as exclusively administrative. A PR title establishes stated intent, not the success of the change or its actual landing. Use commit-linked bors/landing evidence when establishing historical acceptance; GitHub's `merged` flag alone is unreliable for this workflow.

## 4. Assess affected quality dimensions

| Dimension | Evidence that could support an effect | Insufficient shortcut |
| --- | --- | --- |
| `argument_abstraction` | More appropriate mathematical objects, removal of duplicated derivation, clearer dependency reasoning | Fewer lines or a changed tactic set |
| `reuse_modularity` | A suitable general result replaces bespoke reasoning; useful factoring | Any shorter lemma invocation |
| `automation_fit` | Direct reasoning exposes the goal; appropriately scoped solver; actual search/performance evidence | `rfl`, `simp` or `grind` always wins |
| `explanatory_clarity` | Reader can reconstruct the argument more readily; meaningful intermediate claims/comments | Formatting or capitalization alone |
| `robustness_maintenance` | Reduced dependence on fragile unfolding, positional structure or uncontrolled rewriting, with a concrete mechanism | A style rule automatically proves fragility |
| `library_integration` | Better API fit, reuse or import discipline, with consequences for library users | Conforming to house style alone |

Report `convention_conformity` separately: rule/source, applicability at the historical date if known, and observed compliance change. It has **no automatic quality direction**. If conformity has a concrete effect, assess that effect in an appropriate dimension. ProofJudge tactic prescriptions and present-day Mathlib guidance are references to question, not timeless laws.

For each assessed dimension record:

- `direction`: `final_better`, `earlier_better`, `no_material_preference`, `tradeoff`, `insufficient_evidence`, `not_applicable`, or `not_assessed`.
- `magnitude`: `small`, `material`, `unclear`, or `not_applicable`. Material means a specific consequence for understanding, abstraction, reuse, automation or maintenance beyond mere conformity; explain it. There is no line/token threshold.
- `benefit_scope`: one or both of `local_proof` and `library_fit`.
- `evidence_sufficiency`: `sufficient`, `partial`, `none`; `confidence`: `high`, `medium`, `low`, with reason. Confidence cannot replace missing evidence.
- `comparability` as above, and `decisive` (boolean) identifying whether this dimension determines a conclusion or unresolved decision; explain why when true.
- Exact evidence references, causal explanation, limitations and counterarguments. A dimension left `not_assessed` may be recorded with only its name and direction; it is not a neutral judgment.

`no_material_preference` requires positive inspection of the relevant difference. It is not a substitute for uncertainty. `tradeoff` requires supported competing effects; a speculative downside yields an unresolved question instead. Multiple labels/effects set `mixed=true`; neither majority voting nor character length resolves them.

For each claimed effect, record `support_level` (B2): `observed` for an observed consequence such as breakage, compilation or measurement under a stated setup; `mechanism_documented` when the code exhibits the relevant pattern and a cited source explains the mechanism; `speculative` when that mechanism lacks support. Record exact evidence and applicable historical context. Observing a syntactic pattern alone does not establish its claimed consequence.

Proposed threshold: a tradeoff requires both opposing effects to have at least `mechanism_documented` support; record each effect's level separately. Mechanism-supported risk is not observed breakage. A speculative opposing effect stays an unresolved question. This threshold is explicitly for the user's approval. Row 1291 remains a candidate to investigate under this rule, not a preassigned tradeoff label.

For A/B presentations (B3), initial observations refer only to A and B. Open the orientation map before writing historical `earlier_better`/`final_better` fields and store `orientation_map_sha256`; preserve the initial observation. Record chronology exposure rather than claiming blindness if history was already known.

Optional `pair_summary`: `final_better_supported`, `earlier_better_supported`, `no_material_preference_supported`, `tradeoff`, `insufficient_evidence`, `comparison_blocked`, or `not_assessed`. Identify the dimensions driving any summary. Proposed pilot default: leave this optional; never force a total ordering.

## 5. Evidence and historical API checks

Evidence types: `source_comparison`, `local_review_reason`, `local_review_suggestion`, `pr_context`, `historical_api_check`, `compilation`, `profiling`, `human_judgment`, `reference_guidance`. Each record identifies its source, what was actually checked, and the exact claim it supports. Map comments/profiles to endpoints; evidence for a different revision cannot substantiate this pair. Absence of reviewer reasons does not preclude a source-based assessment, but that assessment must be labeled as such.

A directional reuse claim requires checking relevant declarations and availability in the historical snapshots and bases:

| Availability | Interpretation |
| --- | --- |
| `available_at_earlier_base` | Already present in the earlier base; check accessibility in the earlier proof context |
| `pr_internal_present_at_earlier_snapshot` | Added in the PR before or at the earlier snapshot |
| `pr_internal_added_after_earlier_snapshot` | Added later within the PR; establish provenance, not merely absence/presence |
| `upstream_between_bases` | Present at the final base, absent at the earlier base, and not introduced in the PR’s own diff; record the historical checks supporting all three |
| `unresolved` | Checks incomplete, ambiguous, unavailable or not yet performed; record why |

Check imports, names, types and relevant hypotheses as well as textual existence. File absence alone is not proof of global absence; use historical search/rename history where needed. If accessibility or applicability remains decisive and unresolved, mark the claim conditional or insufficient. Final-side reuse may improve the final proof without implying that the earlier author ignored an available lemma.

Compilation and profiling are separate checks. Report errors, missing environments and unrun checks; never discard failed historical builds silently. No runtime advantage without measurements under a stated comparison setup. No proof-term compression or width claim without a separate approved experiment and definition.

## 6. Diagnostic anchors, not gold labels

Rows refer to the pinned dataset; use the inventory ID in actual records. These examples are already exposed and must not enter an unexposed agreement estimate.

| Rows | Consolidated use |
| --- | --- |
| 129–130 | Fixture/admitted-dependency/expected-failure checks precede ordinary quality comparisons |
| 911 | Capitalization is a comment change without added explanation |
| 1019 | Syntax/presentation can change without a new mathematical argument |
| 611 | Extensionality route is unchanged; direct-term versus `simpa` effects remain open, not automatically neutral or superior |
| 1345 | Claude checked the general theorem in the earlier snapshot: stronger reuse candidate; assess applicability, not just existence |
| 1844 | Direct reviewer support for algebraic abstraction/reuse, with a lemma introduced after the earlier snapshot |
| 1291 | Cancellation replaces unfolding; investigate potential robustness effects. Do not prescribe a tradeoff merely because ProofJudge dislikes `simp; rfl` |
| 853–854 | Automation fit is assessable; the cited PR timing compares different revisions and cannot prove this pair faster |
| 639–642 | API/migration and local simplification can coexist. Deprecated aliases prevent inferring that every spelling change was forced |
| 1296 | Anonymous-binder mutation demonstrates classifier sensitivity, not a quality judgment |
| 135, 211, 230, 412, 1912 | Additional exposed comment, automation, accessor and cleanup probes from Claude; investigate individually |

## 7. Record and revision discipline

Follow the shared record contract in [REVIEW-PLAN.md](REVIEW-PLAN.md). Preserve each agent's independent records and the user's actual judgments. Missing fields, access failures and abstentions remain visible. Never convert an agent agreement into a human decision, or a review outcome into `keep_for_training`.

A rubric amendment needs user approval before use. Keep the old rubric/hash and records, document the change, and reassess affected records under the new version. The proposed convention split, materiality rule, optional pair summary and evidence budget are all subject to user approval.

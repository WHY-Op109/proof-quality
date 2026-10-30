# Fast proof-pair screening: round 2 and comparison

2026-10-30. Continues the user-requested direct pass (round 1 by Codex, archived at `fast-screen/archive-initial-pass/FAST-SCREENING.round1.md`). The approved rubric v0.3 (`RUBRIC.md`, sha256 `bc072e19…cdb8`) is applied directly through its dimensions, materiality and support levels. No rubric amendment. Training inclusion is **not decided**.

## Coverage

| | Rows |
| --- | ---: |
| Population (declaration pairs) | 2,379 |
| Your recorded verdicts (21 records, 20 cases; 16 final, 4 deferred) | 20 |
| Codex individual code examination, round 1 | 130 |
| Codex continuation diff examinations (465; **175 were missing from the exports** before reconciliation and are now merged) | 465 |
| Claude Code round-2 individual diff examinations (12 parallel reviewers, `fast-screen/round2/`) | 1,764 |
| **Rows assessed only by an automated rule** | **0** (was 1,939 in the last manifest, 1,764 after reconciliation) |

| Decision | Final better | Earlier better | No material preference | Unresolved | Total |
| --- | ---: | ---: | ---: | ---: | ---: |
| retain | 230 | 5 | – | – | **235** |
| exclude | – | – | 1,960 | 3* | **1,963** |
| unresolved | 1† | – | – | 180 | **181** |

\* Usability-gated rows whose quality question was itself unresolved. † Row 445: your final-better verdict is kept, but the row is withheld because of the statement/proof boundary defect.

**Unresolved ≠ unexamined.** Every unresolved row has an individual reason: 5 are your deferrals, 53 are Codex round-1 abstentions, and 123 are round-2 abstentions. 27 rows carry a discussion flag (5 yours, 22 agent suggestions); see `FAST-DISCUSSION.md`. The 0 automated-only figure means each row was individually read by you or an agent. It does **not** mean it was compiled, profiled, or availability-checked.

Usability gate (kept apart from quality): 6 statement/proof boundary defects, 3 test-fixture paths, and 2 empty proof bodies (1177 final `by`, 1628 earlier `by`; both new in this round). None are exported as retained.

Agent disagreements are kept in `fast-screen/agent-disagreements.jsonl` (40 rows from the 60-row checkpoint where Codex or Claude independent records differ from each other or from the fast outcome; 18 of these are cases you decided). They are not merged into verdicts. Your verdicts override and are never relabelled.

**Calibration gap.** Round 2 was done by model reviewers with a shared brief (`fast-screen/round2/BRIEF.md`). I spot-checked the earlier-better rows, a random sample of Spencer-retained exclusions and of retained rows, and found them consistent with the diffs. Every reason was mechanically checked against its own row's code (packet scratch files collided during the run; no misattributed reason was found). Round 2 has **not** been audited by you.

## Comparison with Spencer's 539 / 2,379

| Spencer \ this pass | retain | exclude | unresolved | total |
| --- | ---: | ---: | ---: | ---: |
| retained | 166 | 253 | 120 | 539 |
| excluded | 69 | 1,710 | 61 | 1,840 |
| total | 235 | 1,963 | 181 | 2,379 |

That gives 1,876 determinate agreements, 322 determinate changes (253 Spencer-retained excluded, 69 Spencer-excluded retained) and 181 abstentions. No precision or recall is claimed, because neither selection is a gold standard.

By Spencer class: of his `construction` rows, 164 are retained, 235 excluded and 120 unresolved. Of his `minor` rows, 67 are retained. His `rename`, `layout`, `style` and `bookkeeping` classes are almost entirely excluded here too (888 of 893).

**Where Spencer's filter succeeds.** It is cheap, deterministic and reproducible. Its rename/layout/style/bookkeeping classes agree almost perfectly with the individual reading, so it reliably removes the large volume of surface edits.

**Where it fails.** (1) `construction` is detected from tactic-name sets, so swapping `linarith`→`ring`, `set`→`let` or `intro`→binder (e.g. 1845, 2170, 1512) looks structural; about 45% (235 of 519) of his `construction` rows were judged surface-level. (2) A one-line swap from a bespoke derivation to a general characterisation lemma uses ordinary tactic words, so it lands in `minor` and is dropped (69 recovered rows, almost all reuse: 1462-style `eq_zero_of_predictable`, 2058 `ExistsUnique.choose_eq_iff`, 1122/1123 Galois correspondence). (3) It assumes the accepted revision is the better one, so it cannot express earlier-better.

**Where this pass succeeds.** It separates reuse from surface edits, records a preference direction (5 earlier-better), keeps your verdicts authoritative, and names the open question for every abstention.

**Where it fails.** (1) **Length bias persists**: the final is shorter in 218 of 230 final-better retains (Spencer 430/539, population 1,638/2,379). Reviewers were told length is not evidence, but reuse almost always shortens the script, so the two are confounded. (2) Most reuse claims are "earlier availability unverified": the final may use a lemma that did not exist for the earlier author (rubric §5). (3) Individual model judgments vary, and a different reviewer would move some exclude↔unresolved borderline rows. (4) The 181 unresolved rows concentrate the cases you care about most (automation versus explicit), so the retained set under-represents them. (5) No compilation, timing or robustness evidence.

Neither approach is shown better overall. The individual pass is more discriminating on reuse and direction. Spencer's filter is cheaper and nearly as good on surface classes.

## Illustrative examples

Reuse recovered from Spencer's exclusions:
- **2058** ExistsUnique.choose_eq_iff replaces manual unpacking. Spencer **exclude** (minor); this pass **retain** / `final_better`, assessor claude-code-round2. Earlier unpacks `(existsUnique ...).choose_spec` and proves both directions by hand; final is exactly the general fact `ExistsUnique.choose_eq_iff`, a clearer use of the general characterisation. [viewer](http://127.0.0.1:8740/#33442%2FtoIcoDiv_eq_iff) · [record](http://127.0.0.1:8740/explanation/2058)
- **1122** Galois correspondence replaces a cardinality sandwich. Spencer **exclude** (minor); this pass **retain** / `final_better`, assessor claude-code-round2. Bespoke cardinality/finrank sandwich argument replaced by reusing the Galois correspondence order isomorphism `intermediateFieldEquivSubgroup`; the result is read off from the general correspondence (earlier availability unverified). [viewer](http://127.0.0.1:8740/#29688%2FIsGaloisGroup.fixingSubgroup_fixedPoints) · [record](http://127.0.0.1:8740/explanation/1122)

Agreement on a material improvement:
- **1462** Predictable-martingale lemma replaces an explicit induction. Spencer **retain** (construction); this pass **retain** / `final_better`, assessor claude-code-round2. Explicit induction with a long `condExp_of_stronglyMeasurable`/`Germ` chain replaced by a direct application of the general `eq_zero_of_predictable`; removes a duplicated argument by reuse (earlier availability unverified). [viewer](http://127.0.0.1:8740/#30997%2FMeasureTheory.Martingale.eq_zero_of_predictable%27) · [record](http://127.0.0.1:8740/explanation/1462)
- **1844** Bernoulli reflection identity (round 1). Spencer **retain** (construction); this pass **retain** / `final_better`, assessor codex. Uses the Bernoulli polynomial reflection identity instead of induction and integration. Existing saved reviewer evidence independently supports this abstraction change. [viewer](http://127.0.0.1:8740/#32364%2FbernoulliFun_eval_one_sub) · [record](http://127.0.0.1:8740/explanation/1844)

Earlier revision better:
- **1936** one bracketing lemma versus a nth_rw re-derivation. Spencer **exclude** (minor); this pass **retain** / `earlier_better`, assessor claude-code-round2. Earlier is one simpa using the bracketing lemma agm_mem_Icc_of_le; final re-derives both bounds with le_antisymm and occurrence-indexed nth_rw on max_self/min_self, longer and more brittle for the same fact (unless the earlier lemma was removed). [viewer](http://127.0.0.1:8740/#32892%2FNNReal.agm_self) · [record](http://127.0.0.1:8740/explanation/1936)
- **1800** explicit key bound versus rpow manipulation. Spencer **retain** (construction); this pass **retain** / `earlier_better`, assessor claude-code-round2. Earlier's calc exposes the key bound `log x ≤ 2√x` then `(2√x)^2 = 4x`; final replaces it with rpow rewriting (`log_le_rpow_div` with ε = 1/2, `nth_rw`, `rpow_add`, `norm_num`, `linarith`) that hides the same estimate in manipulation (earlier lemma availability unverified). [viewer](http://127.0.0.1:8740/#32252%2FChebyshev.psi_le_const_mul_self) · [record](http://127.0.0.1:8740/explanation/1800)
- **1764** pullback stability of monomorphisms versus an element-level proof. Spencer **retain** (construction); this pass **retain** / `earlier_better`, assessor claude-code-round2. Earlier derives injectivity of l from the general fact that monomorphisms are stable under pullback; final hand-rolls an element-level injectivity proof, hiding the general principle (possibly forced by imports, not visible). [viewer](http://127.0.0.1:8740/#32180%2FCategoryTheory.Limits.Types.mono_of_isPushout_of_isPullback) · [record](http://127.0.0.1:8740/explanation/1764)

Spencer-retained but surface-level here:
- **1845** set→let, binder-style haves. Spencer **retain** (construction); this pass **exclude** / `no_material_preference`, assessor claude-code-round2. `set` → `let`, binder-style `have`s, and the `integrable` tactic replaced by explicit `Continuous.intervalIntegrable (by fun_prop)`; same argument, tactic/API adaptation. [viewer](http://127.0.0.1:8740/exclude/#32364%2FbernoulliFun_mul) · [record](http://127.0.0.1:8740/explanation/1845)
- **2170** simp→rw, funext→ext1. Spencer **retain** (construction); this pass **exclude** / `no_material_preference`, assessor claude-code-round2. `simp` -> `rw [inv_zero]`, funext -> ext1, extra `_` argument after signature change. [viewer](http://127.0.0.1:8740/exclude/#33893%2FHeight.mulHeight%E2%82%81_inv) · [record](http://127.0.0.1:8740/explanation/2170)

Unresolved (automation versus explicit):
- **2221** one-line grind versus an explicit case split. Spencer **retain** (construction); this pass **unresolved** / `unresolved`, assessor claude-code-round2. One-line `grind [realize_sentence_iff]` replaced by a 9-line explicit proof that cases on completeness (φ ∈ T or ¬φ ∈ T) and derives a contradiction; is the exposed case analysis an improvement or needless length for a routine fact? [viewer](http://127.0.0.1:8740/unresolved/#34112%2FFirstOrder.Language.Theory.IsComplete.eq_complete_theory) · [record](http://127.0.0.1:8740/explanation/2221)
- **803** dif_pos/dif_neg case analysis versus grind. Spencer **exclude** (minor); this pass **unresolved** / `unresolved`, assessor claude-code-round2. Nine lines of explicit `dif_pos`/`dif_neg` case analysis using disjointness `hST` are replaced by a bare `grind`; the earlier is bookkeeping but does show where disjointness is used, while the final hides it. [viewer](http://127.0.0.1:8740/unresolved/#28241%2FProbabilityTheory.Kernel.iIndepFun.indepFun_finset) · [record](http://127.0.0.1:8740/explanation/803)

## Reformulated research question

The pairs compare **tactic scripts**: the stored text of two historical revisions of one declaration. Three different objects could be meant by "proof quality":

| Object | What a better instance has | What the pair text can show |
| --- | --- | --- |
| Mathematical argument | A more general or more natural route, fewer ad hoc steps, the key idea visible | Only indirectly: the script names lemmas and intermediate claims, but automation can hide the route entirely |
| Lean formalisation | Better reuse of library abstractions, better API fit, less duplicated work, robustness to library change | Partly: named-lemma reuse and structure are visible; availability, robustness and elaboration cost are not |
| Tactic script | Readable and maintainable to a Mathlib reviewer, conforming to conventions of its date | Directly, but convention conformity alone has no quality direction under rubric §4 |

Most retained pairs in this round are justified at the **formalisation** level (reuse of a general theorem, removal of a bespoke derivation), not by a new mathematical argument. Most excluded pairs differ only at the **script** level. The unresolved pool is dominated by cases where the scripts plausibly encode the **same mathematics** and differ in how much of it is explicit.

**Proposed question.** *Given two accepted-quality scripts for the same statement, which differences change the formal argument (what is proved, from which facts, by which reusable abstractions), and which only change its presentation? For changes of the first kind, which direction do informed readers prefer, and why?*

When two scripts appear to encode the same mathematics, a preference can only be justified by consequences beyond the mathematics:

1. **Reader reconstruction.** Can a reader recover the argument? Explicit witnesses favour the reader. Opaque automation does not, unless the omitted step is routine. The user judged aesop for a finiteness side condition neutral (1381), deferred cat_disch (1617) and explicit grind→witness expansion (2218), and preferred one simpler presentation (2124). The data therefore do not support a global rule.
2. **Maintenance.** Will the proof survive library refactors? This needs observed breakage or a documented mechanism, rubric B2. Neither was gathered in this round.
3. **Library fit.** Does the proof route through the abstraction that later proofs will also use? This is the most defensible source-visible criterion and drives most retained rows.
4. **Cost.** Elaboration time and proof-term size need measurement under a stated setup, which was not done here.

If none of these can be shown, "same mathematics, different script" should be **no_material_preference** or **unresolved**, never an automatic preference for the accepted or shorter version.

## Proposed experiment: elaborated proof terms (not implemented)

**Goal.** Separate structural facts about the two proofs from quality claims, and test whether the "same mathematics" judgments above hold at the term level.

**Setup.** For each pair, check out the earlier and final snapshot commits. Build the containing file at each with the toolchain pinned by that commit. Extract the elaborated `ConstantInfo.value` of the declaration, using `instantiateMVars` and no `zeta`/`beta` normalisation beyond what the kernel stored. Record failures (build error, missing declaration, renamed) as a separate outcome, never as a quality signal.

**Structural measurements (descriptive only):**
- Term size: nodes and max depth; number of `let`/`have` binders.
- Constant dependency sets: direct and transitive to depth k. Compare the earlier and final sets with Jaccard, and count new Mathlib lemmas versus local helpers.
- Shared-lemma test: does the final term apply a constant whose own value contains a subterm α-equivalent (up to instance arguments) to a subterm of the earlier term? This is the operational trace of "reuse replaced a bespoke derivation".
- Tactic-generated scaffolding share: fraction of nodes under `Eq.mpr`/`id`/`of_eq_true` and auxiliary `_proof_` constants (automation residue).
- Kernel check time and `#print axioms` for both endpoints, measured separately with repetition. Instability is reported, not hidden.

**Hypotheses that can be tested:**
- H1: pairs judged "same mathematics, presentation only" (excluded) have high dependency-set overlap and no shared-lemma hit. A sizeable number of low-overlap exclusions would indicate that our source-level exclusions hide real changes.
- H2: retained reuse pairs show a shared-lemma hit more often than excluded pairs.
- H3: grind/simp-versus-explicit pairs (the user's deferred class) differ mostly in scaffolding share, not in the mathematical dependency set.

**What would not follow.** Smaller terms, fewer dependencies or faster kernel checking are **not** quality by themselves. They become evidence only for the specific rubric dimension they bear on, such as reuse_modularity for a shared-lemma hit or automation_fit for measured cost, and only together with a human reading of the pair. The experiment calibrates and audits screening decisions. It does not replace them.

**Cost and risk.** Each pair needs two historical builds, about 2×923 PR snapshots. The cache helps only for nearby commits. A pilot on the 60-row checkpoint plus about 40 deferred and agent-flagged cases would test feasibility before any population run.

## Files

- `FAST-SCREENING.jsonl`: one record per row: decision, preference_direction, reason, assessment_method, assessor, dimensions, human verdict, discussion flag, agent_disagreements, usability flags.
- `fast-retained.pairs.jsonl`, `fast-unresolved.pairs.jsonl`, `fast-excluded.pairs.jsonl`: exact original rows, never swapped.
- `fast-navigation.jsonl`: viewer URLs.
- `fast-screen/run.py` (merge policy), `fast-screen/round2/` (brief, packets, outputs), `fast-screen/manifest.json` (input/output hashes).
- Viewer: in the fork, `python3 tools/screening_view/serve.py`.

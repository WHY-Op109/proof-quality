# Fast-pass discussion cases

2026-10-30. These are discussion records, not new human judgments. Viewer: `python3 tools/screening_view/serve.py` from the fork, then open `/discussion/`. Links below assume port 8740.

## Part A — Cases you flagged as difficult (5)

Preserved from the round-1 file without changing their recorded text. Each row stays as you recorded it: deferred cases remain **unresolved**, and 1381 keeps your no-material-preference verdict while still flagged for the meeting.

**Why these are hard to judge.** In every one of them both scripts encode the same mathematics, and they differ in how much of the argument is explicit:
- 1574: `simp only [...]`→`simp [...]` inside a grind witness. This is only simp-set visibility.
- 1617: explicit witness transport→`cat_disch`. The automation is opaque and its search is undocumented for the reader.
- 1587: split_ifs/rw→`by_cases <;> simp`. There is no mathematical difference, so any quality claim has to rest on readability or maintenance evidence that the code alone does not provide.
- 1128: a calc split into more steps. It is a small presentation gain whose materiality is unclear.
- 1381: an explicit finiteness proof→`aesop`. You judged it neutral but kept it as an automation example.

### Original example 1128: Matrix.charpoly_inv
Stable ID: `mathlibpr-v1:cfff294db74d0617ec924bf51f883d2d2e12b850bceb81d016629065b57e34ba`. Spencer: retain; fast: unresolved; direction: unresolved. [Viewer](http://127.0.0.1:8740/unresolved/#29705%2FMatrix.charpoly_inv), subset row 1016.
User endorsed the recommendation: small presentation improvement, no clear meaningful proof-quality difference; outside the default retained set and unresolved for discussion.
**Extracted statement**

```lean
theorem charpoly_inv
    {R : Type u}
    [CommRing R]
    {n G : Type v}
    [DecidableEq n]
    [Fintype n]
    {α β : Type v}
    [DecidableEq α] (A : Matrix n n R) (h : IsUnit A) :
    A⁻¹.charpoly = (-1) ^ Fintype.card n * C (Ring.inverse A.det) * A.charpolyRev :=
```
**Earlier**

```lean
by
  have : Invertible A := h.invertible
  calc
  _ = (scalar n X - C.mapMatrix A⁻¹).det := rfl
  _ = C A⁻¹.det * (C.mapMatrix A * (scalar n X - C.mapMatrix A⁻¹)).det := by
    rw [det_mul, ← RingHom.map_det, ← mul_assoc, ← C_mul, ← det_mul, inv_mul_of_invertible]
    simp
  _ = _ := by
    rw [mul_sub, ← RingHom.map_mul, mul_inv_of_invertible, RingHom.map_one, ← neg_sub, det_neg,
      det_one_sub_mul_comm, charpolyRev, smul_eq_diagonal_mul]
    simp
    ring
```
**Final**

```lean
by
  have : Invertible A := h.invertible
  calc
  _ = (scalar n X - C.mapMatrix A⁻¹).det := rfl
  _ = C (A⁻¹ * A).det * (scalar n X - C.mapMatrix A⁻¹).det := by simp
  _ = C A⁻¹.det * C A.det * (scalar n X - C.mapMatrix A⁻¹).det := by rw [det_mul]; simp
  _ = C A⁻¹.det * (C A.det * (scalar n X - C.mapMatrix A⁻¹).det) := by ac_rfl
  _ = C A⁻¹.det * (C.mapMatrix A * (scalar n X - C.mapMatrix A⁻¹)).det := by simp [RingHom.map_det]
  _ = C A⁻¹.det * (C.mapMatrix A * scalar n X - 1).det := by rw [mul_sub, ← RingHom.map_mul]; simp
  _ = C A⁻¹.det * ((-1) ^ Fintype.card n * (1 - scalar n X * C.mapMatrix A).det) := by
    rw [← neg_sub, det_neg, det_one_sub_mul_comm]
  _ = _ := by simp [charpolyRev, smul_eq_diagonal_mul]; ac_rfl
```

### Original example 1381: EReal.toReal_pos
Stable ID: `mathlibpr-v1:e35160ca4a017815d112dcdeb12a8c738a30f32adbbebd1dbe0c655636392b75`. Spencer: retain; fast: exclude; direction: no_material_preference. [Viewer](http://127.0.0.1:8740/exclude/#30746%2FEReal.toReal_pos), subset row 90.
The user judges replacing the explicit finiteness side-condition proof with aesop to make no meaningful quality difference.
**Extracted statement**

```lean
lemma toReal_pos {x : EReal} (hx : 0 < x) (h'x : x ≠ ⊤) : 0 < x.toReal :=
```
**Earlier**

```lean
by
  lift x to ℝ using ⟨h'x, (ne_of_lt (bot_lt_zero.trans hx)).symm⟩
  simpa using hx
```
**Final**

```lean
by
  lift x to ℝ using by aesop
  simpa using hx
```

### Original example 1574: MeasureTheory.hittingAfter_mono
Stable ID: `mathlibpr-v1:a506bde05bd64048ca18da354671c9063b5c4e51639a0275197551a7f657467e`. Spencer: exclude; fast: unresolved; direction: unresolved. [Viewer](http://127.0.0.1:8740/unresolved/#31541%2FMeasureTheory.hittingAfter_mono), subset row 1419.
Flagged by the user as difficult to judge; await suggestions from the meeting before finalizing.
**Extracted statement**

```lean
lemma hittingAfter_mono
    {Ω β ι : Type*}
    {m : MeasurableSpace Ω}
    [ConditionallyCompleteLinearOrder ι]
    {n i : ι}
    {ω : Ω} (u : ι → Ω → β) (s : Set β) : Monotone (hittingAfter u s) :=
```
**Earlier**

```lean
by
  intro n m hnm ω
  simp only [hittingAfter]
  split_ifs with h_n h_m h_m
  · norm_cast
    gcongr
    exacts [⟨n, by simp only [mem_lowerBounds, Set.mem_setOf_eq, and_imp]; grind⟩, h_m]
  · simp
  · have ⟨t, ht⟩ := h_m
    exact absurd ⟨t, hnm.trans ht.1, ht.2⟩ h_n
  · simp
```
**Final**

```lean
by
  intro n m hnm ω
  simp only [hittingAfter]
  split_ifs with h_n h_m h_m
  · norm_cast
    gcongr
    exacts [⟨n, by simp [mem_lowerBounds]; grind⟩, h_m]
  · simp
  · have ⟨t, ht⟩ := h_m
    exact absurd ⟨t, hnm.trans ht.1, ht.2⟩ h_n
  · simp
```

### Original example 1587: MeasureTheory.stoppedProcess_indicator_comm
Stable ID: `mathlibpr-v1:559d4bb1797ef0ab2e32df2809cd86d2c98de0c6d927c83bef3354aec632c318`. Spencer: retain; fast: unresolved; direction: unresolved. [Viewer](http://127.0.0.1:8740/unresolved/#31557%2FMeasureTheory.stoppedProcess_indicator_comm), subset row 1432.
User sees no mathematical significance to this change and finds proof quality difficult to assess from code alone; explicitly deferred for meeting discussion.
**Extracted statement**

```lean
lemma stoppedProcess_indicator_comm
    {Ω β ι : Type*}
    [Nonempty ι]
    [LinearOrder ι]
    {u : ι → Ω → β}
    {τ σ : Ω → WithTop ι} [Zero β] {s : Set Ω} (i : ι) :
    stoppedProcess (fun i ↦ s.indicator (u i)) τ i = s.indicator (stoppedProcess u τ i) :=
```
**Earlier**

```lean
by
  ext ω
  rw [Set.indicator]
  split_ifs with hω
  · rw [stoppedProcess, Set.indicator_of_mem hω, stoppedProcess]
  · rw [stoppedProcess, Set.indicator_of_notMem hω]
```
**Final**

```lean
by
  ext ω
  by_cases hω : ω ∈ s <;> simp [stoppedProcess, hω]
```

### Original example 1617: ModuleCat.uliftFunctor_map_exact
Stable ID: `mathlibpr-v1:08b37df1a722181f84984f692c9fbfd53a5036b72dba4861882044737061e9a9`. Spencer: retain; fast: unresolved; direction: unresolved. [Viewer](http://127.0.0.1:8740/unresolved/#31706%2FModuleCat.uliftFunctor_map_exact), subset row 1461.
Defer automated versus explicit witness transport for discussion, similar to case 13.
**Extracted statement**

```lean
lemma uliftFunctor_map_exact
    (R : Type u)
    [Ring R] (S : ShortComplex (ModuleCat.{v} R)) (h : S.Exact) :
    (S.map (uliftFunctor R)).Exact :=
```
**Earlier**

```lean
by
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  simp only [uliftFunctor, ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃,
    ShortComplex.map_f, hom_ofHom, LinearMap.coe_comp, LinearEquiv.coe_coe, ShortComplex.map_g]
  intro x
  simp only [Function.comp_apply, Set.mem_range, LinearEquiv.symm_apply_eq, map_zero]
  rw [(CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp h]
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun ⟨y, hy⟩ ↦ ⟨ULift.moduleEquiv y, hy⟩⟩
  use ULift.moduleEquiv.symm (R := R) y
  simpa
```
**Final**

```lean
by
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  dsimp [uliftFunctor]
  intro x
  simp only [Function.comp_apply, Set.mem_range, LinearEquiv.symm_apply_eq, map_zero]
  rw [(CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp h]
  cat_disch
```

## Part B: Your answers to the question sheet

Your answers are recorded verbatim in `fast-screen/human-cluster-answers.jsonl`, kept separate from your per-pair verdicts. Each answer applies only to its own cluster.

| Q | Cluster | Pairs | Your answer | Effect |
| --- | --- | ---: | --- | --- |
| Q1 | automation-hides-routine-steps ([example row 1997](http://127.0.0.1:8740/#r1997)) | 18 | “Q1. unknown, to be discussion(for the one need to be discussion, make a now tab to collect them, this one be labled as automated tactics)” | Kept unresolved; listed for discussion under *Automated tactics* |
| Q2 | sibling-reuse-vs-rederivation ([example row 1359](http://127.0.0.1:8740/#r1359)) | 17 | “Q2. Seems like convention change, no difference, but still worth to saying on the meeting.” | Applied; listed for discussion under *Convention: helper-lemma call vs direct proof* |
| Q3 | automation-hides-main-step ([example row 1344](http://127.0.0.1:8740/#r1344)) | 11 | “Q3. Same as Q1, automated tactics.” | Kept unresolved; listed for discussion under *Automated tactics* |
| Q4 | api-interface-adaptation ([example row 2144](http://127.0.0.1:8740/#r2144)) | 10 | “Q4. Same.” | Applied |
| Q5 | different-valid-route ([example row 396](http://127.0.0.1:8740/#r396)) | 8 | “Q5. worth to discussion, based on different mathematician taste.” | Kept unresolved; listed for discussion under *Mathematical taste: different valid routes* |
| Q6 | explicit-names-key-content ([example row 1405](http://127.0.0.1:8740/#r1405)) | 8 | “Q6. Same for grind, this still worth to discussion, mathlib's convention to the use of grind and when prefer grind or other automated tactics, needed to be check online and worth to mention during discussion.” | Kept unresolved; listed for discussion under *Automated tactics: Mathlib convention for grind* |
| Q7 | explicit-replaces-automation-no-insight ([example row 2220](http://127.0.0.1:8740/#r2220)) | 6 | “Q7, Same as Q6. Worth to discussion, and you categorize it.” | Kept unresolved; listed for discussion under *Automated tactics: Mathlib convention for grind* |
| Q8 | singleton-1957 ([example row 1957](http://127.0.0.1:8740/#r1957)) | 1 | “Q8 discussion” | Kept unresolved; listed for discussion under *Automated tactics: Mathlib convention for grind* |

Not a question: row(s) 2313 cannot be judged from the stored pair (the argument moved into a helper lemma that the pair does not contain).

## Part C: Meeting agenda by topic

This matches the viewer tab *For discussion*, where you can filter by topic.

### Automated tactics (33 pairs)

Includes your earlier meeting cases 1381 (`aesop`), 1574 (simp set inside `grind`), 1587 (`by_cases <;> simp`) and 1617 (`cat_disch`). Q1 covers routine steps folded into automation, and Q3 covers automation that hides the main step.

Rows: [64](http://127.0.0.1:8740/#r64), [357](http://127.0.0.1:8740/#r357), [450](http://127.0.0.1:8740/#r450), [452](http://127.0.0.1:8740/#r452), [567](http://127.0.0.1:8740/#r567), [727](http://127.0.0.1:8740/#r727), [924](http://127.0.0.1:8740/#r924), [1046](http://127.0.0.1:8740/#r1046), [1056](http://127.0.0.1:8740/#r1056), [1132](http://127.0.0.1:8740/#r1132), [1167](http://127.0.0.1:8740/#r1167), [1243](http://127.0.0.1:8740/#r1243), [1342](http://127.0.0.1:8740/#r1342), [1344](http://127.0.0.1:8740/#r1344), [1381](http://127.0.0.1:8740/#r1381), [1503](http://127.0.0.1:8740/#r1503), [1558](http://127.0.0.1:8740/#r1558), [1574](http://127.0.0.1:8740/#r1574), [1587](http://127.0.0.1:8740/#r1587), [1617](http://127.0.0.1:8740/#r1617), [1638](http://127.0.0.1:8740/#r1638), [1664](http://127.0.0.1:8740/#r1664), [1762](http://127.0.0.1:8740/#r1762), [1804](http://127.0.0.1:8740/#r1804), [1814](http://127.0.0.1:8740/#r1814), [1955](http://127.0.0.1:8740/#r1955), [1962](http://127.0.0.1:8740/#r1962), [1997](http://127.0.0.1:8740/#r1997), [2017](http://127.0.0.1:8740/#r2017), [2020](http://127.0.0.1:8740/#r2020), [2021](http://127.0.0.1:8740/#r2021), [2048](http://127.0.0.1:8740/#r2048), [2260](http://127.0.0.1:8740/#r2260).

Example, row 1344 `SimplexCategoryGenRel.lt_and_eval_eq_eval_add_one_of_mem_isAdmissible` (Q3):

```diff
--- earlier
+++ final
@@ -1,4 +1,2 @@
 by
-  simp_rw [List.mem_iff_getElem] at hj
-  rcases hj with ⟨k, hk, rfl⟩
-  exact ⟨hL.getElem_lt, hL.simplicialEvalσ_succ_getElem⟩+  grind [List.mem_iff_getElem]```

Example, row 1997 `Metric.maximalSeparatedSet_subset` (Q1):

```diff
--- earlier
+++ final
@@ -1,5 +1 @@
-by
-  by_cases h : packingNumber ε A ≠ ⊤
-  · simp only [maximalSeparatedSet, ne_eq, h, not_false_eq_true, ↓reduceDIte]
-    exact (exists_set_encard_eq_packingNumber h).choose_spec.1
-  · simp only [maximalSeparatedSet, h, dite_false, Set.empty_subset]+by grind [maximalSeparatedSet]```

### Convention: helper-lemma call vs direct proof (17 pairs)

You judged these to be a convention change with no difference (pending confirmation), but still worth mentioning at the meeting.

Rows: [106](http://127.0.0.1:8740/#r106), [107](http://127.0.0.1:8740/#r107), [390](http://127.0.0.1:8740/#r390), [397](http://127.0.0.1:8740/#r397), [774](http://127.0.0.1:8740/#r774), [1079](http://127.0.0.1:8740/#r1079), [1095](http://127.0.0.1:8740/#r1095), [1355](http://127.0.0.1:8740/#r1355), [1359](http://127.0.0.1:8740/#r1359), [1532](http://127.0.0.1:8740/#r1532), [1675](http://127.0.0.1:8740/#r1675), [1676](http://127.0.0.1:8740/#r1676), [1980](http://127.0.0.1:8740/#r1980), [2031](http://127.0.0.1:8740/#r2031), [2195](http://127.0.0.1:8740/#r2195), [2284](http://127.0.0.1:8740/#r2284), [2319](http://127.0.0.1:8740/#r2319).

Example, row 1359 `Real.log_prod` (Q2):

```diff
--- earlier
+++ final
@@ -1 +1,3 @@
-log_prod' hf+by
+  rw [← prod_map_toList, log_list_prod (by simp_all)]
+  simp```

### Automated tactics: Mathlib convention for grind (15 pairs)

**Online check (2026-10-30).** I found no official Mathlib style rule on when to prefer `grind` over `simp`, other automation or explicit steps.
- The closest discussion is an informal Zulip thread on `@[grind]` *annotations*, not on using `grind` to close goals. It suggests passing one-off lemmas explicitly (`grind [lemma]`) instead of adding global annotations: [Zulip: Good practices for grind annotation](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Good.20practices.20for.20grind.20annotation.html).
- The Lean reference documents how `grind` works (E-matching, congruence closure, case splits), but it gives no style guidance: [Lean reference: the grind tactic](https://lean-lang.org/doc/reference/latest/The--grind--tactic/Bigger-Examples/).
- A 2025 Mathlib tooling talk still lists `grind` as automation that is "in progress": [LeanTogether 2025 slides](https://scanner-eg.ipv4.math.uni-bonn.de/people/rothgang/slides_LeanTogether2025_mathlib_tooling.pdf).
- The data contain one concrete reason a revision moved *away* from `grind`. In row [740](http://127.0.0.1:8740/#r740), the final proof's comment cites heartbeat variance, so the motivation was performance stability, not readability.

**Question for the meeting.** Does current Mathlib review practice treat `grind` as preferred, neutral or discouraged for closing goals? The Mathlib style guide and the #mathlib4 Zulip stream are where to confirm this.

Rows: [398](http://127.0.0.1:8740/#r398), [500](http://127.0.0.1:8740/#r500), [501](http://127.0.0.1:8740/#r501), [740](http://127.0.0.1:8740/#r740), [875](http://127.0.0.1:8740/#r875), [1102](http://127.0.0.1:8740/#r1102), [1124](http://127.0.0.1:8740/#r1124), [1165](http://127.0.0.1:8740/#r1165), [1252](http://127.0.0.1:8740/#r1252), [1405](http://127.0.0.1:8740/#r1405), [1957](http://127.0.0.1:8740/#r1957), [2218](http://127.0.0.1:8740/#r2218), [2219](http://127.0.0.1:8740/#r2219), [2220](http://127.0.0.1:8740/#r2220), [2377](http://127.0.0.1:8740/#r2377).

Example, row 1405 `Equiv.eq_or_eq_of_swap_apply_ne_self` (Q6):

```diff
--- earlier
+++ final
@@ -1,2 +1,3 @@
 by
-  grind+  contrapose! h
+  exact swap_apply_of_ne_of_ne h.1 h.2```

Example, row 1957 `LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero` (Q8):

```diff
--- earlier
+++ final
@@ -7,15 +7,13 @@
     simp [← s.sum_filter_add_sum_filter_not (p := fun i ↦ 0 ≤ c i) (f := fun i ↦ c i • v i)]
   have hx₀ : x = 0 := by
-    rw [← hB.le_zero_iff, B.toQuadraticMap_apply]
-    nth_rw 1 [hx]
-    rw [hc, hy]
-    simp only [map_sum, map_smul, neg_smul, Finset.sum_neg_distrib, map_neg, LinearMap.coe_sum,
-      Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Left.neg_nonpos_iff]
+    suffices B x y ≤ 0 by simpa [hc, ← hB.le_zero_iff, B.toQuadraticMap_apply]
+    suffices 0 ≤ ∑ x ∈ s with c x < 0, ∑ i ∈ s with 0 ≤ c i, c x * (c i * (B (v i)) (v x)) by
+      simpa [hx, hy, map_neg, Finset.mul_sum]
     refine Finset.sum_nonneg fun i hi ↦ Finset.sum_nonneg fun j hj ↦ ?_
     rcases eq_or_ne i j with rfl | hij
     · rw [← mul_assoc]
       exact mul_nonneg (mul_self_nonneg _) (hB.nonneg _)
-    · exact mul_nonneg_iff.mpr <|
-        Or.inr ⟨by grind, mul_nonpos_iff.mpr <| Or.inl ⟨by grind, hn hij.symm⟩⟩
+    · specialize hn hij.symm
+      grind [mul_nonneg_iff, mul_nonpos_iff]
   replace hx : ∑ i ∈ s with 0 ≤ c i, c i * f (v i) = 0 := by
     rw [hx₀] at hx
@@ -30,6 +28,5 @@
     grind
   replace hy : ∑ i ∈ s with c i < 0, c i * f (v i) = 0 := by
-    rw [hx₀] at hc
-    rw [← hc] at hy
+    rw [← hc, hx₀] at hy
     simpa using (congr(f $hy)).symm
   replace hy (i : ι) (hi : i ∈ s) : 0 ≤ c i := by
```

Example, row 2220 `Equiv.Perm.support_swap_mul_eq` (Q7):

```diff
--- earlier
+++ final
@@ -1,2 +1,11 @@
 by
-  grind [notMem_support, mul_apply, ne_and_ne_of_swap_mul_apply_ne_self]+  by_cases hx : f x = x
+  · simp [hx, sdiff_singleton_eq_erase, notMem_support.mpr hx, erase_eq_of_notMem]
+  ext z
+  by_cases hzx : z = x
+  · simp [hzx]
+  by_cases hzf : z = f x
+  · simp [hzf, hx, h, swap_apply_of_ne_of_ne]
+  by_cases hzfx : f z = x
+  · simp [Ne.symm hzx, hzx, Ne.symm hzf, hzfx]
+  · simp [hzx, hzfx, f.injective.ne hzx, swap_apply_of_ne_of_ne]```

### Mathematical taste: different valid routes (8 pairs)

Your note: the preference depends on the mathematician's taste.

Rows: [396](http://127.0.0.1:8740/#r396), [692](http://127.0.0.1:8740/#r692), [1458](http://127.0.0.1:8740/#r1458), [1619](http://127.0.0.1:8740/#r1619), [1803](http://127.0.0.1:8740/#r1803), [2091](http://127.0.0.1:8740/#r2091), [2205](http://127.0.0.1:8740/#r2205), [2243](http://127.0.0.1:8740/#r2243).

Example, row 396 `RingHom.finitePresentation_respectsIso` (Q5):

```diff
--- earlier
+++ final
@@ -1,4 +1,2 @@
-by
-  refine finitePresentation_stableUnderComposition.respectsIso (fun {R S} _ _ e ↦ ?_)
-  algebraize [e.toRingHom]
-  apply Algebra.FinitePresentation.equiv <| .ofRingEquiv (congrFun rfl)+  finitePresentation_stableUnderComposition.respectsIso
+    fun e ↦ .of_surjective _ e.surjective <| by simpa using Submodule.fg_bot```

### Presentation detail: calc granularity (1 pair)

Your earlier deferral: a small presentation gain, but no clear meaningful difference.

Rows: [1128](http://127.0.0.1:8740/#r1128).

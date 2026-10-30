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

## Part B: Your question sheet (8 questions covering 79 unresolved pairs)

Agents screened every pair twice and adjudicated each disagreement. These are the only open questions left. Each one is asked once, on a representative pair, and your answer would be applied to that cluster only, after you see which rows it changes. A one-word answer is enough: **final / earlier / same / depends**. Open each representative in the viewer under *Hard cases*.

| # | Question | Pairs | Representative |
| --- | --- | ---: | --- |
| 1 | When the final folds routine steps (definitional case splits, membership or category bookkeeping, intermediate arithmetic/calc steps) into automation or a shorter chain while the key fact stays the same or remains cited, is there no difference? | 18 | [row 1997](http://127.0.0.1:8740/#r1997) |
| 2 | When the earlier proof is a short appeal to a sibling or helper lemma and the final proves the statement directly (plausibly because the helper was removed, moved below the import level, or is now derived from this lemma), is the earlier proof better or is there no difference? | 17 | [row 1359](http://127.0.0.1:8740/#r1359) |
| 3 | When automation (grind, aesop, nlinarith or a golfed term) replaces the explicit proof of the lemma's main step, so the decisive lemma, hypothesis or witness is no longer visible, is the earlier proof better? | 11 | [row 1344](http://127.0.0.1:8740/#r1344) |
| 4 | When the argument is unchanged and the final only switches the interface used to carry it out (erw vs simp, unfolding a definition vs a transport/API lemma, coe_* vs generic map_* lemmas), apparently following an upstream definition or API change, is there no difference? | 10 | [row 2144](http://127.0.0.1:8740/#r2144) |
| 5 | When both proofs are valid and the final takes a different route of similar length (more general lemma vs direct lemma, abstract characterisation vs elementary argument, structural vs direct computation), is there no difference? | 8 | [row 396](http://127.0.0.1:8740/#r396) |
| 6 | When the final replaces automation or a terse chain with explicit steps that name the key lemma, certificate or intermediate bound (or add a roadmap comment) for the same argument, is the final better? | 8 | [row 1405](http://127.0.0.1:8740/#r1405) |
| 7 | When the final replaces short automation with a longer explicit proof that adds no mathematical insight (case bashes, rewrite or witness plumbing), is the earlier proof better? | 6 | [row 2220](http://127.0.0.1:8740/#r2220) |
| 8 | The final states the reduced goals via suffices but replaces the explicit sign-case argument with grind; is the final better overall? | 1 | [row 1957](http://127.0.0.1:8740/#r1957) |

The cluster *automation hides routine steps* includes the same kinds of change as your deferred cases 1574, 1617 and 1587. Your answer would **not** be applied to those three automatically.

Not a question: row(s) 2313 cannot be judged from the stored pair: Blocked by data: row 86's final body appears truncated (only the conv_lhs line); row 2313's change moves the argument into a `proof_body` lemma not visible in the pair.

### Q1. automation-hides-routine-steps: row 1997, Metric.maximalSeparatedSet_subset
When the final folds routine steps (definitional case splits, membership or category bookkeeping, intermediate arithmetic/calc steps) into automation or a shorter chain while the key fact stays the same or remains cited, is there no difference?

All pairs in this cluster: 64, 357, 452, 567, 727, 1046, 1132, 1167, 1243, 1342, 1503, 1638, 1664, 1955, 1997, 2020, 2021, 2260.

```diff
--- earlier
+++ final
@@ -1,5 +1 @@
-by
-  by_cases h : packingNumber ε A ≠ ⊤
-  · simp only [maximalSeparatedSet, ne_eq, h, not_false_eq_true, ↓reduceDIte]
-    exact (exists_set_encard_eq_packingNumber h).choose_spec.1
-  · simp only [maximalSeparatedSet, h, dite_false, Set.empty_subset]+by grind [maximalSeparatedSet]```

### Q2. sibling-reuse-vs-rederivation: row 1359, Real.log_prod
When the earlier proof is a short appeal to a sibling or helper lemma and the final proves the statement directly (plausibly because the helper was removed, moved below the import level, or is now derived from this lemma), is the earlier proof better or is there no difference?

All pairs in this cluster: 106, 107, 390, 397, 774, 1079, 1095, 1355, 1359, 1532, 1675, 1676, 1980, 2031, 2195, 2284, 2319.

```diff
--- earlier
+++ final
@@ -1 +1,3 @@
-log_prod' hf+by
+  rw [← prod_map_toList, log_list_prod (by simp_all)]
+  simp```

### Q3. automation-hides-main-step: row 1344, SimplexCategoryGenRel.lt_and_eval_eq_eval_add_one_of_mem_isAdmissible
When automation (grind, aesop, nlinarith or a golfed term) replaces the explicit proof of the lemma's main step, so the decisive lemma, hypothesis or witness is no longer visible, is the earlier proof better?

All pairs in this cluster: 450, 924, 1056, 1344, 1558, 1762, 1804, 1814, 1962, 2017, 2048.

```diff
--- earlier
+++ final
@@ -1,4 +1,2 @@
 by
-  simp_rw [List.mem_iff_getElem] at hj
-  rcases hj with ⟨k, hk, rfl⟩
-  exact ⟨hL.getElem_lt, hL.simplicialEvalσ_succ_getElem⟩+  grind [List.mem_iff_getElem]```

### Q4. api-interface-adaptation: row 2144, RCLike.sqrt_of_nonneg
When the argument is unchanged and the final only switches the interface used to carry it out (erw vs simp, unfolding a definition vs a transport/API lemma, coe_* vs generic map_* lemmas), apparently following an upstream definition or API change, is there no difference?

All pairs in this cluster: 9, 41, 634, 979, 1186, 1255, 1448, 2144, 2145, 2304.

```diff
--- earlier
+++ final
@@ -1,6 +1,5 @@
 by
   obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := 𝕜)
-  · simp [h, sqrt]
-  apply_fun complexRingEquiv h
-  rw [← sqrt_complexRingEquiv h, Complex.sqrt_of_nonneg (by grind)]
+  · simp [h, sqrt_eq_ite]
+  rw [sqrt_eq_ite, dif_pos h, RingEquiv.symm_apply_eq, Complex.sqrt_of_nonneg (by simpa)]
   simp```

### Q5. different-valid-route: row 396, RingHom.finitePresentation_respectsIso
When both proofs are valid and the final takes a different route of similar length (more general lemma vs direct lemma, abstract characterisation vs elementary argument, structural vs direct computation), is there no difference?

All pairs in this cluster: 396, 692, 1458, 1619, 1803, 2091, 2205, 2243.

```diff
--- earlier
+++ final
@@ -1,4 +1,2 @@
-by
-  refine finitePresentation_stableUnderComposition.respectsIso (fun {R S} _ _ e ↦ ?_)
-  algebraize [e.toRingHom]
-  apply Algebra.FinitePresentation.equiv <| .ofRingEquiv (congrFun rfl)+  finitePresentation_stableUnderComposition.respectsIso
+    fun e ↦ .of_surjective _ e.surjective <| by simpa using Submodule.fg_bot```

### Q6. explicit-names-key-content: row 1405, Equiv.eq_or_eq_of_swap_apply_ne_self
When the final replaces automation or a terse chain with explicit steps that name the key lemma, certificate or intermediate bound (or add a roadmap comment) for the same argument, is the final better?

All pairs in this cluster: 398, 501, 875, 1124, 1165, 1252, 1405, 2377.

```diff
--- earlier
+++ final
@@ -1,2 +1,3 @@
 by
-  grind+  contrapose! h
+  exact swap_apply_of_ne_of_ne h.1 h.2```

### Q7. explicit-replaces-automation-no-insight: row 2220, Equiv.Perm.support_swap_mul_eq
When the final replaces short automation with a longer explicit proof that adds no mathematical insight (case bashes, rewrite or witness plumbing), is the earlier proof better?

All pairs in this cluster: 500, 740, 1102, 2218, 2219, 2220.

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

### Q8. singleton-1957: row 1957, LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero
The final states the reduced goals via suffices but replaces the explicit sign-case argument with grind; is the final better overall?

All pairs in this cluster: 1957.

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

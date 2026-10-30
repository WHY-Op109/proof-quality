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

## Part B — Agent suggestions (not flagged by you; 22)

The agents decided routine cases themselves. The cases below are ones where an agent judged the quality direction genuinely ambiguous and a decision from you would settle a whole class of cases. All of them remain **unresolved**. They are distinct from rows that were never individually examined (there are none after round 2; see FAST-SCREENING.md).

### Grouped questions for you

**Automation versus explicit proof**
- Rows 721: When grind is replaced by an explicit simp only list that names the logical facts (or vice versa) for a trivial set identity, is that a quality difference or convention?
- Rows 739: When the final replaces short automation (grind) for routine finset-membership side goals with substantially longer explicit bookkeeping terms that carry no mathematical content, should that count as earlier_better (noise) or no difference (as with aesop in 1381)?
- Rows 740: Should replacing short automation (`grind`/`simp`) with long explicit rewrite chains, done for performance/heartbeat stability, count as earlier_better (readability), final_better (robustness), or no preference?
- Rows 803: When a block of explicit case bookkeeping (dite unfolding + a disjointness fact) is replaced by `grind`, should that count as no difference, final better (less noise), or earlier better (hides where the hypothesis is used)?
- Rows 1056: When a proof keeps its intermediate `have` statements but replaces each one's explicit lemma-chain justification with `grind`, is that no material difference (the skeleton carries the mathematics), or is the loss of named lemmas a quality loss?
- Rows 1124: When a closing `grind` is replaced by an explicit `linear_combination` certificate for the same algebraic identity, should that count as final_better (explicit, robust certificate) or as no material difference?
- Rows 1252: When grind is given exactly the lemmas used, is an explicit case-by-case application of those lemmas a material clarity gain, or convention (same class as 1265, 1448)?
- Rows 1283: If the final uses a mathematically more direct argument (membership equality, no dimension-one step) but hides it inside simp_all, while the earlier spells out a longer explicit argument, which do you prefer?
- Rows 1327: When an explicit rewrite chain that spells out a small case analysis (here: empty finset gives zero sum) is replaced by one `simp +contextual`, is the earlier proof better, or is this just automation convention?
- Rows 1333: For a tiny logic fact with a readable explicit term proof, should replacing it by grind with definition hints count as earlier_better, final_better, or no difference?
- Rows 1355: When a direct application of a named library lemma is replaced by `grind` over a characterisation plus a lemma list, should the direct reuse be considered better (earlier_better), or is this neutral if the old lemma was deprecated?
- Rows 1405: When a one-line `grind` is replaced by a two-line explicit proof that names the key lemma (contrapositive of `swap_apply_of_ne_of_ne`), do you count the explicit version as better?
- Rows 1619: When a readable two-direction ext proof is compressed into simp + dense term mode while reusing a new lemma (inner_map_eq_flip), does the reuse outweigh the readability loss?
- Rows 1762: When grind/aesop replaces an explicit proof of the *main* step of a characterisation (here: h₁ gives injectivity, h₂ gives surjectivity of the comparison map), should the explicit earlier proof count as better, or is this the same no-difference automation case as a side condition (cf. 1381)?
- Rows 1962: When grind/simp replaces a short explicit witness-based argument (here: covering Spec by basic opens), should this be treated as no difference, final better (less bookkeeping), or earlier better (hides the witness)?
- Rows 2221: When a one-line `grind` is replaced by an explicit proof that exposes a simple case split (here φ ∈ T or ¬φ ∈ T), do you consider the explicit version better, or is this no material difference?
- Rows 2243: When a structural proof composing library preservation lemmas (with explicit @-instance plumbing) is replaced by a short direct computation of the measure of univ, which do you prefer?

**Reuse direction / dependency reversal**
- Rows 2031: When a final proof replaces a one-line appeal to a sibling lemma with a direct proof, most likely because the dependency was inverted so the sibling is now derived from this one, should that count as earlier_better (lost reuse) or no material preference?

**Other**
- Rows 106, 1095, 2218: Earlier Codex pass example; no specific question recorded.
- Rows 1916: User verdicts treat comment placement/removal as no difference (947, 1063, 2250). Does *adding* substantive proof-strategy comments that narrate the main idea of a nontrivial proof (as here) count as a material explanatory improvement, or also no difference?

A single answer to the first group would also calibrate the many round-2 rows marked unresolved for automation reasons. Those rows are not listed here individually; filter `FAST-SCREENING.jsonl` with `decision=unresolved` and `rule=R8`.

### Original example 106: IsCyclotomicExtension.subsingleton_iff
Stable ID: `mathlibpr-v1:c8506abf5d631ee27481d2a189ea30a16876203e789cdb1385abbea754289b0f`. Spencer: retain; fast: unresolved; direction: unresolved. [Viewer](http://127.0.0.1:8740/unresolved/#25114%2FIsCyclotomicExtension.subsingleton_iff), subset row 100.
Longer final script inspected as an expansion countercheck. The change concerns explicit steps, implementation/API compatibility, automation or local presentation; no clear quality direction established without further context.
**Extracted statement**

```lean
theorem subsingleton_iff
    (S T : Set ℕ)
    (A : Type u)
    (B : Type v)
    (K : Type w)
    (L : Type z)
    [CommRing A]
    [CommRing B]
    [Algebra A B]
    [Field K]
    [Field L]
    [Algebra K L] [Subsingleton B] :
    IsCyclotomicExtension S A B ↔ S ⊆ {0, 1} :=
```
**Earlier**

```lean
by
  rw [eq_sdiff_zero, subsingleton_iff_aux _ _ _ (by simp), ← subset_singleton_iff_eq,
    diff_singleton_subset_iff]
```
**Final**

```lean
by
  have : Subsingleton (Subalgebra A B) := inferInstance
  refine ⟨fun ⟨hprim, _⟩ ↦ ?_, fun hS ↦ ?_⟩
  · refine subset_pair_iff.mpr fun s hs ↦ or_iff_not_imp_left.mpr fun hs' ↦ ?_
    obtain ⟨ζ, hζ⟩ := hprim hs hs'
    exact mod_cast hζ.unique (IsPrimitiveRoot.of_subsingleton ζ)
  · refine ⟨fun {s} hs hs' ↦ ?_, fun x ↦ by convert (mem_top (R := A) : x ∈ ⊤)⟩
    · have : s = 1 := (subset_pair_iff.mp hS s hs).resolve_left hs'
      exact ⟨0, this ▸ IsPrimitiveRoot.of_subsingleton 0⟩
```

### Original example 721: Function.mulSupport_prod_mk
Spencer: retain (construction); fast: **unresolved**. Assessor: claude-code-round2. [Viewer](http://127.0.0.1:8740/unresolved/#27670%2FFunction.mulSupport_prod_mk).

Opaque `grind` replaced by an explicit `simp only` list naming the logical facts (`not_and_or`, `Prod.mk_eq_one`); the set identity is trivial either way, so the value of the explicit list is unclear.

```diff
--- earlier
+++ final
@@ -1 +1,2 @@
-  Set.ext fun x => by grind+  Set.ext fun x => by
+    simp only [mulSupport, not_and_or, mem_union, mem_setOf_eq, Prod.mk_eq_one, Ne]```

### Original example 739: CategoryTheory.Limits.colimitLimitToLimitColimit_injective
Spencer: retain (construction); fast: **unresolved**. Assessor: claude-code-round2. [Viewer](http://127.0.0.1:8740/unresolved/#27818%2FCategoryTheory.Limits.colimitLimitToLimitColimit_injective).

Final replaces six `by grind` finset-membership side goals with long hand-written `Finset.mem_union.mpr (Or.inl ...)` terms including empty `simp only`; pure bookkeeping, much noisier, but the explicit form may be more robust than grind.

```diff
--- earlier
+++ final
@@ -28,17 +28,31 @@
     -- morphisms `f j` and `g j`.
     let O : Finset K := Finset.univ.image k ∪ {kx, ky}
-    have kxO : kx ∈ O := by grind
-    have kyO : ky ∈ O := by grind
-    have kjO : ∀ j, k j ∈ O := by grind
+    have kxO : kx ∈ O := Finset.mem_union.mpr (Or.inr (by simp))
+    have kyO : ky ∈ O := Finset.mem_union.mpr (Or.inr (by simp))
+    have kjO : ∀ j, k j ∈ O := fun j => Finset.mem_union.mpr (Or.inl (by simp))
     let H : Finset (Σ' (X Y : K) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
       (Finset.univ.image fun j : J =>
-          ⟨kx, k j, kxO, by grind, f j⟩) ∪
-        Finset.univ.image fun j : J => ⟨ky, k j, kyO, by grind, g j⟩
+          ⟨kx, k j, kxO, Finset.mem_union.mpr (Or.inl (by simp)), f j⟩) ∪
+        Finset.univ.image fun j : J => ⟨ky, k j, kyO, Finset.mem_union.mpr (Or.inl (by simp)), g j⟩
     obtain ⟨S, T, W⟩ := IsFiltered.sup_exists O H
     have fH : ∀ j, (⟨kx, k j, kxO, kjO j, f j⟩ : Σ' (X Y : K) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) ∈ H :=
-      fun j => by grind
+      fun j =>
+      Finset.mem_union.mpr
+        (Or.inl
+          (by
+            simp only [true_and, Finset.mem_univ,
+              Finset.mem_image]
+            refine ⟨j, ?_⟩
+            simp only ))
     have gH :
       ∀ j, (⟨ky, k j, kyO, kjO j, g j⟩ : Σ' (X Y : K) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) ∈ H :=
-      fun j => by grind
+      fun j =>
+      Finset.mem_union.mpr
+        (Or.inr
+          (by
+            simp only [true_and, Finset.mem_univ,
+              Finset.mem_image]
+            refine ⟨j, ?_⟩
+            simp only))
     -- Our goal is now an equation between equivalence classes of representatives of a colimit,
     -- and so it suffices to show those representative become equal somewhere, in particular at `S`.
```

### Original example 740: CategoryTheory.Limits.colimitLimitToLimitColimit_surjective
Spencer: retain (construction); fast: **unresolved**. Assessor: claude-code-round2. [Viewer](http://127.0.0.1:8740/unresolved/#27818%2FCategoryTheory.Limits.colimitLimitToLimitColimit_surjective).

Three `by grind` membership side goals replaced by explicit witness terms and long `rw [PSigma.mk.injEq, heq_eq_eq, ...]` chains, justified by a comment about heartbeat variance; is performance stability worth replacing a one-word discharge with an unreadable rewrite chain?

```diff
--- earlier
+++ final
@@ -70,5 +70,7 @@
       Finset.mem_union.mpr
         (Or.inl
-          (Finset.mem_biUnion.mpr ⟨j, by grind⟩))
+          (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j,
+            Finset.mem_biUnion.mpr ⟨j', Finset.mem_univ j',
+              Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩⟩⟩))
     have k'O : k' ∈ O := Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
     let H : Finset (Σ' (X Y : K) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
@@ -87,8 +89,20 @@
       · exact Finset.mem_biUnion.mpr ⟨j₃, Finset.mem_univ _,
           Finset.mem_biUnion.mpr ⟨j₄, Finset.mem_univ _,
-            Finset.mem_biUnion.mpr ⟨f', Finset.mem_univ _, by grind⟩⟩⟩
+            Finset.mem_biUnion.mpr ⟨f', Finset.mem_univ _, by
+              -- This works by `simp`, but has very high variation in heartbeats.
+              rw [Finset.mem_insert, PSigma.mk.injEq, heq_eq_eq, PSigma.mk.injEq, heq_eq_eq,
+                PSigma.mk.injEq, heq_eq_eq, PSigma.mk.injEq, heq_eq_eq, eq_self, true_and, eq_self,
+                true_and, eq_self, true_and, eq_self, true_and, Finset.mem_singleton, eq_self,
+                or_true]
+              trivial⟩⟩⟩
       · exact Finset.mem_biUnion.mpr ⟨j₁, Finset.mem_univ _,
           Finset.mem_biUnion.mpr ⟨j₂, Finset.mem_univ _,
-            Finset.mem_biUnion.mpr ⟨f, Finset.mem_univ _, by grind⟩⟩⟩
+            Finset.mem_biUnion.mpr ⟨f, Finset.mem_univ _, by
+              -- This works by `simp`, but has very high variation in heartbeats.
+              rw [Finset.mem_insert, PSigma.mk.injEq, heq_eq_eq, PSigma.mk.injEq, heq_eq_eq,
+                PSigma.mk.injEq, heq_eq_eq, PSigma.mk.injEq, heq_eq_eq, eq_self, true_and, eq_self,
+                true_and, eq_self, true_and, eq_self, true_and, Finset.mem_singleton, eq_self,
+                true_or]
+              trivial⟩⟩⟩
     clear_value i
     clear s' i' H kfO k'O O
```

### Original example 803: ProbabilityTheory.Kernel.iIndepFun.indepFun_finset
Spencer: exclude (minor); fast: **unresolved**. Assessor: claude-code-round2. [Viewer](http://127.0.0.1:8740/unresolved/#28241%2FProbabilityTheory.Kernel.iIndepFun.indepFun_finset).

Nine lines of explicit `dif_pos`/`dif_neg` case analysis using disjointness `hST` are replaced by a bare `grind`; the earlier is bookkeeping but does show where disjointness is used, while the final hides it.

```diff
--- earlier
+++ final
@@ -62,17 +62,8 @@
     simp_rw [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Finset.mem_union]
     constructor <;> intro h
-    · intro i hi
-      rcases hi with hiS | hiT
-      · replace h := h.1 i hiS
-        simp_rw [sets_s', sets_t', dif_pos hiS, dif_neg (Finset.disjoint_left.mp hST hiS)]
-        simp only [sets_s'] at h
-        exact ⟨by rwa [dif_pos hiS] at h, Set.mem_univ _⟩
-      · replace h := h.2 i hiT
-        simp_rw [sets_s', sets_t', dif_pos hiT, dif_neg (Finset.disjoint_right.mp hST hiT)]
-        simp only [sets_t'] at h
-        exact ⟨Set.mem_univ _, by rwa [dif_pos hiT] at h⟩
+    · grind
     · exact ⟨fun i hi => (h i (Or.inl hi)).1, fun i hi => (h i (Or.inr hi)).2⟩
   have h_meas_inter : ∀ i ∈ S ∪ T, MeasurableSet (sets_s' i ∩ sets_t' i) := by
-    intros i hi_mem
+    intro i hi_mem
     rw [Finset.mem_union] at hi_mem
     rcases hi_mem with hi_mem | hi_mem
```

### Original example 1056: Finset.exists_subset_or_subset_of_two_mul_lt_card
Spencer: retain (construction); fast: **unresolved**. Assessor: claude-code-round2. [Viewer](http://127.0.0.1:8740/unresolved/#29461%2FFinset.exists_subset_or_subset_of_two_mul_lt_card).

The intermediate `have` statements (`#(X ∩ (Y \ X)) = 0`, `#(X ∪ Y) = #X + #(Y \ X)`) and the case split are kept. Their explicit justifications (`inter_sdiff_self`, `card_union_add_card_inter`, `union_sdiff_self_eq_union`, `sdiff_subset`) are all replaced by `grind`. The skeleton still shows the mathematics, but the cited set-theoretic facts disappear.

```diff
--- earlier
+++ final
@@ -1,8 +1,6 @@
 by
-  have h₁ : #(X ∩ (Y \ X)) = 0 := Finset.card_eq_zero.mpr (Finset.inter_sdiff_self X Y)
-  have h₂ : #(X ∪ Y) = #X + #(Y \ X) := by
-    rw [← card_union_add_card_inter X (Y \ X), Finset.union_sdiff_self_eq_union, h₁, Nat.add_zero]
-  rw [h₂, Nat.two_mul] at hXY
-  obtain h | h : n < #X ∨ n < #(Y \ X) := by contrapose! hXY; cutsat
-  · exact ⟨X, h, Or.inl (Finset.Subset.refl X)⟩
-  · exact ⟨Y \ X, h, Or.inr sdiff_subset⟩+  have h₁ : #(X ∩ (Y \ X)) = 0 := Finset.card_eq_zero.mpr (by grind)
+  have h₂ : #(X ∪ Y) = #X + #(Y \ X) := by grind
+  obtain h | h : n < #X ∨ n < #(Y \ X) := by cutsat
+  · exact ⟨X, by grind⟩
+  · exact ⟨Y \ X, by grind⟩```

### Original example 1095: ArchimedeanClass.mk_le_mk_iff_denselyOrdered
Stable ID: `mathlibpr-v1:83276970687bb334978d7bf0110742f6879db645ab6f78ae6df81ded0353c9cc`. Spencer: retain; fast: unresolved; direction: unresolved. [Viewer](http://127.0.0.1:8740/unresolved/#29611%2FArchimedeanClass.mk_le_mk_iff_denselyOrdered), subset row 987.
Longer final script inspected as an expansion countercheck. The change concerns explicit steps, implementation/API compatibility, automation or local presentation; no clear quality direction established without further context.
**Extracted statement**

```lean
theorem mk_le_mk_iff_denselyOrdered
    {R S : Type*}
    [LinearOrder R]
    [LinearOrder S]
    [CommRing R]
    [IsStrictOrderedRing R] [Ring S] [IsStrictOrderedRing S]
    [DenselyOrdered R] [Archimedean R] {x y : S} (f : R →+* S) (hf : StrictMono f) :
    mk x ≤ mk y ↔ ∃ q : R, 0 < f q ∧ f q * |y| ≤ |x| :=
```
**Earlier**

```lean
by
  obtain hy | rfl | hy := lt_trichotomy y 0
  · simpa using mk_le_mk_iff_denselyOrdered' f hf (neg_pos.2 hy)
  · have : ∃ q, 0 < f q := ⟨1, by simp⟩
    simpa
  · exact mk_le_mk_iff_denselyOrdered' f hf hy
```
**Final**

```lean
by
  have H {q} : 0 < f q ↔ 0 < q := by simpa using hf.lt_iff_lt (a := 0)
  constructor
  · rintro ⟨(_ | n), hn⟩
    · simp_all [exists_zero_lt]
    · obtain ⟨q, hq₀, hq⟩ := exists_nsmul_lt_of_pos (one_pos (α := R)) (n + 1)
      refine ⟨q, H.2 hq₀, le_of_mul_le_mul_left ?_ n.cast_add_one_pos⟩
      simpa [← mul_assoc] using mul_le_mul (hf hq).le hn (abs_nonneg y) (by simp)
  · rintro ⟨q, hq₀, hq⟩
    have hq₀' := H.1 hq₀
    obtain ⟨n, hn⟩ := exists_lt_nsmul hq₀' 1
    refine ⟨n, le_of_mul_le_mul_left ?_ hq₀⟩
    have h : 0 ≤ f (n • q) := by
      rw [← f.map_zero]
      exact hf.monotone (nsmul_nonneg hq₀'.le n)
    simpa [mul_comm, mul_assoc] using mul_le_mul (hf hn).le hq (mul_nonneg hq₀.le (abs_nonneg y)) h
```

### Original example 1124: imo2008_q4
Spencer: exclude (minor); fast: **unresolved**. Assessor: claude-code-round2. [Viewer](http://127.0.0.1:8740/unresolved/#29692%2Fimo2008_q4).

A closing `grind` becomes an explicit `linear_combination` certificate, a `grind` becomes the term `(H₁ 1 zero_lt_one).ne'`, and `simp [field, ...]` becomes `simp only`. Open question: does the explicit algebraic certificate count as a material gain over `grind`?

```diff
--- earlier
+++ final
@@ -8,8 +8,8 @@
       rw [h w hw, h x hx, h (y ^ 2) (pow_pos hy 2), h (z ^ 2) (pow_pos hz 2)]
       field_simp
-      grind
+      linear_combination - (z ^ 2 + y ^ 2) * (w ^ 2 + x ^ 2) * (w * x + y * z) * hprod
   -- proof that the only solutions are f(x) = x or f(x) = 1/x
   intro H₂
-  have h₀ : f 1 ≠ 0 := by specialize H₁ 1 zero_lt_one; grind
+  have h₀ : f 1 ≠ 0 := (H₁ 1 zero_lt_one).ne'
   have h₁ : f 1 = 1 := by
     specialize H₂ 1 1 1 1 zero_lt_one zero_lt_one zero_lt_one
@@ -41,5 +41,5 @@
     grind [abs_of_pos]
   -- f(ab) = 1/ab → a^4 = 1 → a = 1 → f(a) = 1/a → false
-  · simp [field, hab₂] at H₂
+  · simp only [hab₂, field] at H₂
     obtain ha₂ := abs_eq_one_of_pow_eq_one a 4 (show 4 ≠ 0 by simp) (by grind)
     grind [abs_of_pos]```

### Original example 1252: mul_lt_mul_iff_of_le_of_le
Spencer: retain (construction); fast: **unresolved**. Assessor: claude-code-round2. [Viewer](http://127.0.0.1:8740/unresolved/#30280%2Fmul_lt_mul_iff_of_le_of_le).

grind with three named lemmas replaced by an explicit refine/rcases that shows which lemma closes which case; both expose the same mathematics.

```diff
--- earlier
+++ final
@@ -1,2 +1,5 @@
 by
-  grind [lt_or_lt_of_mul_lt_mul, mul_lt_mul_of_lt_of_le, mul_lt_mul_of_le_of_lt]+  refine ⟨lt_or_lt_of_mul_lt_mul, fun h => ?_⟩
+  rcases h with ha' | hb'
+  · exact mul_lt_mul_of_lt_of_le ha' hb
+  · exact mul_lt_mul_of_le_of_lt ha hb'```

### Original example 1283: IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
Spencer: retain (construction); fast: **unresolved**. Assessor: claude-code-round2. [Viewer](http://127.0.0.1:8740/unresolved/#30404%2FIsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation).

Earlier gives an explicit argument (one inclusion via the valuation iff, then `prime_le_prime_iff_eq` using dimension one); final closes with `simp_all` using `valuation_lt_one_iff_mem` and `Ideal.ext_iff`, apparently a more direct membership argument that does not need dimension one, but hidden inside automation.

```diff
--- earlier
+++ final
@@ -1,8 +1,3 @@
 by
-  rw [Valuation.isEquiv_iff_val_lt_one] at hpq
-  rw [HeightOneSpectrum.ext_iff, ← Ring.DimensionLeOne.prime_le_prime_iff_eq p.ne_bot]
-  intro x hx
-  specialize hpq (x := algebraMap R K x)
-  rw [valuation_lt_one_iff_dvd p x, valuation_lt_one_iff_dvd q x, Ideal.dvd_span_singleton,
-    Ideal.dvd_span_singleton] at hpq
-  exact hpq.mp hx+  simp_all [Valuation.isEquiv_iff_val_lt_one, HeightOneSpectrum.ext_iff, Ideal.ext_iff,
+    ← valuation_lt_one_iff_mem (K := K)]```

### Original example 1327: Finset.expect_eq_zero_iff_of_nonpos
Spencer: retain (construction); fast: **unresolved**. Assessor: claude-code-round2. [Viewer](http://127.0.0.1:8740/unresolved/#30502%2FFinset.expect_eq_zero_iff_of_nonpos).

Explicit rw chain (expect as card⁻¹ • sum, smul_eq_zero, card_eq_zero, empty sum) replaced by `simp +contextual [expect, sum_eq_zero_iff_of_nonpos hf]`. Open question: the earlier spells out the empty-finset case split that the final hides; is that exposition worth the length?

```diff
--- earlier
+++ final
@@ -1,5 +1,2 @@
 by
-  rw [←sum_eq_zero_iff_of_nonpos hf, expect, smul_eq_zero, or_iff_right_iff_imp,
-      inv_eq_zero, Nat.cast_eq_zero, card_eq_zero]
-  intro hs
-  rw [hs, sum_empty]+  simp +contextual [expect, sum_eq_zero_iff_of_nonpos hf]```

### Original example 1333: reflexive_iff_subrelation_eq
Spencer: retain (construction); fast: **unresolved**. Assessor: claude-code-round2. [Viewer](http://127.0.0.1:8740/unresolved/#30557%2Freflexive_iff_subrelation_eq).

A short explicit term proof (reflexive gives subrelation of eq and conversely) replaced by grind [Reflexive, Subrelation]; the term exposes the two-line argument, grind is shorter but opaque.

```diff
--- earlier
+++ final
@@ -1 +1,2 @@
-  ⟨fun hr _ _ heq ↦ heq ▸ hr _, fun hsub _ ↦ hsub rfl⟩+by
+  grind [Reflexive, Subrelation]```

### Original example 1355: SimpleGraph.IsAcyclic.isAcyclic_sup_fromEdgeSet_of_not_reachable
Spencer: retain (construction); fast: **unresolved**. Assessor: claude-code-round2. [Viewer](http://127.0.0.1:8740/unresolved/#30640%2FSimpleGraph.IsAcyclic.isAcyclic_sup_fromEdgeSet_of_not_reachable).

A one-line application of `isAcyclic_sup_fromEdgeSet_of_notMem_reachabilitySet` becomes `grind` over a bridge characterisation and five lemmas. Open question: if the earlier lemma still exists, is direct reuse better than a grind proof that exposes the bridge argument?

```diff
--- earlier
+++ final
@@ -1 +1,3 @@
-  isAcyclic_sup_fromEdgeSet_of_notMem_reachabilitySet hnreach hacyc+by
+  grind [isAcyclic_iff_forall_edge_isBridge, IsBridge.sup_fromEdgeSet_of_not_reachable,
+    edgeSet_sup, IsBridge.sup_fromEdgeSet_of_not_reachable_of_isBridge, edgeSet_fromEdgeSet]```

### Original example 1405: Equiv.eq_or_eq_of_swap_apply_ne_self
Spencer: retain (construction); fast: **unresolved**. Assessor: claude-code-round2. [Viewer](http://127.0.0.1:8740/unresolved/#30909%2FEquiv.eq_or_eq_of_swap_apply_ne_self).

One-line `grind` replaced by `contrapose! h; exact swap_apply_of_ne_of_ne h.1 h.2`, which names the key fact (swap fixes points other than a, b). Open question: is naming the key lemma a material clarity gain over grind?

```diff
--- earlier
+++ final
@@ -1,2 +1,3 @@
 by
-  grind+  contrapose! h
+  exact swap_apply_of_ne_of_ne h.1 h.2```

### Original example 1619: Submodule.map_orthogonal
Spencer: retain (construction); fast: **unresolved**. Assessor: claude-code-round2. [Viewer](http://127.0.0.1:8740/unresolved/#31728%2FSubmodule.map_orthogonal).

Earlier is a readable two-direction ext proof; final uses `inner_map_eq_flip` in a simp set and a dense term-mode closing. Open: is the compressed term proof less explanatory, outweighing the lemma reuse?

```diff
--- earlier
+++ final
@@ -1,10 +1,4 @@
 by
-  ext x
-  simp only [mem_map, mem_orthogonal, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
-  constructor
-  · rintro ⟨y, hy, rfl⟩ x hx
-    simp [hy x hx]
-  · rintro h
-    refine ⟨f.symm x, ?_, by simp⟩
-    intro y hy
-    rw [← show f.symm (f y) = y by simp, LinearIsometryEquiv.inner_map_map, h y hy]+  simp only [Submodule.ext_iff, mem_map, mem_orthogonal, forall_exists_index, and_imp,
+    forall_apply_eq_imp_iff₂, LinearIsometryEquiv.inner_map_eq_flip]
+  exact fun x ↦ ⟨fun ⟨y, hy⟩ z hz ↦ by simp [← hy.2, hy.1 _ hz], fun h ↦ ⟨_, h, by simp⟩⟩```

### Original example 1762: CategoryTheory.Limits.Types.isPullback_iff
Spencer: retain (construction); fast: **unresolved**. Assessor: claude-code-round2. [Viewer](http://127.0.0.1:8740/unresolved/#32180%2FCategoryTheory.Limits.Types.isPullback_iff).

Earlier proves the comparison map φ is bijective explicitly: injectivity from h₁ (via Subtype/Prod ext) and surjectivity from h₂; final closes it with `grind [Function.Bijective, Function.Injective, Function.Surjective]`. This is the core step of the pullback characterisation, so the automation hides which hypothesis gives which half; unclear whether that is a material loss of explanation or acceptable brevity.

```diff
--- earlier
+++ final
@@ -7,11 +7,5 @@
     have hφ : IsIso φ := by
       rw [isIso_iff_bijective]
-      constructor
-      · intro x₁ y₁ h
-        rw [Subtype.ext_iff, Prod.ext_iff] at h
-        exact h₁ _ _ h
-      · rintro ⟨⟨x₂, x₃⟩, h⟩
-        obtain ⟨x₁, rfl, rfl⟩ := h₂ x₂ x₃ h
-        exact ⟨x₁, rfl⟩
+      grind [Function.Bijective, Function.Injective, Function.Surjective]
     exact ⟨⟨w⟩, ⟨IsLimit.ofIsoLimit ((Types.pullbackLimitCone r b).isLimit)
       (PullbackCone.ext (asIso φ)).symm⟩⟩```

### Original example 1916: Function.Surjective.card_le_card_add_one_iff
Spencer: exclude (minor); fast: **unresolved**. Assessor: claude-code-round2. [Viewer](http://127.0.0.1:8740/unresolved/#32772%2FFunction.Surjective.card_le_card_add_one_iff).

Final adds step-by-step proof-strategy comments (pick inverse g; 'g misses at most one element'; where collisions occur) and hoists `replace hf` so both directions share it instead of repeating `Function.surjInv_eq hf`. The code change is minor; the open question is whether such added strategy comments are a material explanatory gain.

```diff
--- earlier
+++ final
@@ -2,19 +2,24 @@
   rcases isEmpty_or_nonempty α
   · simp
+  -- pick an inverse `g` to `f`
   let g := Function.surjInv hf
+  -- the "decreases cardinality by at most one condition" becomes "`g` misses at most one element"
   rw [← Set.ncard_range_of_injective (Function.injective_surjInv hf),
     ← Set.ncard_add_ncard_compl (Set.range g), add_le_add_iff_left]
+  replace hf : ∀ b, f (g b) = b := Function.surjInv_eq hf
   refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
   · rw [Set.ncard_le_one_iff_subset_singleton] at h
+    -- if `g` misses at most one element, let `x` be this element
     obtain ⟨x, hx⟩ := h
-    replace hf : ∀ b, f (g b) = b := Function.surjInv_eq hf
     simp only [Set.subset_def, Set.mem_compl_iff] at hx
+    -- we show that the only possible collision is between `x` and `g (f x)`
     suffices ∀ a b : α, f a = f b → a ≠ b → a = x ∨ a = g (f x) by grind
     intro a b
     by_cases ha : a ∈ Set.range g <;> by_cases hb : b ∈ Set.range g <;> grind
-  · rw [Set.ncard_le_one]
+  · -- we must show that any two elements `a` and `b` missed by `g` are equal
+    rw [Set.ncard_le_one]
     simp only [Set.mem_compl_iff, Set.mem_range, not_exists, ← ne_eq]
     intro a ha b hb
+    -- there is a collision between `a` and `g (f a)`, and between `b` and `g (f b)`
     simpa [(ha (f b)).symm] using congrArg (a ∈ ·) (h a (g (f a)) b (g (f b))
-      (Function.surjInv_eq hf (f a)).symm (Function.surjInv_eq hf (f b)).symm
-      (ha (f a)).symm (hb (f b)).symm)+      (hf (f a)).symm (hf (f b)).symm (ha (f a)).symm (hb (f b)).symm)```

### Original example 1962: Algebra.Smooth.exists_span_eq_top_isStandardSmooth
Spencer: retain (construction); fast: **unresolved**. Assessor: claude-code-round2. [Viewer](http://127.0.0.1:8740/unresolved/#32924%2FAlgebra.Smooth.exists_span_eq_top_isStandardSmooth).

Earlier shows the basic opens cover Spec S by exhibiting p for each prime and applying hf₁, and the membership part via hf₂; final uses simp with ext lemmas plus two grind calls. Open: automation versus explicit covering argument.

```diff
--- earlier
+++ final
@@ -1,11 +1,5 @@
 by
   choose f hf₁ hf₂ using IsSmoothAt.exists_notMem_isStandardSmooth R (S := S)
-  refine ⟨Set.range (fun p : PrimeSpectrum S ↦ f p.asIdeal), ?_, ?_⟩
-  · rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff, _root_.eq_top_iff]
-    rintro p -
-    rw [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.coe_mk, Set.mem_iUnion]
-    use p
-    apply hf₁
-  · simp_rw [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
-    intro p
-    apply hf₂+  refine ⟨Set.range (fun p : PrimeSpectrum S ↦ f p.asIdeal), ?_, by grind⟩
+  simp [← PrimeSpectrum.iSup_basicOpen_eq_top_iff, TopologicalSpace.Opens.ext_iff, Set.ext_iff]
+  grind```

### Original example 2031: IsScalarTower.algebraMap_eq
Spencer: exclude (minor); fast: **unresolved**. Assessor: claude-code-round2. [Viewer](http://127.0.0.1:8740/unresolved/#33353%2FIsScalarTower.algebraMap_eq).

Earlier is a one-line appeal to `algebraMap_comp_algebraMap`; final proves the identity directly by `RingHom.ext` and smul rewriting. Open question: is this a dependency inversion (the sibling lemma now derived from this one), making it neutral, or a loss of reuse?

```diff
--- earlier
+++ final
@@ -1 +1,2 @@
-  (algebraMap_comp_algebraMap _ _ _).symm+  RingHom.ext fun x => by
+    simp_rw [RingHom.comp_apply, Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]```

### Original example 2218: Finset.memberSubfamily_union_nonMemberSubfamily
Stable ID: `mathlibpr-v1:390efec9292e7f6bdada74f26093780ca7556e8ebcabf177312520ca6df430aa`. Spencer: retain; fast: unresolved; direction: unresolved. [Viewer](http://127.0.0.1:8740/unresolved/#34112%2FFinset.memberSubfamily_union_nonMemberSubfamily), subset row 2011.
A grind proof becomes explicit membership witnesses; user has not settled a general automation-versus-explicit preference.
**Extracted statement**

```lean
theorem memberSubfamily_union_nonMemberSubfamily
    {α : Type*}
    [DecidableEq α]
    {s : Finset α} (a : α) (𝒜 : Finset (Finset α)) :
    𝒜.memberSubfamily a ∪ 𝒜.nonMemberSubfamily a = 𝒜.image fun s => s.erase a :=
```
**Earlier**

```lean
by
  ext s
  grind [memberSubfamily, erase_ne_self]
```
**Final**

```lean
by
  ext s
  simp only [mem_union, mem_memberSubfamily, mem_nonMemberSubfamily, mem_image]
  constructor
  · rintro (h | h)
    · exact ⟨_, h.1, erase_insert h.2⟩
    · exact ⟨_, h.1, erase_eq_of_notMem h.2⟩
  · rintro ⟨s, hs, rfl⟩
    by_cases ha : a ∈ s
    · exact Or.inl ⟨by rwa [insert_erase ha], notMem_erase _ _⟩
    · exact Or.inr ⟨by rwa [erase_eq_of_notMem ha], notMem_erase _ _⟩
```

### Original example 2221: FirstOrder.Language.Theory.IsComplete.eq_complete_theory
Spencer: retain (construction); fast: **unresolved**. Assessor: claude-code-round2. [Viewer](http://127.0.0.1:8740/unresolved/#34112%2FFirstOrder.Language.Theory.IsComplete.eq_complete_theory).

One-line `grind [realize_sentence_iff]` replaced by a 9-line explicit proof that cases on completeness (φ ∈ T or ¬φ ∈ T) and derives a contradiction; is the exposed case analysis an improvement or needless length for a routine fact?

```diff
--- earlier
+++ final
@@ -1,2 +1,10 @@
 by
-  grind [realize_sentence_iff]+  ext φ
+  simp only [Set.mem_setOf_eq, L.mem_completeTheory]
+  refine ⟨fun h_models => h_models.realize_sentence M, fun h_realize => ?_⟩
+  cases h.2 φ with
+  | inl hT => exact hT
+  | inr hT =>
+      have : M ⊨ φ.not := hT.realize_sentence M
+      rw [Sentence.realize_not] at this
+      contradiction```

### Original example 2243: MeasureTheory.isProbabilityMeasure_bind
Spencer: exclude (minor); fast: **unresolved**. Assessor: claude-code-round2. [Viewer](http://127.0.0.1:8740/unresolved/#34239%2FMeasureTheory.isProbabilityMeasure_bind).

Structural proof (bind = join of map, each preserves probability measures via isProbabilityMeasure_join) replaced by a direct computation of (μ.bind f) univ via bind_apply and lintegral_eq_const; open question: is the structural composition or the direct computation the better argument?

```diff
--- earlier
+++ final
@@ -1,4 +1,4 @@
 by
-  simp only [Measure.bind]
-  apply @isProbabilityMeasure_join _ _ _ (Measure.isProbabilityMeasure_map hf₀)
-    ((ae_map_iff hf₀ ProbabilityMeasure.measurableSet_isProbabilityMeasure).mpr hf₁)+  simp only [isProbabilityMeasure_iff, MeasurableSet.univ, Measure.bind_apply _ hf₀]
+  simp_rw [isProbabilityMeasure_iff] at hf₁
+  exact lintegral_eq_const hf₁```

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteKernelAdaptedSupply

/-!
# The handle-digit flip supply and the repair theorem

The kernel-adapted reduction left two per-stage data: the coordinate derivation family and the
handle-digit repair (`SqStageHandleDigitRepairSupply`).  This file reduces the repair to a
single sharply isolated per-slot statement, the **handle-digit flip supply**: for every handle
slot, one depth-`k-1` correction whose literal core-plus-handle shift word is trivial, whose
mod-`2^(k+1)` cyclotomic digit at that slot is nontrivial, and whose digits at every other
handle slot are trivial.

The reduction is pure bookkeeping over the raw correction group: the literal shift is a
homomorphism (`rawDepthShiftHom`), the digit at a fixed slot is a homomorphism, and the digit
group over depth-`k-1` corrections is elementary of order two by sharpness of the character
filtration, so one simultaneous product of flips cancels every bad digit at once
(`stageFlip_deep_cancel`).  Consequently the forward presentation capstone consumes exactly a
coordinate derivation family and a flip supply at every stage
(`nonempty_orientedEquiv_oddDegree_of_family_of_flipSupply`).
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## Generic helpers -/

/-- A finite product with a unique possibly nontrivial factor evaluates to that factor. -/
private theorem stageFlip_list_prod_single
    {H I : Type*} [Monoid H] (l : List I) (j : I) (f : I → H)
    (hj : j ∈ l) (hnodup : l.Nodup)
    (hf : ∀ i ∈ l, i ≠ j → f i = 1) :
    (l.map f).prod = f j := by
  induction l with
  | nil => simp at hj
  | cons i l ih =>
      have hnd := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hj with hij | hj
      · subst i
        have htail : (l.map f).prod = 1 := by
          apply List.prod_eq_one
          intro x hx
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
          exact hf b (List.mem_cons_of_mem _ hb) (fun hbj ↦ hnd.1 (hbj ▸ hb))
        simp [htail]
      · have hij : i ≠ j := by
          intro hEq
          exact hnd.1 (hEq ▸ hj)
        rw [List.map_cons, List.prod_cons, hf i (by simp) hij, one_mul,
          ih hj hnd.2 (fun b hb hbj ↦ hf b (List.mem_cons_of_mem _ hb) hbj)]

/-- Two `2`-adic values with sharp digit at level `n` multiply to one with a trivial level-`n`
digit.  This is the arithmetic heart of the simultaneous digit repair: the digit group of the
depth-`k-1` modification space is elementary of order two. -/
private theorem stageFlip_deep_cancel {n : ℕ} (hn : 1 ≤ n) {u w : ℤ_[2]}
    (hu : (2 : ℤ_[2]) ^ n ∣ u - 1) (hu' : ¬ (2 : ℤ_[2]) ^ (n + 1) ∣ u - 1)
    (hw : (2 : ℤ_[2]) ^ n ∣ w - 1) (hw' : ¬ (2 : ℤ_[2]) ^ (n + 1) ∣ w - 1) :
    (2 : ℤ_[2]) ^ (n + 1) ∣ u * w - 1 := by
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hw
  have ha2 : ¬ (2 : ℤ_[2]) ∣ a := by
    rintro ⟨e, rfl⟩
    exact hu' ⟨e, by rw [ha, pow_succ]; ring⟩
  have hb2 : ¬ (2 : ℤ_[2]) ∣ b := by
    rintro ⟨e, rfl⟩
    exact hw' ⟨e, by rw [hb, pow_succ]; ring⟩
  have hab : (2 : ℤ_[2]) ∣ a + b := by
    rw [show (2 : ℤ_[2]) = 2 ^ 1 by ring, two_pow_dvd_iff] at ha2 hb2 ⊢
    rw [map_add]
    revert ha2 hb2
    generalize PadicInt.toZModPow 1 a = x
    generalize PadicInt.toZModPow 1 b = y
    revert x y
    decide
  obtain ⟨e, he⟩ := hab
  refine ⟨e + 2 ^ (n - 1) * (a * b), ?_⟩
  have hu2 : u = 1 + 2 ^ n * a := by linear_combination ha
  have hw2 : w = 1 + 2 ^ n * b := by linear_combination hb
  have hpow : (2 : ℤ_[2]) ^ n * 2 ^ n = 2 ^ (n + 1) * 2 ^ (n - 1) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [hu2, hw2]
  linear_combination (2 : ℤ_[2]) ^ n * he + (a * b) * hpow

/-- Evaluation of a raw depth correction at one generator slot, as a homomorphism. -/
private def stageFlipEval {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {h k : ℕ} (t : Fin (SqCore.sqRank h)) :
    RawDepthCorrection G h k →* levelQuot G (k + 1) where
  toFun V := V.correction t
  map_one' := rfl
  map_mul' _ _ := rfl

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-! ## The flip supply -/

/-- **The handle-digit flip supply.**  For each handle slot, a depth-`k-1` correction whose
literal core-plus-handle shift word is trivial, whose next-precision cyclotomic digit at that
slot is nontrivial, and whose digits at all other handle slots are trivial.  Core-slot digits
are unconstrained: the sharp core rows are repaired downstream by the existing moves.  This
is the exact remaining content of `SqStageHandleDigitRepairSupply`. -/
def SqStageHandleDigitFlipSupply {h k : ℕ} (T : SqCyclotomicStageTuple K h k) : Prop :=
  (∀ j : Fin h,
    ∃ V : RawDepthCorrection (maxProPQuotient 2 (GalK K)) h k,
      sqCoreHandleDbarWord
          (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
          V.correction = 1 ∧
      chiLevel (chiCycKTwo (K := K)) (k + 1)
          (V.correction (SqCore.sqHandleIdxU j)) ≠ 1 ∧
      (∀ l : Fin h, l ≠ j → chiLevel (chiCycKTwo (K := K)) (k + 1)
          (V.correction (SqCore.sqHandleIdxU l)) = 1) ∧
      (∀ l : Fin h, chiLevel (chiCycKTwo (K := K)) (k + 1)
          (V.correction (SqCore.sqHandleIdxV l)) = 1)) ∧
  (∀ j : Fin h,
    ∃ V : RawDepthCorrection (maxProPQuotient 2 (GalK K)) h k,
      sqCoreHandleDbarWord
          (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
          V.correction = 1 ∧
      chiLevel (chiCycKTwo (K := K)) (k + 1)
          (V.correction (SqCore.sqHandleIdxV j)) ≠ 1 ∧
      (∀ l : Fin h, l ≠ j → chiLevel (chiCycKTwo (K := K)) (k + 1)
          (V.correction (SqCore.sqHandleIdxV l)) = 1) ∧
      (∀ l : Fin h, chiLevel (chiCycKTwo (K := K)) (k + 1)
          (V.correction (SqCore.sqHandleIdxU l)) = 1))

/-- At handle count zero the flip supply is vacuous. -/
theorem sqStageHandleDigitFlipSupply_of_rank_zero {k : ℕ}
    (T : SqCyclotomicStageTuple K 0 k) :
    SqStageHandleDigitFlipSupply T :=
  ⟨fun j ↦ j.elim0, fun j ↦ j.elim0⟩

/-! ## Digit arithmetic over the depth-`k-1` modification space -/

omit [FiniteDimensional ℚ_[2] ↥K] [T2Space (GalK K)] in
/-- The mod-`2^(k+1)` cyclotomic digit of a depth-`k-1` class through an ambient witness. -/
private theorem stageFlip_digit_eq {k : ℕ}
    {q : levelQuot (maxProPQuotient 2 (GalK K)) (k + 1)}
    {u : maxProPQuotient 2 (GalK K)}
    (hu : levelMk (maxProPQuotient 2 (GalK K)) (k + 1) u = q) :
    chiLevel (chiCycKTwo (K := K)) (k + 1) q =
      Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom (chiCycKTwo (K := K) u) := by
  rw [← hu, chiLevel_levelMk]

omit [FiniteDimensional ℚ_[2] ↥K] [T2Space (GalK K)] in
/-- The sharp congruence of the digit of a depth-`k-1` witness. -/
private theorem stageFlip_witness_dvd {k : ℕ} (hk : 3 ≤ k)
    {u : maxProPQuotient 2 (GalK K)}
    (hu : u ∈ twoCentralSeries (maxProPQuotient 2 (GalK K)) (k - 1)) :
    (2 : ℤ_[2]) ^ k ∣ ((chiCycKTwo (K := K) u : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  have hd := dvd_chi_of_mem_twoCentralSeries (chiCycKTwo (K := K))
    (by omega : 2 ≤ k - 1) hu
  rwa [show k - 1 + 1 = k by omega] at hd

omit [FiniteDimensional ℚ_[2] ↥K] [T2Space (GalK K)] in
/-- A nontrivial digit certifies the sharp non-divisibility of the witness. -/
private theorem stageFlip_witness_not_dvd {k : ℕ}
    {q : levelQuot (maxProPQuotient 2 (GalK K)) (k + 1)}
    {u : maxProPQuotient 2 (GalK K)}
    (hu : levelMk (maxProPQuotient 2 (GalK K)) (k + 1) u = q)
    (hq : chiLevel (chiCycKTwo (K := K)) (k + 1) q ≠ 1) :
    ¬ (2 : ℤ_[2]) ^ (k + 1) ∣ ((chiCycKTwo (K := K) u : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  intro hdvd
  apply hq
  rw [stageFlip_digit_eq hu]
  exact MonoidHom.mem_ker.mp (mem_ker_units_toZModPow_iff.mpr (by exact_mod_cast hdvd))

omit [FiniteDimensional ℚ_[2] ↥K] [T2Space (GalK K)] in
/-- **The order-two digit cancellation.**  Two depth-`k-1` classes with nontrivial
next-precision cyclotomic digits have digits multiplying to one. -/
private theorem stageFlip_digit_cancel {k : ℕ} (hk : 3 ≤ k)
    {q q' : levelQuot (maxProPQuotient 2 (GalK K)) (k + 1)}
    (hq : q ∈ lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1))
    (hq' : q' ∈ lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1))
    (hne : chiLevel (chiCycKTwo (K := K)) (k + 1) q ≠ 1)
    (hne' : chiLevel (chiCycKTwo (K := K)) (k + 1) q' ≠ 1) :
    chiLevel (chiCycKTwo (K := K)) (k + 1) q *
      chiLevel (chiCycKTwo (K := K)) (k + 1) q' = 1 := by
  obtain ⟨u, humem, hu⟩ := hq
  obtain ⟨u', humem', hu'⟩ := hq'
  have hcancel := stageFlip_deep_cancel (n := k) (by omega)
    (stageFlip_witness_dvd hk humem) (stageFlip_witness_not_dvd hu hne)
    (stageFlip_witness_dvd hk humem') (stageFlip_witness_not_dvd hu' hne')
  rw [stageFlip_digit_eq hu, stageFlip_digit_eq hu', ← map_mul]
  refine MonoidHom.mem_ker.mp (mem_ker_units_toZModPow_iff.mpr ?_)
  have hval : ((chiCycKTwo (K := K) u * chiCycKTwo (K := K) u' : ℤ_[2]ˣ) : ℤ_[2]) =
      ((chiCycKTwo (K := K) u : ℤ_[2]ˣ) : ℤ_[2]) *
        ((chiCycKTwo (K := K) u' : ℤ_[2]ˣ) : ℤ_[2]) := by
    push_cast
    ring
  rw [hval]
  exact_mod_cast hcancel

/-! ## The repair from the flips -/

/-- **The handle-digit repair from the flip supply.**  Any defect-killing depth correction is
multiplied by one simultaneous product of per-slot flips: the literal shift word is unchanged
because every flip has trivial shift word, and each bad handle digit is cancelled by exactly
one flip through the order-two digit arithmetic. -/
theorem sqStageHandleDigitRepairSupply_of_flipSupply {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} (hk : 3 ≤ k)
    (Hflip : SqStageHandleDigitFlipSupply T) :
    SqStageHandleDigitRepairSupply T := by
  classical
  intro c hdepth hkill
  obtain ⟨HU, HV⟩ := Hflip
  choose VU hVUword hVUdiag hVUoffU hVUoffV using HU
  choose VV hVVword hVVdiag hVVoffV hVVoffU using HV
  set base : Fin (SqCore.sqRank h) →
      levelQuot (maxProPQuotient 2 (GalK K)) (k + 1) :=
    fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i) with hbase
  -- the per-slot flips, applied only where the current digit is bad
  set DU : Fin h → RawDepthCorrection (maxProPQuotient 2 (GalK K)) h k :=
    fun j ↦ if chiLevel (chiCycKTwo (K := K)) (k + 1)
        (c (SqCore.sqHandleIdxU j)) = 1 then 1 else VU j with hDU
  set DV : Fin h → RawDepthCorrection (maxProPQuotient 2 (GalK K)) h k :=
    fun j ↦ if chiLevel (chiCycKTwo (K := K)) (k + 1)
        (c (SqCore.sqHandleIdxV j)) = 1 then 1 else VV j with hDV
  set L : List (RawDepthCorrection (maxProPQuotient 2 (GalK K)) h k) :=
    ((List.finRange h).map DU) ++ ((List.finRange h).map DV) with hL
  set C : RawDepthCorrection (maxProPQuotient 2 (GalK K)) h k := ⟨c, hdepth⟩ with hC
  set W : RawDepthCorrection (maxProPQuotient 2 (GalK K)) h k := C * L.prod with hW
  -- every list entry has trivial shift word
  have hLword : ∀ V ∈ L, (rawDepthShiftHom base hk) V = 1 := by
    intro V hV
    rw [hL] at hV
    rcases List.mem_append.mp hV with hV | hV <;>
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hV
    · by_cases hbad : chiLevel (chiCycKTwo (K := K)) (k + 1)
          (c (SqCore.sqHandleIdxU j)) = 1
      · rw [hDU]
        simp only [if_pos hbad]
        exact map_one _
      · rw [hDU]
        simp only [if_neg hbad]
        exact Subtype.ext (hVUword j)
    · by_cases hbad : chiLevel (chiCycKTwo (K := K)) (k + 1)
          (c (SqCore.sqHandleIdxV j)) = 1
      · rw [hDV]
        simp only [if_pos hbad]
        exact map_one _
      · rw [hDV]
        simp only [if_neg hbad]
        exact Subtype.ext (hVVword j)
  have hLprod : (rawDepthShiftHom base hk) L.prod = 1 := by
    rw [map_list_prod]
    apply List.prod_eq_one
    intro x hx
    obtain ⟨V, hV, rfl⟩ := List.mem_map.mp hx
    exact hLword V hV
  -- the digit of the flip product at a fixed handle slot
  have hdigU : ∀ j0 : Fin h,
      chiLevel (chiCycKTwo (K := K)) (k + 1)
          ((L.prod).correction (SqCore.sqHandleIdxU j0)) =
        chiLevel (chiCycKTwo (K := K)) (k + 1)
          ((DU j0).correction (SqCore.sqHandleIdxU j0)) := by
    intro j0
    have hEval : chiLevel (chiCycKTwo (K := K)) (k + 1)
        ((L.prod).correction (SqCore.sqHandleIdxU j0)) =
        ((chiLevel (chiCycKTwo (K := K)) (k + 1)).comp
          (stageFlipEval (SqCore.sqHandleIdxU j0))) L.prod := rfl
    rw [hEval, map_list_prod, hL, List.map_append, List.map_map, List.map_map,
      List.prod_append]
    have hDVpart : ((List.finRange h).map
        (⇑((chiLevel (chiCycKTwo (K := K)) (k + 1)).comp
          (stageFlipEval (SqCore.sqHandleIdxU j0))) ∘ DV)).prod = 1 := by
      apply List.prod_eq_one
      intro x hx
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hx
      show chiLevel (chiCycKTwo (K := K)) (k + 1)
        ((DV l).correction (SqCore.sqHandleIdxU j0)) = 1
      by_cases hbad : chiLevel (chiCycKTwo (K := K)) (k + 1)
          (c (SqCore.sqHandleIdxV l)) = 1
      · rw [hDV]
        simp only [if_pos hbad, RawDepthCorrection.one_correction]
        exact map_one _
      · rw [hDV]
        simp only [if_neg hbad]
        exact hVVoffU l j0
    have hDUpart : ((List.finRange h).map
        (⇑((chiLevel (chiCycKTwo (K := K)) (k + 1)).comp
          (stageFlipEval (SqCore.sqHandleIdxU j0))) ∘ DU)).prod =
        chiLevel (chiCycKTwo (K := K)) (k + 1)
          ((DU j0).correction (SqCore.sqHandleIdxU j0)) := by
      refine stageFlip_list_prod_single (List.finRange h) j0 _ (by simp)
        (List.nodup_finRange h) ?_
      intro l _ hlj
      show chiLevel (chiCycKTwo (K := K)) (k + 1)
        ((DU l).correction (SqCore.sqHandleIdxU j0)) = 1
      by_cases hbad : chiLevel (chiCycKTwo (K := K)) (k + 1)
          (c (SqCore.sqHandleIdxU l)) = 1
      · rw [hDU]
        simp only [if_pos hbad, RawDepthCorrection.one_correction]
        exact map_one _
      · rw [hDU]
        simp only [if_neg hbad]
        exact hVUoffU l j0 (fun hEq ↦ hlj hEq.symm)
    rw [hDUpart, hDVpart, mul_one]
  have hdigV : ∀ j0 : Fin h,
      chiLevel (chiCycKTwo (K := K)) (k + 1)
          ((L.prod).correction (SqCore.sqHandleIdxV j0)) =
        chiLevel (chiCycKTwo (K := K)) (k + 1)
          ((DV j0).correction (SqCore.sqHandleIdxV j0)) := by
    intro j0
    have hEval : chiLevel (chiCycKTwo (K := K)) (k + 1)
        ((L.prod).correction (SqCore.sqHandleIdxV j0)) =
        ((chiLevel (chiCycKTwo (K := K)) (k + 1)).comp
          (stageFlipEval (SqCore.sqHandleIdxV j0))) L.prod := rfl
    rw [hEval, map_list_prod, hL, List.map_append, List.map_map, List.map_map,
      List.prod_append]
    have hDUpart : ((List.finRange h).map
        (⇑((chiLevel (chiCycKTwo (K := K)) (k + 1)).comp
          (stageFlipEval (SqCore.sqHandleIdxV j0))) ∘ DU)).prod = 1 := by
      apply List.prod_eq_one
      intro x hx
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hx
      show chiLevel (chiCycKTwo (K := K)) (k + 1)
        ((DU l).correction (SqCore.sqHandleIdxV j0)) = 1
      by_cases hbad : chiLevel (chiCycKTwo (K := K)) (k + 1)
          (c (SqCore.sqHandleIdxU l)) = 1
      · rw [hDU]
        simp only [if_pos hbad, RawDepthCorrection.one_correction]
        exact map_one _
      · rw [hDU]
        simp only [if_neg hbad]
        exact hVUoffV l j0
    have hDVpart : ((List.finRange h).map
        (⇑((chiLevel (chiCycKTwo (K := K)) (k + 1)).comp
          (stageFlipEval (SqCore.sqHandleIdxV j0))) ∘ DV)).prod =
        chiLevel (chiCycKTwo (K := K)) (k + 1)
          ((DV j0).correction (SqCore.sqHandleIdxV j0)) := by
      refine stageFlip_list_prod_single (List.finRange h) j0 _ (by simp)
        (List.nodup_finRange h) ?_
      intro l _ hlj
      show chiLevel (chiCycKTwo (K := K)) (k + 1)
        ((DV l).correction (SqCore.sqHandleIdxV j0)) = 1
      by_cases hbad : chiLevel (chiCycKTwo (K := K)) (k + 1)
          (c (SqCore.sqHandleIdxV l)) = 1
      · rw [hDV]
        simp only [if_pos hbad, RawDepthCorrection.one_correction]
        exact map_one _
      · rw [hDV]
        simp only [if_neg hbad]
        exact hVVoffV l j0 (fun hEq ↦ hlj hEq.symm)
    rw [hDUpart, hDVpart, one_mul]
  refine ⟨W.correction, W.depth, ?_, ?_, ?_⟩
  · -- the literal shift is preserved
    have hCword : sqCoreHandleDbarWord base c =
        (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹ := by
      rw [sqCoreHandleDbarWord,
        ← stageShift_eq_dbarWordR2_mul_sqHandleDbarWord h k hk base c hdepth]
      exact hkill
    have hWhom : (rawDepthShiftHom base hk) W = (rawDepthShiftHom base hk) C := by
      rw [hW, map_mul, hLprod, mul_one]
    have hWword : sqCoreHandleDbarWord base W.correction =
        sqCoreHandleDbarWord base c := congrArg Subtype.val hWhom
    calc SqCyclotomicStageTuple.stageShift base W.correction
        = sqCoreHandleDbarWord base W.correction := by
          rw [sqCoreHandleDbarWord,
            stageShift_eq_dbarWordR2_mul_sqHandleDbarWord h k hk base W.correction W.depth]
      _ = sqCoreHandleDbarWord base c := hWword
      _ = (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹ := hCword
  · -- the U-handle digits are repaired
    intro j0
    have hWc : W.correction (SqCore.sqHandleIdxU j0) =
        c (SqCore.sqHandleIdxU j0) * (L.prod).correction (SqCore.sqHandleIdxU j0) := rfl
    rw [hWc, map_mul, hdigU j0]
    by_cases hbad : chiLevel (chiCycKTwo (K := K)) (k + 1)
        (c (SqCore.sqHandleIdxU j0)) = 1
    · rw [hbad, hDU]
      simp only [if_pos hbad, RawDepthCorrection.one_correction]
      rw [map_one, mul_one]
    · rw [hDU]
      simp only [if_neg hbad]
      exact stageFlip_digit_cancel hk (hdepth (SqCore.sqHandleIdxU j0))
        ((VU j0).depth (SqCore.sqHandleIdxU j0)) hbad (hVUdiag j0)
  · -- the V-handle digits are repaired
    intro j0
    have hWc : W.correction (SqCore.sqHandleIdxV j0) =
        c (SqCore.sqHandleIdxV j0) * (L.prod).correction (SqCore.sqHandleIdxV j0) := rfl
    rw [hWc, map_mul, hdigV j0]
    by_cases hbad : chiLevel (chiCycKTwo (K := K)) (k + 1)
        (c (SqCore.sqHandleIdxV j0)) = 1
    · rw [hbad, hDV]
      simp only [if_pos hbad, RawDepthCorrection.one_correction]
      rw [map_one, mul_one]
    · rw [hDV]
      simp only [if_neg hbad]
      exact stageFlip_digit_cancel hk (hdepth (SqCore.sqHandleIdxV j0))
        ((VV j0).depth (SqCore.sqHandleIdxV j0)) hbad (hVVdiag j0)

/-! ## Assembly against the kernel-adapted reduction -/

/-- **The kernel-adapted supply from a family and a flip supply at every stage.** -/
theorem sqKernelAdaptedDefectSupply_of_family_of_flipSupply {h : ℕ}
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : SqCyclotomicStageTuple K h k,
      Nonempty (SqStageCoordinateDerivationFamily T))
    (Hflip : ∀ (k : ℕ), 3 ≤ k → ∀ T : SqCyclotomicStageTuple K h k,
      SqStageHandleDigitFlipSupply T) :
    SqKernelAdaptedDefectSupply K h :=
  sqKernelAdaptedDefectSupply_of_family_of_digitRepair Hfam
    (fun k hk T ↦ sqStageHandleDigitRepairSupply_of_flipSupply hk (Hflip k hk T))

/-- **The forward presentation theorem over the family and the flips.**  For an odd-degree
field, a coordinate derivation family and a handle-digit flip supply at every stage deliver
the oriented presentation equivalence. -/
theorem nonempty_orientedEquiv_oddDegree_of_family_of_flipSupply
    {Rec : LocalReciprocity} (B : MarkedRecip Rec K)
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (Hfam : ∀ (k : ℕ), 3 ≤ k →
      ∀ T : SqCyclotomicStageTuple K ((Module.finrank ℚ_[2] K - 1) / 2) k,
        Nonempty (SqStageCoordinateDerivationFamily T))
    (Hflip : ∀ (k : ℕ), 3 ≤ k →
      ∀ T : SqCyclotomicStageTuple K ((Module.finrank ℚ_[2] K - 1) / 2) k,
        SqStageHandleDigitFlipSupply T) :
    Nonempty (OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2))
      (chiCycKTwo (K := K))) :=
  nonempty_orientedEquiv_oddDegree_of_kernelAdaptedSupply B hodd
    (sqKernelAdaptedDefectSupply_of_family_of_flipSupply Hfam Hflip)

#print axioms sqStageHandleDigitFlipSupply_of_rank_zero
#print axioms sqStageHandleDigitRepairSupply_of_flipSupply
#print axioms sqKernelAdaptedDefectSupply_of_family_of_flipSupply
#print axioms nonempty_orientedEquiv_oddDegree_of_family_of_flipSupply

end

end GQ2.Dyadic.LSquare

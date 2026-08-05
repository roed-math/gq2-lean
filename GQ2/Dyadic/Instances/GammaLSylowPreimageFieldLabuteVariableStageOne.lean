/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteVariableStage
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteCharacterRefinementObstruction

/-!
# Variable-rank stage one: the sharp supply from a kernel-adapted raw kill

The forward capstone consumes, at every stage, one sharp-admissible correction killing the
current improved-word defect (`CoreHandleSharpActualDefectSupply`).  This file proves that for
an *exact* stage tuple the full sharp statement follows from a raw kill whose modified handle
rows are trivial at the next finite precision.  The three core character rows need no further
arithmetic input:

* the `σ`- and `x₀`-rows are adjusted by `2^(k-2)`-th powers of the opposite core base letter
  (`sharp_move`); each such move commutes with its bracket partner, so the literal
  core-plus-handle shift is unchanged;
* the `x₁`-row is automatic: the corrected relator dies in `Q_(k+1)`, its χ-value is
  therefore `1 mod 2^(k+2)`, and the abelian collapse `sqRelWord_comm` turns this into the
  square congruence consumed by `dvd_succ_of_sq`;
* the residual fresh mod-`2^(k+2)` digits of all rows are then flipped by central `Z_k`
  classes with nontrivial sharp shadow (`stageResidual_exists_deep_zLayer_of_surjective`).
  Such flips change no literal shift at all: every bracket against a central class dies and
  the diagonal square dies by `zLayer_sq` (`sqCoreHandleDbarWord_eq_one_of_zLayer`).

Consequently the single remaining arithmetic obligation of the forward presentation theorem
is the kernel-adapted raw reachability recorded by `SqKernelAdaptedDefectSupply`; at `h = 0`
it degenerates to raw Labute reachability, and the `K = ⊥` oracle satisfies it.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## The exact per-slot cyclotomic targets -/

/-- The exact per-slot cyclotomic targets of the improved square presentation: the three
core values on `σ, x₀, x₁`, and the trivial unit on every hyperbolic handle letter. -/
noncomputable def sqStageChiTargetUnit (h : ℕ) (i : Fin (SqCore.sqRank h)) : ℤ_[2]ˣ :=
  if (i : ℕ) = 0 then GQ2.Roe.SvalUnit
  else if (i : ℕ) = 1 then GQ2.Roe.rootXUnit
  else if (i : ℕ) = 2 then GQ2.Roe.YvalUnit
  else 1

@[simp] theorem sqStageChiTargetUnit_zero (h : ℕ) :
    sqStageChiTargetUnit h 0 = GQ2.Roe.SvalUnit := by
  rw [sqStageChiTargetUnit, if_pos (SqCore.sqVal_zero h)]

@[simp] theorem sqStageChiTargetUnit_one (h : ℕ) :
    sqStageChiTargetUnit h 1 = GQ2.Roe.rootXUnit := by
  rw [sqStageChiTargetUnit, if_neg (by rw [SqCore.sqVal_one]; omega),
    if_pos (SqCore.sqVal_one h)]

@[simp] theorem sqStageChiTargetUnit_two (h : ℕ) :
    sqStageChiTargetUnit h 2 = GQ2.Roe.YvalUnit := by
  rw [sqStageChiTargetUnit, if_neg (by rw [SqCore.sqVal_two]; omega),
    if_neg (by rw [SqCore.sqVal_two]; omega), if_pos (SqCore.sqVal_two h)]

@[simp] theorem sqStageChiTargetUnit_handleU (h : ℕ) (j : Fin h) :
    sqStageChiTargetUnit h (SqCore.sqHandleIdxU j) = 1 := by
  rw [sqStageChiTargetUnit, if_neg (by rw [SqCore.sqHandleIdxU_val]; omega),
    if_neg (by rw [SqCore.sqHandleIdxU_val]; omega),
    if_neg (by rw [SqCore.sqHandleIdxU_val]; omega)]

@[simp] theorem sqStageChiTargetUnit_handleV (h : ℕ) (j : Fin h) :
    sqStageChiTargetUnit h (SqCore.sqHandleIdxV j) = 1 := by
  rw [sqStageChiTargetUnit, if_neg (by rw [SqCore.sqHandleIdxV_val]; omega),
    if_neg (by rw [SqCore.sqHandleIdxV_val]; omega),
    if_neg (by rw [SqCore.sqHandleIdxV_val]; omega)]

/-! ## Index disequalities for the improved marking -/

private theorem sqStageFin_zero_ne_one (h : ℕ) : (0 : Fin (SqCore.sqRank h)) ≠ 1 := by
  intro hEq
  have hv := congrArg Fin.val hEq
  rw [SqCore.sqVal_zero, SqCore.sqVal_one] at hv
  omega

private theorem sqStageFin_one_ne_zero (h : ℕ) : (1 : Fin (SqCore.sqRank h)) ≠ 0 := by
  intro hEq
  have hv := congrArg Fin.val hEq
  rw [SqCore.sqVal_one, SqCore.sqVal_zero] at hv
  omega

private theorem sqStageFin_two_ne_zero (h : ℕ) : (2 : Fin (SqCore.sqRank h)) ≠ 0 := by
  intro hEq
  have hv := congrArg Fin.val hEq
  rw [SqCore.sqVal_two, SqCore.sqVal_zero] at hv
  omega

private theorem sqStageFin_two_ne_one (h : ℕ) : (2 : Fin (SqCore.sqRank h)) ≠ 1 := by
  intro hEq
  have hv := congrArg Fin.val hEq
  rw [SqCore.sqVal_two, SqCore.sqVal_one] at hv
  omega

private theorem sqStageFin_handleU_ne_zero {h : ℕ} (j : Fin h) :
    SqCore.sqHandleIdxU j ≠ (0 : Fin (SqCore.sqRank h)) := by
  intro hEq
  have hv := congrArg Fin.val hEq
  rw [SqCore.sqHandleIdxU_val, SqCore.sqVal_zero] at hv
  omega

private theorem sqStageFin_handleU_ne_one {h : ℕ} (j : Fin h) :
    SqCore.sqHandleIdxU j ≠ (1 : Fin (SqCore.sqRank h)) := by
  intro hEq
  have hv := congrArg Fin.val hEq
  rw [SqCore.sqHandleIdxU_val, SqCore.sqVal_one] at hv
  omega

private theorem sqStageFin_handleV_ne_zero {h : ℕ} (j : Fin h) :
    SqCore.sqHandleIdxV j ≠ (0 : Fin (SqCore.sqRank h)) := by
  intro hEq
  have hv := congrArg Fin.val hEq
  rw [SqCore.sqHandleIdxV_val, SqCore.sqVal_zero] at hv
  omega

private theorem sqStageFin_handleV_ne_one {h : ℕ} (j : Fin h) :
    SqCore.sqHandleIdxV j ≠ (1 : Fin (SqCore.sqRank h)) := by
  intro hEq
  have hv := congrArg Fin.val hEq
  rw [SqCore.sqHandleIdxV_val, SqCore.sqVal_one] at hv
  omega

/-! ## The deep-digit cancellation -/

/-- Two `2`-adic values with sharp (exact) digit at level `n` multiply to one with a trivial
level-`n` digit: the fresh digits of two flagged rows cancel.  This is the arithmetic core of
the central `Z_k` flip. -/
private theorem stageResidual_deep_cancel {n : ℕ} (hn : 1 ≤ n) {u w : ℤ_[2]}
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

/-! ## Unit-map plumbing at the sharp precision -/

private theorem stageResidual_units_map_eq_of_dvd {n : ℕ} {x y : ℤ_[2]ˣ}
    (hxy : (2 : ℤ_[2]) ^ n ∣ ((x * y⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1) :
    Units.map (PadicInt.toZModPow n).toMonoidHom x =
      Units.map (PadicInt.toZModPow n).toMonoidHom y := by
  have hker : x * y⁻¹ ∈ (Units.map (PadicInt.toZModPow n).toMonoidHom).ker := by
    rw [mem_ker_units_toZModPow_iff]
    exact_mod_cast hxy
  have h1 := MonoidHom.mem_ker.mp hker
  rwa [map_mul, map_inv, mul_inv_eq_one] at h1

private theorem stageResidual_dvd_of_units_map_eq {n : ℕ} {x y : ℤ_[2]ˣ}
    (hxy : Units.map (PadicInt.toZModPow n).toMonoidHom x =
      Units.map (PadicInt.toZModPow n).toMonoidHom y) :
    (2 : ℤ_[2]) ^ n ∣ ((x * y⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  have hker : x * y⁻¹ ∈ (Units.map (PadicInt.toZModPow n).toMonoidHom).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
    exact hxy
  rw [mem_ker_units_toZModPow_iff] at hker
  exact_mod_cast hker

/-! ## Central corrections never move the literal shift -/

/-- A coordinatewise central `Z_k` correction has literally trivial core-plus-handle shift:
all its brackets die by centrality and the diagonal square dies because `Z_k` has exponent
two.  This is the exact mechanism making the fresh-digit flip free. -/
theorem sqCoreHandleDbarWord_eq_one_of_zLayer
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {h k : ℕ} (base v : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hv : ∀ i, v i ∈ zLayer G k) :
    sqCoreHandleDbarWord base v = 1 := by
  have hcomm : ∀ (i : Fin (SqCore.sqRank h)) (t : levelQuot G (k + 1)),
      commP (v i) t = 1 := fun i t ↦
    commP_eq_one_of_mul_comm (zLayer_commute (hv i) t).eq
  have hhandle : sqHandleDbarWord base v = 1 := by
    rw [sqHandleDbarWord]
    apply List.prod_eq_one
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    rw [hcomm, hcomm, one_mul]
  rw [sqCoreHandleDbarWord, hhandle, mul_one, dbarWordR2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [zLayer_sq _ (hv 2), hcomm, hcomm, hcomm, one_mul, one_mul, one_mul]

namespace SqCyclotomicStageTuple

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-- The exact cyclotomic fibres of a stage tuple pin all its finite character rows to the
canonical per-slot targets. -/
theorem stageResidual_chiLevel_generators {h k : ℕ} (T : SqCyclotomicStageTuple K h k)
    (i : Fin (SqCore.sqRank h)) :
    chiLevel (chiCycKTwo (K := K)) k (T.generators i) =
      Units.map (PadicInt.toZModPow k).toMonoidHom (sqStageChiTargetUnit h i) := by
  rcases SqCore.sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · obtain ⟨x, hxchi, hx⟩ := T.sigma
    rw [hx, chiLevel_levelMk, hxchi, sqStageChiTargetUnit_zero]
  · obtain ⟨x, hxchi, hx⟩ := T.x0
    rw [hx, chiLevel_levelMk, hxchi, sqStageChiTargetUnit_one]
  · obtain ⟨x, hxchi, hx⟩ := T.x1
    rw [hx, chiLevel_levelMk, hxchi, sqStageChiTargetUnit_two]
  · obtain ⟨x, hxchi, hx⟩ := T.handleU j
    have hx1 : chiCycKTwo (K := K) x = 1 := MonoidHom.mem_ker.mp hxchi
    rw [hx, chiLevel_levelMk, hx1, sqStageChiTargetUnit_handleU]
  · obtain ⟨x, hxchi, hx⟩ := T.handleV j
    have hx1 : chiCycKTwo (K := K) x = 1 := MonoidHom.mem_ker.mp hxchi
    rw [hx, chiLevel_levelMk, hx1, sqStageChiTargetUnit_handleV]

/-! ## The sharp supply from a kernel-adapted raw kill -/

/-- **The sharp actual-defect supply from a kernel-adapted raw kill.**  For an exact stage
tuple, any depth correction that kills the current improved-word defect and leaves trivial
handle rows at the next finite precision upgrades to a sharp-admissible defect-killing
correction: the `σ` and `x₀` rows are fixed by commuting `2^(k-2)`-power moves, the `x₁` row
is automatic from the corrected relator through the abelian collapse, and every remaining
fresh mod-`2^(k+2)` digit is flipped by a central deep class with literally trivial shift. -/
theorem stageResidual_nonempty_actualDefectSupply_of_kernelAdaptedKill
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} (hk : 3 ≤ k)
    (hsurj : Function.Surjective (chiCycKTwo (K := K)))
    (c : Fin (SqCore.sqRank h) → levelQuot (maxProPQuotient 2 (GalK K)) (k + 1))
    (hdepth : ∀ i, c i ∈ lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1))
    (hkill : stageShift
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) c =
      (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹)
    (hhU : ∀ j : Fin h, chiLevel (chiCycKTwo (K := K)) (k + 1)
        (stageModified
          (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) c
          (SqCore.sqHandleIdxU j)) = 1)
    (hhV : ∀ j : Fin h, chiLevel (chiCycKTwo (K := K)) (k + 1)
        (stageModified
          (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) c
          (SqCore.sqHandleIdxV j)) = 1) :
    Nonempty (CoreHandleSharpActualDefectSupply T hk) := by
  set base : Fin (SqCore.sqRank h) → levelQuot (maxProPQuotient 2 (GalK K)) (k + 1) :=
    fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i) with hbase
  have hbase_apply : ∀ i, base i =
      canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i) := fun i ↦ rfl
  -- ambient lifts of the base and of the correction, with their χ-congruences
  choose a ha using fun i ↦
    levelMk_surjective (maxProPQuotient 2 (GalK K)) (k + 1) (base i)
  choose u hu hcu using fun i ↦ hdepth i
  have haT : ∀ i, levelMk (maxProPQuotient 2 (GalK K)) k (a i) = T.generators i := by
    intro i
    have hp := congrArg (GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k) (ha i)
    rwa [levelProj_levelMk, hbase_apply i, levelProj_canonLift] at hp
  have hdev : ∀ i, (2 : ℤ_[2]) ^ k ∣
      ((chiCycKTwo (K := K) (a i) * (sqStageChiTargetUnit h i)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
    fun i ↦ dvd_of_chiLevel_eq (chiCycKTwo (K := K)) (sqStageChiTargetUnit h i) (haT i)
      (stageResidual_chiLevel_generators T i)
  have hchiu : ∀ i, (2 : ℤ_[2]) ^ k ∣
      ((chiCycKTwo (K := K) (u i) : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    intro i
    have hd := dvd_chi_of_mem_twoCentralSeries (chiCycKTwo (K := K)) (k := k - 1)
      (by omega) (hu i)
    rwa [show k - 1 + 1 = k by omega] at hd
  -- word form of the kill
  have hword : sqCoreHandleDbarWord base c =
      (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹ := by
    rw [sqCoreHandleDbarWord,
      ← stageShift_eq_dbarWordR2_mul_sqHandleDbarWord h k hk base c hdepth]
    exact hkill
  -- mod-8 anchors of the two moved targets
  have hSval8 : PadicInt.toZModPow 3 ((GQ2.Roe.SvalUnit : ℤ_[2]ˣ) : ℤ_[2]) = 5 := by
    simpa [chiTargetR2, chiTargetUnitsR2] using chiTargetR2_three 0
  have hrootX8 : PadicInt.toZModPow 3 ((GQ2.Roe.rootXUnit : ℤ_[2]ˣ) : ℤ_[2]) = 5 := by
    simpa [chiTargetR2, chiTargetUnitsR2] using chiTargetR2_three 1
  -- the two commuting sharp moves
  obtain ⟨d1, hd1, hd1odd⟩ : ∃ d : ℤ_[2],
      ((chiCycKTwo (K := K) (a 1) ^ 2 ^ (k - 2) : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ k * d ∧
        ¬ (2 : ℤ_[2]) ∣ d := by
    refine sharp_move hk hrootX8 ?_
    have hd := hdev 1
    rwa [sqStageChiTargetUnit_one] at hd
  obtain ⟨d0, hd0, hd0odd⟩ : ∃ d : ℤ_[2],
      ((chiCycKTwo (K := K) (a 0) ^ 2 ^ (k - 2) : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ k * d ∧
        ¬ (2 : ℤ_[2]) ∣ d := by
    refine sharp_move hk hSval8 ?_
    have hd := hdev 0
    rwa [sqStageChiTargetUnit_zero] at hd
  -- the dichotomy digits for the σ- and x₀-rows
  have hrow0 : (2 : ℤ_[2]) ^ k ∣
      ((chiCycKTwo (K := K) (a 0) * GQ2.Roe.SvalUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
        ((chiCycKTwo (K := K) (u 0) : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have hd := hdev 0
    rw [sqStageChiTargetUnit_zero] at hd
    exact dvd_mul_sub_one hd (hchiu 0)
  have hrow1 : (2 : ℤ_[2]) ^ k ∣
      ((chiCycKTwo (K := K) (a 1) * GQ2.Roe.rootXUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
        ((chiCycKTwo (K := K) (u 1) : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have hd := hdev 1
    rw [sqStageChiTargetUnit_one] at hd
    exact dvd_mul_sub_one hd (hchiu 1)
  obtain ⟨e0, he0⟩ : ∃ e0 : ℕ, (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiCycKTwo (K := K) (a 0) * GQ2.Roe.SvalUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
          ((chiCycKTwo (K := K) (u 0) : ℤ_[2]ˣ) : ℤ_[2]) *
          ((chiCycKTwo (K := K) (a 1) ^ 2 ^ (k - 2) : ℤ_[2]ˣ) : ℤ_[2]) ^ e0 - 1 := by
    rcases dvd_or_dvd_mul (by omega : 1 ≤ k) hrow0 hd1 hd1odd with hcase | hcase
    · exact ⟨0, by simpa using hcase⟩
    · exact ⟨1, by simpa using hcase⟩
  obtain ⟨e1, he1⟩ : ∃ e1 : ℕ, (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiCycKTwo (K := K) (a 1) * GQ2.Roe.rootXUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
          ((chiCycKTwo (K := K) (u 1) : ℤ_[2]ˣ) : ℤ_[2]) *
          ((chiCycKTwo (K := K) (a 0) ^ 2 ^ (k - 2) : ℤ_[2]ˣ) : ℤ_[2]) ^ e1 - 1 := by
    rcases dvd_or_dvd_mul (by omega : 1 ≤ k) hrow1 hd0 hd0odd with hcase | hcase
    · exact ⟨0, by simpa using hcase⟩
    · exact ⟨1, by simpa using hcase⟩
  -- the moves in the level quotient
  obtain ⟨p, hpdef⟩ : ∃ p : levelQuot (maxProPQuotient 2 (GalK K)) (k + 1),
      p = (base 1 ^ 2 ^ (k - 2)) ^ e0 := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q : levelQuot (maxProPQuotient 2 (GalK K)) (k + 1),
      q = (base 0 ^ 2 ^ (k - 2)) ^ e1 := ⟨_, rfl⟩
  have hpmem : p ∈ lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1) := by
    rw [hpdef]
    refine Subgroup.pow_mem _ ?_ e0
    have hp2 := pow_two_pow_mem_lambdaImage (base 1) (k - 2)
    rwa [show 1 + (k - 2) = k - 1 by omega] at hp2
  have hqmem : q ∈ lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1) := by
    rw [hqdef]
    refine Subgroup.pow_mem _ ?_ e1
    have hq2 := pow_two_pow_mem_lambdaImage (base 0) (k - 2)
    rwa [show 1 + (k - 2) = k - 1 by omega] at hq2
  -- the combined move, its depth, and its literally trivial shift
  obtain ⟨w, hwdef⟩ : ∃ w : Fin (SqCore.sqRank h) →
      levelQuot (maxProPQuotient 2 (GalK K)) (k + 1),
      w = fun i ↦ (if i = 0 then p else 1) * (if i = 1 then q else 1) := ⟨_, rfl⟩
  have hw0 : w 0 = p := by
    simp only [hwdef]
    simp [sqStageFin_zero_ne_one h]
  have hw1 : w 1 = q := by
    simp only [hwdef]
    simp [sqStageFin_one_ne_zero h]
  have hwU : ∀ j : Fin h, w (SqCore.sqHandleIdxU j) = 1 := by
    intro j
    simp only [hwdef]
    simp [sqStageFin_handleU_ne_zero j, sqStageFin_handleU_ne_one j]
  have hwV : ∀ j : Fin h, w (SqCore.sqHandleIdxV j) = 1 := by
    intro j
    simp only [hwdef]
    simp [sqStageFin_handleV_ne_zero j, sqStageFin_handleV_ne_one j]
  have hwdepth : ∀ i, w i ∈ lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1) := by
    intro i
    simp only [hwdef]
    refine Subgroup.mul_mem _ ?_ ?_
    · split_ifs
      · exact hpmem
      · exact Subgroup.one_mem _
    · split_ifs
      · exact hqmem
      · exact Subgroup.one_mem _
  have hpcomm : p * base 1 = base 1 * p := by
    rw [hpdef]
    exact (((Commute.refl (base 1)).pow_left (2 ^ (k - 2))).pow_left e0).eq
  have hqcomm : q * base 0 = base 0 * q := by
    rw [hqdef]
    exact (((Commute.refl (base 0)).pow_left (2 ^ (k - 2))).pow_left e1).eq
  have hwword : sqCoreHandleDbarWord base w = 1 := by
    have hsplit : w = fun i ↦
        (rawDepthCoordinateCorrection (G := maxProPQuotient 2 (GalK K)) (h := h) (k := k) 0
          ⟨p, hpmem⟩).correction i *
          (rawDepthCoordinateCorrection (G := maxProPQuotient 2 (GalK K)) (h := h) (k := k) 1
            ⟨q, hqmem⟩).correction i := by
      rw [hwdef]
      rfl
    rw [hsplit, sqCoreHandleDbarWord_mul h k hk base
      (rawDepthCoordinateCorrection 0 ⟨p, hpmem⟩).depth
      (rawDepthCoordinateCorrection 1 ⟨q, hqmem⟩).depth]
    have h0 : sqCoreHandleDbarWord base
        (rawDepthCoordinateCorrection (G := maxProPQuotient 2 (GalK K)) (h := h) (k := k) 0
          ⟨p, hpmem⟩).correction = commP p (base 1) :=
      rawDepthShiftHom_zero_apply base hk ⟨p, hpmem⟩
    have h1 : sqCoreHandleDbarWord base
        (rawDepthCoordinateCorrection (G := maxProPQuotient 2 (GalK K)) (h := h) (k := k) 1
          ⟨q, hqmem⟩).correction = commP q (base 0) :=
      rawDepthShiftHom_one_apply base hk ⟨q, hqmem⟩
    rw [h0, h1, commP_eq_one_of_mul_comm hpcomm, commP_eq_one_of_mul_comm hqcomm, one_mul]
  -- the moved correction
  obtain ⟨c', hc'def⟩ : ∃ c' : Fin (SqCore.sqRank h) →
      levelQuot (maxProPQuotient 2 (GalK K)) (k + 1),
      c' = fun i ↦ c i * w i := ⟨_, rfl⟩
  have hc'depth : ∀ i, c' i ∈ lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1) := by
    intro i
    simp only [hc'def]
    exact Subgroup.mul_mem _ (hdepth i) (hwdepth i)
  have hc'word : sqCoreHandleDbarWord base c' =
      (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹ := by
    simp only [hc'def]
    rw [sqCoreHandleDbarWord_mul h k hk base hdepth hwdepth, hword, hwword, mul_one]
  -- ambient lifts of the move and of the moved modified tuple
  obtain ⟨what, hwhatdef⟩ : ∃ what : Fin (SqCore.sqRank h) → maxProPQuotient 2 (GalK K),
      what = fun i ↦ (if i = 0 then (a 1 ^ 2 ^ (k - 2)) ^ e0 else 1) *
        (if i = 1 then (a 0 ^ 2 ^ (k - 2)) ^ e1 else 1) := ⟨_, rfl⟩
  have hwhat : ∀ i, levelMk (maxProPQuotient 2 (GalK K)) (k + 1) (what i) = w i := by
    intro i
    simp only [hwhatdef, hwdef, map_mul,
      apply_ite (levelMk (maxProPQuotient 2 (GalK K)) (k + 1)), map_pow, map_one, ha,
      hpdef, hqdef]
  obtain ⟨m, hmdef⟩ : ∃ m : Fin (SqCore.sqRank h) → maxProPQuotient 2 (GalK K),
      m = fun i ↦ a i * (u i * what i) := ⟨_, rfl⟩
  have hmlift : ∀ i, levelMk (maxProPQuotient 2 (GalK K)) (k + 1) (m i) =
      stageModified base c' i := by
    intro i
    simp only [hmdef, map_mul, ha, hcu, hwhat, hc'def]
    rfl
  -- the σ-row at the next precision
  have hdvd0 : (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiCycKTwo (K := K) (m 0) * GQ2.Roe.SvalUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have hm0 : m 0 = a 0 * (u 0 * (a 1 ^ 2 ^ (k - 2)) ^ e0) := by
      simp only [hmdef, hwhatdef]
      simp [sqStageFin_zero_ne_one h]
    rw [hm0]
    have hEq : ((chiCycKTwo (K := K) (a 0 * (u 0 * (a 1 ^ 2 ^ (k - 2)) ^ e0)) *
        GQ2.Roe.SvalUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) =
        ((chiCycKTwo (K := K) (a 0) * GQ2.Roe.SvalUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
          ((chiCycKTwo (K := K) (u 0) : ℤ_[2]ˣ) : ℤ_[2]) *
          ((chiCycKTwo (K := K) (a 1) ^ 2 ^ (k - 2) : ℤ_[2]ˣ) : ℤ_[2]) ^ e0 := by
      push_cast [map_mul, map_pow]
      ring
    rw [hEq]
    exact he0
  -- the x₀-row at the next precision
  have hdvd1 : (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiCycKTwo (K := K) (m 1) * GQ2.Roe.rootXUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have hm1 : m 1 = a 1 * (u 1 * (a 0 ^ 2 ^ (k - 2)) ^ e1) := by
      simp only [hmdef, hwhatdef]
      simp [sqStageFin_one_ne_zero h]
    rw [hm1]
    have hEq : ((chiCycKTwo (K := K) (a 1 * (u 1 * (a 0 ^ 2 ^ (k - 2)) ^ e1)) *
        GQ2.Roe.rootXUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) =
        ((chiCycKTwo (K := K) (a 1) * GQ2.Roe.rootXUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
          ((chiCycKTwo (K := K) (u 1) : ℤ_[2]ˣ) : ℤ_[2]) *
          ((chiCycKTwo (K := K) (a 0) ^ 2 ^ (k - 2) : ℤ_[2]ˣ) : ℤ_[2]) ^ e1 := by
      push_cast [map_mul, map_pow]
      ring
    rw [hEq]
    exact he1
  -- the corrected relator dies at level k+1
  have hrel1 : SqCore.sqRelWord (stageModified base c') = 1 := by
    have hshift : stageShift base c' =
        (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹ := by
      rw [stageShift_eq_dbarWordR2_mul_sqHandleDbarWord h k hk base c' hc'depth]
      exact hc'word
    rw [sqRelWord_stageModified base c', hshift]
    have hδ : SqCore.sqRelWord base =
        sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators := rfl
    rw [hδ, mul_inv_cancel]
  have hrelG : SqCore.sqRelWord m ∈
      twoCentralSeries (maxProPQuotient 2 (GalK K)) (k + 1) := by
    have hmk : levelMk (maxProPQuotient 2 (GalK K)) (k + 1) (SqCore.sqRelWord m) = 1 := by
      rw [SqCore.map_sqRelWord,
        show (fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) (k + 1) (m i)) =
          stageModified base c' from funext hmlift]
      exact hrel1
    exact (QuotientGroup.eq_one_iff _).mp hmk
  have hchirel := dvd_chi_of_mem_twoCentralSeries (chiCycKTwo (K := K))
    (k := k + 1) (by omega) hrelG
  have hcollapse : chiCycKTwo (K := K) (SqCore.sqRelWord m) =
      (chiCycKTwo (K := K) (m 1) ^ 4)⁻¹ * chiCycKTwo (K := K) (m 2) ^ 2 := by
    rw [show chiCycKTwo (K := K) (SqCore.sqRelWord m) =
      SqCore.sqRelWord (fun i ↦ chiCycKTwo (K := K) (m i)) from
        SqCore.map_sqRelWord (chiCycKTwo (K := K)) m]
    exact SqCore.sqRelWord_comm (fun i ↦ chiCycKTwo (K := K) (m i))
  rw [hcollapse] at hchirel
  -- the automatic x₁-row
  have hdvd2 : (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiCycKTwo (K := K) (m 2) * GQ2.Roe.YvalUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have hm2 : m 2 = a 2 * u 2 := by
      simp only [hmdef, hwhatdef]
      simp [sqStageFin_two_ne_zero h, sqStageFin_two_ne_one h]
    have hρ2k : (2 : ℤ_[2]) ^ k ∣
        ((chiCycKTwo (K := K) (m 2) * GQ2.Roe.YvalUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
      rw [hm2]
      have hEq : ((chiCycKTwo (K := K) (a 2 * u 2) *
          GQ2.Roe.YvalUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) =
          ((chiCycKTwo (K := K) (a 2) * GQ2.Roe.YvalUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
            ((chiCycKTwo (K := K) (u 2) : ℤ_[2]ˣ) : ℤ_[2]) := by
        push_cast [map_mul]
        ring
      rw [hEq]
      have hd := hdev 2
      rw [sqStageChiTargetUnit_two] at hd
      exact dvd_mul_sub_one hd (hchiu 2)
    refine dvd_succ_of_sq (by omega) hρ2k ?_
    have h4 : (2 : ℤ_[2]) ^ (k + 2) ∣
        (((chiCycKTwo (K := K) (m 1) * GQ2.Roe.rootXUnit⁻¹) ^ 4 : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
      refine dvd_trans (pow_dvd_pow 2 (by omega : k + 2 ≤ k + 1 + 2)) ?_
      have h4' := dvd_pow_two_pow_sub_one (k := k + 1) (by omega) hdvd1 2
      rw [Units.val_pow_eq_pow_val]
      simpa using h4'
    have hidU : (chiCycKTwo (K := K) (m 2) * GQ2.Roe.YvalUnit⁻¹) ^ 2 =
        ((chiCycKTwo (K := K) (m 1) ^ 4)⁻¹ * chiCycKTwo (K := K) (m 2) ^ 2) *
          (chiCycKTwo (K := K) (m 1) * GQ2.Roe.rootXUnit⁻¹) ^ 4 := by
      have hAB : ∀ A B C : ℤ_[2]ˣ, A⁻¹ * B * (A * C) = B * C := by
        intro A B C
        rw [show A⁻¹ * B * (A * C) = A⁻¹ * (B * A) * C by group, mul_comm B A,
          show A⁻¹ * (A * B) * C = A⁻¹ * A * (B * C) by group, inv_mul_cancel, one_mul]
      rw [mul_pow, mul_pow, hAB, inv_pow, inv_pow, GQ2.Roe.YvalUnit_sq_eq]
    have hcomb := dvd_mul_sub_one hchirel h4
    rw [← Units.val_mul, ← hidU, Units.val_pow_eq_pow_val] at hcomb
    exact hcomb
  -- the uniform next-precision congruence at every slot
  have hdvdAll : ∀ i, (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiCycKTwo (K := K) (m i) *
        (sqStageChiTargetUnit h i)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    intro i
    have hstage : ∀ j : Fin h,
        stageModified base c' (SqCore.sqHandleIdxU j) =
          stageModified base c (SqCore.sqHandleIdxU j) ∧
        stageModified base c' (SqCore.sqHandleIdxV j) =
          stageModified base c (SqCore.sqHandleIdxV j) := by
      intro j
      constructor
      · show base _ * c' _ = base _ * c _
        simp only [hc'def]
        rw [hwU j, mul_one]
      · show base _ * c' _ = base _ * c _
        simp only [hc'def]
        rw [hwV j, mul_one]
    rcases SqCore.sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [sqStageChiTargetUnit_zero]
      exact hdvd0
    · rw [sqStageChiTargetUnit_one]
      exact hdvd1
    · rw [sqStageChiTargetUnit_two]
      exact hdvd2
    · rw [sqStageChiTargetUnit_handleU]
      refine dvd_of_chiLevel_eq (chiCycKTwo (K := K)) 1 (hmlift (SqCore.sqHandleIdxU j)) ?_
      rw [(hstage j).1, hhU j, map_one]
    · rw [sqStageChiTargetUnit_handleV]
      refine dvd_of_chiLevel_eq (chiCycKTwo (K := K)) 1 (hmlift (SqCore.sqHandleIdxV j)) ?_
      rw [(hstage j).2, hhV j, map_one]
  -- the deep central class with exact fresh digit
  obtain ⟨z, hzmem, hzsharp⟩ :=
    stageResidual_exists_deep_zLayer_of_surjective hsurj k (by omega)
  obtain ⟨g, hg, hgz⟩ := hzmem
  have hgdvd : (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiCycKTwo (K := K) g : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
    dvd_chi_of_mem_twoCentralSeries (chiCycKTwo (K := K)) (by omega) hg
  have hgndvd : ¬ (2 : ℤ_[2]) ^ (k + 2) ∣
      ((chiCycKTwo (K := K) g : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    intro hdvd
    apply hzsharp
    rw [← hgz, sharpChiLevel_levelMk]
    have hker : chiCycKTwo (K := K) g ∈
        (Units.map (PadicInt.toZModPow (k + 2)).toMonoidHom).ker := by
      rw [mem_ker_units_toZModPow_iff]
      exact_mod_cast hdvd
    exact MonoidHom.mem_ker.mp hker
  -- the per-slot fresh-digit flip
  have hflip : ∀ i, ∃ (v : levelQuot (maxProPQuotient 2 (GalK K)) (k + 1))
      (g' : maxProPQuotient 2 (GalK K)),
      v ∈ zLayer (maxProPQuotient 2 (GalK K)) k ∧
      levelMk (maxProPQuotient 2 (GalK K)) (k + 1) g' = v ∧
      (2 : ℤ_[2]) ^ (k + 2) ∣
        ((chiCycKTwo (K := K) (m i) * chiCycKTwo (K := K) g' *
          (sqStageChiTargetUnit h i)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    intro i
    by_cases hsharp : (2 : ℤ_[2]) ^ (k + 2) ∣
        ((chiCycKTwo (K := K) (m i) * (sqStageChiTargetUnit h i)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1
    · refine ⟨1, 1, Subgroup.one_mem _, map_one _, ?_⟩
      rw [map_one, mul_one]
      exact hsharp
    · refine ⟨z, g, ⟨g, hg, hgz⟩, hgz, ?_⟩
      have hprod := stageResidual_deep_cancel (n := k + 1) (by omega)
        (hdvdAll i) hsharp hgdvd hgndvd
      have hEq : ((chiCycKTwo (K := K) (m i) * chiCycKTwo (K := K) g *
          (sqStageChiTargetUnit h i)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) =
          ((chiCycKTwo (K := K) (m i) * (sqStageChiTargetUnit h i)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
            ((chiCycKTwo (K := K) g : ℤ_[2]ˣ) : ℤ_[2]) := by
        push_cast
        ring
      rw [hEq]
      exact hprod
  choose v gv hvz hvlift hvsharp using hflip
  -- the final sharp correction
  obtain ⟨cF, hcFdef⟩ : ∃ cF : Fin (SqCore.sqRank h) →
      levelQuot (maxProPQuotient 2 (GalK K)) (k + 1),
      cF = fun i ↦ c' i * v i := ⟨_, rfl⟩
  have hcFdepth : ∀ i, cF i ∈ lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1) := by
    intro i
    simp only [hcFdef]
    exact Subgroup.mul_mem _ (hc'depth i) (lambdaImage_le_of_le (by omega) (hvz i))
  have hcFword : sqCoreHandleDbarWord base cF =
      (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹ := by
    simp only [hcFdef]
    rw [sqCoreHandleDbarWord_mul h k hk base hc'depth
      (fun i ↦ lambdaImage_le_of_le (by omega) (hvz i)),
      hc'word, sqCoreHandleDbarWord_eq_one_of_zLayer base v hvz, mul_one]
  have hcFlift : ∀ i, levelMk (maxProPQuotient 2 (GalK K)) (k + 1) (m i * gv i) =
      stageModified base cF i := by
    intro i
    rw [map_mul, hmlift i, hvlift i]
    show base i * c' i * v i = base i * cF i
    simp only [hcFdef]
    rw [mul_assoc]
  have hsharpRows : ∀ i, sharpChiLevel (chiCycKTwo (K := K)) (k + 1) (by omega)
      (stageModified base cF i) =
      Units.map (PadicInt.toZModPow (k + 2)).toMonoidHom (sqStageChiTargetUnit h i) := by
    intro i
    rw [← hcFlift i, sharpChiLevel_levelMk]
    refine stageResidual_units_map_eq_of_dvd ?_
    rw [map_mul]
    exact hvsharp i
  -- assembly
  refine ⟨⟨{ correction := cF
             depth := hcFdepth
             sigma := ?_
             x0 := ?_
             x1 := ?_
             handleU := ?_
             handleV := ?_ }, ?_⟩⟩
  · have hs := hsharpRows 0
    rwa [sqStageChiTargetUnit_zero] at hs
  · have hs := hsharpRows 1
    rwa [sqStageChiTargetUnit_one] at hs
  · have hs := hsharpRows 2
    rwa [sqStageChiTargetUnit_two] at hs
  · intro j
    have hs := hsharpRows (SqCore.sqHandleIdxU j)
    rwa [sqStageChiTargetUnit_handleU, map_one] at hs
  · intro j
    have hs := hsharpRows (SqCore.sqHandleIdxV j)
    rwa [sqStageChiTargetUnit_handleV, map_one] at hs
  · change sqCoreHandleDbarWord base cF = _
    exact hcFword

end SqCyclotomicStageTuple

#print axioms sqStageChiTargetUnit
#print axioms sqCoreHandleDbarWord_eq_one_of_zLayer
#print axioms SqCyclotomicStageTuple.stageResidual_chiLevel_generators
#print axioms SqCyclotomicStageTuple.stageResidual_nonempty_actualDefectSupply_of_kernelAdaptedKill

end

end GQ2.Dyadic.LSquare

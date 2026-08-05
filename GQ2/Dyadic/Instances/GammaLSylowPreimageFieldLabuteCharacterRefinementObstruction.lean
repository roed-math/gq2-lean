/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteRawSpan
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStageRegression

/-!
# Refutation of the universal sharp character refinement

`RawDefectSharpCharacterRefinement` demands that *every* raw depth correction killing the
current defect share its finite sharp-character vector with some sharp-admissible base point.
This file proves that the demand is too strong: whenever the sharp actual-defect supply is
nonempty and the graded layer carries one class with nontrivial fresh character digit, the
interface is false.  The obstruction is exact: sharp admissibility *forces* the character
vector, while multiplying a defect-killing correction by a central deep class with nontrivial
digit changes the vector without changing the literal improved-word shift.

At the bottom field both side conditions are theorems, so the interface is unconditionally
false there at every stage level — even though the equivalent existential form
`RawDefectSharpCharacterMatchSupply` is unconditionally *true* there.  Consequently the
variable-rank campaign must target the existential form; the universal form admits no
instances wherever the campaign succeeds.

The deep class is manufactured from the unit `1 + 2^(k+1)`, which is trivial modulo
`2^(k+1)` and nontrivial modulo `2^(k+2)`, pushed through the proven exactness of the sharp
character filtration.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Roe.Labute

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## The deep dyadic unit `1 + 2^(k+1)` -/

private theorem stageResidual_two_pow_zmod_self (n : ℕ) :
    (2 : ZMod (2 ^ n)) ^ n = 0 := by
  have h := ZMod.natCast_self (2 ^ n)
  push_cast at h
  exact h

private theorem stageResidual_two_pow_succ_ne (k : ℕ) :
    (2 : ZMod (2 ^ (k + 2))) ^ (k + 1) ≠ 0 := by
  intro h0
  have hcast : ((2 ^ (k + 1) : ℕ) : ZMod (2 ^ (k + 2))) = 0 := by
    push_cast
    exact h0
  rw [ZMod.natCast_eq_zero_iff] at hcast
  have hpos : 0 < (2 : ℕ) ^ (k + 1) := pow_pos (by norm_num) (k + 1)
  have hle := Nat.le_of_dvd hpos hcast
  rw [pow_succ] at hle
  omega

/-- `1 + 2^(k+1)` is a dyadic unit. -/
theorem stageResidualDeepUnit_isUnit (k : ℕ) :
    IsUnit (1 + 2 ^ (k + 1) : ℤ_[2]) := by
  rw [PadicInt.isUnit_iff]
  have hnorm2 : ‖(2 : ℤ_[2])‖ = 2⁻¹ := by
    simpa using PadicInt.norm_p (p := 2)
  have hsmall : ‖(2 : ℤ_[2]) ^ (k + 1)‖ < 1 := by
    rw [pow_succ]
    calc ‖(2 : ℤ_[2]) ^ k * 2‖ ≤ ‖(2 : ℤ_[2]) ^ k‖ * ‖(2 : ℤ_[2])‖ := norm_mul_le _ _
      _ ≤ 1 * ‖(2 : ℤ_[2])‖ :=
          mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (norm_nonneg _)
      _ = 2⁻¹ := by rw [one_mul, hnorm2]
      _ < 1 := by norm_num
  apply le_antisymm
  · calc ‖(1 : ℤ_[2]) + 2 ^ (k + 1)‖ ≤ max ‖(1 : ℤ_[2])‖ ‖(2 : ℤ_[2]) ^ (k + 1)‖ :=
        PadicInt.nonarchimedean _ _
      _ ≤ 1 := by
          rw [norm_one]
          exact max_le le_rfl (le_of_lt hsmall)
  · have hle : (1 : ℝ) ≤ max ‖(1 : ℤ_[2]) + 2 ^ (k + 1)‖ ‖(2 : ℤ_[2]) ^ (k + 1)‖ := by
      have harg := PadicInt.nonarchimedean
        ((1 : ℤ_[2]) + 2 ^ (k + 1)) (-(2 ^ (k + 1)))
      have hsum : (1 : ℤ_[2]) + 2 ^ (k + 1) + -(2 ^ (k + 1)) = 1 := by ring
      rw [hsum, norm_one, norm_neg] at harg
      exact harg
    rcases le_max_iff.mp hle with hone | hone
    · exact hone
    · linarith [hsmall]

/-- The deep unit with value `1 + 2^(k+1)`. -/
noncomputable def stageResidualDeepUnit (k : ℕ) : ℤ_[2]ˣ :=
  (stageResidualDeepUnit_isUnit k).unit

@[simp] theorem stageResidualDeepUnit_val (k : ℕ) :
    ((stageResidualDeepUnit k : ℤ_[2]ˣ) : ℤ_[2]) = 1 + 2 ^ (k + 1) :=
  (stageResidualDeepUnit_isUnit k).unit_spec

/-- The deep unit is trivial one digit down: it lies in the sharp kernel at level `k`. -/
theorem stageResidualDeepUnit_map_eq_one (k : ℕ) :
    Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom (stageResidualDeepUnit k) = 1 := by
  apply Units.ext
  change PadicInt.toZModPow (k + 1)
    ((stageResidualDeepUnit k : ℤ_[2]ˣ) : ℤ_[2]) = 1
  rw [stageResidualDeepUnit_val, map_add, map_one, map_pow, map_ofNat,
    stageResidual_two_pow_zmod_self (k + 1), add_zero]

/-- The deep unit is nontrivial at the fresh digit. -/
theorem stageResidualDeepUnit_map_succ_ne_one (k : ℕ) :
    Units.map (PadicInt.toZModPow (k + 2)).toMonoidHom (stageResidualDeepUnit k) ≠ 1 := by
  intro h1
  have hval : PadicInt.toZModPow (k + 2)
      ((stageResidualDeepUnit k : ℤ_[2]ˣ) : ℤ_[2]) = 1 :=
    congrArg Units.val h1
  rw [stageResidualDeepUnit_val, map_add, map_one, map_pow, map_ofNat] at hval
  have hx : (2 : ZMod (2 ^ (k + 2))) ^ (k + 1) = 0 := by
    have h' : (1 : ZMod (2 ^ (k + 2))) + 2 ^ (k + 1) = 1 + 0 := by
      rw [add_zero]
      exact hval
    exact add_left_cancel h'
  exact stageResidual_two_pow_succ_ne k hx

namespace SqCyclotomicStageTuple

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-! ## A graded class with nontrivial fresh digit -/

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- When the cyclotomic character is surjective, the graded layer `Z_k` carries a class whose
sharp shadow is nontrivial: the fresh mod-`2^(k+2)` digit genuinely moves inside a level
coset.  This is the exactness of the sharp filtration read at one strict step. -/
theorem stageResidual_exists_deep_zLayer_of_surjective
    (hsurj : Function.Surjective (chiCycKTwo (K := K)))
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ z : levelQuot (maxProPQuotient 2 (GalK K)) (k + 1),
      z ∈ zLayer (maxProPQuotient 2 (GalK K)) k ∧
        sharpChiLevel (chiCycKTwo (K := K)) (k + 1) (by omega) z ≠ 1 := by
  have Hexact : SharpCharacterFiltrationExact
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) :=
    SharpCharacterFiltrationExact.of_surjective hsurj sharpUnitsFiltrationExact
  have humem : stageResidualDeepUnit k ∈
      (Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom).ker :=
    MonoidHom.mem_ker.mpr (stageResidualDeepUnit_map_eq_one k)
  rw [← Hexact.map_twoCentralSeries_eq_succKernel k hk] at humem
  obtain ⟨g, hg, hgu⟩ := humem
  have hgu' : chiCycKTwo (K := K) g = stageResidualDeepUnit k := hgu
  refine ⟨levelMk (maxProPQuotient 2 (GalK K)) (k + 1) g, ⟨g, hg, rfl⟩, ?_⟩
  rw [sharpChiLevel_levelMk, hgu']
  exact stageResidualDeepUnit_map_succ_ne_one k

/-! ## The universal refinement interface is false wherever the supply exists -/

/-- **Refutation of `RawDefectSharpCharacterRefinement`.**  Sharp admissibility forces the
finite character vector of every base point, while multiplying a defect-killing correction by
a central deep class with nontrivial fresh digit changes the vector but not the shift.  So as
soon as (i) the sharp actual-defect supply is nonempty and (ii) the layer has a class with
nontrivial sharp shadow, the universal refinement interface has no instance. -/
theorem stageResidual_not_rawDefectSharpCharacterRefinement {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} (hk : 3 ≤ k)
    (Hsupply : Nonempty (CoreHandleSharpActualDefectSupply T hk))
    (Hdeep : ∃ z : levelQuot (maxProPQuotient 2 (GalK K)) (k + 1),
      z ∈ zLayer (maxProPQuotient 2 (GalK K)) k ∧
        sharpChiLevel (chiCycKTwo (K := K)) (k + 1) (by omega) z ≠ 1) :
    ¬ RawDefectSharpCharacterRefinement T hk := by
  obtain ⟨S⟩ := Hsupply
  obtain ⟨z, hzmem, hzsharp⟩ := Hdeep
  intro Href
  have hzdepth : z ∈ lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1) :=
    lambdaImage_le_of_le (by omega) hzmem
  let v : Fin (SqCore.sqRank h) → levelQuot (maxProPQuotient 2 (GalK K)) (k + 1) :=
    fun j ↦ if j = 0 then z else 1
  have hvdepth : ∀ j, v j ∈
      lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1) := by
    intro j
    by_cases hj : j = 0
    · simpa [v, hj] using hzdepth
    · simp [v, hj]
  let c : Fin (SqCore.sqRank h) → levelQuot (maxProPQuotient 2 (GalK K)) (k + 1) :=
    fun j ↦ S.correction.correction j * v j
  have hcdepth : ∀ j, c j ∈
      lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1) :=
    fun j ↦ Subgroup.mul_mem _ (S.correction.depth j) (hvdepth j)
  have hvshift : sqCoreHandleDbarWord
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) v =
        commP z (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 1)) :=
    rawDepthShiftHom_zero_apply
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk
      ⟨z, hzdepth⟩
  have hzcomm : commP z
      (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 1)) = 1 :=
    commP_eq_one_of_mul_comm (zLayer_commute hzmem _).eq
  have hckill : stageShift
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) c =
        (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹ := by
    rw [stageShift_eq_dbarWordR2_mul_sqHandleDbarWord h k hk
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) c hcdepth]
    change sqCoreHandleDbarWord
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
      (fun j ↦ S.correction.correction j * v j) = _
    rw [sqCoreHandleDbarWord_mul h k hk
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
      S.correction.depth hvdepth, hvshift, hzcomm, mul_one]
    exact S.hitsDefect
  obtain ⟨W, hmatch⟩ := Href c hcdepth hckill
  have hforced : sharpChiLevel (chiCycKTwo (K := K)) (k + 1) (by omega)
      ((W.correction 0)⁻¹ * S.correction.correction 0) = 1 :=
    (W.differenceNeutral S.correction).sharpKernel 0
  have heq0 : sharpChiLevel (chiCycKTwo (K := K)) (k + 1) (by omega)
      (W.correction 0) =
        sharpChiLevel (chiCycKTwo (K := K)) (k + 1) (by omega)
          (S.correction.correction 0) := by
    rw [map_mul, map_inv] at hforced
    exact inv_mul_eq_one.mp hforced
  have hmatch0 := hmatch 0
  have hc0 : c 0 = S.correction.correction 0 * z := by
    show S.correction.correction 0 *
      (if (0 : Fin (SqCore.sqRank h)) = 0 then z else 1) =
        S.correction.correction 0 * z
    rw [if_pos rfl]
  rw [hc0, map_mul, heq0] at hmatch0
  have hz1 : sharpChiLevel (chiCycKTwo (K := K)) (k + 1) (by omega) z = 1 := by
    have h' : sharpChiLevel (chiCycKTwo (K := K)) (k + 1) (by omega)
        (S.correction.correction 0) *
          sharpChiLevel (chiCycKTwo (K := K)) (k + 1) (by omega) z =
        sharpChiLevel (chiCycKTwo (K := K)) (k + 1) (by omega)
          (S.correction.correction 0) * 1 := by
      rw [mul_one]
      exact hmatch0
    exact mul_left_cancel h'
  exact hzsharp hz1

end SqCyclotomicStageTuple

/-! ## Unconditional bottom-field verdicts -/

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- At the bottom field the universal sharp character refinement is false at every stage
level: the supply is a theorem and the cyclotomic character is surjective. -/
theorem stageResidual_bot_not_rawDefectSharpCharacterRefinement
    (k : ℕ) (hk : 3 ≤ k)
    (T : SqCyclotomicStageTuple (⊥ : IntermediateField ℚ_[2] ℚ̄₂) 0 k) :
    ¬ SqCyclotomicStageTuple.RawDefectSharpCharacterRefinement T hk :=
  SqCyclotomicStageTuple.stageResidual_not_rawDefectSharpCharacterRefinement hk
    (SqCyclotomicStageTuple.stageResidual_nonempty_actualDefectSupply_of_defectReachable hk
      (sqCyclotomicStageTuple_bot_all_defectReachable k hk T))
    (SqCyclotomicStageTuple.stageResidual_exists_deep_zLayer_of_surjective
      chiCycKTwo_bot_surjective k (by omega))

/-- In sharp contrast, the *existential* form of the raw-plus-character interface is an
unconditional theorem at the bottom field.  The variable-rank campaign must therefore target
`RawDefectSharpCharacterMatchSupply`, never the universal refinement. -/
theorem stageResidual_bot_rawDefectSharpCharacterMatchSupply
    (k : ℕ) (hk : 3 ≤ k)
    (T : SqCyclotomicStageTuple (⊥ : IntermediateField ℚ_[2] ℚ̄₂) 0 k) :
    SqCyclotomicStageTuple.RawDefectSharpCharacterMatchSupply T hk :=
  SqCyclotomicStageTuple.rawDefectSharpCharacterMatchSupply_iff_nonempty_actualDefectSupply.mpr
    (SqCyclotomicStageTuple.stageResidual_nonempty_actualDefectSupply_of_defectReachable hk
      (sqCyclotomicStageTuple_bot_all_defectReachable k hk T))

#print axioms stageResidualDeepUnit_isUnit
#print axioms stageResidualDeepUnit_map_eq_one
#print axioms stageResidualDeepUnit_map_succ_ne_one
#print axioms SqCyclotomicStageTuple.stageResidual_exists_deep_zLayer_of_surjective
#print axioms SqCyclotomicStageTuple.stageResidual_not_rawDefectSharpCharacterRefinement
#print axioms stageResidual_bot_not_rawDefectSharpCharacterRefinement
#print axioms stageResidual_bot_rawDefectSharpCharacterMatchSupply

end

end GQ2.Dyadic.LSquare

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStageDigitFlip

/-!
# The neutral shift span and the σ-power flip

The flip supply asks, per handle slot, for a trivial-shift correction with one nontrivial
next-precision cyclotomic digit.  This file builds the canonical candidate and reduces the
flip supply to a span statement:

* the **neutral correction subgroup** (`stageNeutralCorrections`): depth-`k-1` corrections
  with trivial mod-`2^(k+1)` cyclotomic digits at every handle coordinate, and its literal
  shift image, the **neutral shift span** (`stageNeutralShiftSpan`);
* the **σ-power flip head**: the `2^(k-2)`-th power of the canonical σ-slot base letter has
  depth `k-1` and *sharp* digit (`stageFlip_move_digit_ne_one`) — the exact-fibre σ-value is
  `5 mod 8`, so its `2^(k-2)`-th power is `1 + 2^k·odd`;
* inserting the flip head at a handle slot damages the literal shift by one bracket row
  against the partner letter.  The **neutral damage supply**
  (`SqStageNeutralDamageSupply`) asks precisely that these `2h` brackets lie in the neutral
  shift span; it implies the flip supply (`sqStageHandleDigitFlipSupply_of_neutralDamage`)
  and hence, with a coordinate derivation family, the forward presentation capstone
  (`nonempty_orientedEquiv_oddDegree_of_family_of_neutralDamage`).
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## Handle-index disequalities -/

private theorem stageDamage_hU_ne_hU {h : ℕ} {l j : Fin h} (hlj : l ≠ j) :
    SqCore.sqHandleIdxU l ≠ SqCore.sqHandleIdxU j := by
  intro hEq
  apply hlj
  apply Fin.ext
  have hv := congrArg Fin.val hEq
  rw [SqCore.sqHandleIdxU_val, SqCore.sqHandleIdxU_val] at hv
  omega

private theorem stageDamage_hV_ne_hV {h : ℕ} {l j : Fin h} (hlj : l ≠ j) :
    SqCore.sqHandleIdxV l ≠ SqCore.sqHandleIdxV j := by
  intro hEq
  apply hlj
  apply Fin.ext
  have hv := congrArg Fin.val hEq
  rw [SqCore.sqHandleIdxV_val, SqCore.sqHandleIdxV_val] at hv
  omega

private theorem stageDamage_hU_ne_hV {h : ℕ} (l j : Fin h) :
    SqCore.sqHandleIdxU l ≠ SqCore.sqHandleIdxV j := by
  intro hEq
  have hv := congrArg Fin.val hEq
  rw [SqCore.sqHandleIdxU_val, SqCore.sqHandleIdxV_val] at hv
  omega

private theorem stageDamage_hV_ne_hU {h : ℕ} (l j : Fin h) :
    SqCore.sqHandleIdxV l ≠ SqCore.sqHandleIdxU j := by
  intro hEq
  have hv := congrArg Fin.val hEq
  rw [SqCore.sqHandleIdxV_val, SqCore.sqHandleIdxU_val] at hv
  omega

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-! ## The neutral correction subgroup and its shift span -/

/-- **The neutral correction subgroup**: raw depth-`k-1` corrections whose mod-`2^(k+1)`
cyclotomic digits at every handle coordinate are trivial.  The core coordinates are
unconstrained. -/
def stageNeutralCorrections {h k : ℕ} :
    Subgroup (RawDepthCorrection (maxProPQuotient 2 (GalK K)) h k) where
  carrier := {V | (∀ j : Fin h, chiLevel (chiCycKTwo (K := K)) (k + 1)
      (V.correction (SqCore.sqHandleIdxU j)) = 1) ∧
    ∀ j : Fin h, chiLevel (chiCycKTwo (K := K)) (k + 1)
      (V.correction (SqCore.sqHandleIdxV j)) = 1}
  one_mem' := by
    refine ⟨fun j ↦ ?_, fun j ↦ ?_⟩ <;>
      rw [RawDepthCorrection.one_correction] <;> exact map_one _
  mul_mem' := by
    rintro V V' ⟨hVU, hVV⟩ ⟨hV'U, hV'V⟩
    refine ⟨fun j ↦ ?_, fun j ↦ ?_⟩
    · rw [RawDepthCorrection.mul_correction, map_mul, hVU j, hV'U j, one_mul]
    · rw [RawDepthCorrection.mul_correction, map_mul, hVV j, hV'V j, one_mul]
  inv_mem' := by
    rintro V ⟨hVU, hVV⟩
    refine ⟨fun j ↦ ?_, fun j ↦ ?_⟩
    · have hinv : (V⁻¹).correction (SqCore.sqHandleIdxU j) =
          (V.correction (SqCore.sqHandleIdxU j))⁻¹ := rfl
      rw [hinv, map_inv, hVU j, inv_one]
    · have hinv : (V⁻¹).correction (SqCore.sqHandleIdxV j) =
          (V.correction (SqCore.sqHandleIdxV j))⁻¹ := rfl
      rw [hinv, map_inv, hVV j, inv_one]

/-- **The neutral shift span**: literal core-plus-handle shift words of neutral corrections
over the canonical-lift base, as a subgroup of the ambient level quotient. -/
def stageNeutralShiftSpan {h k : ℕ} (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k) :
    Subgroup (levelQuot (maxProPQuotient 2 (GalK K)) (k + 1)) :=
  Subgroup.map (zLayer (maxProPQuotient 2 (GalK K)) k).subtype
    (Subgroup.map (rawDepthShiftHom
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk)
      stageNeutralCorrections)

/-- The word of a neutral correction lies in the neutral shift span. -/
theorem stageNeutral_word_mem_shiftSpan {h k : ℕ} {T : SqCyclotomicStageTuple K h k}
    (hk : 3 ≤ k) {V : RawDepthCorrection (maxProPQuotient 2 (GalK K)) h k}
    (hV : V ∈ stageNeutralCorrections) :
    sqCoreHandleDbarWord
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
        V.correction ∈ stageNeutralShiftSpan T hk :=
  ⟨(rawDepthShiftHom
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk) V,
    ⟨V, hV, rfl⟩, rfl⟩

/-- Every element of the neutral shift span is the word of a neutral correction. -/
theorem exists_of_mem_stageNeutralShiftSpan {h k : ℕ} {T : SqCyclotomicStageTuple K h k}
    {hk : 3 ≤ k} {s : levelQuot (maxProPQuotient 2 (GalK K)) (k + 1)}
    (hs : s ∈ stageNeutralShiftSpan T hk) :
    ∃ V ∈ (stageNeutralCorrections
        (K := K) (h := h) (k := k)),
      sqCoreHandleDbarWord
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
        V.correction = s := by
  obtain ⟨y, ⟨V, hV, rfl⟩, rfl⟩ := hs
  exact ⟨V, hV, rfl⟩

/-- The neutral shift span is contained in the raw shift span. -/
theorem stageNeutralShiftSpan_le_rawShiftSpan {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k) :
    stageNeutralShiftSpan T hk ≤ rawShiftSpan
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk := by
  rintro s ⟨y, ⟨V, _, rfl⟩, rfl⟩
  exact ⟨(rawDepthShiftHom _ hk) V, ⟨V, rfl⟩, rfl⟩

omit [FiniteDimensional ℚ_[2] ↥K] [T2Space (GalK K)] in
/-- One-coordinate corrections at core slots are neutral. -/
theorem stageNeutral_coordinate_mem {h k : ℕ}
    {i : Fin (SqCore.sqRank h)}
    (hU : ∀ l : Fin h, SqCore.sqHandleIdxU l ≠ i)
    (hV : ∀ l : Fin h, SqCore.sqHandleIdxV l ≠ i)
    (p : lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1)) :
    rawDepthCoordinateCorrection i p ∈
      stageNeutralCorrections (K := K) (h := h) (k := k) := by
  refine ⟨fun l ↦ ?_, fun l ↦ ?_⟩
  · rw [rawDepthCoordinateCorrection_apply, if_neg (hU l)]
    exact map_one _
  · rw [rawDepthCoordinateCorrection_apply, if_neg (hV l)]
    exact map_one _

/-! ## The exact next-precision digits of the canonical base -/

/-- The canonical-lift base of an exact stage tuple has the exact per-slot cyclotomic digits
at the next precision: the zLayer ambiguity of the canonical lift is sharp-neutral. -/
theorem stageFlip_chiLevel_canonLift {h k : ℕ} (T : SqCyclotomicStageTuple K h k)
    (hk : 2 ≤ k) (i : Fin (SqCore.sqRank h)) :
    chiLevel (chiCycKTwo (K := K)) (k + 1)
        (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) =
      Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom (sqStageChiTargetUnit h i) := by
  obtain ⟨x, hxchi, hxlvl⟩ := SqCyclotomicStageTuple.exists_exactChiLift T
  have hproj : GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k
      (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) =
      GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k
        (levelMk (maxProPQuotient 2 (GalK K)) (k + 1) (x i)) := by
    rw [levelProj_canonLift, levelProj_levelMk, hxlvl i]
  obtain ⟨z, hz, heq⟩ := exists_zLayer_mul (G := maxProPQuotient 2 (GalK K)) hproj
  rw [heq, map_mul, chiLevel_levelMk, hxchi i]
  obtain ⟨g, hg, rfl⟩ := hz
  rw [chiLevel_levelMk]
  have hdvd := dvd_chi_of_mem_twoCentralSeries (chiCycKTwo (K := K)) hk hg
  have h1 : Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom
      (chiCycKTwo (K := K) g) = 1 :=
    MonoidHom.mem_ker.mp (mem_ker_units_toZModPow_iff.mpr (by exact_mod_cast hdvd))
  rw [h1, one_mul]

/-- An ambient witness of the canonical base with the exact next-precision congruence. -/
theorem stageFlip_exists_canonLift_witness {h k : ℕ} (T : SqCyclotomicStageTuple K h k)
    (hk : 2 ≤ k) (i : Fin (SqCore.sqRank h)) :
    ∃ a : maxProPQuotient 2 (GalK K),
      levelMk (maxProPQuotient 2 (GalK K)) (k + 1) a =
        canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i) ∧
      (2 : ℤ_[2]) ^ (k + 1) ∣
        ((chiCycKTwo (K := K) a * (sqStageChiTargetUnit h i)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  obtain ⟨a, ha⟩ := levelMk_surjective (maxProPQuotient 2 (GalK K)) (k + 1)
    (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
  exact ⟨a, ha, dvd_of_chiLevel_eq (chiCycKTwo (K := K)) (sqStageChiTargetUnit h i) ha
    (stageFlip_chiLevel_canonLift T hk i)⟩

/-! ## The σ-power flip head -/

/-- The flip head has depth `k-1`. -/
theorem stageFlip_move_depth {h k : ℕ} (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k) :
    (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 2) ∈
      lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1) := by
  have hmem := pow_two_pow_mem_lambdaImage
    (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) (k - 2)
  rwa [show 1 + (k - 2) = k - 1 by omega] at hmem

/-- **The flip head has a sharp digit**: the σ-slot target is `5 mod 8`, so the
`2^(k-2)`-th power of the canonical σ base letter has cyclotomic value `1 + 2^k·odd`,
which is nontrivial modulo `2^(k+1)`. -/
theorem stageFlip_move_digit_ne_one {h k : ℕ} (T : SqCyclotomicStageTuple K h k)
    (hk : 3 ≤ k) :
    chiLevel (chiCycKTwo (K := K)) (k + 1)
      ((canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 2)) ≠ 1 := by
  obtain ⟨a, ha, hdvd⟩ := stageFlip_exists_canonLift_witness T (by omega) 0
  rw [sqStageChiTargetUnit_zero] at hdvd
  have hSval8 : PadicInt.toZModPow 3 ((GQ2.Roe.SvalUnit : ℤ_[2]ˣ) : ℤ_[2]) = 5 := by
    simpa [chiTargetR2, chiTargetUnitsR2] using chiTargetR2_three 0
  obtain ⟨d, hd, hdodd⟩ := sharp_move hk hSval8
    (dvd_trans (pow_dvd_pow 2 (by omega : k ≤ k + 1)) hdvd)
  intro h1
  have hdig : chiLevel (chiCycKTwo (K := K)) (k + 1)
      ((canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 2)) =
      Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom
        (chiCycKTwo (K := K) a ^ 2 ^ (k - 2)) := by
    rw [← ha, ← map_pow, chiLevel_levelMk, map_pow]
  rw [hdig] at h1
  have hker : ((2 : ℕ) : ℤ_[2]) ^ (k + 1) ∣
      ((chiCycKTwo (K := K) a ^ 2 ^ (k - 2) : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
    mem_ker_units_toZModPow_iff.mp (MonoidHom.mem_ker.mpr h1)
  have hker2 : (2 : ℤ_[2]) ^ (k + 1) ∣
      ((chiCycKTwo (K := K) a ^ 2 ^ (k - 2) : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    exact_mod_cast hker
  rw [hd] at hker2
  obtain ⟨e, he⟩ := hker2
  apply hdodd
  refine ⟨e, ?_⟩
  have h2k : (2 : ℤ_[2]) ^ k ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℤ_[2]) ≠ 0)
  apply mul_left_cancel₀ h2k
  rw [he, pow_succ]
  ring

/-! ## The neutral damage supply -/

/-- **The neutral damage supply.**  Inserting the σ-power flip head at a handle slot damages
the literal shift by exactly one bracket row against the partner letter; the supply asks
that these `2h` damage brackets lie in the neutral shift span.  This is the sole remaining
content of the handle-digit flip supply. -/
def SqStageNeutralDamageSupply {h k : ℕ} (T : SqCyclotomicStageTuple K h k)
    (hk : 3 ≤ k) : Prop :=
  ∀ j : Fin h,
    commP ((canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 2))
        (canonLift (maxProPQuotient 2 (GalK K)) k
          (T.generators (SqCore.sqHandleIdxV j))) ∈ stageNeutralShiftSpan T hk ∧
    commP ((canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 2))
        (canonLift (maxProPQuotient 2 (GalK K)) k
          (T.generators (SqCore.sqHandleIdxU j))) ∈ stageNeutralShiftSpan T hk

/-- At handle count zero the neutral damage supply is vacuous. -/
theorem sqStageNeutralDamageSupply_of_rank_zero {k : ℕ}
    (T : SqCyclotomicStageTuple K 0 k) (hk : 3 ≤ k) :
    SqStageNeutralDamageSupply T hk :=
  fun j ↦ j.elim0

/-- **The flip supply from the neutral damage supply.**  The flip at a handle slot is the
σ-power head at that slot times the inverse of a neutral realization of its damage: the
literal shift words cancel, the head contributes the sharp digit at the slot, and the
neutral compensator contributes no handle digit at all. -/
theorem sqStageHandleDigitFlipSupply_of_neutralDamage {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} (hk : 3 ≤ k)
    (Hdam : SqStageNeutralDamageSupply T hk) :
    SqStageHandleDigitFlipSupply T := by
  constructor
  · -- flips at `U` slots
    intro j
    obtain ⟨N, hN, hNword⟩ := exists_of_mem_stageNeutralShiftSpan (Hdam j).1
    refine ⟨rawDepthCoordinateCorrection (SqCore.sqHandleIdxU j)
      ⟨_, stageFlip_move_depth T hk⟩ * N⁻¹, ?_, ?_, ?_, ?_⟩
    · -- the shift words cancel
      have h1 : (rawDepthShiftHom
          (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk)
          (rawDepthCoordinateCorrection (SqCore.sqHandleIdxU j)
            ⟨_, stageFlip_move_depth T hk⟩ * N⁻¹) = 1 := by
        rw [map_mul, map_inv, mul_inv_eq_one]
        apply Subtype.ext
        rw [rawDepthShiftHom_handleU_apply
          (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk j
          ⟨_, stageFlip_move_depth T hk⟩]
        exact hNword.symm
      exact congrArg Subtype.val h1
    · -- sharp digit at the slot
      have hcorr : (rawDepthCoordinateCorrection (SqCore.sqHandleIdxU j)
          ⟨_, stageFlip_move_depth T hk⟩ * N⁻¹).correction (SqCore.sqHandleIdxU j) =
          (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 2) *
            (N.correction (SqCore.sqHandleIdxU j))⁻¹ := by
        rw [RawDepthCorrection.mul_correction, rawDepthCoordinateCorrection_apply,
          if_pos rfl]
        rfl
      rw [hcorr, map_mul, map_inv, hN.1 j, inv_one, mul_one]
      exact stageFlip_move_digit_ne_one T hk
    · -- other `U` digits are trivial
      intro l hlj
      have hcorr : (rawDepthCoordinateCorrection (SqCore.sqHandleIdxU j)
          ⟨_, stageFlip_move_depth T hk⟩ * N⁻¹).correction (SqCore.sqHandleIdxU l) =
          1 * (N.correction (SqCore.sqHandleIdxU l))⁻¹ := by
        rw [RawDepthCorrection.mul_correction, rawDepthCoordinateCorrection_apply,
          if_neg (stageDamage_hU_ne_hU hlj)]
        rfl
      rw [hcorr, map_mul, map_inv, map_one, hN.1 l, inv_one, mul_one]
    · -- all `V` digits are trivial
      intro l
      have hcorr : (rawDepthCoordinateCorrection (SqCore.sqHandleIdxU j)
          ⟨_, stageFlip_move_depth T hk⟩ * N⁻¹).correction (SqCore.sqHandleIdxV l) =
          1 * (N.correction (SqCore.sqHandleIdxV l))⁻¹ := by
        rw [RawDepthCorrection.mul_correction, rawDepthCoordinateCorrection_apply,
          if_neg (stageDamage_hV_ne_hU l j)]
        rfl
      rw [hcorr, map_mul, map_inv, map_one, hN.2 l, inv_one, mul_one]
  · -- flips at `V` slots
    intro j
    obtain ⟨N, hN, hNword⟩ := exists_of_mem_stageNeutralShiftSpan (Hdam j).2
    refine ⟨rawDepthCoordinateCorrection (SqCore.sqHandleIdxV j)
      ⟨_, stageFlip_move_depth T hk⟩ * N⁻¹, ?_, ?_, ?_, ?_⟩
    · have h1 : (rawDepthShiftHom
          (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk)
          (rawDepthCoordinateCorrection (SqCore.sqHandleIdxV j)
            ⟨_, stageFlip_move_depth T hk⟩ * N⁻¹) = 1 := by
        rw [map_mul, map_inv, mul_inv_eq_one]
        apply Subtype.ext
        rw [rawDepthShiftHom_handleV_apply
          (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk j
          ⟨_, stageFlip_move_depth T hk⟩]
        exact hNword.symm
      exact congrArg Subtype.val h1
    · have hcorr : (rawDepthCoordinateCorrection (SqCore.sqHandleIdxV j)
          ⟨_, stageFlip_move_depth T hk⟩ * N⁻¹).correction (SqCore.sqHandleIdxV j) =
          (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 2) *
            (N.correction (SqCore.sqHandleIdxV j))⁻¹ := by
        rw [RawDepthCorrection.mul_correction, rawDepthCoordinateCorrection_apply,
          if_pos rfl]
        rfl
      rw [hcorr, map_mul, map_inv, hN.2 j, inv_one, mul_one]
      exact stageFlip_move_digit_ne_one T hk
    · intro l hlj
      have hcorr : (rawDepthCoordinateCorrection (SqCore.sqHandleIdxV j)
          ⟨_, stageFlip_move_depth T hk⟩ * N⁻¹).correction (SqCore.sqHandleIdxV l) =
          1 * (N.correction (SqCore.sqHandleIdxV l))⁻¹ := by
        rw [RawDepthCorrection.mul_correction, rawDepthCoordinateCorrection_apply,
          if_neg (stageDamage_hV_ne_hV hlj)]
        rfl
      rw [hcorr, map_mul, map_inv, map_one, hN.2 l, inv_one, mul_one]
    · intro l
      have hcorr : (rawDepthCoordinateCorrection (SqCore.sqHandleIdxV j)
          ⟨_, stageFlip_move_depth T hk⟩ * N⁻¹).correction (SqCore.sqHandleIdxU l) =
          1 * (N.correction (SqCore.sqHandleIdxU l))⁻¹ := by
        rw [RawDepthCorrection.mul_correction, rawDepthCoordinateCorrection_apply,
          if_neg (stageDamage_hU_ne_hV l j)]
        rfl
      rw [hcorr, map_mul, map_inv, map_one, hN.1 l, inv_one, mul_one]

/-! ## Assembly -/

/-- **The kernel-adapted supply from a family and a neutral damage supply at every stage.** -/
theorem sqKernelAdaptedDefectSupply_of_family_of_neutralDamage {h : ℕ}
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : SqCyclotomicStageTuple K h k,
      Nonempty (SqStageCoordinateDerivationFamily T))
    (Hdam : ∀ (k : ℕ) (hk : 3 ≤ k), ∀ T : SqCyclotomicStageTuple K h k,
      SqStageNeutralDamageSupply T hk) :
    SqKernelAdaptedDefectSupply K h :=
  sqKernelAdaptedDefectSupply_of_family_of_flipSupply Hfam
    (fun k hk T ↦ sqStageHandleDigitFlipSupply_of_neutralDamage hk (Hdam k hk T))

/-- **The forward presentation theorem over the family and the neutral damage supply.** -/
theorem nonempty_orientedEquiv_oddDegree_of_family_of_neutralDamage
    {Rec : LocalReciprocity} (B : MarkedRecip Rec K)
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (Hfam : ∀ (k : ℕ), 3 ≤ k →
      ∀ T : SqCyclotomicStageTuple K ((Module.finrank ℚ_[2] K - 1) / 2) k,
        Nonempty (SqStageCoordinateDerivationFamily T))
    (Hdam : ∀ (k : ℕ) (hk : 3 ≤ k),
      ∀ T : SqCyclotomicStageTuple K ((Module.finrank ℚ_[2] K - 1) / 2) k,
        SqStageNeutralDamageSupply T hk) :
    Nonempty (OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2))
      (chiCycKTwo (K := K))) :=
  nonempty_orientedEquiv_oddDegree_of_kernelAdaptedSupply B hodd
    (sqKernelAdaptedDefectSupply_of_family_of_neutralDamage Hfam Hdam)

#print axioms stageFlip_chiLevel_canonLift
#print axioms stageFlip_move_digit_ne_one
#print axioms sqStageHandleDigitFlipSupply_of_neutralDamage
#print axioms sqKernelAdaptedDefectSupply_of_family_of_neutralDamage
#print axioms nonempty_orientedEquiv_oddDegree_of_family_of_neutralDamage

end

end GQ2.Dyadic.LSquare

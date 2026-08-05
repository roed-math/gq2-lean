/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteKernelAdaptedSupply

/-!
# Model calibration of the stage functional calculus

Two consistency certificates for the coordinate-derivation route:

* **The model carries coordinate derivations at every stage.**  `sqDerivModel` extends the
  cubic `sqDerivFour` of the raw-span obstruction file to every precision: for each offset
  vector, a continuous homomorphism `D_sq(h) → WL N` with base the mod-`2^N` shadow of the
  canonical square orientation.  Consequently the tail obstruction holds at **every** level
  `k ≥ 3` of the free model (`sqCore_rawTail_not_mem_rawShiftSpan_all`), extending the
  in-tree cubic refutation: no forward proof can place a non-twisted tail in the literal raw
  shift span at any stage.

* **The family premise is implied by the conclusion.**  An oriented equivalence of the field
  group with the model transports the model's coordinate derivations to a
  `SqStageCoordinateDerivationFamily` on the transported stage tuple at every level
  (`sqStageFamilyOfOrientedEquiv`).  The reduction of the kernel-adapted supply to the
  family is therefore exactly calibrated: the family exists whenever the presentation
  theorem holds, so no hidden strengthening has been smuggled into the reduction.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.FoxH

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## The finite lift group is pro-2 at every precision -/

private theorem stageModel_isPGroup_WL {N : ℕ} (hN : 1 ≤ N) : IsPGroup 2 (WL N) := by
  have hcard : Nat.card (WL N) = 2 ^ (N + (N - 1)) := by
    have h1 : Nat.card (WL N) = Nat.card (ZMod (2 ^ N)) * Nat.card ((ZMod (2 ^ N))ˣ) := by
      rw [Nat.card_congr (WordLift.equivProd (A := ZMod (2 ^ N)) (C := (ZMod (2 ^ N))ˣ)),
        Nat.card_prod]
    have h2 : Nat.card (ZMod (2 ^ N)) = 2 ^ N := by
      haveI : NeZero (2 ^ N) := ⟨by positivity⟩
      simp [Nat.card_eq_fintype_card]
    have h3 : Nat.card ((ZMod (2 ^ N))ˣ) = 2 ^ (N - 1) := by
      haveI : NeZero (2 ^ N) := ⟨by positivity⟩
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow Nat.prime_two (by omega)]
      simp
    rw [h1, h2, h3, ← pow_add]
  exact IsPGroup.of_card hcard

private theorem stageModel_isProP_WL {N : ℕ} (hN : 1 ≤ N) : IsProP 2 (WL N) :=
  isProP_of_isPGroup (stageModel_isPGroup_WL hN)

/-! ## The model marking at the canonical targets -/

/-- The canonical orientation values of the model generators are the per-slot targets. -/
theorem chiSq_sqGen_eq_target (h : ℕ) (i : Fin (SqCore.sqRank h)) :
    SqCore.chiSq h (SqCore.sqGen h i) = sqStageChiTargetUnit h i := by
  rcases SqCore.sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [sqStageChiTargetUnit_zero, show SqCore.sqGen h 0 = SqCore.dsqSigma h from rfl]
    exact SqCore.chiSq_sigma h
  · rw [sqStageChiTargetUnit_one, show SqCore.sqGen h 1 = SqCore.dsqX0 h from rfl]
    exact SqCore.chiSq_x0 h
  · rw [sqStageChiTargetUnit_two, show SqCore.sqGen h 2 = SqCore.dsqX1 h from rfl]
    exact SqCore.chiSq_x1 h
  · rw [sqStageChiTargetUnit_handleU]
    exact SqCore.chiSq_handleU h j
  · rw [sqStageChiTargetUnit_handleV]
    exact SqCore.chiSq_handleV h j

/-- The word-lift marking of the model at an offset vector. -/
private def sqStageModelMark (h : ℕ) (v : Fin (SqCore.sqRank h) → ℤ_[2])
    (i : Fin (SqCore.sqRank h)) : WordLift ℤ_[2] ℤ_[2]ˣ :=
  ⟨v i, sqStageChiTargetUnit h i⟩

private theorem sqStageModelMark_relWord (h : ℕ) (v : Fin (SqCore.sqRank h) → ℤ_[2]) :
    SqCore.sqRelWord (sqStageModelMark h v) = 1 :=
  sqStageChiTarget_relWord_wordLift h v

/-! ## The model coordinate derivation at every precision -/

/-- **The model coordinate derivation.**  The continuous homomorphism `D_sq(h) → WL N`
carrying the `i`-th generator to the lift with offset `v i` over the canonical orientation.
It exists at every precision because the improved word is universally closed at the
canonical targets. -/
def sqDerivModel (h : ℕ) {N : ℕ} (hN : 1 ≤ N) (v : Fin (SqCore.sqRank h) → ℤ_[2]) :
    ContinuousMonoidHom (SqCore.DSq h : Type) (WL N) :=
  SqCore.sqLiftHom h (stageModel_isProP_WL hN)
    (fun i ↦ redWL N (sqStageModelMark h v i)) (by
      rw [← SqCore.map_sqRelWord, sqStageModelMark_relWord, map_one])

@[simp] theorem sqDerivModel_sqGen (h : ℕ) {N : ℕ} (hN : 1 ≤ N)
    (v : Fin (SqCore.sqRank h) → ℤ_[2]) (i : Fin (SqCore.sqRank h)) :
    sqDerivModel h hN v (SqCore.sqGen h i) = redWL N (sqStageModelMark h v i) :=
  SqCore.sqLiftHom_gen _ _ _ _ i

/-- The base component of the model derivation is the mod-`2^N` shadow of the canonical
square orientation. -/
theorem sqDerivModel_base (h : ℕ) {N : ℕ} (hN : 1 ≤ N)
    (v : Fin (SqCore.sqRank h) → ℤ_[2]) (a : (SqCore.DSq h : Type)) :
    (sqDerivModel h hN v a).g =
      Units.map (PadicInt.toZModPow N).toMonoidHom (SqCore.chiSq h a) := by
  let baseMap : ContinuousMonoidHom (WL N) ((ZMod (2 ^ N))ˣ) :=
    { toFun := fun p ↦ p.g
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      continuous_toFun := continuous_of_discreteTopology }
  haveI := discreteTopology_levelQuot (SqCore.DSq h : Type) (dsqFinsetTopGen h)
    (SqCore.isProP_DSq h) N
  let targetMap : ContinuousMonoidHom (SqCore.DSq h : Type) ((ZMod (2 ^ N))ˣ) :=
    { toMonoidHom := (chiLevel (SqCore.chiSq h) N).comp (levelMk (SqCore.DSq h : Type) N)
      continuous_toFun := (continuous_of_discreteTopology
        (f := ⇑(chiLevel (SqCore.chiSq h) N))).comp
          (continuous_levelMk (SqCore.DSq h : Type) N) }
  have heq : baseMap.comp (sqDerivModel h hN v) = targetMap := by
    apply SqCore.dsq_hom_ext
    intro i
    change (sqDerivModel h hN v (SqCore.sqGen h i)).g =
      chiLevel (SqCore.chiSq h) N
        (levelMk (SqCore.DSq h : Type) N (SqCore.sqGen h i))
    rw [sqDerivModel_sqGen, chiLevel_levelMk, redWL_g, chiSq_sqGen_eq_target]
    rfl
  have htarget : targetMap a =
      Units.map (PadicInt.toZModPow N).toMonoidHom (SqCore.chiSq h a) := by
    show chiLevel (SqCore.chiSq h) N (levelMk (SqCore.DSq h : Type) N a) = _
    rw [chiLevel_levelMk]
  rw [← htarget]
  exact DFunLike.congr_fun heq a

/-- The model derivation is χ-shadowed over the canonical orientation. -/
theorem sqDerivModel_isChiShadow (h : ℕ) {N : ℕ} (hN : 1 ≤ N)
    (v : Fin (SqCore.sqRank h) → ℤ_[2]) :
    IsChiShadowDeriv (SqCore.chiSq h) (sqDerivModel h hN v) :=
  fun a ↦ sqDerivModel_base h hN v a

/-- The offset of the model derivation at a generator. -/
theorem sqDerivModel_u (h : ℕ) {N : ℕ} (hN : 1 ≤ N)
    (v : Fin (SqCore.sqRank h) → ℤ_[2]) (i : Fin (SqCore.sqRank h)) :
    (sqDerivModel h hN v (SqCore.sqGen h i)).u = PadicInt.toZModPow N (v i) := by
  rw [sqDerivModel_sqGen]
  rfl

/-- The diagonal offset of the coordinate vector is odd. -/
theorem sqDerivModel_single_diag_odd (h : ℕ) {N : ℕ} (hN : 1 ≤ N)
    (i₀ : Fin (SqCore.sqRank h)) :
    ¬ (2 : ZMod (2 ^ N)) ∣
      (sqDerivModel h hN (Pi.single i₀ 1) (SqCore.sqGen h i₀)).u := by
  rw [sqDerivModel_u, Pi.single_eq_same]
  intro hdvd
  have h1 : (2 : ZMod (2 ^ N)) ^ 1 ∣ PadicInt.toZModPow N 1 := by rwa [pow_one]
  have h2 := (two_pow_dvd_toZModPow_iff (N := N) (j := 1) hN).mp h1
  rw [pow_one] at h2
  have h3 : ¬ (2 : ℤ_[2]) ∣ (1 : ℤ_[2]) := by
    simpa using two_not_dvd_one_add_two_mul 0
  exact h3 h2

/-- The off-diagonal offsets of the coordinate vector are even. -/
theorem sqDerivModel_single_off_even (h : ℕ) {N : ℕ} (hN : 1 ≤ N)
    (i₀ j : Fin (SqCore.sqRank h)) (hji : j ≠ i₀) :
    (2 : ZMod (2 ^ N)) ∣
      (sqDerivModel h hN (Pi.single i₀ 1) (SqCore.sqGen h j)).u := by
  rw [sqDerivModel_u, Pi.single_eq_of_ne hji, map_zero]
  exact dvd_zero _

/-! ## The tail obstruction at every stage of the model -/

/-- **The all-stage tail obstruction.**  At the free model, no non-twisted tail lies in the
literal raw shift span at any level `k ≥ 3`.  This extends the cubic refutation
`sqCore_sigma_rawTail_not_mem_rawShiftSpan` to every stage and every non-twisted slot: a
forward argument must treat the tail factor of the specific defect, never the tail atoms
themselves. -/
theorem sqCore_rawTail_not_mem_rawShiftSpan_all (h : ℕ) {k : ℕ} (hk : 3 ≤ k)
    (i₀ : Fin (SqCore.sqRank h)) (hi₀ : i₀ ≠ 2) :
    rawMarkedBase (SqCore.sqGen h) k i₀ ^ 2 ^ (k - 1) ∉
      rawShiftSpan (rawMarkedBase (SqCore.sqGen h) k) hk :=
  stageDeriv_rawTail_not_mem_rawShiftSpan (G := (SqCore.DSq h : Type)) hk
    (sqDerivModel_isChiShadow h (by omega) (Pi.single i₀ 1))
    (SqCore.sqGen h) (chiSq_sqGen_eq_target h) i₀ hi₀
    (sqDerivModel_single_diag_odd h (by omega) i₀)

/-! ## Transport along an oriented equivalence: the family premise is exactly calibrated -/

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-- **The family from the conclusion.**  An oriented equivalence with the model transports
the model coordinate derivations to a coordinate derivation family on the transported stage
tuple at every level.  Hence the family premise of the kernel-adapted supply reduction is
implied by the forward presentation theorem itself: the reduction is exactly calibrated. -/
def sqStageFamilyOfOrientedEquiv {h k : ℕ}
    (e : OrientedContinuousMulEquiv (SqCore.chiSq h) (chiCycKTwo (K := K))) :
    SqStageCoordinateDerivationFamily
      (SqCyclotomicStageTuple.ofOrientedEquiv (K := K) (k := k) e) where
  lifts i := SqCyclotomicStageTuple.orientedCarrier e (SqCore.sqGen h i)
  lifts_chi i := (e.2 (SqCore.sqGen h i)).trans (chiSq_sqGen_eq_target h i)
  lifts_level _ := rfl
  deriv i₀ _ := (sqDerivModel h (by omega : 1 ≤ k + 1) (Pi.single i₀ 1)).comp
    ⟨(SqCyclotomicStageTuple.orientedCarrier e).symm.toMonoidHom,
      (SqCyclotomicStageTuple.orientedCarrier e).symm.continuous_toFun⟩
  deriv_base i₀ hi₀ g := by
    show (sqDerivModel h (by omega : 1 ≤ k + 1) (Pi.single i₀ 1)
        ((SqCyclotomicStageTuple.orientedCarrier e).symm g)).g = _
    rw [sqDerivModel_base]
    have h1 : chiCycKTwo (K := K) (SqCyclotomicStageTuple.orientedCarrier e
        ((SqCyclotomicStageTuple.orientedCarrier e).symm g)) =
        SqCore.chiSq h ((SqCyclotomicStageTuple.orientedCarrier e).symm g) :=
      e.2 ((SqCyclotomicStageTuple.orientedCarrier e).symm g)
    rw [ContinuousMulEquiv.apply_symm_apply] at h1
    rw [← h1]
  deriv_diag i₀ hi₀ := by
    show ¬ (2 : ZMod (2 ^ (k + 1))) ∣
      (sqDerivModel h (by omega : 1 ≤ k + 1) (Pi.single i₀ 1)
        ((SqCyclotomicStageTuple.orientedCarrier e).symm
          (SqCyclotomicStageTuple.orientedCarrier e (SqCore.sqGen h i₀)))).u
    rw [ContinuousMulEquiv.symm_apply_apply]
    exact sqDerivModel_single_diag_odd h (by omega) i₀
  deriv_off i₀ hi₀ j _ hji := by
    show (2 : ZMod (2 ^ (k + 1))) ∣
      (sqDerivModel h (by omega : 1 ≤ k + 1) (Pi.single i₀ 1)
        ((SqCyclotomicStageTuple.orientedCarrier e).symm
          (SqCyclotomicStageTuple.orientedCarrier e (SqCore.sqGen h j)))).u
    rw [ContinuousMulEquiv.symm_apply_apply]
    exact sqDerivModel_single_off_even h (by omega) i₀ j hji

/-- Nonemptiness form of the transported family, for direct consumption against the
`Nonempty`-quantified reduction hypotheses. -/
theorem nonempty_sqStageCoordinateDerivationFamily_of_orientedEquiv {h k : ℕ}
    (e : OrientedContinuousMulEquiv (SqCore.chiSq h) (chiCycKTwo (K := K))) :
    Nonempty (SqStageCoordinateDerivationFamily
      (SqCyclotomicStageTuple.ofOrientedEquiv (K := K) (k := k) e)) :=
  ⟨sqStageFamilyOfOrientedEquiv e⟩

#print axioms chiSq_sqGen_eq_target
#print axioms sqDerivModel
#print axioms sqDerivModel_base
#print axioms sqDerivModel_isChiShadow
#print axioms sqDerivModel_single_diag_odd
#print axioms sqDerivModel_single_off_even
#print axioms sqCore_rawTail_not_mem_rawShiftSpan_all
#print axioms sqStageFamilyOfOrientedEquiv
#print axioms nonempty_sqStageCoordinateDerivationFamily_of_orientedEquiv

end

end GQ2.Dyadic.LSquare

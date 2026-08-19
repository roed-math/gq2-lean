/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralParityQuotient

/-!
# The class-seven neutral and parity-interaction ranks

The exact parity quotient from W292 turns its cardinal product into a dimension identity:
the standard neutral-target rank plus the standard parity-interaction rank is exactly two.
The compact neutral-image transpose rank is bounded by the neutral-target rank itself.

No value is assigned to either summand here.  The remaining finite problem is to compute the
standard parity-interaction rank and the compact connecting image inside the resulting quotient.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralParityRank

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralTargetRank
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralCoordinateBound
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralRankBound
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralParityQuotient
open GQ2.Dyadic.Instances.MpcBalancedNeutralityParity
open GQ2.FoxH
open scoped IsMulCommutative

private abbrev ParityPlane :=
  Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

private abbrev StandardParityInteractionRange : Subgroup ParityPlane :=
  (oneHandleBalancedCoreNeutralityParityRow
    oneHandleStandardBalancedPoint 6 (by omega)).range

private abbrev NeutralTarget := Additive OneHandleC7StandardNeutralityCokernel

private theorem zmodTwoMultiplicative_sq
    (u : Multiplicative (ZMod 2)) : u ^ 2 = 1 := by
  rw [← ofAdd_toAdd u, ← ofAdd_nsmul]
  apply congrArg ofAdd
  generalize toAdd u = a
  revert a
  decide

private theorem parityPlane_add_self (v : Additive ParityPlane) :
    v + v = 0 := by
  apply Additive.toMul.injective
  change v.toMul * v.toMul = 1
  rcases v.toMul with ⟨u, w⟩
  apply Prod.ext
  · change u * u = 1
    simpa [pow_two] using zmodTwoMultiplicative_sq u
  · change w * w = 1
    simpa [pow_two] using zmodTwoMultiplicative_sq w

private theorem parityInteractionRange_add_self
    (v : Additive StandardParityInteractionRange) : v + v = 0 := by
  apply Subtype.ext
  exact parityPlane_add_self (Additive.ofMul v.1)

/-- The F2-dimension of the standard parity-interaction range. -/
noncomputable def oneHandleC7StandardParityInteractionRank : ℕ := by
  letI : Module (ZMod 2) (Additive StandardParityInteractionRange) :=
    AddCommGroup.zmodModule (fun v ↦ by
      rw [two_nsmul]
      exact parityInteractionRange_add_self v)
  exact Module.finrank (ZMod 2) (Additive StandardParityInteractionRange)

theorem natCard_standardParityInteractionRange_eq_pow_rank :
    Nat.card StandardParityInteractionRange =
      2 ^ oneHandleC7StandardParityInteractionRank := by
  letI : Module (ZMod 2) (Additive StandardParityInteractionRange) :=
    AddCommGroup.zmodModule (fun v ↦ by
      rw [two_nsmul]
      exact parityInteractionRange_add_self v)
  letI : FiniteDimensional (ZMod 2)
      (Additive StandardParityInteractionRange) := Module.Finite.of_finite
  change Nat.card (Additive StandardParityInteractionRange) =
    2 ^ Module.finrank (ZMod 2) (Additive StandardParityInteractionRange)
  simpa [ZMod.card] using
    (Module.natCard_eq_pow_finrank
      (K := ZMod 2) (V := Additive StandardParityInteractionRange))

theorem standardNeutralityFinrank_add_parityInteractionRank :
    oneHandleC7StandardNeutralityFinrank +
      oneHandleC7StandardParityInteractionRank = 2 := by
  have hcard := natCard_standardNeutrality_mul_parityInteraction_eq_four
  rw [natCard_oneHandleC7StandardNeutralityCokernel_eq_pow_finrank,
    natCard_standardParityInteractionRange_eq_pow_rank, ← pow_add] at hcard
  have hpow : 2 ^ (oneHandleC7StandardNeutralityFinrank +
      oneHandleC7StandardParityInteractionRank) = 2 ^ 2 := by
    norm_num at hcard ⊢
    exact hcard
  exact (Nat.pow_right_injective (a := 2) (by omega)).eq_iff.mp hpow

theorem neutralImageTransposeRank_le_standardNeutralityFinrank :
    oneHandleCompactNeutralImageTransposeRank ≤
      oneHandleC7StandardNeutralityFinrank := by
  letI : Finite oneHandleCompactNeutralImageTranspose.range :=
    Finite.of_surjective _
      oneHandleCompactNeutralImageTranspose.rangeRestrict_surjective
  have hcardRange : Nat.card oneHandleCompactNeutralImageTranspose.range ≤
      Nat.card (ElemDual NeutralTarget) :=
    Nat.card_le_card_of_surjective
      oneHandleCompactNeutralImageTranspose.rangeRestrict
      oneHandleCompactNeutralImageTranspose.rangeRestrict_surjective
  have hcardDual : Nat.card (ElemDual NeutralTarget) =
      Nat.card NeutralTarget :=
    card_elemDual oneHandleC7StandardNeutralityCokernel_add_self
  have hpow : 2 ^ oneHandleCompactNeutralImageTransposeRank ≤
      2 ^ oneHandleC7StandardNeutralityFinrank := by
    rw [← neutralImageTranspose_rangeCard_eq_pow_rank,
      ← natCard_oneHandleC7StandardNeutralityCokernel_eq_pow_finrank]
    exact hcardRange.trans hcardDual.le
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow

#print axioms oneHandleC7StandardParityInteractionRank
#print axioms natCard_standardParityInteractionRange_eq_pow_rank
#print axioms standardNeutralityFinrank_add_parityInteractionRank
#print axioms neutralImageTransposeRank_le_standardNeutralityFinrank

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralParityRank

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralMaximalRank

/-!
# The parity plane covered by compact class-seven corrections

Pull the compact neutral connecting range back through the standard parity factor.  The
resulting subgroup of `(ZMod 2)^2` is the exact finite object that remains to be computed.

It fills the parity plane exactly when the neutral connecting map is surjective.  Equivalently,
the compact-image rank plus the standard parity-interaction rank is two.  When this concrete
subgroup is top, the full W6 correction follows.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenCoveredParity

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingHom
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactFullSolution
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralConnecting
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralTargetRank
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralCoordinateBound
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralParityRank
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralMaximalRank
open GQ2.FoxH
open scoped IsMulCommutative

private abbrev ParityPlane :=
  Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

private abbrev NeutralTarget := Additive OneHandleC7StandardNeutralityCokernel

/-- Parity vectors whose neutral class is realized by a compact correction. -/
def oneHandleC7StandardCoveredParity : Subgroup ParityPlane :=
  Subgroup.comap oneHandleC7StandardNeutralityParityFactor
    oneHandleCompactNeutralConnectingHom.range

theorem oneHandleC7StandardCoveredParity_eq_top_iff :
    oneHandleC7StandardCoveredParity = ⊤ ↔
      oneHandleCompactNeutralConnectingHom.range = ⊤ := by
  constructor
  · intro hcover
    apply top_unique
    intro x _
    obtain ⟨p, hp⟩ := oneHandleC7StandardNeutralityParityFactor_surjective x
    have hptop : p ∈ oneHandleC7StandardCoveredParity := by
      rw [hcover]
      exact Subgroup.mem_top p
    change oneHandleC7StandardNeutralityParityFactor p ∈
      oneHandleCompactNeutralConnectingHom.range at hptop
    simpa [hp] using hptop
  · intro hrange
    apply top_unique
    intro p _
    change oneHandleC7StandardNeutralityParityFactor p ∈
      oneHandleCompactNeutralConnectingHom.range
    rw [hrange]
    exact Subgroup.mem_top _

theorem neutralImageTransposeRank_eq_standardNeutralityFinrank_iff_range_top :
    oneHandleCompactNeutralImageTransposeRank =
        oneHandleC7StandardNeutralityFinrank ↔
      oneHandleCompactNeutralConnectingHom.range = ⊤ := by
  constructor
  · intro hrank
    apply top_unique
    intro x _
    have hvan :=
      neutralTargetTransposeVanishing_of_rank_eq_standardNeutralityFinrank x hrank
    have hmem :=
      (mem_compactNeutralConnectingValues_iff_transposeVanishing x).mpr hvan
    obtain ⟨K, hK⟩ :=
      (mem_compactNeutralConnectingValues_iff x).mp hmem
    exact ⟨K, hK⟩
  · intro hrange
    have hinj : Function.Injective oneHandleCompactNeutralImageTranspose := by
      intro ell₁ ell₂ hell
      apply AddMonoidHom.ext
      intro x
      have hxmem : x.toMul ∈ oneHandleCompactNeutralConnectingHom.range := by
        rw [hrange]
        exact Subgroup.mem_top _
      obtain ⟨K, hK⟩ := hxmem
      have heval := DFunLike.congr_fun hell (Additive.ofMul K)
      change ell₁ (Additive.ofMul (oneHandleCompactNeutralConnectingHom K)) =
        ell₂ (Additive.ofMul (oneHandleCompactNeutralConnectingHom K)) at heval
      have hx : Additive.ofMul (oneHandleCompactNeutralConnectingHom K) = x := by
        apply Additive.toMul.injective
        exact hK
      rw [hx] at heval
      exact heval
    letI : Finite oneHandleCompactNeutralImageTranspose.range :=
      Finite.of_surjective _
        oneHandleCompactNeutralImageTranspose.rangeRestrict_surjective
    have hbij : Function.Bijective
        oneHandleCompactNeutralImageTranspose.rangeRestrict :=
      ⟨fun x y hxy ↦ hinj (Subtype.ext_iff.mp hxy),
        oneHandleCompactNeutralImageTranspose.rangeRestrict_surjective⟩
    have hcard : Nat.card (ElemDual NeutralTarget) =
        Nat.card oneHandleCompactNeutralImageTranspose.range :=
      Nat.card_eq_of_bijective _ hbij
    have hcardDual : Nat.card (ElemDual NeutralTarget) =
        Nat.card NeutralTarget :=
      card_elemDual oneHandleC7StandardNeutralityCokernel_add_self
    have hpow : 2 ^ oneHandleCompactNeutralImageTransposeRank =
        2 ^ oneHandleC7StandardNeutralityFinrank := by
      rw [← neutralImageTranspose_rangeCard_eq_pow_rank,
        ← natCard_oneHandleC7StandardNeutralityCokernel_eq_pow_finrank]
      exact hcard.symm.trans hcardDual
    exact (Nat.pow_right_injective (a := 2) (by omega)).eq_iff.mp hpow

theorem imageRank_add_parityRank_eq_two_iff_coveredParity_eq_top :
    oneHandleCompactNeutralImageTransposeRank +
        oneHandleC7StandardParityInteractionRank = 2 ↔
      oneHandleC7StandardCoveredParity = ⊤ := by
  rw [oneHandleC7StandardCoveredParity_eq_top_iff,
    ← neutralImageTransposeRank_eq_standardNeutralityFinrank_iff_range_top]
  have htarget := standardNeutralityFinrank_add_parityInteractionRank
  constructor <;> intro h <;> omega

theorem oneHandleW6Correctable_of_coveredParity_eq_top
    (E : OneHandleC7RelativeLift)
    (D : OneHandleCompactKernelCorrection)
    (hD : oneHandleCompactConnectingHom D =
      oneHandleC7StandardRelativeObstruction E)
    (hcover : oneHandleC7StandardCoveredParity = ⊤) :
    OneHandleW6Correctable := by
  apply oneHandleW6Correctable_of_imageRank_add_parityRank_eq_two E D hD
  exact imageRank_add_parityRank_eq_two_iff_coveredParity_eq_top.mpr hcover

#print axioms oneHandleC7StandardCoveredParity
#print axioms oneHandleC7StandardCoveredParity_eq_top_iff
#print axioms neutralImageTransposeRank_eq_standardNeutralityFinrank_iff_range_top
#print axioms imageRank_add_parityRank_eq_two_iff_coveredParity_eq_top
#print axioms oneHandleW6Correctable_of_coveredParity_eq_top

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenCoveredParity

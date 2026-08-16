/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLOddCompatibleRamified

/-!
# Exact arithmetic residuals for instance-aware compatible ramified data

`GammaLOddCompatibleRamified` preserves the caller's `MuN 2` action while consuming a
`CompatibleRamifiedDataAt` packet.  This module reduces that packet to the two arithmetic facts
actually used at each compatible ramified finite quotient:

1. some lift of `c (tqTau P.qK)` is residue-trivial at the anchored kernel;
2. the canonical anchored splitting field carries an `InvolutionFieldPackage`.

The lift is existential.  This is strictly weaker than asking the arbitrary
`Function.surjInv` lift chosen by `tameTauLift` to be residue-trivial.  Both residuals are also
quantified only when the maps are compatible and tame inertia acts nontrivially, matching the
consumer exactly.

The existing anchored certificate builders infer the canonical subgroup action before the
caller's action is visible.  `ramifiedCertificateOfAnchoredSplitAt` repeats that short record
assembly with the source action explicit.  Uniqueness of the action on the two-element group
`MuN 2` identifies it with the canonical action for the local-duality field, without changing
the action path in the returned certificate.

This module does not claim either remaining universal producer.  The repository's
`ResidueLift.exists_residueTrivial_tameLift` is specific to `AbsGalQ2`, `Ttame`, and `q = 2`;
it does not supply the general open-subgroup, `Tq (2 ^ f)` statement here.  Likewise
`VanishCloseK` deliberately retains `InvolutionFieldPackage` as its AX3/AX4 field-side input.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2

private theorem distribMulAction_muN_two_unique {G : Type} [Group G]
    (a b : DistribMulAction G (MuN 2)) : a = b := by
  apply DistribMulAction.ext
  funext g x
  exact (@LiftingDualityG.smul_muN_two_trivialG G _ a g x).trans
    (@LiftingDualityG.smul_muN_two_trivialG G _ b g x).symm

/-- The anchored-splitting certificate builder with the source action path kept explicit. -/
noncomputable def ramifiedCertificateOfAnchoredSplitAt
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (P : FieldParameters) (U : Subgroup AbsGalQ2)
    [instDMA : DistribMulAction ↑U (MuN 2)] [instCS : ContinuousSMul ↑U (MuN 2)]
    (hU : IsOpen (U : Set AbsGalQ2)) [U.FiniteIndex]
    (V : Type) [AddCommGroup V] [DistribMulAction C V]
    (c : ContinuousMonoidHom (Tq P.qK) C) (rho : ContinuousMonoidHom ↑U C)
    (hram : ∃ v : V, c (tqTau P.qK) • v ≠ v)
    (g₀ : ↑U) (hg₀ : rho g₀ = c (tqTau P.qK))
    (hg₀rt : IsResidueTrivial (ancSubgroup (kerAnc (subtypeAnc U) rho)) (subtypeAnc U g₀))
    (hpkg : InvolutionFieldPackage (subtypeAnc U) rho (anchoredSplitField U rho)) :
    RamifiedCertificate P U V c rho := by
  have hDMA : instDMA = U.instDistribMulActionSubtypeMem :=
    distribMulAction_muN_two_unique instDMA U.instDistribMulActionSubtypeMem
  cases hDMA
  letI : FiniteDimensional ℚ_[2] (anchoredSplitField U rho) :=
    anchoredSplitField_finiteDimensional U hU rho
  exact
    { ram := hram
      anc := subtypeAnc U
      hancinj := subtypeAnc_injective U
      hancind := subtypeAnc_isInducing U
      Dker := tateDualityKer rho (subgroup_isLocalDualizingGroup 2 U hU)
      g₀ := g₀
      hg₀ := hg₀
      hg₀rt := hg₀rt
      k₀ := anchoredSplitField U rho
      fd := inferInstance
      htriv := fun g y ↦ ResidueLift.htriv_zmod2 g y
      hker₀ := fun x ↦ (mem_fixingSubgroup_anchoredSplitField_iff U hU rho x).symm
      hpkg := hpkg }

/-- The actual residue-lift datum needed at maps compatible with a fixed tame quotient.
Unlike the selected `surjInv` lift, this asks only for some lift, exactly as
`RamifiedCertificate` does. -/
def CompatibleResidueLiftAt (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) : Prop :=
  ∀ {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    (V : Type) [AddCommGroup V] [DistribMulAction D V]
    (c : ContinuousMonoidHom (Tq P.qK) D) (rho : ContinuousMonoidHom ↑U D),
    (∀ g : ↑U, rho g = c (tame g)) →
      (∃ v : V, c (tqTau P.qK) • v ≠ v) →
      ∃ g₀ : ↑U, rho g₀ = c (tqTau P.qK) ∧
        IsResidueTrivial (ancSubgroup (kerAnc (subtypeAnc U) rho)) (subtypeAnc U g₀)

/-- The involution package at the canonical anchored field, only for compatible ramified uses. -/
def AnchoredInvolutionFieldDataAt (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) : Prop :=
  ∀ {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    (V : Type) [AddCommGroup V] [DistribMulAction D V]
    (c : ContinuousMonoidHom (Tq P.qK) D) (rho : ContinuousMonoidHom ↑U D),
    (∀ g : ↑U, rho g = c (tame g)) →
      (∃ v : V, c (tqTau P.qK) • v ≠ v) →
        InvolutionFieldPackage (subtypeAnc U) rho (anchoredSplitField U rho)

/-- The two independent arithmetic residues produce the instance-aware compatible packet.
The source `MuN 2` action instances remain explicit throughout. -/
theorem compatibleRamifiedDataAt_of_residuals
    (P : FieldParameters) (U : Subgroup AbsGalQ2)
    [DistribMulAction ↑U (MuN 2)] [ContinuousSMul ↑U (MuN 2)]
    (hU : IsOpen (U : Set AbsGalQ2)) [U.FiniteIndex]
    (tame : ContinuousMonoidHom ↑U (Tq P.qK))
    (hLift : CompatibleResidueLiftAt P U tame)
    (hInv : AnchoredInvolutionFieldDataAt P U tame) :
    CompatibleRamifiedDataAt P U tame := by
  intro D _ _ _ _ V _ _ c rho hfac hram
  obtain ⟨g₀, hg₀, hg₀rt⟩ := hLift V c rho hfac hram
  exact ⟨ramifiedCertificateOfAnchoredSplitAt P U hU V c rho hram g₀ hg₀ hg₀rt
    (hInv V c rho hfac hram)⟩

#print axioms ramifiedCertificateOfAnchoredSplitAt
#print axioms CompatibleResidueLiftAt
#print axioms AnchoredInvolutionFieldDataAt
#print axioms compatibleRamifiedDataAt_of_residuals

end
end GQ2.Dyadic

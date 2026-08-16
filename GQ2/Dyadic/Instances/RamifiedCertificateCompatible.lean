/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateAnchoredSplit

/-!
# Ramified certificates at the compatible tame quotient

The determinant proof does not use an arbitrary unrelated pair of maps. Its actual maps satisfy

`rho g = c (tame g)`

for a surjective tame quotient `tame`. Surjectivity selects a canonical preimage of `tqTau`, and
the displayed compatibility equation proves that this element lifts `c tqTau`. Combining this
observation with `ramifiedCertificateOfAnchoredSplit` leaves exactly two arithmetic inputs:

* residue-triviality of the selected tame-`tau` lift;
* `InvolutionFieldPackage` at `anchoredSplitField U rho`.

`CompatibleRamifiedData` records the corrected actual-use quantification. It is deliberately
parallel to, and does not replace or alter, the legacy universal `ramifiedData` binder.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C]

/-- The canonical lift of the tame generator along a surjective tame quotient. -/
noncomputable def tameTauLift {q : ℕ} {U : Subgroup AbsGalQ2}
    (tame : ContinuousMonoidHom ↑U (Tq q)) (htame : Function.Surjective tame) : ↑U :=
  Function.surjInv htame (tqTau q)

@[simp] theorem tame_tameTauLift {q : ℕ} {U : Subgroup AbsGalQ2}
    (tame : ContinuousMonoidHom ↑U (Tq q)) (htame : Function.Surjective tame) :
    tame (tameTauLift tame htame) = tqTau q :=
  Function.rightInverse_surjInv htame (tqTau q)

/-- Compatibility supplies the lift equation; residue-triviality and the involution package
remain. -/
noncomputable def ramifiedCertificateOfCompatibleTame
    (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) [U.FiniteIndex] [Finite C]
    (V : Type) [AddCommGroup V] [DistribMulAction C V]
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) (htame : Function.Surjective tame)
    (c : ContinuousMonoidHom (Tq P.qK) C) (rho : ContinuousMonoidHom ↑U C)
    (hfac : ∀ g : ↑U, rho g = c (tame g))
    (hram : ∃ v : V, c (tqTau P.qK) • v ≠ v)
    (hrt : IsResidueTrivial (ancSubgroup (kerAnc (subtypeAnc U) rho))
      (subtypeAnc U (tameTauLift tame htame)))
    (hpkg : InvolutionFieldPackage (subtypeAnc U) rho (anchoredSplitField U rho)) :
    RamifiedCertificate P U V c rho :=
  ramifiedCertificateOfAnchoredSplit P U hU V c rho hram (tameTauLift tame htame)
    (by rw [hfac, tame_tameTauLift]) hrt hpkg

/-- The compatibility-aware replacement shape for the legacy universal certificate packet. -/
def CompatibleRamifiedData (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) : Prop :=
  ∀ {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    (V : Type) [AddCommGroup V] [DistribMulAction D V]
    (c : ContinuousMonoidHom (Tq P.qK) D) (rho : ContinuousMonoidHom ↑U D),
    (∀ g : ↑U, rho g = c (tame g)) →
      (∃ v : V, c (tqTau P.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate P U V c rho)

/-- The exact two-part residual at each compatible instance implies `CompatibleRamifiedData`. -/
theorem compatibleRamifiedData_of_anchoredResidual
    (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) [U.FiniteIndex]
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) (htame : Function.Surjective tame)
    (H : ∀ {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
      (V : Type) [AddCommGroup V] [DistribMulAction D V]
      (c : ContinuousMonoidHom (Tq P.qK) D) (rho : ContinuousMonoidHom ↑U D)
      (_hfac : ∀ g : ↑U, rho g = c (tame g))
      (_hram : ∃ v : V, c (tqTau P.qK) • v ≠ v),
      IsResidueTrivial (ancSubgroup (kerAnc (subtypeAnc U) rho))
          (subtypeAnc U (tameTauLift tame htame)) ∧
        InvolutionFieldPackage (subtypeAnc U) rho (anchoredSplitField U rho)) :
    CompatibleRamifiedData P U tame := by
  intro D _ _ _ _ V _ _ c rho hfac hram
  obtain ⟨hrt, hpkg⟩ := H V c rho hfac hram
  exact ⟨ramifiedCertificateOfCompatibleTame P U hU V tame htame c rho hfac hram hrt hpkg⟩

#print axioms tameTauLift
#print axioms tame_tameTauLift
#print axioms ramifiedCertificateOfCompatibleTame
#print axioms CompatibleRamifiedData
#print axioms compatibleRamifiedData_of_anchoredResidual

end
end GQ2.Dyadic

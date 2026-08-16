/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.LocalGauss.Main

/-!
# The canonical anchored splitting field for ramified certificates

For a finite quotient `rho` of an open subgroup `U ≤ G_ℚ₂`, the anchored kernel is open in
`G_ℚ₂`. Its fixed field is therefore finite over `ℚ₂`, and Krull correspondence identifies
its fixing subgroup with the anchored kernel. This discharges four routine fields of
`RamifiedCertificate`: `k₀`, finite dimensionality, the trivial action on `ZMod 2`, and `hker₀`.

The resulting constructor `ramifiedCertificateOfAnchoredSplit` retains exactly the genuinely
arithmetic data not supplied here:

* a residue-trivial lift `g₀` of `c (tqTau P.qK)` through `rho`;
* `InvolutionFieldPackage` at the canonical anchored splitting field.

In particular, this module does not claim the packet-level universal `ramifiedData` statement.
That statement quantifies over an unrelated pair `c` and `rho`, while the lift equation
`rho g₀ = c (tqTau P.qK)` already requires compatibility or at least range membership.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]
local notation "GalQ2" => Kummer.GaloisGroup ℚ_[2]

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C]

/-- The finite field cut out by the anchored kernel of a finite quotient of an open source. -/
def anchoredSplitField (U : Subgroup AbsGalQ2) (rho : ContinuousMonoidHom ↑U C) :
    IntermediateField ℚ_[2] ℚ̄₂ :=
  IntermediateField.fixedField (ancSubgroup (kerAnc (subtypeAnc U) rho))

private theorem anchoredKernel_isOpen (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) (rho : ContinuousMonoidHom ↑U C) :
    IsOpen ((ancSubgroup (kerAnc (subtypeAnc U) rho) : Subgroup GalQ2) : Set GalQ2) := by
  have hker : IsOpen (((rho.toMonoidHom.ker : Subgroup ↑U) : Set ↑U)) := by
    have heq : (((rho.toMonoidHom.ker : Subgroup ↑U) : Set ↑U)) = rho ⁻¹' {1} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
      rfl
    rw [heq]
    exact (isOpen_discrete {1}).preimage rho.continuous_toFun
  rw [ancSubgroup_kerAnc, Subgroup.coe_map]
  change IsOpen ((fun x : ↑U ↦ (x : AbsGalQ2)) ''
    (((rho.toMonoidHom.ker : Subgroup ↑U) : Set ↑U)))
  exact hU.isOpenMap_subtype_val _ hker

/-- Krull correspondence recovers the anchored kernel from its fixed field. -/
theorem fixingSubgroup_anchoredSplitField (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) (rho : ContinuousMonoidHom ↑U C) :
    (anchoredSplitField U rho).fixingSubgroup = ancSubgroup (kerAnc (subtypeAnc U) rho) := by
  unfold anchoredSplitField
  exact InfiniteGalois.fixingSubgroup_fixedField
    ⟨_, Subgroup.isClosed_of_isOpen _ (anchoredKernel_isOpen U hU rho)⟩

/-- The anchored splitting field is finite over `ℚ₂`. -/
theorem anchoredSplitField_finiteDimensional (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) (rho : ContinuousMonoidHom ↑U C) :
    FiniteDimensional ℚ_[2] (anchoredSplitField U rho) := by
  rw [← InfiniteGalois.isOpen_iff_finite (anchoredSplitField U rho),
    fixingSubgroup_anchoredSplitField U hU rho]
  exact anchoredKernel_isOpen U hU rho

/-- The exact membership bridge consumed by `RamifiedCertificate.hker₀`. -/
theorem mem_fixingSubgroup_anchoredSplitField_iff (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) (rho : ContinuousMonoidHom ↑U C)
    (x : Kummer.GaloisGroup ℚ_[2]) :
    x ∈ (anchoredSplitField U rho).fixingSubgroup ↔
      x ∈ ancSubgroup (kerAnc (subtypeAnc U) rho) := by
  rw [fixingSubgroup_anchoredSplitField U hU rho]

/-- Build the campaign ramified certificate after discharging its routine fixed-field fields. -/
noncomputable def ramifiedCertificateOfAnchoredSplit
    (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) [U.FiniteIndex]
    [Finite C] (V : Type) [AddCommGroup V] [DistribMulAction C V]
    (c : ContinuousMonoidHom (Tq P.qK) C) (rho : ContinuousMonoidHom ↑U C)
    (hram : ∃ v : V, c (tqTau P.qK) • v ≠ v)
    (g₀ : ↑U) (hg₀ : rho g₀ = c (tqTau P.qK))
    (hg₀rt : IsResidueTrivial (ancSubgroup (kerAnc (subtypeAnc U) rho)) (subtypeAnc U g₀))
    (hpkg : InvolutionFieldPackage (subtypeAnc U) rho (anchoredSplitField U rho)) :
    RamifiedCertificate P U V c rho := by
  letI : FiniteDimensional ℚ_[2] (anchoredSplitField U rho) :=
    anchoredSplitField_finiteDimensional U hU rho
  exact ramifiedCertificateOfSubtype P U hU V c rho hram g₀ hg₀ hg₀rt
    (anchoredSplitField U rho) (fun g y ↦ ResidueLift.htriv_zmod2 g y)
    (fun x ↦ (mem_fixingSubgroup_anchoredSplitField_iff U hU rho x).symm) hpkg

#print axioms anchoredSplitField
#print axioms fixingSubgroup_anchoredSplitField
#print axioms anchoredSplitField_finiteDimensional
#print axioms mem_fixingSubgroup_anchoredSplitField_iff
#print axioms ramifiedCertificateOfAnchoredSplit

end
end GQ2.Dyadic

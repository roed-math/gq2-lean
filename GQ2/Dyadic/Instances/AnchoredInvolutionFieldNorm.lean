/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateCompatibleAt

/-!
# Canonical anchored involution fields and their exact analytic residue

`AnchoredInvolutionFieldDataAt` asks for an `InvolutionFieldPackage` at the canonical anchored
splitting field.  This module constructs every algebraic and Galois-theoretic field in that
package.  For an involution lift `g`, the intermediate field is the fixed field of the anchored
image of `ker rho ⊔ <g>`.

The construction supplies, without further hypotheses:

* finite dimensionality of the involution field;
* its inclusion in `anchoredSplitField U rho`;
* the exact fixing-subgroup membership dictionary;
* index two of the anchored splitting subgroup in the involution subgroup.

Consequently the only remaining field-side premise is the analytic norm-value matching clause.
`AnchoredInvolutionNormDataAt` states that clause with exactly the compatible-use quantification
and the caller's `MuN 2` action retained by `AnchoredInvolutionFieldDataAt`.

The existing `MarkedRecip` bundle does not contain this relative norm-value statement, and the
general-`K` oriented tame quotient does not currently expose an analogue of the hard-coded
`UnramifiedBridge.hunram_involution` theorem over `AbsGalQ2`.  Thus the final norm premise is not
claimed here; it is isolated in the weakest canonical tower where the consumer needs it.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]
local notation "GalQ2" => Kummer.GaloisGroup ℚ_[2]

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C]

/-- The anchored image of the involution overgroup `ker rho ⊔ <g>`. -/
def anchoredInvolutionSubgroup (U : Subgroup AbsGalQ2)
    (rho : ContinuousMonoidHom ↑U C) (g : ↑U) : Subgroup GalQ2 :=
  ((rho.toMonoidHom.ker : Subgroup ↑U) ⊔ Subgroup.zpowers g).map
    (subtypeAnc U).toMonoidHom

/-- The canonical field fixed by the anchored involution overgroup. -/
def anchoredInvolutionField (U : Subgroup AbsGalQ2)
    (rho : ContinuousMonoidHom ↑U C) (g : ↑U) : IntermediateField ℚ_[2] ℚ̄₂ :=
  IntermediateField.fixedField (anchoredInvolutionSubgroup U rho g)

private theorem anchoredInvolutionSubgroup_isOpen (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) (rho : ContinuousMonoidHom ↑U C) (g : ↑U) :
    IsOpen ((anchoredInvolutionSubgroup U rho g : Subgroup GalQ2) : Set GalQ2) := by
  have hker : IsOpen (((rho.toMonoidHom.ker : Subgroup ↑U) : Set ↑U)) :=
    isOpen_ker rho
  have hsup : IsOpen
      ((((rho.toMonoidHom.ker : Subgroup ↑U) ⊔ Subgroup.zpowers g) : Subgroup ↑U) :
        Set ↑U) :=
    Subgroup.isOpen_mono le_sup_left hker
  rw [anchoredInvolutionSubgroup, Subgroup.coe_map]
  change IsOpen ((fun x : ↑U ↦ (x : AbsGalQ2)) ''
    ((((rho.toMonoidHom.ker : Subgroup ↑U) ⊔ Subgroup.zpowers g) : Subgroup ↑U) :
      Set ↑U))
  exact hU.isOpenMap_subtype_val _ hsup

/-- Krull correspondence recovers the anchored involution overgroup from its fixed field. -/
theorem fixingSubgroup_anchoredInvolutionField (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) (rho : ContinuousMonoidHom ↑U C) (g : ↑U) :
    (anchoredInvolutionField U rho g).fixingSubgroup =
      anchoredInvolutionSubgroup U rho g := by
  unfold anchoredInvolutionField
  exact InfiniteGalois.fixingSubgroup_fixedField
    ⟨_, Subgroup.isClosed_of_isOpen _ (anchoredInvolutionSubgroup_isOpen U hU rho g)⟩

/-- The canonical anchored involution field is finite over `ℚ₂`. -/
theorem anchoredInvolutionField_finiteDimensional (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) (rho : ContinuousMonoidHom ↑U C) (g : ↑U) :
    FiniteDimensional ℚ_[2] (anchoredInvolutionField U rho g) := by
  rw [← InfiniteGalois.isOpen_iff_finite (anchoredInvolutionField U rho g),
    fixingSubgroup_anchoredInvolutionField U hU rho g]
  exact anchoredInvolutionSubgroup_isOpen U hU rho g

omit [DiscreteTopology C] in
/-- The involution fixed field lies below the anchored splitting field. -/
theorem anchoredInvolutionField_le_anchoredSplitField (U : Subgroup AbsGalQ2)
    (rho : ContinuousMonoidHom ↑U C) (g : ↑U) :
    anchoredInvolutionField U rho g ≤ anchoredSplitField U rho := by
  intro x hx
  rw [anchoredInvolutionField, IntermediateField.mem_fixedField_iff] at hx
  rw [anchoredSplitField, IntermediateField.mem_fixedField_iff]
  intro y hy
  rw [ancSubgroup_kerAnc] at hy
  obtain ⟨n, hn, rfl⟩ := hy
  exact hx _ ⟨n, Subgroup.mem_sup_left hn, rfl⟩

/-- Membership in the involution overgroup is exactly membership of the anchored element in the
fixing subgroup of the canonical involution field. -/
theorem mem_fixingSubgroup_anchoredInvolutionField_iff (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) (rho : ContinuousMonoidHom ↑U C) (g x : ↑U) :
    x ∈ (rho.toMonoidHom.ker : Subgroup ↑U) ⊔ Subgroup.zpowers g ↔
      subtypeAnc U x ∈ (anchoredInvolutionField U rho g).fixingSubgroup := by
  rw [fixingSubgroup_anchoredInvolutionField U hU rho g]
  constructor
  · exact fun hx ↦ ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, heq⟩
    have hyx : y = x := subtypeAnc_injective U heq
    simpa [hyx] using hy

omit [DiscreteTopology C] in
private theorem anchoredInvolutionSubgroup_index_two (U : Subgroup AbsGalQ2)
    (rho : ContinuousMonoidHom ↑U C) (g : ↑U)
    (hgN : g ∉ (rho.toMonoidHom.ker : Subgroup ↑U))
    (hg2 : g * g ∈ (rho.toMonoidHom.ker : Subgroup ↑U)) :
    (((rho.toMonoidHom.ker : Subgroup ↑U).map (subtypeAnc U).toMonoidHom).subgroupOf
      (anchoredInvolutionSubgroup U rho g)).index = 2 := by
  let N : Subgroup ↑U := rho.toMonoidHom.ker
  let W : Subgroup ↑U := N ⊔ Subgroup.zpowers g
  let a := subtypeAnc U
  have hgW : g ∈ W := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have hagW : a g ∈ anchoredInvolutionSubgroup U rho g := ⟨g, hgW, rfl⟩
  refine InvolutionSplice.index_eq_two_of_decomp
    (s := ⟨a g, hagW⟩) ?_ (fun b hb ↦ ?_)
  · intro hagN
    obtain ⟨n, hn, han⟩ := Subgroup.mem_subgroupOf.mp hagN
    exact hgN (by
      have hng : n = g := subtypeAnc_injective U han
      simpa [N, hng] using hn)
  · obtain ⟨x, hxW, hxb⟩ := b.2
    have hxN : x ∉ N := by
      intro hxN
      apply hb
      apply Subgroup.mem_subgroupOf.mpr
      exact ⟨x, hxN, hxb⟩
    have hxgN : x * g ∈ N := by
      rcases InvolutionSplice.mem_or_mul_mem_of_mem_sup (N := N) hg2 hxW with h | h
      · exact absurd h hxN
      · exact h
    apply Subgroup.mem_subgroupOf.mpr
    refine ⟨x * g, hxgN, ?_⟩
    change a (x * g) = (b : GalQ2) * a g
    change a x = (b : GalQ2) at hxb
    rw [map_mul, hxb]

/-- The anchored splitting subgroup has index two in the canonical involution subgroup. -/
theorem anchoredSplitField_subgroupOf_anchoredInvolutionField_index (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) (rho : ContinuousMonoidHom ↑U C) (g : ↑U)
    (hgN : g ∉ (rho.toMonoidHom.ker : Subgroup ↑U))
    (hg2 : g * g ∈ (rho.toMonoidHom.ker : Subgroup ↑U)) :
    (((anchoredSplitField U rho).fixingSubgroup).subgroupOf
      (anchoredInvolutionField U rho g).fixingSubgroup).index = 2 := by
  rw [fixingSubgroup_anchoredSplitField U hU rho,
    fixingSubgroup_anchoredInvolutionField U hU rho g, ancSubgroup_kerAnc]
  exact anchoredInvolutionSubgroup_index_two U rho g hgN hg2

/-- Every canonical anchored involution tower has a square-root generator.  Thus the quadratic
tower itself is not an additional field-side premise. -/
theorem anchoredInvolutionField_exists_sqrt_generator (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) (rho : ContinuousMonoidHom ↑U C) (g : ↑U)
    (hgN : g ∉ (rho.toMonoidHom.ker : Subgroup ↑U))
    (hg2 : g * g ∈ (rho.toMonoidHom.ker : Subgroup ↑U)) :
    ∃ (d : (↑(anchoredInvolutionField U rho g))ˣ) (δ : ℚ̄₂),
      δ ^ 2 = ((d : ↑(anchoredInvolutionField U rho g)) : ℚ̄₂) ∧
      δ ∈ anchoredSplitField U rho ∧ δ ∉ anchoredInvolutionField U rho g ∧
      IntermediateField.adjoin ↑(anchoredInvolutionField U rho g) {δ} =
        IntermediateField.extendScalars
          (anchoredInvolutionField_le_anchoredSplitField U rho g) := by
  letI : FiniteDimensional ℚ_[2] (anchoredSplitField U rho) :=
    anchoredSplitField_finiteDimensional U hU rho
  have hkL := anchoredInvolutionField_le_anchoredSplitField U rho g
  have hindex :=
    anchoredSplitField_subgroupOf_anchoredInvolutionField_index U hU rho g hgN hg2
  have hdeg : Module.finrank ↑(anchoredInvolutionField U rho g)
      ↑(IntermediateField.extendScalars hkL) = 2 :=
    ShapiroDeepness.finrank_extendScalars_eq_two
      (anchoredInvolutionField U rho g) (anchoredSplitField U rho) hkL hindex
  exact QuadraticAdjoin.exists_sqrt_generator hkL hdeg

/-- The `HasEqualNormValueGroups` spelling of the remaining analytic input.  All conjuncts
except the final one are supplied by `anchoredInvolutionField_exists_sqrt_generator`. -/
def AnchoredInvolutionEqualNormValueGroups (U : Subgroup AbsGalQ2)
    (rho : ContinuousMonoidHom ↑U C) : Prop :=
  ∀ g : ↑U, g ∉ (rho.toMonoidHom.ker : Subgroup ↑U) →
    g * g ∈ (rho.toMonoidHom.ker : Subgroup ↑U) →
      ∃ (d : (↑(anchoredInvolutionField U rho g))ˣ) (δ : ℚ̄₂),
        δ ^ 2 = ((d : ↑(anchoredInvolutionField U rho g)) : ℚ̄₂) ∧
        δ ∈ anchoredSplitField U rho ∧ δ ∉ anchoredInvolutionField U rho g ∧
        IntermediateField.adjoin ↑(anchoredInvolutionField U rho g) {δ} =
          IntermediateField.extendScalars
            (anchoredInvolutionField_le_anchoredSplitField U rho g) ∧
        HasEqualNormValueGroups (anchoredInvolutionField U rho g) δ

/-- The sole analytic residual after choosing the canonical anchored involution fields. -/
def AnchoredInvolutionNormData (U : Subgroup AbsGalQ2)
    (rho : ContinuousMonoidHom ↑U C) : Prop :=
  ∀ g : ↑U, g ∉ (rho.toMonoidHom.ker : Subgroup ↑U) →
    g * g ∈ (rho.toMonoidHom.ker : Subgroup ↑U) →
      ∀ y : ℚ̄₂, y ≠ 0 → y ∈ anchoredSplitField U rho →
        ∃ z : ℚ̄₂, z ≠ 0 ∧ z ∈ anchoredInvolutionField U rho g ∧ ‖y‖ = ‖z‖

/-- Equal norm value groups for a square-root generator give the unfolded norm partner clause. -/
theorem anchoredInvolutionNormData_of_equalNormValueGroups (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) (rho : ContinuousMonoidHom ↑U C)
    (H : AnchoredInvolutionEqualNormValueGroups U rho) :
    AnchoredInvolutionNormData U rho := by
  intro g hgN hg2 y hy0 hyL
  obtain ⟨d, δ, hδ2, hδL, hδk, hadj, hunram⟩ := H g hgN hg2
  letI : FiniteDimensional ℚ_[2] (anchoredSplitField U rho) :=
    anchoredSplitField_finiteDimensional U hU rho
  have hkL := anchoredInvolutionField_le_anchoredSplitField U rho g
  have hindex :=
    anchoredSplitField_subgroupOf_anchoredInvolutionField_index U hU rho g hgN hg2
  have hdeg : Module.finrank ↑(anchoredInvolutionField U rho g)
      ↑(IntermediateField.extendScalars hkL) = 2 :=
    ShapiroDeepness.finrank_extendScalars_eq_two
      (anchoredInvolutionField U rho g) (anchoredSplitField U rho) hkL hindex
  apply norm_partner_of_hasEqualNormValueGroups
    (anchoredInvolutionField U rho g) (anchoredSplitField U rho) δ ?_ hunram y hy0 hyL
  intro x hx
  obtain ⟨a, b, hab⟩ := QuadraticAdjoin.exists_coords hkL hdeg hadj hx
  exact ⟨a, b, hab⟩

/-- Canonical anchored involution fields turn norm matching into the full package. -/
theorem involutionFieldPackage_anchoredSplit_of_normData (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) (rho : ContinuousMonoidHom ↑U C)
    (H : AnchoredInvolutionNormData U rho) :
    InvolutionFieldPackage (subtypeAnc U) rho (anchoredSplitField U rho) := by
  intro g hgN hg2
  letI : FiniteDimensional ℚ_[2] (anchoredInvolutionField U rho g) :=
    anchoredInvolutionField_finiteDimensional U hU rho g
  exact ⟨anchoredInvolutionField U rho g, inferInstance,
    anchoredInvolutionField_le_anchoredSplitField U rho g,
    mem_fixingSubgroup_anchoredInvolutionField_iff U hU rho g,
    anchoredSplitField_subgroupOf_anchoredInvolutionField_index U hU rho g hgN hg2,
    H g hgN hg2⟩

/-- Norm matching in the canonical involution tower, with precisely the compatible ramified-use
quantification and the caller's action that occur in `AnchoredInvolutionFieldDataAt`. -/
def AnchoredInvolutionNormDataAt (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) : Prop :=
  ∀ {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    (V : Type) [AddCommGroup V] [DistribMulAction D V]
    (c : ContinuousMonoidHom (Tq P.qK) D) (rho : ContinuousMonoidHom ↑U D),
    (∀ g : ↑U, rho g = c (tame g)) →
      (∃ v : V, c (tqTau P.qK) • v ≠ v) →
        AnchoredInvolutionNormData U rho

/-- The same compatible-use residual in the `MarkedRecip` norm-value vocabulary. -/
def AnchoredInvolutionEqualNormValueGroupsAt (P : FieldParameters)
    (U : Subgroup AbsGalQ2) (tame : ContinuousMonoidHom ↑U (Tq P.qK)) : Prop :=
  ∀ {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    (V : Type) [AddCommGroup V] [DistribMulAction D V]
    (c : ContinuousMonoidHom (Tq P.qK) D) (rho : ContinuousMonoidHom ↑U D),
    (∀ g : ↑U, rho g = c (tame g)) →
      (∃ v : V, c (tqTau P.qK) • v ≠ v) →
        AnchoredInvolutionEqualNormValueGroups U rho

/-- The exact compatible-use norm residual supplies `AnchoredInvolutionFieldDataAt`. -/
theorem anchoredInvolutionFieldDataAt_of_normData (P : FieldParameters)
    (U : Subgroup AbsGalQ2) (hU : IsOpen (U : Set AbsGalQ2))
    (tame : ContinuousMonoidHom ↑U (Tq P.qK))
    (H : AnchoredInvolutionNormDataAt P U tame) :
    AnchoredInvolutionFieldDataAt P U tame := by
  intro D _ _ _ _ V _ _ c rho hfac hram
  exact involutionFieldPackage_anchoredSplit_of_normData U hU rho
    (H V c rho hfac hram)

/-- Equal norm value groups in each compatible canonical quadratic tower supply
`AnchoredInvolutionFieldDataAt`. -/
theorem anchoredInvolutionFieldDataAt_of_equalNormValueGroups (P : FieldParameters)
    (U : Subgroup AbsGalQ2) (hU : IsOpen (U : Set AbsGalQ2))
    (tame : ContinuousMonoidHom ↑U (Tq P.qK))
    (H : AnchoredInvolutionEqualNormValueGroupsAt P U tame) :
    AnchoredInvolutionFieldDataAt P U tame := by
  apply anchoredInvolutionFieldDataAt_of_normData P U hU tame
  intro D _ _ _ _ V _ _ c rho hfac hram
  exact anchoredInvolutionNormData_of_equalNormValueGroups U hU rho
    (H V c rho hfac hram)

#print axioms anchoredInvolutionSubgroup
#print axioms anchoredInvolutionField
#print axioms fixingSubgroup_anchoredInvolutionField
#print axioms anchoredInvolutionField_finiteDimensional
#print axioms anchoredInvolutionField_le_anchoredSplitField
#print axioms mem_fixingSubgroup_anchoredInvolutionField_iff
#print axioms anchoredSplitField_subgroupOf_anchoredInvolutionField_index
#print axioms anchoredInvolutionField_exists_sqrt_generator
#print axioms AnchoredInvolutionEqualNormValueGroups
#print axioms AnchoredInvolutionNormData
#print axioms anchoredInvolutionNormData_of_equalNormValueGroups
#print axioms involutionFieldPackage_anchoredSplit_of_normData
#print axioms AnchoredInvolutionNormDataAt
#print axioms AnchoredInvolutionEqualNormValueGroupsAt
#print axioms anchoredInvolutionFieldDataAt_of_normData
#print axioms anchoredInvolutionFieldDataAt_of_equalNormValueGroups

end
end GQ2.Dyadic

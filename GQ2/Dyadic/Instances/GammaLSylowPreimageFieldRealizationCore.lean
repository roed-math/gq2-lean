/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldCore
import GQ2.Dyadic.Instances.GammaLRealizationRoute
import GQ2.Dyadic.LocalGauss.Q0

/-!
# Krull construction of the variable GammaL field cores

This optional plumbing layer proves that an ambient `GammaLFieldRealization` supplies the
field-identification interface used by `GammaLSylowPreimageFieldCore`.  It contains no local
classification input: the separate `q = 2` calculation and honest odd-degree dyadic-field
Labute hypothesis remain explicit in the final composition theorem.
-/

namespace GQ2

noncomputable section

/-! ## Topological restrictions of group equivalences -/

/-- Restrict a topological group equivalence to a subgroup and its image. -/
def ContinuousMulEquiv.subgroupMap {G H : Type} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H] (e : G ≃ₜ* H) (U : Subgroup G) :
    ContinuousMulEquiv U (U.map (e : ContinuousMonoidHom G H).toMonoidHom) where
  toMulEquiv := e.toMulEquiv.subgroupMap U
  continuous_toFun :=
    Continuous.subtype_mk (e.continuous_toFun.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk (e.symm.continuous_toFun.comp continuous_subtype_val) _

/-- Equality of ambient subgroups gives the tautological topological group equivalence of their
subtypes. -/
def continuousMulEquivSubgroupOfEq {G : Type} [Group G] [TopologicalSpace G]
    {U V : Subgroup G} (hUV : U = V) : ContinuousMulEquiv U V where
  toMulEquiv := MulEquiv.subgroupCongr hUV
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  continuous_invFun := Continuous.subtype_mk continuous_subtype_val _

end

end GQ2

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.ContCoh

variable {h q : ℕ}
local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## Fixed fields of transported open subgroups -/

/-- An ambient field realization supplies a field identification for every odd-index open
subgroup.  The construction is the Krull fixed field of the subgroup transported first through
the realization and then through the ambient-subgroup inclusion. -/
theorem gammaLOddIndexOpenSubgroupFieldIdentificationSupply_of_fieldRealization
    (R : GammaLFieldRealization h q) :
    GammaLOddIndexOpenSubgroupFieldIdentificationSupply h q := by
  intro U' _ hUopen _hodd
  let N : Subgroup R.subgroup :=
    U'.map (R.equiv : ContinuousMonoidHom (gamma h q : Type) R.subgroup).toMonoidHom
  have hNopen : IsOpen (N : Set R.subgroup) := by
    change IsOpen (R.equiv '' (U' : Set (gamma h q : Type)))
    exact R.equiv.toHomeomorph.isOpenMap _ hUopen
  let H : Subgroup AbsGalQ2 := N.map R.subgroup.subtype
  have hHopen : IsOpen (H : Set AbsGalQ2) := by
    change IsOpen (((fun x : R.subgroup => (x : AbsGalQ2)) '' (N : Set R.subgroup)))
    exact R.isOpen_subgroup.isOpenMap_subtype_val _ hNopen
  have hHclosed : IsClosed (H : Set AbsGalQ2) :=
    Subgroup.isClosed_of_isOpen H hHopen
  let K : IntermediateField ℚ_[2] ℚ̄₂ := IntermediateField.fixedField H
  have hKfix : K.fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, hHclosed⟩
  have hKfin : FiniteDimensional ℚ_[2] K := by
    rw [← InfiniteGalois.isOpen_iff_finite K, hKfix]
    exact hHopen
  let eUN : ContinuousMulEquiv U' N := R.equiv.subgroupMap U'
  let eNH : ContinuousMulEquiv N H := GQ2.Dyadic.anchorEquiv R.subgroup N
  let eHK : ContinuousMulEquiv H (GalK K) :=
    continuousMulEquivSubgroupOfEq hKfix.symm
  let eUK : ContinuousMulEquiv U' (GalK K) := (eUN.trans eNH).trans eHK
  have hNindex : N.index = U'.index := by
    exact Subgroup.index_map_equiv U' R.equiv.toMulEquiv
  have hdegree : Module.finrank ℚ_[2] K = U'.index * (2 * h + 1) := by
    calc
      Module.finrank ℚ_[2] K = K.fixingSubgroup.index :=
        IntermediateField.finrank_eq_fixingSubgroup_index K
      _ = H.index := congrArg Subgroup.index hKfix
      _ = N.index * R.subgroup.index := Subgroup.index_map_subtype N
      _ = U'.index * (2 * h + 1) := by rw [hNindex, R.index_eq]
  exact ⟨{
    K := K
    finiteDimensional := hKfin
    compactSpace := eUK.toHomeomorph.compactSpace
    t2Space := eUK.toHomeomorph.t2Space
    totallyDisconnectedSpace := eUK.toHomeomorph.totallyDisconnectedSpace
    equivGalK := eUK
    degree_eq := hdegree }⟩

/-- Strong field-route endpoint: an ambient field realization leaves precisely the `q = 2`
calculation and the odd-degree dyadic-field Labute classification.  The latter retains the
canonical cyclotomic orientation implicitly through its `GalK K` carrier. -/
theorem gammaLOddIndexOpenSubgroupVariableCorePresentationSupply_of_fieldRealization
    (R : GammaLFieldRealization h q)
    (hqTwo : OddDegreeGalKDemushkinQTwo)
    (hLab : OddDegreeGalKSqLabuteClassification) :
    GammaLOddIndexOpenSubgroupVariableCorePresentationSupply h q :=
  gammaLOddIndexOpenSubgroupVariableCorePresentationSupply_of_field
    (gammaLOddIndexOpenSubgroupFieldIdentificationSupply_of_fieldRealization R)
    hqTwo hLab

#print axioms gammaLOddIndexOpenSubgroupFieldIdentificationSupply_of_fieldRealization
#print axioms gammaLOddIndexOpenSubgroupVariableCorePresentationSupply_of_fieldRealization

end


end GQ2.Dyadic.LSquare

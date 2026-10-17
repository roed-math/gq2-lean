/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5.1
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Character
public import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
public import Mathlib.NumberTheory.Padics.LocalField
public import GQ2.Reciprocity
public import GQ2.TraceForm

@[expose] public section

/-!
# The Galois-group dictionary between gq2 and Tau Ceti (ticket A1)

gq2 states its finite-level inputs (B6, B9, B11a) for a finite intermediate field
`k : IntermediateField ℚ_[2] ℚ̄₂` with Galois group `G_k = ↥k.fixingSubgroup ≤ Gal(ℚ̄₂/ℚ₂)`
acting on `ℚ̄₂`.  Tau Ceti states its theorems for an abstract nonarchimedean local field `K : Type`
with Galois group `TauCeti.AbsoluteGaloisGroup K = Gal(Kˢᵉᵖ/K)` acting on `SeparableClosure K`,
or with Mathlib's `Field.absoluteGaloisGroup K`.  This file is the dictionary between the two
pictures, written once so that the adapter files `GQ2/TauCeti/B*.lean` only instantiate it.

It deliberately imports only light Tau Ceti modules (nothing whose closure contains
`TauCeti.NumberTheory.LocalField.ClassModule`): under the heavy class-field-theory imports,
instance search for `Module.IsTorsionFree ℚ_[2] ℚ̄₂` (hence `IsAlgClosure`, `IsGalois`,
compactness of Galois groups) does not terminate (recon memo, cross-cutting finding 2).  Heavy
adapters therefore `haveI` the named facts of this file instead of searching.

## Contents

* **Galois facts at `ℚ̄₂`** (`isTorsionFree_algebraicClosure`, `isAlgClosure_algebraicClosure`,
  `isGalois_algebraicClosure`, `isSeparable_algebraicClosure`) and compactness of
  `↥k.fixingSubgroup` (`compactSpace_fixingSubgroup`, `locallyCompactSpace_fixingSubgroup`, both
  instances: they are `Prop`-valued, so no diamond is possible).
* **Tau Ceti's local-field package on a finite `↥k`**, as named `def`s/theorems for `letI`/`haveI`
  use (never global instances, which would sit beside the subspace topology inherited from
  `PadicAlgCl`): `valuativeRel`, `localTopology`, `isNonarchimedeanLocalField`,
  `valuativeExtension`.
* **`G_k` in Mathlib's model**: `sepEmb k : ↥k →ₐ[ℚ₂] ℚ₂ˢᵉᵖ`,
  `range_absoluteGaloisGroupExtend_sepEmb` (the image of `G_k` in `G_ℚ₂` is `k.fixingSubgroup`),
  `absGalEquivFixing k : Field.absoluteGaloisGroup ↥k ≃ₜ* ↥k.fixingSubgroup`.
* **`G_k` in Tau Ceti's model and the separable closure seam**:
  `fixingEquivAbsGal k : ↥k.fixingSubgroup ≃ₜ* TauCeti.AbsoluteGaloisGroup ↥k`,
  `sepClosureEquiv k : SeparableClosure ↥k ≃ₐ[↥k] ℚ̄₂`, and the intertwining
  `sepClosureEquiv_fixingEquivAbsGal_apply : e (Φ g x) = g (e x)`.  A2's Kummer comparison and
  the B6/B9 transports are stated for this pair `(Φ, e)`.
* **Finite layers `L/k` inside `ℚ̄₂`**: `layerEmb k L : ↥L →ₐ[↥k] SeparableClosure ↥k` and
  `fixingEquivAbsGal_mem_galoisSubgroup_iff` (`Φ g ∈ galoisSubgroup k L (layerEmb k L) ↔ g`
  fixes `L` pointwise), specialised to `L = quadExt k δ` as the stabilizer of `δ` (B9).
* **The cyclotomic character**: `chiCyc_eq_localCyclotomicCharacter` and its `MonoidHom` and
  abelianized forms (B5, B3c).
* **Krull** (B6): an open subgroup `U ≤ Gal(ℚ̄₂/ℚ₂)` is `(fixedField U).fixingSubgroup`, its
  fixed field is finite of degree `U.index`, and
  `absGalFixedFieldEquiv U hU : Field.absoluteGaloisGroup (fixedField U) ≃ₜ* U`.
* **`rho k : ↥k.fixingSubgroup ≃ₜ* galoisSubgroup ℚ₂ k (sepEmb k)`** (restriction to `ℚ₂ˢᵉᵖ`),
  the form the B11a prototype uses, and its comparison with `fixingEquivAbsGal`.

Tau Ceti names are written fully qualified; nothing here is a global instance on `↥k`.
-/

noncomputable section

namespace GQ2.TauCetiBridge

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ### Galois facts at `ℚ̄₂/ℚ₂`, as named theorems for `haveI` in heavy files -/

/-- `ℚ̄₂` is a torsion-free `ℚ₂`-module (a vector space).  Instance search for this fact does
not terminate under Tau Ceti's class-field-theory imports; `haveI` it there. -/
theorem isTorsionFree_algebraicClosure : Module.IsTorsionFree ℚ_[2] ℚ̄₂ :=
  DivisionSemiring.to_moduleIsTorsionFree

/-- `ℚ̄₂` is an algebraic closure of `ℚ₂` (Mathlib's instance, named for `haveI`). -/
theorem isAlgClosure_algebraicClosure : IsAlgClosure ℚ_[2] ℚ̄₂ :=
  AlgebraicClosure.instIsAlgClosure ℚ_[2]

/-- `ℚ̄₂/ℚ₂` is Galois (characteristic zero). -/
theorem isGalois_algebraicClosure : IsGalois ℚ_[2] ℚ̄₂ :=
  IsAlgClosure.isGalois _ _

/-- `ℚ̄₂/ℚ₂` is separable (characteristic zero). -/
theorem isSeparable_algebraicClosure : Algebra.IsSeparable ℚ_[2] ℚ̄₂ :=
  haveI := isGalois_algebraicClosure
  IsGalois.to_isSeparable

/-- The separable closure of `ℚ₂` inside `ℚ̄₂` is all of `ℚ̄₂` (characteristic zero). -/
theorem separableClosure_eq_top : separableClosure ℚ_[2] ℚ̄₂ = ⊤ :=
  (separableClosure.eq_top_iff ℚ_[2] ℚ̄₂).2 isSeparable_algebraicClosure

/-- Every element of `ℚ̄₂` lies in `separableClosure ℚ_[2] ℚ̄₂` (the intermediate field
whose carrier is `SeparableClosure ℚ_[2]`). -/
theorem mem_separableClosure (x : ℚ̄₂) : x ∈ separableClosure ℚ_[2] ℚ̄₂ :=
  (mem_separableClosure_iff (F := ℚ_[2])).2 (Algebra.IsSeparable.isSeparable ℚ_[2] x)

section FixingSubgroup

variable (k : IntermediateField ℚ_[2] ℚ̄₂)

/-- `G_k = ↥k.fixingSubgroup` is compact: it is closed in the profinite group `Gal(ℚ̄₂/ℚ₂)`.
Not found by instance search before this declaration; `Prop`-valued, so safe as an instance. -/
instance compactSpace_fixingSubgroup : CompactSpace k.fixingSubgroup :=
  haveI := isGalois_algebraicClosure
  isCompact_iff_compactSpace.mp (InfiniteGalois.fixingSubgroup_isClosed k).isCompact

/-- `G_k = ↥k.fixingSubgroup` is locally compact (the `[LocallyCompactSpace G]` hypothesis of
`TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology`). -/
instance locallyCompactSpace_fixingSubgroup : LocallyCompactSpace k.fixingSubgroup :=
  inferInstance

end FixingSubgroup

/-! ### Tau Ceti's local-field package on a finite `↥k`

Installed per proof with `letI`/`haveI`; never global instances (`↥k` already carries the subspace
topology of `PadicAlgCl`, propositionally but not definitionally equal to Tau Ceti's). -/

section LocalField

variable (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]

/-- Tau Ceti's valuative relation on a finite `↥k` (from the spectral norm). -/
@[instance_reducible] def valuativeRel : ValuativeRel k :=
  TauCeti.finiteIntermediateFieldValuativeRel ℚ_[2] ℚ̄₂ k

/-- Tau Ceti's (spectral-norm) topology on a finite `↥k`. -/
@[instance_reducible] def localTopology : TopologicalSpace k :=
  TauCeti.finiteIntermediateFieldTopology ℚ_[2] ℚ̄₂ k

/-- With Tau Ceti's valuative relation and topology, a finite `↥k` is a nonarchimedean local
field. -/
theorem isNonarchimedeanLocalField :
    @IsNonarchimedeanLocalField k _ (valuativeRel k) (localTopology k) :=
  TauCeti.finiteIntermediateField_isNonarchimedeanLocalField ℚ_[2] ℚ̄₂ k

/-- Tau Ceti's valuative relation on `↥k` extends that of `ℚ₂`. -/
theorem valuativeExtension :
    letI := valuativeRel k
    ValuativeExtension ℚ_[2] k :=
  TauCeti.finiteIntermediateField_valuativeExtension ℚ_[2] ℚ̄₂ k

/-- The package applies Tau Ceti's local theorems at `↥k`: here, the normalized valuation of
`↥k` is onto `ℤ`.  (Tau Ceti's `FinitePadicExtension k 2` is then found by instance search as
`FinitePadicExtension.ofInstances`; it is not re-exported here because importing
`TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex` re-introduces the instance-search
pathology this file avoids.) -/
example :
    letI := valuativeRel k
    letI := localTopology k
    haveI := isNonarchimedeanLocalField k
    Function.Surjective (TauCeti.normalizedValuation k) :=
  letI := valuativeRel k
  letI := localTopology k
  haveI := isNonarchimedeanLocalField k
  TauCeti.normalizedValuation_surjective (K := k)

end LocalField

/-! ### `G_k` in Mathlib's model: `Field.absoluteGaloisGroup ↥k ≃ₜ* ↥k.fixingSubgroup` -/

section MathlibModel

variable (k : IntermediateField ℚ_[2] ℚ̄₂)

/-- The inclusion of `k ⊆ ℚ̄₂` into the separable closure `ℚ₂ˢᵉᵖ = separableClosure ℚ₂ ℚ̄₂`
(which is all of `ℚ̄₂`), as a `ℚ₂`-embedding: Tau Ceti's `σ` for the extension `k/ℚ₂`. -/
def sepEmb : k →ₐ[ℚ_[2]] SeparableClosure ℚ_[2] :=
  IntermediateField.inclusion fun x _ ↦ mem_separableClosure x

@[simp] theorem coe_sepEmb_apply (x : k) : (sepEmb k x : ℚ̄₂) = x := rfl

variable [FiniteDimensional ℚ_[2] k]

/-- **The image of `G_k` in `G_ℚ₂` is `k.fixingSubgroup`.** The general form of Tau Ceti's
`range_absoluteGaloisGroupExtend_shapiroFieldEmbedding`, same proof. -/
theorem range_absoluteGaloisGroupExtend_sepEmb :
    (TauCeti.absoluteGaloisGroupExtend ℚ_[2] k (sepEmb k)).range = k.fixingSubgroup := by
  ext g
  rw [TauCeti.mem_range_absoluteGaloisGroupExtend_iff, TauCeti.mem_galoisSubgroup_iff]
  refine ⟨fun h ↦ (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx ↦ ?_,
    fun h x ↦ Subtype.ext ?_⟩
  · exact (TauCeti.coe_absoluteGaloisGroupRestrictEquiv_apply (K := ℚ_[2]) g _).symm.trans
      (congrArg Subtype.val (h ⟨x, hx⟩))
  · exact (TauCeti.coe_absoluteGaloisGroupRestrictEquiv_apply (K := ℚ_[2]) g _).trans
      ((IntermediateField.mem_fixingSubgroup_iff _ _).1 h x x.2)

/-- **gq2's `G_k = ↥k.fixingSubgroup` is Mathlib's `Field.absoluteGaloisGroup ↥k`**, as
topological groups, via `TauCeti.absoluteGaloisGroupExtend ℚ₂ k (sepEmb k)`. -/
def absGalEquivFixing : Field.absoluteGaloisGroup k ≃ₜ*
    ↥(k.fixingSubgroup : Subgroup (GQ2.Kummer.GaloisGroup ℚ_[2])) :=
  TauCeti.absoluteGaloisGroupExtendEquiv ℚ_[2] k (sepEmb k)
    (range_absoluteGaloisGroupExtend_sepEmb k)

@[simp] theorem coe_absGalEquivFixing_apply (g : Field.absoluteGaloisGroup k) :
    ((absGalEquivFixing k g : k.fixingSubgroup) : GQ2.Kummer.GaloisGroup ℚ_[2]) =
      TauCeti.absoluteGaloisGroupExtend ℚ_[2] k (sepEmb k) g :=
  TauCeti.coe_absoluteGaloisGroupExtendEquiv_apply _ _ _ _ g

@[simp] theorem absoluteGaloisGroupExtend_absGalEquivFixing_symm (g : k.fixingSubgroup) :
    TauCeti.absoluteGaloisGroupExtend ℚ_[2] k (sepEmb k) ((absGalEquivFixing k).symm g) =
      (g : GQ2.Kummer.GaloisGroup ℚ_[2]) := by
  rw [← coe_absGalEquivFixing_apply, ContinuousMulEquiv.apply_symm_apply]

end MathlibModel

/-! ### `G_k` in Tau Ceti's model, and the separable-closure seam -/

section TauCetiModel

variable (k : IntermediateField ℚ_[2] ℚ̄₂)

/-- `ℚ₂ˢᵉᵖ = separableClosure ℚ₂ ℚ̄₂` is `ℚ̄₂` (characteristic zero), as `ℚ₂`-algebras; the map
is `Subtype.val`. -/
def sepClosureQ2Equiv : SeparableClosure ℚ_[2] ≃ₐ[ℚ_[2]] ℚ̄₂ :=
  AlgEquiv.ofBijective (separableClosure ℚ_[2] ℚ̄₂).val
    ⟨Subtype.val_injective, fun x ↦ ⟨⟨x, mem_separableClosure x⟩, rfl⟩⟩

@[simp] theorem sepClosureQ2Equiv_apply (x : SeparableClosure ℚ_[2]) :
    sepClosureQ2Equiv x = (x : ℚ̄₂) :=
  AlgEquiv.ofBijective_apply _ _ x

@[simp] theorem coe_sepClosureQ2Equiv_symm_apply (x : ℚ̄₂) :
    (sepClosureQ2Equiv.symm x : ℚ̄₂) = x :=
  (sepClosureQ2Equiv_apply _).symm.trans (sepClosureQ2Equiv.apply_symm_apply x)

/-- **The separable closure of `↥k` is `ℚ̄₂`**, as `↥k`-algebras: Tau Ceti's chosen
identification `separableClosureRingEquiv ℚ₂ k (sepEmb k) : kˢᵉᵖ ≃+* ℚ₂ˢᵉᵖ` followed by
`ℚ₂ˢᵉᵖ = ℚ̄₂`.  This is the `e` of the pair `(Φ, e) = (fixingEquivAbsGal k, sepClosureEquiv k)`
the finite-level transports are stated for. -/
def sepClosureEquiv : SeparableClosure k ≃ₐ[k] ℚ̄₂ :=
  AlgEquiv.ofRingEquiv
    (f := (TauCeti.separableClosureRingEquiv ℚ_[2] k (sepEmb k)).trans
      sepClosureQ2Equiv.toRingEquiv)
    fun x ↦ by
      simp only [RingEquiv.trans_apply, TauCeti.separableClosureRingEquiv_algebraMap,
        AlgEquiv.coe_toRingEquiv, sepClosureQ2Equiv_apply, coe_sepEmb_apply]
      rfl

theorem sepClosureEquiv_apply (x : SeparableClosure k) :
    sepClosureEquiv k x =
      (TauCeti.separableClosureRingEquiv ℚ_[2] k (sepEmb k) x : ℚ̄₂) := by
  simp only [sepClosureEquiv, AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply,
    AlgEquiv.coe_toRingEquiv, sepClosureQ2Equiv_apply]

/-- `sepClosureEquiv` restricts to the inclusion on `k`. -/
@[simp] theorem sepClosureEquiv_algebraMap (x : k) :
    sepClosureEquiv k (algebraMap k (SeparableClosure k) x) = (x : ℚ̄₂) :=
  (sepClosureEquiv k).commutes x

/-- The inverse of `sepClosureEquiv` sends `x ∈ k ⊆ ℚ̄₂` to `x ∈ k ⊆ kˢᵉᵖ` (for A2's
Kummer comparison: a square root of `a ∈ k` in `ℚ̄₂` is carried to one in `kˢᵉᵖ`). -/
@[simp] theorem sepClosureEquiv_symm_coe (x : k) :
    (sepClosureEquiv k).symm (x : ℚ̄₂) = algebraMap k (SeparableClosure k) x :=
  (sepClosureEquiv k).symm_apply_eq.2 (sepClosureEquiv_algebraMap k x).symm

variable [FiniteDimensional ℚ_[2] k]

/-- **gq2's `G_k = ↥k.fixingSubgroup` is Tau Ceti's `G_k = Gal(kˢᵉᵖ/k)`**, as topological
groups: `absGalEquivFixing` followed by Tau Ceti's `absoluteGaloisGroupRestrictEquiv`. -/
def fixingEquivAbsGal : k.fixingSubgroup ≃ₜ* TauCeti.AbsoluteGaloisGroup k :=
  (absGalEquivFixing k).symm.trans (TauCeti.absoluteGaloisGroupRestrictEquiv k)

theorem fixingEquivAbsGal_apply (g : k.fixingSubgroup) :
    fixingEquivAbsGal k g =
      TauCeti.absoluteGaloisGroupRestrictEquiv k ((absGalEquivFixing k).symm g) := rfl

/-- **The intertwining property of the dictionary**: `e (Φ g x) = g (e x)` for `g : G_k` and
`x : kˢᵉᵖ`, where `Φ = fixingEquivAbsGal k` and `e = sepClosureEquiv k`. -/
theorem sepClosureEquiv_fixingEquivAbsGal_apply (g : k.fixingSubgroup) (x : SeparableClosure k) :
    sepClosureEquiv k (fixingEquivAbsGal k g x) =
      (g : GQ2.Kummer.GaloisGroup ℚ_[2]) (sepClosureEquiv k x) := by
  rw [sepClosureEquiv_apply, sepClosureEquiv_apply, fixingEquivAbsGal_apply,
    ← TauCeti.absoluteGaloisGroupExtend_apply_separableClosureRingEquiv ℚ_[2] k (sepEmb k),
    absoluteGaloisGroupExtend_absGalEquivFixing_symm]
  exact TauCeti.coe_absoluteGaloisGroupRestrictEquiv_apply (K := ℚ_[2]) _ _

/-- The intertwining property, inverse form: `Φ g (e⁻¹ y) = e⁻¹ (g y)`. -/
theorem fixingEquivAbsGal_apply_sepClosureEquiv_symm (g : k.fixingSubgroup) (y : ℚ̄₂) :
    fixingEquivAbsGal k g ((sepClosureEquiv k).symm y) =
      (sepClosureEquiv k).symm ((g : GQ2.Kummer.GaloisGroup ℚ_[2]) y) := by
  apply (sepClosureEquiv k).injective
  rw [sepClosureEquiv_fixingEquivAbsGal_apply, AlgEquiv.apply_symm_apply,
    AlgEquiv.apply_symm_apply]

end TauCetiModel

/-! ### Finite layers `L/k` inside `ℚ̄₂` -/

section Layers

variable (k : IntermediateField ℚ_[2] ℚ̄₂) (L : IntermediateField k ℚ̄₂)

/-- A layer `L ⊆ ℚ̄₂` over `↥k`, embedded in `kˢᵉᵖ` through `sepClosureEquiv`: Tau Ceti's `σ`
for the extension `L/k`. -/
def layerEmb : L →ₐ[k] SeparableClosure k :=
  (sepClosureEquiv k).symm.toAlgHom.comp L.val

@[simp] theorem sepClosureEquiv_layerEmb (x : L) :
    sepClosureEquiv k (layerEmb k L x) = (x : ℚ̄₂) := by
  simp [layerEmb]

variable [FiniteDimensional ℚ_[2] k] [FiniteDimensional k L]

/-- **`Φ g` lies in Tau Ceti's `G_L = galoisSubgroup k L (layerEmb k L)` iff `g` fixes `L`
pointwise** (in `ℚ̄₂`). -/
theorem fixingEquivAbsGal_mem_galoisSubgroup_iff (g : k.fixingSubgroup) :
    fixingEquivAbsGal k g ∈ TauCeti.galoisSubgroup k L (layerEmb k L) ↔
      ∀ x ∈ L, (g : GQ2.Kummer.GaloisGroup ℚ_[2]) x = x := by
  rw [TauCeti.mem_galoisSubgroup_iff]
  refine ⟨fun h x hx ↦ ?_, fun h x ↦ (sepClosureEquiv k).injective ?_⟩
  · have := congrArg (sepClosureEquiv k) (h ⟨x, hx⟩)
    rwa [sepClosureEquiv_fixingEquivAbsGal_apply, sepClosureEquiv_layerEmb] at this
  · rw [sepClosureEquiv_fixingEquivAbsGal_apply, sepClosureEquiv_layerEmb]
    exact h x x.2

/-- Tau Ceti's `G_L`, pulled back along `Φ`, is the subgroup of `G_k` fixing `L` pointwise. -/
theorem comap_fixingEquivAbsGal_galoisSubgroup :
    (TauCeti.galoisSubgroup k L (layerEmb k L)).toSubgroup.comap
        (fixingEquivAbsGal k).toMonoidHom =
      (L.restrictScalars ℚ_[2]).fixingSubgroup.subgroupOf k.fixingSubgroup := by
  ext g
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, IntermediateField.mem_fixingSubgroup_iff]
  exact fixingEquivAbsGal_mem_galoisSubgroup_iff k L g

end Layers

/-! ### The quadratic layer `quadExt k δ = k(δ)` (B9): membership is the stabilizer of `δ` -/

section QuadExt

variable (k : IntermediateField ℚ_[2] ℚ̄₂) (δ : ℚ̄₂)

/-- `k(δ)/k` is finite when it has degree `2` (the B9 hypothesis `hdeg`). -/
theorem finiteDimensional_quadExt_of_finrank_eq_two
    (hdeg : Module.finrank k (quadExt k δ) = 2) : FiniteDimensional k (quadExt k δ) :=
  Module.finite_of_finrank_eq_succ hdeg

/-- An element of `G_k` fixing `δ` fixes `k(δ)` pointwise. -/
theorem fixingSubgroup_apply_eq_self_of_mem_quadExt (g : k.fixingSubgroup)
    (hδ : (g : GQ2.Kummer.GaloisGroup ℚ_[2]) δ = δ) {x : ℚ̄₂} (hx : x ∈ quadExt k δ) :
    (g : GQ2.Kummer.GaloisGroup ℚ_[2]) x = x := by
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hδ
  | algebraMap x => exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 x x.2
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

variable [FiniteDimensional ℚ_[2] k] [FiniteDimensional k (quadExt k δ)]

/-- **B9's `G_L`**: `Φ g ∈ galoisSubgroup k (quadExt k δ) (layerEmb …) ↔ g • δ = δ`. -/
theorem fixingEquivAbsGal_mem_galoisSubgroup_quadExt_iff (g : k.fixingSubgroup) :
    fixingEquivAbsGal k g ∈
        TauCeti.galoisSubgroup k (quadExt k δ) (layerEmb k (quadExt k δ)) ↔
      (g : GQ2.Kummer.GaloisGroup ℚ_[2]) • δ = δ := by
  rw [fixingEquivAbsGal_mem_galoisSubgroup_iff, AlgEquiv.smul_def]
  exact ⟨fun h ↦ h δ (IntermediateField.mem_adjoin_simple_self k δ),
    fun h x hx ↦ fixingSubgroup_apply_eq_self_of_mem_quadExt k δ g h hx⟩

/-- **B9's `G_L`, in gq2's spelling**: `Φ g ∈ galoisSubgroup k (quadExt k δ) … ↔
g ∈ (stabilizer δ).subgroupOf k.fixingSubgroup`. -/
theorem fixingEquivAbsGal_mem_galoisSubgroup_quadExt_iff_mem_stabilizer (g : k.fixingSubgroup) :
    fixingEquivAbsGal k g ∈
        TauCeti.galoisSubgroup k (quadExt k δ) (layerEmb k (quadExt k δ)) ↔
      g ∈ (MulAction.stabilizer (GQ2.Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup := by
  rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff,
    fixingEquivAbsGal_mem_galoisSubgroup_quadExt_iff]

/-- Tau Ceti's `G_L` for `L = k(δ)`, pulled back along `Φ`, is gq2's
`U = (stab δ).subgroupOf G_k`. -/
theorem comap_fixingEquivAbsGal_galoisSubgroup_quadExt :
    (TauCeti.galoisSubgroup k (quadExt k δ) (layerEmb k (quadExt k δ))).toSubgroup.comap
        (fixingEquivAbsGal k).toMonoidHom =
      (MulAction.stabilizer (GQ2.Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf k.fixingSubgroup := by
  ext g
  rw [Subgroup.mem_comap]
  exact fixingEquivAbsGal_mem_galoisSubgroup_quadExt_iff_mem_stabilizer k δ g

end QuadExt

/-! ### The cyclotomic character -/

section Cyclotomic

/-- gq2's `χ_cyc` is Tau Ceti's `localCyclotomicCharacter 2 ℚ₂` (both are Mathlib's
`cyclotomicCharacter ℚ̄₂ 2` on the underlying ring automorphism). -/
theorem chiCyc_eq_localCyclotomicCharacter (g : GQ2.AbsGalQ2) :
    GQ2.chiCyc g = TauCeti.localCyclotomicCharacter 2 ℚ_[2] g :=
  (TauCeti.localCyclotomicCharacter_apply 2 ℚ_[2] g).symm

/-- `chiCyc_eq_localCyclotomicCharacter` as an equality of homomorphisms. -/
theorem chiCyc_eq : GQ2.chiCyc = TauCeti.localCyclotomicCharacter 2 ℚ_[2] :=
  MonoidHom.ext chiCyc_eq_localCyclotomicCharacter

/-- gq2's abelianized `χ_cyc` is Tau Ceti's `abelianizedLocalCyclotomicCharacter 2 ℚ₂`. -/
theorem chiCycAb_eq_abelianizedLocalCyclotomicCharacter (x : GQ2.AbsGalQ2ab) :
    GQ2.chiCycAb x = TauCeti.abelianizedLocalCyclotomicCharacter 2 ℚ_[2] x := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [TauCeti.abelianizedLocalCyclotomicCharacter_mk]
    exact chiCyc_eq_localCyclotomicCharacter g

/-- `chiCycAb_eq_abelianizedLocalCyclotomicCharacter` as an equality of homomorphisms. -/
theorem chiCycAb_eq :
    GQ2.chiCycAb = (TauCeti.abelianizedLocalCyclotomicCharacter 2 ℚ_[2]).toMonoidHom :=
  MonoidHom.ext chiCycAb_eq_abelianizedLocalCyclotomicCharacter

end Cyclotomic

/-! ### Krull: open subgroups of `Gal(ℚ̄₂/ℚ₂)` are the fixing subgroups of finite layers (B6)

Stated for `U : Subgroup GQ2.AbsGalQ2` (B6 starts from `ι.range` for `ι : G →* AbsGalQ2`, and
`absGalFixedFieldEquiv` must land in that spelling of `↥U` to compose with
`ContinuousMonoidHom.equivRangeOfIsEmbedding`); a `Subgroup (GQ2.Kummer.GaloisGroup ℚ_[2])` such
as `k.fixingSubgroup` is accepted at that type (`example` below). -/

section Krull

variable (U : Subgroup GQ2.AbsGalQ2)

/-- An open (hence closed) subgroup is the fixing subgroup of its fixed field. -/
theorem fixingSubgroup_fixedField_of_isOpen (hU : IsOpen (U : Set GQ2.AbsGalQ2)) :
    (IntermediateField.fixedField U).fixingSubgroup = U :=
  haveI := isGalois_algebraicClosure
  InfiniteGalois.fixingSubgroup_fixedField ⟨U, Subgroup.isClosed_of_isOpen U hU⟩

/-- The fixed field of an open subgroup is finite over `ℚ₂`. -/
theorem finiteDimensional_fixedField_of_isOpen
    (hU : IsOpen (U : Set GQ2.AbsGalQ2)) :
    FiniteDimensional ℚ_[2] (IntermediateField.fixedField U) := by
  have := isGalois_algebraicClosure
  rw [← InfiniteGalois.isOpen_iff_finite, fixingSubgroup_fixedField_of_isOpen U hU]
  exact hU

/-- The degree of the fixed field of an open subgroup is its index. -/
theorem finrank_fixedField_of_isOpen (hU : IsOpen (U : Set GQ2.AbsGalQ2)) :
    Module.finrank ℚ_[2] (IntermediateField.fixedField U) = U.index := by
  have := isGalois_algebraicClosure
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, fixingSubgroup_fixedField_of_isOpen U hU]
  -- `U.index` in the two spellings of the group structure on `Gal(ℚ̄₂/ℚ₂)`
  rfl

/-- **`U` is the absolute Galois group of its fixed field**: `absGalEquivFixing` at
`k = fixedField U`, with `k.fixingSubgroup = U`. -/
def absGalFixedFieldEquiv (hU : IsOpen (U : Set GQ2.AbsGalQ2)) :
    Field.absoluteGaloisGroup (IntermediateField.fixedField U) ≃ₜ* U :=
  haveI := finiteDimensional_fixedField_of_isOpen U hU
  TauCeti.absoluteGaloisGroupExtendEquiv ℚ_[2] _ (sepEmb _)
    ((range_absoluteGaloisGroupExtend_sepEmb _).trans (fixingSubgroup_fixedField_of_isOpen U hU))

@[simp] theorem coe_absGalFixedFieldEquiv_apply
    (hU : IsOpen (U : Set GQ2.AbsGalQ2))
    (g : Field.absoluteGaloisGroup (IntermediateField.fixedField U)) :
    haveI := finiteDimensional_fixedField_of_isOpen U hU
    ((absGalFixedFieldEquiv U hU g : U) : GQ2.AbsGalQ2) =
      TauCeti.absoluteGaloisGroupExtend ℚ_[2] _ (sepEmb _) g :=
  haveI := finiteDimensional_fixedField_of_isOpen U hU
  TauCeti.coe_absoluteGaloisGroupExtendEquiv_apply _ _ _ _ g

/-- A subgroup of `GQ2.Kummer.GaloisGroup ℚ_[2]` (e.g. a fixing subgroup) is accepted where a
subgroup of `GQ2.AbsGalQ2` is expected, and so is its openness. -/
example (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k] :
    (IntermediateField.fixedField k.fixingSubgroup).fixingSubgroup = k.fixingSubgroup :=
  fixingSubgroup_fixedField_of_isOpen k.fixingSubgroup (IntermediateField.fixingSubgroup_isOpen k)

end Krull

/-! ### `rho k`: restriction of `G_k` to `ℚ₂ˢᵉᵖ`, landing in `galoisSubgroup ℚ₂ k (sepEmb k)`
(B11a) -/

section Rho

variable (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]

theorem restrictEquiv_mem_galoisSubgroup_of_mem (g : GQ2.Kummer.GaloisGroup ℚ_[2])
    (hg : g ∈ k.fixingSubgroup) :
    TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2] g ∈
      TauCeti.galoisSubgroup ℚ_[2] k (sepEmb k) :=
  (TauCeti.mem_range_absoluteGaloisGroupExtend_iff ℚ_[2] k (sepEmb k)).1
    (by rw [range_absoluteGaloisGroupExtend_sepEmb]; exact hg)

theorem restrictEquiv_symm_mem_fixingSubgroup_of_mem_galoisSubgroup
    (h : TauCeti.AbsoluteGaloisGroup ℚ_[2])
    (hh : h ∈ TauCeti.galoisSubgroup ℚ_[2] k (sepEmb k)) :
    (TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2]).symm h ∈ k.fixingSubgroup := by
  have := (TauCeti.mem_range_absoluteGaloisGroupExtend_iff ℚ_[2] k (sepEmb k)
    (g := (TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2]).symm h)).2
    (by rwa [ContinuousMulEquiv.apply_symm_apply])
  rwa [range_absoluteGaloisGroupExtend_sepEmb] at this

/-- `ρ : G_k (gq2) ≃ₜ* galoisSubgroup ℚ₂ k (sepEmb k)`, restriction of `g ∈ Gal(ℚ̄₂/ℚ₂)` to
`ℚ₂ˢᵉᵖ`.  Built by hand: Tau Ceti's `absoluteGaloisGroupRestrictSubgroupEquiv` lands in
`↥(sepEmb k).fieldRange.fixingSubgroup`, which is not definitionally `↥(galoisSubgroup …)`
from a `module` file. -/
def rho : k.fixingSubgroup ≃ₜ* ↥(TauCeti.galoisSubgroup ℚ_[2] k (sepEmb k)).toSubgroup where
  toFun g :=
    ⟨TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2] (g : GQ2.Kummer.GaloisGroup ℚ_[2]),
      restrictEquiv_mem_galoisSubgroup_of_mem k g g.2⟩
  invFun h := ⟨(TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2]).symm h,
    restrictEquiv_symm_mem_fixingSubgroup_of_mem_galoisSubgroup k h h.2⟩
  left_inv _ := Subtype.ext ((TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2]).symm_apply_apply _)
  right_inv _ := Subtype.ext ((TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2]).apply_symm_apply _)
  map_mul' _ _ := Subtype.ext (map_mul (TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2]) _ _)
  continuous_toFun :=
    ((TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2]).continuous.comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2]).symm.continuous.comp
      continuous_subtype_val).subtype_mk _

@[simp] theorem coe_rho_apply (g : k.fixingSubgroup) :
    (rho k g : TauCeti.AbsoluteGaloisGroup ℚ_[2]) =
      TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2] (g : GQ2.Kummer.GaloisGroup ℚ_[2]) := rfl

/-- `ρ g` acts on `y ∈ ℚ₂ˢᵉᵖ` as `g` acts on `y ∈ ℚ̄₂`. -/
@[simp] theorem coe_rho_apply_apply (g : k.fixingSubgroup) (y : SeparableClosure ℚ_[2]) :
    ((rho k g : TauCeti.AbsoluteGaloisGroup ℚ_[2]) y : ℚ̄₂) =
      (g : GQ2.Kummer.GaloisGroup ℚ_[2]) y :=
  TauCeti.coe_absoluteGaloisGroupRestrictEquiv_apply (K := ℚ_[2]) _ y

/-- `ρ` is `Φ = fixingEquivAbsGal k` followed by Tau Ceti's
`galoisSubgroupEquiv ℚ₂ k (sepEmb k)`. -/
theorem coe_rho_eq_galoisSubgroupEquiv_fixingEquivAbsGal (g : k.fixingSubgroup) :
    (rho k g : TauCeti.AbsoluteGaloisGroup ℚ_[2]) =
      (TauCeti.galoisSubgroupEquiv ℚ_[2] k (sepEmb k) (fixingEquivAbsGal k g) :
        TauCeti.AbsoluteGaloisGroup ℚ_[2]) := by
  rw [coe_rho_apply, fixingEquivAbsGal_apply,
    ← TauCeti.absoluteGaloisGroupRestrictEquiv_absoluteGaloisGroupExtend,
    absoluteGaloisGroupExtend_absGalEquivFixing_symm]

end Rho

end GQ2.TauCetiBridge

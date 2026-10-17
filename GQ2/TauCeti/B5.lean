/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5.1
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.ArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Unramified
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Reciprocity
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Cyclotomic
public import TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.ArtinMap
public import TauCeti.NumberTheory.LocalField.Unramified.Coordinate
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Component
public import GQ2.Reciprocity
public import GQ2.TauCeti.GaloisDict

@[expose] public section

/-!
# B5: the local reciprocity bundle, discharged from Tau Ceti

Ticket **B5** of the Tau Ceti discharge campaign
(`docs/orchestration/tauceti-tickets.md`, memo `docs/orchestration/tauceti-t2-recon.md`, §B5).
This file provides

* `GQ2.TauCetiBridge.localReciprocity_tauceti : GQ2.LocalReciprocity`, a term of the type of the
  `localReciprocity` field of `GQ2.LiteratureInputs`, built from Tau Ceti's local class field
  theory for `ℚ₂`, with no `sorry` and at the standard three axioms;
* the named facts that ticket **B10** (oriented tame quotient) and the assembly ticket C1 consume:
  `localReciprocity_tauceti_recip` (`recip` is `TauCeti.ClassFieldTheory.artinMap ℚ_[2]`),
  `localReciprocity_tauceti_nu_ur`, the general lift lemma
  `zHat_lift_unramifiedCoordinate_artinMap` (`lift a ∘ unramifiedCoordinate ∘ artinMap = a ^ v₂`),
  and the valuations `v2_unitEmbed`, `v2_uniformizer`.

## Translation (memo §B5)

* `recip := TauCeti.ClassFieldTheory.artinMap ℚ_[2]`, with no cast: the Artin map's target is
  literally `GQ2.AbsGalQ2ab`. Both `recip` and Tau Ceti's Artin map are *arithmetic* (the
  uniformizer goes to arithmetic Frobenius). Continuity and density are Tau Ceti's theorems.
* `nu_ur := nuUr`, the **inverse** of the `ℤ₂`-reduction `zHat.lift (ofAdd 1)` of Tau Ceti's
  (arithmetic) `unramifiedCoordinate ℚ_[2]`; gq2's `ν_ur` is normalized geometrically, which is
  where the inversion comes from. `nu_ur_recip` is `unramifiedCoordinate_artinMap` +
  `zHat.lift_ofInt` + `Padic.toAdd_normalizedValuation_eq_valuation`.
* The cyclotomic clauses are `localCyclotomicCharacter_artinMap_padic` and
  `localCyclotomicCharacter_artinMap_padic_uniformizer`, read through
  `localCyclotomicCharacter_apply` (gq2's `chiCyc` is Mathlib's `cyclotomicCharacter`).
* `norm_reciprocity` goes through the finite-layer map `localArtinMap ℚ_[2] L ι` for the
  embedding `ι = layerEmbedding L` of the layer into the separable closure:
  `artinMap_restrict` identifies it with `restrictAb L hab ∘ artinMap`, then
  `surjective_localArtinMap` gives surjectivity and `localArtinMap_eq_zero_iff` the kernel,
  with `normSubgroup L = TauCeti.normGroup ℚ_[2] L` by `mem_normGroup_iff`.

## Instance notes

* `Algebra.IsSeparable ℚ_[2] ↥L` for a finite Galois layer times out under these imports
  (memo, cross-cutting 2); it is supplied as `IsGalois.to_isSeparable` inside `layerEmbedding`.
* `rw` with `coe_absoluteGaloisGroupRestrictEquiv_apply` misses on `AbsGalQ2`-typed terms
  (cross-cutting 6); it is applied as a term with `.trans`.

This file needs none of the Wave 1 dictionaries (A1, A2, P1).
-/

namespace GQ2.TauCetiBridge

/-! ## The finite layers: embedding into the separable closure and restriction -/

/-- The embedding of a finite Galois layer `L ⊆ ℚ̄₂` into Tau Ceti's `SeparableClosure ℚ_[2]`
(the separable closure of `ℚ₂` inside `ℚ̄₂`), the `ι` that Tau Ceti's finite-layer reciprocity
`localArtinMap ℚ_[2] L ι` is stated for. -/
noncomputable def layerEmbedding (L : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] L] [IsGalois ℚ_[2] L] : L →ₐ[ℚ_[2]] SeparableClosure ℚ_[2] :=
  haveI : Algebra.IsSeparable ℚ_[2] L := IsGalois.to_isSeparable
  L.val.codRestrict (separableClosure ℚ_[2] (AlgebraicClosure ℚ_[2])).toSubalgebra
    fun z ↦ mem_separableClosure_iff.2 ((Algebra.IsSeparable.isSeparable ℚ_[2] z).map L.val
      L.val.injective)

@[simp]
theorem coe_layerEmbedding_apply (L : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] L] [IsGalois ℚ_[2] L] (y : L) :
    ((layerEmbedding L y : SeparableClosure ℚ_[2]) : AlgebraicClosure ℚ_[2]) = y :=
  AlgHom.coe_codRestrict _ _ _ y

/-- Restricting `σ ∈ G_{ℚ₂}` to the layer `L` through Tau Ceti's separable-closure model
(`absoluteGaloisGroupRestrictEquiv` then `restrictNormalHom` along `layerEmbedding L`) is gq2's
`restrictHom L σ`. -/
theorem restrictNormalHom_layerEmbedding (L : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] L] [IsGalois ℚ_[2] L] (σ : AbsGalQ2) :
    (layerEmbedding L).restrictNormalHom (TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[2] σ) =
      restrictHom L σ := by
  refine AlgEquiv.ext fun y ↦ (layerEmbedding L).injective <|
    ((layerEmbedding L).restrictNormalHom_commutes _ y).trans (Subtype.ext ?_)
  refine (TauCeti.coe_absoluteGaloisGroupRestrictEquiv_apply (K := ℚ_[2]) σ _).trans ?_
  change DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[2]/ℚ_[2])) σ
      ((layerEmbedding L y : SeparableClosure ℚ_[2]) : AlgebraicClosure ℚ_[2]) =
    ((layerEmbedding L (restrictHom L σ y) : SeparableClosure ℚ_[2]) : AlgebraicClosure ℚ_[2])
  rw [coe_layerEmbedding_apply, coe_layerEmbedding_apply]
  exact (AlgEquiv.restrictNormal_commutes σ L y).symm

/-- Tau Ceti's finite-layer Artin map along `layerEmbedding L` is gq2's `restrictAb L hab` after
the absolute Artin map (`artinMap_restrict`, with gq2's `toAb` as the lift). -/
theorem localArtinMap_layerEmbedding (L : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] L] [IsGalois ℚ_[2] L]
    (hab : ∀ σ τ : (L ≃ₐ[ℚ_[2]] L), σ * τ = τ * σ) (x : ℚ_[2]ˣ) :
    TauCeti.ClassFieldTheory.localArtinMap ℚ_[2] L (layerEmbedding L) (Additive.ofMul x) =
      Additive.ofMul (Abelianization.of
        (restrictAb L hab (TauCeti.ClassFieldTheory.artinMap ℚ_[2] x))) := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective commClosure
    (TauCeti.ClassFieldTheory.artinMap ℚ_[2] x)
  rw [← hg]
  change _ = Additive.ofMul (Abelianization.of (restrictAb L hab (toAb g)))
  rw [restrictAb_toAb, ← restrictNormalHom_layerEmbedding]
  exact TauCeti.ClassFieldTheory.artinMap_restrict ℚ_[2] L (layerEmbedding L) x g hg

/-- gq2's norm subgroup of a finite layer is Tau Ceti's `normGroup`. -/
theorem normSubgroup_eq_normGroup (L : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] L] : normSubgroup L = TauCeti.normGroup ℚ_[2] L := by
  ext y
  rw [TauCeti.mem_normGroup_iff]
  simp [normSubgroup, Units.ext_iff]

/-- **Clause (a), norm residue**, for `recip = artinMap ℚ_[2]`: on every finite abelian Galois
layer `L/ℚ₂`, `restrictAb L hab ∘ artinMap` is surjective with kernel `normSubgroup L`. -/
theorem norm_reciprocity_tauceti (L : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] L] [IsGalois ℚ_[2] L]
    (hab : ∀ σ τ : (L ≃ₐ[ℚ_[2]] L), σ * τ = τ * σ) :
    Function.Surjective ((restrictAb L hab).comp
        (TauCeti.ClassFieldTheory.artinMap ℚ_[2] : ℚ_[2]ˣ →* AbsGalQ2ab)) ∧
      ((restrictAb L hab).comp
        (TauCeti.ClassFieldTheory.artinMap ℚ_[2] : ℚ_[2]ˣ →* AbsGalQ2ab)).ker =
          normSubgroup L := by
  -- `hab` makes `Gal(L/ℚ₂)` commutative, so `Abelianization.of` is injective on it.
  let _ : CommGroup (L ≃ₐ[ℚ_[2]] L) :=
    { (inferInstance : Group (L ≃ₐ[ℚ_[2]] L)) with mul_comm := hab }
  have hinj : Function.Injective (Abelianization.of (G := L ≃ₐ[ℚ_[2]] L)) :=
    (Abelianization.equivOfComm (H := L ≃ₐ[ℚ_[2]] L)).injective
  refine ⟨fun τ ↦ ?_, ?_⟩
  · obtain ⟨a, ha⟩ := TauCeti.ClassFieldTheory.surjective_localArtinMap ℚ_[2] L
      (layerEmbedding L) (Additive.ofMul (Abelianization.of τ))
    refine ⟨Additive.toMul a, hinj (Additive.ofMul.injective ?_)⟩
    rw [MonoidHom.comp_apply, ← localArtinMap_layerEmbedding, ofMul_toMul, ha]
  · ext x
    rw [MonoidHom.mem_ker, normSubgroup_eq_normGroup,
      ← TauCeti.ClassFieldTheory.localArtinMap_eq_zero_iff ℚ_[2] L (layerEmbedding L),
      localArtinMap_layerEmbedding L hab, MonoidHom.comp_apply]
    constructor
    · intro h; rw [h, map_one, ofMul_one]
    · intro h
      apply hinj
      rw [map_one]
      exact Additive.ofMul.injective h

/-! ## The unramified coordinate -/

/-- The geometric unramified coordinate `ν_ur : G_{ℚ₂}^{ab} →* Multiplicative ℤ₂`: the
**inverse** of the `ℤ₂`-reduction (`zHat.lift (ofAdd 1)`) of Tau Ceti's arithmetic
`unramifiedCoordinate ℚ_[2]`. -/
noncomputable def nuUr : AbsGalQ2ab →* Multiplicative ℤ_[2] :=
  (invMonoidHom : Multiplicative ℤ_[2] →* Multiplicative ℤ_[2]).comp
    ((TauCeti.zHat.lift (Multiplicative.ofAdd (1 : ℤ_[2]))).toMonoidHom.comp
      (TauCeti.unramifiedCoordinate ℚ_[2]).toMonoidHom)

@[simp]
theorem nuUr_apply (x : AbsGalQ2ab) :
    nuUr x = (TauCeti.zHat.lift (Multiplicative.ofAdd (1 : ℤ_[2]))
      (TauCeti.unramifiedCoordinate ℚ_[2] x))⁻¹ := rfl

theorem continuous_nuUr : Continuous nuUr :=
  continuous_inv.comp ((TauCeti.zHat.lift _).continuous.comp
    (TauCeti.unramifiedCoordinate ℚ_[2]).continuous)

theorem surjective_nuUr : Function.Surjective nuUr := by
  intro y
  obtain ⟨z, hz⟩ := TauCeti.zHat.component_surjective 2 (-(Multiplicative.toAdd y))
  obtain ⟨x, hx⟩ := TauCeti.unramifiedCoordinate_surjective ℚ_[2] (Additive.toMul z)
  refine ⟨x, ?_⟩
  simp only [nuUr_apply, hx, TauCeti.zHat.lift_ofAdd_one_padicInt_apply]
  simp [hz]

/-- **The valuation lemma behind both orientation clauses.** Any `ℤ̂`-lift `zHat.lift a` into a
profinite group, applied to the unramified coordinate of the Artin image of `x`, is `a ^ v₂ x`.
At `a = ofAdd 1` this is `nu_ur_recip` (up to the inversion); B10 uses it at `a = ztwoOne⁻¹`. -/
theorem zHat_lift_unramifiedCoordinate_artinMap {P : Type*} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [TotallyDisconnectedSpace P] (a : P) (x : ℚ_[2]ˣ) :
    TauCeti.zHat.lift a (TauCeti.unramifiedCoordinate ℚ_[2]
      (TauCeti.ClassFieldTheory.artinMap ℚ_[2] x)) = a ^ v2 x := by
  rw [TauCeti.ClassFieldTheory.unramifiedCoordinate_artinMap, TauCeti.zHat.lift_ofInt,
    Padic.toAdd_normalizedValuation_eq_valuation]
  rfl

/-- **Clause (b), unramified normalization**, for `recip = artinMap ℚ_[2]`: `ν_ur ∘ rec = −v₂`. -/
theorem nuUr_artinMap (x : ℚ_[2]ˣ) :
    nuUr (TauCeti.ClassFieldTheory.artinMap ℚ_[2] x) =
      Multiplicative.ofAdd ((-(v2 x) : ℤ) : ℤ_[2]) := by
  rw [nuUr_apply, zHat_lift_unramifiedCoordinate_artinMap, ← ofAdd_zsmul, ← ofAdd_neg]
  simp

/-! ## Valuations of the two test elements (used by B10's orientation clauses) -/

theorem v2_unitEmbed (u : ℤ_[2]ˣ) : v2 (unitEmbed u) = 0 := by
  have hv : (u : ℤ_[2]).valuation = 0 := by
    have h := PadicInt.valuation_mul (p := 2) u.ne_zero u⁻¹.ne_zero
    rw [Units.mul_inv, PadicInt.valuation_one] at h
    omega
  simp [v2, unitEmbed, hv]

theorem v2_uniformizer : v2 uniformizer = 1 := by
  simp [v2, uniformizer]

/-! ## The cyclotomic clauses -/

/-- **Clause (c), units**, for `recip = artinMap ℚ_[2]`: `χ_cyc(rec u) = u⁻¹` for `u ∈ ℤ₂ˣ`. -/
theorem chiCycAb_artinMap_unitEmbed (u : ℤ_[2]ˣ) :
    chiCycAb (TauCeti.ClassFieldTheory.artinMap ℚ_[2] (unitEmbed u)) = u⁻¹ := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective commClosure
    (TauCeti.ClassFieldTheory.artinMap ℚ_[2] (unitEmbed u))
  rw [← hg]
  change chiCycAb (toAb g) = u⁻¹
  rw [chiCycAb_toAb, chiCyc_eq_localCyclotomicCharacter]
  exact TauCeti.ClassFieldTheory.localCyclotomicCharacter_artinMap_padic 2 u g hg

/-- **Clause (c), uniformizer**, for `recip = artinMap ℚ_[2]`: `χ_cyc(rec 2) = 1`. -/
theorem chiCycAb_artinMap_uniformizer :
    chiCycAb (TauCeti.ClassFieldTheory.artinMap ℚ_[2] uniformizer) = 1 := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective commClosure
    (TauCeti.ClassFieldTheory.artinMap ℚ_[2] uniformizer)
  rw [← hg]
  change chiCycAb (toAb g) = 1
  rw [chiCycAb_toAb, chiCyc_eq_localCyclotomicCharacter]
  exact TauCeti.ClassFieldTheory.localCyclotomicCharacter_artinMap_padic_uniformizer 2 g hg

/-! ## The bundle -/

/-- **B5, discharged.** gq2's local reciprocity bundle for `ℚ₂`, with `recip` Tau Ceti's Artin
map and `nu_ur` the geometric unramified coordinate `nuUr`. -/
noncomputable def localReciprocity_tauceti : LocalReciprocity where
  recip := TauCeti.ClassFieldTheory.artinMap ℚ_[2]
  continuous_recip := TauCeti.ClassFieldTheory.continuous_artinMap ℚ_[2]
  denseRange_recip := TauCeti.ClassFieldTheory.denseRange_artinMap ℚ_[2]
  nu_ur := nuUr
  continuous_nu_ur := continuous_nuUr
  surjective_nu_ur := surjective_nuUr
  norm_reciprocity := norm_reciprocity_tauceti
  nu_ur_recip := nuUr_artinMap
  chiCyc_recip_unit := chiCycAb_artinMap_unitEmbed
  chiCyc_recip_uniformizer := chiCycAb_artinMap_uniformizer

/-- The reciprocity map of the bundle is Tau Ceti's Artin map (B10 rewrites its hypotheses
`toAb g = localReciprocity_tauceti.recip x` with this). -/
@[simp]
theorem localReciprocity_tauceti_recip :
    localReciprocity_tauceti.recip = TauCeti.ClassFieldTheory.artinMap ℚ_[2] := rfl

/-- The unramified coordinate of the bundle is `nuUr`. -/
@[simp]
theorem localReciprocity_tauceti_nu_ur : localReciprocity_tauceti.nu_ur = nuUr := rfl

end GQ2.TauCetiBridge

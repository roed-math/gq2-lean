/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateAbsoluteResidueBaseChange

/-!
# Relative unit-index reciprocity for the uniform odd-degree endpoint

The anchored norm residue was previously exposed as `AnchoredUnitSpectralReciprocity`, a
statement quantified over every finite group homomorphism.  The determinant consumer uses only
homomorphisms factoring through `Tq`.  For those uses, this module proves that the prescribed
anchored field is a finite abelian Galois extension of `K`: its defining subgroup contains the
commutator subgroup because `Tq/inertiaPartQ` is the procyclic group `Zhat`.

This identifies the conventional local-CFT input precisely.  `RelativeUnitIndexReciprocity`
says, uniformly for every finite abelian layer `L/K`, that the image of spectral units under
marked reciprocity has cardinality `e(L/K)`.  It is the direct relative analogue of
`UnitNormIndex.card_unitImage_eq_e` over `Q_2`.  The main adapter proves every compatible
anchored field unramified from this single standard theorem, and the final endpoint eliminates
the custom per-action spectral premise.

The present `MarkedRecip` bundle deliberately omits finite-layer norm reciprocity over `K`, so
`RelativeUnitIndexReciprocity` is not inferred here.  This module proves the full group/field
reduction around it without a nilpotency class, presentation family, or handle-count hypothesis.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

private theorem zhat_mul_comm_relativeUnitIndex (a b : Zhat) : a * b = b * a := by
  have ofInt_mul_comm : ∀ n : ℤ, Zhat.ofInt n * b = b * Zhat.ofInt n := by
    intro n
    have h := Zhat.funext_ofInt
      (f := fun z => Zhat.ofInt n * z) (g := fun z => z * Zhat.ofInt n)
      (continuous_const_mul _) (continuous_mul_const _)
      (fun m => by rw [← Zhat.ofInt_add, ← Zhat.ofInt_add, Int.add_comm])
    exact congrFun h b
  have h := Zhat.funext_ofInt (f := fun z => z * b) (g := fun z => b * z)
    (continuous_mul_const _) (continuous_const_mul _) ofInt_mul_comm
  exact congrFun h a

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]

/-- Restriction from `G_K` to a finite normal layer presented inside `Qbar_2`. -/
noncomputable def relativeRestrictHom
    (L : IntermediateField ℚ_[2] ℚ̄₂) (hKL : K ≤ L)
    [Normal (↥K) (IntermediateField.extendScalars hKL)] :
    GalK K →* ((IntermediateField.extendScalars hKL) ≃ₐ[↥K]
      (IntermediateField.extendScalars hKL)) :=
  (AlgEquiv.restrictNormalHom (IntermediateField.extendScalars hKL)).comp
    (IntermediateField.fixingSubgroupEquiv K).toMonoidHom

/-- The restrictions to `L` of lifts of reciprocity classes of spectral units. -/
noncomputable def relativeReciprocityUnitImage
    (B : MarkedRecip R K) (L : IntermediateField ℚ_[2] ℚ̄₂) (hKL : K ≤ L)
    [Normal (↥K) (IntermediateField.extendScalars hKL)] :
    Subgroup ((IntermediateField.extendScalars hKL) ≃ₐ[↥K]
      (IntermediateField.extendScalars hKL)) where
  carrier := {σ | ∃ u : ↥(normUnits K), ∃ g : GalK K,
    toAbK K g = B.recip u.1 ∧ relativeRestrictHom L hKL g = σ}
  one_mem' := ⟨1, 1, by simp [relativeRestrictHom]⟩
  mul_mem' := by
    rintro σ τ ⟨u, g, hgu, rfl⟩ ⟨v, h, hhv, rfl⟩
    refine ⟨u * v, g * h, ?_, ?_⟩
    · rw [map_mul, hgu, hhv]
      exact (map_mul B.recip u.1 v.1).symm
    · exact map_mul _ _ _
  inv_mem' := by
    rintro σ ⟨u, g, hgu, rfl⟩
    refine ⟨u⁻¹, g⁻¹, ?_, ?_⟩
    · rw [map_inv, hgu]
      exact (map_inv B.recip u.1).symm
    · exact map_inv _ _

/-- The conventional relative local-CFT unit-index theorem, uniformly over finite abelian
layers inside `Qbar_2`. -/
def RelativeUnitIndexReciprocity (B : MarkedRecip R K)
    (FK : DyadicUnitFiltration K) : Prop :=
  ∀ (L : IntermediateField ℚ_[2] ℚ̄₂) (hKL : K ≤ L)
    [FiniteDimensional ℚ_[2] L]
    [FiniteDimensional (↥K) (IntermediateField.extendScalars hKL)]
    [IsGalois (↥K) (IntermediateField.extendScalars hKL)]
    (_hab : ∀ σ τ : ((IntermediateField.extendScalars hKL) ≃ₐ[↥K]
      (IntermediateField.extendScalars hKL)), σ * τ = τ * σ)
    (FL : DyadicUnitFiltration L),
      Nat.card ↥(relativeReciprocityUnitImage B L hKL) =
        (GaloisCosetNorm.relE FK FL hKL).toNat

/-- If every reciprocity unit fixes one finite abelian layer, relative unit-index reciprocity
forces its relative ramification index to be one. -/
theorem relE_eq_one_of_relativeUnitIndexReciprocity
    (B : MarkedRecip R K) (FK : DyadicUnitFiltration K)
    (H : RelativeUnitIndexReciprocity B FK)
    (L : IntermediateField ℚ_[2] ℚ̄₂) (hKL : K ≤ L)
    [FiniteDimensional ℚ_[2] L]
    [FiniteDimensional (↥K) (IntermediateField.extendScalars hKL)]
    [IsGalois (↥K) (IntermediateField.extendScalars hKL)]
    (hab : ∀ σ τ : ((IntermediateField.extendScalars hKL) ≃ₐ[↥K]
      (IntermediateField.extendScalars hKL)), σ * τ = τ * σ)
    (FL : DyadicUnitFiltration L)
    (hfix : ∀ (u : ↥(normUnits K)) (g : GalK K),
      toAbK K g = B.recip u.1 → relativeRestrictHom L hKL g = 1) :
    GaloisCosetNorm.relE FK FL hKL = 1 := by
  have himage : relativeReciprocityUnitImage B L hKL = ⊥ := by
    ext σ
    constructor
    · rintro ⟨u, g, hgu, rfl⟩
      exact (hfix u g hgu : relativeRestrictHom L hKL g = 1)
    · intro hσ
      rw [Subgroup.mem_bot] at hσ
      subst σ
      exact one_mem _
  have hcard := H L hKL hab FL
  rw [himage] at hcard
  have hone : Nat.card ↥(⊥ : Subgroup
      ((IntermediateField.extendScalars hKL) ≃ₐ[↥K]
        (IntermediateField.extendScalars hKL))) = 1 := Nat.card_unique
  rw [hone] at hcard
  have hpos := GaloisCosetNorm.relE_pos FK FL hKL
  have hcast : ((GaloisCosetNorm.relE FK FL hKL).toNat : ℤ) =
      GaloisCosetNorm.relE FK FL hKL :=
    Int.toNat_of_nonneg (by omega)
  omega

omit [FiniteDimensional ℚ_[2] K] in
/-- In a finite quotient factoring through `Tq`, the preimage of the cyclic tau subgroup
contains the commutator subgroup. -/
theorem commutator_le_anchoredTameInertia_preimage
    (P : FieldParameters)
    {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    (tame : ContinuousMonoidHom ↑(GalKsub K) (Tq P.qK))
    (c : ContinuousMonoidHom (Tq P.qK) D)
    (rho : ContinuousMonoidHom ↑(GalKsub K) D)
    (hfac : ∀ g : ↑(GalKsub K), rho g = c (tame g)) :
    commutator (GalK K) ≤
      (Subgroup.zpowers (c (tqTau P.qK))).comap rho.toMonoidHom := by
  rw [show commutator (GalK K) = ⁅(⊤ : Subgroup (GalK K)), ⊤⁆ from rfl,
    Subgroup.commutator_le]
  intro g _ h _
  change rho ((@commutatorElement (GalK K) _).bracket g h) ∈
    Subgroup.zpowers (c (tqTau P.qK))
  rw [hfac]
  apply inertiaPartQ_le_comap_zpowers_tqTau P.qK c
  rw [mem_inertiaPartQ_iff_qMkQ_eq_one, map_commutatorElement]
  apply (qurQEquivZhat P.qK).injective
  simp only [map_commutatorElement, map_one]
  let x : Zhat := qurQEquivZhat P.qK (qMkQ P.qK (tame g))
  let y : Zhat := qurQEquivZhat P.qK (qMkQ P.qK (tame h))
  change x * y * x⁻¹ * y⁻¹ = 1
  rw [mul_assoc x y x⁻¹, zhat_mul_comm_relativeUnitIndex y x⁻¹,
    ← mul_assoc x x⁻¹ y, mul_inv_cancel, one_mul, mul_inv_cancel]

omit [FiniteDimensional ℚ_[2] K] in
/-- Hence that preimage is normal in `G_K`. -/
theorem anchoredTameInertia_preimage_normal
    (P : FieldParameters)
    {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    (tame : ContinuousMonoidHom ↑(GalKsub K) (Tq P.qK))
    (c : ContinuousMonoidHom (Tq P.qK) D)
    (rho : ContinuousMonoidHom ↑(GalKsub K) D)
    (hfac : ∀ g : ↑(GalKsub K), rho g = c (tame g)) :
    ((Subgroup.zpowers (c (tqTau P.qK))).comap rho.toMonoidHom).Normal :=
  Subgroup.Normal.of_commutator_le (G := GalK K)
    (commutator_le_anchoredTameInertia_preimage P tame c rho hfac)

/-- The anchored field of a compatible finite tame quotient is Galois over `K`. -/
theorem anchoredTameInertiaField_relative_isGalois
    (P : FieldParameters)
    {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    (tame : ContinuousMonoidHom ↑(GalKsub K) (Tq P.qK))
    (c : ContinuousMonoidHom (Tq P.qK) D)
    (rho : ContinuousMonoidHom ↑(GalKsub K) D)
    (hfac : ∀ g : ↑(GalKsub K), rho g = c (tame g)) :
    IsGalois (↥K) (IntermediateField.extendScalars
      (baseField_le_anchoredTameInertiaField K rho (c (tqTau P.qK)))) := by
  let H : Subgroup (GalK K) :=
    (Subgroup.zpowers (c (tqTau P.qK))).comap rho.toMonoidHom
  let F₀ := anchoredTameInertiaField (GalKsub K) rho (c (tqTau P.qK))
  let hKF₀ := baseField_le_anchoredTameInertiaField K rho (c (tqTau P.qK))
  let E := IntermediateField.extendScalars hKF₀
  haveI hHN : H.Normal := anchoredTameInertia_preimage_normal P tame c rho hfac
  have hsub : F₀.fixingSubgroup.subgroupOf K.fixingSubgroup = H := by
    ext g
    rw [Subgroup.mem_subgroupOf,
      fixingSubgroup_anchoredTameInertiaField (GalKsub K)
        (isOpen_fixingSubgroup K) rho (c (tqTau P.qK))]
    let g' : ↑(GalKsub K) := ⟨g.1, g.2⟩
    change (g'.1 : AbsGalQ2) ∈ H.map (subtypeAnc (GalKsub K)).toMonoidHom ↔ g' ∈ H
    constructor
    · rintro ⟨x, hx, hxg⟩
      have hxeq : x = g' := subtypeAnc_injective (GalKsub K) hxg
      simpa [hxeq] using hx
    · intro hg
      exact ⟨g', hg, rfl⟩
  have hmap : H.map (IntermediateField.fixingSubgroupEquiv K).toMonoidHom =
      E.fixingSubgroup := by
    rw [← hsub]
    ext g
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf,
      IntermediateField.mem_fixingSubgroup_iff,
      IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h y hy => h y (IntermediateField.mem_extendScalars hKF₀ |>.mp hy),
      fun h y hy => h y (IntermediateField.mem_extendScalars hKF₀ |>.mpr hy)⟩
  have hmapN :
      (H.map (IntermediateField.fixingSubgroupEquiv K).toMonoidHom).Normal :=
    hHN.map (IntermediateField.fixingSubgroupEquiv K).toMonoidHom
      (IntermediateField.fixingSubgroupEquiv K).surjective
  exact (InfiniteGalois.normal_iff_isGalois E).mp (hmap ▸ hmapN)

omit [FiniteDimensional ℚ_[2] K] in
/-- Restriction from `G_K` to a finite Galois layer is surjective. -/
theorem relativeRestrictHom_surjective
    (L : IntermediateField ℚ_[2] ℚ̄₂) (hKL : K ≤ L)
    [FiniteDimensional (↥K) (IntermediateField.extendScalars hKL)]
    [IsGalois (↥K) (IntermediateField.extendScalars hKL)] :
    Function.Surjective (relativeRestrictHom L hKL) := by
  intro σ
  obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := ↥K) (K₁ := IntermediateField.extendScalars hKL) (E := ℚ̄₂) σ
  refine ⟨(IntermediateField.fixingSubgroupEquiv K).symm g, ?_⟩
  change (AlgEquiv.restrictNormalHom (IntermediateField.extendScalars hKL))
      (IntermediateField.fixingSubgroupEquiv K
        ((IntermediateField.fixingSubgroupEquiv K).symm g)) = σ
  rw [(IntermediateField.fixingSubgroupEquiv K).apply_symm_apply, hg]

/-- The defining tame-inertia preimage fixes the corresponding relative anchored layer. -/
theorem anchoredTameInertia_preimage_le_relativeRestrictHom_ker
    (P : FieldParameters)
    {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    (c : ContinuousMonoidHom (Tq P.qK) D)
    (rho : ContinuousMonoidHom ↑(GalKsub K) D)
    [IsGalois (↥K) (IntermediateField.extendScalars
      (baseField_le_anchoredTameInertiaField K rho (c (tqTau P.qK))))] :
    (Subgroup.zpowers (c (tqTau P.qK))).comap rho.toMonoidHom ≤
      (relativeRestrictHom
        (anchoredTameInertiaField (GalKsub K) rho (c (tqTau P.qK)))
        (baseField_le_anchoredTameInertiaField K rho
          (c (tqTau P.qK)))).ker := by
  let H : Subgroup (GalK K) :=
    (Subgroup.zpowers (c (tqTau P.qK))).comap rho.toMonoidHom
  let F₀ := anchoredTameInertiaField (GalKsub K) rho (c (tqTau P.qK))
  let hKF₀ := baseField_le_anchoredTameInertiaField K rho (c (tqTau P.qK))
  let E := IntermediateField.extendScalars hKF₀
  have hsub : F₀.fixingSubgroup.subgroupOf K.fixingSubgroup = H := by
    ext g
    rw [Subgroup.mem_subgroupOf,
      fixingSubgroup_anchoredTameInertiaField (GalKsub K)
        (isOpen_fixingSubgroup K) rho (c (tqTau P.qK))]
    let g' : ↑(GalKsub K) := ⟨g.1, g.2⟩
    change (g'.1 : AbsGalQ2) ∈ H.map (subtypeAnc (GalKsub K)).toMonoidHom ↔ g' ∈ H
    constructor
    · rintro ⟨x, hx, hxg⟩
      have hxeq : x = g' := subtypeAnc_injective (GalKsub K) hxg
      simpa [hxeq] using hx
    · intro hg
      exact ⟨g', hg, rfl⟩
  have hmap : H.map (IntermediateField.fixingSubgroupEquiv K).toMonoidHom =
      E.fixingSubgroup := by
    rw [← hsub]
    ext g
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf,
      IntermediateField.mem_fixingSubgroup_iff,
      IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h y hy => h y (IntermediateField.mem_extendScalars hKF₀ |>.mp hy),
      fun h y hy => h y (IntermediateField.mem_extendScalars hKF₀ |>.mpr hy)⟩
  intro g hg
  change relativeRestrictHom F₀ hKF₀ g = 1
  have hgmap : IntermediateField.fixingSubgroupEquiv K g ∈ E.fixingSubgroup := by
    rw [← hmap]
    exact ⟨g, hg, rfl⟩
  have hgker : IntermediateField.fixingSubgroupEquiv K g ∈
      (AlgEquiv.restrictNormalHom E).ker := by
    rwa [IntermediateField.restrictNormalHom_ker]
  exact hgker

/-- The relative anchored Galois group is abelian: its defining subgroup contains the
commutator subgroup of `G_K`. -/
theorem anchoredTameInertiaField_relative_commutative
    (P : FieldParameters)
    {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    (tame : ContinuousMonoidHom ↑(GalKsub K) (Tq P.qK))
    (c : ContinuousMonoidHom (Tq P.qK) D)
    (rho : ContinuousMonoidHom ↑(GalKsub K) D)
    (hfac : ∀ g : ↑(GalKsub K), rho g = c (tame g))
    [FiniteDimensional (↥K) (IntermediateField.extendScalars
      (baseField_le_anchoredTameInertiaField K rho (c (tqTau P.qK))))]
    [IsGalois (↥K) (IntermediateField.extendScalars
      (baseField_le_anchoredTameInertiaField K rho (c (tqTau P.qK))))] :
    ∀ σ τ : ((IntermediateField.extendScalars
      (baseField_le_anchoredTameInertiaField K rho (c (tqTau P.qK)))) ≃ₐ[↥K]
        (IntermediateField.extendScalars
          (baseField_le_anchoredTameInertiaField K rho (c (tqTau P.qK))))),
      σ * τ = τ * σ := by
  intro σ τ
  let F₀ := anchoredTameInertiaField (GalKsub K) rho (c (tqTau P.qK))
  let hKF₀ := baseField_le_anchoredTameInertiaField K rho (c (tqTau P.qK))
  obtain ⟨g, rfl⟩ := relativeRestrictHom_surjective F₀ hKF₀ σ
  obtain ⟨h, rfl⟩ := relativeRestrictHom_surjective F₀ hKF₀ τ
  have hcomm : (@commutatorElement (GalK K) _).bracket g h ∈
      (Subgroup.zpowers (c (tqTau P.qK))).comap rho.toMonoidHom :=
    commutator_le_anchoredTameInertia_preimage P tame c rho hfac
      (by
        change (@commutatorElement (GalK K) _).bracket g h ∈
          ⁅(⊤ : Subgroup (GalK K)), ⊤⁆
        exact Subgroup.commutator_mem_commutator
          (Subgroup.mem_top g) (Subgroup.mem_top h))
  have hres := anchoredTameInertia_preimage_le_relativeRestrictHom_ker
    P c rho hcomm
  rw [MonoidHom.mem_ker, map_commutatorElement] at hres
  exact (commutatorElement_eq_one_iff_commute.mp hres).eq

/-- Relative unit-index reciprocity closes the prescribed anchored-field residue for every
compatible finite tame action.  Unlike `AnchoredUnitSpectralReciprocity`, the input ranges only
over ordinary finite abelian layers; compatibility proves that every field used here is one. -/
theorem anchoredTameInertiaRelativeUnramifiedDataAt_of_relativeUnitIndexReciprocity
    (P : FieldParameters)
    (B : MarkedRecip R K) (FK : DyadicUnitFiltration K)
    (tame : ContinuousMonoidHom ↑(GalKsub K) (Tq P.qK))
    (Hunit : TameUnitInertiaRefinementAt P K B tame)
    (Hrel : RelativeUnitIndexReciprocity B FK) :
    AnchoredTameInertiaRelativeUnramifiedDataAt P K FK tame := by
  intro D _ _ _ _ V _ _ c rho hfac _hram
  let F₀ := anchoredTameInertiaField (GalKsub K) rho (c (tqTau P.qK))
  let hKF₀ := baseField_le_anchoredTameInertiaField K rho (c (tqTau P.qK))
  let E := IntermediateField.extendScalars hKF₀
  letI : FiniteDimensional ℚ_[2] F₀ :=
    anchoredTameInertiaField_finiteDimensional (GalKsub K)
      (isOpen_fixingSubgroup K) rho (c (tqTau P.qK))
  letI hEfinQ2 : FiniteDimensional ℚ_[2] E := by
    let e : ↥F₀ ≃ₗ[ℚ_[2]] ↥E :=
      { toFun := fun x => ⟨x.1, x.2⟩
        invFun := fun x => ⟨x.1, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact Module.Finite.equiv e
  letI : FiniteDimensional (↥K) E := Module.Finite.right ℚ_[2] (↥K) E
  letI : IsGalois (↥K) E :=
    anchoredTameInertiaField_relative_isGalois P tame c rho hfac
  let F₀F : DyadicUnitFiltration F₀ := dyadicUnitFiltration F₀
  refine ⟨F₀F, relE_eq_one_of_relativeUnitIndexReciprocity
    B FK Hrel F₀ hKF₀
      (anchoredTameInertiaField_relative_commutative P tame c rho hfac) F₀F ?_⟩
  intro u g hgu
  apply anchoredTameInertia_preimage_le_relativeRestrictHom_ker P c rho
  change rho g ∈ Subgroup.zpowers (c (tqTau P.qK))
  rw [hfac]
  apply inertiaPartQ_le_comap_zpowers_tqTau P.qK c
  apply Hunit u.1 g
  · exact (mem_normUnits K u.1).mp u.2
  · exact hgu

/-- The uniform odd-degree endpoint with the anchored residue replaced by the conventional
relative unit-index theorem over all finite abelian layers of `K`. -/
theorem LSquare.gammaR_lSq_equiv_galK_oddDegree_of_baseAndRelativeUnitIndex
    (B : MarkedRecip R K) (FK : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FK)
    (D : FiniteDyadicParameters K FK) {h : ℕ}
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] [CompactSpace AbsGalQ2]
    [TotallyDisconnectedSpace AbsGalQ2]
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (Hbase : AbsoluteResidueBaseReciprocityLaw R)
    (Htame : AbstractTameLocalReciprocityLaw T)
    (Hrel : RelativeUnitIndexReciprocity B FK) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FK) : Type) (GalK K)) := by
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  have Hunit : TameUnitInertiaRefinement B FK T :=
    (abstractTameLocalReciprocityLaw_iff_rows T |>.mp Htame).1
  have HunitAt : TameUnitInertiaRefinementAt D.params K B
      (tameAtParams D.params D.qK_eq_qOf T.tameFK) :=
    tameUnitInertiaRefinementAt_tameAtParams_of_oriented
      K B FK T D.params D.qK_eq_qOf Hunit
  have Hunram : AnchoredTameInertiaRelativeUnramifiedDataAt
      D.params K FK (tameAtParams D.params D.qK_eq_qOf T.tameFK) :=
    anchoredTameInertiaRelativeUnramifiedDataAt_of_relativeUnitIndexReciprocity
      D.params B FK (tameAtParams D.params D.qK_eq_qOf T.tameFK) HunitAt Hrel
  have hNorm : AnchoredInvolutionEqualNormValueGroupsAt D.params (GalKsub K)
      (tameAtParams D.params D.qK_eq_qOf T.tameFK) :=
    anchoredInvolutionEqualNormValueGroupsAt_of_prescribedTameUnramified
      D.params K FK (tameAtParams D.params D.qK_eq_qOf T.tameFK)
        (tameAtParams_surjective_for_spectralReciprocity D.params D.qK_eq_qOf
          T.tameFK T.tameFK_surjective) hodd Hunram
  exact LSquare.gammaR_lSq_equiv_galK_oddDegree_of_baseReciprocity
    B FK T D hdeg Hbase Htame hNorm

#print axioms relativeRestrictHom
#print axioms relativeReciprocityUnitImage
#print axioms RelativeUnitIndexReciprocity
#print axioms relE_eq_one_of_relativeUnitIndexReciprocity
#print axioms commutator_le_anchoredTameInertia_preimage
#print axioms anchoredTameInertia_preimage_normal
#print axioms anchoredTameInertiaField_relative_isGalois
#print axioms relativeRestrictHom_surjective
#print axioms anchoredTameInertia_preimage_le_relativeRestrictHom_ker
#print axioms anchoredTameInertiaField_relative_commutative
#print axioms
  anchoredTameInertiaRelativeUnramifiedDataAt_of_relativeUnitIndexReciprocity
#print axioms LSquare.gammaR_lSq_equiv_galK_oddDegree_of_baseAndRelativeUnitIndex

end
end GQ2.Dyadic

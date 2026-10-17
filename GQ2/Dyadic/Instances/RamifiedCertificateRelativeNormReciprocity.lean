/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateRelativeUnitIndex

/-!
# Relative finite-abelian norm reciprocity

This module proves the relative analogue of `UnitNormIndex.card_unitImage_eq_e` for every finite
dyadic tower `L/K`.  The analytic argument is uniform: the spectral norm gives

`e(L/K) * v_K(N pi_L) = [L:K]`,

the relative norm subgroup has exactly the multiples of `v_K(N pi_L)` as its valuation image,
and the usual uniformizer/unit decomposition counts the Artin image of the spectral units.

`RelativeFiniteAbelianNormReciprocity` packages the conventional finite-layer local-CFT theorem:
the relative Artin map is surjective, its kernel is the norm subgroup, and it agrees with the
restriction of lifts of `MarkedRecip.recip`.  The final theorem derives
`RelativeUnitIndexReciprocity`, which is the exact arithmetic premise consumed by the uniform
odd-degree endpoint.  No presentation family, nilpotency class, or handle count occurs here.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open IntermediateField
open scoped Classical

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]

omit [FiniteDimensional ℚ_[2] K] in
theorem relative_norm_val
    (E : IntermediateField (↥K) ℚ̄₂) [FiniteDimensional (↥K) E] (x : E) :
    ‖((Algebra.norm (↥K) x : ↥K) : ℚ̄₂)‖ =
      ‖(x : ℚ̄₂)‖ ^ Module.finrank (↥K) E := by
  classical
  have hconj : ∀ σ : E →ₐ[↥K] ℚ̄₂, ‖σ x‖ = ‖(x : ℚ̄₂)‖ := by
    intro σ
    let g : ℚ̄₂ ≃ₐ[↥K] ℚ̄₂ :=
      AlgEquiv.ofBijective (σ.liftNormal ℚ̄₂)
        (AlgHom.normal_bijective (↥K) ℚ̄₂ ℚ̄₂ _)
    let gQ : ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂ := g.restrictScalars ℚ_[2]
    have hcomm : g (algebraMap E ℚ̄₂ x) = σ x := by
      simpa [g] using σ.liftNormal_commutes ℚ̄₂ x
    rw [← hcomm]
    exact norm_galois gQ (algebraMap E ℚ̄₂ x)
  have hprod : algebraMap (↥K) ℚ̄₂ (Algebra.norm (↥K) x) =
      ∏ σ : E →ₐ[↥K] ℚ̄₂, σ x :=
    Algebra.norm_eq_prod_embeddings (↥K) ℚ̄₂ x
  change ‖algebraMap (↥K) ℚ̄₂ (Algebra.norm (↥K) x)‖ = _
  rw [hprod, norm_prod]
  calc
    ∏ σ : E →ₐ[↥K] ℚ̄₂, ‖σ x‖ =
        ∏ _σ : E →ₐ[↥K] ℚ̄₂, ‖(x : ℚ̄₂)‖ :=
      Finset.prod_congr rfl (fun σ _ ↦ hconj σ)
    _ = ‖(x : ℚ̄₂)‖ ^ Module.finrank (↥K) E := by
      rw [Finset.prod_const, Finset.card_univ, AlgHom.card]

noncomputable def relativePiUnit
    (L : IntermediateField ℚ_[2] ℚ̄₂) (hKL : K ≤ L)
    (FL : DyadicUnitFiltration L) :
    (IntermediateField.extendScalars hKL)ˣ :=
  Units.mk0 ⟨FL.π, FL.hπ_mem⟩ fun h =>
    FL.hπ_ne (by simpa using congrArg Subtype.val h)

noncomputable def relativeNormValPi
    (FK : DyadicUnitFiltration K)
    (L : IntermediateField ℚ_[2] ℚ̄₂) (hKL : K ≤ L)
    [FiniteDimensional (↥K) (IntermediateField.extendScalars hKL)]
    (FL : DyadicUnitFiltration L) : ℤ :=
  dyadicValuation FK
    (Units.map (Algebra.norm (↥K) (S := IntermediateField.extendScalars hKL))
      (relativePiUnit L hKL FL))

omit [FiniteDimensional ℚ_[2] K] in
theorem relE_mul_relativeNormValPi
    (FK : DyadicUnitFiltration K)
    (L : IntermediateField ℚ_[2] ℚ̄₂) (hKL : K ≤ L)
    [FiniteDimensional (↥K) (IntermediateField.extendScalars hKL)]
    (FL : DyadicUnitFiltration L) :
    GaloisCosetNorm.relE FK FL hKL * relativeNormValPi FK L hKL FL =
      (Module.finrank (↥K) (IntermediateField.extendScalars hKL) : ℤ) := by
  let E := IntermediateField.extendScalars hKL
  let πE : Eˣ := relativePiUnit L hKL FL
  let Nπ : (↥K)ˣ := Units.map (Algebra.norm (↥K) (S := E)) πE
  have hN : ‖(((Nπ : (↥K)ˣ) : ↥K) : ℚ̄₂)‖ =
      ‖FL.π‖ ^ Module.finrank (↥K) E := by
    simpa [Nπ, πE, relativePiUnit] using relative_norm_val E (πE : E)
  have hleft : ‖(((Nπ : (↥K)ˣ) : ↥K) : ℚ̄₂)‖ =
      ‖FL.π‖ ^
        (GaloisCosetNorm.relE FK FL hKL * relativeNormValPi FK L hKL FL) := by
    rw [norm_eq_zpow_dyadicValuation FK Nπ]
    change ‖FK.π‖ ^ relativeNormValPi FK L hKL FL = _
    rw [GaloisCosetNorm.relE_spec FK FL hKL, ← zpow_mul]
  apply zpow_right_injective₀ (norm_pos_iff.mpr FL.hπ_ne) (ne_of_lt FL.hπ_lt)
  change ‖FL.π‖ ^
      (GaloisCosetNorm.relE FK FL hKL * relativeNormValPi FK L hKL FL) =
    ‖FL.π‖ ^ (Module.finrank (↥K) E : ℤ)
  rw [← hleft, hN, zpow_natCast]

omit [FiniteDimensional ℚ_[2] K] in
theorem relE_mul_val_relativeNorm
    (FK : DyadicUnitFiltration K)
    (L : IntermediateField ℚ_[2] ℚ̄₂) (hKL : K ≤ L)
    [FiniteDimensional (↥K) (IntermediateField.extendScalars hKL)]
    (FL : DyadicUnitFiltration L)
    (y : (IntermediateField.extendScalars hKL)ˣ) :
    GaloisCosetNorm.relE FK FL hKL *
        dyadicValuation FK
          (Units.map (Algebra.norm (↥K)
            (S := IntermediateField.extendScalars hKL)) y) =
      (Module.finrank (↥K) (IntermediateField.extendScalars hKL) : ℤ) *
        dyadicValuation FL
          (Units.mk0 ⟨(y : IntermediateField.extendScalars hKL), y.1.2⟩
            (by exact y.ne_zero) : (↥L)ˣ) := by
  let E := IntermediateField.extendScalars hKL
  let yL : (↥L)ˣ := Units.mk0 ⟨(y : E), y.1.2⟩ (by exact y.ne_zero)
  let Ny : (↥K)ˣ := Units.map (Algebra.norm (↥K) (S := E)) y
  have hN : ‖(((Ny : (↥K)ˣ) : ↥K) : ℚ̄₂)‖ =
      ‖((yL : ↥L) : ℚ̄₂)‖ ^ Module.finrank (↥K) E := by
    exact relative_norm_val E (y : E)
  have hright : ‖(((Ny : (↥K)ˣ) : ↥K) : ℚ̄₂)‖ =
      ‖FL.π‖ ^
        ((Module.finrank (↥K) E : ℤ) * dyadicValuation FL yL) := by
    rw [hN, norm_eq_zpow_dyadicValuation FL yL,
      ← zpow_natCast (‖FL.π‖ ^ dyadicValuation FL yL), ← zpow_mul]
    congr 1
    ring
  have hleft : ‖(((Ny : (↥K)ˣ) : ↥K) : ℚ̄₂)‖ =
      ‖FL.π‖ ^
        (GaloisCosetNorm.relE FK FL hKL * dyadicValuation FK Ny) := by
    rw [norm_eq_zpow_dyadicValuation FK Ny,
      GaloisCosetNorm.relE_spec FK FL hKL, ← zpow_mul]
  apply zpow_right_injective₀ (norm_pos_iff.mpr FL.hπ_ne) (ne_of_lt FL.hπ_lt)
  change ‖FL.π‖ ^
      (GaloisCosetNorm.relE FK FL hKL * dyadicValuation FK Ny) =
    ‖FL.π‖ ^
      ((Module.finrank (↥K) E : ℤ) * dyadicValuation FL yL)
  rw [← hleft, hright]

omit [FiniteDimensional ℚ_[2] K] in
theorem relativeNormValPi_pos
    (FK : DyadicUnitFiltration K)
    (L : IntermediateField ℚ_[2] ℚ̄₂) (hKL : K ≤ L)
    [FiniteDimensional (↥K) (IntermediateField.extendScalars hKL)]
    (FL : DyadicUnitFiltration L) :
    1 ≤ relativeNormValPi FK L hKL FL := by
  have hmul := relE_mul_relativeNormValPi FK L hKL FL
  have he := GaloisCosetNorm.relE_pos FK FL hKL
  have hn : 0 < (Module.finrank (↥K)
      (IntermediateField.extendScalars hKL) : ℤ) := by
    exact_mod_cast Module.finrank_pos
  nlinarith

omit [FiniteDimensional ℚ_[2] K] in
theorem dyadicValuation_zpow_relative (FK : DyadicUnitFiltration K)
    (x : (↥K)ˣ) (m : ℤ) :
    dyadicValuation FK (x ^ m) = m * dyadicValuation FK x := by
  have h := map_zpow (dyadicValuationHom FK) x m
  exact congrArg Multiplicative.toAdd h

omit [FiniteDimensional ℚ_[2] K] in
theorem dyadicValuation_inv_relative (FK : DyadicUnitFiltration K)
    (x : (↥K)ˣ) :
    dyadicValuation FK x⁻¹ = -dyadicValuation FK x := by
  simpa using dyadicValuation_zpow_relative FK x (-1)

omit [FiniteDimensional ℚ_[2] K] in
theorem dyadicValuation_eq_zero_iff_mem_normUnits
    (FK : DyadicUnitFiltration K) (x : (↥K)ˣ) :
    dyadicValuation FK x = 0 ↔ x ∈ normUnits K := by
  constructor
  · intro hx
    rw [mem_normUnits]
    rw [norm_eq_zpow_dyadicValuation FK x, hx, zpow_zero]
  · intro hx
    apply dyadicValuation_eq_of_norm_eq_zpow FK x 0
    rw [zpow_zero]
    exact (mem_normUnits K x).mp hx

omit [FiniteDimensional ℚ_[2] K] in
theorem relativeNormValPi_dvd_dyadicValuation_of_mem
    (FK : DyadicUnitFiltration K)
    (L : IntermediateField ℚ_[2] ℚ̄₂) (hKL : K ≤ L)
    [FiniteDimensional (↥K) (IntermediateField.extendScalars hKL)]
    (FL : DyadicUnitFiltration L) {x : (↥K)ˣ}
    (hx : x ∈ relativeNormSubgroup K (IntermediateField.extendScalars hKL)) :
    relativeNormValPi FK L hKL FL ∣ dyadicValuation FK x := by
  obtain ⟨y, rfl⟩ := hx
  let E := IntermediateField.extendScalars hKL
  let yL : (↥L)ˣ := Units.mk0 ⟨(y : E), y.1.2⟩ (by exact y.ne_zero)
  refine ⟨dyadicValuation FL yL, ?_⟩
  have hval : GaloisCosetNorm.relE FK FL hKL *
        dyadicValuation FK
          (Units.map (Algebra.norm (↥K) (S := E)) y) =
      (Module.finrank (↥K) E : ℤ) * dyadicValuation FL yL := by
    simpa [E, yL] using relE_mul_val_relativeNorm FK L hKL FL y
  have hpi := relE_mul_relativeNormValPi FK L hKL FL
  have he : GaloisCosetNorm.relE FK FL hKL ≠ 0 := by
    exact ne_of_gt (GaloisCosetNorm.relE_pos FK FL hKL)
  apply mul_left_cancel₀ he
  calc
    GaloisCosetNorm.relE FK FL hKL *
        dyadicValuation FK
          (Units.map (Algebra.norm (↥K) (S := E)) y) =
        (Module.finrank (↥K) E : ℤ) * dyadicValuation FL yL := hval
    _ = (GaloisCosetNorm.relE FK FL hKL *
          relativeNormValPi FK L hKL FL) * dyadicValuation FL yL := by rw [hpi]
    _ = GaloisCosetNorm.relE FK FL hKL *
          (relativeNormValPi FK L hKL FL * dyadicValuation FL yL) := by ring

omit [FiniteDimensional ℚ_[2] K] in
theorem exists_mem_relativeNormSubgroup_dyadicValuation_eq
    (FK : DyadicUnitFiltration K)
    (L : IntermediateField ℚ_[2] ℚ̄₂) (hKL : K ≤ L)
    [FiniteDimensional (↥K) (IntermediateField.extendScalars hKL)]
    (FL : DyadicUnitFiltration L) (m : ℤ) :
    ∃ w ∈ relativeNormSubgroup K (IntermediateField.extendScalars hKL),
      dyadicValuation FK w = relativeNormValPi FK L hKL FL * m := by
  let E := IntermediateField.extendScalars hKL
  let πE : Eˣ := relativePiUnit L hKL FL
  let Nπ : (↥K)ˣ := Units.map (Algebra.norm (↥K) (S := E)) πE
  refine ⟨Units.map (Algebra.norm (↥K) (S := E)) (πE ^ m), ⟨πE ^ m, rfl⟩, ?_⟩
  rw [map_zpow, dyadicValuation_zpow_relative]
  change m * relativeNormValPi FK L hKL FL = _
  ring

/-- A conventional finite abelian local-reciprocity theorem for one relative layer. -/
structure RelativeFiniteAbelianNormLayer
    (B : MarkedRecip R K)
    (L : IntermediateField ℚ_[2] ℚ̄₂) (hKL : K ≤ L)
    [FiniteDimensional (↥K) (IntermediateField.extendScalars hKL)]
    [IsGalois (↥K) (IntermediateField.extendScalars hKL)] where
  artin : (↥K)ˣ →*
    ((IntermediateField.extendScalars hKL) ≃ₐ[↥K]
      (IntermediateField.extendScalars hKL))
  surjective : Function.Surjective artin
  ker_eq : artin.ker = relativeNormSubgroup K (IntermediateField.extendScalars hKL)
  lift_compat : ∀ (x : (↥K)ˣ) (g : GalK K),
    toAbK K g = B.recip x → relativeRestrictHom L hKL g = artin x

/-- Full relative finite-abelian norm reciprocity over every embedded layer. -/
def RelativeFiniteAbelianNormReciprocity (B : MarkedRecip R K) : Prop :=
  ∀ (L : IntermediateField ℚ_[2] ℚ̄₂) (hKL : K ≤ L)
    [FiniteDimensional ℚ_[2] L]
    [FiniteDimensional (↥K) (IntermediateField.extendScalars hKL)]
    [IsGalois (↥K) (IntermediateField.extendScalars hKL)]
    (_hab : ∀ σ τ : ((IntermediateField.extendScalars hKL) ≃ₐ[↥K]
      (IntermediateField.extendScalars hKL)), σ * τ = τ * σ),
      Nonempty (RelativeFiniteAbelianNormLayer B L hKL)

theorem card_artin_normUnits_eq_relE
    (B : MarkedRecip R K)
    (FK : DyadicUnitFiltration K)
    (L : IntermediateField ℚ_[2] ℚ̄₂) (hKL : K ≤ L)
    [FiniteDimensional ℚ_[2] L]
    [FiniteDimensional (↥K) (IntermediateField.extendScalars hKL)]
    [IsGalois (↥K) (IntermediateField.extendScalars hKL)]
    (hab : ∀ σ τ : ((IntermediateField.extendScalars hKL) ≃ₐ[↥K]
      (IntermediateField.extendScalars hKL)), σ * τ = τ * σ)
    (FL : DyadicUnitFiltration L)
    (D : RelativeFiniteAbelianNormLayer B L hKL) :
    Nat.card ↥((D.artin.comp (normUnits K).subtype).range) =
      (GaloisCosetNorm.relE FK FL hKL).toNat := by
  let E := IntermediateField.extendScalars hKL
  let φ := D.artin
  let Gu : Subgroup (E ≃ₐ[↥K] E) := (φ.comp (normUnits K).subtype).range
  haveI hGuN : Gu.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rwa [hab g n, mul_inv_cancel_right]
  have hf0pos : 1 ≤ relativeNormValPi FK L hKL FL :=
    relativeNormValPi_pos FK L hKL FL
  have hcast : ((relativeNormValPi FK L hKL FL).toNat : ℤ) =
      relativeNormValPi FK L hKL FL := Int.toNat_of_nonneg (by omega)
  set q : (E ≃ₐ[↥K] E) ⧸ Gu :=
    QuotientGroup.mk (φ (uniformizerK K FK)) with hqdef
  have hUdie : ∀ u : ↥(normUnits K),
      (QuotientGroup.mk (φ u.1) : (E ≃ₐ[↥K] E) ⧸ Gu) = 1 :=
    fun u => (QuotientGroup.eq_one_iff _).mpr ⟨u, rfl⟩
  have hgen : ∀ z : (E ≃ₐ[↥K] E) ⧸ Gu, z ∈ Subgroup.zpowers q := by
    intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨x, rfl⟩ := D.surjective g
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨dyadicValuation FK x, ?_⟩
    rw [hqdef, ← QuotientGroup.mk_zpow, ← map_zpow]
    conv_rhs => rw [← normalizedUnit_mul_uniformizer FK x]
    rw [map_mul, QuotientGroup.mk_mul, hUdie, one_mul]
  have hpow : ∀ k : ℤ, q ^ k = 1 ↔ relativeNormValPi FK L hKL FL ∣ k := by
    intro k
    rw [hqdef, ← QuotientGroup.mk_zpow, ← map_zpow, QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨u, hu⟩
      rw [MonoidHom.comp_apply] at hu
      have hN : uniformizerK K FK ^ k * (u.1)⁻¹ ∈
          relativeNormSubgroup K E := by
        rw [← D.ker_eq, MonoidHom.mem_ker]
        change φ (uniformizerK K FK ^ k * (u.1)⁻¹) = 1
        change φ u.1 = φ (uniformizerK K FK ^ k) at hu
        rw [map_mul, map_inv, ← hu, mul_inv_cancel]
      have hdvd := relativeNormValPi_dvd_dyadicValuation_of_mem FK L hKL FL hN
      rwa [dyadicValuation_mul, dyadicValuation_zpow_relative,
        dyadicValuation_uniformizerK, mul_one, dyadicValuation_inv_relative,
        (dyadicValuation_eq_zero_iff_mem_normUnits FK u.1).2 u.2, neg_zero,
        add_zero] at hdvd
    · rintro ⟨m, rfl⟩
      obtain ⟨w, hwN, hwv⟩ :=
        exists_mem_relativeNormSubgroup_dyadicValuation_eq FK L hKL FL m
      have hv0 : dyadicValuation FK
          (uniformizerK K FK ^ (relativeNormValPi FK L hKL FL * m) * w⁻¹) = 0 := by
        rw [dyadicValuation_mul, dyadicValuation_zpow_relative,
          dyadicValuation_uniformizerK, mul_one, dyadicValuation_inv_relative, hwv]
        ring
      let u : ↥(normUnits K) :=
        ⟨uniformizerK K FK ^ (relativeNormValPi FK L hKL FL * m) * w⁻¹,
          (dyadicValuation_eq_zero_iff_mem_normUnits FK _).1 hv0⟩
      have hw1 : φ w = 1 := by
        rw [← MonoidHom.mem_ker, D.ker_eq]
        exact hwN
      refine ⟨u, ?_⟩
      rw [MonoidHom.comp_apply]
      change φ (uniformizerK K FK ^
        (relativeNormValPi FK L hKL FL * m) * w⁻¹) = _
      rw [map_mul, map_inv, hw1, inv_one, mul_one]
  have horder : orderOf q = (relativeNormValPi FK L hKL FL).toNat := by
    have h1 : orderOf q ∣ (relativeNormValPi FK L hKL FL).toNat :=
      orderOf_dvd_of_pow_eq_one (by
        have h := (hpow (relativeNormValPi FK L hKL FL)).mpr dvd_rfl
        rwa [← hcast, zpow_natCast] at h)
    have h2 : (relativeNormValPi FK L hKL FL).toNat ∣ orderOf q := by
      have hq1 : q ^ ((orderOf q : ℕ) : ℤ) = 1 := by
        rw [zpow_natCast, pow_orderOf_eq_one]
      have h := (hpow ((orderOf q : ℕ) : ℤ)).mp hq1
      rwa [← hcast, Int.natCast_dvd_natCast] at h
    exact Nat.dvd_antisymm h1 h2
  have hcardQ : Nat.card ((E ≃ₐ[↥K] E) ⧸ Gu) =
      (relativeNormValPi FK L hKL FL).toNat := by
    have htop : Subgroup.zpowers q = ⊤ := (Subgroup.eq_top_iff' _).mpr hgen
    rw [← horder, ← Nat.card_zpowers, htop, Subgroup.card_top]
  have hcards := Subgroup.card_mul_index Gu
  rw [Subgroup.index_eq_card, hcardQ] at hcards
  have hcardG : Nat.card (E ≃ₐ[↥K] E) = Module.finrank (↥K) E :=
    IsGalois.card_aut_eq_finrank (↥K) E
  rw [hcardG] at hcards
  have hef : (GaloisCosetNorm.relE FK FL hKL).toNat *
      (relativeNormValPi FK L hKL FL).toNat = Module.finrank (↥K) E := by
    have h := relE_mul_relativeNormValPi FK L hKL FL
    have hecast : ((GaloisCosetNorm.relE FK FL hKL).toNat : ℤ) =
        GaloisCosetNorm.relE FK FL hKL := Int.toNat_of_nonneg
          (by have := GaloisCosetNorm.relE_pos FK FL hKL; omega)
    rw [← hecast, ← hcast] at h
    exact_mod_cast h
  have hfin : Nat.card Gu * (relativeNormValPi FK L hKL FL).toNat =
      (GaloisCosetNorm.relE FK FL hKL).toNat *
        (relativeNormValPi FK L hKL FL).toNat := by
    rw [hcards, hef]
  exact Nat.eq_of_mul_eq_mul_right (by omega) hfin

theorem relativeReciprocityUnitImage_eq_artin_normUnits
    (B : MarkedRecip R K)
    (L : IntermediateField ℚ_[2] ℚ̄₂) (hKL : K ≤ L)
    [FiniteDimensional (↥K) (IntermediateField.extendScalars hKL)]
    [IsGalois (↥K) (IntermediateField.extendScalars hKL)]
    (D : RelativeFiniteAbelianNormLayer B L hKL) :
    relativeReciprocityUnitImage B L hKL =
      (D.artin.comp (normUnits K).subtype).range := by
  ext σ
  constructor
  · rintro ⟨u, g, hgu, rfl⟩
    refine ⟨u, ?_⟩
    exact (D.lift_compat u.1 g hgu).symm
  · rintro ⟨u, rfl⟩
    obtain ⟨g, hg⟩ := surjective_toAbK K (B.recip u.1)
    refine ⟨u, g, hg, ?_⟩
    exact D.lift_compat u.1 g hg

/-- Full finite-abelian norm reciprocity implies the relative unit-index theorem. -/
theorem relativeUnitIndexReciprocity_of_relativeFiniteAbelianNormReciprocity
    (B : MarkedRecip R K) (FK : DyadicUnitFiltration K)
    (H : RelativeFiniteAbelianNormReciprocity B) :
    RelativeUnitIndexReciprocity B FK := by
  intro L hKL _ _ _ hab FL
  obtain ⟨D⟩ := H L hKL hab
  rw [relativeReciprocityUnitImage_eq_artin_normUnits B L hKL D]
  exact card_artin_normUnits_eq_relE B FK L hKL hab FL D

/-- The uniform odd-degree endpoint from the conventional full relative norm-reciprocity
theorem.  All valuation and unit-index arithmetic is discharged in this module. -/
theorem LSquare.gammaR_lSq_equiv_galK_oddDegree_of_baseAndRelativeNormReciprocity
    (B : MarkedRecip R K) (FK : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FK)
    (D : FiniteDyadicParameters K FK) {h : ℕ}
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] [CompactSpace AbsGalQ2]
    [TotallyDisconnectedSpace AbsGalQ2]
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (Hbase : AbsoluteResidueBaseReciprocityLaw R)
    (Htame : AbstractTameLocalReciprocityLaw T)
    (Hnorm : RelativeFiniteAbelianNormReciprocity B) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FK) : Type) (GalK K)) :=
  LSquare.gammaR_lSq_equiv_galK_oddDegree_of_baseAndRelativeUnitIndex
    B FK T D hdeg Hbase Htame
      (relativeUnitIndexReciprocity_of_relativeFiniteAbelianNormReciprocity B FK Hnorm)

#print axioms relativeReciprocityUnitImage_eq_artin_normUnits
#print axioms relativeUnitIndexReciprocity_of_relativeFiniteAbelianNormReciprocity
#print axioms
  LSquare.gammaR_lSq_equiv_galK_oddDegree_of_baseAndRelativeNormReciprocity

#print axioms card_artin_normUnits_eq_relE

#print axioms relativeNormValPi_dvd_dyadicValuation_of_mem
#print axioms exists_mem_relativeNormSubgroup_dyadicValuation_eq

#print axioms relE_mul_val_relativeNorm
#print axioms relativeNormValPi_pos

#print axioms relE_mul_relativeNormValPi

#print axioms relative_norm_val

end

end GQ2.Dyadic

/-
T2 recon (dyadic Tau Ceti discharge), lane `bridge`: the norm ↔ valuation bridge on a finite
`↥K ⊆ ℚ̄₂` (A1-K), the topology comparison, and the residue-degree bridge (recon question Q3).
Scratch prototype, not library code.
-/
module

public import GQ2.TauCeti.GaloisDict
public import TauCeti.NumberTheory.LocalField.NormalizedValuation
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import GQ2.UnitFiltrationCounts

@[expose] public section

noncomputable section

namespace GQ2.TauCetiBridge

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

open ValuativeRel

/-! ### The generic bridge: one line from Tau Ceti's uniqueness of the extended valuation -/

/-- Any valuative relation on an algebraic extension `M/F` of a local field that extends `F`'s is
the relation of any valuation `w` of `M` restricting to `F`'s valuation class. -/
theorem vle_iff_of_isEquiv {F M : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field M] [Algebra F M] [Algebra.IsAlgebraic F M]
    [ValuativeRel M] [ValuativeExtension F M] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {w : Valuation M Γ} (hw : (w.comap (algebraMap F M)).IsEquiv (valuation F)) (x y : M) :
    x ≤ᵥ y ↔ w x ≤ w y :=
  (TauCeti.vle_iff_algebraicExtensionNormedField_norm_le F x y).trans
    (TauCeti.algebraicExtensionNormedField_norm_le_norm_iff hw x y)

/-! ### At a finite `↥K ⊆ ℚ̄₂` over `ℚ₂` -/

section K

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]

/-- gq2's spectral norm of `ℚ̄₂`, restricted to `↥K`, as an `ℝ≥0`-valued valuation. -/
def normValuation : Valuation K NNReal :=
  (NormedField.valuation : Valuation ℚ̄₂ NNReal).comap (K.val : K →+* ℚ̄₂)

@[simp] theorem normValuation_apply (x : K) : normValuation K x = ‖(x : ℚ̄₂)‖₊ := rfl

/-- On `ℚ₂ ⊆ ↥K` the restricted norm is the `2`-adic norm, which orders `ℚ₂` like Tau Ceti's
valuation (`Padic.normalizedAbsoluteValue_eq_nnnorm`). -/
theorem isEquiv_normValuation :
    ((normValuation K).comap (algebraMap ℚ_[2] K)).IsEquiv (valuation ℚ_[2]) := by
  intro a b
  simp only [Valuation.comap_apply, normValuation_apply]
  rw [← TauCeti.normalizedAbsoluteValue_le_normalizedAbsoluteValue_iff, ← NNRat.cast_le (K := NNReal),
    Padic.normalizedAbsoluteValue_eq_nnnorm, Padic.normalizedAbsoluteValue_eq_nnnorm]
  change ‖algebraMap ℚ_[2] ℚ̄₂ a‖₊ ≤ ‖algebraMap ℚ_[2] ℚ̄₂ b‖₊ ↔ _
  rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm,
    norm_algebraMap' (𝕜' := ℚ̄₂), norm_algebraMap' (𝕜' := ℚ̄₂), ← NNReal.coe_le_coe, coe_nnnorm,
    coe_nnnorm]

/-- **The norm ↔ valuation bridge (A1-K).** Tau Ceti's valuative relation on `↥K` (A1's
`valuativeRel K`) compares gq2's spectral norms. -/
theorem vle_iff_norm_le (x y : K) :
    letI := valuativeRel K
    x ≤ᵥ y ↔ ‖(x : ℚ̄₂)‖ ≤ ‖(y : ℚ̄₂)‖ := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  haveI := valuativeExtension K
  rw [vle_iff_of_isEquiv (isEquiv_normValuation K) x y, normValuation_apply, normValuation_apply,
    ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]

theorem valuation_le_iff_norm_le (x y : K) :
    letI := valuativeRel K
    valuation K x ≤ valuation K y ↔ ‖(x : ℚ̄₂)‖ ≤ ‖(y : ℚ̄₂)‖ := by
  letI := valuativeRel K
  exact (Valuation.Compatible.vle_iff_le (v := valuation K) x y).symm.trans (vle_iff_norm_le K x y)

theorem valuation_eq_iff_norm_eq (x y : K) :
    letI := valuativeRel K
    valuation K x = valuation K y ↔ ‖(x : ℚ̄₂)‖ = ‖(y : ℚ̄₂)‖ := by
  letI := valuativeRel K
  rw [le_antisymm_iff, le_antisymm_iff, valuation_le_iff_norm_le, valuation_le_iff_norm_le]

/-- **Units (B5-K `nu_ur_recip_unit`, B10-K `nuT_recip_unit`).** -/
theorem normalizedValuation_eq_one_of_norm_eq_one (u : Kˣ) (hu : ‖((u : K) : ℚ̄₂)‖ = 1) :
    letI := valuativeRel K
    letI := localTopology K
    haveI := isNonarchimedeanLocalField K
    TauCeti.normalizedValuation K u = 1 := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  rw [TauCeti.normalizedValuation_eq_one_iff, ← map_one (valuation K), valuation_eq_iff_norm_eq]
  simpa using hu

/-- **Uniformizers (B5-K `nu_ur_recip_uniformizer`, B10-K `nuT_recip_uniformizer`).** gq2's
spectral uniformizer spec ("maximal norm `< 1`") gives normalized valuation `1`. -/
theorem normalizedValuation_eq_ofAdd_one_of_norm (π : Kˣ) (hπ : ‖((π : K) : ℚ̄₂)‖ < 1)
    (hmax : ∀ z : K, z ≠ 0 → ‖(z : ℚ̄₂)‖ < 1 → ‖(z : ℚ̄₂)‖ ≤ ‖((π : K) : ℚ̄₂)‖) :
    letI := valuativeRel K
    letI := localTopology K
    haveI := isNonarchimedeanLocalField K
    TauCeti.normalizedValuation K π = Multiplicative.ofAdd 1 := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  obtain ⟨ϖ, hϖ⟩ := TauCeti.normalizedValuation_surjective (K := K) (Multiplicative.ofAdd 1)
  -- `π` is not a unit: `v(π) ≥ 1`
  have h1 : 1 ≤ (TauCeti.normalizedValuation K π).toAdd := by
    have hle : (0 : ℤ) ≤ (TauCeti.normalizedValuation K π).toAdd := by
      rw [show (0 : ℤ) = (TauCeti.normalizedValuation K 1).toAdd by simp,
        TauCeti.toAdd_normalizedValuation_le_iff_valuation_le, Units.val_one,
        valuation_le_iff_norm_le]
      simpa using hπ.le
    have hne : (TauCeti.normalizedValuation K π).toAdd ≠ 0 := by
      intro h0
      have : TauCeti.normalizedValuation K π = 1 := toAdd_eq_zero.mp h0
      rw [TauCeti.normalizedValuation_eq_one_iff, ← map_one (valuation K),
        valuation_eq_iff_norm_eq] at this
      simp at this
      exact absurd this hπ.ne
    omega
  -- `ϖ` has norm `< 1`, so `‖ϖ‖ ≤ ‖π‖`, so `v(π) ≤ v(ϖ) = 1`
  have hϖlt : ‖((ϖ : K) : ℚ̄₂)‖ < 1 := by
    have h := (TauCeti.toAdd_normalizedValuation_le_iff_valuation_le (K := K) 1 ϖ).1
      (by rw [hϖ]; simp)
    rw [Units.val_one, valuation_le_iff_norm_le] at h
    rcases h.lt_or_eq with h | h
    · simpa using h
    · exfalso
      have : TauCeti.normalizedValuation K ϖ = 1 := by
        rw [TauCeti.normalizedValuation_eq_one_iff, ← map_one (valuation K),
          valuation_eq_iff_norm_eq]
        simpa using h
      rw [hϖ] at this
      exact absurd (congrArg Multiplicative.toAdd this) (by simp)
  have h2 : (TauCeti.normalizedValuation K π).toAdd ≤ 1 := by
    have := hmax ϖ ϖ.ne_zero hϖlt
    rw [← valuation_le_iff_norm_le, ← TauCeti.toAdd_normalizedValuation_le_iff_valuation_le,
      hϖ] at this
    simpa using this
  exact Multiplicative.toAdd.injective (by simp; omega)

/-- **`v_K(2) ≥ 1` (recon Q1):** `2` is not a unit of `↥K`. -/
theorem normalizedValuation_two_ne_one :
    letI := valuativeRel K
    letI := localTopology K
    haveI := isNonarchimedeanLocalField K
    TauCeti.normalizedValuation K (Units.mk0 (2 : K) two_ne_zero) ≠ 1 := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  rw [Ne, TauCeti.normalizedValuation_eq_one_iff, ← map_one (valuation K), valuation_eq_iff_norm_eq]
  intro h
  have h2 : ‖(2 : ℚ̄₂)‖ < 1 := by
    rw [← map_ofNat (algebraMap ℚ_[2] ℚ̄₂) 2, norm_algebraMap' (𝕜' := ℚ̄₂)]
    exact_mod_cast Padic.norm_p_lt_one (p := 2)
  simp only [Units.val_mk0, OneMemClass.coe_one, norm_one] at h
  exact absurd h (by exact_mod_cast h2.ne)


/-! ### Q3: the residue field (`Nat.card 𝓀[↥K] = 2 ^ FF.f`) -/

/-- gq2's unit ball `Osub K = {‖x‖ ≤ 1}` is Tau Ceti's `𝒪[↥K]` (same subring of `↥K`). -/
theorem osub_eq_integer :
    letI := valuativeRel K
    UnitFiltrationCounts.Osub K = (valuation K).integer := by
  letI := valuativeRel K
  ext x
  change ‖x‖ ≤ 1 ↔ valuation K x ≤ 1
  rw [← map_one (valuation K), valuation_le_iff_norm_le]
  simp only [OneMemClass.coe_one, norm_one]
  rfl

/-- The residue map `Osub K →+* 𝓀[↥K]`. -/
def osubToResidue :
    letI := valuativeRel K
    UnitFiltrationCounts.Osub K →+* IsLocalRing.ResidueField (valuation K).integer :=
  letI := valuativeRel K
  (IsLocalRing.residue _).comp (RingEquiv.subringCongr (osub_eq_integer K)).toRingHom

theorem osubToResidue_surjective :
    letI := valuativeRel K
    Function.Surjective (osubToResidue K) := by
  letI := valuativeRel K
  exact (IsLocalRing.residue_surjective).comp (RingEquiv.subringCongr (osub_eq_integer K)).surjective

theorem ker_osubToResidue :
    letI := valuativeRel K
    RingHom.ker (osubToResidue K) = UnitFiltrationCounts.maxIdeal K := by
  letI := valuativeRel K
  ext x
  rw [RingHom.mem_ker, osubToResidue, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  change valuation K (x : K) < 1 ↔ ‖(x : K)‖ < 1
  rw [← map_one (valuation K), lt_iff_lt_of_le_iff_le (valuation_le_iff_norm_le K 1 (x : K))]
  simp

/-- **Q3, the residue-degree bridge.** `#𝓀[↥K] = #(O/𝔪)` (gq2's intrinsic residue field). -/
theorem natCard_residueField_eq :
    letI := valuativeRel K
    Nat.card (IsLocalRing.ResidueField (valuation K).integer) =
      Nat.card (UnitFiltrationCounts.ResidueField K) := by
  letI := valuativeRel K
  refine Nat.card_congr ((Ideal.quotEquivOfEq (ker_osubToResidue K).symm).trans
    (RingHom.quotientKerEquivOfSurjective (osubToResidue_surjective K))).toEquiv.symm

/-- **Q3 answered:** with gq2's `card_gradeI`-based `residueField_card_eq_pow_f` (public), Tau
Ceti's residue cardinality is `qOf K FF = 2 ^ FF.f`.  No private lemma is needed. -/
theorem natCard_residueField_eq_two_pow (FF : DyadicUnitFiltration K) :
    letI := valuativeRel K
    Nat.card (IsLocalRing.ResidueField (valuation K).integer) = 2 ^ FF.f :=
  (natCard_residueField_eq K).trans (UnitFiltrationCounts.residueField_card_eq_pow_f K FF)

/-! ### The two topologies on `↥K` are equal -/

/-- The subspace (`PadicAlgCl`) topology of `↥K` is a valuative topology for Tau Ceti's
valuative relation. -/
theorem isValuativeTopology_subtype :
    @IsValuativeTopology K _ (valuativeRel K) inferInstance := by
  letI := valuativeRel K
  haveI : (NormedField.valuation (K := K)).Compatible :=
    ⟨fun x y => by
      rw [vle_iff_norm_le, NormedField.valuation_apply, NormedField.valuation_apply,
        ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
      rfl⟩
  exact IsValuativeTopology.of_mem_nhds_zero_iff_vle NormedField.valuation
    fun {s} => NormedField.toValued.is_topological_valuation s

/-- **A1-K `localTopology_eq`:** Tau Ceti's spectral-norm topology on `↥K` is the subspace
topology gq2's statements see.  (Needed for `continuous_recip` and `denseRange_recip`.) -/
theorem localTopology_eq :
    localTopology K = (inferInstance : TopologicalSpace K) := by
  have h1 := @TauCeti.finiteIntermediateField_isValuativeTopology ℚ_[2] _ _ _ _ ℚ̄₂ _ _ K _
  have h2 := isValuativeTopology_subtype K
  letI := valuativeRel K
  refine TopologicalSpace.ext_nhds fun x => Filter.ext fun s => ?_
  rw [@IsValuativeTopology.mem_nhds_iff _ _ _ (localTopology K) h1,
    @IsValuativeTopology.mem_nhds_iff _ _ _ _ h2]

end K

end GQ2.TauCetiBridge

#print axioms GQ2.TauCetiBridge.normalizedValuation_eq_ofAdd_one_of_norm
#print axioms GQ2.TauCetiBridge.normalizedValuation_two_ne_one
#print axioms GQ2.TauCetiBridge.natCard_residueField_eq_two_pow
#print axioms GQ2.TauCetiBridge.localTopology_eq

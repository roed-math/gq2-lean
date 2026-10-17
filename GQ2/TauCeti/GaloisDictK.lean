/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5.5
-/
module

public import GQ2.TauCeti.GaloisDict
public import GQ2.Dyadic.MarkedRecipBundle
public import GQ2.UnitFiltrationCounts
public import TauCeti.NumberTheory.LocalField.NormalizedValuation
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic
public import TauCeti.Topology.Algebra.Group.TopologicalAbelianization
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

@[expose] public section

/-!
# The dictionary at a finite `K/ℚ₂` (ticket A1-K)

Ticket **A1-K** of the dyadic Tau Ceti discharge campaign
(`docs/dyadic/tauceti-discharge-tickets.md`, memo `docs/dyadic/tauceti-discharge-recon.md`,
sections "A1-K: dictionary additions" and "Proposed A1-K lemma list"; prototype
`docs/dyadic/tauceti-t2-evidence/bridge/bridge.lean`).  It extends A1 (`GaloisDict.lean`) from
the Galois-group seam to the arithmetic of a finite `K : IntermediateField ℚ_[2] ℚ̄₂`, for the
two `K`-level adapters B5-K (`B5K.lean`) and B10-K (`B10K.lean`).

## The local-field package on `↥K`

Tau Ceti's local-field structure on `↥K` is A1's four named facts, used as
`letI := valuativeRel K; letI := localTopology K; haveI := isNonarchimedeanLocalField K`, plus
`haveI := valuativeExtension K` wherever an extension `ℚ₂ → ↥K` of local fields is needed (the
norm ↔ valuation bridge below, `TauCeti.FinitePadicExtension ↥K 2`, `artinMap_norm`): the first
three do **not** produce `ValuativeExtension ℚ_[2] ↥K` (memo, finding 5 and the instance table).
Nothing here is a global instance on `↥K`.

## Contents

* **The norm ↔ valuation bridge.** `vle_iff_of_isEquiv` (generic, one line from Tau Ceti's two
  uniqueness theorems for the extended valuation); at `↥K`, with `normValuationK K` gq2's spectral
  norm of `ℚ̄₂` read as a valuation, `vle_iff_norm_le`, `valuation_le_iff_norm_le` and
  `valuation_eq_iff_norm_eq`: Tau Ceti's valuation on `↥K` compares gq2's norms.  No Tau Ceti
  definition is unfolded, so the bridge survives Tau Ceti's lack of `@[expose]`.
* **Normalized valuations**: of a norm-one unit (`= 1`), of a gq2 spectral uniformizer
  (`= ofAdd 1`), and of `2` (`≠ 1`).
* **The topology comparison** `localTopology_eq`: Tau Ceti's spectral-norm topology on `↥K` is the
  subspace topology of `PadicAlgCl` that gq2's statements see.
* **The residue-degree bridge** (memo Q3) `natCard_residueField_eq_two_pow : #𝓀[↥K] = 2 ^ FF.f`,
  through `osub_eq_integer` (gq2's unit ball is Tau Ceti's `𝒪[↥K]`) and gq2's own count
  `UnitFiltrationCounts.residueField_card_eq_pow_f`.
* **`G_K^{ab}` in Tau Ceti's model**: `galKEquiv` (gq2's `GalK K` is A1's `↥K.fixingSubgroup`, the
  same type on two instance paths),
  `abEquivK : GalKab K ≃ₜ* Field.absoluteGaloisGroupAbelianization ↥K` with its values, the
  `inclAbK` compatibility `inclAbK_abEquivK_symm_mk`, and compactness of `GalK K` and `GalKab K`
  as named theorems.

This file keeps A1's light imports (no class-field-theory module): under the heavy B5 imports one
`simpa` of the bridge timed out at `DiscreteTopology ℚ̄₂` (memo, "Pathology met").
-/

noncomputable section

namespace GQ2.TauCetiBridge

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

open ValuativeRel GQ2.Dyadic

/-! ## The generic bridge -/

/-- **The generic norm ↔ valuation bridge.** Any valuative relation on an algebraic extension
`M/F` of a local field that extends `F`'s is the relation of any valuation `w` of `M` whose
restriction to `F` is equivalent to `F`'s valuation.

Tau Ceti: `TauCeti.vle_iff_algebraicExtensionNormedField_norm_le`
(`TauCeti/NumberTheory/LocalField/AlgebraicExtension/Basic.lean:266`) followed by
`TauCeti.algebraicExtensionNormedField_norm_le_norm_iff` (`:241`), the two uniqueness theorems
for Tau Ceti's spectral norm on `M`; only their statements are used. -/
theorem vle_iff_of_isEquiv {F M : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field M] [Algebra F M] [Algebra.IsAlgebraic F M]
    [ValuativeRel M] [ValuativeExtension F M] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {w : Valuation M Γ} (hw : (w.comap (algebraMap F M)).IsEquiv (valuation F)) (x y : M) :
    x ≤ᵥ y ↔ w x ≤ w y :=
  (TauCeti.vle_iff_algebraicExtensionNormedField_norm_le F x y).trans
    (TauCeti.algebraicExtensionNormedField_norm_le_norm_iff hw x y)

section K

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]

/-! ## The bridge at `↥K` -/

/-- gq2's spectral norm of `ℚ̄₂` (Mathlib's `PadicAlgCl`), restricted to `↥K`, as an
`ℝ≥0`-valued valuation: the `w` of `vle_iff_of_isEquiv` at `M = ↥K`. -/
def normValuationK : Valuation K NNReal :=
  (NormedField.valuation : Valuation ℚ̄₂ NNReal).comap (K.val : K →+* ℚ̄₂)

omit [FiniteDimensional ℚ_[2] K] in
@[simp] theorem normValuationK_apply (x : K) : normValuationK K x = ‖(x : ℚ̄₂)‖₊ := rfl

omit [FiniteDimensional ℚ_[2] K] in
/-- On `ℚ₂ ⊆ ↥K` the restricted norm is the `2`-adic norm, which orders `ℚ₂` like Tau Ceti's
valuation: Tau Ceti's `Padic.normalizedAbsoluteValue_eq_nnnorm`
(`TauCeti/NumberTheory/LocalField/Padic.lean:164`) with
`TauCeti.normalizedAbsoluteValue_le_normalizedAbsoluteValue_iff`
(`TauCeti/NumberTheory/LocalField/NormalizedValuation.lean:493`), and Mathlib's
`norm_algebraMap'`.  This is the hypothesis of `vle_iff_of_isEquiv` at `(ℚ₂, ↥K)`. -/
theorem isEquiv_normValuationK :
    ((normValuationK K).comap (algebraMap ℚ_[2] K)).IsEquiv (valuation ℚ_[2]) := by
  intro a b
  simp only [Valuation.comap_apply, normValuationK_apply]
  rw [← TauCeti.normalizedAbsoluteValue_le_normalizedAbsoluteValue_iff,
    ← NNRat.cast_le (K := NNReal),
    Padic.normalizedAbsoluteValue_eq_nnnorm, Padic.normalizedAbsoluteValue_eq_nnnorm]
  change ‖algebraMap ℚ_[2] ℚ̄₂ a‖₊ ≤ ‖algebraMap ℚ_[2] ℚ̄₂ b‖₊ ↔ _
  rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm,
    norm_algebraMap' (𝕜' := ℚ̄₂), norm_algebraMap' (𝕜' := ℚ̄₂), ← NNReal.coe_le_coe, coe_nnnorm,
    coe_nnnorm]

/-- **The norm ↔ valuation bridge at `↥K`, valuation form.** Tau Ceti's valuation on `↥K` (for
A1's `valuativeRel K`) compares gq2's spectral norms: `vle_iff_of_isEquiv` at `(ℚ₂, ↥K)` with
`w = normValuationK K`, under the package plus `valuativeExtension K`.  Every norm hypothesis of
B5-K and B10-K (`nu_ur_recip_unit`, `nu_ur_recip_uniformizer`, `nuT_recip_unit`,
`nuT_recip_uniformizer`, `ki_unramified`) is read into Tau Ceti through this lemma. -/
theorem valuation_le_iff_norm_le (x y : K) :
    letI := valuativeRel K
    valuation K x ≤ valuation K y ↔ ‖(x : ℚ̄₂)‖ ≤ ‖(y : ℚ̄₂)‖ := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  haveI := valuativeExtension K
  rw [← Valuation.Compatible.vle_iff_le (v := valuation K) x y,
    vle_iff_of_isEquiv (isEquiv_normValuationK K) x y, normValuationK_apply, normValuationK_apply,
    ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]

/-- **The norm ↔ valuation bridge at `↥K`, relation form**: Tau Ceti's `x ≤ᵥ y` on `↥K` is
`‖x‖ ≤ ‖y‖` in gq2's spectral norm. -/
theorem vle_iff_norm_le (x y : K) :
    letI := valuativeRel K
    x ≤ᵥ y ↔ ‖(x : ℚ̄₂)‖ ≤ ‖(y : ℚ̄₂)‖ := by
  letI := valuativeRel K
  exact (Valuation.Compatible.vle_iff_le (v := valuation K) x y).trans
    (valuation_le_iff_norm_le K x y)

/-- The norm ↔ valuation bridge at `↥K`, for equalities. -/
theorem valuation_eq_iff_norm_eq (x y : K) :
    letI := valuativeRel K
    valuation K x = valuation K y ↔ ‖(x : ℚ̄₂)‖ = ‖(y : ℚ̄₂)‖ := by
  letI := valuativeRel K
  rw [le_antisymm_iff, le_antisymm_iff, valuation_le_iff_norm_le, valuation_le_iff_norm_le]

/-! ## Normalized valuations -/

/-- **Units.** A unit of `↥K` of spectral norm `1` has Tau Ceti normalized valuation `1`:
`TauCeti.normalizedValuation_eq_one_iff`
(`TauCeti/NumberTheory/LocalField/NormalizedValuation.lean:232`) and the bridge.  Fills the unit
clauses B5-K `nu_ur_recip_unit` and B10-K `nuT_recip_unit`. -/
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

/-- **Uniformizers.** gq2's spectral uniformizer specification (norm `< 1`, and maximal among
nonzero elements of norm `< 1`) gives Tau Ceti normalized valuation `ofAdd 1`.  Tau Ceti:
`TauCeti.normalizedValuation_surjective` (`NormalizedValuation.lean:327`) supplies a `ϖ` of
valuation `ofAdd 1`, `TauCeti.toAdd_normalizedValuation_le_iff_valuation_le` (`:258`) and the
bridge compare it with `π`.  Fills the uniformizer clauses B5-K `nu_ur_recip_uniformizer` and
B10-K `nuT_recip_uniformizer`. -/
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
        valuation_le_iff_norm_le, OneMemClass.coe_one, norm_one]
      exact hπ.le
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

/-- **`v_K(2) ≠ 0`**: `2` is not a unit of `↥K`, since `‖2‖ < 1` (Mathlib's `Padic.norm_p_lt_one`)
and the bridge.  It makes `rec_K(2)` the witness of the marked level in B5-K (memo Q1). -/
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

/-! ## The two topologies on `↥K` are equal -/

/-- The subspace (`PadicAlgCl`) topology of `↥K` is a valuative topology for Tau Ceti's relation
`valuativeRel K`: Mathlib's `IsValuativeTopology.of_mem_nhds_zero_iff_vle`
(`Mathlib/Topology/Algebra/ValuativeRel/ValuativeTopology.lean`) with gq2's
`NormedField.valuation`, compatible with Tau Ceti's relation by `vle_iff_norm_le`. -/
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

/-- **The topology comparison.** Tau Ceti's topology `localTopology K` on `↥K` (from
`TauCeti.finiteIntermediateFieldTopology`) equals the subspace topology gq2's statements use.
Both are valuative topologies for the same relation (Tau Ceti's
`TauCeti.finiteIntermediateField_isValuativeTopology`,
`TauCeti/NumberTheory/LocalField/FiniteExtension/IntermediateField.lean:89`, and
`isValuativeTopology_subtype`), so their neighbourhood filters agree by Mathlib's
`IsValuativeTopology.mem_nhds_iff`.  The equation is not `rfl`.  B5-K `continuous_recip` needs it,
since gq2 states continuity for the subspace topology on `(↥K)ˣ`. -/
theorem localTopology_eq :
    localTopology K = (inferInstance : TopologicalSpace K) := by
  have h1 := @TauCeti.finiteIntermediateField_isValuativeTopology ℚ_[2] _ _ _ _ ℚ̄₂ _ _ K _
  have h2 := isValuativeTopology_subtype K
  letI := valuativeRel K
  refine TopologicalSpace.ext_nhds fun x => Filter.ext fun s => ?_
  rw [@IsValuativeTopology.mem_nhds_iff _ _ _ (localTopology K) h1,
    @IsValuativeTopology.mem_nhds_iff _ _ _ _ h2]

/-! ## The residue-degree bridge (memo Q3) -/

/-- gq2's unit ball `UnitFiltrationCounts.Osub K = {‖x‖ ≤ 1}` is Tau Ceti's ring of integers
`𝒪[↥K] = (valuation ↥K).integer`, as subrings of `↥K` (the bridge). -/
theorem osub_eq_integer :
    letI := valuativeRel K
    UnitFiltrationCounts.Osub K = (valuation K).integer := by
  letI := valuativeRel K
  ext x
  change ‖x‖ ≤ 1 ↔ valuation K x ≤ 1
  rw [← map_one (valuation K), valuation_le_iff_norm_le]
  simp only [OneMemClass.coe_one, norm_one]
  rfl

/-- The residue map `Osub K →+* 𝓀[↥K]`, through `osub_eq_integer`. -/
def osubToResidue :
    letI := valuativeRel K
    UnitFiltrationCounts.Osub K →+* IsLocalRing.ResidueField (valuation K).integer :=
  letI := valuativeRel K
  (IsLocalRing.residue _).comp (RingEquiv.subringCongr (osub_eq_integer K)).toRingHom

theorem osubToResidue_surjective :
    letI := valuativeRel K
    Function.Surjective (osubToResidue K) := by
  letI := valuativeRel K
  exact (IsLocalRing.residue_surjective).comp
    (RingEquiv.subringCongr (osub_eq_integer K)).surjective

/-- The kernel of the residue map is gq2's maximal ideal `{‖x‖ < 1}` (Mathlib's
`Valuation.Integer.not_isUnit_iff_valuation_lt_one` and the bridge). -/
theorem ker_osubToResidue :
    letI := valuativeRel K
    RingHom.ker (osubToResidue K) = UnitFiltrationCounts.maxIdeal K := by
  letI := valuativeRel K
  ext x
  rw [RingHom.mem_ker, osubToResidue, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  change valuation K (x : K) < 1 ↔ ‖(x : K)‖ < 1
  rw [← map_one (valuation K), lt_iff_lt_of_le_iff_le (valuation_le_iff_norm_le K 1 (x : K))]
  simp

/-- Tau Ceti's residue field `𝓀[↥K]` has the size of gq2's intrinsic residue field
`UnitFiltrationCounts.ResidueField K = O/𝔪`. -/
theorem natCard_residueField_eq :
    letI := valuativeRel K
    Nat.card (IsLocalRing.ResidueField (valuation K).integer) =
      Nat.card (UnitFiltrationCounts.ResidueField K) := by
  letI := valuativeRel K
  refine Nat.card_congr ((Ideal.quotEquivOfEq (ker_osubToResidue K).symm).trans
    (RingHom.quotientKerEquivOfSurjective (osubToResidue_surjective K))).toEquiv.symm

/-- **The residue-degree bridge (memo Q3).** `#𝓀[↥K] = 2 ^ FF.f` for every dyadic unit
filtration `FF` of `K`: `natCard_residueField_eq` with gq2's public count
`UnitFiltrationCounts.residueField_card_eq_pow_f`.  It identifies Tau Ceti's relator exponent
`Nat.card 𝓀[↥K]` with gq2's `qOf K FF` in the B10-K `equiv`; no private lemma is needed. -/
theorem natCard_residueField_eq_two_pow (FF : DyadicUnitFiltration K) :
    letI := valuativeRel K
    Nat.card (IsLocalRing.ResidueField (valuation K).integer) = 2 ^ FF.f :=
  (natCard_residueField_eq K).trans (UnitFiltrationCounts.residueField_card_eq_pow_f K FF)

/-! ## `G_K^{ab}` in Tau Ceti's model -/

/-- gq2's `GalK K` (a subgroup of `AbsGalQ2`) is A1's `↥K.fixingSubgroup` (a subgroup of
`Kummer.GaloisGroup ℚ₂`): the same type with two registered instance paths (bundle memo R6), so
the identity is a topological group isomorphism. -/
def galKEquiv : GalK K ≃ₜ* ↥(K.fixingSubgroup : Subgroup (GQ2.Kummer.GaloisGroup ℚ_[2])) :=
  ContinuousMulEquiv.refl _

/-- **`abEquivK`**: gq2's `G_K^{ab}` is Tau Ceti's (Mathlib's)
`Field.absoluteGaloisGroupAbelianization ↥K`, the abelianization of `galKEquiv` followed by A1's
`absGalEquivFixing K` inverted.  Tau Ceti: `ContinuousMulEquiv.topologicalAbelianizationCongr`
(`TauCeti/Topology/Algebra/Group/TopologicalAbelianization.lean:208`).  B5-K transports the Artin
map and the unramified coordinate of `↥K` along it. -/
def abEquivK : GalKab K ≃ₜ* Field.absoluteGaloisGroupAbelianization K :=
  ((galKEquiv K).trans (absGalEquivFixing K).symm).topologicalAbelianizationCongr

/-- `abEquivK` on a class `toAbK g` (Tau Ceti's `topologicalAbelianizationCongr_mk`, `:214`). -/
theorem abEquivK_toAbK (g : GalK K) :
    abEquivK K (toAbK K g) =
      (((absGalEquivFixing K).symm (galKEquiv K g) : Field.absoluteGaloisGroup K) :
        Field.absoluteGaloisGroupAbelianization K) :=
  ContinuousMulEquiv.topologicalAbelianizationCongr_mk _ g

/-- `abEquivK⁻¹` on the class of `τ ∈ G_{↥K}`. -/
theorem abEquivK_symm_mk (τ : Field.absoluteGaloisGroup K) :
    (abEquivK K).symm (τ : Field.absoluteGaloisGroupAbelianization K) =
      toAbK K ((galKEquiv K).symm (absGalEquivFixing K τ)) := by
  rw [ContinuousMulEquiv.symm_apply_eq, abEquivK_toAbK]
  show _ = (((absGalEquivFixing K).symm (absGalEquivFixing K τ) : Field.absoluteGaloisGroup K) :
    Field.absoluteGaloisGroupAbelianization K)
  rw [ContinuousMulEquiv.symm_apply_apply]

/-- The `G_K`-element attached to `τ ∈ G_{↥K}`, read in `AbsGalQ2`, is
`TauCeti.absoluteGaloisGroupExtend ℚ₂ ↥K (sepEmb K) τ` (A1's `coe_absGalEquivFixing_apply`). -/
theorem coe_galKEquiv_symm_absGalEquivFixing (τ : Field.absoluteGaloisGroup K) :
    (((galKEquiv K).symm (absGalEquivFixing K τ) : GalK K) : AbsGalQ2) =
      TauCeti.absoluteGaloisGroupExtend ℚ_[2] K (sepEmb K) τ :=
  coe_absGalEquivFixing_apply K τ

/-- **The `inclAbK` compatibility.** gq2's abelianized inclusion
`inclAbK K : G_K^{ab} → G_{ℚ₂}^{ab}` on the `abEquivK`-transport of the class of `τ ∈ G_{↥K}` is
the class of Tau Ceti's extension `absoluteGaloisGroupExtend ℚ₂ ↥K (sepEmb K) τ`, the map
`artinMap_norm` is stated with.  It holds pointwise (`inclAbK_toAbK` is `rfl`), so no comparison of
abelianized maps is needed. -/
theorem inclAbK_abEquivK_symm_mk (τ : Field.absoluteGaloisGroup K) :
    inclAbK K ((abEquivK K).symm (τ : Field.absoluteGaloisGroupAbelianization K)) =
      toAb (TauCeti.absoluteGaloisGroupExtend ℚ_[2] K (sepEmb K) τ) := by
  rw [abEquivK_symm_mk, inclAbK_toAbK, coe_galKEquiv_symm_absGalEquivFixing]

omit [FiniteDimensional ℚ_[2] K] in
/-- `G_K` is compact, on gq2's (`AbsGalQ2`) instance path: A1's `compactSpace_fixingSubgroup`.
A theorem, not an instance: instance search does not find it through `GalK K`, and B5-K passes
it explicitly. -/
theorem compactSpace_galK_of_fixingSubgroup : CompactSpace (GalK K) :=
  compactSpace_fixingSubgroup K

omit [FiniteDimensional ℚ_[2] K] in
/-- `G_K^{ab}` is compact (a quotient of `compactSpace_galK_of_fixingSubgroup`).  B5-K passes it
explicitly to the level lemma, where instance search misses it even with it in context (see the
memo's instance table). -/
theorem compactSpace_galKab_of_fixingSubgroup : CompactSpace (GalKab K) :=
  haveI := compactSpace_galK_of_fixingSubgroup K
  Quotient.compactSpace

end K

end GQ2.TauCetiBridge

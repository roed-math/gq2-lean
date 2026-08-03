/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.OrientedTameBundle
import GQ2.Dyadic.SemanticSelected
import GQ2.Dyadic.MarkedCore.Cores
import GQ2.UnitNormIndex

/-!
# Arithmetic branch selection for a finite dyadic field

This file carries the general presentation as far as the current field formalization permits.
For `B : MarkedRecip Rec K` and `FF : DyadicUnitFiltration K`, the filtration supplies a
uniformizer, hence surjectivity of `B.nu_ur`; `B.toMarkedPair` then constructs the complete
`CyclotomicFrobeniusDatum`.  On an even Labute family, explicitly supplied family-specific
marked-generator data determine the compact/procyclic row.  For `M`, the product splitting and
the ramified-`i` hypothesis exclude the even-eta row.  For `N`, the whole procyclic orientation
image directly makes the canonical generator odd.  The procyclic selector applies
`exists_isEtaFor_with_display_of_not_even`, so the eta stored in the selected branch is the
arithmetic lift chosen by that theorem and carries its own honest display.

The unresolved general Labute theorem is visible in the corrected
`FamilyFieldBranchWitness`:

* the caller chooses `L`, `M alpha`, or `N alpha` and proves the required degree parity;
* on `L`, the caller supplies the still-missing theorem that the marked level is zero;
* on `M`, the caller supplies the product splitting used by packet Proposition 8.1 at the
  canonical `mUnit alpha`;
* on `N`, the caller supplies whole-image procyclic generator data at the canonical
  `nUnit alpha`, never the contradictory product splitting.

`FieldDataEven` proves the even cup-form normal form, but it does not determine `M` versus `N` or
the integer `alpha`; `LabuteInterface` deliberately keeps that classification conditional.
The inverse equations for the standard M/N units are no longer part of the residual interface:
they uniquely determine, and are discharged by, `mUnit alpha` and `nUnit alpha`.  No selector
without this residual family-classification witness is currently justified.  There is no
uniqueness claim for eta: a residue class has many 2-adic lifts, and the semantic presentation
works with the one chosen here.  The older `FieldBranchWitness` and `FieldBranchSelection` remain
below for source compatibility, with an explicit theorem showing why their legacy `N` path is
uninhabited.

The resulting semantic word is exactly the improved five-row table:

| row | word |
|---|---|
| `L` | `Words.LSq.lSqW` |
| `N0` | `Words.nCompactW` |
| `Npc` | `Words.Npc.npcWUnit` |
| `M0` | `Words.MCompact.mCompactW` |
| `Mpc` | `Words.Mpc.mpcWUnit` with `p epsilon r` |
-/

namespace GQ2.Dyadic

open GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

noncomputable section

/-! ## Field data already available in the repository -/

/-- The minimal numerical identification between `FieldParameters` and a finite field carrying
a unit filtration.  The only arithmetic content beyond the two displayed identifications is the
divisibility `FF.f ∣ [K : Q_2]` already carried by `FieldParameters`. -/
structure FiniteDyadicParameters (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] (FF : DyadicUnitFiltration K) where
  params : FieldParameters
  degree_eq : params.n = Module.finrank ℚ_[2] K
  residueDegree_eq : params.f = FF.f

namespace FiniteDyadicParameters

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  {FF : DyadicUnitFiltration K}

/-- The carried numerical data has the residue cardinality supplied by the filtration. -/
theorem qK_eq_qOf (D : FiniteDyadicParameters K FF) : D.params.qK = qOf K FF := by
  rw [D.params.qK_eq, qOf, D.residueDegree_eq]

/-- Construct the numerical parameter record from the weakest arithmetic fact it consumes:
the filtration's residue degree divides the field degree.  In particular callers do not choose
`qK` or separately prove positivity. -/
def ofResidueDegreeDvd (FF : DyadicUnitFiltration K)
    (hdiv : FF.f ∣ Module.finrank ℚ_[2] K) : FiniteDyadicParameters K FF where
  params :=
    { n := Module.finrank ℚ_[2] K
      f := FF.f
      qK := 2 ^ FF.f
      qK_eq := rfl
      one_le_n := Module.finrank_pos
      one_le_f := FF.hf_pos
      f_dvd_n := hdiv }
  degree_eq := rfl
  residueDegree_eq := rfl

@[simp] theorem ofResidueDegreeDvd_n (FF : DyadicUnitFiltration K)
    (hdiv : FF.f ∣ Module.finrank ℚ_[2] K) :
    (ofResidueDegreeDvd FF hdiv).params.n = Module.finrank ℚ_[2] K := rfl

@[simp] theorem ofResidueDegreeDvd_f (FF : DyadicUnitFiltration K)
    (hdiv : FF.f ∣ Module.finrank ℚ_[2] K) :
    (ofResidueDegreeDvd FF hdiv).params.f = FF.f := rfl

@[simp] theorem ofResidueDegreeDvd_qK (FF : DyadicUnitFiltration K)
    (hdiv : FF.f ∣ Module.finrank ℚ_[2] K) :
    (ofResidueDegreeDvd FF hdiv).params.qK = qOf K FF := rfl

/-- Exact existence boundary for the numerical selector package.  This is strictly weaker than
the fundamental identity involving `FF.e`, and is the smallest missing arithmetic proposition
for constructing `FiniteDyadicParameters`. -/
theorem nonempty_iff_residueDegree_dvd (FF : DyadicUnitFiltration K) :
    Nonempty (FiniteDyadicParameters K FF) ↔ FF.f ∣ Module.finrank ℚ_[2] K := by
  constructor
  · rintro ⟨D⟩
    rw [← D.residueDegree_eq, ← D.degree_eq]
    exact D.params.f_dvd_n
  · exact fun hdiv => ⟨ofResidueDegreeDvd FF hdiv⟩

/-- Construct the numerical parameter record from the classical fundamental identity. -/
def ofFundamentalIdentity (FF : DyadicUnitFiltration K)
    (hdegree : Module.finrank ℚ_[2] K = FF.e * FF.f) : FiniteDyadicParameters K FF :=
  ofResidueDegreeDvd FF ⟨FF.e, by rw [hdegree, Nat.mul_comm]⟩

@[simp] theorem ofFundamentalIdentity_n (FF : DyadicUnitFiltration K)
    (hdegree : Module.finrank ℚ_[2] K = FF.e * FF.f) :
    (ofFundamentalIdentity FF hdegree).params.n = Module.finrank ℚ_[2] K := rfl

@[simp] theorem ofFundamentalIdentity_f (FF : DyadicUnitFiltration K)
    (hdegree : Module.finrank ℚ_[2] K = FF.e * FF.f) :
    (ofFundamentalIdentity FF hdegree).params.f = FF.f := rfl

@[simp] theorem ofFundamentalIdentity_qK (FF : DyadicUnitFiltration K)
    (hdegree : Module.finrank ℚ_[2] K = FF.e * FF.f) :
    (ofFundamentalIdentity FF hdegree).params.qK = qOf K FF := rfl

/-- A numerical parameter package identifies the filtration ramification index exactly when the
fundamental identity holds.  Thus the weaker divisibility package does not silently assert that
its quotient `params.e` is `FF.e`. -/
theorem params_e_eq_iff_fundamentalIdentity (D : FiniteDyadicParameters K FF) :
    D.params.e = FF.e ↔ Module.finrank ℚ_[2] K = FF.e * FF.f := by
  constructor
  · intro he
    calc
      Module.finrank ℚ_[2] K = D.params.n := D.degree_eq.symm
      _ = D.params.e * D.params.f := D.params.n_eq
      _ = FF.e * FF.f := by rw [he, D.residueDegree_eq]
  · intro hdegree
    apply Nat.eq_of_mul_eq_mul_right FF.hf_pos
    calc
      D.params.e * FF.f = D.params.e * D.params.f := by rw [D.residueDegree_eq]
      _ = D.params.n := D.params.e_mul_f
      _ = Module.finrank ℚ_[2] K := D.degree_eq
      _ = FF.e * FF.f := hdegree

section Galois

variable [IsGalois ℚ_[2] K]

/-- The norm of a filtration uniformizer supplies an unconditional factorization of the degree
in the Galois case.  The still-missing residue-field bridge is precisely the identification of
this norm valuation with `FF.f`. -/
theorem degree_eq_e_mul_normValPiToNat (FF : DyadicUnitFiltration K) :
    Module.finrank ℚ_[2] K =
      FF.e * (GQ2.UnitNormIndex.normValPi K FF).toNat := by
  have hpos := GQ2.UnitNormIndex.normValPi_pos K FF
  have hcast : (((GQ2.UnitNormIndex.normValPi K FF).toNat : ℕ) : ℤ) =
      GQ2.UnitNormIndex.normValPi K FF := Int.toNat_of_nonneg (by omega)
  have h := GQ2.UnitNormIndex.e_mul_normValPi K FF
  rw [← hcast] at h
  exact_mod_cast h.symm

/-- In a Galois layer the fundamental identity is equivalent to the one missing compatibility:
`FF.f` equals the valuation of the norm of the chosen uniformizer. -/
theorem fundamentalIdentity_iff_residueDegree_eq_normValPiToNat
    (FF : DyadicUnitFiltration K) :
    Module.finrank ℚ_[2] K = FF.e * FF.f ↔
      FF.f = (GQ2.UnitNormIndex.normValPi K FF).toNat := by
  constructor
  · intro hdegree
    apply Nat.eq_of_mul_eq_mul_left FF.he_pos
    rw [← hdegree]
    exact degree_eq_e_mul_normValPiToNat FF
  · intro hf
    rw [hf]
    exact degree_eq_e_mul_normValPiToNat FF

omit [FiniteDimensional ℚ_[2] K] [IsGalois ℚ_[2] K] in
/-- Canonical residue-field form of the missing norm compatibility.  The left side mentions the
filtration coordinate `FF.f`; the right side mentions only the intrinsic residue field and the
norm of the chosen uniformizer. -/
theorem residueDegree_eq_normValPiToNat_iff_residueField_card_eq
    (FF : DyadicUnitFiltration K) :
    FF.f = (GQ2.UnitNormIndex.normValPi K FF).toNat ↔
      Nat.card (GQ2.UnitFiltrationCounts.ResidueField K) =
        2 ^ (GQ2.UnitNormIndex.normValPi K FF).toNat := by
  rw [GQ2.UnitFiltrationCounts.residueField_card_eq_pow_f K FF]
  constructor
  · exact fun h => congrArg (fun n : ℕ => 2 ^ n) h
  · exact fun h => Nat.pow_right_injective (le_refl 2) h

/-- Galois-layer constructor reduced to the exact residue/norm compatibility, rather than an
externally supplied degree equation. -/
def ofNormValPi (FF : DyadicUnitFiltration K)
    (hf : FF.f = (GQ2.UnitNormIndex.normValPi K FF).toNat) :
    FiniteDyadicParameters K FF :=
  ofFundamentalIdentity FF
    ((fundamentalIdentity_iff_residueDegree_eq_normValPiToNat FF).2 hf)

/-- Selector constructor whose sole arithmetic input is the canonical residue-cardinality/norm
formula.  This is equivalent to `ofNormValPi`, but does not expose the filtration's chosen
residue exponent to callers. -/
def ofResidueFieldCardNormValPi (FF : DyadicUnitFiltration K)
    (hcard : Nat.card (GQ2.UnitFiltrationCounts.ResidueField K) =
      2 ^ (GQ2.UnitNormIndex.normValPi K FF).toNat) :
    FiniteDyadicParameters K FF :=
  ofNormValPi FF
    ((residueDegree_eq_normValPiToNat_iff_residueField_card_eq FF).2 hcard)

end Galois

/-! ### Degree parity consequences -/

omit [FiniteDimensional ℚ_[2] K] in
/-- Under the fundamental identity, the field degree is even exactly when at least one of the
ramification index and residue degree is even. -/
theorem degree_even_iff (FF : DyadicUnitFiltration K)
    (hdegree : Module.finrank ℚ_[2] K = FF.e * FF.f) :
    Even (Module.finrank ℚ_[2] K) ↔ Even FF.e ∨ Even FF.f := by
  rw [hdegree, Nat.even_mul]

omit [FiniteDimensional ℚ_[2] K] in
/-- Under the fundamental identity, the field degree is odd exactly when both filtration
invariants are odd. -/
theorem degree_odd_iff (FF : DyadicUnitFiltration K)
    (hdegree : Module.finrank ℚ_[2] K = FF.e * FF.f) :
    Odd (Module.finrank ℚ_[2] K) ↔ Odd FF.e ∧ Odd FF.f := by
  rw [← Nat.not_even_iff_odd, degree_even_iff FF hdegree, not_or,
    Nat.not_even_iff_odd, Nat.not_even_iff_odd]

end FiniteDyadicParameters

/-- The campaign's ramified-`i` hypothesis, with the square root and the repo's literal
equal-norm-value-groups negation kept visible. -/
structure RamifiedIData (K : IntermediateField ℚ_[2] ℚ̄₂) where
  deltaI : ℚ̄₂
  sq_deltaI : deltaI ^ 2 = -1
  ramified : ¬ HasEqualNormValueGroups K deltaI

namespace MarkedRecip

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K]

/-- A unit filtration supplies the uniformizer needed to prove surjectivity of the marked
unramified coordinate. -/
theorem nuUrSurjective (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) :
    Function.Surjective B.nu_ur :=
  B.surjective_nu_ur_of_uniformizer (uniformizerK K FF)
    (norm_uniformizerK_lt_one K FF) (uniformizerK_max K FF)

/-- The strongest canonical arithmetic datum currently constructed for every finite dyadic
field from the marked-reciprocity and unit-filtration interfaces. -/
def fieldMarkedPair (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) :
    MarkedPair (GalKab K) :=
  B.toMarkedPair (B.nuUrSurjective FF)

@[simp] theorem fieldMarkedPair_r (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) :
    (B.fieldMarkedPair FF).r = B.r := rfl

end MarkedRecip

/-! ## The exact residual arithmetic witnesses -/

/-- The legacy product-type generator and topological splitting facts required by packet
Proposition 8.1.  This is the `M_alpha` shape; it remains parameterized by the unit for source
compatibility.  `not_nonempty_nUnit` below proves that it cannot carry a valid `N_alpha` unit. -/
structure MarkedGeneratorData {A : Type*} [CommGroup A] (Q : MarkedPair A) (u : ℤ_[2]ˣ) where
  unit_mem : u ∈ Q.C
  negOne_mem : (-1 : ℤ_[2]ˣ) ∈ Q.C
  procyclic : Subgroup ↥Q.C
  unit_mem_procyclic : (⟨u, unit_mem⟩ : ↥Q.C) ∈ procyclic
  lambdaAdd_procyclic : ∀ w ∈ procyclic,
    ∃ j : ℤ, Q.lambdaAdd w = j • Q.lambdaAdd ⟨u, unit_mem⟩
  exists_decomp : ∀ c : ↥Q.C, ∃ w ∈ procyclic,
    c = w ∨ c = (⟨-1, negOne_mem⟩ : ↥Q.C) * w
  cyclotomic_trivial : ∀ w ∈ procyclic,
    PadicInt.toZModPow 2 (((Q.C).subtype w : ℤ_[2]ˣ) : ℤ_[2]) = 1

namespace MarkedGeneratorData

variable {A : Type*} [CommGroup A] {Q : MarkedPair A} {u : ℤ_[2]ˣ}

/-- Assemble the exact `MarkedSplitting` consumed by the existing exclusion theorem. -/
def toMarkedSplitting (G : MarkedGeneratorData Q u) : MarkedSplitting Q.datum :=
  Q.toMarkedSplitting u G.unit_mem G.negOne_mem G.procyclic G.unit_mem_procyclic
    G.lambdaAdd_procyclic G.exists_decomp

end MarkedGeneratorData

/-! ### The family boundary of the splitting interface

`MarkedGeneratorData` is the product-type (`M`) splitting: its distinguished generator lies in
a subgroup all of whose elements are `1 mod 4`, while `-1` is supplied as the other factor.
That is not the shape of the `N` orientation image.  For valid `N_alpha`, the canonical
orientation unit `nUnit alpha = -(1 + 2^alpha)^{-1}` is `-1 mod 4`; its orientation image is
procyclic as a whole and does not use a separate `-1` factor.

The impossibility theorem below is deliberately kept next to the old interface.  It prevents a
future all-field selector from silently reusing the `M` splitting in the `N` branch.  The
family-indexed replacement is non-breaking: the `M` case is definitionally the old record, while
the `N` case records the actual procyclic shape and already proves the one fact branch selection
needs at positive level, namely that the marked value of its generator is odd.
-/

/-- The weak algebraic shadow of a procyclic orientation image.  The selector uses topological
generation only through its finite-quotient consequence: the `lambda`-image of all of `C` is
generated by the distinguished unit.  Stating that consequence directly removes the artificial
subgroup, membership, `-1` and mod-4 binders of the product-type interface. -/
structure ProcyclicMarkedGeneratorData {A : Type*} [CommGroup A]
    (Q : MarkedPair A) (u : ℤ_[2]ˣ) where
  generator : ↥Q.C
  generator_eq : (generator : ℤ_[2]ˣ) = u
  lambdaAdd_generated : ∀ w : ↥Q.C,
    ∃ j : ℤ, Q.lambdaAdd w = j • Q.lambdaAdd generator

namespace ProcyclicMarkedGeneratorData

variable {A : Type*} [CommGroup A] {Q : MarkedPair A} {u : ℤ_[2]ˣ}

/-- The pinned standard unit belongs to the cyclotomic image. -/
theorem unit_mem (G : ProcyclicMarkedGeneratorData Q u) : u ∈ Q.C := by
  rw [← G.generator_eq]
  exact G.generator.property

/-- The packaged generator is the pinned standard unit in `C`. -/
theorem generator_eq_mk (G : ProcyclicMarkedGeneratorData Q u) :
    G.generator = ⟨u, G.unit_mem⟩ :=
  Subtype.ext G.generator_eq

/-- A generator of the whole procyclic orientation image has odd marked value at every positive
level.  This is the `N`-family replacement for the `M`-specific ramified-`i` exclusion argument. -/
theorem not_even_lambdaAdd (G : ProcyclicMarkedGeneratorData Q u) (hr : 1 ≤ Q.r) :
    ¬ Even (Q.lambdaAdd ⟨u, G.unit_mem⟩) := by
  rw [← G.generator_eq_mk]
  intro huEven
  obtain ⟨c, hc⟩ := Q.surjective_lambdaAdd 1
  obtain ⟨j, hj⟩ := G.lambdaAdd_generated c
  have honeEven : Even (1 : ZMod (2 ^ Q.r)) := by
    rw [← hc, hj]
    obtain ⟨z, hz⟩ := huEven
    refine ⟨j • z, ?_⟩
    rw [hz, smul_add]
  exact not_even_of_isUnit hr (isUnit_one : IsUnit (1 : ZMod (2 ^ Q.r))) honeEven

end ProcyclicMarkedGeneratorData

/-- Family-specific marked-generator data.  The existing record is retained exactly on `M`;
`N` uses its genuinely procyclic orientation image; `L` needs neither. -/
def FamilyMarkedGeneratorData {A : Type*} [CommGroup A] (Q : MarkedPair A) :
    LabuteType → Type
  | .L => PUnit
  | .M alpha => MarkedGeneratorData Q (MarkedCore.mUnit alpha)
  | .N alpha => ProcyclicMarkedGeneratorData Q (MarkedCore.nUnit alpha)

namespace MarkedGeneratorData

variable {A : Type*} [CommGroup A] {Q : MarkedPair A}

/-- The old splitting interface embeds definitionally into the `M` case of the family-specific
interface. -/
def toFamilyM {alpha : ℕ} (G : MarkedGeneratorData Q (MarkedCore.mUnit alpha)) :
    FamilyMarkedGeneratorData Q (.M alpha) := G

/-- A valid canonical `N` unit is `-1 mod 4`. -/
theorem nUnit_toZModPow_two {alpha : ℕ} (halpha : 2 ≤ alpha) :
    PadicInt.toZModPow 2 ((MarkedCore.nUnit alpha : ℤ_[2]ˣ) : ℤ_[2]) = -1 := by
  have h := congrArg (PadicInt.toZModPow 2)
    (MarkedCore.nUnit_mul (α := alpha) (by omega))
  simp only [map_mul, map_add, map_one, map_pow, map_ofNat, map_neg] at h
  have hpow : ((2 : ZMod (2 ^ 2)) ^ alpha) = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, alpha = k + 2 := ⟨alpha - 2, by omega⟩
    rw [pow_add]
    rw [show ((2 : ZMod (2 ^ 2)) ^ 2) = 0 by decide, mul_zero]
  rw [hpow, add_zero, mul_one] at h
  exact h

/-- **Regression: the legacy product splitting cannot be instantiated by a valid `N` unit.**
Its procyclic factor is required to be `1 mod 4`, but `nUnit alpha` is `-1 mod 4`.

This uses only the two conflicting fields (`unit_mem_procyclic` and `cyclotomic_trivial`); in
particular no claim about the still-unformalized field classification is smuggled into the
result. -/
theorem not_nonempty_nUnit {alpha : ℕ} (halpha : 2 ≤ alpha) :
    ¬ Nonempty (MarkedGeneratorData Q (MarkedCore.nUnit alpha)) := by
  rintro ⟨G⟩
  have hmod := G.cyclotomic_trivial ⟨MarkedCore.nUnit alpha, G.unit_mem⟩
    G.unit_mem_procyclic
  have hmod' : PadicInt.toZModPow 2 ((MarkedCore.nUnit alpha : ℤ_[2]ˣ) : ℤ_[2]) = 1 :=
    hmod
  rw [nUnit_toZModPow_two halpha] at hmod'
  exact (by decide : (-1 : ZMod (2 ^ 2)) ≠ 1) hmod'

end MarkedGeneratorData

namespace RamifiedIData

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K]

/-- The exact unconditional consequence of ramified `K(i)/K` currently available from the
marked-reciprocity interface: for any supplied marked splitting, either the marked level is zero
or its eta invariant is not even.  This does not choose between the alternatives and does not
construct the splitting. -/
theorem level_zero_or_not_even_eta (RI : RamifiedIData K) (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) {u : ℤ_[2]ˣ}
    (G : MarkedGeneratorData (B.fieldMarkedPair FF) u) :
    B.r = 0 ∨ (1 ≤ B.r ∧ ¬ Even G.toMarkedSplitting.eta) :=
  B.level_zero_or_not_even_eta_of_ramified (B.nuUrSurjective FF) G.toMarkedSplitting
    G.cyclotomic_trivial RI.deltaI RI.sq_deltaI RI.ramified

/-- Positive marked level selects the non-even-eta side of the ramified-`i` dichotomy. -/
theorem not_even_eta_of_level_ne_zero (RI : RamifiedIData K) (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) {u : ℤ_[2]ˣ}
    (G : MarkedGeneratorData (B.fieldMarkedPair FF) u) (hr : B.r ≠ 0) :
    1 ≤ B.r ∧ ¬ Even G.toMarkedSplitting.eta :=
  (RI.level_zero_or_not_even_eta B FF G).resolve_left hr

end RamifiedIData

/-- The legacy Labute-family witness.  Its `M` constructor pins the standard unit formula as well
as the product splitting.  The retained `N` constructor uses the same historical field, but
`CanonicalFieldBranchWitness.N_impossible` below proves that field contradictory at valid
`alpha`; new code should use `FamilyMarkedGeneratorData` instead. -/
inductive FieldBranchWitness {A : Type*} [CommGroup A] (P : FieldParameters)
    (Q : MarkedPair A) : Type
  | L (degree_odd : Odd P.n) (level_zero : Q.r = 0)
  | M (alpha : ℕ) (alpha_valid : 2 ≤ alpha) (degree_even : Even P.n)
      (u : ℤ_[2]ˣ) (unit_spec : (u : ℤ_[2]) * (1 - 2 ^ alpha) = 1)
      (marked : MarkedGeneratorData Q u)
  | N (alpha : ℕ) (alpha_valid : 2 ≤ alpha) (degree_even : Even P.n)
      (u : ℤ_[2]ˣ) (unit_spec : (u : ℤ_[2]) * (-(1 + 2 ^ alpha)) = 1)
      (marked : MarkedGeneratorData Q u)

namespace FieldBranchWitness

variable {A : Type*} [CommGroup A] {P : FieldParameters} {Q : MarkedPair A}

open MarkedCore

/-- The Labute family explicitly supplied by the residual classification witness. -/
def family : FieldBranchWitness P Q → LabuteType
  | .L .. => .L
  | .M alpha .. => .M alpha
  | .N alpha .. => .N alpha

/-- Arithmetic correctness of a selected branch relative to its source witness.  On a
procyclic row this retains the chosen eta-lift equation; on `Mpc` it also retains the extracted
sign equation. -/
def Matches : (W : FieldBranchWitness P Q) → BranchData → Prop
  | .L .., B => B = .L
  | .M alpha _ _ _ _ _, .M0 beta => beta = alpha ∧ Q.r = 0
  | .M alpha _ _ _ _ G, .Mpc beta r epsilon eta =>
      beta = alpha ∧ r = Q.r ∧
        G.toMarkedSplitting.negOneVal =
          ((epsVal epsilon * 2 ^ (Q.r - 1) : ℕ) : ZMod (2 ^ Q.r)) ∧
        IsEtaFor Q.datum G.toMarkedSplitting.u eta
  | .N alpha _ _ _ _ _, .N0 beta => beta = alpha ∧ Q.r = 0
  | .N alpha _ _ _ _ G, .Npc beta r eta =>
      beta = alpha ∧ r = Q.r ∧ IsEtaFor Q.datum G.toMarkedSplitting.u eta
  | _, _ => False

/-! ### Canonical orientation units

The two unit fields in the original witness are not arithmetic hypotheses.  Their displayed
inverse equations determine them uniquely, and the marked-core library already constructs the
canonical units `mUnit alpha` and `nUnit alpha`. -/

/-- The `M_alpha` inverse equation uniquely pins the unit to `mUnit alpha`. -/
theorem unit_eq_mUnit {alpha : ℕ} (halpha : 1 ≤ alpha) {u : ℤ_[2]ˣ}
    (hu : (u : ℤ_[2]) * (1 - 2 ^ alpha) = 1) : u = mUnit alpha := by
  apply Units.ext
  have hne : (1 - 2 ^ alpha : ℤ_[2]) ≠ 0 := by
    rw [← oneSubTwoPow_val halpha]
    exact Units.ne_zero _
  exact mul_right_cancel₀ hne (hu.trans (mUnit_mul halpha).symm)

/-- The `N_alpha` inverse equation uniquely pins the unit to `nUnit alpha`. -/
theorem unit_eq_nUnit {alpha : ℕ} (halpha : 1 ≤ alpha) {u : ℤ_[2]ˣ}
    (hu : (u : ℤ_[2]) * (-(1 + 2 ^ alpha)) = 1) : u = nUnit alpha := by
  apply Units.ext
  have hne : (-(1 + 2 ^ alpha) : ℤ_[2]) ≠ 0 := by
    rw [neg_ne_zero, ← onePlusTwoPow_val halpha]
    exact Units.ne_zero _
  apply mul_right_cancel₀ hne
  rw [hu]
  rw [mul_neg, nUnit_mul halpha, neg_neg]

end FieldBranchWitness

/-! ## The exact residual arithmetic classification interface

`CanonicalFieldBranchWitness` removes the artificial arbitrary-unit choices from
`FieldBranchWitness`.  Its remaining fields are precisely what the current local-field library
does not construct: the L/M/N family (and `alpha`), the parity consequence of that family, the
odd-family level-zero theorem, and the topological marked splitting for the appropriate
canonical standard unit.  In particular `FieldDataEven` cannot select M versus N: its cup-form
normal form is shared by both families.
-/

/-- The still-missing arithmetic classification, with the standard orientation units filled by
the marked-core library rather than supplied by the caller. -/
inductive CanonicalFieldBranchWitness {A : Type*} [CommGroup A] (P : FieldParameters)
    (Q : MarkedPair A) : Type
  | L (degree_odd : Odd P.n) (level_zero : Q.r = 0)
  | M (alpha : ℕ) (alpha_valid : 2 ≤ alpha) (degree_even : Even P.n)
      (marked : MarkedGeneratorData Q (MarkedCore.mUnit alpha))
  | N (alpha : ℕ) (alpha_valid : 2 ≤ alpha) (degree_even : Even P.n)
      (marked : MarkedGeneratorData Q (MarkedCore.nUnit alpha))

namespace CanonicalFieldBranchWitness

variable {A : Type*} [CommGroup A] {P : FieldParameters} {Q : MarkedPair A}

/-- **Selector-level regression:** the legacy `N` constructor is uninhabited at every valid
`alpha`.  It is retained in the inductive only for source compatibility; a corrected selector
must replace its `MarkedGeneratorData` field by `ProcyclicMarkedGeneratorData` before it can
classify `N` fields. -/
theorem N_impossible {alpha : ℕ} (alpha_valid : 2 ≤ alpha)
    (marked : MarkedGeneratorData Q (MarkedCore.nUnit alpha)) : False :=
  MarkedGeneratorData.not_nonempty_nUnit alpha_valid ⟨marked⟩

/-- Expand the minimal arithmetic classification into the legacy witness expected by the
selector.  The standard-unit equations are theorems, not new hypotheses. -/
noncomputable def toFieldBranchWitness :
    CanonicalFieldBranchWitness P Q → FieldBranchWitness P Q
  | .L degree_odd level_zero => .L degree_odd level_zero
  | .M alpha alpha_valid degree_even marked =>
      .M alpha alpha_valid degree_even (MarkedCore.mUnit alpha)
        (MarkedCore.mUnit_mul (le_trans (by omega) alpha_valid)) marked
  | .N alpha alpha_valid degree_even marked =>
      .N alpha alpha_valid degree_even (MarkedCore.nUnit alpha) (by
        rw [mul_neg, MarkedCore.nUnit_mul (le_trans (by omega) alpha_valid), neg_neg]) marked

/-- Normalize an older witness to the canonical-unit interface.  Thus the new record loses no
information: the arbitrary unit in an old M/N witness was already uniquely determined by its
equation. -/
noncomputable def ofFieldBranchWitness :
    FieldBranchWitness P Q → CanonicalFieldBranchWitness P Q
  | .L degree_odd level_zero => .L degree_odd level_zero
  | .M alpha alpha_valid degree_even u unit_spec marked =>
      .M alpha alpha_valid degree_even
        (FieldBranchWitness.unit_eq_mUnit (le_trans (by omega) alpha_valid) unit_spec ▸ marked)
  | .N alpha alpha_valid degree_even u unit_spec marked =>
      .N alpha alpha_valid degree_even
        (FieldBranchWitness.unit_eq_nUnit (le_trans (by omega) alpha_valid) unit_spec ▸ marked)

@[simp] theorem family_toFieldBranchWitness (W : CanonicalFieldBranchWitness P Q) :
    W.toFieldBranchWitness.family =
      match W with
      | .L .. => .L
      | .M alpha .. => .M alpha
      | .N alpha .. => .N alpha := by
  cases W <;> rfl

end CanonicalFieldBranchWitness

/-! ## The selected arithmetic branch -/

/-- A field branch selected from the strongest existing arithmetic datum and the explicit
residual Labute witness.  `display` belongs only to this chosen branch/lift; it is not a global
displayability assertion for arbitrary 2-adic units. -/
structure FieldBranchSelection (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] (P : FieldParameters) (Q : MarkedPair (GalKab K))
    (W : FieldBranchWitness P Q) where
  branch : BranchData
  valid : branch.Valid
  compatible : Compatible P branch
  level_eq : branch.level = Q.r
  family_eq : branch.labuteType = W.family
  arithmetic_matches : W.Matches branch
  display : branch.DisplayFor
  degree_eq_params :
    (SemanticPresentation.ofBranch (handleCount P branch) branch).degree = P.n
  degree_eq_field :
    (SemanticPresentation.ofBranch (handleCount P branch) branch).degree =
      Module.finrank ℚ_[2] K

namespace FieldBranchSelection

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  {P : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness P Q}

/-- The total improved semantic presentation attached to the selected arithmetic branch. -/
def semantic (S : FieldBranchSelection K P Q W) : SemanticPresentation :=
  SemanticPresentation.ofBranch (handleCount P S.branch) S.branch

@[simp] theorem semantic_degree (S : FieldBranchSelection K P Q W) :
    S.semantic.degree = P.n := S.degree_eq_params

theorem semantic_degree_field (S : FieldBranchSelection K P Q W) :
    S.semantic.degree = Module.finrank ℚ_[2] K := S.degree_eq_field

/-- The improved word table, at the handle count dictated by the field parameters. -/
noncomputable def improvedWord (P : FieldParameters) (B : BranchData) :
    PWord (Generator (SemanticPresentation.ofBranch (handleCount P B) B).degree) :=
  match B with
  | .L => Words.LSq.lSqW (handleCount P .L)
  | .N0 alpha => Words.nCompactW alpha (handleCount P (.N0 alpha))
  | .Npc alpha r eta => Words.Npc.npcWUnit alpha r (handleCount P (.Npc alpha r eta)) eta
  | .M0 alpha => Words.MCompact.mCompactW alpha (handleCount P (.M0 alpha))
  | .Mpc alpha r epsilon eta =>
      Words.Mpc.mpcWUnit alpha r (p epsilon r) eta (handleCount P (.Mpc alpha r epsilon eta))

@[simp] theorem improvedWord_L (P : FieldParameters) :
    improvedWord P .L = Words.LSq.lSqW (handleCount P .L) := rfl

@[simp] theorem improvedWord_N0 (P : FieldParameters) (alpha : ℕ) :
    improvedWord P (.N0 alpha) = Words.nCompactW alpha (handleCount P (.N0 alpha)) := rfl

/-- Arbitrary-unit regression: field selection uses `npcWUnit`, not the display-restricted or
uncorrected N word. -/
@[simp] theorem improvedWord_Npc (P : FieldParameters) (alpha r : ℕ) (eta : ℤ_[2]ˣ) :
    improvedWord P (.Npc alpha r eta) =
      Words.Npc.npcWUnit alpha r (handleCount P (.Npc alpha r eta)) eta := rfl

@[simp] theorem improvedWord_M0 (P : FieldParameters) (alpha : ℕ) :
    improvedWord P (.M0 alpha) =
      Words.MCompact.mCompactW alpha (handleCount P (.M0 alpha)) := rfl

/-- Arbitrary-unit and sign regression: field selection uses `mpcWUnit` with the literal
arithmetic parameter `p epsilon r`. -/
@[simp] theorem improvedWord_Mpc (P : FieldParameters) (alpha r : ℕ) (epsilon : Bool)
    (eta : ℤ_[2]ˣ) :
    improvedWord P (.Mpc alpha r epsilon eta) =
      Words.Mpc.mpcWUnit alpha r (p epsilon r) eta
        (handleCount P (.Mpc alpha r epsilon eta)) := rfl

/-- The selected semantic word is definitionally one of the five improved constructors. -/
theorem semantic_word_eq_improved (S : FieldBranchSelection K P Q W) :
    S.semantic.word = improvedWord P S.branch := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      cases branch <;> rfl

end FieldBranchSelection

/-! ## Construction -/

/-- Select the most arithmetic `BranchData` currently justified for a finite dyadic field.

All choices are honest.  In particular, each procyclic case constructs eta together with its
own integral display; no theorem about displayability of a pre-existing arbitrary unit is used.
-/
noncomputable def selectFieldBranch
    {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
    [FiniteDimensional ℚ_[2] K] (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (W : FieldBranchWitness D.params (B.fieldMarkedPair FF)) :
    FieldBranchSelection K D.params (B.fieldMarkedPair FF) W := by
  classical
  cases W with
  | L degree_odd level_zero =>
      have hcompat : Compatible D.params .L := compatible_L.mpr degree_odd
      refine
        { branch := .L
          valid := trivial
          compatible := hcompat
          level_eq := level_zero.symm
          family_eq := rfl
          arithmetic_matches := rfl
          display := PUnit.unit
          degree_eq_params := ?_
          degree_eq_field := ?_ }
      · change 2 * handleCount D.params .L + 1 = D.params.n
        exact two_mul_handleCount_add_one hcompat rfl
      · exact (two_mul_handleCount_add_one hcompat rfl).trans D.degree_eq
  | M alpha alpha_valid degree_even u unit_spec marked =>
      by_cases level_zero : B.r = 0
      · have hcompat : Compatible D.params (.M0 alpha) := compatible_M0.mpr degree_even
        refine
          { branch := .M0 alpha
            valid := alpha_valid
            compatible := hcompat
            level_eq := level_zero.symm
            family_eq := rfl
            arithmetic_matches := ⟨rfl, level_zero⟩
            display := PUnit.unit
            degree_eq_params := ?_
            degree_eq_field := ?_ }
        · change 2 + 2 * handleCount D.params (.M0 alpha) = D.params.n
          exact two_add_two_mul_handleCount hcompat rfl
        · exact (two_add_two_mul_handleCount hcompat rfl).trans D.degree_eq
      · have level_pos : 1 ≤ B.r := Nat.one_le_iff_ne_zero.mpr level_zero
        let S := marked.toMarkedSplitting
        have hodd : ¬ Even S.eta :=
          ((B.level_zero_or_not_even_eta_of_ramified (B.nuUrSurjective FF) S
            marked.cyclotomic_trivial RI.deltaI RI.sq_deltaI RI.ramified).resolve_left
              level_zero).2
        let hetaExists := exists_isEtaFor_with_display_of_not_even hodd
        let eta := Classical.choose hetaExists
        have hdisplayExists : ∃ _display : NpcDisplayFor eta,
            IsEtaFor (B.fieldMarkedPair FF).datum S.u eta :=
          Classical.choose_spec hetaExists
        let etaDisplay := Classical.choose hdisplayExists
        have heta : IsEtaFor (B.fieldMarkedPair FF).datum S.u eta :=
          Classical.choose_spec hdisplayExists
        let epsilon := (S.exists_eps level_pos).choose
        have hepsilon :
            S.negOneVal =
              ((epsVal epsilon * 2 ^ (B.r - 1) : ℕ) : ZMod (2 ^ B.r)) :=
          (S.exists_eps level_pos).choose_spec
        have hcompat : Compatible D.params (.Mpc alpha B.r epsilon eta) :=
          compatible_Mpc.mpr degree_even
        refine
          { branch := .Mpc alpha B.r epsilon eta
            valid := ⟨alpha_valid, level_pos⟩
            compatible := hcompat
            level_eq := rfl
            family_eq := rfl
            arithmetic_matches := ⟨rfl, rfl, hepsilon, heta⟩
            display := MpcDisplayFor.ofNpc etaDisplay
            degree_eq_params := ?_
            degree_eq_field := ?_ }
        · change 2 + 2 * handleCount D.params (.Mpc alpha B.r epsilon eta) = D.params.n
          exact two_add_two_mul_handleCount hcompat rfl
        · exact (two_add_two_mul_handleCount hcompat rfl).trans D.degree_eq
  | N alpha alpha_valid degree_even u unit_spec marked =>
      by_cases level_zero : B.r = 0
      · have hcompat : Compatible D.params (.N0 alpha) := compatible_N0.mpr degree_even
        refine
          { branch := .N0 alpha
            valid := alpha_valid
            compatible := hcompat
            level_eq := level_zero.symm
            family_eq := rfl
            arithmetic_matches := ⟨rfl, level_zero⟩
            display := PUnit.unit
            degree_eq_params := ?_
            degree_eq_field := ?_ }
        · change 2 + 2 * handleCount D.params (.N0 alpha) = D.params.n
          exact two_add_two_mul_handleCount hcompat rfl
        · exact (two_add_two_mul_handleCount hcompat rfl).trans D.degree_eq
      · have level_pos : 1 ≤ B.r := Nat.one_le_iff_ne_zero.mpr level_zero
        let S := marked.toMarkedSplitting
        have hodd : ¬ Even S.eta :=
          ((B.level_zero_or_not_even_eta_of_ramified (B.nuUrSurjective FF) S
            marked.cyclotomic_trivial RI.deltaI RI.sq_deltaI RI.ramified).resolve_left
              level_zero).2
        let hetaExists := exists_isEtaFor_with_display_of_not_even hodd
        let eta := Classical.choose hetaExists
        have hdisplayExists : ∃ _display : NpcDisplayFor eta,
            IsEtaFor (B.fieldMarkedPair FF).datum S.u eta :=
          Classical.choose_spec hetaExists
        let etaDisplay := Classical.choose hdisplayExists
        have heta : IsEtaFor (B.fieldMarkedPair FF).datum S.u eta :=
          Classical.choose_spec hdisplayExists
        have hcompat : Compatible D.params (.Npc alpha B.r eta) :=
          compatible_Npc.mpr degree_even
        refine
          { branch := .Npc alpha B.r eta
            valid := ⟨alpha_valid, level_pos⟩
            compatible := hcompat
            level_eq := rfl
            family_eq := rfl
            arithmetic_matches := ⟨rfl, rfl, heta⟩
            display := etaDisplay
            degree_eq_params := ?_
            degree_eq_field := ?_ }
        · change 2 + 2 * handleCount D.params (.Npc alpha B.r eta) = D.params.n
          exact two_add_two_mul_handleCount hcompat rfl
        · exact (two_add_two_mul_handleCount hcompat rfl).trans D.degree_eq

/-- The strongest current field-family selector: all data already formalized from local
reciprocity and the unit filtration is discharged by `selectFieldBranch`; its sole classification
input is the canonical residual witness above.  In particular the caller no longer supplies or
pins an arbitrary M/N orientation unit. -/
noncomputable def selectFieldBranchCanonical
    {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
    [FiniteDimensional ℚ_[2] K] (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (W : CanonicalFieldBranchWitness D.params (B.fieldMarkedPair FF)) :
    FieldBranchSelection K D.params (B.fieldMarkedPair FF) W.toFieldBranchWitness :=
  selectFieldBranch B FF D RI W.toFieldBranchWitness

/-- Exact improved-word preservation for the canonical arithmetic interface. -/
theorem semantic_word_eq_improved_of_canonical
    {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
    [FiniteDimensional ℚ_[2] K] (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (W : CanonicalFieldBranchWitness D.params (B.fieldMarkedPair FF)) :
    (selectFieldBranchCanonical B FF D RI W).semantic.word =
      FieldBranchSelection.improvedWord D.params
        (selectFieldBranchCanonical B FF D RI W).branch :=
  FieldBranchSelection.semantic_word_eq_improved _

/-! ## Corrected family-indexed selector

The legacy selector above cannot honestly select an `N` field: its `N` witness asks for the
product splitting `MarkedGeneratorData`, which is contradictory for the canonical `nUnit` at
every valid `alpha`.  The parallel interface below is the non-breaking migration path.  Its `M`
constructor is exactly the old product splitting, while its `N` constructor uses the whole-image
procyclic datum and its odd-generator theorem.  The selected five-row words are unchanged.
-/

/-- The corrected residual family witness.  The marked-generator field is indexed by the
Labute family, so an `N` witness can no longer accidentally demand the `M` product splitting. -/
inductive FamilyFieldBranchWitness {A : Type*} [CommGroup A] (P : FieldParameters)
    (Q : MarkedPair A) : Type
  | L (degree_odd : Odd P.n) (level_zero : Q.r = 0)
  | M (alpha : ℕ) (alpha_valid : 2 ≤ alpha) (degree_even : Even P.n)
      (marked : FamilyMarkedGeneratorData Q (.M alpha))
  | N (alpha : ℕ) (alpha_valid : 2 ≤ alpha) (degree_even : Even P.n)
      (marked : FamilyMarkedGeneratorData Q (.N alpha))

namespace FamilyFieldBranchWitness

variable {A : Type*} [CommGroup A] {P : FieldParameters} {Q : MarkedPair A}

/-- The Labute family carried by the corrected witness. -/
def family : FamilyFieldBranchWitness P Q → LabuteType
  | .L .. => .L
  | .M alpha .. => .M alpha
  | .N alpha .. => .N alpha

/-- Arithmetic correctness for the corrected selector.  The `Mpc` row retains the product
splitting's sign and eta equations.  The `Npc` row instead marks the canonical generator of the
whole procyclic image; it has no artificial `-1` factor. -/
def Matches : (W : FamilyFieldBranchWitness P Q) → BranchData → Prop
  | .L .., B => B = .L
  | .M alpha _ _ _, .M0 beta => beta = alpha ∧ Q.r = 0
  | .M alpha _ _ G, .Mpc beta r epsilon eta =>
      beta = alpha ∧ r = Q.r ∧
        G.toMarkedSplitting.negOneVal =
          ((epsVal epsilon * 2 ^ (Q.r - 1) : ℕ) : ZMod (2 ^ Q.r)) ∧
        IsEtaFor Q.datum G.toMarkedSplitting.u eta
  | .N alpha _ _ _, .N0 beta => beta = alpha ∧ Q.r = 0
  | .N alpha _ _ G, .Npc beta r eta =>
      beta = alpha ∧ r = Q.r ∧
        IsEtaFor Q.datum
          (⟨MarkedCore.nUnit alpha, G.unit_mem⟩ : ↥Q.C) eta
  | _, _ => False

/-- Every legacy canonical witness has a corrected interpretation.  The old `N` case is
eliminated by the regression theorem showing that its product splitting is impossible. -/
noncomputable def ofCanonical :
    CanonicalFieldBranchWitness P Q → FamilyFieldBranchWitness P Q
  | .L degree_odd level_zero => .L degree_odd level_zero
  | .M alpha alpha_valid degree_even marked =>
      .M alpha alpha_valid degree_even marked
  | .N _alpha alpha_valid _ marked =>
      (CanonicalFieldBranchWitness.N_impossible alpha_valid marked).elim

end FamilyFieldBranchWitness

/-- A selected arithmetic branch over the corrected family witness.  This intentionally
parallels `FieldBranchSelection` instead of changing it under existing exact-lifting clients. -/
structure FamilyFieldBranchSelection (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] (P : FieldParameters) (Q : MarkedPair (GalKab K))
    (W : FamilyFieldBranchWitness P Q) where
  branch : BranchData
  valid : branch.Valid
  compatible : Compatible P branch
  level_eq : branch.level = Q.r
  family_eq : branch.labuteType = W.family
  arithmetic_matches : W.Matches branch
  display : branch.DisplayFor
  degree_eq_params :
    (SemanticPresentation.ofBranch (handleCount P branch) branch).degree = P.n
  degree_eq_field :
    (SemanticPresentation.ofBranch (handleCount P branch) branch).degree =
      Module.finrank ℚ_[2] K

namespace FamilyFieldBranchSelection

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  {P : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FamilyFieldBranchWitness P Q}

/-- The semantic presentation selected by the corrected family path. -/
def semantic (S : FamilyFieldBranchSelection K P Q W) : SemanticPresentation :=
  SemanticPresentation.ofBranch (handleCount P S.branch) S.branch

@[simp] theorem semantic_degree (S : FamilyFieldBranchSelection K P Q W) :
    S.semantic.degree = P.n := S.degree_eq_params

theorem semantic_degree_field (S : FamilyFieldBranchSelection K P Q W) :
    S.semantic.degree = Module.finrank ℚ_[2] K := S.degree_eq_field

/-- Regression: the corrected selector still uses the improved five-row constructor table,
including arbitrary eta and the literal `p epsilon r` in the `Mpc` word. -/
theorem semantic_word_eq_improved (S : FamilyFieldBranchSelection K P Q W) :
    S.semantic.word = FieldBranchSelection.improvedWord P S.branch := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      cases branch <;> rfl

end FamilyFieldBranchSelection

/-- Select a five-row branch from the corrected family-indexed arithmetic witness.

The positive `M` case keeps the ramified-`i` exclusion argument based on the product splitting.
The positive `N` case does not manufacture that splitting: the generator of the whole procyclic
orientation image is odd by `ProcyclicMarkedGeneratorData.not_even_lambdaAdd`, which is exactly
the input needed to choose an eta lift together with its display. -/
noncomputable def selectFieldBranchFamily
    {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
    [FiniteDimensional ℚ_[2] K] (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (W : FamilyFieldBranchWitness D.params (B.fieldMarkedPair FF)) :
    FamilyFieldBranchSelection K D.params (B.fieldMarkedPair FF) W := by
  classical
  cases W with
  | L degree_odd level_zero =>
      have hcompat : Compatible D.params .L := compatible_L.mpr degree_odd
      refine
        { branch := .L
          valid := trivial
          compatible := hcompat
          level_eq := level_zero.symm
          family_eq := rfl
          arithmetic_matches := rfl
          display := PUnit.unit
          degree_eq_params := ?_
          degree_eq_field := ?_ }
      · change 2 * handleCount D.params .L + 1 = D.params.n
        exact two_mul_handleCount_add_one hcompat rfl
      · exact (two_mul_handleCount_add_one hcompat rfl).trans D.degree_eq
  | M alpha alpha_valid degree_even marked =>
      by_cases level_zero : B.r = 0
      · have hcompat : Compatible D.params (.M0 alpha) := compatible_M0.mpr degree_even
        refine
          { branch := .M0 alpha
            valid := alpha_valid
            compatible := hcompat
            level_eq := level_zero.symm
            family_eq := rfl
            arithmetic_matches := ⟨rfl, level_zero⟩
            display := PUnit.unit
            degree_eq_params := ?_
            degree_eq_field := ?_ }
        · change 2 + 2 * handleCount D.params (.M0 alpha) = D.params.n
          exact two_add_two_mul_handleCount hcompat rfl
        · exact (two_add_two_mul_handleCount hcompat rfl).trans D.degree_eq
      · have level_pos : 1 ≤ B.r := Nat.one_le_iff_ne_zero.mpr level_zero
        let S := marked.toMarkedSplitting
        have hodd : ¬ Even S.eta :=
          ((B.level_zero_or_not_even_eta_of_ramified (B.nuUrSurjective FF) S
            marked.cyclotomic_trivial RI.deltaI RI.sq_deltaI RI.ramified).resolve_left
              level_zero).2
        let hetaExists := exists_isEtaFor_with_display_of_not_even
          (d := (B.fieldMarkedPair FF).datum) (u := S.u) hodd
        let eta := Classical.choose hetaExists
        have hdisplayExists : ∃ _display : NpcDisplayFor eta,
            IsEtaFor (B.fieldMarkedPair FF).datum S.u eta :=
          Classical.choose_spec hetaExists
        let etaDisplay := Classical.choose hdisplayExists
        have heta : IsEtaFor (B.fieldMarkedPair FF).datum S.u eta :=
          Classical.choose_spec hdisplayExists
        let epsilon := (S.exists_eps level_pos).choose
        have hepsilon :
            S.negOneVal =
              ((epsVal epsilon * 2 ^ (B.r - 1) : ℕ) : ZMod (2 ^ B.r)) :=
          (S.exists_eps level_pos).choose_spec
        have hcompat : Compatible D.params (.Mpc alpha B.r epsilon eta) :=
          compatible_Mpc.mpr degree_even
        refine
          { branch := .Mpc alpha B.r epsilon eta
            valid := ⟨alpha_valid, level_pos⟩
            compatible := hcompat
            level_eq := rfl
            family_eq := rfl
            arithmetic_matches := ⟨rfl, rfl, hepsilon, heta⟩
            display := MpcDisplayFor.ofNpc etaDisplay
            degree_eq_params := ?_
            degree_eq_field := ?_ }
        · change 2 + 2 * handleCount D.params (.Mpc alpha B.r epsilon eta) = D.params.n
          exact two_add_two_mul_handleCount hcompat rfl
        · exact (two_add_two_mul_handleCount hcompat rfl).trans D.degree_eq
  | N alpha alpha_valid degree_even marked =>
      by_cases level_zero : B.r = 0
      · have hcompat : Compatible D.params (.N0 alpha) := compatible_N0.mpr degree_even
        refine
          { branch := .N0 alpha
            valid := alpha_valid
            compatible := hcompat
            level_eq := level_zero.symm
            family_eq := rfl
            arithmetic_matches := ⟨rfl, level_zero⟩
            display := PUnit.unit
            degree_eq_params := ?_
            degree_eq_field := ?_ }
        · change 2 + 2 * handleCount D.params (.N0 alpha) = D.params.n
          exact two_add_two_mul_handleCount hcompat rfl
        · exact (two_add_two_mul_handleCount hcompat rfl).trans D.degree_eq
      · have level_pos : 1 ≤ B.r := Nat.one_le_iff_ne_zero.mpr level_zero
        let u : ↥(B.fieldMarkedPair FF).C :=
          ⟨MarkedCore.nUnit alpha, marked.unit_mem⟩
        have hodd : ¬ Even ((B.fieldMarkedPair FF).lambdaAdd u) := by
          exact marked.not_even_lambdaAdd level_pos
        let hetaExists := exists_isEtaFor_with_display_of_not_even
          (d := (B.fieldMarkedPair FF).datum) (u := u) hodd
        let eta := Classical.choose hetaExists
        have hdisplayExists : ∃ _display : NpcDisplayFor eta,
            IsEtaFor (B.fieldMarkedPair FF).datum u eta :=
          Classical.choose_spec hetaExists
        let etaDisplay := Classical.choose hdisplayExists
        have heta : IsEtaFor (B.fieldMarkedPair FF).datum u eta :=
          Classical.choose_spec hdisplayExists
        have hcompat : Compatible D.params (.Npc alpha B.r eta) :=
          compatible_Npc.mpr degree_even
        refine
          { branch := .Npc alpha B.r eta
            valid := ⟨alpha_valid, level_pos⟩
            compatible := hcompat
            level_eq := rfl
            family_eq := rfl
            arithmetic_matches := ⟨rfl, rfl, heta⟩
            display := etaDisplay
            degree_eq_params := ?_
            degree_eq_field := ?_ }
        · change 2 + 2 * handleCount D.params (.Npc alpha B.r eta) = D.params.n
          exact two_add_two_mul_handleCount hcompat rfl
        · exact (two_add_two_mul_handleCount hcompat rfl).trans D.degree_eq

/-- End-to-end improved-word preservation for the corrected all-family selector. -/
theorem semantic_word_eq_improved_of_family
    {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
    [FiniteDimensional ℚ_[2] K] (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (W : FamilyFieldBranchWitness D.params (B.fieldMarkedPair FF)) :
    (selectFieldBranchFamily B FF D RI W).semantic.word =
      FieldBranchSelection.improvedWord D.params
        (selectFieldBranchFamily B FF D RI W).branch :=
  FamilyFieldBranchSelection.semantic_word_eq_improved _

end

end GQ2.Dyadic

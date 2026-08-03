/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.OrientedTameBundle
import GQ2.Dyadic.SemanticSelected
import GQ2.Dyadic.MarkedCore.Cores

/-!
# Arithmetic branch selection for a finite dyadic field

This file carries the general presentation as far as the current field formalization permits.
For `B : MarkedRecip Rec K` and `FF : DyadicUnitFiltration K`, the filtration supplies a
uniformizer, hence surjectivity of `B.nu_ur`; `B.toMarkedPair` then constructs the complete
`CyclotomicFrobeniusDatum`.  On an even Labute family, an explicitly supplied marked generator
and splitting determine the compact/procyclic row.  Under the explicit ramified-`i` hypothesis,
`MarkedRecip.level_zero_or_not_even_eta_of_ramified` excludes the even-eta row.  The procyclic
selector applies `exists_isEtaFor_with_display_of_not_even`, so the eta stored in the selected
branch is the arithmetic lift chosen by that theorem and carries its own honest display.

The unresolved general Labute theorem is visible in `FieldBranchWitness`:

* the caller chooses `L`, `M alpha`, or `N alpha` and proves the required degree parity;
* on `L`, the caller supplies the still-missing theorem that the marked level is zero;
* on `M` and `N`, the caller supplies the topological splitting facts used by packet
  Proposition 8.1, now at the library's canonical `mUnit alpha` or `nUnit alpha`.

`FieldDataEven` proves the even cup-form normal form, but it does not determine `M` versus `N` or
the integer `alpha`; `LabuteInterface` deliberately keeps that classification conditional.
The inverse equations for the standard M/N units are no longer part of the residual interface:
they uniquely determine, and are discharged by, `mUnit alpha` and `nUnit alpha`.  Consequently no
stronger all-field selector is currently justified.  There is no uniqueness claim for eta: a
residue class has many 2-adic lifts, and the semantic presentation works with the one chosen here.

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
a unit filtration.  The divisibility `f ∣ n` remains part of `params`; the constructor below
derives it from the single still-missing fundamental identity `[K : Q_2] = e f`. -/
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

/-- Construct the numerical parameter record directly from the unit-filtration invariants once
the fundamental identity `[K : Q_2] = e f` is available.  That identity is deliberately the
only hypothesis: the current `DyadicUnitFiltration` interface records `e` and `f` but does not
relate their product to `Module.finrank`.

In particular, callers no longer have to choose `qK`, prove positivity, or separately prove
`f | n`; all of those fields are consequences of the filtration. -/
def ofFundamentalIdentity (FF : DyadicUnitFiltration K)
    (hdegree : Module.finrank ℚ_[2] K = FF.e * FF.f) : FiniteDyadicParameters K FF where
  params :=
    { n := Module.finrank ℚ_[2] K
      f := FF.f
      qK := 2 ^ FF.f
      qK_eq := rfl
      one_le_n := Module.finrank_pos
      one_le_f := FF.hf_pos
      f_dvd_n := ⟨FF.e, by rw [hdegree, Nat.mul_comm]⟩ }
  degree_eq := rfl
  residueDegree_eq := rfl

@[simp] theorem ofFundamentalIdentity_n (FF : DyadicUnitFiltration K)
    (hdegree : Module.finrank ℚ_[2] K = FF.e * FF.f) :
    (ofFundamentalIdentity FF hdegree).params.n = Module.finrank ℚ_[2] K := rfl

@[simp] theorem ofFundamentalIdentity_f (FF : DyadicUnitFiltration K)
    (hdegree : Module.finrank ℚ_[2] K = FF.e * FF.f) :
    (ofFundamentalIdentity FF hdegree).params.f = FF.f := rfl

@[simp] theorem ofFundamentalIdentity_qK (FF : DyadicUnitFiltration K)
    (hdegree : Module.finrank ℚ_[2] K = FF.e * FF.f) :
    (ofFundamentalIdentity FF hdegree).params.qK = qOf K FF := rfl

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

/-- The standard generator and topological splitting facts required by packet Proposition 8.1.
The unit itself is a parameter so that `FieldBranchWitness` can separately pin it to the
`M_alpha` or `N_alpha` formula. -/
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

/-- The missing general Labute-family theorem, factored into its precise current residue.

The `M` and `N` constructors pin the standard unit formula as well as the splitting, preventing
an arbitrary topological generator from being attached to the wrong `alpha`. -/
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

end

end GQ2.Dyadic

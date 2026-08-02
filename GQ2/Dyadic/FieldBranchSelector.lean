/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.OrientedTameBundle
import GQ2.Dyadic.SemanticSelected

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
* on `M` and `N`, the caller supplies the correct standard unit and the topological splitting
  facts used by packet Proposition 8.1.

`FieldDataEven` proves the even cup-form normal form, but it does not determine `M` versus `N` or
the integer `alpha`; `LabuteInterface` deliberately keeps that classification conditional.
Consequently no stronger all-field selector is currently justified.  There is no uniqueness
claim: a residue class has many 2-adic lifts, and the semantic presentation works with the one
chosen here.

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
a unit filtration.  The divisibility `f ∣ n` remains part of `params`: no existing theorem
constructs that field automatically from `DyadicUnitFiltration`. -/
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

end FieldBranchWitness

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

end

end GQ2.Dyadic

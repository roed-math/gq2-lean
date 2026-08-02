/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.SelectedEta
import GQ2.Dyadic.Branches

/-!
# Total semantic selection of the improved dyadic presentations

`SelectedPresentation` deliberately stores the finite display data used by the frozen
certificates.  It cannot be selected from an arbitrary `BranchData`: the latter carries an
arbitrary unit of `Z_2`, and not every such unit has a rational `EtaData` display.

`SemanticPresentation` is the total companion required by the general arithmetic statement.  It
stores only a handle count and the already-classified `BranchData`; its dependent `word` uses the
five improved R5 formulas directly:

| branch | semantic word |
|---|---|
| `L` | `Words.LSq.lSqW` |
| `N0` | `Words.nCompactW` |
| `Npc` | corrected `Words.Npc.npcWUnit` |
| `M0` | `Words.MCompact.mCompactW` |
| `Mpc` | `Words.Mpc.mpcWUnit` with `p epsilon r` |

Thus selection is total without manufacturing display syntax.  When compatible display data is
available, the semantic and certificate selectors agree literally for `Npc` and define the same
corrected `GammaR` for `Mpc`; `GammaR_eq_selected_ofBranch` packages the comparison for all five
rows.

The arithmetic classification has a narrower positive result.  Its proof of
`exists_etaUnit_of_not_even` lifts an odd residue class using a natural-number representative.
`exists_displayedEtaLift_of_not_even` records that this *chosen lift* may be given an integral
display.  This does not say that an arbitrary unit already stored in `BranchData` is rational,
nor does it make `BranchData.DisplayFor` inhabited in general.
-/

namespace GQ2.Dyadic

/-! ## A displayed version of the arithmetic odd-residue lift -/

/-- A rationally displayed lift of an odd residue-class eta value. -/
structure DisplayedEtaLift (r : ℕ) (x : ZMod (2 ^ r)) where
  eta : ℤ_[2]ˣ
  display : NpcDisplayFor eta
  reduces : ((etaUnit r eta : (ZMod (2 ^ r))ˣ) : ZMod (2 ^ r)) = x

/-- The arithmetic lift used in branch classification can be chosen with an integral display.

This strengthens the construction underlying `exists_etaUnit_of_not_even`; it does not attach a
display to every possible lift of the same residue class. -/
theorem exists_displayedEtaLift_of_not_even {r : ℕ} {x : ZMod (2 ^ r)} (hx : ¬ Even x) :
    Nonempty (DisplayedEtaLift r x) := by
  haveI : NeZero (2 ^ r) := ⟨by positivity⟩
  obtain ⟨k, hk⟩ := ZMod.natCast_zmod_surjective x
  have hkodd : ¬ Even k := by
    rintro ⟨m, rfl⟩
    exact hx (hk ▸ ⟨(m : ZMod (2 ^ r)), by push_cast; ring⟩)
  have hunit : IsUnit ((k : ℤ_[2])) := by
    rw [PadicInt.isUnit_iff]
    rcases eq_or_lt_of_le (PadicInt.norm_le_one ((k : ℤ_[2]))) with h | h
    · exact h
    · refine absurd ?_ hkodd
      rw [PadicInt.norm_lt_one_iff_dvd] at h
      obtain ⟨c, hc⟩ := h
      have h0 : ((k : ℕ) : ZMod 2) = 0 := by
        have h2 := congrArg PadicInt.toZMod hc
        rwa [map_natCast, map_mul, map_natCast, ZMod.natCast_self, zero_mul] at h2
      exact ZMod.natCast_eq_zero_iff_even.1 h0
  have hkmodEq : (k : ℤ) % 2 = 1 := by
    exact_mod_cast (Nat.not_even_iff.mp hkodd)
  have hkmod : (k : ℤ) % 2 ≠ 0 := by omega
  have hinv : PadicInt.inv (1 : ℤ_[2]) = 1 := by
    simpa using PadicInt.mul_inv (z := (1 : ℤ_[2])) (norm_one : ‖(1 : ℤ_[2])‖ = 1)
  let eta : ℤ_[2]ˣ := hunit.unit
  let display : NpcDisplayFor eta :=
    { data := ⟨k, 1⟩
      num_odd := hkmod
      den_odd := by norm_num
      represents := by
        rw [EtaData.RepresentsUnit, EtaData.toPadic]
        simp only [Int.cast_natCast, Int.cast_one, hinv, mul_one]
        exact hunit.unit_spec.symm }
  exact ⟨⟨eta, display, by
    rw [etaUnit_coe, show (eta : ℤ_[2]) = (k : ℤ_[2]) from hunit.unit_spec,
      map_natCast, hk]⟩⟩

/-- The existing odd-value branch-classification lift can be chosen together with display data. -/
theorem exists_isEtaFor_with_display_of_not_even {C : Type*} [Group C]
    {d : CyclotomicFrobeniusDatum C} {u : C} (hx : ¬ Even (d.lambdaAdd u)) :
    ∃ eta : ℤ_[2]ˣ, ∃ _display : NpcDisplayFor eta, IsEtaFor d u eta := by
  let L := Classical.choice (exists_displayedEtaLift_of_not_even hx)
  exact ⟨L.eta, L.display, L.reduces.symm⟩

/-! ## The total semantic selector -/

/-- A total semantic selection: the handle count together with the arithmetic branch datum. -/
structure SemanticPresentation where
  handleCount : ℕ
  branch : BranchData

namespace SemanticPresentation

/-- Total selection from a branch datum; no finite display is required. -/
def ofBranch (h : ℕ) (B : BranchData) : SemanticPresentation := ⟨h, B⟩

/-- The generator degree of a semantic branch presentation. -/
def degree : SemanticPresentation → ℕ
  | ⟨h, .L⟩ => 2 * h + 1
  | ⟨h, .N0 _⟩ | ⟨h, .Npc _ _ _⟩ | ⟨h, .M0 _⟩ | ⟨h, .Mpc _ _ _ _⟩ => 2 + 2 * h

/-- The improved selected word, interpreted directly at an arbitrary branch unit. -/
noncomputable def word : (S : SemanticPresentation) → PWord (Generator S.degree)
  | ⟨h, .L⟩ => Words.LSq.lSqW h
  | ⟨h, .N0 alpha⟩ => Words.nCompactW alpha h
  | ⟨h, .Npc alpha r eta⟩ => Words.Npc.npcWUnit alpha r h eta
  | ⟨h, .M0 alpha⟩ => Words.MCompact.mCompactW alpha h
  | ⟨h, .Mpc alpha r epsilon eta⟩ => Words.Mpc.mpcWUnit alpha r (p epsilon r) eta h

/-- Cast a semantic word to a separately named, propositionally equal degree. -/
noncomputable def wordAt (S : SemanticPresentation) (n : ℕ) (hn : S.degree = n) :
    PWord (Generator n) := by
  subst n
  exact S.word

@[simp] theorem degree_ofBranch_L (h : ℕ) : (ofBranch h .L).degree = 2 * h + 1 := rfl

@[simp] theorem degree_ofBranch_N0 (alpha h : ℕ) :
    (ofBranch h (.N0 alpha)).degree = 2 + 2 * h := rfl

@[simp] theorem degree_ofBranch_Npc (alpha r h : ℕ) (eta : ℤ_[2]ˣ) :
    (ofBranch h (.Npc alpha r eta)).degree = 2 + 2 * h := rfl

@[simp] theorem degree_ofBranch_M0 (alpha h : ℕ) :
    (ofBranch h (.M0 alpha)).degree = 2 + 2 * h := rfl

@[simp] theorem degree_ofBranch_Mpc (alpha r h : ℕ) (epsilon : Bool) (eta : ℤ_[2]ˣ) :
    (ofBranch h (.Mpc alpha r epsilon eta)).degree = 2 + 2 * h := rfl

@[simp] theorem word_ofBranch_L (h : ℕ) :
    (ofBranch h .L).word = Words.LSq.lSqW h := rfl

@[simp] theorem word_ofBranch_N0 (alpha h : ℕ) :
    (ofBranch h (.N0 alpha)).word = Words.nCompactW alpha h := rfl

@[simp] theorem word_ofBranch_Npc (alpha r h : ℕ) (eta : ℤ_[2]ˣ) :
    (ofBranch h (.Npc alpha r eta)).word = Words.Npc.npcWUnit alpha r h eta := rfl

@[simp] theorem word_ofBranch_M0 (alpha h : ℕ) :
    (ofBranch h (.M0 alpha)).word = Words.MCompact.mCompactW alpha h := rfl

@[simp] theorem word_ofBranch_Mpc (alpha r h : ℕ) (epsilon : Bool) (eta : ℤ_[2]ˣ) :
    (ofBranch h (.Mpc alpha r epsilon eta)).word =
      Words.Mpc.mpcWUnit alpha r (p epsilon r) eta h := rfl

/-! ## Comparison with the displayed certificate selector -/

/-- Semantic and displayed selections always have the same generator degree. -/
theorem degree_eq_selected_ofBranch (h : ℕ) (B : BranchData) (d : B.DisplayFor) :
    (ofBranch h B).degree = (SelectedPresentation.ofBranch h B d).degree := by
  cases B <;> rfl

/-- On `Npc`, a compatible rational display identifies the semantic and selected syntax trees. -/
theorem word_eq_selected_ofBranch_Npc (alpha r h : ℕ) (eta : ℤ_[2]ˣ)
    (d : NpcDisplayFor eta) :
    (ofBranch h (.Npc alpha r eta)).word =
      (SelectedPresentation.ofBranch h (.Npc alpha r eta) d).word :=
  Words.Npc.npcWUnit_eq_display alpha r h d

/-- On `Mpc`, a compatible display identifies the corrected semantic and displayed
presentations, without falsely identifying `.one`/`.lit` syntax with `profPow` syntax. -/
theorem GammaR_eq_selected_ofBranch_Mpc (alpha r h q : ℕ) (epsilon : Bool)
    (eta : ℤ_[2]ˣ) (d : MpcDisplayFor eta) :
    GammaR (2 + 2 * h) q (ofBranch h (.Mpc alpha r epsilon eta)).word =
      GammaR (2 + 2 * h) q
        (SelectedPresentation.ofBranch h (.Mpc alpha r epsilon eta) d).word :=
  Words.Mpc.GammaR_mpcWUnit_eq_display alpha r (p epsilon r) h q d

/-- For every row, whenever certificate display data is supplied, the total semantic selector
defines the same corrected admissible-limit presentation as the displayed selector. -/
theorem GammaR_eq_selected_ofBranch (h q : ℕ) (B : BranchData) (d : B.DisplayFor) :
    GammaR (ofBranch h B).degree q (ofBranch h B).word =
      GammaR (SelectedPresentation.ofBranch h B d).degree q
        (SelectedPresentation.ofBranch h B d).word := by
  cases B with
  | L => rfl
  | N0 alpha => rfl
  | Npc alpha r eta =>
      change GammaR (2 + 2 * h) q (Words.Npc.npcWUnit alpha r h eta) =
        GammaR (2 + 2 * h) q (Words.Npc.npcW alpha r h d.data)
      rw [Words.Npc.npcWUnit_eq_display alpha r h d]
  | M0 alpha => rfl
  | Mpc alpha r epsilon eta =>
      exact GammaR_eq_selected_ofBranch_Mpc alpha r h q epsilon eta d

end SemanticPresentation

end GQ2.Dyadic

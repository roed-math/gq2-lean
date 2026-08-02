/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Words.L
import GQ2.Dyadic.Words.N0
import GQ2.Dyadic.Words.Npc
import GQ2.Dyadic.Words.M0
import GQ2.Dyadic.Words.Mpc

/-!
# The R5-selected dyadic presentation constructors

This file is the typed constructor table for the five rows frozen by
`general_2adic/artifacts/reports/selection-freeze.md`.  Consumers constructing the general
ramified-`i` presentation should select a value of `SelectedPresentation` and use its `word`;
they should not re-author a relator from the earlier paper displays.

| row | selected Lean constructor | excluded alternative |
|---|---|---|
| odd `L` | `Words.LSq.lSqW` | the collector `R_{L,K}` |
| compact `N` | `Words.nCompactW` | — |
| procyclic `N` | `Words.Npc.npcW` | the uncorrected word without `E_{r,eta}` |
| compact `M` | `Words.MCompact.mCompactW` | the forward `E`-block and any `r -> 0` interpolation |
| procyclic `M` | `Words.Mpc.mpcW` | the sign row and the retired field-specific relative-norm word |

The `Npc` and `Mpc` constructors retain their certificate display data.  This is deliberate:
`BranchData` carries an arbitrary 2-adic unit, while the hash-pinned trees carry a concrete
`EtaData`/`EtaDisplay`.  `GQ2.Dyadic.SelectedEta` supplies typed compatibility packages and
semantic arbitrary-unit words.  It proves literal equality for the `Npc` display, evaluation
equality for every compatible `Mpc` display, and literal equality for the genuine profinite
`.hat` display.  It deliberately does not identify evaluation equality with presentation
equivalence.
-/

namespace GQ2.Dyadic

/-- A fully displayed member of the R5-selected presentation family.

The handle count is stored in every constructor because it controls the generator alphabet.
For `Mpc`, the word exponent `p = epsilon * 2^(r-1)` is computed from the branch parameters and
is not accepted as an independent input. -/
inductive SelectedPresentation where
  | L (h : ℕ)
  | N0 (alpha h : ℕ)
  | Npc (alpha r h : ℕ) (eta : EtaData)
  | M0 (alpha h : ℕ)
  | Mpc (alpha r : ℕ) (epsilon : Bool) (eta : Words.Mpc.EtaDisplay) (h : ℕ)

namespace SelectedPresentation

/-- The degree/alphabet parameter belonging to a selected presentation row. -/
def degree : SelectedPresentation → ℕ
  | .L h => 2 * h + 1
  | .N0 _ h => 2 + 2 * h
  | .Npc _ _ h _ => 2 + 2 * h
  | .M0 _ h => 2 + 2 * h
  | .Mpc _ _ _ _ h => 2 + 2 * h

/-- The exact R5-selected word.  Every branch is definitionally one of the five frozen semantic
constructors; no retired or regression-only presentation occurs in this definition. -/
noncomputable def word : (S : SelectedPresentation) → PWord (Generator S.degree)
  | .L h => Words.LSq.lSqW h
  | .N0 alpha h => Words.nCompactW alpha h
  | .Npc alpha r h eta => Words.Npc.npcW alpha r h eta
  | .M0 alpha h => Words.MCompact.mCompactW alpha h
  | .Mpc alpha r epsilon eta h => Words.Mpc.mpcW alpha r (p epsilon r) eta h

/-- Cast a selected word to a separately named, propositionally equal degree. -/
noncomputable def wordAt (S : SelectedPresentation) (n : ℕ) (hn : S.degree = n) :
    PWord (Generator n) := by
  subst n
  exact S.word

@[simp] theorem word_L (h : ℕ) : (SelectedPresentation.L h).word = Words.LSq.lSqW h := rfl

@[simp] theorem word_N0 (alpha h : ℕ) :
    (SelectedPresentation.N0 alpha h).word = Words.nCompactW alpha h := rfl

@[simp] theorem word_Npc (alpha r h : ℕ) (eta : EtaData) :
    (SelectedPresentation.Npc alpha r h eta).word = Words.Npc.npcW alpha r h eta := rfl

@[simp] theorem word_M0 (alpha h : ℕ) :
    (SelectedPresentation.M0 alpha h).word = Words.MCompact.mCompactW alpha h := rfl

@[simp] theorem word_Mpc (alpha r : ℕ) (epsilon : Bool) (eta : Words.Mpc.EtaDisplay) (h : ℕ) :
    (SelectedPresentation.Mpc alpha r epsilon eta h).word =
      Words.Mpc.mpcW alpha r (p epsilon r) eta h := rfl

end SelectedPresentation

end GQ2.Dyadic

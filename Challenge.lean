/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.GammaA
import GQ2.Foundations.Axioms

/-!
# Comparator challenge: Theorem 1.2 (the presentation theorem)

Challenge file for [leanprover/comparator](https://github.com/leanprover/comparator),
paired with `Solution.lean` and `comparator-config.json`.

States the paper's main theorem — the absolute Galois group `G_{ℚ₂}` is isomorphic as a
profinite group to the marked quotient `Γ_A` — with a `sorry`.  The imports provide only
what is needed to *state* the theorem (`GQ2.GammaA`, `GQ2.AbsGalQ2`); the proof lives in
the library (`GQ2.main_presentation_literal`, `GQ2/PresentationLiteral.lean`) and is
re-attached in `Solution.lean`.

Permitted axioms for the solution: the std-3 (`propext`, `Classical.choice`,
`Quot.sound`) plus the project's frozen census of 9 literature axioms declared in
`GQ2/Foundations/Axioms.lean` (enforced by `scripts/check_axioms.sh`).
-/

open GQ2 in
/-- **Theorem 1.2 (presentation theorem), literal form.**  `Γ_A` — the marked quotient
profinite group of paper eq. (7) — is isomorphic, as a topological group, to the absolute
Galois group of `ℚ₂`. -/
theorem challenge_main_presentation_literal
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] :
    Nonempty (ContinuousMulEquiv GammaA AbsGalQ2) := sorry

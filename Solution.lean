/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.PresentationLiteral
import GQ2.Roe.Main

/-!
# Comparator solution: Theorem 1.2 (the presentation theorem) and its `Γ_R` replacement

Solution file for [leanprover/comparator](https://github.com/leanprover/comparator),
paired with `Challenge.lean` and `comparator-config.json`.  Restates each of the two
challenge statements verbatim and attaches the library proof: `GQ2.main_presentation_literal`
(`GQ2/PresentationLiteral.lean`) and `GQ2.main_presentation_literal_roe_unconditional`
(`GQ2/Roe/Main.lean`).

The second proof term is the campaign's terminal corollary
`main_presentation_literal_roe bLab` — the hypothesis-parametrized Replacement theorem with
its one input discharged by `GQ2.Roe.Labute.bLab`.  Both theorems print the same axioms
(std-3 plus the nine literature axioms of `comparator-config.json`), which
`scripts/check_axioms.sh` check 5 and `GQ2/AxiomLedger.lean`'s terminal certificate both
enforce against the library declarations cited here.
-/

open GQ2 in
/-- **Theorem 1.2 (presentation theorem), literal form.**  `Γ_A` — the marked quotient
profinite group of paper eq. (7) — is isomorphic, as a topological group, to the absolute
Galois group of `ℚ₂`. -/
theorem challenge_main_presentation_literal
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] :
    Nonempty (ContinuousMulEquiv GammaA AbsGalQ2) :=
  GQ2.main_presentation_literal

open GQ2 in
/-- **The Replacement theorem, literal form, unconditional.**  `Γ_R` — the Roe candidate
marked quotient — is isomorphic, as a topological group, to the absolute Galois group of `ℚ₂`.
No hypotheses and no instance binders: the Labute-classification instance `BLabHypothesis`
this statement was once conditional on is now the in-repo theorem `GQ2.Roe.Labute.bLab`. -/
theorem challenge_main_presentation_literal_roe_unconditional :
    Nonempty (ContinuousMulEquiv GammaR AbsGalQ2) :=
  GQ2.main_presentation_literal_roe_unconditional

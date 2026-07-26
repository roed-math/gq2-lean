/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.GammaA
import GQ2.Roe.GammaR
import GQ2.Roe.MarkedPro2
import GQ2.Foundations.Axioms

/-!
# Comparator challenge: Theorem 1.2 (the presentation theorem) and its `Γ_R` replacement

Challenge file for [leanprover/comparator](https://github.com/leanprover/comparator),
paired with `Solution.lean` and `comparator-config.json`.

States, each with a `sorry`:

* the paper's main theorem — the absolute Galois group `G_{ℚ₂}` is isomorphic as a
  profinite group to the marked quotient `Γ_A`;
* the **Replacement theorem** — the same statement for the Roe candidate `Γ_R`, granted the
  Labute-classification hypothesis `BLabHypothesis`.

The imports provide only what is needed to *state* the two theorems (`GQ2.GammaA`,
`GQ2.Roe.GammaR`, `GQ2.Roe.MarkedPro2` for `BLabHypothesis`, and `GQ2.AbsGalQ2`); the proofs
live in the library (`GQ2.main_presentation_literal`, `GQ2/PresentationLiteral.lean`, and
`GQ2.main_presentation_literal_roe`, `GQ2/Roe/Main.lean`) and are re-attached in
`Solution.lean`.  Neither statement's import closure reaches `GQ2/Roe/Labute/`, where the
L-campaign's in-flight proof of `BLabHypothesis` lives.

Permitted axioms for the solution: the std-3 (`propext`, `Classical.choice`,
`Quot.sound`) plus the project's frozen census of 9 literature axioms declared in
`GQ2/Foundations/Axioms.lean` (enforced by `scripts/check_axioms.sh`).  The list is shared by
both theorems — `main_presentation_literal_roe` prints exactly the axioms of
`main_presentation_literal`, since `BLabHypothesis` is a hypothesis binder and not an axiom.

Conjugation convention: `Γ_R`'s words follow the paper's `conjP x g = g⁻¹ x g`, as `Γ_A`'s do.
The q2 archive that independently pins the `Γ_R` marking counts writes `g^h = h g h⁻¹`; the two
are reconciled by the bijection `σ ↦ σ⁻¹` (see `GQ2/Roe/Sanity.lean` and `GQ2/Roe/Main.lean`).
`comparator-config.json` itself is strict JSON and cannot carry this note.
-/

open GQ2 in
/-- **Theorem 1.2 (presentation theorem), literal form.**  `Γ_A` — the marked quotient
profinite group of paper eq. (7) — is isomorphic, as a topological group, to the absolute
Galois group of `ℚ₂`. -/
theorem challenge_main_presentation_literal
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] :
    Nonempty (ContinuousMulEquiv GammaA AbsGalQ2) := sorry

open GQ2 in
/-- **The Replacement theorem, literal form.**  `Γ_R` — the Roe candidate marked quotient — is
isomorphic, as a topological group, to the absolute Galois group of `ℚ₂`, granted the single
Labute-classification instance `BLabHypothesis`.  That hypothesis is an explicit binder, **not**
an axiom: discharging it is the L-campaign's job, and until it lands this theorem is conditional
while the `Γ_A` statement above is not. -/
theorem challenge_main_presentation_literal_roe (hBLab : BLabHypothesis) :
    Nonempty (ContinuousMulEquiv GammaR AbsGalQ2) := sorry

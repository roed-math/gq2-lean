/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.GammaA
import GQ2.Roe.GammaR

/-!
# Comparator challenge: Theorem 1.2 (the presentation theorem) and its `Γ_R` replacement

Challenge file for [leanprover/comparator](https://github.com/leanprover/comparator),
paired with `Solution.lean` and `comparator-config.json`.

States, each with a `sorry`:

* the paper's main theorem — the absolute Galois group `G_{ℚ₂}` is isomorphic as a
  profinite group to the marked quotient `Γ_A`;
* the **Replacement theorem** — the same statement for the Roe candidate `Γ_R`,
  **unconditionally**: no hypothesis binder, nothing granted.

Between 2026-07-25 and 2026-07-26 the second challenge carried an explicit
`(hBLab : BLabHypothesis)` binder — the Labute classification instance, deliberately not
admitted as an axiom — so a passing Comparator run then certified only the *conditional*
statement.  The L-campaign discharged that hypothesis as the theorem `GQ2.Roe.Labute.bLab`
(`GQ2/Roe/Labute/Assembly.lean`, standard three axioms), so the challenge below is the
hypothesis-free form and `GQ2.Roe.MarkedPro2` — imported only for `BLabHypothesis` — is no
longer needed to state it.

The imports provide only what is needed to *state* the two theorems: `GQ2.GammaA` and
`GQ2.Roe.GammaR` for the two candidate groups (`GQ2.Statement`'s `AbsGalQ2` arrives through
`GQ2.GammaA`'s public imports).  In particular `GQ2/Foundations/Axioms.lean` is **not**
imported: the nine literature axioms belong to the permitted *solution* trust base listed
below, not to the challenge statements, whose import closure is axiom-free vocabulary.  The
proofs live in the library (`GQ2.main_presentation_literal`, `GQ2/PresentationLiteral.lean`,
and `GQ2.main_presentation_literal_roe_unconditional`, `GQ2/Roe/Main.lean`) and are
re-attached in `Solution.lean`.  No `GQ2/Roe/Labute/` module is in either challenge statement's import
closure; the *solution*'s closure now reaches nine of them, since that is where the discharged
hypothesis is proved — sorry-free, like the rest of the library (`scripts/check_axioms.sh`
checks 2 and 5).

Permitted axioms for the solution: the std-3 (`propext`, `Classical.choice`,
`Quot.sound`) plus the project's frozen census of 9 literature axioms declared in
`GQ2/Foundations/Axioms.lean` (enforced by `scripts/check_axioms.sh`).  The list is shared by
both theorems — `main_presentation_literal_roe_unconditional` prints exactly the axioms of
`main_presentation_literal`, so *proving* the Labute instance rather than assuming it widened
the trust base by nothing at all.

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
/-- **The Replacement theorem, literal form, unconditional.**  `Γ_R` — the Roe candidate
marked quotient — is isomorphic, as a topological group, to the absolute Galois group of `ℚ₂`.
No hypotheses and no instance binders: the Labute-classification instance `BLabHypothesis`
this statement was once conditional on is now the in-repo theorem `GQ2.Roe.Labute.bLab`. -/
theorem challenge_main_presentation_literal_roe_unconditional :
    Nonempty (ContinuousMulEquiv GammaR AbsGalQ2) := sorry

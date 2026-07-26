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
paired with `Challenge.lean` and `comparator-config.json`.  Restates each challenge
theorem verbatim and attaches the library proof: `GQ2.main_presentation_literal`
(`GQ2/PresentationLiteral.lean`) and `GQ2.main_presentation_literal_roe`
(`GQ2/Roe/Main.lean`), the latter applied to the challenge's own `BLabHypothesis` binder.
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
/-- **The Replacement theorem, literal form.**  `Γ_R` — the Roe candidate marked quotient — is
isomorphic, as a topological group, to the absolute Galois group of `ℚ₂`, granted the single
Labute-classification instance `BLabHypothesis`.  That hypothesis is an explicit binder, **not**
an axiom: discharging it is the L-campaign's job, and until it lands this theorem is conditional
while the `Γ_A` statement above is not. -/
theorem challenge_main_presentation_literal_roe (hBLab : BLabHypothesis) :
    Nonempty (ContinuousMulEquiv GammaR AbsGalQ2) :=
  GQ2.main_presentation_literal_roe hBLab

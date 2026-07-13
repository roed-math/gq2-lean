import GQ2.PresentationLiteral

/-!
# Comparator solution: Theorem 1.2 (the presentation theorem)

Solution file for [leanprover/comparator](https://github.com/leanprover/comparator),
paired with `Challenge.lean` and `comparator-config.json`.  Restates the challenge
theorem verbatim and attaches the library proof `GQ2.main_presentation_literal`
(`GQ2/PresentationLiteral.lean`).
-/

open GQ2 in
/-- **Theorem 1.2 (presentation theorem), literal form.**  `Γ_A` — the marked quotient
profinite group of paper eq. (7) — is isomorphic, as a topological group, to the absolute
Galois group of `ℚ₂`. -/
theorem challenge_main_presentation_literal
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] :
    Nonempty (ContinuousMulEquiv GammaA AbsGalQ2) :=
  GQ2.main_presentation_literal

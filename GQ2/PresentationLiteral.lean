import GQ2.GammaA
import GQ2.SectionTenSources
import GQ2.Prop23
import GQ2.FinitelyGenerated

/-!
# Theorem 1.2, literal presentation form  (P-19)

`main_presentation_literal : Nonempty (ContinuousMulEquiv GammaA AbsGalQ2)` — the literal
Theorem 1.2 — as the instantiation of `Statement.main_presentation` at the honest candidate `Γ_A`
(`GQ2/GammaA.lean`, paper eq. (7)).

**Why here, not in `GammaA.lean`.**  The proof supplies `main_presentation`'s two count hypotheses:
`hΓA := prop_2_3` (Prop. 2.3, `Nat.card (ContSurj Γ_A G) = admissibleCount G`) and
`hcount := SectionTen.main_surjection_count'` (Theorem 1.2's surjection count for `G_{ℚ₂}`,
eq. (154) + Prop. 2.3).  `Prop23` and `SectionTenSources` sit **downstream** of the upstream
`GammaA.lean`, so an in-place proof would cycle — the statement-move pattern (P-08/P-15d/P-18e);
`GammaA.lean` carries a comment-pointer here.

**Axioms.**  Std-3 + `sorryAx` (through the allowlisted `SectionNine.thm_4_2` until P-17i) + the
tower's Track-B literature axioms (via `main_surjection_count'` / the boundary construction) + B1
(topological finite generation of `G_{ℚ₂}`).  No new axiom, no `sorry` token in this file.
-/

namespace GQ2

/-- **Theorem 1.2 (literal presentation form)**: the honest candidate `Γ_A` is continuously
isomorphic to `G_{ℚ₂}`.  Instantiates `main_presentation` at `Γ_A`: `hΓA := prop_2_3` (the `Γ_A`
admissible-marking count), `hcount := SectionTen.main_surjection_count'` (the `G_{ℚ₂}` surjection
count), and the topological finite-generation witnesses of `Γ_A` and `G_{ℚ₂}`. -/
theorem main_presentation_literal
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] :
    Nonempty (ContinuousMulEquiv GammaA AbsGalQ2) :=
  main_presentation GammaA
    gammaA_topologicallyFinitelyGenerated
    Foundations.absGalQ2_isTopologicallyFinitelyGenerated
    prop_2_3
    (fun G => SectionTen.main_surjection_count' G)

end GQ2

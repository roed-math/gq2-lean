import GQ2.Foundations.Axioms

/-!
# Classical foundations — moved  (T-19)

The literature axioms (B1, B2, B5, B7, B7′) now live in **`GQ2/Foundations/Axioms.lean`** —
the single file allowed to contain `axiom` declarations (enforced by
`scripts/check_axioms.sh`).  This module remains as a re-export so `import GQ2.Foundations`
keeps working; all names are unchanged (`GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated`,
`GQ2.Foundations.cyclotomicCharacter_two_surjective`, …).
-/

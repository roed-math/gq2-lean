/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Foundations.Axioms

/-!
# Classical foundations

The literature axioms (B1, B5, B7, B7′, …) now live in **`GQ2/Foundations/Axioms.lean`** —
the single file allowed to contain `axiom` declarations (enforced by
`scripts/check_axioms.sh`).  This module remains as a re-export so `import GQ2.Foundations`
keeps working; all names are unchanged
(`GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated`, …).
-/

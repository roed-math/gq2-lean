/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Foundations.Interfaces

/-!
# Classical foundations

The literature axioms (B1, B3c, B5, B6, B7, B8, B9, B10, B11a) live in
**`GQ2/Foundations/Axioms.lean`** — the single file allowed to contain `axiom` declarations
(enforced by `scripts/check_axioms.sh`), and since 2026-07-27 containing the nine axioms and
nothing else.  The derived same-name interfaces over them (B7′, B11b, B12, B13, the derived
B9 form `evensKahn_dyadic`, the B6 base member `tateDuality`, and the
`HasEqualNormValueGroups` convention) are in **`GQ2/Foundations/Interfaces.lean`**, which
re-exports the axioms.  This module remains as a re-export of both so
`import GQ2.Foundations` keeps working; all names are unchanged
(`GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated`, …).
-/

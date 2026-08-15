/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Foundations.Interfaces

/-!
# Classical foundations

The literature axioms (B1, B3c, B5, B5-K, B6, B7, B8, B9, B10, B10-K, B11a) live in
**`GQ2/Foundations/Axioms.lean`** — the single file allowed to contain `axiom` declarations
(enforced by `scripts/check_axioms.sh`), and since 2026-07-27 containing the census and
nothing else.

[W75-HOUSE, watch round 11 §4.5, second site found by grepping that fix.  The list above
omitted B5-K `markedRecipAt` and B10-K `orientedTameQuotientAt`, and the sentence said "the
nine axioms", against the eleven `axiom` declarations in `GQ2/Foundations/Axioms.lean`,
`GQ2/AxiomLedger.lean`'s eleven `bAxioms` entries and `scripts/check_axioms.sh:28`'s
`EXPECTED_AXIOMS=11`.  Both were stale at the AX3/AX4 census flips of 2026-07-29.  The
"since 2026-07-27" date is about the file's contents, not the count, and stands.
Comment-only.]  The derived same-name interfaces over them (B7′, B11b, B12, B13, the derived
B9 form `evensKahn_dyadic`, the B6 base member `tateDuality`, and the
`HasEqualNormValueGroups` convention) are in **`GQ2/Foundations/Interfaces.lean`**, which
re-exports the axioms.  This module remains as a re-export of both so
`import GQ2.Foundations` keeps working; all names are unchanged
(`GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated`, …).
-/

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Foundations.Interfaces
import GQ2.Foundations.TauCetiInstance

/-!
# Classical foundations

The nine literature inputs (B1, B3c, B5, B6, B7, B8, B9, B10, B11a) were `axiom` declarations in
`GQ2/Foundations/Axioms.lean` until 2026-10-17; since the Tau Ceti discharge (ticket C2) the
library contains no `axiom` at all.  The nine legacy names are now theorems/definitions proved from
Tau Ceti in **`GQ2/Foundations/TauCetiInstance.lean`**, with their statements unchanged, and that
file provides the `LiteratureInputs` instance (`tauCetiLiteratureInputs`).  The derived same-name
interfaces (B7′, B11b, B12, B13, the derived B9 form `evensKahn_dyadic`, the B6 base member
`tateDuality`, and the `HasEqualNormValueGroups` convention) are in
**`GQ2/Foundations/Interfaces.lean`**.  This module re-exports both, so `import GQ2.Foundations`
keeps working; all names are unchanged
(`GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated`, …).
-/

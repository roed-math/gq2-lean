/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe
-/
import GQ2.Dyadic.SqCore.GradedRowMove

/-!
# The graded row-move ladder at class `k ≥ 4` (W86-LADDER4)

Wave 85 (`GradedRowMove.lean`) reduced the row-move pair, hence the clearing
`SqNuOrientedClearAtUnitPivot h` and through it the odd-degree classification, to the rungs
`(gRowSet h A B k).Nonempty` for `k ≥ 4` on the unit locus `IsUnit (A - c0 h B)`. Rungs
`k ≤ 3` are proved there: `k ≤ 2` free for every frame, `k = 3` free with the bare frame
(the defect `[x0, w^B] · [w^B, σ]` dies by parity).

This module extends the ladder. Contents are recorded incrementally; the acceptance target is
`gLad_clearing (h) : SqNuOrientedClearAtUnitPivot h` with the full composition into the
odd-degree classification, or the sharpest per-rung record with the first obstruction in
closed form.

All declarations carry `#print axioms` pins recorded in comments at the end of the file.
-/

open Multiplicative

namespace GQ2

open Roe Roe.Labute

namespace Dyadic

namespace SqCore

open MarkedCore
open scoped commutatorElement

end SqCore

end Dyadic

end GQ2

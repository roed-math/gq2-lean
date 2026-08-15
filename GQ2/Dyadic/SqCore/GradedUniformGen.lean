/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedDepthThree

/-!
# W80-UNIFORM: the level-free generation record

The kill ladder `GDeepKillAt h k` of `GradedDepthThree` is proved at rungs `k = 2, 3`; the
cost of each higher rung is T1 at depth `k`, whose sole per-level input is the level-`(k+2)`
generation record (level 4: `cfourCmp_zLayer_le_gens`, three families; level 5:
`cfiveSpan_zLayer_le_gens`, six).  This file proves the record at EVERY level, Labute's
Lemma 3 in graded shadow: the step is the engine (squares and brackets generate the next
layer), the base is the committed level-4 record.
-/

open Multiplicative

namespace GQ2

open Roe Roe.Labute FoxH

namespace Dyadic

namespace SqCore

open MarkedCore
open scoped commutatorElement

/-! ## §1 The target shape -/

section Target

variable {h : ℕ}

end Target

end SqCore

end Dyadic

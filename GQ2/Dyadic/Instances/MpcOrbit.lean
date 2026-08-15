/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.MpcPivot

/-!
# W83-ORBIT: the `M6` orbit question on `D_M 2 0`

Wave 82 reduced the `ℚ₂(√−10)` row to one abstract move on `D_M 2 0`, `MpcPivShift 2`, MC1
§5.3's family `M6` at parameter one (`Y_c : C̄₀ ↦ B̄^{2c₁}·C̄₀`).  This module decides it.

Declaration prefix `mpcOrb` (namespace `GQ2.Dyadic.Instances.MpcOrb`).  No `sorry`, no new
axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.
-/

namespace GQ2.Dyadic.Instances.MpcOrb

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcPiv

noncomputable section

end

end GQ2.Dyadic.Instances.MpcOrb

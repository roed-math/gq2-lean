/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.MpcFive

/-!
# W88-SIX: the `M6` word at class six, and the uniform shape of a kill

Wave 87 (`GQ2/Dyadic/Instances/MpcFive.lean`) climbed the class-five rung of the `M6` ansatz,
so the residue of `MpcPivShift 2` starts at class six.  This module is the class-six lane.

Declaration prefix `mpcSx` (namespace `GQ2.Dyadic.Instances.MpcSx`).  No `sorry`, no new axiom,
no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.
-/

namespace GQ2.Dyadic.Instances.MpcSx

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcPiv GQ2.Dyadic.Instances.MpcOrb GQ2.Dyadic.Instances.MpcWord
open GQ2.Dyadic.Instances.MpcBld GQ2.Dyadic.Instances.MpcLad GQ2.Dyadic.Instances.MpcFv
open GQ2.Roe.Labute GQ2.Dyadic.SqCore

noncomputable section

end

end GQ2.Dyadic.Instances.MpcSx

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedUniformJoin
import GQ2.Dyadic.SqCore.GradedBaseDecide

/-!
# W78-ABSORB: the leftover normal form and Labute's Theorem 5 absorption

Wave 77 refuted the depth-2 base (`GBaseResidual h`, `GJoinBase h`) at every `h`: the
images of `⁅x₁,σ⁆²` and `⁅x₁,x₀⁆²` are unreachable from the tower side.  Labute's own
proof survives this because his successive approximation never needs full layer
generation: at each level the leftover decomposes as a knob image times coker classes
with `𝔽₂`-coefficients, and in the character-pinned regime (his Theorem 5) those
coefficients are killed by the Δ-functional constraint rather than absorbed.

This file formalizes that mechanism.  Contents to be built in this lane:

* the leftover normal form at depth 2 (T1);
* the coefficient-killing constraint for the supply's actual defects (T2);
* the re-seeded clearing recursion (T3).
-/

open Multiplicative

namespace GQ2

open Roe Roe.Labute FoxH

namespace Dyadic

namespace SqCore

open MarkedCore
open scoped commutatorElement

end SqCore

end Dyadic

end GQ2

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe
-/
import GQ2.Dyadic.Instances.OddSeam

/-!
# W83-FRAME: the cup-adapted frame at odd degree

Lane module for W83-FRAME. Target: the odd classification's last input, one
cup-adapted Frattini frame per odd-degree field, in the form the wave-82 seam
calculus made exact. By `oddSeam_supply_iff_cupAdaptedFrame` the seam
`SqMarkedForwardSupply B h` is equivalent to one cup-adapted frame killing the
improved relator and carrying the two nu-rows, and the rows reduce to their
mod-2 shadows.

T1: the mod-2 cup structure on the odd-degree field's H^1 (dimension, shape of
the form under ramified-i, normal form). T2: the frame, or the smallest named
arithmetic Prop it still costs. T3: `oddFrame_supply` into the wave-82 chain.

All declarations carry `#print axioms` output recorded in comments.
-/

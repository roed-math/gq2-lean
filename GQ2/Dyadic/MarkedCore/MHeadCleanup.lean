/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.MarkedCore.Cores
import GQ2.Dyadic.MarkedCore.FreeProTwoCharacterCorrection
import GQ2.Roe.Labute.AdditiveCharacters

/-!
# The coupled ordinary head row of an actual M-relator correction

The full, arbitrary-rank `M_alpha` word has ordinary row
`2 f(x0) + 2^alpha f(x2)`: unlike the `N` word it is **coupled**, carrying the
`C` column as well as the `A` column. This module extracts the head digit from
that coupled row without setting the `C` row to zero and without any
orientation or vanishing-`C` premise.

Every declaration here carries the lane prefix `mHead`. That prefix is a naming
reservation for this module; it is not a claim about the peripheral head word
`GQ2.Dyadic.MarkedCore.mHead` of `Cores`, which is a different object.

Nothing here constructs the corrections, asserts a derivative image, or
preserves a relator equation after replacement.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative Roe.Labute

end
end GQ2.Dyadic.MarkedCore

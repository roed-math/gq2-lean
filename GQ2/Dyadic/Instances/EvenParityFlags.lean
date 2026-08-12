/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.Instances.EvenParityKummer

/-!
# W68-FLAGS: the even parity supply at even degree, without the positivity binder

## What this file is

One theorem.  `EvenParityKummer.evenParity_paritySupply_evenDegree` states the even
twisted-cocycle parity supply in the handle count `(n - 2) / 2` the campaign uses at the
endpoint, and carries `2 ≤ [K : ℚ₂]` as an EXPLICIT hypothesis alongside the degree parity.
Wave 67's house round flagged that binder as redundant, and it is: `[K : ℚ₂]` is positive for
free from `Module.finrank_pos` under the ambient `[FiniteDimensional ℚ_[2] K]`, and a positive
even natural number is at least `2`.  So the hypothesis is derivable from the other binders and
buys nothing.

`evenParityF_paritySupply_evenDegree'` is that statement with the binder discharged
internally: the degree parity alone, at every level `k ≥ 3`, for every stage tuple of every
even word datum.  It is the form matching
`EvenParityModel.parityFinal_evenClassification_evenDegree`, which already takes its positivity
from `Module.finrank_pos` and so carries the degree parity alone; the two now agree on what an
even-degree hypothesis is.

## What it does NOT do

⚠ Nothing mathematical.  The proof is the original applied to a discharged binder, so the
content, the axiom print and the reach are exactly the original's.  This is a signature
convenience, not a strengthening: `Even n` plus `0 < n` is `2 ≤ n`, and the original was never
weaker than it looked.

⚠ The original `evenParity_paritySupply_evenDegree` is UNCHANGED and stays.  Its signature is
committed and pinned in `EvenParityKummer.lean`, its consumers keep it, and this file adds a
form beside it rather than replacing it.  Callers that already have `2 ≤ [K : ℚ₂]` in hand
should keep using the original.

## Naming

The `evenParityF` prefix marks this lane's additions inside the shared
`GQ2.Dyadic.EvenParity` namespace, so nothing here can collide with the `evenParity_` family
of `EvenParityKummer.lean`.  The prime marks the binder-free form in the usual way.
-/

namespace GQ2.Dyadic.EvenParity

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.FoxH
open ContCoh
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.EvenFamily
open GQ2.Dyadic.LSquare

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-! ## The binder-free form -/

omit [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- **`2 ≤ [K : ℚ₂]` is redundant given `Even [K : ℚ₂]`.**  The degree is positive under the
ambient finite-dimensionality (`Module.finrank_pos`), and a positive even natural number is at
least `2`.  Kept as a named step so the discharge is visible at the one place it happens. -/
theorem evenParityF_two_le_finrank_of_even
    (heven : Even (Module.finrank ℚ_[2] K)) : 2 ≤ Module.finrank ℚ_[2] K := by
  have hpos : 0 < Module.finrank ℚ_[2] K := Module.finrank_pos
  obtain ⟨m, hm⟩ := heven
  omega

omit [T2Space (GalK K)] in
/-- **THE PARITY SUPPLY AT EVEN DEGREE, ON THE DEGREE PARITY ALONE.**  Exactly
`evenParity_paritySupply_evenDegree` with its `2 ≤ [K : ℚ₂]` binder discharged internally: for
`Even [K : ℚ₂]`, every stage tuple of every even word datum at every level `k ≥ 3` has the
supply, in the handle count `([K : ℚ₂] - 2) / 2` the campaign uses at the endpoint.

⚠ Same content, same reach, same print as the original, which is unchanged and stays for the
callers that already carry the positivity.  The only difference is the binder. -/
theorem evenParityF_paritySupply_evenDegree'
    (heven : Even (Module.finrank ℚ_[2] K)) {k : ℕ} (hk : 3 ≤ k)
    {W : StageWord (MarkedCore.coreRank ((Module.finrank ℚ_[2] K - 2) / 2))}
    {v : Fin (MarkedCore.coreRank ((Module.finrank ℚ_[2] K - 2) / 2)) → ℤ_[2]ˣ}
    (T : Tuple W v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k) :
    EvenFamParitySupply T :=
  evenParity_paritySupply_evenDegree (evenParityF_two_le_finrank_of_even heven) heven hk T

end

/-! ## Axiom pins

Printed beside the original whose binder this file drops: the binder-free form must not exceed
what the original already carries. -/

section AxiomPins

#print axioms evenParityF_two_le_finrank_of_even
#print axioms evenParityF_paritySupply_evenDegree'

-- the original, for the side-by-side
#print axioms evenParity_paritySupply_evenDegree

end AxiomPins

end GQ2.Dyadic.EvenParity

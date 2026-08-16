/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/

import GQ2.Dyadic.Instances.MpcInitialRelatorTower

/-!
# Preservation of the marked-cost range under squaring

Combines the square-tower identity with an existing range witness. No exactness or
absorption statement is assumed.
-/

namespace GQ2.Dyadic.Instances.MpcMk

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcWord GQ2.Dyadic.Instances.MpcBld
open GQ2.Dyadic.Instances.MpcLad GQ2.Dyadic.Instances.MpcSx
open GQ2.Roe.Labute GQ2.Dyadic.SqCore

noncomputable section

theorem mpcMkRawCost_markedSquare_eq {r : Nat} (hr : 2 ≤ r)
    (hr1 : 2 ≤ r + 1)
    (u : MpcMkRawSource r)
    (v : MpcMkCostDomain r)
    (hv : mpcMkCost r hr 1 1 v = mpcMkRawCost r hr 1 1 u) :
    mpcMkCost (r + 1) hr1 1 1 (mpcMkMarkedSquare v) =
      mpcMkRawCost (r + 1) hr1 1 1 (mpcMkRawSquare u) := by
  apply Subtype.ext
  have hxy : levelMk (DM 2 0 : Type) (r + 2)
      (mpcBldIncr 1 1 u.1 u.2.1 u.2.2.1 u.2.2.2) =
      levelMk (DM 2 0 : Type) (r + 2)
        (mpcBldIncr 1 1 v.1 v.2.1 v.2.2.1 v.2.2.2) := by
    have he := congrArg Subtype.val hv
    rw [mpcMkRawCost_apply] at he
    exact he.symm
  have hsquare := mpcMk_level_square_congr hr
    (mpcMk_incr_mem_succ u.1.2 u.2.1.2 u.2.2.1.2 u.2.2.2.2)
    (mpcMk_incr_mem_succ v.1.2.2 v.2.1.2.2 v.2.2.1.2.2 v.2.2.2.2.2)
    hxy
  rw [mpcMkRawCost_apply]
  change levelMk (DM 2 0 : Type) (r + 3)
      (mpcBldIncr 1 1 (v.1 ^ 2) (v.2.1 ^ 2) (v.2.2.1 ^ 2) (v.2.2.2 ^ 2)) =
    levelMk (DM 2 0 : Type) (r + 3)
      (mpcBldIncr 1 1 (u.1 ^ 2) (u.2.1 ^ 2) (u.2.2.1 ^ 2) (u.2.2.2 ^ 2))
  symm
  calc
    _ = levelMk (DM 2 0 : Type) (r + 3)
        ((mpcBldIncr 1 1 u.1 u.2.1 u.2.2.1 u.2.2.2) ^ 2) :=
      mpcMk_incr_square hr u.1.2 u.2.1.2 u.2.2.1.2 u.2.2.2.2
    _ = levelMk (DM 2 0 : Type) (r + 3)
        ((mpcBldIncr 1 1 v.1 v.2.1 v.2.2.1 v.2.2.2) ^ 2) := hsquare
    _ = _ := (mpcMk_incr_square hr
      v.1.2.2 v.2.1.2.2 v.2.2.1.2.2 v.2.2.2.2.2).symm

theorem mpcMkRawCost_square_mem_of_mem {r : Nat} (hr : 2 ≤ r)
    (hr1 : 2 ≤ r + 1)
    (u : MpcMkRawSource r)
    (h : mpcMkRawCost r hr 1 1 u ∈
      MonoidHom.range (mpcMkCost r hr 1 1)) :
    mpcMkRawCost (r + 1) hr1 1 1 (mpcMkRawSquare u) ∈
      MonoidHom.range (mpcMkCost (r + 1) hr1 1 1) := by
  obtain ⟨v, hv⟩ := h
  exact ⟨mpcMkMarkedSquare v, mpcMkRawCost_markedSquare_eq hr hr1 u v hv⟩

#print axioms mpcMkRawCost_markedSquare_eq
#print axioms mpcMkRawCost_square_mem_of_mem

end
end GQ2.Dyadic.Instances.MpcMk

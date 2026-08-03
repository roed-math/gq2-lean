/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Count.ProTwo
import GQ2.Dyadic.SelectedEta

/-!
# The arbitrary-unit, arbitrary-handle procyclic-M core dictionary

This file supplies the forward half of the general procyclic-`M` presentation dictionary.  For
an alphabet marking `t`, first use the compact-`N` indexing

`(x0, x1, sigma, x2, handles)`

and then apply the triangular change of variables

`(A, B, C0, D) = (x0^-1 C0^-m, x1 sigma^p, x2 sigma^s, sigma^etaHat)`.

The handles are untouched.  The final theorem identifies the pro-`2` value of the semantic
word `mpcWUnit alpha r p eta h` with the defining `D_M` relator on that vector.  It is uniform
in the unit and in the handle count and does not replace the parameter `p` by a specialized
formula.

The inverse dictionary is deliberately not bundled as a `Count.CoreReindex`: its `ofCore` field
would have to recover `sigma` from `sigma^etaHat` in every profinite target.  The current library
has the needed inverse-unit theorem for `Z_2`-powering on pro-`2` groups
(`zpowZtwo_bijective`), but not the corresponding arbitrary-profinite `etaHatZ` theorem.
-/

namespace GQ2.Dyadic.Instances.MProcyclicCore

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Count.PilotN

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- The triangular procyclic-`M` change of core coordinates, for an arbitrary semantic unit.
The input vector is in compact-`N` order `(x0,x1,sigma,x2,handles)`; the output vector is in
`D_M` order `(A,B,C0,D,handles)`. -/
noncomputable def mpcUnitTwist (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (c : Fin (coreRank h) → G) : Fin (coreRank h) → G :=
  fun i ↦ if (i : ℕ) = 0 then
      (c 0)⁻¹ * ((c 3 * c 2 ^ s r) ^ m alpha)⁻¹
    else if (i : ℕ) = 1 then c 1 * c 2 ^ p
    else if (i : ℕ) = 2 then c 3 * c 2 ^ s r
    else if (i : ℕ) = 3 then c 2 ^ᶻ etaHatZ (eta : ℤ_[2])
    else c i

@[simp] theorem mpcUnitTwist_zero (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (c : Fin (coreRank h) → G) :
    mpcUnitTwist alpha r p eta h c 0 =
      (c 0)⁻¹ * ((c 3 * c 2 ^ s r) ^ m alpha)⁻¹ := by
  rw [mpcUnitTwist, if_pos (coreVal_zero h)]

@[simp] theorem mpcUnitTwist_one (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (c : Fin (coreRank h) → G) :
    mpcUnitTwist alpha r p eta h c 1 = c 1 * c 2 ^ p := by
  rw [mpcUnitTwist, if_neg (by rw [coreVal_one]; omega), if_pos (coreVal_one h)]

@[simp] theorem mpcUnitTwist_two (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (c : Fin (coreRank h) → G) :
    mpcUnitTwist alpha r p eta h c 2 = c 3 * c 2 ^ s r := by
  rw [mpcUnitTwist, if_neg (by rw [coreVal_two]; omega),
    if_neg (by rw [coreVal_two]; omega), if_pos (coreVal_two h)]

@[simp] theorem mpcUnitTwist_three (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (c : Fin (coreRank h) → G) :
    mpcUnitTwist alpha r p eta h c 3 = c 2 ^ᶻ etaHatZ (eta : ℤ_[2]) := by
  rw [mpcUnitTwist, if_neg (by rw [coreVal_three]; omega),
    if_neg (by rw [coreVal_three]; omega), if_neg (by rw [coreVal_three]; omega),
    if_pos (coreVal_three h)]

@[simp] theorem mpcUnitTwist_handleIdxU (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (c : Fin (coreRank h) → G) (j : Fin h) :
    mpcUnitTwist alpha r p eta h c (handleIdxU j) = c (handleIdxU j) := by
  rw [mpcUnitTwist, if_neg (by rw [handleIdxU_val]; omega),
    if_neg (by rw [handleIdxU_val]; omega), if_neg (by rw [handleIdxU_val]; omega),
    if_neg (by rw [handleIdxU_val]; omega)]

@[simp] theorem mpcUnitTwist_handleIdxV (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (c : Fin (coreRank h) → G) (j : Fin h) :
    mpcUnitTwist alpha r p eta h c (handleIdxV j) = c (handleIdxV j) := by
  rw [mpcUnitTwist, if_neg (by rw [handleIdxV_val]; omega),
    if_neg (by rw [handleIdxV_val]; omega), if_neg (by rw [handleIdxV_val]; omega),
    if_neg (by rw [handleIdxV_val]; omega)]

/-- The semantic arbitrary-unit `Mpc` core vector attached to an alphabet marking. -/
noncomputable def mpcCoreMarkUnit (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (t : Marking (2 + 2 * h) G) : Fin (coreRank h) → G :=
  mpcUnitTwist alpha r p eta h (fun i ↦ t (nIdx h i))

/-- The full `D_M` relator read through the arbitrary-unit dictionary. -/
noncomputable def mpcCoreRelUnit (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (t : Marking (2 + 2 * h) G) : G :=
  mRelWord alpha (mpcCoreMarkUnit alpha r p eta h t)

/-- **The arbitrary-unit, arbitrary-handle dictionary theorem.**  The semantic word's pro-`2`
value is the defining `D_M` relator on `(A,B,C0,D,handles)`. -/
theorem mpcProTwoWordUnit (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (halpha : 1 ≤ alpha) (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (mpcWUnit alpha r p eta h)) = mpcCoreRelUnit alpha r p eta h t := by
  rw [eval_pro2_mpcWUnit halpha r p eta h t]
  unfold mpcCoreRelUnit mpcCoreMarkUnit
  rw [mRelWord]
  simp only [mpcUnitTwist_zero, mpcUnitTwist_one, mpcUnitTwist_two,
    mpcUnitTwist_three, mpcUnitTwist_handleIdxU, mpcUnitTwist_handleIdxV, nIdx_zero,
    nIdx_one, nIdx_two, nIdx_three, nIdx_handleIdxU, nIdx_handleIdxV,
    Marking.apply_sigma]

/-- The same equality in the natural-word spelling consumed by the `D_M` presentation API. -/
theorem eval_pro2_mpcWUnit_eq_mNatWord (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (halpha : 1 ≤ alpha) (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (mpcWUnit alpha r p eta h)) =
      (mNatWord alpha h).ev (mpcCoreMarkUnit alpha r p eta h t) :=
  mpcProTwoWordUnit alpha r p eta h halpha t

end GQ2.Dyadic.Instances.MProcyclicCore

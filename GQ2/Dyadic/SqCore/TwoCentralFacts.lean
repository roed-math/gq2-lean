/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.Cores
import GQ2.Roe.Labute.TwoCentralTower

/-!
# W69-HOIST: shared two-central facts about the square model

This module holds the facts that relate the square model `D_sq h` of `SqCore/Cores.lean` to
the lower two-central tower `twoCentralSeries` of `Roe/Labute/TwoCentralTower.lean`, at the
one point where **both** the `Count` layer and the `SqCore` layer need to read the same
statement.

## Why the module exists

`dsqSigma_pow_four_not_mem_twoCentralSeries_four` was proved inside
`Count/LowerTwoCentralJenningsDegreeThree.lean`, where the class-three Jennings comparison
first needed it (to show the third lower exponent-two central layer is nontrivial).  Wave 68's
class-three lane then wanted to cite the very same fact from `SqCore/GradedBridge.lean`, to
record that the class-three argument provably cannot be replayed one class up: `bridge_sqWord`
consumes `(q²)² = 1` in `Q₃`, `bridge_pow_four_iff` isolates the `Q₄` analogue as the
equivalence `(∀ q : levelQuot G 4, (q²)² = 1) ↔ (∀ g : G, g⁴ ∈ γ₄)`, and this fact refutes the
right-hand side at `g = σ`.

Citing it from `SqCore` would have created the first `SqCore → Count` import.  The owner
refused that edge and chose the hoist (`docs/dyadic/owner-items-2026-08-05.md`, decision 5), so
the fact lives here instead: strictly below both layers, single-sourced, with the layering left
exact.

## Why here, and not lower

The statement's whole dependency closure is `SqCore/Cores.lean` (for `DSq`, `dsqSigma`, `chiSq`,
`chiSq_sigma`, and transitively `Roe/ChiR.lean` and `Roe/OrientationRoot.lean`) together with
`Roe/Labute/TwoCentralTower.lean` (for `twoCentralSeries`, `map_twoCentralSeries_le`,
`twoCentralSeries_units_le`).  Nothing from `Count` is used.  The alternative home,
`Roe/Labute/`, was rejected by the same import graph: the tower material there is deliberately
model-agnostic, and a fact about `D_sq h` would drag the square model down into it.

## The argument

The cyclotomic character `chiSq h : D_sq h → ℤ₂ˣ` sends `σ` to the orientation unit `S`, whose
mod-`32` value is `29`.  A continuous homomorphism carries `γ₄` into `γ₄`, and on `ℤ₂ˣ` the
fourth term of the tower already lies in the kernel of reduction mod `32`.  So if `σ⁴` were in
`γ₄` then `29⁴ = 707281` would be `1` mod `32`, which it is not.
-/

namespace GQ2.ContCoh

open GQ2.Roe GQ2.Roe.Labute GQ2.Dyadic.SqCore

/-- The mod-`32` value of the distinguished orientation coordinate is `29`. -/
theorem Sval_toZModPow_five :
    PadicInt.toZModPow 5 (SvalUnit : ℤ_[2]) = 29 := by
  rw [val_SvalUnit]
  have h := congrArg (PadicInt.toZModPow (p := 2) 5) Sval_mul_denom
  simp only [map_mul, map_add, map_pow, map_one, map_neg] at h
  rw [rootX_toZModPow_five] at h
  exact (by decide : ∀ z : ZMod (2 ^ 5),
    z * ((21 : ZMod (2 ^ 5)) ^ 2 + 21 + 1) = -(21 : ZMod (2 ^ 5)) ^ 3 →
      z = 29) _ h

/-- The fourth power of `sigma` is not in the fourth lower-two-central subgroup.  Its
cyclotomic value is `29^4 = 17`, not `1`, modulo `32`, whereas the fourth term of the tower on
`ℤ₂ˣ` lies in the kernel of reduction mod `32` (`twoCentralSeries_units_le`).  (Wave 70: the
comparison group on this line used to be spelled `lambda_4`, which names nothing in the tree and
read as `γ₄` of the source group rather than of `ℤ₂ˣ`.) -/
theorem dsqSigma_pow_four_not_mem_twoCentralSeries_four (h : ℕ) :
    dsqSigma h ^ 4 ∉ twoCentralSeries (DSq h : Type) 4 := by
  intro hs
  have himage : chiSq h (dsqSigma h ^ 4) ∈ twoCentralSeries ℤ_[2]ˣ 4 :=
    map_twoCentralSeries_le (chiSq h).toMonoidHom (chiSq h).continuous_toFun 4
      ⟨dsqSigma h ^ 4, hs, rfl⟩
  have hker := twoCentralSeries_units_le 4 (by omega) himage
  have hunit := MonoidHom.mem_ker.mp hker
  have hval := congrArg Units.val hunit
  change PadicInt.toZModPow 5 ((chiSq h (dsqSigma h ^ 4) : ℤ_[2]ˣ) : ℤ_[2]) = 1 at hval
  rw [map_pow, chiSq_sigma, Units.val_pow_eq_pow_val,
    map_pow, Sval_toZModPow_five] at hval
  exact (by decide : (707281 : ZMod (2 ^ 5)) ≠ 1) hval

/-! ## Axiom pins -/

section AxiomPins

#print axioms Sval_toZModPow_five
#print axioms dsqSigma_pow_four_not_mem_twoCentralSeries_four

end AxiomPins

end GQ2.ContCoh

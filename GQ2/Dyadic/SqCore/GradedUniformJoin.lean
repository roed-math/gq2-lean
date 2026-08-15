/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedUniformTower
import GQ2.Dyadic.SqCore.GradedDeltaFunctionals

/-!
# W75-JOIN: joining the uniform tower to the delta functionals

Wave 74 landed two modules that were written blind to each other:

* `GQ2/Dyadic/SqCore/GradedUniformTower.lean` (prefix `gTower`), the class-uniform
  engine, which reduces the whole `h ≥ 1` residual `SqLamMarkTransitivity h` to two named
  interfaces `GTowerDefectVanishing h` and `GTowerKnobRealizable h`, plus one base index
  `GTowerLayerReach h ν' 2`;
* `GQ2/Dyadic/SqCore/GradedDeltaFunctionals.lean` (prefix `gDelta`), Labute's Lemma 4
  apparatus, whose interface `GDeltaDefectVanishing h` is **proved outright**.

This file is the join.  It states the shape mismatch between the two interfaces exactly,
records which half of it is a theorem and which half is a genuine mathematical obligation,
and assembles what can be assembled.

## The shape mismatch, precisely

`GDeltaDefectVanishing h` says: for every functional coefficient `c`, marking `ν'`, handle
`j` and dressing `a` with `χ_sq(a i) = 1` at every slot,
`gDelta h c (sqRelWord (sqArbFrame h ν' j a)) = 0`.

`GTowerDefectVanishing h` says: for every *selected* marking `ν'`, handle `j`, level
`k ≥ 2` and dressing `a` with `λ(a i) = 1` and `ν'(a i) = 1` at every slot, the layer class
of the relator lies in `Subgroup.closure (gTowerKnobSet h ν' k)`.

The two differ on **both** sides:

* **Hypothesis side (the torsion gap).**  The tower's dressing clause is the supply's, two
  logged rows; the functional's is `χ_sq = 1`.  The supply's `λ`-clause forces only
  `χ_sq(a i) = ±1` (`gDelta_chiSq_of_nuLam`, wave 74's own honesty artifact).  So
  `GDeltaDefectVanishing` is available on a **strict sub-space** of the dressings that
  `GTowerDefectVanishing` quantifies over.  §1 below makes the containment a theorem and
  isolates the `-1` branch.
* **Conclusion side (Labute's `Im δ = ⋂ ker Δ`).**  The functional side delivers a
  *reading* (`gDelta … = 0`); the tower side wants a *membership* (knob span).  Bridging
  them is the second half of his Lemma 4 and needs two further inputs, both named here:
  the knobs must be invisible to the functionals at the layer bit, and the admissible
  towers must be detected by them.

-/

open Multiplicative

namespace GQ2

open Roe Roe.Labute FoxH

namespace Dyadic

namespace SqCore

open MarkedCore
open scoped commutatorElement

/-! ## §1 The hypothesis side: the torsion gap, made a theorem

The `χ`-trivial dressings are exactly the ones the functional interface covers.  They are a
sub-family of the admissible dressings, and the defect of the complement is precisely the
`-1` branch of `gDelta_chiSq_of_nuLam`. -/

section Hypotheses

variable {h : ℕ}

variable (h) in
/-- **The `χ`-trivial dressing space**: the dressings for which `GDeltaDefectVanishing`
speaks.  (Both row clauses of the supply, *plus* exact `χ`-triviality at every slot.) -/
def GJoinChiAdm (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (a : Fin (sqRank h) → (DSq h : Type)) : Prop :=
  (∀ i, nuLam h (a i) = 1) ∧ (∀ i, nu' (a i) = 1) ∧ (∀ i, chiSq h (a i) = 1)

/-- A `χ`-trivial dressing is an admissible one: the containment is by definition, and it is
recorded so the direction of the gap is unambiguous. -/
theorem gJoin_chiAdm_rows
    {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}
    {a : Fin (sqRank h) → (DSq h : Type)} (ha : GJoinChiAdm h nu' a) :
    (∀ i, nuLam h (a i) = 1) ∧ (∀ i, nu' (a i) = 1) :=
  ⟨ha.1, ha.2.1⟩

/-- ⭐ **The torsion gap, slot by slot**: an admissible dressing slot is either `χ`-trivial
or carries the torsion value `-1`; there is no third possibility.  So the family that
`GTowerDefectVanishing` quantifies over is covered by `GJoinChiAdm` exactly off the `-1`
branch. -/
theorem gJoin_slot_dichotomy {a : (DSq h : Type)} (hl : nuLam h a = 1) :
    chiSq h a = 1 ∨ chiSq h a = -1 :=
  gDelta_chiSq_of_nuLam hl

/-- The gap is a `2`-torsion phenomenon and nothing more: on admissible slots `χ_sq` takes
values in `μ₂`. -/
theorem gJoin_slot_sq {a : (DSq h : Type)} (hl : nuLam h a = 1) : (chiSq h a) ^ 2 = 1 :=
  gDelta_chiSq_sq_of_nuLam hl

/-- ⭐ **The functional kill on the `χ`-trivial dressing space**: every functional reads
zero on the relator value of every `χ`-trivial dressing of every frame.  This is
`GDeltaDefectVanishing` re-stated in the join's vocabulary, and it is the *whole* of what
the FUNC lane exports towards `GTowerDefectVanishing`. -/
theorem gJoin_reading_zero (c : Fin (sqRank h) → ℤ_[2])
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)
    {a : Fin (sqRank h) → (DSq h : Type)} (ha : GJoinChiAdm h nu' a) :
    gDelta h c (sqRelWord (sqArbFrame h nu' j a)) = 0 :=
  gDeltaDefectVanishing_holds h c nu' j a ha.2.2

end Hypotheses

/-! ## §2 Axiom pins -/

section AxiomPins

#print axioms GQ2.Dyadic.SqCore.GJoinChiAdm
#print axioms gJoin_chiAdm_rows
#print axioms gJoin_slot_dichotomy
#print axioms gJoin_slot_sq
#print axioms gJoin_reading_zero

end AxiomPins

end SqCore

end Dyadic

end GQ2

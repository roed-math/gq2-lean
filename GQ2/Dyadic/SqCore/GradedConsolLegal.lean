/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFiveLive
import GQ2.Dyadic.SqCore.PivotClimb

/-!
# W65-CONSOL: the uniform legality statement, and the free `nu'` strengthening

The tree answers the question **"does any LEGAL dressing `g` have `Phi g = x0`?"** three times at
three points, by three incomparable single-column arguments: wave 60 off `lambda` and `nu'` mod
`2`, wave 61 off the fifth abelian column using `7` a unit, and W63-LIVE5 off the FIRST abelian
column.  All three are recorded in prose and none is formalised; W63-LIVE5's says so in its own
words, "recorded here rather than formalised" (`GradedFiveLive`, section "The legality audit,
REDONE"), and reappears as a MEASURED row.  W64-VERIFY's task C then found ONE criterion that
covers all three and measured it exhaustively
(`scripts/w64_verify/results/task_c_legality.txt`).

This file makes that criterion a theorem, and takes the strengthening W64-VERIFY found for free.

## ⭐⭐⭐ The uniform criterion

`consolLegal_fiveTuple_ne`.  At a point given by a `fiveTuple` marking, legality is a condition
on the generator exponents alone and is the SAME condition at every point, so the obstruction is
a condition on the point's abelian columns, five slots at a time:

```text
   sigma slot   a-column = 0 mod 4    b-column ODD
   x0 slot      a-column = 2 mod 4    b-column even
   x1, U, V     a-column = 0 mod 4    b-column even
   the target   a-column ≠ 0 mod 4    b-column even     ⇒  unreachable
```

The mechanism is one hom identity, checked on the `3 + 2h` generators and transported by
`dsq_hom_ext`: `(Phi g).a mod 4 = 2 lambda(g) + 2 e (Phi g).b mod 2`, where `e` is the parity of
`lambda` on the sigma slot.  ⚠ `e` is **never evaluated**.  It cancels against itself at the
sigma slot (`2e + 2e = 0` in `ZMod 4`) and is killed by the target's even `b`-column at the end,
which is why nothing here pins the census axiom `sqPivotExp` - the tree's own reason for leaving
this argument out of `GradedFiveLive` in the first place.

## ⭐⭐ The free `nu'` strengthening

W64-VERIFY dropped the `nu'` half of legality and measured that the door stays shut at all three
points (task C section 3, `NOT load-bearing (lambda alone suffices)`).  The theorems below carry
that strengthening: **`nu'` does not appear in any statement in this file**, and the only
legality hypothesis is `lam g = 1`.

The reason it is free is worth naming, because it is not that `nu'` was redundant as a
functional.  W63-LIVE5's prose uses `nu'` to force the sigma exponent `a_s = 0`.  But the
`b`-column of the point IS `a_s`, so an equation `Phi g = x` supplies `a_s` mod `8` on its own,
from the target's `b`-column, and the hypothesis is doing work the conclusion already does.  That
is why the strengthening costs nothing here and why the criterion asks the target for an even
`b`-column instead.

## ⚠ What this file does NOT do

* It instantiates the criterion at **one** of the three points, W63-LIVE5's live binder point
  (`consolLegal_liveBlk_ne_stageX`), the one whose audit is explicitly unformalised.  Wave 60's
  `fiveFrameHom` and wave 61's `stageFrameHom` are **not** instantiated here and nothing below
  asserts the criterion's hypotheses hold at them; each is a five-slot `decide` for a later
  wave, and until it is run the other two rows stay where W64-VERIFY left them, MEASURED.
* It says nothing about which dressings ARE reachable, and nothing about achievability: the
  conclusion is a non-membership at one slot value, not a description of the image.
* It does not re-derive the exponent lattice `L` of W64-VERIFY's task C.  ⚠ The Lean route does
  not mention exponents at all - `D_sq h` has no exponent map - and works with the column
  characters instead.  The lattice is the reading, not the proof.
* ⚠ `lambda` is carried **abstractly**, as any continuous marking with the committed values on
  `x0`, `x1` and the handle letters.  `nuLam` has exactly those values (`nuLam_x0`, `nuLam_x1`,
  `nuLam_handleU`, `nuLam_handleV`), so the theorems apply to it; that instantiation is not
  performed here because it would pin `sqPivotExp` through `nuLam`'s definition, and the
  criterion is strictly more general without it.

## Contents

* **1** the two reductions `ZMod 8 → ZMod 4` and `ZMod 2 → ZMod 4`;
* **2** ⭐⭐⭐ the uniform criterion at a `fiveTuple` point;
* **3** ⭐⭐ the instance at W63-LIVE5's live binder point;
* **4** axiom pins.

## Merge notes

Nothing is redefined.  Reused: `SqU6`, `SqU6.one_a`, `SqU6.one_b`, `SqU6.mul_a`, `SqU6.mul_b`,
`sqGen`, `DSq`, `dsqX0`, `dsqX1`, `fiveTuple` and its slot lemmas (`GradedFive`); `sqRank`,
`sqHandleIdxU`, `sqHandleIdxV`, `dsq_hom_ext` (`Cores`); `sqIdx_cases` (`Certificate`); `gr3R`,
`selPar`, `selPar_add`, `selPar_zero` (`GradedSelect`); `sqRedMark`, `sqModTwo`,
`toAdd_sqModTwo_of_odd`, `toAdd_sqModTwo_of_even` (`PivotClimb`); `liveBlkHom`, `liveBlkHom_gen`,
`liveBlkWit`, `liveBlkSig`, `liveBlkY`, `liveBlkU`, `liveBlkV` (`GradedFiveLive`); `stageX`
(`GradedFiveStageFour`).

New public names, all carrying a `consol` marker against the concurrent wave-65 lanes:
`consolRedFour`, `consolRedFour_zero`, `consolRedFour_add`, `consolTwoUp`, `consolTwoUp_add`,
`consolTwoUp_self`, `consolTwoUp_zero`, `consolLegal_column`, `consolLegal_fiveTuple_ne`,
`consolLegal_liveBlk_ne_stageX`.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats` bump; every `decide` is on
`ZMod 8`, `ZMod 4`, `ZMod 2` or on `SqU6 gr3R` built over `ZMod 8`.  All **6** committed prints
are **std-3**.  ⚠ **No census axiom is reachable**: `sqPivotExp`
is not mentioned, and `nuLam` - which is defined through it - is deliberately not instantiated.
-/

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The two reductions -/

section Reductions

/-- The reduction `ℤ/8 → ℤ/4`.  The first abelian column carries `2 a_0`, and what the argument
needs from it is the parity of `a_0`, i.e. `2` told apart from `0` and from `4`.  ⚠ Remark, not
used below and not proved here: no homomorphism `ℤ/8 → ℤ/2` tells them apart, the only
non-trivial one being reduction mod `2`; that is why the target is `ℤ/4`. -/
def consolRedFour : gr3R → ZMod 4 := fun x => (x.val : ZMod 4)

@[simp] theorem consolRedFour_zero : consolRedFour 0 = 0 := by decide

theorem consolRedFour_add :
    ∀ x y : gr3R, consolRedFour (x + y) = consolRedFour x + consolRedFour y := by decide

@[simp] theorem consolRedFour_two : consolRedFour 2 = 2 := by decide

/-- The doubling `ℤ/2 → ℤ/4`.  Additive, and `2 t + 2 t = 0`, which is the cancellation that
keeps the sigma slot's unknown `lambda`-parity out of every statement below. -/
def consolTwoUp : ZMod 2 → ZMod 4 := fun t => 2 * (t.val : ZMod 4)

@[simp] theorem consolTwoUp_zero : consolTwoUp 0 = 0 := by decide

theorem consolTwoUp_add :
    ∀ s t : ZMod 2, consolTwoUp (s + t) = consolTwoUp s + consolTwoUp t := by decide

/-- ⭐ The cancellation: `2 e + 2 e = 0` in `ℤ/4`, for either value of `e`. -/
theorem consolTwoUp_self : ∀ t : ZMod 2, consolTwoUp t + consolTwoUp t = 0 := by decide

end Reductions

/-! ## 2 The uniform criterion -/

section Criterion

variable {h : ℕ}

/-- The obstructing column, as a character: `g ↦ (Phi g).a mod 4`. -/
private noncomputable def consolAChar (Φ : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R)) :
    ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 4)) where
  toFun g := Multiplicative.ofAdd (consolRedFour (Φ g).a)
  map_one' := by rw [map_one, SqU6.one_a, consolRedFour_zero]; rfl
  map_mul' p q := by rw [map_mul, SqU6.mul_a, consolRedFour_add, ofAdd_add]
  continuous_toFun :=
    (continuous_of_discreteTopology
      (f := fun p : SqU6 gr3R => Multiplicative.ofAdd (consolRedFour p.a))).comp
      Φ.continuous_toFun

/-- The legality side, as a character: `g ↦ 2 lambda(g) + 2 e (Phi g).b`, both terms mod `2`. -/
private noncomputable def consolLegalChar (Φ : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R))
    (lam : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (e : ZMod 2) :
    ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 4)) where
  toFun g := Multiplicative.ofAdd (consolTwoUp (Multiplicative.toAdd (sqRedMark lam g)))
    * Multiplicative.ofAdd (consolTwoUp (e * selPar (Φ g).b))
  map_one' := by
    simp only [map_one, toAdd_one, SqU6.one_b, selPar_zero, mul_zero]
    decide
  map_mul' p q := by
    simp only [map_mul, toAdd_mul, SqU6.mul_b, selPar_add, mul_add, consolTwoUp_add, ofAdd_add]
    exact mul_mul_mul_comm _ _ _ _
  continuous_toFun := by
    refine Continuous.mul ?_ ?_
    · exact (continuous_of_discreteTopology
        (f := fun p : Multiplicative (ZMod 2) =>
          Multiplicative.ofAdd (consolTwoUp (Multiplicative.toAdd p)))).comp
        (sqRedMark lam).continuous_toFun
    · exact (continuous_of_discreteTopology
        (f := fun p : SqU6 gr3R =>
          Multiplicative.ofAdd (consolTwoUp (e * selPar p.b)))).comp Φ.continuous_toFun

/-- ⭐⭐ **THE COLUMN IDENTITY, TRANSPORTED OFF THE GENERATORS.**  A generator-level check of
the identity `(Phi g).a mod 4 = 2 lambda(g) + 2 e (Phi g).b` upgrades to every `g`, because both
sides are continuous characters into `ℤ/4` and `D_sq h` is topologically generated by its
`3 + 2h` letters.  No property of `Phi`, `lam` or `e` beyond the check is used. -/
theorem consolLegal_column (Φ : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R))
    (lam : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (e : ZMod 2)
    (hgen : ∀ i, consolRedFour (Φ (sqGen h i)).a
      = consolTwoUp (Multiplicative.toAdd (sqRedMark lam (sqGen h i)))
        + consolTwoUp (e * selPar (Φ (sqGen h i)).b))
    (g : (DSq h : Type)) :
    consolRedFour (Φ g).a
      = consolTwoUp (Multiplicative.toAdd (sqRedMark lam g))
        + consolTwoUp (e * selPar (Φ g).b) := by
  have hext : consolAChar Φ = consolLegalChar Φ lam e :=
    dsq_hom_ext _ _ fun i => by
      show Multiplicative.ofAdd (consolRedFour (Φ (sqGen h i)).a)
        = Multiplicative.ofAdd (consolTwoUp (Multiplicative.toAdd (sqRedMark lam (sqGen h i))))
          * Multiplicative.ofAdd (consolTwoUp (e * selPar (Φ (sqGen h i)).b))
      rw [← ofAdd_add, hgen i]
  have hg := DFunLike.congr_fun hext g
  have hg' : Multiplicative.ofAdd (consolRedFour (Φ g).a)
      = Multiplicative.ofAdd (consolTwoUp (Multiplicative.toAdd (sqRedMark lam g))
        + consolTwoUp (e * selPar (Φ g).b)) := by
    rw [ofAdd_add]; exact hg
  exact Multiplicative.ofAdd.injective hg'

end Criterion

/-! ### The criterion in the shape the points are stated -/

section FiveTuple

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐⭐ **THE UNIFORM LEGALITY STATEMENT.**  At a point carried by a `fiveTuple` marking whose
five slots satisfy the ten column conditions below (two per slot), **no `lambda`-legal `g`
has `Phi g = x`**,
for any `x` with an even `b`-column and an `a`-column that is not `0` mod `4`.  At every handle
count and every handle.

⚠ **There is no `nu'` hypothesis**, which is W64-VERIFY's free strengthening: the `b`-column
conditions do the work `nu'`-triviality did in the prose arguments, and the target's own
`b`-column supplies the sigma exponent.

⚠ The sigma slot's `lambda`-parity `e` is a bound variable, never evaluated: it cancels against
itself at the sigma slot.  So nothing here needs `sqPivotExp` to be a unit, which is what the
prose arguments used and what would pin a census axiom.

⚠ **Not claimed**: that the hypotheses hold at any particular point.  They are ten `decide`s
per point; section 3 runs them at one point only. -/
theorem consolLegal_fiveTuple_ne {S X Y U V : SqU6 gr3R}
    (Φ : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R))
    (lam : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hΦ : ∀ i, Φ (sqGen h i) = fiveTuple gr3R h j S X Y U V i)
    (hlx0 : lam (dsqX0 h) = Multiplicative.ofAdd (1 : ℤ_[2]))
    (hlx1 : lam (dsqX1 h) = Multiplicative.ofAdd (2 : ℤ_[2]))
    (hlU : ∀ j' : Fin h, lam (sqGen h (sqHandleIdxU j')) = 1)
    (hlV : ∀ j' : Fin h, lam (sqGen h (sqHandleIdxV j')) = 1)
    (hSa : consolRedFour S.a = 0) (hSb : selPar S.b = 1)
    (hXa : consolRedFour X.a = 2) (hXb : selPar X.b = 0)
    (hYa : consolRedFour Y.a = 0) (hYb : selPar Y.b = 0)
    (hUa : consolRedFour U.a = 0) (hUb : selPar U.b = 0)
    (hVa : consolRedFour V.a = 0) (hVb : selPar V.b = 0)
    {x : SqU6 gr3R} (hxa : consolRedFour x.a ≠ 0) (hxb : selPar x.b = 0)
    {g : (DSq h : Type)} (hleg : lam g = 1) :
    Φ g ≠ x := by
  set e : ZMod 2 := Multiplicative.toAdd (sqRedMark lam (sqGen h 0)) with he
  -- the generator check, slot by slot
  have hgen : ∀ i, consolRedFour (Φ (sqGen h i)).a
      = consolTwoUp (Multiplicative.toAdd (sqRedMark lam (sqGen h i)))
        + consolTwoUp (e * selPar (Φ (sqGen h i)).b) := by
    intro i
    have hone : ∀ j' : Fin h, ∀ y : (DSq h : Type), lam y = 1 →
        Multiplicative.toAdd (sqRedMark lam y) = 0 := by
      intro _ y hy
      show Multiplicative.toAdd (sqModTwo (lam y)) = 0
      rw [hy, map_one]
      rfl
    rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
    · rw [hΦ 0, fiveTuple_zero, hSa, hSb, mul_one, ← he, consolTwoUp_self]
    · have hl : Multiplicative.toAdd (sqRedMark lam (sqGen h 1)) = 1 := by
        show Multiplicative.toAdd (sqModTwo (lam (dsqX0 h))) = 1
        rw [hlx0]
        exact toAdd_sqModTwo_of_odd (isUnit_iff_not_two_dvd.mp isUnit_one)
      rw [hΦ 1, fiveTuple_one, hXa, hXb, mul_zero, hl, consolTwoUp_zero, add_zero]
      decide
    · have hl : Multiplicative.toAdd (sqRedMark lam (sqGen h 2)) = 0 := by
        show Multiplicative.toAdd (sqModTwo (lam (dsqX1 h))) = 0
        rw [hlx1]
        exact toAdd_sqModTwo_of_even ⟨1, by ring⟩
      rw [hΦ 2, fiveTuple_two, hYa, hYb, mul_zero, hl, consolTwoUp_zero, add_zero]
    · rw [hΦ _, hone j' _ (hlU j'), consolTwoUp_zero, zero_add]
      by_cases hjj : j' = j
      · subst hjj
        rw [fiveTuple_handleU, hUa, hUb, mul_zero, consolTwoUp_zero]
      · rw [fiveTuple_handleU_ne hjj, SqU6.one_a, SqU6.one_b, consolRedFour_zero, selPar_zero,
          mul_zero, consolTwoUp_zero]
    · rw [hΦ _, hone j' _ (hlV j'), consolTwoUp_zero, zero_add]
      by_cases hjj : j' = j
      · subst hjj
        rw [fiveTuple_handleV, hVa, hVb, mul_zero, consolTwoUp_zero]
      · rw [fiveTuple_handleV_ne hjj, SqU6.one_a, SqU6.one_b, consolRedFour_zero, selPar_zero,
          mul_zero, consolTwoUp_zero]
  -- …transported to `g`, and read at the target
  intro hcon
  have hcol := consolLegal_column Φ lam e hgen g
  have hlg : Multiplicative.toAdd (sqRedMark lam g) = 0 := by
    show Multiplicative.toAdd (sqModTwo (lam g)) = 0
    rw [hleg, map_one]
    rfl
  rw [hcon, hlg, consolTwoUp_zero, zero_add, hxb, mul_zero, consolTwoUp_zero] at hcol
  exact hxa hcol

end FiveTuple

/-! ## 3 The instance at the live binder point -/

section LivePoint

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐ **W63-LIVE5'S LEGALITY AUDIT, FORMALISED, AND WITHOUT ITS `nu'` HALF.**  At the live
binder point, at every handle count and every handle, **no `lambda`-legal `g` has
`liveBlkHom h j g = stageX`**.

`GradedFiveLive` records this argument in prose ("recorded here rather than formalised") and
lists it as MEASURED, "the legality obstruction on the first abelian column, exhaustive over
even `a_0`".  It is now a theorem, with `lambda` carried abstractly and `nu'` gone: the ten
slot conditions of `consolLegal_fiveTuple_ne` hold at this point by `decide`, and `stageX` has
`a = 2` and `b = 0`, which are the two the target has to supply.

⚠ This is the FIRST abelian column's obstruction, which is W63-LIVE5's route and not wave 60's
or wave 61's; those two points are not touched here.  ⚠ It says nothing about the class-five
line, the block reading, or achievability. -/
theorem consolLegal_liveBlk_ne_stageX
    (lam : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hlx0 : lam (dsqX0 h) = Multiplicative.ofAdd (1 : ℤ_[2]))
    (hlx1 : lam (dsqX1 h) = Multiplicative.ofAdd (2 : ℤ_[2]))
    (hlU : ∀ j' : Fin h, lam (sqGen h (sqHandleIdxU j')) = 1)
    (hlV : ∀ j' : Fin h, lam (sqGen h (sqHandleIdxV j')) = 1)
    {g : (DSq h : Type)} (hleg : lam g = 1) :
    liveBlkHom h j g ≠ stageX :=
  consolLegal_fiveTuple_ne (j := j) (S := liveBlkSig * 1) (X := stageX) (Y := liveBlkY)
    (U := liveBlkU) (V := liveBlkV) (liveBlkHom h j) lam
    (fun i => by rw [liveBlkHom_gen, liveBlkWit]) hlx0 hlx1 hlU hlV
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hleg

end LivePoint

/-! ## 4 Axiom pins -/

section AxiomPins

#print axioms consolRedFour_add
#print axioms consolTwoUp_add
#print axioms consolTwoUp_self
#print axioms consolLegal_column
#print axioms consolLegal_fiveTuple_ne
#print axioms consolLegal_liveBlk_ne_stageX

end AxiomPins

end SqCore

end Dyadic

end GQ2

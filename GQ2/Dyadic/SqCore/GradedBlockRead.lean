/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFiveBlind
import GQ2.Dyadic.SqCore.GradedFiveStageFour

/-!
# W61-BLOCK: reading the handle block, and the first handle-count forcing

Wave 57 proved the handle block invisible to the class-four selection bit by an identity.
Wave 58 found the identity ends at class five and named the coupling.  Wave 59 proved the
class-five blindness **at the committed sigma slot** and refuted the general form: one
`nu'`-trivial letter away there is a relator-killing marking whose block coordinate is odd and
whose class-five response the selection bit separates (`blindCex_not_handle_blind`).  So the
block is visible at class five away from the committed slot, and nothing had used that.

This file builds the reading, and the answer is a **negative with a positive corollary**.

## ⭐⭐⭐ Headline 1: THE BLOCK EQUATION, and it is a closed form

`SqU6.selPar_handleWord_i_of_relator`.  At **every** relator-killing marking over
`gr3R = ZMod 8`, at **every** handle count, at **every** sigma slot, with **no** gauge:

```text
selPar (handle block)_46  =  selPar (s_45 * x_56  -  s_56 * x_45)
```

the right side being `SqU6.blockRead (m 0) (m 1)`: four entries of the sigma slot and the `x0`
slot, and no evaluation of the core word at all.  Only two of the fifteen relator rows are used,
the `(4,5)`-row and the `(4,6)`-row, and the `(5,6)`-row does the first one's job equally well.

⭐ **This is an equality where wave 59 has an implication.**
`SqU6.handleWord_i_even_of_relator` carries the hypothesis
`(m 0).d * (m 1).e - (m 0).e * (m 1).d = 2 * t`, which is exactly "`blockRead` is even", and
concludes the block coordinate is even.  The converse half is the new content
(`SqU6.handleWord_i_odd_of_relator`): an **odd** block reading forces an **odd** block
coordinate.  That is what makes it a reading rather than a bound, and it is what turns wave 59's
counterexample from an anomaly into an instance: `blindCex_block_equation` derives the committed
`blindCex_handleWord_i = 1` from the counterexample's own core slots.

## ⭐⭐⭐ Headline 2: so the class-five selection bit reads NO handle datum

`SqU6.selPar_sqRelWord_sigFiveDress_o_core`.  At every relator-killing marking, on the
`nu'`-gauge, at **every** sigma slot:

```text
selPar (Delta_v relator top row)
  =  selPar (Delta_v core word top row)  +  selPar (coupling)  *  selPar (blockRead)
```

Every symbol on the right is a **core slot**.  Hence
`SqU6.selPar_sqRelWord_sigFiveDress_o_eq_of_core`: two relator-killing markings with the same
three core slots have the same class-five selection bit, **at different handle counts, with
different handle letters, and with no hypothesis on the sigma slot**.  Wave 59's committed
theorem `SqU6.selPar_sqRelWord_sigFiveDress_o` is the `blockRead = 0` instance of this, and
wave 59's counterexample does not contradict it: what the bit separates there is the
counterexample's own sigma slot, which is the only thing that changed.

**This is the negative the brief asked to be certified.**  Away from the committed slot the
block coordinate is visible, and what it shows is already determined by `(m 0, m 1)`.  The
class-five instrument set sees nothing about the handle letters that it does not already see
from the core.  ⭐ The honest control is `SqU6.handleWord_eq_inv_sqWord_of_relator`: the relator
pins the **whole** block element, not merely its `(4,6)` coordinate, so core-determinacy of the
bit is cheap and the content is the closed form.  The reason wave 58's live/dead pair looked
like visibility is that `GradedFive.deadFiveMark` does **not** kill the relator.

## ⭐⭐ Headline 3: the positive corollary, and it is a handle-count forcing

The equation runs the other way too.  At `h = 0` there is no block, so
`SqU6.blockRead_even_of_relator_handleFree` forces the block reading **even**, and
⭐⭐ `SqU6.pos_of_blockRead_odd`: a relator-killing marking with an **odd** block reading has
`0 < h`.  Sharper, ⭐ `SqU6.exists_handle_minor_odd`: some handle pair's `(4,5)/(5,6)` minor is
odd, that is, its two letters are independent mod `2` in those two columns.

⭐⭐⭐ `blindCexCore_not_relator_handleFree` makes it concrete and non-vacuous:
**wave 59's counterexample core slots are realized by a relator-killing marking at every
handle count `h >= 1` (the committed `sqRelWord_blindCexMark`) and by NONE at `h = 0`, whatever
the `x1` slot is.**  Every committed statement of the lane that mentions the handle count takes
`0 < h` as a hypothesis; this pair separates the two cases, and it is proved rather than
measured.

⭐⭐ The forcing in the campaign's usual shape is
`SqU6.selPar_blockRead_dress_of_relator`: a sigma dressing that keeps the relator killed pairs
**evenly** against the `x0` slot in the two outer abelian columns.  ⚠ Its scope: the diagonal
dressing `v = m 1` satisfies it outright, and so does every `gamma_2`-dressing, so it bites only
on abelian dressings, which is a channel no committed forcing reads and also not the channel the
committed exclusions run on.

## ⭐⭐ Headline 4: the block channel is BELOW the achievable lattice

`SqU6.blockRead_gaThreeDress`, `SqU6.blockCoupling_gaThreeDress`,
⭐⭐ `SqU6.blockChannel_gaThreeDress`.  A `gamma_2`-dressing of any slot cannot move the block
reading and a `gamma_3`-dressing cannot move the coupling, because both are read at class
**two** while the campaign's achievable refinements live in `gamma_4` at class five and in
`gamma_3` one filtration step wider.  So the block channel's contribution to the class-five bit
is invariant under the whole lattice, with no soundness chain, no even-column hypothesis and no
covector condition - and in particular **no analogue of wave 59's stage-four hole**, which
`GradedFiveStageFour` had to close by strengthening the point.  Soundness here is structural
rather than arithmetic: this is the one place where the block reading is strictly better behaved
than the sigma reading.

## PROVED versus measured

**PROVED**, with no live hypothesis: everything named above.  No `sorry`, no new axiom, no
`native_decide`; every `decide` is on `ZMod 8` or `ZMod 2`.

**Measured** (`scripts/w61_block/`, certified outputs in `scripts/w61_block/results/`):
the block parity law **exhaustively** over `ZMod 8` (`4194304` points, `0` failures) and its
failure without the abelian row; the block equation at `410` relator-killing markings produced
by a layered solve at handle counts `0..4`, cross-checked by honest `6 x 6` matrix collection;
the solve's row-`(4,6)` solvability against the equation in **both** directions (`20000`
agreements, `0` disagreements); the characterisation of the admissible sigma slots (`30000`
trials, `0` disagreements); the `h = 0` forcing (`3074` odd core pairs, `0` completions, plus an
exhaustive re-run at wave 59's core slots); the bit collapse against honestly collected relators
(`1360` comparisons, `0` mismatches); the `gamma_2`/`gamma_3` invariances with their controls,
and the honest lower central series of the image subgroup.  `50` named checks in three scripts,
`0` failures.

## Contents

* **1** the block reading and the closed form of the `(4,6)` row;
* **2** ⭐⭐⭐ the block equation, and both halves of it;
* **3** ⭐⭐ the handle-count forcing;
* **4** ⭐⭐⭐ the collapse of the class-five selection bit onto the core slots;
* **5** ⭐⭐ soundness: the block channel sits below the achievable lattice;
* **6** the committed points, and the concrete handle-count separation;
* **7** axiom pins.

## Axiom hygiene

All prints are **std-3** (`propext`, `Classical.choice`, `Quot.sound`) or a subset.
-/

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The block reading -/

section BlockRead

variable {R : Type} [CommRing R]

/-- ⭐⭐ **THE BLOCK READING** `s_45 * x_56 - s_56 * x_45`: the `2 x 2` minor of the sigma slot
against the `x0` slot in the two outer abelian columns.

It is the sigma pairing of `SqU6.sqWord_i` that `docs/dyadic/w58-sigma5-note.md` section 4.2
dropped, because that note computed at `sigma = E_23`, where both columns vanish.  Section 2
shows it is the parity of the handle block's `(4,6)` coordinate at every relator-killing
marking. -/
def SqU6.blockRead (s x : SqU6 R) : R := s.d * x.e - s.e * x.d

theorem SqU6.blockRead_def (s x : SqU6 R) : SqU6.blockRead s x = s.d * x.e - s.e * x.d := rfl

/-- At a sigma slot with vanishing `(4,5)`- and `(5,6)`-columns - the committed `sigFiveMark`,
and the trivial slot the live class-five point uses - the block reading vanishes.  This is why
wave 59's theorem is the `blockRead = 0` instance of section 4. -/
theorem SqU6.blockRead_eq_zero_of_slot {s x : SqU6 R} (hsd : s.d = 0) (hse : s.e = 0) :
    SqU6.blockRead s x = 0 := by
  simp only [SqU6.blockRead, hsd, hse]
  ring

theorem SqU6.blockRead_sigFiveMark (x : SqU6 R) : SqU6.blockRead (sigFiveMark R) x = 0 :=
  SqU6.blockRead_eq_zero_of_slot rfl rfl

/-- ⭐ **The `(4,6)` row of the core word IS the block reading, up to an explicit even
correction** - over **any** commutative ring, as soon as the `x1` slot's `(4,5)`-column is even.
Every one of the four remaining terms of `SqU6.sqWord_i` carries a factor `2`, three of them
outright and the fourth through the hypothesis. -/
theorem SqU6.sqWord_i_eq_blockRead (s x y : SqU6 R) {k : R} (hyd : y.d = 2 * k) :
    (sqWord s x y).i = SqU6.blockRead s x
      + 2 * (-2 * x.i + y.i + 5 * (x.d * x.e) - 4 * (x.d * y.e) + k * y.e) := by
  rw [SqU6.sqWord_i, SqU6.blockRead, hyd]
  ring

end BlockRead

/-! ## 2 ⭐⭐⭐ The block equation -/

section BlockEquation

variable {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R}

/-- ⭐⭐ **THE BLOCK EQUATION, integral form.**  At every relator-killing marking over
`gr3R = ZMod 8`, at every handle count and every handle, at **every** sigma slot and with no
gauge hypothesis anywhere: the handle block's `(4,6)` coordinate is the block reading of the two
core slots, up to a multiple of `2`.

Two of the fifteen relator rows are used and no more: the `(4,6)`-row, through the committed
`SqU6.handleWord_i_of_relator`, and the `(4,5)`-row, which forces the `x1` slot's `(4,5)`-column
even.  The `(5,6)`-row would do the second one's job equally well. -/
theorem SqU6.handleWord_i_eq_blockRead_of_relator (hrel : sqRelWord m = 1) :
    ∃ t : gr3R, (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).i
      = SqU6.blockRead (m 0) (m 1) + 2 * t := by
  have hd : -(4 * (m 1).d) + 2 * (m 2).d = 0 := by
    have h0 : (sqRelWord m).d = 0 := by rw [hrel]; rfl
    rw [SqU6.sqRelWord_d] at h0
    linear_combination h0
  obtain ⟨kd, hkd⟩ := abelRow_even _ _ hd
  refine ⟨-(SqU6.blockRead (m 0) (m 1))
    - (-2 * (m 1).i + (m 2).i + 5 * ((m 1).d * (m 1).e) - 4 * ((m 1).d * (m 2).e)
        + kd * (m 2).e), ?_⟩
  rw [SqU6.handleWord_i_of_relator hrel, SqU6.sqWord_i_eq_blockRead _ _ _ hkd]
  ring

/-- ⭐⭐⭐ **THE BLOCK EQUATION.**  The parity of the handle block's `(4,6)` coordinate is a
closed form in four entries of the two core slots, at every relator-killing marking over
`gr3R`, at every handle count, at every sigma slot, with no gauge.

The direction wave 59 does not have is the interesting one: it says an **odd** block reading
forces an **odd** block coordinate, so the block coordinate is not merely bounded but *read*. -/
theorem SqU6.selPar_handleWord_i_of_relator (hrel : sqRelWord m = 1) :
    selPar (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).i
      = selPar (SqU6.blockRead (m 0) (m 1)) := by
  obtain ⟨t, ht⟩ := SqU6.handleWord_i_eq_blockRead_of_relator hrel
  rw [ht, selPar_add, selPar_two_mul, add_zero]

/-- ⭐⭐ **The converse of wave 59's parity, which is the new content.**
`SqU6.handleWord_i_even_of_relator` carries the hypothesis
`(m 0).d * (m 1).e - (m 0).e * (m 1).d = 2 * t`, which is literally "the block reading is even",
and concludes the block coordinate is even.  Here is the other half. -/
theorem SqU6.handleWord_i_odd_of_relator (hrel : sqRelWord m = 1)
    (hodd : selPar (SqU6.blockRead (m 0) (m 1)) = 1) :
    selPar (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).i = 1 :=
  (SqU6.selPar_handleWord_i_of_relator hrel).trans hodd

/-- **The honest control**, and the reason the collapse of section 4 is cheap: the relator pins
the **whole** block element, not merely its `(4,6)` coordinate.  So every functional of the
handle block is a functional of the three core slots at a relator-killing marking, and the
content of the block equation is not that fact but the **closed form** - four core entries out
of thirty, with no evaluation of the core word. -/
theorem SqU6.handleWord_eq_inv_sqWord_of_relator {R : Type} [CommRing R]
    {m : Fin (sqRank h) → SqU6 R} (hrel : sqRelWord m = 1) :
    handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))
      = (sqWord (m 0) (m 1) (m 2))⁻¹ :=
  (inv_eq_iff_mul_eq_one.mpr hrel).symm

end BlockEquation

/-! ## 3 ⭐⭐ The handle-count forcing -/

section HandleForcing

private theorem zmodTwo_eq_zero_of_ne_one : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide

/-- ⭐⭐ **At `h = 0` the block reading is forced even.**  There is no block, so the equation of
section 2 reads `blockRead = 2 * (-t)`.  No gauge, no sigma-slot hypothesis, no condition on the
`x1` slot. -/
theorem SqU6.blockRead_even_of_relator_handleFree {m : Fin (sqRank 0) → SqU6 gr3R}
    (hrel : sqRelWord m = 1) : ∃ t : gr3R, SqU6.blockRead (m 0) (m 1) = 2 * t := by
  obtain ⟨t, ht⟩ := SqU6.handleWord_i_eq_blockRead_of_relator hrel
  rw [handleWord_zero, SqU6.one_i] at ht
  exact ⟨-t, by linear_combination -ht⟩

/-- ⭐⭐ **THE HANDLE-COUNT FORCING.**  A relator-killing marking whose block reading is odd
has a **positive** handle count.  Every committed statement of the lane that mentions the handle
count takes `0 < h` as a **hypothesis** (`EichRefutation.not_sqEichRelWord`,
`PivotClimb.not_sqPivotUnitizer`, and the rest); this one **produces** it, and the datum it reads
is a `2 x 2` minor of the two core slots in the two outer abelian columns - class-one data,
below everything the committed instruments look at. -/
theorem SqU6.pos_of_blockRead_odd {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R}
    (hrel : sqRelWord m = 1) (hodd : selPar (SqU6.blockRead (m 0) (m 1)) = 1) : 0 < h := by
  rcases Nat.eq_zero_or_pos h with rfl | hp
  · obtain ⟨t, ht⟩ := SqU6.blockRead_even_of_relator_handleFree hrel
    rw [ht, selPar_two_mul] at hodd
    exact absurd hodd (by decide)
  · exact hp

/-- ⭐ **…and it is one handle in particular.**  `SqU6.handleWord_i` writes the block coordinate
as a sum of `2 x 2` minors, one per handle, in the columns `(4,5)` and `(5,6)`.  An odd block
reading therefore forces some handle whose two letters are **independent mod `2`** in those two
columns: an odd minor is exactly independence over `F_2`. -/
theorem SqU6.exists_handle_minor_odd {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R}
    (hrel : sqRelWord m = 1) (hodd : selPar (SqU6.blockRead (m 0) (m 1)) = 1) :
    ∃ j : Fin h, selPar ((m (sqHandleIdxU j)).d * (m (sqHandleIdxV j)).e
      - (m (sqHandleIdxV j)).d * (m (sqHandleIdxU j)).e) = 1 := by
  by_contra hcon
  have hall : ∀ j : Fin h, ∃ t : gr3R, (m (sqHandleIdxU j)).d * (m (sqHandleIdxV j)).e
      - (m (sqHandleIdxV j)).d * (m (sqHandleIdxU j)).e = 2 * t := fun j =>
    (selPar_eq_zero_iff _).mp (zmodTwo_eq_zero_of_ne_one _ (not_exists.mp hcon j))
  choose t ht using hall
  have hsum : (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).i
      = 2 * ∑ j, t j := by
    rw [SqU6.handleWord_i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => ht j
  have hz := SqU6.selPar_handleWord_i_of_relator hrel
  rw [hsum, selPar_two_mul] at hz
  exact absurd (hz.trans hodd) (by decide)

/-- ⭐⭐ **The forcing in the campaign's usual shape**: a sigma dressing that keeps the relator
killed must have an **even** bit, the bit being its own pairing against the `x0` slot in the two
outer abelian columns.  The handle letters are untouched by a sigma dressing, so the block
coordinate cannot move, so the block reading cannot move either.

⚠ Scope, stated because it decides what this is worth: the diagonal dressing `v = m 1` meets the
conclusion outright (the minor of a slot against itself is `0`), and so does every
`gamma_2`-dressing (`d`- and `e`-columns vanish).  The forcing bites exactly on **abelian**
dressings, a channel no committed forcing reads and not the channel the committed exclusions run
on. -/
theorem SqU6.selPar_blockRead_dress_of_relator {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R}
    {v : SqU6 gr3R} (hrel : sqRelWord m = 1) (hrel' : sqRelWord (sigFiveDress m v) = 1) :
    selPar (v.d * (m 1).e - v.e * (m 1).d) = 0 := by
  have hU : ∀ j : Fin h, sigFiveDress m v (sqHandleIdxU j) = m (sqHandleIdxU j) := fun j =>
    sigFiveDress_handleU j
  have hV : ∀ j : Fin h, sigFiveDress m v (sqHandleIdxV j) = m (sqHandleIdxV j) := fun j =>
    sigFiveDress_handleV j
  have e2 := SqU6.selPar_handleWord_i_of_relator hrel'
  rw [funext hU, funext hV, sigFiveDress_zero, sigFiveDress_one,
    SqU6.selPar_handleWord_i_of_relator hrel] at e2
  have hsplit : SqU6.blockRead (m 0 * v) (m 1)
      = SqU6.blockRead (m 0) (m 1) + (v.d * (m 1).e - v.e * (m 1).d) := by
    simp only [SqU6.blockRead, SqU6.mul_d, SqU6.mul_e]
    ring
  rw [hsplit, selPar_add] at e2
  linear_combination -e2

end HandleForcing

/-! ## 4 ⭐⭐⭐ The class-five selection bit collapses onto the core slots -/

section Collapse

variable {R : Type} [CommRing R]

/-- **The class-three sigma coupling** the class-five top row reads the handle block through:
the response of the core word's `(1,4)` row to a sigma dressing, `GradedFive.SqU6.sqWord_j_dress`
named. -/
def SqU6.blockCoupling (v s x : SqU6 R) : R :=
  v.a * x.g - v.g * x.a + v.f * x.c - v.c * x.f - s.b * (v.a * x.c + v.c * x.a)

theorem SqU6.sqWord_j_dress_blockCoupling (s v x y : SqU6 R) (hxb : x.b = 0) (hyb : y.b = 0)
    (hvb : v.b = 0) :
    (sqWord (s * v) x y).j - (sqWord s x y).j = SqU6.blockCoupling v s x :=
  SqU6.sqWord_j_dress s v x y hxb hyb hvb

/-- The committed coupling identity `GradedFive.SqU6.sqRelWord_sigFiveDress_o`, with the
coefficient named. -/
theorem SqU6.sqRelWord_sigFiveDress_o_blockCoupling {h : ℕ} {m : Fin (sqRank h) → SqU6 R}
    {v : SqU6 R} (hxb : (m 1).b = 0) (hyb : (m 2).b = 0) (hvb : v.b = 0) :
    (sqRelWord (sigFiveDress m v)).o - (sqRelWord m).o
      = ((sqWord (m 0 * v) (m 1) (m 2)).o - (sqWord (m 0) (m 1) (m 2)).o)
        + SqU6.blockCoupling v (m 0) (m 1)
          * (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).i :=
  SqU6.sqRelWord_sigFiveDress_o hxb hyb hvb

variable {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R} {v : SqU6 gr3R}

/-- ⭐⭐⭐ **THE COLLAPSE.**  At every relator-killing marking over `gr3R`, on the `nu'`-gauge,
at **every** sigma slot and at every handle count, the class-five selection bit of the relator's
response to a sigma dressing is

```text
selPar (Delta_v core word top row)  +  selPar (coupling)  *  selPar (blockRead)
```

and every symbol in it is a **core slot**.  The handle letters have been eliminated.

Wave 59's `SqU6.selPar_sqRelWord_sigFiveDress_o` is the instance at a sigma slot with vanishing
`(4,5)`- and `(5,6)`-columns, where the second summand is `0` by
`SqU6.blockRead_eq_zero_of_slot`; and wave 59's counterexample is the instance where it is `1`,
which is why the bit separates there.  Neither needs the handle block. -/
theorem SqU6.selPar_sqRelWord_sigFiveDress_o_core (hrel : sqRelWord m = 1)
    (hxb : (m 1).b = 0) (hyb : (m 2).b = 0) (hvb : v.b = 0) :
    selPar ((sqRelWord (sigFiveDress m v)).o - (sqRelWord m).o)
      = selPar ((sqWord (m 0 * v) (m 1) (m 2)).o - (sqWord (m 0) (m 1) (m 2)).o)
        + selPar (SqU6.blockCoupling v (m 0) (m 1)) * selPar (SqU6.blockRead (m 0) (m 1)) := by
  obtain ⟨t, ht⟩ := SqU6.handleWord_i_eq_blockRead_of_relator hrel
  rw [SqU6.sqRelWord_sigFiveDress_o_blockCoupling hxb hyb hvb, ht, selPar_add, selPar_mul,
    selPar_add, selPar_two_mul, add_zero]

/-- ⭐⭐⭐ **THE CLASS-FIVE BIT IS BLIND TO THE HANDLE BLOCK, EVERYWHERE.**  Two relator-killing
markings with the same three core slots have the same class-five selection bit - at **different
handle counts**, with **different handle letters**, and with **no hypothesis on the sigma slot**.

This is the statement wave 57 proved at class four by an identity and wave 59 proved at class
five only at the committed sigma slot.  The mechanism is neither: among relator-killing markings
the block is not an independent datum at all. -/
theorem SqU6.selPar_sqRelWord_sigFiveDress_o_eq_of_core {h' : ℕ}
    {m' : Fin (sqRank h') → SqU6 gr3R} (hrel : sqRelWord m = 1) (hrel' : sqRelWord m' = 1)
    (h0 : m' 0 = m 0) (h1 : m' 1 = m 1) (h2 : m' 2 = m 2)
    (hxb : (m 1).b = 0) (hyb : (m 2).b = 0) (hvb : v.b = 0) :
    selPar ((sqRelWord (sigFiveDress m v)).o - (sqRelWord m).o)
      = selPar ((sqRelWord (sigFiveDress m' v)).o - (sqRelWord m').o) := by
  rw [SqU6.selPar_sqRelWord_sigFiveDress_o_core hrel hxb hyb hvb,
    SqU6.selPar_sqRelWord_sigFiveDress_o_core hrel' (by rw [h1]; exact hxb)
      (by rw [h2]; exact hyb) hvb, h0, h1, h2]

/-- ⭐ **Wave 59's committed blindness theorem, recovered from the collapse.**  At a sigma slot
with vanishing `(4,5)`- and `(5,6)`-columns the block channel is `0`, so the relator's bit is the
core word's.  `SqU6.selPar_sqRelWord_sigFiveDress_o` proves this from the block's evenness; here
it is the `blockRead = 0` instance of a statement that also covers the odd case. -/
theorem SqU6.selPar_sqRelWord_sigFiveDress_o_of_slot (hrel : sqRelWord m = 1)
    (hsd : (m 0).d = 0) (hse : (m 0).e = 0)
    (hxb : (m 1).b = 0) (hyb : (m 2).b = 0) (hvb : v.b = 0) :
    selPar ((sqRelWord (sigFiveDress m v)).o - (sqRelWord m).o)
      = selPar ((sqWord (m 0 * v) (m 1) (m 2)).o - (sqWord (m 0) (m 1) (m 2)).o) := by
  rw [SqU6.selPar_sqRelWord_sigFiveDress_o_core hrel hxb hyb hvb,
    SqU6.blockRead_eq_zero_of_slot hsd hse, selPar_zero, mul_zero, add_zero]

end Collapse

/-! ## 5 ⭐⭐ Soundness: the block channel sits below the achievable lattice -/

section BelowLattice

variable {R : Type} [CommRing R]

/-- **A `gamma_2`-dressing of either core slot cannot move the block reading**, because every
`gamma_2`-element has vanishing abelian columns and the reading is built from two of them. -/
theorem SqU6.blockRead_gaTwoDress (s x z w : SqU6 R) (hzd : z.d = 0) (hze : z.e = 0)
    (hwd : w.d = 0) (hwe : w.e = 0) :
    SqU6.blockRead (s * z) (x * w) = SqU6.blockRead s x := by
  simp only [SqU6.blockRead, SqU6.mul_d, SqU6.mul_e, hzd, hze, hwd, hwe]
  ring

theorem SqU6.blockRead_gaThreeDress (s x z w : SqU6 R) (hz : z.IsGaThree) (hw : w.IsGaThree) :
    SqU6.blockRead (s * z) (x * w) = SqU6.blockRead s x :=
  SqU6.blockRead_gaTwoDress s x z w hz.2.2.2.1 hz.2.2.2.2.1 hw.2.2.2.1 hw.2.2.2.2.1

/-- **A `gamma_3`-dressing of either core slot cannot move the coupling either**: the coupling
reads the `x0` slot's `(1,2)`, `(3,4)`, `(1,3)` and `(2,4)` entries and the sigma slot's
`nu'`-column, all of class `<= 2`. -/
theorem SqU6.blockCoupling_gaThreeDress (v s x z w : SqU6 R) (hz : z.IsGaThree)
    (hw : w.IsGaThree) :
    SqU6.blockCoupling v (s * z) (x * w) = SqU6.blockCoupling v s x := by
  obtain ⟨_, zb, _, _, _, _, _, _, _⟩ := hz
  obtain ⟨wa, wb, wc, _, _, wf, wg, _, _⟩ := hw
  simp only [SqU6.blockCoupling, SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_f, SqU6.mul_g,
    zb, wa, wb, wc, wf, wg]
  ring

/-- ⭐⭐ **THE BLOCK CHANNEL IS REFINEMENT-PROOF.**  Its contribution to the class-five
selection bit is unchanged by a `gamma_3`-dressing of the sigma slot and of the `x0` slot, with
no soundness chain, no even-column hypothesis and no covector condition.

The campaign's achievable refinements are `gamma_4`-shaped at class five
(`GradedFiveForce.forceLcs_three_le_forceN4`) and `gamma_3`-shaped one filtration step wider
(`GradedFiveStageFour.forceLcs_two_le_stageN3`), and both are inside `gamma_3`; the block
channel is read at class **two**, below all of it.  In particular there is no analogue here of
wave 59's stage-four hole, where a `gamma_3`-move of the point's own letters killed the dressed
frame. -/
theorem SqU6.blockChannel_gaThreeDress (v s x z w : SqU6 gr3R) (hz : z.IsGaThree)
    (hw : w.IsGaThree) :
    selPar (SqU6.blockCoupling v (s * z) (x * w)) * selPar (SqU6.blockRead (s * z) (x * w))
      = selPar (SqU6.blockCoupling v s x) * selPar (SqU6.blockRead s x) := by
  rw [SqU6.blockCoupling_gaThreeDress v s x z w hz hw, SqU6.blockRead_gaThreeDress s x z w hz hw]

end BelowLattice

/-! ## 6 The committed points, and the concrete handle-count separation -/

section Points

/-- The block reading at wave 59's counterexample slots: `-1`, and **odd**. -/
theorem blindCex_blockRead : SqU6.blockRead blindCexS blindCexX = 7 := by decide

theorem blindCex_blockRead_odd : selPar (SqU6.blockRead blindCexS blindCexX) = 1 := by decide

/-- ⭐⭐ **Wave 59's counterexample, explained.**  The committed `blindCex_handleWord_i` says
the block coordinate there is `1`; the block equation **predicts** it, from the counterexample's
own core slots and nothing else.  So the odd block is not a free datum the bit discovered: it is
the sigma slot's own minor against the `x0` slot. -/
theorem blindCex_block_equation (h : ℕ) (j : Fin h) :
    selPar (handleWord (fun j' => blindCexMark h j (sqHandleIdxU j'))
        (fun j' => blindCexMark h j (sqHandleIdxV j'))).i = 1 := by
  rw [SqU6.selPar_handleWord_i_of_relator (sqRelWord_blindCexMark h j)]
  simp only [blindCexMark, fiveTuple_zero, fiveTuple_one]
  exact blindCex_blockRead_odd

/-- …and it agrees with the committed value, by kernel computation, which is the composite check
the doctrine asks for. -/
theorem blindCex_block_equation_crosscheck (h : ℕ) (j : Fin h) :
    selPar (handleWord (fun j' => blindCexMark h j (sqHandleIdxU j'))
        (fun j' => blindCexMark h j (sqHandleIdxV j'))).i
      = selPar (1 : gr3R) := by
  rw [blindCex_handleWord_i h j]

/-- ⭐⭐⭐ **A CORE-SLOT PAIR THAT REQUIRES A HANDLE.**  Wave 59's counterexample sigma slot and
`x0` slot admit a relator-killing marking at **every** handle count `h >= 1` and every handle
(the committed `sqRelWord_blindCexMark`), and admit **none** at `h = 0`, whatever the `x1` slot
is.  Proved, not measured: a pair of core slots on which the two cases genuinely differ. -/
theorem blindCexCore_not_relator_handleFree (m : Fin (sqRank 0) → SqU6 gr3R)
    (h0 : m 0 = blindCexS) (h1 : m 1 = blindCexX) : sqRelWord m ≠ 1 := by
  intro hrel
  exact absurd (SqU6.pos_of_blockRead_odd hrel
    (by rw [h0, h1]; exact blindCex_blockRead_odd)) (lt_irrefl 0)

/-- The live class-five point of `GradedFive` sits at the other extreme: its sigma slot is
trivial, so the block reading is `0` and the block coordinate is even - which is the committed
`liveFive_handleWord_i = 2`, again predicted rather than computed. -/
theorem liveFive_blockRead : SqU6.blockRead (1 : SqU6 gr3R) fiveX = 0 :=
  SqU6.blockRead_eq_zero_of_slot rfl rfl

theorem liveFive_block_equation (h : ℕ) (j : Fin h) :
    selPar (handleWord (fun j' => liveFiveMark h j (sqHandleIdxU j'))
        (fun j' => liveFiveMark h j (sqHandleIdxV j'))).i = 0 := by
  rw [SqU6.selPar_handleWord_i_of_relator (sqRelWord_liveFiveMark h j)]
  simp only [liveFiveMark, fiveTuple_zero, fiveTuple_one]
  rw [liveFive_blockRead, selPar_zero]

end Points

/-! ## 7 Axiom pins

Committed prints for every public declaration: all **std-3** (`propext`, `Classical.choice`,
`Quot.sound`) or a subset; no census axiom is reachable.  Every `decide` is on `ZMod 8` or
`ZMod 2`. -/

section AxiomPins

#print axioms SqU6.blockRead
#print axioms SqU6.blockRead_def
#print axioms SqU6.blockRead_eq_zero_of_slot
#print axioms SqU6.blockRead_sigFiveMark
#print axioms SqU6.sqWord_i_eq_blockRead
#print axioms SqU6.handleWord_i_eq_blockRead_of_relator
#print axioms SqU6.selPar_handleWord_i_of_relator
#print axioms SqU6.handleWord_i_odd_of_relator
#print axioms SqU6.handleWord_eq_inv_sqWord_of_relator
#print axioms SqU6.blockRead_even_of_relator_handleFree
#print axioms SqU6.pos_of_blockRead_odd
#print axioms SqU6.exists_handle_minor_odd
#print axioms SqU6.selPar_blockRead_dress_of_relator
#print axioms SqU6.blockCoupling
#print axioms SqU6.sqWord_j_dress_blockCoupling
#print axioms SqU6.sqRelWord_sigFiveDress_o_blockCoupling
#print axioms SqU6.selPar_sqRelWord_sigFiveDress_o_core
#print axioms SqU6.selPar_sqRelWord_sigFiveDress_o_eq_of_core
#print axioms SqU6.selPar_sqRelWord_sigFiveDress_o_of_slot
#print axioms SqU6.blockRead_gaTwoDress
#print axioms SqU6.blockRead_gaThreeDress
#print axioms SqU6.blockCoupling_gaThreeDress
#print axioms SqU6.blockChannel_gaThreeDress
#print axioms blindCex_blockRead
#print axioms blindCex_blockRead_odd
#print axioms blindCex_block_equation
#print axioms blindCex_block_equation_crosscheck
#print axioms blindCexCore_not_relator_handleFree
#print axioms liveFive_blockRead
#print axioms liveFive_block_equation

end AxiomPins

end SqCore

end Dyadic

end GQ2

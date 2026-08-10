/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFive
import GQ2.Dyadic.SqCore.GradedSigmaFive

/-!
# W59-BLIND5: class-five handle blindness is arithmetic, and it is sigma-slot local

Wave 58 left two class-five statements measured and flagged "cheap once the carrier lands"
(`docs/dyadic/w58-sigma5-note.md` section 6).  The carrier landed in the same wave
(`GQ2/Dyadic/SqCore/GradedFive.lean`).  This file turns both into theorems, and finds that one
of them is **narrower than the note states**.

## Headline 1: the class-five handle-blindness theorem, and what it is NOT

⭐⭐ `SqU6.sqRelWord_sigFiveDress_handle_blind_five`.  At every relator-killing marking whose
sigma slot has vanishing `(4,5)`- and `(5,6)`-columns, over `gr3R = ZMod 8`, the class-five
sigma response of the **relator** is the class-five sigma response of the **core word** plus an
explicitly even correction:

```text
Delta_v (relator top row) = Delta_v (core word top row) + 2 * (sigFourH v x * k)
```

The block is therefore invisible to the class-five selection bit
(⭐ `SqU6.selPar_sqRelWord_sigFiveDress_o`).  The `2` is written into the statement on purpose.
Wave 57's class-four blindness is an **identity**: the block cancels from the difference of two
responses over any ring and at any marking
(`SqU6.sqRelWord_sigFiveDress_handle_blind_four`).  Nothing of that kind is true here.  The
block enters the class-five response honestly, through the coupling
`SqU6.sqRelWord_sigFiveDress_o`, and it is killed by a **parity of the forced block**, over
`ZMod 8`, at relator-killing markings only.  The statement is written so that the arithmetic is
visible in the statement rather than buried in the proof: the handle term is literally of the
form `2 * (coefficient * k)`, and dropping the relator hypothesis destroys it.

The mechanism, in three committed steps:

* ⭐ `SqU6.sqWord_i` gives the `(4,6)` row of the core word in closed form, at an **arbitrary**
  sigma slot.  It is the committed `SqU6.sqWord_f` with `(a, b, f)` replaced by `(d, e, i)`.
* ⭐ `SqU6.handleWord_i_of_relator`: the relator pins the block's `(4,6)` coordinate to minus
  the core word's, over any ring and at any handle count.
* ⭐⭐ `SqU6.handleWord_i_even_of_relator`: over `gr3R` the relator's **fourth abelian row
  alone** forces that coordinate even, once the sigma slot pairs evenly against the `x0` slot.
  One row, not two: the note uses the `(4,5)` and `(5,6)` rows, and the `(5,6)` one is not
  needed.

## ⭐⭐ Headline 2: the blindness is sigma-slot local, and that is a correction

`docs/dyadic/w58-sigma5-note.md` section 4.2 states the block parity as holding "at every
relator-killing marking, at every handle count, on every row, gauge or no gauge", from the
printed closed form

```text
W_46 = -4*x_46 + 2*y_46 + 10*x_45*x_56 - 8*x_45*y_56 + y_45*y_56.
```

That closed form is the `sigma = E_23` instance.  ⭐ `SqU6.sqWord_i` shows the general row also
carries `s_45 * x_56 - s_56 * x_45`, which the relator's abelian rows do not touch, and the
conclusion really does fail without it:

⭐⭐ `blindCex_not_handle_blind`.  At the sigma slot `E_23 * <e = 1>` - the committed sigma
marking dressed by a single `nu'`-**trivial** letter - there is a marking that kills all fifteen
relator rows at **every** handle count, whose handle block has **odd** `(4,6)` coordinate, and
at which the class-five relator response differs from the core-word reading by exactly `1`.  So
the class-five selection bit reads the handle block there
(⭐⭐ `blindCex_response`, ⭐ `blindCex_selPar_ne`).

This is a bound on the scope of the wave-58 headline, not a refutation of it: at the committed
sigma marking the blindness is a theorem (headline 1), and the class-eight forecast concerns
that marking.  What it refutes is the **unqualified** reading, and the composite it forbids is
the obvious one: a two-step comparison whose base point is already dressed leaves the committed
slot, and then the block is visible at class **five**, not class eight.  Section 4.3 of the note
derives its forecast from "for `m >= 3` the corner `(m..c+1)` misses the sigma letter `E_23`
entirely", which is the same conditional step at every class, so the forecast inherits the same
scope and no more.

## Headline 3: the class-five gauge parity theorem

⭐⭐ `SqU6.sqWord_sigFiveMark_gauge_even`.  On the class-two-forced gauge the **twelve** rows of
class at most three of the core word are even (the `b`-row vanishing outright), and
⭐⭐ `sqWord_sigFiveMark_gauge_three_odd` exhibits a gauge point at which the remaining three -
`m` (`x_15`), `n` (`x_26`), `o` (`x_16`) - are **all odd at once**.  So exactly three can be
odd, against exactly one at class four
(`GradedFourCleared.sqWord_sigFourMark_gauge_even`), and the two new ones are the class-four
rows.

Nine of the twelve rows are the committed class-four theorem read through `SqU6.toU5L`, because
⭐ `SqU6.toU5L_sigFiveMark` says the left quotient carries `E_23` to `E_23`; only the rows `e`,
`i`, `l` - the three that live in the sixth column - need class-five work.  ⭐ The transposition
is also **sharper** than the naive one: the class-two-forced gauge's two new hypotheses
`x_56` even and `x_46` even are not needed for any of the twelve, and
`SqU6.sqWord_sigFiveMark_extGauge_even` records that the faithful fourteen-hypothesis
transposition is the weaker statement.

## PROVED versus measured

**PROVED**, with no live hypothesis: everything named above.  Both class-five statements wave 58
deferred are now theorems, the counterexample is a `decide` at every handle count, and the
`a0 = a1` half is untouched (it is `GradedSigmaFive`'s, and nothing here weakens it).

**Measured** (`scripts/w59_blind5/`, certified outputs in `scripts/w59_blind5/results/`): the
transcribed `U_6` law against honest `6 x 6` matrices (`2000` comparisons, `0` mismatches) and
`sqWord` by both routes at `60` markings; the mod-2 reductions of the three top rows, which
reproduce section 4.4 of the note exactly (`W.m = y13*y35`, `W.n = x36 + y24*y46`,
`W.o = y13*y36 + y46*y14`, with nothing hidden in the note's trailing "..."); the exhaustive
`16384`-point corroboration of the block parity at the committed slot; and the layered solve
that produces the counterexample.  `35` named checks, `0` failures.

## Contents

* **1** the `(4,6)` row of the core word and of the relator, and the forced parity of the block;
* **2** the class-five sigma marking and the coupling coefficient as the committed `sigFourH`;
* **3** ⭐⭐ the class-five handle-blindness theorem, and the second, independent closure;
* **4** ⭐⭐ the counterexample that fixes its scope;
* **5** ⭐⭐ the class-five gauge parity theorem and the three rows that can be odd;
* **6** axiom pins.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`; every `decide` is on `ZMod 8`.  All prints are
**std-3** (`propext`, `Classical.choice`, `Quot.sound`) or a subset.
-/

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The `(4,6)` row, and the parity the relator forces on the handle block -/

section BlockRow

variable {R : Type} [CommRing R] {h : ℕ}

/-- **The fourth class-two row of the core word**, at an arbitrary sigma slot.  It is the
committed `SqU6.sqWord_f` with the columns `(a, b)` replaced by `(d, e)` and the class-two
coordinate `f` by `i`, which is what the `(1..3)`-corner and the `(4..6)`-corner being the same
shape amounts to.

⚠ The sigma slot does **not** drop out: the pairing `s.d * x.e - s.e * x.d` survives, and
section 4 shows it is load-bearing.  `docs/dyadic/w58-sigma5-note.md` section 4.2 prints the
`s.d = s.e = 0` instance. -/
theorem SqU6.sqWord_i (s x y : SqU6 R) :
    (sqWord s x y).i = -4 * x.i + 2 * y.i
      + (s.d * x.e - s.e * x.d + 10 * (x.d * x.e) - 8 * (x.d * y.e) + y.d * y.e) := by
  simp only [sqWord, SqU6.mul_d, SqU6.mul_i, SqU6.inv_d, SqU6.inv_e, SqU6.inv_i,
    SqU6.conjP_d, SqU6.conjP_e, SqU6.conjP_i, SqU6.pow_d, SqU6.pow_e, SqU6.pow_i,
    SqU6.commP_e, SqU6.commP_i]
  norm_num
  ring

/-- **The `(4,6)` row of the relator**: the core word's plus the block's, with no cross term,
because the handle block's fifth abelian column vanishes. -/
theorem SqU6.sqRelWord_i (m : Fin (sqRank h) → SqU6 R) :
    (sqRelWord m).i = (sqWord (m 0) (m 1) (m 2)).i
      + (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).i := by
  rw [sqRelWord, SqU6.mul_i, SqU6.handleWord_e, mul_zero, add_zero]

/-- ⭐ **The relator pins the block's `(4,6)` coordinate.**  Over any ring, at any handle count
and any handle: the coordinate the class-five top row reads the block through is minus the core
word's own `(4,6)` row.  This is the only place the relator hypothesis is used below. -/
theorem SqU6.handleWord_i_of_relator {m : Fin (sqRank h) → SqU6 R} (hrel : sqRelWord m = 1) :
    (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).i
      = -(sqWord (m 0) (m 1) (m 2)).i := by
  have hz : (0 : R) = (sqWord (m 0) (m 1) (m 2)).i
      + (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).i := by
    rw [← SqU6.sqRelWord_i, hrel, SqU6.one_i]
  linear_combination -hz

end BlockRow

section BlockParity

variable {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R}

/-- ⭐⭐ **The relator forces the block's `(4,6)` coordinate even.**  Over `gr3R = ZMod 8`, at
any handle count and any handle, with **no gauge hypothesis on the `x0` or `x1` slot** and only
the relator's **fourth** abelian row in play (the note uses two rows; one suffices).

The one hypothesis that is not free is on the **sigma slot**: its `(4,5)`- and `(5,6)`-columns
must pair evenly against the `x0` slot's.  Section 4 shows this cannot be dropped. -/
theorem SqU6.handleWord_i_even_of_relator {t : gr3R} (hrel : sqRelWord m = 1)
    (hs : (m 0).d * (m 1).e - (m 0).e * (m 1).d = 2 * t) :
    ∃ k : gr3R, (handleWord (fun j => m (sqHandleIdxU j))
      (fun j => m (sqHandleIdxV j))).i = 2 * k := by
  have hd : -(4 * (m 1).d) + 2 * (m 2).d = 0 := by
    have h0 : (sqRelWord m).d = 0 := by rw [hrel]; rfl
    rw [SqU6.sqRelWord_d] at h0
    linear_combination h0
  obtain ⟨kd, hkd⟩ := abelRow_even _ _ hd
  refine ⟨2 * (m 1).i - (m 2).i - t - 5 * ((m 1).d * (m 1).e) + 4 * ((m 1).d * (m 2).e)
    - kd * (m 2).e, ?_⟩
  rw [SqU6.handleWord_i_of_relator hrel, SqU6.sqWord_i]
  linear_combination -hs - (m 2).e * hkd

/-- The committed sigma marking meets the hypothesis outright, and so does the trivial slot the
live class-five point of `GradedFive` uses. -/
theorem SqU6.handleWord_i_even_of_relator_of_slot (hrel : sqRelWord m = 1)
    (hsd : (m 0).d = 0) (hse : (m 0).e = 0) :
    ∃ k : gr3R, (handleWord (fun j => m (sqHandleIdxU j))
      (fun j => m (sqHandleIdxV j))).i = 2 * k :=
  SqU6.handleWord_i_even_of_relator (t := 0) hrel (by rw [hsd, hse]; ring)

end BlockParity

/-! ## 2 The class-five sigma marking, and the coupling coefficient -/

section SigmaMark

variable {R : Type} [CommRing R]

variable (R) in
/-- **The class-five sigma marking** `E_23`: the unique lift of `GradedSigmaFour.sigFourMark`
along the left `U_5`-quotient. -/
def sigFiveMark : SqU6 R := ⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

@[simp] theorem sigFiveMark_b : (sigFiveMark R).b = 1 := rfl

@[simp] theorem sigFiveMark_d : (sigFiveMark R).d = 0 := rfl

@[simp] theorem sigFiveMark_e : (sigFiveMark R).e = 0 := rfl

/-- ⭐ **The left quotient carries the class-five sigma marking to the class-four one**, so
every class-`<= 4` fact about the first five columns at the class-five sigma marking is the
committed fact, verbatim. -/
theorem SqU6.toU5L_sigFiveMark : SqU6.toU5L (sigFiveMark R) = sigFourMark R := rfl

/-- **The last-four-columns corner**, `(3,4,5,6)`, as a `U_4`-quotient.  The class-five sigma
letter `E_23` misses this corner entirely, which is the structural reason the `(3,6)` row of the
core word is a **trivial-slot** class-three core and carries no sigma dependence at all. -/
def SqU6.toU4RR : SqU6 R →* SqU4 R where
  toFun p := ⟨p.c, p.d, p.e, p.h, p.i, p.l⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem SqU6.toU4RR_apply (p : SqU6 R) :
    SqU6.toU4RR p = ⟨p.c, p.d, p.e, p.h, p.i, p.l⟩ := rfl

/-- …and the class-five sigma marking dies there. -/
theorem SqU6.toU4RR_sigFiveMark : SqU6.toU4RR (sigFiveMark R) = 1 := rfl

/-- ⭐ **The `(3,6)` row of the core word at the class-five sigma marking.**  It is
`GradedThree`'s `sqU4Core` at a **trivial** sigma slot, read on the last-four-columns corner:
the marking `E_23` is invisible there.  The two monomials that survive mod `2` are
`y_34 * y_46` and `y_56 * y_35`, both killed by the class-two-forced gauge's `x1`-slot
hypotheses. -/
theorem SqU6.sqWord_l_sigFiveMark (x y : SqU6 R) :
    (sqWord (sigFiveMark R) x y).l = -4 * x.l + 2 * y.l
      + (-20 * (x.c * x.d * x.e) + 20 * (x.c * x.d * y.e) - 4 * (x.c * y.d * y.e)
        + 10 * (x.c * x.i) - 8 * (x.c * y.i) + 10 * (x.e * x.h) - 8 * (x.h * y.e)
        + y.c * y.i + y.e * y.h) := by
  have hcore : (sqWord (sigFiveMark R) x y).l
      = -4 * x.l + 2 * y.l + sqU4Core 1 (SqU6.toU4RR x) (SqU6.toU4RR y) := by
    have hm := map_sqWord (SqU6.toU4RR (R := R)) (sigFiveMark R) x y
    rw [SqU6.toU4RR_sigFiveMark] at hm
    have hf := congrArg SqU4.f hm
    rwa [SqU4.sqWord_f] at hf
  rw [hcore]
  simp only [sqU4Core, SqU6.toU4RR_apply, SqU4.one_a, SqU4.one_b, SqU4.one_c, SqU4.one_d,
    SqU4.one_e]
  ring

/-- ⭐ **The coupling coefficient of the class-five response is the committed class-four
functional.**  `GradedFive.SqU6.sqWord_j_dress` gives the class-three response at an arbitrary
sigma slot; at the class-five sigma marking it is exactly `GradedSigmaFour.sigFourH` read
through the left quotient.  So the coupling identity of
`docs/dyadic/w58-sigma5-note.md` section 4.1,
`Delta_v(top) = sigFiveRead + sigFourH * H_46`, is literally the committed `sigFourH`. -/
theorem SqU6.sqWord_j_dress_sigFiveMark (v x y : SqU6 R) (hxb : x.b = 0) (hyb : y.b = 0)
    (hvb : v.b = 0) :
    (sqWord (sigFiveMark R * v) x y).j - (sqWord (sigFiveMark R) x y).j
      = sigFourH (SqU6.toU5L v) (SqU6.toU5L x) := by
  rw [SqU6.sqWord_j_dress _ _ _ _ hxb hyb hvb]
  simp only [sigFourH, SqU6.toU5L_apply, sigFiveMark]
  ring

end SigmaMark

/-! ## 3 ⭐⭐ The class-five handle-blindness theorem -/

section BlindFive

variable {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R} {v : SqU6 gr3R}

/-- ⭐⭐ **THE CLASS-FIVE HANDLE-BLINDNESS THEOREM.**  At every relator-killing marking whose
sigma slot has vanishing `(4,5)`- and `(5,6)`-columns, on the `nu'`-gauge, the class-five sigma
response of the relator is the class-five sigma response of the core word plus `2` times the
coupling coefficient times an integer.  The handle block contributes, and contributes evenly.

The `2` is in the statement deliberately.  At class four the corresponding statement is an
identity with no arithmetic in it at all
(`SqU6.sqRelWord_sigFiveDress_handle_blind_four`): the block cancels over any ring at any
marking.  Here it does not cancel; it is killed by the parity of the block coordinate that the
relator itself forces (`SqU6.handleWord_i_even_of_relator`), which is a fact about `ZMod 8` and
about relator-killing markings, and about nothing else.  Removing `hrel` removes the theorem,
and section 4 removes `hsd`, `hse` and the theorem with them. -/
theorem SqU6.sqRelWord_sigFiveDress_handle_blind_five (hrel : sqRelWord m = 1)
    (hsd : (m 0).d = 0) (hse : (m 0).e = 0)
    (hxb : (m 1).b = 0) (hyb : (m 2).b = 0) (hvb : v.b = 0) :
    ∃ k : gr3R,
      (sqRelWord (sigFiveDress m v)).o - (sqRelWord m).o
        = ((sqWord (m 0 * v) (m 1) (m 2)).o - (sqWord (m 0) (m 1) (m 2)).o)
          + 2 * ((v.a * (m 1).g - v.g * (m 1).a + v.f * (m 1).c - v.c * (m 1).f
              - (m 0).b * (v.a * (m 1).c + v.c * (m 1).a)) * k) := by
  obtain ⟨k, hk⟩ := SqU6.handleWord_i_even_of_relator_of_slot hrel hsd hse
  refine ⟨k, ?_⟩
  rw [SqU6.sqRelWord_sigFiveDress_o hxb hyb hvb, hk]
  ring

/-- ⭐⭐ …at the committed sigma marking, in the shape the wave-58 note states: the class-five
reading of the core word, plus the committed class-four functional `sigFourH` against an **even**
block coordinate. -/
theorem SqU6.sqRelWord_sigFiveDress_handle_blind_five_mark (hrel : sqRelWord m = 1)
    (hs0 : m 0 = sigFiveMark gr3R)
    (hxb : (m 1).b = 0) (hyb : (m 2).b = 0) (hvb : v.b = 0) :
    ∃ k : gr3R,
      (sqRelWord (sigFiveDress m v)).o - (sqRelWord m).o
        = ((sqWord (sigFiveMark gr3R * v) (m 1) (m 2)).o
            - (sqWord (sigFiveMark gr3R) (m 1) (m 2)).o)
          + sigFourH (SqU6.toU5L v) (SqU6.toU5L (m 1)) * (2 * k) := by
  obtain ⟨k, hk⟩ := SqU6.handleWord_i_even_of_relator_of_slot hrel
    (by rw [hs0]; rfl) (by rw [hs0]; rfl)
  refine ⟨k, ?_⟩
  rw [SqU6.sqRelWord_sigFiveDress_o hxb hyb hvb, hk, hs0]
  simp only [sigFourH, SqU6.toU5L_apply, sigFiveMark]
  ring

/-- ⭐ **…and therefore the class-five selection bit does not read the handle block.**  The
parity of the relator's class-five response is the parity of the core word's, at every
relator-killing marking with a committed-shaped sigma slot. -/
theorem SqU6.selPar_sqRelWord_sigFiveDress_o (hrel : sqRelWord m = 1)
    (hsd : (m 0).d = 0) (hse : (m 0).e = 0)
    (hxb : (m 1).b = 0) (hyb : (m 2).b = 0) (hvb : v.b = 0) :
    selPar ((sqRelWord (sigFiveDress m v)).o - (sqRelWord m).o)
      = selPar ((sqWord (m 0 * v) (m 1) (m 2)).o - (sqWord (m 0) (m 1) (m 2)).o) := by
  obtain ⟨k, hk⟩ := SqU6.sqRelWord_sigFiveDress_handle_blind_five hrel hsd hse hxb hyb hvb
  rw [hk, selPar_add, selPar_two_mul, add_zero]

/-- **The second, independent closure**, and the composite check the doctrine asks for: on the
class-two-forced gauge the coupling **coefficient** is even too, so the channel is shut twice
over and neither fact leans on the other.  This is `GradedSigmaFour.sigFourH_gauge_even` reused
one level up, through the left quotient. -/
theorem SqU6.coupling_even_of_gauge {R : Type} [CommRing R] {v x : SqU6 R} {xa xc xf xg : R}
    (hxa : x.a = 2 * xa) (hxc : x.c = 2 * xc) (hxf : x.f = 2 * xf) (hxg : x.g = 2 * xg) :
    ∃ k : R, sigFourH (SqU6.toU5L v) (SqU6.toU5L x) = 2 * k := by
  refine ⟨v.a * (xg - xc) - v.c * (xa + xf) + v.f * xc - v.g * xa, ?_⟩
  simp only [sigFourH, SqU6.toU5L_apply]
  rw [hxa, hxc, hxf, hxg]
  ring

/-- ⭐ **Composite check against the committed live class-five point.**  `GradedFive`'s live
point kills all fifteen relator rows, sits on the `nu'`-gauge, and has sigma slot `1`, so the
general theorem applies and predicts that the class-five bit cannot separate the relator's
response from the core word's.  `GradedFive.liveFive_response` independently computes the
correction there to be exactly `2`, which is even: the structural route and the machine route
meet.  It is also the sharpest statement the point admits, since `2` is not `0` - the block
does contribute, and it is the parity and only the parity that hides it. -/
theorem liveFive_selPar_handle_blind (h : ℕ) (j : Fin h) :
    selPar ((sqRelWord (sigFiveDress (liveFiveMark h j) fiveDress)).o
        - (sqRelWord (liveFiveMark h j)).o)
      = selPar ((sqWord (liveFiveMark h j 0 * fiveDress) (liveFiveMark h j 1)
            (liveFiveMark h j 2)).o
          - (sqWord (liveFiveMark h j 0) (liveFiveMark h j 1) (liveFiveMark h j 2)).o) := by
  obtain ⟨-, -, -, hxb, hyb, hvb⟩ := liveFiveMark_gauge h j
  exact SqU6.selPar_sqRelWord_sigFiveDress_o (sqRelWord_liveFiveMark h j)
    (by simp only [liveFiveMark, fiveTuple_zero]; rfl)
    (by simp only [liveFiveMark, fiveTuple_zero]; rfl) hxb hyb hvb

end BlindFive

/-! ## 4 ⭐⭐ The sigma slot is load-bearing: a certified counterexample

One `nu'`-trivial letter away from the committed sigma marking, the block parity fails, and it
fails in a way the class-five bit reads. -/

section BlindCex

/-- The dressing letter that moves the sigma slot off the committed marking.  It is
`nu'`-trivial: its `b`-column vanishes, so no gauge hypothesis of the campaign excludes it. -/
def blindCexShift : SqU6 gr3R := ⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The sigma slot of the counterexample: the committed marking `E_23`, dressed. -/
def blindCexS : SqU6 gr3R := ⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The `x0` slot: the `(4,5)` column carries the odd datum, the `(2,4)` column switches the
class-three response on, and the `(3,6)` coordinate fixes the class-four row. -/
def blindCexX : SqU6 gr3R := ⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩

/-- The `x1` slot: the layered solve of the remaining fourteen rows against the live block. -/
def blindCexY : SqU6 gr3R := ⟨0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 1, 2, 0, 1, 0⟩

/-- The `u`-letter of the live handle. -/
def blindCexU : SqU6 gr3R := ⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The `v`-letter of the live handle.  `[U, V]` is the `(4,6)` generator, so the block
coordinate the class-five top row reads is `1`, and odd. -/
def blindCexV : SqU6 gr3R := ⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The sigma dressing: the first abelian column alone, `nu'`-trivial. -/
def blindCexDress : SqU6 gr3R := ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- ⭐⭐ **The counterexample marking**, at every handle count and every handle. -/
def blindCexMark (h : ℕ) (j : Fin h) : Fin (sqRank h) → SqU6 gr3R :=
  fiveTuple gr3R h j blindCexS blindCexX blindCexY blindCexU blindCexV

/-- The sigma slot really is the committed marking moved by one `nu'`-trivial letter. -/
theorem blindCexS_eq : blindCexS = sigFiveMark gr3R * blindCexShift ∧ blindCexShift.b = 0 := by
  refine ⟨?_, rfl⟩
  simp only [blindCexS, blindCexShift, sigFiveMark]
  decide

/-- ⭐⭐ **All fifteen relator rows die**, at every handle count and every handle. -/
theorem sqRelWord_blindCexMark (h : ℕ) (j : Fin h) : sqRelWord (blindCexMark h j) = 1 := by
  rw [blindCexMark, sqRelWord_fiveTuple]
  decide

/-- ⭐⭐ **…and the handle block's `(4,6)` coordinate is ODD there**, which
`SqU6.handleWord_i_even_of_relator` forbids at the committed sigma slot. -/
theorem blindCex_handleWord_i (h : ℕ) (j : Fin h) :
    (handleWord (fun j' => blindCexMark h j (sqHandleIdxU j'))
      (fun j' => blindCexMark h j (sqHandleIdxV j'))).i = 1 := by
  rw [blindCexMark, fiveTuple_handleWord]
  decide

theorem blindCexMark_gauge (h : ℕ) (j : Fin h) :
    (blindCexMark h j 1).b = 0 ∧ (blindCexMark h j 2).b = 0 ∧ blindCexDress.b = 0 := by
  refine ⟨?_, ?_, rfl⟩ <;>
    simp only [blindCexMark, fiveTuple_one, fiveTuple_two] <;> rfl

/-- The class-three sigma response at the counterexample point, in the shape
`SqU6.sqRelWord_sigFiveDress_o` produces it: the unit `1`, so the coupling coefficient is odd
as well as the block coordinate. -/
theorem blindCexDress_weight :
    blindCexDress.a * blindCexX.g - blindCexDress.g * blindCexX.a
        + blindCexDress.f * blindCexX.c - blindCexDress.c * blindCexX.f
        - blindCexS.b * (blindCexDress.a * blindCexX.c + blindCexDress.c * blindCexX.a)
      = 1 := by decide

/-- ⭐⭐ **The class-five relator response differs from the core-word reading by exactly `1`.**
At every handle count and every handle.  Compare
`SqU6.sqRelWord_sigFiveDress_handle_blind_five`, which says the difference is even at a
committed-shaped sigma slot. -/
theorem blindCex_response (h : ℕ) (j : Fin h) :
    (sqRelWord (sigFiveDress (blindCexMark h j) blindCexDress)).o
        - (sqRelWord (blindCexMark h j)).o
      = ((sqWord (blindCexS * blindCexDress) blindCexX blindCexY).o
          - (sqWord blindCexS blindCexX blindCexY).o) + 1 := by
  obtain ⟨hxb, hyb, hvb⟩ := blindCexMark_gauge h j
  rw [SqU6.sqRelWord_sigFiveDress_o hxb hyb hvb, blindCex_handleWord_i]
  simp only [blindCexMark, fiveTuple_zero, fiveTuple_one, fiveTuple_two]
  rw [blindCexDress_weight]
  ring

/-- ⭐⭐ **The class-five handle-blindness theorem is FALSE without its sigma-slot hypothesis.**
The exact negation of `SqU6.sqRelWord_sigFiveDress_handle_blind_five`'s conclusion, at a marking
that satisfies every one of its other hypotheses. -/
theorem blindCex_not_handle_blind (h : ℕ) (j : Fin h) :
    ¬ ∃ k : gr3R,
      (sqRelWord (sigFiveDress (blindCexMark h j) blindCexDress)).o
          - (sqRelWord (blindCexMark h j)).o
        = ((sqWord (blindCexS * blindCexDress) blindCexX blindCexY).o
            - (sqWord blindCexS blindCexX blindCexY).o) + 2 * k := by
  have hodd : ∀ k : gr3R, (1 : gr3R) ≠ 2 * k := by decide
  rintro ⟨k, hk⟩
  have hone : (1 : gr3R) = 2 * k := by
    have := blindCex_response h j
    linear_combination hk - this
  exact hodd k hone

/-- ⭐ …and the class-five **selection bit** separates the two, so this is visibility and not
only an off-by-an-odd-number. -/
theorem blindCex_selPar_ne (h : ℕ) (j : Fin h) :
    selPar ((sqRelWord (sigFiveDress (blindCexMark h j) blindCexDress)).o
        - (sqRelWord (blindCexMark h j)).o)
      ≠ selPar ((sqWord (blindCexS * blindCexDress) blindCexX blindCexY).o
          - (sqWord blindCexS blindCexX blindCexY).o) := by
  rw [blindCex_response h j, selPar_add, selPar_one]
  intro hcon
  exact absurd (by linear_combination hcon : (1 : ZMod 2) = 0) (by decide)

/-- **Independent check**, taken straight from `sqRelWord` by kernel computation at `h = 1`
without going through section 5 of `GradedFive` or `sqRelWord_fiveTuple`.  Wave 57's process
finding was that two correct results can compose into a false one, so the structural route and
the machine route are made to meet here. -/
theorem blindCex_decide_crosscheck :
    sqRelWord (blindCexMark 1 0) = 1 ∧
      (sqRelWord (sigFiveDress (blindCexMark 1 0) blindCexDress)).o
          - (sqRelWord (blindCexMark 1 0)).o
        = ((sqWord (blindCexS * blindCexDress) blindCexX blindCexY).o
            - (sqWord blindCexS blindCexX blindCexY).o) + 1 := by decide

end BlindCex

/-! ## 5 ⭐⭐ The class-five gauge parity theorem -/

section GaugeParity

variable {R : Type} [CommRing R] {x y : SqU6 R} {xa xc xd xe xf xg xh xi ya yc yd ye : R}

set_option maxHeartbeats 1000000 in
/-- ⭐⭐ **THE CLASS-FIVE GAUGE PARITY THEOREM.**  On the class-two-forced gauge - the `x0`
slot's abelian columns `a, c, d` and its three lower class-two coordinates `f, g, h` even with
vanishing `b`-column, the `x1` slot's abelian columns `a, c, d, e` even with vanishing
`b`-column - **every one of the twelve rows of class at most three** of
`sqWord (sigFiveMark R) x y` is even, and the `b`-row vanishes outright.

Nine of the twelve are `GradedFourCleared.sqWord_sigFourMark_gauge_even` read through
`SqU6.toU5L`, which is legitimate because `SqU6.toU5L_sigFiveMark` carries the class-five sigma
marking to the class-four one; only `e`, `i`, `l` - the rows living in the sixth column - are
class-five work, and the closed forms behind them are
`SqU6.sqWord_e`, `SqU6.sqWord_i` and `sqU4Core` at a trivial sigma slot.

⭐ Sharper than the naive transposition: the two hypotheses class four could not state,
`x_56` even and `x_46` even, are **not used**.  See `SqU6.sqWord_sigFiveMark_extGauge_even`. -/
theorem SqU6.sqWord_sigFiveMark_gauge_even
    (hxa : x.a = 2 * xa) (hxb : x.b = 0) (hxc : x.c = 2 * xc) (hxd : x.d = 2 * xd)
    (hxf : x.f = 2 * xf) (hxg : x.g = 2 * xg) (hxh : x.h = 2 * xh)
    (hya : y.a = 2 * ya) (hyb : y.b = 0) (hyc : y.c = 2 * yc) (hyd : y.d = 2 * yd)
    (hye : y.e = 2 * ye) :
    (∃ k : R, (sqWord (sigFiveMark R) x y).a = 2 * k) ∧
      (sqWord (sigFiveMark R) x y).b = 0 ∧
      (∃ k : R, (sqWord (sigFiveMark R) x y).c = 2 * k) ∧
      (∃ k : R, (sqWord (sigFiveMark R) x y).d = 2 * k) ∧
      (∃ k : R, (sqWord (sigFiveMark R) x y).e = 2 * k) ∧
      (∃ k : R, (sqWord (sigFiveMark R) x y).f = 2 * k) ∧
      (∃ k : R, (sqWord (sigFiveMark R) x y).g = 2 * k) ∧
      (∃ k : R, (sqWord (sigFiveMark R) x y).h = 2 * k) ∧
      (∃ k : R, (sqWord (sigFiveMark R) x y).i = 2 * k) ∧
      (∃ k : R, (sqWord (sigFiveMark R) x y).j = 2 * k) ∧
      (∃ k : R, (sqWord (sigFiveMark R) x y).k = 2 * k) ∧
      (∃ k : R, (sqWord (sigFiveMark R) x y).l = 2 * k) := by
  have hnat : SqU6.toU5L (sqWord (sigFiveMark R) x y)
      = sqWord (sigFourMark R) (SqU6.toU5L x) (SqU6.toU5L y) := by
    have hm := map_sqWord (SqU6.toU5L (R := R)) (sigFiveMark R) x y
    rwa [SqU6.toU5L_sigFiveMark] at hm
  obtain ⟨⟨ka, hka⟩, hb, ⟨kc, hkc⟩, ⟨kd, hkd⟩, ⟨kf, hkf⟩, ⟨kg, hkg⟩, ⟨kh, hkh⟩,
      ⟨kj, hkj⟩, ⟨kk, hkk⟩⟩ :=
    sqWord_sigFourMark_gauge_even (x := SqU6.toU5L x) (y := SqU6.toU5L y)
      (xa := xa) (xc := xc) (xd := xd) (xe := xf) (xf := xg) (xg := xh)
      (ya := ya) (yc := yc) (yd := yd) hxa hxb hxc hxd hxf hxg hxh hya hyb hyc hyd
  refine ⟨⟨ka, (congrArg SqU5.a hnat).trans hka⟩, (congrArg SqU5.b hnat).trans hb,
    ⟨kc, (congrArg SqU5.c hnat).trans hkc⟩, ⟨kd, (congrArg SqU5.d hnat).trans hkd⟩,
    ⟨-2 * x.e + y.e, by rw [SqU6.sqWord_e]; ring⟩,
    ⟨kf, (congrArg SqU5.e hnat).trans hkf⟩, ⟨kg, (congrArg SqU5.f hnat).trans hkg⟩,
    ⟨kh, (congrArg SqU5.g hnat).trans hkh⟩, ?_,
    ⟨kj, (congrArg SqU5.h hnat).trans hkj⟩, ⟨kk, (congrArg SqU5.i hnat).trans hkk⟩, ?_⟩
  · refine ⟨-2 * x.i + y.i + 5 * (x.d * x.e) - 8 * (x.d * ye) + y.d * ye, ?_⟩
    rw [SqU6.sqWord_i, hye]
    simp only [sigFiveMark]
    ring
  · refine ⟨-2 * x.l + y.l - 10 * (x.c * x.d * x.e) + 20 * (x.c * x.d * ye)
      - 4 * (x.c * y.d * ye) + 5 * (x.c * x.i) - 4 * (x.c * y.i) + 5 * (x.e * x.h)
      - 8 * (x.h * ye) + yc * y.i + ye * y.h, ?_⟩
    rw [SqU6.sqWord_l_sigFiveMark, hyc, hye]
    ring

/-- The faithful fourteen-hypothesis transposition of the class-four gauge, for the record: it
is the weaker statement, because the two hypotheses class four cannot express are not
consumed. -/
theorem SqU6.sqWord_sigFiveMark_extGauge_even
    (hxa : x.a = 2 * xa) (hxb : x.b = 0) (hxc : x.c = 2 * xc) (hxd : x.d = 2 * xd)
    (_hxe : x.e = 2 * xe) (hxf : x.f = 2 * xf) (hxg : x.g = 2 * xg) (hxh : x.h = 2 * xh)
    (_hxi : x.i = 2 * xi)
    (hya : y.a = 2 * ya) (hyb : y.b = 0) (hyc : y.c = 2 * yc) (hyd : y.d = 2 * yd)
    (hye : y.e = 2 * ye) :
    (∃ k : R, (sqWord (sigFiveMark R) x y).a = 2 * k) ∧
      (sqWord (sigFiveMark R) x y).b = 0 ∧
      (∃ k : R, (sqWord (sigFiveMark R) x y).c = 2 * k) ∧
      (∃ k : R, (sqWord (sigFiveMark R) x y).d = 2 * k) ∧
      (∃ k : R, (sqWord (sigFiveMark R) x y).e = 2 * k) ∧
      (∃ k : R, (sqWord (sigFiveMark R) x y).f = 2 * k) ∧
      (∃ k : R, (sqWord (sigFiveMark R) x y).g = 2 * k) ∧
      (∃ k : R, (sqWord (sigFiveMark R) x y).h = 2 * k) ∧
      (∃ k : R, (sqWord (sigFiveMark R) x y).i = 2 * k) ∧
      (∃ k : R, (sqWord (sigFiveMark R) x y).j = 2 * k) ∧
      (∃ k : R, (sqWord (sigFiveMark R) x y).k = 2 * k) ∧
      (∃ k : R, (sqWord (sigFiveMark R) x y).l = 2 * k) :=
  SqU6.sqWord_sigFiveMark_gauge_even hxa hxb hxc hxd hxf hxg hxh hya hyb hyc hyd hye

end GaugeParity

/-! ### The three rows that can be odd -/

section GaugeOdd

/-- A gauge `x0` slot: everything the gauge constrains is `0`, the `(3,6)` coordinate is `1`. -/
def gaugeOddX : SqU6 gr3R := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩

/-- A gauge `x1` slot: everything the gauge constrains is `0`, and `y_13 = y_35 = y_36 = 1`. -/
def gaugeOddY : SqU6 gr3R := ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩

/-- The point satisfies every hypothesis of `SqU6.sqWord_sigFiveMark_gauge_even`, with all
twelve halves equal to `0`. -/
theorem gaugeOddPoint_on_gauge :
    gaugeOddX.a = 2 * 0 ∧ gaugeOddX.b = 0 ∧ gaugeOddX.c = 2 * 0 ∧ gaugeOddX.d = 2 * 0 ∧
      gaugeOddX.e = 2 * 0 ∧ gaugeOddX.f = 2 * 0 ∧ gaugeOddX.g = 2 * 0 ∧ gaugeOddX.h = 2 * 0 ∧
      gaugeOddX.i = 2 * 0 ∧ gaugeOddY.a = 2 * 0 ∧ gaugeOddY.b = 0 ∧ gaugeOddY.c = 2 * 0 ∧
      gaugeOddY.d = 2 * 0 ∧ gaugeOddY.e = 2 * 0 := by decide

/-- ⭐⭐ **Exactly three rows can be odd, and all three can be odd at once.**  At class four
only the single class-four row could be odd
(`GradedFourCleared.sqWord_sigFourMark_gauge_even`); at class five the two class-four rows and
the class-five row all can, which is `docs/dyadic/w58-sigma5-note.md` section 4.4 turned into a
theorem.  Their mod-2 closed forms, derived in `scripts/w59_blind5/derive_blind5.py` and
matching the note exactly, are `y13*y35`, `x36 + y24*y46` and `y13*y36 + y46*y14`; this point
switches on `y13 = y35 = y36 = 1` and `x36 = 1`. -/
theorem sqWord_sigFiveMark_gauge_three_odd :
    selPar (sqWord (sigFiveMark gr3R) gaugeOddX gaugeOddY).m = 1 ∧
      selPar (sqWord (sigFiveMark gr3R) gaugeOddX gaugeOddY).n = 1 ∧
      selPar (sqWord (sigFiveMark gr3R) gaugeOddX gaugeOddY).o = 1 := by decide

/-- …and the twelve lower rows at the very same point are even, which is the general theorem
met by kernel computation. -/
theorem sqWord_sigFiveMark_gauge_twelve_even :
    selPar (sqWord (sigFiveMark gr3R) gaugeOddX gaugeOddY).a = 0 ∧
      selPar (sqWord (sigFiveMark gr3R) gaugeOddX gaugeOddY).b = 0 ∧
      selPar (sqWord (sigFiveMark gr3R) gaugeOddX gaugeOddY).c = 0 ∧
      selPar (sqWord (sigFiveMark gr3R) gaugeOddX gaugeOddY).d = 0 ∧
      selPar (sqWord (sigFiveMark gr3R) gaugeOddX gaugeOddY).e = 0 ∧
      selPar (sqWord (sigFiveMark gr3R) gaugeOddX gaugeOddY).f = 0 ∧
      selPar (sqWord (sigFiveMark gr3R) gaugeOddX gaugeOddY).g = 0 ∧
      selPar (sqWord (sigFiveMark gr3R) gaugeOddX gaugeOddY).h = 0 ∧
      selPar (sqWord (sigFiveMark gr3R) gaugeOddX gaugeOddY).i = 0 ∧
      selPar (sqWord (sigFiveMark gr3R) gaugeOddX gaugeOddY).j = 0 ∧
      selPar (sqWord (sigFiveMark gr3R) gaugeOddX gaugeOddY).k = 0 ∧
      selPar (sqWord (sigFiveMark gr3R) gaugeOddX gaugeOddY).l = 0 := by decide

end GaugeOdd

/-! ## 6 Axiom pins

Committed prints for every public declaration: all **std-3** (`propext`, `Classical.choice`,
`Quot.sound`) or a subset; no census axiom is reachable.  Every `decide` is on `ZMod 8`. -/

section AxiomPins

#print axioms SqU6.sqWord_i
#print axioms SqU6.sqRelWord_i
#print axioms SqU6.handleWord_i_of_relator
#print axioms SqU6.handleWord_i_even_of_relator
#print axioms SqU6.handleWord_i_even_of_relator_of_slot
#print axioms sigFiveMark
#print axioms sigFiveMark_b
#print axioms sigFiveMark_d
#print axioms sigFiveMark_e
#print axioms SqU6.toU5L_sigFiveMark
#print axioms SqU6.toU4RR
#print axioms SqU6.toU4RR_apply
#print axioms SqU6.toU4RR_sigFiveMark
#print axioms SqU6.sqWord_l_sigFiveMark
#print axioms SqU6.sqWord_j_dress_sigFiveMark
#print axioms SqU6.sqRelWord_sigFiveDress_handle_blind_five
#print axioms SqU6.sqRelWord_sigFiveDress_handle_blind_five_mark
#print axioms SqU6.selPar_sqRelWord_sigFiveDress_o
#print axioms SqU6.coupling_even_of_gauge
#print axioms liveFive_selPar_handle_blind
#print axioms blindCexShift
#print axioms blindCexS
#print axioms blindCexX
#print axioms blindCexY
#print axioms blindCexU
#print axioms blindCexV
#print axioms blindCexDress
#print axioms blindCexMark
#print axioms blindCexS_eq
#print axioms sqRelWord_blindCexMark
#print axioms blindCex_handleWord_i
#print axioms blindCexMark_gauge
#print axioms blindCexDress_weight
#print axioms blindCex_response
#print axioms blindCex_not_handle_blind
#print axioms blindCex_selPar_ne
#print axioms blindCex_decide_crosscheck
#print axioms SqU6.sqWord_sigFiveMark_gauge_even
#print axioms SqU6.sqWord_sigFiveMark_extGauge_even
#print axioms gaugeOddX
#print axioms gaugeOddY
#print axioms gaugeOddPoint_on_gauge
#print axioms sqWord_sigFiveMark_gauge_three_odd
#print axioms sqWord_sigFiveMark_gauge_twelve_even

end AxiomPins

end SqCore

end Dyadic

end GQ2

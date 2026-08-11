/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFiveGammaTwo

/-!
# W62-CHANNELS: the `gamma_2`-level exclusion, and the functional that closes it

`GradedFiveGammaTwo` proved the `gamma_2`-level translation identity at class five and reduced
the whole class-five row, modulo two, to **three channels** and nothing else
(`SqU6.sqRelWord_gaTwoDress_o_channel`, with the functional `SqU6.gaTwoShiftChan`).  It then
named the one experiment that would turn that transport into an exclusion one filtration step
wider than wave 60's:

> A `gamma_2`-level exclusion needs a point at which the three channels are even, and finding
> one is the next step, not this one.

This file runs that experiment and settles it, in the negative and structurally.

## ⭐⭐⭐ Headline: the channel functional IS the selection bit, at every usable point

`SqU6.gaTwoChannel_commP_low` and its marking-level form
`SqU6.gaTwoShiftChan_gaTwoSlotTwo_low`.  Take any marking with `stageN1` core letters and an
`x1`-slot whose `d`- and `e`-columns are even (`sqRelWord_lower_x1_even`: this is **free**,
forced by the relator's own class-one rows at any marking killing the four abelian rows, which
both frames of wave 60's separation do).  Then the commutator `[x0, x1]` of two of the marking's
own letters, placed on the `x1` slot, is an **achievable** `gamma_2`-dressing whose three-channel
value is

```text
   SqU6.gaTwoChannel [x0, x1] x1  =  x0.e * x1.f * x1.h   (mod 2),
```

which is exactly wave 58's closed form for the **class-five separation bit** of the `a0 = a1`
dressing, once `stageN1` makes `x0.a` even.  The two `F_2` functionals the campaign was hoping
to separate are the same functional.

So `SqU6.gaTwoChannel_even_bit_even`: if the three channels are even on the achievable lattice
then the separation form is **even** too, and the point cannot separate the two sigma dressings.
⚠ **The `gamma_2` route to widening wave 60's exclusion is closed, at every binder point and not
merely at wave 60's.**  This is the branch `GradedFiveGammaTwo` flagged as possible and the
campaign needed decided.

⭐ The class-two-forced gauge is **not** the hypothesis.  Neither half of the collision uses it:
the channel identity needs `stageN1` plus the two `x1`-columns the relator pins, and wave 58's
bit form was re-measured here under the same weaker hypothesis with zero exceptions (it fails at
1022 of 4000 markings only when the `x1`-columns are dropped too, `results/derive.txt` section 4).
So the negative does not evaporate off the gauge, and the escape wave 61 hoped for is not there
to be found.

## ⭐⭐ What the wave still buys: the exclusion widens for even-channel dressings

`sqRelWord_stageWit_diag_gaTwo_ne_one`.  At wave 60's binder point, at every handle count and
every handle, **no achievable `gamma_2`-dressing whose three-channel functional is even kills the
dressed frame**.  That is a genuine filtration step wider than
`GradedFiveStageFour.sqRelWord_stageWit_diag_ne_one`, with one condition attached, and it is the
sharpest form the transport supports.  `stageWit_gaTwoShiftChan_slotTwo_odd` then shows the
condition is not vacuous and not universal: it fails at the explicit achievable dressing above.

## ⭐ Wave 61's census, upgraded from measured to proved

`GradedFiveGammaTwo`'s scope note reported that at wave 60's point the functional is odd on six
of the ten commutator generators, measured in `scripts/w61_wider/results/census.txt`.
`stageWit_gaTwoShiftChan_slotTwo_odd` proves one of those six inside Lean, and it is the one
that matters: `[x0, x1]` on the `x1` slot.  `stageWit_gaTwo_forced_not_vacuous` assembles the
consequence: wave 61's forcing conclusion is **satisfied** at that dressing, so it yields no
contradiction there.

## What is proved versus what is measured

**PROVED** (this file, no `sorry`, no new axiom, no `native_decide`): all of the above.  The
channel arithmetic is over any commutative ring; the free `x1`-hypotheses and the statements at
wave 60's point are over `gr3R`.

**MEASURED** (`scripts/w62_channels/`, certified output in `results/`; `derive.txt` has 15 named
checks and 0 failures):

* that the parity triple `(m, i, l) mod 2` is a homomorphism on the achievable lattice and kills
  `gamma_3` of the image, so the whole functional is decided by the ten pairwise commutators of
  the letters (4000 lattice pairs, 4000 deeper commutators, 24000 sampled lattice elements, zero
  exceptions; the same additivity fails at 532 of 2000 unrestricted `gamma_2`-elements);
* that the class-five separation bit is `x0.a x1.g x1.i + x0.e x1.f x1.h`, in the stronger
  DIFFERENCE form that needs no relator-killing hypothesis, at 4000 gauge markings AND at 4000
  markings that keep only the `x1`-columns the relator pins, zero exceptions in both; drop those
  two columns as well and the form fails at 1022 of 4000, so the hypothesis is exactly the free
  one;
* **the exhaustive sweep** (`results/sweep_f2.txt`): all `2^20` parity patterns of the four
  letters in the five coordinates that decide the functional.  `0` of the patterns that are both
  bit-odd and compatible with the relator's own two `x1`-columns have even channels; the `2432`
  even-channel bit-odd patterns that do exist all need `x0.d`, `x0.f` or `x1.d` odd, and `x1.d`
  is pinned;
* **the marking census** (`results/census.txt`): `8000` gauge markings and `8000` markings with
  only the relator's own columns, with the HONEST difference bit rather than the closed form,
  plus **131072 honest live binder points** (undressed frame killing, `a0 = a1` frame central
  with an odd residue, every letter `stageN1`).  Target hits (channels even and bit odd): `0`,
  `0` and `0`; and `chan([x0,x1], x1)` is odd at all 131072, which is this file's verdict on
  every one of them.

## Scope, honestly

* **The one measured link.**  What is PROVED is that even channels force `x0.e * x1.f * x1.h`
  even.  That this form is the class-five separation bit is wave 58's measurement, re-measured
  here under the weakest hypothesis it needs; it is not proved in Lean, and proving it would
  need the relator's `(1,6)`-row in closed form, which no wave has built.  Every Lean statement
  below is about the FORM, and the statements at wave 60's point are checked by kernel
  computation, so nothing in the chain depends on the measurement.
* **What is NOT claimed.**  This is not a proof that no achievable `gamma_2`-dressing kills the
  dressed frame; it is a proof that the mod-two transport cannot decide it, because the
  functional it would have to kill is the bit.  Wave 61's single-slot census found no kill
  either, so the question stays open in both directions, now with a reason.
* **The remaining escape** is a marking whose `x1` slot has an odd abelian column, which the
  relator forbids at any marking killing the four abelian rows, or a bit produced by a term
  outside wave 58's form.  Both are hom-layer questions this file does not touch.
* Like `GradedFiveGammaTwo` this file works at the level of **marking tuples**: the hom layer is
  not consumed.

## Contents

* **1** the channel arithmetic and ⭐⭐⭐ `SqU6.gaTwoChannel_commP_low`;
* **2** the single-slot dressing and ⭐⭐ `SqU6.gaTwoShiftChan_gaTwoSlotTwo`;
* **3** ⭐⭐⭐ the collision and `SqU6.gaTwoChannel_even_bit_even`;
* **4** the free `x1`-hypotheses; **5** wave 60's point: achievability, the odd channel, and
  ⭐⭐ the conditional widening; **6** axiom pins.

Companion memo: `docs/dyadic/w62-channels-note.md`.
-/

open Multiplicative

open scoped commutatorElement

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The three channels at a commutator dressing -/

section ChannelArithmetic

variable {R : Type} [CommRing R] {p q : SqU6 R}

/-- **The class-four coordinate of a commutator of two `stageN1` letters**, modulo two: the
`(j, d)`- and `(f, h)`-pairings, and nothing else.  Every one of the other eighteen monomials of
`SqU6.u6Comm4L` carries an `a`- or a `c`-column of one of the two letters. -/
theorem SqU6.commP_m_parity (hpa : (2 : R) ∣ p.a) (hpc : (2 : R) ∣ p.c) (hqa : (2 : R) ∣ q.a)
    (hqc : (2 : R) ∣ q.c) :
    (2 : R) ∣ ((commP p q).m - (p.j * q.d + p.d * q.j + p.f * q.h + p.h * q.f)) := by
  obtain ⟨pa, hpa⟩ := hpa
  obtain ⟨pc, hpc⟩ := hpc
  obtain ⟨qa, hqa⟩ := hqa
  obtain ⟨qc, hqc⟩ := hqc
  refine ⟨-(p.d * q.j) - p.h * q.f + pa * q.k - p.k * qa + pa * p.h * q.b - pa * p.b * q.h
    + p.h * qa * q.b - p.b * qa * q.h + p.d * p.f * qc - pc * p.f * q.d + p.d * qc * q.f
    - pc * q.d * q.f + pa * p.d * q.g + p.d * qa * q.g - pa * p.g * q.d - p.g * qa * q.d
    + 2 * (pa * p.b * pc * q.d) - 2 * (pa * p.b * p.d * qc) + 2 * (pa * pc * q.b * q.d)
    - 2 * (pa * p.d * q.b * qc) + 2 * (pc * qa * q.b * q.d) - 2 * (p.d * qa * q.b * qc), ?_⟩
  rw [SqU6.commP_m, SqU6.u6Comm4L, hpa, hpc, hqa, hqc]
  ring

/-- **The fourth class-two coordinate of a commutator**, modulo two: the `(d, e)`-pairing,
symmetrised.  No hypothesis is needed. -/
theorem SqU6.commP_i_parity (p q : SqU6 R) :
    (2 : R) ∣ ((commP p q).i - (p.d * q.e + p.e * q.d)) :=
  ⟨-(p.e * q.d), by rw [SqU6.commP_i]; ring⟩

/-- **The right class-three coordinate of a commutator of two `stageN1` letters**, modulo two:
the `(h, e)`-pairing, symmetrised.  Only the `c`-columns are needed. -/
theorem SqU6.commP_l_parity (hpc : (2 : R) ∣ p.c) (hqc : (2 : R) ∣ q.c) :
    (2 : R) ∣ ((commP p q).l - (p.h * q.e + p.e * q.h)) := by
  obtain ⟨pc, hpc⟩ := hpc
  obtain ⟨qc, hqc⟩ := hqc
  refine ⟨pc * q.i - p.i * qc - p.e * q.h + pc * p.e * q.d - pc * p.d * q.e + p.e * qc * q.d
    - p.d * qc * q.e, ?_⟩
  rw [SqU6.commP_l, SqU6.u6Comm3R, hpc, hqc]
  ring

/-- **The head of the channel at a commutator dressing**: `SqU6.gaTwoChannel (commP p q) q` with
each commutator coordinate replaced by its parity form.  Purely a bookkeeping device for
section 1. -/
def SqU6.gaTwoChannelHead (p q : SqU6 R) : R :=
  (p.j * q.d + p.d * q.j + p.f * q.h + p.h * q.f) * q.e
    + (p.d * q.e + p.e * q.d) * q.j + (p.h * q.e + p.e * q.h) * q.f

/-- The channel at a commutator dressing agrees with its head modulo two. -/
theorem SqU6.gaTwoChannel_commP_head (hpa : (2 : R) ∣ p.a) (hpc : (2 : R) ∣ p.c)
    (hqa : (2 : R) ∣ q.a) (hqc : (2 : R) ∣ q.c) :
    (2 : R) ∣ (SqU6.gaTwoChannel (commP p q) q - SqU6.gaTwoChannelHead p q) := by
  have hrw : SqU6.gaTwoChannel (commP p q) q - SqU6.gaTwoChannelHead p q
      = ((commP p q).m - (p.j * q.d + p.d * q.j + p.f * q.h + p.h * q.f)) * q.e
        + ((commP p q).i - (p.d * q.e + p.e * q.d)) * q.j
        + ((commP p q).l - (p.h * q.e + p.e * q.h)) * q.f := by
    rw [SqU6.gaTwoChannel, SqU6.gaTwoChannelHead]
    ring
  rw [hrw]
  exact dvd_add (dvd_add (Dvd.dvd.mul_right (SqU6.commP_m_parity hpa hpc hqa hqc) _)
    (Dvd.dvd.mul_right (SqU6.commP_i_parity p q) _))
    (Dvd.dvd.mul_right (SqU6.commP_l_parity hpc hqc) _)

/-- ⭐⭐ **The head collapses as soon as the `x1`-slot's `d`- and `e`-columns are even.**  Two of
the three channels die outright and the third leaves exactly `x0.e * x1.f * x1.h`.  ⭐ Nothing
is asked of the `x0` slot: the collapse is driven entirely by the letter that the relator's own
class-one rows already pin (`sqRelWord_lower_x1_even`). -/
theorem SqU6.gaTwoChannelHead_low (hqd : (2 : R) ∣ q.d) (hqe : (2 : R) ∣ q.e) :
    (2 : R) ∣ (SqU6.gaTwoChannelHead p q - p.e * q.f * q.h) := by
  obtain ⟨qd, hqd⟩ := hqd
  obtain ⟨qe, hqe⟩ := hqe
  refine ⟨qe * (2 * (p.j * qd) + p.d * q.j + p.f * q.h + p.h * q.f) + p.d * qe * q.j
    + p.e * qd * q.j + p.h * qe * q.f, ?_⟩
  rw [SqU6.gaTwoChannelHead, hqd, hqe]
  ring

/-- ⭐⭐⭐ **THE COLLISION.**  At any marking whose four core columns are `stageN1` (`a` and `c`
even on both letters) and whose `x1`-slot has even `d`- and `e`-columns, the three-channel value
of the achievable dressing `[x0, x1]` read against the `x1`-slot letter is

```text
   x0.e * x1.f * x1.h   (mod 2),
```

which is wave 58's closed form for the class-five separation bit once `stageN1` makes `x0.a`
even.  ⚠ So the functional a `gamma_2`-level exclusion needs to KILL is the very functional the
point needs LIVE in order to separate the two sigma dressings at all.

⭐ Every hypothesis is free.  `stageN1` is the transport's own
(`SqU6.sqRelWord_gaTwoDress_o_channel` asks it of every slot), and the two `x1`-columns are
forced by the relator itself at any marking killing the four abelian rows
(`sqRelWord_lower_x1_even`).  In particular **no gauge hypothesis is used**: the class-two
forcing enters only when the right-hand side is identified with the separation bit. -/
theorem SqU6.gaTwoChannel_commP_low (hpa : (2 : R) ∣ p.a) (hpc : (2 : R) ∣ p.c)
    (hqa : (2 : R) ∣ q.a) (hqc : (2 : R) ∣ q.c) (hqd : (2 : R) ∣ q.d) (hqe : (2 : R) ∣ q.e) :
    (2 : R) ∣ (SqU6.gaTwoChannel (commP p q) q - p.e * q.f * q.h) := by
  have hrw : SqU6.gaTwoChannel (commP p q) q - p.e * q.f * q.h
      = (SqU6.gaTwoChannel (commP p q) q - SqU6.gaTwoChannelHead p q)
        + (SqU6.gaTwoChannelHead p q - p.e * q.f * q.h) := by ring
  rw [hrw]
  exact dvd_add (SqU6.gaTwoChannel_commP_head hpa hpc hqa hqc)
    (SqU6.gaTwoChannelHead_low hqd hqe)

end ChannelArithmetic

/-! ## 2 The single-slot dressing on the `x1` slot -/

section SlotTwo

variable {R : Type} [CommRing R] {h : ℕ}

/-- The three channels vanish at the trivial dressing. -/
@[simp] theorem SqU6.gaTwoChannel_one (L : SqU6 R) : SqU6.gaTwoChannel (1 : SqU6 R) L = 0 := by
  rw [SqU6.gaTwoChannel, SqU6.one_m, SqU6.one_i, SqU6.one_l]
  ring

variable (h) in
/-- **The dressing carrying `w` on the `x1` slot and nothing anywhere else.**  Every slot of a
five-slot dressing may be chosen independently, so this is the cheapest probe of the
three-channel functional there is. -/
def gaTwoSlotTwo (w : SqU6 R) : Fin (sqRank h) → SqU6 R :=
  fun i => if (i : ℕ) = 2 then w else 1

@[simp] theorem gaTwoSlotTwo_two (w : SqU6 R) : gaTwoSlotTwo h w 2 = w := by
  simp only [gaTwoSlotTwo, sqVal_two, if_pos]

theorem gaTwoSlotTwo_of_ne (w : SqU6 R) {i : Fin (sqRank h)} (hi : (i : ℕ) ≠ 2) :
    gaTwoSlotTwo h w i = 1 := by
  simp only [gaTwoSlotTwo, if_neg hi]

@[simp] theorem gaTwoSlotTwo_zero (w : SqU6 R) : gaTwoSlotTwo h w 0 = 1 :=
  gaTwoSlotTwo_of_ne w (by rw [sqVal_zero]; omega)

@[simp] theorem gaTwoSlotTwo_one (w : SqU6 R) : gaTwoSlotTwo h w 1 = 1 :=
  gaTwoSlotTwo_of_ne w (by rw [sqVal_one]; omega)

@[simp] theorem gaTwoSlotTwo_handleU (w : SqU6 R) (k : Fin h) :
    gaTwoSlotTwo h w (sqHandleIdxU k) = 1 :=
  gaTwoSlotTwo_of_ne w (by rw [sqHandleIdxU_val]; omega)

@[simp] theorem gaTwoSlotTwo_handleV (w : SqU6 R) (k : Fin h) :
    gaTwoSlotTwo h w (sqHandleIdxV k) = 1 :=
  gaTwoSlotTwo_of_ne w (by rw [sqHandleIdxV_val]; omega)

/-- ⭐⭐ **The three-channel functional at a single-slot `x1` dressing** is one channel: the
dressing against the `x1`-slot letter.  The sigma slot, the `x0` slot with its Fox letter and
every handle contribute nothing, because `SqU6.gaTwoChannel` is linear in the dressing and the
dressing is trivial there. -/
theorem SqU6.gaTwoShiftChan_gaTwoSlotTwo (m : Fin (sqRank h) → SqU6 R) (w : SqU6 R) :
    SqU6.gaTwoShiftChan h m (gaTwoSlotTwo h w) = SqU6.gaTwoChannel w (m 2) := by
  rw [SqU6.gaTwoShiftChan]
  simp only [gaTwoSlotTwo_zero, gaTwoSlotTwo_one, gaTwoSlotTwo_two, gaTwoSlotTwo_handleU,
    gaTwoSlotTwo_handleV, SqU6.gaTwoChannel_one, sub_self, Finset.sum_const_zero]
  ring

end SlotTwo

/-! ## 3 The collision at the marking level -/

section Collision

variable {R : Type} [CommRing R] {h : ℕ} {m : Fin (sqRank h) → SqU6 R}

/-- ⭐⭐⭐ **THE COLLISION, at the marking level.**  The three-channel functional, evaluated at
the achievable dressing that puts the commutator `[x0, x1]` of the marking's own two core letters
on the `x1` slot, is congruent modulo two to `x0.e * x1.f * x1.h`. -/
theorem SqU6.gaTwoShiftChan_gaTwoSlotTwo_low
    (hpa : (2 : R) ∣ (m 1).a) (hpc : (2 : R) ∣ (m 1).c) (hqa : (2 : R) ∣ (m 2).a)
    (hqc : (2 : R) ∣ (m 2).c) (hqd : (2 : R) ∣ (m 2).d) (hqe : (2 : R) ∣ (m 2).e) :
    (2 : R) ∣ (SqU6.gaTwoShiftChan h m (gaTwoSlotTwo h (commP (m 1) (m 2)))
      - (m 1).e * (m 2).f * (m 2).h) := by
  rw [SqU6.gaTwoShiftChan_gaTwoSlotTwo]
  exact SqU6.gaTwoChannel_commP_low hpa hpc hqa hqc hqd hqe

/-- ⭐⭐⭐ **EVEN CHANNELS FORCE AN EVEN BIT.**  At any marking with `stageN1` core letters and an
`x1` slot whose `d`- and `e`-columns are even, if the three-channel functional is even at the
achievable dressing `[x0, x1]` on the `x1` slot, then wave 58's class-five separation form
`x0.e * x1.f * x1.h` is even as well.

⚠ This is the certified negative of the wave.  `GradedFiveGammaTwo` needs a point at which the
channels are even, and `GradedFiveStageFour` needs a point at which the bit is odd; since the
bit IS that form, no point is both.  The exhaustive parity sweep
(`scripts/w62_channels/results/sweep_f2.txt`) confirms it from the other side: `0` of the
bit-odd patterns compatible with the relator's own two `x1`-columns have even channels, and the
`2432` even-channel bit-odd patterns that do exist all need `x0.d`, `x0.f` or `x1.d` odd. -/
theorem SqU6.gaTwoChannel_even_bit_even
    (hpa : (2 : R) ∣ (m 1).a) (hpc : (2 : R) ∣ (m 1).c) (hqa : (2 : R) ∣ (m 2).a)
    (hqc : (2 : R) ∣ (m 2).c) (hqd : (2 : R) ∣ (m 2).d) (hqe : (2 : R) ∣ (m 2).e)
    (hchan : (2 : R) ∣ SqU6.gaTwoShiftChan h m (gaTwoSlotTwo h (commP (m 1) (m 2)))) :
    (2 : R) ∣ (m 1).e * (m 2).f * (m 2).h := by
  have h1 := SqU6.gaTwoShiftChan_gaTwoSlotTwo_low (m := m) hpa hpc hqa hqc hqd hqe
  have h2 : (m 1).e * (m 2).f * (m 2).h
      = SqU6.gaTwoShiftChan h m (gaTwoSlotTwo h (commP (m 1) (m 2)))
        - (SqU6.gaTwoShiftChan h m (gaTwoSlotTwo h (commP (m 1) (m 2)))
          - (m 1).e * (m 2).f * (m 2).h) := by ring
  rw [h2]
  exact dvd_sub hchan h1

end Collision

/-! ## 4 The `x1`-slot hypotheses are free -/

section FreeHypotheses

variable {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R}

/-- Over the eight-element ring, `2 y = 4 z` forces `y` even. -/
private theorem two_dvd_of_two_mul_eq :
    ∀ y z : gr3R, 2 * y = 4 * z → ∃ t : gr3R, y = 2 * t := by decide

/-- ⭐ **The `x1`-slot's abelian columns are even at any marking whose relator's four abelian
rows vanish.**  Each of those rows is `-4 x0.k + 2 x1.k` (`SqU6.sqRelWord_a` and its siblings,
committed), so killing it forces `x1.k` even.  Both frames of wave 60's separation qualify: the
undressed one kills the relator outright, and the `a0 = a1` one leaves `SqU6.liftO 1`, whose
fourteen lower rows vanish. -/
theorem sqRelWord_lower_x1_even (ha : (sqRelWord m).a = 0) (hc : (sqRelWord m).c = 0)
    (hd : (sqRelWord m).d = 0) (he : (sqRelWord m).e = 0) :
    (2 : gr3R) ∣ (m 2).a ∧ (2 : gr3R) ∣ (m 2).c ∧ (2 : gr3R) ∣ (m 2).d
      ∧ (2 : gr3R) ∣ (m 2).e := by
  rw [SqU6.sqRelWord_a] at ha
  rw [SqU6.sqRelWord_c] at hc
  rw [SqU6.sqRelWord_d] at hd
  rw [SqU6.sqRelWord_e] at he
  exact ⟨two_dvd_of_two_mul_eq _ (m 1).a (by linear_combination ha),
    two_dvd_of_two_mul_eq _ (m 1).c (by linear_combination hc),
    two_dvd_of_two_mul_eq _ (m 1).d (by linear_combination hd),
    two_dvd_of_two_mul_eq _ (m 1).e (by linear_combination he)⟩

end FreeHypotheses

/-! ## 5 Wave 60's point: the odd channel, and the conditional widening -/

section Point

variable {h : ℕ} {j : Fin h}

/-- ⭐ **The commutator of the marking's own two core letters, on the `x1` slot, is an
achievable `gamma_2`-dressing**: it lies in `forceLcs (stageImage h j v) 1`, the honest
`gamma_2` of the image subgroup, and every other slot carries `1`. -/
theorem gaTwoSlotTwo_comm_mem_forceLcs (v : SqU6 gr3R) (i : Fin (sqRank h)) :
    gaTwoSlotTwo h (commP (stageWit h j v 1) (stageWit h j v 2)) i
      ∈ forceLcs (stageImage h j v) 1 := by
  by_cases hi : (i : ℕ) = 2
  · rw [gaTwoSlotTwo, if_pos hi]
    have h1 : stageWit h j v 1 ∈ stageImage h j v := Subgroup.subset_closure ⟨1, rfl⟩
    have h2 : stageWit h j v 2 ∈ stageImage h j v := Subgroup.subset_closure ⟨2, rfl⟩
    have hcomm : commP (stageWit h j v 1) (stageWit h j v 2)
        = ⁅(stageWit h j v 1)⁻¹, (stageWit h j v 2)⁻¹⁆ := by
      rw [commutatorElement_eq_commP, inv_inv, inv_inv]
    rw [hcomm]
    exact Subgroup.commutator_mem_commutator (inv_mem h1) (inv_mem h2)
  · rw [gaTwoSlotTwo, if_neg hi]
    exact one_mem _

/-- The point's two core letters, column by column.  The collision consumes only `stageN1`
on both and the `x1`-slot's `d`- and `e`-columns; the `x0`-slot's `d`, `f` and `h` are recorded
because they are what the class-two-forced gauge pins and an off-gauge escape would have to
break.  The last conjunct is the separation form, ODD. -/
theorem stageWit_gauge_columns :
    (stageX.a = 2 * 1 ∧ stageX.c = 2 * 0 ∧ stageX.d = 2 * 0 ∧ stageX.f = 2 * 0
        ∧ stageX.h = 2 * 0)
      ∧ (stageY.a = 2 * 0 ∧ stageY.c = 2 * 0 ∧ stageY.d = 2 * 0 ∧ stageY.e = 2 * 1)
      ∧ selPar (stageX.e * stageY.f * stageY.h) = 1 := by decide

/-- ⭐⭐ **The three-channel functional is ODD at wave 60's binder point**, at an explicitly
achievable dressing, at every handle count and every handle.  `GradedFiveGammaTwo` reported this
as a measurement over the ten commutator generators
(`scripts/w61_wider/results/census.txt`); here it is a theorem, for the generator that decides
the question. -/
theorem stageWit_gaTwoShiftChan_slotTwo_odd (h : ℕ) (j : Fin h) :
    selPar (SqU6.gaTwoShiftChan h (stageWit h j stageX)
      (gaTwoSlotTwo h (commP stageX stageY))) = 1 := by
  rw [SqU6.gaTwoShiftChan_gaTwoSlotTwo, stageWit, fiveTuple_two]
  decide

/-- ⭐⭐ **THE WIDENING, WITH ITS CONDITION.**  At wave 60's binder point, at every handle count
and every handle, **no achievable `gamma_2`-dressing whose three-channel functional is even kills
the dressed frame**.  This is `GradedFiveStageFour.sqRelWord_stageWit_diag_ne_one` one filtration
step wider, and the condition is exactly the price `GradedFiveGammaTwo` named. -/
theorem sqRelWord_stageWit_diag_gaTwo_ne_one {z : Fin (sqRank h) → SqU6 gr3R}
    (hz : ∀ i, z i ∈ forceLcs (stageImage h j stageX) 1)
    (hchan : selPar (SqU6.gaTwoShiftChan h (stageWit h j stageX) z) = 0) :
    sqRelWord (conFiveDress (stageWit h j stageX) z) ≠ 1 := by
  intro hc
  have hp := stageWit_gaTwo_forced (h := h) (j := j) ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩ hz hc
  rw [sqRelWord_stageWit_diag, SqU6.liftO_o, selPar_add, hchan, selPar_one] at hp
  exact absurd hp (by decide)

/-- ⚠ **…and the condition is not vacuous.**  At the same point there is an achievable
`gamma_2`-dressing whose functional is odd, so wave 61's forcing conclusion is **satisfied**
there and produces no contradiction.  The `gamma_2` transport therefore cannot make wave 60's
exclusion unconditional one filtration step wider at this point, and by
`SqU6.gaTwoChannel_even_bit_even` not at any point with an odd bit either. -/
theorem stageWit_gaTwo_forced_not_vacuous (h : ℕ) (j : Fin h) :
    ∃ z : Fin (sqRank h) → SqU6 gr3R, (∀ i, z i ∈ forceLcs (stageImage h j stageX) 1)
      ∧ selPar (SqU6.gaTwoShiftChan h (stageWit h j stageX) z) = 1
      ∧ selPar ((sqRelWord (stageWit h j stageX)).o
        + SqU6.gaTwoShiftChan h (stageWit h j stageX) z) = 0 := by
  refine ⟨gaTwoSlotTwo h (commP stageX stageY), ?_, stageWit_gaTwoShiftChan_slotTwo_odd h j, ?_⟩
  · intro i
    have := gaTwoSlotTwo_comm_mem_forceLcs (h := h) (j := j) stageX i
    rwa [stageWit, fiveTuple_one, fiveTuple_two] at this
  · rw [selPar_add, stageWit_gaTwoShiftChan_slotTwo_odd, sqRelWord_stageWit_diag, SqU6.liftO_o,
      selPar_one]
    decide

/-- ⭐ **The collision, at wave 60's point.**  The channel value and the separation bit are both
odd, so their sum is even: the two functionals agree, exactly as
`SqU6.gaTwoChannel_even_bit_even` predicts. -/
theorem stageWit_channel_eq_bit :
    selPar (SqU6.gaTwoChannel (commP stageX stageY) stageY)
      = selPar (stageX.e * stageY.f * stageY.h) := by decide

end Point

/-! ## 6 Axiom pins

Committed prints for every public declaration of this file: all **std-3** (`propext`,
`Classical.choice`, `Quot.sound`) or a subset; no census axiom is reachable.  Every `decide` is
on `gr3R = ZMod 8` or on `SqU6 gr3R`; there is no `native_decide`. -/

section AxiomPins

#print axioms SqU6.commP_m_parity
#print axioms SqU6.commP_i_parity
#print axioms SqU6.commP_l_parity
#print axioms SqU6.gaTwoChannelHead
#print axioms SqU6.gaTwoChannel_commP_head
#print axioms SqU6.gaTwoChannelHead_low
#print axioms SqU6.gaTwoChannel_commP_low
#print axioms SqU6.gaTwoChannel_one
#print axioms gaTwoSlotTwo
#print axioms gaTwoSlotTwo_two
#print axioms gaTwoSlotTwo_of_ne
#print axioms gaTwoSlotTwo_zero
#print axioms gaTwoSlotTwo_one
#print axioms gaTwoSlotTwo_handleU
#print axioms gaTwoSlotTwo_handleV
#print axioms SqU6.gaTwoShiftChan_gaTwoSlotTwo
#print axioms SqU6.gaTwoShiftChan_gaTwoSlotTwo_low
#print axioms SqU6.gaTwoChannel_even_bit_even
#print axioms sqRelWord_lower_x1_even
#print axioms gaTwoSlotTwo_comm_mem_forceLcs
#print axioms stageWit_gauge_columns
#print axioms stageWit_gaTwoShiftChan_slotTwo_odd
#print axioms sqRelWord_stageWit_diag_gaTwo_ne_one
#print axioms stageWit_gaTwo_forced_not_vacuous
#print axioms stageWit_channel_eq_bit

end AxiomPins

end SqCore

end Dyadic

end GQ2

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedGammaTwoCentral
import GQ2.Dyadic.SqCore.GradedFiveLive

/-!
# W64-CENSUS5: the class-four KNOB, and the `gamma_2` census it decides

`GradedGammaTwoCentral` (W63-CENTRAL2) refuted the `gamma_2` route at ONE point, named its
mechanism in prose, and wrote down the criterion that would decide the census:

> A point survives only if its achievable `gamma_2` lattice has an EVEN class-four coordinate at
> the sigma slot, or `x0.e` is EVEN - and an even `x0.e` kills the class-five separation bit
> itself.  If those two demands are incompatible, the `gamma_2` route is dead at EVERY point.

This file turns that mechanism into a theorem, runs the census, and reports both halves honestly.

## ⭐⭐⭐ Headline 1: the mechanism is a KNOB, and it has a GEARING

⭐⭐⭐ `SqU6.sqWord_mul_censKnob`.  Multiplying the sigma letter by `SqU6.censKnob t` - the
class-four coordinate `m` and nothing else - translates the core word by the central element
`SqU6.liftO (x0.e * t)` and moves **no other row**, at every marking and over **any commutative
ring**.  No transport, no achievability, no `stageN1`, no gauge.  So W63-CENTRAL2's
`cenKill_mechanism`, which was two numbers side by side at wave 60's point, becomes the identity

```text
   relator(sigma slot dressed by <m = t>)  =  relator  *  liftO (x0.e * t).
```

⭐⭐ And the sigma slot is not the only place it turns.  `SqU6.commP_mul_censKnob_left` and
`_right`: the same knob on either letter of a commutator translates it centrally by `t * q.e`
and by `-(t * p.e)`, so the LIVE HANDLE carries two more knobs, geared by `v_j.e` and `-u_j.e`.
**Three knobs, three gearings** (`sqRelWord_cenSigDress_censKnob`, `sqRelWord_censSlotU_censKnob`,
`sqRelWord_censSlotV_censKnob`), each a central translation of the relator.

⚠ There is no fourth or fifth: at the two CORE slots the same dressing does **not** act
centrally - it disturbs the class-three and class-four rows - and
`scripts/w64_census5/results/derive.txt` section 1 records that as a measured negative, so the
knob list is exactly three and this file does not pretend otherwise.

## ⭐⭐⭐ Headline 2: the census criterion, quantified over binder points

⭐⭐⭐ `cens_lines_false_of_central_kill` is the engine: at a marking with an ODD CENTRAL relator,
**any** achievable `gamma_2`-dressing that translates the relator centrally onto `1` refutes the
`gamma_2` forcing, the CENTRALITY line and the parity line at once.  Centrality comes free
because the translation is central by hypothesis, which is what W63-CENTRAL2 had to check
separately at its one dressing.

⭐⭐ `cens_sigKnob_dichotomy`, `cens_uKnob_dichotomy`, `cens_vKnob_dichotomy`.  If `GaTwoForces`
HOLDS at a binder point then, for **each** of the three gearings,

* either the gearing is EVEN,
* or the achievable lattice misses `censKnob t` for the unique `t` solving that knob's equation,
  and that `t` is ODD.

⚠ This is sharper than the prose criterion in three ways: it is quantified over points rather
than stated at one; it runs at THREE slots rather than at the sigma slot alone; and its second
horn is a single membership `censKnob t ∉ forceLcs _ 1`, not the coarser "the lattice has an even
class-four coordinate there".  The two are NOT equivalent, and the census exhibits binder points
where a lattice with odd class-four coordinates still misses the knob.

## ⭐⭐⭐ Headline 3: W63-LIVE5's point is killed by W63-CENTRAL2's own dressing

⭐⭐⭐ `liveBlkWit_lines_false`.  W63 recorded this composite as genuinely unresolved.
`GradedFiveLive.liveBlkWit` reuses `stageX` in its `x0` slot - the slot the sigma knob's gearing
reads - and its `a0 = a1` residue is the same odd `1`, so `censKnob 3 = gaTwoCenKill` kills its
DIAGONALLY dressed frame too, at every handle count and every handle, and all three `gamma_2`
lines fail there.  ⭐ The achievability certificate is simpler than wave 60's:
`liveBlk_censKnob_comm_form` writes the knob as `[u, sigma x0] * [sigma x0, v]`, a product of two
honest commutators of the point's own letters with no inverse and no power.

⚠ `GradedFiveLive.sqRelWord_liveBlkWit_diag_ne_one` and every other stage-four exclusion are
untouched: `censKnob_odd_not_mem_stageN3` says an odd knob is not in `stageN3`, so it is not an
achievable stage-four dressing.  What dies is the `gamma_2` widening, exactly as at wave 60's
point.

## PROVED versus MEASURED

**PROVED** (this file, no `sorry`, no new axiom, no `native_decide`): the knob identity at the
sigma slot and at both letters of a commutator, over any commutative ring; the three relator
identities at the one-handle-live family; that the sigma knob's `gamma_2` shift is exactly the
central translation; the refutation engine; the three dichotomies; the widening of
W63-CENTRAL2's refutation from its one point to the whole `stageWit` family; and the kill at
W63-LIVE5's point with its certificate.

**MEASURED** (`scripts/w64_census5/`, certified output in `results/`):

* `derive.txt` - the knob identity at all five slots and its three central cases over eight
  moduli; the structural facts that license the census machinery, WITH the record that the fast
  ones fail at the two core slots; three independent routes (fast census, nested sweep, honest
  brute force over every element) agreeing on sub-lattices of wave 60's own lattice; W62's
  class-four parity form re-measured; and ⭐ **the parity horn**: over sixty thousand `(x0, x1)`
  pairs at each parity, an EVEN `x0.e` never produces an odd residue while an odd one produces
  them in quantity.  Wave 58's closed form is re-measured on the same sample and is
  exceptionless.
* `census.txt` - binder points decided EXACTLY at the sigma slot and both handle slots (and at
  the core slots too wherever those three all fail), with per-slot kill counts, the three
  gearings, and knob achievability.

⭐ **The verdict.**  At **67** binder points decided exactly, **0** survive: every one is killed
by an achievable single-slot `gamma_2`-dressing.  Two findings make the census worth more than
its sample size, and both cut against the knob being the whole story: **(a)** the sigma knob is
NOT always achievable - at `18` of the `67` its lattice misses it, and at `6` of those the sigma
slot has **no achievable killing dressing at all**, so W63-CENTRAL2's route alone does not close
the census; **(b)** at exactly those `6` a HANDLE SLOT kills instead, with thousands of
dressings.  ⚠ At those points the handle knobs are unachievable too, so the killer there is a
general lattice element and **not** a knob: the knob theorems are a proved SUFFICIENT mechanism,
not a classification of the killers, and this file does not claim otherwise.

## Scope, honestly

* **The parity horn is MEASURED, not proved.**  "A live binder point has an odd `x0.e`" rests on
  wave 58's closed form for the class-five separation bit, which is a measurement everywhere in
  the tree and is re-measured here in a decoupled form (once the undressed frame kills, the
  residue is `sqWord(sigma x0, x0, x1) * sqWord(sigma, x0, x1)^{-1}`, which does not involve the
  handle letters at all).  Proving it needs the relator's `(1,6)`-row in closed form, which no
  wave has built.  Every Lean statement below is conditional on a gearing's parity and never
  asserts it.
* **The achievability horn is MEASURED, not proved.**  Whether `censKnob t` lies in
  `forceLcs (image) 1` is a property of the point, checked by exact polycyclic sifting; no
  theorem here says it must.  So the census is a certified sweep over the points it reaches and
  **not** a proof that the `gamma_2` route is dead at every binder point.  The honest verdict is:
  **dead at every point reached, by a mechanism now proved in general, with the two side
  conditions isolated and measured.**
* **Single-slot, mostly.**  `GaTwoForces` quantifies over five-slot dressings; the census decides
  single-slot dressings exactly.  A point killed by one slot is killed outright, so the verdict
  direction is sound; a hypothetical survivor of all five slots would need a five-slot search,
  and none is claimed to have been run.
* **Marking-tuple level, not hom level.**  Like `GradedFiveGammaTwo`, `GradedGammaTwoPoint` and
  `GradedGammaTwoCentral`, this file works with tuples in `SqU6 gr3R`.  The killing dressings are
  images of explicit commutators of the letters, so a hom-level lift is bookkeeping, but it is
  not done here.

## The sweep against the tree's refutations

Doctrine rule 4, item by item.  Nothing quotes wave 56's retracted `EvenRouteCarriedDeep`
structures.  Wave 60's three-covector class-five line is never used as a criterion.  Wave 61's
`gamma_2` affineness is not used at all: the knob identities are proved directly and the
`gamma_2` shift is obtained by cancelling `SqU6.sqRelWord_gaTwoDress`, never from an emitted
closed form; the scripts likewise read every shift off the relator.  Wave 62's collision is
inherited, not evaded: the parity horn IS that collision, restated as "an even `x0.e` kills the
bit", and no search for a point with three even channels is made anywhere.  W63-SECOND's warning
about whole-form vanishing is respected: no two-pair computation is used to conclude that
anything vanishes; the vanishing statements here are `SqU6.liftO`-shaped identities proved on all
fifteen coordinates by `ext`.  W62's handle-count invariant is not invoked.  ⭐ **Doctrine
rule 1** (the sharpest bound, wherever something SURVIVES): the only survival claims here are the
two horns of the dichotomy, and both are stated as hypotheses rather than asserted; where the
census finds a point surviving one slot it does not stop, but decides the other slots and reports
that a handle knob kills.  ⭐ **Doctrine rule 3** (composites): `sqRelWord_stageWit_censKnob`
re-derives W63-CENTRAL2's kill from the general identity instead of from its kernel computation,
and the scripts cross-check the fast census against a nested sweep and against honest brute force.

## Contents

* **1** the knob and the sigma-slot identity; **2** the two handle knobs;
* **3** ⭐⭐⭐ the refutation engine; **4** the three knobs instantiated;
* **5** ⭐⭐⭐ the census criterion and the three dichotomies;
* **6** W63-CENTRAL2's point widened to its family; **7** ⭐⭐⭐ W63-LIVE5's point;
* **8** axiom pins.

Companion memo: `docs/dyadic/w64-census5-note.md`.
-/

open scoped commutatorElement

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The knob, and the sigma slot -/

section Knob

variable {R : Type} [CommRing R]

/-- ⭐⭐ **THE KNOB**: the class-four coordinate `m`, alone.
`GradedGammaTwoCentral.gaTwoCenKill` is `censKnob 3`; this is the one-parameter family it sits
in, over any commutative ring. -/
def SqU6.censKnob (t : R) : SqU6 R := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, t, 0, 0⟩

@[simp] theorem SqU6.censKnob_m (t : R) : (SqU6.censKnob t).m = t := rfl

theorem SqU6.censKnob_isGaThree (t : R) : (SqU6.censKnob t).IsGaThree :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SqU6.censKnob_isGaTwo (t : R) : (SqU6.censKnob t).IsGaTwo :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 1000000 in
/-- ⭐⭐⭐ **THE KNOB IDENTITY AT THE SIGMA SLOT.**  Multiplying the sigma letter of the core word
by `censKnob t` translates the word by the central element `SqU6.liftO (x.e * t)` and does
**nothing else**, at every marking and over **any commutative ring**.

⭐ This is `GradedGammaTwoCentral.cenKill_mechanism` turned from a numerical coincidence at wave
60's point into a theorem: the class-four coordinate at the sigma slot is a knob whose GEARING is
exactly the `x0`-slot letter's `(5,6)`-column, so it reaches every residue in the ideal that
column generates, and no lower row can register the move.  No transport, no achievability, no
`stageN1`, no gauge: componentwise expansion, exactly as
`GradedFiveStageFour.SqU6.sqWord_mul_gaThree`. -/
theorem SqU6.sqWord_mul_censKnob (s x y : SqU6 R) (t : R) :
    sqWord (s * SqU6.censKnob t) x y = sqWord s x y * SqU6.liftO (x.e * t) := by
  ext <;>
    simp only [SqU6.censKnob, SqU6.liftO, sqWord, conjP, commP, pow_succ, pow_zero, one_mul,
      SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e, SqU6.mul_f, SqU6.mul_g,
      SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l, SqU6.mul_m, SqU6.mul_n,
      SqU6.mul_o, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d, SqU6.inv_e, SqU6.inv_f,
      SqU6.inv_g, SqU6.inv_h, SqU6.inv_i, SqU6.inv_j, SqU6.inv_k, SqU6.inv_l, SqU6.inv_m,
      SqU6.inv_n, SqU6.inv_o] <;>
    ring

variable {h : ℕ} {j : Fin h}

/-- …and the handle block cannot see it either, because the translation is central. -/
theorem sqRelWord_fiveTuple_censKnob (S X Y U V : SqU6 R) (t : R) :
    sqRelWord (fiveTuple R h j (S * SqU6.censKnob t) X Y U V)
      = sqRelWord (fiveTuple R h j S X Y U V) * SqU6.liftO (X.e * t) := by
  rw [sqRelWord_fiveTuple, sqRelWord_fiveTuple, SqU6.sqWord_mul_censKnob, mul_assoc,
    ← SqU6.liftO_comm, ← mul_assoc]

/-- ⭐⭐ **The knob as a DRESSING.**  `GradedGammaTwoCentral.cenSigDress` puts an element on the
sigma slot alone, and `conFiveDress_fiveTuple_cenSigDress` says that reparametrises the marking,
so the knob identity is a statement about achievable dressings with no transport at all. -/
theorem sqRelWord_cenSigDress_censKnob (S X Y U V : SqU6 R) (t : R) :
    sqRelWord (conFiveDress (fiveTuple R h j S X Y U V) (cenSigDress h (SqU6.censKnob t)))
      = sqRelWord (fiveTuple R h j S X Y U V) * SqU6.liftO (X.e * t) := by
  rw [conFiveDress_fiveTuple_cenSigDress, sqRelWord_fiveTuple_censKnob]

/-- The knob dressing is `gamma_2`-shaped in every slot, which is all the transport asks. -/
theorem cenSigDress_censKnob_isGaTwo (t : R) (i : Fin (sqRank h)) :
    (cenSigDress h (SqU6.censKnob t) i).IsGaTwo := by
  by_cases hi : (i : ℕ) = 0
  · rw [cenSigDress, if_pos hi]
    exact SqU6.censKnob_isGaTwo t
  · rw [cenSigDress, if_neg hi]
    exact SqU6.isGaTwo_one

end Knob

/-! ## 2 The two handle knobs -/

section HandleKnob

variable {R : Type} [CommRing R] {h : ℕ} {j : Fin h}

set_option maxHeartbeats 400000 in
/-- ⭐⭐ **The knob on the LEFT letter of a commutator** translates it centrally by `t * q.e`, at
every pair and over any commutative ring.  So the handle block carries a knob of its own, geared
by the OTHER handle letter's `(5,6)`-column. -/
theorem SqU6.commP_mul_censKnob_left (p q : SqU6 R) (t : R) :
    commP (p * SqU6.censKnob t) q = commP p q * SqU6.liftO (t * q.e) := by
  ext <;>
    simp only [SqU6.censKnob, SqU6.liftO, commP,
      SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e, SqU6.mul_f, SqU6.mul_g,
      SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l, SqU6.mul_m, SqU6.mul_n,
      SqU6.mul_o, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d, SqU6.inv_e, SqU6.inv_f,
      SqU6.inv_g, SqU6.inv_h, SqU6.inv_i, SqU6.inv_j, SqU6.inv_k, SqU6.inv_l, SqU6.inv_m,
      SqU6.inv_n, SqU6.inv_o] <;>
    ring

set_option maxHeartbeats 400000 in
/-- ⭐⭐ …and on the RIGHT letter, geared by `-p.e`. -/
theorem SqU6.commP_mul_censKnob_right (p q : SqU6 R) (t : R) :
    commP p (q * SqU6.censKnob t) = commP p q * SqU6.liftO (-(t * p.e)) := by
  ext <;>
    simp only [SqU6.censKnob, SqU6.liftO, commP,
      SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e, SqU6.mul_f, SqU6.mul_g,
      SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l, SqU6.mul_m, SqU6.mul_n,
      SqU6.mul_o, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d, SqU6.inv_e, SqU6.inv_f,
      SqU6.inv_g, SqU6.inv_h, SqU6.inv_i, SqU6.inv_j, SqU6.inv_k, SqU6.inv_l, SqU6.inv_m,
      SqU6.inv_n, SqU6.inv_o] <;>
    ring

variable (h j) in
/-- **The dressing carrying `w` on the live handle's `u`-slot and nothing anywhere else.**
`GradedGammaTwoCentral.cenSigDress` at the handle instead of at the sigma slot. -/
def censSlotU (w : SqU6 R) : Fin (sqRank h) → SqU6 R :=
  fun i => if (i : ℕ) = (sqHandleIdxU j : ℕ) then w else 1

variable (h j) in
/-- …and on its `v`-slot. -/
def censSlotV (w : SqU6 R) : Fin (sqRank h) → SqU6 R :=
  fun i => if (i : ℕ) = (sqHandleIdxV j : ℕ) then w else 1

theorem censSlotU_isGaTwo {w : SqU6 R} (hw : w.IsGaTwo) (i : Fin (sqRank h)) :
    (censSlotU h j w i).IsGaTwo := by
  by_cases hi : (i : ℕ) = (sqHandleIdxU j : ℕ)
  · rw [censSlotU, if_pos hi]; exact hw
  · rw [censSlotU, if_neg hi]; exact SqU6.isGaTwo_one

theorem censSlotV_isGaTwo {w : SqU6 R} (hw : w.IsGaTwo) (i : Fin (sqRank h)) :
    (censSlotV h j w i).IsGaTwo := by
  by_cases hi : (i : ℕ) = (sqHandleIdxV j : ℕ)
  · rw [censSlotV, if_pos hi]; exact hw
  · rw [censSlotV, if_neg hi]; exact SqU6.isGaTwo_one

/-- Dressing the live handle's `u`-slot reparametrises the marking, exactly as at the sigma
slot. -/
theorem conFiveDress_fiveTuple_censSlotU (S X Y U V w : SqU6 R) :
    conFiveDress (fiveTuple R h j S X Y U V) (censSlotU h j w)
      = fiveTuple R h j S X Y (U * w) V := by
  funext i
  rw [conFiveDress_apply]
  by_cases hi : (i : ℕ) = (sqHandleIdxU j : ℕ)
  · rw [censSlotU, if_pos hi]
    simp only [fiveTuple, if_neg (show ¬ (i : ℕ) = 0 by rw [hi, sqHandleIdxU_val]; omega),
      if_neg (show ¬ (i : ℕ) = 1 by rw [hi, sqHandleIdxU_val]; omega),
      if_neg (show ¬ (i : ℕ) = 2 by rw [hi, sqHandleIdxU_val]; omega), if_pos hi]
  · rw [censSlotU, if_neg hi, mul_one]
    simp only [fiveTuple, if_neg hi]

/-- …and the same for the `v`-slot. -/
theorem conFiveDress_fiveTuple_censSlotV (S X Y U V w : SqU6 R) :
    conFiveDress (fiveTuple R h j S X Y U V) (censSlotV h j w)
      = fiveTuple R h j S X Y U (V * w) := by
  funext i
  rw [conFiveDress_apply]
  by_cases hi : (i : ℕ) = (sqHandleIdxV j : ℕ)
  · rw [censSlotV, if_pos hi]
    simp only [fiveTuple, if_neg (show ¬ (i : ℕ) = 0 by rw [hi, sqHandleIdxV_val]; omega),
      if_neg (show ¬ (i : ℕ) = 1 by rw [hi, sqHandleIdxV_val]; omega),
      if_neg (show ¬ (i : ℕ) = 2 by rw [hi, sqHandleIdxV_val]; omega),
      if_neg (show ¬ (i : ℕ) = (sqHandleIdxU j : ℕ) by
        rw [hi, sqHandleIdxU_val, sqHandleIdxV_val]; omega), if_pos hi]
  · rw [censSlotV, if_neg hi, mul_one]
    simp only [fiveTuple, if_neg hi]

/-- ⭐⭐ **The `u`-slot knob translates the relator centrally by `t * V.e`.** -/
theorem sqRelWord_censSlotU_censKnob (S X Y U V : SqU6 R) (t : R) :
    sqRelWord (conFiveDress (fiveTuple R h j S X Y U V) (censSlotU h j (SqU6.censKnob t)))
      = sqRelWord (fiveTuple R h j S X Y U V) * SqU6.liftO (t * V.e) := by
  rw [conFiveDress_fiveTuple_censSlotU, sqRelWord_fiveTuple, sqRelWord_fiveTuple,
    SqU6.commP_mul_censKnob_left, ← mul_assoc]

/-- ⭐⭐ …and the `v`-slot knob by `-(t * U.e)`. -/
theorem sqRelWord_censSlotV_censKnob (S X Y U V : SqU6 R) (t : R) :
    sqRelWord (conFiveDress (fiveTuple R h j S X Y U V) (censSlotV h j (SqU6.censKnob t)))
      = sqRelWord (fiveTuple R h j S X Y U V) * SqU6.liftO (-(t * U.e)) := by
  rw [conFiveDress_fiveTuple_censSlotV, sqRelWord_fiveTuple, sqRelWord_fiveTuple,
    SqU6.commP_mul_censKnob_right, ← mul_assoc]

end HandleKnob

/-! ## 3 The refutation engine: one central kill refutes all three lines -/

section Engine

variable {h : ℕ} {m z : Fin (sqRank h) → SqU6 gr3R} {c g : gr3R}

/-- `1 + s = 0` in `ZMod 2` forces `s = 1`: the parity bookkeeping of this file, once. -/
private theorem censParTwo : ∀ s : ZMod 2, 1 + s = 0 → s = 1 := by decide

/-- ⭐⭐⭐ **THE ENGINE.**  Let a marking have the CENTRAL relator `SqU6.liftO c` with `c` ODD.
If some achievable `gamma_2`-dressing translates that relator centrally by `SqU6.liftO g` with
`c + g = 0`, then **all three `gamma_2` lines fail at that marking**: the forcing, the centrality
line and the parity line.

⭐ Nothing about the shape of the dressing is used - only that its effect on the relator is a
CENTRAL translation, which is what turns a kill into a counterexample to the centrality line and
not merely to the parity line.  `GradedGammaTwoCentral` had to check that separately at its one
dressing (`gaTwoShift_stageWit_cenKill`); here it is part of the hypothesis and is discharged
once for the three knobs of sections 1 and 2. -/
theorem cens_lines_false_of_central_kill
    (hres : sqRelWord m = SqU6.liftO c) (hodd : selPar c = 1)
    (hshift : sqRelWord (conFiveDress m z) = sqRelWord m * SqU6.liftO g) (hkill : c + g = 0)
    (hga : ∀ i, (z i).IsGaTwo)
    (hach : ∀ i, z i ∈ forceLcs (Subgroup.closure (Set.range m)) 1) :
    ¬ GaTwoForces m ∧ ¬ GaTwoCentral m ∧ ¬ GaTwoOrth m := by
  have hgodd : selPar g = 1 := by
    have h0 : selPar (c + g) = 0 := by rw [hkill]; rfl
    rw [selPar_add, hodd] at h0
    exact censParTwo _ h0
  have hone : sqRelWord (conFiveDress m z) = 1 := by
    rw [hshift, hres, SqU6.liftO_mul_liftO, hkill]
    ext <;> simp [SqU6.liftO]
  have hsh : SqU6.gaTwoShift h m z = SqU6.liftO g := by
    have hid := SqU6.sqRelWord_gaTwoDress (m := m) hga
    rw [hshift] at hid
    exact (mul_left_cancel hid).symm
  have hF : ¬ GaTwoForces m := by
    intro hF
    have hb := hF z hach hone
    rw [hres, SqU6.liftO_o, hodd] at hb
    exact absurd hb (by decide)
  have hC : ¬ GaTwoCentral m := by
    intro hC
    obtain ⟨k, hk⟩ := hC z g hach hsh
    rw [hk, selPar_two_mul] at hgodd
    exact absurd hgodd (by decide)
  exact ⟨hF, hC, fun hO => hC (gaTwoCentral_of_gaTwoOrth hO)⟩

end Engine

/-! ## 4 The three knobs, instantiated -/

section Knobs

variable {h : ℕ} {j : Fin h} {S X Y U V : SqU6 gr3R} {c t : gr3R}

/-- A dressing carrying an achievable element on the sigma slot and `1` elsewhere is achievable
in every slot: `GradedGammaTwoCentral.cenSigDress_cenKill_mem` with the point removed. -/
theorem cens_sigDress_mem_forceLcs {H : Subgroup (SqU6 gr3R)} {w : SqU6 gr3R}
    (hw : w ∈ forceLcs H 1) (i : Fin (sqRank h)) : cenSigDress h w i ∈ forceLcs H 1 := by
  by_cases hi : (i : ℕ) = 0
  · rw [cenSigDress, if_pos hi]; exact hw
  · rw [cenSigDress, if_neg hi]; exact one_mem _

theorem censSlotU_mem_forceLcs {H : Subgroup (SqU6 gr3R)} {w : SqU6 gr3R}
    (hw : w ∈ forceLcs H 1) (i : Fin (sqRank h)) : censSlotU h j w i ∈ forceLcs H 1 := by
  by_cases hi : (i : ℕ) = (sqHandleIdxU j : ℕ)
  · rw [censSlotU, if_pos hi]; exact hw
  · rw [censSlotU, if_neg hi]; exact one_mem _

theorem censSlotV_mem_forceLcs {H : Subgroup (SqU6 gr3R)} {w : SqU6 gr3R}
    (hw : w ∈ forceLcs H 1) (i : Fin (sqRank h)) : censSlotV h j w i ∈ forceLcs H 1 := by
  by_cases hi : (i : ℕ) = (sqHandleIdxV j : ℕ)
  · rw [censSlotV, if_pos hi]; exact hw
  · rw [censSlotV, if_neg hi]; exact one_mem _

/-- ⭐⭐⭐ **THE SIGMA KNOB REFUTES ALL THREE LINES**, at every marking of the one-handle-live
family whose relator is an ODD central translation and whose image achieves the solving knob.
This is `GradedGammaTwoCentral.gaTwoForces_stageWit_false` and its two siblings with wave 60's
point replaced by hypotheses a census can check. -/
theorem cens_lines_false_of_sigKnob
    (hres : sqRelWord (fiveTuple gr3R h j S X Y U V) = SqU6.liftO c) (hodd : selPar c = 1)
    (ht : c + X.e * t = 0)
    (hach : SqU6.censKnob t
      ∈ forceLcs (Subgroup.closure (Set.range (fiveTuple gr3R h j S X Y U V))) 1) :
    ¬ GaTwoForces (fiveTuple gr3R h j S X Y U V)
      ∧ ¬ GaTwoCentral (fiveTuple gr3R h j S X Y U V)
      ∧ ¬ GaTwoOrth (fiveTuple gr3R h j S X Y U V) :=
  cens_lines_false_of_central_kill hres hodd (sqRelWord_cenSigDress_censKnob S X Y U V t) ht
    (cenSigDress_censKnob_isGaTwo t) (fun i => cens_sigDress_mem_forceLcs hach i)

/-- ⭐⭐⭐ **…and so does the `u`-HANDLE KNOB**, geared by the OTHER handle letter's
`(5,6)`-column.  ⚠ This is a route `GradedGammaTwoCentral` did not have: its refutation ran
through the sigma slot alone, and `scripts/w64_census5/results/census.txt` exhibits binder points
where the sigma slot has NO achievable kill at all and a handle slot has thousands. -/
theorem cens_lines_false_of_uKnob
    (hres : sqRelWord (fiveTuple gr3R h j S X Y U V) = SqU6.liftO c) (hodd : selPar c = 1)
    (ht : c + t * V.e = 0)
    (hach : SqU6.censKnob t
      ∈ forceLcs (Subgroup.closure (Set.range (fiveTuple gr3R h j S X Y U V))) 1) :
    ¬ GaTwoForces (fiveTuple gr3R h j S X Y U V)
      ∧ ¬ GaTwoCentral (fiveTuple gr3R h j S X Y U V)
      ∧ ¬ GaTwoOrth (fiveTuple gr3R h j S X Y U V) :=
  cens_lines_false_of_central_kill hres hodd (sqRelWord_censSlotU_censKnob S X Y U V t) ht
    (censSlotU_isGaTwo (SqU6.censKnob_isGaTwo t)) (fun i => censSlotU_mem_forceLcs hach i)

/-- ⭐⭐⭐ …and the `v`-handle knob, geared by `-u_j.e`. -/
theorem cens_lines_false_of_vKnob
    (hres : sqRelWord (fiveTuple gr3R h j S X Y U V) = SqU6.liftO c) (hodd : selPar c = 1)
    (ht : c + -(t * U.e) = 0)
    (hach : SqU6.censKnob t
      ∈ forceLcs (Subgroup.closure (Set.range (fiveTuple gr3R h j S X Y U V))) 1) :
    ¬ GaTwoForces (fiveTuple gr3R h j S X Y U V)
      ∧ ¬ GaTwoCentral (fiveTuple gr3R h j S X Y U V)
      ∧ ¬ GaTwoOrth (fiveTuple gr3R h j S X Y U V) :=
  cens_lines_false_of_central_kill hres hodd (sqRelWord_censSlotV_censKnob S X Y U V t) ht
    (censSlotV_isGaTwo (SqU6.censKnob_isGaTwo t)) (fun i => censSlotV_mem_forceLcs hach i)

end Knobs

/-! ## 5 The census criterion: what a survivor must satisfy, at THREE slots -/

section Criterion

variable {h : ℕ} {j : Fin h} {S X Y U V : SqU6 gr3R} {c : gr3R}

/-- **The knob equation is solvable exactly when the gearing is a unit**, and then the solution
has the parity of the residue: over `ZMod 8` an odd `u` is invertible and `t = -c u^{-1}`. -/
theorem censKnob_solve : ∀ c u : gr3R, selPar u = 1 →
    ∃ t : gr3R, c + u * t = 0 ∧ selPar t = selPar c ∧ selPar (u * t) = selPar c := by decide

/-- ⭐ **An even gearing is a dead knob.**  If the gearing is EVEN then the knob's translation
`SqU6.liftO (u * t)` is even whatever `t` is, so it can never cancel an odd residue and that
knob is silent at the point. -/
theorem censKnob_shift_even_of_gear_even {u : gr3R} (hu : selPar u = 0) (t : gr3R) :
    selPar (u * t) = 0 := by rw [selPar_mul, hu, zero_mul]

/-- ⭐⭐⭐ **THE CENSUS CRITERION, quantified over binder points.**  Let a marking of the
one-handle-live family have an ODD CENTRAL relator - which is exactly what makes it a class-five
binder point.  If the `gamma_2` forcing HOLDS there, then for **each** of the three gearings
`x0.e`, `v_j.e`, `u_j.e`,

* either the gearing is EVEN,
* or the achievable `gamma_2` lattice of the image misses `censKnob t` for the (unique) `t` that
  solves that knob's equation, and that `t` is ODD.

⚠ This is the exact form of `GradedGammaTwoCentral`'s prose criterion, and it is sharper in three
ways: it is quantified over points rather than stated at one; it runs at THREE slots rather than
at the sigma slot alone; and its second horn is the single membership `censKnob t ∉ forceLcs _ 1`
rather than the coarser "the lattice has an even class-four coordinate at that slot".  The two
are NOT the same, and `scripts/w64_census5/results/census.txt` exhibits binder points where a
lattice with odd class-four coordinates still misses the knob. -/
theorem cens_survivor_dichotomy {u : gr3R} {m : Fin (sqRank h) → SqU6 gr3R}
    {Z : gr3R → Fin (sqRank h) → SqU6 gr3R}
    (hres : sqRelWord m = SqU6.liftO c) (hodd : selPar c = 1)
    (hshift : ∀ t : gr3R,
      sqRelWord (conFiveDress m (Z t)) = sqRelWord m * SqU6.liftO (u * t))
    (hga : ∀ (t : gr3R) i, (Z t i).IsGaTwo)
    (hmem : ∀ t : gr3R, SqU6.censKnob t ∈ forceLcs (Subgroup.closure (Set.range m)) 1 →
      ∀ i, Z t i ∈ forceLcs (Subgroup.closure (Set.range m)) 1)
    (hF : GaTwoForces m) :
    selPar u = 0 ∨ ∃ t : gr3R, selPar t = 1 ∧ c + u * t = 0
      ∧ SqU6.censKnob t ∉ forceLcs (Subgroup.closure (Set.range m)) 1 := by
  by_cases hu : selPar u = 0
  · exact Or.inl hu
  have hu1 : selPar u = 1 := by
    revert hu
    generalize selPar u = s
    revert s
    decide
  obtain ⟨t, ht, htpar, -⟩ := censKnob_solve c u hu1
  refine Or.inr ⟨t, by rw [htpar, hodd], ht, fun hach => ?_⟩
  exact (cens_lines_false_of_central_kill hres hodd (hshift t) ht (hga t) (hmem t hach)).1 hF

/-- ⭐⭐ **The dichotomy at the SIGMA slot**, with the gearing `x0.e`. -/
theorem cens_sigKnob_dichotomy
    (hres : sqRelWord (fiveTuple gr3R h j S X Y U V) = SqU6.liftO c) (hodd : selPar c = 1)
    (hF : GaTwoForces (fiveTuple gr3R h j S X Y U V)) :
    selPar X.e = 0 ∨ ∃ t : gr3R, selPar t = 1 ∧ c + X.e * t = 0 ∧ SqU6.censKnob t
      ∉ forceLcs (Subgroup.closure (Set.range (fiveTuple gr3R h j S X Y U V))) 1 :=
  cens_survivor_dichotomy (Z := fun t => cenSigDress h (SqU6.censKnob t)) hres hodd
    (fun t => sqRelWord_cenSigDress_censKnob S X Y U V t)
    (fun t => cenSigDress_censKnob_isGaTwo t)
    (fun _ hach i => cens_sigDress_mem_forceLcs hach i) hF

/-- ⭐⭐ **…at the `u`-handle slot**, with the gearing `v_j.e`. -/
theorem cens_uKnob_dichotomy
    (hres : sqRelWord (fiveTuple gr3R h j S X Y U V) = SqU6.liftO c) (hodd : selPar c = 1)
    (hF : GaTwoForces (fiveTuple gr3R h j S X Y U V)) :
    selPar V.e = 0 ∨ ∃ t : gr3R, selPar t = 1 ∧ c + V.e * t = 0 ∧ SqU6.censKnob t
      ∉ forceLcs (Subgroup.closure (Set.range (fiveTuple gr3R h j S X Y U V))) 1 :=
  cens_survivor_dichotomy (Z := fun t => censSlotU h j (SqU6.censKnob t)) hres hodd
    (fun t => by rw [sqRelWord_censSlotU_censKnob, mul_comm t])
    (fun t => censSlotU_isGaTwo (SqU6.censKnob_isGaTwo t))
    (fun _ hach i => censSlotU_mem_forceLcs hach i) hF

/-- ⭐⭐ **…and at the `v`-handle slot**, with the gearing `-u_j.e`. -/
theorem cens_vKnob_dichotomy
    (hres : sqRelWord (fiveTuple gr3R h j S X Y U V) = SqU6.liftO c) (hodd : selPar c = 1)
    (hF : GaTwoForces (fiveTuple gr3R h j S X Y U V)) :
    selPar (-U.e) = 0 ∨ ∃ t : gr3R, selPar t = 1 ∧ c + -U.e * t = 0 ∧ SqU6.censKnob t
      ∉ forceLcs (Subgroup.closure (Set.range (fiveTuple gr3R h j S X Y U V))) 1 :=
  cens_survivor_dichotomy (Z := fun t => censSlotV h j (SqU6.censKnob t)) hres hodd
    (fun t => by rw [sqRelWord_censSlotV_censKnob]; ring_nf)
    (fun t => censSlotV_isGaTwo (SqU6.censKnob_isGaTwo t))
    (fun _ hach i => censSlotV_mem_forceLcs hach i) hF

end Criterion

/-! ## 6 W63-CENTRAL2's point, widened to its whole family -/

section StageFamily

variable {h : ℕ} {j : Fin h}

/-- W63-CENTRAL2's killing dressing **is** the knob at `t = 3`. -/
theorem censKnob_eq_gaTwoCenKill : gaTwoCenKill = SqU6.censKnob (3 : gr3R) := rfl

/-- ⭐ **The kill at wave 60's point, from the general identity.**  `GradedGammaTwoCentral`
proved this by kernel computation on the reparametrised tuple; here it falls out of the knob
identity with `c = 1` and `stageX.e = 5`, since `1 + 5 * 3 = 0` in `ZMod 8`.  ⭐ Doctrine rule 3:
the two routes are made to meet, and they agree. -/
theorem sqRelWord_stageWit_censKnob (h : ℕ) (j : Fin h) :
    sqRelWord (conFiveDress (stageWit h j stageX) (cenSigDress h (SqU6.censKnob (3 : gr3R))))
      = 1 := by
  rw [stageWit, sqRelWord_cenSigDress_censKnob, ← stageWit, sqRelWord_stageWit_diag,
    SqU6.liftO_mul_liftO]
  decide

/-- ⭐⭐ **The whole `stageWit` FAMILY, not one point.**  At every sigma parameter `v` whose frame
has an ODD central relator, at every handle count and every handle, the three `gamma_2` lines fail
as soon as the solving knob is achievable - and the gearing `stageX.e = 5` is a unit at every
member of the family, so the knob equation always has a solution.  ⚠ Achievability is genuinely
a hypothesis: `scripts/w64_census5/results/census.txt` records binder points where the knob is NOT
achievable, so it cannot be dropped. -/
theorem stageWit_lines_false_of_censKnob {v : SqU6 gr3R} {c t : gr3R}
    (hres : sqRelWord (stageWit h j v) = SqU6.liftO c) (hodd : selPar c = 1)
    (ht : c + (5 : gr3R) * t = 0)
    (hach : SqU6.censKnob t ∈ forceLcs (stageImage h j v) 1) :
    ¬ GaTwoForces (stageWit h j v) ∧ ¬ GaTwoCentral (stageWit h j v)
      ∧ ¬ GaTwoOrth (stageWit h j v) := by
  rw [stageImage] at hach
  rw [stageWit] at hres hach ⊢
  exact cens_lines_false_of_sigKnob hres hodd
    (by rw [show stageX.e = (5 : gr3R) from rfl]; exact ht) hach

end StageFamily

/-! ## 7 W63-LIVE5's point: the composite W63 left open -/

section LiveBlk

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐ **The knob is achievable at `GradedFiveLive`'s point too**, by a certificate simpler than
wave 60's: a product of TWO honest commutators of the point's own letters, with no inverse and no
power. -/
theorem liveBlk_censKnob_comm_form :
    SqU6.censKnob (3 : gr3R) = commP liveBlkU (liveBlkSig * stageX)
      * commP (liveBlkSig * stageX) liveBlkV := by decide

/-- …so `censKnob 3` lies in the honest `gamma_2` of `GradedFiveLive`'s image subgroup. -/
theorem liveBlk_censKnob_mem :
    SqU6.censKnob (3 : gr3R) ∈ forceLcs (liveBlkImage h j stageX) 1 := by
  have hS : liveBlkSig * stageX ∈ liveBlkImage h j stageX :=
    Subgroup.subset_closure ⟨0, by rw [liveBlkWit, fiveTuple_zero]⟩
  have hU : liveBlkU ∈ liveBlkImage h j stageX :=
    Subgroup.subset_closure ⟨sqHandleIdxU j, by rw [liveBlkWit, fiveTuple_handleU]⟩
  have hV : liveBlkV ∈ liveBlkImage h j stageX :=
    Subgroup.subset_closure ⟨sqHandleIdxV j, by rw [liveBlkWit, fiveTuple_handleV]⟩
  rw [liveBlk_censKnob_comm_form]
  exact mul_mem (commP_mem_commSub hU hS) (commP_mem_commSub hS hV)

/-- ⭐⭐⭐ **W63-LIVE5's point is killed by W63-CENTRAL2's own dressing.**  `liveBlkWit` reuses
`stageX` in the `x0` slot, which is exactly the slot the sigma knob's gearing reads, and its
`a0 = a1` residue is the same odd `1`; so `censKnob 3` kills its DIAGONALLY dressed frame too, at
every handle count and every handle, and all three `gamma_2` lines fail there.  This is the
composite W63 recorded as unresolved.

⚠ What this does NOT touch is `GradedFiveLive`'s own stage-four exclusion
`sqRelWord_liveBlkWit_diag_ne_one`, which quantifies over `forceLcs _ 2`: the knob is not there,
by `censKnob_odd_not_mem_stageN3` below. -/
theorem liveBlkWit_lines_false (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (liveBlkWit h j stageX) ∧ ¬ GaTwoCentral (liveBlkWit h j stageX)
      ∧ ¬ GaTwoOrth (liveBlkWit h j stageX) := by
  rw [liveBlkWit]
  refine cens_lines_false_of_sigKnob (c := 1) (t := 3) ?_ (by decide) (by decide) ?_
  · rw [← liveBlkWit]; exact sqRelWord_liveBlkWit_diag h j
  · rw [← liveBlkWit, ← liveBlkImage]; exact liveBlk_censKnob_mem

/-- …and the kill itself, stated on the relator. -/
theorem sqRelWord_liveBlkWit_censKnob (h : ℕ) (j : Fin h) :
    sqRelWord (conFiveDress (liveBlkWit h j stageX)
      (cenSigDress h (SqU6.censKnob (3 : gr3R)))) = 1 := by
  rw [liveBlkWit, sqRelWord_cenSigDress_censKnob, ← liveBlkWit, sqRelWord_liveBlkWit_diag,
    SqU6.liftO_mul_liftO]
  decide

/-- ⭐ **The boundary is the one W63-CENTRAL2 drew.**  An odd knob is `gamma_3`-shaped with an ODD
class-four coordinate, so it is not an achievable STAGE-FOUR dressing at any marking with even
`(1,2)`- and `(3,4)`-columns, and no stage-four exclusion in the tree is touched. -/
theorem censKnob_odd_not_mem_stageN3 {t : gr3R} (ht : selPar t = 1) :
    SqU6.censKnob t ∉ stageN3 := by
  intro hz
  obtain ⟨s, hs⟩ := (stageN3_even hz).2.2
  rw [SqU6.censKnob_m] at hs
  rw [hs, selPar_two_mul] at ht
  exact absurd ht (by decide)

end LiveBlk

/-! ## 8 Axiom pins -/

section AxiomPins

#print axioms SqU6.censKnob
#print axioms SqU6.censKnob_m
#print axioms SqU6.censKnob_isGaThree
#print axioms SqU6.censKnob_isGaTwo
#print axioms SqU6.sqWord_mul_censKnob
#print axioms sqRelWord_fiveTuple_censKnob
#print axioms sqRelWord_cenSigDress_censKnob
#print axioms cenSigDress_censKnob_isGaTwo
#print axioms SqU6.commP_mul_censKnob_left
#print axioms SqU6.commP_mul_censKnob_right
#print axioms censSlotU
#print axioms censSlotV
#print axioms censSlotU_isGaTwo
#print axioms censSlotV_isGaTwo
#print axioms conFiveDress_fiveTuple_censSlotU
#print axioms conFiveDress_fiveTuple_censSlotV
#print axioms sqRelWord_censSlotU_censKnob
#print axioms sqRelWord_censSlotV_censKnob
#print axioms cens_lines_false_of_central_kill
#print axioms cens_sigDress_mem_forceLcs
#print axioms censSlotU_mem_forceLcs
#print axioms censSlotV_mem_forceLcs
#print axioms cens_lines_false_of_sigKnob
#print axioms cens_lines_false_of_uKnob
#print axioms cens_lines_false_of_vKnob
#print axioms censKnob_solve
#print axioms censKnob_shift_even_of_gear_even
#print axioms cens_survivor_dichotomy
#print axioms cens_sigKnob_dichotomy
#print axioms cens_uKnob_dichotomy
#print axioms cens_vKnob_dichotomy
#print axioms censKnob_eq_gaTwoCenKill
#print axioms sqRelWord_stageWit_censKnob
#print axioms stageWit_lines_false_of_censKnob
#print axioms liveBlk_censKnob_comm_form
#print axioms liveBlk_censKnob_mem
#print axioms liveBlkWit_lines_false
#print axioms sqRelWord_liveBlkWit_censKnob
#print axioms censKnob_odd_not_mem_stageN3

end AxiomPins

end SqCore

end Dyadic

end GQ2

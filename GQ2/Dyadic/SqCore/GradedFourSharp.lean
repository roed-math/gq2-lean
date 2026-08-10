/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFrameNecessity

/-!
# W60-MIGRATE: the committed class-four catalogue, moved onto the sharp line

`GradedFrameNecessity` (wave 59) proved that `GradedFourCleared.liveFrameSub`, the class-four
soundness hypothesis the campaign carries at every live-block point, is **merely sufficient**,
characterised the sharp condition (`sigmaForces_iff_frameOrth`, `FrameOrth`), and reported that
several committed points need only half of it.  This file spends that characterisation: it
migrates **every** committed class-four forcing statement onto the sharp line, and it verifies
wave 59's covector table rather than trusting it.

## ⭐⭐⭐ Headline 1: one mod-`2` functional, and the campaign carries four

At **every** committed point the class-four sigma forcing consumes exactly **one** mod-`2`
linear functional of the two handle moves - the pairing `sigIncrPair` - and the committed
statements carry **four** evenness conditions, one per class-three coordinate of each move,
supplied by a containment of the whole marking in `GradedFourRow.rowFrameSub` or
`GradedFourCleared.liveFrameSub`.

```text
point                wave  file              (U.d,U.a) (V.d,V.a)  carried      now needed
cleared   clrFour    W57   GradedFourCleared  (0, 1)   (0, 0)     all four     z₄.i even
live      liveFour   W57   GradedFourCleared  (0, 1)   (0, 0)     all four     z₄.i even
two-live  twoLive    W58   GradedFourTwoLive  (0, 1)   (0, 0)     all four     z₄.i even
doubly    dblFour    W56   GradedFourMirror   (0, 1)   (0, 1)     all four     z₄.i − z₃.i even
doubly ×  dblLive    W58   GradedFourTwoLive  (0, 1)   (0, 1)     all four     z₄.i − z₃.i even
mirror    mirFour    W56   GradedFourMirror   (0, 1)   (1, 0)     all four     z₃.h + z₄.i even
mirror ×  mirLive    W58   GradedFourTwoLive  (0, 1)   (1, 0)     all four     z₃.h + z₄.i even
2nd power hiLive     W58   GradedFourTwoLive  (0, 1)   (1, 0)     all four     z₃.h + z₄.i even
unclr-v   rowFour    W55   GradedFourRow      (1, 0)   (0, 1)     all four     z₃.i + z₄.h even
unclr-v   rowWide    W56   GradedFourMirror   (1, 0)   (0, 1)     all four     z₃.i + z₄.h even
unclr-v × rowLive    W58   GradedFourTwoLive  (1, 0)   (0, 1)     all four     z₃.i + z₄.h even
W58 KILL  oddLive    W58   GradedFourTwoLive  (0, 1)   (1, 0)     -            fails: block odd
```

(`×` marks a point with a **live** handle block; "all four" is evenness of `z₃.h`, `z₃.i`,
`z₄.h`, `z₄.i`.)  Each `…Wit_sigma_forced_sharp` is the migrated forcing at its point, and
`sharp_covector_table` verifies the whole table by `decide` over all eighteen letters, at every
pivot residue.

## ⭐⭐⭐ Headline 2: the achievability convention is not consumed either

The committed `…_sigma_forced_gaTwo` statements quantify the two handle moves over
`GradedFourRow.rowGaTwoOf` of the marking's image - the campaign's standing achievability
convention.  **Every `…_sharp` statement of this file quantifies over nothing at all**: it takes
the parity as a hypothesis and holds for arbitrary `γ₃`-shaped moves.  So achievability is not
what the forcing needs; the *parity achievability supplies* is.  That refines wave 58's measured
"achievability is load-bearing", and ⭐⭐⭐ `clrFour_unrestricted_sigma_forced_false` turns the
measurement into a theorem at the cleared row: `GradedFrameNecessity.mixMove`, one `γ₃`-move with
an odd second class-three coordinate, kills the relator at the odd dressing
(`clrFour_sharp_kill`).  The single hypothesis is therefore load-bearing and not a convenience.

## ⭐⭐ Headline 3: on the achievable set, half at five points and the whole at six

Read as a condition on the achievable set rather than on one pair of moves, the reduction is
uneven, and this is the honest half of the report.

```text
group                                        carried              sharp                factor
cleared, live, two-live, doubly (dead+live)  z.h even ∧ z.i even  z.i even             2
mirror, mirror-live, second power            z.h even ∧ z.i even  z.h even ∧ z.i even  1
uncleared-v, wide, row-live                  z.h = 0 ∧ z.i even   z.h even ∧ z.i even  1
```

⭐⭐⭐ `clrFour_frameOrth_iff` and its ten siblings prove this **in both directions**, so the
per-point condition is the weakest one, not merely a sufficient one; wave 59 supplied only the
`←` half (`frameOrth_of_gaTwo_i_even`).  At the six points of the second and third rows the
answer is that the campaign needs what it carries on the achievable set, and the reduction is
only from the frame containment to its consequence.  **Six of the eleven committed points get no
factor of two, and saying so is the point of the lane.**

## ⭐⭐ Headline 4: the covectors are pivot-invariant, so the committed composites are sound

The displaced points state the forcing at the **cleared frame** while drawing moves from the
**displaced marking**'s `γ₂`; the two have different handle letters.  ⭐⭐
`covectors_pivot_invariant` checks that a pivot power moves the first abelian column by a
multiple of `2` and leaves the fourth alone, so marking and frame impose the *same* mod-`2`
condition at every residue.  Without that the committed `_gaTwo` statements would have been
mixing two objects; with it they are sound, and the migration may read one table for both.

## ⭐⭐⭐ Headline 5: the same table predicts the tree's one refutation

⭐⭐⭐ `oddLive_not_frameOrth`.  Wave 58's killing point is read by the same covector table, lands
in the *full* group, and its block is odd in the first class-three coordinate - so the sharp
invariant **fails** there, recovering `GradedFrameNecessity.twoLiveOdd_not_sigmaForces` from the
migration rather than being contradicted by it.  ⭐⭐⭐ `sharp_migration` states the whole outcome
once: eleven committed points on the line, the killing point off it.

## The sweep against every refutation in the tree

* `GradedFourTwoLive.twoLiveOdd_kill` / `twoLiveOdd_sigma_forced_false` (the forcing FAILS at
  `twoLiveMark … sigFourU oddLiveV`): swept, and **predicted** - `oddLive_not_frameOrth`.
* `GradedFrameNecessity.mix_unrestricted_kill` / `mix_unrestricted_sigma_forced_false` (an
  unachievable move kills at the mixed point): no conflict; that move has odd second class-three
  coordinate, which is exactly what every `…_sharp` statement excludes by hypothesis.  The
  cleared-row analogue is proved here.
* `GradedFrameNecessity.orth_not_le_liveFrameSub`, `mix_not_le_liveFrameSub`,
  `frameOrth_strictly_weaker` (the carried hypothesis fails where the forcing holds): consistent
  by construction - `frameOrth_of_gaTwo_even` supersedes `frameOrth_of_le_liveFrameSub` and is
  strictly weaker.
* `liveFour_not_rowGaTwoSub`, `mirLive_not_rowGaTwoSub`, `rowLive_not_rowGaTwoSub`,
  `dblLive_not_rowGaTwoSub`, `hiLive_not_rowGaTwoSub`, `twoLive_not_rowGaTwoSub` (the sharper
  wave-55 bound is false at every live point): consistent - nothing here asks for a *vanishing*
  first class-three coordinate; the uncleared-`v` migration explicitly weakens `z.h = 0` to
  `z.h` even.
* `GradedFourTwoLive.commP_coupling_ne_zero_imp`: its docstring's last sentence was the one
  claim of the tree this lane had to **repair** rather than merely sweep; see below.
* `GradedLatticeWide.selLamThreePlus_not_commP_zero_handleV` and the class-five refutations of
  wave 59: different class or different object; untouched.

## Did any committed statement rely on more than it stated?

**No.**  Every `…_gaTwo` companion discharges its evenness from a soundness lemma whose
quantifier is the achievable set the statement itself names, and the displaced-row composite is
sound by `covectors_pivot_invariant`.  `GradedFourRow.rowFourWit_increment_even_gaTwo` uses
`z₄.h = 0` rather than "even", but that is what `rowGaTwoSub` supplies at its own point.
Nothing was found under-stated.

## Docstrings repaired

* `GradedFourTwoLive.commP_coupling_ne_zero_imp`: "it is unavailable to any point the forcing can
  be run at" is **false**.  `GradedFrameNecessity.orthV` has a nonzero `c`-column, sits outside
  `liveFrameSub`, and the forcing holds at it.  Wave 59 noted this in its own file and left the
  committed docstring standing; it is annotated now.
* `GradedFourCleared` §6 header: "which is all the increment lemma asks" overstates; the
  increment asks only for the pairing.
* `GradedFourCleared` module docstring, "Soundness at the live point, and the sharpest bound":
  right about the conclusion, wrong if read as a claim about the hypothesis - at that point the
  first class-three coordinate is never read.

`GradedFourMirror`, `GradedFourRow` and `GradedLatticeWide` were swept and need no repair.
`GradedLatticeWide` already states its class-four commutator bound in **pairing** language
("pair evenly against both handle letters' outer columns"), one wave before the pairing was
isolated - the formulation was available and was not used.

## PROVED versus carried versus measured

**PROVED**, with no live hypothesis: the two covector readings; the sharp invariant as a mod-`2`
statement and its four specialisations, each an **equivalence**; the carried hypothesis spent
down to its consequence and the dual half; the forcing on the pairing at all four committed
witness shapes; the covector table and its pivot invariance; all eleven committed points, in
both directions, at every handle count, every handle and every pivot residue; the certified
negative at the cleared row; the prediction of the wave-58 refutation.

**Carried, and named**: nothing.  The `…_frameOrth_iff` and `…_sigmaForces` statements mention
`rowGaTwoOf`, but only as the set the *committed* statements quantify over; the migrated forcing
statements consume no convention at all.

**Measured, not proved**: nothing new.  This file adds no census; wave 59's `6932`-marking
sweep is what found the line, and everything here is derived from the characterisation.

## What this does NOT do

* It does not modify a committed statement or proof.  Every result is a new named corollary that
  supersedes one, plus three docstring repairs.
* It does not migrate the **hom-level** statements (`sqArbFrame_sigma_forced_…`).  Those compose
  a frame identification with the witness-level forcing; the migration of the second factor is
  here and the composite is mechanical, but it is not written.
* It does not touch the lattice-level `…_sigma_forced` / `…_lam` companions, which consume
  `selLamThree` rather than achievability; their reduction is the same one and is not stated.
* It does not build a point at a displaced row outside the frame invariant.  Wave 59 said its
  §6 rule of thumb about the displaced rows is a reading of the covectors; this file verifies
  the covectors and leaves the point unbuilt.
* It says nothing about class five.  The class-four precedent - a carried soundness hypothesis
  that turned out strictly stronger than the line - is the campaign's reason to expect the same
  at class five, and it is a wave-60 item elsewhere.

## Contents

* **1** the two covector readings of the pairing;
* **2** ⭐⭐⭐ the sharp invariant in parities, and its four specialisations as equivalences;
* **3** ⭐⭐ the carried hypothesis spent down to its consequence, and the dual half;
* **4** ⭐⭐⭐ the forcing on the pairing at all four committed witness shapes;
* **5** ⭐⭐⭐ the covector table and its pivot invariance;
* **6** group A - the cleared row, the live point, the two-live point: one condition;
* **7** group B - the doubly displaced row, dead and live: one condition;
* **8** group C - the mirror row, its live version, the second power: both coordinates;
* **9** group D - the uncleared-`v` row, wide and live: both coordinates;
* **10** ⭐⭐⭐ the sweep, the certified negative, and the migration in one statement;
* **11** axiom pins, with the superseded statements printed alongside.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`; every `decide` is on `ZMod 8`, `ZMod 2` or tuples
over them.  All **54** committed prints are **std-3** (`propext`, `Classical.choice`,
`Quot.sound`) or a subset (`52` std-3, `2` `propext` + `Quot.sound`), and each is printed
alongside the statement it supersedes: **the migration changes no axiom footprint anywhere.**
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 Reading the pairing off the two covectors -/

section Reading

variable {R : Type} [CommRing R] {h : ℕ} {j : Fin h} {m : Fin (sqRank h) → SqU5 R} {z : SqU5 R}

/-- The **left** half of the pairing, which is all `FrameOrth`'s first clause reads: the
`v`-slot's mod-`2` covector `(V.d, V.a)` applied to the move's class-three coordinates. -/
theorem sigIncrPair_left :
    sigIncrPair m j z 1 = z.h * (m (sqHandleIdxV j)).d - z.i * (m (sqHandleIdxV j)).a := by
  simp only [sigIncrPair, SqU5.one_h, SqU5.one_i]
  ring

/-- The **right** half, which is all `FrameOrth`'s second clause reads: the `u`-slot's covector
`(U.d, U.a)`. -/
theorem sigIncrPair_right :
    sigIncrPair m j 1 z = (m (sqHandleIdxU j)).a * z.i - (m (sqHandleIdxU j)).d * z.h := by
  simp only [sigIncrPair, SqU5.one_h, SqU5.one_i]
  ring

end Reading

/-! ## 2 The sharp invariant read purely in parities -/

section Parities

variable {h : ℕ} {j : Fin h} {m : Fin (sqRank h) → SqU5 gr3R}

/-- ⭐⭐⭐ **THE SHARP INVARIANT IS A MOD-`2` STATEMENT, AND THIS IS IT.**  `FrameOrth` holds
exactly when, for every achievable `γ₃`-shaped move, the two mod-`2` covectors of the handle
slots annihilate the pair `(z.h, z.i)`.  Everything below is this identity with the covectors
of a committed point substituted in. -/
theorem frameOrth_iff_par :
    FrameOrth m j ↔ ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range m)), z.IsGaThree →
      selPar z.h * selPar (m (sqHandleIdxV j)).d = selPar z.i * selPar (m (sqHandleIdxV j)).a
        ∧ selPar (m (sqHandleIdxU j)).a * selPar z.i
            = selPar (m (sqHandleIdxU j)).d * selPar z.h := by
  constructor
  · intro hO z hz hz3
    obtain ⟨h1, h2⟩ := hO z hz hz3
    rw [sigIncrPair_left, ← selPar_eq_zero_iff, selPar_sub, selPar_mul, selPar_mul,
      sub_eq_zero] at h1
    rw [sigIncrPair_right, ← selPar_eq_zero_iff, selPar_sub, selPar_mul, selPar_mul,
      sub_eq_zero] at h2
    exact ⟨h1, h2⟩
  · intro hp z hz hz3
    obtain ⟨h1, h2⟩ := hp z hz hz3
    constructor
    · refine (selPar_eq_zero_iff _).mp ?_
      rw [sigIncrPair_left, selPar_sub, selPar_mul, selPar_mul, sub_eq_zero]
      exact h1
    · refine (selPar_eq_zero_iff _).mp ?_
      rw [sigIncrPair_right, selPar_sub, selPar_mul, selPar_mul, sub_eq_zero]
      exact h2

/-- ⭐⭐⭐ **HALF THE CARRIED HYPOTHESIS, AND EXACTLY HALF.**  When the `u`-covector is `(0, 1)`
and the `v`-slot's fourth abelian column is even, the sharp invariant is **equivalent** to
"every achievable move has even *second* class-three coordinate".  Wave 59's
`frameOrth_of_gaTwo_i_even` is the `←` half; the `→` half is what makes the reduction sharp
rather than merely sufficient. -/
theorem frameOrth_iff_i_even (hUa : selPar (m (sqHandleIdxU j)).a = 1)
    (hUd : selPar (m (sqHandleIdxU j)).d = 0) (hVd : selPar (m (sqHandleIdxV j)).d = 0) :
    FrameOrth m j ↔ ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range m)), z.IsGaThree →
      ∃ k : gr3R, z.i = 2 * k := by
  rw [frameOrth_iff_par]
  constructor <;> intro hp z hz hz3
  · have h2 := (hp z hz hz3).2
    rw [hUa, hUd, one_mul, zero_mul] at h2
    exact (selPar_eq_zero_iff _).mp h2
  · have hi : selPar z.i = 0 := (selPar_eq_zero_iff _).mpr (hp z hz hz3)
    rw [hUa, hUd, hVd, hi]
    exact ⟨by ring, by ring⟩

/-- ⭐⭐⭐ **The dual half.**  When the `v`-covector is `(1, 0)` and the `u`-slot's first abelian
column is even, the sharp invariant is equivalent to "every achievable move has even *first*
class-three coordinate".  No committed point of the catalogue is of this type: the campaign's
`u`-letters all carry an odd `chi_a`-character, which is what keeps the second coordinate in
play everywhere. -/
theorem frameOrth_iff_h_even (hVd : selPar (m (sqHandleIdxV j)).d = 1)
    (hVa : selPar (m (sqHandleIdxV j)).a = 0) (hUa : selPar (m (sqHandleIdxU j)).a = 0) :
    FrameOrth m j ↔ ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range m)), z.IsGaThree →
      ∃ k : gr3R, z.h = 2 * k := by
  rw [frameOrth_iff_par]
  constructor <;> intro hp z hz hz3
  · have h1 := (hp z hz hz3).1
    rw [hVd, hVa, mul_one, mul_zero] at h1
    exact (selPar_eq_zero_iff _).mp h1
  · have hh : selPar z.h = 0 := (selPar_eq_zero_iff _).mpr (hp z hz hz3)
    rw [hVd, hVa, hUa, hh]
    exact ⟨by ring, by ring⟩

/-- ⭐⭐ **The full hypothesis, and it really is needed.**  When the `v`-covector is `(1, 0)` and
the `u`-covector is `(0, 1)` the two clauses read the two class-three coordinates separately, so
the sharp invariant is equivalent to the whole of what `liveFrameSub` supplies.  The mirror row,
the mirror-live row and the second-power row are of this type. -/
theorem frameOrth_iff_both_even (hUa : selPar (m (sqHandleIdxU j)).a = 1)
    (hUd : selPar (m (sqHandleIdxU j)).d = 0) (hVd : selPar (m (sqHandleIdxV j)).d = 1)
    (hVa : selPar (m (sqHandleIdxV j)).a = 0) :
    FrameOrth m j ↔ ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range m)), z.IsGaThree →
      (∃ k : gr3R, z.h = 2 * k) ∧ ∃ k : gr3R, z.i = 2 * k := by
  rw [frameOrth_iff_par]
  constructor <;> intro hp z hz hz3
  · obtain ⟨h1, h2⟩ := hp z hz hz3
    rw [hVd, hVa, mul_one, mul_zero] at h1
    rw [hUa, hUd, one_mul, zero_mul] at h2
    exact ⟨(selPar_eq_zero_iff _).mp h1, (selPar_eq_zero_iff _).mp h2⟩
  · obtain ⟨hh, hi⟩ := hp z hz hz3
    rw [hUa, hUd, hVd, hVa, (selPar_eq_zero_iff _).mpr hh, (selPar_eq_zero_iff _).mpr hi]
    exact ⟨by ring, by ring⟩

/-- ⭐⭐ **…and the same with the two roles swapped**, which is the uncleared-`v` family: the
`u`-covector is `(1, 0)` and the `v`-covector is `(0, 1)`.  The two clauses again read the two
coordinates separately, so the full hypothesis is needed here too. -/
theorem frameOrth_iff_both_even' (hUa : selPar (m (sqHandleIdxU j)).a = 0)
    (hUd : selPar (m (sqHandleIdxU j)).d = 1) (hVd : selPar (m (sqHandleIdxV j)).d = 0)
    (hVa : selPar (m (sqHandleIdxV j)).a = 1) :
    FrameOrth m j ↔ ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range m)), z.IsGaThree →
      (∃ k : gr3R, z.h = 2 * k) ∧ ∃ k : gr3R, z.i = 2 * k := by
  rw [frameOrth_iff_par]
  constructor <;> intro hp z hz hz3
  · obtain ⟨h1, h2⟩ := hp z hz hz3
    rw [hVd, hVa, mul_zero, mul_one] at h1
    rw [hUa, hUd, zero_mul, one_mul] at h2
    exact ⟨(selPar_eq_zero_iff _).mp h2.symm, (selPar_eq_zero_iff _).mp h1.symm⟩
  · obtain ⟨hh, hi⟩ := hp z hz hz3
    rw [hUa, hUd, hVd, hVa, (selPar_eq_zero_iff _).mpr hh, (selPar_eq_zero_iff _).mpr hi]
    exact ⟨by ring, by ring⟩

end Parities

/-! ## 3 The carried hypothesis spent down, and its dual -/

section Weakest

/-- Multiplying by an **odd** scalar does not change evenness, so a covector entry is read only
through its parity.  This is why a pivot-displaced marking and its cleared frame impose the
same condition. -/
theorem even_mul_odd_iff :
    ∀ u x : gr3R, selPar u = 1 → ((∃ k : gr3R, u * x = 2 * k) ↔ ∃ k : gr3R, x = 2 * k) := by
  decide

variable {h : ℕ} {j : Fin h} {m : Fin (sqRank h) → SqU5 gr3R}

/-- ⭐⭐ **The carried hypothesis, spent down to its consequence.**  `FrameOrth` needs only that
every achievable `γ₃`-shaped move be even in both class-three coordinates; membership of the
*slots* in `GradedFourCleared.liveFrameSub` is one way to get that and is never used again.
This supersedes `frameOrth_of_le_liveFrameSub`, which factors through it, and it is strictly
weaker: `GradedFrameNecessity.orth_frameOrth` and `mix_frameOrth` hold where the containment
fails. -/
theorem frameOrth_of_gaTwo_even
    (hall : ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range m)), z.IsGaThree →
      (∃ k : gr3R, z.h = 2 * k) ∧ ∃ k : gr3R, z.i = 2 * k) : FrameOrth m j := by
  have hone : (∃ a : gr3R, (1 : SqU5 gr3R).h = 2 * a) ∧ ∃ b : gr3R, (1 : SqU5 gr3R).i = 2 * b :=
    ⟨⟨0, by rw [SqU5.one_h]; ring⟩, 0, by rw [SqU5.one_i]; ring⟩
  intro z hz hz3
  exact ⟨sigIncrPair_even_of_gaThree_even (hall z hz hz3) hone,
    sigIncrPair_even_of_gaThree_even hone (hall z hz hz3)⟩

/-- ⭐⭐⭐ **The OTHER half is enough whenever both handle slots have an even first abelian
column.**  Then both covectors read only the first class-three coordinate.  This is the exact
dual of wave 59's `frameOrth_of_gaTwo_i_even`; the orthogonal point of `GradedFrameNecessity`
§5 is the degenerate case in which both covectors vanish outright. -/
theorem frameOrth_of_gaTwo_h_even
    (hUa : ∃ k : gr3R, (m (sqHandleIdxU j)).a = 2 * k)
    (hVa : ∃ k : gr3R, (m (sqHandleIdxV j)).a = 2 * k)
    (hh : ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range m)), z.IsGaThree →
      ∃ k : gr3R, z.h = 2 * k) : FrameOrth m j := by
  obtain ⟨ua, hua⟩ := hUa
  obtain ⟨va, hva⟩ := hVa
  intro z hz hz3
  obtain ⟨kz, hkz⟩ := hh z hz hz3
  refine ⟨⟨kz * (m (sqHandleIdxV j)).d - z.i * va, ?_⟩,
    ⟨ua * z.i - (m (sqHandleIdxU j)).d * kz, ?_⟩⟩ <;>
    simp only [sigIncrPair, hua, hva, hkz, SqU5.one_h, SqU5.one_i] <;>
    ring

end Weakest

/-! ## 4 The forcing at the committed witness shapes, on the pairing -/

section Shapes

variable {h : ℕ} {j : Fin h} {U V y v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R}

/-- ⭐⭐⭐ **`GradedFourMirror.mirWit_sigma_forced`, migrated.**  The dead-handle witness shape
forces an even `chi_a`-character as soon as the two handle moves pair evenly against the two
handle letters.  The committed hypothesis - both moves even in **both** class-three coordinates
- implies this and is strictly stronger. -/
theorem mirWit_sigma_forced_pair (hUV : commP U V = 1) (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (hp : ∃ k : gr3R, (z₃.h * V.d - z₃.i * V.a) + (U.a * z₄.i - U.d * z₄.h) = 2 * k)
    (hkill : sqRelWord (sigLift j (mirWit h j U V v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 := by
  rw [mirWit_eq_dress] at hkill
  exact gaugeX_sigma_forced_pair (by rw [mirWit_zero, mul_one]) mirWit_one
    (by rw [mirWit_two]; decide) (by rw [mirWit_two]; decide)
    (by rw [mirWit_two]; decide) (by rw [mirWit_two]; decide)
    (sqRelWord_mirWit_triv hUV) hvb hz₀ hw₁ hw₂ hz₃ hz₄
    (by simpa only [sigIncrPair, mirWit_handleU, mirWit_handleV] using hp) hkill

/-- ⭐⭐⭐ **`GradedFourTwoLive.liveWit_sigma_forced`, migrated.**  The same statement at the
live witness shape with its free `x₁`-slot. -/
theorem liveWit_sigma_forced_pair (hya : y.a = 0) (hyb : y.b = 0) (hyc : y.c = 0) (hyd : y.d = 0)
    (hrel : sqRelWord (liveWit h j y U V 1) = 1) (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (hp : ∃ k : gr3R, (z₃.h * V.d - z₃.i * V.a) + (U.a * z₄.i - U.d * z₄.h) = 2 * k)
    (hkill : sqRelWord (sigLift j (liveWit h j y U V v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 := by
  rw [liveWit_eq_dress] at hkill
  exact gaugeX_sigma_forced_pair (by rw [liveWit_zero, mul_one]) liveWit_one
    (by rw [liveWit_two]; exact hya) (by rw [liveWit_two]; exact hyb)
    (by rw [liveWit_two]; exact hyc) (by rw [liveWit_two]; exact hyd) hrel hvb hz₀ hw₁ hw₂
    hz₃ hz₄ (by simpa only [sigIncrPair, liveWit_handleU, liveWit_handleV] using hp) hkill

variable {j₁ j₂ : Fin h}

/-- ⭐⭐⭐ **`GradedFourTwoLive.twoLiveWit_sigma_forced`, migrated.**  The same statement at the
two-live-handle witness shape. -/
theorem twoLiveWit_sigma_forced_pair (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (hp : ∃ k : gr3R, (z₃.h * V.d - z₃.i * V.a) + (U.a * z₄.i - U.d * z₄.h) = 2 * k)
    (hkill : sqRelWord (sigLift j₁ (twoLiveWit h j₁ j₂ U V v) z₀ w₁ w₂ z₃ z₄) = 1)
    (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    selPar v.a = 0 := by
  rw [twoLiveWit_eq_dress] at hkill
  refine gaugeX_sigma_forced_pair (by rw [twoLiveWit, twoTuple_zero, mul_one])
    (by rw [twoLiveWit, twoTuple_one]) (by rw [twoLiveWit, twoTuple_two]; decide)
    (by rw [twoLiveWit, twoTuple_two]; decide) (by rw [twoLiveWit, twoTuple_two]; decide)
    (by rw [twoLiveWit, twoTuple_two]; decide)
    (by rw [twoLiveWit_one]; exact sqRelWord_twoLiveMark hlt) hvb hz₀ hw₁ hw₂ hz₃ hz₄ ?_ hkill
  simpa only [sigIncrPair, twoLiveWit, twoTuple_handleU_one, twoTuple_handleV_one] using hp

/-- ⭐⭐⭐ **`GradedFourRow.rowFourWit_sigma_forced`, migrated.**  Wave 55's witness shape is
built from `rowTuple` rather than from `mirWit`, so it gets its own migration. -/
theorem rowFourWit_sigma_forced_pair {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (hp : ∃ k : gr3R, (z₃.h * rowFourV.d - z₃.i * rowFourV.a)
      + (rowFourU.a * z₄.i - rowFourU.d * z₄.h) = 2 * k)
    (hkill : sqRelWord (sigLift 0 (rowFourWit v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 := by
  rw [rowFourWit_eq_dress] at hkill
  exact gaugeX_sigma_forced_pair (by rw [rowFourWit_zero, mul_one]) (rowFourWit_one 1)
    (by rw [rowFourWit_two]; decide) (by rw [rowFourWit_two]; decide)
    (by rw [rowFourWit_two]; decide) (by rw [rowFourWit_two]; decide)
    sqRelWord_rowFourWit_triv hvb hz₀ hw₁ hw₂ hz₃ hz₄
    (by simpa only [sigIncrPair, rowFourWit_handleU, rowFourWit_handleV] using hp) hkill

end Shapes

/-! ## 5 The covector table, verified -/

section Table

/-- ⭐⭐⭐ **THE COVECTOR TABLE OF THE WHOLE COMMITTED CATALOGUE, VERIFIED.**  Wave 59's
`committed_covectors` reads nine letters; this reads **all eighteen**, marking letters and
cleared frame letters, at every pivot residue.  The four blocks are the four rows of the
migration table: `(U.d, U.a)` then `(V.d, V.a)` at each point.

```text
point                         (U.d, U.a)   (V.d, V.a)   a move must satisfy
cleared / live / two-live       (0, 1)       (0, 0)     z.i even
doubly displaced, dead + live   (0, 1)       (0, 1)     z.i even
mirror, mirror-live, 2nd power  (0, 1)       (1, 0)     z.h and z.i even
uncleared-v, wide, row-live     (1, 0)       (0, 1)     z.h and z.i even
```
-/
theorem sharp_covector_table :
    ((selPar sigFourU.d = 0 ∧ selPar sigFourU.a = 1) ∧
        (selPar sigFourV.d = 0 ∧ selPar sigFourV.a = 0) ∧
        (selPar liveFourU.d = 0 ∧ selPar liveFourU.a = 1) ∧
        (selPar liveFourV.d = 0 ∧ selPar liveFourV.a = 0) ∧
        (selPar twoLiveU.d = 0 ∧ selPar twoLiveU.a = 1) ∧
        (selPar twoLiveV.d = 0 ∧ selPar twoLiveV.a = 0)) ∧
      ((selPar mirFourU.d = 0 ∧ selPar mirFourU.a = 1) ∧
        (selPar mirFourV.d = 1 ∧ selPar mirFourV.a = 0) ∧
        (selPar mirLiveV.d = 1 ∧ selPar mirLiveV.a = 0) ∧
        (selPar hiLiveV.d = 1 ∧ selPar hiLiveV.a = 0)) ∧
      ((selPar rowFourU.d = 1 ∧ selPar rowFourU.a = 0) ∧
        (selPar rowFourV.d = 0 ∧ selPar rowFourV.a = 1) ∧
        (selPar rowLiveU.d = 1 ∧ selPar rowLiveU.a = 0) ∧
        (selPar dblLiveV.d = 0 ∧ selPar dblLiveV.a = 1)) ∧
      ∀ c : gr3R,
        (selPar (mirFourUGen c).d = 0 ∧ selPar (mirFourUGen c).a = 1) ∧
          (selPar (rowFourVGen c).d = 0 ∧ selPar (rowFourVGen c).a = 1) ∧
          (selPar (dblLiveVGen c).d = 0 ∧ selPar (dblLiveVGen c).a = 1) ∧
          (selPar (hiLiveUGen c).d = 0 ∧ selPar (hiLiveUGen c).a = 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ⭐⭐⭐ **THE COVECTORS ARE PIVOT-INVARIANT.**  At all four displaced rows the marking's
handle letter differs from the cleared frame letter by a power of the pivot, which moves the
first abelian column by a multiple of `2` and leaves the fourth alone.  So the marking and the
frame impose **the same** mod-`2` condition, at every pivot residue - which is what lets the
migration read one table for both. -/
theorem covectors_pivot_invariant : ∀ c : gr3R,
    (selPar (mirFourUGen c).d = selPar mirFourU.d ∧
        selPar (mirFourUGen c).a = selPar mirFourU.a) ∧
      (selPar (rowFourVGen c).d = selPar rowFourV.d ∧
        selPar (rowFourVGen c).a = selPar rowFourV.a) ∧
      (selPar (dblLiveVGen c).d = selPar dblLiveV.d ∧
        selPar (dblLiveVGen c).a = selPar dblLiveV.a) ∧
      (selPar (hiLiveUGen c).d = selPar sigFourU.d ∧
        selPar (hiLiveUGen c).a = selPar sigFourU.a) := by
  decide

end Table

/-! ## 6 Group A: the cleared row, the live point and the two-live point -/

section GroupA

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐⭐ **THE CLEARED ROW NEEDS ONE MOD-`2` CONDITION, NOT FOUR.**  The `v`-covector vanishes
and the `u`-covector is `(0, 1)`, so the pairing is `z₄.i` modulo `2` and nothing else: the
forcing at the cleared row is driven by the **second** class-three coordinate of the **second**
handle move alone.  `GradedFourCleared.clrFourWit_sigma_forced_gaTwo` carries evenness of all
four coordinates of the two moves. -/
theorem clrFourWit_sigma_forced_sharp {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree) (h₄ : ∃ k : gr3R, z₄.i = 2 * k)
    (hkill : sqRelWord (sigLift j (clrFourWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 := by
  obtain ⟨k₄, hk₄⟩ := h₄
  simp only [clrFourWit] at hkill
  refine mirWit_sigma_forced_pair commP_clrFour hvb hz₀ hw₁ hw₂ hz₃ hz₄ ⟨k₄ - z₃.i, ?_⟩ hkill
  rw [hk₄, show (sigFourV.d : gr3R) = 0 from rfl, show (sigFourV.a : gr3R) = 2 from rfl,
    show (sigFourU.a : gr3R) = 1 from rfl, show (sigFourU.d : gr3R) = 0 from rfl]
  ring

/-- ⭐⭐⭐ **…and that is EXACTLY what the cleared point needs**, in both directions. -/
theorem clrFour_frameOrth_iff :
    FrameOrth (clrFourMark h j) j ↔
      ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range (clrFourMark h j))), z.IsGaThree →
        ∃ k : gr3R, z.i = 2 * k :=
  frameOrth_iff_i_even (by rw [clrFourMark_handleU]; decide)
    (by rw [clrFourMark_handleU]; decide) (by rw [clrFourMark_handleV]; decide)

/-- ⭐⭐ **The cleared point is on the sharp line**, discharged from half of its committed
soundness lemma. -/
theorem clrFour_sigmaForces : SigmaForces (clrFourMark h j) j :=
  sigmaForces_of_frameOrth clrFourMark_zero clrFourMark_one
    (by rw [clrFourMark_two]; decide) (by rw [clrFourMark_two]; decide)
    (by rw [clrFourMark_two]; decide) (by rw [clrFourMark_two]; decide)
    sqRelWord_clrFourMark
    (clrFour_frameOrth_iff.mpr fun _ hz _ => (clrFour_gaTwo_even hz).2)

/-- ⭐⭐⭐ **THE LIVE POINT NEEDS ONE MOD-`2` CONDITION.**  Same covectors as the cleared row,
with a live handle block. -/
theorem liveFourWit_sigma_forced_sharp {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree) (h₄ : ∃ k : gr3R, z₄.i = 2 * k)
    (hkill : sqRelWord (sigLift j (liveFourWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 := by
  obtain ⟨k₄, hk₄⟩ := h₄
  refine liveWit_sigma_forced_pair (y := liveFourY) (U := liveFourU) (V := liveFourV)
    (by decide) (by decide) (by decide) (by decide) ?_ hvb hz₀ hw₁ hw₂ hz₃ hz₄
    ⟨k₄ - z₃.i, ?_⟩ hkill
  · rw [show liveWit h j liveFourY liveFourU liveFourV 1 = liveFourMark h j from rfl]
    exact sqRelWord_liveFourMark
  · rw [hk₄, show (liveFourV.d : gr3R) = 0 from rfl, show (liveFourV.a : gr3R) = 2 from rfl,
      show (liveFourU.a : gr3R) = 1 from rfl, show (liveFourU.d : gr3R) = 0 from rfl]
    ring

theorem liveFour_frameOrth_iff :
    FrameOrth (liveFourMark h j) j ↔
      ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range (liveFourMark h j))), z.IsGaThree →
        ∃ k : gr3R, z.i = 2 * k :=
  frameOrth_iff_i_even (by rw [liveFourMark_handleU]; decide)
    (by rw [liveFourMark_handleU]; decide) (by rw [liveFourMark_handleV]; decide)

theorem liveFour_sigmaForces : SigmaForces (liveFourMark h j) j :=
  sigmaForces_of_frameOrth liveFourMark_zero liveFourMark_one
    (by rw [liveFourMark_two]; decide) (by rw [liveFourMark_two]; decide)
    (by rw [liveFourMark_two]; decide) (by rw [liveFourMark_two]; decide)
    sqRelWord_liveFourMark
    (liveFour_frameOrth_iff.mpr fun _ hz _ => (liveFour_gaTwo_even hz).2)

variable {j₁ j₂ : Fin h}

/-- ⭐⭐⭐ **THE TWO-LIVE POINT NEEDS ONE MOD-`2` CONDITION.**  Wave 58's headline point, the one
at which the frame invariant was declared load-bearing, uses a quarter of what it carries. -/
theorem twoLiveWit_sigma_forced_sharp {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree) (h₄ : ∃ k : gr3R, z₄.i = 2 * k)
    (hkill : sqRelWord (sigLift j₁ (twoLiveWit h j₁ j₂ twoLiveU twoLiveV v)
      z₀ w₁ w₂ z₃ z₄) = 1) (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    selPar v.a = 0 := by
  obtain ⟨k₄, hk₄⟩ := h₄
  refine twoLiveWit_sigma_forced_pair hvb hz₀ hw₁ hw₂ hz₃ hz₄ ⟨k₄ - z₃.i, ?_⟩ hkill hlt
  rw [hk₄, show (twoLiveV.d : gr3R) = 0 from rfl, show (twoLiveV.a : gr3R) = 2 from rfl,
    show (twoLiveU.a : gr3R) = 1 from rfl, show (twoLiveU.d : gr3R) = 0 from rfl]
  ring

theorem twoLive_frameOrth_iff :
    FrameOrth (twoLiveMark h j₁ j₂ twoLiveU twoLiveV) j₁ ↔
      ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range (twoLiveMark h j₁ j₂ twoLiveU twoLiveV))),
        z.IsGaThree → ∃ k : gr3R, z.i = 2 * k :=
  frameOrth_iff_i_even (by rw [twoLiveMark_handleU_one]; decide)
    (by rw [twoLiveMark_handleU_one]; decide) (by rw [twoLiveMark_handleV_one]; decide)

theorem twoLive_sigmaForces (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    SigmaForces (twoLiveMark h j₁ j₂ twoLiveU twoLiveV) j₁ :=
  sigmaForces_of_frameOrth twoLiveMark_zero twoLiveMark_one
    (by rw [twoLiveMark_two]; decide) (by rw [twoLiveMark_two]; decide)
    (by rw [twoLiveMark_two]; decide) (by rw [twoLiveMark_two]; decide)
    (sqRelWord_twoLiveMark hlt)
    (twoLive_frameOrth_iff.mpr fun _ hz _ => (twoLive_gaTwo_even (by omega) hz).2)

end GroupA

/-! ## 7 Group B: the doubly displaced row, dead and live -/

section GroupB

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐⭐ **THE DOUBLY DISPLACED ROW NEEDS ONE MOD-`2` CONDITION ON THE PAIR.**  Both covectors
are `(0, 1)`, so the pairing is `z₄.i - z₃.i`: the two moves' second class-three coordinates
need only agree modulo `2`, and neither has to be even. -/
theorem dblFourWit_sigma_forced_sharp {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree) (hp : ∃ k : gr3R, z₄.i - z₃.i = 2 * k)
    (hkill : sqRelWord (sigLift j (dblFourWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 := by
  obtain ⟨k, hk⟩ := hp
  simp only [dblFourWit] at hkill
  refine mirWit_sigma_forced_pair commP_dblFour hvb hz₀ hw₁ hw₂ hz₃ hz₄ ⟨k, ?_⟩ hkill
  rw [show (rowFourV.d : gr3R) = 0 from rfl, show (rowFourV.a : gr3R) = 1 from rfl,
    show (mirFourU.a : gr3R) = 1 from rfl, show (mirFourU.d : gr3R) = 0 from rfl]
  linear_combination hk

theorem dblFour_frameOrth_iff (c : gr3R) :
    FrameOrth (dblFourMark h j c) j ↔
      ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range (dblFourMark h j c))), z.IsGaThree →
        ∃ k : gr3R, z.i = 2 * k :=
  frameOrth_iff_i_even (by rw [dblFourMark_handleU]; revert c; decide)
    (by rw [dblFourMark_handleU]; revert c; decide)
    (by rw [dblFourMark_handleV]; revert c; decide)

theorem dblFour_sigmaForces (c : gr3R) : SigmaForces (dblFourMark h j c) j :=
  sigmaForces_of_frameOrth (dblFourMark_zero c) (dblFourMark_one c)
    (by rw [dblFourMark_two]; decide) (by rw [dblFourMark_two]; decide)
    (by rw [dblFourMark_two]; decide) (by rw [dblFourMark_two]; decide)
    (sqRelWord_dblFourMark c)
    ((dblFour_frameOrth_iff c).mpr fun _ hz _ => (dblFour_gaTwo_even hz).2)

/-- ⭐⭐⭐ **The doubly displaced LIVE row, same reading.** -/
theorem dblLiveWit_sigma_forced_sharp {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree) (hp : ∃ k : gr3R, z₄.i - z₃.i = 2 * k)
    (hkill : sqRelWord (sigLift j (dblLiveWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 := by
  obtain ⟨k, hk⟩ := hp
  simp only [dblLiveWit] at hkill
  refine liveWit_sigma_forced_pair (by decide) (by decide) (by decide) (by decide)
    sqRelWord_dblLiveWit_triv hvb hz₀ hw₁ hw₂ hz₃ hz₄ ⟨k, ?_⟩ hkill
  rw [show (dblLiveV.d : gr3R) = 0 from rfl, show (dblLiveV.a : gr3R) = 1 from rfl,
    show (mirFourU.a : gr3R) = 1 from rfl, show (mirFourU.d : gr3R) = 0 from rfl]
  linear_combination hk

theorem dblLive_frameOrth_iff (c : gr3R) :
    FrameOrth (dblLiveMark h j c) j ↔
      ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range (dblLiveMark h j c))), z.IsGaThree →
        ∃ k : gr3R, z.i = 2 * k :=
  frameOrth_iff_i_even (by rw [dblLiveMark_handleU]; revert c; decide)
    (by rw [dblLiveMark_handleU]; revert c; decide)
    (by rw [dblLiveMark_handleV]; revert c; decide)

theorem dblLive_sigmaForces (c : gr3R) : SigmaForces (dblLiveMark h j c) j :=
  sigmaForces_of_frameOrth (dblLiveMark_zero c) (dblLiveMark_one c)
    (by rw [dblLiveMark_two]; decide) (by rw [dblLiveMark_two]; decide)
    (by rw [dblLiveMark_two]; decide) (by rw [dblLiveMark_two]; decide)
    (sqRelWord_dblLiveMark c)
    ((dblLive_frameOrth_iff c).mpr fun _ hz _ => (dblLive_gaTwo_even c hz).2)

end GroupB

/-! ## 8 Group C: the mirror row, its live version, and the second power -/

section GroupC

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐ **THE MIRROR ROW GENUINELY NEEDS BOTH COORDINATES.**  The `v`-covector is `(1, 0)` and
the `u`-covector is `(0, 1)`, so the pairing is `z₃.h + z₄.i`: what is sharp here is the **sum**
of the first coordinate of the first move and the second coordinate of the second, and no
smaller hypothesis will do.  The reduction at this row is from four coordinate conditions to
one condition on a sum, not a factor of two on the achievable set. -/
theorem mirFourWit_sigma_forced_sharp {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree) (hp : ∃ k : gr3R, z₃.h + z₄.i = 2 * k)
    (hkill : sqRelWord (sigLift j (mirFourWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 := by
  obtain ⟨k, hk⟩ := hp
  simp only [mirFourWit] at hkill
  refine mirWit_sigma_forced_pair commP_mirFour hvb hz₀ hw₁ hw₂ hz₃ hz₄ ⟨k, ?_⟩ hkill
  rw [show (mirFourV.d : gr3R) = 1 from rfl, show (mirFourV.a : gr3R) = 0 from rfl,
    show (mirFourU.a : gr3R) = 1 from rfl, show (mirFourU.d : gr3R) = 0 from rfl]
  linear_combination hk

theorem mirFour_frameOrth_iff (c : gr3R) :
    FrameOrth (mirFourMark h j c) j ↔
      ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range (mirFourMark h j c))), z.IsGaThree →
        (∃ k : gr3R, z.h = 2 * k) ∧ ∃ k : gr3R, z.i = 2 * k :=
  frameOrth_iff_both_even (by rw [mirFourMark_handleU]; revert c; decide)
    (by rw [mirFourMark_handleU]; revert c; decide)
    (by rw [mirFourMark_handleV]; decide) (by rw [mirFourMark_handleV]; decide)

theorem mirFour_sigmaForces (c : gr3R) : SigmaForces (mirFourMark h j c) j :=
  sigmaForces_of_frameOrth (mirFourMark_zero c) (mirFourMark_one c)
    (by rw [mirFourMark_two]; decide) (by rw [mirFourMark_two]; decide)
    (by rw [mirFourMark_two]; decide) (by rw [mirFourMark_two]; decide)
    (sqRelWord_mirFourMark c)
    ((mirFour_frameOrth_iff c).mpr fun _ hz _ => mirFour_gaTwo_even hz)

/-- ⭐⭐ **The mirror LIVE row, same reading.** -/
theorem mirLiveWit_sigma_forced_sharp {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree) (hp : ∃ k : gr3R, z₃.h + z₄.i = 2 * k)
    (hkill : sqRelWord (sigLift j (mirLiveWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 := by
  obtain ⟨k, hk⟩ := hp
  simp only [mirLiveWit] at hkill
  refine liveWit_sigma_forced_pair (by decide) (by decide) (by decide) (by decide)
    sqRelWord_mirLiveWit_triv hvb hz₀ hw₁ hw₂ hz₃ hz₄ ⟨k, ?_⟩ hkill
  rw [show (mirLiveV.d : gr3R) = 1 from rfl, show (mirLiveV.a : gr3R) = 0 from rfl,
    show (mirFourU.a : gr3R) = 1 from rfl, show (mirFourU.d : gr3R) = 0 from rfl]
  linear_combination hk

theorem mirLive_frameOrth_iff (c : gr3R) :
    FrameOrth (mirLiveMark h j c) j ↔
      ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range (mirLiveMark h j c))), z.IsGaThree →
        (∃ k : gr3R, z.h = 2 * k) ∧ ∃ k : gr3R, z.i = 2 * k :=
  frameOrth_iff_both_even (by rw [mirLiveMark_handleU]; revert c; decide)
    (by rw [mirLiveMark_handleU]; revert c; decide)
    (by rw [mirLiveMark_handleV]; decide) (by rw [mirLiveMark_handleV]; decide)

theorem mirLive_sigmaForces (c : gr3R) : SigmaForces (mirLiveMark h j c) j :=
  sigmaForces_of_frameOrth (mirLiveMark_zero c) (mirLiveMark_one c)
    (by rw [mirLiveMark_two]; decide) (by rw [mirLiveMark_two]; decide)
    (by rw [mirLiveMark_two]; decide) (by rw [mirLiveMark_two]; decide)
    (sqRelWord_mirLiveMark c)
    ((mirLive_frameOrth_iff c).mpr fun _ hz _ => mirLive_gaTwo_even c hz)

/-- ⭐⭐ **The second-power row, same reading.** -/
theorem hiLiveWit_sigma_forced_sharp {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree) (hp : ∃ k : gr3R, z₃.h + z₄.i = 2 * k)
    (hkill : sqRelWord (sigLift j (hiLiveWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 := by
  obtain ⟨k, hk⟩ := hp
  simp only [hiLiveWit] at hkill
  refine liveWit_sigma_forced_pair (by decide) (by decide) (by decide) (by decide)
    sqRelWord_hiLiveWit_triv hvb hz₀ hw₁ hw₂ hz₃ hz₄ ⟨k, ?_⟩ hkill
  rw [show (hiLiveV.d : gr3R) = 1 from rfl, show (hiLiveV.a : gr3R) = 0 from rfl,
    show (sigFourU.a : gr3R) = 1 from rfl, show (sigFourU.d : gr3R) = 0 from rfl]
  linear_combination hk

theorem hiLive_frameOrth_iff (c : gr3R) :
    FrameOrth (hiLiveMark h j c) j ↔
      ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range (hiLiveMark h j c))), z.IsGaThree →
        (∃ k : gr3R, z.h = 2 * k) ∧ ∃ k : gr3R, z.i = 2 * k :=
  frameOrth_iff_both_even (by rw [hiLiveMark_handleU]; revert c; decide)
    (by rw [hiLiveMark_handleU]; revert c; decide)
    (by rw [hiLiveMark_handleV]; decide) (by rw [hiLiveMark_handleV]; decide)

theorem hiLive_sigmaForces (c : gr3R) : SigmaForces (hiLiveMark h j c) j :=
  sigmaForces_of_frameOrth (hiLiveMark_zero c) (hiLiveMark_one c)
    (by rw [hiLiveMark_two]; decide) (by rw [hiLiveMark_two]; decide)
    (by rw [hiLiveMark_two]; decide) (by rw [hiLiveMark_two]; decide)
    (sqRelWord_hiLiveMark c)
    ((hiLive_frameOrth_iff c).mpr fun _ hz _ => hiLive_gaTwo_even c hz)

end GroupC

/-! ## 9 Group D: the uncleared-`v` row, wide and live -/

section GroupD

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐ **THE UNCLEARED-`v` ROW GENUINELY NEEDS BOTH COORDINATES**, with the roles of the two
letters swapped: the pairing is `-(z₃.i + z₄.h)`. -/
theorem rowFourWit_sigma_forced_sharp {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree) (hp : ∃ k : gr3R, z₃.i + z₄.h = 2 * k)
    (hkill : sqRelWord (sigLift 0 (rowFourWit v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 := by
  obtain ⟨k, hk⟩ := hp
  refine rowFourWit_sigma_forced_pair hvb hz₀ hw₁ hw₂ hz₃ hz₄ ⟨-k, ?_⟩ hkill
  rw [show (rowFourV.d : gr3R) = 0 from rfl, show (rowFourV.a : gr3R) = 1 from rfl,
    show (rowFourU.a : gr3R) = 0 from rfl, show (rowFourU.d : gr3R) = 1 from rfl]
  linear_combination -hk

theorem rowFour_frameOrth_iff (c : gr3R) :
    FrameOrth (rowFourMark c) 0 ↔
      ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowFourMark c))), z.IsGaThree →
        (∃ k : gr3R, z.h = 2 * k) ∧ ∃ k : gr3R, z.i = 2 * k :=
  frameOrth_iff_both_even' (by rw [rowFourMark_handleU]; decide)
    (by rw [rowFourMark_handleU]; decide) (by rw [rowFourMark_handleV]; revert c; decide)
    (by rw [rowFourMark_handleV]; revert c; decide)

theorem rowFour_sigmaForces (c : gr3R) : SigmaForces (rowFourMark c) 0 :=
  sigmaForces_of_frameOrth (rowFourMark_zero c) (rowFourMark_one c)
    (by rw [rowFourMark_two]; decide) (by rw [rowFourMark_two]; decide)
    (by rw [rowFourMark_two]; decide) (by rw [rowFourMark_two]; decide)
    (sqRelWord_rowFourMark c)
    ((rowFour_frameOrth_iff c).mpr fun _ hz _ =>
      ⟨⟨0, by rw [(rowFour_gaTwo_even hz).1]; ring⟩, (rowFour_gaTwo_even hz).2⟩)

/-- ⭐⭐ **The uncleared-`v` row at every handle count, same reading.** -/
theorem rowWideWit_sigma_forced_sharp {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree) (hp : ∃ k : gr3R, z₃.i + z₄.h = 2 * k)
    (hkill : sqRelWord (sigLift j (rowWideWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 := by
  obtain ⟨k, hk⟩ := hp
  simp only [rowWideWit] at hkill
  refine mirWit_sigma_forced_pair commP_rowWide hvb hz₀ hw₁ hw₂ hz₃ hz₄ ⟨-k, ?_⟩ hkill
  rw [show (rowFourV.d : gr3R) = 0 from rfl, show (rowFourV.a : gr3R) = 1 from rfl,
    show (rowFourU.a : gr3R) = 0 from rfl, show (rowFourU.d : gr3R) = 1 from rfl]
  linear_combination -hk

theorem rowWide_frameOrth_iff (c : gr3R) :
    FrameOrth (rowWideMark h j c) j ↔
      ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowWideMark h j c))), z.IsGaThree →
        (∃ k : gr3R, z.h = 2 * k) ∧ ∃ k : gr3R, z.i = 2 * k :=
  frameOrth_iff_both_even' (by rw [rowWideMark_handleU]; decide)
    (by rw [rowWideMark_handleU]; decide) (by rw [rowWideMark_handleV]; revert c; decide)
    (by rw [rowWideMark_handleV]; revert c; decide)

theorem rowWide_sigmaForces (c : gr3R) : SigmaForces (rowWideMark h j c) j :=
  sigmaForces_of_frameOrth (rowWideMark_zero c) (rowWideMark_one c)
    (by rw [rowWideMark_two]; decide) (by rw [rowWideMark_two]; decide)
    (by rw [rowWideMark_two]; decide) (by rw [rowWideMark_two]; decide)
    (sqRelWord_rowWideMark c)
    ((rowWide_frameOrth_iff c).mpr fun _ hz _ => rowWide_gaTwo_even hz)

/-- ⭐⭐ **The uncleared-`v` LIVE row, same reading.** -/
theorem rowLiveWit_sigma_forced_sharp {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree) (hp : ∃ k : gr3R, z₃.i + z₄.h = 2 * k)
    (hkill : sqRelWord (sigLift j (rowLiveWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 := by
  obtain ⟨k, hk⟩ := hp
  simp only [rowLiveWit] at hkill
  refine liveWit_sigma_forced_pair (by decide) (by decide) (by decide) (by decide)
    sqRelWord_rowLiveWit_triv hvb hz₀ hw₁ hw₂ hz₃ hz₄ ⟨-k, ?_⟩ hkill
  rw [show (rowFourV.d : gr3R) = 0 from rfl, show (rowFourV.a : gr3R) = 1 from rfl,
    show (rowLiveU.a : gr3R) = 0 from rfl, show (rowLiveU.d : gr3R) = 1 from rfl]
  linear_combination -hk

theorem rowLive_frameOrth_iff (c : gr3R) :
    FrameOrth (rowLiveMark h j c) j ↔
      ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowLiveMark h j c))), z.IsGaThree →
        (∃ k : gr3R, z.h = 2 * k) ∧ ∃ k : gr3R, z.i = 2 * k :=
  frameOrth_iff_both_even' (by rw [rowLiveMark_handleU]; decide)
    (by rw [rowLiveMark_handleU]; decide) (by rw [rowLiveMark_handleV]; revert c; decide)
    (by rw [rowLiveMark_handleV]; revert c; decide)

theorem rowLive_sigmaForces (c : gr3R) : SigmaForces (rowLiveMark h j c) j :=
  sigmaForces_of_frameOrth (rowLiveMark_zero c) (rowLiveMark_one c)
    (by rw [rowLiveMark_two]; decide) (by rw [rowLiveMark_two]; decide)
    (by rw [rowLiveMark_two]; decide) (by rw [rowLiveMark_two]; decide)
    (sqRelWord_rowLiveMark c)
    ((rowLive_frameOrth_iff c).mpr fun _ hz _ => rowLive_gaTwo_even c hz)

end GroupD

/-! ## 10 The sweep against the tree's refutations, and the certified negative -/

section Sweep

variable {h : ℕ} {j : Fin h} {j₁ j₂ : Fin h}

/-- ⭐⭐⭐ **THE SAME TABLE READS THE TREE'S ONE REFUTATION.**  `GradedFourTwoLive`'s killing
point has covectors `(0, 1)` and `(1, 0)`, so it belongs to the *full* group, and the sharp
invariant there demands an even **first** class-three coordinate of every achievable move. -/
theorem oddLive_frameOrth_iff :
    FrameOrth (twoLiveMark h j₁ j₂ sigFourU oddLiveV) j₁ ↔
      ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range (twoLiveMark h j₁ j₂ sigFourU oddLiveV))),
        z.IsGaThree → (∃ k : gr3R, z.h = 2 * k) ∧ ∃ k : gr3R, z.i = 2 * k :=
  frameOrth_iff_both_even (by rw [twoLiveMark_handleU_one]; decide)
    (by rw [twoLiveMark_handleU_one]; decide) (by rw [twoLiveMark_handleV_one]; decide)
    (by rw [twoLiveMark_handleV_one]; decide)

/-- ⭐⭐⭐ **…and the reading PREDICTS the refutation.**  The block is odd in the first
class-three coordinate and it is achievable, so the sharp invariant fails at the wave-58 killing
point: `GradedFrameNecessity.twoLiveOdd_not_sigmaForces` is recovered from the migration table
rather than contradicted by it.  This is the sweep the doctrine asks for, executed against the
only class-four refutation the tree owns. -/
theorem oddLive_not_frameOrth : ¬ FrameOrth (twoLiveMark h j₁ j₂ sigFourU oddLiveV) j₁ := by
  intro hO
  exact absurd (oddLive_frameOrth_iff.mp hO _ commP_oddLive_mem_gaTwoOf
    commP_oddLive_isGaThree).1 (by decide)

/-- ⭐⭐⭐ **THE ONE PARITY HYPOTHESIS CANNOT BE DROPPED, EVEN AT THE CLEARED ROW.**  Wave 59's
`mixMove` - a `γ₃`-shaped move with **odd** second class-three coordinate, achievable at no
committed point - together with the class-four exponent move `liftC (-1)` kills the relator at
the cleared row's **odd** sigma dressing.  Wave 58 measured that unrestricted `γ₃`-moves kill at
every point of the catalogue; at the cleared row it is now a theorem, and the coordinate it kills
through is exactly the one `clrFourWit_sigma_forced_sharp` reads. -/
theorem clrFour_sharp_kill :
    sqRelWord (sigLift j (clrFourWit h j sigFourU) 1 1 (liftC (-1)) 1 mixMove) = 1 := by
  have hd : clrFourWit h j sigFourU = sigFourDress (clrFourMark h j) sigFourU := mirWit_eq_dress
  rw [hd]
  refine gaugeX_kill_of_pair (t := 1) (by rw [clrFourMark_one]) SqU5.isGaThree_one
    mixMove_isGaThree (by rw [← hd]; exact sqRelWord_clrFourWit_U) ?_
  simp only [sigIncrPair, clrFourMark_handleU, clrFourMark_handleV,
    show (sigFourU.a : gr3R) = 1 from rfl, show (sigFourU.d : gr3R) = 0 from rfl,
    show (sigFourV.a : gr3R) = 2 from rfl, show (sigFourV.d : gr3R) = 0 from rfl,
    show (mixMove.h : gr3R) = 0 from rfl, show (mixMove.i : gr3R) = 1 from rfl,
    SqU5.one_h, SqU5.one_i]
  decide

/-- ⭐⭐⭐ **…so the UNRESTRICTED forcing is false at the cleared row**, and
`clrFourWit_sigma_forced_sharp`'s single hypothesis is load-bearing rather than a convenience.
Note what this does *not* say: the achievability convention is nowhere used by the sharp
statement, and what achievability supplies at the committed points is exactly this parity. -/
theorem clrFour_unrestricted_sigma_forced_false :
    ¬ ∀ v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R, v.b = 0 → z₀.IsGaThree → w₁.IsGaFour → w₂.IsGaFour →
        z₃.IsGaThree → z₄.IsGaThree →
        sqRelWord (sigLift j (clrFourWit h j v) z₀ w₁ w₂ z₃ z₄) = 1 → selPar v.a = 0 := by
  intro hforce
  have hcon := hforce sigFourU 1 1 (liftC (-1)) 1 mixMove (by decide) SqU5.isGaThree_one
    SqU5.isGaFour_one (liftC_isGaFour _) SqU5.isGaThree_one mixMove_isGaThree clrFour_sharp_kill
  rw [show (sigFourU.a : gr3R) = 1 from rfl] at hcon
  exact absurd hcon (by decide)

/-- ⭐⭐⭐ **THE MIGRATION, IN ONE STATEMENT.**  Every committed class-four point of the campaign
satisfies the sharp invariant and therefore the whole forcing, discharged from the covector table
and nothing else; and the wave-58 killing point is off the line, read by the same table.  Ten
points at every handle count, every handle and every pivot residue, one at `h = 1`, and one
refutation. -/
theorem sharp_migration (c : gr3R) (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    SigmaForces (clrFourMark h j) j ∧ SigmaForces (liveFourMark h j) j ∧
      SigmaForces (twoLiveMark h j₁ j₂ twoLiveU twoLiveV) j₁ ∧
      SigmaForces (dblFourMark h j c) j ∧ SigmaForces (dblLiveMark h j c) j ∧
      SigmaForces (mirFourMark h j c) j ∧ SigmaForces (mirLiveMark h j c) j ∧
      SigmaForces (hiLiveMark h j c) j ∧ SigmaForces (rowWideMark h j c) j ∧
      SigmaForces (rowLiveMark h j c) j ∧ SigmaForces (rowFourMark c) 0 ∧
      ¬ FrameOrth (twoLiveMark h j₁ j₂ sigFourU oddLiveV) j₁ :=
  ⟨clrFour_sigmaForces, liveFour_sigmaForces, twoLive_sigmaForces hlt, dblFour_sigmaForces c,
    dblLive_sigmaForces c, mirFour_sigmaForces c, mirLive_sigmaForces c, hiLive_sigmaForces c,
    rowWide_sigmaForces c, rowLive_sigmaForces c, rowFour_sigmaForces c, oddLive_not_frameOrth⟩

end Sweep

/-! ## 11 Axiom pins -/

section Pins

#print axioms sigIncrPair_left
#print axioms sigIncrPair_right
#print axioms frameOrth_iff_par
#print axioms frameOrth_iff_i_even
#print axioms frameOrth_iff_h_even
#print axioms frameOrth_iff_both_even
#print axioms frameOrth_iff_both_even'
#print axioms even_mul_odd_iff
#print axioms frameOrth_of_gaTwo_even
#print axioms frameOrth_of_gaTwo_h_even
#print axioms mirWit_sigma_forced_pair
#print axioms liveWit_sigma_forced_pair
#print axioms twoLiveWit_sigma_forced_pair
#print axioms rowFourWit_sigma_forced_pair
#print axioms sharp_covector_table
#print axioms covectors_pivot_invariant
#print axioms clrFourWit_sigma_forced_sharp
#print axioms clrFour_frameOrth_iff
#print axioms clrFour_sigmaForces
#print axioms liveFourWit_sigma_forced_sharp
#print axioms liveFour_frameOrth_iff
#print axioms liveFour_sigmaForces
#print axioms twoLiveWit_sigma_forced_sharp
#print axioms twoLive_frameOrth_iff
#print axioms twoLive_sigmaForces
#print axioms dblFourWit_sigma_forced_sharp
#print axioms dblFour_frameOrth_iff
#print axioms dblFour_sigmaForces
#print axioms dblLiveWit_sigma_forced_sharp
#print axioms dblLive_frameOrth_iff
#print axioms dblLive_sigmaForces
#print axioms mirFourWit_sigma_forced_sharp
#print axioms mirFour_frameOrth_iff
#print axioms mirFour_sigmaForces
#print axioms mirLiveWit_sigma_forced_sharp
#print axioms mirLive_frameOrth_iff
#print axioms mirLive_sigmaForces
#print axioms hiLiveWit_sigma_forced_sharp
#print axioms hiLive_frameOrth_iff
#print axioms hiLive_sigmaForces
#print axioms rowFourWit_sigma_forced_sharp
#print axioms rowFour_frameOrth_iff
#print axioms rowFour_sigmaForces
#print axioms rowWideWit_sigma_forced_sharp
#print axioms rowWide_frameOrth_iff
#print axioms rowWide_sigmaForces
#print axioms rowLiveWit_sigma_forced_sharp
#print axioms rowLive_frameOrth_iff
#print axioms rowLive_sigmaForces
#print axioms oddLive_frameOrth_iff
#print axioms oddLive_not_frameOrth
#print axioms clrFour_sharp_kill
#print axioms clrFour_unrestricted_sigma_forced_false
#print axioms sharp_migration

/-! ### The superseded statements, for comparison

Every print below is the committed statement that the corresponding new one supersedes.  All of
them are **std-3** (`propext`, `Classical.choice`, `Quot.sound`), and so is every print above
except `sigIncrPair_left` and `sigIncrPair_right`, which are `propext` + `Quot.sound`.  So the
migration changes **no axiom footprint anywhere**: what changes is the hypothesis, not the
foundation. -/

#print axioms mirWit_sigma_forced
#print axioms liveWit_sigma_forced
#print axioms twoLiveWit_sigma_forced
#print axioms rowFourWit_sigma_forced_gaTwo
#print axioms frameOrth_of_le_liveFrameSub
#print axioms frameOrth_of_gaTwo_i_even
#print axioms clrFourWit_sigma_forced_gaTwo
#print axioms liveFourWit_sigma_forced_gaTwo
#print axioms dblFourWit_sigma_forced_gaTwo
#print axioms dblLiveWit_sigma_forced_gaTwo
#print axioms mirFourWit_sigma_forced_gaTwo
#print axioms mirLiveWit_sigma_forced_gaTwo
#print axioms hiLiveWit_sigma_forced_gaTwo
#print axioms rowWideWit_sigma_forced_gaTwo
#print axioms rowLiveWit_sigma_forced_gaTwo
#print axioms twoLiveOdd_not_sigmaForces

end Pins

end SqCore

end Dyadic

end GQ2

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFiveStageFour
import GQ2.Dyadic.SqCore.GradedFiveNecessity

/-!
# W61-SHARP4: the STAGE-FOUR soundness condition is MERELY SUFFICIENT, and its sharp line is
NOT a covector condition

`GradedFiveStageFour` (wave 60) made the class-five exclusion unconditional on a soundness
chain it proved rather than assumed: an even `(1,2)`- and `(3,4)`-column at every slot
(`stageN1`) forces every achievable STAGE-FOUR dressing into `stageN3`, `j`, `l` and `m` even,
which makes `gaThreeShiftO` even.  Its own scope note recorded that the chain is
"**sufficient, not shown sharp**".  It is not sharp, and the way it fails is different from
the two lines examined before it.

## ⭐⭐⭐ Headline 1: MERELY SUFFICIENT, and by a wide margin

`scripts/w61_sharp4/results/sweep_sharp4.txt`: of **1650** admissible stage-four markings -
relator a central translation with an odd class-five residue, the `x1`-slot produced by wave
60's layered solve so that a perturbed set of letters is pushed back onto an admissible
marking - the forcing holds at `1560`, and among those wave 60's HYPOTHESIS fails at **620**,
its exact soundness hypothesis at **354**, and its CONCLUSION at **80**.  Section 4 proves one
such marking end to end, at every handle count and every handle.

## ⭐⭐⭐ Headline 2: the sharp line is the CENTRAL one, and that is a new phenomenon

At class four and class five every refinement in scope moves the relator **centrally**, so a
dressing kills exactly when its class-five increment matches the residue, and the sharp line is
the parity of one pairing.  ⭐ **A `gamma_3`-dressing does not act centrally**: it moves the two
class-four rows as well, and a kill has to leave them alone.  So the line is

⭐⭐⭐ `stageForces_iff_stageCentral`: at any marking whose relator is a central translation with
an odd residue, the stage-four forcing holds **if and only if** every achievable stage-four
dressing whose shift is **central** moves the class-five row by an even amount (`StageCentral`).

Its engine is ⭐⭐ `stageCentral_of_stageForces`, which needs the shift to be a homomorphism of
the dressing tuple (⭐ `gaThreeShift_mul`, `gaThreeShift_pow`): a central shift with an odd
class-five row is a **unit** in `ZMod 8`, so a suitable power of the dressing hits the residue
exactly and kills.  Nothing is tuned by hand; at class five the free central exponent slot did
that job, and at stage four there is no free slot.

The parity line `StageOrth` - every achievable dressing, central or not, moves the class-five
row evenly - sits strictly between the two:

```text
   letters in stageN1  =>  achievable dressings in stageN3  =>  StageOrth  =>  StageCentral
        (wave 60)                    (wave 60)                            <=>  the forcing
```

and the census finds all three implications strict: the last at **4** of the 1650 markings,
where an achievable dressing pairs oddly and yet kills nothing because it moves a class-four row
by `4` or by `2`.  ⚠ Those four are **measured**, not proved; the Lean file proves the
characterisation itself and the strictness of the first two steps.  An exact search - not a
sample - decides `KILL` at every marking by testing membership of the residue in the image
module of the achievable tuple lattice, and it agrees with the sharp line at **1650 of 1650**.

## ⭐⭐⭐ Headline 3: THE ORTHOGONAL ROUTE IS CLOSED, which it is not at class four or five

Wave 59 and wave 60 each exhibited an **orthogonal point** where the covectors vanish outright
and the forcing holds for arbitrary moves with no achievability at all.  There is no such
stage-four point, and that is a theorem rather than a failed search.

* ⭐⭐ `gaThreeShiftO_even_of_columns`: if every slot has an even `a`, `e`, `f` and `i` column -
  which is measured to be exactly the condition making all five stage-four covectors vanish -
  then **every** `gamma_3`-dressing moves the class-five row evenly, achievable or not.
* ⭐⭐⭐ `stageQ_bit_even`: at such a marking the class-five selection bit is **already** `0`.
  So the free hypothesis is available only where the forcing has nothing to say.  The proof is
  short and structural: `selPar (·).o` is a **group homomorphism** on that subgroup, because
  all four cross terms of `SqU6.mul_o` meet one of the four even columns; the relator is a
  product of commutators, conjugates, a square and a fourth power, so its image is `0`.

⭐ **Consequence, and it is what the campaign should carry**: at stage four the forcing is
never free.  Every stage-four forcing consumes either achievability or a genuinely finer
invariant, which is not so one filtration step narrower.

## ⭐⭐⭐ Headline 4: the class-five sharp line does NOT survive one step wider

⭐⭐⭐ `orthFive_stage_kill`.  At `GradedFiveNecessity`'s own orthogonal point - where all three
class-five covectors vanish, `orthFive_pair_eq_zero` gives the class-five pairing identically
`0` and `orthFive_no_kill` excludes **every** `gamma_4`-shaped refinement whatever its
provenance - the **achievable** stage-four dressing `[[V, sigma], x0]^5 = <j = 5>` on the
handle-`U` slot **kills the relator**, and it is not alone: `2048` of the `81920` single-slot
achievable stage-four dressings kill there.  So `orthFive_stageForces_false`: a marking can be
orthogonal at class five and still lose at stage four, and the three-covector condition is not
the stage-four line even as a sufficient one.  The reason is visible in the covectors: the
killing dressing is `<j = 5>`, and **no class-five covector reads `j`**.

## ⭐⭐ The stage-four covectors, and the arity progression

Over any marking the class-five row of `gaThreeShift` is, mod `2`, a sum of one covector per
dressed slot, each pairing the dressing's `(j, k, l, m, n)` against the slot's letter:

```text
slot            paired letter        (j, k, l, m, n)-covector, mod 2
sigma           x0                   (L.i, L.a·L.e, L.f + L.a·L.b, L.e, L.a) + corrections
x0              10x0 - sigma - 8x1   the same shape, at the Fox letter
x1              x1                   the same shape
handle U        V                    the same shape
handle V        U                    the same shape
```

**Class four needed two covectors of length two; class five three of length two; stage four
needs `2h + 3` of length five** - five at one handle.  The arity does not go `2, 3, 4`: every
dressed slot contributes, because a `gamma_3`-dressing of an exponent slot is not central, and
each covector is longer, because a `gamma_3`-element has three live coordinates a
`gamma_4`-element does not.  And the count is not the whole story, since the sharp line reads
the covectors only on the tuples that act centrally.

## ⭐⭐ A second sufficient condition, incomparable with wave 60's

⭐⭐ `stageOrth_of_outer`: at a marking whose slots have even `a`, `e` and `i` columns, every
achievable dressing with an even `l` pairs evenly - and an even `e` column at every slot forces
exactly that, by wave 60's own `fiveEvenI_of_commutator` / `fiveEvenL_of_commutator` chain
stopped one filtration step short of where that wave used it
(`forceLcs_two_le_fiveEvenL`).

```text
                            reads of the letters      reads of the dressing
wave 60's stageN1/stageN3   a                          j, l, m
this file's outer chain     a, e, i                    l
```

Neither implies the other, and section 4's point is inside the second and outside the first in
**both** halves.

## PROVED versus carried versus measured

**PROVED**: the shift's multiplicativity and its coordinate rows; the unconditional
`gamma_3`-shape of an achievable stage-four dressing; the three properties and the
characterisation; wave 60's condition as a sufficient one; the outer-column condition and its
chain; the mixed point end to end at every handle count and every handle, with wave 60's
hypothesis AND conclusion failing there; the closure of the orthogonal route; the kill at wave
60's class-five orthogonal point.

**Carried, and named**: `StageForces` quantifies its five dressings over
`forceLcs (Subgroup.closure (Set.range m)) 2`, which is `GradedFiveStageFour`'s achievability
convention verbatim.  The characterisation's converse half needs the relator to be a central
translation with an odd residue, exactly as wave 60's class-five characterisation does.

**Measured, not proved** (`scripts/w61_sharp4/results/`, `validate.txt` has **36** named
checks and **0** failures): the census (`sweep_sharp4.txt`); the four markings where the parity
line fails and the forcing holds (`hunt_gap.txt`); that all five covectors vanish **only** under
the four even columns of section 5; and the kill counts at the named points.  The engine reads
every stage-four shift off the honest `6 x 6` matrices of `scripts/w59_force5/u6mat.py` rather
than from any transcribed formula; the covector table above is then compared against those
honest shifts at `2000` slot-marking pairs, and the linearity that licenses the module
computation - the measured form of `gaThreeShift_mul` - at `1200` tuples over ten markings.

⚠ **What the language needs.**  The sharp line is not a mod-`2` covector condition and cannot
be made into one.  A natural candidate - that the class-five covector be a fixed mod-`2`
combination of the two class-four ones, which would make centrality force evenness by pure
linear algebra - holds at **0** of the 1650 markings (`MODLOW` in the census): the class-four
rows' own covectors read the dressing's `(j, k)` and `(k, l)` alone, so no combination of them
can match the class-five covector's `(m, n)` entries unless those vanish, which is wave 60's
class-five orthogonality at every slot at once.  What
makes the four gap markings work is arithmetic over `Z/8` rather than mod `2`: the class-four
row there is `4` or `2` times the coordinate the class-five covector reads, so it is invisible
mod `2` and still forces that coordinate even once it is set to zero.  A sharp stage-four line
therefore has to name the **kernel of the class-four rows over `Z/8`**, which is what
`StageCentral` does.

## Contents

* **1** the shift as a linear object; **2** ⭐⭐⭐ the three properties and the characterisation;
* **3** ⭐⭐ the outer-column condition and its chain; **4** ⭐⭐⭐ the mixed point;
* **5** ⭐⭐⭐ the closure of the orthogonal route; **6** ⭐⭐⭐ the class-five point that dies at
  stage four; **7** what the committed statements carry; **8** axiom pins.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`; every `decide` is on `ZMod 8`, `ZMod 2` or tuples
over them.  All **79** committed prints are **std-3** (`propext`, `Classical.choice`,
`Quot.sound`) or a subset: `49` std-3, `22` `propext` + `Quot.sound`, `8` `propext` alone.  No
census axiom is reachable.
-/

open scoped commutatorElement

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The stage-four shift as a linear object -/

section Linear

variable {R : Type} [CommRing R] {h : ℕ}

@[simp] theorem gaThreeShift_j (m z : Fin (sqRank h) → SqU6 R) :
    (gaThreeShift h m z).j = -4 * (z 1).j + 2 * (z 2).j := by
  simp only [gaThreeShift, SqU6.mul_j, SqU6.mul_a, SqU6.mul_f, SqU6.liftO, gaThreeCore]
  ring

@[simp] theorem gaThreeShift_k (m z : Fin (sqRank h) → SqU6 R) :
    (gaThreeShift h m z).k = -4 * (z 1).k + 2 * (z 2).k := by
  simp only [gaThreeShift, SqU6.mul_k, SqU6.mul_b, SqU6.mul_g, SqU6.liftO, gaThreeCore]
  ring

/-- The shift's first class-four row: the Frobenius weights on the exponent slots, plus the
summed class-four graded Fox pairings of the core and the handles. -/
theorem gaThreeShift_m (m z : Fin (sqRank h) → SqU6 R) :
    (gaThreeShift h m z).m = (gaThreeCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).m
      + ∑ k : Fin h, (gaThreeHandle (m (sqHandleIdxU k)) (m (sqHandleIdxV k))
          (z (sqHandleIdxU k)) (z (sqHandleIdxV k))).m := by
  simp only [gaThreeShift, SqU6.mul_m, SqU6.mul_a, SqU6.mul_f, SqU6.mul_j, SqU6.liftO,
    gaThreeCore]
  ring

/-- …and its second. -/
theorem gaThreeShift_n (m z : Fin (sqRank h) → SqU6 R) :
    (gaThreeShift h m z).n = (gaThreeCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).n
      + ∑ k : Fin h, (gaThreeHandle (m (sqHandleIdxU k)) (m (sqHandleIdxV k))
          (z (sqHandleIdxU k)) (z (sqHandleIdxV k))).n := by
  simp only [gaThreeShift, SqU6.mul_n, SqU6.mul_b, SqU6.mul_g, SqU6.mul_k, SqU6.liftO,
    gaThreeCore]
  ring

/-- Two `gamma_3`-shaped elements agreeing in their six live coordinates are equal. -/
theorem SqU6.gaThree_ext {p q : SqU6 R} (hp : p.IsGaThree) (hq : q.IsGaThree) (hj : p.j = q.j)
    (hk : p.k = q.k) (hl : p.l = q.l) (hm : p.m = q.m) (hn : p.n = q.n) (ho : p.o = q.o) :
    p = q := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := hp
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := hq
  ext <;>
    simp only [p1, p2, p3, p4, p5, p6, p7, p8, p9, q1, q2, q3, q4, q5, q6, q7, q8, q9,
      hj, hk, hl, hm, hn, ho]

theorem SqU6.IsGaThree.mul {p q : SqU6 R} (hp : p.IsGaThree) (hq : q.IsGaThree) :
    (p * q).IsGaThree := by
  rw [SqU6.gaThree_mul hp hq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SqU6.IsGaThree.pow {p : SqU6 R} (hp : p.IsGaThree) : ∀ k : ℕ, (p ^ k).IsGaThree
  | 0 => by rw [pow_zero]; exact SqU6.isGaThree_one
  | k + 1 => by rw [pow_succ]; exact (SqU6.IsGaThree.pow hp k).mul hp

section GaThreeCoords

variable {p q : SqU6 R} (hp : p.IsGaThree) (hq : q.IsGaThree)
include hp hq

omit hq in
theorem SqU6.gaThree_mul_j : (p * q).j = p.j + q.j := by
  simp only [SqU6.mul_j, hp.1, hp.2.2.2.2.2.1, zero_mul, add_zero]

omit hq in
theorem SqU6.gaThree_mul_k : (p * q).k = p.k + q.k := by
  simp only [SqU6.mul_k, hp.2.1, hp.2.2.2.2.2.2.1, zero_mul, add_zero]

omit hq in
theorem SqU6.gaThree_mul_l : (p * q).l = p.l + q.l := by
  simp only [SqU6.mul_l, hp.2.2.1, hp.2.2.2.2.2.2.2.1, zero_mul, add_zero]

theorem SqU6.gaThree_mul_m : (p * q).m = p.m + q.m := by
  simp only [SqU6.mul_m, hp.1, hp.2.2.2.2.2.1, hq.2.2.2.1, zero_mul, mul_zero, add_zero]

theorem SqU6.gaThree_mul_n : (p * q).n = p.n + q.n := by
  simp only [SqU6.mul_n, hp.2.1, hp.2.2.2.2.2.2.1, hq.2.2.2.2.1, zero_mul, mul_zero, add_zero]

theorem SqU6.gaThree_mul_o : (p * q).o = p.o + q.o := by
  simp only [SqU6.mul_o, hp.1, hp.2.2.2.2.2.1, hq.2.2.2.2.2.2.2.2, hq.2.2.2.2.1, zero_mul,
    mul_zero, add_zero]

end GaThreeCoords

/-- ⭐⭐ **The stage-four shift is a HOMOMORPHISM of the dressing tuple.**  Both the shift and
the dressings live in `gamma_3`, which is abelian in a carrier of class five
(`SqU6.gaThree_comm`), and every one of the shift's six rows is linear in the dressings'
coordinates - `GradedFiveStageFour`'s headline that the transport is affine rather than
quadratic, read as a statement about the shift map rather than about its coefficients. -/
theorem gaThreeShift_mul {m z w : Fin (sqRank h) → SqU6 R} (hz : ∀ i, (z i).IsGaThree)
    (hw : ∀ i, (w i).IsGaThree) :
    gaThreeShift h m (fun i => z i * w i) = gaThreeShift h m z * gaThreeShift h m w := by
  have hj : ∀ i, (z i * w i).j = (z i).j + (w i).j := fun i =>
    SqU6.gaThree_mul_j (hz i)
  have hk : ∀ i, (z i * w i).k = (z i).k + (w i).k := fun i =>
    SqU6.gaThree_mul_k (hz i)
  have hl : ∀ i, (z i * w i).l = (z i).l + (w i).l := fun i =>
    SqU6.gaThree_mul_l (hz i)
  have hm : ∀ i, (z i * w i).m = (z i).m + (w i).m := fun i =>
    SqU6.gaThree_mul_m (hz i) (hw i)
  have hn : ∀ i, (z i * w i).n = (z i).n + (w i).n := fun i =>
    SqU6.gaThree_mul_n (hz i) (hw i)
  have ho : ∀ i, (z i * w i).o = (z i).o + (w i).o := fun i =>
    SqU6.gaThree_mul_o (hz i) (hw i)
  refine SqU6.gaThree_ext gaThreeShift_isGaThree
    (gaThreeShift_isGaThree.mul gaThreeShift_isGaThree) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [gaThreeShift_j, SqU6.gaThree_mul_j gaThreeShift_isGaThree,
      gaThreeShift_j, gaThreeShift_j, hj, hj]
    ring
  · rw [gaThreeShift_k, SqU6.gaThree_mul_k gaThreeShift_isGaThree,
      gaThreeShift_k, gaThreeShift_k, hk, hk]
    ring
  · rw [gaThreeShift_l, SqU6.gaThree_mul_l gaThreeShift_isGaThree,
      gaThreeShift_l, gaThreeShift_l, hl, hl]
    ring
  · have hsum : ∑ t : Fin h, (gaThreeHandle (m (sqHandleIdxU t)) (m (sqHandleIdxV t))
          (z (sqHandleIdxU t) * w (sqHandleIdxU t))
          (z (sqHandleIdxV t) * w (sqHandleIdxV t))).m
        = (∑ t : Fin h, (gaThreeHandle (m (sqHandleIdxU t)) (m (sqHandleIdxV t))
            (z (sqHandleIdxU t)) (z (sqHandleIdxV t))).m)
          + ∑ t : Fin h, (gaThreeHandle (m (sqHandleIdxU t)) (m (sqHandleIdxV t))
            (w (sqHandleIdxU t)) (w (sqHandleIdxV t))).m := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => by
        simp only [gaThreeHandle, gaThreePairL, hj, hk]
        ring
    rw [gaThreeShift_m, SqU6.gaThree_mul_m gaThreeShift_isGaThree gaThreeShift_isGaThree,
      gaThreeShift_m, gaThreeShift_m, hsum]
    simp only [gaThreeCore, gaThreePairL, hj, hk, hm]
    ring
  · have hsum : ∑ t : Fin h, (gaThreeHandle (m (sqHandleIdxU t)) (m (sqHandleIdxV t))
          (z (sqHandleIdxU t) * w (sqHandleIdxU t))
          (z (sqHandleIdxV t) * w (sqHandleIdxV t))).n
        = (∑ t : Fin h, (gaThreeHandle (m (sqHandleIdxU t)) (m (sqHandleIdxV t))
            (z (sqHandleIdxU t)) (z (sqHandleIdxV t))).n)
          + ∑ t : Fin h, (gaThreeHandle (m (sqHandleIdxU t)) (m (sqHandleIdxV t))
            (w (sqHandleIdxU t)) (w (sqHandleIdxV t))).n := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => by
        simp only [gaThreeHandle, gaThreePairR, hk, hl]
        ring
    rw [gaThreeShift_n, SqU6.gaThree_mul_n gaThreeShift_isGaThree gaThreeShift_isGaThree,
      gaThreeShift_n, gaThreeShift_n, hsum]
    simp only [gaThreeCore, gaThreePairR, hk, hl, hn]
    ring
  · have hsum : ∑ t : Fin h, (gaThreeHandle (m (sqHandleIdxU t)) (m (sqHandleIdxV t))
          (z (sqHandleIdxU t) * w (sqHandleIdxU t))
          (z (sqHandleIdxV t) * w (sqHandleIdxV t))).o
        = (∑ t : Fin h, (gaThreeHandle (m (sqHandleIdxU t)) (m (sqHandleIdxV t))
            (z (sqHandleIdxU t)) (z (sqHandleIdxV t))).o)
          + ∑ t : Fin h, (gaThreeHandle (m (sqHandleIdxU t)) (m (sqHandleIdxV t))
            (w (sqHandleIdxU t)) (w (sqHandleIdxV t))).o := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => by
        simp only [gaThreeHandle, gaThreePair, hj, hk, hl, hm, hn]
        ring
    rw [gaThreeShift_o, SqU6.gaThree_mul_o gaThreeShift_isGaThree gaThreeShift_isGaThree,
      gaThreeShift_o, gaThreeShift_o]
    simp only [gaThreeShiftO]
    rw [hsum]
    simp only [gaThreeCore, gaThreePair, gaThreeCorr, hj, hk, hl, hm, hn, ho]
    ring

/-- …hence a `Z/8`-linear one: the `k`-th power of a dressing shifts by the `k`-th power. -/
theorem gaThreeShift_pow {m z : Fin (sqRank h) → SqU6 R} (hz : ∀ i, (z i).IsGaThree) :
    ∀ k : ℕ, gaThreeShift h m (fun i => z i ^ k) = gaThreeShift h m z ^ k
  | 0 => by
    simp only [pow_zero]
    refine SqU6.gaThree_ext gaThreeShift_isGaThree SqU6.isGaThree_one ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp only [gaThreeShift_j, gaThreeShift_k, gaThreeShift_l, gaThreeShift_m,
        gaThreeShift_n, gaThreeShift_o, gaThreeShiftO, gaThreeCore, gaThreeHandle,
        gaThreePair, gaThreePairL, gaThreePairR, gaThreeCorr, SqU6.one_j, SqU6.one_k,
        SqU6.one_l, SqU6.one_m, SqU6.one_n, SqU6.one_o] <;>
      simp
  | k + 1 => by
    have := gaThreeShift_mul (m := m) (z := fun i => z i ^ k) (w := z)
      (fun i => (hz i).pow k) hz
    simp only [← pow_succ] at this
    rw [this, gaThreeShift_pow hz k, ← pow_succ]

/-- A central element's powers: `liftO` is additive, so this is multiplication of the residue. -/
theorem SqU6.liftO_pow (v : R) : ∀ k : ℕ, SqU6.liftO v ^ k = SqU6.liftO ((k : R) * v)
  | 0 => by
    rw [pow_zero, Nat.cast_zero, zero_mul]
    ext <;> simp [SqU6.liftO]
  | k + 1 => by
    rw [pow_succ, SqU6.liftO_pow v k, SqU6.liftO_mul_liftO, Nat.cast_succ]
    exact congrArg SqU6.liftO (by ring)

end Linear

/-! ## 2 The three properties, and the characterisation -/

section Properties

variable {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R}

/-- **Every achievable stage-four dressing is `gamma_3`-shaped**, at every marking and with no
hypothesis at all: `GradedFiveNecessity.forceLcs_three_le_gaFourSub` one filtration step
short.  `GradedFiveStageFour` gets the shape from `stageN3`, that is, conditionally on the two
even columns; the characterisation needs it unconditionally. -/
theorem forceLcs_two_le_gaThreeSub (H : Subgroup (SqU6 gr3R)) :
    forceLcs H 2 ≤ gaThreeSub gr3R := by
  have h1 : forceLcs H 1 ≤ gaTwoSub gr3R :=
    Subgroup.commutator_le.mpr fun p _ q _ => gaTwoSub_of_commutator p q
  exact Subgroup.commutator_le.mpr fun p hp q _ => gaThreeSub_of_commutator (h1 hp) q

theorem isGaThree_of_mem_forceLcs {H : Subgroup (SqU6 gr3R)} {p : SqU6 gr3R}
    (hp : p ∈ forceLcs H 2) : p.IsGaThree :=
  forceLcs_two_le_gaThreeSub H hp

/-- **The stage-four sigma forcing at a marking**, in exactly the shape
`GradedFiveStageFour.stageWit_sigma_forced` proves and `sqRelWord_stageWit_diag_ne_one`
negates: every achievable five-slot STAGE-FOUR refinement that kills the relator leaves an
even class-five residue. -/
def StageForces {h : ℕ} (m : Fin (sqRank h) → SqU6 gr3R) : Prop :=
  ∀ z : Fin (sqRank h) → SqU6 gr3R,
    (∀ i, z i ∈ forceLcs (Subgroup.closure (Set.range m)) 2) →
    sqRelWord (conFiveDress m z) = 1 → selPar (sqRelWord m).o = 0

/-- **THE PARITY LINE**: every achievable stage-four dressing moves the class-five row by an
even amount.  This is what wave 60's soundness chain delivers, and section 4 shows the chain is
strictly stronger than it. -/
def StageOrth {h : ℕ} (m : Fin (sqRank h) → SqU6 gr3R) : Prop :=
  ∀ z : Fin (sqRank h) → SqU6 gr3R,
    (∀ i, z i ∈ forceLcs (Subgroup.closure (Set.range m)) 2) →
    (2 : gr3R) ∣ gaThreeShiftO h m z

/-- ⭐⭐⭐ **THE SHARP LINE**: every achievable stage-four dressing whose shift is **central**
moves the class-five row by an even amount.  A `gamma_3`-dressing moves the two class-four rows
as well, and a kill has to leave them alone, so only the centrally acting tuples can ever
threaten the bit.  At class four and class five every refinement in scope acts centrally and
this collapses to the parity line; at stage four it does not. -/
def StageCentral {h : ℕ} (m : Fin (sqRank h) → SqU6 gr3R) : Prop :=
  ∀ (z : Fin (sqRank h) → SqU6 gr3R) (w : gr3R),
    (∀ i, z i ∈ forceLcs (Subgroup.closure (Set.range m)) 2) →
    gaThreeShift h m z = SqU6.liftO w → (2 : gr3R) ∣ w

/-- The parity line is the sharp line read on all tuples rather than the central ones. -/
theorem stageCentral_of_stageOrth (hO : StageOrth m) : StageCentral m := by
  intro z w hz hcen
  have ho : gaThreeShiftO h m z = w := by
    rw [← gaThreeShift_o, hcen, SqU6.liftO_o]
  rw [← ho]
  exact hO z hz

/-- **THE SHARP LINE SUFFICES.**  At a marking whose relator is a central translation, an
achievable stage-four refinement that kills it must move the relator by the central element
`liftO (-c)`, and the sharp line says that element is even. -/
theorem stageForces_of_stageCentral {c : gr3R} (hres : sqRelWord m = SqU6.liftO c)
    (hC : StageCentral m) : StageForces m := by
  intro z hz hkill
  have hga : ∀ i, (z i).IsGaThree := fun i => isGaThree_of_mem_forceLcs (hz i)
  rw [sqRelWord_gaThreeDress hga, hres] at hkill
  have hcen : gaThreeShift h m z = SqU6.liftO (-c) := by
    have h1 : SqU6.liftO c * gaThreeShift h m z = SqU6.liftO c * SqU6.liftO (-c) := by
      rw [hkill, SqU6.liftO_mul_liftO, add_neg_cancel]
      ext <;> simp [SqU6.liftO]
    exact mul_left_cancel h1
  obtain ⟨k, hk⟩ := hC z (-c) hz hcen
  rw [hres, SqU6.liftO_o, show c = 2 * (-k) from by linear_combination -hk, selPar_two_mul]

/-- ⭐⭐ **THE SHARP LINE IS NECESSARY.**  At a marking whose relator is a central translation
with an **odd** residue, an achievable dressing acting centrally with an odd class-five row
produces an explicit kill: the shift is a homomorphism of the tuple, an odd element of
`ZMod 8` is a unit, and the tuple's `k`-th power moves the relator by exactly `liftO (-c)`.
No hand tuning and no free slot: at class five the exponent slot's arbitrary `gamma_5`-move
did this job, and stage four has no such slot. -/
theorem stageCentral_of_stageForces {c : gr3R} (hres : sqRelWord m = SqU6.liftO c)
    (hc : selPar c = 1) (hF : StageForces m) : StageCentral m := by
  intro z w hz hcen
  by_contra hodd
  have hw : selPar w = 1 := by
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (selPar w) with h0 | h1
    · obtain ⟨y, hy⟩ := (selPar_eq_zero_iff w).mp h0
      exact absurd ⟨y, hy⟩ hodd
    · exact h1
  have hunit : w * w = 1 := (by decide : ∀ x : gr3R, selPar x = 1 → x * x = 1) w hw
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ((k : ℕ) : gr3R) = -c * w :=
    ⟨(-c * w).val, by simp [ZMod.natCast_val, ZMod.cast_id]⟩
  have hga : ∀ i, (z i).IsGaThree := fun i => isGaThree_of_mem_forceLcs (hz i)
  have hpow : gaThreeShift h m (fun i => z i ^ k) = SqU6.liftO (-c) := by
    rw [gaThreeShift_pow hga, hcen, SqU6.liftO_pow, hk]
    refine congrArg SqU6.liftO ?_
    calc -c * w * w = -c * (w * w) := by ring
      _ = -c := by rw [hunit, mul_one]
  have hkill : sqRelWord (conFiveDress m (fun i => z i ^ k)) = 1 := by
    rw [sqRelWord_gaThreeDress (fun i => (hga i).pow k), hpow, hres,
      SqU6.liftO_mul_liftO, add_neg_cancel]
    ext <;> simp [SqU6.liftO]
  have hbit := hF (fun i => z i ^ k) (fun i => pow_mem (hz i) k) hkill
  rw [hres, SqU6.liftO_o, hc] at hbit
  exact absurd hbit (by decide)

/-- ⭐⭐⭐ **THE CHARACTERISATION.**  At any marking whose relator is a central translation with
an odd class-five residue, the stage-four sigma forcing holds **exactly** when every achievable
stage-four dressing acting centrally moves the class-five row evenly. -/
theorem stageForces_iff_stageCentral {c : gr3R} (hres : sqRelWord m = SqU6.liftO c)
    (hc : selPar c = 1) : StageForces m ↔ StageCentral m :=
  ⟨stageCentral_of_stageForces hres hc, stageForces_of_stageCentral hres⟩

/-- **The parity line suffices**, at a central relator. -/
theorem stageForces_of_stageOrth {c : gr3R} (hres : sqRelWord m = SqU6.liftO c)
    (hO : StageOrth m) : StageForces m :=
  stageForces_of_stageCentral hres (stageCentral_of_stageOrth hO)

/-- **Wave 60's soundness condition is SUFFICIENT for the parity line**: its two inputs are
exactly the two hypotheses of `gaThreeShiftO_even`. -/
theorem stageOrth_of_columns (ha : ∀ i, (2 : gr3R) ∣ (m i).a)
    (hle : forceLcs (Subgroup.closure (Set.range m)) 2 ≤ stageN3) : StageOrth m :=
  fun _ hz => gaThreeShiftO_even ha (fun i => stageN3_even (hle (hz i)))

/-- …and its hypothesis `stageN1` supplies both, by `forceLcs_two_le_stageN3`. -/
theorem stageOrth_of_le_stageN1 (hle : Subgroup.closure (Set.range m) ≤ stageN1) :
    StageOrth m :=
  stageOrth_of_columns
    (fun i => (mem_stageN1.mp (hle (Subgroup.subset_closure ⟨i, rfl⟩))).1)
    (forceLcs_two_le_stageN3 hle)

/-- **…so wave 60's forcing is recovered from the sharp line**, at any central relator. -/
theorem stageForces_of_le_stageN1 {c : gr3R} (hres : sqRelWord m = SqU6.liftO c)
    (hle : Subgroup.closure (Set.range m) ≤ stageN1) : StageForces m :=
  stageForces_of_stageOrth hres (stageOrth_of_le_stageN1 hle)

end Properties

/-! ## 3 A second sufficient condition: the OUTER columns -/

section Outer

variable {R : Type} [CommRing R] {h : ℕ}

/-- ⭐ **The class-five pairing form is even** as soon as the letter's `(1,2)`-, `(5,6)`- and
outer class-two columns are even and the dressing's `l` meets the letter's first class-two
column evenly.  Wave 60's `gaThreePair_even` reads the letter's `a` column alone and pays for
it with three dressing coordinates; this reads three letter columns and pays with one. -/
theorem gaThreePair_even_of_outer {z L : SqU6 R} (ha : (2 : R) ∣ L.a) (he : (2 : R) ∣ L.e)
    (hi : (2 : R) ∣ L.i) (hlf : (2 : R) ∣ z.l * L.f) : (2 : R) ∣ gaThreePair z L := by
  obtain ⟨a', ha⟩ := ha
  obtain ⟨e', he⟩ := he
  obtain ⟨i', hi⟩ := hi
  obtain ⟨t, hlf⟩ := hlf
  refine ⟨z.m * e' - z.n * a' + z.j * i' - t + z.l * (a' * L.b) - z.k * (a' * L.e), ?_⟩
  rw [gaThreePair, ha, he, hi]
  linear_combination -hlf

/-- …and so is the correction block, under the same two abelian columns and **no** hypothesis
on the dressing at all.  Six of the nine coefficient blocks meet the even `(1,2)`-column, the
three `j`-blocks meet the even `(5,6)`-column, and the two middle `k`-blocks have even
coefficients outright. -/
theorem gaThreeCorr_even_of_outer {s x y z₀ z₁ z₂ : SqU6 R}
    (hsa : (2 : R) ∣ s.a) (hxa : (2 : R) ∣ x.a) (hya : (2 : R) ∣ y.a)
    (hse : (2 : R) ∣ s.e) (hxe : (2 : R) ∣ x.e) (hye : (2 : R) ∣ y.e) :
    (2 : R) ∣ gaThreeCorr s x y z₀ z₁ z₂ := by
  obtain ⟨sa, hsa⟩ := hsa
  obtain ⟨xa, hxa⟩ := hxa
  obtain ⟨ya, hya⟩ := hya
  obtain ⟨se, hse⟩ := hse
  obtain ⟨xe, hxe⟩ := hxe
  obtain ⟨ye, hye⟩ := hye
  refine ⟨z₀.j * (-(s.d * xe) + se * x.d - 4 * (x.d * xe) + 2 * (x.d * ye) + y.d * ye)
      + z₀.k * (4 * (x.a * x.e) - x.a * y.e - x.e * y.a - y.a * y.e)
      + z₀.l * (sa * x.b - s.b * xa - 4 * (xa * x.b) + x.b * y.a + ya * y.b)
      + z₁.j * (3 * (s.d * xe) - s.d * y.e + se * x.d - 20 * (x.d * xe) + 20 * (x.d * ye)
        - 2 * (y.d * y.e))
      + z₁.k * (s.a * s.e - 7 * (s.a * x.e) + 5 * (s.a * y.e) - 7 * (s.e * x.a)
        + 5 * (s.e * y.a) + 65 * (x.a * x.e) - 50 * (x.a * y.e) - 50 * (x.e * y.a)
        + 40 * (y.a * y.e))
      + z₁.l * (-(s.a * s.b) + 11 * (sa * x.b) - 4 * (s.a * y.b) + 13 * (s.b * xa)
        - 5 * (s.b * y.a) - 110 * (xa * x.b) + 40 * (x.a * y.b) + 100 * (x.b * ya)
        - 38 * (y.a * y.b))
      + z₂.j * (-(s.d * y.e) + se * y.d)
      + z₂.k * (sa * y.e + se * y.a)
      + z₂.l * (sa * y.b - s.b * y.a), ?_⟩
  rw [gaThreeCorr, hsa, hxa, hya, hse, hxe, hye]
  ring

/-- ⭐ **The core shift's class-five row is even** under the three outer letter columns, once
each dressing's `l` meets its slot's letter evenly. -/
theorem gaThreeCore_o_even_of_outer {s x y z₀ z₁ z₂ : SqU6 R}
    (hsa : (2 : R) ∣ s.a) (hxa : (2 : R) ∣ x.a) (hya : (2 : R) ∣ y.a)
    (hse : (2 : R) ∣ s.e) (hxe : (2 : R) ∣ x.e) (hye : (2 : R) ∣ y.e)
    (hsi : (2 : R) ∣ s.i) (hxi : (2 : R) ∣ x.i) (hyi : (2 : R) ∣ y.i)
    (h0 : (2 : R) ∣ z₀.l * x.f) (h1 : (2 : R) ∣ z₁.l * (sqFoxX6 s x y).f)
    (h2 : (2 : R) ∣ z₂.l * y.f) :
    (2 : R) ∣ (gaThreeCore s x y z₀ z₁ z₂).o := by
  have hfa : (2 : R) ∣ (sqFoxX6 s x y).a := by
    rw [sqFoxX6_a]
    exact dvd_sub (dvd_sub (Dvd.dvd.mul_left hxa 10) hsa) (Dvd.dvd.mul_left hya 8)
  have hfe : (2 : R) ∣ (sqFoxX6 s x y).e := by
    rw [sqFoxX6_e]
    exact dvd_sub (dvd_sub (Dvd.dvd.mul_left hxe 10) hse) (Dvd.dvd.mul_left hye 8)
  have hfi : (2 : R) ∣ (sqFoxX6 s x y).i := by
    rw [sqFoxX6_i]
    exact dvd_sub (dvd_sub (Dvd.dvd.mul_left hxi 10) hsi) (Dvd.dvd.mul_left hyi 8)
  have hfrob : (2 : R) ∣ (-4 * z₁.o + 2 * z₂.o) := ⟨-2 * z₁.o + z₂.o, by ring⟩
  refine dvd_add (dvd_add hfrob (dvd_add (dvd_add ?_ ?_) ?_))
    (gaThreeCorr_even_of_outer hsa hxa hya hse hxe hye)
  · exact gaThreePair_even_of_outer hxa hxe hxi h0
  · exact gaThreePair_even_of_outer hfa hfe hfi h1
  · exact gaThreePair_even_of_outer hya hye hyi h2

/-- ⭐ **…and so is each handle shift's class-five row**: the two extra blocks pair the letters'
`(1,2)`- and `(5,6)`-columns against the dressings. -/
theorem gaThreeHandle_o_even_of_outer {p q z w : SqU6 R} (hpa : (2 : R) ∣ p.a)
    (hqa : (2 : R) ∣ q.a) (hpe : (2 : R) ∣ p.e) (hqe : (2 : R) ∣ q.e) (hpi : (2 : R) ∣ p.i)
    (hqi : (2 : R) ∣ q.i) (hzl : (2 : R) ∣ z.l * q.f) (hwl : (2 : R) ∣ w.l * p.f) :
    (2 : R) ∣ (gaThreeHandle p q z w).o := by
  refine dvd_add (dvd_sub (dvd_sub (gaThreePair_even_of_outer hqa hqe hqi hzl)
    (gaThreePair_even_of_outer hpa hpe hpi hwl)) ?_) ?_
  · exact Dvd.dvd.mul_right (dvd_sub (Dvd.dvd.mul_left hqe _) (Dvd.dvd.mul_right hpe _)) _
  · exact Dvd.dvd.mul_right (dvd_sub (Dvd.dvd.mul_right hpa _) (Dvd.dvd.mul_left hqa _)) _

/-- The shift's Frobenius collection factor is even outright. -/
private theorem blocks_even {m z : Fin (sqRank h) → SqU6 R} :
    (2 : R) ∣ (sqU6BlockI (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
        * (-4 * (z 1).j + 2 * (z 2).j)
      - sqU6BlockF (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
        * (-4 * (z 1).l + 2 * (z 2).l)) :=
  dvd_sub (Dvd.dvd.mul_left ⟨-2 * (z 1).j + (z 2).j, by ring⟩ _)
    (Dvd.dvd.mul_left ⟨-2 * (z 1).l + (z 2).l, by ring⟩ _)

/-- ⭐⭐ **THE OUTER-COLUMN SOUNDNESS.**  At any marking all of whose slots have an even
`(1,2)`-column, an even `(5,6)`-column and an even outer class-two column, every five-slot
`gamma_3`-dressing whose slots have an even `l` moves the relator's class-five row by an
**even** amount.  Wave 60's `gaThreeShiftO_even` reads one letter column and three dressing
coordinates; this one reads three letter columns and one dressing coordinate, and neither
hypothesis implies the other. -/
theorem gaThreeShiftO_even_of_outer {m z : Fin (sqRank h) → SqU6 R}
    (ha : ∀ i, (2 : R) ∣ (m i).a) (he : ∀ i, (2 : R) ∣ (m i).e) (hi : ∀ i, (2 : R) ∣ (m i).i)
    (hz : ∀ i, (2 : R) ∣ (z i).l) : (2 : R) ∣ gaThreeShiftO h m z := by
  refine dvd_add (dvd_add (gaThreeCore_o_even_of_outer (ha 0) (ha 1) (ha 2) (he 0) (he 1)
    (he 2) (hi 0) (hi 1) (hi 2) (Dvd.dvd.mul_right (hz 0) _) (Dvd.dvd.mul_right (hz 1) _)
    (Dvd.dvd.mul_right (hz 2) _)) ?_) blocks_even
  exact Finset.dvd_sum fun k _ =>
    gaThreeHandle_o_even_of_outer (ha _) (ha _) (he _) (he _) (hi _) (hi _)
      (Dvd.dvd.mul_right (hz _) _) (Dvd.dvd.mul_right (hz _) _)

/-- ⭐⭐ **…and with the letters' FIRST class-two column even as well, no hypothesis on the
dressing is needed at all.**  This is the identity that closes the orthogonal route in section
5: the four even columns make the whole stage-four pairing vanish mod `2`. -/
theorem gaThreeShiftO_even_of_columns {m : Fin (sqRank h) → SqU6 R}
    (ha : ∀ i, (2 : R) ∣ (m i).a) (he : ∀ i, (2 : R) ∣ (m i).e) (hf : ∀ i, (2 : R) ∣ (m i).f)
    (hi : ∀ i, (2 : R) ∣ (m i).i) (z : Fin (sqRank h) → SqU6 R) :
    (2 : R) ∣ gaThreeShiftO h m z := by
  have hff : (2 : R) ∣ (sqFoxX6 (m 0) (m 1) (m 2)).f := by
    rw [sqFoxX6_f]
    exact dvd_sub (dvd_sub (Dvd.dvd.mul_left (hf 1) 10) (hf 0)) (Dvd.dvd.mul_left (hf 2) 8)
  refine dvd_add (dvd_add (gaThreeCore_o_even_of_outer (ha 0) (ha 1) (ha 2) (he 0) (he 1)
    (he 2) (hi 0) (hi 1) (hi 2) (Dvd.dvd.mul_left (hf 1) _) (Dvd.dvd.mul_left hff _)
    (Dvd.dvd.mul_left (hf 2) _)) ?_) blocks_even
  exact Finset.dvd_sum fun k _ =>
    gaThreeHandle_o_even_of_outer (ha _) (ha _) (he _) (he _) (hi _) (hi _)
      (Dvd.dvd.mul_left (hf _) _) (Dvd.dvd.mul_left (hf _) _)

end Outer

/-! ### The chain that supplies the even `l` -/

section EvenLChain

/-- **The achievable stage-four dressings have an even `l`** at any marking whose slots have an
even `(5,6)`-column: `GradedFiveNecessity`'s own chain, stopped one filtration step short of
where wave 60 used it.  That wave carried it to `gamma_4` and read the second class-four
coordinate; the stage-four line needs it at `gamma_3`. -/
theorem forceLcs_two_le_fiveEvenL {H : Subgroup (SqU6 gr3R)} (hH : H ≤ fiveEvenE gr3R) :
    forceLcs H 2 ≤ fiveEvenL gr3R := by
  have h1 : forceLcs H 1 ≤ fiveEvenI gr3R :=
    Subgroup.commutator_le.mpr fun p hp q hq => fiveEvenI_of_commutator (hH hp) (hH hq)
  exact Subgroup.commutator_le.mpr fun p hp q hq => fiveEvenL_of_commutator (h1 hp) (hH hq)

/-- ⭐⭐ **The outer-column condition gives the parity line.**  Even `(1,2)`-, `(5,6)`- and
outer class-two columns at every slot: the first and third are read directly by the pairing,
and the second doubles as the input of the chain that makes every achievable dressing's `l`
even. -/
theorem stageOrth_of_outer {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R}
    (ha : ∀ i, (2 : gr3R) ∣ (m i).a) (he : ∀ i, (2 : gr3R) ∣ (m i).e)
    (hi : ∀ i, (2 : gr3R) ∣ (m i).i) : StageOrth m := by
  have hle : Subgroup.closure (Set.range m) ≤ fiveEvenE gr3R := by
    rw [Subgroup.closure_le]
    rintro z ⟨i, rfl⟩
    obtain ⟨t, ht⟩ := he i
    exact ⟨t, ht⟩
  intro z hz
  exact gaThreeShiftO_even_of_outer ha he hi
    fun i => (forceLcs_two_le_fiveEvenL hle (hz i)).2.2.2.2.2.2.2.2.2.imp fun _ ht => ht

end EvenLChain

/-! ## 4 The mixed point: wave 60's condition fails in BOTH halves, the forcing HOLDS -/

section MixPoint

variable {h : ℕ} {j : Fin h}

/-- The sigma slot of the mixed point: `<a=2, b=4, i=2, o=2>`. -/
def mixStageS : SqU6 gr3R := ⟨2, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2⟩

/-- Its `x0`-slot: `<a=4, d=3, e=4, i=2>`. -/
def mixStageX : SqU6 gr3R := ⟨4, 0, 0, 3, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩

/-- Its `x1`-slot, the layered solve of the fifteen rows: `<d=2, l=1>`. -/
def mixStageY : SqU6 gr3R := ⟨0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩

/-- Its handle-`U` letter: `<a=6, e=2, i=2, j=1, k=3, l=1, n=5>`. -/
def mixStageU : SqU6 gr3R := ⟨6, 0, 0, 0, 2, 0, 0, 0, 2, 1, 3, 1, 0, 5, 0⟩

/-- Its handle-`V` letter: `<a=6, c=5, e=2, f=1, i=4, k=7>`.  ⚠ Its `(3,4)`-column is **odd**,
which is where wave 60's hypothesis fails, and its first class-two column is odd, which is what
keeps the stage-four covector live. -/
def mixStageV : SqU6 gr3R := ⟨6, 0, 5, 0, 2, 1, 0, 0, 4, 0, 7, 0, 0, 0, 0⟩

variable (h j) in
/-- **The mixed stage-four marking**, at every handle count and every handle. -/
def mixStageMark : Fin (sqRank h) → SqU6 gr3R :=
  fiveTuple gr3R h j mixStageS mixStageX mixStageY mixStageU mixStageV

/-- ⭐ **The relator is a central translation with an ODD class-five residue**, at every handle
count and every handle: the situation the stage-four exclusion is about. -/
theorem sqRelWord_mixStageMark : sqRelWord (mixStageMark h j) = SqU6.liftO 7 := by
  rw [mixStageMark, sqRelWord_fiveTuple]
  decide

/-- The handle block is live. -/
theorem commP_mixStageUV_live : commP mixStageU mixStageV ≠ 1 := by decide

/-- Every slot of a one-handle-live tuple is one of its five letters or trivial.
(`GradedFiveStageFour`'s copy is `private`, so this one is rebuilt here.) -/
private theorem mixTuple_cases {R : Type} [CommRing R] {hh : ℕ} {jj : Fin hh}
    (S X Y U V : SqU6 R) (i : Fin (sqRank hh)) :
    fiveTuple R hh jj S X Y U V i = S ∨ fiveTuple R hh jj S X Y U V i = X
      ∨ fiveTuple R hh jj S X Y U V i = Y ∨ fiveTuple R hh jj S X Y U V i = U
      ∨ fiveTuple R hh jj S X Y U V i = V ∨ fiveTuple R hh jj S X Y U V i = 1 := by
  simp only [fiveTuple]
  split_ifs <;> tauto

/-- ⭐ **Every slot has an even `(1,2)`-column, an even `(5,6)`-column and an even outer
class-two column**, which is the whole input of the outer-column chain. -/
theorem mixStage_columns (i : Fin (sqRank h)) :
    (2 : gr3R) ∣ (mixStageMark h j i).a ∧ (2 : gr3R) ∣ (mixStageMark h j i).e
      ∧ (2 : gr3R) ∣ (mixStageMark h j i).i := by
  simp only [mixStageMark]
  rcases mixTuple_cases mixStageS mixStageX mixStageY mixStageU mixStageV i with
    h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1]
  · exact ⟨⟨1, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩⟩
  · exact ⟨⟨2, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩⟩
  · exact ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩
  · exact ⟨⟨3, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩⟩
  · exact ⟨⟨3, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩⟩
  · exact ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩

/-- ⭐⭐ **The parity line holds at the mixed point**, by the outer-column chain. -/
theorem mixStage_stageOrth : StageOrth (mixStageMark h j) :=
  stageOrth_of_outer (fun i => (mixStage_columns i).1) (fun i => (mixStage_columns i).2.1)
    (fun i => (mixStage_columns i).2.2)

/-- ⭐⭐⭐ **THE STAGE-FOUR FORCING HOLDS AT THE MIXED POINT**, at every handle count and every
handle: no achievable stage-four dressing kills the relator without leaving an even class-five
residue - and the residue is odd, so none kills at all. -/
theorem mixStage_stageForces : StageForces (mixStageMark h j) :=
  stageForces_of_stageOrth sqRelWord_mixStageMark mixStage_stageOrth

/-- …and the exclusion in the shape wave 60 states it. -/
theorem mixStage_diag_ne_one {z : Fin (sqRank h) → SqU6 gr3R}
    (hz : ∀ i, z i ∈ forceLcs (Subgroup.closure (Set.range (mixStageMark h j))) 2) :
    sqRelWord (conFiveDress (mixStageMark h j) z) ≠ 1 := by
  intro hc
  have hp := mixStage_stageForces z hz hc
  rw [sqRelWord_mixStageMark, SqU6.liftO_o] at hp
  exact absurd hp (by decide)

/-- ⚠ **Wave 60's HYPOTHESIS fails here**: the handle-`V` letter's `(3,4)`-column is `5`. -/
theorem mixStageV_not_stageN1 : mixStageV ∉ stageN1 := by
  intro hc
  obtain ⟨-, ⟨t, ht⟩⟩ := mem_stageN1.mp hc
  exact absurd ht (by revert t; decide)

theorem mixStage_not_le_stageN1 :
    ¬ Subgroup.closure (Set.range (mixStageMark h j)) ≤ stageN1 := fun hle =>
  mixStageV_not_stageN1 (hle (Subgroup.subset_closure
    ⟨sqHandleIdxV j, by rw [mixStageMark, fiveTuple_handleV]⟩))

/-- ⚠ **…and so does its CONCLUSION**: the achievable stage-four dressing `[[x0, V], V]` has
first class-four coordinate `7`, which `stageN3` forbids.  So the mixed point is outside wave
60's condition in **both** halves and inside the line. -/
theorem mixStage_breaker_mem :
    commP (commP mixStageX mixStageV) mixStageV
      ∈ forceLcs (Subgroup.closure (Set.range (mixStageMark h j))) 2 := by
  have hX : mixStageX ∈ Subgroup.closure (Set.range (mixStageMark h j)) :=
    Subgroup.subset_closure ⟨1, by rw [mixStageMark, fiveTuple_one]⟩
  have hV : mixStageV ∈ Subgroup.closure (Set.range (mixStageMark h j)) :=
    Subgroup.subset_closure ⟨sqHandleIdxV j, by rw [mixStageMark, fiveTuple_handleV]⟩
  exact commP_mem_commSub (commP_mem_commSub hX hV) hV

theorem mixStage_breaker_not_stageN3 :
    commP (commP mixStageX mixStageV) mixStageV ∉ stageN3 := by
  intro hc
  obtain ⟨-, -, ⟨t, ht⟩⟩ := stageN3_even hc
  rw [show (commP (commP mixStageX mixStageV) mixStageV).m = 7 from by decide] at ht
  exact absurd ht (by revert t; decide)

theorem mixStage_forceLcs_not_le_stageN3 :
    ¬ forceLcs (Subgroup.closure (Set.range (mixStageMark h j))) 2 ≤ stageN3 := fun hle =>
  mixStage_breaker_not_stageN3 (hle (mixStage_breaker_mem (h := h) (j := j)))

/-- ⭐⭐⭐ **THE STRICTNESS, IN ONE STATEMENT.**  At the mixed point wave 60's stage-four
soundness condition fails in its hypothesis AND in its conclusion, and the stage-four forcing
holds anyway.  So `forceLcs_two_le_stageN3` is **merely sufficient**. -/
theorem mixStage_separates :
    ¬ Subgroup.closure (Set.range (mixStageMark h j)) ≤ stageN1
      ∧ ¬ forceLcs (Subgroup.closure (Set.range (mixStageMark h j))) 2 ≤ stageN3
      ∧ StageForces (mixStageMark h j) :=
  ⟨mixStage_not_le_stageN1, mixStage_forceLcs_not_le_stageN3, mixStage_stageForces⟩

/-- **Independent check of the point**, at one handle, straight from `sqRelWord` by kernel
computation, without `sqRelWord_fiveTuple` or the algebra of sections 1 and 3. -/
theorem mixStage_decide_crosscheck :
    sqRelWord (mixStageMark 1 0) = SqU6.liftO 7 := by decide

end MixPoint

/-! ## 5 The orthogonal route is CLOSED at stage four -/

section Closed

/-- **`Q`**: an even `(1,2)`-column, an even `(5,6)`-column and even outer class-two columns
`f` and `i`.  Measured (`scripts/w61_sharp4/results/validate.txt`) to be exactly the condition
making all five stage-four covectors vanish, so it is the only route to a forcing that consumes
no achievability - and the next theorem shows that route is empty. -/
def stageQ : Subgroup (SqU6 gr3R) where
  carrier := {z | (2 : gr3R) ∣ z.a ∧ (2 : gr3R) ∣ z.e ∧ (2 : gr3R) ∣ z.f ∧ (2 : gr3R) ∣ z.i}
  mul_mem' := by
    rintro p q ⟨pa, pe, pf, pi⟩ ⟨qa, qe, qf, qi⟩
    exact ⟨by rw [SqU6.mul_a]; exact dvd_add pa qa,
      by rw [SqU6.mul_e]; exact dvd_add pe qe,
      by rw [SqU6.mul_f]; exact dvd_add (dvd_add pf qf) (Dvd.dvd.mul_right pa _),
      by rw [SqU6.mul_i]; exact dvd_add (dvd_add pi qi) (Dvd.dvd.mul_left qe _)⟩
  one_mem' := ⟨by rw [SqU6.one_a]; exact dvd_zero _, by rw [SqU6.one_e]; exact dvd_zero _,
    by rw [SqU6.one_f]; exact dvd_zero _, by rw [SqU6.one_i]; exact dvd_zero _⟩
  inv_mem' := by
    rintro p ⟨pa, pe, pf, pi⟩
    exact ⟨by rw [SqU6.inv_a]; exact pa.neg_right, by rw [SqU6.inv_e]; exact pe.neg_right,
      by rw [SqU6.inv_f]; exact dvd_sub (Dvd.dvd.mul_right pa _) pf,
      by rw [SqU6.inv_i]; exact dvd_sub (Dvd.dvd.mul_left pe _) pi⟩

theorem mem_stageQ {z : SqU6 gr3R} :
    z ∈ stageQ ↔ (2 : gr3R) ∣ z.a ∧ (2 : gr3R) ∣ z.e ∧ (2 : gr3R) ∣ z.f ∧ (2 : gr3R) ∣ z.i :=
  Iff.rfl

/-- ⭐⭐ **The class-five selection bit is ADDITIVE on `Q`.**  All four cross terms of
`SqU6.mul_o` - `p.a * q.n`, `p.f * q.l`, `p.j * q.i` and `p.m * q.e` - meet one of the four even
columns, so `selPar (·).o` is a group homomorphism there. -/
theorem stageQ_bit_mul {p q : SqU6 gr3R} (hp : p ∈ stageQ) (hq : q ∈ stageQ) :
    selPar (p * q).o = selPar p.o + selPar q.o := by
  obtain ⟨⟨a, ha⟩, -, ⟨f, hf⟩, -⟩ := hp
  obtain ⟨-, ⟨e', he'⟩, -, ⟨i', hi'⟩⟩ := hq
  have hpq : (p * q).o = p.o + q.o + 2 * (a * q.n + f * q.l + p.j * i' + p.m * e') := by
    rw [SqU6.mul_o, ha, hf, hi', he']
    ring
  rw [hpq, selPar_add, selPar_add, selPar_two_mul, add_zero]

/-- …and inversion fixes it, `ZMod 2` being its own negative. -/
theorem stageQ_bit_inv {p : SqU6 gr3R} (hp : p ∈ stageQ) : selPar p⁻¹.o = selPar p.o := by
  obtain ⟨⟨a, ha⟩, ⟨e, he⟩, ⟨f, hf⟩, ⟨i, hi⟩⟩ := hp
  have hinv : p⁻¹.o = 2 * (-2 * (a * p.b * p.c * p.d * e) + 2 * (a * p.b * p.c * i)
      + 2 * (a * p.b * e * p.h) - a * p.b * p.l + 2 * (a * p.d * e * p.g) - 2 * (a * e * p.k)
      - 2 * (a * p.g * i) + a * p.n + 2 * (p.c * p.d * e * f) - 2 * (p.c * f * i)
      - p.d * e * p.j - 2 * (e * f * p.h) + e * p.m + f * p.l + i * p.j) - p.o := by
    rw [SqU6.inv_o, ha, he, hf, hi]
    ring
  rw [hinv, selPar_sub, selPar_two_mul, zero_sub]
  exact (by decide : ∀ x : ZMod 2, -x = x) _

/-- …so conjugation fixes it. -/
theorem stageQ_bit_conj {x g : SqU6 gr3R} (hx : x ∈ stageQ) (hg : g ∈ stageQ) :
    selPar (conjP x g).o = selPar x.o := by
  rw [conjP, stageQ_bit_mul (stageQ.mul_mem (stageQ.inv_mem hg) hx) hg,
    stageQ_bit_mul (stageQ.inv_mem hg) hx, stageQ_bit_inv hg]
  exact (by decide : ∀ u v : ZMod 2, u + v + u = v) _ _

/-- …and a commutator kills it. -/
theorem stageQ_bit_commP {p q : SqU6 gr3R} (hp : p ∈ stageQ) (hq : q ∈ stageQ) :
    selPar (commP p q).o = 0 := by
  rw [commP, stageQ_bit_mul (stageQ.mul_mem (stageQ.mul_mem (stageQ.inv_mem hp)
      (stageQ.inv_mem hq)) hp) hq,
    stageQ_bit_mul (stageQ.mul_mem (stageQ.inv_mem hp) (stageQ.inv_mem hq)) hp,
    stageQ_bit_mul (stageQ.inv_mem hp) (stageQ.inv_mem hq), stageQ_bit_inv hp,
    stageQ_bit_inv hq]
  exact (by decide : ∀ u v : ZMod 2, u + v + u + v = 0) _ _

theorem stageQ_bit_pow {p : SqU6 gr3R} (hp : p ∈ stageQ) :
    ∀ k : ℕ, selPar (p ^ k).o = (k : ZMod 2) * selPar p.o
  | 0 => by rw [pow_zero, Nat.cast_zero, zero_mul, SqU6.one_o, selPar_zero]
  | k + 1 => by
    rw [pow_succ, stageQ_bit_mul (stageQ.pow_mem hp k) hp, stageQ_bit_pow hp k, Nat.cast_succ]
    ring

theorem commP_mem_stageQ {p q : SqU6 gr3R} (hp : p ∈ stageQ) (hq : q ∈ stageQ) :
    commP p q ∈ stageQ :=
  stageQ.mul_mem (stageQ.mul_mem (stageQ.mul_mem (stageQ.inv_mem hp) (stageQ.inv_mem hq)) hp) hq

theorem conjP_mem_stageQ {x g : SqU6 gr3R} (hx : x ∈ stageQ) (hg : g ∈ stageQ) :
    conjP x g ∈ stageQ :=
  stageQ.mul_mem (stageQ.mul_mem (stageQ.inv_mem hg) hx) hg

theorem sqWord_mem_stageQ {s x y : SqU6 gr3R} (hs : s ∈ stageQ) (hx : x ∈ stageQ)
    (hy : y ∈ stageQ) : sqWord s x y ∈ stageQ :=
  stageQ.mul_mem (stageQ.mul_mem (stageQ.mul_mem
    (stageQ.inv_mem (conjP_mem_stageQ hx hs)) (stageQ.inv_mem (stageQ.pow_mem hx 3)))
    (stageQ.pow_mem hy 2)) (commP_mem_stageQ hy (conjP_mem_stageQ hy hs))

theorem handleWord_mem_stageQ : ∀ (n : ℕ) (u v : Fin n → SqU6 gr3R), (∀ k, u k ∈ stageQ) →
    (∀ k, v k ∈ stageQ) → handleWord u v ∈ stageQ
  | 0, _, _, _, _ => by rw [handleWord_zero]; exact one_mem _
  | n + 1, u, v, hu, hv => by
    rw [handleWord_succ]
    exact stageQ.mul_mem (commP_mem_stageQ (hu 0) (hv 0))
      (handleWord_mem_stageQ n _ _ (fun k => hu _) (fun k => hv _))

theorem stageQ_bit_handleWord : ∀ (n : ℕ) (u v : Fin n → SqU6 gr3R), (∀ k, u k ∈ stageQ) →
    (∀ k, v k ∈ stageQ) → selPar (handleWord u v).o = 0
  | 0, _, _, _, _ => by rw [handleWord_zero, SqU6.one_o, selPar_zero]
  | n + 1, u, v, hu, hv => by
    rw [handleWord_succ, stageQ_bit_mul (commP_mem_stageQ (hu 0) (hv 0))
      (handleWord_mem_stageQ n _ _ (fun k => hu _) (fun k => hv _)),
      stageQ_bit_handleWord n _ _ (fun k => hu _) (fun k => hv _), add_zero]
    exact stageQ_bit_commP (hu 0) (hv 0)

/-- The core word's class-five bit vanishes on `Q`: the conjugate and the cube contribute
`selPar x.o` and `3 * selPar x.o`, the square contributes `2 * selPar y.o`, and the commutator
contributes nothing, so the total is `4 * selPar x.o = 0`. -/
theorem stageQ_bit_sqWord {s x y : SqU6 gr3R} (hs : s ∈ stageQ) (hx : x ∈ stageQ)
    (hy : y ∈ stageQ) : selPar (sqWord s x y).o = 0 := by
  have hcx : conjP x s ∈ stageQ := conjP_mem_stageQ hx hs
  have hcy : conjP y s ∈ stageQ := conjP_mem_stageQ hy hs
  have h1 : selPar ((conjP x s)⁻¹ * (x ^ 3)⁻¹).o
      = selPar x.o + ((3 : ℕ) : ZMod 2) * selPar x.o := by
    rw [stageQ_bit_mul (stageQ.inv_mem hcx) (stageQ.inv_mem (stageQ.pow_mem hx 3)),
      stageQ_bit_inv hcx, stageQ_bit_inv (stageQ.pow_mem hx 3), stageQ_bit_conj hx hs,
      stageQ_bit_pow hx 3]
  have h2 : selPar ((conjP x s)⁻¹ * (x ^ 3)⁻¹ * y ^ 2).o
      = selPar x.o + ((3 : ℕ) : ZMod 2) * selPar x.o + ((2 : ℕ) : ZMod 2) * selPar y.o := by
    rw [stageQ_bit_mul (stageQ.mul_mem (stageQ.inv_mem hcx)
      (stageQ.inv_mem (stageQ.pow_mem hx 3))) (stageQ.pow_mem hy 2), h1, stageQ_bit_pow hy 2]
  rw [sqWord, stageQ_bit_mul (stageQ.mul_mem (stageQ.mul_mem
    (stageQ.inv_mem hcx) (stageQ.inv_mem (stageQ.pow_mem hx 3))) (stageQ.pow_mem hy 2))
    (commP_mem_stageQ hy hcy), h2, stageQ_bit_commP hy hcy]
  exact (by decide : ∀ u v : ZMod 2,
    u + ((3 : ℕ) : ZMod 2) * u + ((2 : ℕ) : ZMod 2) * v + 0 = 0) _ _

/-- ⭐⭐⭐ **THE ORTHOGONAL ROUTE IS CLOSED.**  At any marking all of whose slots have an even
`(1,2)`-column, an even `(5,6)`-column and even outer class-two columns - the exact condition
under which every stage-four covector vanishes, so that `gaThreeShiftO_even_of_columns` gives
the forcing for **arbitrary** dressings with no achievability at all - the class-five selection
bit is **already** `0`.  So unlike wave 59's `orth` point and wave 60's `orthFiveMark`, there is
no stage-four marking at which the free hypothesis says anything. -/
theorem stageQ_bit_even {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R} (hm : ∀ i, m i ∈ stageQ) :
    selPar (sqRelWord m).o = 0 := by
  rw [sqRelWord, stageQ_bit_mul (sqWord_mem_stageQ (hm 0) (hm 1) (hm 2))
    (handleWord_mem_stageQ h _ _ (fun k => hm _) (fun k => hm _)),
    stageQ_bit_sqWord (hm 0) (hm 1) (hm 2),
    stageQ_bit_handleWord h _ _ (fun k => hm _) (fun k => hm _), add_zero]

end Closed

/-! ## 6 The class-five sharp line does NOT survive one filtration step wider -/

section OrthFiveDies

/-- The stage-four dressing that kills wave 60's orthogonal point: the handle-`U` slot alone,
by the fifth power of the triple commutator `[[V, sigma], x0]`. -/
def orthStageDress : Fin (sqRank 1) → SqU6 gr3R :=
  fun i => if (i : ℕ) = 3 then ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0⟩ else 1

/-- It is a fifth power of a triple commutator of the point's own letters. -/
theorem orthStage_generator :
    (commP (commP orthFiveV orthFiveS) orthFiveX) ^ 5
      = (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0⟩ : SqU6 gr3R) := by decide

/-- …so it is ACHIEVABLE: it lies in `gamma_3` of the point's image. -/
theorem orthStageDress_mem (i : Fin (sqRank 1)) :
    orthStageDress i ∈ forceLcs (Subgroup.closure (Set.range (orthFiveMark 1 0))) 2 := by
  rw [orthStageDress]
  split_ifs with hi
  · have hS : orthFiveS ∈ Subgroup.closure (Set.range (orthFiveMark 1 0)) :=
      Subgroup.subset_closure ⟨0, orthFiveMark_zero⟩
    have hX : orthFiveX ∈ Subgroup.closure (Set.range (orthFiveMark 1 0)) :=
      Subgroup.subset_closure ⟨1, orthFiveMark_one⟩
    have hV : orthFiveV ∈ Subgroup.closure (Set.range (orthFiveMark 1 0)) :=
      Subgroup.subset_closure ⟨sqHandleIdxV 0, orthFiveMark_handleV⟩
    rw [← orthStage_generator]
    exact pow_mem (commP_mem_commSub (commP_mem_commSub hV hS) hX) 5
  · exact one_mem _

/-- ⭐⭐⭐ **WAVE 60's ORTHOGONAL POINT IS KILLED AT STAGE FOUR.**  There
`orthFive_pair_eq_zero` makes the class-five pairing identically `0` and `orthFive_no_kill`
excludes every `gamma_4`-shaped refinement of any provenance; one filtration step wider an
**achievable** `gamma_3`-dressing of a single slot kills the relator outright. -/
theorem orthFive_stage_kill :
    sqRelWord (conFiveDress (orthFiveMark 1 0) orthStageDress) = 1 := by decide

/-- ⭐⭐⭐ …so the class-five sharp invariant is not a stage-four sufficient condition. -/
theorem orthFive_stageForces_false : ¬ StageForces (orthFiveMark 1 0) := by
  intro hF
  have hb := hF orthStageDress orthStageDress_mem orthFive_stage_kill
  rw [sqRelWord_orthFiveMark, liftC6_o] at hb
  exact absurd hb (by decide)

/-- ⚠ **And the reason is visible in the covectors**: the class-five ones read the dressing's
`(m, n)` and vanish at that point, while the stage-four ones also read `j`, and the killing
dressing is `<j = 5>`, invisible to every class-five covector. -/
theorem orthStage_kill_is_gaThree :
    (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0⟩ : SqU6 gr3R).IsGaThree
      ∧ ¬ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0⟩ : SqU6 gr3R).IsGaFour := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  intro hc
  exact absurd hc.2.2.2.2.2.2.2.2.2 (by decide)

end OrthFiveDies

/-! ## 7 What the committed statements carry on the sharp line -/

section Migration

variable {h : ℕ} {j : Fin h}

/-- **Wave 60's committed forcing, on the sharp line.**  `stageWit_sigma_forced` carries
`v.a` and `v.c` even together with the whole lower-central-series chain; on the line it carries
only that the centrally acting achievable dressings pair evenly. -/
theorem stageWit_stageForces_of_stageCentral {v : SqU6 gr3R} {c : gr3R}
    (hres : sqRelWord (stageWit h j v) = SqU6.liftO c)
    (hC : StageCentral (stageWit h j v)) : StageForces (stageWit h j v) :=
  stageForces_of_stageCentral hres hC

/-- **…and the committed statement is recovered from it**, at the committed point: wave 60's
own `stageImage_le_stageN1` gives the parity line, which gives the sharp line, which gives the
forcing. -/
theorem stageWit_stageForces (h : ℕ) (j : Fin h) : StageForces (stageWit h j stageX) :=
  stageForces_of_stageOrth (sqRelWord_stageWit_diag h j)
    (stageOrth_of_le_stageN1 (stageImage_le_stageN1 (h := h) (j := j)
      ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩))

/-- …giving `GradedFiveStageFour.sqRelWord_stageWit_diag_ne_one` back with nothing lost. -/
theorem sqRelWord_stageWit_diag_ne_one_of_sharp {z : Fin (sqRank h) → SqU6 gr3R}
    (hz : ∀ i, z i ∈ forceLcs (stageImage h j stageX) 2) :
    sqRelWord (conFiveDress (stageWit h j stageX) z) ≠ 1 := by
  intro hc
  have hp := stageWit_stageForces h j z hz hc
  rw [sqRelWord_stageWit_diag, SqU6.liftO_o] at hp
  exact absurd hp (by decide)

end Migration

/-! ## 8 Axiom pins -/

section AxiomPins

#print axioms gaThreeShift_j
#print axioms gaThreeShift_k
#print axioms gaThreeShift_m
#print axioms gaThreeShift_n
#print axioms SqU6.gaThree_ext
#print axioms SqU6.IsGaThree.mul
#print axioms SqU6.IsGaThree.pow
#print axioms SqU6.gaThree_mul_j
#print axioms SqU6.gaThree_mul_k
#print axioms SqU6.gaThree_mul_l
#print axioms SqU6.gaThree_mul_m
#print axioms SqU6.gaThree_mul_n
#print axioms SqU6.gaThree_mul_o
#print axioms gaThreeShift_mul
#print axioms gaThreeShift_pow
#print axioms SqU6.liftO_pow
#print axioms forceLcs_two_le_gaThreeSub
#print axioms isGaThree_of_mem_forceLcs
#print axioms StageForces
#print axioms StageOrth
#print axioms StageCentral
#print axioms stageCentral_of_stageOrth
#print axioms stageForces_of_stageCentral
#print axioms stageCentral_of_stageForces
#print axioms stageForces_iff_stageCentral
#print axioms stageForces_of_stageOrth
#print axioms stageOrth_of_columns
#print axioms stageOrth_of_le_stageN1
#print axioms stageForces_of_le_stageN1
#print axioms gaThreePair_even_of_outer
#print axioms gaThreeCorr_even_of_outer
#print axioms gaThreeCore_o_even_of_outer
#print axioms gaThreeHandle_o_even_of_outer
#print axioms gaThreeShiftO_even_of_outer
#print axioms gaThreeShiftO_even_of_columns
#print axioms forceLcs_two_le_fiveEvenL
#print axioms stageOrth_of_outer
#print axioms mixStageS
#print axioms mixStageX
#print axioms mixStageY
#print axioms mixStageU
#print axioms mixStageV
#print axioms mixStageMark
#print axioms sqRelWord_mixStageMark
#print axioms commP_mixStageUV_live
#print axioms mixStage_columns
#print axioms mixStage_stageOrth
#print axioms mixStage_stageForces
#print axioms mixStage_diag_ne_one
#print axioms mixStageV_not_stageN1
#print axioms mixStage_not_le_stageN1
#print axioms mixStage_breaker_mem
#print axioms mixStage_breaker_not_stageN3
#print axioms mixStage_forceLcs_not_le_stageN3
#print axioms mixStage_separates
#print axioms mixStage_decide_crosscheck
#print axioms stageQ
#print axioms mem_stageQ
#print axioms stageQ_bit_mul
#print axioms stageQ_bit_inv
#print axioms stageQ_bit_conj
#print axioms stageQ_bit_commP
#print axioms stageQ_bit_pow
#print axioms commP_mem_stageQ
#print axioms conjP_mem_stageQ
#print axioms sqWord_mem_stageQ
#print axioms handleWord_mem_stageQ
#print axioms stageQ_bit_handleWord
#print axioms stageQ_bit_sqWord
#print axioms stageQ_bit_even
#print axioms orthStageDress
#print axioms orthStage_generator
#print axioms orthStageDress_mem
#print axioms orthFive_stage_kill
#print axioms orthFive_stageForces_false
#print axioms orthStage_kill_is_gaThree
#print axioms stageWit_stageForces_of_stageCentral
#print axioms stageWit_stageForces
#print axioms sqRelWord_stageWit_diag_ne_one_of_sharp

end AxiomPins

end SqCore

end Dyadic

end GQ2

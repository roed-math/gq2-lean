/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedStageFour

/-!
# W64-PSI4: the FOUR gap markings, CLOSED

Wave 61 MEASURED four of 1650 admissible markings at which the parity line `StageOrth` fails
and the stage-four forcing `StageForces` holds.  Wave 62 could not prove them and diagnosed the
resistance.  W63-FOUR removed the obstacle - `le_of_gens_three` bounds the achievable lattice
from the generator triples alone, without naming a containing subgroup - and landed the exact
lattice bound at all four, reducing the forcing to ONE `Z/8`-linear identity that it stated as a
hypothesis and verified computationally.

This file discharges that identity and closes the four.

## ⭐⭐⭐ Headline: THE FOUR FORCING STATEMENTS, UNCONDITIONAL

⭐⭐⭐ `stageForces_gapOneA`, `stageForces_gapOneB`, `stageForces_gapTwoA`,
`stageForces_gapTwoB`: at each of wave 61's four gap markings, at **every** handle count and
**every** handle, `StageForces` holds.  No hypothesis: these are
`GradedStageFour.stageForces_gapOneA_of_psi` and its three siblings with their sole hypothesis
supplied by `psiOne_gapOneMark` and its three siblings, proved here.

Since each of the four relators is a central translation with an ODD class-five residue
(`sqRelWord_gapOneMark` is `liftO 5`, `sqRelWord_gapTwoMark` is `liftO 1`), `StageForces` says
at these markings exactly that **no achievable stage-four dressing kills the relator**, which is
what `gapOneA_no_kill` and its three siblings state with the relator substituted.

## ⭐⭐⭐ Headline 2: WAVE 61'S STRICTNESS MEASUREMENT, IN FULL, AS A THEOREM

⭐⭐⭐ `gapOneA_gap` and its three siblings: at each of the four, at every handle count and every
handle, the relator is the stated central translation, the forcing HOLDS **and the parity line
`StageOrth` FAILS**.  (There is no `Admissible` predicate in the tree; the first conjunct is the
relator identity itself.)
Wave 61's diagram

```text
   letters in stageN1  =>  achievable dressings in stageN3  =>  StageOrth  =>  StageCentral
                                                                          <=>  the forcing
```

recorded the strictness of the first two implications as theorems and the strictness of the
**last** one as a measurement at exactly these four markings.  It is now a theorem too.

The refuting dressing is again the marking's own arithmetic: `gapOneW = [[sigma, V], V]` and
`gapTwoW = [[sigma, V], sigma]` are weight-three brackets of the letters, so achievability is two
applications of `Subgroup.commutator_mem_commutator` on top of three `Subgroup.subset_closure`,
and nothing else.  Carried on the live handle's `U`-slot (`gap-1`) or on the `x0`-slot (`gap-2`),
each moves the class-five row by an ODD amount, `7` and `5` respectively, which is what makes it
pair oddly while killing nothing.  ⚠ The accompanying class-four movements, by `2` and by `4`,
are MEASURED (`scripts/w64_psi4/results/close.txt`); the Lean statements below compute the `.o`
row only.  `StageCentral` is settled separately
in section 6, where it HOLDS at all four: `stageForces_iff_stageCentral` ties it to the forcing,
and the four relators satisfy that theorem's hypothesis.

## ⭐⭐ What the identity actually is, and why it is not an arithmetic accident

⭐⭐ `psiOne_gapOneMark`: for every dressing tuple `z` all of whose slots lie in `gapKOne`,
`psiOne (gaThreeShift h (gapOneMark h j) z) = 0`; and the three siblings.  The proof is three
steps, and the middle one is the only new mathematics:

* **the block terms die.**  `gaThreeShiftO` carries two central collection terms, and each is a
  frame quantity times a Frobenius weight `-4 x + 2 y`.  The certificate reads the class-five
  row multiplied by `4`, and `4 * (-4 x + 2 y) = 8 * (-2 x + y) = 0`, which is what makes
  `psiOne_gaThreeShift` a statement with no block term in it, at ANY marking and any handle
  count.  ⚠ That arithmetic is not a named lemma: the block terms are discharged inside the
  reduction lemmas themselves, by the `gr8c` witness each of their `linear_combination` calls
  carries;
* **the dead handles die.**  At a `fiveTuple` marking every handle other than the live one has
  both letters trivial, and `gaThreeHandle 1 1 z w = 1` (`gaThreeHandle_one_one`), so the handle
  sums collapse to their single live term (`handleShiftSum`).  Neither step reads the letters;
* **what is left is `Z/8`-linear in the thirty dressing coordinates**, and the target was
  constructed to be the joint kernel of its five slot pullbacks.  So the identity is an exact
  linear combination of the target's own defining conditions, with the coefficients

  | marking | pullback of the certificate | combination |
  |---|---|---|
  | `gap-1`, slot `x0` | `6k + 4m + 4n` | `3 * (2k + 4m + 4n)` |
  | `gap-1`, slot `x1` | `2l + 4n` | `1 * (2l + 4n)` |
  | `gap-1`, slot `U` | `6k + 2l + 4m` | `3 * (2k + 4m + 4n) + 1 * (2l + 4n)` |
  | `gap-2`, slot `x0` | `5k + 4n` | `5 * (k + 4n)` |
  | `gap-2`, slot `x1` | `2m` | `1 * (2m)` |
  | `gap-2`, slot `U` | `4l` | `1 * (4l)` |
  | `gap-2`, slot `V` | `6k + 4l` | `6 * (k + 4n) + 1 * (4l)` |

  and the remaining pullbacks identically zero: the `sigma` slot at all four, and at `gap-1` the
  `V` slot as well, so `gap-1` has TWO identically-zero slots and not one.

⚠ **`ring` does not close it.**  `ring` normalises numerals as integers and does not reduce them
modulo `8`, so the identity is closed by `linear_combination` against the target's conditions
**plus** an explicit integer witness `W` times `gr8c : (8 : gr3R) = 0`.  `W` is computed in
`scripts/w64_psi4/derive.py` by reimplementing `gaThreeCore`, `gaThreeCorr`, `gaThreePair` and
`gaThreeHandle` over the INTEGERS, and the resulting form is cross-checked, all `30` coefficients
at each of the four markings, against wave 61's `sharp4lib.slot_matrix`, which is read off wave
59's honest `6 x 6` matrices and never consults a Lean formula.

## PROVED versus MEASURED

**PROVED** here, with no `sorry`, no new axiom and no `native_decide`: the two general reduction
lemmas (`psiOne_gaThreeShift`, `psiTwo_gaThreeShift`) at any marking and any handle count; the
dead-handle collapse at any `fiveTuple` marking over any commutative ring; the four identities;
the four forcing statements and their no-kill readings; the two single-slot closed forms of the
class-five row; the failure of the parity line at all four; and (W65-CONSOL) the SHARP line
`StageCentral` at all four.  Everything at every handle count
and every handle.

**MEASURED**, and NOT claimed here: that these are the ONLY four of wave 61's 1650
admissible markings with this behaviour (`scripts/w61_sharp4/results/sweep_sharp4.txt`); and the
lattice cardinalities `1024` and `256` against which the Lean targets carry index-`16` slack.
Nothing below asserts that the targets ARE the lattices.

⚠ **A gap in W63-FOUR's certification, found and closed.**  `scripts/w63_four/certify.py`
verifies its `216` weight-three brackets with `u6mat.commP`, which is the PAPER convention
`[x, y] = x⁻¹ y⁻¹ x y`, while the Lean file's `gapOneABr` and the whole generator reduction use
mathlib's `⁅x, y⁆ = x y x⁻¹ y⁻¹`.  The two families are different sets, so W63's `216`-bracket
check was not a check of the arithmetic input its Lean `decide` closes.  Both statements are in
fact true: `scripts/w64_psi4/close.py` part D re-runs the census in the MATHLIB convention at all
four markings and finds `0` violations of `864`.  ⚠ The same convention gap bites the odd
dressing below: `[[sigma, V], V]` pairs to `3` in the paper convention and to `7` in mathlib's,
and only the second is what Lean proves.

## The doctrine-rule-3 check

The four theorems consumed here are conditional, so an identity that was subtly not their
hypothesis would silently promote them into false unconditional ones.  The four identities below
are stated in EXACTLY the shape the hypotheses take: same tuple type `Fin (sqRank h) → SqU6 gr3R`,
same membership `∀ i, z i ∈ gapKOne` over ALL slots and not only the five live ones, the same
marking term `gapOneMark h j` and not a `fiveTuple` unfolding of it, and the same free `h` and
`j`, so the forcing statements below are literally `stageForces_gapOneA_of_psi
psiOne_gapOneMark` and its three siblings with nothing in between.
`scripts/w64_psi4/close.py` re-runs W63-FOUR's own certification against the proved form, parses
both files and compares the four hypotheses as strings, re-checks that the five slot pullbacks
are the ones `certify.txt` measured, and re-establishes the CONCLUSION independently on the
honest matrices, so that the four unconditional statements are confirmed by a route that never
consults a Lean formula.

## Sweep against the tree's refutations

Nothing here quotes the retracted wave-56 carried-input structures; nothing here is a general
criterion in the sense wave 60's three-covector class-five line failed to be, since every
statement below that names a marking names one of the four, and the rest - sections 1-2, and the
`gaThreeShiftO_fiveTuple_*` forms of section 5 - are marking-agnostic reduction identities that
assert no criterion at all; nothing here widens the `gamma_2` route that wave
62 closed by a functional collision or that W63-CENTRAL2 refuted at wave 60's binder point, the
filtration layer being `gamma_3` throughout; nothing here asserts block-blindness, which
W63-SECOND refuted; and W62's handle-count invariant is not consumed.  ⚠ **W65-CONSOL amends
the last sentence of this paragraph**, which used to read "the centrality line ... this file does
not touch it": section 6 now DOES touch it, and holds it at all four, by composing section 4 with
`stageForces_iff_stageCentral` after checking that theorem's load-bearing hypothesis (W62's
`stageForces_not_imp_stageCentral` shows it cannot be dropped).

## Contents

* **1** the dead-handle collapse; **2** ⭐⭐ the certificate rows of the shift;
* **3** ⭐⭐⭐ the four identities; **4** ⭐⭐⭐ the four forcing statements;
* **5** ⭐⭐⭐ the parity line refuted at all four; **6** ⭐⭐⭐ the SHARP line HELD at all four;
* **7** axiom pins.

## Merge notes

Every declaration below is new.  Reused: `psiOne`, `psiTwo`, `gapKOne`, `gapKTwo`,
`mem_gapKOne`, `mem_gapKTwo`, `gapOneMark`, `gapOneMark'`, `gapTwoMark`, `gapTwoMark'`,
`gapOneS`/`gapOneX`/`gapOneY`/`gapOneY'`/`gapOneU`/`gapOneV`, the `gapTwo*` letters and
`stageForces_gapOneA_of_psi` and its three siblings (`GradedStageFour`); `gaThreeShift`,
`gaThreeShiftO`, `gaThreeCore`, `gaThreeHandle`, `gaThreePair`, `gaThreePairL`, `gaThreePairR`,
`gaThreeCorr`, `sqFoxX6`, `gaThreeShift_l`, `gaThreeShift_o` (`GradedFiveStageFour`);
`gaThreeShift_m`, `gaThreeShift_n`, `StageForces` (`GradedStageNecessity`); `fiveTuple`,
`fiveTuple_zero`/`_one`/`_two`/`_handleU`/`_handleV`/`_handleU_ne`/`_handleV_ne`, `sqRank`,
`sqHandleIdxU`, `sqHandleIdxV`, `sqU6BlockF`, `sqU6BlockI` (`GradedFive`, `Cores`,
`GradedFiveDefect`); `StageOrth`, `sqVal_zero`/`_one`/`_two`, `sqHandleIdxU_val`,
`sqHandleIdxV_val`, `conFiveDress`, `SqU6.liftO_o`, `forceLcs` (`GradedStageNecessity`, `Cores`,
`GradedFiveDefect`, `GradedFiveForce`).  `gr8c` is a private copy of `GradedStageFour`'s private
`gr8`.  W65-CONSOL's section 6 additionally reuses `StageCentral`, `stageForces_iff_stageCentral`
(`GradedStageNecessity`) and `selPar`, `selPar_one` (`GradedSelect`).

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`; every `decide` is on `ZMod 8` or on `SqU6 gr3R`
built over it.  All **56** committed prints are subsets of
`[propext, Classical.choice, Quot.sound]`: `41` std-3, `14` `propext` + `Quot.sound`, `1`
`propext` alone.  No census axiom is consumed.
-/

open scoped commutatorElement

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The dead handles of a one-handle-live marking contribute nothing -/

section DeadHandles

variable {R : Type} [CommRing R] {h : ℕ} {j : Fin h}

/-- ⭐ **A handle whose two letters are both trivial shifts by nothing.**  All three live rows
of `gaThreeHandle` pair a dressing coordinate against a letter coordinate, so they vanish
identically when both letters do; the two block coefficients `p.d * q.e - p.e * q.d` and
`p.a * q.b - p.b * q.a` vanish for the same reason. -/
theorem gaThreeHandle_one_one (z w : SqU6 R) : gaThreeHandle (1 : SqU6 R) 1 z w = 1 := by
  ext <;>
    simp only [gaThreeHandle, gaThreePair, gaThreePairL, gaThreePairR, SqU6.one_a, SqU6.one_b,
      SqU6.one_c, SqU6.one_d, SqU6.one_e, SqU6.one_f, SqU6.one_g, SqU6.one_h, SqU6.one_i,
      SqU6.one_j, SqU6.one_k, SqU6.one_l, SqU6.one_m, SqU6.one_n, SqU6.one_o] <;>
    ring

/-- …so at a `fiveTuple` marking every handle other than the live one is silent, whatever the
dressing does there. -/
theorem gaThreeHandle_fiveTuple_ne {S X Y U V : SqU6 R} {z : Fin (sqRank h) → SqU6 R}
    {k : Fin h} (hk : k ≠ j) :
    gaThreeHandle (fiveTuple R h j S X Y U V (sqHandleIdxU k))
        (fiveTuple R h j S X Y U V (sqHandleIdxV k))
        (z (sqHandleIdxU k)) (z (sqHandleIdxV k)) = 1 := by
  rw [fiveTuple_handleU_ne hk, fiveTuple_handleV_ne hk, gaThreeHandle_one_one]

/-- ⭐ **The handle sum of the stage-four shift collapses to the live handle**, at every handle
count.  Stated for an arbitrary row `F` killing the identity, so that the `m`-, `n`- and
`o`-rows are all instances. -/
theorem handleShiftSum {S X Y U V : SqU6 R} {z : Fin (sqRank h) → SqU6 R}
    (F : SqU6 R → R) (hF : F 1 = 0) :
    ∑ k : Fin h, F (gaThreeHandle (fiveTuple R h j S X Y U V (sqHandleIdxU k))
        (fiveTuple R h j S X Y U V (sqHandleIdxV k))
        (z (sqHandleIdxU k)) (z (sqHandleIdxV k)))
      = F (gaThreeHandle U V (z (sqHandleIdxU j)) (z (sqHandleIdxV j))) := by
  refine (Finset.sum_eq_single j (fun k _ hk => ?_)
    (fun hj => absurd (Finset.mem_univ j) hj)).trans ?_
  · rw [gaThreeHandle_fiveTuple_ne hk]
    exact hF
  · rw [fiveTuple_handleU, fiveTuple_handleV]

end DeadHandles

/-! ## 2 The certificate rows of the stage-four shift -/

section CertificateRows

variable {h : ℕ} {j : Fin h}

private theorem gr8c : (8 : gr3R) = 0 := by decide

/-- ⭐⭐ **The `gap-1` certificate reads the shift with NO block term**, at any marking and any
handle count: the class-three row is the Frobenius weights alone, and the two central collection
terms of `gaThreeShiftO` are killed by the certificate's factor of `4`. -/
theorem psiOne_gaThreeShift (m z : Fin (sqRank h) → SqU6 gr3R) :
    psiOne (gaThreeShift h m z)
      = (-4 * (z 1).l + 2 * (z 2).l)
        + 2 * ((gaThreeCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).n
          + ∑ k : Fin h, (gaThreeHandle (m (sqHandleIdxU k)) (m (sqHandleIdxV k))
              (z (sqHandleIdxU k)) (z (sqHandleIdxV k))).n)
        + 4 * ((gaThreeCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).o
          + ∑ k : Fin h, (gaThreeHandle (m (sqHandleIdxU k)) (m (sqHandleIdxV k))
              (z (sqHandleIdxU k)) (z (sqHandleIdxV k))).o) := by
  simp only [psiOne, gaThreeShift_l, gaThreeShift_n, gaThreeShift_o, gaThreeShiftO]
  set BI := sqU6BlockI (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k)) with _
  set BF := sqU6BlockF (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k)) with _
  linear_combination (BI * (-2 * (z 1).j + (z 2).j) - BF * (-2 * (z 1).l + (z 2).l)) * gr8c

/-- …and the `gap-2` certificate likewise: its class-four row carries no block term at all, and
the class-five row's two are killed by the same factor of `4`. -/
theorem psiTwo_gaThreeShift (m z : Fin (sqRank h) → SqU6 gr3R) :
    psiTwo (gaThreeShift h m z)
      = ((gaThreeCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).m
          + ∑ k : Fin h, (gaThreeHandle (m (sqHandleIdxU k)) (m (sqHandleIdxV k))
              (z (sqHandleIdxU k)) (z (sqHandleIdxV k))).m)
        + 4 * ((gaThreeCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).o
          + ∑ k : Fin h, (gaThreeHandle (m (sqHandleIdxU k)) (m (sqHandleIdxV k))
              (z (sqHandleIdxU k)) (z (sqHandleIdxV k))).o) := by
  simp only [psiTwo, gaThreeShift_m, gaThreeShift_o, gaThreeShiftO]
  set BI := sqU6BlockI (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k)) with _
  set BF := sqU6BlockF (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k)) with _
  linear_combination (BI * (-2 * (z 1).j + (z 2).j) - BF * (-2 * (z 1).l + (z 2).l)) * gr8c

/-- ⭐⭐ **The `gap-1` certificate at a one-handle-live marking**: the core shift and the single
live handle, and nothing else. -/
theorem psiOne_gaThreeShift_fiveTuple (S X Y U V : SqU6 gr3R)
    (z : Fin (sqRank h) → SqU6 gr3R) :
    psiOne (gaThreeShift h (fiveTuple gr3R h j S X Y U V) z)
      = (-4 * (z 1).l + 2 * (z 2).l)
        + 2 * ((gaThreeCore S X Y (z 0) (z 1) (z 2)).n
          + (gaThreeHandle U V (z (sqHandleIdxU j)) (z (sqHandleIdxV j))).n)
        + 4 * ((gaThreeCore S X Y (z 0) (z 1) (z 2)).o
          + (gaThreeHandle U V (z (sqHandleIdxU j)) (z (sqHandleIdxV j))).o) := by
  rw [psiOne_gaThreeShift, handleShiftSum SqU6.n SqU6.one_n,
    handleShiftSum SqU6.o SqU6.one_o, fiveTuple_zero, fiveTuple_one, fiveTuple_two]

/-- …and the `gap-2` certificate. -/
theorem psiTwo_gaThreeShift_fiveTuple (S X Y U V : SqU6 gr3R)
    (z : Fin (sqRank h) → SqU6 gr3R) :
    psiTwo (gaThreeShift h (fiveTuple gr3R h j S X Y U V) z)
      = ((gaThreeCore S X Y (z 0) (z 1) (z 2)).m
          + (gaThreeHandle U V (z (sqHandleIdxU j)) (z (sqHandleIdxV j))).m)
        + 4 * ((gaThreeCore S X Y (z 0) (z 1) (z 2)).o
          + (gaThreeHandle U V (z (sqHandleIdxU j)) (z (sqHandleIdxV j))).o) := by
  rw [psiTwo_gaThreeShift, handleShiftSum SqU6.m SqU6.one_m,
    handleShiftSum SqU6.o SqU6.one_o, fiveTuple_zero, fiveTuple_one, fiveTuple_two]

end CertificateRows

/-! ## 3 The four certificate identities -/

section Identities

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐⭐ **THE `gap-1a` IDENTITY.**  The `gap-1` certificate kills the stage-four shift of
every dressing tuple whose slots lie in the `gap-1` target, at every handle count and every
handle.  This is `GradedStageFour.stageForces_gapOneA_of_psi`'s sole hypothesis, and W63-FOUR's
`certify.txt` measured it on all `16384` members of `gapKOne` at each of the five slots.

The proof is the combination `3 * (2k + 4m + 4n)` at `x0`, `(2l + 4n)` at `x1` and both at `U`,
plus the integer witness `W` of `scripts/w64_psi4/derive.py` against `8 = 0`. -/
theorem psiOne_gapOneMark (z : Fin (sqRank h) → SqU6 gr3R) (hz : ∀ i, z i ∈ gapKOne) :
    psiOne (gaThreeShift h (gapOneMark h j) z) = 0 := by
  have e1 := (mem_gapKOne.mp (hz 1)).2.1
  have f2 := (mem_gapKOne.mp (hz 2)).2.2
  have e3 := (mem_gapKOne.mp (hz (sqHandleIdxU j))).2.1
  have f3 := (mem_gapKOne.mp (hz (sqHandleIdxU j))).2.2
  rw [gapOneMark, psiOne_gaThreeShift_fiveTuple]
  simp only [gapOneS, gapOneX, gapOneY, gapOneU, gapOneV, gaThreeCore, gaThreeHandle,
    gaThreePair, gaThreePairL, gaThreePairR, gaThreeCorr, sqFoxX6]
  linear_combination 3 * e1 + f2 + 3 * e3 + f3
    + (3 * (z 0).j + 30 * (z 1).j + 6 * (z 1).k - 5 * (z 1).l - 3 * (z 1).m - 2 * (z 1).o
      + (z 2).o + 12 * (z (sqHandleIdxU j)).j - 2 * (z (sqHandleIdxU j)).l
      - 2 * (z (sqHandleIdxU j)).n + 12 * (z (sqHandleIdxV j)).j
      - (z (sqHandleIdxV j)).k - 2 * (z (sqHandleIdxV j)).m) * gr8c

/-- ⭐⭐⭐ **THE `gap-1b` IDENTITY.**  Same certificate, same combination: the two members of the
`gap-1` pair differ only in the `x1`-slot's class-four row, which no coefficient of the shift
reads. -/
theorem psiOne_gapOneMark' (z : Fin (sqRank h) → SqU6 gr3R) (hz : ∀ i, z i ∈ gapKOne) :
    psiOne (gaThreeShift h (gapOneMark' h j) z) = 0 := by
  have e1 := (mem_gapKOne.mp (hz 1)).2.1
  have f2 := (mem_gapKOne.mp (hz 2)).2.2
  have e3 := (mem_gapKOne.mp (hz (sqHandleIdxU j))).2.1
  have f3 := (mem_gapKOne.mp (hz (sqHandleIdxU j))).2.2
  rw [gapOneMark', psiOne_gaThreeShift_fiveTuple]
  simp only [gapOneS, gapOneX, gapOneY', gapOneU, gapOneV, gaThreeCore, gaThreeHandle,
    gaThreePair, gaThreePairL, gaThreePairR, gaThreeCorr, sqFoxX6]
  linear_combination 3 * e1 + f2 + 3 * e3 + f3
    + (3 * (z 0).j + 30 * (z 1).j + 6 * (z 1).k - 5 * (z 1).l - 3 * (z 1).m - 2 * (z 1).o
      + (z 2).o + 12 * (z (sqHandleIdxU j)).j - 2 * (z (sqHandleIdxU j)).l
      - 2 * (z (sqHandleIdxU j)).n + 12 * (z (sqHandleIdxV j)).j
      - (z (sqHandleIdxV j)).k - 2 * (z (sqHandleIdxV j)).m) * gr8c

/-- ⭐⭐⭐ **THE `gap-2a` IDENTITY.**  The `gap-2` certificate kills the stage-four shift of every
dressing tuple whose slots lie in the `gap-2` target, at every handle count and every handle:
the combination is `5 * (k + 4n)` at `x0`, `2m` at `x1`, `4l` at `U` and `6 * (k + 4n) + 4l`
at `V`. -/
theorem psiTwo_gapTwoMark (z : Fin (sqRank h) → SqU6 gr3R) (hz : ∀ i, z i ∈ gapKTwo) :
    psiTwo (gaThreeShift h (gapTwoMark h j) z) = 0 := by
  have e1 := (mem_gapKTwo.mp (hz 1)).2.1
  have g2 := (mem_gapKTwo.mp (hz 2)).2.2.2
  have f3 := (mem_gapKTwo.mp (hz (sqHandleIdxU j))).2.2.1
  have e4 := (mem_gapKTwo.mp (hz (sqHandleIdxV j))).2.1
  have f4 := (mem_gapKTwo.mp (hz (sqHandleIdxV j))).2.2.1
  rw [gapTwoMark, psiTwo_gaThreeShift_fiveTuple]
  simp only [gapTwoS, gapTwoX, gapTwoY, gapTwoU, gapTwoV, gaThreeCore, gaThreeHandle,
    gaThreePair, gaThreePairL, gaThreePairR, gaThreeCorr, sqFoxX6]
  linear_combination 5 * e1 + g2 + f3 + 6 * e4 + f4
    + (2 * (z 1).k - 3 * (z 1).l - 3 * (z 1).m - 2 * (z 1).n - 2 * (z 1).o + (z 2).o
      + 4 * (z (sqHandleIdxU j)).j - 4 * (z (sqHandleIdxU j)).l
      - (z (sqHandleIdxV j)).j) * gr8c

/-- ⭐⭐⭐ **THE `gap-2b` IDENTITY.**  Same certificate and same combination as `gap-2a`, for the
same reason as in the `gap-1` pair. -/
theorem psiTwo_gapTwoMark' (z : Fin (sqRank h) → SqU6 gr3R) (hz : ∀ i, z i ∈ gapKTwo) :
    psiTwo (gaThreeShift h (gapTwoMark' h j) z) = 0 := by
  have e1 := (mem_gapKTwo.mp (hz 1)).2.1
  have g2 := (mem_gapKTwo.mp (hz 2)).2.2.2
  have f3 := (mem_gapKTwo.mp (hz (sqHandleIdxU j))).2.2.1
  have e4 := (mem_gapKTwo.mp (hz (sqHandleIdxV j))).2.1
  have f4 := (mem_gapKTwo.mp (hz (sqHandleIdxV j))).2.2.1
  rw [gapTwoMark', psiTwo_gaThreeShift_fiveTuple]
  simp only [gapTwoS, gapTwoX, gapTwoY', gapTwoU, gapTwoV, gaThreeCore, gaThreeHandle,
    gaThreePair, gaThreePairL, gaThreePairR, gaThreeCorr, sqFoxX6]
  linear_combination 5 * e1 + g2 + f3 + 6 * e4 + f4
    + (2 * (z 1).k - 3 * (z 1).l - 3 * (z 1).m - 2 * (z 1).n - 2 * (z 1).o + (z 2).o
      + 4 * (z (sqHandleIdxU j)).j - 4 * (z (sqHandleIdxU j)).l
      - (z (sqHandleIdxV j)).j) * gr8c

end Identities

/-! ## 4 The four forcing statements, unconditional -/

section Forcing

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐⭐ **THE STAGE-FOUR FORCING HOLDS AT `gap-1a`**, at every handle count and every handle,
with no hypothesis.  Its relator is the central translation `liftO 5`, so the conclusion
`selPar (sqRelWord m).o = 0` is FALSE, and the statement says exactly that **no achievable
five-slot stage-four dressing kills the relator** at this marking.  Wave 61 measured this; three
waves later it is a theorem. -/
theorem stageForces_gapOneA : StageForces (gapOneMark h j) :=
  stageForces_gapOneA_of_psi psiOne_gapOneMark

/-- ⭐⭐⭐ …at `gap-1b`. -/
theorem stageForces_gapOneB : StageForces (gapOneMark' h j) :=
  stageForces_gapOneB_of_psi psiOne_gapOneMark'

/-- ⭐⭐⭐ …at `gap-2a`, whose relator is `liftO 1`. -/
theorem stageForces_gapTwoA : StageForces (gapTwoMark h j) :=
  stageForces_gapTwoA_of_psi psiTwo_gapTwoMark

/-- ⭐⭐⭐ …and at `gap-2b`. -/
theorem stageForces_gapTwoB : StageForces (gapTwoMark' h j) :=
  stageForces_gapTwoB_of_psi psiTwo_gapTwoMark'

/-- ⭐⭐⭐ **WHAT THE FORCING SAYS AT `gap-1a`, WITH THE RELATOR SUBSTITUTED.**  Because the
relator there is `liftO 5` and `5` is odd, `StageForces` has a FALSE conclusion, so it reads as
the exclusion: **no achievable five-slot stage-four dressing kills the relator**, at every handle
count and every handle.  This is the statement wave 61 measured and waves 62 and 63 could not
prove. -/
theorem gapOneA_no_kill (z : Fin (sqRank h) → SqU6 gr3R)
    (hz : ∀ i, z i ∈ forceLcs (Subgroup.closure (Set.range (gapOneMark h j))) 2) :
    sqRelWord (conFiveDress (gapOneMark h j) z) ≠ 1 := by
  intro hkill
  have hp := stageForces_gapOneA z hz hkill
  rw [sqRelWord_gapOneMark, SqU6.liftO_o] at hp
  exact absurd hp (by decide)

/-- ⭐⭐⭐ …at `gap-1b`. -/
theorem gapOneB_no_kill (z : Fin (sqRank h) → SqU6 gr3R)
    (hz : ∀ i, z i ∈ forceLcs (Subgroup.closure (Set.range (gapOneMark' h j))) 2) :
    sqRelWord (conFiveDress (gapOneMark' h j) z) ≠ 1 := by
  intro hkill
  have hp := stageForces_gapOneB z hz hkill
  rw [sqRelWord_gapOneMark', SqU6.liftO_o] at hp
  exact absurd hp (by decide)

/-- ⭐⭐⭐ …at `gap-2a`, whose relator is `liftO 1`. -/
theorem gapTwoA_no_kill (z : Fin (sqRank h) → SqU6 gr3R)
    (hz : ∀ i, z i ∈ forceLcs (Subgroup.closure (Set.range (gapTwoMark h j))) 2) :
    sqRelWord (conFiveDress (gapTwoMark h j) z) ≠ 1 := by
  intro hkill
  have hp := stageForces_gapTwoA z hz hkill
  rw [sqRelWord_gapTwoMark, SqU6.liftO_o] at hp
  exact absurd hp (by decide)

/-- ⭐⭐⭐ …and at `gap-2b`. -/
theorem gapTwoB_no_kill (z : Fin (sqRank h) → SqU6 gr3R)
    (hz : ∀ i, z i ∈ forceLcs (Subgroup.closure (Set.range (gapTwoMark' h j))) 2) :
    sqRelWord (conFiveDress (gapTwoMark' h j) z) ≠ 1 := by
  intro hkill
  have hp := stageForces_gapTwoB z hz hkill
  rw [sqRelWord_gapTwoMark', SqU6.liftO_o] at hp
  exact absurd hp (by decide)

end Forcing

/-! ## 5 The parity line, refuted at all four -/

section Parity

variable {h : ℕ} {j : Fin h}

/-- ⭐ **The class-five row of the shift at a dressing carried by the live handle's `U`-slot
alone.**  The core term dies because its three dressings are trivial, the dead handles die by
`gaThreeHandle_one_one`, and the two block terms die because they read the exponent slots'
dressings, which are trivial here. -/
theorem gaThreeShiftO_fiveTuple_handleU {S X Y U V w : SqU6 gr3R}
    {z : Fin (sqRank h) → SqU6 gr3R} (h0 : z 0 = 1) (h1 : z 1 = 1) (h2 : z 2 = 1)
    (hU : z (sqHandleIdxU j) = w) (hV : z (sqHandleIdxV j) = 1) :
    gaThreeShiftO h (fiveTuple gr3R h j S X Y U V) z = (gaThreeHandle U V w 1).o := by
  rw [gaThreeShiftO, handleShiftSum SqU6.o SqU6.one_o, fiveTuple_zero, fiveTuple_one,
    fiveTuple_two, h0, h1, h2, hU, hV]
  simp only [gaThreeCore, gaThreePair, gaThreePairL, gaThreePairR, gaThreeCorr,
    SqU6.one_j, SqU6.one_k, SqU6.one_l, SqU6.one_m, SqU6.one_n, SqU6.one_o]
  ring

/-- …and at a dressing carried by the `x0`-slot alone, where the two block terms need TWO of the
dressing's three class-three rows to vanish: the hypotheses are `w.j = 0` and `w.l = 0`, and
`w.k` is left free. -/
theorem gaThreeShiftO_fiveTuple_x0 {S X Y U V w : SqU6 gr3R}
    {z : Fin (sqRank h) → SqU6 gr3R} (h0 : z 0 = 1) (h1 : z 1 = w) (h2 : z 2 = 1)
    (hU : z (sqHandleIdxU j) = 1) (hV : z (sqHandleIdxV j) = 1)
    (hwj : w.j = 0) (hwl : w.l = 0) :
    gaThreeShiftO h (fiveTuple gr3R h j S X Y U V) z = (gaThreeCore S X Y 1 w 1).o := by
  rw [gaThreeShiftO, handleShiftSum SqU6.o SqU6.one_o, fiveTuple_zero, fiveTuple_one,
    fiveTuple_two, h0, h1, h2, hU, hV]
  simp only [gaThreeHandle, gaThreePair, gaThreePairL, gaThreePairR,
    SqU6.one_j, SqU6.one_k, SqU6.one_l, SqU6.one_m, SqU6.one_n, hwj, hwl]
  ring

/-- ⭐ **The `gap-1` ODD dressing**: the weight-three bracket `[[sigma, V], V]` of the marking's
OWN letters, so its achievability is immediate.  It is `<k = 4, l = 6, m = 1, n = 1, o = 6>`. -/
def gapOneW : SqU6 gr3R := ⁅⁅gapOneS, gapOneV⁆, gapOneV⁆

variable (h j) in
/-- …placed on the live handle's `U`-slot, every other slot undressed. -/
def gapOneOdd : Fin (sqRank h) → SqU6 gr3R :=
  fun i => if (i : ℕ) = (sqHandleIdxU j : ℕ) then gapOneW else 1

theorem gapOneOdd_zero : gapOneOdd h j 0 = 1 := by
  simp only [gapOneOdd, sqVal_zero, sqHandleIdxU_val]
  exact if_neg (by omega)

theorem gapOneOdd_one : gapOneOdd h j 1 = 1 := by
  simp only [gapOneOdd, sqVal_one, sqHandleIdxU_val]
  exact if_neg (by omega)

theorem gapOneOdd_two : gapOneOdd h j 2 = 1 := by
  simp only [gapOneOdd, sqVal_two, sqHandleIdxU_val]
  exact if_neg (by omega)

theorem gapOneOdd_handleU : gapOneOdd h j (sqHandleIdxU j) = gapOneW := by
  show (if ((sqHandleIdxU j : Fin (sqRank h)) : ℕ) = (sqHandleIdxU j : ℕ) then gapOneW else 1)
      = gapOneW
  rw [if_pos rfl]

theorem gapOneOdd_handleV : gapOneOdd h j (sqHandleIdxV j) = 1 := by
  simp only [gapOneOdd, sqHandleIdxU_val, sqHandleIdxV_val]
  exact if_neg (by omega)

/-- ⭐ **The `gap-1` odd dressing pairs to `7`**, at every handle count and every handle: the
whole shift is the single live handle's, and it is odd.  That oddness is why it pairs oddly and
yet kills nothing.  ⚠ The statement computes the `.o` row and nothing else; that the class-four
row moves by `2` is MEASURED (`scripts/w64_psi4/results/close.txt`), not proved here. -/
theorem gapOneW_shift : (gaThreeHandle gapOneU gapOneV gapOneW 1).o = 7 := by decide

/-- ⭐ **The `gap-2` ODD dressing**: the weight-three bracket `[[sigma, V], sigma]`, which is
`<k = 4, m = 4, n = 5, o = 4>`.  ⚠ Not all its class-three rows vanish - `k` is one of them and
equals `4` - but the two the block terms need do: `gapTwoW_j` and `gapTwoW_l` are what feed
`gaThreeShiftO_fiveTuple_x0`, and that is why the block terms die. -/
def gapTwoW : SqU6 gr3R := ⁅⁅gapTwoS, gapTwoV⁆, gapTwoS⁆

theorem gapTwoW_j : gapTwoW.j = 0 := by decide

theorem gapTwoW_l : gapTwoW.l = 0 := by decide

variable (h) in
/-- …placed on the `x0`-slot, every other slot undressed. -/
def gapTwoOdd : Fin (sqRank h) → SqU6 gr3R :=
  fun i => if (i : ℕ) = 1 then gapTwoW else 1

theorem gapTwoOdd_zero : gapTwoOdd h 0 = 1 := by
  simp only [gapTwoOdd, sqVal_zero]
  exact if_neg (by omega)

theorem gapTwoOdd_one : gapTwoOdd h 1 = gapTwoW := by
  show (if ((1 : Fin (sqRank h)) : ℕ) = 1 then gapTwoW else 1) = gapTwoW
  rw [if_pos (sqVal_one h)]

theorem gapTwoOdd_two : gapTwoOdd h 2 = 1 := by
  simp only [gapTwoOdd, sqVal_two]
  exact if_neg (by omega)

theorem gapTwoOdd_handleU : gapTwoOdd h (sqHandleIdxU j) = 1 := by
  simp only [gapTwoOdd, sqHandleIdxU_val]
  exact if_neg (by omega)

theorem gapTwoOdd_handleV : gapTwoOdd h (sqHandleIdxV j) = 1 := by
  simp only [gapTwoOdd, sqHandleIdxV_val]
  exact if_neg (by omega)

/-- ⭐ **The `gap-2` odd dressing pairs to `5`**, an odd amount, which is why it pairs oddly and
yet kills nothing.  ⚠ The statement computes the `.o` row and nothing else; that the class-four
row moves by `4` is MEASURED (`scripts/w64_psi4/results/close.txt`), not proved here. -/
theorem gapTwoW_shift : (gaThreeCore gapTwoS gapTwoX gapTwoY 1 gapTwoW 1).o = 5 := by decide

/-- …and the same at the `gap-2b` letters, whose `x1`-slot differs only in a row the core
shift does not read. -/
theorem gapTwoW_shift' : (gaThreeCore gapTwoS gapTwoX gapTwoY' 1 gapTwoW 1).o = 5 := by decide

private theorem not_dvd_seven : ¬ (2 : gr3R) ∣ 7 := by
  rintro ⟨t, ht⟩
  exact absurd ht (by revert t; decide)

private theorem not_dvd_five : ¬ (2 : gr3R) ∣ 5 := by
  rintro ⟨t, ht⟩
  exact absurd ht (by revert t; decide)

/-- ⭐⭐⭐ **THE PARITY LINE FAILS AT `gap-1a`**, at every handle count and every handle.  Wave
61 measured this; together with `stageCentral_gapOneA` of section 6 it makes the strictness of
`StageOrth => StageCentral` a THEOREM here, `StageCentral` holding and `StageOrth` failing at the
same marking.  This is the last of wave 61's three implications and the only one that wave left
unproved.

⚠ `stageCentral_gapOneA` is the load-bearing input and `stageForces_gapOneA` alone is NOT enough:
the forcing does not imply the sharp line in general, which is exactly what
`GradedStageSeparate.sepMark_separates` and `stageForces_not_imp_stageCentral` exhibit.  What
licenses the composition at this marking is the hypothesis of `stageForces_iff_stageCentral`,
namely `sqRelWord_gapOneMark`: the relator is the central translation `liftO 5`, central in ALL
rows, with odd class-five residue. -/
theorem not_stageOrth_gapOneMark : ¬ StageOrth (gapOneMark h j) := by
  intro hO
  have hv := hO (gapOneOdd h j) (fun i => by
    simp only [gapOneOdd]
    split_ifs
    · exact Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator
        (Subgroup.subset_closure ⟨0, by rw [gapOneMark, fiveTuple_zero]⟩)
        (Subgroup.subset_closure ⟨sqHandleIdxV j, by rw [gapOneMark, fiveTuple_handleV]⟩))
        (Subgroup.subset_closure ⟨sqHandleIdxV j, by rw [gapOneMark, fiveTuple_handleV]⟩)
    · exact one_mem _)
  rw [gapOneMark, gaThreeShiftO_fiveTuple_handleU gapOneOdd_zero gapOneOdd_one gapOneOdd_two
    gapOneOdd_handleU gapOneOdd_handleV, gapOneW_shift] at hv
  exact not_dvd_seven hv

/-- ⭐⭐⭐ …at `gap-1b`. -/
theorem not_stageOrth_gapOneMark' : ¬ StageOrth (gapOneMark' h j) := by
  intro hO
  have hv := hO (gapOneOdd h j) (fun i => by
    simp only [gapOneOdd]
    split_ifs
    · exact Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator
        (Subgroup.subset_closure ⟨0, by rw [gapOneMark', fiveTuple_zero]⟩)
        (Subgroup.subset_closure ⟨sqHandleIdxV j, by rw [gapOneMark', fiveTuple_handleV]⟩))
        (Subgroup.subset_closure ⟨sqHandleIdxV j, by rw [gapOneMark', fiveTuple_handleV]⟩)
    · exact one_mem _)
  rw [gapOneMark', gaThreeShiftO_fiveTuple_handleU gapOneOdd_zero gapOneOdd_one gapOneOdd_two
    gapOneOdd_handleU gapOneOdd_handleV, gapOneW_shift] at hv
  exact not_dvd_seven hv

/-- ⭐⭐⭐ …at `gap-2a`, where the odd dressing sits on the `x0`-slot instead. -/
theorem not_stageOrth_gapTwoMark : ¬ StageOrth (gapTwoMark h j) := by
  intro hO
  have hv := hO (gapTwoOdd h) (fun i => by
    simp only [gapTwoOdd]
    split_ifs
    · exact Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator
        (Subgroup.subset_closure ⟨0, by rw [gapTwoMark, fiveTuple_zero]⟩)
        (Subgroup.subset_closure ⟨sqHandleIdxV j, by rw [gapTwoMark, fiveTuple_handleV]⟩))
        (Subgroup.subset_closure ⟨0, by rw [gapTwoMark, fiveTuple_zero]⟩)
    · exact one_mem _)
  rw [gapTwoMark, gaThreeShiftO_fiveTuple_x0 gapTwoOdd_zero gapTwoOdd_one gapTwoOdd_two
    gapTwoOdd_handleU gapTwoOdd_handleV gapTwoW_j gapTwoW_l, gapTwoW_shift] at hv
  exact not_dvd_five hv

/-- ⭐⭐⭐ …and at `gap-2b`. -/
theorem not_stageOrth_gapTwoMark' : ¬ StageOrth (gapTwoMark' h j) := by
  intro hO
  have hv := hO (gapTwoOdd h) (fun i => by
    simp only [gapTwoOdd]
    split_ifs
    · exact Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator
        (Subgroup.subset_closure ⟨0, by rw [gapTwoMark', fiveTuple_zero]⟩)
        (Subgroup.subset_closure ⟨sqHandleIdxV j, by rw [gapTwoMark', fiveTuple_handleV]⟩))
        (Subgroup.subset_closure ⟨0, by rw [gapTwoMark', fiveTuple_zero]⟩)
    · exact one_mem _)
  rw [gapTwoMark', gaThreeShiftO_fiveTuple_x0 gapTwoOdd_zero gapTwoOdd_one gapTwoOdd_two
    gapTwoOdd_handleU gapTwoOdd_handleV gapTwoW_j gapTwoW_l, gapTwoW_shift'] at hv
  exact not_dvd_five hv

/-- ⭐⭐⭐ **WAVE 61'S MEASUREMENT, IN FULL, AS A THEOREM.**  At `gap-1a`, at every handle count
and every handle: the marking is admissible (its relator is the central translation `liftO 5`,
odd), the stage-four forcing HOLDS, and the parity line FAILS.  So the parity line is strictly
weaker than the forcing, which is the last of wave 61's three implications and the one it left
measured. -/
theorem gapOneA_gap :
    sqRelWord (gapOneMark h j) = SqU6.liftO 5 ∧ StageForces (gapOneMark h j)
      ∧ ¬ StageOrth (gapOneMark h j) :=
  ⟨sqRelWord_gapOneMark, stageForces_gapOneA, not_stageOrth_gapOneMark⟩

/-- ⭐⭐⭐ …at `gap-1b`. -/
theorem gapOneB_gap :
    sqRelWord (gapOneMark' h j) = SqU6.liftO 5 ∧ StageForces (gapOneMark' h j)
      ∧ ¬ StageOrth (gapOneMark' h j) :=
  ⟨sqRelWord_gapOneMark', stageForces_gapOneB, not_stageOrth_gapOneMark'⟩

/-- ⭐⭐⭐ …at `gap-2a`. -/
theorem gapTwoA_gap :
    sqRelWord (gapTwoMark h j) = SqU6.liftO 1 ∧ StageForces (gapTwoMark h j)
      ∧ ¬ StageOrth (gapTwoMark h j) :=
  ⟨sqRelWord_gapTwoMark, stageForces_gapTwoA, not_stageOrth_gapTwoMark⟩

/-- ⭐⭐⭐ …and at `gap-2b`. -/
theorem gapTwoB_gap :
    sqRelWord (gapTwoMark' h j) = SqU6.liftO 1 ∧ StageForces (gapTwoMark' h j)
      ∧ ¬ StageOrth (gapTwoMark' h j) :=
  ⟨sqRelWord_gapTwoMark', stageForces_gapTwoB, not_stageOrth_gapTwoMark'⟩

end Parity

/-! ## 6 The SHARP line at the four -/

section Central

variable {h : ℕ} {j : Fin h}

/-- The `gap-1` residue `5` is odd; this is the second hypothesis of
`stageCentral_of_stageForces` and it is genuinely checked, not assumed. -/
private theorem selPar_five : selPar (5 : gr3R) = 1 := by decide

/-- ⭐⭐⭐ **THE SHARP LINE HOLDS AT `gap-1a`**, at every handle count and every handle.

⚠ **The hypothesis of `stageForces_iff_stageCentral` is LOAD-BEARING and is verified here, not
assumed.**  W62 proved that the forcing does NOT imply the sharp line in general
(`GradedStageSeparate.stageForces_not_imp_stageCentral`, whose witness `sepMark` has a relator
that is central in every row **but its class-three one**).  The composition below is legitimate
exactly because `sqRelWord_gapOneMark` says the relator is the central translation `liftO 5` -
central in ALL rows - and `selPar_five` says its class-five residue is odd. -/
theorem stageCentral_gapOneA : StageCentral (gapOneMark h j) :=
  (stageForces_iff_stageCentral sqRelWord_gapOneMark selPar_five).mp stageForces_gapOneA

/-- ⭐⭐⭐ …at `gap-1b`. -/
theorem stageCentral_gapOneB : StageCentral (gapOneMark' h j) :=
  (stageForces_iff_stageCentral sqRelWord_gapOneMark' selPar_five).mp stageForces_gapOneB

/-- ⭐⭐⭐ …at `gap-2a`, where the residue is `liftO 1`. -/
theorem stageCentral_gapTwoA : StageCentral (gapTwoMark h j) :=
  (stageForces_iff_stageCentral sqRelWord_gapTwoMark selPar_one).mp stageForces_gapTwoA

/-- ⭐⭐⭐ …and at `gap-2b`. -/
theorem stageCentral_gapTwoB : StageCentral (gapTwoMark' h j) :=
  (stageForces_iff_stageCentral sqRelWord_gapTwoMark' selPar_one).mp stageForces_gapTwoB

/-- ⭐⭐⭐ **WAVE 61'S TABLE, WITH ITS LAST MEASURED ENTRY DISCHARGED**, at `gap-1a`, at every
handle count and every handle.  The relator is the central translation `liftO 5`; the stage-four
forcing HOLDS; the SHARP line `StageCentral` HOLDS; and the parity line `StageOrth` FAILS.

So at these markings the diagram

```text
   letters in stageN1  =>  achievable in stageN3  =>  StageOrth  =>  StageCentral  <=>  forcing
```

has its last arrow strict as a THEOREM in both halves: `StageCentral` holds and `StageOrth` does
not.  ⚠ This says nothing about the FIRST two arrows at these markings, which are strict for the
separate reasons of `GradedStageSeparate`, and nothing about how many markings behave this way -
"exactly four of 1650" is still MEASURED. -/
theorem gapOneA_sharp :
    sqRelWord (gapOneMark h j) = SqU6.liftO 5 ∧ StageForces (gapOneMark h j)
      ∧ StageCentral (gapOneMark h j) ∧ ¬ StageOrth (gapOneMark h j) :=
  ⟨sqRelWord_gapOneMark, stageForces_gapOneA, stageCentral_gapOneA, not_stageOrth_gapOneMark⟩

/-- ⭐⭐⭐ …at `gap-1b`. -/
theorem gapOneB_sharp :
    sqRelWord (gapOneMark' h j) = SqU6.liftO 5 ∧ StageForces (gapOneMark' h j)
      ∧ StageCentral (gapOneMark' h j) ∧ ¬ StageOrth (gapOneMark' h j) :=
  ⟨sqRelWord_gapOneMark', stageForces_gapOneB, stageCentral_gapOneB, not_stageOrth_gapOneMark'⟩

/-- ⭐⭐⭐ …at `gap-2a`. -/
theorem gapTwoA_sharp :
    sqRelWord (gapTwoMark h j) = SqU6.liftO 1 ∧ StageForces (gapTwoMark h j)
      ∧ StageCentral (gapTwoMark h j) ∧ ¬ StageOrth (gapTwoMark h j) :=
  ⟨sqRelWord_gapTwoMark, stageForces_gapTwoA, stageCentral_gapTwoA, not_stageOrth_gapTwoMark⟩

/-- ⭐⭐⭐ …and at `gap-2b`. -/
theorem gapTwoB_sharp :
    sqRelWord (gapTwoMark' h j) = SqU6.liftO 1 ∧ StageForces (gapTwoMark' h j)
      ∧ StageCentral (gapTwoMark' h j) ∧ ¬ StageOrth (gapTwoMark' h j) :=
  ⟨sqRelWord_gapTwoMark', stageForces_gapTwoB, stageCentral_gapTwoB, not_stageOrth_gapTwoMark'⟩

end Central

/-! ## 7 Axiom pins -/

section AxiomPins

#print axioms gaThreeHandle_one_one
#print axioms gaThreeHandle_fiveTuple_ne
#print axioms handleShiftSum
#print axioms psiOne_gaThreeShift
#print axioms psiTwo_gaThreeShift
#print axioms psiOne_gaThreeShift_fiveTuple
#print axioms psiTwo_gaThreeShift_fiveTuple
#print axioms psiOne_gapOneMark
#print axioms psiOne_gapOneMark'
#print axioms psiTwo_gapTwoMark
#print axioms psiTwo_gapTwoMark'
#print axioms stageForces_gapOneA
#print axioms stageForces_gapOneB
#print axioms stageForces_gapTwoA
#print axioms stageForces_gapTwoB
#print axioms gapOneA_no_kill
#print axioms gapOneB_no_kill
#print axioms gapTwoA_no_kill
#print axioms gapTwoB_no_kill
#print axioms gaThreeShiftO_fiveTuple_handleU
#print axioms gaThreeShiftO_fiveTuple_x0
#print axioms gapOneW
#print axioms gapOneOdd
#print axioms gapOneOdd_zero
#print axioms gapOneOdd_one
#print axioms gapOneOdd_two
#print axioms gapOneOdd_handleU
#print axioms gapOneOdd_handleV
#print axioms gapOneW_shift
#print axioms gapTwoW
#print axioms gapTwoW_j
#print axioms gapTwoW_l
#print axioms gapTwoOdd
#print axioms gapTwoOdd_zero
#print axioms gapTwoOdd_one
#print axioms gapTwoOdd_two
#print axioms gapTwoOdd_handleU
#print axioms gapTwoOdd_handleV
#print axioms gapTwoW_shift
#print axioms gapTwoW_shift'
#print axioms not_stageOrth_gapOneMark
#print axioms not_stageOrth_gapOneMark'
#print axioms not_stageOrth_gapTwoMark
#print axioms not_stageOrth_gapTwoMark'
#print axioms gapOneA_gap
#print axioms gapOneB_gap
#print axioms gapTwoA_gap
#print axioms gapTwoB_gap
#print axioms stageCentral_gapOneA
#print axioms stageCentral_gapOneB
#print axioms stageCentral_gapTwoA
#print axioms stageCentral_gapTwoB
#print axioms gapOneA_sharp
#print axioms gapOneB_sharp
#print axioms gapTwoA_sharp
#print axioms gapTwoB_sharp

end AxiomPins

end SqCore

end Dyadic

end GQ2

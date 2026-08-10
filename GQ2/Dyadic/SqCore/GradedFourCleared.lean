/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFourMirror

/-!
# W57-CLEARED: the last selected row at every handle count, and the first live handle block

`GradedFourMirror` (wave 56) covered three of the four selected rows at **every** handle count
and priced the fourth exactly:

> The **cleared** row `nuSel h j 0 0` is left where `GradedFourHom` put it, at `h = 1`. …
> widening it would be a fourth instantiation of §2, not new mathematics; it was not attempted
> for length.

and named the structural feature no class-four point had:

> The handle commutator is trivial in the image at both new points (`commP_mirFour`,
> `commP_dblFour`), exactly as at both committed points; **no point with a live handle block
> is produced.**

This file does both.  The first is indeed a fourth instantiation and costs eighty lines.  The
second is not, and it changes what the campaign knows about the handle block.

## Headline 1: all four selected rows are now covered at every handle count

```text
row (t, s)          status before             status now
(0, 0)  CLEARED     GradedFourHom, h = 1      ⭐ every h, every handle j   (§1, clrFour…)
(0, 1)  uncleared v GradedFourMirror, every h  unchanged
(1, 0)  mirror      GradedFourMirror, every h  unchanged
(1, 1)  doubly      GradedFourMirror, every h  unchanged
```

⭐ `sqArbFrame_sigma_forced_cleared` (with its `_gaTwo` companion): at **every** handle count
`h`, at **every** live handle `j`, at the honest continuous homomorphism built by the committed
lift from `GradedSigmaFour`'s own binder point, **every `ν'`-trivial sigma dressing of the
arbitrary-dressing frame whose image is killed by any achievable five-slot class-four refinement
has an even `chi_a`-character.**  The handle-clearing hypotheses `hu`, `hv` of
`GradedFourHom.sqArbFrame_sigma_forced` are discharged from the row rather than carried, exactly
as at the other three rows.  Wave 56's forecast was right: the letters are `sigFourU`,
`sigFourV`, their commutator is trivial, the row puts no pivot power in either handle slot, so
the marking is `GradedFourMirror.mirWit` at the committed letters and **the lattice parameters
`(A, B, C, D, E, F, T, S) = (1, 2, 0, 0, 0, 0, 1, 0)` are the committed ones**, whence
`GradedSigmaFour.sigFourWit_lamThree_even` is reused verbatim at every `h`.

## ⭐⭐ Headline 2: a point with a LIVE handle block, and why the forcing still cannot see it

At every class-four point built so far the handle commutator is trivial in the image.  With the
committed core slots that is **forced**, not chosen: `sqWord sigFourMark sigFourX sigFourY = 1`,
so the relator of a one-handle-live marking is exactly `commP U V` and killing the relator kills
the block.  A live block therefore needs a core word that is **not** trivial, and one that the
block can cancel.

⭐⭐ `liveFourMark`: move the `x₁`-slot's first class-three coordinate from `0` to `3` and the
`v`-letter's second class-two coordinate from `0` to `2`.  Then

```text
sqWord sigFourMark sigFourX liveFourY = ⟨0,…,0, h = 6, 0, 0⟩     (a class-three element)
commP liveFourU liveFourV             = ⟨0,…,0, h = 2, 0, 0⟩     ⭐⭐ LIVE, of order four
```

and the two cancel: `sqRelWord_liveFourMark` kills all ten rows at **every** handle count with
`commP_liveFour_ne_one`.  The `u`-letter is the committed `sigFourU` unchanged, so the odd
dressing, the even dressing, the bit and all three verdicts are the committed ones:

```text
a0 = 1                    relator dies outright     sqRelWord_liveFrame_sigTriv
a0 = (u-letter)²          residue 2, dies to one    sqRelWord_liveFrame_sigUsq[_complete]
a0 = u-letter  (χ_a = 1)  residue 1, survives none  sqRelWord_liveFrame_sigU[_ne_one]
```

**What does the forcing see there?  Nothing new, and §2 proves it cannot.**

⭐⭐ `sqRelWord_sigFourDress_handle_blind`.  The sigma slot is not in the handle block, so the
handle word contributes the *same* amount to the relator whatever the sigma dressing is: for two
markings with the **same** core slots `(σ, x₀, x₁)` and **arbitrary, different** handle blocks,
the four top rows respond to a sigma dressing identically.  ⭐⭐
`sqRelWord_mirTuple_dress_response` states the positive form: the class-four response is
`sigFourRead v x y`, a functional of the core slots alone, in which the handle letters do not
occur.  The selection bit is a *difference* of two dressings, so the block cancels out of it
identically: ⭐⭐ `mirTuple_sigma_bit` gives

```text
selPar (relator at dressing v).j  =  selPar (relator at dressing 1).j  +  selPar v.a
```

for **every** marking of this shape, live block or not.  So the honest verdict is a certified
impossibility rather than a missing construction: **a live handle block exists at class four,
and the class-four sigma forcing provably cannot see it.**  Whatever the block, it enters only
as the constant that the relator condition pins to the core word's residue.  Seeing a handle
block requires a functional the sigma slot meets, and at class four there is none; that is the
`h ≥ 1` route's reason to go to class five.

## ⭐⭐ Headline 3: a live handle block cannot break the soundness either

The block is not merely invisible to the *bit*; it is also harmless to the *increment*, and
that is a second theorem rather than a second observation.  `commP U V` lies in `γ₂` of the
image, so under the achievability convention it is itself a legal handle dressing, and if its
class-three coordinates were odd the increment lemma would fail and the point would be unsound.
They cannot be:

⭐⭐ `sqWord_sigFourMark_gauge_even`.  On the class-two-forced gauge - the `x₀`-slot's columns
`a, c, d, e, f` and its third class-two coordinate `g` all even with vanishing `b`-column, the
`x₁`-slot's columns `a, c, d` even with vanishing `b`-column - **every one of the nine lower
rows of the core word is even.  Only the class-four row can be odd.**  (Derived symbolically
over `ℤ` in `scripts/w57_cleared/`; the `x₀`-slot's `g`-column is exactly the hypothesis the
`i`-row needs, and it is one of `GradedFourRow.rowFrameSub`'s three invariants.)

⭐⭐ `commP_gaThree_even_of_relator`.  Hence at **any** relator-killing one-handle-live marking
over that gauge, at any handle count, `commP U V` has **both** class-three coordinates even.
The relator's own rows protect the forcing: a live block is automatically achievable-shaped.

## Soundness at the live point, and the sharpest bound

The live point leaves `GradedFourRow.rowFrameSub`: its `v`-letter has `f = 2 ≠ 0`, so the
wave-55 invariant "`f`-column vanishes" is **false** here.  It has to be, by ⭐⭐
`commP_central_of_rowFrameSub`: **inside the wave-55 invariants a `ν'`-trivial handle block is
CENTRAL**, so the only live blocks available there are class-four ones, which the increment does
not read at all.  A block live where the increment looks must leave those invariants.  ⭐⭐
`liveFrameSub` weakens the one it must leave to
"`f`-column **even**" - still a subgroup, still enough for ⭐⭐ `commP_mem_liveGaTwoSub`, which
gives **even** (rather than vanishing) first class-three coordinate.  Following the wave-56
doctrine, that is checked to be the sharpest bound the point admits and not a convenience: the
census in `scripts/w57_cleared/results/sweep_cleared.txt` finds the commutator `h`-values
realised in `γ₂` of the honest image to be exactly `{0, 2, 4, 6}` at the live point (so `h = 0`
is refuted there) against exactly `{0}` at the cleared point, and `|⟨slots⟩| = 1048576` against
`65536`.

CORRECTED BY W59-INVARIANT AND W60-MIGRATE: "the sharpest bound the point admits" is right
about the CONCLUSION - `even` cannot be improved to `vanishing` here - and wrong if read as a
statement about the HYPOTHESIS.  The forcing does not need both class-three coordinates of an
achievable move: over the committed gauge the increment's parity is the move's pairing against
the handle slots' outer abelian columns, and at this point the `v`-covector `(V.d, V.a)`
vanishes and the `u`-covector is `(0, 1)`, so **only the second class-three coordinate of the
second handle move is read** (`GradedFourSharp.liveFour_frameOrth_iff`,
`liveFourWit_sigma_forced_sharp`).  The evenness of the first coordinate, which the census
above measures, is spare at this point.  The sharp line is
`GradedFrameNecessity.sigmaForces_iff_frameOrth`.

## PROVED versus carried versus measured

**PROVED**, with no live hypothesis: the cleared row end to end at every handle count and every
handle - ten-row solve, hom, pivot anchor, `b`-column, frame identification, three verdicts,
three soundness statements, forcing in both the lattice and the `γ₂` form, non-vacuity,
class-three blindness; the handle-blindness of the four top dressing responses and of the
selection bit (any ring, any marking of the shape, any handle count); the gauge parity theorem
(any ring); the automatic evenness of a relator-killing handle block (any ring, any handle
count); and the live point end to end, to the same ten-row standard as the cleared one.

**Carried, and named**: nothing beyond legality in the headlines.  The `γ₂`-level statements
carry the campaign's standing **achievability convention** exactly as `GradedGammaTwo` and
`GradedFourMirror` do; the lattice-level statements carry `selLamThree` / `selLamThreePlus` as
models instead.  `mirTuple_sigma_bit` carries the `x₁`-slot's three even columns, discharged at
both points by `decide`.

**Measured, not proved** (`scripts/w57_cleared/results/`): the kill sweep at each point - at the
cleared point `2097152` achievable five-slot refinements, at the live point `134217728`, **zero**
of which kill the odd dressing, while `1024` of `4096` and `65536` of `262144` essentially
distinct ones kill the even dressing; the subgroup census above; and the count of live-block
markings in the scanned family (`120` live against `8` dead).  Also measured: `8` of the `64`
**unrestricted** `γ₃`-moves on the `v`-slot kill the odd dressing at each point, so achievability
is load-bearing here exactly as it is at the committed points.

Every explicit claim of this file is mirrored numerically one for one in
`scripts/w57_cleared/instance_cleared.py`, at `h = 1, 2, 3, 4`, every handle `j < h` and every
pivot residue, and the library is validated against the committed `GradedSigmaFour`,
`GradedFourHom`, `GradedFourRow` and `GradedFourMirror` facts before anything new is derived:
**1487360 comparisons, zero mismatches**, alongside `731` named checks in the derivation
(`derive_cleared.py`, which also carries the symbolic derivation of the gauge parity theorem over
`ℤ`) and `35` in the census (`sweep_cleared.py`).

## What this does NOT do

* The live point sits at the **cleared** row.  At a row with `ν'(v_j) ≠ 0` the handle letters
  carry pivot powers, and whether a live block survives the displacement is not settled here.
* No point with **two** live handles is produced; §2's handle-blindness covers those too, but
  the cross-handle coupling `GradedFour` names at class four is untouched.
* Higher pivot powers (a row value that is a non-unit but nonzero `2`-adic integer) are still
  covered only in principle, by `GradedFourMirror.chiA_row_forced`; no point is built.
* The residual obstruction of `GradedSigmaFour` §7 is untouched and still needs class five.

## Contents

* **1** ⭐ the cleared row `nuSel h j 0 0` at every handle count, end to end;
* **2** ⭐⭐ the handle-blindness of the sigma response and of the selection bit;
* **3** ⭐⭐ the gauge parity theorem and the automatic evenness of a live block;
* **4** ⭐⭐ the live-handle-block point: letters, block, ten-row solve, verdicts;
* **5** the live point as a continuous homomorphism;
* **6** ⭐⭐ soundness at the live point: the widened invariants and the `γ₂`-level bound;
* **7** ⭐⭐ the sigma forcing at the live point and the verdicts on `sqArbFrame`;
* **8** committed axiom prints.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`; every `decide` is on `ZMod 8`, `ZMod 2` or tuples
and words over them.  All committed prints are **std-3** (`propext`, `Classical.choice`,
`Quot.sound`) or a subset; no census axiom is reachable, `sqPivotExp` included.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The cleared row `nuSel h j 0 0`, at every handle count

Wave 56's §2 is stated for arbitrary cleared handle letters with trivial commutator, so the
cleared row is exactly the instantiation at the committed `sigFourU`, `sigFourV`.  The row
clears both handle letters, so **no** pivot power enters either handle slot and the marking does
not depend on the pivot residue at all: there is no `Gen` family here, and the whole section is
`GradedFourMirror` §3-§6 with the displacement removed. -/

section ClearedRow

variable {h : ℕ} {j : Fin h}

/-- The committed handle block is dead, as it must be: with the committed core slots the relator
**is** `commP U V`. -/
theorem commP_clrFour : commP sigFourU sigFourV = 1 := by decide

variable (h j) in
/-- **The cleared row's marking at every handle count**: the committed sigma-, `x₀`- and
`x₁`-slots, the committed letters in the `j`-th handle pair, every other handle letter trivial.
At `h = 1` this is `GradedSigmaFour.sigFourWit 1`. -/
def clrFourMark : Fin (sqRank h) → SqU5 gr3R := mirWit h j sigFourU sigFourV 1

variable (h j) in
/-- The cleared row's witness at every handle count, with the sigma slot dressed by `v`. -/
def clrFourWit (v : SqU5 gr3R) : Fin (sqRank h) → SqU5 gr3R := mirWit h j sigFourU sigFourV v

/-- ⭐ **The ten-row solve at the cleared row, at every handle count.** -/
theorem sqRelWord_clrFourMark : sqRelWord (clrFourMark h j) = 1 :=
  sqRelWord_mirWit_triv commP_clrFour

theorem sqRelWord_clrFourWit_triv : sqRelWord (clrFourWit h j 1) = 1 :=
  sqRelWord_mirWit_triv commP_clrFour

theorem sqRelWord_clrFourWit (v : SqU5 gr3R) :
    sqRelWord (clrFourWit h j v) = sqWord (sigFourMark gr3R * v) sigFourX sigFourY :=
  sqRelWord_mirWit commP_clrFour

/-- The `u`-letter has odd `chi_a`-character: the open channel. -/
theorem clrFourU_chiA : selPar sigFourU.a = 1 := by decide

/-- ⭐ Dressing the sigma slot by the `u`-letter leaves the **odd** residue `1`. -/
theorem sqRelWord_clrFourWit_U : sqRelWord (clrFourWit h j sigFourU) = liftC 1 := by
  rw [sqRelWord_clrFourWit]; decide

/-- …and by its square the **even** residue `2`. -/
theorem sqRelWord_clrFourWit_Usq :
    sqRelWord (clrFourWit h j (sigFourU * sigFourU)) = liftC 2 := by
  rw [sqRelWord_clrFourWit]; decide

/-- The `v`-letter is the square of the `u`-letter, so it leaves the same even residue. -/
theorem sqRelWord_clrFourWit_V : sqRelWord (clrFourWit h j sigFourV) = liftC 2 := by
  rw [sqRelWord_clrFourWit]; decide

/-- The even residue dies by one explicit achievable `γ₄`-move on the `x₁` slot. -/
theorem sqRelWord_clrFourWit_Usq_complete :
    sqRelWord (sigLift j (clrFourWit h j (sigFourU * sigFourU)) 1 1 (liftC 7) 1 1) = 1 := by
  rw [sqRelWord_sigLift SqU5.isGaThree_one SqU5.isGaFour_one (liftC_isGaFour 7)
    SqU5.isGaThree_one SqU5.isGaThree_one, sqRelWord_clrFourWit_Usq, liftC_mul_liftC]
  refine Eq.trans (congrArg liftC ?_) liftC_zero
  simp only [clrFourWit, mirWit_one, mirWit_handleU, mirWit_handleV, SqU5.one_h, SqU5.one_i,
    SqU5.one_j, sigFourU, sigFourV, sigFourX]
  decide

/-- ⭐ **Every class-`≤ 3` verdict is the same for all three dressings** at every handle count:
the committed class-three machinery cannot see the separation. -/
theorem clrFourWit_class_three_blind :
    (SqU5.toU4L (sqRelWord (clrFourWit h j 1)) = 1 ∧
      SqU5.toU4R (sqRelWord (clrFourWit h j 1)) = 1) ∧
    (SqU5.toU4L (sqRelWord (clrFourWit h j (sigFourU * sigFourU))) = 1 ∧
      SqU5.toU4R (sqRelWord (clrFourWit h j (sigFourU * sigFourU))) = 1) ∧
    (SqU5.toU4L (sqRelWord (clrFourWit h j sigFourU)) = 1 ∧
      SqU5.toU4R (sqRelWord (clrFourWit h j sigFourU)) = 1) := by
  rw [sqRelWord_clrFourWit_triv, sqRelWord_clrFourWit_Usq, sqRelWord_clrFourWit_U]
  refine ⟨⟨map_one _, map_one _⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

@[simp] theorem clrFourMark_zero : clrFourMark h j 0 = sigFourMark gr3R := by
  rw [clrFourMark, mirWit_zero, mul_one]

@[simp] theorem clrFourMark_one : clrFourMark h j 1 = sigFourX := by
  rw [clrFourMark, mirWit_one]

@[simp] theorem clrFourMark_two : clrFourMark h j 2 = sigFourY := by
  rw [clrFourMark, mirWit_two]

@[simp] theorem clrFourMark_handleU : clrFourMark h j (sqHandleIdxU j) = sigFourU := by
  rw [clrFourMark, mirWit_handleU]

@[simp] theorem clrFourMark_handleV : clrFourMark h j (sqHandleIdxV j) = sigFourV := by
  rw [clrFourMark, mirWit_handleV]

theorem clrFourMark_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    clrFourMark h j (sqHandleIdxU j') = 1 := by rw [clrFourMark, mirWit_handleU_ne hne]

theorem clrFourMark_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    clrFourMark h j (sqHandleIdxV j') = 1 := by rw [clrFourMark, mirWit_handleV_ne hne]

variable (h j) in
/-- ⭐ **`GradedFourHom.sigFourHom` at every handle count.** -/
noncomputable def clrFourHom : ContinuousMonoidHom (DSq h : Type) (SqU5 gr3R) :=
  sqU5Hom gr3R_card h (clrFourMark h j) sqRelWord_clrFourMark

@[simp] theorem clrFourHom_gen (i : Fin (sqRank h)) :
    clrFourHom h j (sqGen h i) = clrFourMark h j i := sqU5Hom_gen _ _ _ i

@[simp] theorem clrFourHom_sigma : clrFourHom h j (dsqSigma h) = sigFourMark gr3R := by
  rw [dsqSigma, clrFourHom_gen, clrFourMark_zero]

@[simp] theorem clrFourHom_x0 : clrFourHom h j (dsqX0 h) = sigFourX := by
  rw [dsqX0, clrFourHom_gen, clrFourMark_one]

@[simp] theorem clrFourHom_x1 : clrFourHom h j (dsqX1 h) = sigFourY := by
  rw [dsqX1, clrFourHom_gen, clrFourMark_two]

@[simp] theorem clrFourHom_handleU :
    clrFourHom h j (sqGen h (sqHandleIdxU j)) = sigFourU := by
  rw [clrFourHom_gen, clrFourMark_handleU]

@[simp] theorem clrFourHom_handleV :
    clrFourHom h j (sqGen h (sqHandleIdxV j)) = sigFourV := by
  rw [clrFourHom_gen, clrFourMark_handleV]

theorem clrFourHom_handle_ne {j' : Fin h} (hne : j' ≠ j) :
    clrFourHom h j (sqGen h (sqHandleIdxU j')) = 1 ∧
      clrFourHom h j (sqGen h (sqHandleIdxV j')) = 1 :=
  ⟨by rw [clrFourHom_gen, clrFourMark_handleU_ne hne],
    by rw [clrFourHom_gen, clrFourMark_handleV_ne hne]⟩

/-- The pivot anchor at every handle count, through the even-obstruction power lemma. -/
theorem clrFourHom_sqPivot :
    clrFourHom h j (sqPivot h) = rowPivotVal (gr3Pi sqPivotExp) :=
  mirHom_sqPivot clrFourHom_sigma clrFourHom_x0

/-- The cleared row leaves the `u`-letter `ν'`-trivial. -/
theorem nuSelClr_handleU : nuSel h j 0 0 (sqGen h (sqHandleIdxU j)) = 1 := by
  rw [nuSel_handleU, ofAdd_zero]

/-- …and the `v`-letter likewise. -/
theorem nuSelClr_handleV : nuSel h j 0 0 (sqGen h (sqHandleIdxV j)) = 1 := by
  rw [nuSel_handleV, ofAdd_zero]

theorem clrFourHom_sqEichU : clrFourHom h j (sqEichU h (nuSel h j 0 0) j) = sigFourU := by
  rw [sqEichU_of_cleared nuSelClr_handleU, clrFourHom_handleU]

theorem clrFourHom_sqEichV : clrFourHom h j (sqEichV h (nuSel h j 0 0) j) = sigFourV := by
  rw [sqEichV_of_cleared nuSelClr_handleV, clrFourHom_handleV]

/-- The `b`-column of the cleared-row hom is the selected row, at every handle count:
`GradedFourHom.sigFourHom_b` widened. -/
theorem clrFourHom_b (x : (DSq h : Type)) :
    (clrFourHom h j x).b = gr3Pi (toAdd (nuSel h j 0 0 x)) :=
  mirHom_b (by rw [clrFourHom_sigma]; rfl) (by rw [clrFourHom_x0]; rfl)
    (by rw [clrFourHom_x1]; rfl) (by rw [clrFourHom_handleU, map_zero]; rfl)
    (by rw [clrFourHom_handleV, map_zero]; rfl)
    (fun j' hj' => by rw [(clrFourHom_handle_ne hj').1, (clrFourHom_handle_ne hj').2]; exact
      ⟨rfl, rfl⟩) x

theorem clrFourHom_b_eq_zero {g : (DSq h : Type)} (hg : nuSel h j 0 0 g = 1) :
    (clrFourHom h j g).b = 0 := by
  rw [clrFourHom_b, hg, toAdd_one, map_zero]

theorem clrFourHom_sqArbFrame (g : (DSq h : Type)) :
    (fun i => clrFourHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h g) i))
      = clrFourWit h j (clrFourHom h j g) := by
  rw [clrFourWit]
  exact mirHom_sqArbFrame clrFourHom_sigma clrFourHom_x0 clrFourHom_x1 clrFourHom_sqEichU
    clrFourHom_sqEichV (fun j' hj' => clrFourHom_handle_ne hj') g

/-! ### Soundness at the cleared row

The point's lattice parameters are the **committed** `(1, 2, 0, 0, 0, 0, 1, 0)` and do not
depend on `h`, so `GradedSigmaFour.sigFourWit_lamThree_even` is reused verbatim; and every slot
of the marking satisfies `GradedFourRow`'s three invariants, so the model-independent `γ₂`-level
bound applies too. -/

/-- The committed achievable lattice is even at the cleared point, at every `(P, Q, R)`. -/
theorem clrFourWit_lamThree_even {P Q R : gr3R} {z : SqU5 gr3R}
    (hz : selLamThree 1 2 0 0 0 0 1 0 P Q R z) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) :=
  sigFourWit_lamThree_even hz

/-- The `σ`-`x₁` commutator at the cleared point: `(h, i) = (0, 4)`, i.e. `R = 4`. -/
theorem clrFourWit_commP_zero_two :
    commP (clrFourMark h j 0) (clrFourMark h j 2) = (⟨0, 0, 0, 0, 0, 0, 0, 0, 4, 0⟩ :
      SqU5 gr3R) := by
  rw [clrFourMark_zero, clrFourMark_two]; decide

/-- The `x₁`-`U` commutator is central. -/
theorem clrFourWit_commP_two_handleU :
    commP (clrFourMark h j 2) (clrFourMark h j (sqHandleIdxU j))
      = (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 6⟩ : SqU5 gr3R) := by
  rw [clrFourMark_two, clrFourMark_handleU]; decide

/-- …and so is the `x₁`-`V` commutator. -/
theorem clrFourWit_commP_two_handleV :
    commP (clrFourMark h j 2) (clrFourMark h j (sqHandleIdxV j))
      = (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 4⟩ : SqU5 gr3R) := by
  rw [clrFourMark_two, clrFourMark_handleV]
  decide

/-- The extended lattice of `GradedGammaTwo` is even at the cleared point too, at the point's
own extended-lattice data `(P, Q, R) = (0, 0, 4)`. -/
theorem clrFourWit_lamThreePlus_even {z : SqU5 gr3R}
    (hz : selLamThreePlus 1 2 0 0 0 0 1 0 0 0 4 z) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) := by
  obtain ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, t₁, t₂, t₃, hh, hi⟩ := hz
  exact ⟨⟨0, by rw [hh]; ring⟩,
    ⟨4 * r₅ + 4 * r₆ + 2 * t₁, by rw [hi]; ring⟩⟩

/-- Every slot of the cleared marking satisfies `GradedFourRow`'s three invariants. -/
theorem clrFourMark_le_rowFrameSub :
    Subgroup.closure (Set.range (clrFourMark h j)) ≤ rowFrameSub gr3R := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [clrFourMark_zero]
    exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩
  · rw [clrFourMark_one]
    exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩
  · rw [clrFourMark_two]
    exact ⟨rfl, rfl, 2, by show (4 : gr3R) = 2 * 2; decide⟩
  · by_cases hjj : j' = j
    · subst hjj
      rw [clrFourMark_handleU]
      exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩
    · rw [clrFourMark_handleU_ne hjj]
      exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩
  · by_cases hjj : j' = j
    · subst hjj
      rw [clrFourMark_handleV]
      exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩
    · rw [clrFourMark_handleV_ne hjj]
      exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩

/-- ⭐ **The model-independent soundness at the cleared point**, at every handle count. -/
theorem clrFour_commutator_le :
    rowGaTwoOf (Subgroup.closure (Set.range (clrFourMark h j))) ≤ rowGaTwoSub gr3R := by
  rw [rowGaTwoOf, Subgroup.closure_le]
  rintro z ⟨p, hp, q, hq, rfl⟩
  exact commP_mem_rowGaTwoSub (clrFourMark_le_rowFrameSub hp) (clrFourMark_le_rowFrameSub hq)

theorem clrFour_gaTwo_even {z : SqU5 gr3R}
    (hz : z ∈ rowGaTwoOf (Subgroup.closure (Set.range (clrFourMark h j)))) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) := by
  obtain ⟨-, -, -, -, -, -, hh, hi⟩ := clrFour_commutator_le hz
  exact ⟨⟨0, by rw [hh]; ring⟩, hi⟩

/-- **The image of the cleared-row hom is the closure of the marking.** -/
theorem clrFourHom_mem_closure (x : (DSq h : Type)) :
    clrFourHom h j x ∈ Subgroup.closure (Set.range (clrFourMark h j)) := by
  have hgen : Subgroup.closure (Set.range (sqGen h))
      ≤ Subgroup.comap (clrFourHom h j).toMonoidHom
        (Subgroup.closure (Set.range (clrFourMark h j))) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    show clrFourHom h j (sqGen h i) ∈ Subgroup.closure (Set.range (clrFourMark h j))
    rw [clrFourHom_gen]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hclosed : IsClosed ((Subgroup.comap (clrFourHom h j).toMonoidHom
      (Subgroup.closure (Set.range (clrFourMark h j))) :
        Subgroup (DSq h : Type)) : Set (DSq h : Type)) := by
    have hpre : ((Subgroup.comap (clrFourHom h j).toMonoidHom
        (Subgroup.closure (Set.range (clrFourMark h j))) :
          Subgroup (DSq h : Type)) : Set (DSq h : Type))
        = clrFourHom h j ⁻¹' ((Subgroup.closure (Set.range (clrFourMark h j))) :
            Set (SqU5 gr3R)) := rfl
    rw [hpre]
    exact (isClosed_discrete _).preimage (clrFourHom h j).continuous_toFun
  have hle := Subgroup.topologicalClosure_minimal _ hgen hclosed
  rw [dsq_topGen h] at hle
  exact hle (Subgroup.mem_top x)

/-! ### The forcing at the cleared row -/

/-- ⭐ **The sigma-slot forcing at the cleared point**, against the committed lattice. -/
theorem clrFourWit_sigma_forced {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hvb : v.b = 0) (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : selLamThree 1 2 0 0 0 0 1 0 P Q R z₃)
    (l₄ : selLamThree 1 2 0 0 0 0 1 0 P Q R z₄)
    (hkill : sqRelWord (sigLift j (clrFourWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  mirWit_sigma_forced commP_clrFour hvb hz₀ hw₁ hw₂ hz₃ hz₄
    (clrFourWit_lamThree_even l₃) (clrFourWit_lamThree_even l₄) hkill

/-- ⭐ **…and with no lattice model at all.** -/
theorem clrFourWit_sigma_forced_gaTwo {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R}
    (hvb : v.b = 0) (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (clrFourMark h j))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (clrFourMark h j))))
    (hkill : sqRelWord (sigLift j (clrFourWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  mirWit_sigma_forced commP_clrFour hvb hz₀ hw₁ hw₂ hz₃ hz₄
    (clrFour_gaTwo_even l₃) (clrFour_gaTwo_even l₄) hkill

theorem nuLam_clrEichU : nuLam h (sqEichU h (nuSel h j 0 0) j) = 1 :=
  Multiplicative.toAdd.injective (by rw [toAdd_nuLam_sqEichU, toAdd_one])

theorem nu_clrEichU : nuSel h j 0 0 (sqEichU h (nuSel h j 0 0) j) = 1 :=
  Multiplicative.toAdd.injective (by rw [toAdd_nu_sqEichU nuSel_sigma nuSel_x0, toAdd_one])

theorem nuLam_clrEichU_sq :
    nuLam h (sqEichU h (nuSel h j 0 0) j * sqEichU h (nuSel h j 0 0) j) = 1 := by
  rw [map_mul, nuLam_clrEichU, one_mul]

theorem nu_clrEichU_sq :
    nuSel h j 0 0 (sqEichU h (nuSel h j 0 0) j * sqEichU h (nuSel h j 0 0) j) = 1 := by
  rw [map_mul, nu_clrEichU, one_mul]

/-- ⭐ **The forcing is not vacuous at the cleared row**, at every handle count. -/
theorem clrFour_forcing_nonvacuous :
    nuLam h (sqEichU h (nuSel h j 0 0) j) = 1 ∧
      nuSel h j 0 0 (sqEichU h (nuSel h j 0 0) j) = 1 ∧
      selPar (clrFourHom h j (sqEichU h (nuSel h j 0 0) j)).a = 1 :=
  ⟨nuLam_clrEichU, nu_clrEichU, by rw [clrFourHom_sqEichU]; exact clrFourU_chiA⟩

theorem nuLam_sigArbDress_clrU (i : Fin (sqRank h)) :
    nuLam h (sigArbDress h (sqEichU h (nuSel h j 0 0) j) i) = 1 :=
  nuLam_sigArbDress nuLam_clrEichU i

theorem nu_sigArbDress_clrU (i : Fin (sqRank h)) :
    nuSel h j 0 0 (sigArbDress h (sqEichU h (nuSel h j 0 0) j) i) = 1 :=
  nu_sigArbDress nu_clrEichU i

theorem nuLam_sigArbDress_clrUsq (i : Fin (sqRank h)) :
    nuLam h (sigArbDress h
      (sqEichU h (nuSel h j 0 0) j * sqEichU h (nuSel h j 0 0) j) i) = 1 :=
  nuLam_sigArbDress nuLam_clrEichU_sq i

theorem nu_sigArbDress_clrUsq (i : Fin (sqRank h)) :
    nuSel h j 0 0 (sigArbDress h
      (sqEichU h (nuSel h j 0 0) j * sqEichU h (nuSel h j 0 0) j) i) = 1 :=
  nu_sigArbDress nu_clrEichU_sq i

theorem sqRelWord_clrFrame_sigTriv :
    sqRelWord (fun i =>
      clrFourHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h 1) i)) = 1 := by
  rw [clrFourHom_sqArbFrame, map_one]
  exact sqRelWord_clrFourWit_triv

theorem sqRelWord_clrFrame_sigUsq :
    sqRelWord (fun i => clrFourHom h j (sqArbFrame h (nuSel h j 0 0) j
      (sigArbDress h (sqEichU h (nuSel h j 0 0) j * sqEichU h (nuSel h j 0 0) j)) i))
      = liftC 2 := by
  rw [clrFourHom_sqArbFrame, map_mul, clrFourHom_sqEichU]
  exact sqRelWord_clrFourWit_Usq

theorem sqRelWord_clrFrame_sigU :
    sqRelWord (fun i => clrFourHom h j (sqArbFrame h (nuSel h j 0 0) j
      (sigArbDress h (sqEichU h (nuSel h j 0 0) j)) i)) = liftC 1 := by
  rw [clrFourHom_sqArbFrame, clrFourHom_sqEichU]
  exact sqRelWord_clrFourWit_U

theorem sqRelWord_clrFrame_sigUsq_complete :
    sqRelWord (sigLift j (fun i => clrFourHom h j (sqArbFrame h (nuSel h j 0 0) j
      (sigArbDress h (sqEichU h (nuSel h j 0 0) j * sqEichU h (nuSel h j 0 0) j)) i))
      1 1 (liftC 7) 1 1) = 1 := by
  rw [clrFourHom_sqArbFrame, map_mul, clrFourHom_sqEichU]
  exact sqRelWord_clrFourWit_Usq_complete

/-- ⭐ **The odd dressing survives nothing** at the cleared row, at every handle count. -/
theorem sqRelWord_clrFrame_sigU_ne_one {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : selLamThree 1 2 0 0 0 0 1 0 P Q R z₃)
    (l₄ : selLamThree 1 2 0 0 0 0 1 0 P Q R z₄) :
    sqRelWord (sigLift j (fun i => clrFourHom h j (sqArbFrame h (nuSel h j 0 0) j
      (sigArbDress h (sqEichU h (nuSel h j 0 0) j)) i)) z₀ w₁ w₂ z₃ z₄) ≠ 1 := by
  rw [clrFourHom_sqArbFrame, clrFourHom_sqEichU]
  intro hc
  have hpar := clrFourWit_sigma_forced (v := sigFourU) (by decide) hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄ hc
  rw [show (sigFourU.a : gr3R) = 1 from rfl] at hpar
  exact absurd hpar (by decide)

/-- ⭐ …and nothing at the `γ₂` level either. -/
theorem sqRelWord_clrFrame_sigU_ne_one_gaTwo {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (clrFourMark h j))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (clrFourMark h j)))) :
    sqRelWord (sigLift j (fun i => clrFourHom h j (sqArbFrame h (nuSel h j 0 0) j
      (sigArbDress h (sqEichU h (nuSel h j 0 0) j)) i)) z₀ w₁ w₂ z₃ z₄) ≠ 1 := by
  rw [clrFourHom_sqArbFrame, clrFourHom_sqEichU]
  intro hc
  have hpar := clrFourWit_sigma_forced_gaTwo (v := sigFourU) (by decide) hz₀ hw₁ hw₂ hz₃ hz₄
    l₃ l₄ hc
  rw [show (sigFourU.a : gr3R) = 1 from rfl] at hpar
  exact absurd hpar (by decide)

/-- ⭐ **The class-four selection bit on `sqArbFrame` at the cleared row, at every handle
count.** -/
theorem sqArbFrame_sigma_bit_cleared {g : (DSq h : Type)} (hg : nuSel h j 0 0 g = 1) :
    selPar ((sqRelWord fun i =>
        clrFourHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h g) i)).j)
      = selPar (clrFourHom h j g).a := by
  rw [clrFourHom_sqArbFrame g, clrFourWit]
  exact mirWit_bit commP_clrFour (clrFourHom_b_eq_zero hg)

/-- ⭐ **`GradedFourHom.sqArbFrame_sigma_forced_nuSel` at every handle count**, and with the two
handle-clearing hypotheses discharged from the row rather than carried. -/
theorem sqArbFrame_sigma_forced_cleared {g : (DSq h : Type)} (hg : nuSel h j 0 0 g = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : selLamThree 1 2 0 0 0 0 1 0 P Q R z₃)
    (l₄ : selLamThree 1 2 0 0 0 0 1 0 P Q R z₄)
    (hkill : sqRelWord (sigLift j
      (fun i => clrFourHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (clrFourHom h j g).a = 0 := by
  rw [clrFourHom_sqArbFrame g] at hkill
  exact clrFourWit_sigma_forced (clrFourHom_b_eq_zero hg) hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄ hkill

/-- ⭐ **…and at the `γ₂` level.** -/
theorem sqArbFrame_sigma_forced_cleared_gaTwo {g : (DSq h : Type)} (hg : nuSel h j 0 0 g = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (clrFourMark h j))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (clrFourMark h j))))
    (hkill : sqRelWord (sigLift j
      (fun i => clrFourHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (clrFourHom h j g).a = 0 := by
  rw [clrFourHom_sqArbFrame g] at hkill
  exact clrFourWit_sigma_forced_gaTwo (clrFourHom_b_eq_zero hg) hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄ hkill

/-- ⭐ **The escape separates the sigma dressings at the cleared row**, at every handle count,
with the legality of both dressings exhibited. -/
theorem clrFour_escape_separates :
    ((∀ i, nuLam h (sigArbDress h
        (sqEichU h (nuSel h j 0 0) j * sqEichU h (nuSel h j 0 0) j) i) = 1) ∧
      ∀ i, nuSel h j 0 0 (sigArbDress h
        (sqEichU h (nuSel h j 0 0) j * sqEichU h (nuSel h j 0 0) j) i) = 1) ∧
    ((∀ i, nuLam h (sigArbDress h (sqEichU h (nuSel h j 0 0) j) i) = 1) ∧
      ∀ i, nuSel h j 0 0 (sigArbDress h (sqEichU h (nuSel h j 0 0) j) i) = 1) ∧
    sqRelWord (fun i => clrFourHom h j (sqArbFrame h (nuSel h j 0 0) j
      (sigArbDress h (sqEichU h (nuSel h j 0 0) j * sqEichU h (nuSel h j 0 0) j)) i))
      = liftC 2 ∧
    sqRelWord (fun i => clrFourHom h j (sqArbFrame h (nuSel h j 0 0) j
      (sigArbDress h (sqEichU h (nuSel h j 0 0) j)) i)) = liftC 1 :=
  ⟨⟨nuLam_sigArbDress_clrUsq, nu_sigArbDress_clrUsq⟩,
    ⟨nuLam_sigArbDress_clrU, nu_sigArbDress_clrU⟩,
    sqRelWord_clrFrame_sigUsq, sqRelWord_clrFrame_sigU⟩

/-- ⭐ Every class-`≤ 3` verdict on the frame is the same for all three dressings. -/
theorem clrFrame_class_three_blind :
    (SqU5.toU4L (sqRelWord fun i => clrFourHom h j (sqArbFrame h (nuSel h j 0 0) j
        (sigArbDress h 1) i)) = 1 ∧
      SqU5.toU4R (sqRelWord fun i => clrFourHom h j (sqArbFrame h (nuSel h j 0 0) j
        (sigArbDress h 1) i)) = 1) ∧
    (SqU5.toU4L (sqRelWord fun i => clrFourHom h j (sqArbFrame h (nuSel h j 0 0) j
        (sigArbDress h (sqEichU h (nuSel h j 0 0) j
          * sqEichU h (nuSel h j 0 0) j)) i)) = 1 ∧
      SqU5.toU4R (sqRelWord fun i => clrFourHom h j (sqArbFrame h (nuSel h j 0 0) j
        (sigArbDress h (sqEichU h (nuSel h j 0 0) j
          * sqEichU h (nuSel h j 0 0) j)) i)) = 1) ∧
    (SqU5.toU4L (sqRelWord fun i => clrFourHom h j (sqArbFrame h (nuSel h j 0 0) j
        (sigArbDress h (sqEichU h (nuSel h j 0 0) j)) i)) = 1 ∧
      SqU5.toU4R (sqRelWord fun i => clrFourHom h j (sqArbFrame h (nuSel h j 0 0) j
        (sigArbDress h (sqEichU h (nuSel h j 0 0) j)) i)) = 1) := by
  rw [sqRelWord_clrFrame_sigTriv, sqRelWord_clrFrame_sigUsq, sqRelWord_clrFrame_sigU]
  refine ⟨⟨map_one _, map_one _⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

end ClearedRow

/-! ## 2 ⭐⭐ The handle block is invisible to the sigma forcing

Every class-four point the campaign has built has a **dead** handle block, and §4 below builds a
live one.  Before that, the reason the distinction cannot matter to the forcing.

The sigma slot is not in the handle block: `sqRelWord m = sqWord (m 0) (m 1) (m 2) · handleWord`
and the handle word does not see slot `0`.  So the handle word's contribution to the relator is
**the same before and after any sigma dressing**, and the class-four selection bit - which is a
*difference* between two dressings - cannot depend on it.  This is a statement about arbitrary
markings over an arbitrary commutative ring, and it is what turns "no live handle block has been
produced" into "a live handle block cannot be seen at class four". -/

section HandleBlind

variable {R : Type} [CommRing R] {h : ℕ}

/-- ⭐⭐ **Handle-blindness of the four top dressing responses.**  Two markings with the same
core slots `(σ, x₀, x₁)` and **arbitrary, possibly different** handle blocks respond to a
sigma-slot dressing by exactly the same amount in each of the four top rows.  Nothing is assumed
about either handle block: neither may be trivial, they need not be equal, and the markings need
not kill the relator. -/
theorem sqRelWord_sigFourDress_handle_blind {m m' : Fin (sqRank h) → SqU5 R} {v : SqU5 R}
    (hm0 : m 0 = sigFourMark R) (hm0' : m' 0 = sigFourMark R)
    (h1 : m' 1 = m 1) (h2 : m' 2 = m 2)
    (hxb : (m 1).b = 0) (hyb : (m 2).b = 0) (hvb : v.b = 0) :
    (sqRelWord (sigFourDress m v)).g - (sqRelWord m).g
        = (sqRelWord (sigFourDress m' v)).g - (sqRelWord m').g ∧
      (sqRelWord (sigFourDress m v)).h - (sqRelWord m).h
        = (sqRelWord (sigFourDress m' v)).h - (sqRelWord m').h ∧
      (sqRelWord (sigFourDress m v)).i - (sqRelWord m).i
        = (sqRelWord (sigFourDress m' v)).i - (sqRelWord m').i ∧
      (sqRelWord (sigFourDress m v)).j - (sqRelWord m).j
        = (sqRelWord (sigFourDress m' v)).j - (sqRelWord m').j := by
  obtain ⟨g₁, h₁, i₁, j₁⟩ := sqRelWord_sigFourDress (m := m) (v := v) hm0 hxb hyb hvb
  obtain ⟨g₂, h₂, i₂, j₂⟩ := sqRelWord_sigFourDress (m := m') (v := v) hm0'
    (by rw [h1]; exact hxb) (by rw [h2]; exact hyb) hvb
  rw [g₁, g₂, h₁, h₂, i₁, i₂, j₁, j₂, h1, h2]
  exact ⟨by ring, by ring, by ring, by ring⟩

variable {j : Fin h} {s x y U V v : SqU5 R}

/-- **How the handle block enters the class-four row, and the only way it can**: through its own
class-four coordinate and through its class-three and third class-two coordinates paired against
the core word's two outermost class-`≤ 2` coordinates.  Each of the three factors it meets is
fixed by the core slots, and `sqWord_sigFour_low` says a sigma dressing moves neither of the two
core coefficients, which is the computation behind the blindness above. -/
theorem sqRelWord_mirTuple_j :
    (sqRelWord (mirTuple R h j s x y U V)).j
      = (sqWord s x y).j + ((commP U V).j + (sqWord s x y).a * (commP U V).i
          + (sqWord s x y).e * (commP U V).g) := by
  rw [sqRelWord_mirTuple, SqU5.mul_j, SqU5.commP_d, mul_zero]
  ring

/-- The one-handle-live tuple with the sigma slot dressed really is the sigma-dressing of the
undressed one. -/
theorem mirTuple_eq_dress :
    mirTuple R h j (sigFourMark R * v) x y U V
      = sigFourDress (mirTuple R h j (sigFourMark R) x y U V) v := by
  funext i
  by_cases h0 : (i : ℕ) = 0
  · have hi : i = 0 := Fin.val_injective (by rw [h0, sqVal_zero])
    subst hi
    rw [sigFourDress_zero, mirTuple_zero, mirTuple_zero]
  · rw [sigFourDress_ne h0]
    simp only [mirTuple, if_neg h0]

/-- ⭐⭐ **The positive form: the class-four response is a functional of the core slots alone.**
Dressing the sigma slot of a one-handle-live marking moves the class-four row by
`sigFourRead v x y`, in which **the handle letters do not occur**.  At every handle count, for
every pair of handle letters, live block or dead. -/
theorem sqRelWord_mirTuple_dress_response (hxb : x.b = 0) (hyb : y.b = 0) (hvb : v.b = 0) :
    (sqRelWord (mirTuple R h j (sigFourMark R * v) x y U V)).j
      = (sqRelWord (mirTuple R h j (sigFourMark R) x y U V)).j + sigFourRead v x y := by
  obtain ⟨-, -, -, hjj⟩ := sqRelWord_sigFourDress
    (m := mirTuple R h j (sigFourMark R) x y U V) (v := v) mirTuple_zero
    (by rw [mirTuple_one]; exact hxb) (by rw [mirTuple_two]; exact hyb) hvb
  rw [mirTuple_eq_dress, hjj, mirTuple_one, mirTuple_two]

/-- …and the same for the third class-two row and the two class-three rows. -/
theorem sqRelWord_mirTuple_dress_response_low (hxb : x.b = 0) (hyb : y.b = 0) (hvb : v.b = 0) :
    (sqRelWord (mirTuple R h j (sigFourMark R * v) x y U V)).g
        = (sqRelWord (mirTuple R h j (sigFourMark R) x y U V)).g + sigFourG v x ∧
      (sqRelWord (mirTuple R h j (sigFourMark R * v) x y U V)).h
        = (sqRelWord (mirTuple R h j (sigFourMark R) x y U V)).h + sigFourH v x ∧
      (sqRelWord (mirTuple R h j (sigFourMark R * v) x y U V)).i
        = (sqRelWord (mirTuple R h j (sigFourMark R) x y U V)).i + sigFourI v x := by
  obtain ⟨hg, hh, hi, -⟩ := sqRelWord_sigFourDress
    (m := mirTuple R h j (sigFourMark R) x y U V) (v := v) mirTuple_zero
    (by rw [mirTuple_one]; exact hxb) (by rw [mirTuple_two]; exact hyb) hvb
  rw [mirTuple_eq_dress, hg, hh, hi, mirTuple_one]
  exact ⟨rfl, rfl, rfl⟩

end HandleBlind

section BlindBit

variable {h : ℕ} {j : Fin h} {y U V v : SqU5 gr3R}

/-- ⭐⭐ **The class-four selection bit is handle-blind.**  At the committed `x₀`-gauge and any
`ν'`-trivial `x₁`-slot with vanishing outer columns, dressing the sigma slot of a one-handle-live
marking moves the parity of the class-four row by exactly the dressing's own
`chi_a`-character - **whatever the handle letters are, and whether or not their commutator is
trivial**.  `GradedFourMirror.mirWit_bit` is the special case in which the marking kills the
relator and the block is dead. -/
theorem mirTuple_sigma_bit (hya : y.a = 0) (hyb : y.b = 0) (hyc : y.c = 0) (hyd : y.d = 0)
    (hvb : v.b = 0) :
    selPar ((sqRelWord (mirTuple gr3R h j (sigFourMark gr3R * v) sigFourX y U V)).j)
      = selPar ((sqRelWord (mirTuple gr3R h j (sigFourMark gr3R) sigFourX y U V)).j)
        + selPar v.a := by
  rw [sqRelWord_mirTuple_dress_response (by decide) hyb hvb, selPar_add,
    sigFourRead_gauge_par (v := v) (x := sigFourX) (y := y) (xa := 1) (xc := 0) (xd := 0)
      (xe := 0) (xf := 0) (ya := 0) (yc := 0) (yd := 0)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hya]; ring) (by rw [hyc]; ring) (by rw [hyd]; ring),
    show (sigFourX.g + sigFourX.i : gr3R) = 1 by decide,
    show (sigFourX.h : gr3R) = 0 by decide, show (sigFourX.g : gr3R) = 0 by decide,
    mul_one, mul_zero, mul_zero, selPar_zero, add_zero, add_zero]

/-- The bit at a marking that kills the relator: the handle block has disappeared entirely. -/
theorem mirTuple_sigma_bit_of_rel (hya : y.a = 0) (hyb : y.b = 0) (hyc : y.c = 0)
    (hyd : y.d = 0) (hvb : v.b = 0)
    (hrel : sqRelWord (mirTuple gr3R h j (sigFourMark gr3R) sigFourX y U V) = 1) :
    selPar ((sqRelWord (mirTuple gr3R h j (sigFourMark gr3R * v) sigFourX y U V)).j)
      = selPar v.a := by
  rw [mirTuple_sigma_bit hya hyb hyc hyd hvb, hrel, SqU5.one_j, selPar_zero, zero_add]

end BlindBit

/-! ## 3 ⭐⭐ The gauge parity theorem, and why a live block is automatically sound

A live handle block is a nontrivial element of `γ₂` of the image, so under the achievability
convention it is itself a legal handle dressing.  If its class-three coordinates could be odd,
the increment lemma would fail and the point would be unsound.  They cannot be, and the reason
is the gauge: below class four **every** row of the core word is even. -/

section GaugeParity

variable {R : Type} [CommRing R] {x y : SqU5 R} {xa xc xd xe xf xg ya yc yd : R}

set_option maxHeartbeats 1000000 in
/-- ⭐⭐ **The gauge is even below class four.**  On the class-two-forced `x₀`-gauge - the
`x₀`-slot's columns `a, c, d, e, f` and its third class-two coordinate `g` even with vanishing
`b`-column, the `x₁`-slot's columns `a, c, d` even with vanishing `b`-column - every one of the
nine lower rows of `sqWord (sigFourMark R) x y` is **even**, and the `b`-row vanishes outright.
Only the class-four row can be odd, which is exactly the separation `GradedSigmaFour` is about.

The `x₀`-slot's `g`-column is the hypothesis the `i`-row needs and no lower one does; it is one
of `GradedFourRow.rowFrameSub`'s three invariants, so every marking of this family supplies it.
Closed forms derived symbolically over `ℤ` in `scripts/w57_cleared/derive_cleared.py`. -/
theorem sqWord_sigFourMark_gauge_even
    (hxa : x.a = 2 * xa) (hxb : x.b = 0) (hxc : x.c = 2 * xc) (hxd : x.d = 2 * xd)
    (hxe : x.e = 2 * xe) (hxf : x.f = 2 * xf) (hxg : x.g = 2 * xg)
    (hya : y.a = 2 * ya) (hyb : y.b = 0) (hyc : y.c = 2 * yc) (hyd : y.d = 2 * yd) :
    (∃ k : R, (sqWord (sigFourMark R) x y).a = 2 * k) ∧
      (sqWord (sigFourMark R) x y).b = 0 ∧
      (∃ k : R, (sqWord (sigFourMark R) x y).c = 2 * k) ∧
      (∃ k : R, (sqWord (sigFourMark R) x y).d = 2 * k) ∧
      (∃ k : R, (sqWord (sigFourMark R) x y).e = 2 * k) ∧
      (∃ k : R, (sqWord (sigFourMark R) x y).f = 2 * k) ∧
      (∃ k : R, (sqWord (sigFourMark R) x y).g = 2 * k) ∧
      (∃ k : R, (sqWord (sigFourMark R) x y).h = 2 * k) ∧
      (∃ k : R, (sqWord (sigFourMark R) x y).i = 2 * k) := by
  refine ⟨⟨-4 * xa + 2 * ya, ?_⟩, ?_, ⟨-4 * xc + 2 * yc, ?_⟩, ⟨-4 * xd + 2 * yd, ?_⟩,
    ⟨-xa - 4 * xe + y.e, ?_⟩, ⟨xc - 4 * xf + y.f, ?_⟩,
    ⟨-4 * xg + y.g + 20 * (xc * xd) - 16 * (xc * yd) + 2 * (yc * yd), ?_⟩,
    ⟨-2 * x.h + y.h + 6 * (xa * xc) + 20 * (xa * xf) - 4 * (xa * yc) - 8 * (xa * y.f)
      + 20 * (xc * xe) - 16 * (xe * yc) - 4 * (ya * yc) + ya * y.f + yc * y.e, ?_⟩,
    ⟨xg - 2 * x.i + y.i - 8 * (xc * xd) + 4 * (xc * yd) + 20 * (xd * xf) - 16 * (xf * yd)
      + 2 * (yc * yd) + yd * y.f, ?_⟩⟩ <;>
  · simp only [sqWord, conjP, commP, pow_succ, pow_zero, one_mul, sigFourMark,
      SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d, SqU5.mul_e, SqU5.mul_f, SqU5.mul_g,
      SqU5.mul_h, SqU5.mul_i, SqU5.inv_a, SqU5.inv_b, SqU5.inv_c, SqU5.inv_d, SqU5.inv_e,
      SqU5.inv_f, SqU5.inv_g, SqU5.inv_h, SqU5.inv_i, hxa, hxb, hxc, hxd, hxe, hxf, hxg,
      hya, hyb, hyc, hyd]
    ring

variable {h : ℕ} {j : Fin h} {U V : SqU5 R}

/-- ⭐⭐ **A live handle block is automatically sound.**  At **any** one-handle-live marking over
the gauge whose relator vanishes, at **any** handle count, the handle commutator has **both**
class-three coordinates even - exactly the hypothesis `GradedFourMirror.mirWit_increment_even`
consumes.  So the relator's own rows protect the forcing: the block cannot be live in a way that
enlarges the achievable increment set beyond the even one.

Nothing here says the block is trivial.  §4 exhibits one that is not. -/
theorem commP_gaThree_even_of_relator
    (hxa : x.a = 2 * xa) (hxb : x.b = 0) (hxc : x.c = 2 * xc) (hxd : x.d = 2 * xd)
    (hxe : x.e = 2 * xe) (hxf : x.f = 2 * xf) (hxg : x.g = 2 * xg)
    (hya : y.a = 2 * ya) (hyb : y.b = 0) (hyc : y.c = 2 * yc) (hyd : y.d = 2 * yd)
    (hrel : sqRelWord (mirTuple R h j (sigFourMark R) x y U V) = 1) :
    (∃ k : R, (commP U V).h = 2 * k) ∧ (∃ k : R, (commP U V).i = 2 * k) := by
  obtain ⟨⟨ka, hka⟩, hb, -, -, -, -, -, ⟨kh, hkh⟩, ⟨ki, hki⟩⟩ :=
    sqWord_sigFourMark_gauge_even hxa hxb hxc hxd hxe hxf hxg hya hyb hyc hyd
  rw [sqRelWord_mirTuple] at hrel
  have hh : (sqWord (sigFourMark R) x y).h + (commP U V).h
      + (sqWord (sigFourMark R) x y).a * (commP U V).f
      + (sqWord (sigFourMark R) x y).e * (commP U V).c = 0 := by
    rw [← SqU5.mul_h, hrel, SqU5.one_h]
  have hi : (sqWord (sigFourMark R) x y).i + (commP U V).i
      + (sqWord (sigFourMark R) x y).b * (commP U V).g
      + (sqWord (sigFourMark R) x y).f * (commP U V).d = 0 := by
    rw [← SqU5.mul_i, hrel, SqU5.one_i]
  rw [SqU5.commP_c, mul_zero, add_zero, hka, hkh] at hh
  rw [SqU5.commP_d, mul_zero, add_zero, hb, zero_mul, add_zero, hki] at hi
  exact ⟨⟨-kh - ka * (commP U V).f, by linear_combination hh⟩,
    ⟨-ki, by linear_combination hi⟩⟩

end GaugeParity

/-! ## 4 ⭐⭐ The live-handle-block point

With the committed core slots a live block is impossible: `sqWord sigFourMark sigFourX sigFourY`
is `1`, so the relator of a one-handle-live marking **is** the handle commutator.  Two changes
buy a live block, and they are the smallest available: move the `x₁`-slot's first class-three
coordinate to `3`, which makes the core word the class-three element with `h = 6`, and the
`v`-letter's second class-two coordinate to `2`, which makes the handle commutator the
class-three element with `h = 2`.  The two are inverse, so the relator dies with the block
alive.

The `u`-letter is the committed `sigFourU`, untouched, so the open channel, the two regression
dressings, the selection bit and all three verdicts are the committed ones. -/

section LivePoint

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐ **The live point's `x₁`-slot**: `GradedSigmaFour.sigFourY` with its first class-three
coordinate moved from `0` to `3`.  Its outer columns still vanish, so §2's bit applies. -/
def liveFourY : SqU5 gr3R := ⟨0, 0, 0, 0, 1, 0, 4, 3, 2, 0⟩

/-- The live point's `u`-letter is the committed one. -/
def liveFourU : SqU5 gr3R := ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- ⭐⭐ **The live point's `v`-letter**: the committed `sigFourV` with its second class-two
coordinate moved from `0` to `2`.  This is the one slot that leaves
`GradedFourRow.rowFrameSub`. -/
def liveFourV : SqU5 gr3R := ⟨2, 0, 0, 0, 0, 2, 0, 0, 0, 0⟩

theorem liveFourU_eq : liveFourU = sigFourU := rfl

theorem liveFourY_eq : liveFourY = sigFourY * (⟨0, 0, 0, 0, 0, 0, 0, 3, 0, 0⟩ : SqU5 gr3R) := by
  decide

theorem liveFourV_eq : liveFourV = (⟨0, 0, 0, 0, 0, 2, 0, 0, 0, 0⟩ : SqU5 gr3R) * sigFourV := by
  decide

/-- ⭐⭐ **THE LIVE HANDLE BLOCK.**  The handle commutator is the class-three element with first
coordinate `2` - an element of order **four**, not merely nonzero.  Every class-four point built
before this one has it trivial. -/
theorem commP_liveFour :
    commP liveFourU liveFourV = (⟨0, 0, 0, 0, 0, 0, 0, 2, 0, 0⟩ : SqU5 gr3R) := by decide

/-- ⭐⭐ …and it is genuinely nontrivial. -/
theorem commP_liveFour_ne_one : commP liveFourU liveFourV ≠ 1 := by decide

/-- The core word at the live point is the **inverse** class-three element: this is what the
block cancels against. -/
theorem sqWord_liveFour :
    sqWord (sigFourMark gr3R) sigFourX liveFourY
      = (⟨0, 0, 0, 0, 0, 0, 0, 6, 0, 0⟩ : SqU5 gr3R) := by decide

/-- The committed point has no room for a live block: its core word is trivial, so its relator
**is** the handle commutator. -/
theorem sqWord_clrFour : sqWord (sigFourMark gr3R) sigFourX sigFourY = 1 := by decide

variable (h j) in
/-- ⭐⭐ **The live point's marking at every handle count.** -/
def liveFourMark : Fin (sqRank h) → SqU5 gr3R :=
  mirTuple gr3R h j (sigFourMark gr3R) sigFourX liveFourY liveFourU liveFourV

variable (h j) in
/-- The live point's witness, with the sigma slot dressed by `v`. -/
def liveFourWit (v : SqU5 gr3R) : Fin (sqRank h) → SqU5 gr3R :=
  mirTuple gr3R h j (sigFourMark gr3R * v) sigFourX liveFourY liveFourU liveFourV

theorem liveFourWit_one : liveFourWit h j 1 = liveFourMark h j := by
  rw [liveFourWit, liveFourMark, mul_one]

theorem sqRelWord_liveFourWit (v : SqU5 gr3R) :
    sqRelWord (liveFourWit h j v)
      = sqWord (sigFourMark gr3R * v) sigFourX liveFourY * commP liveFourU liveFourV :=
  sqRelWord_mirTuple

/-- ⭐⭐ **The ten-row solve at the live point, at every handle count**: all ten rows of the
relator vanish **with the handle block alive**.  The core word and the block are inverse
class-three elements. -/
theorem sqRelWord_liveFourMark : sqRelWord (liveFourMark h j) = 1 := by
  rw [liveFourMark, sqRelWord_mirTuple, sqWord_liveFour, commP_liveFour]
  decide

theorem sqRelWord_liveFourWit_triv : sqRelWord (liveFourWit h j 1) = 1 := by
  rw [liveFourWit_one]; exact sqRelWord_liveFourMark

/-- The `u`-letter has odd `chi_a`-character, as at the committed point. -/
theorem liveFourU_chiA : selPar liveFourU.a = 1 := by decide

/-- ⭐⭐ Dressing the sigma slot by the `u`-letter leaves the **odd** residue `1`, exactly as at
the committed point: the live block has changed no verdict. -/
theorem sqRelWord_liveFourWit_U : sqRelWord (liveFourWit h j liveFourU) = liftC 1 := by
  rw [sqRelWord_liveFourWit]; decide

/-- …and by its square the **even** residue `2`. -/
theorem sqRelWord_liveFourWit_Usq :
    sqRelWord (liveFourWit h j (liveFourU * liveFourU)) = liftC 2 := by
  rw [sqRelWord_liveFourWit]; decide

/-- The even residue dies by one explicit achievable `γ₄`-move on the `x₁` slot. -/
theorem sqRelWord_liveFourWit_Usq_complete :
    sqRelWord (sigLift j (liveFourWit h j (liveFourU * liveFourU)) 1 1 (liftC 7) 1 1) = 1 := by
  rw [sqRelWord_sigLift SqU5.isGaThree_one SqU5.isGaFour_one (liftC_isGaFour 7)
    SqU5.isGaThree_one SqU5.isGaThree_one, sqRelWord_liveFourWit_Usq, liftC_mul_liftC]
  refine Eq.trans (congrArg liftC ?_) liftC_zero
  simp only [liveFourWit, mirTuple_one, mirTuple_handleU, mirTuple_handleV, SqU5.one_h,
    SqU5.one_i, SqU5.one_j, liveFourU, liveFourV, sigFourX]
  decide

/-- ⭐⭐ **Every class-`≤ 3` verdict is the same for all three dressings at the live point too.**
The live block is invisible to the committed class-three machinery as well. -/
theorem liveFourWit_class_three_blind :
    (SqU5.toU4L (sqRelWord (liveFourWit h j 1)) = 1 ∧
      SqU5.toU4R (sqRelWord (liveFourWit h j 1)) = 1) ∧
    (SqU5.toU4L (sqRelWord (liveFourWit h j (liveFourU * liveFourU))) = 1 ∧
      SqU5.toU4R (sqRelWord (liveFourWit h j (liveFourU * liveFourU))) = 1) ∧
    (SqU5.toU4L (sqRelWord (liveFourWit h j liveFourU)) = 1 ∧
      SqU5.toU4R (sqRelWord (liveFourWit h j liveFourU)) = 1) := by
  rw [sqRelWord_liveFourWit_triv, sqRelWord_liveFourWit_Usq, sqRelWord_liveFourWit_U]
  refine ⟨⟨map_one _, map_one _⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

/-- ⭐⭐ **The live block is automatically sound at this point**, through §3's general theorem
rather than by computation: the gauge and the relator do it. -/
theorem commP_liveFour_even :
    (∃ k : gr3R, (commP liveFourU liveFourV).h = 2 * k) ∧
      (∃ k : gr3R, (commP liveFourU liveFourV).i = 2 * k) :=
  commP_gaThree_even_of_relator (h := 1) (j := (0 : Fin 1)) (xa := 1) (xc := 0) (xd := 0)
    (xe := 0) (xf := 0) (xg := 0) (ya := 0) (yc := 0) (yd := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) sqRelWord_liveFourMark

end LivePoint

/-! ## 5 The live point as a continuous homomorphism -/

section LiveHom

variable {h : ℕ} {j : Fin h}

@[simp] theorem liveFourMark_zero : liveFourMark h j 0 = sigFourMark gr3R := mirTuple_zero

@[simp] theorem liveFourMark_one : liveFourMark h j 1 = sigFourX := mirTuple_one

@[simp] theorem liveFourMark_two : liveFourMark h j 2 = liveFourY := mirTuple_two

@[simp] theorem liveFourMark_handleU : liveFourMark h j (sqHandleIdxU j) = liveFourU :=
  mirTuple_handleU

@[simp] theorem liveFourMark_handleV : liveFourMark h j (sqHandleIdxV j) = liveFourV :=
  mirTuple_handleV

theorem liveFourMark_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    liveFourMark h j (sqHandleIdxU j') = 1 := mirTuple_handleU_ne hne

theorem liveFourMark_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    liveFourMark h j (sqHandleIdxV j') = 1 := mirTuple_handleV_ne hne

variable (h j) in
/-- ⭐⭐ **The live point's test hom**, at every handle count. -/
noncomputable def liveFourHom : ContinuousMonoidHom (DSq h : Type) (SqU5 gr3R) :=
  sqU5Hom gr3R_card h (liveFourMark h j) sqRelWord_liveFourMark

@[simp] theorem liveFourHom_gen (i : Fin (sqRank h)) :
    liveFourHom h j (sqGen h i) = liveFourMark h j i := sqU5Hom_gen _ _ _ i

@[simp] theorem liveFourHom_sigma : liveFourHom h j (dsqSigma h) = sigFourMark gr3R := by
  rw [dsqSigma, liveFourHom_gen, liveFourMark_zero]

@[simp] theorem liveFourHom_x0 : liveFourHom h j (dsqX0 h) = sigFourX := by
  rw [dsqX0, liveFourHom_gen, liveFourMark_one]

@[simp] theorem liveFourHom_x1 : liveFourHom h j (dsqX1 h) = liveFourY := by
  rw [dsqX1, liveFourHom_gen, liveFourMark_two]

@[simp] theorem liveFourHom_handleU :
    liveFourHom h j (sqGen h (sqHandleIdxU j)) = liveFourU := by
  rw [liveFourHom_gen, liveFourMark_handleU]

@[simp] theorem liveFourHom_handleV :
    liveFourHom h j (sqGen h (sqHandleIdxV j)) = liveFourV := by
  rw [liveFourHom_gen, liveFourMark_handleV]

theorem liveFourHom_handle_ne {j' : Fin h} (hne : j' ≠ j) :
    liveFourHom h j (sqGen h (sqHandleIdxU j')) = 1 ∧
      liveFourHom h j (sqGen h (sqHandleIdxV j')) = 1 :=
  ⟨by rw [liveFourHom_gen, liveFourMark_handleU_ne hne],
    by rw [liveFourHom_gen, liveFourMark_handleV_ne hne]⟩

theorem liveFourHom_sqPivot :
    liveFourHom h j (sqPivot h) = rowPivotVal (gr3Pi sqPivotExp) :=
  mirHom_sqPivot liveFourHom_sigma liveFourHom_x0

/-- ⭐⭐ **The handle commutator is live in the IMAGE**, not merely in a tuple: it is the
commutator of the images of the two handle generators under an honest continuous homomorphism on
`D_sq h`. -/
theorem liveFourHom_commP_ne_one :
    commP (liveFourHom h j (sqGen h (sqHandleIdxU j)))
      (liveFourHom h j (sqGen h (sqHandleIdxV j))) ≠ 1 := by
  rw [liveFourHom_handleU, liveFourHom_handleV]
  exact commP_liveFour_ne_one

theorem liveFourHom_sqEichU : liveFourHom h j (sqEichU h (nuSel h j 0 0) j) = liveFourU := by
  rw [sqEichU_of_cleared nuSelClr_handleU, liveFourHom_handleU]

theorem liveFourHom_sqEichV : liveFourHom h j (sqEichV h (nuSel h j 0 0) j) = liveFourV := by
  rw [sqEichV_of_cleared nuSelClr_handleV, liveFourHom_handleV]

theorem liveFourHom_b (x : (DSq h : Type)) :
    (liveFourHom h j x).b = gr3Pi (toAdd (nuSel h j 0 0 x)) :=
  mirHom_b (by rw [liveFourHom_sigma]; rfl) (by rw [liveFourHom_x0]; rfl)
    (by rw [liveFourHom_x1]; rfl) (by rw [liveFourHom_handleU, map_zero]; rfl)
    (by rw [liveFourHom_handleV, map_zero]; rfl)
    (fun j' hj' => by rw [(liveFourHom_handle_ne hj').1, (liveFourHom_handle_ne hj').2]; exact
      ⟨rfl, rfl⟩) x

theorem liveFourHom_b_eq_zero {g : (DSq h : Type)} (hg : nuSel h j 0 0 g = 1) :
    (liveFourHom h j g).b = 0 := by
  rw [liveFourHom_b, hg, toAdd_one, map_zero]

/-- The frame identification at the live point: `GradedFourMirror.mirHom_sqArbFrame` is stated
for the mirror witness shape, so it is reproved here for the free `x₁`-slot. -/
theorem liveFourHom_sqArbFrame (g : (DSq h : Type)) :
    (fun i => liveFourHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h g) i))
      = liveFourWit h j (liveFourHom h j g) := by
  funext i
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [sqArbFrame, sqArbBase_zero, sigArbDress_zero, map_mul, liveFourHom_sigma, liveFourWit,
      mirTuple_zero]
  · rw [sqArbFrame, sqArbBase_one, sigArbDress_ne (by rw [sqVal_one]; omega), mul_one,
      liveFourHom_x0, liveFourWit, mirTuple_one]
  · rw [sqArbFrame, sqArbBase_two, sigArbDress_ne (by rw [sqVal_two]; omega), mul_one,
      liveFourHom_x1, liveFourWit, mirTuple_two]
  · by_cases hjj : j' = j
    · subst hjj
      rw [sqArbFrame, sqArbBase_handleU, sigArbDress_ne (by rw [sqHandleIdxU_val]; omega),
        mul_one, liveFourHom_sqEichU, liveFourWit, mirTuple_handleU]
    · rw [sqArbFrame, sqArbBase_handleU_ne hjj,
        sigArbDress_ne (by rw [sqHandleIdxU_val]; omega), mul_one,
        (liveFourHom_handle_ne hjj).1, liveFourWit, mirTuple_handleU_ne hjj]
  · by_cases hjj : j' = j
    · subst hjj
      rw [sqArbFrame, sqArbBase_handleV, sigArbDress_ne (by rw [sqHandleIdxV_val]; omega),
        mul_one, liveFourHom_sqEichV, liveFourWit, mirTuple_handleV]
    · rw [sqArbFrame, sqArbBase_handleV_ne hjj,
        sigArbDress_ne (by rw [sqHandleIdxV_val]; omega), mul_one,
        (liveFourHom_handle_ne hjj).2, liveFourWit, mirTuple_handleV_ne hjj]

end LiveHom

/-! ## 6 ⭐⭐ Soundness at the live point: the widened invariants

The live point's `v`-letter has second class-two coordinate `2`, so the wave-55 invariant
"`f`-column vanishes" is **false** at this marking and `GradedFourRow.rowFrameSub` cannot be
used.  The repair is exactly one notch: the `f`-column need only be **even**.  That is still a
subgroup, and its commutators still have both class-three coordinates even - which is all the
increment lemma asks.  What is lost is the sharper "first class-three coordinate **vanishes**",
and that loss is real rather than an artefact: the census in `scripts/w57_cleared/` finds the
value `2` realised among the honest commutators of the image.

CORRECTED BY W60-MIGRATE: "which is all the increment lemma asks" overstates.  The increment
lemma below asks for both class-three coordinates because it is stated for an arbitrary marking;
the increment itself asks only that the move PAIR evenly against the handle slots' outer abelian
columns (`GradedFrameNecessity.gaugeX_increment_even_of_pair`), and at this point the
`v`-covector vanishes, so the first class-three coordinate is never read
(`GradedFourSharp.liveFour_frameOrth_iff`).  The widening to an even `f`-column is still
necessary for a live block, and `commP_mem_liveGaTwoSub` is still true; only the reading "and
that is exactly what the forcing needs" is wrong. -/

section LiveSoundness

variable {R : Type} [CommRing R]

/-- ⭐⭐ **Inside `GradedFourRow.rowFrameSub` a `ν'`-trivial handle block is CENTRAL.**  With
vanishing third abelian column, vanishing second class-two coordinate and vanishing `b`-columns -
the wave-55 invariants plus the cleared row's own `ν'`-triviality - the handle commutator has
**every** coordinate below the class-four one equal to zero.  So a block that is live in a
coordinate the increment actually reads *must* leave the wave-55 invariants, which is why the
live point's `v`-letter does and why the widening below is a necessity rather than a
convenience. -/
theorem commP_central_of_rowFrameSub {p q : SqU5 R} (hp : p ∈ rowFrameSub R)
    (hq : q ∈ rowFrameSub R) (hpb : p.b = 0) (hqb : q.b = 0) :
    commP p q = liftC (commP p q).j := by
  obtain ⟨hpc, hpf, -⟩ := hp
  obtain ⟨hqc, hqf, -⟩ := hq
  ext <;>
    simp only [liftC, SqU5.commP_a, SqU5.commP_b, SqU5.commP_c, SqU5.commP_d, SqU5.commP_e,
      SqU5.commP_f, SqU5.commP_g, SqU5.commP_h, SqU5.commP_i, SqU5.u5Comm3L, SqU5.u5Comm3R,
      hpc, hqc, hpf, hqf, hpb, hqb] <;>
    ring

variable (R) in
/-- ⭐⭐ **The widened frame invariants**: vanishing third abelian column, **even** second
class-two coordinate, even third one.  `GradedFourRow.rowFrameSub` is the sub-case with the
second coordinate vanishing outright. -/
def liveFrameSub : Subgroup (SqU5 R) where
  carrier := {p | p.c = 0 ∧ (∃ k : R, p.f = 2 * k) ∧ ∃ k : R, p.g = 2 * k}
  mul_mem' := fun {p q} hp hq => by
    obtain ⟨hpc, ⟨mp, hpf⟩, kp, hpg⟩ := hp
    obtain ⟨hqc, ⟨mq, hqf⟩, kq, hqg⟩ := hq
    exact ⟨by rw [SqU5.mul_c, hpc, hqc]; ring,
      ⟨mp + mq, by rw [SqU5.mul_f, hpf, hqf, hqc]; ring⟩,
      kp + kq, by rw [SqU5.mul_g, hpg, hqg, hpc]; ring⟩
  one_mem' := ⟨rfl, ⟨0, by rw [SqU5.one_f]; ring⟩, 0, by rw [SqU5.one_g]; ring⟩
  inv_mem' := fun {p} hp => by
    obtain ⟨hpc, ⟨mp, hpf⟩, kp, hpg⟩ := hp
    exact ⟨by rw [SqU5.inv_c, hpc]; ring,
      ⟨-mp, by rw [SqU5.inv_f, hpc, hpf]; ring⟩,
      -kp, by rw [SqU5.inv_g, hpc, hpg]; ring⟩

theorem mem_liveFrameSub {p : SqU5 R} :
    p ∈ liveFrameSub R ↔ p.c = 0 ∧ (∃ k : R, p.f = 2 * k) ∧ ∃ k : R, p.g = 2 * k := Iff.rfl

/-- `GradedFourRow.rowFrameSub` sits inside the widened one. -/
theorem rowFrameSub_le_liveFrameSub : rowFrameSub R ≤ liveFrameSub R := by
  rintro p ⟨hpc, hpf, k, hpg⟩
  exact ⟨hpc, ⟨0, by rw [hpf]; ring⟩, k, hpg⟩

variable (R) in
/-- The subgroup where every `γ₂`-level commutator of the live frame lands: as
`GradedFourRow.rowGaTwoSub` but with the first class-three coordinate only **even**. -/
def liveGaTwoSub : Subgroup (SqU5 R) where
  carrier := {p | p.a = 0 ∧ p.b = 0 ∧ p.c = 0 ∧ p.d = 0 ∧ p.f = 0 ∧ p.g = 0 ∧
    (∃ k : R, p.h = 2 * k) ∧ ∃ k : R, p.i = 2 * k}
  mul_mem' := fun {p q} hp hq => by
    obtain ⟨hpa, hpb, hpc, hpd, hpf, hpg, ⟨np, hph⟩, kp, hpi⟩ := hp
    obtain ⟨hqa, hqb, hqc, hqd, hqf, hqg, ⟨nq, hqh⟩, kq, hqi⟩ := hq
    exact ⟨by rw [SqU5.mul_a, hpa, hqa]; ring, by rw [SqU5.mul_b, hpb, hqb]; ring,
      by rw [SqU5.mul_c, hpc, hqc]; ring, by rw [SqU5.mul_d, hpd, hqd]; ring,
      by rw [SqU5.mul_f, hpf, hqf, hqc]; ring, by rw [SqU5.mul_g, hpg, hqg, hpc]; ring,
      ⟨np + nq, by rw [SqU5.mul_h, hph, hqh, hqf, hqc, hpa]; ring⟩,
      kp + kq, by rw [SqU5.mul_i, hpi, hqi, hpb, hpf]; ring⟩
  one_mem' := ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨0, by rw [SqU5.one_h]; ring⟩,
    0, by rw [SqU5.one_i]; ring⟩
  inv_mem' := fun {p} hp => by
    obtain ⟨hpa, hpb, hpc, hpd, hpf, hpg, ⟨np, hph⟩, kp, hpi⟩ := hp
    exact ⟨by rw [SqU5.inv_a, hpa]; ring, by rw [SqU5.inv_b, hpb]; ring,
      by rw [SqU5.inv_c, hpc]; ring, by rw [SqU5.inv_d, hpd]; ring,
      by rw [SqU5.inv_f, hpc, hpf]; ring, by rw [SqU5.inv_g, hpc, hpg]; ring,
      ⟨-np, by rw [SqU5.inv_h, hpa, hpc, hph]; ring⟩,
      -kp, by rw [SqU5.inv_i, hpb, hpd, hpi]; ring⟩

theorem mem_liveGaTwoSub {p : SqU5 R} :
    p ∈ liveGaTwoSub R ↔ p.a = 0 ∧ p.b = 0 ∧ p.c = 0 ∧ p.d = 0 ∧ p.f = 0 ∧ p.g = 0 ∧
      (∃ k : R, p.h = 2 * k) ∧ ∃ k : R, p.i = 2 * k := Iff.rfl

/-- ⭐⭐ **The one algebraic fact behind the widened soundness**: a commutator of two elements
with vanishing `c`-column and **even** second and third class-two coordinates has **even**
class-three coordinates.  `GradedFourRow.commP_mem_rowGaTwoSub` is the sharper conclusion from
the sharper hypothesis, and it is unavailable at a live point. -/
theorem commP_mem_liveGaTwoSub {p q : SqU5 R} (hp : p ∈ liveFrameSub R)
    (hq : q ∈ liveFrameSub R) : commP p q ∈ liveGaTwoSub R := by
  obtain ⟨hpc, ⟨mp, hpf⟩, kp, hpg⟩ := hp
  obtain ⟨hqc, ⟨mq, hqf⟩, kq, hqg⟩ := hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨p.a * mq - mp * q.a, ?_⟩,
    ⟨p.b * kq - kp * q.b + mp * q.d - p.d * mq, ?_⟩⟩ <;>
    simp only [SqU5.commP_a, SqU5.commP_b, SqU5.commP_c, SqU5.commP_d, SqU5.commP_f,
      SqU5.commP_g, SqU5.commP_h, SqU5.commP_i, SqU5.u5Comm3L, SqU5.u5Comm3R,
      hpc, hqc, hpf, hqf, hpg, hqg] <;>
    ring

variable {h : ℕ} {j : Fin h}

/-- Every slot of the live marking satisfies the widened invariants. -/
theorem liveFourMark_le_liveFrameSub :
    Subgroup.closure (Set.range (liveFourMark h j)) ≤ liveFrameSub gr3R := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [liveFourMark_zero]
    exact ⟨rfl, ⟨0, by show (0 : gr3R) = 2 * 0; ring⟩, 0, by show (0 : gr3R) = 2 * 0; ring⟩
  · rw [liveFourMark_one]
    exact ⟨rfl, ⟨0, by show (0 : gr3R) = 2 * 0; ring⟩, 0, by show (0 : gr3R) = 2 * 0; ring⟩
  · rw [liveFourMark_two]
    exact ⟨rfl, ⟨0, by show (0 : gr3R) = 2 * 0; ring⟩, 2, by show (4 : gr3R) = 2 * 2; decide⟩
  · by_cases hjj : j' = j
    · subst hjj
      rw [liveFourMark_handleU]
      exact ⟨rfl, ⟨0, by show (0 : gr3R) = 2 * 0; ring⟩, 0, by show (0 : gr3R) = 2 * 0; ring⟩
    · rw [liveFourMark_handleU_ne hjj]
      exact ⟨rfl, ⟨0, by show (0 : gr3R) = 2 * 0; ring⟩, 0, by show (0 : gr3R) = 2 * 0; ring⟩
  · by_cases hjj : j' = j
    · subst hjj
      rw [liveFourMark_handleV]
      exact ⟨rfl, ⟨1, by show (2 : gr3R) = 2 * 1; decide⟩, 0,
        by show (0 : gr3R) = 2 * 0; ring⟩
    · rw [liveFourMark_handleV_ne hjj]
      exact ⟨rfl, ⟨0, by show (0 : gr3R) = 2 * 0; ring⟩, 0, by show (0 : gr3R) = 2 * 0; ring⟩

/-- ⭐⭐ **The model-independent soundness at the live point.**  The whole commutator subgroup of
the marking's image - the object the achievability convention lets a `γ₂`-level dressing be drawn
from, the live handle block included - is **even** in both class-three coordinates. -/
theorem liveFour_commutator_le :
    rowGaTwoOf (Subgroup.closure (Set.range (liveFourMark h j))) ≤ liveGaTwoSub gr3R := by
  rw [rowGaTwoOf, Subgroup.closure_le]
  rintro z ⟨p, hp, q, hq, rfl⟩
  exact commP_mem_liveGaTwoSub (liveFourMark_le_liveFrameSub hp)
    (liveFourMark_le_liveFrameSub hq)

/-- …in the form the increment lemma consumes. -/
theorem liveFour_gaTwo_even {z : SqU5 gr3R}
    (hz : z ∈ rowGaTwoOf (Subgroup.closure (Set.range (liveFourMark h j)))) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) := by
  obtain ⟨-, -, -, -, -, -, hh, hi⟩ := liveFour_commutator_le hz
  exact ⟨hh, hi⟩

/-- ⭐⭐ **The sharper wave-55 bound is FALSE at the live point**: the handle block itself is a
commutator of two elements of the image whose first class-three coordinate does not vanish.  So
"even" is the sharpest bound this point admits, and using it is not a weakening of convenience.
-/
theorem liveFour_not_rowGaTwoSub :
    ¬ rowGaTwoOf (Subgroup.closure (Set.range (liveFourMark h j))) ≤ rowGaTwoSub gr3R := by
  intro hle
  have hmem : commP (liveFourMark h j (sqHandleIdxU j)) (liveFourMark h j (sqHandleIdxV j))
      ∈ rowGaTwoOf (Subgroup.closure (Set.range (liveFourMark h j))) :=
    Subgroup.subset_closure ⟨_, Subgroup.subset_closure ⟨_, rfl⟩, _,
      Subgroup.subset_closure ⟨_, rfl⟩, rfl⟩
  obtain ⟨-, -, -, -, -, -, hh, -⟩ := hle hmem
  rw [liveFourMark_handleU, liveFourMark_handleV, commP_liveFour] at hh
  exact absurd hh (by decide)

/-- **The image of the live hom is the closure of the marking.** -/
theorem liveFourHom_mem_closure (x : (DSq h : Type)) :
    liveFourHom h j x ∈ Subgroup.closure (Set.range (liveFourMark h j)) := by
  have hgen : Subgroup.closure (Set.range (sqGen h))
      ≤ Subgroup.comap (liveFourHom h j).toMonoidHom
        (Subgroup.closure (Set.range (liveFourMark h j))) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    show liveFourHom h j (sqGen h i) ∈ Subgroup.closure (Set.range (liveFourMark h j))
    rw [liveFourHom_gen]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hclosed : IsClosed ((Subgroup.comap (liveFourHom h j).toMonoidHom
      (Subgroup.closure (Set.range (liveFourMark h j))) :
        Subgroup (DSq h : Type)) : Set (DSq h : Type)) := by
    have hpre : ((Subgroup.comap (liveFourHom h j).toMonoidHom
        (Subgroup.closure (Set.range (liveFourMark h j))) :
          Subgroup (DSq h : Type)) : Set (DSq h : Type))
        = liveFourHom h j ⁻¹' ((Subgroup.closure (Set.range (liveFourMark h j))) :
            Set (SqU5 gr3R)) := rfl
    rw [hpre]
    exact (isClosed_discrete _).preimage (liveFourHom h j).continuous_toFun
  have hle := Subgroup.topologicalClosure_minimal _ hgen hclosed
  rw [dsq_topGen h] at hle
  exact hle (Subgroup.mem_top x)

/-- The committed achievable lattice is even at the live point too: its parameters
`(A, B, C, D, E, F, T, S) = (1, 2, 0, 0, 0, 0, 1, 0)` are the committed cleared-row ones, because
the live perturbation touches no column the lattice reads. -/
theorem liveFourWit_lamThree_even {P Q R : gr3R} {z : SqU5 gr3R}
    (hz : selLamThree 1 2 0 0 0 0 1 0 P Q R z) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) :=
  sigFourWit_lamThree_even hz

/-- The three `x₁`-slot commutators at the live point are the committed ones: the perturbation
touches none of them, so the extended-lattice data `(P, Q, R) = (0, 0, 4)` is unchanged and
`clrFourWit_lamThreePlus_even` covers the live point too. -/
theorem liveFourWit_commP_data :
    commP (sigFourMark gr3R) liveFourY = (⟨0, 0, 0, 0, 0, 0, 0, 0, 4, 0⟩ : SqU5 gr3R) ∧
      commP liveFourY liveFourU = (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 6⟩ : SqU5 gr3R) ∧
      commP liveFourY liveFourV = (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 4⟩ : SqU5 gr3R) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end LiveSoundness

/-! ## 7 ⭐⭐ The sigma forcing at the live point

The forcing runs unchanged, and §2 says why it must: the bit does not see the block.  What has to
be redone is the increment, because `GradedFourMirror.mirWit_increment_even` is stated at the
committed `x₁`-slot; the increment does not read that slot at all, so the proof is the mirror's
verbatim. -/

section LiveForcing

variable {h : ℕ} {j : Fin h}

/-- The five-slot increment at the live point is even as soon as both handle dressings are.  The
`x₀`-slot's columns `(a, d) = (2, 0)` and the `u`-letter's `(a, d) = (1, 0)` are the committed
ones, so this is `GradedFourMirror.mirWit_increment_even` at the live letters. -/
theorem liveFourWit_increment_even {v z₀ z₃ z₄ w₁ w₂ : SqU5 gr3R}
    (h₃ : (∃ a : gr3R, z₃.h = 2 * a) ∧ (∃ b : gr3R, z₃.i = 2 * b))
    (h₄ : (∃ a : gr3R, z₄.h = 2 * a) ∧ (∃ b : gr3R, z₄.i = 2 * b)) :
    ∃ k : gr3R, (z₀.h * (liveFourWit h j v 1).d - z₀.i * (liveFourWit h j v 1).a)
        + (-4 * w₁.j + 2 * w₂.j)
        + ((z₃.h * (liveFourWit h j v (sqHandleIdxV j)).d
            - z₃.i * (liveFourWit h j v (sqHandleIdxV j)).a)
          + ((liveFourWit h j v (sqHandleIdxU j)).a * z₄.i
            - (liveFourWit h j v (sqHandleIdxU j)).d * z₄.h)) = 2 * k := by
  obtain ⟨⟨a₃, ha₃⟩, b₃, hb₃⟩ := h₃
  obtain ⟨⟨a₄, ha₄⟩, b₄, hb₄⟩ := h₄
  refine ⟨-z₀.i - 2 * w₁.j + w₂.j - b₃ * 2 + b₄, ?_⟩
  rw [liveFourWit, mirTuple_one, mirTuple_handleU, mirTuple_handleV, ha₃, hb₃, ha₄, hb₄]
  simp only [sigFourX, liveFourU, liveFourV]
  ring

/-- ⭐⭐ **The sigma forcing at the live point.**  A sigma dressing whose frame is killed by a
five-slot class-four refinement whose two handle moves are even in both class-three coordinates
has an **even** `chi_a`-character - with the handle block alive throughout. -/
theorem liveFourWit_sigma_forced {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (h₃ : (∃ a : gr3R, z₃.h = 2 * a) ∧ (∃ b : gr3R, z₃.i = 2 * b))
    (h₄ : (∃ a : gr3R, z₄.h = 2 * a) ∧ (∃ b : gr3R, z₄.i = 2 * b))
    (hkill : sqRelWord (sigLift j (liveFourWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 := by
  rw [sqRelWord_sigLift hz₀ hw₁ hw₂ hz₃ hz₄] at hkill
  obtain ⟨k, hk⟩ := liveFourWit_increment_even (h := h) (j := j) (v := v) (z₀ := z₀) (w₁ := w₁)
    (w₂ := w₂) h₃ h₄
  rw [hk, mul_liftC_apply] at hkill
  have hjj := congrArg SqU5.j hkill
  simp only [SqU5.one_j] at hjj
  have hp := congrArg selPar hjj
  rw [selPar_add, selPar_two_mul, add_zero, liveFourWit,
    mirTuple_sigma_bit_of_rel (by decide) (by decide) (by decide) (by decide) hvb
      sqRelWord_liveFourMark, selPar_zero] at hp
  exact hp

/-- ⭐⭐ **…against the committed achievable lattice.** -/
theorem liveFourWit_sigma_forced_lam {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hvb : v.b = 0) (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : selLamThree 1 2 0 0 0 0 1 0 P Q R z₃)
    (l₄ : selLamThree 1 2 0 0 0 0 1 0 P Q R z₄)
    (hkill : sqRelWord (sigLift j (liveFourWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  liveFourWit_sigma_forced hvb hz₀ hw₁ hw₂ hz₃ hz₄ (liveFourWit_lamThree_even l₃)
    (liveFourWit_lamThree_even l₄) hkill

/-- ⭐⭐ **…and with no lattice model at all**, over the honest commutator subgroup of the image,
the live block included. -/
theorem liveFourWit_sigma_forced_gaTwo {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (liveFourMark h j))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (liveFourMark h j))))
    (hkill : sqRelWord (sigLift j (liveFourWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  liveFourWit_sigma_forced hvb hz₀ hw₁ hw₂ hz₃ hz₄ (liveFour_gaTwo_even l₃)
    (liveFour_gaTwo_even l₄) hkill

/-- ⭐⭐ **The forcing is not vacuous at the live point**: the `u`-letter is a legal sigma
dressing with an odd `chi_a`-character, exactly as at the committed point. -/
theorem liveFour_forcing_nonvacuous :
    nuLam h (sqEichU h (nuSel h j 0 0) j) = 1 ∧
      nuSel h j 0 0 (sqEichU h (nuSel h j 0 0) j) = 1 ∧
      selPar (liveFourHom h j (sqEichU h (nuSel h j 0 0) j)).a = 1 :=
  ⟨nuLam_clrEichU, nu_clrEichU, by rw [liveFourHom_sqEichU]; exact liveFourU_chiA⟩

theorem sqRelWord_liveFrame_sigTriv :
    sqRelWord (fun i =>
      liveFourHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h 1) i)) = 1 := by
  rw [liveFourHom_sqArbFrame, map_one]
  exact sqRelWord_liveFourWit_triv

theorem sqRelWord_liveFrame_sigUsq :
    sqRelWord (fun i => liveFourHom h j (sqArbFrame h (nuSel h j 0 0) j
      (sigArbDress h (sqEichU h (nuSel h j 0 0) j * sqEichU h (nuSel h j 0 0) j)) i))
      = liftC 2 := by
  rw [liveFourHom_sqArbFrame, map_mul, liveFourHom_sqEichU]
  exact sqRelWord_liveFourWit_Usq

/-- ⭐⭐ **The odd residue at the live point is the committed one.** -/
theorem sqRelWord_liveFrame_sigU :
    sqRelWord (fun i => liveFourHom h j (sqArbFrame h (nuSel h j 0 0) j
      (sigArbDress h (sqEichU h (nuSel h j 0 0) j)) i)) = liftC 1 := by
  rw [liveFourHom_sqArbFrame, liveFourHom_sqEichU]
  exact sqRelWord_liveFourWit_U

theorem sqRelWord_liveFrame_sigUsq_complete :
    sqRelWord (sigLift j (fun i => liveFourHom h j (sqArbFrame h (nuSel h j 0 0) j
      (sigArbDress h (sqEichU h (nuSel h j 0 0) j * sqEichU h (nuSel h j 0 0) j)) i))
      1 1 (liftC 7) 1 1) = 1 := by
  rw [liveFourHom_sqArbFrame, map_mul, liveFourHom_sqEichU]
  exact sqRelWord_liveFourWit_Usq_complete

/-- ⭐⭐ **The odd dressing survives nothing at the live point either**, over the honest
commutator subgroup of the image. -/
theorem sqRelWord_liveFrame_sigU_ne_one_gaTwo {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (liveFourMark h j))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (liveFourMark h j)))) :
    sqRelWord (sigLift j (fun i => liveFourHom h j (sqArbFrame h (nuSel h j 0 0) j
      (sigArbDress h (sqEichU h (nuSel h j 0 0) j)) i)) z₀ w₁ w₂ z₃ z₄) ≠ 1 := by
  rw [liveFourHom_sqArbFrame, liveFourHom_sqEichU]
  intro hc
  have hpar := liveFourWit_sigma_forced_gaTwo (v := liveFourU) (by decide) hz₀ hw₁ hw₂ hz₃ hz₄
    l₃ l₄ hc
  rw [show (liveFourU.a : gr3R) = 1 from rfl] at hpar
  exact absurd hpar (by decide)

/-- ⭐⭐ **The class-four selection bit on `sqArbFrame` at the live point.**  Identical to the
committed one: this is §2's handle-blindness executed on an honest frame. -/
theorem sqArbFrame_sigma_bit_live {g : (DSq h : Type)} (hg : nuSel h j 0 0 g = 1) :
    selPar ((sqRelWord fun i =>
        liveFourHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h g) i)).j)
      = selPar (liveFourHom h j g).a := by
  rw [liveFourHom_sqArbFrame g, liveFourWit]
  exact mirTuple_sigma_bit_of_rel (by decide) (by decide) (by decide) (by decide)
    (liveFourHom_b_eq_zero hg) sqRelWord_liveFourMark

/-- ⭐⭐ **THE HEADLINE AT THE LIVE POINT.**  At the cleared row, at every handle count, at an
honest continuous homomorphism whose handle commutator is **nontrivial in the image**, every
`ν'`-trivial sigma dressing of the arbitrary-dressing frame killed by any achievable five-slot
class-four refinement has an even `chi_a`-character.  The conclusion, the bit and all three
verdicts are the committed ones: the live block changes nothing the forcing can read, and §2
proves that is not an accident of this point. -/
theorem sqArbFrame_sigma_forced_live {g : (DSq h : Type)} (hg : nuSel h j 0 0 g = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (liveFourMark h j))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (liveFourMark h j))))
    (hkill : sqRelWord (sigLift j
      (fun i => liveFourHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (liveFourHom h j g).a = 0 := by
  rw [liveFourHom_sqArbFrame g] at hkill
  exact liveFourWit_sigma_forced_gaTwo (liveFourHom_b_eq_zero hg) hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄
    hkill

/-- ⭐⭐ **…and against the committed achievable lattice.** -/
theorem sqArbFrame_sigma_forced_live_lam {g : (DSq h : Type)} (hg : nuSel h j 0 0 g = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : selLamThree 1 2 0 0 0 0 1 0 P Q R z₃)
    (l₄ : selLamThree 1 2 0 0 0 0 1 0 P Q R z₄)
    (hkill : sqRelWord (sigLift j
      (fun i => liveFourHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (liveFourHom h j g).a = 0 := by
  rw [liveFourHom_sqArbFrame g] at hkill
  exact liveFourWit_sigma_forced_lam (liveFourHom_b_eq_zero hg) hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄ hkill

/-- ⭐⭐ **The escape separates the sigma dressings at a point with a live handle block**, with
the legality of both dressings exhibited and the block's nontriviality recorded alongside. -/
theorem liveFour_escape_separates :
    commP (liveFourHom h j (sqGen h (sqHandleIdxU j)))
        (liveFourHom h j (sqGen h (sqHandleIdxV j))) ≠ 1 ∧
    ((∀ i, nuLam h (sigArbDress h
        (sqEichU h (nuSel h j 0 0) j * sqEichU h (nuSel h j 0 0) j) i) = 1) ∧
      ∀ i, nuSel h j 0 0 (sigArbDress h
        (sqEichU h (nuSel h j 0 0) j * sqEichU h (nuSel h j 0 0) j) i) = 1) ∧
    ((∀ i, nuLam h (sigArbDress h (sqEichU h (nuSel h j 0 0) j) i) = 1) ∧
      ∀ i, nuSel h j 0 0 (sigArbDress h (sqEichU h (nuSel h j 0 0) j) i) = 1) ∧
    sqRelWord (fun i => liveFourHom h j (sqArbFrame h (nuSel h j 0 0) j
      (sigArbDress h (sqEichU h (nuSel h j 0 0) j * sqEichU h (nuSel h j 0 0) j)) i))
      = liftC 2 ∧
    sqRelWord (fun i => liveFourHom h j (sqArbFrame h (nuSel h j 0 0) j
      (sigArbDress h (sqEichU h (nuSel h j 0 0) j)) i)) = liftC 1 :=
  ⟨liveFourHom_commP_ne_one,
    ⟨nuLam_sigArbDress_clrUsq, nu_sigArbDress_clrUsq⟩,
    ⟨nuLam_sigArbDress_clrU, nu_sigArbDress_clrU⟩,
    sqRelWord_liveFrame_sigUsq, sqRelWord_liveFrame_sigU⟩

/-- ⭐ Every class-`≤ 3` verdict on the frame is the same for all three dressings at the live
point too. -/
theorem liveFrame_class_three_blind :
    (SqU5.toU4L (sqRelWord fun i => liveFourHom h j (sqArbFrame h (nuSel h j 0 0) j
        (sigArbDress h 1) i)) = 1 ∧
      SqU5.toU4R (sqRelWord fun i => liveFourHom h j (sqArbFrame h (nuSel h j 0 0) j
        (sigArbDress h 1) i)) = 1) ∧
    (SqU5.toU4L (sqRelWord fun i => liveFourHom h j (sqArbFrame h (nuSel h j 0 0) j
        (sigArbDress h (sqEichU h (nuSel h j 0 0) j
          * sqEichU h (nuSel h j 0 0) j)) i)) = 1 ∧
      SqU5.toU4R (sqRelWord fun i => liveFourHom h j (sqArbFrame h (nuSel h j 0 0) j
        (sigArbDress h (sqEichU h (nuSel h j 0 0) j
          * sqEichU h (nuSel h j 0 0) j)) i)) = 1) ∧
    (SqU5.toU4L (sqRelWord fun i => liveFourHom h j (sqArbFrame h (nuSel h j 0 0) j
        (sigArbDress h (sqEichU h (nuSel h j 0 0) j)) i)) = 1 ∧
      SqU5.toU4R (sqRelWord fun i => liveFourHom h j (sqArbFrame h (nuSel h j 0 0) j
        (sigArbDress h (sqEichU h (nuSel h j 0 0) j)) i)) = 1) := by
  rw [sqRelWord_liveFrame_sigTriv, sqRelWord_liveFrame_sigUsq, sqRelWord_liveFrame_sigU]
  refine ⟨⟨map_one _, map_one _⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

end LiveForcing

/-! ## 8 Axiom pins

Committed prints for every public declaration of this file. -/

section AxiomPins

#print axioms commP_clrFour
#print axioms clrFourMark
#print axioms clrFourWit
#print axioms sqRelWord_clrFourMark
#print axioms sqRelWord_clrFourWit_triv
#print axioms sqRelWord_clrFourWit
#print axioms clrFourU_chiA
#print axioms sqRelWord_clrFourWit_U
#print axioms sqRelWord_clrFourWit_Usq
#print axioms sqRelWord_clrFourWit_V
#print axioms sqRelWord_clrFourWit_Usq_complete
#print axioms clrFourWit_class_three_blind
#print axioms clrFourMark_zero
#print axioms clrFourMark_one
#print axioms clrFourMark_two
#print axioms clrFourMark_handleU
#print axioms clrFourMark_handleV
#print axioms clrFourMark_handleU_ne
#print axioms clrFourMark_handleV_ne
#print axioms clrFourHom
#print axioms clrFourHom_gen
#print axioms clrFourHom_sigma
#print axioms clrFourHom_x0
#print axioms clrFourHom_x1
#print axioms clrFourHom_handleU
#print axioms clrFourHom_handleV
#print axioms clrFourHom_handle_ne
#print axioms clrFourHom_sqPivot
#print axioms nuSelClr_handleU
#print axioms nuSelClr_handleV
#print axioms clrFourHom_sqEichU
#print axioms clrFourHom_sqEichV
#print axioms clrFourHom_b
#print axioms clrFourHom_b_eq_zero
#print axioms clrFourHom_sqArbFrame
#print axioms clrFourWit_lamThree_even
#print axioms clrFourWit_commP_zero_two
#print axioms clrFourWit_commP_two_handleU
#print axioms clrFourWit_commP_two_handleV
#print axioms clrFourWit_lamThreePlus_even
#print axioms clrFourMark_le_rowFrameSub
#print axioms clrFour_commutator_le
#print axioms clrFour_gaTwo_even
#print axioms clrFourHom_mem_closure
#print axioms clrFourWit_sigma_forced
#print axioms clrFourWit_sigma_forced_gaTwo
#print axioms nuLam_clrEichU
#print axioms nu_clrEichU
#print axioms nuLam_clrEichU_sq
#print axioms nu_clrEichU_sq
#print axioms clrFour_forcing_nonvacuous
#print axioms nuLam_sigArbDress_clrU
#print axioms nu_sigArbDress_clrU
#print axioms nuLam_sigArbDress_clrUsq
#print axioms nu_sigArbDress_clrUsq
#print axioms sqRelWord_clrFrame_sigTriv
#print axioms sqRelWord_clrFrame_sigUsq
#print axioms sqRelWord_clrFrame_sigU
#print axioms sqRelWord_clrFrame_sigUsq_complete
#print axioms sqRelWord_clrFrame_sigU_ne_one
#print axioms sqRelWord_clrFrame_sigU_ne_one_gaTwo
#print axioms sqArbFrame_sigma_bit_cleared
#print axioms sqArbFrame_sigma_forced_cleared
#print axioms sqArbFrame_sigma_forced_cleared_gaTwo
#print axioms clrFour_escape_separates
#print axioms clrFrame_class_three_blind
#print axioms sqRelWord_sigFourDress_handle_blind
#print axioms sqRelWord_mirTuple_j
#print axioms mirTuple_eq_dress
#print axioms sqRelWord_mirTuple_dress_response
#print axioms sqRelWord_mirTuple_dress_response_low
#print axioms mirTuple_sigma_bit
#print axioms mirTuple_sigma_bit_of_rel
#print axioms sqWord_sigFourMark_gauge_even
#print axioms commP_gaThree_even_of_relator
#print axioms liveFourY
#print axioms liveFourU
#print axioms liveFourV
#print axioms liveFourU_eq
#print axioms liveFourY_eq
#print axioms liveFourV_eq
#print axioms commP_liveFour
#print axioms commP_liveFour_ne_one
#print axioms sqWord_liveFour
#print axioms sqWord_clrFour
#print axioms liveFourMark
#print axioms liveFourWit
#print axioms liveFourWit_one
#print axioms sqRelWord_liveFourWit
#print axioms sqRelWord_liveFourMark
#print axioms sqRelWord_liveFourWit_triv
#print axioms liveFourU_chiA
#print axioms sqRelWord_liveFourWit_U
#print axioms sqRelWord_liveFourWit_Usq
#print axioms sqRelWord_liveFourWit_Usq_complete
#print axioms liveFourWit_class_three_blind
#print axioms commP_liveFour_even
#print axioms liveFourMark_zero
#print axioms liveFourMark_one
#print axioms liveFourMark_two
#print axioms liveFourMark_handleU
#print axioms liveFourMark_handleV
#print axioms liveFourMark_handleU_ne
#print axioms liveFourMark_handleV_ne
#print axioms liveFourHom
#print axioms liveFourHom_gen
#print axioms liveFourHom_sigma
#print axioms liveFourHom_x0
#print axioms liveFourHom_x1
#print axioms liveFourHom_handleU
#print axioms liveFourHom_handleV
#print axioms liveFourHom_handle_ne
#print axioms liveFourHom_sqPivot
#print axioms liveFourHom_commP_ne_one
#print axioms liveFourHom_sqEichU
#print axioms liveFourHom_sqEichV
#print axioms liveFourHom_b
#print axioms liveFourHom_b_eq_zero
#print axioms liveFourHom_sqArbFrame
#print axioms commP_central_of_rowFrameSub
#print axioms liveFrameSub
#print axioms mem_liveFrameSub
#print axioms rowFrameSub_le_liveFrameSub
#print axioms liveGaTwoSub
#print axioms mem_liveGaTwoSub
#print axioms commP_mem_liveGaTwoSub
#print axioms liveFourMark_le_liveFrameSub
#print axioms liveFour_commutator_le
#print axioms liveFour_gaTwo_even
#print axioms liveFour_not_rowGaTwoSub
#print axioms liveFourHom_mem_closure
#print axioms liveFourWit_lamThree_even
#print axioms liveFourWit_commP_data
#print axioms liveFourWit_increment_even
#print axioms liveFourWit_sigma_forced
#print axioms liveFourWit_sigma_forced_lam
#print axioms liveFourWit_sigma_forced_gaTwo
#print axioms liveFour_forcing_nonvacuous
#print axioms sqRelWord_liveFrame_sigTriv
#print axioms sqRelWord_liveFrame_sigUsq
#print axioms sqRelWord_liveFrame_sigU
#print axioms sqRelWord_liveFrame_sigUsq_complete
#print axioms sqRelWord_liveFrame_sigU_ne_one_gaTwo
#print axioms sqArbFrame_sigma_bit_live
#print axioms sqArbFrame_sigma_forced_live
#print axioms sqArbFrame_sigma_forced_live_lam
#print axioms liveFour_escape_separates
#print axioms liveFrame_class_three_blind

end AxiomPins

end SqCore

end Dyadic

end GQ2

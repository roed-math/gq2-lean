/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFiveStageFour
import GQ2.Dyadic.SqCore.GradedFiveFrame
import GQ2.Dyadic.SqCore.GradedFiveNecessity

/-!
# W61-STAGEHOM: the class-five forcing, unconditional AND at the hom level

Wave 60 produced two class-five results that did not meet.  `GradedFiveStageFour` proved the
exclusion UNCONDITIONALLY, against achievable stage-four refinements, at a new witness point;
`GradedFiveFrame` proved the forcing at the HOM level, on `sqArbFrame` and continuous
homomorphisms, but at wave 59's old point, so it inherited the stage-five scope limit.  This
file is the single statement that is both.

## ⭐⭐⭐ Headline: one statement, unconditional and about homomorphisms

`sqArbFrame_stage_diag_ne_one_cleared`, and in general form
`sqRelWord_stageFrame_diag_ne_one`.  At **every** handle count `h`, **every** handle `j`, and
every continuous `nu'` cleared at the selected handle, at the honest continuous homomorphism
`stageFrameHom h j : D_sq h -> U_6(Z/8)` built by the committed class-five lift from
`GradedFiveStageFour`'s stage-four binder point: **no achievable five-slot STAGE-FOUR
refinement of the image of the `x0`-dressed arbitrary-dressing frame kills the relator image.**
The quantifier is one filtration step wider than `GradedFiveFrame`'s, which is exactly the
scope the committed class-four exclusion enjoys, and the object quantified over is an honest
frame of `D_sq h` rather than a tuple of matrices.

The three verdicts are executed on the frame itself, at every handle count and every handle:

```text
a0 = 1            relator image dies outright       sqRelWord_stageFrame_triv[_gate]
a0 = x0           residue 1, survives every         sqRelWord_stageFrame_diag[_ne_one]
                  achievable stage-four refinement
a0 = x0           both U_5-quotients trivial        stageFrame_class_four_blind
a0 = [x1, u_j]    residue 5, survives them too      sqRelWord_stageFrame_legal[_ne_one]
a0 = [x1, u_j]    ⚠ NOT class-four blind            stageFrame_legal_not_class_four_blind
a0 = [x1,v_j][x1,u_j]⁻¹   central residue 5,        sqRelWord_stageFrame_stageLegal[_ne_one]
                  survives, class-four blind        stageFrame_stageLegal_class_four_blind
```

and the two routes to the first line are made to meet: `sqRelWord_stageFrame_triv` reads it off
the new point's fifteen-row `decide`, `sqRelWord_stageFrame_triv_gate` gets it from the
class-five gate `sqU6Balance_gen` without touching the point at all.

## ⭐ The frame identification SURVIVES the change of point, and the pivot stays mechanical

The change of point is one extra evenness hypothesis on the letters, and the risk was that the
frame would no longer reach the new letters.  It does.  `stageFrameHom_sqArbFrame` goes through
verbatim, because the identification needs only that the handle slots of the marking are the
**raw** generator images, which `stageWit` shares with `fiveWit` by construction; the letters
themselves never enter.  The row type is forced for the same reason as at the old point, and
the certificate is again explicit:

* `stageFrameHom_sqPivot`, the pivot anchor: `Phi(w) = <a = -2c, b = 1, e = -5c>` with
  `c = gr3Pi sqPivotExp`.  It is **still mechanical**: all ten obstructions of
  `SqU6.zpowZtwo_of_flat` vanish at the new point's `x0`-slot `stageX = <a = 2, e = 5>`
  (`stageX_flat`), exactly as they did at `forceX = <a = 2, e = 1>`.  The change of point moves
  the fifth abelian column from `1` to `5`, and `5` is a unit, so the pivot image is
  non-trivial for the same reason.
* `stageFrameHom_sqArbBase_handleU_ne` and `..._handleV_ne`: at any row bumping the selected
  handle by `1` the frame's handle-slot images are provably not the point's letters.

## ⭐⭐ Legality is automatic, and MORE automatic than at the old point

`GradedFiveFrame`'s first structural gain was that the class-five soundness hypothesis
(`v.c` even) holds for **every** `g : D_sq h` with no row hypothesis, where class four had to
read `(Phi g).b = 0` off the selected row.  The stage-four soundness chain
`forceLcs_two_le_stageN3` asks for **two** even columns rather than one, so there was a real
risk that the second one would have to be carried.  It does not:
`stageFrameHom_mem_stageN1` proves both columns even for every `g`, because both are characters
and every letter of the new point has both even (`stage_letters_even`).  That is precisely the
hypothesis the new point was built to satisfy, and it is exactly what makes the composite work.
The forcing therefore carries **no** hypothesis on the dressing element `g` at all.

## ⚠ The legality analysis, REDONE, and the word that has to change

`ArbFrames` asks the dressings of `sqArbFrame` to lie in `ker lambda ∩ ker nu'`.  Two things
were checked rather than assumed.

* The `x0`-dressing is still `nu'`-trivial and still **not** `lambda`-trivial
  (`nuLam_sigArbDress_x0_ne_one`, imported: it is a statement about `D_sq h` and is
  carrier-independent).  The obstruction argument is different at the new point and is recorded
  here rather than formalised, exactly as at the old one.  Write `(a_s, a_0, a_1, a_U, a_V)`
  for the generator exponents.  The abelian columns of `Phi` are characters, so
  `(Phi g).b = a_s + 7 (a_U + a_V)` and `(Phi g).e = 5 a_0 + 2 a_1 + 3 (a_U + a_V)`, while
  `lambda g = c a_s + a_0 + 2 a_1` with `c = sqPivotExp` a unit and `nu' g = a_s` at the
  cleared row.  Legality forces `a_s = 0` and `a_0 + 2 a_1 = 0`; then `(Phi g).b = 0` forces
  `a_U + a_V = 0` since `7` is a unit, and `(Phi g).e` collapses to `5 a_0 - a_0 = 4 a_0`,
  which is `0` or `4` and never `stageX.e = 5`.  So no legal dressing has `Phi g = stageX`.
  ⚠ Note the argument is NOT wave 60's: there the `e`-column was `lambda + nu'` modulo two,
  and here it is not, because `stageU.e` and `stageV.e` are both odd where `forceU.e` and
  `forceV.e` were even.  The conclusion is the same and the route is not.
* ⚠⚠ **Wave 60's commutator repair does NOT survive the change of point, and the fix is a
  longer word.**  `fiveLegalDress h j = [x1, u_j]` is still fully legal, being a commutator, and
  its image at the new point still leaves an **odd** class-five residue, so the exclusion
  applies to it verbatim (`sqRelWord_stageFrame_legal_ne_one`).  But the residue is
  `<m = 4, n = 2, o = 5>` and not the purely central `liftC6 5` of the old point, so it is
  **NOT** class-four blind: `stageFrame_legal_not_class_four_blind` proves `toU5L` of it is
  non-trivial, and half of wave 60's escape statement is lost at this word.
  ⭐⭐ **The class is not lost with it.**  A census over the whole of `gamma_2` of the new
  point's image, `67108864` elements and exhaustive by the coset decomposition
  (`scripts/w61_stagehom/results/verify_stagehom.txt` section E), finds `1024` universally legal
  dressings that DO leave a purely central odd residue, and the shortest are two-commutator
  words.  `stageLegalDress h j = [x1, v_j] * [x1, u_j]^{-1}` is one of them and leaves exactly
  the residue `5` that wave 60's single commutator leaves at the old point, so
  `stageFrame_escape_separates` restores the full class-four-blind escape here, with the
  exclusion one filtration step wider than wave 60's.  ⚠ A conjecture is refuted by that
  census, and it was this lane's own: the first reading of the `[x1, u_j]` failure was that the
  unconditional point had no legal class-four-blind escape at all.  It has `1024` of them.

## ⭐ The wave-59 killing word, at the new point, is the non-vacuity witness

`GradedFiveFrame`'s scope limit was exhibited by an honest group element,
`fiveKillWord h j = [[sigma, u_j], x1]`, whose image at the old point is `<m = 5, n = 6>` with
an odd class-four coordinate and which kills the `x0`-dressed frame outright.  At the new point
the **same** group element has image `<m = 2, n = 2, o = 4>`, which is achievable
(`stageFrameHom_fiveKillWord_mem_stageN3`), and dressing the sigma slot by it moves the
class-five residue from `1` to `7` without killing
(`stageFrame_fiveKillWord_no_kill`).  So one element discharges two duties: it is the composite
check against wave 59 (doctrine iii) and it is the non-vacuity witness, showing the forcing
quantifies over a class that genuinely acts on the residue and still cannot reach `0`.

## ⭐ The stage-FIVE layer at the new point is already on the sharp line

`stageFrame_fiveForces_iff_fiveOrth`.  `GradedFiveNecessity` characterised the class-five
soundness condition by the three-covector invariant `FiveOrth`, and the new point meets it
(`stageWit_fiveOrth`), because the stage-four hypothesis of two even columns is strictly
stronger than the stage-five hypothesis of one.  At the `x0`-dressed frame the relator image is
a central translation with an odd residue, so `fiveForces_iff_fiveOrth` applies in both
directions.  The consequence worth recording: the composite of this file does not widen a
merely sufficient condition.  The statement it widens is already sharp one class down, and the
widening is a genuine filtration step rather than a repair of slack.

## ⚠ The scope, stated honestly

The composite is **unconditional at the stage-four level and at the hom level**, both at once,
with no residual condition anywhere: no achievability convention in the sharp form, no legality
hypothesis on the dressing, no row hypothesis beyond clearing the selected handle (which is
forced, not chosen).  What is **not** claimed:

* The exclusion is against `gamma_3`-dressings of all five slots.  One filtration step wider
  again, `gamma_2`-dressings, is neither proved nor refuted, here or anywhere in the tree, and
  would need the `gamma_2`-level identity at class five, which WILL carry a quadratic block.
* The soundness chain `forceLcs_two_le_stageN3` is **sufficient, not shown sharp**.  The
  survival statements are therefore stated against `stageN3`, which is the sharpest class the
  tree owns (it strictly contains the achievable lattice and consumes no achievability
  convention); the sharp stage-four line itself is not computed here.
* At `h >= 2` the row hypothesis is strictly weaker than "the row is cleared": `sqArbBase`
  displaces the `j`-th handle pair only, so `nu'` is arbitrary away from `j`.

## PROVED versus MEASURED

**PROVED** (this file, no `sorry`, no new axiom, no `native_decide`): everything above, at
every handle count and every handle, for an arbitrary continuous `nu'` cleared at the selected
handle.

**MEASURED** (`scripts/w61_stagehom/`, certified output in
`results/verify_stagehom.txt`; **40** named checks and **0** failures, on the independently
re-implemented `6 x 6` matrix group of `scripts/w59_force5/u6mat.py`, itself cross-checked in
section 0 against wave 58's independent coordinate library before any measurement is taken):

* the three verdicts and the pivot anchor at the new point, at handle counts `1` to `4`, every
  handle, and all eight pivot residues;
* the achievable stage-four lattice: `gamma_3` of the new point's image has order `8192`,
  **none** of its `8192` single-slot dressings kills the `x0`-dressed frame, and `4000` random
  five-slot achievable refinements kill nothing; at wave 59's point `512` of `16384` **do**
  kill, which is exactly the scope gap this file closes;
* the wave-59 killing word at both points side by side;
* ⭐ the legal-dressing census, EXHAUSTIVE over the `67108864` elements of `gamma_2` of the new
  point's image: `1024` universally legal dressings leave a central odd residue, the single
  commutator `[x1, u_j]` is not one of them, and `[x1, v_j] * [x1, u_j]^{-1}` is.

## Contents

* **1** the stage-four binder hom `stageFrameHom`, its letter values, and its pivot anchor;
* **2** the image, ⭐ both even columns for every element, and the achievable lattice;
* **3** the frame identification, and the certificate that the row type is forced;
* **4** ⭐⭐⭐ the forcing on `sqArbFrame`, unconditional, in the `stageN3` form and the
  achievable-lattice form, and ⭐ the stage-five layer on the sharp line;
* **5** the verdicts, the gate cross-check, the blindness, ⚠ the legality audit, the failure of
  wave 60's repair and ⭐⭐ the two-commutator dressing that replaces it, and the non-vacuity
  witness;
* **6** the named cleared row `nuSel h j 0 0`;
* **7** axiom pins.

## Axiom hygiene

All committed prints are **std-3** (`propext`, `Classical.choice`, `Quot.sound`) or a subset;
no census axiom is reachable, `sqPivotExp` included.  Every `decide` is on `ZMod 8` or on
`Fin`-indexed tuples over it; there is no `native_decide`.

## Merge notes

Nothing is redefined.  `SqU6.IsGaThree`, `SqU6.IsGaFour`, `gaThreeShift`, `gaThreeShift_o`,
`gaThreeShift_l`, `gaThreeShift_isGaThree`, `gaThreeShiftO_even`, `gaThreeCore`,
`gaThreeHandle`, `gaThreePair`, `gaThreePairL`, `gaThreePairR`, `sqRelWord_gaThreeDress`,
`stageX`, `stageY`, `stageU`, `stageV`, `stageWit`, `stageImage`, `stageN1`, `stageN3`,
`mem_stageN1`, `mem_stageN3`, `stageN3_isGaThree`, `stageN3_even`, `forceLcs_two_le_stageN3`,
`stageImage_le_stageN1`, `stageWit_a_even`, `sqRelWord_stageWit_triv`,
`sqRelWord_stageWit_diag` and `stageWit_class_four_blind` come from `GradedFiveStageFour`;
`isProP_two_gr6`, `fiveLegalDress`, `fiveKillWord`, `nuLam_sigArbDress_legal`,
`nu_sigArbDress_legal`, `nuLam_sigArbDress_x0_ne_one` come from `GradedFiveFrame`;
`liftC6`, `forceLcs`, `forceN1`, `mem_forceN1`, `fiveTuple`, `conFiveDress`, `fiveSigMark`
come from `GradedFiveForce` and below; `FiveForces`, `FiveOrth`, `fiveForces_iff_fiveOrth`,
`fiveOrth_of_le_forceN1` come from `GradedFiveNecessity`; `sigArbDress`,
`sqArbBase_of_cleared`, `nuLam_sigArbDress`, `nu_sigArbDress` come from `GradedFourHom`;
`nuSelClr_handleU`, `nuSelClr_handleV` from `GradedFourCleared`.

⚠ **Collision watch for the merge** (doctrine v).  The names most likely to be landed
independently by a sibling class-five lane working at the same point are the slot unpackings
`stageWit_zero`, `stageWit_one`, `stageWit_two`, `stageWit_handleU`, `stageWit_handleV`,
`stageWit_handleU_ne`, `stageWit_handleV_ne`, `stageWit_of_ne_zero`, together with
`stageN1_le_forceN1` and `stageSigDress`.  Each is the mechanical transposition of a
`GradedFiveFrame` name and any duplicate should be statement-identical, but the diff must still
be run.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The stage-four binder point as a continuous homomorphism -/

section FrameHom

variable {h : ℕ} {j : Fin h}

/-- The `sigma`-slot value of the stage-four binder point at dressing `v`. -/
@[simp] theorem stageWit_zero (v : SqU6 gr3R) : stageWit h j v 0 = fiveSigMark gr3R * v := by
  rw [stageWit, fiveTuple_zero]

/-- The `x0`-slot value. -/
@[simp] theorem stageWit_one (v : SqU6 gr3R) : stageWit h j v 1 = stageX := by
  rw [stageWit, fiveTuple_one]

/-- The `x1`-slot value. -/
@[simp] theorem stageWit_two (v : SqU6 gr3R) : stageWit h j v 2 = stageY := by
  rw [stageWit, fiveTuple_two]

/-- The live handle's `u`-slot value. -/
@[simp] theorem stageWit_handleU (v : SqU6 gr3R) :
    stageWit h j v (sqHandleIdxU j) = stageU := by
  rw [stageWit, fiveTuple_handleU]

/-- The live handle's `v`-slot value. -/
@[simp] theorem stageWit_handleV (v : SqU6 gr3R) :
    stageWit h j v (sqHandleIdxV j) = stageV := by
  rw [stageWit, fiveTuple_handleV]

/-- Every other handle slot is trivial. -/
theorem stageWit_handleU_ne (v : SqU6 gr3R) {j' : Fin h} (hne : j' ≠ j) :
    stageWit h j v (sqHandleIdxU j') = 1 := by
  rw [stageWit, fiveTuple_handleU_ne hne]

/-- …and likewise on the `v`-side. -/
theorem stageWit_handleV_ne (v : SqU6 gr3R) {j' : Fin h} (hne : j' ≠ j) :
    stageWit h j v (sqHandleIdxV j') = 1 := by
  rw [stageWit, fiveTuple_handleV_ne hne]

/-- **Only the sigma slot sees the dressing.**  This is what makes the sigma-only dressing of
the frame land on the stage-four binder point at the dressed value, and it is the one shape
fact the frame identification of section 3 consumes. -/
theorem stageWit_of_ne_zero {v : SqU6 gr3R} {i : Fin (sqRank h)} (hi : (i : ℕ) ≠ 0) :
    stageWit h j v i = stageWit h j 1 i := by
  simp only [stageWit, fiveTuple]
  rw [if_neg hi, if_neg hi]

variable (h j) in
/-- ⭐⭐ **The stage-four binder hom.**  `GradedFiveStageFour`'s new point kills the relator at
every handle count and every handle (`sqRelWord_stageWit_triv`), so the committed class-five
lift turns it into an honest continuous homomorphism `D_sq h → U_6(ℤ/8)`.  Every tuple statement
of `GradedFiveStageFour` at that point is now a statement about this hom, and unlike
`GradedFiveFrame.fiveFrameHom` its exclusion is against stage-FOUR refinements. -/
noncomputable def stageFrameHom : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R) :=
  sqU6Hom gr3R_card h (stageWit h j 1) (sqRelWord_stageWit_triv h j)

@[simp] theorem stageFrameHom_gen (i : Fin (sqRank h)) :
    stageFrameHom h j (sqGen h i) = stageWit h j 1 i := sqU6Hom_gen _ _ _ i

@[simp] theorem stageFrameHom_sigma : stageFrameHom h j (dsqSigma h) = fiveSigMark gr3R := by
  rw [dsqSigma, stageFrameHom_gen, stageWit_zero, mul_one]

/-- ⭐ **The `x0`-generator maps to the dressing the exclusion is about.**  The sigma dressing
`a0 = a1` of `GradedSigmaFour` section 7 is, at the hom level, the dressing by the `x0`
generator itself, exactly as at the old point. -/
@[simp] theorem stageFrameHom_x0 : stageFrameHom h j (dsqX0 h) = stageX := by
  rw [dsqX0, stageFrameHom_gen, stageWit_one]

@[simp] theorem stageFrameHom_x1 : stageFrameHom h j (dsqX1 h) = stageY := by
  rw [dsqX1, stageFrameHom_gen, stageWit_two]

@[simp] theorem stageFrameHom_handleU :
    stageFrameHom h j (sqGen h (sqHandleIdxU j)) = stageU := by
  rw [stageFrameHom_gen, stageWit_handleU]

@[simp] theorem stageFrameHom_handleV :
    stageFrameHom h j (sqGen h (sqHandleIdxV j)) = stageV := by
  rw [stageFrameHom_gen, stageWit_handleV]

theorem stageFrameHom_handle_ne {j' : Fin h} (hne : j' ≠ j) :
    stageFrameHom h j (sqGen h (sqHandleIdxU j')) = 1 ∧
      stageFrameHom h j (sqGen h (sqHandleIdxV j')) = 1 :=
  ⟨by rw [stageFrameHom_gen, stageWit_handleU_ne _ hne],
    by rw [stageFrameHom_gen, stageWit_handleV_ne _ hne]⟩

/-! ### The pivot anchor stays mechanical at the new point

`GradedFiveFrame` found the class-five pivot anchor mechanical where the class-four one was
not: all ten obstructions of `SqU6.zpowZtwo_of_flat` vanish at the binder point's `x0`-slot.
The change of point moves that slot from `forceX = <a = 2, e = 1>` to
`stageX = <a = 2, e = 5>`, and the obstructions still all vanish, so the anchor is again two
rewrites. -/

/-- ⭐ **All ten flat obstructions vanish at the new point's `x0`-slot.** -/
theorem stageX_flat :
    stageX.a * stageX.b = 0 ∧ stageX.b * stageX.c = 0 ∧ stageX.c * stageX.d = 0
      ∧ stageX.d * stageX.e = 0 ∧ stageX.a * stageX.g + stageX.f * stageX.c = 0
      ∧ stageX.b * stageX.h + stageX.g * stageX.d = 0
      ∧ stageX.c * stageX.i + stageX.h * stageX.e = 0
      ∧ stageX.a * stageX.k + stageX.f * stageX.h + stageX.j * stageX.d = 0
      ∧ stageX.b * stageX.l + stageX.g * stageX.i + stageX.k * stageX.e = 0
      ∧ stageX.a * stageX.n + stageX.f * stageX.l + stageX.j * stageX.i
          + stageX.m * stageX.e = 0 := by decide

/-- ⭐ **The `x0`-slot's `ℤ₂`-powers at the new point**, through the *flat* power lemma: the
powering is `R`-linear in all fifteen coordinates, with no quadratic correction. -/
theorem stageX_zpowZtwo (u : ℤ_[2]) :
    zpowZtwo isProP_two_gr6 stageX u
      = ⟨2 * gr3Pi u, 0, 0, 0, 5 * gr3Pi u, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := by
  rw [SqU6.zpowZtwo_of_flat isProP_two_gr6 gr3Pi gr3Pi_open (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  ext <;> simp [stageX] <;> ring

/-- ⭐ **The pivot image at the stage-four binder hom**, in closed form.  The `sqPivotExp`
dependence returns only through the residue `c = gr3Pi sqPivotExp`, and the fifth abelian
column is `-5c` where the old point had `-c`. -/
theorem stageFrameHom_sqPivot :
    stageFrameHom h j (sqPivot h)
      = ⟨-(2 * gr3Pi sqPivotExp), 1, 0, 0, -(5 * gr3Pi sqPivotExp),
          0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := by
  rw [sqPivot, sqMixPivotElem, map_mul, map_inv,
    map_zpowZtwo (isProP_DSq h) isProP_two_gr6, stageFrameHom_x0, stageX_zpowZtwo,
    stageFrameHom_sigma]
  ext <;> simp [fiveSigMark]

/-- ⭐ **The pivot image is non-trivial**, and its `b`-coordinate is `1` whatever the pivot
residue is.  This is what makes the row type forced rather than chosen, at the new point for
the same reason as at the old one. -/
theorem stageFrameHom_sqPivot_ne_one : stageFrameHom h j (sqPivot h) ≠ 1 := by
  intro hc
  have hb : (1 : gr3R) = 0 := by
    have hbb := congrArg SqU6.b hc
    rwa [stageFrameHom_sqPivot, SqU6.one_b] at hbb
  exact absurd hb (by decide)

end FrameHom

/-! ## 2 The image, both even columns, and the achievable stage-four lattice -/

section Image

variable {h : ℕ} {j : Fin h}

/-- **The image of the stage-four binder hom lies in the closure of its marking.** -/
theorem stageFrameHom_mem_closure (x : (DSq h : Type)) :
    stageFrameHom h j x ∈ stageImage h j 1 := by
  have hgen : Subgroup.closure (Set.range (sqGen h))
      ≤ Subgroup.comap (stageFrameHom h j).toMonoidHom (stageImage h j 1) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    show stageFrameHom h j (sqGen h i) ∈ stageImage h j 1
    rw [stageFrameHom_gen]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hclosed : IsClosed ((Subgroup.comap (stageFrameHom h j).toMonoidHom
      (stageImage h j 1) : Subgroup (DSq h : Type)) : Set (DSq h : Type)) := by
    have hpre : ((Subgroup.comap (stageFrameHom h j).toMonoidHom
        (stageImage h j 1) : Subgroup (DSq h : Type)) : Set (DSq h : Type))
        = stageFrameHom h j ⁻¹' ((stageImage h j 1) : Set (SqU6 gr3R)) := rfl
    rw [hpre]
    exact (isClosed_discrete _).preimage (stageFrameHom h j).continuous_toFun
  have hle := Subgroup.topologicalClosure_minimal _ hgen hclosed
  rw [dsq_topGen h] at hle
  exact hle (Subgroup.mem_top x)

/-- ⭐⭐ **Both soundness columns are automatic at the new point.**  Every value of the
stage-four binder hom has an even `(1,2)`-column **and** an even `(3,4)`-column, with no
hypothesis on the element at all.  This is the whole reason the composite works: the stage-four
chain `forceLcs_two_le_stageN3` needs two even columns where the stage-five chain needed one,
and `GradedFiveStageFour` built its point precisely so that both are characters vanishing
modulo two on every letter (`stage_letters_even`).  There is no side condition to carry, and
in particular none to read off a row. -/
theorem stageFrameHom_mem_stageN1 (x : (DSq h : Type)) : stageFrameHom h j x ∈ stageN1 :=
  stageImage_le_stageN1 (h := h) (j := j) ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
    (stageFrameHom_mem_closure x)

/-- …in coordinate form. -/
theorem stageFrameHom_columns_even (x : (DSq h : Type)) :
    (2 : gr3R) ∣ (stageFrameHom h j x).a ∧ (2 : gr3R) ∣ (stageFrameHom h j x).c :=
  mem_stageN1.mp (stageFrameHom_mem_stageN1 x)

/-- ⭐ **The achievable stage-four lattice at any dressed image point is sound.**  At the new
point dressed by the image of **any** group element, every achievable `gamma_3`-dressing has
`j`, `l` and `m` even.  One filtration step wider than
`GradedFiveFrame.forceLcs_fiveFrameHom_le_forceN4`. -/
theorem forceLcs_stageFrameHom_le_stageN3 (g : (DSq h : Type)) :
    forceLcs (stageImage h j (stageFrameHom h j g)) 2 ≤ stageN3 :=
  forceLcs_two_le_stageN3 (stageImage_le_stageN1 (stageFrameHom_columns_even g))

end Image

/-! ## 3 The frame identification, and the certificate that the row type is forced -/

section Frame

variable {h : ℕ} {j : Fin h}
variable {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- ⭐⭐ **The frame identification at the new point**: at a row cleared at the selected handle,
the stage-four binder hom sends the arbitrary-dressing frame with a sigma-only dressing `g` to
exactly the stage-four binder point at the dressing value `stageFrameHom h j g`.

⭐ **It survives the change of point unchanged.**  The proof consumes only `stageWit_zero` and
`stageWit_of_ne_zero`, that is, only the fact that the marking's handle slots are the raw
generator images and that just the sigma slot sees the dressing.  Those are properties of the
`fiveTuple` shape, which the new point shares with the old one by construction; the letters
themselves never appear.  So the extra evenness hypothesis that distinguishes the new point
costs the identification nothing. -/
theorem stageFrameHom_sqArbFrame (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) (g : (DSq h : Type)) :
    (fun i => stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i))
      = stageWit h j (stageFrameHom h j g) := by
  funext i
  by_cases h0 : (i : ℕ) = 0
  · have hi : i = 0 := Fin.val_injective (by rw [h0, sqVal_zero])
    subst hi
    rw [sqArbFrame, sqArbBase_of_cleared hu hv, sigArbDress_zero, map_mul, stageFrameHom_gen,
      stageWit_zero, stageWit_zero, mul_one]
  · rw [sqArbFrame, sqArbBase_of_cleared hu hv, sigArbDress_ne h0, mul_one, stageFrameHom_gen,
      stageWit_of_ne_zero (v := stageFrameHom h j g) h0]

/-- The achievable stage-four lattice of the frame's image **is** the achievable stage-four
lattice of the new point at the dressed value: the two conventions agree on the nose. -/
theorem stageImage_eq_frame_closure (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) (g : (DSq h : Type)) :
    Subgroup.closure (Set.range fun i =>
        stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i))
      = stageImage h j (stageFrameHom h j g) := by
  rw [stageFrameHom_sqArbFrame hu hv g]
  rfl

/-- ⚠⚠ **The `u`-slot is displaced at a bumped row**, so the frame identification cannot hold
there: at `nu'(u_j) = 1` the frame's `u`-slot image is `Phi(w)⁻¹ · stageU`, and it is not
`stageU`, because the pivot image is non-trivial.  Reaching a bumped row at the new point is a
fresh fifteen-row solve at a displaced binder point, exactly as at the old one. -/
theorem stageFrameHom_sqArbBase_handleU_ne
    (hu : nu' (sqGen h (sqHandleIdxU j)) = ofAdd (1 : ℤ_[2])) (v : SqU6 gr3R) :
    stageFrameHom h j (sqArbBase h nu' j (sqHandleIdxU j)) ≠ stageWit h j v (sqHandleIdxU j) := by
  rw [sqArbBase_handleU, sqEichU, hu, toAdd_ofAdd, zpowZtwo_one_exp, map_mul, map_inv,
    stageFrameHom_handleU, stageWit_handleU]
  intro hc
  refine stageFrameHom_sqPivot_ne_one (h := h) (j := j) ?_
  have h1 : (stageFrameHom h j (sqPivot h))⁻¹ * stageU = 1 * stageU := by rw [hc, one_mul]
  rw [← inv_eq_one]
  exact mul_right_cancel h1

/-- ⚠⚠ …and the `v`-slot likewise. -/
theorem stageFrameHom_sqArbBase_handleV_ne
    (hv : nu' (sqGen h (sqHandleIdxV j)) = ofAdd (1 : ℤ_[2])) (v : SqU6 gr3R) :
    stageFrameHom h j (sqArbBase h nu' j (sqHandleIdxV j)) ≠ stageWit h j v (sqHandleIdxV j) := by
  rw [sqArbBase_handleV, sqEichV, hv, toAdd_ofAdd, zpowZtwo_one_exp, map_mul, map_inv,
    stageFrameHom_handleV, stageWit_handleV]
  intro hc
  refine stageFrameHom_sqPivot_ne_one (h := h) (j := j) ?_
  have h1 : stageV * (stageFrameHom h j (sqPivot h))⁻¹ = stageV * 1 := by rw [hc, mul_one]
  rw [← inv_eq_one]
  exact mul_left_cancel h1

end Frame

/-! ## 4 The forcing on `sqArbFrame`, unconditional -/

section Forcing

variable {h : ℕ} {j : Fin h}
variable {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- ⭐⭐ **The stage-four forcing at the tuple level, with the achievability convention
spent.**  `GradedFiveStageFour.stageWit_sigma_forced` asks the dressing to be **achievable** and
the sigma dressing to have both columns even; here the refinement is asked only to be
`gamma_3`-shaped with `j`, `l` and `m` even, and the sigma dressing only to have an even
`(1,2)`-column.  This is the sharpest class the tree owns at stage four: it strictly contains
the achievable lattice by `forceLcs_two_le_stageN3`, and consumes no achievability convention
at all.  ⚠ It is not shown to be the sharp LINE; the sharp stage-four line is not computed
here, and `gaThreeShiftO_even` is the reason exactly these three coordinates appear. -/
theorem stageWit_sigma_forced_sharp {v : SqU6 gr3R} {z : Fin (sqRank h) → SqU6 gr3R}
    (hv : (2 : gr3R) ∣ v.a) (hz : ∀ i, z i ∈ stageN3)
    (hkill : sqRelWord (conFiveDress (stageWit h j v) z) = 1) :
    selPar (sqRelWord (stageWit h j v)).o = 0 := by
  have hga : ∀ i, (z i).IsGaThree := fun i => stageN3_isGaThree (hz i)
  have heven : ∀ i, (2 : gr3R) ∣ (z i).j ∧ (2 : gr3R) ∣ (z i).l ∧ (2 : gr3R) ∣ (z i).m :=
    fun i => stageN3_even (hz i)
  rw [sqRelWord_gaThreeDress hga] at hkill
  have ho := congrArg SqU6.o hkill
  rw [SqU6.mul_o, SqU6.one_o] at ho
  have hsh := gaThreeShift_isGaThree (h := h) (m := stageWit h j v) (z := z)
  obtain ⟨ca, hca⟩ : (2 : gr3R) ∣ (sqRelWord (stageWit h j v)).a :=
    ⟨-2 * (stageWit h j v 1).a + (stageWit h j v 2).a, by rw [SqU6.sqRelWord_a]; ring⟩
  obtain ⟨cl, hcl⟩ : (2 : gr3R) ∣ (gaThreeShift h (stageWit h j v) z).l := by
    rw [gaThreeShift_l]
    exact ⟨-2 * (z 1).l + (z 2).l, by ring⟩
  obtain ⟨co, hco⟩ : (2 : gr3R) ∣ (gaThreeShift h (stageWit h j v) z).o := by
    rw [gaThreeShift_o]
    exact gaThreeShiftO_even (stageWit_a_even hv) heven
  rw [hca, hcl, hco, hsh.2.2.2.2.1, hsh.2.2.2.2.2.2.2.2] at ho
  have hfin : (sqRelWord (stageWit h j v)).o
      = 2 * (-(co + ca * (gaThreeShift h (stageWit h j v) z).n
        + (sqRelWord (stageWit h j v)).f * cl)) := by
    linear_combination ho
  rw [hfin, selPar_two_mul]

/-- ⭐⭐⭐ **THE HEADLINE: the class-five sigma forcing on `sqArbFrame`, against STAGE-FOUR
refinements.**  At every handle count, every handle, and any continuous `nu'` cleared at the
selected handle, a sigma dressing of the arbitrary-dressing frame whose image is killed by
**any** five-slot `gamma_3`-refinement with `j`, `l` and `m` even leaves an **even** class-five
residue.

This is the statement wave 60 produced twice in halves.  It is `GradedFiveFrame`'s hom-level
transport, at `GradedFiveStageFour`'s unconditional point, and it inherits nothing from either
one's price: the refinements are `gamma_3`-shaped, one filtration step wider than
`fiveFrame_sigma_forced_sharp`'s and the same scope the committed class-four exclusion enjoys;
and the object quantified over is an honest frame of `D_sq h`, not a tuple.

**Nothing at all is carried on the dressing.**  There is no legality hypothesis and no column
hypothesis on `g`: `stageFrameHom_mem_stageN1` supplies both even columns for every element.
The two hypotheses that are carried, `hu` and `hv`, are forced by the shape of the witness and
not chosen (`stageFrameHom_sqArbBase_handleU_ne`). -/
theorem stageFrame_sigma_forced_sharp (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) (g : (DSq h : Type))
    {z : Fin (sqRank h) → SqU6 gr3R} (hz : ∀ i, z i ∈ stageN3)
    (hkill : sqRelWord (conFiveDress
      (fun i => stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i)) z) = 1) :
    selPar (sqRelWord fun i =>
      stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i)).o = 0 := by
  rw [stageFrameHom_sqArbFrame hu hv g] at hkill ⊢
  exact stageWit_sigma_forced_sharp (stageFrameHom_columns_even g).1 hz hkill

/-- ⭐⭐ **The same forcing in the committed achievability convention**: the five dressings are
drawn from `gamma_3` of the subgroup generated by the frame's own image slots, the honest
lower central series rather than a declared lattice.  It follows from the sharp form because
the achievable lattice is contained in `stageN3` (`forceLcs_stageFrameHom_le_stageN3`). -/
theorem stageFrame_sigma_forced (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) (g : (DSq h : Type))
    {z : Fin (sqRank h) → SqU6 gr3R}
    (hz : ∀ i, z i ∈ forceLcs (stageImage h j (stageFrameHom h j g)) 2)
    (hkill : sqRelWord (conFiveDress
      (fun i => stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i)) z) = 1) :
    selPar (sqRelWord fun i =>
      stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i)).o = 0 :=
  stageFrame_sigma_forced_sharp hu hv g
    (fun i => forceLcs_stageFrameHom_le_stageN3 g (hz i)) hkill

/-! ### ⭐ The stage-FIVE layer at the new point sits exactly on wave 60's sharp line

`GradedFiveNecessity` characterised the class-five soundness line: at a marking whose relator
is a central translation with an odd residue, the class-five forcing holds **exactly** when the
three-covector invariant `FiveOrth` does.  The new point meets it, so the stage-five layer of
this file's point is not merely sufficient but sharp, and the stage-four exclusion above is the
strict widening of a statement already on the line rather than a widening of a weak one. -/

/-- The stage-four soundness class is contained in the stage-five one: two even columns imply
one.  This is what puts the new point inside the reach of `GradedFiveNecessity`. -/
theorem stageN1_le_forceN1 : stageN1 ≤ forceN1 := fun _ hz => mem_forceN1.mpr (mem_stageN1.mp hz).2

/-- ⭐ **The new point satisfies the SHARP class-five invariant**, at every dressing whose two
columns are even and in particular at every image of the binder hom.  `FiveOrth` is
`GradedFiveNecessity`'s three-covector condition, and `fiveOrth_of_le_forceN1` is the route:
the stage-four hypothesis is strictly stronger than the stage-five one. -/
theorem stageWit_fiveOrth {v : SqU6 gr3R} (hv : (2 : gr3R) ∣ v.a ∧ (2 : gr3R) ∣ v.c) :
    FiveOrth (stageWit h j v) j :=
  fiveOrth_of_le_forceN1 (le_trans (stageImage_le_stageN1 hv) stageN1_le_forceN1)

/-- ⭐⭐ **The class-five forcing at the frame is on the sharp line, in both directions.**  At
the `x0`-dressed frame the relator image is the central translation `liftC6 1` with an odd
residue, so `GradedFiveNecessity.fiveForces_iff_fiveOrth` applies: the stage-FIVE forcing holds
there **exactly** when the sharp invariant does, and it does.  So the composite of this file
does not sit on a merely sufficient condition one class down: it widens a sharp statement. -/
theorem stageFrame_fiveForces_iff_fiveOrth (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    (FiveForces (fun i =>
        stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i)) j
      ↔ FiveOrth (fun i =>
        stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i)) j)
    ∧ FiveOrth (fun i =>
        stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i)) j := by
  have hframe := stageFrameHom_sqArbFrame (nu' := nu') hu hv (dsqX0 h)
  rw [hframe, stageFrameHom_x0]
  have hres : sqRelWord (stageWit h j stageX) = liftC6 1 := sqRelWord_stageWit_diag h j
  exact ⟨fiveForces_iff_fiveOrth hres (by decide),
    stageWit_fiveOrth ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩⟩

end Forcing

/-! ## 5 The verdicts on the frame, the legality audit, the scope, and non-vacuity -/

section Verdicts

variable {h : ℕ} {j : Fin h}
variable {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- ⭐ **The undressed frame kills the relator outright** at the stage-four binder hom: all
fifteen rows vanish, so the hom is a genuine class-five quotient of the frame and the gate is
live. -/
theorem sqRelWord_stageFrame_triv (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    sqRelWord (fun i => stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h 1) i)) = 1 := by
  rw [stageFrameHom_sqArbFrame hu hv, map_one]
  exact sqRelWord_stageWit_triv h j

/-- ⭐ **The same fact by the gate rather than by the tuple.**  At a cleared row the undressed
arbitrary-dressing frame **is** the standard frame, which kills the relator in `D_sq h` itself,
so the class-five gate `sqU6Balance_gen` gives the previous theorem without touching the new
point's fifteen-row `decide`.  Both routes agree, which is wave 57's process finding applied to
this file's own composite. -/
theorem sqRelWord_stageFrame_triv_gate (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    sqRelWord (fun i => stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h 1) i)) = 1 := by
  have hframe : ∀ i, sqArbFrame h nu' j (sigArbDress h (1 : (DSq h : Type))) i = sqGen h i := by
    intro i
    have hd : sigArbDress h (1 : (DSq h : Type)) i = 1 := by
      by_cases h0 : (i : ℕ) = 0
      · rw [show i = 0 from Fin.val_injective (by rw [h0, sqVal_zero]), sigArbDress_zero]
      · rw [sigArbDress_ne h0]
    rw [sqArbFrame, sqArbBase_of_cleared hu hv, hd, mul_one]
  have hcongr : (fun i => stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h 1) i))
      = fun i => stageFrameHom h j (sqGen h i) :=
    funext fun i => congrArg (stageFrameHom h j) (hframe i)
  rw [hcongr]
  exact sqU6Balance_gen (stageFrameHom h j)

/-- ⭐⭐ **The `x0`-dressed frame leaves the ODD class-five residue `1`.**  The sigma dressing
`a0 = a1` of `GradedSigmaFour` section 7, executed on `sqArbFrame` itself at the unconditional
point. -/
theorem sqRelWord_stageFrame_diag (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    sqRelWord (fun i =>
        stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i)) = SqU6.liftO 1 := by
  rw [stageFrameHom_sqArbFrame hu hv, stageFrameHom_x0]
  exact sqRelWord_stageWit_diag h j

/-- ⭐⭐⭐ **THE EXCLUSION ON `sqArbFrame`, UNCONDITIONAL: the `x0`-dressed frame survives every
stage-four refinement.**  No five-slot `gamma_3`-refinement with `j`, `l` and `m` even kills the
relator image, at any handle count, any handle, and any row cleared at the selected handle.
This is the campaign's single statement that is both unconditional and about homomorphisms. -/
theorem sqRelWord_stageFrame_diag_ne_one_sharp (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1)
    {z : Fin (sqRank h) → SqU6 gr3R} (hz : ∀ i, z i ∈ stageN3) :
    sqRelWord (conFiveDress
      (fun i => stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i)) z) ≠ 1 := by
  intro hc
  have hp := stageFrame_sigma_forced_sharp hu hv (dsqX0 h) hz hc
  rw [sqRelWord_stageFrame_diag hu hv, SqU6.liftO_o] at hp
  exact absurd hp (by decide)

/-- ⭐⭐ **The exclusion against the achievable stage-four lattice**, the campaign's convention:
no achievable five-slot `gamma_3`-refinement of the frame's image kills the relator image. -/
theorem sqRelWord_stageFrame_diag_ne_one (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1)
    {z : Fin (sqRank h) → SqU6 gr3R}
    (hz : ∀ i, z i ∈ forceLcs (stageImage h j (stageFrameHom h j (dsqX0 h))) 2) :
    sqRelWord (conFiveDress
      (fun i => stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i)) z) ≠ 1 :=
  sqRelWord_stageFrame_diag_ne_one_sharp hu hv
    (fun i => forceLcs_stageFrameHom_le_stageN3 (dsqX0 h) (hz i))

/-- …and the bit really does separate the two dressings on the frame. -/
theorem stageFrame_bit_separates (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    selPar (sqRelWord fun i =>
        stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h 1) i)).o = 0
      ∧ selPar (sqRelWord fun i =>
        stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i)).o = 1 := by
  refine ⟨?_, ?_⟩
  · rw [sqRelWord_stageFrame_triv hu hv]
    decide
  · rw [sqRelWord_stageFrame_diag hu hv, SqU6.liftO_o]
    decide

/-- ⭐ **Every class-`<= 4` verdict on the frame is the same for both dressings**: both
`U_5`-quotients of the frame's relator image are trivial in each case, so the separation above
is purely class five. -/
theorem stageFrame_class_four_blind (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    (sqRelWord (fun i => SqU6.toU5L
        (stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h 1) i))) = 1
      ∧ sqRelWord (fun i => SqU6.toU5R
        (stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h 1) i))) = 1)
    ∧ (sqRelWord (fun i => SqU6.toU5L
        (stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i))) = 1
      ∧ sqRelWord (fun i => SqU6.toU5R
        (stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i))) = 1) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [← SqU6.toU5L_sqRelWord, sqRelWord_stageFrame_triv hu hv, map_one]
  · rw [← SqU6.toU5R_sqRelWord, sqRelWord_stageFrame_triv hu hv, map_one]
  · rw [← SqU6.toU5L_sqRelWord, sqRelWord_stageFrame_diag hu hv]
    decide
  · rw [← SqU6.toU5R_sqRelWord, sqRelWord_stageFrame_diag hu hv]
    decide

/-! ### ⚠ The legality audit at the new point, and the half of wave 60's repair that fails

`ArbFrames` asks the dressings of `sqArbFrame` to lie in `ker lambda ∩ ker nu'`.  The
`x0`-dressing is `nu'`-trivial and **not** `lambda`-trivial, at the new point exactly as at the
old one, and for a different reason (see the module docstring).  Wave 60's repair was the
commutator `fiveLegalDress h j = [x1, u_j]`, fully legal because a commutator lies in the
kernel of every character.  It is imported, not rebuilt, and its legality carries over verbatim
because it is a statement about `D_sq h`.

⚠⚠ **What does not carry over is the conclusion.**  At the old point the commutator dressing
leaves the purely central odd residue `liftC6 5`, so class four cannot see it.  At the new point
it leaves `<m = 4, n = 2, o = 5>`: still odd at class five, so the exclusion applies to it, but
**not** central, so `toU5L` of the relator image is non-trivial and the class-four machinery
does see it.  The two halves of wave 60's escape statement have come apart, and this file says
which one survives. -/

/-- The `x0`-dressing's `lambda`-row is `1`, so it is **not** `lambda`-trivial, at the new
point as at the old one: the statement is about `D_sq h` and is carrier-independent, so it is
imported and restated rather than reproved. -/
theorem nuLam_stage_sigArbDress_x0_ne_one : nuLam h (sigArbDress h (dsqX0 h) 0) ≠ 1 :=
  nuLam_sigArbDress_x0_ne_one

theorem stageFrameHom_fiveLegalDress :
    stageFrameHom h j (fiveLegalDress h j) = commP stageY stageU := by
  rw [fiveLegalDress, map_commP, stageFrameHom_x1, stageFrameHom_handleU]

/-- ⚠ **The legal dressing at the new point leaves the odd residue `5`, and it is NOT
central.**  Compare `GradedFiveFrame.sqRelWord_fiveWit_legal`, where the same group element
leaves `liftC6 5`. -/
theorem sqRelWord_stageWit_legal (h : ℕ) (j : Fin h) :
    sqRelWord (stageWit h j (commP stageY stageU))
      = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 5⟩ := by
  rw [stageWit, sqRelWord_fiveTuple]
  decide

/-- ⚠ …and the same on `sqArbFrame`. -/
theorem sqRelWord_stageFrame_legal (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    sqRelWord (fun i => stageFrameHom h j
        (sqArbFrame h nu' j (sigArbDress h (fiveLegalDress h j)) i))
      = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 5⟩ := by
  rw [stageFrameHom_sqArbFrame hu hv, stageFrameHom_fiveLegalDress]
  exact sqRelWord_stageWit_legal h j

/-- ⭐ **The exclusion at the legal dressing survives**: no five-slot stage-four refinement with
`j`, `l` and `m` even kills it either, because the class-five residue `5` is odd.  So the half
of wave 60's repair that the campaign needs for the forcing does carry over. -/
theorem sqRelWord_stageFrame_legal_ne_one (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1)
    {z : Fin (sqRank h) → SqU6 gr3R} (hz : ∀ i, z i ∈ stageN3) :
    sqRelWord (conFiveDress (fun i => stageFrameHom h j
      (sqArbFrame h nu' j (sigArbDress h (fiveLegalDress h j)) i)) z) ≠ 1 := by
  intro hc
  have hp := stageFrame_sigma_forced_sharp hu hv (fiveLegalDress h j) hz hc
  rw [sqRelWord_stageFrame_legal hu hv] at hp
  exact absurd hp (by decide)

/-- ⚠⚠ **The half that fails.**  At the new point the fully legal commutator dressing is
**visible** to the class-four machinery: the left `U_5`-quotient of its relator image is
non-trivial, where at the old point both quotients are trivial
(`GradedFiveFrame.fiveFrame_legal_class_four_blind`).  So the class-four-blind escape and the
unconditional exclusion do not currently live at the same point, and this is the one place
where the two wave-60 results genuinely conflict. -/
theorem stageFrame_legal_not_class_four_blind (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    sqRelWord (fun i => SqU6.toU5L (stageFrameHom h j
      (sqArbFrame h nu' j (sigArbDress h (fiveLegalDress h j)) i))) ≠ 1 := by
  rw [← SqU6.toU5L_sqRelWord, sqRelWord_stageFrame_legal hu hv]
  decide

/-! ### ⭐⭐ …and the repair that DOES work at the new point: a two-commutator dressing

The failure above is a failure of the particular element, not of the class.  ⭐ **A census over
the whole of `gamma_2` of the new point's image** (`scripts/w61_stagehom/results/`,
`67108864` elements, exhaustive by the coset decomposition) finds `1024` universally legal
dressings that DO leave a purely central odd residue, and the shortest are two-commutator
words.  `stageLegalDress h j = [x1, v_j] * [x1, u_j]^{-1}` is one, and it leaves exactly the
residue `liftO 5` that wave 60's single commutator leaves at the old point.  So the full
class-four-blind escape is restored at the unconditional point, and nothing about wave 60's
statement has to be given up beyond the choice of word. -/

variable (h j) in
/-- ⭐⭐ **The stage-four legal escape dressing**: the two-commutator word
`[x1, v_j] * [x1, u_j]^{-1}` in the frame's own generators.  Being a product of commutators it
lies in the kernel of every character, so it is `lambda`-trivial and `nu'`-trivial at every
row, and it is the replacement for `GradedFiveFrame.fiveLegalDress` at the new point. -/
noncomputable def stageLegalDress : (DSq h : Type) :=
  commP (dsqX1 h) (sqGen h (sqHandleIdxV j)) * (commP (dsqX1 h) (sqGen h (sqHandleIdxU j)))⁻¹

/-- A commutator is trivial in an abelian target.  (`GradedFiveFrame`'s copy is `private`, so
this one is rebuilt here.) -/
private theorem commP_eq_one_multPadic'' (x y : Multiplicative ℤ_[2]) : commP x y = 1 :=
  Multiplicative.toAdd.injective (by
    simp only [commP, toAdd_mul, toAdd_inv, toAdd_one]
    ring)

/-- The stage-four legal dressing is killed by every character of `D_sq h`. -/
theorem stageLegalDress_char_triv
    {A : Type} [CommGroup A] (chi : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    chi (stageLegalDress h j) = 1 := by
  rw [stageLegalDress, map_mul, map_inv, map_commP, map_commP, commP_eq_one_multPadic'',
    commP_eq_one_multPadic'', inv_one, mul_one]

/-- The stage-four legal dressing is `lambda`-trivial slotwise, at every row. -/
theorem nuLam_stage_sigArbDress_legal (i : Fin (sqRank h)) :
    nuLam h (sigArbDress h (stageLegalDress h j) i) = 1 :=
  nuLam_sigArbDress (stageLegalDress_char_triv (A := Multiplicative ℤ_[2]) (nuLam h)) i

/-- …and `nu'`-trivial slotwise, at every row, for every continuous `nu'`. -/
theorem nu_stage_sigArbDress_legal (i : Fin (sqRank h)) :
    nu' (sigArbDress h (stageLegalDress h j) i) = 1 :=
  nu_sigArbDress (stageLegalDress_char_triv (A := Multiplicative ℤ_[2]) nu') i

theorem stageFrameHom_stageLegalDress :
    stageFrameHom h j (stageLegalDress h j)
      = commP stageY stageV * (commP stageY stageU)⁻¹ := by
  rw [stageLegalDress, map_mul, map_inv, map_commP, map_commP, stageFrameHom_x1,
    stageFrameHom_handleU, stageFrameHom_handleV]

set_option maxRecDepth 40000 in
/-- ⭐⭐ **The repair leaves the purely central, ODD residue `5`** at the new point, at every
handle count and every handle: exactly the value `GradedFiveFrame.sqRelWord_fiveWit_legal` gets
at the old point from a single commutator. -/
theorem sqRelWord_stageWit_stageLegal (h : ℕ) (j : Fin h) :
    sqRelWord (stageWit h j (commP stageY stageV * (commP stageY stageU)⁻¹))
      = SqU6.liftO 5 := by
  rw [stageWit, sqRelWord_fiveTuple]
  decide

/-- ⭐⭐ …and the same on `sqArbFrame`. -/
theorem sqRelWord_stageFrame_stageLegal (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    sqRelWord (fun i => stageFrameHom h j
        (sqArbFrame h nu' j (sigArbDress h (stageLegalDress h j)) i)) = SqU6.liftO 5 := by
  rw [stageFrameHom_sqArbFrame hu hv, stageFrameHom_stageLegalDress]
  exact sqRelWord_stageWit_stageLegal h j

/-- ⭐⭐ **The exclusion at the repaired legal dressing**: no five-slot stage-four refinement
with `j`, `l` and `m` even kills it either. -/
theorem sqRelWord_stageFrame_stageLegal_ne_one (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1)
    {z : Fin (sqRank h) → SqU6 gr3R} (hz : ∀ i, z i ∈ stageN3) :
    sqRelWord (conFiveDress (fun i => stageFrameHom h j
      (sqArbFrame h nu' j (sigArbDress h (stageLegalDress h j)) i)) z) ≠ 1 := by
  intro hc
  have hp := stageFrame_sigma_forced_sharp hu hv (stageLegalDress h j) hz hc
  rw [sqRelWord_stageFrame_stageLegal hu hv, SqU6.liftO_o] at hp
  exact absurd hp (by decide)

/-- ⭐⭐ **The repaired dressing IS class-four invisible**: its relator image is central, so
both `U_5`-quotients are trivial.  This is the half that `fiveLegalDress` loses at the new
point, recovered. -/
theorem stageFrame_stageLegal_class_four_blind (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    sqRelWord (fun i => SqU6.toU5L (stageFrameHom h j
        (sqArbFrame h nu' j (sigArbDress h (stageLegalDress h j)) i))) = 1
      ∧ sqRelWord (fun i => SqU6.toU5R (stageFrameHom h j
        (sqArbFrame h nu' j (sigArbDress h (stageLegalDress h j)) i))) = 1 := by
  refine ⟨?_, ?_⟩
  · rw [← SqU6.toU5L_sqRelWord, sqRelWord_stageFrame_stageLegal hu hv]
    decide
  · rw [← SqU6.toU5R_sqRelWord, sqRelWord_stageFrame_stageLegal hu hv]
    decide

/-- ⭐⭐ **THE FULL CLASS-FIVE ESCAPE AT THE UNCONDITIONAL POINT.**  Same hom, same frame, same
row, both dressings `lambda`-trivial and `nu'`-trivial slotwise; the trivial dressing kills the
relator image and `[x1, v_j] * [x1, u_j]^{-1}` leaves the odd central residue `5`, which the
class-four machinery cannot see and which no achievable stage-four refinement can remove.  This
is `GradedFiveFrame.fiveFrame_escape_separates` at the new point, with the exclusion one
filtration step wider, and it needed a different word. -/
theorem stageFrame_escape_separates (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    ((∀ i, nuLam h (sigArbDress h (1 : (DSq h : Type)) i) = 1)
        ∧ ∀ i, nu' (sigArbDress h (1 : (DSq h : Type)) i) = 1)
      ∧ ((∀ i, nuLam h (sigArbDress h (stageLegalDress h j) i) = 1)
        ∧ ∀ i, nu' (sigArbDress h (stageLegalDress h j) i) = 1)
      ∧ sqRelWord (fun i => stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h 1) i)) = 1
      ∧ sqRelWord (fun i => stageFrameHom h j
          (sqArbFrame h nu' j (sigArbDress h (stageLegalDress h j)) i)) = SqU6.liftO 5 :=
  ⟨⟨nuLam_sigArbDress (map_one _), nu_sigArbDress (map_one _)⟩,
    ⟨nuLam_stage_sigArbDress_legal, nu_stage_sigArbDress_legal⟩,
    sqRelWord_stageFrame_triv hu hv, sqRelWord_stageFrame_stageLegal hu hv⟩

/-! ### ⭐ The wave-59 killing word at the new point: the composite check and the non-vacuity
witness

`GradedFiveFrame` exhibited its scope limit by an honest group element,
`fiveKillWord h j = [[sigma, u_j], x1]`, whose image at the OLD point is `<m = 5, n = 6>` and
which kills the `x0`-dressed frame outright.  The same element is examined here at the NEW
point, where the exclusion is supposed to hold against it.  Both files are right and the
composite is consistent: the element's image has moved to `<m = 2, n = 2, o = 4>`, which is
`gamma_3`-shaped with `j`, `l` and `m` even, so it is inside the class the exclusion quantifies
over and cannot kill.  It moves the residue from `1` to `7`, which makes it the non-vacuity
witness as well. -/

variable (h) in
/-- **The sigma-only stage-four dressing** of a frame: the sigma slot dressed by `w`, every
other slot standing.  `GradedFourHom.sigArbDress` in the carrier rather than in `D_sq h`. -/
def stageSigDress (w : SqU6 gr3R) : Fin (sqRank h) → SqU6 gr3R :=
  fun i => if (i : ℕ) = 0 then w else 1

@[simp] theorem stageSigDress_zero (w : SqU6 gr3R) : stageSigDress h w 0 = w := by
  simp only [stageSigDress, sqVal_zero]
  norm_num

theorem stageSigDress_ne {w : SqU6 gr3R} {i : Fin (sqRank h)} (hi : (i : ℕ) ≠ 0) :
    stageSigDress h w i = 1 := if_neg hi

theorem stageSigDress_mem_stageN3 {w : SqU6 gr3R} (hw : w ∈ stageN3) (i : Fin (sqRank h)) :
    stageSigDress h w i ∈ stageN3 := by
  by_cases h0 : (i : ℕ) = 0
  · rw [show i = 0 from Fin.val_injective (by rw [h0, sqVal_zero]), stageSigDress_zero]
    exact hw
  · rw [stageSigDress_ne h0]
    exact stageN3.one_mem

/-- **The stage-four shift of a sigma-only dressing** collapses to the core shift with the two
exponent slots undressed: the handle shifts vanish because both their dressings are trivial,
and the central collection term vanishes because it reads only the exponent slots' dressings. -/
theorem gaThreeShift_stageSigDress (m : Fin (sqRank h) → SqU6 gr3R) (w : SqU6 gr3R) :
    gaThreeShift h m (stageSigDress h w) = gaThreeCore (m 0) (m 1) (m 2) w 1 1 := by
  have hz1 : stageSigDress h w 1 = 1 := stageSigDress_ne (by rw [sqVal_one]; omega)
  have hz2 : stageSigDress h w 2 = 1 := stageSigDress_ne (by rw [sqVal_two]; omega)
  have hzU : ∀ k : Fin h, stageSigDress h w (sqHandleIdxU k) = 1 :=
    fun k => stageSigDress_ne (by rw [sqHandleIdxU_val]; omega)
  have hzV : ∀ k : Fin h, stageSigDress h w (sqHandleIdxV k) = 1 :=
    fun k => stageSigDress_ne (by rw [sqHandleIdxV_val]; omega)
  have hhm : ∀ p q : SqU6 gr3R, (gaThreeHandle p q 1 1).m = 0 := by
    intro p q
    simp only [gaThreeHandle, gaThreePairL, SqU6.one_j, SqU6.one_k]
    ring
  have hhn : ∀ p q : SqU6 gr3R, (gaThreeHandle p q 1 1).n = 0 := by
    intro p q
    simp only [gaThreeHandle, gaThreePairR, SqU6.one_k, SqU6.one_l]
    ring
  have hho : ∀ p q : SqU6 gr3R, (gaThreeHandle p q 1 1).o = 0 := by
    intro p q
    simp only [gaThreeHandle, gaThreePair, SqU6.one_j, SqU6.one_k, SqU6.one_l, SqU6.one_m,
      SqU6.one_n]
    ring
  rw [gaThreeShift, stageSigDress_zero, hz1, hz2]
  simp only [hzU, hzV, hhm, hhn, hho, Finset.sum_const_zero, SqU6.one_j, SqU6.one_l,
    mul_zero, add_zero, sub_zero]
  ext <;>
    simp only [SqU6.liftO, SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e,
      SqU6.mul_f, SqU6.mul_g, SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l,
      SqU6.mul_m, SqU6.mul_n, SqU6.mul_o, gaThreeCore] <;>
    ring

/-- **The relator under a sigma-only stage-four dressing**, at every handle count and every
handle. -/
theorem sqRelWord_stageSigDress {m : Fin (sqRank h) → SqU6 gr3R} {w : SqU6 gr3R}
    (hw : w.IsGaThree) :
    sqRelWord (conFiveDress m (stageSigDress h w))
      = sqRelWord m * gaThreeCore (m 0) (m 1) (m 2) w 1 1 := by
  have hz : ∀ i, (stageSigDress h w i).IsGaThree := by
    intro i
    by_cases h0 : (i : ℕ) = 0
    · rw [show i = 0 from Fin.val_injective (by rw [h0, sqVal_zero]), stageSigDress_zero]
      exact hw
    · rw [stageSigDress_ne h0]
      exact SqU6.isGaThree_one
  rw [sqRelWord_gaThreeDress hz, gaThreeShift_stageSigDress]

theorem stageFrameHom_fiveKillWord :
    stageFrameHom h j (fiveKillWord h j) = commP (commP (fiveSigMark gr3R) stageU) stageY := by
  rw [fiveKillWord, map_commP, map_commP, stageFrameHom_sigma, stageFrameHom_handleU,
    stageFrameHom_x1]

/-- ⭐ **The wave-59 killing word is an ACHIEVABLE stage-four dressing at the new point.**  Its
image is `<m = 2, n = 2, o = 4>`, which lies in `stageN3`: at wave 59's point the same word has
image `<m = 5, n = 6>` with an **odd** class-four coordinate and is outside the corresponding
lattice (`GradedFiveStageFour.fiveWit_gaThree_kill_not_stageN3`).  The single odd column of
wave 59's `U`-letter is the whole difference. -/
theorem stageFrameHom_fiveKillWord_mem_stageN3 :
    stageFrameHom h j (fiveKillWord h j) ∈ stageN3 := by
  rw [stageFrameHom_fiveKillWord, mem_stageN3]
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩⟩

/-- …so the sigma-only dressing by it lies slotwise in the class the exclusion quantifies over.
This is what makes the next theorem a non-vacuity statement rather than a remark. -/
theorem stageFrame_fiveKillWord_dressing_mem (i : Fin (sqRank h)) :
    stageSigDress h (stageFrameHom h j (fiveKillWord h j)) i ∈ stageN3 :=
  stageSigDress_mem_stageN3 stageFrameHom_fiveKillWord_mem_stageN3 i

/-- ⭐⭐ **THE COMPOSITE CHECK AND THE NON-VACUITY WITNESS IN ONE.**  Dressing the sigma slot of
the `x0`-dressed frame by the image of the wave-59 killing word moves the class-five residue
from `1` to `7`.  Two things follow.  The composite with `GradedFiveFrame` is consistent: the
element that kills at the old point cannot kill here, and it is inside the class this file's
exclusion quantifies over rather than outside it.  And the forcing is not vacuous: the
quantified class genuinely acts on the residue, and the content of the exclusion is that it
cannot reach `0`. -/
theorem stageFrame_fiveKillWord_no_kill (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    sqRelWord (conFiveDress
        (fun i => stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i))
        (stageSigDress h (stageFrameHom h j (fiveKillWord h j))))
      = SqU6.liftO 7 := by
  rw [stageFrameHom_sqArbFrame hu hv, stageFrameHom_x0,
    sqRelWord_stageSigDress (stageN3_isGaThree stageFrameHom_fiveKillWord_mem_stageN3),
    sqRelWord_stageWit_diag, stageWit_zero, stageWit_one, stageWit_two,
    stageFrameHom_fiveKillWord]
  ext <;>
    simp only [SqU6.liftO, SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e,
      SqU6.mul_f, SqU6.mul_g, SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l,
      SqU6.mul_m, SqU6.mul_n, SqU6.mul_o, gaThreeCore] <;>
    decide

set_option maxRecDepth 40000 in
/-- **Independent check of the two verdicts and of the non-vacuity move**, at one handle,
straight from `sqRelWord` by kernel computation, without going through `sqRelWord_fiveTuple` or
the translation identity of `GradedFiveStageFour` section 3.  Wave 57's process finding was
that two results of one wave can each be right while their composition is vacuous, so the
structural route and the machine route are made to meet here as well. -/
theorem stageFrame_decide_crosscheck :
    sqRelWord (stageWit 1 0 1) = 1
      ∧ sqRelWord (stageWit 1 0 stageX) = SqU6.liftO 1
      ∧ sqRelWord (conFiveDress (stageWit 1 0 stageX)
          (stageSigDress 1 (commP (commP (fiveSigMark gr3R) stageU) stageY))) = SqU6.liftO 7
      ∧ sqRelWord (stageWit 1 0 (commP stageY stageU))
          = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 5⟩ := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end Verdicts

/-! ## 6 The named cleared row `nuSel h j 0 0`

The row hypotheses `hu`, `hv` are discharged from the row itself at the committed cleared
selected marking, at every handle count and every handle.  Nothing else is carried: the
dressing's soundness columns were discharged for every element in section 2. -/

section ClearedRow

variable {h : ℕ} {j : Fin h}

/-- The frame identification at the cleared row. -/
theorem stageFrameHom_sqArbFrame_cleared (g : (DSq h : Type)) :
    (fun i => stageFrameHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h g) i))
      = stageWit h j (stageFrameHom h j g) :=
  stageFrameHom_sqArbFrame nuSelClr_handleU nuSelClr_handleV g

/-- ⭐⭐⭐ **The headline at the named row**: at every handle count, every handle, and the
committed cleared selected marking `nuSel h j 0 0`, every sigma dressing of the
arbitrary-dressing frame whose image is killed by any five-slot STAGE-FOUR refinement with
`j`, `l` and `m` even leaves an **even** class-five residue.  Nothing is carried: not the row
(it is the row), not the dressing's legality, and not the achievability convention. -/
theorem sqArbFrame_stage_sigma_forced_cleared (g : (DSq h : Type))
    {z : Fin (sqRank h) → SqU6 gr3R} (hz : ∀ i, z i ∈ stageN3)
    (hkill : sqRelWord (conFiveDress
      (fun i => stageFrameHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h g) i)) z) = 1) :
    selPar (sqRelWord fun i =>
      stageFrameHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h g) i)).o = 0 :=
  stageFrame_sigma_forced_sharp nuSelClr_handleU nuSelClr_handleV g hz hkill

/-- …and in the committed achievability convention. -/
theorem sqArbFrame_stage_sigma_forced_cleared_lattice (g : (DSq h : Type))
    {z : Fin (sqRank h) → SqU6 gr3R}
    (hz : ∀ i, z i ∈ forceLcs (stageImage h j (stageFrameHom h j g)) 2)
    (hkill : sqRelWord (conFiveDress
      (fun i => stageFrameHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h g) i)) z) = 1) :
    selPar (sqRelWord fun i =>
      stageFrameHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h g) i)).o = 0 :=
  stageFrame_sigma_forced nuSelClr_handleU nuSelClr_handleV g hz hkill

/-- ⭐⭐⭐ **THE EXCLUSION AT THE NAMED ROW, UNCONDITIONAL AND AT THE HOM LEVEL.**  This is the
statement the campaign's `h >= 1` endgame wants: an honest continuous homomorphism, an honest
frame of `D_sq h`, the committed cleared selected marking, and no achievable STAGE-FOUR
refinement whatsoever kills the relator image of the `x0`-dressed frame. -/
theorem sqArbFrame_stage_diag_ne_one_cleared
    {z : Fin (sqRank h) → SqU6 gr3R} (hz : ∀ i, z i ∈ stageN3) :
    sqRelWord (conFiveDress (fun i => stageFrameHom h j
      (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h (dsqX0 h)) i)) z) ≠ 1 :=
  sqRelWord_stageFrame_diag_ne_one_sharp nuSelClr_handleU nuSelClr_handleV hz

/-- …and in the committed achievability convention. -/
theorem sqArbFrame_stage_diag_ne_one_cleared_lattice
    {z : Fin (sqRank h) → SqU6 gr3R}
    (hz : ∀ i, z i ∈ forceLcs (stageImage h j (stageFrameHom h j (dsqX0 h))) 2) :
    sqRelWord (conFiveDress (fun i => stageFrameHom h j
      (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h (dsqX0 h)) i)) z) ≠ 1 :=
  sqRelWord_stageFrame_diag_ne_one nuSelClr_handleU nuSelClr_handleV hz

/-- The `x0`-dressing is `ν'`-trivial slotwise at the cleared row, so it lies in the class the
residual quantifies over. -/
theorem nu_stage_sigArbDress_x0_cleared (i : Fin (sqRank h)) :
    nuSel h j 0 0 (sigArbDress h (dsqX0 h) i) = 1 :=
  nu_sigArbDress (by rw [nuSel_x0, ofAdd_zero]) i

/-- ⭐⭐ **The verdicts at the named row**, with the `ν'`-legality of the `x0`-dressing and the
full `λ`- and `ν'`-legality of the two-commutator dressing exhibited: the trivial dressing
kills, the `x0`-dressing leaves the odd residue `1`, and the repaired legal dressing leaves the
odd central residue `5`. -/
theorem stageFrame_escape_separates_cleared :
    (∀ i, nuSel h j 0 0 (sigArbDress h (dsqX0 h) i) = 1)
      ∧ ((∀ i, nuLam h (sigArbDress h (stageLegalDress h j) i) = 1)
        ∧ ∀ i, nuSel h j 0 0 (sigArbDress h (stageLegalDress h j) i) = 1)
      ∧ sqRelWord (fun i =>
          stageFrameHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h 1) i)) = 1
      ∧ sqRelWord (fun i =>
          stageFrameHom h j
            (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h (dsqX0 h)) i)) = SqU6.liftO 1
      ∧ sqRelWord (fun i =>
          stageFrameHom h j
            (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h (stageLegalDress h j)) i))
          = SqU6.liftO 5 :=
  ⟨nu_stage_sigArbDress_x0_cleared,
    ⟨nuLam_stage_sigArbDress_legal, nu_stage_sigArbDress_legal⟩,
    sqRelWord_stageFrame_triv nuSelClr_handleU nuSelClr_handleV,
    sqRelWord_stageFrame_diag nuSelClr_handleU nuSelClr_handleV,
    sqRelWord_stageFrame_stageLegal nuSelClr_handleU nuSelClr_handleV⟩

/-- ⭐⭐ **The exclusion at the named row for the fully legal dressing too.**  Every hypothesis
is discharged: the row, the legality of the dressing, and the achievability convention. -/
theorem sqArbFrame_stage_legal_ne_one_cleared
    {z : Fin (sqRank h) → SqU6 gr3R} (hz : ∀ i, z i ∈ stageN3) :
    sqRelWord (conFiveDress (fun i => stageFrameHom h j
      (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h (stageLegalDress h j)) i)) z) ≠ 1 :=
  sqRelWord_stageFrame_stageLegal_ne_one nuSelClr_handleU nuSelClr_handleV hz

end ClearedRow

/-! ## 7 Axiom pins

Committed prints for every public declaration of this file: all **std-3** (`propext`,
`Classical.choice`, `Quot.sound`) or a subset; no census axiom is reachable, `sqPivotExp`
included.  Every `decide` is on `ZMod 8` or on `Fin`-indexed tuples over it; there is no
`native_decide`. -/

section AxiomPins

#print axioms stageWit_zero
#print axioms stageWit_one
#print axioms stageWit_two
#print axioms stageWit_handleU
#print axioms stageWit_handleV
#print axioms stageWit_handleU_ne
#print axioms stageWit_handleV_ne
#print axioms stageWit_of_ne_zero
#print axioms stageFrameHom
#print axioms stageFrameHom_gen
#print axioms stageFrameHom_sigma
#print axioms stageFrameHom_x0
#print axioms stageFrameHom_x1
#print axioms stageFrameHom_handleU
#print axioms stageFrameHom_handleV
#print axioms stageFrameHom_handle_ne
#print axioms stageX_flat
#print axioms stageX_zpowZtwo
#print axioms stageFrameHom_sqPivot
#print axioms stageFrameHom_sqPivot_ne_one
#print axioms stageFrameHom_mem_closure
#print axioms stageFrameHom_mem_stageN1
#print axioms stageFrameHom_columns_even
#print axioms forceLcs_stageFrameHom_le_stageN3
#print axioms stageFrameHom_sqArbFrame
#print axioms stageImage_eq_frame_closure
#print axioms stageFrameHom_sqArbBase_handleU_ne
#print axioms stageFrameHom_sqArbBase_handleV_ne
#print axioms stageWit_sigma_forced_sharp
#print axioms stageFrame_sigma_forced_sharp
#print axioms stageFrame_sigma_forced
#print axioms stageN1_le_forceN1
#print axioms stageWit_fiveOrth
#print axioms stageFrame_fiveForces_iff_fiveOrth
#print axioms sqRelWord_stageFrame_triv
#print axioms sqRelWord_stageFrame_triv_gate
#print axioms sqRelWord_stageFrame_diag
#print axioms sqRelWord_stageFrame_diag_ne_one_sharp
#print axioms sqRelWord_stageFrame_diag_ne_one
#print axioms stageFrame_bit_separates
#print axioms stageFrame_class_four_blind
#print axioms nuLam_stage_sigArbDress_x0_ne_one
#print axioms stageFrameHom_fiveLegalDress
#print axioms sqRelWord_stageWit_legal
#print axioms sqRelWord_stageFrame_legal
#print axioms sqRelWord_stageFrame_legal_ne_one
#print axioms stageFrame_legal_not_class_four_blind
#print axioms stageLegalDress
#print axioms stageLegalDress_char_triv
#print axioms nuLam_stage_sigArbDress_legal
#print axioms nu_stage_sigArbDress_legal
#print axioms stageFrameHom_stageLegalDress
#print axioms sqRelWord_stageWit_stageLegal
#print axioms sqRelWord_stageFrame_stageLegal
#print axioms sqRelWord_stageFrame_stageLegal_ne_one
#print axioms stageFrame_stageLegal_class_four_blind
#print axioms stageFrame_escape_separates
#print axioms stageSigDress
#print axioms stageSigDress_zero
#print axioms stageSigDress_ne
#print axioms stageSigDress_mem_stageN3
#print axioms gaThreeShift_stageSigDress
#print axioms sqRelWord_stageSigDress
#print axioms stageFrameHom_fiveKillWord
#print axioms stageFrameHom_fiveKillWord_mem_stageN3
#print axioms stageFrame_fiveKillWord_dressing_mem
#print axioms stageFrame_fiveKillWord_no_kill
#print axioms stageFrame_decide_crosscheck
#print axioms stageFrameHom_sqArbFrame_cleared
#print axioms sqArbFrame_stage_sigma_forced_cleared
#print axioms sqArbFrame_stage_sigma_forced_cleared_lattice
#print axioms sqArbFrame_stage_diag_ne_one_cleared
#print axioms sqArbFrame_stage_diag_ne_one_cleared_lattice
#print axioms nu_stage_sigArbDress_x0_cleared
#print axioms stageFrame_escape_separates_cleared
#print axioms sqArbFrame_stage_legal_ne_one_cleared

end AxiomPins

end SqCore

end Dyadic

end GQ2

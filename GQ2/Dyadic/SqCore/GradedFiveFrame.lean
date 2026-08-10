/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFiveForce
import GQ2.Dyadic.SqCore.GradedFourCleared

/-!
# W60-HOM5: the class-five sigma forcing as a statement about `sqArbFrame`

`GradedFiveForce` (wave 59) excluded the sigma dressing `a0 = a1` at class five, and closed with
its own price:

> Like `GradedFour`, `GradedLift` and `GradedSigmaFour`, this file works at the level of
> **marking tuples** in `SqU6 gr3R`: the hom layer of `GradedFive` is not consumed, so no
> statement here claims that a given tuple is the image of a continuous homomorphism on
> `D_sq h`.  Turning `fiveWit_sigma_forced` into a statement about `sqArbFrame` is the
> class-five transposition of `GradedFourCleared`, and it is not attempted here.

This file does that transposition, at **every** handle count and **every** handle.

## ⭐⭐ Headline: the class-five exclusion is now a statement about `sqArbFrame`

`sqRelWord_fiveFrame_diag_ne_one`, and at the named cleared row
`sqArbFrame_five_sigma_forced_cleared`.  At every handle count `h`, at every handle `j`, at the
honest continuous homomorphism `fiveFrameHom h j : D_sq h -> U_6(Z/8)` built by the committed
class-five lift from `GradedFiveForce`'s binder point: **every sigma dressing of the
arbitrary-dressing frame whose image is killed by any achievable five-slot class-five refinement
leaves an even class-five residue**, and the dressing by the `x0`-generator leaves the odd
residue `7`, so no achievable refinement kills it.  The three verdicts are executed on the frame
itself:

```text
a0 = 1          relator image dies outright      sqRelWord_fiveFrame_triv[_gate]
a0 = x0         residue 7, survives everything   sqRelWord_fiveFrame_diag[_ne_one]
a0 = x0         both U_5-quotients trivial       fiveFrame_class_four_blind
a0 = [x1, u_j]  residue 5, survives everything   sqRelWord_fiveFrame_legal[_ne_one]
a0 = [x1, u_j]  both U_5-quotients trivial       fiveFrame_legal_class_four_blind
```

and the two routes to the first line are made to meet: `sqRelWord_fiveFrame_triv` reads it off
the binder point's fifteen-row `decide`, `sqRelWord_fiveFrame_triv_gate` gets it from the
class-five gate `sqU6Balance_gen` without touching the point at all.

## ⚠ An honesty point, and the repair: the `x0`-dressing is not `lambda`-trivial

`ArbFrames` asks the dressings of `sqArbFrame` to lie in `ker lambda ∩ ker nu'`.  The dressing
wave 59 excluded is the `x0`-generator, and `nuLam h (x0) = ofAdd 1`, so it is `nu'`-trivial
(`nu_sigArbDress_x0_cleared`) and **not** `lambda`-trivial
(⚠ `nuLam_sigArbDress_x0_ne_one`).  No other choice of `g` repairs it, by the following argument
(recorded here, not formalised): at the cleared row all three of `lambda`, `nu'` and the
`e`-column of `Phi` are characters, with `e`-column values `(0, 1, 2, 0, 2)` on
`(sigma, x0, x1, u_j, v_j)`, `lambda` values `(c, 1, 2, 0, 0)` with `c` a unit, and `nu'` values
`(1, 0, 0, 0, 0)`.  Modulo two the `e`-column is therefore `lambda + nu'`, so `lambda(g) = 0`
and `nu'(g) = 0` force `(Phi g).e` even, against `forceX.e = 1`.  So the exclusion at `a0 = x0`
is a statement about a `nu'`-trivial dressing only, and this file says so instead of claiming
the full legality.

⭐⭐ The repair is a **fully legal** dressing with the same three properties, and it is a
commutator, hence in the kernel of every character: `fiveLegalDress h j = [x1, u_j]`.  Its
image `commP forceY forceU` leaves the relator image the purely central, **odd** value
`liftC6 5`, so the class-four machinery is blind to it and nothing in the sharp class kills it.
`fiveFrame_escape_separates` therefore exhibits the full class-four-style escape at class five,
with `lambda`- and `nu'`-triviality of both dressings proved.

**Two hypotheses that class four carried are gone, and the survival bound is not merely
sharpened but CHARACTERISED.**

* ⭐ **The dressing legality is discharged for EVERY dressing, not just the legal ones.**
  `GradedFourHom` and `GradedFourCleared` carry `hgb : (Phi g).b = 0`, the class-four form of
  "the dressing is `nu'`-trivial", and discharge it at the selected row through the `b`-column
  identification.  The class-five soundness hypothesis is instead `v.c` **even**, and
  `fiveFrameHom_c_even` proves it for **every** `g : D_sq h` with no row hypothesis at all: the
  `(3,4)`-column is a character, `forceU` is the only letter with a non-zero one and it is `2`,
  so the whole image lies in `forceN1`.  There is no class-five analogue of the `b`-column side
  condition to carry.
* ⭐⭐ **The sharp class-five soundness line at this point, in BOTH directions.**  The five-slot
  increment here is
  ```text
  z0.m - 2 z0.n - 4 w1.o + 2 w2.o + 2 z3.m + z4.n
  ```
  because the sigma dressing pairs against `forceX = <a = 2, e = 1>`, the handle-`u` dressing
  against `forceV` (whose `a`-column vanishes and whose `e`-column is `2`) and the handle-`v`
  dressing against `forceU = <a = 1, e = 0>`.  Modulo two that is `z0.m + z4.n`, so of the six
  class-four coordinates of a five-slot refinement only **one parity** is load-bearing:

  ```text
  fiveFrame_sigma_forced_sharp   selPar (z0.m + z4.n) = 0  =>  no refinement kills
  fiveFrame_odd_sum_kill         selPar (z0.m + z4.n) = 1  =>  an explicit central one does
  ```

  The handle-`u` dressing `z3` is **entirely unconstrained**, as are `z0.n` and `z4.m`.  The
  line is genuinely about the **sum**: ⭐⭐ `fiveFrame_both_odd_no_kill` shows that the two
  individually-killing moves `z0 = <m = 1>` (`GradedFiveForce.fiveWit_unrestricted_kill`) and
  `z4 = <n = 1>` (`fiveFrame_handleV_odd_kill`, new here) leave the residue `1` when applied
  **together**, so no conjunction of per-slot conditions is the sharp line.  Wave 59's cross-lane
  check asked for exactly this, on the strength of the class-four precedent that the carried
  hypothesis is strictly stronger than the sharp line; here the class-five line is not merely
  weaker than what is carried but a characterisation.  This class strictly contains
  `forceN4^3`, so by doctrine the survival statement is stated against it, and the `forceN4` and
  achievable-lattice forms are corollaries.
* ⭐ **The achievable lattice is exactly `forceN4`.**  Measured
  (`scripts/w60_hom5/results/verify_frame5.txt` section B): the letterwise triple commutators of
  the point already generate the whole of `forceN4`, and the committed
  `forceLcs_three_le_forceN4` is the other inclusion, so `gamma_4` of the image **is** `forceN4`
  and `fiveFrame_sigma_forced` (the committed convention) loses nothing to
  `fiveFrame_sigma_forced_gaFour`.

## ⚠ The row type is FORCED, and this file certifies that rather than asserting it

Wave 54's honest cost repeats verbatim one class up.  `fiveWit`'s handle slots are the **raw**
generator images `forceU`, `forceV`, so the frame identification `fiveFrameHom_sqArbFrame`
needs `nu'(u_j) = nu'(v_j) = 1`: the reachable row is the one **cleared at the selected
handle**.  This is not a convenience, and the certificate is explicit:

* ⭐ `fiveFrameHom_sqPivot`, the class-five pivot anchor: `Phi(w) = <a = -2c, b = 1, e = -c>`
  with `c = gr3Pi sqPivotExp`.  ⭐ Unlike class four this is **mechanical**: all ten
  obstructions of `SqU6.zpowZtwo_of_flat` vanish at the binder point's `x0`-slot `forceX`
  (`forceX_flat`), where `GradedFourHom` needed the even-obstruction lemma because its
  `x0`-slot had `a * i = 2`.  The one non-mechanical step of the class-four transposition is
  not present at class five.
* ⭐⭐ `fiveFrameHom_sqArbBase_handleU_ne` and `..._handleV_ne`: at **any** row bumping the
  selected handle by `1` the frame's `U`-slot image is **provably not** `forceU` and its
  `V`-slot image is **provably not** `forceV`, because `Phi(w) != 1` (its `b`-coordinate is
  `1`).  So the frame identification cannot hold at a bumped row, and reaching one is a fresh
  class-five solve at a displaced binder point, exactly as wave 55 needed at class four.

What is **not** constrained is the other handles: `sqArbBase` displaces the `j`-th handle pair
only, so `nu'` is arbitrary away from `j` and the statements are proved for an arbitrary
continuous `nu'` with the two values at `j` cleared.  At `h = 1` that is the whole row; at
`h >= 2` it is strictly weaker than "the row is cleared".

## ⚠⚠ The scope limit is inherited, and stated at the hom level

`GradedFiveForce`'s exclusion is against **stage-five** refinements and is **false one
filtration step wider**.  Nothing here strengthens that, and the transport makes the wider
killing dressing *more* concrete rather than less: ⭐⭐ `sqRelWord_fiveFrame_gaThree_kill`
exhibits it as `Phi` of the honest group element

```text
fiveKillWord h j = commP (commP sigma u_j) x1  in  D_sq h ,
```

a triple commutator of the frame's **own generators**, whose image `<m = 5, n = 6>` is
`gamma_4`-shaped with an odd class-four coordinate; it lies in `gamma_3` of the image
(`fiveFrameHom_fiveKillWord_mem`), not in `forceN4`
(`fiveFrameHom_fiveKillWord_not_gaFour`), and it kills the `x0`-dressed frame outright.  Every
theorem below whose conclusion is a survival is therefore scoped to `forceN4`-dressings, and no
statement in this file claims otherwise.

## Non-vacuity

⭐ `fiveFrame_forcing_nonvacuous`: `fiveMoveWord h j = commP (commP (commP v_j u_j) x0) sigma`
is another honest group element whose image `<n = 2>` **is** achievable (it lies in `forceN4`
and in `gamma_4` of the image), and dressing the sigma slot by it moves the class-five residue
from `7` to `3`.  So the forcing quantifies over a class that genuinely acts on the residue and
still cannot reach `0`; it is not a statement about the trivial dressing.

## PROVED versus MEASURED

**PROVED** (this file, no `sorry`, no new axiom, no `native_decide`): everything above, at every
handle count and every handle, for an arbitrary continuous `nu'` cleared at the selected handle.

**MEASURED** (`scripts/w60_hom5/`, certified output in `results/verify_frame5.txt`; 55 named
checks, 0 failures, on an independently re-implemented `U_6(Z/8)`):

* that `gamma_4` of the image is **exactly** `forceN4`, so the `forceN4`-level quantifier is
  sharp and not a widening by fiat (the letterwise triple commutators generate all `128`);
* the exclusion over the **whole** of `forceN4` and both central slots, `262144` combinations,
  zero kills, plus `4000` honest refinements against the translation identity and `4000`
  against an honest kill search;
* the **characterisation** of section G in both directions: `262144` combinations with even sum,
  zero kills; every odd-sum triple killed by some central move, no exceptions; `4000` honest
  even-sum refinements; the two necessity witnesses, the both-odd witness, and the four
  unconstrained-coordinate witnesses;
* the legal dressing of section H: the central odd residue `5`, `262144` even-sum refinements
  with zero kills, and that `[x1, u_j]` is the **unique** letterwise commutator dressing with a
  central odd relator;
* the pivot anchor and the displacement at all four possible pivot residues;
* the evenness of the `(3,4)`-column on `20000` random words in the letters.

## Contents

* **1** the class-five binder hom `fiveFrameHom`, its letter values and its pivot anchor;
* **2** the image, the even `(3,4)`-column, and the automatic legality;
* **3** the frame identification, and the certificate that the row type is forced;
* **4** ⭐⭐ the forcing on `sqArbFrame`, in the sharp form, the `forceN4` form and the
  achievable-lattice form;
* **5** the verdicts, the gate cross-check, the blindness, ⭐⭐ the converse that makes the sharp
  form a characterisation, the scope limit, the necessity witnesses and the non-vacuity witness;
* **6** the named cleared row `nuSel h j 0 0`;
* **7** axiom pins.

## Axiom hygiene

All committed prints are **std-3** (`propext`, `Classical.choice`, `Quot.sound`) or a subset;
no census axiom is reachable, `sqPivotExp` included.  Every `decide` is on `ZMod 8` or on
`Fin`-indexed tuples over it.

## Merge notes

Nothing is redefined.  `SqU6.IsGaFour` comes from `GradedFiveDefect` through `GradedFiveForce`;
`forceN1`, `forceN4`, `forceLcs`, `forceImage`, `fiveWit`, `fiveLift` and the whole soundness
chain come from `GradedFiveForce`; `sigArbDress`, `sqArbBase_of_cleared`, `sqEichU_of_cleared`,
`nuLam_sigArbDress`, `nu_sigArbDress` come from `GradedFourHom` (they are statements about
`D_sq h`, carrier-independent, and are imported rather than transposed); `nuSelClr_handleU`,
`nuSelClr_handleV` come from `GradedFourCleared`.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The class-five binder point as a continuous homomorphism -/

section FrameHom

variable {h : ℕ} {j : Fin h}

/-- The class-five test group over `ℤ/8` is pro-2. -/
theorem isProP_two_gr6 : IsProP 2 (SqU6 gr3R) := SqU6.isProP_two gr3R_card

/-- The `sigma`-slot value of the binder point at dressing `v`. -/
@[simp] theorem fiveWit_zero (v : SqU6 gr3R) : fiveWit h j v 0 = fiveSigMark gr3R * v := by
  rw [fiveWit, fiveTuple_zero]

/-- The `x0`-slot value. -/
@[simp] theorem fiveWit_one (v : SqU6 gr3R) : fiveWit h j v 1 = forceX := by
  rw [fiveWit, fiveTuple_one]

/-- The `x1`-slot value. -/
@[simp] theorem fiveWit_two (v : SqU6 gr3R) : fiveWit h j v 2 = forceY := by
  rw [fiveWit, fiveTuple_two]

/-- The live handle's `u`-slot value. -/
@[simp] theorem fiveWit_handleU (v : SqU6 gr3R) :
    fiveWit h j v (sqHandleIdxU j) = forceU := by
  rw [fiveWit, fiveTuple_handleU]

/-- The live handle's `v`-slot value. -/
@[simp] theorem fiveWit_handleV (v : SqU6 gr3R) :
    fiveWit h j v (sqHandleIdxV j) = forceV := by
  rw [fiveWit, fiveTuple_handleV]

/-- Every other handle slot is trivial. -/
theorem fiveWit_handleU_ne (v : SqU6 gr3R) {j' : Fin h} (hne : j' ≠ j) :
    fiveWit h j v (sqHandleIdxU j') = 1 := by
  rw [fiveWit, fiveTuple_handleU_ne hne]

/-- …and likewise on the `v`-side. -/
theorem fiveWit_handleV_ne (v : SqU6 gr3R) {j' : Fin h} (hne : j' ≠ j) :
    fiveWit h j v (sqHandleIdxV j') = 1 := by
  rw [fiveWit, fiveTuple_handleV_ne hne]

/-- **Only the sigma slot sees the dressing.**  This is what makes the sigma-only dressing of
the frame land on the binder point at the dressed value. -/
theorem fiveWit_of_ne_zero {v : SqU6 gr3R} {i : Fin (sqRank h)} (hi : (i : ℕ) ≠ 0) :
    fiveWit h j v i = fiveWit h j 1 i := by
  simp only [fiveWit, fiveTuple]
  rw [if_neg hi, if_neg hi]

variable (h j) in
/-- ⭐ **The class-five binder hom.**  `GradedFiveForce`'s binder point kills the relator at
every handle count and every handle (`sqRelWord_fiveWit_triv`), so the committed class-five lift
turns it into an honest continuous homomorphism `D_sq h → U_6(ℤ/8)`.  Every tuple statement of
`GradedFiveForce` at that point is now a statement about this hom.  `GradedFourCleared`'s
`clrFourHom` one class up. -/
noncomputable def fiveFrameHom : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R) :=
  sqU6Hom gr3R_card h (fiveWit h j 1) (sqRelWord_fiveWit_triv h j)

@[simp] theorem fiveFrameHom_gen (i : Fin (sqRank h)) :
    fiveFrameHom h j (sqGen h i) = fiveWit h j 1 i := sqU6Hom_gen _ _ _ i

@[simp] theorem fiveFrameHom_sigma : fiveFrameHom h j (dsqSigma h) = fiveSigMark gr3R := by
  rw [dsqSigma, fiveFrameHom_gen, fiveWit_zero, mul_one]

/-- ⭐ **The `x0`-generator maps to the dressing the exclusion is about.**  The sigma dressing
`a0 = a1` of `GradedSigmaFour` section 7 is, at the hom level, the dressing by the `x0`
generator itself. -/
@[simp] theorem fiveFrameHom_x0 : fiveFrameHom h j (dsqX0 h) = forceX := by
  rw [dsqX0, fiveFrameHom_gen, fiveWit_one]

@[simp] theorem fiveFrameHom_x1 : fiveFrameHom h j (dsqX1 h) = forceY := by
  rw [dsqX1, fiveFrameHom_gen, fiveWit_two]

@[simp] theorem fiveFrameHom_handleU :
    fiveFrameHom h j (sqGen h (sqHandleIdxU j)) = forceU := by
  rw [fiveFrameHom_gen, fiveWit_handleU]

@[simp] theorem fiveFrameHom_handleV :
    fiveFrameHom h j (sqGen h (sqHandleIdxV j)) = forceV := by
  rw [fiveFrameHom_gen, fiveWit_handleV]

theorem fiveFrameHom_handle_ne {j' : Fin h} (hne : j' ≠ j) :
    fiveFrameHom h j (sqGen h (sqHandleIdxU j')) = 1 ∧
      fiveFrameHom h j (sqGen h (sqHandleIdxV j')) = 1 :=
  ⟨by rw [fiveFrameHom_gen, fiveWit_handleU_ne _ hne],
    by rw [fiveFrameHom_gen, fiveWit_handleV_ne _ hne]⟩

/-! ### The pivot anchor, and why it is mechanical here

`GradedFourHom`'s scope note called the pivot the one step of the class-four transposition that
is **not** mechanical: the class-four `x0`-slot `sigFourX` has `a * i = 2`, so the flat power
lemma does not apply and the even-obstruction lemma had to be built.  At class five the binder
point's `x0`-slot is `forceX = <a = 2, e = 1>`, and **all ten** obstructions of
`SqU6.zpowZtwo_of_flat` vanish there, so the anchor is two rewrites. -/

/-- ⭐ **All ten flat obstructions vanish at the binder point's `x0`-slot.**  Certified
independently in `scripts/w60_hom5/results/verify_frame5.txt` section F. -/
theorem forceX_flat :
    forceX.a * forceX.b = 0 ∧ forceX.b * forceX.c = 0 ∧ forceX.c * forceX.d = 0
      ∧ forceX.d * forceX.e = 0 ∧ forceX.a * forceX.g + forceX.f * forceX.c = 0
      ∧ forceX.b * forceX.h + forceX.g * forceX.d = 0
      ∧ forceX.c * forceX.i + forceX.h * forceX.e = 0
      ∧ forceX.a * forceX.k + forceX.f * forceX.h + forceX.j * forceX.d = 0
      ∧ forceX.b * forceX.l + forceX.g * forceX.i + forceX.k * forceX.e = 0
      ∧ forceX.a * forceX.n + forceX.f * forceX.l + forceX.j * forceX.i
          + forceX.m * forceX.e = 0 := by decide

/-- ⭐ **The `x0`-slot's `ℤ₂`-powers at the binder point**, through the *flat* power lemma:
the powering is `R`-linear in all fifteen coordinates, with no quadratic correction of the kind
class four's pivot needed. -/
theorem forceX_zpowZtwo (u : ℤ_[2]) :
    zpowZtwo isProP_two_gr6 forceX u
      = ⟨2 * gr3Pi u, 0, 0, 0, gr3Pi u, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := by
  rw [SqU6.zpowZtwo_of_flat isProP_two_gr6 gr3Pi gr3Pi_open (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  ext <;> simp [forceX]
  ring

/-- ⭐ **The pivot image at the binder hom**, in closed form: the `sqPivotExp`-dependence
returns only through the residue `c = gr3Pi sqPivotExp`, and there is no quadratic layer.
`GradedFourCleared.clrFourHom_sqPivot` one class up. -/
theorem fiveFrameHom_sqPivot :
    fiveFrameHom h j (sqPivot h)
      = ⟨-(2 * gr3Pi sqPivotExp), 1, 0, 0, -gr3Pi sqPivotExp,
          0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := by
  rw [sqPivot, sqMixPivotElem, map_mul, map_inv,
    map_zpowZtwo (isProP_DSq h) isProP_two_gr6, fiveFrameHom_x0, forceX_zpowZtwo,
    fiveFrameHom_sigma]
  ext <;> simp [fiveSigMark]

/-- ⭐ **The pivot image is non-trivial**, and its `b`-coordinate is `1` whatever the pivot
residue is.  This is what makes the row type forced rather than chosen. -/
theorem fiveFrameHom_sqPivot_ne_one : fiveFrameHom h j (sqPivot h) ≠ 1 := by
  intro hc
  have hb : (1 : gr3R) = 0 := by
    have hbb := congrArg SqU6.b hc
    rwa [fiveFrameHom_sqPivot, SqU6.one_b] at hbb
  exact absurd hb (by decide)

end FrameHom

/-! ## 2 The image, the even `(3,4)`-column, and the automatic legality -/

section Image

variable {h : ℕ} {j : Fin h}

/-- **The image of the binder hom lies in the closure of the marking.**  The transposition of
`GradedFourCleared.clrFourHom_mem_closure`: the generators land in the closure, the preimage of
a subgroup of a discrete group is closed, and `D_sq h` is topologically generated. -/
theorem fiveFrameHom_mem_closure (x : (DSq h : Type)) :
    fiveFrameHom h j x ∈ forceImage h j 1 := by
  have hgen : Subgroup.closure (Set.range (sqGen h))
      ≤ Subgroup.comap (fiveFrameHom h j).toMonoidHom (forceImage h j 1) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    show fiveFrameHom h j (sqGen h i) ∈ forceImage h j 1
    rw [fiveFrameHom_gen]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hclosed : IsClosed ((Subgroup.comap (fiveFrameHom h j).toMonoidHom
      (forceImage h j 1) : Subgroup (DSq h : Type)) : Set (DSq h : Type)) := by
    have hpre : ((Subgroup.comap (fiveFrameHom h j).toMonoidHom
        (forceImage h j 1) : Subgroup (DSq h : Type)) : Set (DSq h : Type))
        = fiveFrameHom h j ⁻¹' ((forceImage h j 1) : Set (SqU6 gr3R)) := rfl
    rw [hpre]
    exact (isClosed_discrete _).preimage (fiveFrameHom h j).continuous_toFun
  have hle := Subgroup.topologicalClosure_minimal _ hgen hclosed
  rw [dsq_topGen h] at hle
  exact hle (Subgroup.mem_top x)

/-- ⭐⭐ **Legality is automatic at class five.**  Every value of the binder hom has an **even**
`(3,4)`-column, with no hypothesis on the element at all.  This is the class-five replacement
for `GradedFourHom`'s `b`-column identification: at class four the soundness hypothesis is
"`(Phi g).b = 0`", a genuine constraint that has to be read off the selected row; at class five
it is "`(Phi g).c` is even", and `forceU` is the only letter with a non-zero `(3,4)`-column and
it is `2`, so the constraint is empty. -/
theorem fiveFrameHom_c_even (x : (DSq h : Type)) : ∃ t : gr3R, (fiveFrameHom h j x).c = 2 * t :=
  mem_forceN1.mp (forceImage_le_forceN1 (h := h) (j := j) ⟨0, by decide⟩
    (fiveFrameHom_mem_closure x))

/-- …in subgroup form: the whole image lies in `forceN1`, the single input the soundness chain
of `GradedFiveForce` section 5 consumes. -/
theorem fiveFrameHom_mem_forceN1 (x : (DSq h : Type)) : fiveFrameHom h j x ∈ forceN1 :=
  fiveFrameHom_c_even x

/-- ⭐ **The achievable lattice at any dressed image point is sound.**  Combining the two: at
the binder point dressed by the image of **any** group element, every achievable
`gamma_4`-dressing is `gamma_4`-shaped with even class-four coordinates. -/
theorem forceLcs_fiveFrameHom_le_forceN4 (g : (DSq h : Type)) :
    forceLcs (forceImage h j (fiveFrameHom h j g)) 3 ≤ forceN4 :=
  forceLcs_three_le_forceN4 (forceImage_le_forceN1 (fiveFrameHom_c_even g))

end Image

/-! ## 3 The frame identification, and the certificate that the row type is forced -/

section Frame

variable {h : ℕ} {j : Fin h}
variable {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- ⭐⭐ **The frame identification at class five**: at a row cleared at the selected handle,
the binder hom sends the arbitrary-dressing frame with a sigma-only dressing `g` to exactly the
class-five binder point at the dressing value `fiveFrameHom h j g`.
`GradedFourCleared.clrFourHom_sqArbFrame` one class up, and it is what makes every tuple verdict
of `GradedFiveForce` a verdict about `sqArbFrame`. -/
theorem fiveFrameHom_sqArbFrame (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) (g : (DSq h : Type)) :
    (fun i => fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i))
      = fiveWit h j (fiveFrameHom h j g) := by
  funext i
  by_cases h0 : (i : ℕ) = 0
  · have hi : i = 0 := Fin.val_injective (by rw [h0, sqVal_zero])
    subst hi
    rw [sqArbFrame, sqArbBase_of_cleared hu hv, sigArbDress_zero, map_mul, fiveFrameHom_gen,
      fiveWit_zero, fiveWit_zero, mul_one]
  · rw [sqArbFrame, sqArbBase_of_cleared hu hv, sigArbDress_ne h0, mul_one, fiveFrameHom_gen,
      fiveWit_of_ne_zero (v := fiveFrameHom h j g) h0]

/-- The achievable lattice of the frame's image **is** the achievable lattice of the binder
point at the dressed value: the two conventions agree on the nose. -/
theorem forceImage_eq_frame_closure (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) (g : (DSq h : Type)) :
    Subgroup.closure (Set.range fun i =>
        fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i))
      = forceImage h j (fiveFrameHom h j g) := by
  rw [fiveFrameHom_sqArbFrame hu hv g]
  rfl

/-! ### ⚠ The reachable row type, and the certificate that it is forced

`fiveWit`'s handle slots are the raw generator images, so the frame identification above cannot
survive a pivot power in either handle slot.  The two statements below say so with a proof
rather than an appeal to shape: at any row bumping the selected handle by `1`, the frame's
handle-slot images are **provably different** from the binder point's letters, so no frame over
such a row has `fiveWit`-shaped image and the committed forcing does not reach it.  Reaching a
bumped row at class five is a fresh fifteen-row solve at the displaced binder point, which is
the class-five form of the gap wave 55 had to close at class four. -/

/-- ⚠⚠ **The `u`-slot is displaced at a bumped row.**  At `nu'(u_j) = 1` the frame's `u`-slot
image is `Phi(w)⁻¹ · forceU`, and it is not `forceU`, because the pivot image is non-trivial. -/
theorem fiveFrameHom_sqArbBase_handleU_ne
    (hu : nu' (sqGen h (sqHandleIdxU j)) = ofAdd (1 : ℤ_[2])) (v : SqU6 gr3R) :
    fiveFrameHom h j (sqArbBase h nu' j (sqHandleIdxU j)) ≠ fiveWit h j v (sqHandleIdxU j) := by
  rw [sqArbBase_handleU, sqEichU, hu, toAdd_ofAdd, zpowZtwo_one_exp, map_mul, map_inv,
    fiveFrameHom_handleU, fiveWit_handleU]
  intro hc
  refine fiveFrameHom_sqPivot_ne_one (h := h) (j := j) ?_
  have h1 : (fiveFrameHom h j (sqPivot h))⁻¹ * forceU = 1 * forceU := by rw [hc, one_mul]
  rw [← inv_eq_one]
  exact mul_right_cancel h1

/-- ⚠⚠ …and the `v`-slot likewise. -/
theorem fiveFrameHom_sqArbBase_handleV_ne
    (hv : nu' (sqGen h (sqHandleIdxV j)) = ofAdd (1 : ℤ_[2])) (v : SqU6 gr3R) :
    fiveFrameHom h j (sqArbBase h nu' j (sqHandleIdxV j)) ≠ fiveWit h j v (sqHandleIdxV j) := by
  rw [sqArbBase_handleV, sqEichV, hv, toAdd_ofAdd, zpowZtwo_one_exp, map_mul, map_inv,
    fiveFrameHom_handleV, fiveWit_handleV]
  intro hc
  refine fiveFrameHom_sqPivot_ne_one (h := h) (j := j) ?_
  have h1 : forceV * (fiveFrameHom h j (sqPivot h))⁻¹ = forceV * 1 := by rw [hc, mul_one]
  rw [← inv_eq_one]
  exact mul_left_cancel h1

end Frame

/-! ## 4 The forcing on `sqArbFrame` -/

section Forcing

variable {h : ℕ} {j : Fin h}
variable {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- Reading the class-five residue off a killed frame.  (`GradedFiveForce`'s copy is `private`,
so this one is rebuilt here.) -/
private theorem o_of_mul_liftC6_eq_one' {p : SqU6 gr3R} {w : gr3R} (hp : p * liftC6 w = 1) :
    p.o = -w := by
  have hq := congrArg SqU6.o hp
  rw [mul_liftC6_apply] at hq
  simp only [SqU6.one_o] at hq
  exact eq_neg_of_add_eq_zero_left hq

/-- ⭐⭐ **The class-five selection bit, forced by the two coordinates that actually carry it.**

This is the sharpest form the tree owns, and it is strictly sharper than the committed
statement in two independent ways.

* No lattice and no `nu'`-legality.  `GradedFiveForce.fiveWit_sigma_forced` asks the three
  `gamma_4`-dressings to be **achievable** and the sigma dressing to have an even
  `(3,4)`-column; here nothing is asked of the dressing, and the refinements are asked only to
  be `gamma_4`-shaped.
* Only **one parity** out of the six class-four coordinates of a five-slot refinement is
  load-bearing at this point, and this statement asks for exactly it.  The five-slot increment
  is `z0.m - 2 z0.n - 4 w1.o + 2 w2.o + 2 z3.m + z4.n`, because the sigma slot pairs against
  `forceX = <a = 2, e = 1>`, the handle-`u` dressing against `forceV` (whose `a`-column vanishes
  and whose `e`-column is `2`) and the handle-`v` dressing against `forceU = <a = 1, e = 0>`.
  Modulo two the increment is `z0.m + z4.n`, so the whole handle-`u` dressing `z3` is
  **unconstrained**, `z0.n` and `z4.m` are **unconstrained**, and the single hypothesis is that
  the **sum** `z0.m + z4.n` is even.

The hypothesis is exactly sharp, by `fiveFrame_odd_sum_kill`: whenever the sum is **odd** a
central refinement kills.  It is not the conjunction of two evennesses:
`GradedFiveForce.fiveWit_unrestricted_kill` kills with `z0 = <m = 1>` and
`fiveFrame_handleV_odd_kill` kills with `z4 = <n = 1>`, but ⭐⭐ `fiveFrame_both_odd_no_kill`
shows that **both together** do not kill.  Certified in
`scripts/w60_hom5/results/verify_frame5.txt` section G. -/
theorem fiveWit_sigma_forced_sharp {v z₀ w₁ w₂ z₃ z₄ : SqU6 gr3R}
    (hz₀ : z₀.IsGaFour) (hw₁ : w₁.IsGaFive) (hw₂ : w₂.IsGaFive)
    (hz₃ : z₃.IsGaFour) (hz₄ : z₄.IsGaFour) (hsum : selPar (z₀.m + z₄.n) = 0)
    (hkill : sqRelWord (fiveLift j (fiveWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (sqRelWord (fiveWit h j v)).o = 0 := by
  obtain ⟨t, ht⟩ := (selPar_eq_zero_iff _).mp hsum
  rw [sqRelWord_fiveLift hz₀ hw₁ hw₂ hz₃ hz₄] at hkill
  have heven : (sqRelWord (fiveWit h j v)).o
      = 2 * (-(t - z₀.n - 2 * w₁.o + w₂.o + z₃.m)) := by
    rw [o_of_mul_liftC6_eq_one' hkill, fiveWit_one, fiveWit_handleU, fiveWit_handleV]
    simp only [forceX, forceU, forceV]
    linear_combination -ht
  rw [heven, selPar_two_mul]

/-- The sum of two even residues is even: the bridge from the achievable lattice to the sharp
hypothesis. -/
private theorem selPar_add_eq_zero_of_even {x y : gr3R} (hx : ∃ t : gr3R, x = 2 * t)
    (hy : ∃ t : gr3R, y = 2 * t) : selPar (x + y) = 0 := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  rw [ha, hb, ← mul_add, selPar_two_mul]

/-- ⭐ **The same forcing against the achievable `gamma_4`-lattice `forceN4`.**  Every dressing
in `forceN4` has both class-four coordinates even, so their sum is even and this is a corollary.
Measured: `gamma_4` of the image at the point **is** `forceN4`
(`scripts/w60_hom5/results/verify_frame5.txt` section B), so this form covers exactly the
achievable refinements. -/
theorem fiveWit_sigma_forced_gaFour {v z₀ w₁ w₂ z₃ z₄ : SqU6 gr3R}
    (hz₀ : z₀ ∈ forceN4) (hw₁ : w₁.IsGaFive) (hw₂ : w₂.IsGaFive)
    (hz₃ : z₃ ∈ forceN4) (hz₄ : z₄ ∈ forceN4)
    (hkill : sqRelWord (fiveLift j (fiveWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (sqRelWord (fiveWit h j v)).o = 0 :=
  fiveWit_sigma_forced_sharp (forceN4_isGaFour hz₀) hw₁ hw₂ (forceN4_isGaFour hz₃)
    (forceN4_isGaFour hz₄)
    (selPar_add_eq_zero_of_even (forceN4_even hz₀).1 (forceN4_even hz₄).2) hkill

/-- ⭐⭐ **THE HEADLINE: the class-five sigma forcing on `sqArbFrame` itself.**  At every handle
count and every handle, at any continuous `nu'` cleared at the selected handle, a sigma dressing
of the arbitrary-dressing frame whose image is killed by **any** five-slot class-five refinement
whose two load-bearing coordinates are even leaves an **even** class-five residue.  This is
`GradedFiveForce.fiveWit_sigma_forced` transported through the class-five gate: the hypothesis
is now about an honest frame of `D_sq h` and an honest continuous homomorphism, not about a
tuple.

Two hypotheses of the class-four model are **not** carried.  There is no `hgb`: the class-five
legality is evenness of the `(3,4)`-column, which `fiveFrameHom_c_even` gives for every `g`, so
the dressing `g` is completely unrestricted.  And there is no lattice model: the refinement is
`gamma_4`-shaped with two even coordinates and nothing else.

The two hypotheses that **are** carried, `hu` and `hv`, are forced by the shape of the witness,
not chosen: see `fiveFrameHom_sqArbBase_handleU_ne`.

⚠ The refinements are `gamma_4`-shaped; one filtration step wider the statement is **false**
(`sqRelWord_fiveFrame_gaThree_kill`). -/
theorem fiveFrame_sigma_forced_sharp (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) (g : (DSq h : Type))
    {z₀ w₁ w₂ z₃ z₄ : SqU6 gr3R} (hz₀ : z₀.IsGaFour) (hw₁ : w₁.IsGaFive) (hw₂ : w₂.IsGaFive)
    (hz₃ : z₃.IsGaFour) (hz₄ : z₄.IsGaFour) (hsum : selPar (z₀.m + z₄.n) = 0)
    (hkill : sqRelWord (fiveLift j
      (fun i => fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (sqRelWord fun i =>
      fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i)).o = 0 := by
  rw [fiveFrameHom_sqArbFrame hu hv g] at hkill ⊢
  exact fiveWit_sigma_forced_sharp hz₀ hw₁ hw₂ hz₃ hz₄ hsum hkill

/-- ⭐⭐ **The headline against the achievable `gamma_4`-lattice**, which is the form the
campaign's achievability convention quantifies over.  Measured: `forceN4` **is** `gamma_4` of
the image at this point, so nothing achievable escapes it. -/
theorem fiveFrame_sigma_forced_gaFour (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) (g : (DSq h : Type))
    {z₀ w₁ w₂ z₃ z₄ : SqU6 gr3R} (hz₀ : z₀ ∈ forceN4) (hw₁ : w₁.IsGaFive) (hw₂ : w₂.IsGaFive)
    (hz₃ : z₃ ∈ forceN4) (hz₄ : z₄ ∈ forceN4)
    (hkill : sqRelWord (fiveLift j
      (fun i => fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (sqRelWord fun i =>
      fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i)).o = 0 :=
  fiveFrame_sigma_forced_sharp hu hv g (forceN4_isGaFour hz₀) hw₁ hw₂ (forceN4_isGaFour hz₃)
    (forceN4_isGaFour hz₄)
    (selPar_add_eq_zero_of_even (forceN4_even hz₀).1 (forceN4_even hz₄).2) hkill

/-- ⭐⭐ **The same forcing in the committed achievability convention**: the three dressings are
drawn from `gamma_4` of the subgroup generated by the frame's own image slots.  This is the
literal transposition of `GradedFiveForce.fiveWit_sigma_forced`, and it follows from the sharp
form because the achievable lattice is contained in `forceN4`
(`forceLcs_fiveFrameHom_le_forceN4`); measured, the two coincide. -/
theorem fiveFrame_sigma_forced (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) (g : (DSq h : Type))
    {z₀ w₁ w₂ z₃ z₄ : SqU6 gr3R}
    (hz₀ : z₀ ∈ forceLcs (forceImage h j (fiveFrameHom h j g)) 3)
    (hw₁ : w₁.IsGaFive) (hw₂ : w₂.IsGaFive)
    (hz₃ : z₃ ∈ forceLcs (forceImage h j (fiveFrameHom h j g)) 3)
    (hz₄ : z₄ ∈ forceLcs (forceImage h j (fiveFrameHom h j g)) 3)
    (hkill : sqRelWord (fiveLift j
      (fun i => fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (sqRelWord fun i =>
      fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i)).o = 0 :=
  fiveFrame_sigma_forced_gaFour hu hv g (forceLcs_fiveFrameHom_le_forceN4 g hz₀) hw₁ hw₂
    (forceLcs_fiveFrameHom_le_forceN4 g hz₃) (forceLcs_fiveFrameHom_le_forceN4 g hz₄) hkill

end Forcing

/-! ## 5 The verdicts on the frame, the blindness, the scope limit, and non-vacuity -/

section Verdicts

variable {h : ℕ} {j : Fin h}
variable {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- ⭐ **The undressed frame kills the relator outright** at the binder hom: all fifteen rows
vanish, so the hom is a genuine class-five quotient of the frame and the gate is live. -/
theorem sqRelWord_fiveFrame_triv (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    sqRelWord (fun i => fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h 1) i)) = 1 := by
  rw [fiveFrameHom_sqArbFrame hu hv, map_one]
  exact sqRelWord_fiveWit_triv h j

/-- ⭐ **The same fact by the gate rather than by the tuple.**  Wave 57's process finding was
that two results of one wave can each be right while their composition is vacuous, so the two
routes are made to meet here: at a cleared row the undressed arbitrary-dressing frame **is** the
standard frame, which kills the relator in `D_sq h` itself, so the class-five gate
`sqU6Balance_gen` gives the previous theorem without touching the binder point's fifteen-row
`decide`.  Both routes agree. -/
theorem sqRelWord_fiveFrame_triv_gate (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    sqRelWord (fun i => fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h 1) i)) = 1 := by
  have hframe : ∀ i, sqArbFrame h nu' j (sigArbDress h (1 : (DSq h : Type))) i = sqGen h i := by
    intro i
    have hd : sigArbDress h (1 : (DSq h : Type)) i = 1 := by
      by_cases h0 : (i : ℕ) = 0
      · rw [show i = 0 from Fin.val_injective (by rw [h0, sqVal_zero]), sigArbDress_zero]
      · rw [sigArbDress_ne h0]
    rw [sqArbFrame, sqArbBase_of_cleared hu hv, hd, mul_one]
  have hcongr : (fun i => fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h 1) i))
      = fun i => fiveFrameHom h j (sqGen h i) :=
    funext fun i => congrArg (fiveFrameHom h j) (hframe i)
  rw [hcongr]
  exact sqU6Balance_gen (fiveFrameHom h j)

/-- ⭐⭐ **The `x0`-dressed frame leaves the ODD class-five residue `7`.**  The sigma dressing
`a0 = a1` of `GradedSigmaFour` section 7, executed on `sqArbFrame` itself. -/
theorem sqRelWord_fiveFrame_diag (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    sqRelWord (fun i =>
        fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i)) = liftC6 7 := by
  rw [fiveFrameHom_sqArbFrame hu hv, fiveFrameHom_x0]
  exact sqRelWord_fiveWit_diag h j

/-- ⭐⭐ **THE EXCLUSION ON `sqArbFrame`: the `x0`-dressed frame survives everything.**  No
five-slot class-five refinement whose one load-bearing parity `z0.m + z4.n` is even kills the
relator image, at any handle count, any handle, and any row cleared at the selected handle.
This is the sharpest survival bound the tree owns at this point: the handle-`u` dressing `z3`
and the coordinates `z0.n`, `z4.m` are entirely unconstrained, and the hypothesis that remains
is exactly necessary by `fiveFrame_odd_sum_kill`.  ⚠ Read with
`sqRelWord_fiveFrame_gaThree_kill`: one filtration step wider the statement is false. -/
theorem sqRelWord_fiveFrame_diag_ne_one_sharp (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU6 gr3R} (hz₀ : z₀.IsGaFour) (hw₁ : w₁.IsGaFive) (hw₂ : w₂.IsGaFive)
    (hz₃ : z₃.IsGaFour) (hz₄ : z₄.IsGaFour) (hsum : selPar (z₀.m + z₄.n) = 0) :
    sqRelWord (fiveLift j
      (fun i => fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i))
      z₀ w₁ w₂ z₃ z₄) ≠ 1 := by
  intro hc
  have hp := fiveFrame_sigma_forced_sharp hu hv (dsqX0 h) hz₀ hw₁ hw₂ hz₃ hz₄ hsum hc
  rw [sqRelWord_fiveFrame_diag hu hv, liftC6_o] at hp
  exact absurd hp (by decide)

/-- ⭐⭐ **The converse: the sharp condition is a CHARACTERISATION, not merely a sufficient
condition.**  Whenever `z0.m + z4.n` is **odd** there is a central `gamma_5`-dressing of the
`x1`-slot that kills the `x0`-dressed frame, for **any** `gamma_4`-shaped `z0`, `z3`, `z4`.  So
the class-five soundness line at this point is exactly "the sum of the sigma dressing's first
class-four coordinate and the handle-`v` dressing's second one is even", and the campaign should
carry that rather than the achievable lattice: wave 59's cross-lane check asked for exactly this
at class five, on the strength of the class-four precedent that the carried hypothesis is
strictly stronger than the sharp line. -/
theorem fiveFrame_odd_sum_kill (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1)
    {z₀ z₃ z₄ : SqU6 gr3R} (hz₀ : z₀.IsGaFour) (hz₃ : z₃.IsGaFour) (hz₄ : z₄.IsGaFour)
    (hsum : selPar (z₀.m + z₄.n) = 1) :
    ∃ w₂ : SqU6 gr3R, w₂.IsGaFive ∧
      sqRelWord (fiveLift j
        (fun i => fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i))
        z₀ 1 w₂ z₃ z₄) = 1 := by
  have hpar : selPar (1 - (z₀.m + z₄.n)) = 0 := by
    rw [selPar_sub, selPar_one, hsum, sub_self]
  obtain ⟨u, hu2⟩ := (selPar_eq_zero_iff _).mp hpar
  refine ⟨liftC6 (u + z₀.n - z₃.m), liftC6_isGaFive _, ?_⟩
  rw [fiveFrameHom_sqArbFrame hu hv, fiveFrameHom_x0,
    sqRelWord_fiveLift hz₀ SqU6.isGaFive_one (liftC6_isGaFive _) hz₃ hz₄,
    sqRelWord_fiveWit_diag, liftC6_mul_liftC6]
  refine Eq.trans (congrArg liftC6 ?_) liftC6_zero
  simp only [fiveWit_one, fiveWit_handleU, fiveWit_handleV, SqU6.one_o, liftC6_o,
    forceX, forceU, forceV]
  have h8 : (8 : gr3R) = 0 := by decide
  linear_combination -hu2 + h8

/-- ⭐⭐ **The sharp line is about the SUM, not about the two coordinates separately.**  The
`gamma_4`-shaped move `<m = 1>` on the sigma slot kills
(`GradedFiveForce.fiveWit_unrestricted_kill`), the move `<n = 1>` on the handle-`v` slot kills
(`fiveFrame_handleV_odd_kill`), and applying **both at once** leaves the residue `1` and kills
nothing.  So no conjunction of per-slot conditions is the sharp line. -/
theorem fiveFrame_both_odd_no_kill (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    sqRelWord (fiveLift j
      (fun i => fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i))
      ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩ 1 1 1
      ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩) = liftC6 1 := by
  rw [fiveFrameHom_sqArbFrame hu hv, fiveFrameHom_x0,
    sqRelWord_fiveLift ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      SqU6.isGaFive_one SqU6.isGaFive_one SqU6.isGaFour_one
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    sqRelWord_fiveWit_diag, liftC6_mul_liftC6]
  refine congrArg liftC6 ?_
  simp only [fiveWit_one, fiveWit_handleU, fiveWit_handleV, SqU6.one_m, SqU6.one_n, SqU6.one_o,
    forceX, forceU, forceV]
  decide

/-- ⭐⭐ **The exclusion against the achievable `gamma_4`-lattice**, the campaign's convention:
no achievable five-slot class-five refinement of the frame's image kills the relator. -/
theorem sqRelWord_fiveFrame_diag_ne_one (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU6 gr3R} (hz₀ : z₀ ∈ forceN4) (hw₁ : w₁.IsGaFive) (hw₂ : w₂.IsGaFive)
    (hz₃ : z₃ ∈ forceN4) (hz₄ : z₄ ∈ forceN4) :
    sqRelWord (fiveLift j
      (fun i => fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i))
      z₀ w₁ w₂ z₃ z₄) ≠ 1 :=
  sqRelWord_fiveFrame_diag_ne_one_sharp hu hv (forceN4_isGaFour hz₀) hw₁ hw₂
    (forceN4_isGaFour hz₃) (forceN4_isGaFour hz₄)
    (selPar_add_eq_zero_of_even (forceN4_even hz₀).1 (forceN4_even hz₄).2)

/-- ⚠ **The handle-`v` slot carries the other half of the load-bearing parity**: the
`gamma_4`-shaped move `<n = 1>` there has increment `forceU.a * 1 = 1`, and `7 + 1 = 0`, so it
kills the `x0`-dressed frame outright.  It is unachievable for the same reason
`GradedFiveForce`'s `<m = 1>` is: its class-four coordinate is odd.  This is the companion of
`GradedFiveForce.fiveWit_unrestricted_kill` on the other load-bearing coordinate. -/
theorem fiveFrame_handleV_odd_kill (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    sqRelWord (fiveLift j
      (fun i => fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i))
      1 1 1 1 ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩) = 1 := by
  rw [fiveFrameHom_sqArbFrame hu hv, fiveFrameHom_x0,
    sqRelWord_fiveLift SqU6.isGaFour_one SqU6.isGaFive_one SqU6.isGaFive_one SqU6.isGaFour_one
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    sqRelWord_fiveWit_diag, liftC6_mul_liftC6]
  refine Eq.trans (congrArg liftC6 ?_) liftC6_zero
  simp only [fiveWit_one, fiveWit_handleU, fiveWit_handleV, SqU6.one_m, SqU6.one_n, SqU6.one_o,
    forceX, forceU, forceV]
  decide

/-- …and it is **not** an achievable dressing, which is why it does not contradict the
exclusion. -/
theorem fiveFrame_handleV_odd_not_achievable :
    (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩ : SqU6 gr3R) ∉ forceN4 := by
  intro hc
  obtain ⟨-, ⟨t, ht⟩⟩ := forceN4_even hc
  exact absurd ht (by revert t; decide)

/-- …and the bit really does separate the two dressings on the frame. -/
theorem fiveFrame_bit_separates (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    selPar (sqRelWord fun i =>
        fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h 1) i)).o = 0
      ∧ selPar (sqRelWord fun i =>
        fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i)).o = 1 := by
  refine ⟨?_, ?_⟩
  · rw [sqRelWord_fiveFrame_triv hu hv]
    decide
  · rw [sqRelWord_fiveFrame_diag hu hv, liftC6_o]
    decide

/-- ⭐ **Every class-`<= 4` verdict on the frame is the same for both dressings**: both
`U_5`-quotients of the frame's relator image are trivial in each case, so the separation above
is purely class five.  `GradedFiveForce.fiveWit_class_four_blind`, on `sqArbFrame`. -/
theorem fiveFrame_class_four_blind (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    (sqRelWord (fun i => SqU6.toU5L
        (fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h 1) i))) = 1
      ∧ sqRelWord (fun i => SqU6.toU5R
        (fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h 1) i))) = 1)
    ∧ (sqRelWord (fun i => SqU6.toU5L
        (fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i))) = 1
      ∧ sqRelWord (fun i => SqU6.toU5R
        (fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i))) = 1) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [← SqU6.toU5L_sqRelWord, sqRelWord_fiveFrame_triv hu hv, map_one]
  · rw [← SqU6.toU5R_sqRelWord, sqRelWord_fiveFrame_triv hu hv, map_one]
  · rw [← SqU6.toU5L_sqRelWord, sqRelWord_fiveFrame_diag hu hv]
    decide
  · rw [← SqU6.toU5R_sqRelWord, sqRelWord_fiveFrame_diag hu hv]
    decide

/-! ### ⚠ The `x0`-dressing is `nu'`-trivial but NOT `lambda`-trivial, and a fully legal
dressing that does the same job

`ArbFrames` asks the dressings of `sqArbFrame` to lie in `ker lambda ∩ ker nu'`.  The dressing
the wave-59 exclusion is about is the `x0`-generator, and `nuLam h (x0) = ofAdd 1`, so it lies in
`ker nu'` and **not** in `ker lambda`.  That is recorded rather than glossed
(`nuLam_sigArbDress_x0_ne_one`), and it is forced: `lambda(g) = 0`, `nu'(g) = 0` and
`Phi(g) = forceX` are inconsistent, because the `b`-column of `Phi` is the sigma-count and the
`e`-column is `x0-count + 2 x1-count + 2 v_j-count`, whose reduction is even once `lambda` and
`nu'` both vanish, while `forceX.e = 1`.

There is nevertheless a **fully legal** dressing with the same three properties, and it is a
commutator, hence in the kernel of every character: `fiveLegalDress h j = [x1, u_j]`.  Its image
`commP forceY forceU` leaves the relator image the **purely central, odd** value `liftC6 5`,
so the class-four machinery is blind to it and no refinement in the sharp class kills it.  This
restores the class-four escape statement (`GradedFourCleared.clrFour_escape_separates`) in full
at class five, with the legality of the dressing exhibited. -/

/-- The `x0`-dressing's `lambda`-row is `1`, so it is **not** `lambda`-trivial.  Recorded so the
legality class of the wave-59 escape dressing is not overstated. -/
theorem nuLam_sigArbDress_x0_ne_one : nuLam h (sigArbDress h (dsqX0 h) 0) ≠ 1 := by
  rw [sigArbDress_zero, nuLam_x0]
  intro hc
  have hz := congrArg Multiplicative.toAdd hc
  rw [toAdd_ofAdd, toAdd_one] at hz
  exact absurd hz one_ne_zero

/-- A commutator is trivial in an abelian target. -/
private theorem commP_eq_one_multPadic (x y : Multiplicative ℤ_[2]) : commP x y = 1 :=
  Multiplicative.toAdd.injective (by
    simp only [commP, toAdd_mul, toAdd_inv, toAdd_one]
    ring)

variable (h j) in
/-- ⭐ **The legal escape dressing**: the commutator `[x1, u_j]` of the frame's own generators.
Being a commutator it is `lambda`-trivial and `nu'`-trivial for **every** row, so it lies in the
class `ArbFrames` quantifies over. -/
noncomputable def fiveLegalDress : (DSq h : Type) :=
  commP (dsqX1 h) (sqGen h (sqHandleIdxU j))

theorem fiveFrameHom_fiveLegalDress :
    fiveFrameHom h j (fiveLegalDress h j) = commP forceY forceU := by
  rw [fiveLegalDress, map_commP, fiveFrameHom_x1, fiveFrameHom_handleU]

/-- The legal dressing is `lambda`-trivial slotwise, at every row. -/
theorem nuLam_sigArbDress_legal (i : Fin (sqRank h)) :
    nuLam h (sigArbDress h (fiveLegalDress h j) i) = 1 :=
  nuLam_sigArbDress (by rw [fiveLegalDress, map_commP]; exact commP_eq_one_multPadic _ _) i

/-- …and `nu'`-trivial slotwise, at every row, for every continuous `nu'`. -/
theorem nu_sigArbDress_legal (i : Fin (sqRank h)) :
    nu' (sigArbDress h (fiveLegalDress h j) i) = 1 :=
  nu_sigArbDress (by rw [fiveLegalDress, map_commP]; exact commP_eq_one_multPadic _ _) i

/-- ⭐⭐ **The legal dressing leaves the purely central, ODD residue `5`** at the binder point,
at every handle count and every handle. -/
theorem sqRelWord_fiveWit_legal (h : ℕ) (j : Fin h) :
    sqRelWord (fiveWit h j (commP forceY forceU)) = liftC6 5 := by
  rw [fiveWit, sqRelWord_fiveTuple]
  decide

/-- ⭐⭐ …and the same on `sqArbFrame`. -/
theorem sqRelWord_fiveFrame_legal (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    sqRelWord (fun i => fiveFrameHom h j
      (sqArbFrame h nu' j (sigArbDress h (fiveLegalDress h j)) i)) = liftC6 5 := by
  rw [fiveFrameHom_sqArbFrame hu hv, fiveFrameHom_fiveLegalDress]
  exact sqRelWord_fiveWit_legal h j

/-- ⭐⭐ **The exclusion at the legal dressing**: no five-slot class-five refinement with even
load-bearing parity kills it either. -/
theorem sqRelWord_fiveFrame_legal_ne_one (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU6 gr3R} (hz₀ : z₀.IsGaFour) (hw₁ : w₁.IsGaFive) (hw₂ : w₂.IsGaFive)
    (hz₃ : z₃.IsGaFour) (hz₄ : z₄.IsGaFour) (hsum : selPar (z₀.m + z₄.n) = 0) :
    sqRelWord (fiveLift j
      (fun i => fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h (fiveLegalDress h j)) i))
      z₀ w₁ w₂ z₃ z₄) ≠ 1 := by
  intro hc
  have hp := fiveFrame_sigma_forced_sharp hu hv (fiveLegalDress h j) hz₀ hw₁ hw₂ hz₃ hz₄ hsum hc
  rw [sqRelWord_fiveFrame_legal hu hv, liftC6_o] at hp
  exact absurd hp (by decide)

/-- ⭐ **The legal dressing is class-four invisible too**: its relator image is central, so both
`U_5`-quotients are trivial. -/
theorem fiveFrame_legal_class_four_blind (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    sqRelWord (fun i => SqU6.toU5L (fiveFrameHom h j
        (sqArbFrame h nu' j (sigArbDress h (fiveLegalDress h j)) i))) = 1
      ∧ sqRelWord (fun i => SqU6.toU5R (fiveFrameHom h j
        (sqArbFrame h nu' j (sigArbDress h (fiveLegalDress h j)) i))) = 1 := by
  refine ⟨?_, ?_⟩
  · rw [← SqU6.toU5L_sqRelWord, sqRelWord_fiveFrame_legal hu hv]
    decide
  · rw [← SqU6.toU5R_sqRelWord, sqRelWord_fiveFrame_legal hu hv]
    decide

/-- ⭐⭐ **The class-five escape separates the sigma dressings on `sqArbFrame` itself, with the
legality of both dressings exhibited**: same hom, same frame, same row, both dressings
`lambda`-trivial and `nu'`-trivial slotwise; the trivial dressing kills the relator image and
`[x1, u_j]` leaves the odd central residue `5`, which the class-four machinery cannot see and no
refinement in the sharp class kills.  `GradedFourCleared.clrFour_escape_separates` one class
up. -/
theorem fiveFrame_escape_separates (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    ((∀ i, nuLam h (sigArbDress h (1 : (DSq h : Type)) i) = 1)
        ∧ ∀ i, nu' (sigArbDress h (1 : (DSq h : Type)) i) = 1)
      ∧ ((∀ i, nuLam h (sigArbDress h (fiveLegalDress h j) i) = 1)
        ∧ ∀ i, nu' (sigArbDress h (fiveLegalDress h j) i) = 1)
      ∧ sqRelWord (fun i => fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h 1) i)) = 1
      ∧ sqRelWord (fun i => fiveFrameHom h j
          (sqArbFrame h nu' j (sigArbDress h (fiveLegalDress h j)) i)) = liftC6 5 :=
  ⟨⟨nuLam_sigArbDress (map_one _), nu_sigArbDress (map_one _)⟩,
    ⟨nuLam_sigArbDress_legal, nu_sigArbDress_legal⟩,
    sqRelWord_fiveFrame_triv hu hv, sqRelWord_fiveFrame_legal hu hv⟩

/-! ### ⚠⚠ The scope limit, at the hom level

`GradedFiveForce`'s exclusion is against stage-five refinements and is false one filtration step
wider.  The transport does not repair that and does not hide it: the killing dressing is the
image of a **triple commutator of the frame's own generators**, so at the hom level it is an
honest element of `D_sq h` rather than a hand-built tuple. -/

variable (h j) in
/-- ⚠⚠ **The wider killing word**: `[[sigma, u_j], x1]` in `D_sq h`.  Its image is the
`gamma_4`-shaped element `<m = 5, n = 6>` with an **odd** class-four coordinate. -/
noncomputable def fiveKillWord : (DSq h : Type) :=
  commP (commP (dsqSigma h) (sqGen h (sqHandleIdxU j))) (dsqX1 h)

theorem fiveFrameHom_fiveKillWord :
    fiveFrameHom h j (fiveKillWord h j) = commP (commP (fiveSigMark gr3R) forceU) forceY := by
  rw [fiveKillWord, map_commP, map_commP, fiveFrameHom_sigma, fiveFrameHom_handleU,
    fiveFrameHom_x1]

/-- ⚠⚠ **…and it kills the `x0`-dressed frame outright**, at every handle count and every
handle.  So the exclusion above is genuinely scoped: the `forceN4` quantifier cannot be widened
to `gamma_3` of the image. -/
theorem sqRelWord_fiveFrame_gaThree_kill (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    sqRelWord (fiveLift j
      (fun i => fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i))
      (fiveFrameHom h j (fiveKillWord h j)) 1 1 1 1) = 1 := by
  rw [fiveFrameHom_sqArbFrame hu hv, fiveFrameHom_x0, fiveFrameHom_fiveKillWord]
  exact fiveWit_gaThree_kill h j

/-- ⚠⚠ **The killing dressing is achievable one filtration step wider**: it lies in `gamma_3`
of the image. -/
theorem fiveFrameHom_fiveKillWord_mem :
    fiveFrameHom h j (fiveKillWord h j) ∈ forceLcs (forceImage h j forceX) 2 := by
  rw [fiveFrameHom_fiveKillWord]
  exact fiveWit_gaThree_kill_mem h j

/-- ⚠⚠ **…and not at the stage the exclusion quantifies over**: its class-four coordinate is
`5`, so it is outside `forceN4`.  This is exactly why the two statements do not contradict
each other. -/
theorem fiveFrameHom_fiveKillWord_not_gaFour :
    fiveFrameHom h j (fiveKillWord h j) ∉ forceN4 := by
  rw [fiveFrameHom_fiveKillWord]
  exact fiveWit_gaThree_kill_not_gaFour

/-! ### Non-vacuity: the forcing quantifies over dressings that genuinely move the residue -/

variable (h j) in
/-- **The non-vacuity word**: `[[[v_j, u_j], x0], sigma]` in `D_sq h`, whose image is the
achievable dressing `<n = 2>`. -/
noncomputable def fiveMoveWord : (DSq h : Type) :=
  commP (commP (commP (sqGen h (sqHandleIdxV j)) (sqGen h (sqHandleIdxU j))) (dsqX0 h))
    (dsqSigma h)

theorem fiveFrameHom_fiveMoveWord :
    fiveFrameHom h j (fiveMoveWord h j)
      = commP (commP (commP forceV forceU) forceX) (fiveSigMark gr3R) := by
  rw [fiveMoveWord, map_commP, map_commP, map_commP, fiveFrameHom_handleV,
    fiveFrameHom_handleU, fiveFrameHom_x0, fiveFrameHom_sigma]

/-- A repo commutator of two members lands in the commutator subgroup.  (`GradedFiveForce`'s
copy is `private`, so this one is rebuilt here.) -/
private theorem commP_mem_commutator' {H K : Subgroup (SqU6 gr3R)} {p q : SqU6 gr3R}
    (hp : p ∈ H) (hq : q ∈ K) : commP p q ∈ ⁅H, K⁆ := by
  have hc := Subgroup.commutator_mem_commutator (H.inv_mem hp) (K.inv_mem hq)
  rwa [commutatorElement_eq_commP, inv_inv, inv_inv] at hc

/-- ⭐ **The non-vacuity witness is achievable**: it is a triple commutator of the point's own
letters, so it lies in `gamma_4` of the image. -/
theorem fiveFrameHom_fiveMoveWord_mem :
    fiveFrameHom h j (fiveMoveWord h j) ∈ forceLcs (forceImage h j forceX) 3 := by
  rw [fiveFrameHom_fiveMoveWord]
  have hzero : fiveSigMark gr3R * forceX ∈ forceImage h j forceX := by
    have hm := mem_forceImage_slot h j forceX 0
    rwa [fiveWit_zero] at hm
  have hX : forceX ∈ forceImage h j forceX := by
    have hm := mem_forceImage_slot h j forceX 1
    rwa [fiveWit_one] at hm
  have hU : forceU ∈ forceImage h j forceX := by
    have hm := mem_forceImage_slot h j forceX (sqHandleIdxU j)
    rwa [fiveWit_handleU] at hm
  have hV : forceV ∈ forceImage h j forceX := by
    have hm := mem_forceImage_slot h j forceX (sqHandleIdxV j)
    rwa [fiveWit_handleV] at hm
  have hS : fiveSigMark gr3R ∈ forceImage h j forceX := by
    have hmul := (forceImage h j forceX).mul_mem hzero ((forceImage h j forceX).inv_mem hX)
    rwa [mul_inv_cancel_right] at hmul
  exact commP_mem_commutator' (commP_mem_commutator' (commP_mem_commutator' hV hU) hX) hS

/-- ⭐ …and it lies in `forceN4`, so the sharp form quantifies over it too. -/
theorem fiveFrameHom_fiveMoveWord_gaFour :
    fiveFrameHom h j (fiveMoveWord h j) ∈ forceN4 := by
  rw [fiveFrameHom_fiveMoveWord, mem_forceN4]
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, ⟨0, by decide⟩, ⟨1, by decide⟩⟩

/-- ⭐⭐ **The forcing is not vacuous.**  Dressing the sigma slot of the `x0`-dressed frame by
the achievable dressing `Phi(fiveMoveWord)` moves the class-five residue from `7` to `3`: the
quantified class genuinely acts on the residue, and the content of the exclusion is that it
cannot reach `0`.  Compare `GradedFiveForce.fiveWit_unrestricted_kill`, which shows what an
**un**achievable move does. -/
theorem fiveFrame_forcing_nonvacuous (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    sqRelWord (fiveLift j
      (fun i => fiveFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i))
      (fiveFrameHom h j (fiveMoveWord h j)) 1 1 1 1) = liftC6 3 := by
  have hz : (fiveFrameHom h j (fiveMoveWord h j)).IsGaFour :=
    forceN4_isGaFour fiveFrameHom_fiveMoveWord_gaFour
  rw [fiveFrameHom_sqArbFrame hu hv, fiveFrameHom_x0, sqRelWord_fiveLift hz
    SqU6.isGaFive_one SqU6.isGaFive_one SqU6.isGaFour_one SqU6.isGaFour_one,
    sqRelWord_fiveWit_diag, liftC6_mul_liftC6]
  refine congrArg liftC6 ?_
  simp only [fiveWit_one, fiveWit_handleU, fiveWit_handleV, SqU6.one_m, SqU6.one_n, SqU6.one_o,
    fiveFrameHom_fiveMoveWord]
  ring_nf
  decide

end Verdicts

/-! ## 6 The named cleared row `nuSel h j 0 0`

The row hypotheses `hu`, `hv` are discharged from the row itself at the committed cleared
selected marking, at every handle count and every handle.  The dressing legality that class four
had to discharge here has already been discharged for every dressing in section 2, so these
statements carry **nothing**. -/

section ClearedRow

variable {h : ℕ} {j : Fin h}

/-- The frame identification at the cleared row. -/
theorem fiveFrameHom_sqArbFrame_cleared (g : (DSq h : Type)) :
    (fun i => fiveFrameHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h g) i))
      = fiveWit h j (fiveFrameHom h j g) :=
  fiveFrameHom_sqArbFrame nuSelClr_handleU nuSelClr_handleV g

/-- ⭐⭐ **The headline at the named row**: at every handle count, every handle, and the
committed cleared selected marking `nuSel h j 0 0`, every sigma dressing of the
arbitrary-dressing frame whose image is killed by any five-slot class-five refinement with even
load-bearing coordinates leaves an **even** class-five residue.  Nothing is carried: not the row
(it is the row), and not the dressing's legality (there is none to carry at class five). -/
theorem sqArbFrame_five_sigma_forced_cleared (g : (DSq h : Type))
    {z₀ w₁ w₂ z₃ z₄ : SqU6 gr3R} (hz₀ : z₀.IsGaFour) (hw₁ : w₁.IsGaFive) (hw₂ : w₂.IsGaFive)
    (hz₃ : z₃.IsGaFour) (hz₄ : z₄.IsGaFour) (hsum : selPar (z₀.m + z₄.n) = 0)
    (hkill : sqRelWord (fiveLift j
      (fun i => fiveFrameHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (sqRelWord fun i =>
      fiveFrameHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h g) i)).o = 0 :=
  fiveFrame_sigma_forced_sharp nuSelClr_handleU nuSelClr_handleV g hz₀ hw₁ hw₂ hz₃ hz₄ hsum
    hkill

/-- …and against the achievable `gamma_4`-lattice `forceN4`. -/
theorem sqArbFrame_five_sigma_forced_cleared_gaFour (g : (DSq h : Type))
    {z₀ w₁ w₂ z₃ z₄ : SqU6 gr3R} (hz₀ : z₀ ∈ forceN4) (hw₁ : w₁.IsGaFive) (hw₂ : w₂.IsGaFive)
    (hz₃ : z₃ ∈ forceN4) (hz₄ : z₄ ∈ forceN4)
    (hkill : sqRelWord (fiveLift j
      (fun i => fiveFrameHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (sqRelWord fun i =>
      fiveFrameHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h g) i)).o = 0 :=
  fiveFrame_sigma_forced_gaFour nuSelClr_handleU nuSelClr_handleV g hz₀ hw₁ hw₂ hz₃ hz₄ hkill

/-- …and in the committed achievability convention. -/
theorem sqArbFrame_five_sigma_forced_cleared_lattice (g : (DSq h : Type))
    {z₀ w₁ w₂ z₃ z₄ : SqU6 gr3R}
    (hz₀ : z₀ ∈ forceLcs (forceImage h j (fiveFrameHom h j g)) 3)
    (hw₁ : w₁.IsGaFive) (hw₂ : w₂.IsGaFive)
    (hz₃ : z₃ ∈ forceLcs (forceImage h j (fiveFrameHom h j g)) 3)
    (hz₄ : z₄ ∈ forceLcs (forceImage h j (fiveFrameHom h j g)) 3)
    (hkill : sqRelWord (fiveLift j
      (fun i => fiveFrameHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (sqRelWord fun i =>
      fiveFrameHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h g) i)).o = 0 :=
  fiveFrame_sigma_forced nuSelClr_handleU nuSelClr_handleV g hz₀ hw₁ hw₂ hz₃ hz₄ hkill

/-- ⭐⭐ **The exclusion at the named row.** -/
theorem sqArbFrame_five_diag_ne_one_cleared
    {z₀ w₁ w₂ z₃ z₄ : SqU6 gr3R} (hz₀ : z₀ ∈ forceN4) (hw₁ : w₁.IsGaFive) (hw₂ : w₂.IsGaFive)
    (hz₃ : z₃ ∈ forceN4) (hz₄ : z₄ ∈ forceN4) :
    sqRelWord (fiveLift j
      (fun i => fiveFrameHom h j
        (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h (dsqX0 h)) i))
      z₀ w₁ w₂ z₃ z₄) ≠ 1 :=
  sqRelWord_fiveFrame_diag_ne_one nuSelClr_handleU nuSelClr_handleV hz₀ hw₁ hw₂ hz₃ hz₄

/-- The `x0`-dressing is `ν'`-trivial slotwise at the cleared row, so it lies in the class the
residual quantifies over. -/
theorem nu_sigArbDress_x0_cleared (i : Fin (sqRank h)) :
    nuSel h j 0 0 (sigArbDress h (dsqX0 h) i) = 1 :=
  nu_sigArbDress (by rw [nuSel_x0, ofAdd_zero]) i

/-- ⭐ **The verdicts at the named row**, with the `ν'`-legality of the `x0`-dressing and the
full `λ`- and `ν'`-legality of the commutator dressing exhibited. -/
theorem fiveFrame_escape_separates_cleared :
    (∀ i, nuSel h j 0 0 (sigArbDress h (dsqX0 h) i) = 1)
      ∧ ((∀ i, nuLam h (sigArbDress h (fiveLegalDress h j) i) = 1)
        ∧ ∀ i, nuSel h j 0 0 (sigArbDress h (fiveLegalDress h j) i) = 1)
      ∧ sqRelWord (fun i =>
          fiveFrameHom h j (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h 1) i)) = 1
      ∧ sqRelWord (fun i =>
          fiveFrameHom h j
            (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h (dsqX0 h)) i)) = liftC6 7
      ∧ sqRelWord (fun i =>
          fiveFrameHom h j
            (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h (fiveLegalDress h j)) i))
          = liftC6 5 :=
  ⟨nu_sigArbDress_x0_cleared, ⟨nuLam_sigArbDress_legal, nu_sigArbDress_legal⟩,
    sqRelWord_fiveFrame_triv nuSelClr_handleU nuSelClr_handleV,
    sqRelWord_fiveFrame_diag nuSelClr_handleU nuSelClr_handleV,
    sqRelWord_fiveFrame_legal nuSelClr_handleU nuSelClr_handleV⟩

end ClearedRow

/-! ## 7 Axiom pins

Committed prints for every public declaration of this file: all **std-3** (`propext`,
`Classical.choice`, `Quot.sound`) or a subset; no census axiom is reachable, `sqPivotExp`
included.  Every `decide` is on `ZMod 8` or on `Fin`-indexed tuples over it; there is no
`native_decide`. -/

section AxiomPins

#print axioms isProP_two_gr6
#print axioms fiveWit_zero
#print axioms fiveWit_one
#print axioms fiveWit_two
#print axioms fiveWit_handleU
#print axioms fiveWit_handleV
#print axioms fiveWit_handleU_ne
#print axioms fiveWit_handleV_ne
#print axioms fiveWit_of_ne_zero
#print axioms fiveFrameHom
#print axioms fiveFrameHom_gen
#print axioms fiveFrameHom_sigma
#print axioms fiveFrameHom_x0
#print axioms fiveFrameHom_x1
#print axioms fiveFrameHom_handleU
#print axioms fiveFrameHom_handleV
#print axioms fiveFrameHom_handle_ne
#print axioms forceX_flat
#print axioms forceX_zpowZtwo
#print axioms fiveFrameHom_sqPivot
#print axioms fiveFrameHom_sqPivot_ne_one
#print axioms fiveFrameHom_mem_closure
#print axioms fiveFrameHom_c_even
#print axioms fiveFrameHom_mem_forceN1
#print axioms forceLcs_fiveFrameHom_le_forceN4
#print axioms fiveFrameHom_sqArbFrame
#print axioms forceImage_eq_frame_closure
#print axioms fiveFrameHom_sqArbBase_handleU_ne
#print axioms fiveFrameHom_sqArbBase_handleV_ne
#print axioms fiveWit_sigma_forced_sharp
#print axioms fiveWit_sigma_forced_gaFour
#print axioms fiveFrame_sigma_forced_sharp
#print axioms fiveFrame_sigma_forced_gaFour
#print axioms fiveFrame_sigma_forced
#print axioms sqRelWord_fiveFrame_triv
#print axioms sqRelWord_fiveFrame_triv_gate
#print axioms sqRelWord_fiveFrame_diag
#print axioms sqRelWord_fiveFrame_diag_ne_one_sharp
#print axioms fiveFrame_odd_sum_kill
#print axioms fiveFrame_both_odd_no_kill
#print axioms sqRelWord_fiveFrame_diag_ne_one
#print axioms fiveFrame_handleV_odd_kill
#print axioms fiveFrame_handleV_odd_not_achievable
#print axioms fiveFrame_bit_separates
#print axioms fiveFrame_class_four_blind
#print axioms nuLam_sigArbDress_x0_ne_one
#print axioms fiveLegalDress
#print axioms fiveFrameHom_fiveLegalDress
#print axioms nuLam_sigArbDress_legal
#print axioms nu_sigArbDress_legal
#print axioms sqRelWord_fiveWit_legal
#print axioms sqRelWord_fiveFrame_legal
#print axioms sqRelWord_fiveFrame_legal_ne_one
#print axioms fiveFrame_legal_class_four_blind
#print axioms fiveFrame_escape_separates
#print axioms fiveKillWord
#print axioms fiveFrameHom_fiveKillWord
#print axioms sqRelWord_fiveFrame_gaThree_kill
#print axioms fiveFrameHom_fiveKillWord_mem
#print axioms fiveFrameHom_fiveKillWord_not_gaFour
#print axioms fiveMoveWord
#print axioms fiveFrameHom_fiveMoveWord
#print axioms fiveFrameHom_fiveMoveWord_mem
#print axioms fiveFrameHom_fiveMoveWord_gaFour
#print axioms fiveFrame_forcing_nonvacuous
#print axioms fiveFrameHom_sqArbFrame_cleared
#print axioms sqArbFrame_five_sigma_forced_cleared
#print axioms sqArbFrame_five_sigma_forced_cleared_gaFour
#print axioms sqArbFrame_five_sigma_forced_cleared_lattice
#print axioms sqArbFrame_five_diag_ne_one_cleared
#print axioms nu_sigArbDress_x0_cleared
#print axioms fiveFrame_escape_separates_cleared

end AxiomPins

end SqCore

end Dyadic

end GQ2

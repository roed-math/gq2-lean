/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFiveForce

/-!
# W60-SHARP5: the class-five soundness condition is MERELY SUFFICIENT, and here is the line

`GradedFiveForce` (wave 59) discharged the sigma residual carried since wave 51, on a soundness
chain it proved rather than assumed: an even `(3,4)`-column at every slot (`forceN1`) forces
every achievable class-four dressing into `forceN4`, both class-four coordinates even, which
makes the five-slot increment of `sqRelWord_fiveLift` even.  The wave-59 cross-lane check
recorded, correctly, that this must **not** be read as a characterisation, and that the
class-four precedent of `GradedFrameNecessity` was positive evidence it is not.

It is not.  This file says what is true instead, in both directions, and then says the one
thing that is genuinely surprising: at wave 59's **own** point the chain's conclusion is
exactly the sharp line, so nothing published there is weaker than it looks - while its
hypothesis is not the line anywhere, and the exclusion it proves can be strengthened even at
that point.

## ⭐⭐⭐ Headline 1: MERELY SUFFICIENT, in both halves

Sections 6 and 7 exhibit two class-five markings - relator a **central** translation with an
**odd** class-five residue, handle block **live**, at every handle count and every handle - at
which `forceN1` fails, `forceLcs … 3 ≤ forceN4` fails, and the class-five sigma forcing
**holds** (`orthFive_separates`, `halfFive_separates`).

## ⭐⭐⭐ Headline 2: THE CHARACTERISATION, and it has THREE covectors

Over any marking the five-slot increment's parity is exactly

```text
fiveIncrPair m j z₀ z₃ z₄ = (z₀.m·X.e − z₀.n·X.a)      sigma slot, against the x0-slot
                          + (z₃.m·V.e − z₃.n·V.a)      handle-U dressing, against V
                          + (U.a·z₄.n − U.e·z₄.m)      handle-V dressing, against U
```

with the exponent slots contributing `-4 w₁.o + 2 w₂.o`, even for free.  ⭐⭐⭐
`fiveForces_iff_fiveOrth`: at any marking whose relator is a central translation with an odd
residue, the class-five sigma forcing holds **if and only if** the three mod-`2` covectors
`(X.e, X.a)`, `(V.e, V.a)` and `(U.e, U.a)` annihilate the class-four parity image of `γ₄` of
the marking's image (`FiveOrth`).

**Class four had two covectors; class five has three.**  At class four the committed gauge
makes the sigma term even for free (`sigFourX` has outer columns `(d, a) = (0, 2)`).  At class
five the `x0`-slot's fifth abelian column is precisely the datum that escapes the committed
gauge - `forceX.e = 1`, which `GradedFiveForce.forceX_gauge` calls "a matrix entry `U_5` does
not have" - so the sigma slot's term is live and the sharp line reads it.

Two ingredients are new and are used throughout.

* ⭐⭐ `forceLcs_three_le_gaFourSub`: **every achievable class-four dressing is `γ₄`-shaped, at
  every marking, with no hypothesis at all.**  Wave 59 obtained the shape from
  `forceN4_isGaFour`, that is, conditionally on the even column; the characterisation needs it
  unconditionally, and it is true unconditionally.
* ⭐⭐⭐ `fiveKill_of_pair`: an odd pairing always produces an **explicit** kill, because the
  even part of the increment is fully tunable by the class-five exponent slot.

## ⭐⭐⭐ Headline 3: the honest other half, and what it buys anyway

⭐⭐⭐ `fiveWit_fiveOrth_iff`: **at wave 59's binder point the sharp invariant and
`forceLcs … 3 ≤ forceN4` are the same condition.**  The two live covectors there are `(1, 0)`
and `(0, 1)`, which span the mod-`2` dual, so "the covectors annihilate the parity image" is
literally "both coordinates are even".  So `GradedFiveForce`'s conclusion is sharp at the
point it was proved for; what sections 6 and 7 refute is the reading of it as the line in
general, exactly as wave 59's cross-lane check anticipated.

The sharp line still buys three things at that very point.

* ⭐⭐⭐ `fiveWit_diag_ne_one_sharp`: **the exclusion with no achievability hypothesis at all.**
  The `V`-covector VANISHES there, so the handle-`U` dressing `z₃` is **arbitrary**; the sigma
  dressing needs only `z₀.m` even and the handle-`V` dressing only `z₄.n` even.  No lower
  central series, no even column, no lattice.  `sqRelWord_fiveWit_diag_ne_one_of_sharp`
  recovers the committed statement from it.
* ⭐⭐⭐ `fiveWit_diag_kill_iff`: at that point a class-four move kills **exactly** when its
  pairing is odd, whatever its provenance.
* ⭐⭐⭐ `fiveWit_gaThree_kill_pair_odd`: so **wave 59's stage-four hole is an odd-pairing
  hole**, and the covector that sees it is the sigma one: the triple commutator
  `[[sigma, U], x1]` has first class-four coordinate `5`, and `(X.e, X.a) = (1, 0)` reads it
  oddly.  A point without the hole is a point whose `γ₃`-layer pairs evenly against the three
  slots, which is a condition on the covectors, not on the stage convention.

## ⭐⭐ The five column conditions, and which of them force what

Wave 59's `forceN1` is one of **five** natural slot-column conditions, and they do not all do
the same job.  A class-four coordinate is a four-fold bracket, `x_{15}` running over the edges
`x_{12} x_{23} x_{34} x_{45}` and `x_{26}` over `x_{23} x_{34} x_{45} x_{56}`, so each term
contains exactly one factor from each column named:

```text
every slot even in     forces x_{15} even     forces x_{26} even
a = x_{12}                   yes                    no
b = x_{23}                   yes                    yes
c = x_{34}  (wave 59)        yes                    yes
d = x_{45}                   yes                    yes
e = x_{56}                   no                     yes
```

Section 5 proves the `e`-row - `forceLcs_three_le_fiveEvenN`, a second soundness theorem by a
chain `E_1 ⊇ … ⊇ E_4` in the shape of wave 59's - and `fiveEvenE_incomparable_forceN1` shows
the two are incomparable: the half point of section 7 is inside the `e`-condition and outside
`forceN1`, and wave 59's binder point is inside `forceN1` and outside the `e`-condition,
because its `x0`-slot's fifth abelian column is odd.  The other three rows are **measured**,
not proved - but exhaustively, over all `67` mod-`2` abelian-column subspaces of each
hyperplane (`scripts/w60_sharp5/results/column_table.txt`).

## ⭐⭐ The two points, and what each one shows

* **§6, the orthogonal point.**  All six covector entries are **zero**, so
  `orthFive_pair_eq_zero` gives the pairing identically `0` for **arbitrary** class-four moves,
  and ⭐⭐⭐ `orthFive_no_kill` excludes every five-slot refinement by `γ₄`-shaped moves whatever
  their provenance.  That is strictly wider than wave 59's quantifier, and in particular it
  covers the `γ₄`-shaped elements of `γ₃` of the image, which is exactly where wave 59's
  stage-four hole lives: **this point has no such hole.**  (It is not a *stage-four* exclusion
  in general: a dressing that is `γ₃`-shaped rather than `γ₄`-shaped is outside
  `sqRelWord_fiveLift`, and the stage-four translation identity is still not built.)
  Meanwhile the achievable lattice is `{(k, 0)}` with `k` **odd** allowed, so `forceN4`
  genuinely fails, witnessed by the four-fold commutator `[[[S, V], x0], U]` of the point's own
  letters, whose first class-four coordinate is `7`.
* **§7, the half point.**  Here the `U`-covector is `(0, 1)`, so §6's route is closed and one
  covector really reads the moves.  The forcing holds through a different invariant: every
  letter has an even **fifth** abelian column, which forces the **second** class-four
  coordinate even (`halfFive_gaFour_n_even`) while the first is odd
  (`halfFive_quad_not_forceN4`).  And here achievability IS load-bearing: ⭐⭐⭐
  `halfFive_unrestricted_kill` exhibits an **unachievable** class-four move that kills, so
  `halfFive_unrestricted_forces_false` while `halfFive_fiveForces`.

## ⭐⭐ What the campaign should carry

The honest hypothesis is `FiveOrth`, not `forceN1` and not `forceN4`.  Reading the covectors
off the committed class-five letters: at wave 59's binder point the `V`-covector is `(0, 0)`
and the handle-`U` dressing is unconstrained; at the committed **live** class-five point
`GradedFive.liveFiveMark` all three covectors vanish (`liveFive_covectors`), so a forcing there
would hold for arbitrary class-four moves with no hypothesis whatsoever.  Concretely, two
committed statements should migrate:

```text
committed                                     carries now                on the sharp line
GradedFiveForce.fiveWit_sigma_forced          v.c even, and all three    z₀.m even, z₄.n even,
                                              moves achievable           z₃ arbitrary
  ->  fiveWit_sigma_forced_of_columns

GradedFiveForce.sqRelWord_fiveWit_diag_ne_one same, at v = forceX        same
  ->  fiveWit_diag_ne_one_sharp
```

`sqRelWord_fiveWit_diag_ne_one_of_sharp` and `fiveWit_fiveForces_of_le_forceN1` recover the
committed statements from the migrated ones, so nothing is lost.

## PROVED versus carried versus measured

**PROVED**, with no live hypothesis: the pairing and its additivity; four sufficient conditions
(all-even moves, all-even slot columns, and the two halves); the unconditional `γ₄`-shape of
achievable dressings; the forcing at the pairing hypothesis; the kill from an odd pairing at an
arbitrary marking; the characterisation; the second soundness chain and its incomparability
with wave 59's; both new points end to end at every handle count and every handle; the sharp
form of wave 59's exclusion and the recovery of the committed one from it; the kill criterion
at the binder point and the odd-pairing reading of the stage-four hole.

**Carried, and named**: `FiveForces` quantifies its three class-four dressings over
`forceLcs (Subgroup.closure (Set.range m)) 3`, which is `GradedFiveForce`'s achievability
convention verbatim.  §6's exclusion does **not** carry it, and neither does
`fiveWit_diag_ne_one_sharp`.

**Measured, not proved** (`scripts/w60_sharp5/results/`): the census, which is what found the
answer before it was proved, and the three unproved rows of the column table.  Over **`1936`**
admissible class-five markings in seven families - relator central with an odd residue, the
`x1`-slot produced by a layered solve so that a perturbed set of letters is pushed back onto an
admissible marking rather than discarded - the sharp criterion and an independent kill search
run through the honest group law agree at **every single marking**, `0` disagreements; `53`
break the forcing, **`366` have wave 59's CONCLUSION failing with the forcing holding**, `622`
have its HYPOTHESIS failing with the forcing holding, and `154` sit outside **both** sufficient
conditions of section 1.  No marking inside the conclusion ever breaks.  The lattice engine is
validated against wave 59's own route and against honest closure of the image's lower central
series, reproducing `|γ₃| = 16384` and `|γ₄| = 128` at the binder point; the translation
identity is checked at `4100` refinements of `41` markings; the fast product used for volume is
checked against wave 59's honest `6 x 6` matrices on `20000` comparisons.  Kill counts at the
three named points, over the `1536` UNRESTRICTED single-slot class-four moves: `0` at the
orthogonal point; `64` at the half point, **all on the handle-`V` slot**; and at wave 59's
binder point `64` on the sigma slot, `64` on the handle-`V` slot and **`0` on the handle-`U`
slot**, which is the covector table read as a measurement.

## What this does NOT do

* The characterisation's converse half needs the relator to be a central translation with an
  odd residue.  That is exactly the situation `GradedFiveForce` is in and every point of this
  file supplies it, but it is a hypothesis, not a theorem.
* Nothing here revisits `GradedFiveForce`'s theorems, all of which stand, or its stage-four
  scope warning, which stands and is now explained.  What is corrected is a **reading**: the
  step from "this condition proves the class-five soundness" to "this condition is the
  class-five soundness".
* The `a`, `b` and `d` rows of the column table are measured only; only the `c`-row (wave 59)
  and the `e`-row (section 5) are theorems.
* Like `GradedFiveForce`, this file works at the level of marking **tuples**: no statement here
  claims a tuple is the image of a continuous homomorphism on `D_sq h`.

## Contents

* **1** ⭐⭐⭐ the class-five increment pairing, and four sufficient conditions;
* **2** ⭐⭐ the unconditional `γ₄`-shape of an achievable dressing;
* **3** ⭐⭐⭐ the forcing at the pairing hypothesis, and the kill from an odd pairing;
* **4** ⭐⭐⭐ `FiveForces`, `FiveOrth`, and the characterisation;
* **5** ⭐⭐ the second soundness chain, on the fifth abelian column;
* **6** ⭐⭐⭐ the orthogonal point, where no refinement of any provenance kills;
* **7** ⭐⭐⭐ the half point, where achievability is load-bearing;
* **8** ⭐⭐⭐ what the committed class-five statements carry on the sharp line;
* **9** axiom pins.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`; every `decide` is on `ZMod 8`, `ZMod 2` or
tuples over them.  All **102** committed prints are **std-3** (`propext`, `Classical.choice`,
`Quot.sound`) or a subset (`66` std-3, `36` `propext` + `Quot.sound`); no census axiom is
reachable.
-/

open scoped commutatorElement

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The class-five increment pairing -/

section Pairing

variable {R : Type} [CommRing R] {h : ℕ} {j : Fin h} {z₀ z₃ z₄ : SqU6 R}

/-- **THE CLASS-FIVE INCREMENT PAIRING.**  The slot part of the five-slot increment of
`GradedFiveForce.sqRelWord_fiveLift`: the three class-four moves' `(m, n)`-coordinates paired
against the sigma-, `V`- and `U`-slots' **outermost** abelian columns `(e, a)`. -/
def fiveIncrPair {h : ℕ} (m : Fin (sqRank h) → SqU6 R) (j : Fin h) (z₀ z₃ z₄ : SqU6 R) : R :=
  (z₀.m * (m 1).e - z₀.n * (m 1).a)
    + ((z₃.m * (m (sqHandleIdxV j)).e - z₃.n * (m (sqHandleIdxV j)).a)
      + ((m (sqHandleIdxU j)).a * z₄.n - (m (sqHandleIdxU j)).e * z₄.m))

variable {m : Fin (sqRank h) → SqU6 R}

/-- The pairing is additive in its three arguments. -/
theorem fiveIncrPair_eq_add :
    fiveIncrPair m j z₀ z₃ z₄
      = fiveIncrPair m j z₀ 1 1 + fiveIncrPair m j 1 z₃ 1 + fiveIncrPair m j 1 1 z₄ := by
  simp only [fiveIncrPair, SqU6.one_m, SqU6.one_n]
  ring

/-- **The first sufficient condition, which is what wave 59's `forceN4` supplies.** -/
theorem fiveIncrPair_even_of_moves_even
    (h₀ : (∃ a : R, z₀.m = 2 * a) ∧ (∃ b : R, z₀.n = 2 * b))
    (h₃ : (∃ a : R, z₃.m = 2 * a) ∧ (∃ b : R, z₃.n = 2 * b))
    (h₄ : (∃ a : R, z₄.m = 2 * a) ∧ (∃ b : R, z₄.n = 2 * b)) :
    ∃ k : R, fiveIncrPair m j z₀ z₃ z₄ = 2 * k := by
  obtain ⟨⟨a₀, ha₀⟩, b₀, hb₀⟩ := h₀
  obtain ⟨⟨a₃, ha₃⟩, b₃, hb₃⟩ := h₃
  obtain ⟨⟨a₄, ha₄⟩, b₄, hb₄⟩ := h₄
  refine ⟨(a₀ * (m 1).e - b₀ * (m 1).a)
    + ((a₃ * (m (sqHandleIdxV j)).e - b₃ * (m (sqHandleIdxV j)).a)
      + ((m (sqHandleIdxU j)).a * b₄ - (m (sqHandleIdxU j)).e * a₄)), ?_⟩
  simp only [fiveIncrPair, ha₀, hb₀, ha₃, hb₃, ha₄, hb₄]
  ring

/-- **The second, DUAL sufficient condition, which no wave has used**: the three slots have
even outer abelian columns. -/
theorem fiveIncrPair_even_of_slots_even
    (hXe : ∃ k : R, (m 1).e = 2 * k) (hXa : ∃ k : R, (m 1).a = 2 * k)
    (hVe : ∃ k : R, (m (sqHandleIdxV j)).e = 2 * k)
    (hVa : ∃ k : R, (m (sqHandleIdxV j)).a = 2 * k)
    (hUe : ∃ k : R, (m (sqHandleIdxU j)).e = 2 * k)
    (hUa : ∃ k : R, (m (sqHandleIdxU j)).a = 2 * k) :
    ∃ k : R, fiveIncrPair m j z₀ z₃ z₄ = 2 * k := by
  obtain ⟨xe, hxe⟩ := hXe
  obtain ⟨xa, hxa⟩ := hXa
  obtain ⟨ve, hve⟩ := hVe
  obtain ⟨va, hva⟩ := hVa
  obtain ⟨ue, hue⟩ := hUe
  obtain ⟨ua, hua⟩ := hUa
  refine ⟨(z₀.m * xe - z₀.n * xa) + ((z₃.m * ve - z₃.n * va) + (ua * z₄.n - ue * z₄.m)), ?_⟩
  simp only [fiveIncrPair, hxe, hxa, hve, hva, hue, hua]
  ring

/-- **HALF of either condition is enough**: if all three slots have an even outermost column
`e` then the pairing reads only the moves' SECOND class-four coordinate. -/
theorem fiveIncrPair_even_of_slotE_even
    (hXe : ∃ k : R, (m 1).e = 2 * k) (hVe : ∃ k : R, (m (sqHandleIdxV j)).e = 2 * k)
    (hUe : ∃ k : R, (m (sqHandleIdxU j)).e = 2 * k)
    (h₀ : ∃ b : R, z₀.n = 2 * b) (h₃ : ∃ b : R, z₃.n = 2 * b) (h₄ : ∃ b : R, z₄.n = 2 * b) :
    ∃ k : R, fiveIncrPair m j z₀ z₃ z₄ = 2 * k := by
  obtain ⟨xe, hxe⟩ := hXe
  obtain ⟨ve, hve⟩ := hVe
  obtain ⟨ue, hue⟩ := hUe
  obtain ⟨b₀, hb₀⟩ := h₀
  obtain ⟨b₃, hb₃⟩ := h₃
  obtain ⟨b₄, hb₄⟩ := h₄
  refine ⟨(z₀.m * xe - b₀ * (m 1).a)
    + ((z₃.m * ve - b₃ * (m (sqHandleIdxV j)).a)
      + ((m (sqHandleIdxU j)).a * b₄ - ue * z₄.m)), ?_⟩
  simp only [fiveIncrPair, hxe, hve, hue, hb₀, hb₃, hb₄]
  ring

/-- …and the mirror half, on the moves' FIRST class-four coordinate. -/
theorem fiveIncrPair_even_of_slotA_even
    (hXa : ∃ k : R, (m 1).a = 2 * k) (hVa : ∃ k : R, (m (sqHandleIdxV j)).a = 2 * k)
    (hUa : ∃ k : R, (m (sqHandleIdxU j)).a = 2 * k)
    (h₀ : ∃ b : R, z₀.m = 2 * b) (h₃ : ∃ b : R, z₃.m = 2 * b) (h₄ : ∃ b : R, z₄.m = 2 * b) :
    ∃ k : R, fiveIncrPair m j z₀ z₃ z₄ = 2 * k := by
  obtain ⟨xa, hxa⟩ := hXa
  obtain ⟨va, hva⟩ := hVa
  obtain ⟨ua, hua⟩ := hUa
  obtain ⟨b₀, hb₀⟩ := h₀
  obtain ⟨b₃, hb₃⟩ := h₃
  obtain ⟨b₄, hb₄⟩ := h₄
  refine ⟨(b₀ * (m 1).e - z₀.n * xa)
    + ((b₃ * (m (sqHandleIdxV j)).e - z₃.n * va) + (ua * z₄.n - b₄ * (m (sqHandleIdxU j)).e)),
    ?_⟩
  simp only [fiveIncrPair, hxa, hva, hua, hb₀, hb₃, hb₄]
  ring

end Pairing

/-! ## 2 The class-four SHAPE of an achievable dressing, with no evenness hypothesis -/

section Shape

variable {R : Type} [CommRing R]

variable (R) in
/-- The `gamma_2`-shaped elements of the class-five carrier, as a subgroup. -/
def gaTwoSub : Subgroup (SqU6 R) where
  carrier := {p | p.a = 0 ∧ p.b = 0 ∧ p.c = 0 ∧ p.d = 0 ∧ p.e = 0}
  mul_mem' := by
    rintro p q ⟨pa, pb, pc, pd, pe⟩ ⟨qa, qb, qc, qd, qe⟩
    exact ⟨by rw [SqU6.mul_a, pa, qa]; ring, by rw [SqU6.mul_b, pb, qb]; ring,
      by rw [SqU6.mul_c, pc, qc]; ring, by rw [SqU6.mul_d, pd, qd]; ring,
      by rw [SqU6.mul_e, pe, qe]; ring⟩
  one_mem' := ⟨rfl, rfl, rfl, rfl, rfl⟩
  inv_mem' := by
    rintro p ⟨pa, pb, pc, pd, pe⟩
    exact ⟨by rw [SqU6.inv_a, pa]; ring, by rw [SqU6.inv_b, pb]; ring,
      by rw [SqU6.inv_c, pc]; ring, by rw [SqU6.inv_d, pd]; ring,
      by rw [SqU6.inv_e, pe]; ring⟩

variable (R) in
/-- The `gamma_3`-shaped elements. -/
def gaThreeSub : Subgroup (SqU6 R) where
  carrier := {p | p.a = 0 ∧ p.b = 0 ∧ p.c = 0 ∧ p.d = 0 ∧ p.e = 0
    ∧ p.f = 0 ∧ p.g = 0 ∧ p.h = 0 ∧ p.i = 0}
  mul_mem' := by
    rintro p q ⟨pa, pb, pc, pd, pe, pf, pg, ph, pi⟩ ⟨qa, qb, qc, qd, qe, qf, qg, qh, qi⟩
    exact ⟨by rw [SqU6.mul_a, pa, qa]; ring, by rw [SqU6.mul_b, pb, qb]; ring,
      by rw [SqU6.mul_c, pc, qc]; ring, by rw [SqU6.mul_d, pd, qd]; ring,
      by rw [SqU6.mul_e, pe, qe]; ring, by rw [SqU6.mul_f, pf, qf, pa]; ring,
      by rw [SqU6.mul_g, pg, qg, pb]; ring, by rw [SqU6.mul_h, ph, qh, pc]; ring,
      by rw [SqU6.mul_i, pi, qi, pd]; ring⟩
  one_mem' := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  inv_mem' := by
    rintro p ⟨pa, pb, pc, pd, pe, pf, pg, ph, pi⟩
    exact ⟨by rw [SqU6.inv_a, pa]; ring, by rw [SqU6.inv_b, pb]; ring,
      by rw [SqU6.inv_c, pc]; ring, by rw [SqU6.inv_d, pd]; ring,
      by rw [SqU6.inv_e, pe]; ring, by rw [SqU6.inv_f, pf, pa, pb]; ring,
      by rw [SqU6.inv_g, pg, pb, pc]; ring, by rw [SqU6.inv_h, ph, pc, pd]; ring,
      by rw [SqU6.inv_i, pi, pd, pe]; ring⟩

variable (R) in
/-- The `gamma_4`-shaped elements, `GradedFiveDefect.SqU6.IsGaFour` as a subgroup. -/
def gaFourSub : Subgroup (SqU6 R) where
  carrier := {p | p.IsGaFour}
  mul_mem' := by
    rintro p q ⟨pa, pb, pc, pd, pe, pf, pg, ph, pi, pj, pk, pl⟩
      ⟨qa, qb, qc, qd, qe, qf, qg, qh, qi, qj, qk, ql⟩
    exact ⟨by rw [SqU6.mul_a, pa, qa]; ring, by rw [SqU6.mul_b, pb, qb]; ring,
      by rw [SqU6.mul_c, pc, qc]; ring, by rw [SqU6.mul_d, pd, qd]; ring,
      by rw [SqU6.mul_e, pe, qe]; ring, by rw [SqU6.mul_f, pf, qf, pa]; ring,
      by rw [SqU6.mul_g, pg, qg, pb]; ring, by rw [SqU6.mul_h, ph, qh, pc]; ring,
      by rw [SqU6.mul_i, pi, qi, pd]; ring, by rw [SqU6.mul_j, pj, qj, pa, pf]; ring,
      by rw [SqU6.mul_k, pk, qk, pb, pg]; ring, by rw [SqU6.mul_l, pl, ql, pc, ph]; ring⟩
  one_mem' := SqU6.isGaFour_one
  inv_mem' := by
    rintro p ⟨pa, pb, pc, pd, pe, pf, pg, ph, pi, pj, pk, pl⟩
    exact ⟨by rw [SqU6.inv_a, pa]; ring, by rw [SqU6.inv_b, pb]; ring,
      by rw [SqU6.inv_c, pc]; ring, by rw [SqU6.inv_d, pd]; ring,
      by rw [SqU6.inv_e, pe]; ring, by rw [SqU6.inv_f, pf, pa, pb]; ring,
      by rw [SqU6.inv_g, pg, pb, pc]; ring, by rw [SqU6.inv_h, ph, pc, pd]; ring,
      by rw [SqU6.inv_i, pi, pd, pe]; ring,
      by rw [SqU6.inv_j, pj, pa, pb, pc, pf, pg]; ring,
      by rw [SqU6.inv_k, pk, pb, pc, pd, pg, ph]; ring,
      by rw [SqU6.inv_l, pl, pc, pd, pe, ph, pi]; ring⟩

theorem mem_gaFourSub {p : SqU6 R} : p ∈ gaFourSub R ↔ p.IsGaFour := Iff.rfl

end Shape

section ShapeChain

/-- Every commutator is `gamma_2`-shaped. -/
theorem gaTwoSub_of_commutator (p q : SqU6 gr3R) : ⁅p, q⁆ ∈ gaTwoSub gr3R := by
  rw [commutatorElement_eq_commP]
  exact ⟨SqU6.commP_a _ _, SqU6.commP_b _ _, SqU6.commP_c _ _, SqU6.commP_d _ _,
    SqU6.commP_e _ _⟩

/-- A commutator of a `gamma_2`-shaped element against **anything** is `gamma_3`-shaped. -/
theorem gaThreeSub_of_commutator {p : SqU6 gr3R} (hp : p ∈ gaTwoSub gr3R) (q : SqU6 gr3R) :
    ⁅p, q⁆ ∈ gaThreeSub gr3R := by
  obtain ⟨pa, pb, pc, pd, pe⟩ := hp
  rw [commutatorElement_eq_commP]
  refine ⟨SqU6.commP_a _ _, SqU6.commP_b _ _, SqU6.commP_c _ _, SqU6.commP_d _ _,
    SqU6.commP_e _ _, ?_, ?_, ?_, ?_⟩
  · simp only [SqU6.commP_f, SqU6.inv_a, SqU6.inv_b, pa, pb]; ring
  · simp only [SqU6.commP_g, SqU6.inv_b, SqU6.inv_c, pb, pc]; ring
  · simp only [SqU6.commP_h, SqU6.inv_c, SqU6.inv_d, pc, pd]; ring
  · simp only [SqU6.commP_i, SqU6.inv_d, SqU6.inv_e, pd, pe]; ring

/-- A commutator of a `gamma_3`-shaped element against **anything** is `gamma_4`-shaped. -/
theorem gaFourSub_of_commutator {p : SqU6 gr3R} (hp : p ∈ gaThreeSub gr3R) (q : SqU6 gr3R) :
    ⁅p, q⁆ ∈ gaFourSub gr3R := by
  obtain ⟨pa, pb, pc, pd, pe, pf, pg, ph, pi⟩ := hp
  rw [commutatorElement_eq_commP]
  refine ⟨SqU6.commP_a _ _, SqU6.commP_b _ _, SqU6.commP_c _ _, SqU6.commP_d _ _,
    SqU6.commP_e _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [SqU6.commP_f, SqU6.inv_a, SqU6.inv_b, pa, pb]; ring
  · simp only [SqU6.commP_g, SqU6.inv_b, SqU6.inv_c, pb, pc]; ring
  · simp only [SqU6.commP_h, SqU6.inv_c, SqU6.inv_d, pc, pd]; ring
  · simp only [SqU6.commP_i, SqU6.inv_d, SqU6.inv_e, pd, pe]; ring
  · simp only [SqU6.commP_j, SqU6.u6Comm3L, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_f,
      SqU6.inv_g, pa, pb, pc, pf, pg]
    ring
  · simp only [SqU6.commP_k, SqU6.u6Comm3M, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d, SqU6.inv_g,
      SqU6.inv_h, pb, pc, pd, pg, ph]
    ring
  · simp only [SqU6.commP_l, SqU6.u6Comm3R, SqU6.inv_c, SqU6.inv_d, SqU6.inv_e, SqU6.inv_h,
      SqU6.inv_i, pc, pd, pe, ph, pi]
    ring

/-- **EVERY achievable class-four dressing is `gamma_4`-SHAPED**, at every marking and with no
evenness hypothesis whatsoever.  `GradedFiveForce.forceN4_isGaFour` extracts the same shape
from the even-`(3,4)`-column hypothesis; this says the shape never needed it, which is what
lets the characterisation below run at markings wave 59's soundness chain cannot reach. -/
theorem forceLcs_three_le_gaFourSub (H : Subgroup (SqU6 gr3R)) :
    forceLcs H 3 ≤ gaFourSub gr3R := by
  have h1 : forceLcs H 1 ≤ gaTwoSub gr3R :=
    Subgroup.commutator_le.mpr fun p _ q _ => gaTwoSub_of_commutator p q
  have h2 : forceLcs H 2 ≤ gaThreeSub gr3R :=
    Subgroup.commutator_le.mpr fun p hp q _ => gaThreeSub_of_commutator (h1 hp) q
  exact Subgroup.commutator_le.mpr fun p hp q _ => gaFourSub_of_commutator (h2 hp) q

/-- …stated as the shape predicate the translation identity consumes. -/
theorem isGaFour_of_mem_forceLcs {H : Subgroup (SqU6 gr3R)} {z : SqU6 gr3R}
    (hz : z ∈ forceLcs H 3) : z.IsGaFour :=
  forceLcs_three_le_gaFourSub H hz

end ShapeChain

/-! ## 3 The forcing at the sharpest hypothesis, and the kill from an odd pairing -/

section SharpForcing

variable {h : ℕ} {j : Fin h} {m : Fin (sqRank h) → SqU6 gr3R} {z₀ w₁ w₂ z₃ z₄ : SqU6 gr3R}

/-- Reading the class-five residue off a killed frame. -/
private theorem o_of_kill_liftC6 {p : SqU6 gr3R} {w : gr3R} (hp : p * liftC6 w = 1) :
    p.o = -w := by
  have hq := congrArg SqU6.o hp
  rw [mul_liftC6_apply] at hq
  simp only [SqU6.one_o] at hq
  exact eq_neg_of_add_eq_zero_left hq

/-- **THE FORCING, at the sharpest hypothesis the tree can state.**  At **any** marking, a
five-slot class-five refinement whose three class-four moves pair evenly against the slots'
outer abelian columns leaves the class-five residue even.  The exponent-slot part of the
increment, `-4 w1.o + 2 w2.o`, is even for free, and the pairing is the whole remainder.

`GradedFiveForce.fiveWit_sigma_forced` is the special case in which the pairing is even
because all six of its terms are; that route needs the even-`(3,4)`-column hypothesis and
this one needs nothing. -/
theorem fiveSigma_forced_of_pair (hz₀ : z₀.IsGaFour) (hw₁ : w₁.IsGaFive) (hw₂ : w₂.IsGaFive)
    (hz₃ : z₃.IsGaFour) (hz₄ : z₄.IsGaFour)
    (hp : ∃ k : gr3R, fiveIncrPair m j z₀ z₃ z₄ = 2 * k)
    (hkill : sqRelWord (fiveLift j m z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (sqRelWord m).o = 0 := by
  obtain ⟨k, hk⟩ := hp
  rw [sqRelWord_fiveLift hz₀ hw₁ hw₂ hz₃ hz₄] at hkill
  have ho := o_of_kill_liftC6 hkill
  have heven : (sqRelWord m).o = 2 * (-(k - 2 * w₁.o + w₂.o)) := by
    rw [ho]
    simp only [fiveIncrPair] at hk
    linear_combination -hk
  rw [heven, selPar_two_mul]

/-- **AN ODD PAIRING PRODUCES A KILL.**  At any marking whose relator is a **central**
translation `liftC6 c`, and any three `gamma_4`-shaped moves whose pairing satisfies
`c + pair = 2 t`, the refinement with trivial sigma-exponent move and second exponent move
`liftC6 (-t)` **kills the relator**.  Nothing is assumed about the letters, the lattice or
achievability: the even part of the increment is fully tunable by the class-five exponent
slot, so the pairing's parity is the only obstruction to a kill. -/
theorem fiveKill_of_pair {c t : gr3R} (hz₀ : z₀.IsGaFour) (hz₃ : z₃.IsGaFour)
    (hz₄ : z₄.IsGaFour) (hres : sqRelWord m = liftC6 c)
    (ht : c + fiveIncrPair m j z₀ z₃ z₄ = 2 * t) :
    sqRelWord (fiveLift j m z₀ 1 (liftC6 (-t)) z₃ z₄) = 1 := by
  rw [sqRelWord_fiveLift hz₀ SqU6.isGaFive_one (liftC6_isGaFive (-t)) hz₃ hz₄, hres,
    liftC6_mul_liftC6]
  refine Eq.trans (congrArg liftC6 ?_) liftC6_zero
  simp only [fiveIncrPair] at ht
  simp only [SqU6.one_o, liftC6_o]
  linear_combination ht

/-- **THE FORCING FAILS WHENEVER THE PAIRING IS ODD.**  At a marking whose relator is a
central translation with an **odd** residue, any three `gamma_4`-shaped moves with odd pairing
give an explicit five-slot refinement killing the relator.  With the previous theorem this
makes the pairing the sharp line. -/
theorem fiveKill_of_pair_odd {c : gr3R} (hz₀ : z₀.IsGaFour) (hz₃ : z₃.IsGaFour)
    (hz₄ : z₄.IsGaFour) (hres : sqRelWord m = liftC6 c) (hc : selPar c = 1)
    (hodd : ¬ ∃ k : gr3R, fiveIncrPair m j z₀ z₃ z₄ = 2 * k) :
    ∃ w₂ : SqU6 gr3R, w₂.IsGaFive ∧
      sqRelWord (fiveLift j m z₀ 1 w₂ z₃ z₄) = 1 := by
  have hpodd : selPar (fiveIncrPair m j z₀ z₃ z₄) = 1 :=
    (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _
      (fun h0 => hodd ((selPar_eq_zero_iff _).mp h0))
  obtain ⟨t, ht⟩ := (selPar_eq_zero_iff (c + fiveIncrPair m j z₀ z₃ z₄)).mp
    (by rw [selPar_add, hc, hpodd]; decide)
  exact ⟨liftC6 (-t), liftC6_isGaFive _, fiveKill_of_pair hz₀ hz₃ hz₄ hres ht⟩

end SharpForcing

/-! ## 4 The two properties, and the characterisation -/

section Characterisation

variable {h : ℕ} {j : Fin h} {m : Fin (sqRank h) → SqU6 gr3R}

/-- **The class-five sigma forcing at a marking**, in exactly the shape
`GradedFiveForce.fiveWit_sigma_forced` proves and `sqRelWord_fiveWit_diag_ne_one` negates:
every achievable five-slot class-five refinement that kills the relator leaves an even
class-five residue. -/
def FiveForces {h : ℕ} (m : Fin (sqRank h) → SqU6 gr3R) (j : Fin h) : Prop :=
  ∀ z₀ w₁ w₂ z₃ z₄ : SqU6 gr3R,
    z₀ ∈ forceLcs (Subgroup.closure (Set.range m)) 3 → w₁.IsGaFive → w₂.IsGaFive →
    z₃ ∈ forceLcs (Subgroup.closure (Set.range m)) 3 →
    z₄ ∈ forceLcs (Subgroup.closure (Set.range m)) 3 →
    sqRelWord (fiveLift j m z₀ w₁ w₂ z₃ z₄) = 1 → selPar (sqRelWord m).o = 0

/-- **THE SHARP INVARIANT.**  All three mod-`2` covectors `((m 1).e, (m 1).a)`, `(V.e, V.a)`
and `(U.e, U.a)` annihilate the class-four parity image of `gamma_4` of the marking's image:
every achievable class-four dressing pairs **evenly** against each slot's outer abelian
columns.  Class four had two covectors, because the committed gauge made the sigma-slot term
even for free; at class five the `x0`-slot's fifth abelian column is exactly the datum that
escapes the gauge, so there are three. -/
def FiveOrth {h : ℕ} (m : Fin (sqRank h) → SqU6 gr3R) (j : Fin h) : Prop :=
  ∀ z ∈ forceLcs (Subgroup.closure (Set.range m)) 3,
    (∃ k : gr3R, fiveIncrPair m j z 1 1 = 2 * k)
      ∧ (∃ k : gr3R, fiveIncrPair m j 1 z 1 = 2 * k)
      ∧ (∃ k : gr3R, fiveIncrPair m j 1 1 z = 2 * k)

/-- The invariant gives the pairing hypothesis on any achievable triple, by additivity. -/
theorem FiveOrth.triple (hO : FiveOrth m j) {z₀ z₃ z₄ : SqU6 gr3R}
    (h₀ : z₀ ∈ forceLcs (Subgroup.closure (Set.range m)) 3)
    (h₃ : z₃ ∈ forceLcs (Subgroup.closure (Set.range m)) 3)
    (h₄ : z₄ ∈ forceLcs (Subgroup.closure (Set.range m)) 3) :
    ∃ k : gr3R, fiveIncrPair m j z₀ z₃ z₄ = 2 * k := by
  obtain ⟨k₀, hk₀⟩ := (hO z₀ h₀).1
  obtain ⟨k₃, hk₃⟩ := (hO z₃ h₃).2.1
  obtain ⟨k₄, hk₄⟩ := (hO z₄ h₄).2.2
  exact ⟨k₀ + k₃ + k₄, by rw [fiveIncrPair_eq_add, hk₀, hk₃, hk₄]; ring⟩

/-- **THE INVARIANT SUFFICES.** -/
theorem fiveForces_of_fiveOrth (hO : FiveOrth m j) : FiveForces m j :=
  fun _ _ _ _ _ h₀ hw₁ hw₂ h₃ h₄ hkill =>
    fiveSigma_forced_of_pair (isGaFour_of_mem_forceLcs h₀) hw₁ hw₂
      (isGaFour_of_mem_forceLcs h₃) (isGaFour_of_mem_forceLcs h₄) (hO.triple h₀ h₃ h₄) hkill

/-- **THE INVARIANT IS NECESSARY**, at any marking whose relator is a central translation with
an odd residue: an achievable move failing any one of the three orthogonalities gives an
explicit refinement killing the relator. -/
theorem fiveOrth_of_fiveForces {c : gr3R} (hres : sqRelWord m = liftC6 c) (hc : selPar c = 1)
    (hF : FiveForces m j) : FiveOrth m j := by
  have hres1 : selPar (sqRelWord m).o = 1 := by rw [hres, liftC6_o]; exact hc
  intro z hz
  have hz4 : z.IsGaFour := isGaFour_of_mem_forceLcs hz
  refine ⟨?_, ?_, ?_⟩
  · by_contra hodd
    obtain ⟨w₂, hw₂, hkill⟩ := fiveKill_of_pair_odd (j := j) (z₀ := z) (z₃ := 1) (z₄ := 1)
      hz4 SqU6.isGaFour_one SqU6.isGaFour_one hres hc hodd
    rw [hF z 1 w₂ 1 1 hz SqU6.isGaFive_one hw₂ (one_mem _) (one_mem _) hkill] at hres1
    exact absurd hres1 (by decide)
  · by_contra hodd
    obtain ⟨w₂, hw₂, hkill⟩ := fiveKill_of_pair_odd (j := j) (z₀ := 1) (z₃ := z) (z₄ := 1)
      SqU6.isGaFour_one hz4 SqU6.isGaFour_one hres hc hodd
    rw [hF 1 1 w₂ z 1 (one_mem _) SqU6.isGaFive_one hw₂ hz (one_mem _) hkill] at hres1
    exact absurd hres1 (by decide)
  · by_contra hodd
    obtain ⟨w₂, hw₂, hkill⟩ := fiveKill_of_pair_odd (j := j) (z₀ := 1) (z₃ := 1) (z₄ := z)
      SqU6.isGaFour_one SqU6.isGaFour_one hz4 hres hc hodd
    rw [hF 1 1 w₂ 1 z (one_mem _) SqU6.isGaFive_one hw₂ (one_mem _) hz hkill] at hres1
    exact absurd hres1 (by decide)

/-- **THE CHARACTERISATION.**  At any marking whose relator is a central translation with an
odd class-five residue, the class-five sigma forcing holds **exactly** when the sharp
invariant does. -/
theorem fiveForces_iff_fiveOrth {c : gr3R} (hres : sqRelWord m = liftC6 c) (hc : selPar c = 1) :
    FiveForces m j ↔ FiveOrth m j :=
  ⟨fiveOrth_of_fiveForces hres hc, fiveForces_of_fiveOrth⟩

/-- **Wave 59's condition is SUFFICIENT.**  A marking whose image lies in
`GradedFiveForce.forceN1` satisfies the sharp invariant, because there every achievable
class-four dressing is even in both coordinates. -/
theorem fiveOrth_of_le_forceN1 (hle : Subgroup.closure (Set.range m) ≤ forceN1) :
    FiveOrth m j := by
  have hone : (∃ a : gr3R, (1 : SqU6 gr3R).m = 2 * a)
      ∧ ∃ b : gr3R, (1 : SqU6 gr3R).n = 2 * b :=
    ⟨⟨0, by rw [SqU6.one_m]; ring⟩, 0, by rw [SqU6.one_n]; ring⟩
  intro z hz
  have hev := forceN4_even (forceLcs_three_le_forceN4 hle hz)
  exact ⟨fiveIncrPair_even_of_moves_even hev hone hone,
    fiveIncrPair_even_of_moves_even hone hev hone,
    fiveIncrPair_even_of_moves_even hone hone hev⟩

/-- **A second, DUAL sufficient condition, which no wave has used**: the three slots have even
outer abelian columns, and the achievable lattice is not consulted at all. -/
theorem fiveOrth_of_slots_even
    (hXe : ∃ k : gr3R, (m 1).e = 2 * k) (hXa : ∃ k : gr3R, (m 1).a = 2 * k)
    (hVe : ∃ k : gr3R, (m (sqHandleIdxV j)).e = 2 * k)
    (hVa : ∃ k : gr3R, (m (sqHandleIdxV j)).a = 2 * k)
    (hUe : ∃ k : gr3R, (m (sqHandleIdxU j)).e = 2 * k)
    (hUa : ∃ k : gr3R, (m (sqHandleIdxU j)).a = 2 * k) : FiveOrth m j :=
  fun _ _ => ⟨fiveIncrPair_even_of_slots_even hXe hXa hVe hVa hUe hUa,
    fiveIncrPair_even_of_slots_even hXe hXa hVe hVa hUe hUa,
    fiveIncrPair_even_of_slots_even hXe hXa hVe hVa hUe hUa⟩

/-- **HALF the achievable evenness is enough when the three slots have an even OUTERMOST
column.**  Then all three covectors read only the moves' second class-four coordinate. -/
theorem fiveOrth_of_gaFour_n_even
    (hXe : ∃ k : gr3R, (m 1).e = 2 * k) (hVe : ∃ k : gr3R, (m (sqHandleIdxV j)).e = 2 * k)
    (hUe : ∃ k : gr3R, (m (sqHandleIdxU j)).e = 2 * k)
    (hn : ∀ z ∈ forceLcs (Subgroup.closure (Set.range m)) 3, ∃ k : gr3R, z.n = 2 * k) :
    FiveOrth m j := by
  have hone : ∃ b : gr3R, (1 : SqU6 gr3R).n = 2 * b := ⟨0, by rw [SqU6.one_n]; ring⟩
  intro z hz
  exact ⟨fiveIncrPair_even_of_slotE_even hXe hVe hUe (hn z hz) hone hone,
    fiveIncrPair_even_of_slotE_even hXe hVe hUe hone (hn z hz) hone,
    fiveIncrPair_even_of_slotE_even hXe hVe hUe hone hone (hn z hz)⟩

/-- …and the mirror half, when the three slots have an even FIRST abelian column. -/
theorem fiveOrth_of_gaFour_m_even
    (hXa : ∃ k : gr3R, (m 1).a = 2 * k) (hVa : ∃ k : gr3R, (m (sqHandleIdxV j)).a = 2 * k)
    (hUa : ∃ k : gr3R, (m (sqHandleIdxU j)).a = 2 * k)
    (hm : ∀ z ∈ forceLcs (Subgroup.closure (Set.range m)) 3, ∃ k : gr3R, z.m = 2 * k) :
    FiveOrth m j := by
  have hone : ∃ b : gr3R, (1 : SqU6 gr3R).m = 2 * b := ⟨0, by rw [SqU6.one_m]; ring⟩
  intro z hz
  exact ⟨fiveIncrPair_even_of_slotA_even hXa hVa hUa (hm z hz) hone hone,
    fiveIncrPair_even_of_slotA_even hXa hVa hUa hone (hm z hz) hone,
    fiveIncrPair_even_of_slotA_even hXa hVa hUa hone hone (hm z hz)⟩

end Characterisation

/-! ## 5 A second soundness chain: an even FIFTH abelian column controls only `n` -/

section EvenE

variable {R : Type} [CommRing R]

variable (R) in
/-- **`E_1`**: an even fifth abelian column `x_{56}`.  This is `GradedFiveForce.forceN1` with
the `(3,4)`-column replaced by the `(5,6)`-column, and unlike that one it controls only ONE of
the two class-four coordinates. -/
def fiveEvenE : Subgroup (SqU6 R) where
  carrier := {z | ∃ t : R, z.e = 2 * t}
  mul_mem' := by
    rintro p q ⟨s, hs⟩ ⟨t, ht⟩
    exact ⟨s + t, by rw [SqU6.mul_e, hs, ht]; ring⟩
  one_mem' := ⟨0, by rw [SqU6.one_e]; ring⟩
  inv_mem' := by
    rintro p ⟨s, hs⟩
    exact ⟨-s, by rw [SqU6.inv_e, hs]; ring⟩

variable (R) in
/-- **`E_2`**: a `gamma_2`-element whose FOURTH class-two coordinate is even. -/
def fiveEvenI : Subgroup (SqU6 R) where
  carrier := {z | z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0 ∧ ∃ t : R, z.i = 2 * t}
  mul_mem' := by
    rintro p q ⟨pa, pb, pc, pd, pe, s, hs⟩ ⟨qa, qb, qc, qd, qe, t, ht⟩
    exact ⟨by rw [SqU6.mul_a, pa, qa]; ring, by rw [SqU6.mul_b, pb, qb]; ring,
      by rw [SqU6.mul_c, pc, qc]; ring, by rw [SqU6.mul_d, pd, qd]; ring,
      by rw [SqU6.mul_e, pe, qe]; ring, s + t, by rw [SqU6.mul_i, hs, ht, pd]; ring⟩
  one_mem' := ⟨rfl, rfl, rfl, rfl, rfl, 0, by rw [SqU6.one_i]; ring⟩
  inv_mem' := by
    rintro p ⟨pa, pb, pc, pd, pe, s, hs⟩
    exact ⟨by rw [SqU6.inv_a, pa]; ring, by rw [SqU6.inv_b, pb]; ring,
      by rw [SqU6.inv_c, pc]; ring, by rw [SqU6.inv_d, pd]; ring,
      by rw [SqU6.inv_e, pe]; ring, -s, by rw [SqU6.inv_i, hs, pd, pe]; ring⟩

variable (R) in
/-- **`E_3`**: a `gamma_3`-element whose THIRD class-three coordinate is even. -/
def fiveEvenL : Subgroup (SqU6 R) where
  carrier := {z | z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0 ∧ z.f = 0 ∧ z.g = 0
    ∧ z.h = 0 ∧ z.i = 0 ∧ ∃ t : R, z.l = 2 * t}
  mul_mem' := by
    rintro p q ⟨pa, pb, pc, pd, pe, pf, pg, ph, pi, s, hs⟩
      ⟨qa, qb, qc, qd, qe, qf, qg, qh, qi, t, ht⟩
    exact ⟨by rw [SqU6.mul_a, pa, qa]; ring, by rw [SqU6.mul_b, pb, qb]; ring,
      by rw [SqU6.mul_c, pc, qc]; ring, by rw [SqU6.mul_d, pd, qd]; ring,
      by rw [SqU6.mul_e, pe, qe]; ring, by rw [SqU6.mul_f, pf, qf, pa]; ring,
      by rw [SqU6.mul_g, pg, qg, pb]; ring, by rw [SqU6.mul_h, ph, qh, pc]; ring,
      by rw [SqU6.mul_i, pi, qi, pd]; ring, s + t, by rw [SqU6.mul_l, hs, ht, pc, ph]; ring⟩
  one_mem' := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, 0, by rw [SqU6.one_l]; ring⟩
  inv_mem' := by
    rintro p ⟨pa, pb, pc, pd, pe, pf, pg, ph, pi, s, hs⟩
    exact ⟨by rw [SqU6.inv_a, pa]; ring, by rw [SqU6.inv_b, pb]; ring,
      by rw [SqU6.inv_c, pc]; ring, by rw [SqU6.inv_d, pd]; ring,
      by rw [SqU6.inv_e, pe]; ring, by rw [SqU6.inv_f, pf, pa, pb]; ring,
      by rw [SqU6.inv_g, pg, pb, pc]; ring, by rw [SqU6.inv_h, ph, pc, pd]; ring,
      by rw [SqU6.inv_i, pi, pd, pe]; ring,
      -s, by rw [SqU6.inv_l, hs, pc, pd, pe, ph, pi]; ring⟩

variable (R) in
/-- **`E_4`**: a `gamma_4`-element whose SECOND class-four coordinate is even.  Nothing is
claimed about the first, and at the half point of section 7 the first is genuinely odd. -/
def fiveEvenN : Subgroup (SqU6 R) where
  carrier := {z | z.IsGaFour ∧ ∃ t : R, z.n = 2 * t}
  mul_mem' := by
    rintro p q hp hq
    obtain ⟨⟨pa, pb, pc, pd, pe, pf, pg, ph, pi, pj, pk, pl⟩, s, hs⟩ := id hp
    obtain ⟨-, t, ht⟩ := id hq
    exact ⟨(gaFourSub R).mul_mem hp.1 hq.1, s + t,
      by rw [SqU6.mul_n, hs, ht, pb, pg, pk]; ring⟩
  one_mem' := ⟨SqU6.isGaFour_one, 0, by rw [SqU6.one_n]; ring⟩
  inv_mem' := by
    rintro p hp
    obtain ⟨⟨pa, pb, pc, pd, pe, pf, pg, ph, pi, pj, pk, pl⟩, s, hs⟩ := id hp
    exact ⟨(gaFourSub R).inv_mem hp.1, -s,
      by rw [SqU6.inv_n, hs, pb, pc, pd, pe, pg, ph, pi, pk, pl]; ring⟩

theorem mem_fiveEvenE {z : SqU6 R} : z ∈ fiveEvenE R ↔ ∃ t : R, z.e = 2 * t := Iff.rfl

theorem fiveEvenN_even {z : SqU6 R} (hz : z ∈ fiveEvenN R) : ∃ t : R, z.n = 2 * t := hz.2

end EvenE

section EvenEChain

/-- **Step one**: a commutator of two elements with even fifth abelian columns has an even
fourth class-two coordinate.  The pairing is `p.d * q.e - p.e * q.d`, and both terms meet the
even column. -/
theorem fiveEvenI_of_commutator {p q : SqU6 gr3R} (hp : p ∈ fiveEvenE gr3R)
    (hq : q ∈ fiveEvenE gr3R) : ⁅p, q⁆ ∈ fiveEvenI gr3R := by
  obtain ⟨s, hs⟩ := mem_fiveEvenE.mp hp
  obtain ⟨t, ht⟩ := mem_fiveEvenE.mp hq
  rw [commutatorElement_eq_commP]
  refine ⟨SqU6.commP_a _ _, SqU6.commP_b _ _, SqU6.commP_c _ _, SqU6.commP_d _ _,
    SqU6.commP_e _ _, -(p⁻¹.d * t) + s * q⁻¹.d, ?_⟩
  simp only [SqU6.commP_i, SqU6.inv_d, SqU6.inv_e, hs, ht]
  ring

/-- **Step two**: pairing such a `gamma_2`-element against an even fifth column gives a
`gamma_3`-element with an even third class-three coordinate; the surviving pairing is
`-z.i * q.c + z.h * q.e`, and its two terms meet the two evennesses. -/
theorem fiveEvenL_of_commutator {p q : SqU6 gr3R} (hp : p ∈ fiveEvenI gr3R)
    (hq : q ∈ fiveEvenE gr3R) : ⁅p, q⁆ ∈ fiveEvenL gr3R := by
  obtain ⟨pa, pb, pc, pd, pe, s, hs⟩ := hp
  obtain ⟨t, ht⟩ := mem_fiveEvenE.mp hq
  rw [commutatorElement_eq_commP]
  refine ⟨SqU6.commP_a _ _, SqU6.commP_b _ _, SqU6.commP_c _ _, SqU6.commP_d _ _,
    SqU6.commP_e _ _, ?_, ?_, ?_, ?_, s * q⁻¹.c - p⁻¹.h * t, ?_⟩
  · simp only [SqU6.commP_f, SqU6.inv_a, SqU6.inv_b, pa, pb]; ring
  · simp only [SqU6.commP_g, SqU6.inv_b, SqU6.inv_c, pb, pc]; ring
  · simp only [SqU6.commP_h, SqU6.inv_c, SqU6.inv_d, pc, pd]; ring
  · simp only [SqU6.commP_i, SqU6.inv_d, SqU6.inv_e, pd, pe]; ring
  · simp only [SqU6.commP_l, SqU6.u6Comm3R, SqU6.inv_c, SqU6.inv_d, SqU6.inv_e, SqU6.inv_h,
      SqU6.inv_i, pc, pd, pe, hs, ht]
    ring

/-- **Step three**: pairing such a `gamma_3`-element against an even fifth column gives a
`gamma_4`-element with an even SECOND class-four coordinate.  The pairing is
`z.k * q.e - z.l * q.b`: the first term meets the column, the second meets step two.  The
first class-four coordinate's pairing `z.j * q.d - z.k * q.a` is untouched. -/
theorem fiveEvenN_of_commutator {p q : SqU6 gr3R} (hp : p ∈ fiveEvenL gr3R)
    (hq : q ∈ fiveEvenE gr3R) : ⁅p, q⁆ ∈ fiveEvenN gr3R := by
  have hshape : ⁅p, q⁆ ∈ gaFourSub gr3R :=
    gaFourSub_of_commutator ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1,
      hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.1⟩ q
  obtain ⟨pa, pb, pc, pd, pe, pf, pg, ph, pi, s, hs⟩ := hp
  obtain ⟨t, ht⟩ := mem_fiveEvenE.mp hq
  refine ⟨hshape, -(p⁻¹.k * t) + s * q⁻¹.b, ?_⟩
  rw [commutatorElement_eq_commP]
  simp only [SqU6.commP_n, SqU6.u6Comm4R, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d, SqU6.inv_e,
    SqU6.inv_g, SqU6.inv_h, SqU6.inv_i, SqU6.inv_l, pb, pc, pd, pe, pg, ph, pi, hs, ht]
  ring

/-- **A SECOND soundness theorem, incomparable with wave 59's.**  At any marking all of whose
slots have an even FIFTH abelian column, every achievable class-four dressing is
`gamma_4`-shaped with an even SECOND class-four coordinate `x_{26}`.  The first is not
controlled, and section 7 exhibits a marking where it is odd. -/
theorem forceLcs_three_le_fiveEvenN {H : Subgroup (SqU6 gr3R)} (hH : H ≤ fiveEvenE gr3R) :
    forceLcs H 3 ≤ fiveEvenN gr3R := by
  have h1 : forceLcs H 1 ≤ fiveEvenI gr3R :=
    Subgroup.commutator_le.mpr fun p hp q hq => fiveEvenI_of_commutator (hH hp) (hH hq)
  have h2 : forceLcs H 2 ≤ fiveEvenL gr3R :=
    Subgroup.commutator_le.mpr fun p hp q hq => fiveEvenL_of_commutator (h1 hp) (hH hq)
  exact Subgroup.commutator_le.mpr fun p hp q hq => fiveEvenN_of_commutator (h2 hp) (hH hq)

/-- …read as the evenness that the sharp invariant's half version consumes. -/
theorem gaFour_n_even_of_le_fiveEvenE {H : Subgroup (SqU6 gr3R)} (hH : H ≤ fiveEvenE gr3R)
    {z : SqU6 gr3R} (hz : z ∈ forceLcs H 3) : ∃ k : gr3R, z.n = 2 * k :=
  fiveEvenN_even (forceLcs_three_le_fiveEvenN hH hz)

end EvenEChain

/-! ## 6 A marking far outside wave 59's condition at which the forcing HOLDS -/

section OrthFive

variable {h : ℕ} {j : Fin h}

/-- A repo commutator of two members lands in the commutator subgroup.  (`GradedFiveForce`'s
copy is `private`, so this one is rebuilt here.) -/
theorem commP_mem_commSub {H K : Subgroup (SqU6 gr3R)} {p q : SqU6 gr3R}
    (hp : p ∈ H) (hq : q ∈ K) : commP p q ∈ ⁅H, K⁆ := by
  have hc := Subgroup.commutator_mem_commutator (H.inv_mem hp) (K.inv_mem hq)
  rwa [commutatorElement_eq_commP, inv_inv, inv_inv] at hc

/-- The orthogonal point's sigma slot. -/
def orthFiveS : SqU6 gr3R := ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0⟩

/-- …its `x0`-slot, whose `(3,4)`-column is **odd**, so wave 59's hypothesis fails here. -/
def orthFiveX : SqU6 gr3R := ⟨0, 4, 3, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0⟩

/-- …its `x1`-slot, the layered solve of the fifteen rows. -/
def orthFiveY : SqU6 gr3R := ⟨0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 7, 0⟩

/-- …and its two handle letters, whose commutator is live. -/
def orthFiveU : SqU6 gr3R := ⟨0, 0, 0, 1, 0, 0, 6, 0, 0, 3, 0, 0, 0, 2, 0⟩

/-- The orthogonal point's `V`-letter. -/
def orthFiveV : SqU6 gr3R := ⟨0, 5, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0⟩

variable (h j) in
/-- **THE ORTHOGONAL CLASS-FIVE POINT**, at every handle count and every handle. -/
def orthFiveMark : Fin (sqRank h) → SqU6 gr3R :=
  fiveTuple gr3R h j orthFiveS orthFiveX orthFiveY orthFiveU orthFiveV

@[simp] theorem orthFiveMark_zero : orthFiveMark h j 0 = orthFiveS := fiveTuple_zero

@[simp] theorem orthFiveMark_one : orthFiveMark h j 1 = orthFiveX := fiveTuple_one

@[simp] theorem orthFiveMark_handleU : orthFiveMark h j (sqHandleIdxU j) = orthFiveU :=
  fiveTuple_handleU

@[simp] theorem orthFiveMark_handleV : orthFiveMark h j (sqHandleIdxV j) = orthFiveV :=
  fiveTuple_handleV

/-- **The relator is a central translation with an ODD residue**, at every handle count and
every handle: the point is admissible for the characterisation. -/
theorem sqRelWord_orthFiveMark : sqRelWord (orthFiveMark h j) = liftC6 1 := by
  rw [orthFiveMark, sqRelWord_fiveTuple]
  decide

/-- **The handle block is live.** -/
theorem commP_orthFive_ne_one : commP orthFiveU orthFiveV ≠ 1 := by decide

/-- ⭐⭐⭐ **ALL THREE COVECTORS VANISH**, so the increment pairing is identically zero for
**arbitrary** class-four moves, achievable or not. -/
theorem orthFive_pair_eq_zero (z₀ z₃ z₄ : SqU6 gr3R) :
    fiveIncrPair (orthFiveMark h j) j z₀ z₃ z₄ = 0 := by
  simp only [fiveIncrPair, orthFiveMark_one, orthFiveMark_handleU, orthFiveMark_handleV,
    show (orthFiveX.a : gr3R) = 0 from rfl, show (orthFiveX.e : gr3R) = 0 from rfl,
    show (orthFiveU.a : gr3R) = 0 from rfl, show (orthFiveU.e : gr3R) = 0 from rfl,
    show (orthFiveV.a : gr3R) = 0 from rfl, show (orthFiveV.e : gr3R) = 0 from rfl]
  ring

theorem orthFive_pair_even (z₀ z₃ z₄ : SqU6 gr3R) :
    ∃ k : gr3R, fiveIncrPair (orthFiveMark h j) j z₀ z₃ z₄ = 2 * k :=
  ⟨0, by rw [orthFive_pair_eq_zero]; ring⟩

/-- ⭐⭐⭐ **NO five-slot class-five refinement kills the relator at the orthogonal point**, and
the quantifier is over **every** class-four move, not merely the achievable ones: the lower
central series is never consulted.  Compare `GradedFiveForce.sqRelWord_fiveWit_diag_ne_one`,
whose quantifier is over `forceLcs … 3` and which is FALSE one filtration step wider. -/
theorem orthFive_no_kill {z₀ w₁ w₂ z₃ z₄ : SqU6 gr3R} (hz₀ : z₀.IsGaFour)
    (hw₁ : w₁.IsGaFive) (hw₂ : w₂.IsGaFive) (hz₃ : z₃.IsGaFour) (hz₄ : z₄.IsGaFour) :
    sqRelWord (fiveLift j (orthFiveMark h j) z₀ w₁ w₂ z₃ z₄) ≠ 1 := by
  intro hc
  have hp := fiveSigma_forced_of_pair hz₀ hw₁ hw₂ hz₃ hz₄ (orthFive_pair_even z₀ z₃ z₄) hc
  rw [sqRelWord_orthFiveMark, liftC6_o] at hp
  exact absurd hp (by decide)

theorem orthFive_fiveOrth : FiveOrth (orthFiveMark h j) j :=
  fun _ _ => ⟨orthFive_pair_even _ _ _, orthFive_pair_even _ _ _, orthFive_pair_even _ _ _⟩

theorem orthFive_fiveForces : FiveForces (orthFiveMark h j) j :=
  fiveForces_of_fiveOrth orthFive_fiveOrth

/-- ⭐⭐ **Wave 59's HYPOTHESIS fails**: the `x0`-slot's `(3,4)`-column is odd. -/
theorem orthFive_not_le_forceN1 :
    ¬ Subgroup.closure (Set.range (orthFiveMark h j)) ≤ forceN1 := by
  intro hle
  obtain ⟨t, ht⟩ := hle (Subgroup.subset_closure ⟨1, orthFiveMark_one⟩)
  rw [show (orthFiveX.c : gr3R) = 3 from rfl] at ht
  exact absurd ht (by revert t; decide)

/-- A four-fold commutator of the point's own letters, hence achievable. -/
theorem orthFive_quad_mem :
    commP (commP (commP orthFiveS orthFiveV) orthFiveX) orthFiveU
      ∈ forceLcs (Subgroup.closure (Set.range (orthFiveMark h j))) 3 :=
  commP_mem_commSub (commP_mem_commSub (commP_mem_commSub
    (Subgroup.subset_closure ⟨0, orthFiveMark_zero⟩)
    (Subgroup.subset_closure ⟨sqHandleIdxV j, orthFiveMark_handleV⟩))
    (Subgroup.subset_closure ⟨1, orthFiveMark_one⟩))
    (Subgroup.subset_closure ⟨sqHandleIdxU j, orthFiveMark_handleU⟩)

/-- ⭐⭐⭐ **…and it has an ODD first class-four coordinate**, so wave 59's CONCLUSION fails
too: the achievable class-four dressings are **not** contained in `forceN4`. -/
theorem orthFive_quad_not_forceN4 :
    commP (commP (commP orthFiveS orthFiveV) orthFiveX) orthFiveU ∉ forceN4 := by
  intro hc
  obtain ⟨⟨t, ht⟩, -⟩ := forceN4_even hc
  rw [show (commP (commP (commP orthFiveS orthFiveV) orthFiveX) orthFiveU).m = 7 from by
    decide] at ht
  exact absurd ht (by revert t; decide)

theorem orthFive_not_le_forceN4 :
    ¬ forceLcs (Subgroup.closure (Set.range (orthFiveMark h j))) 3 ≤ forceN4 :=
  fun hle => orthFive_quad_not_forceN4 (hle (orthFive_quad_mem (h := h) (j := j)))

/-- ⭐⭐⭐ **THE ANSWER, at one point.**  A relator-central class-five marking with an odd
residue and a live handle block, at which **both** wave 59's hypothesis and its conclusion
fail, and at which the class-five sigma forcing nevertheless holds - with no achievability
hypothesis at all. -/
theorem orthFive_separates :
    sqRelWord (orthFiveMark h j) = liftC6 1 ∧ commP orthFiveU orthFiveV ≠ 1 ∧
      ¬ Subgroup.closure (Set.range (orthFiveMark h j)) ≤ forceN1 ∧
      ¬ forceLcs (Subgroup.closure (Set.range (orthFiveMark h j))) 3 ≤ forceN4 ∧
      FiveOrth (orthFiveMark h j) j ∧ FiveForces (orthFiveMark h j) j :=
  ⟨sqRelWord_orthFiveMark, commP_orthFive_ne_one, orthFive_not_le_forceN1,
    orthFive_not_le_forceN4, orthFive_fiveOrth, orthFive_fiveForces⟩

end OrthFive

/-! ## 7 The HALF point: one covector alive, and achievability load-bearing -/

section HalfFive

variable {h : ℕ} {j : Fin h}

/-- The half point's sigma slot. -/
def halfFiveS : SqU6 gr3R := ⟨2, 0, 0, 0, 4, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- …its `x0`-slot. -/
def halfFiveX : SqU6 gr3R := ⟨0, 7, 6, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- …its `x1`-slot. -/
def halfFiveY : SqU6 gr3R := ⟨0, 2, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0, 0, 0, 0⟩

/-- …its `U`-letter, whose FIRST abelian column is **odd**, so the orthogonal route of
section 6 is unavailable: one covector really reads the moves. -/
def halfFiveU : SqU6 gr3R := ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0⟩

/-- …and its `V`-letter, whose `(3,4)`-column is **odd**. -/
def halfFiveV : SqU6 gr3R := ⟨2, 0, 3, 7, 4, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0⟩

variable (h j) in
/-- **THE HALF CLASS-FIVE POINT**, at every handle count and every handle. -/
def halfFiveMark : Fin (sqRank h) → SqU6 gr3R :=
  fiveTuple gr3R h j halfFiveS halfFiveX halfFiveY halfFiveU halfFiveV

@[simp] theorem halfFiveMark_zero : halfFiveMark h j 0 = halfFiveS := fiveTuple_zero

@[simp] theorem halfFiveMark_one : halfFiveMark h j 1 = halfFiveX := fiveTuple_one

@[simp] theorem halfFiveMark_two : halfFiveMark h j 2 = halfFiveY := fiveTuple_two

@[simp] theorem halfFiveMark_handleU : halfFiveMark h j (sqHandleIdxU j) = halfFiveU :=
  fiveTuple_handleU

@[simp] theorem halfFiveMark_handleV : halfFiveMark h j (sqHandleIdxV j) = halfFiveV :=
  fiveTuple_handleV

theorem sqRelWord_halfFiveMark : sqRelWord (halfFiveMark h j) = liftC6 3 := by
  rw [halfFiveMark, sqRelWord_fiveTuple]
  decide

theorem commP_halfFive_ne_one : commP halfFiveU halfFiveV ≠ 1 := by decide

/-- ⭐⭐ **The `U`-covector is `(0, 1)`**, so section 6's route is closed. -/
theorem halfFiveU_covector : selPar halfFiveU.e = 0 ∧ selPar halfFiveU.a = 1 := by
  exact ⟨by decide, by decide⟩

/-- **Every slot value has an even fifth abelian column**, which is the input to the second
soundness chain of section 5. -/
theorem halfFiveMark_le_fiveEvenE :
    Subgroup.closure (Set.range (halfFiveMark h j)) ≤ fiveEvenE gr3R := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · exact ⟨2, by rw [halfFiveMark_zero]; decide⟩
  · exact ⟨1, by rw [halfFiveMark_one]; decide⟩
  · exact ⟨0, by rw [halfFiveMark_two]; decide⟩
  · by_cases hj : j' = j
    · subst hj
      exact ⟨0, by rw [halfFiveMark_handleU]; decide⟩
    · exact ⟨0, by rw [halfFiveMark, fiveTuple_handleU_ne hj]; decide⟩
  · by_cases hj : j' = j
    · subst hj
      exact ⟨2, by rw [halfFiveMark_handleV]; decide⟩
    · exact ⟨0, by rw [halfFiveMark, fiveTuple_handleV_ne hj]; decide⟩

/-- ⭐⭐ **Every achievable class-four dressing has an even SECOND coordinate**, by the
even-fifth-column chain.  The FIRST is not even, and the next theorem shows it. -/
theorem halfFive_gaFour_n_even {z : SqU6 gr3R}
    (hz : z ∈ forceLcs (Subgroup.closure (Set.range (halfFiveMark h j))) 3) :
    ∃ k : gr3R, z.n = 2 * k :=
  gaFour_n_even_of_le_fiveEvenE halfFiveMark_le_fiveEvenE hz

/-- ⭐⭐⭐ **THE SHARP INVARIANT HOLDS AT THE HALF POINT**, through a genuinely different
route: all three slots have an even fifth abelian column, so the three covectors read only the
moves' second class-four coordinate, which the even-fifth-column chain makes even. -/
theorem halfFive_fiveOrth : FiveOrth (halfFiveMark h j) j :=
  fiveOrth_of_gaFour_n_even ⟨1, by rw [halfFiveMark_one]; decide⟩
    ⟨2, by rw [halfFiveMark_handleV]; decide⟩ ⟨0, by rw [halfFiveMark_handleU]; decide⟩
    (fun _ hz => halfFive_gaFour_n_even hz)

theorem halfFive_fiveForces : FiveForces (halfFiveMark h j) j :=
  fiveForces_of_fiveOrth halfFive_fiveOrth

theorem halfFive_not_le_forceN1 :
    ¬ Subgroup.closure (Set.range (halfFiveMark h j)) ≤ forceN1 := by
  intro hle
  obtain ⟨t, ht⟩ := hle (Subgroup.subset_closure ⟨sqHandleIdxV j, halfFiveMark_handleV⟩)
  rw [show (halfFiveV.c : gr3R) = 3 from rfl] at ht
  exact absurd ht (by revert t; decide)

theorem halfFive_quad_mem :
    commP (commP (commP halfFiveX halfFiveU) halfFiveV) halfFiveV
      ∈ forceLcs (Subgroup.closure (Set.range (halfFiveMark h j))) 3 :=
  commP_mem_commSub (commP_mem_commSub (commP_mem_commSub
    (Subgroup.subset_closure ⟨1, halfFiveMark_one⟩)
    (Subgroup.subset_closure ⟨sqHandleIdxU j, halfFiveMark_handleU⟩))
    (Subgroup.subset_closure ⟨sqHandleIdxV j, halfFiveMark_handleV⟩))
    (Subgroup.subset_closure ⟨sqHandleIdxV j, halfFiveMark_handleV⟩)

theorem halfFive_quad_not_forceN4 :
    commP (commP (commP halfFiveX halfFiveU) halfFiveV) halfFiveV ∉ forceN4 := by
  intro hc
  obtain ⟨⟨t, ht⟩, -⟩ := forceN4_even hc
  rw [show (commP (commP (commP halfFiveX halfFiveU) halfFiveV) halfFiveV).m = 5 from by
    decide] at ht
  exact absurd ht (by revert t; decide)

theorem halfFive_not_le_forceN4 :
    ¬ forceLcs (Subgroup.closure (Set.range (halfFiveMark h j))) 3 ≤ forceN4 :=
  fun hle => halfFive_quad_not_forceN4 (hle (halfFive_quad_mem (h := h) (j := j)))

/-! ### At the half point achievability is LOAD-BEARING -/

/-- The class-four move with second coordinate `1`: **not** achievable at the half point. -/
def halfFiveMove : SqU6 gr3R := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩

theorem halfFiveMove_isGaFour : halfFiveMove.IsGaFour :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem halfFiveMove_not_mem :
    halfFiveMove ∉ forceLcs (Subgroup.closure (Set.range (halfFiveMark h j))) 3 := by
  intro hc
  obtain ⟨k, hk⟩ := halfFive_gaFour_n_even hc
  rw [show (halfFiveMove.n : gr3R) = 1 from rfl] at hk
  exact absurd hk (by revert k; decide)

/-- ⭐⭐⭐ **An UNACHIEVABLE move kills the relator at the half point.**  Dressing the handle-`V`
slot by `halfFiveMove` pairs oddly against `U`'s odd first abelian column, and the class-five
exponent slot absorbs the rest.  So the half point's forcing genuinely consumes achievability,
unlike section 6's, and the sharp invariant is the exact place where it does. -/
theorem halfFive_unrestricted_kill :
    sqRelWord (fiveLift j (halfFiveMark h j) 1 1 (liftC6 (-2)) 1 halfFiveMove) = 1 :=
  fiveKill_of_pair (t := 2) SqU6.isGaFour_one SqU6.isGaFour_one halfFiveMove_isGaFour
    sqRelWord_halfFiveMark
    (by
      simp only [fiveIncrPair, halfFiveMark_one, halfFiveMark_handleU, halfFiveMark_handleV,
        SqU6.one_m, SqU6.one_n, show (halfFiveMove.m : gr3R) = 0 from rfl,
        show (halfFiveMove.n : gr3R) = 1 from rfl,
        show (halfFiveX.a : gr3R) = 0 from rfl, show (halfFiveX.e : gr3R) = 2 from rfl,
        show (halfFiveU.a : gr3R) = 1 from rfl, show (halfFiveU.e : gr3R) = 0 from rfl,
        show (halfFiveV.a : gr3R) = 2 from rfl, show (halfFiveV.e : gr3R) = 4 from rfl]
      decide)

/-- …so the UNRESTRICTED forcing is **false** at the half point, while the achievable one of
`halfFive_fiveForces` is true.  This is the exact dual of section 6, where no move of any
provenance kills. -/
theorem halfFive_unrestricted_forces_false :
    ¬ ∀ z₀ w₁ w₂ z₃ z₄ : SqU6 gr3R, z₀.IsGaFour → w₁.IsGaFive → w₂.IsGaFive →
        z₃.IsGaFour → z₄.IsGaFour →
        sqRelWord (fiveLift j (halfFiveMark h j) z₀ w₁ w₂ z₃ z₄) ≠ 1 := by
  intro hall
  exact hall 1 1 (liftC6 (-2)) 1 halfFiveMove SqU6.isGaFour_one SqU6.isGaFive_one
    (liftC6_isGaFive _) SqU6.isGaFour_one halfFiveMove_isGaFour halfFive_unrestricted_kill

/-- ⭐⭐⭐ **THE ANSWER, at the harder point.**  A marking outside wave 59's hypothesis and
outside its conclusion, whose handle slot has an ODD outer column so that section 6's dual
condition fails too, at which the class-five sigma forcing nevertheless **holds**. -/
theorem halfFive_separates :
    sqRelWord (halfFiveMark h j) = liftC6 3 ∧ commP halfFiveU halfFiveV ≠ 1 ∧
      selPar halfFiveU.a = 1 ∧
      ¬ Subgroup.closure (Set.range (halfFiveMark h j)) ≤ forceN1 ∧
      ¬ forceLcs (Subgroup.closure (Set.range (halfFiveMark h j))) 3 ≤ forceN4 ∧
      FiveOrth (halfFiveMark h j) j ∧ FiveForces (halfFiveMark h j) j :=
  ⟨sqRelWord_halfFiveMark, commP_halfFive_ne_one, halfFiveU_covector.2,
    halfFive_not_le_forceN1, halfFive_not_le_forceN4, halfFive_fiveOrth, halfFive_fiveForces⟩

end HalfFive

/-! ## 8 What the committed class-five statements would carry on the sharp line -/

section Migration

variable {h : ℕ} {j : Fin h}

/-- **THE COVECTORS AT WAVE 59'S BINDER POINT.**  The sharp line reads each of the three slots
only through its mod-`2` covector `(slot.e, slot.a)`, and at the committed point one of the
three **vanishes**:

```text
slot whose columns are read   covector   the move it reads    must satisfy
x0   = forceX <a=2, e=1>       (1, 0)    sigma dressing z₀     z₀.m even
V    = forceV <d=1, e=2, …>    (0, 0)    handle-U dressing z₃  nothing at all
U    = forceU <a=1, c=2, …>    (0, 1)    handle-V dressing z₄  z₄.n even
```

(The cross pairing is the commutator's: the dressing of the handle-`U` slot is read against
the `V`-letter's columns and conversely.)  So wave 59's `forceN4` - both coordinates even at
all three slots - is strictly more than the point uses. -/
theorem fiveWit_covectors :
    (selPar forceX.e = 1 ∧ selPar forceX.a = 0) ∧
      (selPar forceV.e = 0 ∧ selPar forceV.a = 0) ∧
      (selPar forceU.e = 0 ∧ selPar forceU.a = 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> exact ⟨by decide, by decide⟩

/-- ⭐ **The handle-`U` dressing at the binder point is FREE.**  It is read against the
`V`-letter's columns, whose covector vanishes, so its contribution to the increment is even for
**every** class-four move, achievable or not; wave 59's quantifier over `forceLcs … 3` in that
slot is spare. -/
theorem fiveWit_handleU_free (v z : SqU6 gr3R) :
    fiveIncrPair (fiveWit h j v) j 1 z 1 = 2 * z.m := by
  simp only [fiveIncrPair, fiveWit, fiveTuple_one, fiveTuple_handleU, fiveTuple_handleV,
    SqU6.one_m, SqU6.one_n, show (forceV.e : gr3R) = 2 from rfl,
    show (forceV.a : gr3R) = 0 from rfl, show (forceU.a : gr3R) = 1 from rfl,
    show (forceU.e : gr3R) = 0 from rfl, show (forceX.e : gr3R) = 1 from rfl,
    show (forceX.a : gr3R) = 2 from rfl]
  ring

/-- …and the two live covectors read exactly one coordinate each. -/
theorem fiveWit_pair_of_half (v z₀ z₃ z₄ : SqU6 gr3R) {a b : gr3R}
    (h₀ : z₀.m = 2 * a) (h₄ : z₄.n = 2 * b) :
    ∃ k : gr3R, fiveIncrPair (fiveWit h j v) j z₀ z₃ z₄ = 2 * k := by
  refine ⟨a - z₀.n + z₃.m + b, ?_⟩
  simp only [fiveIncrPair, fiveWit, fiveTuple_one, fiveTuple_handleU, fiveTuple_handleV,
    h₀, h₄, show (forceV.e : gr3R) = 2 from rfl, show (forceV.a : gr3R) = 0 from rfl,
    show (forceU.a : gr3R) = 1 from rfl, show (forceU.e : gr3R) = 0 from rfl,
    show (forceX.e : gr3R) = 1 from rfl, show (forceX.a : gr3R) = 2 from rfl]
  ring

/-- ⭐⭐⭐ **WAVE 59'S EXCLUSION, ON THE SHARP LINE.**  The sigma dressing `a0 = a1` is excluded
against every five-slot class-five refinement whose sigma move has an even FIRST class-four
coordinate and whose handle-`V` move has an even SECOND one.  **The handle-`U` move is
arbitrary, and no achievability hypothesis is used anywhere**: no lower central series, no
even-`(3,4)`-column, no lattice.

`GradedFiveForce.sqRelWord_fiveWit_diag_ne_one` is the corollary below. -/
theorem fiveWit_diag_ne_one_sharp {z₀ w₁ w₂ z₃ z₄ : SqU6 gr3R} {a b : gr3R}
    (hz₀ : z₀.IsGaFour) (h₀ : z₀.m = 2 * a) (hw₁ : w₁.IsGaFive) (hw₂ : w₂.IsGaFive)
    (hz₃ : z₃.IsGaFour) (hz₄ : z₄.IsGaFour) (h₄ : z₄.n = 2 * b) :
    sqRelWord (fiveLift j (fiveWit h j forceX) z₀ w₁ w₂ z₃ z₄) ≠ 1 := by
  intro hc
  have hp := fiveSigma_forced_of_pair hz₀ hw₁ hw₂ hz₃ hz₄
    (fiveWit_pair_of_half forceX z₀ z₃ z₄ h₀ h₄) hc
  rw [sqRelWord_fiveWit_diag, liftC6_o] at hp
  exact absurd hp (by decide)

/-- **…and it subsumes the committed statement**: an achievable dressing has both class-four
coordinates even by `GradedFiveForce.forceLcs_three_le_forceN4`, so it satisfies the two
parity hypotheses above and its `V`-slot hypothesis is not needed at all. -/
theorem sqRelWord_fiveWit_diag_ne_one_of_sharp {z₀ w₁ w₂ z₃ z₄ : SqU6 gr3R}
    (hz₀ : z₀ ∈ forceLcs (forceImage h j forceX) 3) (hw₁ : w₁.IsGaFive) (hw₂ : w₂.IsGaFive)
    (hz₃ : z₃.IsGaFour)
    (hz₄ : z₄ ∈ forceLcs (forceImage h j forceX) 3) :
    sqRelWord (fiveLift j (fiveWit h j forceX) z₀ w₁ w₂ z₃ z₄) ≠ 1 := by
  have hle := forceLcs_three_le_forceN4 (forceImage_le_forceN1 (h := h) (j := j)
    (v := forceX) ⟨0, by decide⟩)
  obtain ⟨a, ha⟩ := (forceN4_even (hle hz₀)).1
  obtain ⟨b, hb⟩ := (forceN4_even (hle hz₄)).2
  exact fiveWit_diag_ne_one_sharp (isGaFour_of_mem_forceLcs hz₀) ha hw₁ hw₂ hz₃
    (isGaFour_of_mem_forceLcs hz₄) hb

/-- ⭐⭐ **At the committed LIVE class-five point all three covectors vanish**, so there the
class-five sigma forcing holds for arbitrary class-four moves with no achievability, no
lattice and no column hypothesis: `fiveOrth_of_slots_even` applies on the nose. -/
theorem liveFive_covectors :
    (selPar fiveX.e = 0 ∧ selPar fiveX.a = 0) ∧ (selPar fiveV.e = 0 ∧ selPar fiveV.a = 0) ∧
      (selPar fiveU.e = 0 ∧ selPar fiveU.a = 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> exact ⟨by decide, by decide⟩

/-- ⭐⭐⭐ **AND THE HONEST OTHER HALF: at wave 59's own binder point the sharp line and its
CONCLUSION coincide.**  The two live covectors `(1, 0)` and `(0, 1)` span the mod-`2` dual, so
"both covectors annihilate the achievable class-four parity image" is literally "every
achievable dressing lies in `forceN4`" there.  So the class-five soundness CONCLUSION is not
weakened at the point it was proved for; what sections 6 and 7 refute is the claim that it is
the line **in general**, and `fiveWit_diag_ne_one_sharp` is what it buys even here. -/
theorem fiveWit_fiveOrth_iff (v : SqU6 gr3R) :
    FiveOrth (fiveWit h j v) j ↔
      ∀ z ∈ forceLcs (Subgroup.closure (Set.range (fiveWit h j v))) 3,
        (∃ a : gr3R, z.m = 2 * a) ∧ ∃ b : gr3R, z.n = 2 * b := by
  constructor
  · intro hO z hz
    obtain ⟨k₀, hk₀⟩ := (hO z hz).1
    obtain ⟨k₄, hk₄⟩ := (hO z hz).2.2
    simp only [fiveIncrPair, fiveWit, fiveTuple_one, fiveTuple_handleU, fiveTuple_handleV,
      SqU6.one_m, SqU6.one_n, show (forceX.e : gr3R) = 1 from rfl,
      show (forceX.a : gr3R) = 2 from rfl, show (forceV.e : gr3R) = 2 from rfl,
      show (forceV.a : gr3R) = 0 from rfl, show (forceU.a : gr3R) = 1 from rfl,
      show (forceU.e : gr3R) = 0 from rfl] at hk₀ hk₄
    exact ⟨⟨k₀ + z.n, by linear_combination hk₀⟩, ⟨k₄, by linear_combination hk₄⟩⟩
  · intro hev z hz
    obtain ⟨a, ha⟩ := (hev z hz).1
    obtain ⟨b, hb⟩ := (hev z hz).2
    have hone_m : (1 : SqU6 gr3R).m = 2 * 0 := by rw [SqU6.one_m]; ring
    have hone_n : (1 : SqU6 gr3R).n = 2 * 0 := by rw [SqU6.one_n]; ring
    exact ⟨fiveWit_pair_of_half v z 1 1 ha hone_n,
      fiveWit_pair_of_half v 1 z 1 hone_m hone_n,
      fiveWit_pair_of_half v 1 1 z hone_m hb⟩

/-- ⭐⭐⭐ **THE COMMITTED FORCING, ON THE SHARP LINE.**  At the binder point with **any** sigma
dressing `v`, a five-slot class-five refinement that kills leaves an even class-five residue as
soon as the sigma move's FIRST class-four coordinate and the handle-`V` move's SECOND one are
even.  The handle-`U` move is arbitrary; the even-`(3,4)`-column hypothesis `hv` of
`GradedFiveForce.fiveWit_sigma_forced` is gone, and so is achievability in all three slots.
This is the migration the campaign should make.

Naming, recorded at merge: the SHARPER companion of this statement, taking only the SUM
`z0.m + z4.n` even rather than both columns separately, is `fiveWit_sigma_forced_sharp` in
`SqCore/GradedFiveFrame.lean`.  Both landed in wave 60 from sibling lanes that did not import
each other and both were originally called `fiveWit_sigma_forced_sharp`; this one was renamed
at merge.  The frame file's version is the stronger theorem and should be preferred; this one
is kept because the pairing machinery of this file produces it directly and because the
characterisation `fiveForces_iff_fiveOrth` below is stated against this file's `fiveIncrPair`,
of which the sum condition is the specialisation at the binder point. -/
theorem fiveWit_sigma_forced_of_columns {v z₀ w₁ w₂ z₃ z₄ : SqU6 gr3R} {a b : gr3R}
    (hz₀ : z₀.IsGaFour) (h₀ : z₀.m = 2 * a) (hw₁ : w₁.IsGaFive) (hw₂ : w₂.IsGaFive)
    (hz₃ : z₃.IsGaFour) (hz₄ : z₄.IsGaFour) (h₄ : z₄.n = 2 * b)
    (hkill : sqRelWord (fiveLift j (fiveWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (sqRelWord (fiveWit h j v)).o = 0 :=
  fiveSigma_forced_of_pair hz₀ hw₁ hw₂ hz₃ hz₄ (fiveWit_pair_of_half v z₀ z₃ z₄ h₀ h₄) hkill

/-- **The composite check**: wave 59's forcing is recovered from this file's machinery, so the
two accounts agree where they overlap.  `GradedFiveForce.fiveWit_sigma_forced` is the
statement below with its five dressings supplied one at a time. -/
theorem fiveWit_fiveForces_of_le_forceN1 {v : SqU6 gr3R} (hv : ∃ t : gr3R, v.c = 2 * t) :
    FiveForces (fiveWit h j v) j :=
  fiveForces_of_fiveOrth (fiveOrth_of_le_forceN1 (forceImage_le_forceN1 hv))

/-- ⭐⭐⭐ **AT THE BINDER POINT A CLASS-FOUR MOVE KILLS EXACTLY WHEN ITS PAIRING IS ODD.**
No shape, no lattice, no provenance: the pairing's parity is the whole criterion, and the
class-five exponent slot absorbs everything else.  This is what wave 59's scope warning is,
read on the sharp line. -/
theorem fiveWit_diag_kill_iff {z₀ z₃ z₄ : SqU6 gr3R} (hz₀ : z₀.IsGaFour) (hz₃ : z₃.IsGaFour)
    (hz₄ : z₄.IsGaFour) :
    (∃ w₂ : SqU6 gr3R, w₂.IsGaFive ∧
        sqRelWord (fiveLift j (fiveWit h j forceX) z₀ 1 w₂ z₃ z₄) = 1)
      ↔ ¬ ∃ k : gr3R, fiveIncrPair (fiveWit h j forceX) j z₀ z₃ z₄ = 2 * k := by
  constructor
  · rintro ⟨w₂, hw₂, hkill⟩ hp
    have := fiveSigma_forced_of_pair hz₀ SqU6.isGaFive_one hw₂ hz₃ hz₄ hp hkill
    rw [sqRelWord_fiveWit_diag, liftC6_o] at this
    exact absurd this (by decide)
  · exact fun hodd => fiveKill_of_pair_odd hz₀ hz₃ hz₄ (sqRelWord_fiveWit_diag h j)
      (by decide) hodd

/-- ⭐⭐⭐ **…so wave 59's stage-four hole is an ODD-PAIRING hole, and the covector that sees it
is the sigma one.**  The triple commutator `[[sigma, U], x1]` of the point's own letters has
first class-four coordinate `5`, which the `x0`-slot's covector `(1, 0)` reads oddly; that odd
pairing is the whole reason `GradedFiveForce.fiveWit_gaThree_kill` exists.  Any point without
the hole must therefore have every `gamma_4`-shaped element of `gamma_3` of its image pairing
evenly against the three slots, which is a condition on the covectors and the class-three
layer rather than on the stage convention. -/
theorem fiveWit_gaThree_kill_pair_odd :
    ¬ ∃ k : gr3R, fiveIncrPair (fiveWit h j forceX) j
        (commP (commP (fiveSigMark gr3R) forceU) forceY) 1 1 = 2 * k := by
  simp only [fiveIncrPair, fiveWit, fiveTuple_one, fiveTuple_handleU, fiveTuple_handleV,
    SqU6.one_m, SqU6.one_n,
    show (commP (commP (fiveSigMark gr3R) forceU) forceY).m = 5 from by decide,
    show (commP (commP (fiveSigMark gr3R) forceU) forceY).n = 6 from by decide,
    show (forceX.e : gr3R) = 1 from rfl, show (forceX.a : gr3R) = 2 from rfl,
    show (forceV.e : gr3R) = 2 from rfl, show (forceV.a : gr3R) = 0 from rfl,
    show (forceU.a : gr3R) = 1 from rfl, show (forceU.e : gr3R) = 0 from rfl]
  decide

/-- ⭐⭐ **The two soundness columns are INCOMPARABLE.**  Wave 59's even-`(3,4)`-column
condition holds at its binder point and fails at the half point; section 5's
even-`(5,6)`-column condition holds at the half point and fails at the binder point, where the
`x0`-slot's fifth abelian column is the one datum escaping the committed gauge. -/
theorem fiveEvenE_incomparable_forceN1 {h : ℕ} {j : Fin h} :
    (Subgroup.closure (Set.range (halfFiveMark h j)) ≤ fiveEvenE gr3R ∧
        ¬ Subgroup.closure (Set.range (halfFiveMark h j)) ≤ forceN1) ∧
      (forceImage h j forceX ≤ forceN1 ∧ ¬ forceImage h j forceX ≤ fiveEvenE gr3R) := by
  refine ⟨⟨halfFiveMark_le_fiveEvenE, halfFive_not_le_forceN1⟩,
    forceImage_le_forceN1 ⟨0, by decide⟩, fun hle => ?_⟩
  obtain ⟨t, ht⟩ := hle (Subgroup.subset_closure ⟨1, by rw [fiveWit, fiveTuple_one]⟩)
  rw [show (forceX.e : gr3R) = 1 from rfl] at ht
  exact absurd ht (by revert t; decide)

end Migration

/-! ## 9 Axiom pins

Committed prints for every public declaration of this file: all **std-3** (`propext`,
`Classical.choice`, `Quot.sound`) or a subset; no census axiom is reachable.  Every `decide`
is on `ZMod 8`, `ZMod 2` or `Fin`-indexed tuples over them; there is no `native_decide`. -/

section AxiomPins

#print axioms fiveIncrPair
#print axioms fiveIncrPair_eq_add
#print axioms fiveIncrPair_even_of_moves_even
#print axioms fiveIncrPair_even_of_slots_even
#print axioms fiveIncrPair_even_of_slotE_even
#print axioms fiveIncrPair_even_of_slotA_even
#print axioms gaTwoSub
#print axioms gaThreeSub
#print axioms gaFourSub
#print axioms mem_gaFourSub
#print axioms gaTwoSub_of_commutator
#print axioms gaThreeSub_of_commutator
#print axioms gaFourSub_of_commutator
#print axioms forceLcs_three_le_gaFourSub
#print axioms isGaFour_of_mem_forceLcs
#print axioms fiveSigma_forced_of_pair
#print axioms fiveKill_of_pair
#print axioms fiveKill_of_pair_odd
#print axioms FiveForces
#print axioms FiveOrth
#print axioms FiveOrth.triple
#print axioms fiveForces_of_fiveOrth
#print axioms fiveOrth_of_fiveForces
#print axioms fiveForces_iff_fiveOrth
#print axioms fiveOrth_of_le_forceN1
#print axioms fiveOrth_of_slots_even
#print axioms fiveOrth_of_gaFour_n_even
#print axioms fiveOrth_of_gaFour_m_even
#print axioms fiveEvenE
#print axioms fiveEvenI
#print axioms fiveEvenL
#print axioms fiveEvenN
#print axioms mem_fiveEvenE
#print axioms fiveEvenN_even
#print axioms fiveEvenI_of_commutator
#print axioms fiveEvenL_of_commutator
#print axioms fiveEvenN_of_commutator
#print axioms forceLcs_three_le_fiveEvenN
#print axioms gaFour_n_even_of_le_fiveEvenE
#print axioms commP_mem_commSub
#print axioms orthFiveS
#print axioms orthFiveX
#print axioms orthFiveY
#print axioms orthFiveU
#print axioms orthFiveV
#print axioms orthFiveMark
#print axioms orthFiveMark_zero
#print axioms orthFiveMark_one
#print axioms orthFiveMark_handleU
#print axioms orthFiveMark_handleV
#print axioms sqRelWord_orthFiveMark
#print axioms commP_orthFive_ne_one
#print axioms orthFive_pair_eq_zero
#print axioms orthFive_pair_even
#print axioms orthFive_no_kill
#print axioms orthFive_fiveOrth
#print axioms orthFive_fiveForces
#print axioms orthFive_not_le_forceN1
#print axioms orthFive_quad_mem
#print axioms orthFive_quad_not_forceN4
#print axioms orthFive_not_le_forceN4
#print axioms orthFive_separates
#print axioms halfFiveS
#print axioms halfFiveX
#print axioms halfFiveY
#print axioms halfFiveU
#print axioms halfFiveV
#print axioms halfFiveMark
#print axioms halfFiveMark_zero
#print axioms halfFiveMark_one
#print axioms halfFiveMark_two
#print axioms halfFiveMark_handleU
#print axioms halfFiveMark_handleV
#print axioms sqRelWord_halfFiveMark
#print axioms commP_halfFive_ne_one
#print axioms halfFiveU_covector
#print axioms halfFiveMark_le_fiveEvenE
#print axioms halfFive_gaFour_n_even
#print axioms halfFive_fiveOrth
#print axioms halfFive_fiveForces
#print axioms halfFive_not_le_forceN1
#print axioms halfFive_quad_mem
#print axioms halfFive_quad_not_forceN4
#print axioms halfFive_not_le_forceN4
#print axioms halfFiveMove
#print axioms halfFiveMove_isGaFour
#print axioms halfFiveMove_not_mem
#print axioms halfFive_unrestricted_kill
#print axioms halfFive_unrestricted_forces_false
#print axioms halfFive_separates
#print axioms fiveWit_covectors
#print axioms fiveWit_handleU_free
#print axioms fiveWit_pair_of_half
#print axioms fiveWit_diag_ne_one_sharp
#print axioms sqRelWord_fiveWit_diag_ne_one_of_sharp
#print axioms liveFive_covectors
#print axioms fiveWit_sigma_forced_of_columns
#print axioms fiveWit_fiveForces_of_le_forceN1
#print axioms fiveWit_diag_kill_iff
#print axioms fiveWit_gaThree_kill_pair_odd
#print axioms fiveWit_fiveOrth_iff
#print axioms fiveEvenE_incomparable_forceN1

end AxiomPins

end SqCore

end Dyadic

end GQ2

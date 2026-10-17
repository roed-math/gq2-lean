/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFourCleared

/-!
# W58-TWOLIVE: the class-four point catalogue completed

`GradedFourCleared` (wave 57) built the **first** live handle block, at the **cleared** row, and
named the three things it did not do:

> * The live point sits at the **cleared** row.  At a row with `ν'(v_j) ≠ 0` the handle letters
>   carry pivot powers, and whether a live block survives the displacement is not settled here.
> * No point with **two** live handles is produced; §2's handle-blindness covers those too, but
>   the cross-handle coupling `GradedFour` names at class four is untouched.
> * Higher pivot powers … are still covered only in principle …; no point is built.

All three are settled here, and the second one does not come out the way the forecast reads.

## Headline 1: a live handle block at EVERY selected row, and beyond

```text
row (t, s)           dead point            LIVE point (this file)        block order
(0, 0)  cleared      GradedFourHom         GradedFourCleared, W57        four   (h = 2)
(0, 1)  uncleared v  GradedFourRow/Mirror  ⭐⭐ §6  rowLive…              two    (h = 4)
(1, 0)  mirror       GradedFourMirror      ⭐⭐ §5  mirLive…              two    (h = 4)
(1, 1)  doubly       GradedFourMirror      ⭐⭐ §7  dblLive…              two    (h = 4)
(2, 0)  SECOND POWER not built             ⭐⭐ §12 hiLive…               four   (h = 2)
(0, 0)  cleared, TWO live handles          ⭐⭐⭐ §9 twoLive…             four   (h = 2)
```

⭐⭐ `sqArbFrame_sigma_forced_mirLive`, `…_rowLive`, `…_dblLive`, `…_hiLive`, ⭐⭐⭐
`sqArbFrame_sigma_forced_twoLive`, each with its lattice companion: at **every** handle count
`h`, at **every** handle `j`, at **every** pivot residue, at an honest continuous homomorphism
whose handle commutator is **nontrivial in the image**, every `ν'`-trivial sigma dressing of
the arbitrary-dressing frame killed by any achievable five-slot class-four refinement has an
even `chi_a`-character.  Each point is built to wave 57's ten-row standard: marking and cleared
frame both kill the relator, three verdicts with the even one completed, class-`≤ 3` blindness,
hom with pivot anchor, both Eichler-cleared letters, `b`-column and frame identification,
soundness against the committed lattice **and** the model-independent `γ₂`-bound, and
non-vacuity.

## ⭐⭐ Headline 2: how the sided displacement identities meet a live block

The displacement calculus of `GradedFourMirror` §1 was about the relator's `e`-row.  A live
block makes it about the block itself, and the two sides behave differently:

```text
⁅P·U, V⁆ = ⁅P, V⁆^U · ⁅U, V⁆                     commP_left_displace
⁅U, V·Q⁆ = ⁅U, Q⁆ · ⁅U, V⁆^Q                     commP_right_displace
```

⭐⭐ **On the left the block is inert**: `commP_left_displace_inert`, the marking's block equals
the frame's as soon as the pivot commutes with the `v`-letter.  ⭐⭐ **On the right the block is
CONJUGATED**, and on a `γ₃`-shaped block the conjugation is a central translation
(`commP_right_displace_gaThree`) which at the pivot is exactly

```text
⁅U, V·Φ(w)⁆ = ⁅U, Φ(w)⁆ · ⁅U, V⁆ · liftC (2c · ⁅U, V⁆.i)      commP_rowPivot_right_defect
```

so the block's **own second class-three coordinate** appears in the compatibility condition and
has to be absorbed by `⁅U₀, Φ(w)⁆`.  That is the sharp form of wave 56's "the sidedness
matters": there it changed the *statement* of an identity, here it changes *which blocks a row
can carry*.

⭐⭐ **And that is what the block orders record.**  A legal odd verdict needs the open letter's
own second class-two coordinate to satisfy `2(v.c + v.f) = 0` - `sqRelWord_gaugeX_dress_low`
says the relator's class-three row moves by exactly `-2(v.c + v.f)` under a sigma dressing, so
otherwise the residue is not even central.  Combined with the displacement criteria this pins
both class-three coordinates of a first-power live block into `4·ℤ/8`: ⭐⭐ **at the three
first-power displaced rows a live block has class-three part of order at most two**, while the
cleared row (wave 57) and the second-power row carry order four (`live_block_orders`).  The
displacement's own order controls the block's.

## ⭐⭐⭐ Headline 3: TWO live handles, and what they do and do not break

⭐⭐⭐ `sqRelWord_twoTuple_swap`.  Put a pair of letters at one handle and the **same pair
swapped** at another.  Then `⁅U, V⁆ · ⁅V, U⁆ = 1` is a **group identity** (`commP_swap`), the
whole handle block collapses, and the relator is the bare core word - for **arbitrary** letters,
in **any** group, at **every** handle count and every ordered pair of handles.  With the
committed core slots, whose core word is trivial, this is a relator-killing marking with **two
live blocks**.  So wave 57's "with the committed core slots a live block is forced impossible"
is sharp: it is a statement about **one** handle.

**What two blocks do NOT do.**

* ⭐⭐ **They do not interfere.**  `commP_pair_no_coupling`: the class-four cross-handle coupling
  `GradedFour` names - `(x·y).j` picks up `x.e·y.g` - is **identically zero** whenever the
  second pair's letters have vanishing `c`-column, which is the first of
  `GradedFourCleared.liveFrameSub`'s three invariants; and equally whenever the first pair is
  `ν'`-trivial.  `commP_coupling_ne_zero_imp`: realising the coupling requires a nonzero
  `c`-column, hence a marking where `commP_mem_liveGaTwoSub` fails outright.  The two blocks
  simply add, and the relator sees only their **sum**.
* ⭐⭐ **They do not become visible.**  ⭐⭐ `sqRelWord_gaugeX_sigma_bit` proves wave 57's
  cancellation for an **arbitrary** marking over the committed gauge - one live handle, two, or
  `h` - and ⭐⭐ `gaugeX_sigma_forced` runs the whole forcing from it.  This is a
  **strengthening** of wave 57's negative, not a weakening: the class-four bit is blind to the
  handle block whatever the block is, so a second live handle buys the `h ≥ 1` route nothing.

**What two blocks DO break, and it is not small.**

* ⭐⭐⭐ `twoLiveOdd_block_odd`.  Wave 57's `commP_gaThree_even_of_relator` - at one live handle
  the relator forces the block's class-three coordinates **even**, so a live block is
  automatically sound - **does not extend**.  At two handles the relator controls only the
  product (⭐⭐ `commP_pair_gaThree_even_of_relator`, the sharpest available), and
  `twoLiveMark h j₁ j₂ sigFourU oddLiveV` kills the relator at the committed gauge with **both**
  blocks **odd** in the first class-three coordinate.
* ⭐⭐⭐ `twoLiveOdd_kill` and `twoLiveOdd_sigma_forced_false`.  At that marking the block
  `⁅U, V⁆` is a commutator of two slot values, hence a legal `γ₂`-level dressing under the
  standing achievability convention, and it is `γ₃`-shaped; using it as the `v`-handle move,
  with the two exponent moves `1` and `liftC 3`, gives an **achievable** five-slot refinement
  that **kills the relator at the odd sigma dressing**.  So the class-four sigma forcing is
  **FALSE** there, and the file proves the negation of its own shape.

  The frame invariant `liveFrameSub` is SUFFICIENT to rule this out

  CORRECTED BY W59-INVARIANT: `liveFrameSub` is MERELY SUFFICIENT here, not the sharp line.
  The sharp invariant is `FrameOrth` (both mod-two covectors of the handle slots' outer
  abelian columns annihilate the class-three parity image), characterised in both directions
  by `sigmaForces_iff_frameOrth`. The killing point below, the orthogonal point and the mixed
  point all carry the SAME odd block and all have their `v`-letter outside `liveFrameSub`,
  yet the forcing FAILS at the first and HOLDS at the other two; the mixed point differs from
  the killing point in ONE coordinate of ONE letter, which is not a frame invariant. So the
  reading "two live blocks outside the frame invariant break the forcing" is FALSE; what
  breaks it is an odd handle pairing. See `SqCore/GradedFrameNecessity.lean`.
  It, and at one live handle wave
  57 proved that the relator supplies it for free.  **At two live handles the frame invariants
  stop being bookkeeping and become the load-bearing hypothesis of the forcing.**

## The machinery, proved once (§1, §2, §4)

* ⭐⭐ `sqRelWord_gaugeX_dress_low` / `sqRelWord_gaugeX_sigma_bit` / `gaugeX_increment_even` /
  `gaugeX_sigma_forced`: the dressing response, the selection bit, the increment and the whole
  forcing at **any** marking whose sigma- and `x₀`-slots are the committed ones and whose
  `x₁`-slot has vanishing outer columns.  Nothing about the handle block is assumed anywhere.
* ⭐⭐ `liveHom_sqArbFrame`: the frame identification with **no** hypothesis on the other
  handles - `GradedFourMirror.mirHom_sqArbFrame` demands they be trivial, and dropping that is
  what lets a second live handle sit in the frame.
* `liveWit` and `liveWit_sigma_forced`: the one-live witness shape at a **free** `x₁`-slot,
  which is what lets the core word cancel a live block; every §5-§7 and §12 forcing is one
  instantiation.
* `handleWord_eq_pair`: the two-handle transposition of `EichRefutation.handleWord_eq_single`.

## PROVED versus carried versus measured

**PROVED**, with no live hypothesis: the two displacement identities and the swap identity (any
group); the `γ₃` conjugation defect and the pivot's closed form; the gauge dressing response,
bit, increment and forcing at an arbitrary marking; the general frame identification; the
two-handle relator and the swapped-pair collapse (any group, any letters, any handle count); the
no-coupling theorems; the four displaced/second-power points and the two-live point end to end
at every handle count, every handle and every pivot residue, each to wave 57's ten-row standard;
the two-live obstruction, its odd block and the achievable refinement that kills the odd
dressing.

**Carried, and named**: nothing beyond legality in the headlines.  The `γ₂`-level statements
carry the campaign's standing **achievability convention** exactly as `GradedGammaTwo`,
`GradedFourMirror` and `GradedFourCleared` do; the lattice-level statements carry `selLamThree`
as a model instead, at each point's own parameters - which are wave 55's / 56's committed ones
at the three first-power rows, because the live perturbation touches no column the lattice reads.

**Measured, not proved** (`scripts/w58_twolive/results/`): the kill sweeps - `33554432`
achievable five-slot refinements at each of the three first-power points and `134217728` at the
second-power and two-live points, **zero** of which kill the odd dressing, against `8388608` and
`33554432` that kill the even one; `1073741824` of `8589934592` **unrestricted** `γ₃`-moves kill
the odd dressing, so achievability is load-bearing here exactly as at the committed points; the
subgroup census at every pivot residue (`|⟨slots⟩|` `1048576` at the mirror and uncleared-`v`
points, `262144` at the doubly one, `2097152` at the second-power one and `1048576` at the
two-live one, with `|[K,K]|` respectively `256`, `256`, `256`, `512`, `512`, all even in class
three and all refuting the sharper wave-55 bound); and at the ODD two-live marking `[K,K]`
realises **every** class-three value `0..7` and `67108864` of `536870912` achievable refinements
kill the odd dressing.  Also measured: `195216` of `200000` random cleared-letter pairs give a
live two-handle point.

Every explicit claim of this file is mirrored numerically one for one in
`scripts/w58_twolive/instance_twolive.py`, at `h = 1, 2, 3, 4`, every handle `j < h`, every
ordered handle pair and every pivot residue, and the library is validated against the committed
`GradedSigmaFour`, `GradedFourHom`, `GradedFourRow`, `GradedFourMirror` and `GradedFourCleared`
facts before anything new is derived: **978987 comparisons, zero mismatches**, alongside `117`
named checks in the derivation (`derive_twolive.py`) and `149` in the sweeps
(`sweep_twolive.py`).

## What this does NOT do

* Only the second pivot power is built; rows `(t, s)` with `t` or `s` of higher valuation are
  still covered only in principle, by `GradedFourMirror.chiA_row_forced`.
* No point with **three or more** live handles is produced.  §1's blindness and §8's
  no-coupling cover them, and §10-§11 say what would have to be checked: the relator controls
  only the product of the blocks, so the frame invariant is what keeps each factor even.
* The two-live points are at the **cleared** row.  A two-live point at a displaced row would
  need the second pair's letters to carry pivot powers too; nothing here forbids it and nothing
  here builds it.
* The residual obstruction of `GradedSigmaFour` §7 is untouched and still needs class five.
* Nothing here makes the handle block visible.  §1 says it cannot be, at class four, at any
  number of live handles; that is the wave's message for the `h ≥ 1` route.

## Contents

* **1** ⭐⭐ the gauge machinery at an arbitrary marking: dressing response, selection bit,
  increment, forcing;
* **2** ⭐⭐ the frame identification with no hypothesis on the other handles;
* **3** ⭐⭐ the sided displacement calculus and its meeting with a live block;
* **4** the live witness shape at a free `x₁`-slot, its forcing and its soundness;
* **5** ⭐⭐ the mirror row `nuSel h j 1 0` with a live block, end to end;
* **6** ⭐⭐ the uncleared-`v` row `nuSel h j 0 1` with a live block, end to end;
* **7** ⭐⭐ the doubly uncleared row `nuSel h j 1 1` with a live block, end to end;
* **8** ⭐⭐ two live handles: `handleWord_eq_pair`, `twoTuple`, and the absence of coupling;
* **9** ⭐⭐⭐ the two-live-handle point at the committed core slots, end to end;
* **10** ⭐⭐ what the relator still forces at two live handles: the product;
* **11** ⭐⭐⭐ the two-live marking with individually odd blocks, and the failure of the forcing;
* **12** ⭐⭐ the second pivot power `nuSel h j 2 0`, end to end;
* **13** committed axiom prints.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`; every `decide` is on `ZMod 8`, `ZMod 2` or tuples
and words over them.  All **351** committed prints are **std-3** (`propext`,
`Classical.choice`, `Quot.sound`) or a subset (`237` std-3, `110` `propext`+`Quot.sound`, `4`
`propext` alone); no census axiom is reachable, `sqPivotExp` included.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The gauge machinery, at an arbitrary marking and an arbitrary handle block -/

section GaugeGeneral

variable {h : ℕ} {m : Fin (sqRank h) → SqU5 gr3R} {y v : SqU5 gr3R}

/-- ⭐⭐ **Only one row below class four moves under a sigma dressing at the committed
`x₀`-gauge, and it moves by exactly `-2(v.c + v.f)`.**  Nothing is assumed about the handle
block: any number of live handles, any letters.  This is the criterion a *legal odd verdict*
has to meet - the residue of a dressing is central exactly when `2(v.c + v.f) = 0` - and it is
what separates the displaced rows from the cleared one in §4-§6. -/
theorem sqRelWord_gaugeX_dress_low (hm0 : m 0 = sigFourMark gr3R) (hm1 : m 1 = sigFourX)
    (hyb : (m 2).b = 0) (hvb : v.b = 0) :
    (sqRelWord (sigFourDress m v)).g = (sqRelWord m).g ∧
      (sqRelWord (sigFourDress m v)).h = (sqRelWord m).h - 2 * (v.c + v.f) ∧
      (sqRelWord (sigFourDress m v)).i = (sqRelWord m).i := by
  obtain ⟨hg, hh, hi, -⟩ := sqRelWord_sigFourDress (m := m) (v := v) hm0
    (by rw [hm1]; decide) hyb hvb
  refine ⟨?_, ?_, ?_⟩
  · rw [hg, hm1, sigFourG, show (sigFourX.c : gr3R) = 0 from rfl,
      show (sigFourX.d : gr3R) = 0 from rfl, mul_zero, mul_zero, sub_zero, add_zero]
  · rw [hh, hm1, sigFourH, show (sigFourX.a : gr3R) = 2 from rfl,
      show (sigFourX.c : gr3R) = 0 from rfl, show (sigFourX.e : gr3R) = 0 from rfl,
      show (sigFourX.f : gr3R) = 0 from rfl]
    ring
  · rw [hi, hm1, sigFourI, show (sigFourX.c : gr3R) = 0 from rfl,
      show (sigFourX.d : gr3R) = 0 from rfl, show (sigFourX.f : gr3R) = 0 from rfl,
      sub_zero, mul_zero, mul_zero, add_zero, add_zero]

/-- ⭐⭐ **The class-four selection bit is blind to the WHOLE handle block.**  At the committed
sigma- and `x₀`-slots and any `x₁`-slot with vanishing outer columns, dressing the sigma slot
moves the parity of the class-four row by exactly the dressing's own `chi_a`-character - for
**every** marking of that gauge, whatever its handle block: one live handle, two, or `h` of
them.  `GradedFourCleared.mirTuple_sigma_bit` is the one-live-handle case, and this is the
form in which wave 57's cancellation covers two blocks. -/
theorem sqRelWord_gaugeX_sigma_bit (hm0 : m 0 = sigFourMark gr3R) (hm1 : m 1 = sigFourX)
    (hya : (m 2).a = 0) (hyb : (m 2).b = 0) (hyc : (m 2).c = 0) (hyd : (m 2).d = 0)
    (hvb : v.b = 0) :
    selPar ((sqRelWord (sigFourDress m v)).j) = selPar ((sqRelWord m).j) + selPar v.a := by
  obtain ⟨-, -, -, hjj⟩ := sqRelWord_sigFourDress (m := m) (v := v) hm0
    (by rw [hm1]; decide) hyb hvb
  rw [hjj, selPar_add, hm1,
    sigFourRead_gauge_par (v := v) (x := sigFourX) (y := m 2) (xa := 1) (xc := 0) (xd := 0)
      (xe := 0) (xf := 0) (ya := 0) (yc := 0) (yd := 0)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hya]; ring) (by rw [hyc]; ring) (by rw [hyd]; ring),
    show (sigFourX.g + sigFourX.i : gr3R) = 1 by decide,
    show (sigFourX.h : gr3R) = 0 by decide, show (sigFourX.g : gr3R) = 0 by decide,
    mul_one, mul_zero, mul_zero, selPar_zero, add_zero, add_zero]

/-- …and at a marking that kills the relator the bit **is** the dressing's character. -/
theorem sqRelWord_gaugeX_sigma_bit_of_rel (hm0 : m 0 = sigFourMark gr3R) (hm1 : m 1 = sigFourX)
    (hya : (m 2).a = 0) (hyb : (m 2).b = 0) (hyc : (m 2).c = 0) (hyd : (m 2).d = 0)
    (hvb : v.b = 0) (hrel : sqRelWord m = 1) :
    selPar ((sqRelWord (sigFourDress m v)).j) = selPar v.a := by
  rw [sqRelWord_gaugeX_sigma_bit hm0 hm1 hya hyb hyc hyd hvb, hrel, SqU5.one_j, selPar_zero,
    zero_add]

variable {j : Fin h} {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R}

/-- ⭐⭐ **The five-slot increment is even at ANY marking over the committed `x₀`-gauge**, as
soon as the two handle moves are even in both class-three coordinates.  It reads only the
`x₀`-slot's outer columns `(a, d) = (2, 0)` and the two handle slots' - never the `x₁`-slot,
never the handle block.  `GradedFourMirror.mirWit_increment_even` is the special case at the
one-live-handle witness shape. -/
theorem gaugeX_increment_even (hm1 : m 1 = sigFourX)
    (h₃ : (∃ a : gr3R, z₃.h = 2 * a) ∧ (∃ b : gr3R, z₃.i = 2 * b))
    (h₄ : (∃ a : gr3R, z₄.h = 2 * a) ∧ (∃ b : gr3R, z₄.i = 2 * b)) :
    ∃ k : gr3R, (z₀.h * (m 1).d - z₀.i * (m 1).a) + (-4 * w₁.j + 2 * w₂.j)
        + ((z₃.h * (m (sqHandleIdxV j)).d - z₃.i * (m (sqHandleIdxV j)).a)
          + ((m (sqHandleIdxU j)).a * z₄.i - (m (sqHandleIdxU j)).d * z₄.h)) = 2 * k := by
  obtain ⟨⟨a₃, ha₃⟩, b₃, hb₃⟩ := h₃
  obtain ⟨⟨a₄, ha₄⟩, b₄, hb₄⟩ := h₄
  refine ⟨-z₀.i - 2 * w₁.j + w₂.j
    + (a₃ * (m (sqHandleIdxV j)).d - b₃ * (m (sqHandleIdxV j)).a)
    + ((m (sqHandleIdxU j)).a * b₄ - (m (sqHandleIdxU j)).d * a₄), ?_⟩
  rw [hm1, ha₃, hb₃, ha₄, hb₄]
  simp only [sigFourX]
  ring

/-- ⭐⭐ **THE FORCING, at any relator-killing marking over the committed gauge.**  One
theorem for every point of this file and of wave 57: at **any** marking whose sigma- and
`x₀`-slots are the committed ones, whose `x₁`-slot has vanishing outer columns and whose
relator vanishes, a `ν'`-trivial sigma dressing whose frame is killed by a five-slot class-four
refinement with even handle moves has an **even** `chi_a`-character.  The handle block is
completely unconstrained: dead, one live pair, two live pairs, or `h`. -/
theorem gaugeX_sigma_forced (hm0 : m 0 = sigFourMark gr3R) (hm1 : m 1 = sigFourX)
    (hya : (m 2).a = 0) (hyb : (m 2).b = 0) (hyc : (m 2).c = 0) (hyd : (m 2).d = 0)
    (hrel : sqRelWord m = 1) (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (h₃ : (∃ a : gr3R, z₃.h = 2 * a) ∧ (∃ b : gr3R, z₃.i = 2 * b))
    (h₄ : (∃ a : gr3R, z₄.h = 2 * a) ∧ (∃ b : gr3R, z₄.i = 2 * b))
    (hkill : sqRelWord (sigLift j (sigFourDress m v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 := by
  have hd1 : sigFourDress m v 1 = m 1 := sigFourDress_ne (by rw [sqVal_one]; omega)
  have hdU : sigFourDress m v (sqHandleIdxU j) = m (sqHandleIdxU j) :=
    sigFourDress_ne (by rw [sqHandleIdxU_val]; omega)
  have hdV : sigFourDress m v (sqHandleIdxV j) = m (sqHandleIdxV j) :=
    sigFourDress_ne (by rw [sqHandleIdxV_val]; omega)
  rw [sqRelWord_sigLift hz₀ hw₁ hw₂ hz₃ hz₄, hd1, hdU, hdV] at hkill
  obtain ⟨k, hk⟩ := gaugeX_increment_even (m := m) (j := j) (z₀ := z₀) (w₁ := w₁) (w₂ := w₂)
    hm1 h₃ h₄
  rw [hk, mul_liftC_apply] at hkill
  have hjj := congrArg SqU5.j hkill
  simp only [SqU5.one_j] at hjj
  have hp := congrArg selPar hjj
  rw [selPar_add, selPar_two_mul, add_zero,
    sqRelWord_gaugeX_sigma_bit_of_rel hm0 hm1 hya hyb hyc hyd hvb hrel] at hp
  exact hp

end GaugeGeneral

/-! ## 2 The frame identification at an arbitrary marking -/

section FrameGeneral

variable {h : ℕ} {j : Fin h} {m : Fin (sqRank h) → SqU5 gr3R}
  {Φ : ContinuousMonoidHom (DSq h : Type) (SqU5 gr3R)}
  {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- ⭐⭐ **The frame identification, with no hypothesis on the other handles.**  For any test
hom whose three core-slot values and whose two Eichler-cleared `j`-handle letters are the
marking's, and whose **other** handle generators map to the marking's other handle slots
(trivial or not), the arbitrary-dressing frame with a sigma-only dressing `g` is exactly the
marking with the sigma slot dressed by `Φ g`.  `GradedFourMirror.mirHom_sqArbFrame` is the case
in which every other handle letter is trivial; dropping that is what lets a **second live
handle** sit in the frame. -/
theorem liveHom_sqArbFrame (h0 : Φ (dsqSigma h) = m 0) (h1 : Φ (dsqX0 h) = m 1)
    (h2 : Φ (dsqX1 h) = m 2) (hEU : Φ (sqEichU h nu' j) = m (sqHandleIdxU j))
    (hEV : Φ (sqEichV h nu' j) = m (sqHandleIdxV j))
    (hne : ∀ j' : Fin h, j' ≠ j →
      Φ (sqGen h (sqHandleIdxU j')) = m (sqHandleIdxU j') ∧
        Φ (sqGen h (sqHandleIdxV j')) = m (sqHandleIdxV j')) (g : (DSq h : Type)) :
    (fun i => Φ (sqArbFrame h nu' j (sigArbDress h g) i)) = sigFourDress m (Φ g) := by
  funext i
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [sqArbFrame, sqArbBase_zero, sigArbDress_zero, map_mul, h0, sigFourDress_zero]
  · rw [sqArbFrame, sqArbBase_one, sigArbDress_ne (by rw [sqVal_one]; omega), mul_one, h1,
      sigFourDress_ne (by rw [sqVal_one]; omega)]
  · rw [sqArbFrame, sqArbBase_two, sigArbDress_ne (by rw [sqVal_two]; omega), mul_one, h2,
      sigFourDress_ne (by rw [sqVal_two]; omega)]
  · rw [sqArbFrame, sigArbDress_ne (by rw [sqHandleIdxU_val]; omega), mul_one,
      sigFourDress_ne (by rw [sqHandleIdxU_val]; omega)]
    by_cases hjj : j' = j
    · subst hjj
      rw [sqArbBase_handleU, hEU]
    · rw [sqArbBase_handleU_ne hjj, (hne j' hjj).1]
  · rw [sqArbFrame, sigArbDress_ne (by rw [sqHandleIdxV_val]; omega), mul_one,
      sigFourDress_ne (by rw [sqHandleIdxV_val]; omega)]
    by_cases hjj : j' = j
    · subst hjj
      rw [sqArbBase_handleV, hEV]
    · rw [sqArbBase_handleV_ne hjj, (hne j' hjj).2]

end FrameGeneral

/-! ## 3 The sided displacement calculus meets the live block -/

section Displacement

/-- **The left displacement of a commutator**, in any group: displacing the first argument on
the left by `P` conjugates `⁅P, V⁆` onto the block. -/
theorem commP_left_displace {G : Type*} [Group G] (P U V : G) :
    commP (P * U) V = conjP (commP P V) U * commP U V := by
  simp only [commP, conjP, mul_inv_rev]
  group

/-- **The right displacement of a commutator**, in any group: displacing the second argument on
the right by `Q` **conjugates the block itself** by `Q`.  ⚠ This is the asymmetry: on the left
the block is untouched, on the right it is moved. -/
theorem commP_right_displace {G : Type*} [Group G] (U V Q : G) :
    commP U (V * Q) = commP U Q * conjP (commP U V) Q := by
  simp only [commP, conjP, mul_inv_rev]
  group

/-- **The swap identity** `⁅U, V⁆ · ⁅V, U⁆ = 1`, in any group.  This one line is the whole
existence proof of a two-live-handle point at the committed core slots (§7). -/
theorem commP_swap {G : Type*} [Group G] (U V : G) : commP U V * commP V U = 1 := by
  simp only [commP]
  group

/-- ⭐⭐ **The left displacement is inert on the block** as soon as the displacing element
commutes with the `v`-letter - and conversely.  At the mirror row this is the *only* condition
the marking's block has to meet. -/
theorem commP_left_displace_inert {G : Type*} [Group G] {P U V : G} (hPV : commP P V = 1) :
    commP (P * U) V = commP U V := by
  rw [commP_left_displace, hPV, conjP, mul_one, inv_mul_cancel, one_mul]

variable {R : Type} [CommRing R]

/-- ⭐⭐ **The right displacement's defect, in closed form.**  When the block is `γ₃`-shaped -
which it is at every point of the campaign, `GradedFourCleared.commP_central_of_rowFrameSub`
and §4-§6 - displacing the `v`-letter on the right by `Q` costs `⁅U, Q⁆` **and** the central
defect `Q.d·b.h − Q.a·b.i` in which the block's own second class-three coordinate appears. -/
theorem commP_right_displace_gaThree {U V Q : SqU5 R} (hz : (commP U V).IsGaThree) :
    commP U (V * Q)
      = commP U Q * (commP U V * liftC (Q.d * (commP U V).h - Q.a * (commP U V).i)) := by
  rw [commP_right_displace, conjP_gaThree hz]

/-- ⭐⭐ **The asymmetry at the pivot.**  `GradedFourRow.rowPivotVal` has vanishing fourth
abelian column and `a`-column `−2c`, so the right displacement's defect is exactly `2c·b.i`:
the block's second class-three coordinate, doubled.  Nothing of the sort happens on the left. -/
theorem commP_rowPivot_right_defect {U V : SqU5 gr3R} {c : gr3R}
    (hz : (commP U V).IsGaThree) :
    commP U (V * rowPivotVal c)
      = commP U (rowPivotVal c) * (commP U V * liftC (2 * c * (commP U V).i)) := by
  rw [commP_right_displace_gaThree hz]
  refine congrArg _ (congrArg _ (congrArg liftC ?_))
  show (rowPivotVal c).d * (commP U V).h - (rowPivotVal c).a * (commP U V).i = _
  rw [show ((rowPivotVal c).d : gr3R) = 0 from rfl, show ((rowPivotVal c).a : gr3R) = -(2 * c)
    from rfl]
  ring

end Displacement

/-! ## 4 The witness shape at a free `x₁`-slot -/

section LiveWit

variable {h : ℕ} {j : Fin h} {y U V v : SqU5 gr3R}

variable (h j) in
/-- **The live witness shape**: the committed sigma- and `x₀`-slots, an **arbitrary** `x₁`-slot
`y`, the `j`-th handle pair carrying `(U, V)`, every other handle letter trivial, and the sigma
slot dressed by `v`.  `GradedFourMirror.mirWit` is the case `y = sigFourY`; the free slot is
what lets the core word cancel a live block. -/
def liveWit (y U V v : SqU5 gr3R) : Fin (sqRank h) → SqU5 gr3R :=
  mirTuple gr3R h j (sigFourMark gr3R * v) sigFourX y U V

@[simp] theorem liveWit_zero : liveWit h j y U V v 0 = sigFourMark gr3R * v := mirTuple_zero

@[simp] theorem liveWit_one : liveWit h j y U V v 1 = sigFourX := mirTuple_one

@[simp] theorem liveWit_two : liveWit h j y U V v 2 = y := mirTuple_two

@[simp] theorem liveWit_handleU : liveWit h j y U V v (sqHandleIdxU j) = U := mirTuple_handleU

@[simp] theorem liveWit_handleV : liveWit h j y U V v (sqHandleIdxV j) = V := mirTuple_handleV

theorem liveWit_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    liveWit h j y U V v (sqHandleIdxU j') = 1 := mirTuple_handleU_ne hne

theorem liveWit_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    liveWit h j y U V v (sqHandleIdxV j') = 1 := mirTuple_handleV_ne hne

/-- The dressed witness is the sigma-dressing of the undressed one. -/
theorem liveWit_eq_dress : liveWit h j y U V v = sigFourDress (liveWit h j y U V 1) v := by
  funext i
  by_cases h0 : (i : ℕ) = 0
  · have hi : i = 0 := Fin.val_injective (by rw [h0, sqVal_zero])
    subst hi
    rw [sigFourDress_zero, liveWit_zero, liveWit_zero, mul_one]
  · rw [sigFourDress_ne h0]
    simp only [liveWit, mirTuple, if_neg h0]

/-- ⭐ **The relator at the live witness shape**, at every handle count: the core word at the
dressed sigma slot times the live block. -/
theorem sqRelWord_liveWit :
    sqRelWord (liveWit h j y U V v)
      = sqWord (sigFourMark gr3R * v) sigFourX y * commP U V :=
  sqRelWord_mirTuple

/-- ⭐⭐ **The forcing at the live witness shape**, for **arbitrary** letters and an arbitrary
`x₁`-slot over the gauge: the single instantiation of §1 that drives every point below. -/
theorem liveWit_sigma_forced {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R}
    (hya : y.a = 0) (hyb : y.b = 0) (hyc : y.c = 0) (hyd : y.d = 0)
    (hrel : sqRelWord (liveWit h j y U V 1) = 1) (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (h₃ : (∃ a : gr3R, z₃.h = 2 * a) ∧ (∃ b : gr3R, z₃.i = 2 * b))
    (h₄ : (∃ a : gr3R, z₄.h = 2 * a) ∧ (∃ b : gr3R, z₄.i = 2 * b))
    (hkill : sqRelWord (sigLift j (liveWit h j y U V v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 := by
  rw [liveWit_eq_dress] at hkill
  exact gaugeX_sigma_forced (by rw [liveWit_zero, mul_one]) liveWit_one
    (by rw [liveWit_two]; exact hya) (by rw [liveWit_two]; exact hyb)
    (by rw [liveWit_two]; exact hyc) (by rw [liveWit_two]; exact hyd) hrel hvb hz₀ hw₁ hw₂
    hz₃ hz₄ h₃ h₄ hkill

/-- ⭐⭐ **The selection bit at the live witness shape.** -/
theorem liveWit_sigma_bit (hya : y.a = 0) (hyb : y.b = 0) (hyc : y.c = 0) (hyd : y.d = 0)
    (hvb : v.b = 0) (hrel : sqRelWord (liveWit h j y U V 1) = 1) :
    selPar ((sqRelWord (liveWit h j y U V v)).j) = selPar v.a := by
  rw [liveWit_eq_dress]
  exact sqRelWord_gaugeX_sigma_bit_of_rel (by rw [liveWit_zero, mul_one]) liveWit_one
    (by rw [liveWit_two]; exact hya) (by rw [liveWit_two]; exact hyb)
    (by rw [liveWit_two]; exact hyc) (by rw [liveWit_two]; exact hyd) hvb hrel

/-- Every slot of a live witness whose five values lie in `GradedFourCleared.liveFrameSub`
does too - the trivial letters of the other handles included. -/
theorem liveWit_le_liveFrameSub (hy : y ∈ liveFrameSub gr3R) (hU : U ∈ liveFrameSub gr3R)
    (hV : V ∈ liveFrameSub gr3R) (hv : sigFourMark gr3R * v ∈ liveFrameSub gr3R) :
    Subgroup.closure (Set.range (liveWit h j y U V v)) ≤ liveFrameSub gr3R := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [liveWit_zero]; exact hv
  · rw [liveWit_one]
    exact ⟨rfl, ⟨0, by show (0 : gr3R) = 2 * 0; ring⟩, 0, by show (0 : gr3R) = 2 * 0; ring⟩
  · rw [liveWit_two]; exact hy
  · by_cases hjj : j' = j
    · subst hjj; rw [liveWit_handleU]; exact hU
    · rw [liveWit_handleU_ne hjj]; exact one_mem _
  · by_cases hjj : j' = j
    · subst hjj; rw [liveWit_handleV]; exact hV
    · rw [liveWit_handleV_ne hjj]; exact one_mem _

/-- ⭐⭐ **The model-independent soundness at any live witness inside the widened frame.** -/
theorem liveWit_gaTwo_even (hy : y ∈ liveFrameSub gr3R) (hU : U ∈ liveFrameSub gr3R)
    (hV : V ∈ liveFrameSub gr3R) (hv : sigFourMark gr3R * v ∈ liveFrameSub gr3R)
    {z : SqU5 gr3R}
    (hz : z ∈ rowGaTwoOf (Subgroup.closure (Set.range (liveWit h j y U V v)))) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) := by
  have hle : rowGaTwoOf (Subgroup.closure (Set.range (liveWit h j y U V v)))
      ≤ liveGaTwoSub gr3R := by
    rw [rowGaTwoOf, Subgroup.closure_le]
    rintro w ⟨p, hp, q, hq, rfl⟩
    exact commP_mem_liveGaTwoSub (liveWit_le_liveFrameSub hy hU hV hv hp)
      (liveWit_le_liveFrameSub hy hU hV hv hq)
  obtain ⟨-, -, -, -, -, -, hh, hi⟩ := hle hz
  exact ⟨hh, hi⟩

end LiveWit

/-! ## 5 The MIRROR row `nuSel h j 1 0` with a live handle block -/

section MirrorLive

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐ **The shared `x₁`-slot of all three displaced live points**: `GradedSigmaFour.sigFourY`
with its first class-three coordinate moved from `0` to `2`.  Wave 57's live point moved it to
`3`; the displaced rows can only use `2`, and §9 explains why. -/
def liveRowY : SqU5 gr3R := ⟨0, 0, 0, 0, 1, 0, 4, 2, 2, 0⟩

/-- The core word at that slot is the class-three element with `h = 4`, of order **two**. -/
theorem sqWord_liveRowY :
    sqWord (sigFourMark gr3R) sigFourX liveRowY
      = (⟨0, 0, 0, 0, 0, 0, 0, 4, 0, 0⟩ : SqU5 gr3R) := by decide

/-- ⭐⭐ **The mirror-live `v`-letter**: `GradedFourMirror.mirFourV` with its second class-two
coordinate moved from `0` to `4`.  The `u`-letter is the committed `mirFourU`, untouched: it is
the open channel and it has to stay a legal dressing, which by
`sqRelWord_gaugeX_dress_low` means its own second class-two coordinate must stay in `{0, 4}`. -/
def mirLiveV : SqU5 gr3R := ⟨0, 0, 0, 1, 0, 4, 0, 0, 0, 0⟩

theorem mirLiveV_eq : mirLiveV = mirFourV * (⟨0, 0, 0, 0, 0, 4, 0, 0, 0, 0⟩ : SqU5 gr3R) := by
  decide

/-- ⭐⭐ **THE LIVE BLOCK AT THE MIRROR ROW.** -/
theorem commP_mirLive :
    commP mirFourU mirLiveV = (⟨0, 0, 0, 0, 0, 0, 0, 4, 0, 0⟩ : SqU5 gr3R) := by decide

theorem commP_mirLive_ne_one : commP mirFourU mirLiveV ≠ 1 := by decide

/-- ⭐⭐ **The left displacement is inert on it**, at every pivot residue: the marking's block
and the frame's block are the *same element*.  This is `commP_left_displace_inert` at
`⁅Φ(w), V₀⁆ = 1`, and it is the whole content of the mirror row's compatibility. -/
theorem commP_mirLiveUGen :
    ∀ c : gr3R, commP (mirFourUGen c) mirLiveV = commP mirFourU mirLiveV := by decide

/-- …and indeed the pivot commutes with the `v`-letter. -/
theorem commP_rowPivot_mirLiveV : ∀ c : gr3R, commP (rowPivotVal c) mirLiveV = 1 := by decide

theorem sqWord_mul_commP_mirLive :
    sqWord (sigFourMark gr3R) sigFourX liveRowY * commP mirFourU mirLiveV = 1 := by decide

variable (h j) in
/-- ⭐⭐ **The marking of the mirror-live point**, at every handle count and every residue. -/
def mirLiveMark (c : gr3R) : Fin (sqRank h) → SqU5 gr3R :=
  liveWit h j liveRowY (mirFourUGen c) mirLiveV 1

variable (h j) in
/-- The mirror-live witness: the same tuple with the **cleared** `u`-letter and the sigma slot
dressed by `v`. -/
def mirLiveWit (v : SqU5 gr3R) : Fin (sqRank h) → SqU5 gr3R :=
  liveWit h j liveRowY mirFourU mirLiveV v

/-- ⭐⭐ **The ten-row solve at the mirror-live point**, at every handle count, every handle and
every pivot residue - **with the handle block alive**. -/
theorem sqRelWord_mirLiveMark (c : gr3R) : sqRelWord (mirLiveMark h j c) = 1 := by
  rw [mirLiveMark, sqRelWord_liveWit, mul_one, commP_mirLiveUGen c, sqWord_mul_commP_mirLive]

/-- ⭐⭐ …and the cleared frame kills the relator too, so both standards of
`GradedFourMirror.chiA_row_forced` are met with a live block. -/
theorem sqRelWord_mirLiveWit_triv : sqRelWord (mirLiveWit h j 1) = 1 := by
  rw [mirLiveWit, sqRelWord_liveWit, mul_one, sqWord_mul_commP_mirLive]

theorem sqRelWord_mirLiveWit (v : SqU5 gr3R) :
    sqRelWord (mirLiveWit h j v)
      = sqWord (sigFourMark gr3R * v) sigFourX liveRowY * commP mirFourU mirLiveV :=
  sqRelWord_liveWit

/-- ⭐⭐ The cleared `u`-dressing leaves the **odd** residue `1`, exactly as at wave 56's dead
mirror point: the live block has changed no verdict. -/
theorem sqRelWord_mirLiveWit_U : sqRelWord (mirLiveWit h j mirFourU) = liftC 1 := by
  rw [sqRelWord_mirLiveWit]; decide

theorem sqRelWord_mirLiveWit_Usq :
    sqRelWord (mirLiveWit h j (mirFourU * mirFourU)) = liftC 2 := by
  rw [sqRelWord_mirLiveWit]; decide

/-- The `v`-letter dressing leaves nothing: it is `chi_a`-trivial by
`GradedFourMirror.chiA_mirror_forced`. -/
theorem sqRelWord_mirLiveWit_V : sqRelWord (mirLiveWit h j mirLiveV) = 1 := by
  rw [sqRelWord_mirLiveWit]; decide

theorem sqRelWord_mirLiveWit_Usq_complete :
    sqRelWord (sigLift j (mirLiveWit h j (mirFourU * mirFourU)) 1 1 (liftC 7) 1 1) = 1 := by
  rw [sqRelWord_sigLift SqU5.isGaThree_one SqU5.isGaFour_one (liftC_isGaFour 7)
    SqU5.isGaThree_one SqU5.isGaThree_one, sqRelWord_mirLiveWit_Usq, liftC_mul_liftC]
  refine Eq.trans (congrArg liftC ?_) liftC_zero
  simp only [mirLiveWit, liveWit_one, liveWit_handleU, liveWit_handleV, SqU5.one_h,
    SqU5.one_i, SqU5.one_j, mirFourU, mirLiveV, sigFourX]
  decide

/-- ⭐ Every class-`≤ 3` verdict is the same for all four dressings at the mirror-live point. -/
theorem mirLiveWit_class_three_blind :
    (SqU5.toU4L (sqRelWord (mirLiveWit h j 1)) = 1 ∧
      SqU5.toU4R (sqRelWord (mirLiveWit h j 1)) = 1) ∧
    (SqU5.toU4L (sqRelWord (mirLiveWit h j (mirFourU * mirFourU))) = 1 ∧
      SqU5.toU4R (sqRelWord (mirLiveWit h j (mirFourU * mirFourU))) = 1) ∧
    (SqU5.toU4L (sqRelWord (mirLiveWit h j mirFourU)) = 1 ∧
      SqU5.toU4R (sqRelWord (mirLiveWit h j mirFourU)) = 1) ∧
    (SqU5.toU4L (sqRelWord (mirLiveWit h j mirLiveV)) = 1 ∧
      SqU5.toU4R (sqRelWord (mirLiveWit h j mirLiveV)) = 1) := by
  rw [sqRelWord_mirLiveWit_triv, sqRelWord_mirLiveWit_Usq, sqRelWord_mirLiveWit_U,
    sqRelWord_mirLiveWit_V]
  refine ⟨⟨map_one _, map_one _⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, map_one _, map_one _⟩ <;> decide

/-! ### The mirror-live point as a continuous homomorphism -/

@[simp] theorem mirLiveMark_zero (c : gr3R) : mirLiveMark h j c 0 = sigFourMark gr3R := by
  rw [mirLiveMark, liveWit_zero, mul_one]

@[simp] theorem mirLiveMark_one (c : gr3R) : mirLiveMark h j c 1 = sigFourX := liveWit_one

@[simp] theorem mirLiveMark_two (c : gr3R) : mirLiveMark h j c 2 = liveRowY := liveWit_two

@[simp] theorem mirLiveMark_handleU (c : gr3R) :
    mirLiveMark h j c (sqHandleIdxU j) = mirFourUGen c := liveWit_handleU

@[simp] theorem mirLiveMark_handleV (c : gr3R) :
    mirLiveMark h j c (sqHandleIdxV j) = mirLiveV := liveWit_handleV

theorem mirLiveMark_handleU_ne (c : gr3R) {j' : Fin h} (hne : j' ≠ j) :
    mirLiveMark h j c (sqHandleIdxU j') = 1 := liveWit_handleU_ne hne

theorem mirLiveMark_handleV_ne (c : gr3R) {j' : Fin h} (hne : j' ≠ j) :
    mirLiveMark h j c (sqHandleIdxV j') = 1 := liveWit_handleV_ne hne

variable (h j) in
/-- ⭐⭐ **The mirror-live test hom.** -/
noncomputable def mirLiveHom : ContinuousMonoidHom (DSq h : Type) (SqU5 gr3R) :=
  sqU5Hom gr3R_card h (mirLiveMark h j (gr3Pi sqPivotExp))
    (sqRelWord_mirLiveMark (gr3Pi sqPivotExp))

@[simp] theorem mirLiveHom_gen (i : Fin (sqRank h)) :
    mirLiveHom h j (sqGen h i) = mirLiveMark h j (gr3Pi sqPivotExp) i := sqU5Hom_gen _ _ _ i

@[simp] theorem mirLiveHom_sigma : mirLiveHom h j (dsqSigma h) = sigFourMark gr3R := by
  rw [dsqSigma, mirLiveHom_gen, mirLiveMark_zero]

@[simp] theorem mirLiveHom_x0 : mirLiveHom h j (dsqX0 h) = sigFourX := by
  rw [dsqX0, mirLiveHom_gen, mirLiveMark_one]

@[simp] theorem mirLiveHom_x1 : mirLiveHom h j (dsqX1 h) = liveRowY := by
  rw [dsqX1, mirLiveHom_gen, mirLiveMark_two]

@[simp] theorem mirLiveHom_handleU :
    mirLiveHom h j (sqGen h (sqHandleIdxU j)) = mirFourUGen (gr3Pi sqPivotExp) := by
  rw [mirLiveHom_gen, mirLiveMark_handleU]

@[simp] theorem mirLiveHom_handleV : mirLiveHom h j (sqGen h (sqHandleIdxV j)) = mirLiveV := by
  rw [mirLiveHom_gen, mirLiveMark_handleV]

theorem mirLiveHom_handle_ne {j' : Fin h} (hne : j' ≠ j) :
    mirLiveHom h j (sqGen h (sqHandleIdxU j')) = 1 ∧
      mirLiveHom h j (sqGen h (sqHandleIdxV j')) = 1 :=
  ⟨by rw [mirLiveHom_gen, mirLiveMark_handleU_ne _ hne],
    by rw [mirLiveHom_gen, mirLiveMark_handleV_ne _ hne]⟩

theorem mirLiveHom_sqPivot :
    mirLiveHom h j (sqPivot h) = rowPivotVal (gr3Pi sqPivotExp) :=
  mirHom_sqPivot mirLiveHom_sigma mirLiveHom_x0

/-- ⭐⭐ **The handle commutator is live in the IMAGE** at the mirror row. -/
theorem mirLiveHom_commP_ne_one :
    commP (mirLiveHom h j (sqGen h (sqHandleIdxU j)))
      (mirLiveHom h j (sqGen h (sqHandleIdxV j))) ≠ 1 := by
  rw [mirLiveHom_handleU, mirLiveHom_handleV, commP_mirLiveUGen]
  exact commP_mirLive_ne_one

theorem mirLiveHom_sqEichV : mirLiveHom h j (sqEichV h (nuSel h j 1 0) j) = mirLiveV := by
  rw [sqEichV_of_cleared nuSelMir_handleV, mirLiveHom_handleV]

/-- ⭐⭐ The cleared `u`-letter is the point's open channel, with one inverse pivot subtracted
on the **left**. -/
theorem mirLiveHom_sqEichU : mirLiveHom h j (sqEichU h (nuSel h j 1 0) j) = mirFourU := by
  rw [sqEichU, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_gr5, nuSel_handleU,
    toAdd_ofAdd, zpowZtwo_one_exp, mirLiveHom_sqPivot, mirLiveHom_handleU, mirFourU_eq]

theorem mirLiveHom_b (x : (DSq h : Type)) :
    (mirLiveHom h j x).b = gr3Pi (toAdd (nuSel h j 1 0 x)) :=
  mirHom_b (by rw [mirLiveHom_sigma]; rfl) (by rw [mirLiveHom_x0]; rfl)
    (by rw [mirLiveHom_x1]; rfl) (by rw [mirLiveHom_handleU, map_one]; rfl)
    (by rw [mirLiveHom_handleV, map_zero]; rfl)
    (fun j' hj' => by rw [(mirLiveHom_handle_ne hj').1, (mirLiveHom_handle_ne hj').2]; exact
      ⟨rfl, rfl⟩) x

theorem mirLiveHom_b_eq_zero {g : (DSq h : Type)} (hg : nuSel h j 1 0 g = 1) :
    (mirLiveHom h j g).b = 0 := by
  rw [mirLiveHom_b, hg, toAdd_one, map_zero]

/-- ⭐⭐ **The frame identification at the mirror-live point.** -/
theorem mirLiveHom_sqArbFrame (g : (DSq h : Type)) :
    (fun i => mirLiveHom h j (sqArbFrame h (nuSel h j 1 0) j (sigArbDress h g) i))
      = mirLiveWit h j (mirLiveHom h j g) := by
  rw [mirLiveWit, liveWit_eq_dress]
  exact liveHom_sqArbFrame (m := mirLiveWit h j 1)
    (by rw [mirLiveHom_sigma, mirLiveWit, liveWit_zero, mul_one])
    (by rw [mirLiveHom_x0, mirLiveWit, liveWit_one])
    (by rw [mirLiveHom_x1, mirLiveWit, liveWit_two])
    (by rw [mirLiveHom_sqEichU, mirLiveWit, liveWit_handleU])
    (by rw [mirLiveHom_sqEichV, mirLiveWit, liveWit_handleV])
    (fun j' hj' => ⟨by rw [(mirLiveHom_handle_ne hj').1, mirLiveWit, liveWit_handleU_ne hj'],
      by rw [(mirLiveHom_handle_ne hj').2, mirLiveWit, liveWit_handleV_ne hj']⟩) g

/-! ### Soundness at the mirror-live point -/

theorem liveRowY_mem_liveFrameSub : liveRowY ∈ liveFrameSub gr3R :=
  ⟨rfl, ⟨0, by show (0 : gr3R) = 2 * 0; ring⟩, 2, by show (4 : gr3R) = 2 * 2; decide⟩

theorem mirFourU_mem_liveFrameSub : mirFourU ∈ liveFrameSub gr3R :=
  ⟨rfl, ⟨0, by show (0 : gr3R) = 2 * 0; ring⟩, 0, by show (0 : gr3R) = 2 * 0; ring⟩

theorem mirLiveV_mem_liveFrameSub : mirLiveV ∈ liveFrameSub gr3R :=
  ⟨rfl, ⟨2, by show (4 : gr3R) = 2 * 2; decide⟩, 0, by show (0 : gr3R) = 2 * 0; ring⟩

theorem mirFourUGen_mem_liveFrameSub (c : gr3R) : mirFourUGen c ∈ liveFrameSub gr3R :=
  ⟨rfl, ⟨0, by show (0 : gr3R) = 2 * 0; ring⟩, 0, by show (0 : gr3R) = 2 * 0; ring⟩

theorem sigFourMark_mem_liveFrameSub : sigFourMark gr3R ∈ liveFrameSub gr3R :=
  ⟨rfl, ⟨0, by show (0 : gr3R) = 2 * 0; ring⟩, 0, by show (0 : gr3R) = 2 * 0; ring⟩

/-- ⭐⭐ **The model-independent soundness at the mirror-live point.** -/
theorem mirLive_gaTwo_even (c : gr3R) {z : SqU5 gr3R}
    (hz : z ∈ rowGaTwoOf (Subgroup.closure (Set.range (mirLiveMark h j c)))) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) :=
  liveWit_gaTwo_even liveRowY_mem_liveFrameSub (mirFourUGen_mem_liveFrameSub c)
    mirLiveV_mem_liveFrameSub (by rw [mul_one]; exact sigFourMark_mem_liveFrameSub) hz

/-- ⭐⭐ **The sharper wave-55 bound is FALSE at the mirror-live point**: the block itself is a
commutator of two image elements with non-vanishing first class-three coordinate, so `even` is
the sharpest bound this point admits. -/
theorem mirLive_not_rowGaTwoSub (c : gr3R) :
    ¬ rowGaTwoOf (Subgroup.closure (Set.range (mirLiveMark h j c))) ≤ rowGaTwoSub gr3R := by
  intro hle
  have hmem : commP (mirLiveMark h j c (sqHandleIdxU j)) (mirLiveMark h j c (sqHandleIdxV j))
      ∈ rowGaTwoOf (Subgroup.closure (Set.range (mirLiveMark h j c))) :=
    Subgroup.subset_closure ⟨_, Subgroup.subset_closure ⟨_, rfl⟩, _,
      Subgroup.subset_closure ⟨_, rfl⟩, rfl⟩
  obtain ⟨-, -, -, -, -, -, hh, -⟩ := hle hmem
  rw [mirLiveMark_handleU, mirLiveMark_handleV, commP_mirLiveUGen, commP_mirLive] at hh
  exact absurd hh (by decide)

/-- The committed achievable lattice is even at the mirror-live point: its parameters are wave
56's mirror ones `(1, 0, 0, 0, 0, 1, 1, 0)`, because the live perturbation touches no column
the lattice reads. -/
theorem mirLiveWit_lamThree_even {P Q R : gr3R} {z : SqU5 gr3R}
    (hz : selLamThree 1 0 0 0 0 1 1 0 P Q R z) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) :=
  mirFourWit_lamThree_even hz

/-- The three `x₁`-slot commutators at the mirror-live point, for the extended lattice. -/
theorem mirLiveWit_commP_data :
    commP (sigFourMark gr3R) liveRowY = (⟨0, 0, 0, 0, 0, 0, 0, 0, 4, 0⟩ : SqU5 gr3R) ∧
      commP liveRowY mirFourU = (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 6⟩ : SqU5 gr3R) ∧
      commP liveRowY mirLiveV = (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 2⟩ : SqU5 gr3R) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem mirLiveHom_mem_closure (x : (DSq h : Type)) :
    mirLiveHom h j x ∈ Subgroup.closure (Set.range (mirLiveMark h j (gr3Pi sqPivotExp))) := by
  have hgen : Subgroup.closure (Set.range (sqGen h))
      ≤ Subgroup.comap (mirLiveHom h j).toMonoidHom
        (Subgroup.closure (Set.range (mirLiveMark h j (gr3Pi sqPivotExp)))) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    show mirLiveHom h j (sqGen h i)
      ∈ Subgroup.closure (Set.range (mirLiveMark h j (gr3Pi sqPivotExp)))
    rw [mirLiveHom_gen]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hclosed : IsClosed ((Subgroup.comap (mirLiveHom h j).toMonoidHom
      (Subgroup.closure (Set.range (mirLiveMark h j (gr3Pi sqPivotExp)))) :
        Subgroup (DSq h : Type)) : Set (DSq h : Type)) := by
    have hpre : ((Subgroup.comap (mirLiveHom h j).toMonoidHom
        (Subgroup.closure (Set.range (mirLiveMark h j (gr3Pi sqPivotExp)))) :
          Subgroup (DSq h : Type)) : Set (DSq h : Type))
        = mirLiveHom h j ⁻¹' ((Subgroup.closure
            (Set.range (mirLiveMark h j (gr3Pi sqPivotExp)))) : Set (SqU5 gr3R)) := rfl
    rw [hpre]
    exact (isClosed_discrete _).preimage (mirLiveHom h j).continuous_toFun
  have hle := Subgroup.topologicalClosure_minimal _ hgen hclosed
  rw [dsq_topGen h] at hle
  exact hle (Subgroup.mem_top x)

/-! ### The forcing at the mirror-live row -/

/-- ⭐⭐ **The sigma forcing at the mirror-live point.** -/
theorem mirLiveWit_sigma_forced {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (h₃ : (∃ a : gr3R, z₃.h = 2 * a) ∧ (∃ b : gr3R, z₃.i = 2 * b))
    (h₄ : (∃ a : gr3R, z₄.h = 2 * a) ∧ (∃ b : gr3R, z₄.i = 2 * b))
    (hkill : sqRelWord (sigLift j (mirLiveWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  liveWit_sigma_forced (by decide) (by decide) (by decide) (by decide)
    sqRelWord_mirLiveWit_triv hvb hz₀ hw₁ hw₂ hz₃ hz₄ h₃ h₄ hkill

/-- ⭐⭐ **…against the committed achievable lattice.** -/
theorem mirLiveWit_sigma_forced_lam {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hvb : v.b = 0) (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : selLamThree 1 0 0 0 0 1 1 0 P Q R z₃)
    (l₄ : selLamThree 1 0 0 0 0 1 1 0 P Q R z₄)
    (hkill : sqRelWord (sigLift j (mirLiveWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  mirLiveWit_sigma_forced hvb hz₀ hw₁ hw₂ hz₃ hz₄ (mirLiveWit_lamThree_even l₃)
    (mirLiveWit_lamThree_even l₄) hkill

/-- ⭐⭐ **…and with no lattice model at all.** -/
theorem mirLiveWit_sigma_forced_gaTwo {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hvb : v.b = 0) (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (mirLiveMark h j c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (mirLiveMark h j c))))
    (hkill : sqRelWord (sigLift j (mirLiveWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  mirLiveWit_sigma_forced hvb hz₀ hw₁ hw₂ hz₃ hz₄ (mirLive_gaTwo_even c l₃)
    (mirLive_gaTwo_even c l₄) hkill

/-- ⭐⭐ **The forcing is not vacuous at the mirror-live point.** -/
theorem mirLive_forcing_nonvacuous :
    nuLam h (sqEichU h (nuSel h j 1 0) j) = 1 ∧
      nuSel h j 1 0 (sqEichU h (nuSel h j 1 0) j) = 1 ∧
      selPar (mirLiveHom h j (sqEichU h (nuSel h j 1 0) j)).a = 1 :=
  ⟨nuLam_mirEichU, nu_mirEichU, by rw [mirLiveHom_sqEichU]; exact mirFourU_chiA⟩

theorem sqRelWord_mirLiveFrame_sigTriv :
    sqRelWord (fun i =>
      mirLiveHom h j (sqArbFrame h (nuSel h j 1 0) j (sigArbDress h 1) i)) = 1 := by
  rw [mirLiveHom_sqArbFrame, map_one]
  exact sqRelWord_mirLiveWit_triv

theorem sqRelWord_mirLiveFrame_sigU :
    sqRelWord (fun i => mirLiveHom h j (sqArbFrame h (nuSel h j 1 0) j
      (sigArbDress h (sqEichU h (nuSel h j 1 0) j)) i)) = liftC 1 := by
  rw [mirLiveHom_sqArbFrame, mirLiveHom_sqEichU]
  exact sqRelWord_mirLiveWit_U

theorem sqRelWord_mirLiveFrame_sigUsq :
    sqRelWord (fun i => mirLiveHom h j (sqArbFrame h (nuSel h j 1 0) j
      (sigArbDress h (sqEichU h (nuSel h j 1 0) j * sqEichU h (nuSel h j 1 0) j)) i))
      = liftC 2 := by
  rw [mirLiveHom_sqArbFrame, map_mul, mirLiveHom_sqEichU]
  exact sqRelWord_mirLiveWit_Usq

theorem sqRelWord_mirLiveFrame_sigUsq_complete :
    sqRelWord (sigLift j (fun i => mirLiveHom h j (sqArbFrame h (nuSel h j 1 0) j
      (sigArbDress h (sqEichU h (nuSel h j 1 0) j * sqEichU h (nuSel h j 1 0) j)) i))
      1 1 (liftC 7) 1 1) = 1 := by
  rw [mirLiveHom_sqArbFrame, map_mul, mirLiveHom_sqEichU]
  exact sqRelWord_mirLiveWit_Usq_complete

/-- ⭐⭐ **The odd dressing survives nothing at the mirror-live point.** -/
theorem sqRelWord_mirLiveFrame_sigU_ne_one_gaTwo {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (mirLiveMark h j c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (mirLiveMark h j c)))) :
    sqRelWord (sigLift j (fun i => mirLiveHom h j (sqArbFrame h (nuSel h j 1 0) j
      (sigArbDress h (sqEichU h (nuSel h j 1 0) j)) i)) z₀ w₁ w₂ z₃ z₄) ≠ 1 := by
  rw [mirLiveHom_sqArbFrame, mirLiveHom_sqEichU]
  intro hc
  have hpar := mirLiveWit_sigma_forced_gaTwo (v := mirFourU) (c := c) (by decide) hz₀ hw₁ hw₂
    hz₃ hz₄ l₃ l₄ hc
  rw [show (mirFourU.a : gr3R) = 1 from rfl] at hpar
  exact absurd hpar (by decide)

/-- ⭐⭐ **The class-four selection bit on `sqArbFrame` at the mirror-live point.** -/
theorem sqArbFrame_sigma_bit_mirLive {g : (DSq h : Type)} (hg : nuSel h j 1 0 g = 1) :
    selPar ((sqRelWord fun i =>
        mirLiveHom h j (sqArbFrame h (nuSel h j 1 0) j (sigArbDress h g) i)).j)
      = selPar (mirLiveHom h j g).a := by
  rw [mirLiveHom_sqArbFrame g, mirLiveWit]
  exact liveWit_sigma_bit (by decide) (by decide) (by decide) (by decide)
    (mirLiveHom_b_eq_zero hg) sqRelWord_mirLiveWit_triv

/-- ⭐⭐ **THE HEADLINE AT THE MIRROR ROW.**  At the displaced row `nuSel h j 1 0`, at every
handle count, at an honest continuous homomorphism whose handle commutator is **nontrivial in
the image**, every `ν'`-trivial sigma dressing of the arbitrary-dressing frame killed by any
achievable five-slot class-four refinement has an even `chi_a`-character. -/
theorem sqArbFrame_sigma_forced_mirLive {g : (DSq h : Type)} (hg : nuSel h j 1 0 g = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (mirLiveMark h j c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (mirLiveMark h j c))))
    (hkill : sqRelWord (sigLift j
      (fun i => mirLiveHom h j (sqArbFrame h (nuSel h j 1 0) j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (mirLiveHom h j g).a = 0 := by
  rw [mirLiveHom_sqArbFrame g] at hkill
  exact mirLiveWit_sigma_forced_gaTwo (mirLiveHom_b_eq_zero hg) hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄ hkill

/-- ⭐⭐ **…and against the committed achievable lattice.** -/
theorem sqArbFrame_sigma_forced_mirLive_lam {g : (DSq h : Type)} (hg : nuSel h j 1 0 g = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : selLamThree 1 0 0 0 0 1 1 0 P Q R z₃)
    (l₄ : selLamThree 1 0 0 0 0 1 1 0 P Q R z₄)
    (hkill : sqRelWord (sigLift j
      (fun i => mirLiveHom h j (sqArbFrame h (nuSel h j 1 0) j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (mirLiveHom h j g).a = 0 := by
  rw [mirLiveHom_sqArbFrame g] at hkill
  exact mirLiveWit_sigma_forced_lam (mirLiveHom_b_eq_zero hg) hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄ hkill

/-- ⭐⭐ **The escape separates the sigma dressings at the mirror row with a live block.** -/
theorem mirLive_escape_separates :
    commP (mirLiveHom h j (sqGen h (sqHandleIdxU j)))
        (mirLiveHom h j (sqGen h (sqHandleIdxV j))) ≠ 1 ∧
    ((∀ i, nuLam h (sigArbDress h
        (sqEichU h (nuSel h j 1 0) j * sqEichU h (nuSel h j 1 0) j) i) = 1) ∧
      ∀ i, nuSel h j 1 0 (sigArbDress h
        (sqEichU h (nuSel h j 1 0) j * sqEichU h (nuSel h j 1 0) j) i) = 1) ∧
    ((∀ i, nuLam h (sigArbDress h (sqEichU h (nuSel h j 1 0) j) i) = 1) ∧
      ∀ i, nuSel h j 1 0 (sigArbDress h (sqEichU h (nuSel h j 1 0) j) i) = 1) ∧
    sqRelWord (fun i => mirLiveHom h j (sqArbFrame h (nuSel h j 1 0) j
      (sigArbDress h (sqEichU h (nuSel h j 1 0) j * sqEichU h (nuSel h j 1 0) j)) i))
      = liftC 2 ∧
    sqRelWord (fun i => mirLiveHom h j (sqArbFrame h (nuSel h j 1 0) j
      (sigArbDress h (sqEichU h (nuSel h j 1 0) j)) i)) = liftC 1 :=
  ⟨mirLiveHom_commP_ne_one,
    ⟨nuLam_sigArbDress_mirUsq, nu_sigArbDress_mirUsq⟩,
    ⟨nuLam_sigArbDress_mirU, nu_sigArbDress_mirU⟩,
    sqRelWord_mirLiveFrame_sigUsq, sqRelWord_mirLiveFrame_sigU⟩

end MirrorLive

/-! ## 6 The uncleared-`v` row `nuSel h j 0 1` with a live handle block -/

section RowLive

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐ **The row-live `u`-letter**: `GradedFourRow.rowFourU` with its second class-two
coordinate moved from `0` to `4`.  The `v`-letter is the committed `rowFourV`, untouched: it is
this row's open channel.  ⚠ Compared with the mirror row the roles are **exchanged**, exactly as
wave 56's dead points exchange them - but for a different reason: here the perturbed letter is
the one the *right* displacement conjugates the block through. -/
def rowLiveU : SqU5 gr3R := ⟨0, 0, 0, 1, 0, 4, 0, 0, 0, 0⟩

theorem rowLiveU_eq : rowLiveU = rowFourU * (⟨0, 0, 0, 0, 0, 4, 0, 0, 0, 0⟩ : SqU5 gr3R) := by
  decide

/-- ⭐⭐ **THE LIVE BLOCK AT THE UNCLEARED-`v` ROW**, the same class-three element as at the
mirror row. -/
theorem commP_rowLive :
    commP rowLiveU rowFourV = (⟨0, 0, 0, 0, 0, 0, 0, 4, 0, 0⟩ : SqU5 gr3R) := by decide

theorem commP_rowLive_ne_one : commP rowLiveU rowFourV ≠ 1 := by decide

/-- ⭐⭐ **The right displacement's two effects cancel**, at every pivot residue: `⁅U₀, Φ(w)⁆`
is trivial and the conjugation defect `2c·b.i` vanishes because the block's second class-three
coordinate does.  By `commP_rowPivot_right_defect` those are exactly the two terms, so the
marking's block and the frame's block agree. -/
theorem commP_rowLiveVGen :
    ∀ c : gr3R, commP rowLiveU (rowFourVGen c) = commP rowLiveU rowFourV := by decide

theorem commP_rowLiveU_rowPivot : ∀ c : gr3R, commP rowLiveU (rowPivotVal c) = 1 := by decide

theorem sqWord_mul_commP_rowLive :
    sqWord (sigFourMark gr3R) sigFourX liveRowY * commP rowLiveU rowFourV = 1 := by decide

variable (h j) in
/-- ⭐⭐ **The marking of the row-live point.** -/
def rowLiveMark (c : gr3R) : Fin (sqRank h) → SqU5 gr3R :=
  liveWit h j liveRowY rowLiveU (rowFourVGen c) 1

variable (h j) in
/-- The row-live witness, with the **cleared** `v`-letter and the sigma slot dressed by `v`. -/
def rowLiveWit (v : SqU5 gr3R) : Fin (sqRank h) → SqU5 gr3R :=
  liveWit h j liveRowY rowLiveU rowFourV v

/-- ⭐⭐ **The ten-row solve at the row-live point**, at every handle count, handle and pivot
residue, with the block alive. -/
theorem sqRelWord_rowLiveMark (c : gr3R) : sqRelWord (rowLiveMark h j c) = 1 := by
  rw [rowLiveMark, sqRelWord_liveWit, mul_one, commP_rowLiveVGen c, sqWord_mul_commP_rowLive]

theorem sqRelWord_rowLiveWit_triv : sqRelWord (rowLiveWit h j 1) = 1 := by
  rw [rowLiveWit, sqRelWord_liveWit, mul_one, sqWord_mul_commP_rowLive]

theorem sqRelWord_rowLiveWit (v : SqU5 gr3R) :
    sqRelWord (rowLiveWit h j v)
      = sqWord (sigFourMark gr3R * v) sigFourX liveRowY * commP rowLiveU rowFourV :=
  sqRelWord_liveWit

theorem sqRelWord_rowLiveWit_V : sqRelWord (rowLiveWit h j rowFourV) = liftC 1 := by
  rw [sqRelWord_rowLiveWit]; decide

theorem sqRelWord_rowLiveWit_Vsq :
    sqRelWord (rowLiveWit h j (rowFourV * rowFourV)) = liftC 2 := by
  rw [sqRelWord_rowLiveWit]; decide

theorem sqRelWord_rowLiveWit_U : sqRelWord (rowLiveWit h j rowLiveU) = 1 := by
  rw [sqRelWord_rowLiveWit]; decide

theorem sqRelWord_rowLiveWit_Vsq_complete :
    sqRelWord (sigLift j (rowLiveWit h j (rowFourV * rowFourV)) 1 1 (liftC 7) 1 1) = 1 := by
  rw [sqRelWord_sigLift SqU5.isGaThree_one SqU5.isGaFour_one (liftC_isGaFour 7)
    SqU5.isGaThree_one SqU5.isGaThree_one, sqRelWord_rowLiveWit_Vsq, liftC_mul_liftC]
  refine Eq.trans (congrArg liftC ?_) liftC_zero
  simp only [rowLiveWit, liveWit_one, liveWit_handleU, liveWit_handleV, SqU5.one_h,
    SqU5.one_i, SqU5.one_j, rowLiveU, rowFourV, sigFourX]
  decide

theorem rowLiveWit_class_three_blind :
    (SqU5.toU4L (sqRelWord (rowLiveWit h j 1)) = 1 ∧
      SqU5.toU4R (sqRelWord (rowLiveWit h j 1)) = 1) ∧
    (SqU5.toU4L (sqRelWord (rowLiveWit h j (rowFourV * rowFourV))) = 1 ∧
      SqU5.toU4R (sqRelWord (rowLiveWit h j (rowFourV * rowFourV))) = 1) ∧
    (SqU5.toU4L (sqRelWord (rowLiveWit h j rowFourV)) = 1 ∧
      SqU5.toU4R (sqRelWord (rowLiveWit h j rowFourV)) = 1) := by
  rw [sqRelWord_rowLiveWit_triv, sqRelWord_rowLiveWit_Vsq, sqRelWord_rowLiveWit_V]
  refine ⟨⟨map_one _, map_one _⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

@[simp] theorem rowLiveMark_zero (c : gr3R) : rowLiveMark h j c 0 = sigFourMark gr3R := by
  rw [rowLiveMark, liveWit_zero, mul_one]

@[simp] theorem rowLiveMark_one (c : gr3R) : rowLiveMark h j c 1 = sigFourX := liveWit_one

@[simp] theorem rowLiveMark_two (c : gr3R) : rowLiveMark h j c 2 = liveRowY := liveWit_two

@[simp] theorem rowLiveMark_handleU (c : gr3R) :
    rowLiveMark h j c (sqHandleIdxU j) = rowLiveU := liveWit_handleU

@[simp] theorem rowLiveMark_handleV (c : gr3R) :
    rowLiveMark h j c (sqHandleIdxV j) = rowFourVGen c := liveWit_handleV

theorem rowLiveMark_handleU_ne (c : gr3R) {j' : Fin h} (hne : j' ≠ j) :
    rowLiveMark h j c (sqHandleIdxU j') = 1 := liveWit_handleU_ne hne

theorem rowLiveMark_handleV_ne (c : gr3R) {j' : Fin h} (hne : j' ≠ j) :
    rowLiveMark h j c (sqHandleIdxV j') = 1 := liveWit_handleV_ne hne

variable (h j) in
/-- ⭐⭐ **The row-live test hom.** -/
noncomputable def rowLiveHom : ContinuousMonoidHom (DSq h : Type) (SqU5 gr3R) :=
  sqU5Hom gr3R_card h (rowLiveMark h j (gr3Pi sqPivotExp))
    (sqRelWord_rowLiveMark (gr3Pi sqPivotExp))

@[simp] theorem rowLiveHom_gen (i : Fin (sqRank h)) :
    rowLiveHom h j (sqGen h i) = rowLiveMark h j (gr3Pi sqPivotExp) i := sqU5Hom_gen _ _ _ i

@[simp] theorem rowLiveHom_sigma : rowLiveHom h j (dsqSigma h) = sigFourMark gr3R := by
  rw [dsqSigma, rowLiveHom_gen, rowLiveMark_zero]

@[simp] theorem rowLiveHom_x0 : rowLiveHom h j (dsqX0 h) = sigFourX := by
  rw [dsqX0, rowLiveHom_gen, rowLiveMark_one]

@[simp] theorem rowLiveHom_x1 : rowLiveHom h j (dsqX1 h) = liveRowY := by
  rw [dsqX1, rowLiveHom_gen, rowLiveMark_two]

@[simp] theorem rowLiveHom_handleU :
    rowLiveHom h j (sqGen h (sqHandleIdxU j)) = rowLiveU := by
  rw [rowLiveHom_gen, rowLiveMark_handleU]

@[simp] theorem rowLiveHom_handleV :
    rowLiveHom h j (sqGen h (sqHandleIdxV j)) = rowFourVGen (gr3Pi sqPivotExp) := by
  rw [rowLiveHom_gen, rowLiveMark_handleV]

theorem rowLiveHom_handle_ne {j' : Fin h} (hne : j' ≠ j) :
    rowLiveHom h j (sqGen h (sqHandleIdxU j')) = 1 ∧
      rowLiveHom h j (sqGen h (sqHandleIdxV j')) = 1 :=
  ⟨by rw [rowLiveHom_gen, rowLiveMark_handleU_ne _ hne],
    by rw [rowLiveHom_gen, rowLiveMark_handleV_ne _ hne]⟩

theorem rowLiveHom_sqPivot :
    rowLiveHom h j (sqPivot h) = rowPivotVal (gr3Pi sqPivotExp) :=
  mirHom_sqPivot rowLiveHom_sigma rowLiveHom_x0

theorem rowLiveHom_commP_ne_one :
    commP (rowLiveHom h j (sqGen h (sqHandleIdxU j)))
      (rowLiveHom h j (sqGen h (sqHandleIdxV j))) ≠ 1 := by
  rw [rowLiveHom_handleU, rowLiveHom_handleV, commP_rowLiveVGen]
  exact commP_rowLive_ne_one

theorem rowLiveHom_sqEichU : rowLiveHom h j (sqEichU h (nuSel h j 0 1) j) = rowLiveU := by
  rw [sqEichU_of_cleared nuSelWide_handleU, rowLiveHom_handleU]

theorem rowLiveHom_sqEichV : rowLiveHom h j (sqEichV h (nuSel h j 0 1) j) = rowFourV := by
  rw [sqEichV, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_gr5, nuSel_handleV,
    toAdd_ofAdd, zpowZtwo_one_exp, rowLiveHom_sqPivot, rowLiveHom_handleV, rowFourV_eq]

theorem rowLiveHom_b (x : (DSq h : Type)) :
    (rowLiveHom h j x).b = gr3Pi (toAdd (nuSel h j 0 1 x)) :=
  mirHom_b (by rw [rowLiveHom_sigma]; rfl) (by rw [rowLiveHom_x0]; rfl)
    (by rw [rowLiveHom_x1]; rfl) (by rw [rowLiveHom_handleU, map_zero]; rfl)
    (by rw [rowLiveHom_handleV, map_one]; rfl)
    (fun j' hj' => by rw [(rowLiveHom_handle_ne hj').1, (rowLiveHom_handle_ne hj').2]; exact
      ⟨rfl, rfl⟩) x

theorem rowLiveHom_b_eq_zero {g : (DSq h : Type)} (hg : nuSel h j 0 1 g = 1) :
    (rowLiveHom h j g).b = 0 := by
  rw [rowLiveHom_b, hg, toAdd_one, map_zero]

theorem rowLiveHom_sqArbFrame (g : (DSq h : Type)) :
    (fun i => rowLiveHom h j (sqArbFrame h (nuSel h j 0 1) j (sigArbDress h g) i))
      = rowLiveWit h j (rowLiveHom h j g) := by
  rw [rowLiveWit, liveWit_eq_dress]
  exact liveHom_sqArbFrame (m := rowLiveWit h j 1)
    (by rw [rowLiveHom_sigma, rowLiveWit, liveWit_zero, mul_one])
    (by rw [rowLiveHom_x0, rowLiveWit, liveWit_one])
    (by rw [rowLiveHom_x1, rowLiveWit, liveWit_two])
    (by rw [rowLiveHom_sqEichU, rowLiveWit, liveWit_handleU])
    (by rw [rowLiveHom_sqEichV, rowLiveWit, liveWit_handleV])
    (fun j' hj' => ⟨by rw [(rowLiveHom_handle_ne hj').1, rowLiveWit, liveWit_handleU_ne hj'],
      by rw [(rowLiveHom_handle_ne hj').2, rowLiveWit, liveWit_handleV_ne hj']⟩) g

theorem rowLiveU_mem_liveFrameSub : rowLiveU ∈ liveFrameSub gr3R :=
  ⟨rfl, ⟨2, by show (4 : gr3R) = 2 * 2; decide⟩, 0, by show (0 : gr3R) = 2 * 0; ring⟩

theorem rowFourV_mem_liveFrameSub : rowFourV ∈ liveFrameSub gr3R :=
  ⟨rfl, ⟨0, by show (0 : gr3R) = 2 * 0; ring⟩, 0, by show (0 : gr3R) = 2 * 0; ring⟩

theorem rowFourVGen_mem_liveFrameSub (c : gr3R) : rowFourVGen c ∈ liveFrameSub gr3R :=
  ⟨rfl, ⟨0, by show (0 : gr3R) = 2 * 0; ring⟩, 0, by show (0 : gr3R) = 2 * 0; ring⟩

/-- ⭐⭐ **The model-independent soundness at the row-live point.** -/
theorem rowLive_gaTwo_even (c : gr3R) {z : SqU5 gr3R}
    (hz : z ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowLiveMark h j c)))) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) :=
  liveWit_gaTwo_even liveRowY_mem_liveFrameSub rowLiveU_mem_liveFrameSub
    (rowFourVGen_mem_liveFrameSub c)
    (by rw [mul_one]; exact sigFourMark_mem_liveFrameSub) hz

/-- ⭐⭐ **The sharper wave-55 bound is FALSE at the row-live point.** -/
theorem rowLive_not_rowGaTwoSub (c : gr3R) :
    ¬ rowGaTwoOf (Subgroup.closure (Set.range (rowLiveMark h j c))) ≤ rowGaTwoSub gr3R := by
  intro hle
  have hmem : commP (rowLiveMark h j c (sqHandleIdxU j)) (rowLiveMark h j c (sqHandleIdxV j))
      ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowLiveMark h j c))) :=
    Subgroup.subset_closure ⟨_, Subgroup.subset_closure ⟨_, rfl⟩, _,
      Subgroup.subset_closure ⟨_, rfl⟩, rfl⟩
  obtain ⟨-, -, -, -, -, -, hh, -⟩ := hle hmem
  rw [rowLiveMark_handleU, rowLiveMark_handleV, commP_rowLiveVGen, commP_rowLive] at hh
  exact absurd hh (by decide)

/-- The committed achievable lattice is even at the row-live point, at wave 55's own
parameters `(0, 1, 0, 0, 1, 0, 0, 1)`. -/
theorem rowLiveWit_lamThree_even {P Q R : gr3R} {z : SqU5 gr3R}
    (hz : selLamThree 0 1 0 0 1 0 0 1 P Q R z) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) :=
  rowFourWit_lamThree_even hz

theorem rowLiveWit_commP_data :
    commP (sigFourMark gr3R) liveRowY = (⟨0, 0, 0, 0, 0, 0, 0, 0, 4, 0⟩ : SqU5 gr3R) ∧
      commP liveRowY rowLiveU = (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 2⟩ : SqU5 gr3R) ∧
      commP liveRowY rowFourV = (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 6⟩ : SqU5 gr3R) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⭐⭐ **The sigma forcing at the row-live point.** -/
theorem rowLiveWit_sigma_forced {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (h₃ : (∃ a : gr3R, z₃.h = 2 * a) ∧ (∃ b : gr3R, z₃.i = 2 * b))
    (h₄ : (∃ a : gr3R, z₄.h = 2 * a) ∧ (∃ b : gr3R, z₄.i = 2 * b))
    (hkill : sqRelWord (sigLift j (rowLiveWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  liveWit_sigma_forced (by decide) (by decide) (by decide) (by decide)
    sqRelWord_rowLiveWit_triv hvb hz₀ hw₁ hw₂ hz₃ hz₄ h₃ h₄ hkill

theorem rowLiveWit_sigma_forced_lam {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hvb : v.b = 0) (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : selLamThree 0 1 0 0 1 0 0 1 P Q R z₃)
    (l₄ : selLamThree 0 1 0 0 1 0 0 1 P Q R z₄)
    (hkill : sqRelWord (sigLift j (rowLiveWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  rowLiveWit_sigma_forced hvb hz₀ hw₁ hw₂ hz₃ hz₄ (rowLiveWit_lamThree_even l₃)
    (rowLiveWit_lamThree_even l₄) hkill

theorem rowLiveWit_sigma_forced_gaTwo {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hvb : v.b = 0) (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowLiveMark h j c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowLiveMark h j c))))
    (hkill : sqRelWord (sigLift j (rowLiveWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  rowLiveWit_sigma_forced hvb hz₀ hw₁ hw₂ hz₃ hz₄ (rowLive_gaTwo_even c l₃)
    (rowLive_gaTwo_even c l₄) hkill

theorem rowLive_forcing_nonvacuous :
    nuLam h (sqEichV h (nuSel h j 0 1) j) = 1 ∧
      nuSel h j 0 1 (sqEichV h (nuSel h j 0 1) j) = 1 ∧
      selPar (rowLiveHom h j (sqEichV h (nuSel h j 0 1) j)).a = 1 :=
  ⟨nuLam_wideEichV, nu_wideEichV, by rw [rowLiveHom_sqEichV]; exact rowFourV_chiA⟩

theorem sqRelWord_rowLiveFrame_sigTriv :
    sqRelWord (fun i =>
      rowLiveHom h j (sqArbFrame h (nuSel h j 0 1) j (sigArbDress h 1) i)) = 1 := by
  rw [rowLiveHom_sqArbFrame, map_one]
  exact sqRelWord_rowLiveWit_triv

theorem sqRelWord_rowLiveFrame_sigV :
    sqRelWord (fun i => rowLiveHom h j (sqArbFrame h (nuSel h j 0 1) j
      (sigArbDress h (sqEichV h (nuSel h j 0 1) j)) i)) = liftC 1 := by
  rw [rowLiveHom_sqArbFrame, rowLiveHom_sqEichV]
  exact sqRelWord_rowLiveWit_V

theorem sqRelWord_rowLiveFrame_sigVsq :
    sqRelWord (fun i => rowLiveHom h j (sqArbFrame h (nuSel h j 0 1) j
      (sigArbDress h (sqEichV h (nuSel h j 0 1) j * sqEichV h (nuSel h j 0 1) j)) i))
      = liftC 2 := by
  rw [rowLiveHom_sqArbFrame, map_mul, rowLiveHom_sqEichV]
  exact sqRelWord_rowLiveWit_Vsq

theorem sqRelWord_rowLiveFrame_sigVsq_complete :
    sqRelWord (sigLift j (fun i => rowLiveHom h j (sqArbFrame h (nuSel h j 0 1) j
      (sigArbDress h (sqEichV h (nuSel h j 0 1) j * sqEichV h (nuSel h j 0 1) j)) i))
      1 1 (liftC 7) 1 1) = 1 := by
  rw [rowLiveHom_sqArbFrame, map_mul, rowLiveHom_sqEichV]
  exact sqRelWord_rowLiveWit_Vsq_complete

/-- ⭐⭐ **The odd dressing survives nothing at the row-live point.** -/
theorem sqRelWord_rowLiveFrame_sigV_ne_one_gaTwo {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowLiveMark h j c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowLiveMark h j c)))) :
    sqRelWord (sigLift j (fun i => rowLiveHom h j (sqArbFrame h (nuSel h j 0 1) j
      (sigArbDress h (sqEichV h (nuSel h j 0 1) j)) i)) z₀ w₁ w₂ z₃ z₄) ≠ 1 := by
  rw [rowLiveHom_sqArbFrame, rowLiveHom_sqEichV]
  intro hc
  have hpar := rowLiveWit_sigma_forced_gaTwo (v := rowFourV) (c := c) (by decide) hz₀ hw₁ hw₂
    hz₃ hz₄ l₃ l₄ hc
  rw [show (rowFourV.a : gr3R) = 1 from rfl] at hpar
  exact absurd hpar (by decide)

theorem sqArbFrame_sigma_bit_rowLive {g : (DSq h : Type)} (hg : nuSel h j 0 1 g = 1) :
    selPar ((sqRelWord fun i =>
        rowLiveHom h j (sqArbFrame h (nuSel h j 0 1) j (sigArbDress h g) i)).j)
      = selPar (rowLiveHom h j g).a := by
  rw [rowLiveHom_sqArbFrame g, rowLiveWit]
  exact liveWit_sigma_bit (by decide) (by decide) (by decide) (by decide)
    (rowLiveHom_b_eq_zero hg) sqRelWord_rowLiveWit_triv

/-- ⭐⭐ **THE HEADLINE AT THE UNCLEARED-`v` ROW.** -/
theorem sqArbFrame_sigma_forced_rowLive {g : (DSq h : Type)} (hg : nuSel h j 0 1 g = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowLiveMark h j c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowLiveMark h j c))))
    (hkill : sqRelWord (sigLift j
      (fun i => rowLiveHom h j (sqArbFrame h (nuSel h j 0 1) j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (rowLiveHom h j g).a = 0 := by
  rw [rowLiveHom_sqArbFrame g] at hkill
  exact rowLiveWit_sigma_forced_gaTwo (rowLiveHom_b_eq_zero hg) hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄ hkill

theorem sqArbFrame_sigma_forced_rowLive_lam {g : (DSq h : Type)} (hg : nuSel h j 0 1 g = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : selLamThree 0 1 0 0 1 0 0 1 P Q R z₃)
    (l₄ : selLamThree 0 1 0 0 1 0 0 1 P Q R z₄)
    (hkill : sqRelWord (sigLift j
      (fun i => rowLiveHom h j (sqArbFrame h (nuSel h j 0 1) j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (rowLiveHom h j g).a = 0 := by
  rw [rowLiveHom_sqArbFrame g] at hkill
  exact rowLiveWit_sigma_forced_lam (rowLiveHom_b_eq_zero hg) hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄ hkill

/-- ⭐⭐ **The escape separates the sigma dressings at the uncleared-`v` row with a live
block.** -/
theorem rowLive_escape_separates :
    commP (rowLiveHom h j (sqGen h (sqHandleIdxU j)))
        (rowLiveHom h j (sqGen h (sqHandleIdxV j))) ≠ 1 ∧
    ((∀ i, nuLam h (sigArbDress h
        (sqEichV h (nuSel h j 0 1) j * sqEichV h (nuSel h j 0 1) j) i) = 1) ∧
      ∀ i, nuSel h j 0 1 (sigArbDress h
        (sqEichV h (nuSel h j 0 1) j * sqEichV h (nuSel h j 0 1) j) i) = 1) ∧
    ((∀ i, nuLam h (sigArbDress h (sqEichV h (nuSel h j 0 1) j) i) = 1) ∧
      ∀ i, nuSel h j 0 1 (sigArbDress h (sqEichV h (nuSel h j 0 1) j) i) = 1) ∧
    sqRelWord (fun i => rowLiveHom h j (sqArbFrame h (nuSel h j 0 1) j
      (sigArbDress h (sqEichV h (nuSel h j 0 1) j * sqEichV h (nuSel h j 0 1) j)) i))
      = liftC 2 ∧
    sqRelWord (fun i => rowLiveHom h j (sqArbFrame h (nuSel h j 0 1) j
      (sigArbDress h (sqEichV h (nuSel h j 0 1) j)) i)) = liftC 1 :=
  ⟨rowLiveHom_commP_ne_one,
    ⟨nuLam_sigArbDress_wideVsq, nu_sigArbDress_wideVsq⟩,
    ⟨nuLam_sigArbDress_wideV, nu_sigArbDress_wideV⟩,
    sqRelWord_rowLiveFrame_sigVsq, sqRelWord_rowLiveFrame_sigV⟩

end RowLive

/-! ## 7 The doubly uncleared row `nuSel h j 1 1` with a live handle block -/

section DoublyLive

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐ **The doubly-live `v`-letter**: `GradedFourRow.rowFourV` with its second class-two
coordinate moved from `0` to `4`.  Its `chi_a` stays odd, so the coupling
`GradedFourMirror.chiA_double_forced` is still satisfied with **two** open channels. -/
def dblLiveV : SqU5 gr3R := ⟨1, 0, 0, 0, 0, 4, 0, 0, 0, 0⟩

/-- **The `v`-slot of the doubly-live marking**: the cleared letter displaced on the right. -/
def dblLiveVGen (c : gr3R) : SqU5 gr3R := ⟨1 - 2 * c, 1, 0, 0, 1, 4, 0, 0, -c, c * c⟩

theorem dblLiveVGen_eq (c : gr3R) : dblLiveVGen c = dblLiveV * rowPivotVal c := by
  ext <;> simp only [dblLiveVGen, dblLiveV, rowPivotVal, SqU5.mul_a, SqU5.mul_b, SqU5.mul_c,
    SqU5.mul_d, SqU5.mul_e, SqU5.mul_f, SqU5.mul_g, SqU5.mul_h, SqU5.mul_i, SqU5.mul_j] <;> ring

theorem dblLiveV_eq (c : gr3R) : dblLiveVGen c * (rowPivotVal c)⁻¹ = dblLiveV := by
  rw [dblLiveVGen_eq, mul_inv_cancel_right]

/-- ⭐⭐ **THE LIVE BLOCK AT THE DOUBLY UNCLEARED ROW.** -/
theorem commP_dblLive :
    commP mirFourU dblLiveV = (⟨0, 0, 0, 0, 0, 0, 0, 4, 0, 0⟩ : SqU5 gr3R) := by decide

theorem commP_dblLive_ne_one : commP mirFourU dblLiveV ≠ 1 := by decide

/-- ⭐⭐ **Both displacements together leave the block alone**, at every pivot residue: the left
one is inert and the right one's two effects cancel. -/
theorem commP_dblLiveGen :
    ∀ c : gr3R, commP (mirFourUGen c) (dblLiveVGen c) = commP mirFourU dblLiveV := by decide

theorem sqWord_mul_commP_dblLive :
    sqWord (sigFourMark gr3R) sigFourX liveRowY * commP mirFourU dblLiveV = 1 := by decide

theorem dblLiveV_chiA : selPar dblLiveV.a = 1 := by decide

variable (h j) in
/-- ⭐⭐ **The marking of the doubly-live point.** -/
def dblLiveMark (c : gr3R) : Fin (sqRank h) → SqU5 gr3R :=
  liveWit h j liveRowY (mirFourUGen c) (dblLiveVGen c) 1

variable (h j) in
/-- The doubly-live witness, with **both** cleared letters. -/
def dblLiveWit (v : SqU5 gr3R) : Fin (sqRank h) → SqU5 gr3R :=
  liveWit h j liveRowY mirFourU dblLiveV v

/-- ⭐⭐ **The ten-row solve at the doubly-live point.** -/
theorem sqRelWord_dblLiveMark (c : gr3R) : sqRelWord (dblLiveMark h j c) = 1 := by
  rw [dblLiveMark, sqRelWord_liveWit, mul_one, commP_dblLiveGen c, sqWord_mul_commP_dblLive]

theorem sqRelWord_dblLiveWit_triv : sqRelWord (dblLiveWit h j 1) = 1 := by
  rw [dblLiveWit, sqRelWord_liveWit, mul_one, sqWord_mul_commP_dblLive]

theorem sqRelWord_dblLiveWit (v : SqU5 gr3R) :
    sqRelWord (dblLiveWit h j v)
      = sqWord (sigFourMark gr3R * v) sigFourX liveRowY * commP mirFourU dblLiveV :=
  sqRelWord_liveWit

theorem sqRelWord_dblLiveWit_U : sqRelWord (dblLiveWit h j mirFourU) = liftC 1 := by
  rw [sqRelWord_dblLiveWit]; decide

theorem sqRelWord_dblLiveWit_Usq :
    sqRelWord (dblLiveWit h j (mirFourU * mirFourU)) = liftC 2 := by
  rw [sqRelWord_dblLiveWit]; decide

/-- ⭐⭐ **The second open channel**: the cleared `v`-letter is odd here too, and it leaves the
same odd residue.  The doubly uncleared row couples the two characters rather than closing one,
and a live block does not change that. -/
theorem sqRelWord_dblLiveWit_V : sqRelWord (dblLiveWit h j dblLiveV) = liftC 1 := by
  rw [sqRelWord_dblLiveWit]; decide

theorem sqRelWord_dblLiveWit_Vsq :
    sqRelWord (dblLiveWit h j (dblLiveV * dblLiveV)) = liftC 2 := by
  rw [sqRelWord_dblLiveWit]; decide

theorem sqRelWord_dblLiveWit_Usq_complete :
    sqRelWord (sigLift j (dblLiveWit h j (mirFourU * mirFourU)) 1 1 (liftC 7) 1 1) = 1 := by
  rw [sqRelWord_sigLift SqU5.isGaThree_one SqU5.isGaFour_one (liftC_isGaFour 7)
    SqU5.isGaThree_one SqU5.isGaThree_one, sqRelWord_dblLiveWit_Usq, liftC_mul_liftC]
  refine Eq.trans (congrArg liftC ?_) liftC_zero
  simp only [dblLiveWit, liveWit_one, liveWit_handleU, liveWit_handleV, SqU5.one_h,
    SqU5.one_i, SqU5.one_j, mirFourU, dblLiveV, sigFourX]
  decide

theorem dblLiveWit_class_three_blind :
    (SqU5.toU4L (sqRelWord (dblLiveWit h j 1)) = 1 ∧
      SqU5.toU4R (sqRelWord (dblLiveWit h j 1)) = 1) ∧
    (SqU5.toU4L (sqRelWord (dblLiveWit h j (mirFourU * mirFourU))) = 1 ∧
      SqU5.toU4R (sqRelWord (dblLiveWit h j (mirFourU * mirFourU))) = 1) ∧
    (SqU5.toU4L (sqRelWord (dblLiveWit h j mirFourU)) = 1 ∧
      SqU5.toU4R (sqRelWord (dblLiveWit h j mirFourU)) = 1) ∧
    (SqU5.toU4L (sqRelWord (dblLiveWit h j dblLiveV)) = 1 ∧
      SqU5.toU4R (sqRelWord (dblLiveWit h j dblLiveV)) = 1) := by
  rw [sqRelWord_dblLiveWit_triv, sqRelWord_dblLiveWit_Usq, sqRelWord_dblLiveWit_U,
    sqRelWord_dblLiveWit_V]
  refine ⟨⟨map_one _, map_one _⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

@[simp] theorem dblLiveMark_zero (c : gr3R) : dblLiveMark h j c 0 = sigFourMark gr3R := by
  rw [dblLiveMark, liveWit_zero, mul_one]

@[simp] theorem dblLiveMark_one (c : gr3R) : dblLiveMark h j c 1 = sigFourX := liveWit_one

@[simp] theorem dblLiveMark_two (c : gr3R) : dblLiveMark h j c 2 = liveRowY := liveWit_two

@[simp] theorem dblLiveMark_handleU (c : gr3R) :
    dblLiveMark h j c (sqHandleIdxU j) = mirFourUGen c := liveWit_handleU

@[simp] theorem dblLiveMark_handleV (c : gr3R) :
    dblLiveMark h j c (sqHandleIdxV j) = dblLiveVGen c := liveWit_handleV

theorem dblLiveMark_handleU_ne (c : gr3R) {j' : Fin h} (hne : j' ≠ j) :
    dblLiveMark h j c (sqHandleIdxU j') = 1 := liveWit_handleU_ne hne

theorem dblLiveMark_handleV_ne (c : gr3R) {j' : Fin h} (hne : j' ≠ j) :
    dblLiveMark h j c (sqHandleIdxV j') = 1 := liveWit_handleV_ne hne

variable (h j) in
/-- ⭐⭐ **The doubly-live test hom.** -/
noncomputable def dblLiveHom : ContinuousMonoidHom (DSq h : Type) (SqU5 gr3R) :=
  sqU5Hom gr3R_card h (dblLiveMark h j (gr3Pi sqPivotExp))
    (sqRelWord_dblLiveMark (gr3Pi sqPivotExp))

@[simp] theorem dblLiveHom_gen (i : Fin (sqRank h)) :
    dblLiveHom h j (sqGen h i) = dblLiveMark h j (gr3Pi sqPivotExp) i := sqU5Hom_gen _ _ _ i

@[simp] theorem dblLiveHom_sigma : dblLiveHom h j (dsqSigma h) = sigFourMark gr3R := by
  rw [dsqSigma, dblLiveHom_gen, dblLiveMark_zero]

@[simp] theorem dblLiveHom_x0 : dblLiveHom h j (dsqX0 h) = sigFourX := by
  rw [dsqX0, dblLiveHom_gen, dblLiveMark_one]

@[simp] theorem dblLiveHom_x1 : dblLiveHom h j (dsqX1 h) = liveRowY := by
  rw [dsqX1, dblLiveHom_gen, dblLiveMark_two]

@[simp] theorem dblLiveHom_handleU :
    dblLiveHom h j (sqGen h (sqHandleIdxU j)) = mirFourUGen (gr3Pi sqPivotExp) := by
  rw [dblLiveHom_gen, dblLiveMark_handleU]

@[simp] theorem dblLiveHom_handleV :
    dblLiveHom h j (sqGen h (sqHandleIdxV j)) = dblLiveVGen (gr3Pi sqPivotExp) := by
  rw [dblLiveHom_gen, dblLiveMark_handleV]

theorem dblLiveHom_handle_ne {j' : Fin h} (hne : j' ≠ j) :
    dblLiveHom h j (sqGen h (sqHandleIdxU j')) = 1 ∧
      dblLiveHom h j (sqGen h (sqHandleIdxV j')) = 1 :=
  ⟨by rw [dblLiveHom_gen, dblLiveMark_handleU_ne _ hne],
    by rw [dblLiveHom_gen, dblLiveMark_handleV_ne _ hne]⟩

theorem dblLiveHom_sqPivot :
    dblLiveHom h j (sqPivot h) = rowPivotVal (gr3Pi sqPivotExp) :=
  mirHom_sqPivot dblLiveHom_sigma dblLiveHom_x0

theorem dblLiveHom_commP_ne_one :
    commP (dblLiveHom h j (sqGen h (sqHandleIdxU j)))
      (dblLiveHom h j (sqGen h (sqHandleIdxV j))) ≠ 1 := by
  rw [dblLiveHom_handleU, dblLiveHom_handleV, commP_dblLiveGen]
  exact commP_dblLive_ne_one

theorem dblLiveHom_sqEichU : dblLiveHom h j (sqEichU h (nuSel h j 1 1) j) = mirFourU := by
  rw [sqEichU, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_gr5, nuSel_handleU,
    toAdd_ofAdd, zpowZtwo_one_exp, dblLiveHom_sqPivot, dblLiveHom_handleU, mirFourU_eq]

theorem dblLiveHom_sqEichV : dblLiveHom h j (sqEichV h (nuSel h j 1 1) j) = dblLiveV := by
  rw [sqEichV, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_gr5, nuSel_handleV,
    toAdd_ofAdd, zpowZtwo_one_exp, dblLiveHom_sqPivot, dblLiveHom_handleV, dblLiveV_eq]

theorem dblLiveHom_b (x : (DSq h : Type)) :
    (dblLiveHom h j x).b = gr3Pi (toAdd (nuSel h j 1 1 x)) :=
  mirHom_b (by rw [dblLiveHom_sigma]; rfl) (by rw [dblLiveHom_x0]; rfl)
    (by rw [dblLiveHom_x1]; rfl) (by rw [dblLiveHom_handleU, map_one]; rfl)
    (by rw [dblLiveHom_handleV, map_one]; rfl)
    (fun j' hj' => by rw [(dblLiveHom_handle_ne hj').1, (dblLiveHom_handle_ne hj').2]; exact
      ⟨rfl, rfl⟩) x

theorem dblLiveHom_b_eq_zero {g : (DSq h : Type)} (hg : nuSel h j 1 1 g = 1) :
    (dblLiveHom h j g).b = 0 := by
  rw [dblLiveHom_b, hg, toAdd_one, map_zero]

theorem dblLiveHom_sqArbFrame (g : (DSq h : Type)) :
    (fun i => dblLiveHom h j (sqArbFrame h (nuSel h j 1 1) j (sigArbDress h g) i))
      = dblLiveWit h j (dblLiveHom h j g) := by
  rw [dblLiveWit, liveWit_eq_dress]
  exact liveHom_sqArbFrame (m := dblLiveWit h j 1)
    (by rw [dblLiveHom_sigma, dblLiveWit, liveWit_zero, mul_one])
    (by rw [dblLiveHom_x0, dblLiveWit, liveWit_one])
    (by rw [dblLiveHom_x1, dblLiveWit, liveWit_two])
    (by rw [dblLiveHom_sqEichU, dblLiveWit, liveWit_handleU])
    (by rw [dblLiveHom_sqEichV, dblLiveWit, liveWit_handleV])
    (fun j' hj' => ⟨by rw [(dblLiveHom_handle_ne hj').1, dblLiveWit, liveWit_handleU_ne hj'],
      by rw [(dblLiveHom_handle_ne hj').2, dblLiveWit, liveWit_handleV_ne hj']⟩) g

theorem dblLiveV_mem_liveFrameSub : dblLiveV ∈ liveFrameSub gr3R :=
  ⟨rfl, ⟨2, by show (4 : gr3R) = 2 * 2; decide⟩, 0, by show (0 : gr3R) = 2 * 0; ring⟩

theorem dblLiveVGen_mem_liveFrameSub (c : gr3R) : dblLiveVGen c ∈ liveFrameSub gr3R :=
  ⟨rfl, ⟨2, by show (4 : gr3R) = 2 * 2; decide⟩, 0, by show (0 : gr3R) = 2 * 0; ring⟩

/-- ⭐⭐ **The model-independent soundness at the doubly-live point.** -/
theorem dblLive_gaTwo_even (c : gr3R) {z : SqU5 gr3R}
    (hz : z ∈ rowGaTwoOf (Subgroup.closure (Set.range (dblLiveMark h j c)))) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) :=
  liveWit_gaTwo_even liveRowY_mem_liveFrameSub (mirFourUGen_mem_liveFrameSub c)
    (dblLiveVGen_mem_liveFrameSub c)
    (by rw [mul_one]; exact sigFourMark_mem_liveFrameSub) hz

/-- ⭐⭐ **The sharper wave-55 bound is FALSE at the doubly-live point.** -/
theorem dblLive_not_rowGaTwoSub (c : gr3R) :
    ¬ rowGaTwoOf (Subgroup.closure (Set.range (dblLiveMark h j c))) ≤ rowGaTwoSub gr3R := by
  intro hle
  have hmem : commP (dblLiveMark h j c (sqHandleIdxU j)) (dblLiveMark h j c (sqHandleIdxV j))
      ∈ rowGaTwoOf (Subgroup.closure (Set.range (dblLiveMark h j c))) :=
    Subgroup.subset_closure ⟨_, Subgroup.subset_closure ⟨_, rfl⟩, _,
      Subgroup.subset_closure ⟨_, rfl⟩, rfl⟩
  obtain ⟨-, -, -, -, -, -, hh, -⟩ := hle hmem
  rw [dblLiveMark_handleU, dblLiveMark_handleV, commP_dblLiveGen, commP_dblLive] at hh
  exact absurd hh (by decide)

/-- The committed achievable lattice is even at the doubly-live point, at wave 56's own
parameters `(1, 1, 0, 0, 0, 0, 1, 1)`. -/
theorem dblLiveWit_lamThree_even {P Q R : gr3R} {z : SqU5 gr3R}
    (hz : selLamThree 1 1 0 0 0 0 1 1 P Q R z) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) :=
  dblFourWit_lamThree_even hz

theorem dblLiveWit_commP_data :
    commP (sigFourMark gr3R) liveRowY = (⟨0, 0, 0, 0, 0, 0, 0, 0, 4, 0⟩ : SqU5 gr3R) ∧
      commP liveRowY mirFourU = (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 6⟩ : SqU5 gr3R) ∧
      commP liveRowY dblLiveV = (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 6⟩ : SqU5 gr3R) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⭐⭐ **The sigma forcing at the doubly-live point.** -/
theorem dblLiveWit_sigma_forced {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (h₃ : (∃ a : gr3R, z₃.h = 2 * a) ∧ (∃ b : gr3R, z₃.i = 2 * b))
    (h₄ : (∃ a : gr3R, z₄.h = 2 * a) ∧ (∃ b : gr3R, z₄.i = 2 * b))
    (hkill : sqRelWord (sigLift j (dblLiveWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  liveWit_sigma_forced (by decide) (by decide) (by decide) (by decide)
    sqRelWord_dblLiveWit_triv hvb hz₀ hw₁ hw₂ hz₃ hz₄ h₃ h₄ hkill

theorem dblLiveWit_sigma_forced_lam {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hvb : v.b = 0) (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : selLamThree 1 1 0 0 0 0 1 1 P Q R z₃)
    (l₄ : selLamThree 1 1 0 0 0 0 1 1 P Q R z₄)
    (hkill : sqRelWord (sigLift j (dblLiveWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  dblLiveWit_sigma_forced hvb hz₀ hw₁ hw₂ hz₃ hz₄ (dblLiveWit_lamThree_even l₃)
    (dblLiveWit_lamThree_even l₄) hkill

theorem dblLiveWit_sigma_forced_gaTwo {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hvb : v.b = 0) (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (dblLiveMark h j c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (dblLiveMark h j c))))
    (hkill : sqRelWord (sigLift j (dblLiveWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  dblLiveWit_sigma_forced hvb hz₀ hw₁ hw₂ hz₃ hz₄ (dblLive_gaTwo_even c l₃)
    (dblLive_gaTwo_even c l₄) hkill

/-- ⭐⭐ **The forcing is not vacuous at the doubly-live point, on TWO channels.** -/
theorem dblLive_forcing_nonvacuous :
    (nuLam h (sqEichU h (nuSel h j 1 1) j) = 1 ∧
        nuSel h j 1 1 (sqEichU h (nuSel h j 1 1) j) = 1 ∧
        selPar (dblLiveHom h j (sqEichU h (nuSel h j 1 1) j)).a = 1) ∧
      (nuLam h (sqEichV h (nuSel h j 1 1) j) = 1 ∧
        nuSel h j 1 1 (sqEichV h (nuSel h j 1 1) j) = 1 ∧
        selPar (dblLiveHom h j (sqEichV h (nuSel h j 1 1) j)).a = 1) :=
  ⟨⟨nuLam_dblEichU, nu_dblEichU, by rw [dblLiveHom_sqEichU]; exact mirFourU_chiA⟩,
    ⟨nuLam_dblEichV, nu_dblEichV, by rw [dblLiveHom_sqEichV]; exact dblLiveV_chiA⟩⟩

theorem sqRelWord_dblLiveFrame_sigTriv :
    sqRelWord (fun i =>
      dblLiveHom h j (sqArbFrame h (nuSel h j 1 1) j (sigArbDress h 1) i)) = 1 := by
  rw [dblLiveHom_sqArbFrame, map_one]
  exact sqRelWord_dblLiveWit_triv

theorem sqRelWord_dblLiveFrame_sigU :
    sqRelWord (fun i => dblLiveHom h j (sqArbFrame h (nuSel h j 1 1) j
      (sigArbDress h (sqEichU h (nuSel h j 1 1) j)) i)) = liftC 1 := by
  rw [dblLiveHom_sqArbFrame, dblLiveHom_sqEichU]
  exact sqRelWord_dblLiveWit_U

theorem sqRelWord_dblLiveFrame_sigUsq :
    sqRelWord (fun i => dblLiveHom h j (sqArbFrame h (nuSel h j 1 1) j
      (sigArbDress h (sqEichU h (nuSel h j 1 1) j * sqEichU h (nuSel h j 1 1) j)) i))
      = liftC 2 := by
  rw [dblLiveHom_sqArbFrame, map_mul, dblLiveHom_sqEichU]
  exact sqRelWord_dblLiveWit_Usq

theorem sqRelWord_dblLiveFrame_sigV :
    sqRelWord (fun i => dblLiveHom h j (sqArbFrame h (nuSel h j 1 1) j
      (sigArbDress h (sqEichV h (nuSel h j 1 1) j)) i)) = liftC 1 := by
  rw [dblLiveHom_sqArbFrame, dblLiveHom_sqEichV]
  exact sqRelWord_dblLiveWit_V

theorem sqRelWord_dblLiveFrame_sigUsq_complete :
    sqRelWord (sigLift j (fun i => dblLiveHom h j (sqArbFrame h (nuSel h j 1 1) j
      (sigArbDress h (sqEichU h (nuSel h j 1 1) j * sqEichU h (nuSel h j 1 1) j)) i))
      1 1 (liftC 7) 1 1) = 1 := by
  rw [dblLiveHom_sqArbFrame, map_mul, dblLiveHom_sqEichU]
  exact sqRelWord_dblLiveWit_Usq_complete

/-- ⭐⭐ **Neither odd dressing survives at the doubly-live point.** -/
theorem sqRelWord_dblLiveFrame_sigU_ne_one_gaTwo {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (dblLiveMark h j c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (dblLiveMark h j c)))) :
    sqRelWord (sigLift j (fun i => dblLiveHom h j (sqArbFrame h (nuSel h j 1 1) j
      (sigArbDress h (sqEichU h (nuSel h j 1 1) j)) i)) z₀ w₁ w₂ z₃ z₄) ≠ 1 := by
  rw [dblLiveHom_sqArbFrame, dblLiveHom_sqEichU]
  intro hc
  have hpar := dblLiveWit_sigma_forced_gaTwo (v := mirFourU) (c := c) (by decide) hz₀ hw₁ hw₂
    hz₃ hz₄ l₃ l₄ hc
  rw [show (mirFourU.a : gr3R) = 1 from rfl] at hpar
  exact absurd hpar (by decide)

theorem sqRelWord_dblLiveFrame_sigV_ne_one_gaTwo {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (dblLiveMark h j c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (dblLiveMark h j c)))) :
    sqRelWord (sigLift j (fun i => dblLiveHom h j (sqArbFrame h (nuSel h j 1 1) j
      (sigArbDress h (sqEichV h (nuSel h j 1 1) j)) i)) z₀ w₁ w₂ z₃ z₄) ≠ 1 := by
  rw [dblLiveHom_sqArbFrame, dblLiveHom_sqEichV]
  intro hc
  have hpar := dblLiveWit_sigma_forced_gaTwo (v := dblLiveV) (c := c) (by decide) hz₀ hw₁ hw₂
    hz₃ hz₄ l₃ l₄ hc
  rw [show (dblLiveV.a : gr3R) = 1 from rfl] at hpar
  exact absurd hpar (by decide)

theorem sqArbFrame_sigma_bit_dblLive {g : (DSq h : Type)} (hg : nuSel h j 1 1 g = 1) :
    selPar ((sqRelWord fun i =>
        dblLiveHom h j (sqArbFrame h (nuSel h j 1 1) j (sigArbDress h g) i)).j)
      = selPar (dblLiveHom h j g).a := by
  rw [dblLiveHom_sqArbFrame g, dblLiveWit]
  exact liveWit_sigma_bit (by decide) (by decide) (by decide) (by decide)
    (dblLiveHom_b_eq_zero hg) sqRelWord_dblLiveWit_triv

/-- ⭐⭐ **THE HEADLINE AT THE DOUBLY UNCLEARED ROW.** -/
theorem sqArbFrame_sigma_forced_dblLive {g : (DSq h : Type)} (hg : nuSel h j 1 1 g = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (dblLiveMark h j c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (dblLiveMark h j c))))
    (hkill : sqRelWord (sigLift j
      (fun i => dblLiveHom h j (sqArbFrame h (nuSel h j 1 1) j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (dblLiveHom h j g).a = 0 := by
  rw [dblLiveHom_sqArbFrame g] at hkill
  exact dblLiveWit_sigma_forced_gaTwo (dblLiveHom_b_eq_zero hg) hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄ hkill

theorem sqArbFrame_sigma_forced_dblLive_lam {g : (DSq h : Type)} (hg : nuSel h j 1 1 g = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : selLamThree 1 1 0 0 0 0 1 1 P Q R z₃)
    (l₄ : selLamThree 1 1 0 0 0 0 1 1 P Q R z₄)
    (hkill : sqRelWord (sigLift j
      (fun i => dblLiveHom h j (sqArbFrame h (nuSel h j 1 1) j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (dblLiveHom h j g).a = 0 := by
  rw [dblLiveHom_sqArbFrame g] at hkill
  exact dblLiveWit_sigma_forced_lam (dblLiveHom_b_eq_zero hg) hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄ hkill

/-- ⭐⭐ **The escape separates the sigma dressings at the doubly uncleared row with a live
block**, on the `u`-channel. -/
theorem dblLive_escape_separates :
    commP (dblLiveHom h j (sqGen h (sqHandleIdxU j)))
        (dblLiveHom h j (sqGen h (sqHandleIdxV j))) ≠ 1 ∧
    ((∀ i, nuLam h (sigArbDress h
        (sqEichU h (nuSel h j 1 1) j * sqEichU h (nuSel h j 1 1) j) i) = 1) ∧
      ∀ i, nuSel h j 1 1 (sigArbDress h
        (sqEichU h (nuSel h j 1 1) j * sqEichU h (nuSel h j 1 1) j) i) = 1) ∧
    ((∀ i, nuLam h (sigArbDress h (sqEichU h (nuSel h j 1 1) j) i) = 1) ∧
      ∀ i, nuSel h j 1 1 (sigArbDress h (sqEichU h (nuSel h j 1 1) j) i) = 1) ∧
    sqRelWord (fun i => dblLiveHom h j (sqArbFrame h (nuSel h j 1 1) j
      (sigArbDress h (sqEichU h (nuSel h j 1 1) j * sqEichU h (nuSel h j 1 1) j)) i))
      = liftC 2 ∧
    sqRelWord (fun i => dblLiveHom h j (sqArbFrame h (nuSel h j 1 1) j
      (sigArbDress h (sqEichU h (nuSel h j 1 1) j)) i)) = liftC 1 :=
  ⟨dblLiveHom_commP_ne_one,
    ⟨nuLam_sigArbDress_dblUsq, nu_sigArbDress_dblUsq⟩,
    ⟨nuLam_sigArbDress_dblU, nu_sigArbDress_dblU⟩,
    sqRelWord_dblLiveFrame_sigUsq, sqRelWord_dblLiveFrame_sigU⟩

end DoublyLive

/-! ## 8 Two live handles -/

section TwoTuple

variable {G : Type*} [Group G] {h : ℕ} {j₁ j₂ : Fin h} {S X Y U₁ V₁ U₂ V₂ : G}

/-- **A handle block in which exactly two commutators survive IS their ordered product.**  The
two-handle transposition of `EichRefutation.handleWord_eq_single`. -/
theorem handleWord_eq_pair (u v : Fin h → G) (hlt : (j₁ : ℕ) < (j₂ : ℕ))
    (hne : ∀ i : Fin h, i ≠ j₁ → i ≠ j₂ → commP (u i) (v i) = 1) :
    handleWord u v = commP (u j₁) (v j₁) * commP (u j₂) (v j₂) := by
  classical
  have hj₁₂ : j₁ ≠ j₂ := fun hc => by rw [hc] at hlt; omega
  set v' : Fin h → G := fun i => if i = j₂ then 1 else v i with hv'def
  have hv'ne : ∀ i : Fin h, i ≠ j₂ → v' i = v i := fun i hi => if_neg hi
  have hv'eq : v' j₂ = 1 := if_pos rfl
  have hsingle : handleWord u v' = commP (u j₁) (v j₁) := by
    rw [handleWord_eq_single u v' j₁ (fun i hi => by
      by_cases h2 : i = j₂
      · rw [h2, hv'eq]; simp [commP]
      · rw [hv'ne i h2]; exact hne i hi h2), hv'ne j₁ hj₁₂]
  have hsuf' : handleSuffix u v' (j₂ : ℕ) = 1 := by
    rw [handleSuffix, List.prod_eq_one]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hge := mem_drop_finRange hi
    by_cases h2 : i = j₂
    · rw [h2, hv'eq]; simp [commP]
    · refine (hv'ne i h2) ▸ hne i (fun hc => ?_) h2
      rw [hc] at hge
      omega
  have hpre' : handlePrefix u v' (j₂ : ℕ) = commP (u j₁) (v j₁) := by
    have hsplit := handlePrefix_mul_handleSuffix u v' (j₂ : ℕ)
    rw [hsuf', mul_one, hsingle] at hsplit
    exact hsplit
  have hpre : handlePrefix u v (j₂ : ℕ) = commP (u j₁) (v j₁) := by
    rw [handlePrefix_congr (u := u) (v := v) (u' := u) (v' := v') (j₂ : ℕ) (fun i hi => by
      rw [hv'ne i (fun hc => by rw [hc] at hi; omega)]), hpre']
  have hsuf : handleSuffix u v ((j₂ : ℕ) + 1) = 1 := by
    rw [handleSuffix, List.prod_eq_one]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hge := mem_drop_finRange hi
    exact hne i (fun hc => by rw [hc] at hge; omega) (fun hc => by rw [hc] at hge; omega)
  rw [handleWord_split u v j₂, hpre, hsuf, mul_one]

variable (G h j₁ j₂) in
/-- **The two-live-handle tuple**: the three core slots, the `j₁`-th handle pair carrying
`(U₁, V₁)`, the `j₂`-th carrying `(U₂, V₂)`, every other handle letter trivial. -/
def twoTuple (S X Y U₁ V₁ U₂ V₂ : G) : Fin (sqRank h) → G :=
  fun i =>
    if (i : ℕ) = 0 then S else
    if (i : ℕ) = 1 then X else
    if (i : ℕ) = 2 then Y else
    if (i : ℕ) = (sqHandleIdxU j₁ : ℕ) then U₁ else
    if (i : ℕ) = (sqHandleIdxV j₁ : ℕ) then V₁ else
    if (i : ℕ) = (sqHandleIdxU j₂ : ℕ) then U₂ else
    if (i : ℕ) = (sqHandleIdxV j₂ : ℕ) then V₂ else 1

@[simp] theorem twoTuple_zero : twoTuple G h j₁ j₂ S X Y U₁ V₁ U₂ V₂ 0 = S := by
  simp only [twoTuple, sqVal_zero]; norm_num

@[simp] theorem twoTuple_one : twoTuple G h j₁ j₂ S X Y U₁ V₁ U₂ V₂ 1 = X := by
  simp only [twoTuple, sqVal_one, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega)]
  norm_num

@[simp] theorem twoTuple_two : twoTuple G h j₁ j₂ S X Y U₁ V₁ U₂ V₂ 2 = Y := by
  simp only [twoTuple, sqVal_two, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega)]
  norm_num

@[simp] theorem twoTuple_handleU_one :
    twoTuple G h j₁ j₂ S X Y U₁ V₁ U₂ V₂ (sqHandleIdxU j₁) = U₁ := by
  simp only [twoTuple, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  norm_num

@[simp] theorem twoTuple_handleV_one :
    twoTuple G h j₁ j₂ S X Y U₁ V₁ U₂ V₂ (sqHandleIdxV j₁) = V₁ := by
  simp only [twoTuple, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  norm_num

theorem twoTuple_handleU_two (hne : (j₁ : ℕ) ≠ (j₂ : ℕ)) :
    twoTuple G h j₁ j₂ S X Y U₁ V₁ U₂ V₂ (sqHandleIdxU j₂) = U₂ := by
  simp only [twoTuple, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]
  norm_num

theorem twoTuple_handleV_two (hne : (j₁ : ℕ) ≠ (j₂ : ℕ)) :
    twoTuple G h j₁ j₂ S X Y U₁ V₁ U₂ V₂ (sqHandleIdxV j₂) = V₂ := by
  simp only [twoTuple, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]
  norm_num

theorem twoTuple_handleU_ne {j' : Fin h} (h1 : j' ≠ j₁) (h2 : j' ≠ j₂) :
    twoTuple G h j₁ j₂ S X Y U₁ V₁ U₂ V₂ (sqHandleIdxU j') = 1 := by
  have hv1 : (j' : ℕ) ≠ (j₁ : ℕ) := fun hc => h1 (Fin.val_injective hc)
  have hv2 : (j' : ℕ) ≠ (j₂ : ℕ) := fun hc => h2 (Fin.val_injective hc)
  have e0 := sqHandleIdxU_val j'
  have e1 := sqHandleIdxU_val j₁
  have e2 := sqHandleIdxV_val j₁
  have e3 := sqHandleIdxU_val j₂
  have e4 := sqHandleIdxV_val j₂
  simp only [twoTuple]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem twoTuple_handleV_ne {j' : Fin h} (h1 : j' ≠ j₁) (h2 : j' ≠ j₂) :
    twoTuple G h j₁ j₂ S X Y U₁ V₁ U₂ V₂ (sqHandleIdxV j') = 1 := by
  have hv1 : (j' : ℕ) ≠ (j₁ : ℕ) := fun hc => h1 (Fin.val_injective hc)
  have hv2 : (j' : ℕ) ≠ (j₂ : ℕ) := fun hc => h2 (Fin.val_injective hc)
  have e0 := sqHandleIdxV_val j'
  have e1 := sqHandleIdxU_val j₁
  have e2 := sqHandleIdxV_val j₁
  have e3 := sqHandleIdxU_val j₂
  have e4 := sqHandleIdxV_val j₂
  simp only [twoTuple]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- ⭐⭐ **The relator of a two-live-handle tuple**, at every handle count: the core word times
the **ordered product** of the two blocks. -/
theorem sqRelWord_twoTuple (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    sqRelWord (twoTuple G h j₁ j₂ S X Y U₁ V₁ U₂ V₂)
      = sqWord S X Y * (commP U₁ V₁ * commP U₂ V₂) := by
  have hj₁₂ : j₁ ≠ j₂ := fun hc => by rw [hc] at hlt; omega
  have hne : (j₁ : ℕ) ≠ (j₂ : ℕ) := by omega
  rw [sqRelWord, twoTuple_zero, twoTuple_one, twoTuple_two,
    handleWord_eq_pair (j₁ := j₁) (j₂ := j₂) _ _ hlt (fun i hi1 hi2 => by
      rw [twoTuple_handleU_ne hi1 hi2, twoTuple_handleV_ne hi1 hi2]
      simp [commP]),
    twoTuple_handleU_one, twoTuple_handleV_one, twoTuple_handleU_two hne,
    twoTuple_handleV_two hne]

/-- ⭐⭐⭐ **THE TWO-LIVE-HANDLE POINT, in one line.**  Put a pair of letters at one handle and
the **same pair swapped** at another: `⁅U, V⁆ · ⁅V, U⁆ = 1` is a group identity, so the whole
handle block collapses and the relator is the bare core word - for **arbitrary** letters, in
**any** group, at **every** handle count.  With the committed core slots, whose core word is
trivial, this is a relator-killing marking with **two live handle blocks**, and wave 57's
"with the committed core slots a live block is forced impossible" is thereby sharp: it is a
statement about *one* handle. -/
theorem sqRelWord_twoTuple_swap (U V : G) (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    sqRelWord (twoTuple G h j₁ j₂ S X Y U V V U) = sqWord S X Y := by
  rw [sqRelWord_twoTuple hlt, commP_swap, mul_one]

end TwoTuple

section NoCoupling

variable {R : Type} [CommRing R] {U₁ V₁ U₂ V₂ : SqU5 R}

/-- The third class-two coordinate of a block vanishes as soon as its two letters have
vanishing `c`-column - the first of `GradedFourCleared.liveFrameSub`'s three invariants. -/
theorem commP_g_eq_zero (h₁ : U₂.c = 0) (h₂ : V₂.c = 0) : (commP U₂ V₂).g = 0 := by
  rw [SqU5.commP_g, h₁, h₂, zero_mul, mul_zero, sub_zero]

/-- The first class-two coordinate of a block vanishes as soon as its two letters are
`ν'`-trivial. -/
theorem commP_e_eq_zero (h₁ : U₁.b = 0) (h₂ : V₁.b = 0) : (commP U₁ V₁).e = 0 := by
  rw [SqU5.commP_e, h₁, h₂, zero_mul, mul_zero, sub_zero]

/-- ⭐⭐ **NO CROSS-HANDLE COUPLING inside the campaign's invariants.**  `GradedFour` names the
class-four coupling of distinct handles - `(x·y).j` picks up `x.e·y.g` - as the one structural
novelty of class four that `h = 1` cannot see.  It is **identically zero** at every marking the
campaign allows: the second pair's letters have vanishing `c`-column (a frame invariant), so
`⁅U₂, V₂⁆.g = 0`, and the two blocks simply add.  Two live handles therefore cannot interfere
at class four; the relator sees only the **sum** of the blocks. -/
theorem commP_pair_no_coupling (h₁ : U₂.c = 0) (h₂ : V₂.c = 0) :
    (commP U₁ V₁ * commP U₂ V₂).j = (commP U₁ V₁).j + (commP U₂ V₂).j := by
  rw [SqU5.mul_j, SqU5.commP_a, SqU5.commP_d, commP_g_eq_zero h₁ h₂, zero_mul, mul_zero,
    mul_zero, add_zero, add_zero, add_zero]

/-- …and the `ν'`-trivial form of the same statement, on the other factor. -/
theorem commP_pair_no_coupling' (h₁ : U₁.b = 0) (h₂ : V₁.b = 0) :
    (commP U₁ V₁ * commP U₂ V₂).j = (commP U₁ V₁).j + (commP U₂ V₂).j := by
  rw [SqU5.mul_j, SqU5.commP_a, SqU5.commP_d, commP_e_eq_zero h₁ h₂, zero_mul, zero_mul,
    mul_zero, add_zero, add_zero, add_zero]

/-- **Realising the coupling needs a nonzero `c`-column**, hence a marking outside
`GradedFourCleared.liveFrameSub` - where `commP_mem_liveGaTwoSub` fails and the class-four
increment is no longer even.  So the coupling is not merely unrealised: it is unavailable to
any point the forcing can be run at.

CORRECTED BY W59-INVARIANT AND W60-MIGRATE: the last sentence is FALSE.  The implication
proved here stands, and so does the failure of `commP_mem_liveGaTwoSub` outside the frame
invariant; what does not follow is the conclusion about the forcing.  The increment is even
whenever the handle PAIRING is even, not only when `commP_mem_liveGaTwoSub` applies, so a
nonzero `c`-column does not put a point beyond the forcing.
`GradedFrameNecessity.orthV` has `c = 1`, sits outside `liveFrameSub`, and the forcing HOLDS at
it (`orth_sigmaForces`) with the coupling still vanishing (`commP_orth_g`); a nonzero
`c`-column is therefore necessary for the coupling and not sufficient, and it is available to a
point the forcing runs at.  See `SqCore/GradedFrameNecessity.lean` §5 and
`SqCore/GradedFourSharp.lean`. -/
theorem commP_coupling_ne_zero_imp (hne : (commP U₂ V₂).g ≠ 0) : U₂.c ≠ 0 ∨ V₂.c ≠ 0 := by
  by_contra hc
  rw [not_or, not_not, not_not] at hc
  exact hne (commP_g_eq_zero hc.1 hc.2)

end NoCoupling

/-! ## 9 The two-live-handle point at the committed core slots -/

section TwoLivePoint

variable {h : ℕ} {j₁ j₂ : Fin h}

variable (h j₁ j₂) in
/-- ⭐⭐⭐ **The two-live-handle marking**: the **committed** sigma-, `x₀`- and `x₁`-slots, the
pair `(U, V)` at handle `j₁` and the swapped pair `(V, U)` at handle `j₂`. -/
def twoLiveMark (U V : SqU5 gr3R) : Fin (sqRank h) → SqU5 gr3R :=
  twoTuple (SqU5 gr3R) h j₁ j₂ (sigFourMark gr3R) sigFourX sigFourY U V V U

variable (h j₁ j₂) in
/-- The two-live witness, with the sigma slot dressed by `v`. -/
def twoLiveWit (U V v : SqU5 gr3R) : Fin (sqRank h) → SqU5 gr3R :=
  twoTuple (SqU5 gr3R) h j₁ j₂ (sigFourMark gr3R * v) sigFourX sigFourY U V V U

variable {U V v : SqU5 gr3R}

theorem twoLiveWit_one : twoLiveWit h j₁ j₂ U V 1 = twoLiveMark h j₁ j₂ U V := by
  rw [twoLiveWit, twoLiveMark, mul_one]

theorem twoLiveWit_eq_dress : twoLiveWit h j₁ j₂ U V v
    = sigFourDress (twoLiveWit h j₁ j₂ U V 1) v := by
  funext i
  by_cases h0 : (i : ℕ) = 0
  · have hi : i = 0 := Fin.val_injective (by rw [h0, sqVal_zero])
    subst hi
    rw [sigFourDress_zero, twoLiveWit, twoTuple_zero, twoLiveWit, twoTuple_zero, mul_one]
  · rw [sigFourDress_ne h0]
    simp only [twoLiveWit, twoTuple, if_neg h0]

/-- ⭐⭐⭐ **THE TEN-ROW SOLVE AT TWO LIVE HANDLES**, at every handle count, every ordered pair
of handles and **arbitrary** letters. -/
theorem sqRelWord_twoLiveMark (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    sqRelWord (twoLiveMark h j₁ j₂ U V) = 1 := by
  rw [twoLiveMark, sqRelWord_twoTuple_swap _ _ hlt]
  decide

theorem sqRelWord_twoLiveWit (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    sqRelWord (twoLiveWit h j₁ j₂ U V v) = sqWord (sigFourMark gr3R * v) sigFourX sigFourY := by
  rw [twoLiveWit, sqRelWord_twoTuple_swap _ _ hlt]

/-- ⭐⭐ **The first block is live whenever the letters do not commute.** -/
theorem commP_twoLive_ne_one (hUV : commP U V ≠ 1) :
    commP (twoLiveMark h j₁ j₂ U V (sqHandleIdxU j₁))
      (twoLiveMark h j₁ j₂ U V (sqHandleIdxV j₁)) ≠ 1 := by
  rw [twoLiveMark, twoTuple_handleU_one, twoTuple_handleV_one]
  exact hUV

/-- ⭐⭐ …and so is the second, being its inverse. -/
theorem commP_twoLive_ne_one' (hne : (j₁ : ℕ) ≠ (j₂ : ℕ)) (hUV : commP U V ≠ 1) :
    commP (twoLiveMark h j₁ j₂ U V (sqHandleIdxU j₂))
      (twoLiveMark h j₁ j₂ U V (sqHandleIdxV j₂)) ≠ 1 := by
  rw [twoLiveMark, twoTuple_handleU_two hne, twoTuple_handleV_two hne]
  intro hc
  have hsw := commP_swap U V
  rw [hc, mul_one] at hsw
  exact hUV hsw

/-- The concrete letters of the two-live point: wave 57's live pair. -/
def twoLiveU : SqU5 gr3R := ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- …and its partner, whose commutator with it has order four. -/
def twoLiveV : SqU5 gr3R := ⟨2, 0, 0, 0, 0, 2, 0, 0, 0, 0⟩

theorem twoLiveU_eq : twoLiveU = sigFourU := rfl

theorem twoLiveV_eq : twoLiveV = liveFourV := rfl

/-- ⭐⭐⭐ **The two blocks of the concrete point**: inverse class-three elements of order four,
neither trivial. -/
theorem commP_twoLive :
    commP twoLiveU twoLiveV = (⟨0, 0, 0, 0, 0, 0, 0, 2, 0, 0⟩ : SqU5 gr3R) ∧
      commP twoLiveV twoLiveU = (⟨0, 0, 0, 0, 0, 0, 0, 6, 0, 0⟩ : SqU5 gr3R) := by
  refine ⟨?_, ?_⟩ <;> decide

theorem commP_twoLive_ne : commP twoLiveU twoLiveV ≠ 1 ∧ commP twoLiveV twoLiveU ≠ 1 := by
  refine ⟨?_, ?_⟩ <;> decide

theorem twoLiveU_chiA : selPar twoLiveU.a = 1 := by decide

/-- ⭐⭐ **The three verdicts at the two-live point are the committed ones.** -/
theorem sqRelWord_twoLiveWit_triv (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    sqRelWord (twoLiveWit h j₁ j₂ twoLiveU twoLiveV 1) = 1 := by
  rw [twoLiveWit_one]; exact sqRelWord_twoLiveMark hlt

theorem sqRelWord_twoLiveWit_U (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    sqRelWord (twoLiveWit h j₁ j₂ twoLiveU twoLiveV twoLiveU) = liftC 1 := by
  rw [sqRelWord_twoLiveWit hlt]; decide

theorem sqRelWord_twoLiveWit_Usq (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    sqRelWord (twoLiveWit h j₁ j₂ twoLiveU twoLiveV (twoLiveU * twoLiveU)) = liftC 2 := by
  rw [sqRelWord_twoLiveWit hlt]; decide

theorem sqRelWord_twoLiveWit_Usq_complete (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    sqRelWord (sigLift j₁ (twoLiveWit h j₁ j₂ twoLiveU twoLiveV (twoLiveU * twoLiveU))
      1 1 (liftC 7) 1 1) = 1 := by
  rw [sqRelWord_sigLift SqU5.isGaThree_one SqU5.isGaFour_one (liftC_isGaFour 7)
    SqU5.isGaThree_one SqU5.isGaThree_one, sqRelWord_twoLiveWit_Usq hlt, liftC_mul_liftC]
  refine Eq.trans (congrArg liftC ?_) liftC_zero
  simp only [twoLiveWit, twoTuple_one, twoTuple_handleU_one, twoTuple_handleV_one,
    SqU5.one_h, SqU5.one_i, SqU5.one_j, twoLiveU, twoLiveV, sigFourX]
  decide

theorem twoLiveWit_class_three_blind (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    (SqU5.toU4L (sqRelWord (twoLiveWit h j₁ j₂ twoLiveU twoLiveV 1)) = 1 ∧
      SqU5.toU4R (sqRelWord (twoLiveWit h j₁ j₂ twoLiveU twoLiveV 1)) = 1) ∧
    (SqU5.toU4L (sqRelWord (twoLiveWit h j₁ j₂ twoLiveU twoLiveV
        (twoLiveU * twoLiveU))) = 1 ∧
      SqU5.toU4R (sqRelWord (twoLiveWit h j₁ j₂ twoLiveU twoLiveV
        (twoLiveU * twoLiveU))) = 1) ∧
    (SqU5.toU4L (sqRelWord (twoLiveWit h j₁ j₂ twoLiveU twoLiveV twoLiveU)) = 1 ∧
      SqU5.toU4R (sqRelWord (twoLiveWit h j₁ j₂ twoLiveU twoLiveV twoLiveU)) = 1) := by
  rw [sqRelWord_twoLiveWit_triv hlt, sqRelWord_twoLiveWit_Usq hlt, sqRelWord_twoLiveWit_U hlt]
  refine ⟨⟨map_one _, map_one _⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

/-! ### The two-live point as a continuous homomorphism -/

@[simp] theorem twoLiveMark_zero : twoLiveMark h j₁ j₂ U V 0 = sigFourMark gr3R := twoTuple_zero

@[simp] theorem twoLiveMark_one : twoLiveMark h j₁ j₂ U V 1 = sigFourX := twoTuple_one

@[simp] theorem twoLiveMark_two : twoLiveMark h j₁ j₂ U V 2 = sigFourY := twoTuple_two

@[simp] theorem twoLiveMark_handleU_one :
    twoLiveMark h j₁ j₂ U V (sqHandleIdxU j₁) = U := twoTuple_handleU_one

@[simp] theorem twoLiveMark_handleV_one :
    twoLiveMark h j₁ j₂ U V (sqHandleIdxV j₁) = V := twoTuple_handleV_one

theorem twoLiveMark_handleU_two (hne : (j₁ : ℕ) ≠ (j₂ : ℕ)) :
    twoLiveMark h j₁ j₂ U V (sqHandleIdxU j₂) = V := twoTuple_handleU_two hne

theorem twoLiveMark_handleV_two (hne : (j₁ : ℕ) ≠ (j₂ : ℕ)) :
    twoLiveMark h j₁ j₂ U V (sqHandleIdxV j₂) = U := twoTuple_handleV_two hne

theorem twoLiveMark_handleU_ne {j' : Fin h} (h1 : j' ≠ j₁) (h2 : j' ≠ j₂) :
    twoLiveMark h j₁ j₂ U V (sqHandleIdxU j') = 1 := twoTuple_handleU_ne h1 h2

theorem twoLiveMark_handleV_ne {j' : Fin h} (h1 : j' ≠ j₁) (h2 : j' ≠ j₂) :
    twoLiveMark h j₁ j₂ U V (sqHandleIdxV j') = 1 := twoTuple_handleV_ne h1 h2

variable (h j₁ j₂) in
/-- ⭐⭐⭐ **The two-live test hom**: an honest continuous homomorphism `D_sq h → U₅(ℤ/8)`
with **two** nontrivial handle commutators in its image. -/
noncomputable def twoLiveHom (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    ContinuousMonoidHom (DSq h : Type) (SqU5 gr3R) :=
  sqU5Hom gr3R_card h (twoLiveMark h j₁ j₂ twoLiveU twoLiveV) (sqRelWord_twoLiveMark hlt)

variable {hlt : (j₁ : ℕ) < (j₂ : ℕ)}

@[simp] theorem twoLiveHom_gen (i : Fin (sqRank h)) :
    twoLiveHom h j₁ j₂ hlt (sqGen h i) = twoLiveMark h j₁ j₂ twoLiveU twoLiveV i :=
  sqU5Hom_gen _ _ _ i

@[simp] theorem twoLiveHom_sigma :
    twoLiveHom h j₁ j₂ hlt (dsqSigma h) = sigFourMark gr3R := by
  rw [dsqSigma, twoLiveHom_gen, twoLiveMark_zero]

@[simp] theorem twoLiveHom_x0 : twoLiveHom h j₁ j₂ hlt (dsqX0 h) = sigFourX := by
  rw [dsqX0, twoLiveHom_gen, twoLiveMark_one]

@[simp] theorem twoLiveHom_x1 : twoLiveHom h j₁ j₂ hlt (dsqX1 h) = sigFourY := by
  rw [dsqX1, twoLiveHom_gen, twoLiveMark_two]

theorem twoLiveHom_sqPivot :
    twoLiveHom h j₁ j₂ hlt (sqPivot h) = rowPivotVal (gr3Pi sqPivotExp) :=
  mirHom_sqPivot twoLiveHom_sigma twoLiveHom_x0

/-- ⭐⭐⭐ **BOTH handle commutators are live in the image.** -/
theorem twoLiveHom_commP_ne_one :
    commP (twoLiveHom h j₁ j₂ hlt (sqGen h (sqHandleIdxU j₁)))
        (twoLiveHom h j₁ j₂ hlt (sqGen h (sqHandleIdxV j₁))) ≠ 1 ∧
      commP (twoLiveHom h j₁ j₂ hlt (sqGen h (sqHandleIdxU j₂)))
        (twoLiveHom h j₁ j₂ hlt (sqGen h (sqHandleIdxV j₂))) ≠ 1 := by
  have hne : (j₁ : ℕ) ≠ (j₂ : ℕ) := by omega
  refine ⟨?_, ?_⟩
  · rw [twoLiveHom_gen, twoLiveHom_gen, twoLiveMark_handleU_one, twoLiveMark_handleV_one]
    exact commP_twoLive_ne.1
  · rw [twoLiveHom_gen, twoLiveHom_gen, twoLiveMark_handleU_two hne,
      twoLiveMark_handleV_two hne]
    exact commP_twoLive_ne.2

theorem twoLiveHom_sqEichU :
    twoLiveHom h j₁ j₂ hlt (sqEichU h (nuSel h j₁ 0 0) j₁) = twoLiveU := by
  rw [sqEichU_of_cleared nuSelClr_handleU, twoLiveHom_gen, twoLiveMark_handleU_one]

theorem twoLiveHom_sqEichV :
    twoLiveHom h j₁ j₂ hlt (sqEichV h (nuSel h j₁ 0 0) j₁) = twoLiveV := by
  rw [sqEichV_of_cleared nuSelClr_handleV, twoLiveHom_gen, twoLiveMark_handleV_one]

theorem twoLiveHom_b (x : (DSq h : Type)) :
    (twoLiveHom h j₁ j₂ hlt x).b = gr3Pi (toAdd (nuSel h j₁ 0 0 x)) := by
  have hne : (j₁ : ℕ) ≠ (j₂ : ℕ) := by omega
  refine mirHom_b (by rw [twoLiveHom_sigma]; rfl) (by rw [twoLiveHom_x0]; rfl)
    (by rw [twoLiveHom_x1]; rfl)
    (by rw [twoLiveHom_gen, twoLiveMark_handleU_one, map_zero]; rfl)
    (by rw [twoLiveHom_gen, twoLiveMark_handleV_one, map_zero]; rfl) (fun j' hj' => ?_) x
  by_cases h2 : j' = j₂
  · subst h2
    exact ⟨by rw [twoLiveHom_gen, twoLiveMark_handleU_two hne]; rfl,
      by rw [twoLiveHom_gen, twoLiveMark_handleV_two hne]; rfl⟩
  · exact ⟨by rw [twoLiveHom_gen, twoLiveMark_handleU_ne hj' h2]; rfl,
      by rw [twoLiveHom_gen, twoLiveMark_handleV_ne hj' h2]; rfl⟩

theorem twoLiveHom_b_eq_zero {g : (DSq h : Type)} (hg : nuSel h j₁ 0 0 g = 1) :
    (twoLiveHom h j₁ j₂ hlt g).b = 0 := by
  rw [twoLiveHom_b, hg, toAdd_one, map_zero]

/-- ⭐⭐ **The frame identification at the two-live point.**  The second live pair sits in the
frame untouched - the row clears only the `j₁`-handle - so this needs the general §2 statement
rather than `GradedFourMirror.mirHom_sqArbFrame`. -/
theorem twoLiveHom_sqArbFrame (g : (DSq h : Type)) :
    (fun i => twoLiveHom h j₁ j₂ hlt (sqArbFrame h (nuSel h j₁ 0 0) j₁ (sigArbDress h g) i))
      = twoLiveWit h j₁ j₂ twoLiveU twoLiveV (twoLiveHom h j₁ j₂ hlt g) := by
  have hne : (j₁ : ℕ) ≠ (j₂ : ℕ) := by omega
  rw [twoLiveWit_eq_dress, twoLiveWit_one]
  refine liveHom_sqArbFrame (m := twoLiveMark h j₁ j₂ twoLiveU twoLiveV)
    (by rw [twoLiveHom_sigma, twoLiveMark_zero]) (by rw [twoLiveHom_x0, twoLiveMark_one])
    (by rw [twoLiveHom_x1, twoLiveMark_two])
    (by rw [twoLiveHom_sqEichU, twoLiveMark_handleU_one])
    (by rw [twoLiveHom_sqEichV, twoLiveMark_handleV_one]) (fun j' hj' => ?_) g
  by_cases h2 : j' = j₂
  · subst h2
    exact ⟨by rw [twoLiveHom_gen], by rw [twoLiveHom_gen]⟩
  · exact ⟨by rw [twoLiveHom_gen], by rw [twoLiveHom_gen]⟩

/-! ### Soundness and the forcing at the two-live point -/

theorem twoLiveU_mem_liveFrameSub : twoLiveU ∈ liveFrameSub gr3R :=
  ⟨rfl, ⟨0, by show (0 : gr3R) = 2 * 0; ring⟩, 0, by show (0 : gr3R) = 2 * 0; ring⟩

theorem twoLiveV_mem_liveFrameSub : twoLiveV ∈ liveFrameSub gr3R :=
  ⟨rfl, ⟨1, by show (2 : gr3R) = 2 * 1; decide⟩, 0, by show (0 : gr3R) = 2 * 0; ring⟩

theorem sigFourY_mem_liveFrameSub : sigFourY ∈ liveFrameSub gr3R :=
  ⟨rfl, ⟨0, by show (0 : gr3R) = 2 * 0; ring⟩, 2, by show (4 : gr3R) = 2 * 2; decide⟩

/-- Every slot of the two-live marking lies in the widened frame - both live pairs. -/
theorem twoLiveMark_le_liveFrameSub (hne : (j₁ : ℕ) ≠ (j₂ : ℕ)) :
    Subgroup.closure (Set.range (twoLiveMark h j₁ j₂ twoLiveU twoLiveV)) ≤ liveFrameSub gr3R := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [twoLiveMark_zero]; exact sigFourMark_mem_liveFrameSub
  · rw [twoLiveMark_one]
    exact ⟨rfl, ⟨0, by show (0 : gr3R) = 2 * 0; ring⟩, 0, by show (0 : gr3R) = 2 * 0; ring⟩
  · rw [twoLiveMark_two]; exact sigFourY_mem_liveFrameSub
  · by_cases h1 : j' = j₁
    · subst h1; rw [twoLiveMark_handleU_one]; exact twoLiveU_mem_liveFrameSub
    · by_cases h2 : j' = j₂
      · subst h2; rw [twoLiveMark_handleU_two hne]; exact twoLiveV_mem_liveFrameSub
      · rw [twoLiveMark_handleU_ne h1 h2]; exact one_mem _
  · by_cases h1 : j' = j₁
    · subst h1; rw [twoLiveMark_handleV_one]; exact twoLiveV_mem_liveFrameSub
    · by_cases h2 : j' = j₂
      · subst h2; rw [twoLiveMark_handleV_two hne]; exact twoLiveU_mem_liveFrameSub
      · rw [twoLiveMark_handleV_ne h1 h2]; exact one_mem _

/-- ⭐⭐ **The model-independent soundness at the two-live point.** -/
theorem twoLive_gaTwo_even (hne : (j₁ : ℕ) ≠ (j₂ : ℕ)) {z : SqU5 gr3R}
    (hz : z ∈ rowGaTwoOf (Subgroup.closure
      (Set.range (twoLiveMark h j₁ j₂ twoLiveU twoLiveV)))) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) := by
  have hle : rowGaTwoOf (Subgroup.closure (Set.range (twoLiveMark h j₁ j₂ twoLiveU twoLiveV)))
      ≤ liveGaTwoSub gr3R := by
    rw [rowGaTwoOf, Subgroup.closure_le]
    rintro w ⟨p, hp, q, hq, rfl⟩
    exact commP_mem_liveGaTwoSub (twoLiveMark_le_liveFrameSub hne hp)
      (twoLiveMark_le_liveFrameSub hne hq)
  obtain ⟨-, -, -, -, -, -, hh, hi⟩ := hle hz
  exact ⟨hh, hi⟩

/-- ⭐⭐ **The sharper wave-55 bound is FALSE at the two-live point.** -/
theorem twoLive_not_rowGaTwoSub :
    ¬ rowGaTwoOf (Subgroup.closure (Set.range (twoLiveMark h j₁ j₂ twoLiveU twoLiveV)))
      ≤ rowGaTwoSub gr3R := by
  intro hle
  have hmem : commP (twoLiveMark h j₁ j₂ twoLiveU twoLiveV (sqHandleIdxU j₁))
      (twoLiveMark h j₁ j₂ twoLiveU twoLiveV (sqHandleIdxV j₁))
      ∈ rowGaTwoOf (Subgroup.closure
        (Set.range (twoLiveMark h j₁ j₂ twoLiveU twoLiveV))) :=
    Subgroup.subset_closure ⟨_, Subgroup.subset_closure ⟨_, rfl⟩, _,
      Subgroup.subset_closure ⟨_, rfl⟩, rfl⟩
  obtain ⟨-, -, -, -, -, -, hh, -⟩ := hle hmem
  rw [twoLiveMark_handleU_one, twoLiveMark_handleV_one, commP_twoLive.1] at hh
  exact absurd hh (by decide)

/-- ⭐⭐ **The sigma forcing at the two-live point.**  §1's general theorem applies verbatim:
the bit does not see either block. -/
theorem twoLiveWit_sigma_forced {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (h₃ : (∃ a : gr3R, z₃.h = 2 * a) ∧ (∃ b : gr3R, z₃.i = 2 * b))
    (h₄ : (∃ a : gr3R, z₄.h = 2 * a) ∧ (∃ b : gr3R, z₄.i = 2 * b))
    (hkill : sqRelWord (sigLift j₁ (twoLiveWit h j₁ j₂ U V v) z₀ w₁ w₂ z₃ z₄) = 1)
    (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    selPar v.a = 0 := by
  rw [twoLiveWit_eq_dress] at hkill
  exact gaugeX_sigma_forced (by rw [twoLiveWit, twoTuple_zero, mul_one])
    (by rw [twoLiveWit, twoTuple_one]) (by rw [twoLiveWit, twoTuple_two]; decide)
    (by rw [twoLiveWit, twoTuple_two]; decide) (by rw [twoLiveWit, twoTuple_two]; decide)
    (by rw [twoLiveWit, twoTuple_two]; decide)
    (by rw [twoLiveWit_one]; exact sqRelWord_twoLiveMark hlt) hvb hz₀ hw₁ hw₂ hz₃ hz₄ h₃ h₄
    hkill

/-- ⭐⭐ **The class-four selection bit at the two-live point**: the dressing's own character,
with **two** live blocks in the marking.  This is §1's blindness executed on a frame. -/
theorem twoLiveWit_sigma_bit (hvb : v.b = 0) (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    selPar ((sqRelWord (twoLiveWit h j₁ j₂ U V v)).j) = selPar v.a := by
  rw [twoLiveWit_eq_dress]
  exact sqRelWord_gaugeX_sigma_bit_of_rel (by rw [twoLiveWit, twoTuple_zero, mul_one])
    (by rw [twoLiveWit, twoTuple_one]) (by rw [twoLiveWit, twoTuple_two]; decide)
    (by rw [twoLiveWit, twoTuple_two]; decide) (by rw [twoLiveWit, twoTuple_two]; decide)
    (by rw [twoLiveWit, twoTuple_two]; decide) hvb
    (by rw [twoLiveWit_one]; exact sqRelWord_twoLiveMark hlt)

/-- ⭐⭐⭐ **THE HEADLINE AT TWO LIVE HANDLES.**  At the cleared row, at every handle count, at
an honest continuous homomorphism with **two** nontrivial handle commutators in its image,
every `ν'`-trivial sigma dressing of the arbitrary-dressing frame killed by any achievable
five-slot class-four refinement has an even `chi_a`-character.  Wave 57's cancellation covers
two blocks: it is a statement about the sigma slot, not about how many handles are live. -/
theorem sqArbFrame_sigma_forced_twoLive {g : (DSq h : Type)} (hg : nuSel h j₁ 0 0 g = 1)
    (hne : (j₁ : ℕ) ≠ (j₂ : ℕ)) {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure
      (Set.range (twoLiveMark h j₁ j₂ twoLiveU twoLiveV))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure
      (Set.range (twoLiveMark h j₁ j₂ twoLiveU twoLiveV))))
    (hkill : sqRelWord (sigLift j₁
      (fun i => twoLiveHom h j₁ j₂ hlt (sqArbFrame h (nuSel h j₁ 0 0) j₁ (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (twoLiveHom h j₁ j₂ hlt g).a = 0 := by
  rw [twoLiveHom_sqArbFrame g] at hkill
  exact twoLiveWit_sigma_forced (twoLiveHom_b_eq_zero hg) hz₀ hw₁ hw₂ hz₃ hz₄
    (twoLive_gaTwo_even hne l₃) (twoLive_gaTwo_even hne l₄) hkill hlt

theorem sqRelWord_twoLiveFrame_sigTriv :
    sqRelWord (fun i => twoLiveHom h j₁ j₂ hlt
      (sqArbFrame h (nuSel h j₁ 0 0) j₁ (sigArbDress h 1) i)) = 1 := by
  rw [twoLiveHom_sqArbFrame, map_one, twoLiveWit_one]
  exact sqRelWord_twoLiveMark hlt

theorem sqRelWord_twoLiveFrame_sigU :
    sqRelWord (fun i => twoLiveHom h j₁ j₂ hlt (sqArbFrame h (nuSel h j₁ 0 0) j₁
      (sigArbDress h (sqEichU h (nuSel h j₁ 0 0) j₁)) i)) = liftC 1 := by
  rw [twoLiveHom_sqArbFrame, twoLiveHom_sqEichU]
  exact sqRelWord_twoLiveWit_U hlt

theorem sqRelWord_twoLiveFrame_sigUsq :
    sqRelWord (fun i => twoLiveHom h j₁ j₂ hlt (sqArbFrame h (nuSel h j₁ 0 0) j₁
      (sigArbDress h (sqEichU h (nuSel h j₁ 0 0) j₁ * sqEichU h (nuSel h j₁ 0 0) j₁)) i))
      = liftC 2 := by
  rw [twoLiveHom_sqArbFrame, map_mul, twoLiveHom_sqEichU]
  exact sqRelWord_twoLiveWit_Usq hlt

/-- ⭐⭐⭐ **The escape separates the sigma dressings at a point with TWO live handle
blocks.** -/
theorem twoLive_escape_separates :
    (commP (twoLiveHom h j₁ j₂ hlt (sqGen h (sqHandleIdxU j₁)))
        (twoLiveHom h j₁ j₂ hlt (sqGen h (sqHandleIdxV j₁))) ≠ 1 ∧
      commP (twoLiveHom h j₁ j₂ hlt (sqGen h (sqHandleIdxU j₂)))
        (twoLiveHom h j₁ j₂ hlt (sqGen h (sqHandleIdxV j₂))) ≠ 1) ∧
    ((∀ i, nuLam h (sigArbDress h
        (sqEichU h (nuSel h j₁ 0 0) j₁ * sqEichU h (nuSel h j₁ 0 0) j₁) i) = 1) ∧
      ∀ i, nuSel h j₁ 0 0 (sigArbDress h
        (sqEichU h (nuSel h j₁ 0 0) j₁ * sqEichU h (nuSel h j₁ 0 0) j₁) i) = 1) ∧
    ((∀ i, nuLam h (sigArbDress h (sqEichU h (nuSel h j₁ 0 0) j₁) i) = 1) ∧
      ∀ i, nuSel h j₁ 0 0 (sigArbDress h (sqEichU h (nuSel h j₁ 0 0) j₁) i) = 1) ∧
    sqRelWord (fun i => twoLiveHom h j₁ j₂ hlt (sqArbFrame h (nuSel h j₁ 0 0) j₁
      (sigArbDress h (sqEichU h (nuSel h j₁ 0 0) j₁ * sqEichU h (nuSel h j₁ 0 0) j₁)) i))
      = liftC 2 ∧
    sqRelWord (fun i => twoLiveHom h j₁ j₂ hlt (sqArbFrame h (nuSel h j₁ 0 0) j₁
      (sigArbDress h (sqEichU h (nuSel h j₁ 0 0) j₁)) i)) = liftC 1 :=
  ⟨twoLiveHom_commP_ne_one,
    ⟨nuLam_sigArbDress_clrUsq, nu_sigArbDress_clrUsq⟩,
    ⟨nuLam_sigArbDress_clrU, nu_sigArbDress_clrU⟩,
    sqRelWord_twoLiveFrame_sigUsq, sqRelWord_twoLiveFrame_sigU⟩

/-- ⭐⭐ **The forcing is not vacuous at the two-live point.** -/
theorem twoLive_forcing_nonvacuous :
    nuLam h (sqEichU h (nuSel h j₁ 0 0) j₁) = 1 ∧
      nuSel h j₁ 0 0 (sqEichU h (nuSel h j₁ 0 0) j₁) = 1 ∧
      selPar (twoLiveHom h j₁ j₂ hlt (sqEichU h (nuSel h j₁ 0 0) j₁)).a = 1 :=
  ⟨nuLam_clrEichU, nu_clrEichU, by rw [twoLiveHom_sqEichU]; exact twoLiveU_chiA⟩

end TwoLivePoint

/-! ## 10 What two live handles break: the relator controls only the PRODUCT -/

section TwoLiveObstruction

variable {R : Type} [CommRing R] {x y : SqU5 R} {xa xc xd xe xf xg ya yc yd : R}
  {h : ℕ} {j₁ j₂ : Fin h} {U₁ V₁ U₂ V₂ : SqU5 R}

/-- ⭐⭐ **What the relator still forces at two live handles**: the **product** of the two
blocks has both class-three coordinates even.  Wave 57's `commP_gaThree_even_of_relator` is the
one-block case, where product and block coincide; §11 shows that at two blocks the individual
factors are **not** controlled, and that the difference is not academic. -/
theorem commP_pair_gaThree_even_of_relator
    (hxa : x.a = 2 * xa) (hxb : x.b = 0) (hxc : x.c = 2 * xc) (hxd : x.d = 2 * xd)
    (hxe : x.e = 2 * xe) (hxf : x.f = 2 * xf) (hxg : x.g = 2 * xg)
    (hya : y.a = 2 * ya) (hyb : y.b = 0) (hyc : y.c = 2 * yc) (hyd : y.d = 2 * yd)
    (hlt : (j₁ : ℕ) < (j₂ : ℕ))
    (hrel : sqRelWord (twoTuple (SqU5 R) h j₁ j₂ (sigFourMark R) x y U₁ V₁ U₂ V₂) = 1) :
    (∃ k : R, (commP U₁ V₁ * commP U₂ V₂).h = 2 * k) ∧
      (∃ k : R, (commP U₁ V₁ * commP U₂ V₂).i = 2 * k) := by
  obtain ⟨⟨ka, hka⟩, hb, -, -, -, -, -, ⟨kh, hkh⟩, ⟨ki, hki⟩⟩ :=
    sqWord_sigFourMark_gauge_even hxa hxb hxc hxd hxe hxf hxg hya hyb hyc hyd
  rw [sqRelWord_twoTuple hlt] at hrel
  set W : SqU5 R := commP U₁ V₁ * commP U₂ V₂ with hW
  have hWc : W.c = 0 := by rw [hW, SqU5.mul_c, SqU5.commP_c, SqU5.commP_c]; ring
  have hWd : W.d = 0 := by rw [hW, SqU5.mul_d, SqU5.commP_d, SqU5.commP_d]; ring
  have hh : (sqWord (sigFourMark R) x y).h + W.h
      + (sqWord (sigFourMark R) x y).a * W.f
      + (sqWord (sigFourMark R) x y).e * W.c = 0 := by
    rw [← SqU5.mul_h, hrel, SqU5.one_h]
  have hi : (sqWord (sigFourMark R) x y).i + W.i
      + (sqWord (sigFourMark R) x y).b * W.g
      + (sqWord (sigFourMark R) x y).f * W.d = 0 := by
    rw [← SqU5.mul_i, hrel, SqU5.one_i]
  rw [hWc, mul_zero, add_zero, hka, hkh] at hh
  rw [hWd, mul_zero, add_zero, hb, zero_mul, add_zero, hki] at hi
  exact ⟨⟨-kh - ka * W.f, by linear_combination hh⟩, ⟨-ki, by linear_combination hi⟩⟩

end TwoLiveObstruction

/-! ## 11 The two-live marking whose blocks are individually ODD -/

section TwoLiveOdd

variable {h : ℕ} {j₁ j₂ : Fin h}

/-- ⭐⭐⭐ **The odd partner letter**: `GradedSigmaFour.sigFourV` with fourth abelian column `1`
and second class-two coordinate `1` - **odd**, so it leaves `GradedFourCleared.liveFrameSub`. -/
def oddLiveV : SqU5 gr3R := ⟨2, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩

/-- ⭐⭐⭐ **The block is ODD in its first class-three coordinate.** -/
theorem commP_oddLive :
    commP sigFourU oddLiveV = (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩ : SqU5 gr3R) := by decide

theorem commP_oddLive_ne_one : commP sigFourU oddLiveV ≠ 1 := by decide

theorem commP_oddLive_isGaThree : (commP sigFourU oddLiveV).IsGaThree := by
  rw [commP_oddLive]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⭐⭐⭐ **Wave 57's automatic soundness does NOT extend to two live handles.**  This marking
kills the relator at the **committed** gauge, at every handle count and every ordered pair of
handles - and its two blocks are each **odd** in the first class-three coordinate.  At one live
handle `GradedFourCleared.commP_gaThree_even_of_relator` forbids exactly this; the two-handle
relator only controls the **sum**, and `commP_pair_gaThree_even_of_relator` is the sharpest
statement available. -/
theorem twoLiveOdd_block_odd (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    sqRelWord (twoLiveMark h j₁ j₂ sigFourU oddLiveV) = 1 ∧
      ¬ (∃ k : gr3R, (commP sigFourU oddLiveV).h = 2 * k) ∧
      (∃ k : gr3R, (commP sigFourU oddLiveV * commP oddLiveV sigFourU).h = 2 * k) :=
  ⟨sqRelWord_twoLiveMark hlt, by decide, by decide⟩

/-- The odd letter really is outside the widened frame. -/
theorem oddLiveV_not_mem_liveFrameSub : oddLiveV ∉ liveFrameSub gr3R := by
  intro hc
  obtain ⟨-, ⟨k, hk⟩, -⟩ := hc
  simp only [oddLiveV] at hk
  revert hk
  revert k
  decide

/-- The odd dressing still leaves the committed central residue `1`. -/
theorem sqRelWord_twoLiveOdd_U (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    sqRelWord (twoLiveWit h j₁ j₂ sigFourU oddLiveV sigFourU) = liftC 1 := by
  rw [sqRelWord_twoLiveWit hlt]; decide

/-- ⭐⭐⭐ **THE CERTIFIED NEGATIVE.**  At the odd two-live marking there is an **achievable**
five-slot class-four refinement - the sigma move trivial, the two exponent moves `1` and
`liftC 3`, the `v`-handle move the block `⁅U, V⁆` itself (a commutator of two slot values,
hence a legal `γ₂`-level dressing under the standing achievability convention, and `γ₃`-shaped)
- which **kills the relator at the odd sigma dressing**.  So the class-four sigma forcing is
FALSE here: the conclusion `selPar v.a = 0` fails at `v = sigFourU`, whose character is `1`.

The frame invariant `GradedFourCleared.liveFrameSub` is SUFFICIENT to rule this out

  CORRECTED BY W59-INVARIANT: `liveFrameSub` is MERELY SUFFICIENT here, not the sharp line.
  The sharp invariant is `FrameOrth` (both mod-two covectors of the handle slots' outer
  abelian columns annihilate the class-three parity image), characterised in both directions
  by `sigmaForces_iff_frameOrth`. The killing point below, the orthogonal point and the mixed
  point all carry the SAME odd block and all have their `v`-letter outside `liveFrameSub`,
  yet the forcing FAILS at the first and HOLDS at the other two; the mixed point differs from
  the killing point in ONE coordinate of ONE letter, which is not a frame invariant. So the
  reading "two live blocks outside the frame invariant break the forcing" is FALSE; what
  breaks it is an odd handle pairing. See `SqCore/GradedFrameNecessity.lean`.
  It, and at one
live handle wave 57 proved the relator supplies it for free.  At two it does not. -/
theorem twoLiveOdd_kill (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    sqRelWord (sigLift j₁ (twoLiveWit h j₁ j₂ sigFourU oddLiveV sigFourU) 1 1 (liftC 3)
      (commP sigFourU oddLiveV) 1) = 1 := by
  rw [sqRelWord_sigLift SqU5.isGaThree_one SqU5.isGaFour_one (liftC_isGaFour 3)
    commP_oddLive_isGaThree SqU5.isGaThree_one, sqRelWord_twoLiveOdd_U hlt, liftC_mul_liftC]
  refine Eq.trans (congrArg liftC ?_) liftC_zero
  simp only [twoLiveWit, twoTuple_one, twoTuple_handleU_one, twoTuple_handleV_one,
    SqU5.one_h, SqU5.one_i, SqU5.one_j, sigFourU, oddLiveV, sigFourX]
  decide

/-- …and the block used is a legal `γ₂`-level dressing of the marking's own image. -/
theorem commP_oddLive_mem_gaTwoOf :
    commP sigFourU oddLiveV
      ∈ rowGaTwoOf (Subgroup.closure (Set.range (twoLiveMark h j₁ j₂ sigFourU oddLiveV))) := by
  refine Subgroup.subset_closure ⟨sigFourU, ?_, oddLiveV, ?_, rfl⟩
  · exact Subgroup.subset_closure ⟨sqHandleIdxU j₁, twoLiveMark_handleU_one⟩
  · exact Subgroup.subset_closure ⟨sqHandleIdxV j₁, twoLiveMark_handleV_one⟩

/-- ⭐⭐⭐ **The class-four sigma forcing is FALSE at the odd two-live point**, stated as the
negation of its own shape: a legal odd dressing, a legal achievable refinement, a killed
relator, and an odd character. -/
theorem twoLiveOdd_sigma_forced_false (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    ¬ ∀ v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R, v.b = 0 → z₀.IsGaThree → w₁.IsGaFour → w₂.IsGaFour →
        z₃.IsGaThree → z₄.IsGaThree →
        z₃ ∈ rowGaTwoOf (Subgroup.closure
          (Set.range (twoLiveMark h j₁ j₂ sigFourU oddLiveV))) →
        z₄ ∈ rowGaTwoOf (Subgroup.closure
          (Set.range (twoLiveMark h j₁ j₂ sigFourU oddLiveV))) →
        sqRelWord (sigLift j₁ (twoLiveWit h j₁ j₂ sigFourU oddLiveV v) z₀ w₁ w₂ z₃ z₄) = 1 →
        selPar v.a = 0 := by
  intro hforce
  have hcon := hforce sigFourU 1 1 (liftC 3) (commP sigFourU oddLiveV) 1 (by decide)
    SqU5.isGaThree_one SqU5.isGaFour_one (liftC_isGaFour 3) commP_oddLive_isGaThree
    SqU5.isGaThree_one commP_oddLive_mem_gaTwoOf (one_mem _) (twoLiveOdd_kill hlt)
  rw [show (sigFourU.a : gr3R) = 1 from rfl] at hcon
  exact absurd hcon (by decide)

end TwoLiveOdd

/-! ## 12 A HIGHER pivot power: the row `nuSel h j 2 0` -/

section HigherPower

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐ **The `v`-letter of the second-power row**: `chi_a` even (forced only mod `4` here,
because `chiA_row_forced` reads `t·χ_a(V₀) = 2·χ_a(V₀)`), and second class-two coordinate `2`.
⚠ That `2` is what the first-power rows cannot afford: their block-preservation criterion pins
the `v`-letter's `f`-column into `{0, 4}`, and this one only into the even residues. -/
def hiLiveV : SqU5 gr3R := ⟨0, 0, 0, 1, 0, 2, 0, 0, 0, 0⟩

/-- **The `u`-slot of the marking**: the cleared letter displaced by the **square** of the
pivot. -/
def hiLiveUGen (c : gr3R) : SqU5 gr3R :=
  ⟨1 - 4 * c, 2, 0, 0, -(2 * c), 0, 0, 0, -(2 * c), 4 * (c * c) + 2 * c⟩

theorem hiLiveUGen_eq (c : gr3R) : hiLiveUGen c = rowPivotVal c * rowPivotVal c * sigFourU := by
  ext <;> simp only [hiLiveUGen, sigFourU, rowPivotVal, SqU5.mul_a, SqU5.mul_b, SqU5.mul_c,
    SqU5.mul_d, SqU5.mul_e, SqU5.mul_f, SqU5.mul_g, SqU5.mul_h, SqU5.mul_i, SqU5.mul_j] <;> ring

theorem hiLiveU_eq (c : gr3R) :
    (rowPivotVal c * rowPivotVal c)⁻¹ * hiLiveUGen c = sigFourU := by
  rw [hiLiveUGen_eq, inv_mul_cancel_left]

/-- ⭐⭐ **THE LIVE BLOCK AT THE SECOND-POWER ROW**: wave 57's own block, of order **four** -
which the three first-power rows provably cannot carry. -/
theorem commP_hiLive :
    commP sigFourU hiLiveV = (⟨0, 0, 0, 0, 0, 0, 0, 2, 0, 0⟩ : SqU5 gr3R) := by decide

theorem commP_hiLive_ne_one : commP sigFourU hiLiveV ≠ 1 := by decide

theorem commP_hiLive_eq_liveFour : commP sigFourU hiLiveV = commP liveFourU liveFourV := by
  decide

/-- ⭐⭐ **The squared displacement is inert on the block**, at every pivot residue. -/
theorem commP_hiLiveUGen :
    ∀ c : gr3R, commP (hiLiveUGen c) hiLiveV = commP sigFourU hiLiveV := by decide

theorem sqWord_mul_commP_hiLive :
    sqWord (sigFourMark gr3R) sigFourX liveFourY * commP sigFourU hiLiveV = 1 := by decide

variable (h j) in
/-- ⭐⭐ **The marking of the second-power point.** -/
def hiLiveMark (c : gr3R) : Fin (sqRank h) → SqU5 gr3R :=
  liveWit h j liveFourY (hiLiveUGen c) hiLiveV 1

variable (h j) in
/-- The second-power witness. -/
def hiLiveWit (v : SqU5 gr3R) : Fin (sqRank h) → SqU5 gr3R :=
  liveWit h j liveFourY sigFourU hiLiveV v

theorem sqRelWord_hiLiveMark (c : gr3R) : sqRelWord (hiLiveMark h j c) = 1 := by
  rw [hiLiveMark, sqRelWord_liveWit, mul_one, commP_hiLiveUGen c, sqWord_mul_commP_hiLive]

theorem sqRelWord_hiLiveWit_triv : sqRelWord (hiLiveWit h j 1) = 1 := by
  rw [hiLiveWit, sqRelWord_liveWit, mul_one, sqWord_mul_commP_hiLive]

theorem sqRelWord_hiLiveWit (v : SqU5 gr3R) :
    sqRelWord (hiLiveWit h j v)
      = sqWord (sigFourMark gr3R * v) sigFourX liveFourY * commP sigFourU hiLiveV :=
  sqRelWord_liveWit

theorem sqRelWord_hiLiveWit_U : sqRelWord (hiLiveWit h j sigFourU) = liftC 1 := by
  rw [sqRelWord_hiLiveWit]; decide

theorem sqRelWord_hiLiveWit_Usq :
    sqRelWord (hiLiveWit h j (sigFourU * sigFourU)) = liftC 2 := by
  rw [sqRelWord_hiLiveWit]; decide

theorem sqRelWord_hiLiveWit_Usq_complete :
    sqRelWord (sigLift j (hiLiveWit h j (sigFourU * sigFourU)) 1 1 (liftC 7) 1 1) = 1 := by
  rw [sqRelWord_sigLift SqU5.isGaThree_one SqU5.isGaFour_one (liftC_isGaFour 7)
    SqU5.isGaThree_one SqU5.isGaThree_one, sqRelWord_hiLiveWit_Usq, liftC_mul_liftC]
  refine Eq.trans (congrArg liftC ?_) liftC_zero
  simp only [hiLiveWit, liveWit_one, liveWit_handleU, liveWit_handleV, SqU5.one_h,
    SqU5.one_i, SqU5.one_j, sigFourU, hiLiveV, sigFourX]
  decide

theorem hiLiveWit_class_three_blind :
    (SqU5.toU4L (sqRelWord (hiLiveWit h j 1)) = 1 ∧
      SqU5.toU4R (sqRelWord (hiLiveWit h j 1)) = 1) ∧
    (SqU5.toU4L (sqRelWord (hiLiveWit h j (sigFourU * sigFourU))) = 1 ∧
      SqU5.toU4R (sqRelWord (hiLiveWit h j (sigFourU * sigFourU))) = 1) ∧
    (SqU5.toU4L (sqRelWord (hiLiveWit h j sigFourU)) = 1 ∧
      SqU5.toU4R (sqRelWord (hiLiveWit h j sigFourU)) = 1) := by
  rw [sqRelWord_hiLiveWit_triv, sqRelWord_hiLiveWit_Usq, sqRelWord_hiLiveWit_U]
  refine ⟨⟨map_one _, map_one _⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

@[simp] theorem hiLiveMark_zero (c : gr3R) : hiLiveMark h j c 0 = sigFourMark gr3R := by
  rw [hiLiveMark, liveWit_zero, mul_one]

@[simp] theorem hiLiveMark_one (c : gr3R) : hiLiveMark h j c 1 = sigFourX := liveWit_one

@[simp] theorem hiLiveMark_two (c : gr3R) : hiLiveMark h j c 2 = liveFourY := liveWit_two

@[simp] theorem hiLiveMark_handleU (c : gr3R) :
    hiLiveMark h j c (sqHandleIdxU j) = hiLiveUGen c := liveWit_handleU

@[simp] theorem hiLiveMark_handleV (c : gr3R) :
    hiLiveMark h j c (sqHandleIdxV j) = hiLiveV := liveWit_handleV

theorem hiLiveMark_handleU_ne (c : gr3R) {j' : Fin h} (hne : j' ≠ j) :
    hiLiveMark h j c (sqHandleIdxU j') = 1 := liveWit_handleU_ne hne

theorem hiLiveMark_handleV_ne (c : gr3R) {j' : Fin h} (hne : j' ≠ j) :
    hiLiveMark h j c (sqHandleIdxV j') = 1 := liveWit_handleV_ne hne

variable (h j) in
/-- ⭐⭐ **The second-power test hom.** -/
noncomputable def hiLiveHom : ContinuousMonoidHom (DSq h : Type) (SqU5 gr3R) :=
  sqU5Hom gr3R_card h (hiLiveMark h j (gr3Pi sqPivotExp))
    (sqRelWord_hiLiveMark (gr3Pi sqPivotExp))

@[simp] theorem hiLiveHom_gen (i : Fin (sqRank h)) :
    hiLiveHom h j (sqGen h i) = hiLiveMark h j (gr3Pi sqPivotExp) i := sqU5Hom_gen _ _ _ i

@[simp] theorem hiLiveHom_sigma : hiLiveHom h j (dsqSigma h) = sigFourMark gr3R := by
  rw [dsqSigma, hiLiveHom_gen, hiLiveMark_zero]

@[simp] theorem hiLiveHom_x0 : hiLiveHom h j (dsqX0 h) = sigFourX := by
  rw [dsqX0, hiLiveHom_gen, hiLiveMark_one]

@[simp] theorem hiLiveHom_x1 : hiLiveHom h j (dsqX1 h) = liveFourY := by
  rw [dsqX1, hiLiveHom_gen, hiLiveMark_two]

@[simp] theorem hiLiveHom_handleU :
    hiLiveHom h j (sqGen h (sqHandleIdxU j)) = hiLiveUGen (gr3Pi sqPivotExp) := by
  rw [hiLiveHom_gen, hiLiveMark_handleU]

@[simp] theorem hiLiveHom_handleV : hiLiveHom h j (sqGen h (sqHandleIdxV j)) = hiLiveV := by
  rw [hiLiveHom_gen, hiLiveMark_handleV]

theorem hiLiveHom_handle_ne {j' : Fin h} (hne : j' ≠ j) :
    hiLiveHom h j (sqGen h (sqHandleIdxU j')) = 1 ∧
      hiLiveHom h j (sqGen h (sqHandleIdxV j')) = 1 :=
  ⟨by rw [hiLiveHom_gen, hiLiveMark_handleU_ne _ hne],
    by rw [hiLiveHom_gen, hiLiveMark_handleV_ne _ hne]⟩

theorem hiLiveHom_sqPivot :
    hiLiveHom h j (sqPivot h) = rowPivotVal (gr3Pi sqPivotExp) :=
  mirHom_sqPivot hiLiveHom_sigma hiLiveHom_x0

theorem hiLiveHom_commP_ne_one :
    commP (hiLiveHom h j (sqGen h (sqHandleIdxU j)))
      (hiLiveHom h j (sqGen h (sqHandleIdxV j))) ≠ 1 := by
  rw [hiLiveHom_handleU, hiLiveHom_handleV, commP_hiLiveUGen]
  exact commP_hiLive_ne_one

theorem nuSelHi_handleV : nuSel h j 2 0 (sqGen h (sqHandleIdxV j)) = 1 := by
  rw [nuSel_handleV, ofAdd_zero]

theorem hiLiveHom_sqEichV : hiLiveHom h j (sqEichV h (nuSel h j 2 0) j) = hiLiveV := by
  rw [sqEichV_of_cleared nuSelHi_handleV, hiLiveHom_handleV]

/-- ⭐⭐ **The cleared `u`-letter at a HIGHER pivot power**: two inverse pivots are subtracted
on the left, through `ArbFrames.zpowZtwo_two_mul`. -/
theorem hiLiveHom_sqEichU : hiLiveHom h j (sqEichU h (nuSel h j 2 0) j) = sigFourU := by
  rw [sqEichU, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_gr5, nuSel_handleU,
    toAdd_ofAdd, show (2 : ℤ_[2]) = 2 * 1 by ring, zpowZtwo_two_mul, zpowZtwo_one_exp,
    hiLiveHom_sqPivot, hiLiveHom_handleU, sq, hiLiveU_eq]

theorem hiLiveHom_b (x : (DSq h : Type)) :
    (hiLiveHom h j x).b = gr3Pi (toAdd (nuSel h j 2 0 x)) :=
  mirHom_b (by rw [hiLiveHom_sigma]; rfl) (by rw [hiLiveHom_x0]; rfl)
    (by rw [hiLiveHom_x1]; rfl)
    (by rw [hiLiveHom_handleU]
        show (2 : gr3R) = gr3Pi (2 : ℤ_[2])
        rw [show (2 : ℤ_[2]) = 1 + 1 by norm_num, map_add, map_one]
        decide)
    (by rw [hiLiveHom_handleV, map_zero]; rfl)
    (fun j' hj' => by rw [(hiLiveHom_handle_ne hj').1, (hiLiveHom_handle_ne hj').2]; exact
      ⟨rfl, rfl⟩) x

theorem hiLiveHom_b_eq_zero {g : (DSq h : Type)} (hg : nuSel h j 2 0 g = 1) :
    (hiLiveHom h j g).b = 0 := by
  rw [hiLiveHom_b, hg, toAdd_one, map_zero]

theorem hiLiveHom_sqArbFrame (g : (DSq h : Type)) :
    (fun i => hiLiveHom h j (sqArbFrame h (nuSel h j 2 0) j (sigArbDress h g) i))
      = hiLiveWit h j (hiLiveHom h j g) := by
  rw [hiLiveWit, liveWit_eq_dress]
  exact liveHom_sqArbFrame (m := hiLiveWit h j 1)
    (by rw [hiLiveHom_sigma, hiLiveWit, liveWit_zero, mul_one])
    (by rw [hiLiveHom_x0, hiLiveWit, liveWit_one])
    (by rw [hiLiveHom_x1, hiLiveWit, liveWit_two])
    (by rw [hiLiveHom_sqEichU, hiLiveWit, liveWit_handleU])
    (by rw [hiLiveHom_sqEichV, hiLiveWit, liveWit_handleV])
    (fun j' hj' => ⟨by rw [(hiLiveHom_handle_ne hj').1, hiLiveWit, liveWit_handleU_ne hj'],
      by rw [(hiLiveHom_handle_ne hj').2, hiLiveWit, liveWit_handleV_ne hj']⟩) g

theorem liveFourY_mem_liveFrameSub : liveFourY ∈ liveFrameSub gr3R :=
  ⟨rfl, ⟨0, by show (0 : gr3R) = 2 * 0; ring⟩, 2, by show (4 : gr3R) = 2 * 2; decide⟩

theorem sigFourU_mem_liveFrameSub : sigFourU ∈ liveFrameSub gr3R :=
  ⟨rfl, ⟨0, by show (0 : gr3R) = 2 * 0; ring⟩, 0, by show (0 : gr3R) = 2 * 0; ring⟩

theorem hiLiveV_mem_liveFrameSub : hiLiveV ∈ liveFrameSub gr3R :=
  ⟨rfl, ⟨1, by show (2 : gr3R) = 2 * 1; decide⟩, 0, by show (0 : gr3R) = 2 * 0; ring⟩

theorem hiLiveUGen_mem_liveFrameSub (c : gr3R) : hiLiveUGen c ∈ liveFrameSub gr3R :=
  ⟨rfl, ⟨0, by show (0 : gr3R) = 2 * 0; ring⟩, 0, by show (0 : gr3R) = 2 * 0; ring⟩

/-- ⭐⭐ **The model-independent soundness at the second-power point.** -/
theorem hiLive_gaTwo_even (c : gr3R) {z : SqU5 gr3R}
    (hz : z ∈ rowGaTwoOf (Subgroup.closure (Set.range (hiLiveMark h j c)))) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) :=
  liveWit_gaTwo_even liveFourY_mem_liveFrameSub (hiLiveUGen_mem_liveFrameSub c)
    hiLiveV_mem_liveFrameSub (by rw [mul_one]; exact sigFourMark_mem_liveFrameSub) hz

/-- ⭐⭐ **The sharper wave-55 bound is FALSE at the second-power point**, and here the block is
of order **four**, not two. -/
theorem hiLive_not_rowGaTwoSub (c : gr3R) :
    ¬ rowGaTwoOf (Subgroup.closure (Set.range (hiLiveMark h j c))) ≤ rowGaTwoSub gr3R := by
  intro hle
  have hmem : commP (hiLiveMark h j c (sqHandleIdxU j)) (hiLiveMark h j c (sqHandleIdxV j))
      ∈ rowGaTwoOf (Subgroup.closure (Set.range (hiLiveMark h j c))) :=
    Subgroup.subset_closure ⟨_, Subgroup.subset_closure ⟨_, rfl⟩, _,
      Subgroup.subset_closure ⟨_, rfl⟩, rfl⟩
  obtain ⟨-, -, -, -, -, -, hh, -⟩ := hle hmem
  rw [hiLiveMark_handleU, hiLiveMark_handleV, commP_hiLiveUGen, commP_hiLive] at hh
  exact absurd hh (by decide)

/-- The committed achievable lattice is even at the second-power point, at the parameters
`(1, 0, 0, 0, 0, 1, 2, 0)` - wave 56's mirror ones with the row value doubled, which the
lattice reads only through `2·(…)`. -/
theorem hiLiveWit_lamThree_even {P Q R : gr3R} {z : SqU5 gr3R}
    (hz : selLamThree 1 0 0 0 0 1 2 0 P Q R z) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) := by
  obtain ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, hh, hi⟩ := hz
  exact ⟨⟨r₆ * Q, by rw [hh]; ring⟩,
    ⟨r₅ * R + 2 * (r₆ * R) - r₇ * Q, by rw [hi]; ring⟩⟩

/-- ⭐⭐ **The sigma forcing at the second-power point.** -/
theorem hiLiveWit_sigma_forced {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (h₃ : (∃ a : gr3R, z₃.h = 2 * a) ∧ (∃ b : gr3R, z₃.i = 2 * b))
    (h₄ : (∃ a : gr3R, z₄.h = 2 * a) ∧ (∃ b : gr3R, z₄.i = 2 * b))
    (hkill : sqRelWord (sigLift j (hiLiveWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  liveWit_sigma_forced (by decide) (by decide) (by decide) (by decide)
    sqRelWord_hiLiveWit_triv hvb hz₀ hw₁ hw₂ hz₃ hz₄ h₃ h₄ hkill

theorem hiLiveWit_sigma_forced_gaTwo {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hvb : v.b = 0) (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (hiLiveMark h j c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (hiLiveMark h j c))))
    (hkill : sqRelWord (sigLift j (hiLiveWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  hiLiveWit_sigma_forced hvb hz₀ hw₁ hw₂ hz₃ hz₄ (hiLive_gaTwo_even c l₃)
    (hiLive_gaTwo_even c l₄) hkill

theorem hiLive_forcing_nonvacuous :
    nuLam h (sqEichU h (nuSel h j 2 0) j) = 1 ∧
      nuSel h j 2 0 (sqEichU h (nuSel h j 2 0) j) = 1 ∧
      selPar (hiLiveHom h j (sqEichU h (nuSel h j 2 0) j)).a = 1 :=
  ⟨Multiplicative.toAdd.injective (by rw [toAdd_nuLam_sqEichU, toAdd_one]),
    Multiplicative.toAdd.injective (by rw [toAdd_nu_sqEichU nuSel_sigma nuSel_x0, toAdd_one]),
    by rw [hiLiveHom_sqEichU]; exact clrFourU_chiA⟩

theorem sqRelWord_hiLiveFrame_sigU :
    sqRelWord (fun i => hiLiveHom h j (sqArbFrame h (nuSel h j 2 0) j
      (sigArbDress h (sqEichU h (nuSel h j 2 0) j)) i)) = liftC 1 := by
  rw [hiLiveHom_sqArbFrame, hiLiveHom_sqEichU]
  exact sqRelWord_hiLiveWit_U

theorem sqRelWord_hiLiveFrame_sigUsq :
    sqRelWord (fun i => hiLiveHom h j (sqArbFrame h (nuSel h j 2 0) j
      (sigArbDress h (sqEichU h (nuSel h j 2 0) j * sqEichU h (nuSel h j 2 0) j)) i))
      = liftC 2 := by
  rw [hiLiveHom_sqArbFrame, map_mul, hiLiveHom_sqEichU]
  exact sqRelWord_hiLiveWit_Usq

/-- ⭐⭐ **THE HEADLINE AT A HIGHER PIVOT POWER.**  The row obstruction of `GradedFourMirror`
is stated for arbitrary displacement parameters; this is the first point built beyond the four
selected rows, and the pattern continues - with an **order-four** live block, which the
first-power rows cannot have. -/
theorem sqArbFrame_sigma_forced_hiLive {g : (DSq h : Type)} (hg : nuSel h j 2 0 g = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (hiLiveMark h j c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (hiLiveMark h j c))))
    (hkill : sqRelWord (sigLift j
      (fun i => hiLiveHom h j (sqArbFrame h (nuSel h j 2 0) j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (hiLiveHom h j g).a = 0 := by
  rw [hiLiveHom_sqArbFrame g] at hkill
  exact hiLiveWit_sigma_forced_gaTwo (hiLiveHom_b_eq_zero hg) hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄ hkill

/-- ⭐⭐ **The block orders across the catalogue**, as a single decidable statement: order four
at the cleared row and at the second power, order two at all three first-power rows. -/
theorem live_block_orders :
    (commP liveFourU liveFourV).h = 2 ∧ (commP sigFourU hiLiveV).h = 2 ∧
      (commP mirFourU mirLiveV).h = 4 ∧ (commP rowLiveU rowFourV).h = 4 ∧
      (commP mirFourU dblLiveV).h = 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end HigherPower

/-! ## 13 Axiom pins

Committed prints for every public declaration of this file. -/

section AxiomPins

#print axioms sqRelWord_gaugeX_dress_low
#print axioms sqRelWord_gaugeX_sigma_bit
#print axioms sqRelWord_gaugeX_sigma_bit_of_rel
#print axioms gaugeX_increment_even
#print axioms gaugeX_sigma_forced
#print axioms liveHom_sqArbFrame
#print axioms commP_left_displace
#print axioms commP_right_displace
#print axioms commP_swap
#print axioms commP_left_displace_inert
#print axioms commP_right_displace_gaThree
#print axioms commP_rowPivot_right_defect
#print axioms liveWit
#print axioms liveWit_zero
#print axioms liveWit_one
#print axioms liveWit_two
#print axioms liveWit_handleU
#print axioms liveWit_handleV
#print axioms liveWit_handleU_ne
#print axioms liveWit_handleV_ne
#print axioms liveWit_eq_dress
#print axioms sqRelWord_liveWit
#print axioms liveWit_sigma_forced
#print axioms liveWit_sigma_bit
#print axioms liveWit_le_liveFrameSub
#print axioms liveWit_gaTwo_even
#print axioms liveRowY
#print axioms sqWord_liveRowY
#print axioms mirLiveV
#print axioms mirLiveV_eq
#print axioms commP_mirLive
#print axioms commP_mirLive_ne_one
#print axioms commP_mirLiveUGen
#print axioms commP_rowPivot_mirLiveV
#print axioms sqWord_mul_commP_mirLive
#print axioms mirLiveMark
#print axioms mirLiveWit
#print axioms sqRelWord_mirLiveMark
#print axioms sqRelWord_mirLiveWit_triv
#print axioms sqRelWord_mirLiveWit
#print axioms sqRelWord_mirLiveWit_U
#print axioms sqRelWord_mirLiveWit_Usq
#print axioms sqRelWord_mirLiveWit_V
#print axioms sqRelWord_mirLiveWit_Usq_complete
#print axioms mirLiveWit_class_three_blind
#print axioms mirLiveMark_zero
#print axioms mirLiveMark_one
#print axioms mirLiveMark_two
#print axioms mirLiveMark_handleU
#print axioms mirLiveMark_handleV
#print axioms mirLiveMark_handleU_ne
#print axioms mirLiveMark_handleV_ne
#print axioms mirLiveHom
#print axioms mirLiveHom_gen
#print axioms mirLiveHom_sigma
#print axioms mirLiveHom_x0
#print axioms mirLiveHom_x1
#print axioms mirLiveHom_handleU
#print axioms mirLiveHom_handleV
#print axioms mirLiveHom_handle_ne
#print axioms mirLiveHom_sqPivot
#print axioms mirLiveHom_commP_ne_one
#print axioms mirLiveHom_sqEichV
#print axioms mirLiveHom_sqEichU
#print axioms mirLiveHom_b
#print axioms mirLiveHom_b_eq_zero
#print axioms mirLiveHom_sqArbFrame
#print axioms liveRowY_mem_liveFrameSub
#print axioms mirFourU_mem_liveFrameSub
#print axioms mirLiveV_mem_liveFrameSub
#print axioms mirFourUGen_mem_liveFrameSub
#print axioms sigFourMark_mem_liveFrameSub
#print axioms mirLive_gaTwo_even
#print axioms mirLive_not_rowGaTwoSub
#print axioms mirLiveWit_lamThree_even
#print axioms mirLiveWit_commP_data
#print axioms mirLiveHom_mem_closure
#print axioms mirLiveWit_sigma_forced
#print axioms mirLiveWit_sigma_forced_lam
#print axioms mirLiveWit_sigma_forced_gaTwo
#print axioms mirLive_forcing_nonvacuous
#print axioms sqRelWord_mirLiveFrame_sigTriv
#print axioms sqRelWord_mirLiveFrame_sigU
#print axioms sqRelWord_mirLiveFrame_sigUsq
#print axioms sqRelWord_mirLiveFrame_sigUsq_complete
#print axioms sqRelWord_mirLiveFrame_sigU_ne_one_gaTwo
#print axioms sqArbFrame_sigma_bit_mirLive
#print axioms sqArbFrame_sigma_forced_mirLive
#print axioms sqArbFrame_sigma_forced_mirLive_lam
#print axioms mirLive_escape_separates
#print axioms rowLiveU
#print axioms rowLiveU_eq
#print axioms commP_rowLive
#print axioms commP_rowLive_ne_one
#print axioms commP_rowLiveVGen
#print axioms commP_rowLiveU_rowPivot
#print axioms sqWord_mul_commP_rowLive
#print axioms rowLiveMark
#print axioms rowLiveWit
#print axioms sqRelWord_rowLiveMark
#print axioms sqRelWord_rowLiveWit_triv
#print axioms sqRelWord_rowLiveWit
#print axioms sqRelWord_rowLiveWit_V
#print axioms sqRelWord_rowLiveWit_Vsq
#print axioms sqRelWord_rowLiveWit_U
#print axioms sqRelWord_rowLiveWit_Vsq_complete
#print axioms rowLiveWit_class_three_blind
#print axioms rowLiveMark_zero
#print axioms rowLiveMark_one
#print axioms rowLiveMark_two
#print axioms rowLiveMark_handleU
#print axioms rowLiveMark_handleV
#print axioms rowLiveMark_handleU_ne
#print axioms rowLiveMark_handleV_ne
#print axioms rowLiveHom
#print axioms rowLiveHom_gen
#print axioms rowLiveHom_sigma
#print axioms rowLiveHom_x0
#print axioms rowLiveHom_x1
#print axioms rowLiveHom_handleU
#print axioms rowLiveHom_handleV
#print axioms rowLiveHom_handle_ne
#print axioms rowLiveHom_sqPivot
#print axioms rowLiveHom_commP_ne_one
#print axioms rowLiveHom_sqEichU
#print axioms rowLiveHom_sqEichV
#print axioms rowLiveHom_b
#print axioms rowLiveHom_b_eq_zero
#print axioms rowLiveHom_sqArbFrame
#print axioms rowLiveU_mem_liveFrameSub
#print axioms rowFourV_mem_liveFrameSub
#print axioms rowFourVGen_mem_liveFrameSub
#print axioms rowLive_gaTwo_even
#print axioms rowLive_not_rowGaTwoSub
#print axioms rowLiveWit_lamThree_even
#print axioms rowLiveWit_commP_data
#print axioms rowLiveWit_sigma_forced
#print axioms rowLiveWit_sigma_forced_lam
#print axioms rowLiveWit_sigma_forced_gaTwo
#print axioms rowLive_forcing_nonvacuous
#print axioms sqRelWord_rowLiveFrame_sigTriv
#print axioms sqRelWord_rowLiveFrame_sigV
#print axioms sqRelWord_rowLiveFrame_sigVsq
#print axioms sqRelWord_rowLiveFrame_sigVsq_complete
#print axioms sqRelWord_rowLiveFrame_sigV_ne_one_gaTwo
#print axioms sqArbFrame_sigma_bit_rowLive
#print axioms sqArbFrame_sigma_forced_rowLive
#print axioms sqArbFrame_sigma_forced_rowLive_lam
#print axioms rowLive_escape_separates
#print axioms dblLiveV
#print axioms dblLiveVGen
#print axioms dblLiveVGen_eq
#print axioms dblLiveV_eq
#print axioms commP_dblLive
#print axioms commP_dblLive_ne_one
#print axioms commP_dblLiveGen
#print axioms sqWord_mul_commP_dblLive
#print axioms dblLiveV_chiA
#print axioms dblLiveMark
#print axioms dblLiveWit
#print axioms sqRelWord_dblLiveMark
#print axioms sqRelWord_dblLiveWit_triv
#print axioms sqRelWord_dblLiveWit
#print axioms sqRelWord_dblLiveWit_U
#print axioms sqRelWord_dblLiveWit_Usq
#print axioms sqRelWord_dblLiveWit_V
#print axioms sqRelWord_dblLiveWit_Vsq
#print axioms sqRelWord_dblLiveWit_Usq_complete
#print axioms dblLiveWit_class_three_blind
#print axioms dblLiveMark_zero
#print axioms dblLiveMark_one
#print axioms dblLiveMark_two
#print axioms dblLiveMark_handleU
#print axioms dblLiveMark_handleV
#print axioms dblLiveMark_handleU_ne
#print axioms dblLiveMark_handleV_ne
#print axioms dblLiveHom
#print axioms dblLiveHom_gen
#print axioms dblLiveHom_sigma
#print axioms dblLiveHom_x0
#print axioms dblLiveHom_x1
#print axioms dblLiveHom_handleU
#print axioms dblLiveHom_handleV
#print axioms dblLiveHom_handle_ne
#print axioms dblLiveHom_sqPivot
#print axioms dblLiveHom_commP_ne_one
#print axioms dblLiveHom_sqEichU
#print axioms dblLiveHom_sqEichV
#print axioms dblLiveHom_b
#print axioms dblLiveHom_b_eq_zero
#print axioms dblLiveHom_sqArbFrame
#print axioms dblLiveV_mem_liveFrameSub
#print axioms dblLiveVGen_mem_liveFrameSub
#print axioms dblLive_gaTwo_even
#print axioms dblLive_not_rowGaTwoSub
#print axioms dblLiveWit_lamThree_even
#print axioms dblLiveWit_commP_data
#print axioms dblLiveWit_sigma_forced
#print axioms dblLiveWit_sigma_forced_lam
#print axioms dblLiveWit_sigma_forced_gaTwo
#print axioms dblLive_forcing_nonvacuous
#print axioms sqRelWord_dblLiveFrame_sigTriv
#print axioms sqRelWord_dblLiveFrame_sigU
#print axioms sqRelWord_dblLiveFrame_sigUsq
#print axioms sqRelWord_dblLiveFrame_sigV
#print axioms sqRelWord_dblLiveFrame_sigUsq_complete
#print axioms sqRelWord_dblLiveFrame_sigU_ne_one_gaTwo
#print axioms sqRelWord_dblLiveFrame_sigV_ne_one_gaTwo
#print axioms sqArbFrame_sigma_bit_dblLive
#print axioms sqArbFrame_sigma_forced_dblLive
#print axioms sqArbFrame_sigma_forced_dblLive_lam
#print axioms dblLive_escape_separates
#print axioms handleWord_eq_pair
#print axioms twoTuple
#print axioms twoTuple_zero
#print axioms twoTuple_one
#print axioms twoTuple_two
#print axioms twoTuple_handleU_one
#print axioms twoTuple_handleV_one
#print axioms twoTuple_handleU_two
#print axioms twoTuple_handleV_two
#print axioms twoTuple_handleU_ne
#print axioms twoTuple_handleV_ne
#print axioms sqRelWord_twoTuple
#print axioms sqRelWord_twoTuple_swap
#print axioms commP_g_eq_zero
#print axioms commP_e_eq_zero
#print axioms commP_pair_no_coupling
#print axioms commP_pair_no_coupling'
#print axioms commP_coupling_ne_zero_imp
#print axioms twoLiveMark
#print axioms twoLiveWit
#print axioms twoLiveWit_one
#print axioms twoLiveWit_eq_dress
#print axioms sqRelWord_twoLiveMark
#print axioms sqRelWord_twoLiveWit
#print axioms commP_twoLive_ne_one
#print axioms commP_twoLive_ne_one'
#print axioms twoLiveU
#print axioms twoLiveV
#print axioms twoLiveU_eq
#print axioms twoLiveV_eq
#print axioms commP_twoLive
#print axioms commP_twoLive_ne
#print axioms twoLiveU_chiA
#print axioms sqRelWord_twoLiveWit_triv
#print axioms sqRelWord_twoLiveWit_U
#print axioms sqRelWord_twoLiveWit_Usq
#print axioms sqRelWord_twoLiveWit_Usq_complete
#print axioms twoLiveWit_class_three_blind
#print axioms twoLiveMark_zero
#print axioms twoLiveMark_one
#print axioms twoLiveMark_two
#print axioms twoLiveMark_handleU_one
#print axioms twoLiveMark_handleV_one
#print axioms twoLiveMark_handleU_two
#print axioms twoLiveMark_handleV_two
#print axioms twoLiveMark_handleU_ne
#print axioms twoLiveMark_handleV_ne
#print axioms twoLiveHom
#print axioms twoLiveHom_gen
#print axioms twoLiveHom_sigma
#print axioms twoLiveHom_x0
#print axioms twoLiveHom_x1
#print axioms twoLiveHom_sqPivot
#print axioms twoLiveHom_commP_ne_one
#print axioms twoLiveHom_sqEichU
#print axioms twoLiveHom_sqEichV
#print axioms twoLiveHom_b
#print axioms twoLiveHom_b_eq_zero
#print axioms twoLiveHom_sqArbFrame
#print axioms twoLiveU_mem_liveFrameSub
#print axioms twoLiveV_mem_liveFrameSub
#print axioms sigFourY_mem_liveFrameSub
#print axioms twoLiveMark_le_liveFrameSub
#print axioms twoLive_gaTwo_even
#print axioms twoLive_not_rowGaTwoSub
#print axioms twoLiveWit_sigma_forced
#print axioms twoLiveWit_sigma_bit
#print axioms sqArbFrame_sigma_forced_twoLive
#print axioms sqRelWord_twoLiveFrame_sigTriv
#print axioms sqRelWord_twoLiveFrame_sigU
#print axioms sqRelWord_twoLiveFrame_sigUsq
#print axioms twoLive_escape_separates
#print axioms twoLive_forcing_nonvacuous
#print axioms commP_pair_gaThree_even_of_relator
#print axioms oddLiveV
#print axioms commP_oddLive
#print axioms commP_oddLive_ne_one
#print axioms commP_oddLive_isGaThree
#print axioms twoLiveOdd_block_odd
#print axioms oddLiveV_not_mem_liveFrameSub
#print axioms sqRelWord_twoLiveOdd_U
#print axioms twoLiveOdd_kill
#print axioms commP_oddLive_mem_gaTwoOf
#print axioms twoLiveOdd_sigma_forced_false
#print axioms hiLiveV
#print axioms hiLiveUGen
#print axioms hiLiveUGen_eq
#print axioms hiLiveU_eq
#print axioms commP_hiLive
#print axioms commP_hiLive_ne_one
#print axioms commP_hiLive_eq_liveFour
#print axioms commP_hiLiveUGen
#print axioms sqWord_mul_commP_hiLive
#print axioms hiLiveMark
#print axioms hiLiveWit
#print axioms sqRelWord_hiLiveMark
#print axioms sqRelWord_hiLiveWit_triv
#print axioms sqRelWord_hiLiveWit
#print axioms sqRelWord_hiLiveWit_U
#print axioms sqRelWord_hiLiveWit_Usq
#print axioms sqRelWord_hiLiveWit_Usq_complete
#print axioms hiLiveWit_class_three_blind
#print axioms hiLiveMark_zero
#print axioms hiLiveMark_one
#print axioms hiLiveMark_two
#print axioms hiLiveMark_handleU
#print axioms hiLiveMark_handleV
#print axioms hiLiveMark_handleU_ne
#print axioms hiLiveMark_handleV_ne
#print axioms hiLiveHom
#print axioms hiLiveHom_gen
#print axioms hiLiveHom_sigma
#print axioms hiLiveHom_x0
#print axioms hiLiveHom_x1
#print axioms hiLiveHom_handleU
#print axioms hiLiveHom_handleV
#print axioms hiLiveHom_handle_ne
#print axioms hiLiveHom_sqPivot
#print axioms hiLiveHom_commP_ne_one
#print axioms nuSelHi_handleV
#print axioms hiLiveHom_sqEichV
#print axioms hiLiveHom_sqEichU
#print axioms hiLiveHom_b
#print axioms hiLiveHom_b_eq_zero
#print axioms hiLiveHom_sqArbFrame
#print axioms liveFourY_mem_liveFrameSub
#print axioms sigFourU_mem_liveFrameSub
#print axioms hiLiveV_mem_liveFrameSub
#print axioms hiLiveUGen_mem_liveFrameSub
#print axioms hiLive_gaTwo_even
#print axioms hiLive_not_rowGaTwoSub
#print axioms hiLiveWit_lamThree_even
#print axioms hiLiveWit_sigma_forced
#print axioms hiLiveWit_sigma_forced_gaTwo
#print axioms hiLive_forcing_nonvacuous
#print axioms sqRelWord_hiLiveFrame_sigU
#print axioms sqRelWord_hiLiveFrame_sigUsq
#print axioms sqArbFrame_sigma_forced_hiLive
#print axioms live_block_orders

end AxiomPins

end SqCore

end Dyadic

end GQ2

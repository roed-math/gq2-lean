/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFourTwoLive

/-!
# W59-INVARIANT: `liveFrameSub` is MERELY SUFFICIENT, and here is the sharp line

`GradedFourTwoLive` (wave 58) refuted a composite the campaign was close to publishing: at
**two** live handles the relator controls only the product of the blocks, both can be odd, and
an achievable five-slot refinement kills the relator at the odd sigma dressing
(`twoLiveOdd_kill`, `twoLiveOdd_sigma_forced_false`).  Its own reading of that refutation was

> The frame invariant `liveFrameSub` is **exactly** what rules this out … at two live handles
> the frame invariants stop being bookkeeping and become the load-bearing hypothesis.

and the campaign log turned it into a headline: *a live block inside the frame invariant never
endangers the class-four forcing; two live blocks outside it do.*  The first half is a theorem.
**The second half is false**, and this file says what is true instead.

## ⭐⭐⭐ Headline 1: the answer is MERELY SUFFICIENT

`GradedFourCleared.liveFrameSub` has exactly one job in the whole tree: it makes every
achievable `γ₂`-level handle move even in both class-three coordinates, which makes the
five-slot increment of `GradedSigmaFour.sqRelWord_sigLift` even.  But the increment does not read
those coordinates alone.  Over the committed `x₀`-gauge its parity is exactly

```text
sigIncrPair m j z₃ z₄ = z₃.h·V.d − z₃.i·V.a + U.a·z₄.i − U.d·z₄.h        (mod 2)
```

with `U`, `V` the two handle slots at the lifted handle.  ⭐⭐⭐ **This pairing is the sharp
line**, and `liveFrameSub` is one of two visibly different ways to make it vanish:

```text
                                    kills the LEFT factor        kills the RIGHT factor
liveFrameSub containment            every achievable move even    -
even handle outer columns           -                             U.a, U.d, V.a, V.d even
```

`frameOrth_of_le_liveFrameSub` and `frameOrth_of_handle_even` are the two implications, and
neither hypothesis implies the other.

## ⭐⭐⭐ Headline 2: THE CHARACTERISATION

⭐⭐⭐ `sigmaForces_iff_frameOrth`.  At any relator-killing marking over the committed gauge
which admits one odd-character `ν'`-trivial dressing with central residue - the escape datum
every point of the catalogue already proves - the class-four sigma forcing holds **if and only
if** both mod-`2` covectors `(V.d, V.a)` and `(U.d, U.a)` annihilate the class-three parity
image of `γ₂` of the marking's image (`FrameOrth`).

The two halves are `sigmaForces_of_frameOrth` (⭐⭐ `gaugeX_sigma_forced_pair`, which subsumes
wave 58's `gaugeX_sigma_forced`) and `frameOrth_of_sigmaForces`, whose engine is ⭐⭐⭐
`gaugeX_kill_of_pair`: an odd pairing always produces an explicit kill, because the even part of
the increment is fully tunable by the class-four exponent slot.  `GradedFourTwoLive`'s
`twoLiveOdd_kill` is one instance of it, with `w₂ = liftC 3`.

## ⭐⭐⭐ Headline 3: three markings, ONE block, two verdicts

The wave-58 killing point, and both new points of §5 and §6, carry the **same** handle block -
the class-three element with first coordinate `1`, **odd** - and all three `v`-letters are
outside `liveFrameSub`.  The forcing FAILS at one and HOLDS at the other two
(`twoLiveOdd_block_not_the_criterion`).

```text
point            u-letter    v-letter                covectors (U.d,U.a),(V.d,V.a)   forcing
W58 oddLive      sigFourU    ⟨2,0,0,1,0,1,0,0,0,0⟩   (0,1), (1,0)                    FAILS
W59 orth §5      ⟨0,…,e=1⟩   ⟨0,0,1,0,0,0,0,0,0,0⟩   (0,0), (0,0)                    HOLDS
W59 mix  §6      sigFourU    ⟨0,0,0,0,0,1,0,0,0,0⟩   (0,1), (0,0)                    HOLDS
```

The wave-58 point and the mixed point differ in **one coordinate of one letter**, the fourth
abelian column, which is not a frame invariant and which no wave has ever constrained
(`mixV_covector_vs_oddLiveV`).  So what breaks the forcing is not the block, and not the frame
invariant: it is the parity of the block's pairing against the handle slots' outer columns.

## ⭐⭐ The two points, and what each one shows

* **§5, the orthogonal point.**  Both covectors vanish, so `orth_pair_eq_zero` gives the pairing
  identically `0` for **arbitrary** `γ₃`-shaped moves.  Hence ⭐⭐⭐ `orth_sigma_forced` holds
  with **no achievability hypothesis at all** - the campaign's standing `γ₂` convention is not
  consumed - while `orth_not_le_liveFrameSub` and `orth_not_gaTwo_even` show the carried
  hypothesis and its consequence both fail there.  The `v`-letter even has a **nonzero
  `c`-column**, the very thing `GradedFourTwoLive.commP_coupling_ne_zero_imp` calls unavailable
  to any point the forcing can be run at; the coupling still vanishes (`commP_orth_g`), so a
  nonzero `c`-column is necessary for the class-four coupling and not sufficient.
* **§6, the mixed point.**  Here the `u`-covector is `(0, 1)`, so **both** sufficient conditions
  fail: the achievable set is odd in its first class-three coordinate and the `u`-slot's outer
  column is odd (`mixU_chiA`).  The forcing holds anyway, through a genuinely different
  invariant, ⭐⭐ `halfFrameSub` - even fourth abelian column, even third class-two coordinate -
  which is **incomparable** with `liveFrameSub` and which controls only the *second* class-three
  coordinate of every commutator (`commP_mem_halfGaTwoSub`).  And here achievability IS
  load-bearing: ⭐⭐⭐ `mix_unrestricted_kill` exhibits an **unachievable** `γ₃` move that kills
  the odd dressing, so `mix_unrestricted_sigma_forced_false` while `mix_sigmaForces`.

## ⭐⭐ What the campaign should carry

The honest hypothesis is `FrameOrth`, not `liveFrameSub`.  `committed_covectors` reads the two
covectors off every committed point, and the answer is uneven: **at the cleared row, the live
point, the two-live point and the doubly displaced row the `v`-covector reads only the second
class-three coordinate, so `frameOrth_of_gaTwo_i_even` - half of what `liveFrameSub` supplies -
is all those points use.  At the mirror row, the uncleared-`v` row and the second-power row both
coordinates are read and the full evenness is genuinely needed.**  The wave-58 killing point is
in the second group, and it fails precisely because its achievable set is odd in the coordinate
its `v`-covector reads.

## PROVED versus carried versus measured

**PROVED**, with no live hypothesis: the pairing and its additivity; both sufficient conditions;
the forcing at the pairing hypothesis and the wave-58 forcing as its corollary; the kill from an
odd pairing at an arbitrary gauge marking; the characterisation; both new points end to end at
every handle count, every ordered pair of handles and arbitrary handle letters, with the
orthogonal point's hom, pivot anchor, Eichler-cleared letters, frame identification and
non-vacuity; the corrected headline.

**Carried, and named**: the standing achievability convention of `GradedGammaTwo`, in exactly
the places wave 58 carries it - `SigmaForces` quantifies handle moves over
`GradedFourRow.rowGaTwoOf` of the marking's image.  §5's forcing does **not** carry it.

**Measured, not proved** (`scripts/w59_invariant/results/`): the census, which is what found the
answer before it was proved.  Over **`6932`** relator-killing two-live markings in four families
- `4096` exhaustive over `0/1` letters, `2000` uniform `ν'`-trivial ones, `324` crossings of the
campaign's own catalogue letters and `512` sweeping the pairing's own coordinates - the sharp
criterion and an independent kill search agree at **every single marking**, `0` disagreements;
`4357` of them break the forcing and `2029` sit **outside `liveFrameSub` with the forcing
holding**, of which `1252` are outside **both** sufficient conditions.  No marking inside
`liveFrameSub` ever breaks.  Kill counts at the headline points: `67108864` of `536870912`
achievable refinements kill the odd dressing at the wave-58 point (the lane's own figure,
reproduced), `0` of `536870912` at the mixed point and `0` of `33554432` at the orthogonal one,
where even `0` of `8589934592` **unrestricted** `γ₃`-moves kill - against `1073741824` at every
other point of the catalogue.  The subgroup engine is an induced polycyclic generating sequence,
validated element by element against a full orbit enumeration of the same subgroup, and it
reproduces wave 58's `|[K,K]| = 512` at the two-live point.  Every claim of this file is mirrored
numerically at `h = 1, 2, 3, 4`, every handle and every ordered handle pair: **`460090` checks in
the derivation, `128` named checks plus the `6932`-marking census in the sweep, `245697` in the
instance mirror, zero mismatches anywhere.**

## What this does NOT do

* The characterisation's converse half needs an odd-character `ν'`-trivial dressing with a
  **central** residue.  Every point of the catalogue supplies one and the swap family supplies
  it uniformly (`sqRelWord_mixWit_U`), but it is a hypothesis, not a theorem.
* The two new points are at the **cleared** row and use the two-live swap construction.  A point
  outside the frame invariant at a **displaced** row is not built, and §6's rule of thumb about
  the displaced rows is a reading of the covectors, not a theorem.
* Nothing here revisits `GradedFourTwoLive`'s own theorems, all of which stand.  What is
  corrected is a **composite**: the step from "these two live blocks outside the invariant break
  the forcing" to "two live blocks outside the invariant break the forcing".
* Nothing here makes the handle block visible; §1 of `GradedFourTwoLive` still says it cannot
  be, at class four, at any number of live handles.

## Contents

* **1** ⭐⭐⭐ the increment pairing, its additivity, and the two sufficient conditions;
* **2** ⭐⭐⭐ the forcing at the pairing hypothesis, and wave 58's as a corollary;
* **3** ⭐⭐⭐ the converse: an odd pairing always kills;
* **4** ⭐⭐⭐ `SigmaForces`, `FrameOrth`, and the characterisation;
* **5** ⭐⭐⭐ the orthogonal point, end to end, with no achievability;
* **6** ⭐⭐⭐ `halfFrameSub` and the mixed point, where achievability is load-bearing;
* **7** ⭐⭐⭐ the wave-58 headline corrected;
* **8** axiom pins.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`; every `decide` is on `ZMod 8`, `ZMod 2` or tuples
over them.  All **87** committed prints are **std-3** (`propext`, `Classical.choice`,
`Quot.sound`) or a subset (`60` std-3, `27` `propext` + `Quot.sound`); no census axiom is
reachable, `sqPivotExp` included.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The increment pairing -/

section Pairing

variable {R : Type} [CommRing R] {h : ℕ} {j : Fin h} {z₃ z₄ : SqU5 R}

/-- ⭐⭐⭐ **THE INCREMENT PAIRING.**  The handle part of the five-slot increment of
`GradedSigmaFour.sqRelWord_sigLift`: the two handle moves' class-three coordinates paired
against the two handle slots' **outer abelian columns**.  Over the committed `x₀`-gauge this
is the whole of the increment modulo `2`, and it is therefore the only thing the class-four
sigma forcing can possibly depend on. -/
def sigIncrPair {h : ℕ} (m : Fin (sqRank h) → SqU5 R) (j : Fin h) (z₃ z₄ : SqU5 R) : R :=
  (z₃.h * (m (sqHandleIdxV j)).d - z₃.i * (m (sqHandleIdxV j)).a)
    + ((m (sqHandleIdxU j)).a * z₄.i - (m (sqHandleIdxU j)).d * z₄.h)

variable {m : Fin (sqRank h) → SqU5 R}

/-- The pairing is additive in its two arguments, so a joint condition on the pair is the
conjunction of two separate conditions. -/
theorem sigIncrPair_eq_add :
    sigIncrPair m j z₃ z₄ = sigIncrPair m j z₃ 1 + sigIncrPair m j 1 z₄ := by
  simp only [sigIncrPair, SqU5.one_h, SqU5.one_i]
  ring

/-- ⭐⭐ **The first sufficient condition, which is what `liveFrameSub` supplies**: if the two
handle moves have even class-three coordinates then the pairing is even, whatever the handle
slots are.  This is the hypothesis `GradedFourTwoLive.gaugeX_increment_even` consumes. -/
theorem sigIncrPair_even_of_gaThree_even
    (h₃ : (∃ a : R, z₃.h = 2 * a) ∧ (∃ b : R, z₃.i = 2 * b))
    (h₄ : (∃ a : R, z₄.h = 2 * a) ∧ (∃ b : R, z₄.i = 2 * b)) :
    ∃ k : R, sigIncrPair m j z₃ z₄ = 2 * k := by
  obtain ⟨⟨a₃, ha₃⟩, b₃, hb₃⟩ := h₃
  obtain ⟨⟨a₄, ha₄⟩, b₄, hb₄⟩ := h₄
  refine ⟨(a₃ * (m (sqHandleIdxV j)).d - b₃ * (m (sqHandleIdxV j)).a)
    + ((m (sqHandleIdxU j)).a * b₄ - (m (sqHandleIdxU j)).d * a₄), ?_⟩
  simp only [sigIncrPair, ha₃, hb₃, ha₄, hb₄]
  ring

/-- ⭐⭐⭐ **The second sufficient condition, which no wave has used**: if the two handle slots
have even outer abelian columns then the pairing is even, whatever the handle moves are.  This
is **dual** to the first and neither implies the other; §4 builds a point where this one holds
and the first fails. -/
theorem sigIncrPair_even_of_handle_even
    (hUa : ∃ k : R, (m (sqHandleIdxU j)).a = 2 * k)
    (hUd : ∃ k : R, (m (sqHandleIdxU j)).d = 2 * k)
    (hVa : ∃ k : R, (m (sqHandleIdxV j)).a = 2 * k)
    (hVd : ∃ k : R, (m (sqHandleIdxV j)).d = 2 * k) :
    ∃ k : R, sigIncrPair m j z₃ z₄ = 2 * k := by
  obtain ⟨ua, hua⟩ := hUa
  obtain ⟨ud, hud⟩ := hUd
  obtain ⟨va, hva⟩ := hVa
  obtain ⟨vd, hvd⟩ := hVd
  refine ⟨(z₃.h * vd - z₃.i * va) + (ua * z₄.i - ud * z₄.h), ?_⟩
  simp only [sigIncrPair, hua, hud, hva, hvd]
  ring

end Pairing

/-! ## 2 The forcing at the sharpest hypothesis -/

section SharpForcing

variable {h : ℕ} {j : Fin h} {m : Fin (sqRank h) → SqU5 gr3R} {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R}

/-- ⭐⭐ **The five-slot increment is even as soon as the PAIRING is**, at any marking over the
committed `x₀`-gauge.  The `z₀`-term reads the `x₀`-slot's columns `(d, a) = (0, 2)` and the two
exponent terms are `-4·w₁.j + 2·w₂.j`; all three are even for free, and the pairing is the whole
remainder.  `GradedFourTwoLive.gaugeX_increment_even` is the special case in which the pairing
is even because each of its four terms is. -/
theorem gaugeX_increment_even_of_pair (hm1 : m 1 = sigFourX)
    (hp : ∃ k : gr3R, sigIncrPair m j z₃ z₄ = 2 * k) :
    ∃ k : gr3R, (z₀.h * (m 1).d - z₀.i * (m 1).a) + (-4 * w₁.j + 2 * w₂.j)
        + ((z₃.h * (m (sqHandleIdxV j)).d - z₃.i * (m (sqHandleIdxV j)).a)
          + ((m (sqHandleIdxU j)).a * z₄.i - (m (sqHandleIdxU j)).d * z₄.h)) = 2 * k := by
  obtain ⟨p, hpp⟩ := hp
  simp only [sigIncrPair] at hpp
  refine ⟨-z₀.i - 2 * w₁.j + w₂.j + p, ?_⟩
  rw [hm1, show (sigFourX.a : gr3R) = 2 from rfl, show (sigFourX.d : gr3R) = 0 from rfl]
  linear_combination hpp

/-- ⭐⭐⭐ **THE FORCING, at the sharpest hypothesis the tree can state.**  At any marking whose
sigma- and `x₀`-slots are the committed ones, whose `x₁`-slot has vanishing outer columns and
whose relator vanishes, a `ν'`-trivial sigma dressing whose frame is killed by a five-slot
class-four refinement **whose handle moves pair evenly against the handle slots** has an even
`chi_a`-character.

This subsumes `GradedFourTwoLive.gaugeX_sigma_forced`, whose hypothesis - both handle moves even
in both class-three coordinates - implies the pairing hypothesis by
`sigIncrPair_even_of_gaThree_even` and is strictly stronger: §4 and §5 exhibit markings where
the pairing hypothesis holds for **every** achievable move and the evenness hypothesis holds for
none. -/
theorem gaugeX_sigma_forced_pair (hm0 : m 0 = sigFourMark gr3R) (hm1 : m 1 = sigFourX)
    (hya : (m 2).a = 0) (hyb : (m 2).b = 0) (hyc : (m 2).c = 0) (hyd : (m 2).d = 0)
    (hrel : sqRelWord m = 1) (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (hp : ∃ k : gr3R, sigIncrPair m j z₃ z₄ = 2 * k)
    (hkill : sqRelWord (sigLift j (sigFourDress m v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 := by
  have hd1 : sigFourDress m v 1 = m 1 := sigFourDress_ne (by rw [sqVal_one]; omega)
  have hdU : sigFourDress m v (sqHandleIdxU j) = m (sqHandleIdxU j) :=
    sigFourDress_ne (by rw [sqHandleIdxU_val]; omega)
  have hdV : sigFourDress m v (sqHandleIdxV j) = m (sqHandleIdxV j) :=
    sigFourDress_ne (by rw [sqHandleIdxV_val]; omega)
  rw [sqRelWord_sigLift hz₀ hw₁ hw₂ hz₃ hz₄, hd1, hdU, hdV] at hkill
  obtain ⟨k, hk⟩ := gaugeX_increment_even_of_pair (m := m) (j := j) (z₀ := z₀) (w₁ := w₁)
    (w₂ := w₂) hm1 hp
  rw [hk, mul_liftC_apply] at hkill
  have hjj := congrArg SqU5.j hkill
  simp only [SqU5.one_j] at hjj
  have hp := congrArg selPar hjj
  rw [selPar_add, selPar_two_mul, add_zero,
    sqRelWord_gaugeX_sigma_bit_of_rel hm0 hm1 hya hyb hyc hyd hvb hrel] at hp
  exact hp

/-- The wave-58 forcing is the special case, recorded so that the strengthening is visible in
one line: its hypothesis feeds `sigIncrPair_even_of_gaThree_even`. -/
theorem gaugeX_sigma_forced_of_gaThree_even (hm0 : m 0 = sigFourMark gr3R) (hm1 : m 1 = sigFourX)
    (hya : (m 2).a = 0) (hyb : (m 2).b = 0) (hyc : (m 2).c = 0) (hyd : (m 2).d = 0)
    (hrel : sqRelWord m = 1) (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (h₃ : (∃ a : gr3R, z₃.h = 2 * a) ∧ (∃ b : gr3R, z₃.i = 2 * b))
    (h₄ : (∃ a : gr3R, z₄.h = 2 * a) ∧ (∃ b : gr3R, z₄.i = 2 * b))
    (hkill : sqRelWord (sigLift j (sigFourDress m v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  gaugeX_sigma_forced_pair hm0 hm1 hya hyb hyc hyd hrel hvb hz₀ hw₁ hw₂ hz₃ hz₄
    (sigIncrPair_even_of_gaThree_even h₃ h₄) hkill

end SharpForcing

/-! ## 3 The converse: an odd pairing kills -/

section Converse

variable {h : ℕ} {j : Fin h} {m : Fin (sqRank h) → SqU5 gr3R} {v z₃ z₄ : SqU5 gr3R}

/-- ⭐⭐⭐ **AN ODD PAIRING PRODUCES A KILL.**  At any marking over the committed `x₀`-gauge
whose sigma dressing leaves a **central** residue `liftC c`, and any two `γ₃`-shaped handle
moves whose pairing satisfies `c + pair = 2·t`, the five-slot refinement with trivial sigma and
first-exponent moves and second-exponent move `liftC (-t)` **kills the relator**.

Nothing is assumed about the handle block, the frame invariants or achievability: the even part
of the increment is fully tunable by the class-four exponent slot, so the pairing's parity is
the only obstruction to a kill. -/
theorem gaugeX_kill_of_pair (hm1 : m 1 = sigFourX) {c t : gr3R}
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (hres : sqRelWord (sigFourDress m v) = liftC c)
    (ht : c + sigIncrPair m j z₃ z₄ = 2 * t) :
    sqRelWord (sigLift j (sigFourDress m v) 1 1 (liftC (-t)) z₃ z₄) = 1 := by
  have hd1 : sigFourDress m v 1 = m 1 := sigFourDress_ne (by rw [sqVal_one]; omega)
  have hdU : sigFourDress m v (sqHandleIdxU j) = m (sqHandleIdxU j) :=
    sigFourDress_ne (by rw [sqHandleIdxU_val]; omega)
  have hdV : sigFourDress m v (sqHandleIdxV j) = m (sqHandleIdxV j) :=
    sigFourDress_ne (by rw [sqHandleIdxV_val]; omega)
  simp only [sigIncrPair] at ht
  rw [sqRelWord_sigLift SqU5.isGaThree_one SqU5.isGaFour_one (liftC_isGaFour (-t)) hz₃ hz₄,
    hd1, hdU, hdV, hres, liftC_mul_liftC, hm1]
  refine Eq.trans (congrArg liftC ?_) liftC_zero
  simp only [SqU5.one_h, SqU5.one_i, SqU5.one_j, liftC_j,
    show (sigFourX.a : gr3R) = 2 from rfl, show (sigFourX.d : gr3R) = 0 from rfl]
  linear_combination ht

/-- ⭐⭐ **The residue of an odd dressing is odd**, at any relator-killing marking over the
gauge: `GradedFourTwoLive.sqRelWord_gaugeX_sigma_bit_of_rel` read on a central residue. -/
theorem selPar_res_of_odd (hm0 : m 0 = sigFourMark gr3R) (hm1 : m 1 = sigFourX)
    (hya : (m 2).a = 0) (hyb : (m 2).b = 0) (hyc : (m 2).c = 0) (hyd : (m 2).d = 0)
    (hrel : sqRelWord m = 1) (hvb : v.b = 0) {c : gr3R}
    (hres : sqRelWord (sigFourDress m v) = liftC c) :
    selPar c = selPar v.a := by
  have := sqRelWord_gaugeX_sigma_bit_of_rel hm0 hm1 hya hyb hyc hyd hvb hrel
  rwa [hres, liftC_j] at this

/-- ⭐⭐⭐ **THE FORCING FAILS WHENEVER THE PAIRING IS ODD.**  At a relator-killing marking over
the gauge with an odd-character `ν'`-trivial dressing whose residue is central, any two
`γ₃`-shaped handle moves with **odd** pairing give an explicit five-slot refinement killing the
relator at that dressing.  This is the general form of `GradedFourTwoLive.twoLiveOdd_kill`, and
with §2 it makes the pairing the sharp line. -/
theorem gaugeX_kill_of_pair_odd (hm0 : m 0 = sigFourMark gr3R) (hm1 : m 1 = sigFourX)
    (hya : (m 2).a = 0) (hyb : (m 2).b = 0) (hyc : (m 2).c = 0) (hyd : (m 2).d = 0)
    (hrel : sqRelWord m = 1) (hvb : v.b = 0) (hva : selPar v.a = 1) {c : gr3R}
    (hres : sqRelWord (sigFourDress m v) = liftC c)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (hodd : ¬ ∃ k : gr3R, sigIncrPair m j z₃ z₄ = 2 * k) :
    ∃ w₂ : SqU5 gr3R, w₂.IsGaFour ∧
      sqRelWord (sigLift j (sigFourDress m v) 1 1 w₂ z₃ z₄) = 1 := by
  have hc : selPar c = 1 := by
    rw [selPar_res_of_odd hm0 hm1 hya hyb hyc hyd hrel hvb hres, hva]
  have hpodd : selPar (sigIncrPair m j z₃ z₄) = 1 :=
    (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _
      (fun h0 => hodd ((selPar_eq_zero_iff _).mp h0))
  obtain ⟨t, ht⟩ := (selPar_eq_zero_iff (c + sigIncrPair m j z₃ z₄)).mp
    (by rw [selPar_add, hc, hpodd]; decide)
  exact ⟨liftC (-t), liftC_isGaFour _, gaugeX_kill_of_pair hm1 hz₃ hz₄ hres ht⟩

end Converse

/-! ## 4 The two properties, and the characterisation -/

section Characterisation

variable {h : ℕ} {j : Fin h} {m : Fin (sqRank h) → SqU5 gr3R}

/-- **The class-four sigma forcing at a marking**, in exactly the shape
`GradedFourTwoLive.twoLiveOdd_sigma_forced_false` negates: every `ν'`-trivial sigma dressing
whose frame is killed by an achievable five-slot class-four refinement has an even
`chi_a`-character. -/
def SigmaForces {h : ℕ} (m : Fin (sqRank h) → SqU5 gr3R) (j : Fin h) : Prop :=
  ∀ v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R, v.b = 0 → z₀.IsGaThree → w₁.IsGaFour → w₂.IsGaFour →
    z₃.IsGaThree → z₄.IsGaThree →
    z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range m)) →
    z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range m)) →
    sqRelWord (sigLift j (sigFourDress m v) z₀ w₁ w₂ z₃ z₄) = 1 → selPar v.a = 0

/-- ⭐⭐⭐ **THE SHARP INVARIANT.**  Both mod-`2` covectors `(V.d, V.a)` and `(U.d, U.a)` of the
two handle slots annihilate the class-three parity image of `γ₂` of the marking's image: every
achievable `γ₃`-shaped handle move pairs **evenly** against the handle slots' outer abelian
columns.

`GradedFourCleared.liveFrameSub` implies this by killing the *left* factor of every pairing
(`frameOrth_of_le_liveFrameSub`); even handle columns imply it by killing the *right*
(`frameOrth_of_handle_even`); and §5-§6 show that neither is necessary. -/
def FrameOrth {h : ℕ} (m : Fin (sqRank h) → SqU5 gr3R) (j : Fin h) : Prop :=
  ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range m)), z.IsGaThree →
    (∃ k : gr3R, sigIncrPair m j z 1 = 2 * k) ∧ (∃ k : gr3R, sigIncrPair m j 1 z = 2 * k)

/-- The invariant gives the pairing hypothesis of `gaugeX_sigma_forced_pair` on any achievable
pair, by additivity. -/
theorem FrameOrth.pair (hO : FrameOrth m j) {z₃ z₄ : SqU5 gr3R}
    (h₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range m))) (hz₃ : z₃.IsGaThree)
    (h₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range m))) (hz₄ : z₄.IsGaThree) :
    ∃ k : gr3R, sigIncrPair m j z₃ z₄ = 2 * k := by
  obtain ⟨k₃, hk₃⟩ := (hO z₃ h₃ hz₃).1
  obtain ⟨k₄, hk₄⟩ := (hO z₄ h₄ hz₄).2
  exact ⟨k₃ + k₄, by rw [sigIncrPair_eq_add, hk₃, hk₄]; ring⟩

/-- ⭐⭐ **The carried hypothesis is SUFFICIENT.**  A marking whose image lies in
`GradedFourCleared.liveFrameSub` satisfies the sharp invariant, because there every achievable
move is even in both class-three coordinates. -/
theorem frameOrth_of_le_liveFrameSub
    (hle : Subgroup.closure (Set.range m) ≤ liveFrameSub gr3R) : FrameOrth m j := by
  have hone : (∃ a : gr3R, (1 : SqU5 gr3R).h = 2 * a) ∧ ∃ b : gr3R, (1 : SqU5 gr3R).i = 2 * b :=
    ⟨⟨0, by rw [SqU5.one_h]; ring⟩, 0, by rw [SqU5.one_i]; ring⟩
  intro z hz _
  have hcomm : rowGaTwoOf (Subgroup.closure (Set.range m)) ≤ liveGaTwoSub gr3R := by
    rw [rowGaTwoOf, Subgroup.closure_le]
    rintro w ⟨p, hp, q, hq, rfl⟩
    exact commP_mem_liveGaTwoSub (hle hp) (hle hq)
  obtain ⟨-, -, -, -, -, -, hh, hi⟩ := hcomm hz
  exact ⟨sigIncrPair_even_of_gaThree_even ⟨hh, hi⟩ hone,
    sigIncrPair_even_of_gaThree_even hone ⟨hh, hi⟩⟩

/-- ⭐⭐⭐ **A second, DUAL sufficient condition, which no wave has used.**  A marking whose two
handle slots have even outer abelian columns satisfies the sharp invariant whatever its
achievable set is - the frame invariants are not consulted at all. -/
theorem frameOrth_of_handle_even
    (hUa : ∃ k : gr3R, (m (sqHandleIdxU j)).a = 2 * k)
    (hUd : ∃ k : gr3R, (m (sqHandleIdxU j)).d = 2 * k)
    (hVa : ∃ k : gr3R, (m (sqHandleIdxV j)).a = 2 * k)
    (hVd : ∃ k : gr3R, (m (sqHandleIdxV j)).d = 2 * k) : FrameOrth m j :=
  fun _ _ _ => ⟨sigIncrPair_even_of_handle_even hUa hUd hVa hVd,
    sigIncrPair_even_of_handle_even hUa hUd hVa hVd⟩

/-- ⭐⭐⭐ **HALF the carried hypothesis is enough whenever both handle slots have an even
fourth abelian column.**  Then both covectors read only the **second** class-three coordinate of
an achievable move, so `liveFrameSub`'s control of the first is spare.  This covers the cleared
row, the live point, the two-live point and the doubly displaced row; §6's mixed point is the
case where it is the whole of the argument. -/
theorem frameOrth_of_gaTwo_i_even
    (hUd : ∃ k : gr3R, (m (sqHandleIdxU j)).d = 2 * k)
    (hVd : ∃ k : gr3R, (m (sqHandleIdxV j)).d = 2 * k)
    (hi : ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range m)), z.IsGaThree →
      ∃ k : gr3R, z.i = 2 * k) : FrameOrth m j := by
  obtain ⟨ud, hud⟩ := hUd
  obtain ⟨vd, hvd⟩ := hVd
  intro z hz hz3
  obtain ⟨kz, hkz⟩ := hi z hz hz3
  refine ⟨⟨z.h * vd - kz * (m (sqHandleIdxV j)).a, ?_⟩,
    ⟨(m (sqHandleIdxU j)).a * kz - ud * z.h, ?_⟩⟩ <;>
    simp only [sigIncrPair, hud, hvd, hkz, SqU5.one_h, SqU5.one_i] <;>
    ring

/-- ⭐⭐⭐ **THE INVARIANT SUFFICES.**  At any relator-killing marking over the committed gauge,
the sharp invariant gives the whole forcing. -/
theorem sigmaForces_of_frameOrth (hm0 : m 0 = sigFourMark gr3R) (hm1 : m 1 = sigFourX)
    (hya : (m 2).a = 0) (hyb : (m 2).b = 0) (hyc : (m 2).c = 0) (hyd : (m 2).d = 0)
    (hrel : sqRelWord m = 1) (hO : FrameOrth m j) : SigmaForces m j :=
  fun _ _ _ _ _ _ hvb hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄ hkill =>
    gaugeX_sigma_forced_pair hm0 hm1 hya hyb hyc hyd hrel hvb hz₀ hw₁ hw₂ hz₃ hz₄
      (hO.pair l₃ hz₃ l₄ hz₄) hkill

/-- ⭐⭐⭐ **THE INVARIANT IS NECESSARY.**  At a relator-killing marking over the gauge which
admits **one** odd-character `ν'`-trivial dressing with central residue - the escape datum every
point of the catalogue already proves - the forcing implies the sharp invariant: an achievable
`γ₃`-shaped move failing either orthogonality gives an explicit refinement killing the relator
at that dressing. -/
theorem frameOrth_of_sigmaForces (hm0 : m 0 = sigFourMark gr3R) (hm1 : m 1 = sigFourX)
    (hya : (m 2).a = 0) (hyb : (m 2).b = 0) (hyc : (m 2).c = 0) (hyd : (m 2).d = 0)
    (hrel : sqRelWord m = 1) {v : SqU5 gr3R} {c : gr3R} (hvb : v.b = 0) (hva : selPar v.a = 1)
    (hres : sqRelWord (sigFourDress m v) = liftC c) (hF : SigmaForces m j) : FrameOrth m j := by
  intro z hz hz3
  constructor
  · by_contra hodd
    obtain ⟨w₂, hw₂, hkill⟩ := gaugeX_kill_of_pair_odd (j := j) (z₃ := z) (z₄ := 1)
      hm0 hm1 hya hyb hyc hyd hrel hvb hva hres hz3 SqU5.isGaThree_one hodd
    have hcon := hF v 1 1 w₂ z 1 hvb SqU5.isGaThree_one SqU5.isGaFour_one hw₂ hz3
      SqU5.isGaThree_one hz (one_mem _) hkill
    rw [hva] at hcon
    exact absurd hcon (by decide)
  · by_contra hodd
    obtain ⟨w₂, hw₂, hkill⟩ := gaugeX_kill_of_pair_odd (j := j) (z₃ := 1) (z₄ := z)
      hm0 hm1 hya hyb hyc hyd hrel hvb hva hres SqU5.isGaThree_one hz3 hodd
    have hcon := hF v 1 1 w₂ 1 z hvb SqU5.isGaThree_one SqU5.isGaFour_one hw₂
      SqU5.isGaThree_one hz3 (one_mem _) hz hkill
    rw [hva] at hcon
    exact absurd hcon (by decide)

/-- ⭐⭐⭐ **THE CHARACTERISATION.**  At a relator-killing marking over the committed gauge with
one odd-character `ν'`-trivial dressing of central residue, the class-four sigma forcing holds
**exactly** when the sharp invariant does.  So `liveFrameSub` is not the line: it is one
sufficient condition among several, and this is the line. -/
theorem sigmaForces_iff_frameOrth (hm0 : m 0 = sigFourMark gr3R) (hm1 : m 1 = sigFourX)
    (hya : (m 2).a = 0) (hyb : (m 2).b = 0) (hyc : (m 2).c = 0) (hyd : (m 2).d = 0)
    (hrel : sqRelWord m = 1) {v : SqU5 gr3R} {c : gr3R} (hvb : v.b = 0) (hva : selPar v.a = 1)
    (hres : sqRelWord (sigFourDress m v) = liftC c) :
    SigmaForces m j ↔ FrameOrth m j :=
  ⟨frameOrth_of_sigmaForces hm0 hm1 hya hyb hyc hyd hrel hvb hva hres,
    sigmaForces_of_frameOrth hm0 hm1 hya hyb hyc hyd hrel⟩

end Characterisation

/-! ## 5 A marking far OUTSIDE the frame invariant at which the forcing HOLDS -/

section OrthPoint

variable {h : ℕ} {j₁ j₂ : Fin h}

/-- ⭐⭐⭐ **The orthogonal point's `u`-letter**: the first class-two coordinate alone. -/
def orthU : SqU5 gr3R := ⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩

/-- ⭐⭐⭐ **...and its `v`-letter**, whose **third abelian column is `1`**.  That column is the
first of `GradedFourCleared.liveFrameSub`'s three invariants, and it is the one
`GradedFourTwoLive.commP_coupling_ne_zero_imp` calls unavailable to any point the forcing can be
run at.  It is available here. -/
def orthV : SqU5 gr3R := ⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩

/-- ⭐⭐⭐ **The block is the SAME element as the wave-58 killing point's**: the class-three
element with first coordinate `1`, ODD. -/
theorem commP_orth : commP orthU orthV = (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩ : SqU5 gr3R) := by decide

theorem commP_orth_eq_oddLive : commP orthU orthV = commP sigFourU oddLiveV := by decide

theorem commP_orth_ne_one : commP orthU orthV ≠ 1 := by decide

theorem commP_orth_isGaThree : (commP orthU orthV).IsGaThree := by
  rw [commP_orth]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⭐⭐ …and the cross-handle coupling still vanishes, although the `c`-column that
`GradedFourTwoLive.commP_coupling_ne_zero_imp` says is needed to realise it is present.  A
nonzero `c`-column is necessary for the coupling, not sufficient. -/
theorem commP_orth_g : (commP orthV orthU).g = 0 := by decide

/-- ⭐⭐⭐ **The `v`-letter is outside the carried frame invariant.** -/
theorem orthV_not_mem_liveFrameSub : orthV ∉ liveFrameSub gr3R := by
  intro hc
  exact absurd hc.1 (by decide)

/-- ⭐⭐⭐ **The block is ODD**, so no evenness the campaign has ever carried holds here. -/
theorem orth_block_odd : ¬ ∃ k : gr3R, (commP orthU orthV).h = 2 * k := by decide

/-- ⭐⭐⭐ **BOTH handle covectors vanish**: the two handle slots have even - indeed zero -
outer abelian columns, which is the second sufficient condition of §4. -/
theorem orth_handle_even :
    (∃ k : gr3R, orthU.a = 2 * k) ∧ (∃ k : gr3R, orthU.d = 2 * k) ∧
      (∃ k : gr3R, orthV.a = 2 * k) ∧ ∃ k : gr3R, orthV.d = 2 * k :=
  ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, 0, by decide⟩

/-- ⭐⭐⭐ **THE PAIRING VANISHES IDENTICALLY** at the orthogonal point: for **arbitrary**
`γ₃`-shaped handle moves, achievable or not. -/
theorem orth_pair_eq_zero (z₃ z₄ : SqU5 gr3R) :
    sigIncrPair (twoLiveMark h j₁ j₂ orthU orthV) j₁ z₃ z₄ = 0 := by
  simp only [sigIncrPair, twoLiveMark_handleU_one, twoLiveMark_handleV_one,
    show orthU.a = (0 : gr3R) from rfl, show orthU.d = (0 : gr3R) from rfl,
    show orthV.a = (0 : gr3R) from rfl, show orthV.d = (0 : gr3R) from rfl]
  ring

theorem orth_pair_even (z₃ z₄ : SqU5 gr3R) :
    ∃ k : gr3R, sigIncrPair (twoLiveMark h j₁ j₂ orthU orthV) j₁ z₃ z₄ = 2 * k :=
  ⟨0, by rw [orth_pair_eq_zero]; ring⟩

/-- ⭐⭐⭐ **THE FORCING HOLDS AT THE ORTHOGONAL POINT, WITH NO ACHIEVABILITY HYPOTHESIS.**  At
every handle count, every ordered pair of handles, every `ν'`-trivial sigma dressing and **every**
`γ₃`-shaped five-slot refinement - not merely the achievable ones - a killed relator forces an
even `chi_a`-character.  Both live blocks sit outside `liveFrameSub` and are odd in class three;
neither can touch the forcing, because the handle slots they sit in read them evenly. -/
theorem orth_sigma_forced {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree) (hlt : (j₁ : ℕ) < (j₂ : ℕ))
    (hkill : sqRelWord (sigLift j₁ (sigFourDress (twoLiveMark h j₁ j₂ orthU orthV) v)
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  gaugeX_sigma_forced_pair twoLiveMark_zero twoLiveMark_one
    (by rw [twoLiveMark_two]; decide) (by rw [twoLiveMark_two]; decide)
    (by rw [twoLiveMark_two]; decide) (by rw [twoLiveMark_two]; decide)
    (sqRelWord_twoLiveMark hlt) hvb hz₀ hw₁ hw₂ hz₃ hz₄ (orth_pair_even z₃ z₄) hkill

/-- ⭐⭐⭐ **…hence the forcing's own shape holds there**, and the marking satisfies the sharp
invariant. -/
theorem orth_frameOrth : FrameOrth (twoLiveMark h j₁ j₂ orthU orthV) j₁ :=
  fun _ _ _ => ⟨orth_pair_even _ _, orth_pair_even _ _⟩

theorem orth_sigmaForces (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    SigmaForces (twoLiveMark h j₁ j₂ orthU orthV) j₁ :=
  fun _ _ _ _ _ _ hvb hz₀ hw₁ hw₂ hz₃ hz₄ _ _ hkill =>
    orth_sigma_forced hvb hz₀ hw₁ hw₂ hz₃ hz₄ hlt hkill

/-- ⭐⭐⭐ **…and the carried hypothesis FAILS there.**  The marking's image does not lie in
`GradedFourCleared.liveFrameSub`. -/
theorem orth_not_le_liveFrameSub :
    ¬ Subgroup.closure (Set.range (twoLiveMark h j₁ j₂ orthU orthV)) ≤ liveFrameSub gr3R :=
  fun hle => orthV_not_mem_liveFrameSub
    (hle (Subgroup.subset_closure ⟨sqHandleIdxV j₁, twoLiveMark_handleV_one⟩))

/-- The block is achievable, so it is a legal `γ₂`-level handle move. -/
theorem commP_orth_mem_gaTwoOf :
    commP orthU orthV
      ∈ rowGaTwoOf (Subgroup.closure (Set.range (twoLiveMark h j₁ j₂ orthU orthV))) :=
  Subgroup.subset_closure ⟨orthU, Subgroup.subset_closure ⟨sqHandleIdxU j₁,
    twoLiveMark_handleU_one⟩, orthV, Subgroup.subset_closure ⟨sqHandleIdxV j₁,
    twoLiveMark_handleV_one⟩, rfl⟩

/-- ⭐⭐⭐ **…and so does its CONSEQUENCE, the evenness the increment lemma consumes.**  The
achievable set contains an element with an odd first class-three coordinate, so
`GradedFourCleared.liveFour_gaTwo_even` and `GradedFourTwoLive.twoLive_gaTwo_even` are both
false here.  The forcing holds anyway. -/
theorem orth_not_gaTwo_even :
    ¬ ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range (twoLiveMark h j₁ j₂ orthU orthV))),
        (∃ a : gr3R, z.h = 2 * a) ∧ ∃ b : gr3R, z.i = 2 * b := by
  intro hall
  exact orth_block_odd (hall _ commP_orth_mem_gaTwoOf).1

/-- ⭐⭐⭐ **THE ANSWER, at one point.**  A marking with two live handle blocks, both odd in
class three, whose `v`-letter is outside `liveFrameSub` and whose achievable set is outside
`liveGaTwoSub` - and the class-four sigma forcing **holds** there. -/
theorem orth_separates (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    sqRelWord (twoLiveMark h j₁ j₂ orthU orthV) = 1 ∧
      commP orthU orthV ≠ 1 ∧ commP orthV orthU ≠ 1 ∧
      (¬ ∃ k : gr3R, (commP orthU orthV).h = 2 * k) ∧
      ¬ Subgroup.closure (Set.range (twoLiveMark h j₁ j₂ orthU orthV)) ≤ liveFrameSub gr3R ∧
      (¬ ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range (twoLiveMark h j₁ j₂ orthU orthV))),
        (∃ a : gr3R, z.h = 2 * a) ∧ ∃ b : gr3R, z.i = 2 * b) ∧
      SigmaForces (twoLiveMark h j₁ j₂ orthU orthV) j₁ :=
  ⟨sqRelWord_twoLiveMark hlt, commP_orth_ne_one, by decide, orth_block_odd,
    orth_not_le_liveFrameSub, orth_not_gaTwo_even, orth_sigmaForces hlt⟩

/-! ### The orthogonal point as a continuous homomorphism -/

variable (h j₁ j₂) in
/-- ⭐⭐⭐ **The orthogonal test hom**: an honest continuous homomorphism `D_sq h → U₅(ℤ/8)`
with two nontrivial handle commutators in its image, both odd in class three. -/
noncomputable def orthHom (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    ContinuousMonoidHom (DSq h : Type) (SqU5 gr3R) :=
  sqU5Hom gr3R_card h (twoLiveMark h j₁ j₂ orthU orthV) (sqRelWord_twoLiveMark hlt)

variable {hlt : (j₁ : ℕ) < (j₂ : ℕ)}

@[simp] theorem orthHom_gen (i : Fin (sqRank h)) :
    orthHom h j₁ j₂ hlt (sqGen h i) = twoLiveMark h j₁ j₂ orthU orthV i :=
  sqU5Hom_gen _ _ _ i

@[simp] theorem orthHom_sigma : orthHom h j₁ j₂ hlt (dsqSigma h) = sigFourMark gr3R := by
  rw [dsqSigma, orthHom_gen, twoLiveMark_zero]

@[simp] theorem orthHom_x0 : orthHom h j₁ j₂ hlt (dsqX0 h) = sigFourX := by
  rw [dsqX0, orthHom_gen, twoLiveMark_one]

@[simp] theorem orthHom_x1 : orthHom h j₁ j₂ hlt (dsqX1 h) = sigFourY := by
  rw [dsqX1, orthHom_gen, twoLiveMark_two]

theorem orthHom_sqPivot :
    orthHom h j₁ j₂ hlt (sqPivot h) = rowPivotVal (gr3Pi sqPivotExp) :=
  mirHom_sqPivot orthHom_sigma orthHom_x0

/-- ⭐⭐⭐ **Both handle commutators are live in the image.** -/
theorem orthHom_commP_ne_one :
    commP (orthHom h j₁ j₂ hlt (sqGen h (sqHandleIdxU j₁)))
        (orthHom h j₁ j₂ hlt (sqGen h (sqHandleIdxV j₁))) ≠ 1 ∧
      commP (orthHom h j₁ j₂ hlt (sqGen h (sqHandleIdxU j₂)))
        (orthHom h j₁ j₂ hlt (sqGen h (sqHandleIdxV j₂))) ≠ 1 := by
  have hne : (j₁ : ℕ) ≠ (j₂ : ℕ) := by omega
  refine ⟨?_, ?_⟩
  · rw [orthHom_gen, orthHom_gen, twoLiveMark_handleU_one, twoLiveMark_handleV_one]
    exact commP_orth_ne_one
  · rw [orthHom_gen, orthHom_gen, twoLiveMark_handleU_two hne, twoLiveMark_handleV_two hne]
    decide

theorem orthHom_sqEichU :
    orthHom h j₁ j₂ hlt (sqEichU h (nuSel h j₁ 0 0) j₁) = orthU := by
  rw [sqEichU_of_cleared nuSelClr_handleU, orthHom_gen, twoLiveMark_handleU_one]

theorem orthHom_sqEichV :
    orthHom h j₁ j₂ hlt (sqEichV h (nuSel h j₁ 0 0) j₁) = orthV := by
  rw [sqEichV_of_cleared nuSelClr_handleV, orthHom_gen, twoLiveMark_handleV_one]

theorem orthHom_b (x : (DSq h : Type)) :
    (orthHom h j₁ j₂ hlt x).b = gr3Pi (toAdd (nuSel h j₁ 0 0 x)) := by
  have hne : (j₁ : ℕ) ≠ (j₂ : ℕ) := by omega
  refine mirHom_b (by rw [orthHom_sigma]; rfl) (by rw [orthHom_x0]; rfl)
    (by rw [orthHom_x1]; rfl)
    (by rw [orthHom_gen, twoLiveMark_handleU_one, map_zero]; rfl)
    (by rw [orthHom_gen, twoLiveMark_handleV_one, map_zero]; rfl) (fun j' hj' => ?_) x
  by_cases h2 : j' = j₂
  · subst h2
    exact ⟨by rw [orthHom_gen, twoLiveMark_handleU_two hne]; rfl,
      by rw [orthHom_gen, twoLiveMark_handleV_two hne]; rfl⟩
  · exact ⟨by rw [orthHom_gen, twoLiveMark_handleU_ne hj' h2]; rfl,
      by rw [orthHom_gen, twoLiveMark_handleV_ne hj' h2]; rfl⟩

theorem orthHom_b_eq_zero {g : (DSq h : Type)} (hg : nuSel h j₁ 0 0 g = 1) :
    (orthHom h j₁ j₂ hlt g).b = 0 := by
  rw [orthHom_b, hg, toAdd_one, map_zero]

/-- ⭐⭐ **The frame identification at the orthogonal point.** -/
theorem orthHom_sqArbFrame (g : (DSq h : Type)) :
    (fun i => orthHom h j₁ j₂ hlt (sqArbFrame h (nuSel h j₁ 0 0) j₁ (sigArbDress h g) i))
      = sigFourDress (twoLiveMark h j₁ j₂ orthU orthV) (orthHom h j₁ j₂ hlt g) := by
  refine liveHom_sqArbFrame (m := twoLiveMark h j₁ j₂ orthU orthV)
    (by rw [orthHom_sigma, twoLiveMark_zero]) (by rw [orthHom_x0, twoLiveMark_one])
    (by rw [orthHom_x1, twoLiveMark_two])
    (by rw [orthHom_sqEichU, twoLiveMark_handleU_one])
    (by rw [orthHom_sqEichV, twoLiveMark_handleV_one]) (fun j' _ => ?_) g
  exact ⟨by rw [orthHom_gen], by rw [orthHom_gen]⟩

/-- ⭐⭐⭐ **THE HEADLINE AT THE ORTHOGONAL POINT.**  At an honest continuous homomorphism with
two nontrivial, class-three-ODD handle commutators in its image, whose `v`-letter is outside the
frame invariant, every `ν'`-trivial sigma dressing of the arbitrary-dressing frame killed by
**any** five-slot class-four refinement has an even `chi_a`-character.  No achievability, no
frame invariant, no lattice. -/
theorem sqArbFrame_sigma_forced_orth {g : (DSq h : Type)} (hg : nuSel h j₁ 0 0 g = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (hkill : sqRelWord (sigLift j₁
      (fun i => orthHom h j₁ j₂ hlt (sqArbFrame h (nuSel h j₁ 0 0) j₁ (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (orthHom h j₁ j₂ hlt g).a = 0 := by
  rw [orthHom_sqArbFrame g] at hkill
  exact orth_sigma_forced (orthHom_b_eq_zero hg) hz₀ hw₁ hw₂ hz₃ hz₄ hlt hkill

/-- ⭐⭐ **The forcing is not vacuous at the orthogonal point.** -/
theorem orth_forcing_nonvacuous (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    nuLam h (sqEichU h (nuSel h j₁ 0 0) j₁) = 1 ∧
      nuSel h j₁ 0 0 (sqEichU h (nuSel h j₁ 0 0) j₁) = 1 ∧
      sqRelWord (sigFourDress (twoLiveMark h j₁ j₂ orthU orthV) sigFourU) = liftC 1 ∧
      selPar sigFourU.a = 1 :=
  ⟨nuLam_clrEichU, nu_clrEichU, by
    rw [show sigFourDress (twoLiveMark h j₁ j₂ orthU orthV) sigFourU
      = twoLiveWit h j₁ j₂ orthU orthV sigFourU by rw [twoLiveWit_eq_dress, twoLiveWit_one],
      sqRelWord_twoLiveWit hlt]
    decide, by decide⟩

end OrthPoint

/-! ## 6 The MIXED point: outside both sufficient conditions, and still forced -/

section HalfFrame

variable {R : Type} [CommRing R]

variable (R) in
/-- ⭐⭐ **The half frame**: **even** fourth abelian column and **even** third class-two
coordinate.  This is `GradedFourRow`'s technique carried to a different pair of columns, and it
is **incomparable** with `GradedFourCleared.liveFrameSub`: that one constrains `c`, `f`, `g`,
this one `d`, `g`.  What it buys is the *second* class-three coordinate of every commutator,
which is the only one the `u`-covector `(U.d, U.a) = (0, 1)` reads. -/
def halfFrameSub : Subgroup (SqU5 R) where
  carrier := {p | (∃ k : R, p.d = 2 * k) ∧ ∃ k : R, p.g = 2 * k}
  mul_mem' := fun {p q} hp hq => by
    obtain ⟨⟨dp, hdp⟩, gp, hgp⟩ := hp
    obtain ⟨⟨dq, hdq⟩, gq, hgq⟩ := hq
    exact ⟨⟨dp + dq, by rw [SqU5.mul_d, hdp, hdq]; ring⟩,
      gp + gq + p.c * dq, by rw [SqU5.mul_g, hgp, hgq, hdq]; ring⟩
  one_mem' := ⟨⟨0, by rw [SqU5.one_d]; ring⟩, 0, by rw [SqU5.one_g]; ring⟩
  inv_mem' := fun {p} hp => by
    obtain ⟨⟨dp, hdp⟩, gp, hgp⟩ := hp
    exact ⟨⟨-dp, by rw [SqU5.inv_d, hdp]; ring⟩,
      p.c * dp - gp, by rw [SqU5.inv_g, hdp, hgp]; ring⟩

theorem mem_halfFrameSub {p : SqU5 R} :
    p ∈ halfFrameSub R ↔ (∃ k : R, p.d = 2 * k) ∧ ∃ k : R, p.g = 2 * k := Iff.rfl

variable (R) in
/-- The subgroup where every `γ₂`-level commutator of the half frame lands: the **second**
class-three coordinate is even, and nothing is claimed about the first. -/
def halfGaTwoSub : Subgroup (SqU5 R) where
  carrier := {p | (∃ k : R, p.d = 2 * k) ∧ (∃ k : R, p.g = 2 * k) ∧ ∃ k : R, p.i = 2 * k}
  mul_mem' := fun {p q} hp hq => by
    obtain ⟨⟨dp, hdp⟩, ⟨gp, hgp⟩, ip, hip⟩ := hp
    obtain ⟨⟨dq, hdq⟩, ⟨gq, hgq⟩, iq, hiq⟩ := hq
    exact ⟨⟨dp + dq, by rw [SqU5.mul_d, hdp, hdq]; ring⟩,
      ⟨gp + gq + p.c * dq, by rw [SqU5.mul_g, hgp, hgq, hdq]; ring⟩,
      ip + iq + p.b * gq + p.f * dq, by rw [SqU5.mul_i, hip, hiq, hgq, hdq]; ring⟩
  one_mem' := ⟨⟨0, by rw [SqU5.one_d]; ring⟩, ⟨0, by rw [SqU5.one_g]; ring⟩,
    0, by rw [SqU5.one_i]; ring⟩
  inv_mem' := fun {p} hp => by
    obtain ⟨⟨dp, hdp⟩, ⟨gp, hgp⟩, ip, hip⟩ := hp
    exact ⟨⟨-dp, by rw [SqU5.inv_d, hdp]; ring⟩,
      ⟨p.c * dp - gp, by rw [SqU5.inv_g, hdp, hgp]; ring⟩,
      -(p.b * p.c * dp) + p.b * gp + dp * p.f - ip, by rw [SqU5.inv_i, hdp, hgp, hip]; ring⟩

theorem mem_halfGaTwoSub {p : SqU5 R} :
    p ∈ halfGaTwoSub R ↔
      (∃ k : R, p.d = 2 * k) ∧ (∃ k : R, p.g = 2 * k) ∧ ∃ k : R, p.i = 2 * k := Iff.rfl

/-- ⭐⭐ **The one algebraic fact behind the mixed point's soundness**: a commutator of two
elements with even fourth abelian column and even third class-two coordinate has an **even
second class-three coordinate**.  Nothing is claimed about the first, and at the mixed point the
first is genuinely odd. -/
theorem commP_mem_halfGaTwoSub {p q : SqU5 R} (hp : p ∈ halfFrameSub R)
    (hq : q ∈ halfFrameSub R) : commP p q ∈ halfGaTwoSub R := by
  obtain ⟨⟨dp, hdp⟩, gp, hgp⟩ := hp
  obtain ⟨⟨dq, hdq⟩, gq, hgq⟩ := hq
  refine ⟨⟨0, ?_⟩, ⟨p.c * dq - dp * q.c, ?_⟩,
    ⟨p.b * gq - gp * q.b + p.f * dq - dp * q.f + p.b * dp * q.c - p.b * p.c * dq
      + dp * q.b * q.c - p.c * q.b * dq, ?_⟩⟩ <;>
    simp only [SqU5.commP_d, SqU5.commP_g, SqU5.commP_i, SqU5.u5Comm3R, hdp, hdq, hgp, hgq] <;>
    ring

end HalfFrame

section MixPoint

variable {h : ℕ} {j₁ j₂ : Fin h}

/-- ⭐⭐⭐ **The mixed point's `u`-letter is the COMMITTED one**, whose `chi_a`-character is odd,
so the `u`-covector `(U.d, U.a) = (0, 1)` does **not** vanish and the orthogonal point's route is
unavailable. -/
def mixU : SqU5 gr3R := ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- ⭐⭐⭐ **…and its `v`-letter has ODD second class-two coordinate**, so it is outside
`GradedFourCleared.liveFrameSub` exactly as `GradedFourTwoLive.oddLiveV` is - and its fourth
abelian column is `0` rather than `1`, which is the ONLY difference. -/
def mixV : SqU5 gr3R := ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩

theorem mixU_eq : mixU = sigFourU := rfl

/-- ⭐⭐⭐ **The mixed point differs from the wave-58 killing point in its COVECTOR only.**  The
two `v`-letters have the same odd second class-two coordinate - the one that puts them both
outside `liveFrameSub` - and even first abelian column; they differ exactly in the **fourth
abelian column**, which is not a frame invariant and which no wave has ever constrained. -/
theorem mixV_covector_vs_oddLiveV :
    mixV.f = oddLiveV.f ∧ selPar mixV.f = 1 ∧
      selPar mixV.a = 0 ∧ selPar oddLiveV.a = 0 ∧
      selPar mixV.d = 0 ∧ selPar oddLiveV.d = 1 := by decide

/-- ⭐⭐⭐ **The block is again the SAME odd element.** -/
theorem commP_mix : commP mixU mixV = (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩ : SqU5 gr3R) := by decide

theorem commP_mix_eq_oddLive : commP mixU mixV = commP sigFourU oddLiveV := by decide

theorem commP_mix_ne_one : commP mixU mixV ≠ 1 := by decide

theorem commP_mix_isGaThree : (commP mixU mixV).IsGaThree := by
  rw [commP_mix]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mix_block_odd : ¬ ∃ k : gr3R, (commP mixU mixV).h = 2 * k := by decide

/-- ⭐⭐⭐ **The `v`-letter is outside the carried frame invariant.** -/
theorem mixV_not_mem_liveFrameSub : mixV ∉ liveFrameSub gr3R := by
  intro hc
  obtain ⟨-, ⟨k, hk⟩, -⟩ := hc
  revert hk
  revert k
  decide

/-- ⭐⭐⭐ **…and the dual sufficient condition fails too**: the `u`-slot's first abelian column
is odd. -/
theorem mixU_chiA : selPar mixU.a = 1 := by decide

/-- Every slot of the mixed marking has even fourth abelian column and even third class-two
coordinate. -/
theorem mixMark_le_halfFrameSub (hne : (j₁ : ℕ) ≠ (j₂ : ℕ)) :
    Subgroup.closure (Set.range (twoLiveMark h j₁ j₂ mixU mixV)) ≤ halfFrameSub gr3R := by
  have hz : ∀ p : SqU5 gr3R, p.d = 0 → p.g = 0 → p ∈ halfFrameSub gr3R := fun p hd hg =>
    ⟨⟨0, by rw [hd]; ring⟩, 0, by rw [hg]; ring⟩
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [twoLiveMark_zero]; exact hz _ rfl rfl
  · rw [twoLiveMark_one]; exact hz _ rfl rfl
  · rw [twoLiveMark_two]
    exact ⟨⟨0, by decide⟩, 2, by decide⟩
  · by_cases h1 : j' = j₁
    · subst h1; rw [twoLiveMark_handleU_one]; exact hz _ rfl rfl
    · by_cases h2 : j' = j₂
      · subst h2; rw [twoLiveMark_handleU_two hne]; exact hz _ rfl rfl
      · rw [twoLiveMark_handleU_ne h1 h2]; exact one_mem _
  · by_cases h1 : j' = j₁
    · subst h1; rw [twoLiveMark_handleV_one]; exact hz _ rfl rfl
    · by_cases h2 : j' = j₂
      · subst h2; rw [twoLiveMark_handleV_two hne]; exact hz _ rfl rfl
      · rw [twoLiveMark_handleV_ne h1 h2]; exact one_mem _

/-- ⭐⭐ **The model-independent half soundness at the mixed point**: every achievable
`γ₂`-level move has an **even second** class-three coordinate.  The first is not even, and
`commP_mix` shows it. -/
theorem mix_gaTwo_i_even (hne : (j₁ : ℕ) ≠ (j₂ : ℕ)) {z : SqU5 gr3R}
    (hz : z ∈ rowGaTwoOf (Subgroup.closure (Set.range (twoLiveMark h j₁ j₂ mixU mixV)))) :
    ∃ k : gr3R, z.i = 2 * k := by
  have hle : rowGaTwoOf (Subgroup.closure (Set.range (twoLiveMark h j₁ j₂ mixU mixV)))
      ≤ halfGaTwoSub gr3R := by
    rw [rowGaTwoOf, Subgroup.closure_le]
    rintro w ⟨p, hp, q, hq, rfl⟩
    exact commP_mem_halfGaTwoSub (mixMark_le_halfFrameSub hne hp)
      (mixMark_le_halfFrameSub hne hq)
  exact (hle hz).2.2

/-- ⭐⭐⭐ **THE SHARP INVARIANT HOLDS AT THE MIXED POINT.**  The `v`-covector `(V.d, V.a)`
vanishes, so the first orthogonality is free; the `u`-covector is `(0, 1)`, so the second reads
exactly the achievable moves' **second** class-three coordinate, which the half frame makes
even.  Neither of §4's two sufficient conditions holds here: the achievable set is odd in its
first class-three coordinate, and the `u`-slot's outer column is odd. -/
theorem mix_frameOrth (hne : (j₁ : ℕ) ≠ (j₂ : ℕ)) :
    FrameOrth (twoLiveMark h j₁ j₂ mixU mixV) j₁ :=
  frameOrth_of_gaTwo_i_even ⟨0, by rw [twoLiveMark_handleU_one]; decide⟩
    ⟨0, by rw [twoLiveMark_handleV_one]; decide⟩
    (fun _ hz _ => mix_gaTwo_i_even hne hz)

/-- ⭐⭐⭐ **THE FORCING HOLDS AT THE MIXED POINT**, from the sharp invariant and nothing
else. -/
theorem mix_sigmaForces (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    SigmaForces (twoLiveMark h j₁ j₂ mixU mixV) j₁ :=
  sigmaForces_of_frameOrth twoLiveMark_zero twoLiveMark_one
    (by rw [twoLiveMark_two]; decide) (by rw [twoLiveMark_two]; decide)
    (by rw [twoLiveMark_two]; decide) (by rw [twoLiveMark_two]; decide)
    (sqRelWord_twoLiveMark hlt) (mix_frameOrth (by omega))

theorem mixV_mem_range :
    mixV ∈ Set.range (twoLiveMark h j₁ j₂ mixU mixV) := ⟨sqHandleIdxV j₁, twoLiveMark_handleV_one⟩

theorem mix_not_le_liveFrameSub :
    ¬ Subgroup.closure (Set.range (twoLiveMark h j₁ j₂ mixU mixV)) ≤ liveFrameSub gr3R :=
  fun hle => mixV_not_mem_liveFrameSub (hle (Subgroup.subset_closure mixV_mem_range))

theorem commP_mix_mem_gaTwoOf :
    commP mixU mixV
      ∈ rowGaTwoOf (Subgroup.closure (Set.range (twoLiveMark h j₁ j₂ mixU mixV))) :=
  Subgroup.subset_closure ⟨mixU, Subgroup.subset_closure ⟨sqHandleIdxU j₁,
    twoLiveMark_handleU_one⟩, mixV, Subgroup.subset_closure ⟨sqHandleIdxV j₁,
    twoLiveMark_handleV_one⟩, rfl⟩

theorem mix_not_gaTwo_even :
    ¬ ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range (twoLiveMark h j₁ j₂ mixU mixV))),
        (∃ a : gr3R, z.h = 2 * a) ∧ ∃ b : gr3R, z.i = 2 * b :=
  fun hall => mix_block_odd (hall _ commP_mix_mem_gaTwoOf).1

/-! ### At the mixed point achievability is LOAD-BEARING -/

/-- The `γ₃`-shaped move with second class-three coordinate `1`: **not** achievable at the mixed
point, since `mix_gaTwo_i_even` forbids it. -/
def mixMove : SqU5 gr3R := ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩

theorem mixMove_isGaThree : mixMove.IsGaThree := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mixMove_not_mem_gaTwoOf (hne : (j₁ : ℕ) ≠ (j₂ : ℕ)) :
    mixMove ∉ rowGaTwoOf (Subgroup.closure (Set.range (twoLiveMark h j₁ j₂ mixU mixV))) := by
  intro hc
  obtain ⟨k, hk⟩ := mix_gaTwo_i_even hne hc
  revert hk
  revert k
  decide

theorem sqRelWord_mixWit_U (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    sqRelWord (sigFourDress (twoLiveMark h j₁ j₂ mixU mixV) sigFourU) = liftC 1 := by
  rw [show sigFourDress (twoLiveMark h j₁ j₂ mixU mixV) sigFourU
    = twoLiveWit h j₁ j₂ mixU mixV sigFourU by rw [twoLiveWit_eq_dress, twoLiveWit_one],
    sqRelWord_twoLiveWit hlt]
  decide

/-- ⭐⭐⭐ **An UNACHIEVABLE move kills the odd dressing at the mixed point.**  So the mixed
point's forcing genuinely consumes the achievability convention, exactly as the committed points
do - and unlike the orthogonal point of §5, where the forcing holds for every `γ₃`-shaped move
whatever its provenance. -/
theorem mix_unrestricted_kill (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    sqRelWord (sigLift j₁ (sigFourDress (twoLiveMark h j₁ j₂ mixU mixV) sigFourU) 1 1
      (liftC (-1)) 1 mixMove) = 1 :=
  gaugeX_kill_of_pair (t := 1) twoLiveMark_one SqU5.isGaThree_one mixMove_isGaThree
    (sqRelWord_mixWit_U hlt)
    (by
      simp only [sigIncrPair, twoLiveMark_handleU_one, twoLiveMark_handleV_one,
        show mixU.a = (1 : gr3R) from rfl, show mixU.d = (0 : gr3R) from rfl,
        show mixV.a = (0 : gr3R) from rfl, show mixV.d = (0 : gr3R) from rfl,
        show mixMove.h = (0 : gr3R) from rfl, show mixMove.i = (1 : gr3R) from rfl,
        SqU5.one_h, SqU5.one_i]
      decide)

/-- ⭐⭐⭐ **…so the UNRESTRICTED forcing is false at the mixed point**, while the achievable one
of `mix_sigmaForces` is true.  This is the exact dual of `GradedFourTwoLive.twoLiveOdd_kill`:
there the killing move was achievable and the forcing really failed; here it is not, and the
forcing survives. -/
theorem mix_unrestricted_sigma_forced_false (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    ¬ ∀ v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R, v.b = 0 → z₀.IsGaThree → w₁.IsGaFour → w₂.IsGaFour →
        z₃.IsGaThree → z₄.IsGaThree →
        sqRelWord (sigLift j₁ (sigFourDress (twoLiveMark h j₁ j₂ mixU mixV) v)
          z₀ w₁ w₂ z₃ z₄) = 1 →
        selPar v.a = 0 := by
  intro hforce
  have hcon := hforce sigFourU 1 1 (liftC (-1)) 1 mixMove (by decide) SqU5.isGaThree_one
    SqU5.isGaFour_one (liftC_isGaFour _) SqU5.isGaThree_one mixMove_isGaThree
    (mix_unrestricted_kill hlt)
  rw [show (sigFourU.a : gr3R) = 1 from rfl] at hcon
  exact absurd hcon (by decide)

/-- ⭐⭐⭐ **THE ANSWER, at the harder point.**  A marking outside `liveFrameSub`, whose
achievable set is odd in class three, whose handle slot has an odd outer column - outside BOTH
sufficient conditions - at which the class-four sigma forcing nevertheless **holds**. -/
theorem mix_separates (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    sqRelWord (twoLiveMark h j₁ j₂ mixU mixV) = 1 ∧
      commP mixU mixV ≠ 1 ∧ (¬ ∃ k : gr3R, (commP mixU mixV).h = 2 * k) ∧
      ¬ Subgroup.closure (Set.range (twoLiveMark h j₁ j₂ mixU mixV)) ≤ liveFrameSub gr3R ∧
      (¬ ∀ z ∈ rowGaTwoOf (Subgroup.closure (Set.range (twoLiveMark h j₁ j₂ mixU mixV))),
        (∃ a : gr3R, z.h = 2 * a) ∧ ∃ b : gr3R, z.i = 2 * b) ∧
      selPar mixU.a = 1 ∧
      SigmaForces (twoLiveMark h j₁ j₂ mixU mixV) j₁ :=
  ⟨sqRelWord_twoLiveMark hlt, commP_mix_ne_one, mix_block_odd, mix_not_le_liveFrameSub,
    mix_not_gaTwo_even, mixU_chiA, mix_sigmaForces hlt⟩

end MixPoint

/-! ## 7 What this does to the wave-58 headline -/

section Headline

variable {h : ℕ} {j₁ j₂ : Fin h}

/-- The wave-58 killing point does break the forcing's own shape, restated in this file's
language. -/
theorem twoLiveOdd_not_sigmaForces (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    ¬ SigmaForces (twoLiveMark h j₁ j₂ sigFourU oddLiveV) j₁ := by
  intro hF
  have hd : sigFourDress (twoLiveMark h j₁ j₂ sigFourU oddLiveV) sigFourU
      = twoLiveWit h j₁ j₂ sigFourU oddLiveV sigFourU := by
    rw [twoLiveWit_eq_dress, twoLiveWit_one]
  have hcon := hF sigFourU 1 1 (liftC 3) (commP sigFourU oddLiveV) 1 (by decide)
    SqU5.isGaThree_one SqU5.isGaFour_one (liftC_isGaFour 3) commP_oddLive_isGaThree
    SqU5.isGaThree_one commP_oddLive_mem_gaTwoOf (one_mem _)
    (by rw [hd]; exact twoLiveOdd_kill hlt)
  rw [show (sigFourU.a : gr3R) = 1 from rfl] at hcon
  exact absurd hcon (by decide)

/-- ⭐⭐⭐ **THE WAVE-58 HEADLINE CORRECTED.**  Three two-live markings at the committed core
slots carry the **same** handle block, the class-three element with first coordinate `1`, odd;
all three are outside `GradedFourCleared.liveFrameSub`; and the class-four sigma forcing FAILS
at one of them and HOLDS at the other two.

So "two live blocks outside the frame invariant break the forcing" is false as a general
statement: what breaks the forcing is not the block, nor the frame invariant, but the parity of
the block's **pairing against the handle slots' outer abelian columns**.  The three points
differ only in those columns. -/
theorem twoLiveOdd_block_not_the_criterion (hlt : (j₁ : ℕ) < (j₂ : ℕ)) :
    commP sigFourU oddLiveV = commP orthU orthV ∧
      commP sigFourU oddLiveV = commP mixU mixV ∧
      (¬ ∃ k : gr3R, (commP sigFourU oddLiveV).h = 2 * k) ∧
      oddLiveV ∉ liveFrameSub gr3R ∧ orthV ∉ liveFrameSub gr3R ∧
        mixV ∉ liveFrameSub gr3R ∧
      ¬ SigmaForces (twoLiveMark h j₁ j₂ sigFourU oddLiveV) j₁ ∧
      SigmaForces (twoLiveMark h j₁ j₂ orthU orthV) j₁ ∧
      SigmaForces (twoLiveMark h j₁ j₂ mixU mixV) j₁ :=
  ⟨commP_orth_eq_oddLive.symm, commP_mix_eq_oddLive.symm, by decide,
    oddLiveV_not_mem_liveFrameSub, orthV_not_mem_liveFrameSub, mixV_not_mem_liveFrameSub,
    twoLiveOdd_not_sigmaForces hlt, orth_sigmaForces hlt, mix_sigmaForces hlt⟩

/-- ⭐⭐⭐ **HOW MUCH OF THE FRAME INVARIANT EACH COMMITTED POINT ACTUALLY NEEDS.**  The sharp
line reads each handle slot only through its mod-`2` covector `(slot.d, slot.a)`, and a
vanishing covector imposes nothing at all.  Reading the table off the committed letters:

```text
row                       (U.d, U.a)   (V.d, V.a)   what an achievable move must satisfy
cleared / live / twoLive    (0, 1)       (0, 0)     z.i even
doubly displaced (1,1)      (0, 1)       (0, 1)     z.i even
mirror (1,0)                (0, 1)       (1, 0)     z.h AND z.i even
uncleared-v (0,1)           (1, 0)       (0, 1)     z.h AND z.i even
second power (2,0)          (0, 1)       (1, 0)     z.h AND z.i even
W58 oddLive (the kill)      (0, 1)       (1, 0)     z.h AND z.i even  -- and z.h is ODD
```

So at three of the six the campaign is carrying strictly more than it uses, and
`frameOrth_of_gaTwo_i_even` is the hypothesis those points actually need. -/
theorem committed_covectors :
    (selPar sigFourU.d = 0 ∧ selPar sigFourU.a = 1) ∧
      (selPar sigFourV.d = 0 ∧ selPar sigFourV.a = 0) ∧
      (selPar liveFourV.d = 0 ∧ selPar liveFourV.a = 0) ∧
      (selPar twoLiveV.d = 0 ∧ selPar twoLiveV.a = 0) ∧
      (selPar mirLiveV.d = 1 ∧ selPar mirLiveV.a = 0) ∧
      (selPar rowLiveU.d = 1 ∧ selPar rowLiveU.a = 0) ∧
      (selPar dblLiveV.d = 0 ∧ selPar dblLiveV.a = 1) ∧
      (selPar hiLiveV.d = 1 ∧ selPar hiLiveV.a = 0) ∧
      (selPar oddLiveV.d = 1 ∧ selPar oddLiveV.a = 0) ∧
      (selPar orthU.d = 0 ∧ selPar orthU.a = 0 ∧ selPar orthV.d = 0 ∧ selPar orthV.a = 0) ∧
      (selPar mixU.d = 0 ∧ selPar mixU.a = 1 ∧ selPar mixV.d = 0 ∧ selPar mixV.a = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact ⟨by decide, by decide⟩

/-- ⭐⭐⭐ **The sharp invariant is STRICTLY weaker than the carried one**, and strictly weaker
than the dual condition too: at the orthogonal point the frame invariant fails and the invariant
holds; at the mixed point **both** sufficient conditions fail and the invariant still holds. -/
theorem frameOrth_strictly_weaker (hne : (j₁ : ℕ) ≠ (j₂ : ℕ)) :
    (FrameOrth (twoLiveMark h j₁ j₂ orthU orthV) j₁ ∧
        ¬ Subgroup.closure (Set.range (twoLiveMark h j₁ j₂ orthU orthV))
          ≤ liveFrameSub gr3R) ∧
      (FrameOrth (twoLiveMark h j₁ j₂ mixU mixV) j₁ ∧
        ¬ Subgroup.closure (Set.range (twoLiveMark h j₁ j₂ mixU mixV)) ≤ liveFrameSub gr3R ∧
        selPar mixU.a = 1) :=
  ⟨⟨orth_frameOrth, orth_not_le_liveFrameSub⟩,
    mix_frameOrth hne, mix_not_le_liveFrameSub, mixU_chiA⟩

end Headline

/-! ## 8 Axiom pins -/

section Pins

#print axioms sigIncrPair
#print axioms sigIncrPair_eq_add
#print axioms sigIncrPair_even_of_gaThree_even
#print axioms sigIncrPair_even_of_handle_even
#print axioms gaugeX_increment_even_of_pair
#print axioms gaugeX_sigma_forced_pair
#print axioms gaugeX_sigma_forced_of_gaThree_even
#print axioms gaugeX_kill_of_pair
#print axioms selPar_res_of_odd
#print axioms gaugeX_kill_of_pair_odd
#print axioms SigmaForces
#print axioms FrameOrth
#print axioms FrameOrth.pair
#print axioms frameOrth_of_le_liveFrameSub
#print axioms frameOrth_of_handle_even
#print axioms frameOrth_of_gaTwo_i_even
#print axioms sigmaForces_of_frameOrth
#print axioms frameOrth_of_sigmaForces
#print axioms sigmaForces_iff_frameOrth
#print axioms orthU
#print axioms orthV
#print axioms commP_orth
#print axioms commP_orth_eq_oddLive
#print axioms commP_orth_ne_one
#print axioms commP_orth_isGaThree
#print axioms commP_orth_g
#print axioms orthV_not_mem_liveFrameSub
#print axioms orth_block_odd
#print axioms orth_handle_even
#print axioms orth_pair_eq_zero
#print axioms orth_pair_even
#print axioms orth_sigma_forced
#print axioms orth_frameOrth
#print axioms orth_sigmaForces
#print axioms orth_not_le_liveFrameSub
#print axioms commP_orth_mem_gaTwoOf
#print axioms orth_not_gaTwo_even
#print axioms orth_separates
#print axioms orthHom
#print axioms orthHom_gen
#print axioms orthHom_sigma
#print axioms orthHom_x0
#print axioms orthHom_x1
#print axioms orthHom_sqPivot
#print axioms orthHom_commP_ne_one
#print axioms orthHom_sqEichU
#print axioms orthHom_sqEichV
#print axioms orthHom_b
#print axioms orthHom_b_eq_zero
#print axioms orthHom_sqArbFrame
#print axioms sqArbFrame_sigma_forced_orth
#print axioms orth_forcing_nonvacuous
#print axioms halfFrameSub
#print axioms mem_halfFrameSub
#print axioms halfGaTwoSub
#print axioms mem_halfGaTwoSub
#print axioms commP_mem_halfGaTwoSub
#print axioms mixU
#print axioms mixV
#print axioms mixU_eq
#print axioms mixV_covector_vs_oddLiveV
#print axioms commP_mix
#print axioms commP_mix_eq_oddLive
#print axioms commP_mix_ne_one
#print axioms commP_mix_isGaThree
#print axioms mix_block_odd
#print axioms mixV_not_mem_liveFrameSub
#print axioms mixU_chiA
#print axioms mixMark_le_halfFrameSub
#print axioms mix_gaTwo_i_even
#print axioms mix_frameOrth
#print axioms mix_sigmaForces
#print axioms mixV_mem_range
#print axioms mix_not_le_liveFrameSub
#print axioms commP_mix_mem_gaTwoOf
#print axioms mix_not_gaTwo_even
#print axioms mixMove
#print axioms mixMove_isGaThree
#print axioms mixMove_not_mem_gaTwoOf
#print axioms sqRelWord_mixWit_U
#print axioms mix_unrestricted_kill
#print axioms mix_unrestricted_sigma_forced_false
#print axioms mix_separates
#print axioms twoLiveOdd_not_sigmaForces
#print axioms twoLiveOdd_block_not_the_criterion
#print axioms committed_covectors
#print axioms frameOrth_strictly_weaker

end Pins

end SqCore

end Dyadic

end GQ2

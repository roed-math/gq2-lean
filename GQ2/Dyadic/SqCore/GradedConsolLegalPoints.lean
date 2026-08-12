/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedConsolLegal
import GQ2.Dyadic.SqCore.GradedFiveFrame
import GQ2.Dyadic.SqCore.GradedStageFrame

/-!
# W66-CONSOLEGAL: the two remaining legality points, decided

`GradedConsolLegal` proves the uniform legality criterion `consolLegal_fiveTuple_ne` and
instantiates it at ONE of the three points it was meant to cover, W63-LIVE5's live binder point.
Of the other two it says:

> Wave 60's `fiveFrameHom` and wave 61's `stageFrameHom` are **not** instantiated here and
> nothing below asserts the criterion's hypotheses hold at them; each is a five-slot `decide`
> for a later wave, and until it is run the other two rows stay where W64-VERIFY left them,
> MEASURED.

This file runs those decides.  **Both points fail**, and the two failures are of different
kinds.  Neither row becomes an instantiation of `consolLegal_fiveTuple_ne`; the machine-checked
mismatch is the result.

## ⭐⭐⭐ The two verdicts

```text
   slot     live point (W63-LIVE5)   wave 60 (fiveFrameHom)   wave 61 (stageFrameHom)
   sigma     a=0  b=1  ok  ok         a=0  b=1  ok  ok         a=0  b=1  ok  ok
   x0        a=2  b=0  ok  ok         a=2  b=0  ok  ok         a=2  b=0  ok  ok
   x1        a=0  b=0  ok  ok         a=0  b=0  ok  ok         a=0  b=0  ok  ok
   U         a=0  b=0  ok  ok         a=1  b=0  ✗   ok         a=6  b=7  ✗   ✗
   V         a=0  b=0  ok  ok         a=0  b=0  ok  ok         a=6  b=7  ✗   ✗
```

(`a`, `b` are the raw `ℤ/8` columns; the criterion reads `a` mod `4` and `b` mod `2`.)

* **Wave 60 is REFUTED, structurally.**  `forceU.a = 1` is **odd**, and the criterion's right-hand
  side `2 lambda(g) + 2 e (Phi g).b` lands in `{0, 2} ⊆ ℤ/4` whatever `e` and `lambda` are.  So it
  is not that the packaged hypotheses need reshuffling: the column identity
  `consolLegal_column` rests on cannot hold at this point for **either** value of `e`
  (`consolLegalPt_fiveFrame_column_ne`), hence the generator hypothesis of `consolLegal_column`
  is unsatisfiable there (`consolLegalPt_fiveFrame_hgen_false`).  The mechanism is unavailable at
  wave 60's point, not merely unverified.
* **Wave 61 fails as packaged but survives at a price.**  `stageU` and `stageV` have
  `a = 6`, i.e. `2` mod `4`, and `b = 7`, i.e. **odd**, so four of the ten conditions are false
  (`consolLegalPt_stageFrame_packaged_false`).  The underlying column identity at those two
  slots holds **exactly when `e = 1`** (`consolLegalPt_stageFrame_column_iff`), `e` being the
  parity of `lambda` on the sigma generator.  Section 3 generalises the criterion to carry `e`
  explicitly and section 4 instantiates it at wave 61's point under that one extra hypothesis
  (`consolLegalPt_stageFrame_ne_stageX_of_sigmaOdd`).

⚠ **The price is named.**  `GradedConsolLegal` keeps `e` a bound variable that is never
evaluated, and says so: that is "why nothing here pins the census axiom `sqPivotExp`".  The
wave-61 row cannot be had that way.  Its instantiation hypothesises `e = 1`, i.e. that `lambda`
is odd on the sigma generator, which is exactly the input the prose arguments used and which
`GradedConsolLegal` was built to avoid.  `lambda` is still carried abstractly here and
`sqPivotExp` is still not mentioned, so **no census axiom is pinned by this file either**; the
hypothesis is simply exposed in the statement instead of being discharged.

## ⚠ What this file does NOT do

* It does not refute the CONCLUSION at either point.  Wave 60 and wave 61 each have their own
  incomparable prose argument for the same non-membership, off different columns; nothing here
  bears on those.  What is refuted at wave 60 is that `consolLegal_fiveTuple_ne` covers it.
* It does not discharge `e = 1` for any concrete `lambda`, and in particular does not
  instantiate at `nuLam`.
* It does not touch W63-LIVE5's live point, which `GradedConsolLegal` already settled.

## Contents

* **1** the twenty decides, as the two column tables;
* **2** ⭐⭐ the wave-60 refutation, at the slot and at the hom;
* **3** ⭐⭐ the criterion generalised to carry `e`, and its subsumption of the packaged form;
* **4** ⭐⭐ the wave-61 instance, under the sigma-parity hypothesis;
* **5** axiom pins.

## Merge notes

Nothing is redefined.  Reused: `consolRedFour`, `consolRedFour_zero`, `consolTwoUp`,
`consolTwoUp_zero`, `consolTwoUp_add`, `consolTwoUp_self`, `consolLegal_column`
(`GradedConsolLegal`); `forceU`, `forceV`, `forceX`, `forceY`, `fiveSigMark`, `fiveWit`
(`GradedFiveForce`); `fiveFrameHom`, `fiveFrameHom_gen`, `fiveFrameHom_handleU`
(`GradedFiveFrame`); `stageX`, `stageY`, `stageU`, `stageV`, `stageWit`
(`GradedFiveStageFour`); `stageFrameHom`, `stageFrameHom_gen` (`GradedStageFrame`);
`fiveTuple` and its slot lemmas (`GradedFive`); `sqGen`, `DSq`, `dsqX0`, `dsqX1`, `sqRank`,
`sqHandleIdxU`, `sqHandleIdxV` (`Cores`); `sqIdx_cases` (`Certificate`); `selPar`, `selPar_zero`
(`GradedSelect`); `sqRedMark`, `sqModTwo`, `toAdd_sqModTwo_of_odd`, `toAdd_sqModTwo_of_even`
(`PivotClimb`).

New public names, all carrying the `consolLegalPt` prefix: `consolLegalPt_fiveFrame_columns`,
`consolLegalPt_stageFrame_columns`, `consolLegalPt_fiveFrame_packaged_false`,
`consolLegalPt_fiveFrame_handleU_a_odd`, `consolLegalPt_fiveFrame_column_ne`,
`consolLegalPt_fiveFrame_hgen_false`, `consolLegalPt_fiveTuple_ne_gen`,
`consolLegalPt_slots_of_packaged`, `consolLegalPt_stageFrame_packaged_false`,
`consolLegalPt_stageFrame_column_iff`, `consolLegalPt_stageFrame_ne_stageX_of_sigmaOdd`.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats` bump; every `decide` is on
`ZMod 8`, `ZMod 4`, `ZMod 2` or on `SqU6 gr3R` built over `ZMod 8`.  Of the **11** committed
prints, **10** are **std-3** and one, `consolLegalPt_fiveFrame_packaged_false`, is the strict
subset `[propext, Quot.sound]`; nothing exceeds std-3.  ⚠ No census axiom is reachable:
`sqPivotExp` is not mentioned and `nuLam` is not instantiated.
-/

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The twenty decides -/

section Columns

/-- `consolTwoUp 1 = 2`.  Needed because the `x0` slot carries an odd `lambda`. -/
private theorem consolLegalPt_twoUp_one : consolTwoUp 1 = 2 := by decide

variable {h : ℕ} {j : Fin h}

/-- ⭐ **THE TEN COLUMN VALUES AT WAVE 60'S POINT** (`fiveFrameHom`, whose slots are
`fiveSigMark * 1`, `forceX`, `forceY`, `forceU`, `forceV`).  Nine agree with
`consolLegal_fiveTuple_ne`; the tenth, the `U` slot's `a`-column, is `1` where the criterion
demands `0`. -/
theorem consolLegalPt_fiveFrame_columns :
    consolRedFour (fiveSigMark gr3R * 1).a = 0 ∧ selPar (fiveSigMark gr3R * 1).b = 1
      ∧ consolRedFour forceX.a = 2 ∧ selPar forceX.b = 0
      ∧ consolRedFour forceY.a = 0 ∧ selPar forceY.b = 0
      ∧ consolRedFour forceU.a = 1 ∧ selPar forceU.b = 0
      ∧ consolRedFour forceV.a = 0 ∧ selPar forceV.b = 0 := by decide

/-- ⭐ **THE TEN COLUMN VALUES AT WAVE 61'S POINT** (`stageFrameHom`, whose slots are
`fiveSigMark * 1`, `stageX`, `stageY`, `stageU`, `stageV`).  Six agree with
`consolLegal_fiveTuple_ne`; the four handle conditions are all false, the `a`-columns being `2`
where `0` is demanded and the `b`-columns odd where even is demanded. -/
theorem consolLegalPt_stageFrame_columns :
    consolRedFour (fiveSigMark gr3R * 1).a = 0 ∧ selPar (fiveSigMark gr3R * 1).b = 1
      ∧ consolRedFour stageX.a = 2 ∧ selPar stageX.b = 0
      ∧ consolRedFour stageY.a = 0 ∧ selPar stageY.b = 0
      ∧ consolRedFour stageU.a = 2 ∧ selPar stageU.b = 1
      ∧ consolRedFour stageV.a = 2 ∧ selPar stageV.b = 1 := by decide

end Columns

/-! ## 2 Wave 60: the criterion is not merely unverified, it is unavailable -/

section FiveFrame

variable {h : ℕ} {j : Fin h}

/-- The packaged hypothesis `hUa` of `consolLegal_fiveTuple_ne` is **false** at wave 60's
point. -/
theorem consolLegalPt_fiveFrame_packaged_false : consolRedFour forceU.a ≠ 0 := by decide

/-- ⭐ **THE ROOT CAUSE.**  The `U` letter of wave 60's point has an **odd** `a`-column.  The
live point and wave 61's point both have an even one (`liveBlkU.a = 0`, `stageU.a = 6`), which is
why only this point is beyond repair. -/
theorem consolLegalPt_fiveFrame_handleU_a_odd : selPar forceU.a = 1 := by decide

/-- ⭐⭐ **THE COLUMN IDENTITY FAILS AT WAVE 60'S POINT FOR BOTH VALUES OF `e`.**  The
right-hand side of `consolLegal_column` is a sum of `consolTwoUp` values, hence even in `ℤ/4`,
while `consolRedFour forceU.a = 1`.  No choice of the sigma-slot parity `e` closes the gap, so
no reshuffling of the ten packaged conditions instantiates the criterion here. -/
theorem consolLegalPt_fiveFrame_column_ne :
    ∀ e : ZMod 2, consolRedFour forceU.a ≠ consolTwoUp (e * selPar forceU.b) := by decide

/-- ⭐⭐ **THE SAME, AT THE HOM.**  For every marking `lam` that is trivial on the `U` handle
letters (one of `consolLegal_fiveTuple_ne`'s own hypotheses; the `V` half is not needed, since
the failure is already at the marked `U` handle) and every `e`, the generator hypothesis
`hgen` of `consolLegal_column` is **unsatisfiable** at wave 60's point: it already fails at the
marked `U` handle.

⚠ This refutes the route, not the conclusion.  Wave 60's own prose argument runs off `lambda` and
`nu'` mod `2` and is untouched by this. -/
theorem consolLegalPt_fiveFrame_hgen_false (e : ZMod 2)
    (lam : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hlU : ∀ j' : Fin h, lam (sqGen h (sqHandleIdxU j')) = 1) :
    ¬ (∀ i, consolRedFour (fiveFrameHom h j (sqGen h i)).a
        = consolTwoUp (Multiplicative.toAdd (sqRedMark lam (sqGen h i)))
          + consolTwoUp (e * selPar (fiveFrameHom h j (sqGen h i)).b)) := by
  intro hgen
  have hz : Multiplicative.toAdd (sqRedMark lam (sqGen h (sqHandleIdxU j))) = 0 := by
    show Multiplicative.toAdd (sqModTwo (lam (sqGen h (sqHandleIdxU j)))) = 0
    rw [hlU j, map_one]
    rfl
  have h1 := hgen (sqHandleIdxU j)
  rw [fiveFrameHom_handleU, hz, consolTwoUp_zero, zero_add] at h1
  exact consolLegalPt_fiveFrame_column_ne e h1

end FiveFrame

/-! ## 3 The criterion, generalised to carry `e` -/

section Generalised

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐⭐ **THE CRITERION WITH THE SIGMA PARITY EXPOSED.**  Same conclusion as
`consolLegal_fiveTuple_ne` -- no `lambda`-legal `g` has `Phi g = x` -- but the five slot
conditions are stated as the five generator instances of the column identity, with the sigma
slot's `lambda`-parity `e` an explicit parameter pinned by `he`.

`consolLegal_fiveTuple_ne` is the special case where every non-sigma `b`-column is even and the
sigma `b`-column is odd, in which `e` drops out of all five (`consolLegalPt_slots_of_packaged`).
Points whose handle letters have an odd `b`-column, such as wave 61's, are reachable only in
this form, and only at one value of `e`.

⚠ `he` is a genuine extra input, not a bookkeeping device: at wave 61's point it is what makes
the handle conditions true (`consolLegalPt_stageFrame_column_iff`). -/
theorem consolLegalPt_fiveTuple_ne_gen {S X Y U V : SqU6 gr3R} (e : ZMod 2)
    (Φ : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R))
    (lam : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hΦ : ∀ i, Φ (sqGen h i) = fiveTuple gr3R h j S X Y U V i)
    (he : Multiplicative.toAdd (sqRedMark lam (sqGen h 0)) = e)
    (hlx0 : lam (dsqX0 h) = Multiplicative.ofAdd (1 : ℤ_[2]))
    (hlx1 : lam (dsqX1 h) = Multiplicative.ofAdd (2 : ℤ_[2]))
    (hlU : ∀ j' : Fin h, lam (sqGen h (sqHandleIdxU j')) = 1)
    (hlV : ∀ j' : Fin h, lam (sqGen h (sqHandleIdxV j')) = 1)
    (hS : consolRedFour S.a = consolTwoUp e + consolTwoUp (e * selPar S.b))
    (hX : consolRedFour X.a = 2 + consolTwoUp (e * selPar X.b))
    (hY : consolRedFour Y.a = consolTwoUp (e * selPar Y.b))
    (hU : consolRedFour U.a = consolTwoUp (e * selPar U.b))
    (hV : consolRedFour V.a = consolTwoUp (e * selPar V.b))
    {x : SqU6 gr3R} (hxa : consolRedFour x.a ≠ 0) (hxb : selPar x.b = 0)
    {g : (DSq h : Type)} (hleg : lam g = 1) :
    Φ g ≠ x := by
  have hone : ∀ y : (DSq h : Type), lam y = 1 →
      Multiplicative.toAdd (sqRedMark lam y) = 0 := by
    intro y hy
    show Multiplicative.toAdd (sqModTwo (lam y)) = 0
    rw [hy, map_one]
    rfl
  have hgen : ∀ i, consolRedFour (Φ (sqGen h i)).a
      = consolTwoUp (Multiplicative.toAdd (sqRedMark lam (sqGen h i)))
        + consolTwoUp (e * selPar (Φ (sqGen h i)).b) := by
    intro i
    rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
    · rw [hΦ 0, fiveTuple_zero, he]
      exact hS
    · have hl : Multiplicative.toAdd (sqRedMark lam (sqGen h 1)) = 1 := by
        show Multiplicative.toAdd (sqModTwo (lam (dsqX0 h))) = 1
        rw [hlx0]
        exact toAdd_sqModTwo_of_odd (isUnit_iff_not_two_dvd.mp isUnit_one)
      rw [hΦ 1, fiveTuple_one, hl, consolLegalPt_twoUp_one]
      exact hX
    · have hl : Multiplicative.toAdd (sqRedMark lam (sqGen h 2)) = 0 := by
        show Multiplicative.toAdd (sqModTwo (lam (dsqX1 h))) = 0
        rw [hlx1]
        exact toAdd_sqModTwo_of_even ⟨1, by ring⟩
      rw [hΦ 2, fiveTuple_two, hl, consolTwoUp_zero, zero_add]
      exact hY
    · rw [hΦ _, hone _ (hlU j'), consolTwoUp_zero, zero_add]
      by_cases hjj : j' = j
      · subst hjj
        rw [fiveTuple_handleU]
        exact hU
      · rw [fiveTuple_handleU_ne hjj, SqU6.one_a, SqU6.one_b, consolRedFour_zero, selPar_zero,
          mul_zero, consolTwoUp_zero]
    · rw [hΦ _, hone _ (hlV j'), consolTwoUp_zero, zero_add]
      by_cases hjj : j' = j
      · subst hjj
        rw [fiveTuple_handleV]
        exact hV
      · rw [fiveTuple_handleV_ne hjj, SqU6.one_a, SqU6.one_b, consolRedFour_zero, selPar_zero,
          mul_zero, consolTwoUp_zero]
  intro hcon
  have hcol := consolLegal_column Φ lam e hgen g
  rw [hcon, hone g hleg, consolTwoUp_zero, zero_add, hxb, mul_zero, consolTwoUp_zero] at hcol
  exact hxa hcol

/-- ⭐ **THE PACKAGED FORM IS THE SPECIAL CASE.**  The ten slot conditions of
`consolLegal_fiveTuple_ne` imply the five of `consolLegalPt_fiveTuple_ne_gen`, at **every** `e`:
the sigma slot's odd `b`-column turns its condition into `consolTwoUp_self`, and the four even
`b`-columns kill `e` outright.  So `consolLegalPt_fiveTuple_ne_gen` is a strict generalisation
and nothing is lost by working in it. -/
theorem consolLegalPt_slots_of_packaged (e : ZMod 2) {S X Y U V : SqU6 gr3R}
    (hSa : consolRedFour S.a = 0) (hSb : selPar S.b = 1)
    (hXa : consolRedFour X.a = 2) (hXb : selPar X.b = 0)
    (hYa : consolRedFour Y.a = 0) (hYb : selPar Y.b = 0)
    (hUa : consolRedFour U.a = 0) (hUb : selPar U.b = 0)
    (hVa : consolRedFour V.a = 0) (hVb : selPar V.b = 0) :
    consolRedFour S.a = consolTwoUp e + consolTwoUp (e * selPar S.b)
      ∧ consolRedFour X.a = 2 + consolTwoUp (e * selPar X.b)
      ∧ consolRedFour Y.a = consolTwoUp (e * selPar Y.b)
      ∧ consolRedFour U.a = consolTwoUp (e * selPar U.b)
      ∧ consolRedFour V.a = consolTwoUp (e * selPar V.b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hSa, hSb, mul_one, consolTwoUp_self]
  · rw [hXa, hXb, mul_zero, consolTwoUp_zero, add_zero]
  · rw [hYa, hYb, mul_zero, consolTwoUp_zero]
  · rw [hUa, hUb, mul_zero, consolTwoUp_zero]
  · rw [hVa, hVb, mul_zero, consolTwoUp_zero]

end Generalised

/-! ## 4 Wave 61, instantiated at the price of the sigma parity -/

section StageFrame

variable {h : ℕ} {j : Fin h}

/-- All four handle conditions of `consolLegal_fiveTuple_ne` are **false** at wave 61's
point. -/
theorem consolLegalPt_stageFrame_packaged_false :
    consolRedFour stageU.a ≠ 0 ∧ selPar stageU.b ≠ 0
      ∧ consolRedFour stageV.a ≠ 0 ∧ selPar stageV.b ≠ 0 := by decide

/-- ⭐⭐ **THE SIGMA PARITY IS EXACTLY WHAT WAVE 61 NEEDS, AND IT IS NOT REMOVABLE.**  At both
handle slots the column identity holds **iff** `e = 1`.  Unlike wave 60, the identity is
available here; unlike the live point, it costs a hypothesis on `lambda` at the sigma
generator. -/
theorem consolLegalPt_stageFrame_column_iff :
    ∀ e : ZMod 2, (consolRedFour stageU.a = consolTwoUp (e * selPar stageU.b) ↔ e = 1)
      ∧ (consolRedFour stageV.a = consolTwoUp (e * selPar stageV.b) ↔ e = 1) := by decide

/-- ⭐⭐ **WAVE 61'S POINT, UNDER THE SIGMA-PARITY HYPOTHESIS.**  If `lambda` is odd on the sigma
generator, then at every handle count and every handle **no `lambda`-legal `g` has
`stageFrameHom h j g = stageX`**.

`lambda` is normalised exactly as `consolLegal_fiveTuple_ne` normalises it, and all four of
those conditions are carried here too: `lambda` sends `x0` to `1` and `x1` to `2`, and is
trivial on every handle letter (`hlx0`, `hlx1`, `hlU`, `hlV`).  `hsig` is the fifth condition
and the only new one.

⚠ `hsig` is not free.  `consolLegal_fiveTuple_ne` never evaluates the sigma parity, and
`GradedConsolLegal` records that as the reason no census axiom is reachable from it; wave 61's
point cannot be taken that way, because `consolLegalPt_stageFrame_column_iff` shows `e = 1` is
equivalent to the handle conditions rather than implied by them.  `lambda` is still abstract
here and `sqPivotExp` is still not mentioned: the input is exposed, not discharged.

⚠ Nothing here says wave 61's row is closed unconditionally.  It is closed for markings that
are odd on sigma. -/
theorem consolLegalPt_stageFrame_ne_stageX_of_sigmaOdd
    (lam : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hsig : Multiplicative.toAdd (sqRedMark lam (sqGen h 0)) = 1)
    (hlx0 : lam (dsqX0 h) = Multiplicative.ofAdd (1 : ℤ_[2]))
    (hlx1 : lam (dsqX1 h) = Multiplicative.ofAdd (2 : ℤ_[2]))
    (hlU : ∀ j' : Fin h, lam (sqGen h (sqHandleIdxU j')) = 1)
    (hlV : ∀ j' : Fin h, lam (sqGen h (sqHandleIdxV j')) = 1)
    {g : (DSq h : Type)} (hleg : lam g = 1) :
    stageFrameHom h j g ≠ stageX :=
  consolLegalPt_fiveTuple_ne_gen (j := j) (S := fiveSigMark gr3R * 1) (X := stageX)
    (Y := stageY) (U := stageU) (V := stageV) 1 (stageFrameHom h j) lam
    (fun i => by rw [stageFrameHom_gen, stageWit]) hsig hlx0 hlx1 hlU hlV
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hleg

end StageFrame

/-! ## 5 Axiom pins -/

section AxiomPins

#print axioms consolLegalPt_fiveFrame_columns
#print axioms consolLegalPt_stageFrame_columns
#print axioms consolLegalPt_fiveFrame_packaged_false
#print axioms consolLegalPt_fiveFrame_handleU_a_odd
#print axioms consolLegalPt_fiveFrame_column_ne
#print axioms consolLegalPt_fiveFrame_hgen_false
#print axioms consolLegalPt_fiveTuple_ne_gen
#print axioms consolLegalPt_slots_of_packaged
#print axioms consolLegalPt_stageFrame_packaged_false
#print axioms consolLegalPt_stageFrame_column_iff
#print axioms consolLegalPt_stageFrame_ne_stageX_of_sigmaOdd

end AxiomPins

end SqCore

end Dyadic

end GQ2

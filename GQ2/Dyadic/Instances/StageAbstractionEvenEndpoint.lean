/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenFrameDeep
import GQ2.Dyadic.Instances.StageAbstractionEvenDigit

/-!
# W54-COMPOSE: the composed even endpoints, and the honest input list of the even route

## Status: this file's *claims* are superseded in three places (waves 54, 55, 56)

Nothing below is unsound and no statement of this file has been changed.  Three of its **prose**
claims were falsified after it was written, twice by later results and once by a sibling lane of
its own wave, and a reader who quotes this file without the following four sentences will quote
something false.  `GQ2/Dyadic/Instances/EvenRouteCarried.lean` (W56-RECUT) publishes the corrected
artefacts.

1. **The isotropy is not refused; it is a theorem.**  The "Refused" paragraph below, the §8
   docstring and the `α = 2` headline all say the `M` branch owes `EvenDeepMIsotropicSupply`
   above `α = 2`.  `GQ2/Dyadic/Instances/EvenDeepIsotropy.lean` (W54-BOCK, same wave, sibling in
   the import graph) proves `evenDeepMIsotropicSupply_holds : EvenDeepMIsotropicSupply K`
   outright.  What §7's `evenEndpoint_mIso_iff_frame` establishes is still true and still sharp:
   the isotropy is *equivalent* to the `M` frame, so no route through a frame avoids it.  It is
   not an *input*, because it is proved.  `EvenRouteCarriedM` below therefore has one field too
   many; `EvenRouteCarried.EvenRouteCarriedDeepM` has two.
2. **The flip supplies are FALSE at `α = 2`.**  `StageAbstractionEvenFlip.lean` §6 (W55-SLOT3)
   proves `¬ EvenDigitFlipSupply 2 W v G chi` on every row table as soon as one stage tuple
   exists.  So `EvenEndpointNFlip`, `EvenEndpointMFlipOffTwo` and all four `EvenRouteCarried*`
   structures below are false at every field whose branch depth is `2`
   (`EvenRouteCarried.evenRouteCarried_not_carried{N,M,NTwo,MTwo}`), and with them the four
   endpoints `evenEndpoint_orientedEquiv{N,M}_two`, `evenRoute_orientedEquiv{N,M}` and
   `evenRoute_orientedEquiv{N,M}_two` are vacuous there.  Every sentence below asserting that the
   `α = 2` stratum carries two inputs should be read as retracted.
3. **The flip demand above `α = 2` is one coordinate, not a family.**  The same wave-55 file
   proves every flip coordinate but `0` on both branches, so the honest carried flip input is
   `EvenDigitFlipSupplySlotZero`, and shave 3 below (the `M` slot `2`) is subsumed.
4. **The depth binders below are unguarded.**  `EvenEndpointMFamily`, `EvenEndpointMFlipOffTwo`,
   `EvenEndpointNFamily`, `EvenEndpointNFlip` and the four structures quantify over every
   `α ≥ 2` without the range identity, while the identity produces one `α` per field.
   `EvenDeepMIsotropicSupply` is the correct pattern and the re-cut follows it.

## What this file is

Wave 53 pushed the even route forward on two independent fronts, each re-cutting one of the
three named inputs of the committed per-`K` endpoints `evenPerK_orientedEquiv{N,M}`
(`StageAbstractionEvenPerK.lean` §6, carrying `Hbase`, `Hfam`, `Hup`):

* **W53-KAPPA** (`StageAbstractionEvenFrameDeep.lean`) discharged `Hbase` on the `M` branch by
  naming the depth class `μ`, at the price of the ramified-`i` binder `κ ≠ 0` and the isotropy
  `EvenDeepMIsotropicSupply`;
* **W53-HUP** (`StageAbstractionEvenDigit.lean`) proved `Hup` EQUIVALENT to the one-digit
  supply `EvenDigitFlipSupply`, and proved the `M`-branch slot-`2` flip outright.

Neither wave-53 file consumed the other: `evenFrameDeep_orientedEquivM` still carries `Hup`,
and `evenDigit_orientedEquiv{N,M}` still carry `Hbase`.  This file composes them and then
audits what is left.

## Headline

**Both advances compose with no conflict, and four further inputs fall.**  The composed
endpoints are §6's `evenEndpoint_orientedEquiv{N,M}` with the strata
`evenEndpoint_orientedEquiv{N,M}_two`, and the even route's carried list after this lane is:

| statement | carried inputs | extra binders |
| --- | --- | --- |
| `evenPerK_orientedEquivN` | `Hbase`, `Hfam`, `Hup` | - |
| `evenDigit_orientedEquivN` | `Hbase`, `Hfam`, flips | - |
| **`evenEndpoint_orientedEquivN`** | **`Hfam`, flips** | **-** |
| `evenPerK_orientedEquivM` | `Hbase`, `Hfam`, `Hup` | - |
| `evenDigit_orientedEquivM` | `Hbase`, `Hfam`, flips | - |
| `evenFrameDeep_orientedEquivM` | `Hiso`, `Hfam`, `Hup` | `κ ≠ 0` |
| **`evenEndpoint_orientedEquivM`** | **`Hiso`, `Hfam`, flips off slot `2`** | **-** |
| `evenPerK_orientedEquivN_two` | `Hfam`, `Hup` | `B`, `κ ≠ 0` |
| `evenDigit_orientedEquivN_two` | `Hfam`, flips | `B`, `κ ≠ 0` |
| **`evenEndpoint_orientedEquivN_two`** | **`Hfam`, flips** | **-** |
| `evenPerK_orientedEquivM_two` | `Hfam`, `Hup` | `B`, `κ ≠ 0` |
| `evenDigit_orientedEquivM_two` | `Hfam`, flips | `B`, `κ ≠ 0` |
| **`evenEndpoint_orientedEquivM_two`** | **`Hfam`, flips off slot `2`** | **-** |

("Extra binders" excludes the branch data every one of these carries: the even-degree binder,
and what the range identity needs - `B` with the ramification datum and `-1 ∉ im χ` on `N`, `B`
with `-1 ∈ im χ` on `M`, or the identification itself on the strata.  The `α ≥ 2` forms of the
carried supplies are used throughout; see shave 4.)

So at `α = 2` **both** branches now carry exactly the odd route's two inputs, with the
raw-to-bracket half reduced to one digit per slot and, on `M`, one slot fewer than that; and
the `N` branch carries those same two inputs at **every** `α ≥ 2`.  The only input the `M`
branch owes above `α = 2` that the `N` branch does not is the isotropy, and W53-KAPPA §5
proves it necessary.

**Retracted, twice** (see the status section above).  The `α = 2` sentence is false: wave 55
refutes both branches' flip supplies there, so the two `α = 2` bundles have no model at a
depth-`2` field and the stratum endpoints are vacuous.  The isotropy sentence is false: W53-KAPPA
§5 proves the isotropy *unavoidable on any route through a frame*, which is not the same as
proving it an input, and W54-BOCK proves it outright in this same wave.  Above `α = 2` the two
branches carry the same two inputs, and the second of them is one flip coordinate.

## The four shaves, and the one refusal

1. **`Hbase` on the `N` branch, discharged for free (§2, §3).**  W53-KAPPA hoisted the
   lifting step out of the frame assembly (`evenFrameDeep_of_realizers`) and observed that on
   `imChiN α` the depth digit *is* the mod-four parity (`evenDeep_digit_imChiN`).  Those two
   facts compose: the `N` realizers' single shadow `κ` already determines the character value
   modulo `2^(α+1)`, which is exactly the precision the corrected deep seam consumes, so the
   `N`-row cup-adapted frame exists from the range identity alone
   (`evenEndpoint_nFrame_of_range`) and with it the level-three base
   (`evenEndpoint_nStageBase`).  No isotropy input, no `ω` pin, and - unlike the committed
   `evenDegreeNCyclotomicFrattiniFrameSupply_holds` - no depth-`1` row seam, which W52 refuted
   at `α ≥ 3`.  This is the exact sense in which "`N` pays nothing": the `M` branch's new datum
   is on the `N` branch the committed `evenFrameCup_kappa_self`, and the `N` branch's *own*
   `Hbase` falls out as a corollary of the same re-cut.
2. **The ramified-`i` binder `κ ≠ 0`, discharged on both branches (§1).**  `κ = 0` says every
   cyclotomic value is `≡ 1 (mod 4)`.  On the `N` branch `nUnit α ∈ imChiN α` has parity `1`,
   on the `M` branch `-1` does, and `-1 ∈ im χ` is a hypothesis the `M` endpoint carries
   anyway.  So the binder is implied by the branch identification on `N`
   (`evenEndpoint_kappa_of_rangeN`) and by `hneg` alone on `M`
   (`evenEndpoint_kappa_of_negOne`).  It is not an independent datum on either branch.
3. **The `M` slot-`2` flip, dropped from the carried set (§4).**  `EvenDigitFlipSupplyOffTwo`
   is `EvenDigitFlipSupply` with the coordinate `2` demand deleted; on the `M` row the deleted
   demand is the theorem `evenDigit_flipSlotTwo_M`, so the two are equivalent there
   (`evenEndpoint_mFlip_iff_offTwo`) and only the reduced one is carried.

   The backlog's companion item, the `M` slot `3`, is **reduced but not shaved** (§4.1).  Slot
   `3`'s bracket partner is index `2`, whose `M` table value is `1`, so no partner power is
   sharp; the paired move that places `base 3 ^ 2^(k-2)` at slot `3` and `base 2 ^ 2^(k-2)` at
   slot `2` has all the right digits, and the entire remaining demand is the single identity
   `[a^n, b] · [b^n, a] = 1` in `levelQuot G (k + 1)`
   (`evenEndpoint_flipSlotThree_M_of_pairedMove`).  That identity is not in the tree, so the
   carried set below keeps slot `3`.
4. **The `α ≥ 1` quantifier of the carried supplies, tightened to `α ≥ 2` (§5.1).**  Every
   committed per-`K` input (`EvenPerK{N,M}StageBase`, `…FamilySupply`, `…RawToBracket`,
   `EvenPerK{N,M}DigitFlip`) quantifies over every `α ≥ 1`, while the range identity produces
   one `α`, and that `α` is `≥ 2`.  The endpoints below carry the `α ≥ 2` forms, which demand
   strictly fewer instances; `evenEndpoint_{n,m}Family_of_perK` and
   `evenEndpoint_nFlip_of_perK` / `evenEndpoint_mFlipOffTwo_of_perK` certify that the committed
   forms imply them, so no wave-53 consumer loses anything.

   Tightening the binder is *not* what W53-KAPPA's remark asked for, and this file does not
   pretend otherwise.  That remark observes that `EvenPerKMStageBase` quantifies over depths at
   all while the identity produces one, so the base can only ever be supplied at the produced
   depth; narrowing `α ≥ 1` to `α ≥ 2` does not repair that, and no quantified base `Prop` can.
   The structural repair is to state the endpoint *at* a depth, which is §5.2, and to let §6
   produce the depth once.  So the re-assembly KAPPA performed is exactly right, and §5.2 is its
   general form.

**Refused: the isotropy on `M`.**  `EvenDeepMIsotropicSupply` is not removable, and this is a
theorem, not a judgement: W53-KAPPA §5's `evenFrameDeep_isotropic_of_frame` derives it from the
mere existence of an `M`-row cup-adapted frame, so any route to the `M` base through a frame
pays it.  §7 restates that as the sharp statement about this file's own `M` endpoint.  The `N`
analogue is free precisely because `evenDeep_digit_imChiN` makes the `N` depth class `κ` itself,
whose isotropy is `evenFrameCup_kappa_self`, a parity corollary at even degree.

**This refusal is withdrawn.**  "Not removable" confuses *unavoidable* with *unproved*.  The
sharpness statement stands: every route through a frame does pay the isotropy.  What this
paragraph got wrong is that paying it costs an input, and it does not, because
`GQ2/Dyadic/Instances/EvenDeepIsotropy.lean` (W54-BOCK, this same wave) proves
`evenDeepMIsotropicSupply_holds : EvenDeepMIsotropicSupply K` for every field and every `α ≥ 2`,
by lifting the depth class to a `ℤ/4`-valued character and killing the Bockstein.  The two lanes
never met in the import graph, which is why this file was published carrying it.  Cost of the
discharge: `tateDualityAt` only, no norm criterion.

**Also dropped, and worth naming: the marked reciprocity bundle `B`.**  Every committed even
endpoint carries a `MarkedRecip R K`, and every one of them uses it for exactly one thing:
producing `α` from `evenRange_range_eq_imChi{N,M}`.  The level-three station carries `B`
unused (`evenLevelThreeN_stageBase`'s docstring says so).  Since §2's base is built without
the station, the at-depth endpoints of §5 and the strata of §7 carry no bundle at all.

## Composition audit: the two advances do not conflict

The only place where a conflict could have arisen is the shape of the depth binder: W53-KAPPA
states its isotropy supply at `2 ≤ alpha` and W53-HUP states its flip supplies at `1 ≤ alpha`,
and the two are fed to the same `α` produced by the identity.  A `1 ≤ alpha` supply demands
strictly more instances than a `2 ≤ alpha` one, so the honest joint form is the `2 ≤ alpha` one,
which is what §5.1 carries and what the committed forms imply.  Nothing is strengthened, and
every wave-53 consumer still applies.

Beyond that the two advances touch disjoint machinery: KAPPA re-cuts the frame that produces the
level-three base, HUP re-cuts the residual supply of the climb above it, and the committed
`evenPerK_forwardGeneratorData{N,M}` is the unchanged seam between them.  So the answer to the
lane's honesty question is that there is no conflict to report: the composition is clean, and
the four shaves are what the composing exposed.

## Numbering

1. the ramified-`i` binder, discharged on both branches;
2. the `N`-row frame from the deep seam, with no new input;
3. the `N` level-three base;
4. the reduced `M` flip supply, and the slot-`3` reduction;
5. the at-depth endpoints, both branches;
6. the per-field endpoints;
7. the `α = 2` stratum, and the sharpness of what is left;
8. the honest carried-input list, as Lean statements;
9. axiom pins.
-/

namespace GQ2.Dyadic.EvenEndpoint

noncomputable section

open GQ2 ContCoh
open GQ2.Roe.Labute
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.EvenForward
open GQ2.Dyadic.EvenRowSupply
open GQ2.Dyadic.EvenCyclotomicRange
open GQ2.Dyadic.LSquare
open GQ2.Dyadic.LSquare.FrattiniFrameSupply
open GQ2.Dyadic.EvenPerK
open GQ2.Dyadic.EvenFrameDeep

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The coefficient action at `G_K(2)`, as everywhere on this route: the unique action of a
group on `𝔽₂`, which is the trivial one.  Declared once for the whole file, at the binders
`maxProPQuotient` actually needs, so that the Hausdorff binder stays omittable. -/
local instance evenEndpointScalar {K : IntermediateField ℚ_[2] ℚ̄₂} [CompactSpace (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] :
    DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

/-- Continuity of that action. -/
local instance evenEndpointContinuousScalar {K : IntermediateField ℚ_[2] ℚ̄₂}
    [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-! ## §1 The ramified-`i` binder, discharged on both branches

`cyclotomicModFourClassKTwo ≠ 0` is the frame layer's spelling of "`K(i)/K` is ramified", and
`FieldDataEven.kappaK_eq_zero_iff` records that nothing in `GQ2/Dyadic/` derives it from the
norm-group form of the ramification hypothesis.  It does not have to: the class is nonzero as
soon as one cyclotomic value has mod-four parity `1`, and on each branch the identification
produces such a value outright.  So on the even route this binder is not an input at all. -/

section Kappa

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- **One character value of parity one makes `κ` nonzero.**  Evaluating the mod-four class at
a preimage of the value is the value's parity (`frattiniFrameEval_modFour`), and the zero class
evaluates to `0` everywhere. -/
theorem evenEndpoint_kappa_of_value {u : ℤ_[2]ˣ}
    (hu : u ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (hpar : Multiplicative.toAdd (unitsModFourParity
      (Units.map (PadicInt.toZModPow 2).toMonoidHom u)) = 1) :
    cyclotomicModFourClassKTwo (K := K) ≠ 0 := by
  obtain ⟨g, hg⟩ := hu
  intro h0
  have hone : frattiniFrameEval (cyclotomicModFourClassKTwo (K := K)) g = 1 := by
    rw [frattiniFrameEval_modFour, show chiCycKTwo (K := K) g = u from hg]
    exact hpar
  rw [h0, frattiniFrameEval_zero] at hone
  exact zero_ne_one hone

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- **The binder on the `N` branch**, from the branch identification alone: `nUnit α` is a
character value and is `≡ 3 (mod 4)` (`evenDegreeN_parity_nUnit`). -/
theorem evenEndpoint_kappa_of_rangeN {α : ℕ} (hα : 2 ≤ α)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN α) :
    cyclotomicModFourClassKTwo (K := K) ≠ 0 :=
  evenEndpoint_kappa_of_value (by rw [hrange]; exact evenRow_nUnit_mem_imChiN α)
    (evenDegreeN_parity_nUnit hα)

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- **The binder on the `M` branch**, from `hneg` alone: `-1` is `≡ 3 (mod 4)`
(`evenDegreeM_parity_negOne`), and `-1 ∈ im χ` is the hypothesis the `M` endpoints carry to
run the range identity.  So the `M` branch pays nothing for the binder either, and in
particular no branch depth is needed.

The argument itself is `EvenFrameDeep.evenFrameDeep_kappa_ne_zero_of_negOne`, which is where the
shared proof lives; `EvenDeepIsotropy.evenDeep_kappa_ne_zero_of_neg` is the other face of it,
with the same statement.  The general `evenEndpoint_kappa_of_value` stays: it is what
`evenEndpoint_kappa_of_rangeN` needs, at a value other than `-1`. -/
theorem evenEndpoint_kappa_of_negOne
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom) :
    cyclotomicModFourClassKTwo (K := K) ≠ 0 :=
  evenFrameDeep_kappa_ne_zero_of_negOne hneg

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- The `M` binder read off the branch identification instead, for the at-depth endpoints,
which take `hrange` rather than `hneg`. -/
theorem evenEndpoint_kappa_of_rangeM {α : ℕ}
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α) :
    cyclotomicModFourClassKTwo (K := K) ≠ 0 :=
  evenEndpoint_kappa_of_negOne (by rw [hrange]; exact neg_one_mem_imChiM α)

end Kappa

/-! ## §2 The `N`-row frame from the deep seam

The `M`-side re-cut of W53-KAPPA has two halves.  The first is generic: `evenFrameDeep_of_realizers`
is the frame assembly with the lifting step hoisted into a hypothesis, so a consumer may reach
the realizers by any route.  The second is `M`-specific: the shadow `(κ, τ)` determines a value
of `imChiM α` only modulo `2^α`, one digit short, which is why the depth class `μ` and its
isotropy had to be bought.

On the `N` branch the second half is free, and `evenDeep_digit_imChiN` is why: on `imChiN α` the
depth digit *equals* the mod-four parity, so the single shadow `κ` already determines the value
modulo `2^(α+1)`, which is the precision `EvenRowDeepFibreLiftSupply (α - 1)` consumes at
`m = 2`.  Feeding that to the hoisted assembly gives the `N` frame with no input beyond the range
identity: no isotropy, no `ω` pin, and no depth-`1` row seam - which matters, because
`evenPerK_not_rowSupplyN` refutes the last one at `α ≥ 3`, so the committed
`evenDegreeNCyclotomicFrattiniFrameSupply_holds` cannot be run there. -/

section NFrame

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The `N`-branch two-class determination collapses to one class.**  Two elements of
`imChiN α` with the same mod-four parity agree modulo `2^(α+1)`: their depth digits agree
automatically, by `evenDeep_digit_imChiN`, so the `M`-branch determination
`evenDeep_map_eq_of_shadow` applies with nothing further to check.  This is
`evenPerK_dvd_of_modEight_imChiN` with the mod-eight hypothesis weakened to mod-four, which is
the whole `N`/`M` asymmetry in one statement. -/
theorem evenEndpoint_nShadow {α : ℕ} (hα : 2 ≤ α) {a b : ℤ_[2]ˣ}
    (ha : a ∈ imChiN α) (hb : b ∈ imChiN α)
    (hpar : Multiplicative.toAdd (unitsModFourParity
        (Units.map (PadicInt.toZModPow 2).toMonoidHom a)) =
      Multiplicative.toAdd (unitsModFourParity
        (Units.map (PadicInt.toZModPow 2).toMonoidHom b))) :
    Units.map (PadicInt.toZModPow (2 + (α - 1))).toMonoidHom a =
      Units.map (PadicInt.toZModPow (2 + (α - 1))).toMonoidHom b :=
  evenDeep_map_eq_of_shadow hα (evenSharp_pmOne_of_mem_imChiN (by omega) ha)
    (evenSharp_pmOne_of_mem_imChiN (by omega) hb) hpar
    (by rw [evenDeep_digit_imChiN hα ha, evenDeep_digit_imChiN hα hb, hpar])

/-- **The `N`-row cup-adapted Frattini frame, from the deep seam.**  For every `α ≥ 2`, from the
branch identification and nothing else: the ramified-`i` binder is §1 and the isotropy input of
the `M` branch has no `N` analogue.

Compare `evenFrameDeep_mFrame_of_range`, which needs `κ ≠ 0` and `EvenDeepMIsotropicSupply`, and
the committed `evenDegreeNCyclotomicFrattiniFrameSupply_holds`, which needs the depth-`1` row
seam that `evenPerK_not_rowSupplyN` refutes at `α ≥ 3`. -/
theorem evenEndpoint_nFrame_of_range {α h : ℕ} (hα : 2 ≤ α)
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 2)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN α) :
    ∃ F : Frame (vN (h := h) α) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)),
      F.IsCupAdapted (evenFrameGram h) (evenFramePairing (K := K)) := by
  classical
  have hfin : Finite (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) := by
    apply Nat.finite_of_card_ne_zero
    rw [card_H1_zmodTwo_maxProTwoGalK (K := K)]
    positivity
  haveI := hfin
  have hcard : Nat.card (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) = 2 ^ (2 * h + 4) := by
    rw [card_H1_zmodTwo_maxProTwoGalK (K := K), hdeg,
      show 2 * h + 2 + 2 = 2 * h + 4 from by omega]
  obtain ⟨Φ, hGram, hΦkappa⟩ :=
    evenFrameAdaptedModelEquiv (isCupFormFp2_frattiniFrameCup (K := K))
      (nondegFp2_frattiniFrameCup (K := K)) (frattiniFrameCup_kappa (K := K))
      (evenFrameCup_kappa_self (K := K) ⟨h + 1, by omega⟩)
      (evenEndpoint_kappa_of_rangeN hα hrange) hcard
  refine evenFrameDeep_of_realizers (vN (h := h) α) Φ hGram fun i ↦ ?_
  obtain ⟨g', hg'⟩ := frattiniFrameEval_realizable (K := K) hfin
    ((evenFrameCoordL i).comp Φ.toLinearMap)
  have hD : ∀ x, frattiniFrameEval x g' = evenFrameCoord i (Φ x) := fun x ↦ hg' x
  have hmemg : chiCycKTwo (K := K) g' ∈ imChiN α := by
    rw [← hrange]; exact ⟨g', rfl⟩
  have hmemv : vN (h := h) α i ∈ imChiN α := by
    obtain ⟨y, hy⟩ := evenClimb_vN_mem_range (h := h) hrange i
    rw [← hrange]; exact ⟨y, hy⟩
  have hpar : Multiplicative.toAdd (unitsModFourParity
        (Units.map (PadicInt.toZModPow 2).toMonoidHom (chiCycKTwo (K := K) g'))) =
      Multiplicative.toAdd (unitsModFourParity
        (Units.map (PadicInt.toZModPow 2).toMonoidHom (vN (h := h) α i))) := by
    rw [← frattiniFrameEval_modFour, hD (cyclotomicModFourClassKTwo (K := K)), hΦkappa,
      evenFrameCoord_kappaVec, evenDegreeN_parity_table hα i]
  obtain ⟨x, hx1, hx2⟩ := (evenClimb_deepRowSupply_n (h := h) hα hrange).lift 2 (le_refl 2) i g'
    (evenEndpoint_nShadow hα hmemg hmemv hpar)
  exact ⟨x, hx1, fun z ↦ (frattiniFrameEval_eq_of_levelMk_eq z hx2).symm.trans (hD z)⟩

end NFrame

/-! ## §3 The `N` level-three base

The frame is cashed exactly as `evenFrameDeep_mStageBase` cashes its own, and exactly as the
committed `evenLevelThreeN_stageBase` cashes the frame it gets from the refuted seam: the
level-three relation realization of `StageAbstractionEvenTransgression.lean` and
`Frame.toLevelThree`.  Only the producer of the frame differs.

The `MarkedRecip` bundle disappears here.  `evenLevelThreeN_stageBase` carries one and does not
consume it (its own docstring says so, and it is carried only for parity with the odd twin);
since §2 does not go through that theorem, the base below has no bundle binder, and neither do
the endpoints that consume it at a given depth. -/

section NBase

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The `N` level-three base, re-cut.**  `evenLevelThreeN_stageBase` with its refuted
`RowExactLevelFibreLiftSupply (vN α)` binder, its `EvenDegreeNModEightImage` seam, its
ramified-`i` binder and its unused `MarkedRecip` bundle all removed: only the branch
identification remains.  This discharges `Hbase` of `evenPerK_orientedEquivN` at the depth the
range identity produces. -/
theorem evenEndpoint_nStageBase {α h : ℕ} (hα : 2 ≤ α)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN α) :
    Nonempty (Tuple (nStageWord α h (Nat.le_of_succ_le hα)) (vN α)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) 3) := by
  obtain ⟨F, hcup⟩ := evenEndpoint_nFrame_of_range (h := h) hα (by omega) hrange
  exact ⟨F.toLevelThree
    (evenTransgression.nLevelThreeRelationRealization_fieldCup K hα
      (evenLevelThree_isEvenGram h) F hcup)
    (maxProTwoGalK_isTopologicallyFinGen K) isProP_maxProPQuotient⟩

end NBase

/-! ## §4 The reduced `M` flip supply

`EvenDigitFlipSupply` asks for one flip per coordinate.  On the `M` row the coordinate-`2` flip
is a theorem (`evenDigit_flipSlotTwo_M`): the row of coordinate `2` is the cross bracket
`[p, base 3]`, so a power of `base 3` has literally trivial row, and `vM α 3 = mUnit α` has
exact level `α`, which makes the `2^(k-2)`-th power sharp at `k + α - 2`.  A carried input must
not contain a theorem, so the `M` branch carries the supply with that demand deleted. -/

section OffTwo

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h : ℕ}

/-- **The digit flip supply off coordinate `2`.**  `EvenDigitFlipSupply` verbatim, with the
demand at `i₀ = 2` deleted.  On the `M` row the deleted demand is a theorem, so this asks
strictly less and gives exactly as much (§4's `evenEndpoint_mFlip_iff_offTwo`); on a general row
table it is a genuine weakening, which is why it is stated separately rather than replacing the
committed `Prop`. -/
def EvenDigitFlipSupplyOffTwo (α : ℕ) {h : ℕ} (W : StageWord (MarkedCore.coreRank h))
    (v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ) (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (chi : ContinuousMonoidHom G ℤ_[2]ˣ) : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ (T : Tuple W v G chi k) (i₀ : Fin (MarkedCore.coreRank h)), i₀ ≠ 2 →
    ∃ F : EvenRawDepthCorrection G h k,
      evenRawDbarWord (fun i ↦ canonLift G k (T.generators i)) F.correction = 1 ∧
      (∃ g : G, F.correction i₀ = levelMk G (k + 1) g ∧
        ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) ∧
      (∀ j : Fin (MarkedCore.coreRank h), j ≠ i₀ →
        ∃ g : G, F.correction j = levelMk G (k + 1) g ∧
          (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The full supply implies the reduced one, trivially. -/
theorem evenEndpoint_offTwo_of_flip {α : ℕ} {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}
    (H : EvenDigitFlipSupply α W v G chi) : EvenDigitFlipSupplyOffTwo α W v G chi :=
  fun k hk T i₀ _ ↦ H k hk T i₀

/-- **The reduced `M` supply gives the full one.**  The one deleted demand is
`evenDigit_flipSlotTwo_M`.  So on the `M` row nothing is lost by carrying the reduced statement,
and the slot-`2` flip leaves the carried set for good. -/
theorem evenEndpoint_mFlip_of_offTwo {α : ℕ} (hα : 2 ≤ α) {hα₁ : 1 ≤ α}
    (H : EvenDigitFlipSupplyOffTwo α (mStageWord α h hα₁) (vM α) G chi) :
    EvenDigitFlipSupply α (mStageWord α h hα₁) (vM α) G chi := by
  intro k hk T i₀
  by_cases hi : i₀ = 2
  · subst hi
    exact evenDigit_flipSlotTwo_M hα hk T
  · exact H k hk T i₀ hi

/-- **The two `M` flip statements are equivalent**, for every `α ≥ 2`. -/
theorem evenEndpoint_mFlip_iff_offTwo {α : ℕ} (hα : 2 ≤ α) {hα₁ : 1 ≤ α} :
    EvenDigitFlipSupply α (mStageWord α h hα₁) (vM α) G chi ↔
      EvenDigitFlipSupplyOffTwo α (mStageWord α h hα₁) (vM α) G chi :=
  ⟨evenEndpoint_offTwo_of_flip, evenEndpoint_mFlip_of_offTwo hα⟩

/-! ### §4.1 The slot-`3` reduction

The backlog's second flip shave, reduced to one identity.  The `M` slot `3` cannot be discharged
the way slot `2` was: the row of coordinate `3` is `[p, base 2]`
(`evenRawDepthShiftHom_three_apply`) and the `M` table value at index `2` is `1`, so a power of
the bracket partner has no character digit at all.  What *does* work is the paired move.  The
core shift word pairs the two cross brackets,

  `… * (commP (correction 3) (base 2) * commP (correction 2) (base 3))`,

so the correction that places `base 3 ^ 2^(k-2)` at slot `3` **and** `base 2 ^ 2^(k-2)` at slot
`2` has row `[a^n, b] · [b^n, a]` with `a = base 3`, `b = base 2`, `n = 2^(k-2)`.  Its digits are
exactly right: slot `3` carries `(mUnit α)^(2^(k-2))`, sharp at `k + α - 2` by the telescoping,
and slot `2` carries `1^(2^(k-2)) = 1`, which is trivial at every depth, so the flip's
"trivial elsewhere" clause survives the second placement.

So the whole slot-`3` demand is the single identity `[a^n, b] · [b^n, a] = 1` in
`levelQuot G (k + 1)`, which is a Hall-Petrescu statement about the two-central filtration and is
not in the tree.  This section states the reduction, so that the backlog item is one identity
rather than a construction; the carried set of §5.1 is *not* changed, because the identity is
unproved. -/

section SlotThree

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h k : ℕ}

/-- The two cross-paired letters are distinct.  (`StageAbstractionEvenRawSpan.lean`'s index
lemmas are `private`, so the one this section needs is re-proved here.) -/
private theorem evenEndpoint_idx23 : (2 : Fin (MarkedCore.coreRank h)) ≠ 3 := fun hh ↦ by
  have := congrArg Fin.val hh
  rw [MarkedCore.coreVal_two, MarkedCore.coreVal_three] at this
  omega

/-- **The flip at coordinate `3`, from the paired move and a sharp table value at index `3`.**
Generic in the word datum and the table, exactly as `evenDigit_flip_two_of_sharp_value` is: what
is used is the exact level of `v 3`, the triviality of `v 2`, the exact fibres of the tuple's
rows `2` and `3`, and the paired-move identity at those two generators. -/
theorem evenEndpoint_flip_three_of_pairedMove {α : ℕ} {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ} (hα : 2 ≤ α) (a : ℤ_[2]ˣ)
    (hv3 : ((v 3 : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ α * (a : ℤ_[2])) (hv2 : v 2 = 1)
    (hk : 3 ≤ k) (T : Tuple W v G chi k)
    (hpair : commP (canonLift G k (T.generators 3) ^ 2 ^ (k - 2))
          (canonLift G k (T.generators 2)) *
        commP (canonLift G k (T.generators 2) ^ 2 ^ (k - 2))
          (canonLift G k (T.generators 3)) = 1) :
    ∃ F : EvenRawDepthCorrection G h k,
      evenRawDbarWord (fun i ↦ canonLift G k (T.generators i)) F.correction = 1 ∧
      (∃ g : G, F.correction 3 = levelMk G (k + 1) g ∧
        ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) ∧
      (∀ j : Fin (MarkedCore.coreRank h), j ≠ 3 →
        ∃ g : G, F.correction j = levelMk G (k + 1) g ∧
          (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) := by
  obtain ⟨x, hxchi, hxrep⟩ := T.rows 3
  obtain ⟨y, hychi, hyrep⟩ := T.rows 2
  set base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1) :=
    fun i ↦ canonLift G k (T.generators i) with hbase
  have hmem : ∀ i : Fin (MarkedCore.coreRank h),
      base i ^ 2 ^ (k - 2) ∈ lambdaImage G (k - 1) (k + 1) := by
    intro i
    have hm := pow_two_pow_mem_lambdaImage (base i) (k - 2)
    rwa [show 1 + (k - 2) = k - 1 by omega] at hm
  -- the two placements, and the group elements realising them
  have hlift : ∀ (i : Fin (MarkedCore.coreRank h)) (z : G), T.generators i = levelMk G k z →
      base i ^ 2 ^ (k - 2) = levelMk G (k + 1) (z ^ 2 ^ (k - 2)) := by
    intro i z hz
    have hbi : base i = canonLift G k (levelMk G k z) := by
      rw [show base i = canonLift G k (T.generators i) from rfl, hz]
    have h1 : base i ^ 2 = levelMk G (k + 1) z ^ 2 := by
      rw [hbi]
      exact (sq_levelMk_eq_sq_canonLift G k z).symm
    have hsplit : (2 : ℕ) * 2 ^ (k - 3) = 2 ^ (k - 2) := by
      rw [show k - 2 = k - 3 + 1 by omega, pow_succ']
    calc base i ^ 2 ^ (k - 2) = (base i ^ 2) ^ 2 ^ (k - 3) := by rw [← pow_mul, hsplit]
      _ = (levelMk G (k + 1) z ^ 2) ^ 2 ^ (k - 3) := by rw [h1]
      _ = levelMk G (k + 1) (z ^ 2 ^ (k - 2)) := by rw [← pow_mul, hsplit, ← map_pow]
  set F : EvenRawDepthCorrection G h k :=
    evenRawDepthCoordinateCorrection 3 ⟨base 3 ^ 2 ^ (k - 2), hmem 3⟩ *
      evenRawDepthCoordinateCorrection 2 ⟨base 2 ^ 2 ^ (k - 2), hmem 2⟩ with hF
  have hcorr : ∀ j : Fin (MarkedCore.coreRank h), F.correction j =
      (if j = 3 then base 3 ^ 2 ^ (k - 2) else 1) * (if j = 2 then base 2 ^ 2 ^ (k - 2) else 1) := by
    intro j
    rw [hF, EvenRawDepthCorrection.mul_correction, evenRawDepthCoordinateCorrection_apply,
      evenRawDepthCoordinateCorrection_apply]
  refine ⟨F, ?_, ?_, ?_⟩
  · -- the row is the paired move
    have hmul : ((evenRawDepthShiftHom base hk) F).1 =
        ((evenRawDepthShiftHom base hk)
            (evenRawDepthCoordinateCorrection 3 ⟨base 3 ^ 2 ^ (k - 2), hmem 3⟩)).1 *
          ((evenRawDepthShiftHom base hk)
            (evenRawDepthCoordinateCorrection 2 ⟨base 2 ^ 2 ^ (k - 2), hmem 2⟩)).1 := by
      rw [hF, map_mul]
      rfl
    show ((evenRawDepthShiftHom base hk) F).1 = 1
    rw [hmul, evenRawDepthShiftHom_three_apply base hk, evenRawDepthShiftHom_two_apply base hk]
    exact hpair
  · -- slot `3` is sharp
    refine ⟨x ^ 2 ^ (k - 2), ?_, ?_⟩
    · rw [hcorr 3, if_pos rfl, if_neg evenEndpoint_idx23.symm, mul_one]
      exact hlift 3 x hxrep
    · rw [map_pow, hxchi, show k + (α - 1) = k - 2 + α + 1 by omega]
      exact (evenDigit_pow_sharp (v 3) a hα hv3 (k - 2)).2
  · -- every other slot is trivial, the second placement included
    intro j hj
    by_cases hj2 : j = 2
    · subst hj2
      refine ⟨y ^ 2 ^ (k - 2), ?_, ?_⟩
      · rw [hcorr 2, if_neg evenEndpoint_idx23, if_pos rfl, one_mul]
        exact hlift 2 y hyrep
      · rw [map_pow, hychi, hv2, one_pow, Units.val_one]
        simp
    · refine ⟨1, ?_, ?_⟩
      · rw [hcorr j, if_neg hj, if_neg hj2, mul_one, map_one]
      · rw [map_one, Units.val_one]
        simp

/-- **The `M`-branch slot-`3` flip, from the paired move alone.**  `vM α 3 = mUnit α` has exact
level `α` and `vM α 2 = 1`, so the two table hypotheses of the reduction are discharged and the
whole demand is the identity `[a^n, b] · [b^n, a] = 1`.

Proving that identity at `a = base 3`, `b = base 2`, `n = 2^(k-2)` would let a future lane carry
the `M` flips off slots `2` **and** `3`, that is at `2 + 2h` of the `4 + 2h` coordinates. -/
theorem evenEndpoint_flipSlotThree_M_of_pairedMove {α : ℕ} (hα : 2 ≤ α) {hα₁ : 1 ≤ α}
    (hk : 3 ≤ k) (T : Tuple (mStageWord α h hα₁) (vM α) G chi k)
    (hpair : commP (canonLift G k (T.generators 3) ^ 2 ^ (k - 2))
          (canonLift G k (T.generators 2)) *
        commP (canonLift G k (T.generators 2) ^ 2 ^ (k - 2))
          (canonLift G k (T.generators 3)) = 1) :
    ∃ F : EvenRawDepthCorrection G h k,
      evenRawDbarWord (fun i ↦ canonLift G k (T.generators i)) F.correction = 1 ∧
      (∃ g : G, F.correction 3 = levelMk G (k + 1) g ∧
        ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) ∧
      (∀ j : Fin (MarkedCore.coreRank h), j ≠ 3 →
        ∃ g : G, F.correction j = levelMk G (k + 1) g ∧
          (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) :=
  evenEndpoint_flip_three_of_pairedMove hα (mUnit α)
    (by rw [vM_three]; exact mUnit_sub_one (by omega)) (vM_two α) hk T hpair

end SlotThree

end OffTwo

/-! ## §5 The at-depth endpoints

The composition proper.  Each branch is run at one field and one branch depth, with `hrange`
given rather than produced, which is the shape in which the two wave-53 advances actually meet:
KAPPA's base discharge and HUP's flip bridge both consume the identification at a *fixed* `α`,
and the committed `evenPerK_forwardGeneratorData{N,M}` is the unchanged seam between them.

Stating the endpoints at a fixed depth is also what removes the `MarkedRecip` bundle: the bundle
exists on this route only to produce `α` (`evenRange_range_eq_imChi{N,M}`), and §6 pays for it
once, there.

§5.1 first records the carried per-field inputs in their tightened `α ≥ 2` form, together with
the certificates that the wave-53 forms imply them, so that no consumer of a wave-53 statement
loses anything. -/

section AtDepth

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-! ### §5.1 The carried per-field inputs, at the depths the identity can produce -/

/-- **`Hfam` at one field, `N` branch**, at every branch depth `α ≥ 2`.  This is
`EvenPerKNFamilySupply` with the depth binder tightened from `1 ≤ alpha` to `2 ≤ alpha`, which
is the only stratum the range identity produces. -/
def EvenEndpointNFamily (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop :=
  ∀ (alpha : ℕ) (halpha : 2 ≤ alpha) (k : ℕ), 3 ≤ k →
    ∀ T : Tuple (nStageWord alpha h (Nat.le_of_succ_le halpha)) (vN alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F

/-- **`Hfam` at one field, `M` branch**, at every branch depth `α ≥ 2`. -/
def EvenEndpointMFamily (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop :=
  ∀ (alpha : ℕ) (halpha : 2 ≤ alpha) (k : ℕ), 3 ≤ k →
    ∀ T : Tuple (mStageWord alpha h (Nat.le_of_succ_le halpha)) (vM alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F

/-- **The flip supply at one field, `N` branch**, at every branch depth `α ≥ 2`.  No slot is
shaved here: every bracket partner of every squarefree `N` row has table value `1`, so the
partner-power construction `evenDigit_flip_two_of_sharp_value`, which is what discharges the `M`
slot `2`, produces nothing on this branch, and the whole supply is carried. -/
def EvenEndpointNFlip (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop :=
  ∀ (alpha : ℕ) (halpha : 2 ≤ alpha),
    EvenDigitFlipSupply alpha (nStageWord alpha h (Nat.le_of_succ_le halpha)) (vN alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))

/-- **The reduced flip supply at one field, `M` branch**, at every branch depth `α ≥ 2` and off
the slot `2` that `evenDigit_flipSlotTwo_M` already proves. -/
def EvenEndpointMFlipOffTwo (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop :=
  ∀ (alpha : ℕ) (halpha : 2 ≤ alpha),
    EvenDigitFlipSupplyOffTwo alpha (mStageWord alpha h (Nat.le_of_succ_le halpha)) (vM alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))

omit [FiniteDimensional ℚ_[2] K] in
/-- The wave-53 `N` family input implies the tightened one. -/
theorem evenEndpoint_nFamily_of_perK {h : ℕ} (H : EvenPerKNFamilySupply h K) :
    EvenEndpointNFamily h K :=
  fun alpha halpha ↦ H alpha (Nat.le_of_succ_le halpha)

omit [FiniteDimensional ℚ_[2] K] in
/-- The wave-53 `M` family input implies the tightened one. -/
theorem evenEndpoint_mFamily_of_perK {h : ℕ} (H : EvenPerKMFamilySupply h K) :
    EvenEndpointMFamily h K :=
  fun alpha halpha ↦ H alpha (Nat.le_of_succ_le halpha)

omit [FiniteDimensional ℚ_[2] K] in
/-- The wave-53 `N` flip input implies the tightened one. -/
theorem evenEndpoint_nFlip_of_perK {h : ℕ} (H : EvenPerKNDigitFlip h K) :
    EvenEndpointNFlip h K :=
  fun alpha halpha ↦ H alpha (Nat.le_of_succ_le halpha)

omit [FiniteDimensional ℚ_[2] K] in
/-- The wave-53 `M` flip input implies the tightened, slot-`2`-free one: first weaken the depth
binder, then delete the demand that is a theorem. -/
theorem evenEndpoint_mFlipOffTwo_of_perK {h : ℕ} (H : EvenPerKMDigitFlip h K) :
    EvenEndpointMFlipOffTwo h K :=
  fun alpha halpha ↦ evenEndpoint_offTwo_of_flip (H alpha (Nat.le_of_succ_le halpha))

/-! ### §5.2 The endpoints at one branch depth -/

/-- **The composed `N` endpoint at one field and one branch depth.**  Both wave-53 advances at
once, with the `N` half of KAPPA's re-cut (§2, §3) discharging the level-three base and HUP's
bridge turning the flips into `Hup`.  Carried: `Hfam` and the flips, and nothing else - no base,
no ramification binder, no reciprocity bundle, no mod-eight seam.

This is the shortest honest even statement of the whole route at a fixed depth, and its input
list is the odd route's. -/
theorem evenEndpoint_orientedEquivN_atDepth {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (nStageWord alpha h (Nat.le_of_succ_le halpha))
        (vN alpha) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F)
    (Hflip : EvenDigitFlipSupply alpha (nStageWord alpha h (Nat.le_of_succ_le halpha)) (vN alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) := by
  obtain ⟨base⟩ := evenEndpoint_nStageBase (h := h) halpha hev hrange
  exact nonempty_orientedEquivN_evenDegree_of_forwardGeneratorData alpha h
    (Nat.le_of_succ_le halpha) hev (EvenDemushkin.evenDem_nModelDemushkin alpha h halpha)
    (evenPerK_forwardGeneratorDataN halpha hrange base Hfam
      (evenDigit_perKRawToBracketN halpha hrange Hflip))

/-- **The composed `M` endpoint at one field and one branch depth.**  KAPPA's base discharge and
HUP's flip bridge at once, with the ramified-`i` binder discharged by §1 and the slot-`2` flip
deleted by §4.  Carried: `Hfam`, the flips off slot `2`, and the isotropy of the depth class,
which §7 shows cannot be dropped. -/
theorem evenEndpoint_orientedEquivM_atDepth {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (hiso : frattiniFrameCup (evenDeepClass alpha (Nat.le_of_succ_le halpha) hrange)
      (evenDeepClass alpha (Nat.le_of_succ_le halpha) hrange) = 0)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (mStageWord alpha h (Nat.le_of_succ_le halpha))
        (vM alpha) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F)
    (Hflip : EvenDigitFlipSupplyOffTwo alpha (mStageWord alpha h (Nat.le_of_succ_le halpha))
      (vM alpha) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) := by
  obtain ⟨base⟩ := evenFrameDeep_mStageBase (h := h) halpha hev
    (evenEndpoint_kappa_of_rangeM hrange) hrange hiso
  exact nonempty_orientedEquivM_evenDegree_of_forwardGeneratorData alpha h
    (Nat.le_of_succ_le halpha) hev (EvenDemushkin.evenDem_mModelDemushkin alpha h halpha)
    (evenPerK_forwardGeneratorDataM halpha hrange base Hfam
      (evenDigit_perKRawToBracketM halpha hrange (evenEndpoint_mFlip_of_offTwo halpha Hflip)))

end AtDepth

/-! ## §6 The per-field endpoints

The at-depth endpoints with `α` produced by the range identity, exactly as the committed
`evenPerK_orientedEquiv{N,M}` produce it, and with the carried inputs in their per-field form.
The branch inputs are unchanged: the `N` endpoint carries the ramified-`i` datum in its
norm-group form together with `-1 ∉ im χ`, and the `M` endpoint carries `-1 ∈ im χ` and no
ramification datum at all.

Note what has become of the ramified-`i` binder.  The `N` endpoint still carries `hram` because
`evenRange_range_eq_imChiN` needs it to produce `α`; what it no longer carries is the *frame*
form `κ ≠ 0`, which the committed endpoints paid separately.  The `M` endpoint carries neither. -/

section PerField

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The composed even `N` endpoint, per field.**  Every even-degree dyadic field of degree
`2 + 2h` whose `K(i)` is ramified and whose cyclotomic range omits `-1` has its own branch depth
`α ≥ 2` at which its maximal pro-`2` Galois group is oriented-isomorphic to the presented `N`
core, and the whole route costs two named inputs: the coordinate derivation family with its
relator kill, and the one-digit flip supply.

This supersedes `evenPerK_orientedEquivN` (which carries `Hbase`, `Hfam`, `Hup`) and
`evenDigit_orientedEquivN` (which carries `Hbase`, `Hfam`, flips): the level-three base is
discharged in §3. -/
theorem evenEndpoint_orientedEquivN {R : LocalReciprocity} (B : MarkedRecip R K)
    (deltaI : ℚ̄₂) (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI)
    (hneg : (-1 : ℤ_[2]ˣ) ∉ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hfam : EvenEndpointNFamily h K) (Hflip : EvenEndpointNFlip h K) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) := by
  obtain ⟨alpha, halpha, hrange⟩ := evenRange_range_eq_imChiN B deltaI hdeltaI hram hneg
  exact ⟨alpha, halpha, evenEndpoint_orientedEquivN_atDepth halpha hrange hev
    (Hfam alpha halpha) (Hflip alpha halpha)⟩

/-- **The composed even `M` endpoint, per field.**  The `M` twin, with `-1 ∈ im χ` in place of
the two `N` branch inputs and with the isotropy of the depth class as the one datum the `M`
branch owes above `α = 2`.

This supersedes `evenPerK_orientedEquivM` (`Hbase`, `Hfam`, `Hup`), `evenDigit_orientedEquivM`
(`Hbase`, `Hfam`, flips) and `evenFrameDeep_orientedEquivM` (`κ ≠ 0`, `Hiso`, `Hfam`, `Hup`): the
base is discharged as in the last of those, the ramified-`i` binder is discharged by §1, the
raw-to-bracket input is in flip form, and slot `2` of the flips is a theorem. -/
theorem evenEndpoint_orientedEquivM {R : LocalReciprocity} (B : MarkedRecip R K)
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hiso : EvenDeepMIsotropicSupply K)
    (Hfam : EvenEndpointMFamily h K) (Hflip : EvenEndpointMFlipOffTwo h K) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) := by
  obtain ⟨alpha, halpha, hrange⟩ := evenRange_range_eq_imChiM B hneg
  exact ⟨alpha, halpha, evenEndpoint_orientedEquivM_atDepth halpha hrange hev
    (Hiso alpha halpha hrange) (Hfam alpha halpha) (Hflip alpha halpha)⟩

end PerField

/-! ## §7 The `α = 2` stratum, and the sharpness of what is left

**The two endpoints of this section are vacuous.**  Wave 55's `evenFlip_not_flipSupply_two`
refutes `EvenDigitFlipSupply 2` on every row table as soon as an `α = 2` stage tuple exists, and
at a field of branch depth `2` one does (`EvenRouteCarried.evenRouteCarried_{n,m}Tuple_two`).  So
`evenEndpoint_orientedEquiv{N,M}_two` have unsatisfiable hypotheses exactly at the fields they
were written for.  The two statements are correct and are kept; what is retracted is the claim
that they cover the stratum.  §7.2's sharpness statements are unaffected.

On the stratum the range identity actually reaches by a committed route, the `M` isotropy is a
theorem (`evenFrameDeep_isotropic_two`), so both branches carry exactly `Hfam` and the flips,
with slot `2` free on `M`.  Neither stratum endpoint carries a reciprocity bundle or a
ramification binder: `hrange` is given, and §1 reads the binder off it.

§7.2 records why the isotropy is the honest residue on `M` and not on `N`: on `M` it is
*equivalent* to the existence of the frame, and on `N` its analogue is the committed
`evenFrameCup_kappa_self`, free at even degree. -/

section AlphaTwo

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The composed `N` endpoint on the `α = 2` stratum.**  Two inputs, `Hfam` and the flips. -/
theorem evenEndpoint_orientedEquivN_two {h : ℕ}
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN 2)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (nStageWord 2 h one_le_two) (vN 2)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F)
    (Hflip : EvenDigitFlipSupply 2 (nStageWord 2 h one_le_two) (vN 2)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    Nonempty (OrientedContinuousMulEquiv (chiN 2 h) (chiCycKTwo (K := K))) :=
  evenEndpoint_orientedEquivN_atDepth (le_refl 2) hrange hev Hfam Hflip

/-- **The composed `M` endpoint on the `α = 2` stratum.**  Two inputs as well: the isotropy is
discharged by `evenFrameDeep_isotropic_two`, and the slot-`2` flip by
`evenDigit_flipSlotTwo_M`.  So on this stratum the even `M` branch owes exactly what the odd
route owes, minus one slot. -/
theorem evenEndpoint_orientedEquivM_two {h : ℕ}
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM 2)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (mStageWord 2 h one_le_two) (vM 2)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F)
    (Hflip : EvenDigitFlipSupplyOffTwo 2 (mStageWord 2 h one_le_two) (vM 2)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    Nonempty (OrientedContinuousMulEquiv (chiM 2 h) (chiCycKTwo (K := K))) := by
  refine evenEndpoint_orientedEquivM_atDepth (le_refl 2) hrange hev ?_ Hfam Hflip
  exact evenFrameDeep_isotropic_two (h := h) (by omega)
    (evenEndpoint_kappa_of_rangeM hrange) hrange

/-! ### §7.2 Why the `M` isotropy stays and the `N` one does not -/

/-- **The `M` isotropy is exactly the `M` frame**, with the ramified-`i` binder discharged.
`evenFrameDeep_mFrame_iff_isotropic` with one hypothesis fewer: so no bookkeeping removes the
input, and any route to the `M` level-three base through a cup-adapted frame pays it. -/
theorem evenEndpoint_mIso_iff_frame {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha) :
    (∃ F : Frame (vM (h := h) alpha) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)),
        F.IsCupAdapted (evenFrameGram h) (evenFramePairing (K := K))) ↔
      frattiniFrameCup (evenDeepClass alpha (Nat.le_of_succ_le halpha) hrange)
        (evenDeepClass alpha (Nat.le_of_succ_le halpha) hrange) = 0 :=
  evenFrameDeep_mFrame_iff_isotropic halpha (by omega)
    (evenEndpoint_kappa_of_rangeM hrange) hrange

omit [T2Space (GalK K)] in
/-- **The `N` analogue of the isotropy input is a theorem.**  On `imChiN α` the depth class is
`κ` itself (`evenDeep_digit_imChiN`), and the isotropy of `κ` at even degree is the committed
`evenFrameCup_kappa_self`.  That single fact is the whole reason §2 needs no input and
`evenFrameDeep_mFrame_of_range` does. -/
theorem evenEndpoint_nIso {h : ℕ} (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    frattiniFrameCup (cyclotomicModFourClassKTwo (K := K))
      (cyclotomicModFourClassKTwo (K := K)) = 0 :=
  evenFrameCup_kappa_self (K := K) ⟨h + 1, by omega⟩

end AlphaTwo

/-! ## §8 The honest carried-input list

**Superseded; do not quote this section.**  All four structures below are false at a field whose
branch depth is `2` (wave 55's flip refutation, reported at the head of this file), the `M` one
has a third field that is a theorem, and all four leave the depth binder unguarded.  The
corrected artefact is `EvenRouteCarried.EvenRouteCarriedDeep{N,M}` in
`GQ2/Dyadic/Instances/EvenRouteCarried.lean`, two fields per branch, guarded by the range
identity, at `α ≥ 3`.  What follows is kept unchanged as the wave-54 record.

The artefact.  One `Prop` per branch per stratum, whose fields are *exactly* the inputs the even
route still carries after this lane, and one endpoint theorem per bundle, so that the list can
be read off a Lean statement rather than off prose.  Nothing else is a hypothesis of those four
theorems except the branch data that produces the identification (`B`, the ramification datum
and the sign condition on `N`; `B` and the sign condition on `M`; on the strata, `hrange`
itself) and the even-degree binder `hev`.

Read against the committed lists:

* `evenPerK_orientedEquiv{N,M}` carry `Hbase + Hfam + Hup`, plus `κ ≠ 0` on the strata;
* `evenDigit_orientedEquiv{N,M}` carry `Hbase + Hfam +` flips, plus `κ ≠ 0` on the strata;
* `evenFrameDeep_orientedEquivM` carries `κ ≠ 0 + Hiso + Hfam + Hup`;
* the four bundles below carry, respectively, `Hfam +` flips; `Hfam +` flips off slot `2` `+
  Hiso`; `Hfam +` flips; `Hfam +` flips off slot `2`.

`evenRoute_carried{N,M}_of_perK` certify the reading in the only direction that could hide a
strengthening: the wave-53 inputs *imply* the bundles, so every consumer holding the old data
holds the new. -/

section Carried

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **What the even route carries on the `N` branch, at every branch depth.**  Two inputs, the
odd route's two: a coordinate derivation family with its relator kill, and the one-digit flip
supply.  No level-three base, no ramification binder, no raw-to-bracket span equality.

**Corrected.**  The `flip` field is false at a field of branch depth `2`
(`EvenRouteCarried.evenRouteCarried_not_carriedN`), and the depth binder is unguarded.  Above the
refuted stratum the flip demand is one coordinate, not the whole supply.  See
`EvenRouteCarried.EvenRouteCarriedDeepN`, which also drops the binder asymmetry with the `M` twin:
neither corrected bundle needs `[FiniteDimensional ℚ_[2] K]`, which this one lacked and its twin
carried only for the isotropy field. -/
structure EvenRouteCarriedN (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop where
  /-- `Hfam`: the coordinate derivation family with its relator kill, at every `α ≥ 2`. -/
  family : EvenEndpointNFamily h K
  /-- The one-digit flip supply, at every `α ≥ 2` and at every slot. -/
  flip : EvenEndpointNFlip h K

/-- **What the even route carries on the `M` branch, at every branch depth.**  Three inputs: the
`N` two, with the flips one slot shorter, plus the isotropy of the depth class, which §7 proves
equivalent to the existence of the `M`-row frame and hence not removable.

**Corrected.**  The third field is a theorem, `EvenDeepIsotropy.evenDeepMIsotropicSupply_holds`,
so "not removable" is wrong: it is unavoidable but free.  The `flip` field is false at a
depth-`2` field (wave 55).  Two fields, guarded, at `α ≥ 3`, in
`EvenRouteCarried.EvenRouteCarriedDeepM`. -/
structure EvenRouteCarriedM (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop where
  /-- `Hfam`, `M` branch. -/
  family : EvenEndpointMFamily h K
  /-- The one-digit flip supply off the slot `2` that `evenDigit_flipSlotTwo_M` proves. -/
  flip : EvenEndpointMFlipOffTwo h K
  /-- The isotropy `frattiniFrameCup μ μ = 0` of the depth class, at every `α ≥ 2`. -/
  isotropy : EvenDeepMIsotropicSupply K

/-- **What the even route carries on the `N` branch at `α = 2`.**  The same two inputs, at the
one depth.

**Refuted.**  This `Prop` has no model at a field of branch depth `2`
(`EvenRouteCarried.evenRouteCarried_not_carriedNTwo`), because wave 55 refutes the flip supply at
`α = 2`.  `evenRoute_orientedEquivN_two` is therefore vacuous. -/
structure EvenRouteCarriedNTwo (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop where
  /-- `Hfam` at `α = 2`. -/
  family : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (nStageWord 2 h one_le_two) (vN 2)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
    ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F
  /-- The flip supply at `α = 2`. -/
  flip : EvenDigitFlipSupply 2 (nStageWord 2 h one_le_two) (vN 2)
    (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))

/-- **What the even route carries on the `M` branch at `α = 2`.**  Two inputs: the isotropy is a
theorem here (`evenFrameDeep_isotropic_two`), so the `M` branch owes exactly what the `N` branch
owes, minus the slot-`2` flip.

**Refuted.**  As for the `N` twin: no model at a field of branch depth `2`
(`EvenRouteCarried.evenRouteCarried_not_carriedMTwo`), so `evenRoute_orientedEquivM_two` is
vacuous. -/
structure EvenRouteCarriedMTwo (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop where
  /-- `Hfam` at `α = 2`, `M` branch. -/
  family : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (mStageWord 2 h one_le_two) (vM 2)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
    ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F
  /-- The reduced flip supply at `α = 2`. -/
  flip : EvenDigitFlipSupplyOffTwo 2 (mStageWord 2 h one_le_two) (vM 2)
    (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))

omit [FiniteDimensional ℚ_[2] K] in
/-- The wave-53 `N` inputs imply the bundle: nothing below is a strengthening. -/
theorem evenRoute_carriedN_of_perK {h : ℕ} (Hfam : EvenPerKNFamilySupply h K)
    (Hflip : EvenPerKNDigitFlip h K) : EvenRouteCarriedN h K :=
  ⟨evenEndpoint_nFamily_of_perK Hfam, evenEndpoint_nFlip_of_perK Hflip⟩

/-- The wave-53 `M` inputs, plus KAPPA's isotropy supply, imply the bundle. -/
theorem evenRoute_carriedM_of_perK {h : ℕ} (Hfam : EvenPerKMFamilySupply h K)
    (Hflip : EvenPerKMDigitFlip h K) (Hiso : EvenDeepMIsotropicSupply K) :
    EvenRouteCarriedM h K :=
  ⟨evenEndpoint_mFamily_of_perK Hfam, evenEndpoint_mFlipOffTwo_of_perK Hflip, Hiso⟩

/-- **The even `N` route, from the carried bundle and nothing else.** -/
theorem evenRoute_orientedEquivN {R : LocalReciprocity} (B : MarkedRecip R K)
    (deltaI : ℚ̄₂) (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI)
    (hneg : (-1 : ℤ_[2]ˣ) ∉ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) (C : EvenRouteCarriedN h K) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) :=
  evenEndpoint_orientedEquivN B deltaI hdeltaI hram hneg h hev C.family C.flip

/-- **The even `M` route, from the carried bundle and nothing else.** -/
theorem evenRoute_orientedEquivM {R : LocalReciprocity} (B : MarkedRecip R K)
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) (C : EvenRouteCarriedM h K) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) :=
  evenEndpoint_orientedEquivM B hneg h hev C.isotropy C.family C.flip

/-- **The even `N` route on the `α = 2` stratum, from the carried bundle and nothing else.** -/
theorem evenRoute_orientedEquivN_two {h : ℕ}
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN 2)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) (C : EvenRouteCarriedNTwo h K) :
    Nonempty (OrientedContinuousMulEquiv (chiN 2 h) (chiCycKTwo (K := K))) :=
  evenEndpoint_orientedEquivN_two hrange hev C.family C.flip

/-- **The even `M` route on the `α = 2` stratum, from the carried bundle and nothing else.** -/
theorem evenRoute_orientedEquivM_two {h : ℕ}
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM 2)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) (C : EvenRouteCarriedMTwo h K) :
    Nonempty (OrientedContinuousMulEquiv (chiM 2 h) (chiCycKTwo (K := K))) :=
  evenEndpoint_orientedEquivM_two hrange hev C.family C.flip

end Carried

end

end GQ2.Dyadic.EvenEndpoint

/-! ## §9 Axiom pins

Every public declaration of this file, printed, the two local coefficient-action instances
included.  §1's `κ` discharges and §4's flip reduction are character-level and expected at
std-3 together with whatever the committed row tables carry; §2, §3, §5 to §8 reach the field
layer and acquire exactly the census axioms of their committed inputs.  No axiom of this file is
new.

**The comparison the campaign's re-cut rule demands**, measured.  Each superseded print is
re-emitted below next to the new one, so the comparison is on the page and needs no cross-file
reading.  Write `S` for the seven-element set

  `[propext, Classical.choice, hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt,
   Quot.sound, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic]`

and `S⁻` for `S` without `hilbertSymbol_normCriterion_finiteDyadic`.  Then:

* every endpoint of this file prints exactly `S`;
* `evenPerK_orientedEquiv{N,M}` and `evenDigit_orientedEquiv{N,M}` print `S⁻`, and
  `evenFrameDeep_orientedEquivM` and all four committed `α = 2` endpoints print `S`.

So the four `α = 2` endpoints and the `M` endpoint of §6 are **character-identical** to the
committed statements they supersede, and the `N` endpoint of §6 **exceeds** the base-carrying
`evenPerK_orientedEquivN` / `evenDigit_orientedEquivN` by exactly
`hilbertSymbol_normCriterion_finiteDyadic`.  That difference is understood and is the same one
W53-KAPPA recorded for its `M` endpoint: it is the price of *building* the level-three base
instead of carrying it, since the frame layer's Witt adaptation runs through the Hilbert-symbol
norm criterion.  The honest comparison target for a base-building statement is a base-building
statement, and against those (`evenPerK_orientedEquiv{N,M}_two`, `evenFrameDeep_orientedEquivM`)
the print is equal, not larger.  No print here is a superset of a comparable one, and no axiom of
this file is new.

Two statement-level prints are worth naming: `EvenRouteCarriedM` and `evenRoute_carriedM_of_perK`
carry `tateDualityAt` because `EvenDeepMIsotropicSupply` mentions `frattiniFrameCup`, exactly as
the committed `EvenDeepMIsotropicSupply` does; and `evenEndpoint_nIso` prints `S` minus
`absGalQ2_isTopologicallyFinitelyGenerated`, being the committed `evenFrameCup_kappa_self`. -/

section AxiomPins

open GQ2.Dyadic.EvenEndpoint

-- the two coefficient-action instances
#print axioms evenEndpointScalar
#print axioms evenEndpointContinuousScalar

-- §1 the ramified-`i` binder, discharged
#print axioms evenEndpoint_kappa_of_value
#print axioms evenEndpoint_kappa_of_rangeN
#print axioms evenEndpoint_kappa_of_negOne
#print axioms evenEndpoint_kappa_of_rangeM

-- §2 the `N`-row frame from the deep seam
#print axioms evenEndpoint_nShadow
#print axioms evenEndpoint_nFrame_of_range

-- §3 the `N` level-three base
#print axioms evenEndpoint_nStageBase

-- §4 the reduced `M` flip supply
#print axioms EvenDigitFlipSupplyOffTwo
#print axioms evenEndpoint_offTwo_of_flip
#print axioms evenEndpoint_mFlip_of_offTwo
#print axioms evenEndpoint_mFlip_iff_offTwo
#print axioms evenEndpoint_flip_three_of_pairedMove
#print axioms evenEndpoint_flipSlotThree_M_of_pairedMove

-- §5.1 the carried per-field inputs and the wave-53 certificates
#print axioms EvenEndpointNFamily
#print axioms EvenEndpointMFamily
#print axioms EvenEndpointNFlip
#print axioms EvenEndpointMFlipOffTwo
#print axioms evenEndpoint_nFamily_of_perK
#print axioms evenEndpoint_mFamily_of_perK
#print axioms evenEndpoint_nFlip_of_perK
#print axioms evenEndpoint_mFlipOffTwo_of_perK

-- §5.2 the at-depth endpoints
#print axioms evenEndpoint_orientedEquivN_atDepth
#print axioms evenEndpoint_orientedEquivM_atDepth

-- §6 the per-field endpoints, against the committed ones they supersede
#print axioms evenEndpoint_orientedEquivN
#print axioms GQ2.Dyadic.EvenPerK.evenPerK_orientedEquivN
#print axioms GQ2.Dyadic.StageGeneric.evenDigit_orientedEquivN
#print axioms evenEndpoint_orientedEquivM
#print axioms GQ2.Dyadic.EvenPerK.evenPerK_orientedEquivM
#print axioms GQ2.Dyadic.StageGeneric.evenDigit_orientedEquivM
#print axioms GQ2.Dyadic.EvenFrameDeep.evenFrameDeep_orientedEquivM

-- §7 the `α = 2` stratum, against the committed strata
#print axioms evenEndpoint_orientedEquivN_two
#print axioms GQ2.Dyadic.EvenPerK.evenPerK_orientedEquivN_two
#print axioms GQ2.Dyadic.StageGeneric.evenDigit_orientedEquivN_two
#print axioms evenEndpoint_orientedEquivM_two
#print axioms GQ2.Dyadic.EvenPerK.evenPerK_orientedEquivM_two
#print axioms GQ2.Dyadic.StageGeneric.evenDigit_orientedEquivM_two
#print axioms evenEndpoint_mIso_iff_frame
#print axioms evenEndpoint_nIso

-- §8 the honest carried-input list
#print axioms EvenRouteCarriedN
#print axioms EvenRouteCarriedM
#print axioms EvenRouteCarriedNTwo
#print axioms EvenRouteCarriedMTwo
#print axioms evenRoute_carriedN_of_perK
#print axioms evenRoute_carriedM_of_perK
#print axioms evenRoute_orientedEquivN
#print axioms evenRoute_orientedEquivM
#print axioms evenRoute_orientedEquivN_two
#print axioms evenRoute_orientedEquivM_two

end AxiomPins

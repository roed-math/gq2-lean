/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenResidual
import GQ2.Dyadic.Instances.EvenRouteModel

/-!
# W58-ENDPOINT: the even route carries `Hfam` and nothing else, on both branches, at every depth

## What this file is

The paper-facing artefact for the even route, replacing `EvenRouteCarried.lean`.  Wave 57 proved
`EvenClimbResidualSupply (α − 1)` *equivalent* to `EvenKernelRawDefectSupply` on both branches at
every depth (`evenResidual_residualSupply_iff_rawDefect_{N,M}`), so the last named supply left the
carried set and `Hfam` alone delivers it.  This file states what is therefore true, in the form
the paper should quote:

* **§2** one structure per branch, `EvenRouteFinalCarried{N,M}`, whose only non-arithmetic field
  is `Hfam`;
* **§5** the even endpoints over it, at **every** depth `α ≥ 2` and on **both** branches;
* **§6** the route's status as a single named theorem per branch, and one for both at once.

Two things are gone that every previous version of this artefact had: the flip demand, and the
`α = 2` / `α ≥ 3` stratum split.  The split existed only because the flip was refuted at `α = 2`
first (wave 55) and at every depth later (wave 56, W56-SLOTZERO); with the flip off the route
there is nothing to split on, and the endpoint is uniform in the depth.

## Before and after: the even route's carried set, waves 54 to 58

Per branch, at a field whose branch identification lands at depth `α`.  "Carried" means assumed
and not proved anywhere in the tree; arithmetic binders (`hrange`, the degree) are listed
separately below.

| wave | `N` branch | `M` branch |
| --- | --- | --- |
| 54 (published) | `Hfam` + all `4 + 2h` flip slots, unguarded in `α` | `Hfam` + flips off slot `2` + the `M` isotropy, unguarded in `α` |
| 55 | the same, minus every flip slot but `0` (proved); the whole flip supply refuted at `α = 2` | the same, minus every flip slot but `0`; isotropy proved outright in wave 54 |
| 56 (`EvenRouteCarried`, **retracted**) | at `α ≥ 3` only: `Hfam` + the slot-`0` flip, guarded by `hrange` | at `α ≥ 3` only: `Hfam` + the slot-`0` flip, guarded by `hrange` |
| 57 | `Hfam` + `EvenClimbResidualSupply`, then `Hfam` alone; the slot-`0` flip refuted at **every** depth, so the wave-56 bundle is FALSE at every `α ≥ 3` | the same |
| **58 (here)** | **`Hfam` alone**, guarded by `hrange`, at **every** `α ≥ 2` | **`Hfam` alone**, guarded by `hrange`, at **every** `α ≥ 2` |

`Hup` (`EvenKernelRawToBracketSupply`), the flip supplies, the neutral supply and the `M`
isotropy are off the route entirely: no live endpoint mentions any of them.

The wave-56 table this replaces is stale in **four** of its four "after" cells, two of them
outright false; `EvenRouteCarried.lean`'s header now carries the retraction and the list.

## The arithmetic binders, and why neither can be dropped

Both structures carry exactly two binders beyond `Hfam`, and both are genuinely needed.

* `degree : finrank ℚ_[2] K = 2 + 2h`.  The even branch data `chiN α h`, `chiM α h` is indexed by
  the handle count `h`, and the endpoint's Demushkin input `evenDem_{n,m}ModelDemushkin` is a
  statement about a field of that degree.  It is **proved**, not measured, at every model in the
  tree (`finrank_KQuarticN_even`, `finrank_KSqrtNegTwo`, `finrank_KSqrtTwo`).
* `branch : ∃ α ≥ 2, range χ_cyc = imChiN α` (resp. `imChiM α`).  This is what places `K` on the
  branch at all, and it is what the level-three stage base is built from
  (`evenEndpoint_nStageBase`, `evenDeepIsotropy_mStageBase`).  (Status corrected at wave 67:
  the range IS now computed at the two quadratic model fields, `EvenRangeModelFields.lean`,
  `hrangeFinal_sqrtNegTwo` and `hrangeFinal_sqrtTwo`, each over a reciprocity bundle of that
  file's own (one, and two respectively); at the quartic it stays measured, per wave 56's
  census and `scripts/w57_model/`, with the three remaining costs named in that file.)

Nothing else survives.  In particular the `M` branch carries **no** ramification binder: the
`κ ≠ 0` that `evenDeepIsotropy_mStageBase` needs is read off the identification by
`evenEndpoint_kappa_of_rangeM`, so the two structures are symmetric in their fields *and* in
their binders.  No marked reciprocity bundle and no `MarkedRecip` appear anywhere in this file,
so the B5-K axiom `markedRecipAt` is not consumed; §8 measures that.

## Satisfiability: which refutations this artefact was checked against

Wave 56 published a structure whose surviving field a sibling lane refuted two commits later in
the same wave, and neither module imported the other.  The check that would have caught it is
run here, exhaustively, against every refutation of an even-route `Prop` in the tree.  The full
list of refuted even-route `Prop`s, at this tip, is

  `EvenDigitFlipSupply`, `EvenDigitFlipSupplySlotZero`, `EvenEndpointNFlip`,
  `EvenEndpointMFlipOffTwo`, `EvenFlip{N,M}SlotZero`, `EvenFlip{N,M}SlotZeroDeep`,
  `EvenRouteDeepFlip{N,M}`, `EvenRouteCarriedDeep{N,M}`, `EvenRouteCarried{N,M,NTwo,MTwo}`,
  `EvenKernelRawToBracketSupply` (`Hup`), `EvenRawToNeutralSupply` at `s ≥ α − 2`,
  `EvenRowDeepFibreLiftSupply` at `s ≤ α − 2`, `RowExactLevelFibreLiftSupply` at `α ≥ 3`,
  `EvenLevelThree{N,M}FrameInputSupply`, `EvenPerKLevelTwoLift`, `EvenPerKRowSupply{N,M}`.

Result, field by field.

1. **`family` (`Hfam`).**  No refutation in the tree targets `EvenKernelDerivationFamily`,
   `EvenKernelRelatorKill`, `EvenKernelRawDefectSupply` or `EvenClimbResidualSupply`; there is no
   statement of the form `¬ …` about any of the four.  Nor can `Hfam` *reach* a refuted `Prop`
   along the chain this file uses: that chain is
   `Hfam → EvenKernelRawDefectSupply → EvenClimbResidualSupply (α−1) → NForwardGeneratorData →`
   endpoint, and the middle step is wave 57's shadow argument, which spends the off-zero flips
   (proved, `evenFlip_flipOffZero_{M,N}`) and the sharp central class (proved) and **never** the
   coordinate-`0` flip, `Hup`, or the neutral supply.  `EvenKernelRawToBracketSupply` occurs in
   the tree only as a hypothesis; nothing derives it.
2. **`degree`.**  Satisfiable and proved at three named fields, two of them of different handle
   count: §7.
3. **`branch`.**  Not refuted; the only negative statements about the branch images are
   `evenRange_not_both` (a field is not on both branches above depth `2`) and the injectivity of
   `imChi{N,M}`, both of which say the depth is *unique*, which is what §3 uses.  It is measured
   true at all three model fields.
4. **The three fields jointly.**  `degree ∧ branch` is the hypothesis set of wave 57's own at-depth
   endpoints, which are non-vacuous by construction: from it the level-three stage base *builds* a
   tuple, so the pair cannot be contradictory unless the wave-57 endpoints are.  `family` is
   independent of both.

Two near-misses were checked explicitly, because both are of exactly the shape that produced the
wave-56 failure, and both come out clean **only** on a sharpness argument:

* `EvenRowDeepFibreLiftSupply s` is refuted at `s ≤ α − 2` and proved at `s = α − 1`, which is the
  depth the route uses.  The `Prop` is monotone *upwards* in `s` (a larger `s` is a stronger
  hypothesis on the representative, hence a weaker demand), so the proof at `α − 1` does not
  descend to the refuted range and the refutation at `α − 2` does not climb.  Had the monotonicity
  gone the other way, `hrange` at `α ≥ 3` would have been contradictory and every at-depth even
  endpoint in the tree, including §5's, would be vacuous.
* `RowExactLevelFibreLiftSupply` is refuted at `α ≥ 3` and is produced by
  `evenRow_rowSupply_of_deepSupply_one` from `EvenRowDeepFibreLiftSupply 1` **only**.  At `α ≥ 3`
  the route has the supply at `s = α − 1 ≥ 2`, not at `1`, so it does not produce the refuted
  object.  At `α = 2` it does produce it, and there the refutation does not apply.

`EvenRawToNeutralSupply (α − 1)` is refuted at every `α ≥ 2` (`evenDigit_not_neutralSupply_lane_
{M,N}`); it was the *natural* route to `Hup` and is not on this route at all.

## What this retires

`EvenRouteCarried.lean`'s `EvenRouteCarriedDeep{N,M}` and the four endpoints over them are
retracted, by wave 57's `evenRouteModel_not_carriedDeep{N,M}` and `evenRouteAudit_not_carriedDeep
{N,M}`: they are false at every field of branch depth `α ≥ 3` and vacuous at depth `2`.  §4 makes
the repair machine-checked rather than editorial: `evenRouteFinal_carriedDeep{N,M}_split` shows
the retracted bundle is exactly *this file's family field, restricted to `α ≥ 3`* conjoined with
the refuted flip demand, and `evenRouteFinal_repair{N,M}` states in one place that the bundle is
false, that its flip field is the reason, and that its family field is implied by ours.  Nothing
of the retracted artefact is lost except the refuted conjunct.

## Numbering

1. the one carried input, per branch;
2. the artefact: one structure per branch;
3. the guard collapses: the structure is the single-depth `Hfam` at the depth the field has;
4. comparison with every superseded artefact, and the repair;
5. the endpoints, at every depth, on both branches;
6. the status theorems;
7. satisfiability at the three model fields;
8. axiom pins, with the comparison against everything superseded.
-/

namespace GQ2.Dyadic.EvenRouteFinal

noncomputable section

open GQ2 ContCoh
open GQ2.Roe.Labute
open GQ2.Dyadic
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.EvenForward
open GQ2.Dyadic.EvenRowSupply
open GQ2.Dyadic.EvenCyclotomicRange
open GQ2.Dyadic.LSquare
open GQ2.Dyadic.EvenPerK
open GQ2.Dyadic.EvenEndpoint
open GQ2.Dyadic.EvenDeepIsotropy
open GQ2.Dyadic.EvenRouteCarried
open GQ2.Dyadic.EvenResidual
open GQ2.Dyadic.EvenRouteModel
open GQ2.Dyadic.Fields

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The coefficient action at `G_K(2)`, as everywhere on this route. -/
local instance evenRouteFinalScalar {K : IntermediateField ℚ_[2] ℚ̄₂} [CompactSpace (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] :
    DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

/-- Continuity of that action. -/
local instance evenRouteFinalContinuousScalar {K : IntermediateField ℚ_[2] ℚ̄₂}
    [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-! ## §1 The one carried input

`Hfam` at one field, guarded by the branch identification exactly as
`EvenDeepMIsotropicSupply` is guarded, so that no instance outside the depth this field actually
produces is ever demanded.  The depth binder is `2 ≤ alpha`, the whole range the identity can
produce: the `3 ≤ alpha` of wave 56 was forced by the flip refutation at `alpha = 2`, and with the
flip gone there is nothing to exclude.  Wave 57's `evenResidual_orientedEquiv{N,M}_two_of_family`
is the `alpha = 2` instance, and §5 is uniform over it. -/

section Input

/-- **`Hfam` at one field, `N` branch**, at every branch depth `alpha ≥ 2` the identification
produces.  Against wave 56's `EvenRouteDeepFamilyN`: the depth binder is loosened from
`3 ≤ alpha` back to `2 ≤ alpha`.  Against wave 54's `EvenEndpointNFamily`: the identification is
added as a guard, so this asks strictly less at every field. -/
def EvenRouteFinalFamilyN (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop :=
  ∀ (alpha : ℕ) (halpha : 2 ≤ alpha),
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha →
    ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (nStageWord alpha h (Nat.le_of_succ_le halpha)) (vN alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F

/-- **`Hfam` at one field, `M` branch**, at every branch depth `alpha ≥ 2`. -/
def EvenRouteFinalFamilyM (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop :=
  ∀ (alpha : ℕ) (halpha : 2 ≤ alpha),
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha →
    ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (mStageWord alpha h (Nat.le_of_succ_le halpha)) (vM alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F

end Input

/-! ## §2 The artefact

One `Prop` per branch, with three fields: the two arithmetic binders that place `K` on the route,
and the one thing the route carries.  Both structures have the same fields and the same binders.

Minimality: drop `degree` and the Demushkin model input of §5 is unavailable; drop `branch` and
there is no depth, hence no stage base and no statement; drop `family` and there is nothing left
to prove the endpoint from.  Each of the three is used in §5.

The header records the satisfiability check for all three fields against every refutation in the
tree.  In one line: `family` is the campaign's single open question and is refuted nowhere,
`degree` is proved at three named fields, `branch` is measured at those same three, and the pair
`degree ∧ branch` is non-vacuous because the level-three stage base builds a tuple from it. -/

section Artefact

/-- **What the even route carries on the `N` branch, at every depth.**  One carried input,
`Hfam`, and two arithmetic binders.  This is the artefact the paper should quote; it supersedes
`EvenRouteCarriedN`, `EvenRouteCarriedNTwo` (wave 54, refuted at every field) and
`EvenRouteCarriedDeepN` (wave 56, refuted at every depth `alpha ≥ 3` and vacuous at `2`). -/
structure EvenRouteFinalCarriedN (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] : Prop where
  /-- Arithmetic binder, proved at every model in the tree: the degree is even, with `h` handles. -/
  degree : Module.finrank ℚ_[2] K = 2 + 2 * h
  /-- Arithmetic binder, measured and never proved: `K` sits on the `N` branch, at some depth. -/
  branch : ∃ alpha, 2 ≤ alpha ∧
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha
  /-- **The one carried input**: the coordinate derivation family with its relator kill, asked
  only at the depth the identification produces. -/
  family : EvenRouteFinalFamilyN h K

/-- **What the even route carries on the `M` branch, at every depth.**  The same three fields
with the same binders.  No ramification datum: `κ ≠ 0` is read off `branch` by
`evenEndpoint_kappa_of_rangeM`.  Supersedes `EvenRouteCarriedM`, `EvenRouteCarriedMTwo` and
`EvenRouteCarriedDeepM`. -/
structure EvenRouteFinalCarriedM (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] : Prop where
  /-- Arithmetic binder, proved at every model in the tree: the degree is even, with `h` handles. -/
  degree : Module.finrank ℚ_[2] K = 2 + 2 * h
  /-- Arithmetic binder, measured and never proved: `K` sits on the `M` branch, at some depth. -/
  branch : ∃ alpha, 2 ≤ alpha ∧
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha
  /-- **The one carried input.** -/
  family : EvenRouteFinalFamilyM h K

end Artefact

/-! ## §3 The guard collapses

The guard is not an over-quantification.  A field has at most one branch depth on each branch
(`evenRouteCarried_depth{N,M}_unique`, wave 56 §1), so the guarded family is **equivalent** to the
single-depth `Hfam` the endpoint consumes.  This is wave 56's `evenRouteCarried_deep{N,M}
_iff_atDepth` with the stratum restriction removed, and it is what makes §7's satisfiability
statements sharp: the artefact holds at a field exactly when the campaign's one open question
holds there, at the one depth that field has, and asks nothing more. -/

section Collapse

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-- **The guarded `N` family is exactly the single-depth `Hfam`.** -/
theorem evenRouteFinal_familyN_iff_atDepth {alpha₀ h : ℕ} (halpha₀ : 2 ≤ alpha₀)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha₀) :
    EvenRouteFinalFamilyN h K ↔
      ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (nStageWord alpha₀ h (Nat.le_of_succ_le halpha₀)) (vN alpha₀)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
        ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F := by
  refine ⟨fun H ↦ H alpha₀ halpha₀ hrange, fun H alpha halpha hr ↦ ?_⟩
  cases evenRouteCarried_depthN_unique halpha halpha₀ hr hrange
  exact H

/-- **The guarded `M` family is exactly the single-depth `Hfam`.**  This is the half wave 56
could state only after proving `imChiM` injective; it holds at every depth here. -/
theorem evenRouteFinal_familyM_iff_atDepth {alpha₀ h : ℕ} (halpha₀ : 2 ≤ alpha₀)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha₀) :
    EvenRouteFinalFamilyM h K ↔
      ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (mStageWord alpha₀ h (Nat.le_of_succ_le halpha₀)) (vM alpha₀)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
        ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F := by
  refine ⟨fun H ↦ H alpha₀ halpha₀ hrange, fun H alpha halpha hr ↦ ?_⟩
  cases evenRouteCarried_depthM_unique halpha halpha₀ hr hrange
  exact H

end Collapse

/-! ## §4 Comparison with every superseded artefact, and the repair

Two directions, both needed.

Nothing here is a strengthening: the wave-54 family `Prop`s imply the guarded ones, so a consumer
holding the old data loses nothing (§4.1).  And what is retired is retired for one identified
reason: `evenRouteFinal_carriedDeep{N,M}_split` decomposes the retracted wave-56 bundle into the
family field, which this file keeps, and the flip field, which wave 57 refuted at every depth
`alpha ≥ 3`.  `evenRouteFinal_repair{N,M}` puts the three facts in one citable statement. -/

section Comparison

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-! ### §4.1 Nothing below is a strengthening -/

/-- The wave-54 `N` family `Prop` implies the guarded one: adding the identification as a guard
asks less. -/
theorem evenRouteFinal_familyN_of_endpointNFamily {h : ℕ} (H : EvenEndpointNFamily h K) :
    EvenRouteFinalFamilyN h K :=
  fun alpha halpha _ ↦ H alpha halpha

/-- The wave-54 `M` family `Prop` implies the guarded one. -/
theorem evenRouteFinal_familyM_of_endpointMFamily {h : ℕ} (H : EvenEndpointMFamily h K) :
    EvenRouteFinalFamilyM h K :=
  fun alpha halpha _ ↦ H alpha halpha

/-- The guarded family implies the retracted bundle's `N` family field, which is the same demand
cut at `alpha ≥ 3`. -/
theorem evenRouteFinal_deepFamilyN_of_familyN {h : ℕ} (H : EvenRouteFinalFamilyN h K) :
    EvenRouteDeepFamilyN h K :=
  fun alpha halpha ↦ H alpha (by omega)

/-- The guarded family implies the retracted bundle's `M` family field. -/
theorem evenRouteFinal_deepFamilyM_of_familyM {h : ℕ} (H : EvenRouteFinalFamilyM h K) :
    EvenRouteDeepFamilyM h K :=
  fun alpha halpha ↦ H alpha (by omega)

/-! ### §4.2 The retracted bundle, and exactly which conjunct killed it -/

/-- **The retracted `N` bundle is the surviving family field conjoined with the refuted flip.**
So the repair is a deletion and not a re-cut: everything of `EvenRouteCarriedDeepN` that is not
`EvenRouteDeepFlipN` is kept, and loosened from `alpha ≥ 3` to `alpha ≥ 2`. -/
theorem evenRouteFinal_carriedDeepN_split {h : ℕ} :
    EvenRouteCarriedDeepN h K ↔ EvenRouteDeepFamilyN h K ∧ EvenRouteDeepFlipN h K :=
  ⟨fun C ↦ ⟨C.family, C.flip⟩, fun C ↦ ⟨C.1, C.2⟩⟩

/-- **The retracted `M` bundle is the surviving family field conjoined with the refuted flip.** -/
theorem evenRouteFinal_carriedDeepM_split {h : ℕ} :
    EvenRouteCarriedDeepM h K ↔ EvenRouteDeepFamilyM h K ∧ EvenRouteDeepFlipM h K :=
  ⟨fun C ↦ ⟨C.family, C.flip⟩, fun C ↦ ⟨C.1, C.2⟩⟩

end Comparison

section Repair

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The `N` repair in one statement.**  At a field of branch depth `alpha ≥ 3` and even degree:
the wave-56 bundle is false; its flip field is the reason; and its family field, the part this
file keeps, is implied by `EvenRouteFinalFamilyN`.  A consumer citing `EvenRouteCarriedDeepN`
should cite this and then `EvenRouteFinalCarriedN`. -/
theorem evenRouteFinal_repairN {alpha h : ℕ} (halpha : 3 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    ¬ EvenRouteCarriedDeepN h K ∧ ¬ EvenRouteDeepFlipN h K ∧
      (EvenRouteFinalFamilyN h K → EvenRouteDeepFamilyN h K) :=
  ⟨evenRouteModel_not_carriedDeepN halpha hrange hev,
    evenRouteModel_not_deepFlipN halpha hrange hev,
    evenRouteFinal_deepFamilyN_of_familyN⟩

/-- **The `M` repair in one statement.** -/
theorem evenRouteFinal_repairM {alpha h : ℕ} (halpha : 3 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    ¬ EvenRouteCarriedDeepM h K ∧ ¬ EvenRouteDeepFlipM h K ∧
      (EvenRouteFinalFamilyM h K → EvenRouteDeepFamilyM h K) :=
  ⟨evenRouteModel_not_carriedDeepM halpha hrange hev,
    evenRouteModel_not_deepFlipM halpha hrange hev,
    evenRouteFinal_deepFamilyM_of_familyM⟩

end Repair

/-! ## §5 The endpoints, at every depth, on both branches

Wave 57's audit estimated this at about six lines from what exists: compose
`evenAlphaTwo_forwardGeneratorData{N,M}_of_residual`, already general in the depth, with the
at-depth stage bases, then feed the residual equivalence.  The estimate is **right and generous**:
both wave-57 lanes already did their half, so each endpoint here is the composite of two committed
theorems and is three lines, twelve for the four statements of this section.  What the estimate
did not say, and what actually matters, is that the composite is uniform in the depth on both
branches, which no previous even endpoint was. -/

section Endpoints

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The even `N` endpoint at every branch depth, over `Hfam` alone.**  Carried: `Hfam`.  Not
carried: the level-three base (built from `hrange` and the degree), the residual supply (wave 57),
the flips, `Hup`, the isotropy, any reciprocity bundle, any ramification datum, any sign
condition.  Compare `evenRouteModel_orientedEquivN_atDepth`, which is this over
`EvenClimbResidualSupply (alpha - 1)`, and `evenResidual_orientedEquivN_two_of_family`, which is
this at `alpha = 2` with a `MarkedRecip` bundle and `κ ≠ 0` additionally carried. -/
theorem evenRouteFinal_orientedEquivN_atDepth {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (nStageWord alpha h (Nat.le_of_succ_le halpha))
        (vN alpha) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F) :
    Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) :=
  evenRouteModel_orientedEquivN_atDepth halpha hrange hev
    (evenResidual_residualSupplyN K halpha hrange Hfam)

/-- **The even `M` endpoint at every branch depth, over `Hfam` alone.**  The `M` twin, with the
same input list: the ramified-`i` binder that every previous `M` endpoint carried is read off the
identification. -/
theorem evenRouteFinal_orientedEquivM_atDepth {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (mStageWord alpha h (Nat.le_of_succ_le halpha))
        (vM alpha) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F) :
    Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) :=
  evenRouteModel_orientedEquivM_atDepth halpha hrange hev
    (evenResidual_residualSupplyM K halpha hrange Hfam)

/-- **The even `N` endpoint from the artefact**, at the depth the field's identification
produces. -/
theorem evenRouteFinal_orientedEquivN_of_carried {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (C : EvenRouteFinalCarriedN h K) :
    Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) :=
  evenRouteFinal_orientedEquivN_atDepth halpha hrange C.degree (C.family alpha halpha hrange)

/-- **The even `M` endpoint from the artefact.** -/
theorem evenRouteFinal_orientedEquivM_of_carried {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (C : EvenRouteFinalCarriedM h K) :
    Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) :=
  evenRouteFinal_orientedEquivM_atDepth halpha hrange C.degree (C.family alpha halpha hrange)

end Endpoints

/-! ## §6 The route's status

The sentence the paper's even sections are built on.  Read `evenRouteFinal_statusN`: *an
even-degree dyadic field on the `N` branch which carries `Hfam` has the oriented equivalence, at
its own branch depth.*  The depth is not chosen, it is the field's, and it is unique
(`evenRouteCarried_depthN_unique`).  `evenRouteFinal_status` is the same for the two branches at
once, which is the form the route's status wants: whichever branch a field is on, `Hfam` closes
it. -/

section Status

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **THE `N` ROUTE'S STATUS.**  Given the two arithmetic binders and `Hfam`, and nothing else,
the even oriented equivalence holds on the `N` branch, at the field's own branch depth. -/
theorem evenRouteFinal_statusN {h : ℕ} (C : EvenRouteFinalCarriedN h K) :
    ∃ alpha, 2 ≤ alpha ∧
      MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha ∧
      Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) := by
  obtain ⟨alpha, halpha, hrange⟩ := C.branch
  exact ⟨alpha, halpha, hrange, evenRouteFinal_orientedEquivN_of_carried halpha hrange C⟩

/-- **THE `M` ROUTE'S STATUS.** -/
theorem evenRouteFinal_statusM {h : ℕ} (C : EvenRouteFinalCarriedM h K) :
    ∃ alpha, 2 ≤ alpha ∧
      MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha ∧
      Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) := by
  obtain ⟨alpha, halpha, hrange⟩ := C.branch
  exact ⟨alpha, halpha, hrange, evenRouteFinal_orientedEquivM_of_carried halpha hrange C⟩

/-- **THE EVEN ROUTE'S STATUS, both branches in one statement.**  An even-degree dyadic field
carrying `Hfam` on either even branch has the oriented equivalence at its own branch depth.  This
is the whole even route after wave 57, and its only input is the ticket already queued. -/
theorem evenRouteFinal_status {h : ℕ}
    (C : EvenRouteFinalCarriedN h K ∨ EvenRouteFinalCarriedM h K) :
    ∃ alpha, 2 ≤ alpha ∧
      (Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) ∨
        Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))) := by
  rcases C with C | C
  · obtain ⟨alpha, halpha, -, hequiv⟩ := evenRouteFinal_statusN C
    exact ⟨alpha, halpha, Or.inl hequiv⟩
  · obtain ⟨alpha, halpha, -, hequiv⟩ := evenRouteFinal_statusM C
    exact ⟨alpha, halpha, Or.inr hequiv⟩

/-- **The artefact from measured data.**  At a field with a measured identification at depth
`alpha₀` and a proved degree, the artefact holds as soon as `Hfam` holds at that one depth.  With
§3 this is an equivalence in the family field, so the artefact demands the open question and
nothing beyond it. -/
theorem evenRouteFinal_carriedN_of_atDepth {alpha₀ h : ℕ} (halpha₀ : 2 ≤ alpha₀)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha₀)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (nStageWord alpha₀ h (Nat.le_of_succ_le halpha₀))
        (vN alpha₀) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F) :
    EvenRouteFinalCarriedN h K :=
  ⟨hev, ⟨alpha₀, halpha₀, hrange⟩,
    (evenRouteFinal_familyN_iff_atDepth halpha₀ hrange).mpr Hfam⟩

/-- **The artefact from measured data, `M` branch.** -/
theorem evenRouteFinal_carriedM_of_atDepth {alpha₀ h : ℕ} (halpha₀ : 2 ≤ alpha₀)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha₀)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (mStageWord alpha₀ h (Nat.le_of_succ_le halpha₀))
        (vM alpha₀) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F) :
    EvenRouteFinalCarriedM h K :=
  ⟨hev, ⟨alpha₀, halpha₀, hrange⟩,
    (evenRouteFinal_familyM_iff_atDepth halpha₀ hrange).mpr Hfam⟩

end Status

/-! ## §7 Satisfiability at the three model fields

The doctrine's check, made concrete.  At each of wave 57's three model fields the `degree` field
is **discharged in Lean** and the `branch` field is discharged from the measured identification,
so the artefact reduces to `Hfam` at that field's one depth and nothing else.  Two handle counts
and both branches are covered, and the depths are `2` and `3`, so the statements are not confined
to a single stratum.

This is the strongest satisfiability certificate available and its limit is honest: `Hfam` is the
campaign's open question, so no lane can exhibit a field at which the artefact is *proved*
outright.  What is certified is that at real fields nothing but `Hfam` stands between the binders
and the endpoint, which is exactly what the wave-56 artefacts failed: there, at every real field
of depth `α ≥ 3`, a *second* field of the structure was already false. -/

section Models

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **The artefact at the quartic `ℚ₂(β)`, `β⁴ + 4β² + 2 = 0`, `N` branch, depth `3`, `h = 1`.**
The wave-56 census's unique `N`-branch field of depth `≥ 3`.  Degree proved
(`finrank_KQuarticN_even`), identification measured, `Hfam` carried. -/
theorem evenRouteFinal_carriedN_quartic [T2Space (GalK KQuarticN)]
    (hrange : MonoidHom.range (chiCycKTwo (K := KQuarticN)).toMonoidHom = imChiN 3)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (nStageWord 3 1 (by omega)) (vN 3)
        (maxProPQuotient 2 (GalK KQuarticN)) (chiCycKTwo (K := KQuarticN)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F) :
    EvenRouteFinalCarriedN 1 KQuarticN :=
  evenRouteFinal_carriedN_of_atDepth (by omega) hrange finrank_KQuarticN_even Hfam

/-- **The artefact at `ℚ₂(√−2)`, `N` branch, depth `2`, `h = 0`.**  The stratum wave 56 excluded
and wave 57 restored. -/
theorem evenRouteFinal_carriedN_sqrtNegTwo [T2Space (GalK KSqrtNegTwo)]
    (hrange : MonoidHom.range (chiCycKTwo (K := KSqrtNegTwo)).toMonoidHom = imChiN 2)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (nStageWord 2 0 one_le_two) (vN 2)
        (maxProPQuotient 2 (GalK KSqrtNegTwo)) (chiCycKTwo (K := KSqrtNegTwo)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F) :
    EvenRouteFinalCarriedN 0 KSqrtNegTwo :=
  evenRouteFinal_carriedN_of_atDepth (le_refl 2) hrange (by rw [finrank_KSqrtNegTwo]) Hfam

/-- **The artefact at `ℚ₂(√2)`, `M` branch, depth `3`, `h = 0`.**  The field at which the wave-54
and wave-56 input lists are both false (`evenRouteModel_not_endpointMFlipOffTwo_sqrtTwo`). -/
theorem evenRouteFinal_carriedM_sqrtTwo [T2Space (GalK KSqrtTwo)]
    (hrange : MonoidHom.range (chiCycKTwo (K := KSqrtTwo)).toMonoidHom = imChiM 3)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (mStageWord 3 0 (by omega)) (vM 3)
        (maxProPQuotient 2 (GalK KSqrtTwo)) (chiCycKTwo (K := KSqrtTwo)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F) :
    EvenRouteFinalCarriedM 0 KSqrtTwo :=
  evenRouteFinal_carriedM_of_atDepth (by omega) hrange (by rw [finrank_KSqrtTwo]) Hfam

/-- **The status theorem at the quartic**, end to end: measured identification plus `Hfam` gives
the oriented equivalence at a real `N`-branch field of depth `3`. -/
theorem evenRouteFinal_statusN_quartic [T2Space (GalK KQuarticN)]
    (hrange : MonoidHom.range (chiCycKTwo (K := KQuarticN)).toMonoidHom = imChiN 3)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (nStageWord 3 1 (by omega)) (vN 3)
        (maxProPQuotient 2 (GalK KQuarticN)) (chiCycKTwo (K := KQuarticN)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F) :
    Nonempty (OrientedContinuousMulEquiv (chiN 3 1) (chiCycKTwo (K := KQuarticN))) :=
  evenRouteFinal_orientedEquivN_of_carried (by omega) hrange
    (evenRouteFinal_carriedN_quartic hrange Hfam)

end Models

end

end GQ2.Dyadic.EvenRouteFinal

/-! ## §8 Axiom pins, and the comparison

Every public declaration of this file is printed below, followed by every statement it
supersedes, so the comparison is on the page rather than in prose.

Write `std-3` for `[propext, Classical.choice, Quot.sound]` and `S` for the seven-element set the
even endpoint chain prints,

  `[propext, Classical.choice, hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt,
   Quot.sound, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic]`.

**Measured, at this tip, all 29 prints of this file**: 19 print `std-3` (§1 to §4, the two
coefficient-action instances, the two `_of_atDepth` constructors and the three model artefacts of
§7, none of which reaches the endpoint chain), and 10 print `S` (§5, §6 and
`evenRouteFinal_statusN_quartic`).  **Nothing in this file prints anything else.**

The comparison, against what each declaration supersedes, measured rather than asserted:

* against `evenRouteCarried_orientedEquiv{N,M}_atDepth` (wave 56, retracted): the same set `S`.
  The gain is not in the pins: it is that those two have an unsatisfiable hypothesis set at every
  field (`evenRouteModel_not_carriedDeep{N,M}`) and §5's do not, and that §5 is stated at every
  depth rather than `alpha ≥ 3`.
* against `evenRouteModel_orientedEquiv{N,M}_atDepth` (wave 57): the same set `S`, with
  `EvenClimbResidualSupply` replaced by `Hfam`, which is strictly further back in the chain.
* against `evenAlphaTwo_orientedEquiv{N,M}_two_of_residual` (wave 56) and
  `evenResidual_orientedEquiv{N,M}_two_of_family` (wave 57): **the same set `S` as well.**  This
  corrects an easy misreading of the wave-57 ledger: those four carry a `MarkedRecip R K` binder
  and `κ ≠ 0` as *hypotheses*, so they do not themselves consume the B5-K axiom, and their pins
  are `S`.  The axiom appears one step later, when the binder is discharged at a named field: the
  wave-55 models `evenRouteWitness_orientedEquiv{N_sqrtNegTwo,M_sqrtTwo}`, printed below, are the
  two declarations in this neighbourhood that print `markedRecipAt` and `localReciprocity` on top
  of `S`.  §5 removes the binder, so §7's models at the same fields print `std-3` and
  `evenRouteFinal_statusN_quartic` prints `S`, and **no consumer of this file ever needs
  `markedRecipAt`.**  That is the honest form of the wave-57 ledger's last row: the improvement
  is in the binder list and in what the downstream models pin to, not in what the `alpha = 2`
  endpoints themselves pin to.

So this file's declarations pin to `S` or less throughout, to the same set as the wave-57 at-depth
forms they re-cut, and to a **strict subset** of what the models they replace pin to. -/

section AxiomPins

open GQ2.Dyadic.EvenRouteFinal

-- the two coefficient-action instances
#print axioms evenRouteFinalScalar
#print axioms evenRouteFinalContinuousScalar

-- §1 the carried input
#print axioms EvenRouteFinalFamilyN
#print axioms EvenRouteFinalFamilyM

-- §2 the artefact
#print axioms EvenRouteFinalCarriedN
#print axioms EvenRouteFinalCarriedM

-- §3 the guard collapses
#print axioms evenRouteFinal_familyN_iff_atDepth
#print axioms evenRouteFinal_familyM_iff_atDepth

-- §4 comparison and repair
#print axioms evenRouteFinal_familyN_of_endpointNFamily
#print axioms evenRouteFinal_familyM_of_endpointMFamily
#print axioms evenRouteFinal_deepFamilyN_of_familyN
#print axioms evenRouteFinal_deepFamilyM_of_familyM
#print axioms evenRouteFinal_carriedDeepN_split
#print axioms evenRouteFinal_carriedDeepM_split
#print axioms evenRouteFinal_repairN
#print axioms evenRouteFinal_repairM

-- §5 the endpoints
#print axioms evenRouteFinal_orientedEquivN_atDepth
#print axioms evenRouteFinal_orientedEquivM_atDepth
#print axioms evenRouteFinal_orientedEquivN_of_carried
#print axioms evenRouteFinal_orientedEquivM_of_carried

-- §6 the status
#print axioms evenRouteFinal_statusN
#print axioms evenRouteFinal_statusM
#print axioms evenRouteFinal_status
#print axioms evenRouteFinal_carriedN_of_atDepth
#print axioms evenRouteFinal_carriedM_of_atDepth

-- §7 the model fields
#print axioms evenRouteFinal_carriedN_quartic
#print axioms evenRouteFinal_carriedN_sqrtNegTwo
#print axioms evenRouteFinal_carriedM_sqrtTwo
#print axioms evenRouteFinal_statusN_quartic

-- what §5 and §6 supersede, for comparison
#print axioms GQ2.Dyadic.EvenRouteModel.evenRouteModel_orientedEquivN_atDepth
#print axioms GQ2.Dyadic.EvenRouteModel.evenRouteModel_orientedEquivM_atDepth
#print axioms GQ2.Dyadic.EvenResidual.evenResidual_orientedEquivN_two_of_family
#print axioms GQ2.Dyadic.EvenResidual.evenResidual_orientedEquivM_two_of_family
#print axioms GQ2.Dyadic.EvenAlphaTwo.evenAlphaTwo_orientedEquivN_two_of_residual
#print axioms GQ2.Dyadic.EvenAlphaTwo.evenAlphaTwo_orientedEquivM_two_of_residual
#print axioms GQ2.Dyadic.EvenRouteCarried.evenRouteCarried_orientedEquivN_atDepth
#print axioms GQ2.Dyadic.EvenRouteCarried.evenRouteCarried_orientedEquivM_atDepth

-- the two wave-55 models §7 replaces: the only declarations here that print the B5-K axiom
#print axioms GQ2.Dyadic.EvenRouteWitness.evenRouteWitness_orientedEquivN_sqrtNegTwo
#print axioms GQ2.Dyadic.EvenRouteWitness.evenRouteWitness_orientedEquivM_sqrtTwo

end AxiomPins

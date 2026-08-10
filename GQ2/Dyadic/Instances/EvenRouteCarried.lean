/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenFlip
import GQ2.Dyadic.Instances.EvenDeepIsotropy
import GQ2.Dyadic.Instances.EvenRouteWitness

/-!
# W56-RECUT: the even route's carried inputs, re-cut to what waves 54 and 55 left true

## RETRACTED (wave 58).  DO NOT QUOTE `EvenRouteCarriedDeepN` OR `EvenRouteCarriedDeepM`

**The two structures this file publishes as the corrected paper-facing list are unusable, and the
before/after table below is stale in all four of its "after" cells.**  Their second field, the
coordinate-`0` flip demand `EvenRouteDeepFlip{N,M}`, was refuted at **every** branch depth by
`EvenSlotZero.lean` (W56-SLOTZERO), landing in a sibling module four commits later in the same
wave, so neither file could see the other.  Composed, in wave 57:

* `EvenRouteModel.evenRouteModel_not_carriedDeep{N,M}` and
  `EvenRouteAudit.evenRouteAudit_not_carriedDeep{N,M}`: both bundles are **FALSE** at every field
  of branch depth `alpha >= 3`, which is the only range in which they are stated;
* `EvenRouteModel.evenRouteModel_deep{N,M}_iff_depth_two`: they hold **exactly** on the depth-`2`
  stratum, which is where §4.3 below proves them vacuous.

So the bundles are true only where they are empty, and false everywhere else, and §5's four
endpoints over them have unsatisfiable hypothesis sets.

**The replacement is `GQ2/Dyadic/Instances/EvenRouteFinal.lean`**, whose
`EvenRouteFinalCarried{N,M}` carry `Hfam` and nothing else, at **every** depth `alpha >= 2` and on
both branches, with the two arithmetic binders stated explicitly.  Wave 57's
`EvenResidual.evenResidual_residualSupply_iff_rawDefect_{N,M}` is what removed the rest.
`EvenRouteFinal.evenRouteFinal_carriedDeep{N,M}_split` records the repair in Lean: this file's
bundle is exactly the replacement's family field, cut at `alpha >= 3`, conjoined with the refuted
flip, so the repair is a deletion and nothing of substance was lost.

Everything below is left as committed; only this notice and the corrections marked
**(stale, wave 58)** are new.  No statement or proof in this file has been changed.

## What this file is

`StageAbstractionEvenEndpoint.lean` §8 published four structures `EvenRouteCarried{N,M,NTwo,MTwo}`
as the machine-checked list of what the even route carries, and the campaign's prose instructs
the paper to quote them.  Two later results falsified that list.

* **W54-BOCK** (`EvenDeepIsotropy.lean`) proved `EvenDeepMIsotropicSupply K` outright, so the
  third field of `EvenRouteCarriedM` is a theorem.  The two wave-54 lanes are siblings in the
  import graph and never met, so the structure was published carrying it anyway.
* **W55-SLOT3** (`StageAbstractionEvenFlip.lean`) proved every flip coordinate except `0` on both
  branches, so the carried flip demand is one coordinate and not a family; and then refuted the
  flip supply outright at `alpha = 2` (`evenFlip_not_flipSupply_two`).

The refutation does not merely over-quantify the published bundles.  §6 below proves that at
**every** field whose branch depth is `2`, all four published bundles are **false**, so the four
endpoints `evenRoute_orientedEquiv{N,M}`, `evenRoute_orientedEquiv{N,M}_two` are vacuous there.
The wave-55 audit ranked the unguarded depth binder as a latent design weakness and proved the
`N` binder harmless; that reading was correct about the binder and is superseded by the
refutation, because at a depth-`2` field the single instance the `N` binder collapses to is the
refuted one.  This is reported at the top rather than buried: it is the sharpest consequence of
wave 55 for the paper-facing artefacts.

This file publishes the corrected list.  It changes no committed statement; it supersedes.

## Before and after: what each branch carries

| branch | stratum | wave 54 published | after waves 54, 55 and this lane | **(stale, wave 58)** the truth |
| --- | --- | --- | --- | --- |
| `N` | `alpha = 2` | `Hfam`, all `4 + 2h` flip slots | **nothing: the input set is FALSE** (§6) | `Hfam` alone; the endpoint holds here |
| `N` | `alpha >= 3` | `Hfam`, all `4 + 2h` flip slots, unguarded in `alpha` | **`Hfam` and the slot-`0` flip, guarded by `hrange`** | `Hfam` alone; the slot-`0` flip is FALSE |
| `M` | `alpha = 2` | `Hfam`, flips off slot `2` | **nothing: the input set is FALSE** (§6) | `Hfam` alone; the endpoint holds here |
| `M` | `alpha >= 3` | `Hfam`, flips off slot `2`, **and the isotropy**, unguarded in `alpha` | **`Hfam` and the slot-`0` flip, guarded by `hrange`** | `Hfam` alone; the slot-`0` flip is FALSE |

("`alpha = 2`" names the stratum of fields whose branch depth is `2`.  §6 proves the falsity
there and claims nothing elsewhere: at a field of depth `>= 3` the same `alpha = 2` instance is
vacuous rather than refuted, and §6.1 proves that too.)

**(stale, wave 58)** All four cells of the fourth column are superseded, two of them outright
false.  The `alpha >= 3` cells name an input that W56-SLOTZERO refuted at every depth, so the row
they describe has no model.  The `alpha = 2` cells are right that the *wave-54* input set is false
there, and wrong as a description of what the route carries: wave 57's
`EvenResidual.evenResidual_orientedEquiv{N,M}_two_of_family` runs the even route on that stratum
carrying `Hfam` alone, so the stratum is live and is no longer split off.  The fifth column is the
wave-58 statement, and it is uniform in `alpha`; see `EvenRouteFinal.lean`.

Three changes, in decreasing order of what they cost to justify.

1. **The `alpha = 2` stratum is gone**, and its endpoints are vacuous.  The bundles below are
   stated at `alpha >= 3`.  §6 states the retraction as Lean, not as prose.
2. **The flip demand is one coordinate.**  `EvenDigitFlipSupplySlotZero` replaces the full
   supply and the wave-54 slot-`2`-free supply; wave 55's §4 proves every other slot on both
   branches.  **(stale, wave 58)** That one coordinate is itself refuted at every depth
   (`EvenSlotZero.evenSlotZero_not_slotZeroSupply_{N,M}`), so the flip demand is not shorter, it
   is gone: the even route carries no flip input at all.
3. **The `M` isotropy field is gone**, discharged at the point of use by
   `evenDeepMIsotropicSupply_holds`.  With it goes the `[FiniteDimensional ℚ_[2] K]` binder that
   `EvenRouteCarriedM` carried only because `EvenDeepMIsotropicSupply` mentions it, so the two
   bundles below are now symmetric in their binders as well as in their fields.  That closes the
   audit's item 6 in the direction that removes a binder rather than adding one.

## The guard, and why both branches need it

The audit's item 4: `EvenEndpointMFamily`, `EvenEndpointMFlipOffTwo` and `EvenRouteCarriedM`
quantify over every `alpha >= 2` unguarded by the range identity, while the identity produces one
`alpha` per field.  `EvenDeepMIsotropicSupply` shows the correct pattern, quantifying over the
identification as well, so that only a produced depth is ever reached.  The four `Prop`s of §3
are cut that way.

The audit could dismiss the `N` binder as harmless (off the produced depth the `N` stage tuples
are empty, `evenRouteWitness_nTuple_isEmpty`) and could not do the same on `M`
(`evenRouteWitness_vM_mem_range`: every deeper `M` row value is still a character value).  §1
removes the asymmetry at its root, by a different argument: **the range images themselves
determine their depth**, on both branches.  `mUnit alpha` lies in no `imChiM beta` with
`beta > alpha` (`evenRouteCarried_mUnit_not_mem_imChiM`), and it lies in every shallower one, so
`imChiM` is injective above `2`; `imChiN` is injective by the audit's own two-power spacing
argument.  Hence a field has at most one branch depth on each branch, and §4 proves that the
guarded bundle is **equivalent** to the single-depth data the at-depth endpoint consumes, on
**both** branches (`evenRouteCarried_deep{N,M}_iff_atDepth`).  That is strictly more than the
audit asked for: it does not merely guard the `M` binder, it shows the guarded binder collapses.

A second dividend: §1 also gives the `M` analogue of the audit's tuple-emptiness lemma in the
range where it is true (`evenRouteCarried_mTuple_isEmpty`, at depths *below* the produced one),
which is what makes the `alpha = 2` instance of a deep `M` field vacuous rather than refuted.

## The `alpha = 2` situation, stated and not hidden

§6 is the honest record the campaign owes the paper.  At a field whose branch depth is `2`:

* an `alpha = 2` stage tuple exists on the branch (the level-three base of wave 54 builds one);
* therefore `EvenDigitFlipSupply 2` is false there, by W55-SLOT3 §6;
* therefore all four published bundles are false, and their four endpoints are vacuous
  (`evenRouteCarried_not_carried{N,M,NTwo,MTwo}`);
* while the two bundles of §4 hold vacuously (`evenRouteCarried_deep{N,M}_of_two`), which is the
  point of guarding: the corrected artefact is true where the published one is false, and says
  nothing there rather than something unsatisfiable.

**(stale, wave 58)** The last clause is the sentence the re-audit singled out, and it reads as a
recommendation it cannot support.  Being "true where the published one is false" buys nothing
here, because that is the *only* place the corrected artefact is true: at every depth `alpha >= 3`
it is false as well (`EvenRouteModel.evenRouteModel_deep{N,M}_iff_depth_two`).  A bundle that is
vacuous on one stratum and refuted on the rest is not a carrier.  The wave-58 replacement is true
on both strata and carries `Hfam` alone; see `EvenRouteFinal.lean`.

The `M` half of the open question has a concrete arithmetic form:
`evenRouteCarried_depthM_two_iff_top` says the refuted `M` stratum is exactly the fields whose
cyclotomic character is **surjective** onto `ℤ₂ˣ`, since `imChiM 2 = ⊤`.

## Numbering

1. depth rigidity: the two range images determine their depth, and the `M` tuple emptiness below;
2. the `alpha = 2` question in arithmetic form;
3. the carried inputs, guarded by the identification and cut at `alpha >= 3`;
4. the two corrected bundles, and their equivalence with the single-depth data;
5. the endpoints over the corrected bundles;
6. the `alpha = 2` retraction, as Lean;
7. axiom pins, with the comparison against every statement superseded.
-/

namespace GQ2.Dyadic.EvenRouteCarried

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
open GQ2.Dyadic.EvenEndpoint
open GQ2.Dyadic.EvenDeepIsotropy
open GQ2.Dyadic.EvenRouteWitness

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The coefficient action at `G_K(2)`, as everywhere on this route. -/
local instance evenRouteCarriedScalar {K : IntermediateField ℚ_[2] ℚ̄₂} [CompactSpace (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] :
    DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

/-- Continuity of that action. -/
local instance evenRouteCarriedContinuousScalar {K : IntermediateField ℚ_[2] ℚ̄₂}
    [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-! ## §1 Depth rigidity

The guard of §3 is only as good as the fact that a field has one branch depth.  On the `N` branch
the audit proved it through the orientation unit (`evenRouteWitness_nUnit_mem_imChiN`); the `M`
branch had no such statement, and the audit's `evenRouteWitness_mUnit_mem_imChiM` is the half that
goes the wrong way (`mUnit alpha` *is* in every shallower image).  The missing half is here: no
`mUnit alpha` reaches a strictly deeper image, for the two-adic reason that
`mUnit alpha - 1 = 2 ^ alpha * mUnit alpha` is exactly `alpha`-sharp and `mUnit alpha + 1` is
`2`-sharp. -/

section Rigidity

/-- **`mUnit alpha` is not a value of a strictly deeper `M` image.**  Both branches of
`evenRange_mem_imChiM_iff` fail: `2 ^ beta ∣ mUnit alpha - 1 = 2 ^ alpha * mUnit alpha` would
make `2` divide a unit, and `2 ^ beta ∣ mUnit alpha + 1` would make `4` divide `2`. -/
theorem evenRouteCarried_mUnit_not_mem_imChiM {alpha beta : ℕ} (halpha : 2 ≤ alpha)
    (hlt : alpha < beta) : mUnit alpha ∉ imChiM beta := by
  intro hmem
  have hkey := mUnit_sub_one (show 1 ≤ alpha by omega)
  rcases (evenRange_mem_imChiM_iff (show 2 ≤ beta by omega)).mp hmem with hd | hd
  · rw [hkey] at hd
    have hsplit : (2 : ℤ_[2]) ^ beta = 2 ^ alpha * 2 ^ (beta - alpha) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit] at hd
    have hcancel : (2 : ℤ_[2]) ^ (beta - alpha) ∣ ((mUnit alpha : ℤ_[2]ˣ) : ℤ_[2]) :=
      (mul_dvd_mul_iff_left (a := (2 : ℤ_[2]) ^ alpha) (pow_ne_zero _ two_ne_zero)).mp hd
    have h2 : (2 : ℤ_[2]) ∣ ((mUnit alpha : ℤ_[2]ˣ) : ℤ_[2]) :=
      (dvd_pow_self 2 (show beta - alpha ≠ 0 by omega)).trans hcancel
    exact evenRouteWitness_not_two_dvd_one (isUnit_of_dvd_unit h2 (Units.isUnit _)).dvd
  · have h4 : (2 : ℤ_[2]) ^ 2 ∣ ((mUnit alpha : ℤ_[2]ˣ) : ℤ_[2]) + 1 :=
      (pow_dvd_pow _ (show 2 ≤ beta by omega)).trans hd
    have h4' : (2 : ℤ_[2]) ^ 2 ∣ 2 ^ alpha * ((mUnit alpha : ℤ_[2]ˣ) : ℤ_[2]) :=
      Dvd.dvd.mul_right (pow_dvd_pow _ halpha) _
    obtain ⟨c, hc⟩ := h4
    obtain ⟨d, hdd⟩ := h4'
    exact evenRouteWitness_not_two_dvd_one
      ⟨c - d, mul_left_cancel₀ (two_ne_zero (α := ℤ_[2])) (by linear_combination hc - hdd - hkey)⟩

/-- **The `M` range images determine their depth.**  Injectivity of `imChiM` above `2`, from the
two halves: `mUnit alpha` is in every shallower image (`evenRouteWitness_mUnit_mem_imChiM`) and in
no deeper one. -/
theorem evenRouteCarried_imChiM_inj {alpha beta : ℕ} (halpha : 2 ≤ alpha) (hbeta : 2 ≤ beta)
    (heq : imChiM alpha = imChiM beta) : alpha = beta := by
  by_contra hne
  rcases Nat.lt_or_ge alpha beta with hlt | hge
  · exact evenRouteCarried_mUnit_not_mem_imChiM halpha hlt
      (by rw [← heq]; exact mUnit_mem_imChiM alpha)
  · exact evenRouteCarried_mUnit_not_mem_imChiM (alpha := beta) (beta := alpha) hbeta (by omega)
      (by rw [heq]; exact mUnit_mem_imChiM beta)

/-- **The `N` range images determine their depth**, by the audit's two-power spacing argument. -/
theorem evenRouteCarried_imChiN_inj {alpha beta : ℕ} (halpha : 2 ≤ alpha) (hbeta : 2 ≤ beta)
    (heq : imChiN alpha = imChiN beta) : alpha = beta :=
  evenRouteWitness_nUnit_mem_imChiN halpha hbeta
    (by rw [← heq]; exact evenRow_nUnit_mem_imChiN alpha)

section Field

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

omit [T2Space (GalK K)] in
/-- **A field has at most one `N` branch depth.** -/
theorem evenRouteCarried_depthN_unique {alpha beta : ℕ} (halpha : 2 ≤ alpha) (hbeta : 2 ≤ beta)
    (ha : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (hb : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN beta) : alpha = beta :=
  evenRouteCarried_imChiN_inj halpha hbeta (ha.symm.trans hb)

omit [T2Space (GalK K)] in
/-- **A field has at most one `M` branch depth.**  This is the statement the audit's Finding 3
could not supply, and it is what lets §4 collapse the guarded `M` bundle exactly as the `N` one. -/
theorem evenRouteCarried_depthM_unique {alpha beta : ℕ} (halpha : 2 ≤ alpha) (hbeta : 2 ≤ beta)
    (ha : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (hb : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM beta) : alpha = beta :=
  evenRouteCarried_imChiM_inj halpha hbeta (ha.symm.trans hb)

omit [T2Space (GalK K)] in
/-- **Below the produced depth the `M` stage tuples do not exist.**  Row `3` of the `M` table is
`mUnit alpha`, a tuple demands a character value there, and §1 puts no shallow `mUnit` in a deep
image.  This is the `M` analogue of `evenRouteWitness_nTuple_isEmpty`, in the range where it is
true: it holds for `alpha < beta` and, by `evenRouteWitness_vM_mem_range`, has no analogue for
`alpha > beta`. -/
theorem evenRouteCarried_mTuple_isEmpty {alpha beta h k : ℕ} (halpha : 2 ≤ alpha)
    (hlt : alpha < beta) {hα₁ : 1 ≤ alpha}
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM beta) :
    IsEmpty (Tuple (mStageWord alpha h hα₁) (vM alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k) := by
  refine ⟨fun T ↦ ?_⟩
  obtain ⟨x, hx, -⟩ := T.rows 3
  rw [vM_three] at hx
  exact evenRouteCarried_mUnit_not_mem_imChiM halpha hlt (hrange ▸ ⟨x, hx⟩)

end Field

end Rigidity

/-! ## §2 The `alpha = 2` question in arithmetic form

The campaign's top open item is whether the range identity ever produces `alpha = 2`.  On the `M`
branch that question has a one-line arithmetic form, because `imChiM 2 = ⊤`
(`evenRouteWitness_imChiM_two_eq_top`). -/

section AlphaTwoShape

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

omit [T2Space (GalK K)] in
/-- **The refuted `M` stratum is exactly the surjective-character locus.**  A field sits on the
`M` branch's `alpha = 2` stratum iff its cyclotomic character reaches every unit of `ℤ₂`.  So the
`M` half of the campaign's `alpha = 2` question is: can `chiCycKTwo` be onto? -/
theorem evenRouteCarried_depthM_two_iff_top :
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM 2 ↔
      MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = ⊤ := by
  rw [evenRouteWitness_imChiM_two_eq_top]

end AlphaTwoShape

/-! ## §3 The carried inputs, guarded and deep

Four `Prop`s, one per branch per input, each cut the way `EvenDeepMIsotropicSupply` is cut: the
branch identification is a binder, so no instance outside the depth the identity produces for
*this* field is ever demanded.  The depth binder starts at `3`, since `alpha = 2` is refuted
(§6).

Against the wave-54 forms (`EvenEndpointNFamily`, `EvenEndpointMFamily`, `EvenEndpointNFlip`,
`EvenEndpointMFlipOffTwo`): the depth binder is tightened from `2 ≤ alpha` to `3 ≤ alpha`, the
identification is added as a guard, and on the flip side the whole supply is replaced by its
coordinate-`0` restriction.  Each of the four asks strictly less; §4's `_of_carried{N,M}`
certifies that in the only direction that could hide a strengthening. -/

section Inputs

/-- **`Hfam` at one field, `N` branch**, at the produced branch depths `alpha >= 3` only. -/
def EvenRouteDeepFamilyN (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop :=
  ∀ (alpha : ℕ) (halpha : 3 ≤ alpha),
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha →
    ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (nStageWord alpha h (by omega)) (vN alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F

/-- **`Hfam` at one field, `M` branch**, at the produced branch depths `alpha >= 3` only. -/
def EvenRouteDeepFamilyM (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop :=
  ∀ (alpha : ℕ) (halpha : 3 ≤ alpha),
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha →
    ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (mStageWord alpha h (by omega)) (vM alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F

/-- **REFUTED (wave 57), at every branch depth.**  `EvenRouteModel.evenRouteModel_not_deepFlipN`:
false at every field of depth `alpha >= 3` whose degree is even, the tuple the refutation needs
being built by wave 54's own level-three base.  This is the field that killed
`EvenRouteCarriedDeepN`, and it is off the even route entirely.

Original text.  **The flip demand at one field, `N` branch**: one digit at the single coordinate
`0` per stage, at the produced branch depths `alpha >= 3` only.  Every other coordinate is a
theorem (`evenFlip_flipOffZero_N`). -/
def EvenRouteDeepFlipN (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop :=
  ∀ (alpha : ℕ) (halpha : 3 ≤ alpha),
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha →
    EvenDigitFlipSupplySlotZero alpha (nStageWord alpha h (by omega)) (vN alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))

/-- **REFUTED (wave 57), at every branch depth**, by
`EvenRouteModel.evenRouteModel_not_deepFlipM`.  See the `N` twin.

Original text.  **The flip demand at one field, `M` branch**: one digit at the single coordinate
`0` per stage, at the produced branch depths `alpha >= 3` only.  Every other coordinate is a
theorem (`evenFlip_flipOffZero_M`), slot `2` already since wave 53. -/
def EvenRouteDeepFlipM (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop :=
  ∀ (alpha : ℕ) (halpha : 3 ≤ alpha),
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha →
    EvenDigitFlipSupplySlotZero alpha (mStageWord alpha h (by omega)) (vM alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))

end Inputs

/-! ## §4 The two corrected bundles

**(stale, wave 58)** These are not the artefact; see the retraction at the head of the file and
`EvenRouteFinal.EvenRouteFinalCarried{N,M}`.  §4.2's collapse is the part that survives, and the
replacement reproves it at every depth (`evenRouteFinal_family{N,M}_iff_atDepth`).

Original text.  The artefact.  One `Prop` per branch, whose fields are exactly the inputs the even
route carries after waves 54 and 55, and nothing else.  Two fields on **both** branches, with
identical binders:
the `M`-side isotropy is discharged at the point of use by `evenDeepMIsotropicSupply_holds`, and
with it goes the `[FiniteDimensional ℚ_[2] K]` binder that only `EvenDeepMIsotropicSupply` needed.

§4.1 is the comparison the campaign's re-cut rule demands at the level of statements: the wave-54
bundles and the wave-55 inputs both imply these, so no consumer holding the old data loses
anything, and nothing below is a strengthening.

§4.2 is what the guard buys.  On both branches the bundle is **equivalent** to the single-depth
pair of inputs the at-depth endpoint consumes.  The `N` half was already known by tuple emptiness
(`evenRouteWitness_carriedN_of_atDepth`); the `M` half is new, and it needed §1, because the
audit's Finding 3 shows that the tuple-emptiness route is unavailable on `M`. -/

section Bundles

/-- **RETRACTED (wave 58).  Do not quote.**  This `Prop` is FALSE at every field of branch depth
`alpha >= 3` (`EvenRouteModel.evenRouteModel_not_carriedDeepN`), because its `flip` field is
refuted at every depth by `EvenSlotZero.evenSlotZero_not_slotZeroSupply_N`, and it holds exactly
on the depth-`2` stratum where §4.3 proves it vacuous
(`EvenRouteModel.evenRouteModel_deepN_iff_depth_two`).  It is therefore never a non-vacuous
carrier.  **Use `EvenRouteFinal.EvenRouteFinalCarriedN`**, which keeps the `family` field, drops
the `flip` field, and holds at every depth `alpha >= 2`;
`EvenRouteFinal.evenRouteFinal_carriedDeepN_split` and `evenRouteFinal_repairN` record the repair.

Original text.  **What the even route carries on the `N` branch, above the refuted stratum.**  Two
inputs: the coordinate derivation family with its relator kill, and one digit at coordinate `0`
per stage, both asked only at branch depths `alpha >= 3` that this field's range identity actually
produces. -/
structure EvenRouteCarriedDeepN (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop where
  /-- `Hfam`: the coordinate derivation family with its relator kill. -/
  family : EvenRouteDeepFamilyN h K
  /-- The one-digit flip demand, at the one coordinate `0`. -/
  flip : EvenRouteDeepFlipN h K

/-- **RETRACTED (wave 58).  Do not quote.**  The `M` twin of the notice on
`EvenRouteCarriedDeepN`: FALSE at every field of branch depth `alpha >= 3`
(`EvenRouteModel.evenRouteModel_not_carriedDeepM`), true exactly where vacuous
(`evenRouteModel_deepM_iff_depth_two`).  **Use `EvenRouteFinal.EvenRouteFinalCarriedM`.**

Original text.  **What the even route carries on the `M` branch, above the refuted stratum.**  The
same two inputs, with the same binders: the isotropy that `EvenRouteCarriedM` carried as a third
field is `evenDeepMIsotropicSupply_holds`, a theorem of wave 54, and is discharged in §5. -/
structure EvenRouteCarriedDeepM (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop where
  /-- `Hfam`, `M` branch. -/
  family : EvenRouteDeepFamilyM h K
  /-- The one-digit flip demand, at the one coordinate `0`. -/
  flip : EvenRouteDeepFlipM h K

/-! ### §4.1 Nothing below is a strengthening -/

section Certificates

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-- **The wave-54 `N` bundle implies the corrected one.**  Guarding and deepening the binder ask
less, and the coordinate-`0` restriction of the flip supply asks less. -/
theorem evenRouteCarried_deepN_of_carriedN {h : ℕ} (C : EvenEndpoint.EvenRouteCarriedN h K) :
    EvenRouteCarriedDeepN h K :=
  ⟨fun alpha halpha _ ↦ C.family alpha (by omega),
    fun alpha halpha _ ↦ evenFlip_slotZero_of_flip (C.flip alpha (by omega))⟩

/-- **The wave-54 `M` bundle implies the corrected one**, its third field simply dropped.  The
slot-`2`-free supply gives the full one on the `M` row (`evenEndpoint_mFlip_of_offTwo`) and the
full one gives the coordinate-`0` restriction. -/
theorem evenRouteCarried_deepM_of_carriedM {h : ℕ} [FiniteDimensional ℚ_[2] K]
    (C : EvenEndpoint.EvenRouteCarriedM h K) : EvenRouteCarriedDeepM h K :=
  ⟨fun alpha halpha _ ↦ C.family alpha (by omega),
    fun alpha halpha _ ↦ evenFlip_slotZero_of_flip
      (evenEndpoint_mFlip_of_offTwo (by omega) (C.flip alpha (by omega)))⟩

/-- **The wave-55 `N` inputs imply the corrected bundle**: the wave-54 family `Prop` together
with the deep slot-`0` flip supply of `StageAbstractionEvenFlip.lean` §7.2. -/
theorem evenRouteCarried_deepN_of_slotZeroDeep {h : ℕ} (Hfam : EvenEndpointNFamily h K)
    (Hflip : EvenFlipNSlotZeroDeep h K) : EvenRouteCarriedDeepN h K :=
  ⟨fun alpha halpha _ ↦ Hfam alpha (by omega), fun alpha halpha _ ↦ Hflip alpha halpha⟩

/-- **The wave-55 `M` inputs imply the corrected bundle.** -/
theorem evenRouteCarried_deepM_of_slotZeroDeep {h : ℕ} (Hfam : EvenEndpointMFamily h K)
    (Hflip : EvenFlipMSlotZeroDeep h K) : EvenRouteCarriedDeepM h K :=
  ⟨fun alpha halpha _ ↦ Hfam alpha (by omega), fun alpha halpha _ ↦ Hflip alpha halpha⟩

/-! ### §4.2 The guarded bundle is exactly the single-depth data -/

/-- **The corrected `N` bundle from the single-depth pair.**  Given the branch identification at
`alpha₀ >= 3`, the two inputs at that one depth already give the bundle: by §1 no other depth
satisfies the guard. -/
theorem evenRouteCarried_deepN_of_atDepth {alpha₀ h : ℕ} (halpha₀ : 3 ≤ alpha₀)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha₀)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (nStageWord alpha₀ h (by omega)) (vN alpha₀)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F)
    (Hflip : EvenDigitFlipSupplySlotZero alpha₀ (nStageWord alpha₀ h (by omega)) (vN alpha₀)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    EvenRouteCarriedDeepN h K := by
  refine ⟨fun alpha halpha hr ↦ ?_, fun alpha halpha hr ↦ ?_⟩ <;>
    · obtain rfl : alpha₀ = alpha :=
        evenRouteCarried_depthN_unique (by omega) (by omega) hrange hr
      assumption

/-- **The corrected `M` bundle from the single-depth pair.**  The `M` statement the audit could
not make: its tuple-emptiness route is unavailable on this branch, and §1's depth rigidity
replaces it. -/
theorem evenRouteCarried_deepM_of_atDepth {alpha₀ h : ℕ} (halpha₀ : 3 ≤ alpha₀)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha₀)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (mStageWord alpha₀ h (by omega)) (vM alpha₀)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F)
    (Hflip : EvenDigitFlipSupplySlotZero alpha₀ (mStageWord alpha₀ h (by omega)) (vM alpha₀)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    EvenRouteCarriedDeepM h K := by
  refine ⟨fun alpha halpha hr ↦ ?_, fun alpha halpha hr ↦ ?_⟩ <;>
    · obtain rfl : alpha₀ = alpha :=
        evenRouteCarried_depthM_unique (by omega) (by omega) hrange hr
      assumption

/-- **The corrected `N` bundle *is* the single-depth data**, at a field with a branch depth
`alpha₀ >= 3`.  So the guarded binder is not a strengthening of what the at-depth endpoint
consumes, and the audit's item 4 is closed on this branch. -/
theorem evenRouteCarried_deepN_iff_atDepth {alpha₀ h : ℕ} (halpha₀ : 3 ≤ alpha₀)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha₀) :
    EvenRouteCarriedDeepN h K ↔
      ((∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (nStageWord alpha₀ h (by omega)) (vN alpha₀)
          (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
        ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F) ∧
      EvenDigitFlipSupplySlotZero alpha₀ (nStageWord alpha₀ h (by omega)) (vN alpha₀)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :=
  ⟨fun C ↦ ⟨C.family alpha₀ halpha₀ hrange, C.flip alpha₀ halpha₀ hrange⟩,
    fun ⟨Hfam, Hflip⟩ ↦ evenRouteCarried_deepN_of_atDepth halpha₀ hrange Hfam Hflip⟩

/-- **The corrected `M` bundle *is* the single-depth data.**  This is the statement the audit
ranked as the `M` branch's open risk; §1 supplies it, so item 4 is closed on both branches. -/
theorem evenRouteCarried_deepM_iff_atDepth {alpha₀ h : ℕ} (halpha₀ : 3 ≤ alpha₀)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha₀) :
    EvenRouteCarriedDeepM h K ↔
      ((∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (mStageWord alpha₀ h (by omega)) (vM alpha₀)
          (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
        ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F) ∧
      EvenDigitFlipSupplySlotZero alpha₀ (mStageWord alpha₀ h (by omega)) (vM alpha₀)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :=
  ⟨fun C ↦ ⟨C.family alpha₀ halpha₀ hrange, C.flip alpha₀ halpha₀ hrange⟩,
    fun ⟨Hfam, Hflip⟩ ↦ evenRouteCarried_deepM_of_atDepth halpha₀ hrange Hfam Hflip⟩

/-! ### §4.3 On the refuted stratum the corrected bundles hold, vacuously

The contrast that makes the guard worth its ink.  §6 shows the four published bundles are false
at a depth-`2` field; here the two corrected ones are true there, and true for the honest reason:
the guard has no instance to reach. -/

/-- **At a depth-`2` `N` field the corrected bundle holds vacuously.** -/
theorem evenRouteCarried_deepN_of_two {h : ℕ}
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN 2) :
    EvenRouteCarriedDeepN h K := by
  refine ⟨fun alpha halpha hr ↦ ?_, fun alpha halpha hr ↦ ?_⟩ <;>
    exact absurd (evenRouteCarried_depthN_unique (le_refl 2) (by omega) hrange hr) (by omega)

/-- **At a depth-`2` `M` field the corrected bundle holds vacuously.** -/
theorem evenRouteCarried_deepM_of_two {h : ℕ}
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM 2) :
    EvenRouteCarriedDeepM h K := by
  refine ⟨fun alpha halpha hr ↦ ?_, fun alpha halpha hr ↦ ?_⟩ <;>
    exact absurd (evenRouteCarried_depthM_unique (le_refl 2) (by omega) hrange hr) (by omega)

end Certificates

end Bundles

/-! ## §5 The endpoints over the corrected bundles

**(vacuous, wave 58)** Every endpoint in this section has an unsatisfiable hypothesis set: its
bundle argument is refuted at the depths it is stated at (`EvenRouteAudit.evenRouteAudit
_orientedEquiv{N,M}_vacuous`, `EvenRouteModel.evenRouteModel_not_carriedDeep{N,M}`), and the
`_dichotomy` forms retain content only at branch depth `2`, where their conclusion is empty
(`evenRouteAudit_dichotomy{N,M}_forces_two`).  The live at-depth endpoints are
`EvenRouteFinal.evenRouteFinal_orientedEquiv{N,M}_atDepth`, over `Hfam` alone and at every depth,
and the per-field statement is `EvenRouteFinal.evenRouteFinal_status{N,M}`.

Original text.  The wave-55 at-depth endpoints, with the flip input taken from the bundle and, on
`M`, the isotropy discharged by `evenDeepMIsotropicSupply_holds` rather than carried.  Everything
is stated at `alpha >= 3`.

The per-field forms come in two shapes, and the pair is the honest statement of the campaign's
position.  `evenRouteCarried_orientedEquiv{N,M}` add one named hypothesis, that the field is not
on the refuted stratum, and conclude at a depth `>= 3`; the `_dichotomy` forms add nothing, name
the produced depth, and conclude only above the refuted stratum.  Neither hides `alpha = 2`. -/

section Endpoints

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The even `N` endpoint at one field and one branch depth `alpha >= 3`, from the corrected
bundle and nothing else.** -/
theorem evenRouteCarried_orientedEquivN_atDepth {alpha h : ℕ} (halpha : 3 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) (C : EvenRouteCarriedDeepN h K) :
    Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) :=
  evenFlip_orientedEquivN_atDepth (by omega) hrange hev (C.family alpha halpha hrange)
    (C.flip alpha halpha hrange)

/-- **The even `M` endpoint at one field and one branch depth `alpha >= 3`, from the corrected
bundle and nothing else.**  The isotropy is `evenDeepMIsotropicSupply_holds`, so the `M` branch
carries exactly what the `N` branch carries: this is the two-input `M` endpoint the campaign has
claimed since wave 54 and had not committed. -/
theorem evenRouteCarried_orientedEquivM_atDepth {alpha h : ℕ} (halpha : 3 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) (C : EvenRouteCarriedDeepM h K) :
    Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) :=
  evenFlip_orientedEquivM_atDepth (by omega) hrange hev
    (evenDeepMIsotropicSupply_holds (K := K) alpha (by omega) hrange)
    (C.family alpha halpha hrange) (C.flip alpha halpha hrange)

/-- **The even `N` route, per field, off the refuted stratum.**  Every even-degree dyadic field of
degree `2 + 2h` whose `K(i)` is ramified, whose cyclotomic range omits `-1`, and whose range is
not the depth-`2` image, has a branch depth `alpha >= 3` at which its maximal pro-`2` Galois group
is oriented-isomorphic to the presented `N` core; and the whole route costs the two fields of
`EvenRouteCarriedDeepN`. -/
theorem evenRouteCarried_orientedEquivN {R : LocalReciprocity} (B : MarkedRecip R K)
    (deltaI : ℚ̄₂) (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI)
    (hneg : (-1 : ℤ_[2]ˣ) ∉ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (hnotTwo : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom ≠ imChiN 2)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) (C : EvenRouteCarriedDeepN h K) :
    ∃ alpha : ℕ, 3 ≤ alpha ∧
      Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) := by
  obtain ⟨alpha, halpha, hrange⟩ := evenRange_range_eq_imChiN B deltaI hdeltaI hram hneg
  have h3 : 3 ≤ alpha := by
    by_contra hlt
    exact hnotTwo (by rw [hrange, show alpha = 2 by omega])
  exact ⟨alpha, h3, evenRouteCarried_orientedEquivN_atDepth h3 hrange hev C⟩

/-- **The even `M` route, per field, off the refuted stratum.**  By §2 the extra hypothesis says
exactly that the cyclotomic character is not surjective. -/
theorem evenRouteCarried_orientedEquivM {R : LocalReciprocity} (B : MarkedRecip R K)
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (hnotTwo : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom ≠ imChiM 2)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) (C : EvenRouteCarriedDeepM h K) :
    ∃ alpha : ℕ, 3 ≤ alpha ∧
      Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) := by
  obtain ⟨alpha, halpha, hrange⟩ := evenRange_range_eq_imChiM B hneg
  have h3 : 3 ≤ alpha := by
    by_contra hlt
    exact hnotTwo (by rw [hrange, show alpha = 2 by omega])
  exact ⟨alpha, h3, evenRouteCarried_orientedEquivM_atDepth h3 hrange hev C⟩

/-- **The even `N` route, per field, with nothing assumed about the stratum.**  The range identity
produces a depth; above the refuted stratum the endpoint holds, and at the refuted stratum the
statement says nothing, which is exactly the campaign's position after wave 55. -/
theorem evenRouteCarried_orientedEquivN_dichotomy {R : LocalReciprocity} (B : MarkedRecip R K)
    (deltaI : ℚ̄₂) (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI)
    (hneg : (-1 : ℤ_[2]ˣ) ∉ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) (C : EvenRouteCarriedDeepN h K) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha ∧
      (3 ≤ alpha →
        Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K)))) := by
  obtain ⟨alpha, halpha, hrange⟩ := evenRange_range_eq_imChiN B deltaI hdeltaI hram hneg
  exact ⟨alpha, halpha, hrange,
    fun h3 ↦ evenRouteCarried_orientedEquivN_atDepth h3 hrange hev C⟩

/-- **The even `M` route, per field, with nothing assumed about the stratum.** -/
theorem evenRouteCarried_orientedEquivM_dichotomy {R : LocalReciprocity} (B : MarkedRecip R K)
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) (C : EvenRouteCarriedDeepM h K) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha ∧
      (3 ≤ alpha →
        Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))) := by
  obtain ⟨alpha, halpha, hrange⟩ := evenRange_range_eq_imChiM B hneg
  exact ⟨alpha, halpha, hrange,
    fun h3 ↦ evenRouteCarried_orientedEquivM_atDepth h3 hrange hev C⟩

end Endpoints

/-! ## §6 The `alpha = 2` retraction, as Lean

W55-SLOT3 §6 proved `EvenDigitFlipSupply 2 W v G chi` false on every row table as soon as one
stage tuple exists, and §7.3 turned that into the falsity of `EvenEndpointNFlip`,
`EvenEndpointMFlipOffTwo`, `EvenFlipNSlotZero` and `EvenFlipMSlotZero` **given a tuple**.  What
was not stated is the field-level form, and it is the form the paper needs, because a tuple at
`alpha = 2` is not an assumption at a depth-`2` field: wave 54's own level-three base builds one
(`evenEndpoint_nStageBase` on `N`, `evenDeepIsotropy_mStageBase` on `M`).

So at every even-degree dyadic field whose branch depth is `2`, **all four published bundles are
false**, and the four endpoints `evenRoute_orientedEquiv{N,M}` and
`evenRoute_orientedEquiv{N,M}_two` are vacuous.  Two consequences worth stating plainly.

* This includes the `N` branch, whose unguarded depth binder the wave-55 audit proved harmless
  (Finding 2, `evenRouteWitness_carriedN_of_atDepth`).  That proof is not wrong: the `N` bundle
  really does collapse to its single-depth instance.  At a depth-`2` field that instance is the
  refuted one, so the collapse delivers the falsity rather than preventing it.  The audit ranked
  the unguarded binder as "a design weakness ... not a falsehood"; against wave 55's refutation it
  is a falsehood on a nonempty class of fields, and the ranking should be read as superseded.
* It is a statement about *hypotheses*, not about the mathematics.  Nothing here says the even
  route fails at depth `2`; it says the published route cannot be run there, because its input is
  refuted.  Whether any field has branch depth `2` at all is open, and §2 gives the `M` half of
  that question its arithmetic form.

Contrast §4.3: at the same fields the two corrected bundles hold, vacuously. -/

section Retraction

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **A depth-`2` `N` field has an `alpha = 2` stage tuple**, namely the level-three base wave 54
builds from the branch identification alone. -/
theorem evenRouteCarried_nTuple_two {h : ℕ}
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN 2)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    Nonempty (Tuple (nStageWord 2 h one_le_two) (vN 2)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) 3) :=
  evenEndpoint_nStageBase (le_refl 2) hev hrange

/-- **A depth-`2` `M` field has an `alpha = 2` stage tuple**, from wave 53's frame re-cut with the
isotropy discharged by wave 54 and the ramified-`i` binder read off the identification. -/
theorem evenRouteCarried_mTuple_two {h : ℕ}
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM 2)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    Nonempty (Tuple (mStageWord 2 h one_le_two) (vM 2)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) 3) :=
  evenDeepIsotropy_mStageBase (le_refl 2) hev (evenEndpoint_kappa_of_rangeM hrange) hrange

/-- **The published `N` bundle is FALSE at a depth-`2` field.**  Its flip field contains the
refuted `alpha = 2` instance, and the tuple that refutes it exists. -/
theorem evenRouteCarried_not_carriedN {h : ℕ}
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN 2)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) : ¬ EvenEndpoint.EvenRouteCarriedN h K := by
  obtain ⟨T⟩ := evenRouteCarried_nTuple_two hrange hev
  exact fun C ↦ evenFlip_not_endpointNFlip (le_refl 3) T C.flip

/-- **The published `M` bundle is FALSE at a depth-`2` field.**  Deleting the slot-`2` demand does
not delete the slot-`0` one, and the isotropy field is beside the point. -/
theorem evenRouteCarried_not_carriedM {h : ℕ}
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM 2)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) : ¬ EvenEndpoint.EvenRouteCarriedM h K := by
  obtain ⟨T⟩ := evenRouteCarried_mTuple_two hrange hev
  exact fun C ↦ evenFlip_not_endpointMFlipOffTwo (le_refl 3) T C.flip

/-- **The published `N` stratum bundle is FALSE at a depth-`2` field**, so
`evenRoute_orientedEquivN_two` is vacuous exactly where it was meant to apply. -/
theorem evenRouteCarried_not_carriedNTwo {h : ℕ}
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN 2)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) : ¬ EvenEndpoint.EvenRouteCarriedNTwo h K := by
  obtain ⟨T⟩ := evenRouteCarried_nTuple_two hrange hev
  exact fun C ↦ evenFlip_not_flipSupply_two (le_refl 3) T C.flip

/-- **The published `M` stratum bundle is FALSE at a depth-`2` field**, so
`evenRoute_orientedEquivM_two` is vacuous exactly where it was meant to apply. -/
theorem evenRouteCarried_not_carriedMTwo {h : ℕ}
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM 2)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) : ¬ EvenEndpoint.EvenRouteCarriedMTwo h K := by
  obtain ⟨T⟩ := evenRouteCarried_mTuple_two hrange hev
  exact fun C ↦ evenFlip_not_flipSupply_two (le_refl 3) T
    (evenEndpoint_mFlip_of_offTwo (le_refl 2) C.flip)

/-! ### §6.1 The sharp limit of the retraction

§6 is a statement about depth-`2` fields and about nothing else, and this is where that limit is
made checkable.  At a field of branch depth `beta >= 3` the `alpha = 2` stage tuples do not exist
(`evenRouteWitness_nTuple_isEmpty` on `N`, §1's `evenRouteCarried_mTuple_isEmpty` on `M`), so the
very instance that is refuted at a depth-`2` field is **vacuously true** there.  The published
unguarded inputs are therefore not false outright; they are false exactly on the stratum wave 55
refuted.  Guarding removes the instance rather than assuming it away. -/

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- **At a deep `N` field the refuted `alpha = 2` instance is vacuous.** -/
theorem evenRouteCarried_flipTwo_of_deepN {beta h : ℕ} (hbeta : 3 ≤ beta)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN beta) :
    EvenDigitFlipSupply 2 (nStageWord 2 h one_le_two) (vN 2)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) :=
  fun k _ T _ ↦ ((evenRouteWitness_nTuple_isEmpty (h := h) (k := k) (le_refl 2) (by omega)
    (by omega) hrange).false T).elim

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- **At a deep `M` field the refuted `alpha = 2` instance is vacuous.**  This one needs §1: the
audit's `evenRouteWitness_vM_mem_range` shows the `M` table has no emptiness argument *above* the
produced depth, and `evenRouteCarried_mTuple_isEmpty` supplies the one *below* it, which is the
side the `alpha = 2` instance sits on. -/
theorem evenRouteCarried_flipTwo_of_deepM {beta h : ℕ} (hbeta : 3 ≤ beta)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM beta) :
    EvenDigitFlipSupply 2 (mStageWord 2 h one_le_two) (vM 2)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) :=
  fun k _ T _ ↦ ((evenRouteCarried_mTuple_isEmpty (h := h) (k := k) (le_refl 2)
    (by omega) hrange).false T).elim

/-- **The retraction in one statement.**  At a depth-`2` field, on either branch, the wave-54
published carried-input bundle and its stratum twin are both false, while the corrected bundle of
§4 holds.  This is the sentence the paper must carry where it used to quote the wave-54 list. -/
theorem evenRouteCarried_alphaTwo_retraction {h : ℕ}
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    (MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN 2 →
        ¬ EvenEndpoint.EvenRouteCarriedN h K ∧ ¬ EvenEndpoint.EvenRouteCarriedNTwo h K ∧
          EvenRouteCarriedDeepN h K) ∧
      (MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM 2 →
        ¬ EvenEndpoint.EvenRouteCarriedM h K ∧ ¬ EvenEndpoint.EvenRouteCarriedMTwo h K ∧
          EvenRouteCarriedDeepM h K) :=
  ⟨fun hrange ↦ ⟨evenRouteCarried_not_carriedN hrange hev,
      evenRouteCarried_not_carriedNTwo hrange hev, evenRouteCarried_deepN_of_two hrange⟩,
    fun hrange ↦ ⟨evenRouteCarried_not_carriedM hrange hev,
      evenRouteCarried_not_carriedMTwo hrange hev, evenRouteCarried_deepM_of_two hrange⟩⟩

end Retraction

end

end GQ2.Dyadic.EvenRouteCarried

/-! ## §7 Axiom pins

Every public declaration of this file, printed, the two local coefficient-action instances
included, together with **every statement this file supersedes**, so the comparison the campaign's
re-cut rule demands is on the page.

Write `S` for the seven-element set

  `[propext, Classical.choice, hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt,
   Quot.sound, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic]`

and `std-3` for `[propext, Classical.choice, Quot.sound]`.  **Measured**, at this tip, all 58
prints below:

* §1, §2, §3 and §4 print **std-3** exactly, with two exceptions, both concerning the wave-54
  `M` structure and both named two paragraphs down;
* §5's six endpoints print **`S`** exactly, as do §6's two stage bases, its four refutations and
  the combined retraction;
* §6.1's two vacuity statements print **std-3**, being pure emptiness arguments.

No print in this file contains `sorryAx`, and the only axioms occurring anywhere in the 58 are
std-3 together with the four census axioms `hilbertSymbol_normCriterion_finiteDyadic`,
`tateDualityAt`, `absGalQ2_isTopologicallyFinitelyGenerated` and
`absGalQ2_localEulerCharacteristic`.

The comparison the re-cut rule demands, statement by statement, measured on both sides:

| new | print | supersedes | print | verdict |
| --- | --- | --- | --- | --- |
| `EvenRouteCarriedDeepN` | std-3 | `EvenEndpoint.EvenRouteCarriedN` | std-3 | equal |
| `EvenRouteCarriedDeepM` | **std-3** | `EvenEndpoint.EvenRouteCarriedM` | std-3 + `tateDualityAt` | **strict subset** |
| `EvenRouteDeepFamily{N,M}` | std-3 | `EvenEndpoint{N,M}Family` | std-3 | equal |
| `EvenRouteDeepFlip{N,M}` | std-3 | `EvenEndpointNFlip`, `EvenEndpointMFlipOffTwo` | std-3 | equal |
| `EvenRouteDeepFlip{N,M}` | std-3 | `EvenFlip{N,M}SlotZeroDeep` | std-3 | equal |
| `evenRouteCarried_orientedEquivN_atDepth` | `S` | `evenFlip_orientedEquivN_atDepth`, `evenEndpoint_orientedEquivN_atDepth` | `S` | equal |
| `evenRouteCarried_orientedEquivM_atDepth` | `S` | `evenFlip_orientedEquivM_atDepth`, `evenEndpoint_orientedEquivM_atDepth` | `S` | equal |
| `evenRouteCarried_orientedEquivN` | `S` | `evenFlip_orientedEquivN`, `evenRoute_orientedEquivN` | `S` | equal |
| `evenRouteCarried_orientedEquivM` | `S` | `evenFlip_orientedEquivM`, `evenRoute_orientedEquivM` | `S` | equal |

**Every new statement pins to a subset of the statement it supersedes, and one pins to a strict
subset.**  That one is the point of the lane: `EvenRouteCarriedM` printed `tateDualityAt` because
its third field `EvenDeepMIsotropicSupply` mentions `frattiniFrameCup`, which is built through
Tate duality; dropping the field drops the axiom, and the corrected `M` bundle is character-equal
to the corrected `N` bundle rather than one axiom above it.  That is the census form of "both
branches carry the same two inputs".

Two prints to read carefully rather than as anomalies.  `evenRouteCarried_deepM_of_carriedM`
prints std-3 plus `tateDualityAt`, because the *hypothesis* it consumes is the wave-54 three-field
structure; the axiom is in what it is given, not in what it produces.  And
`evenRouteCarried_{n,m}Tuple_two` print `S`, being the wave-54 and wave-53 level-three bases
verbatim: §6's refutations cost exactly what building a stage base costs, and nothing more.

No axiom of this file is new; the census stays at eleven. -/

section AxiomPins

open GQ2.Dyadic.EvenRouteCarried

-- the two coefficient-action instances
#print axioms evenRouteCarriedScalar
#print axioms evenRouteCarriedContinuousScalar

-- §1 depth rigidity
#print axioms evenRouteCarried_mUnit_not_mem_imChiM
#print axioms evenRouteCarried_imChiM_inj
#print axioms evenRouteCarried_imChiN_inj
#print axioms evenRouteCarried_depthN_unique
#print axioms evenRouteCarried_depthM_unique
#print axioms evenRouteCarried_mTuple_isEmpty

-- §2 the `alpha = 2` question in arithmetic form
#print axioms evenRouteCarried_depthM_two_iff_top

-- §3 the guarded carried inputs, against the wave-54 and wave-55 forms they replace
#print axioms EvenRouteDeepFamilyN
#print axioms EvenRouteDeepFamilyM
#print axioms EvenRouteDeepFlipN
#print axioms EvenRouteDeepFlipM
#print axioms GQ2.Dyadic.EvenEndpoint.EvenEndpointNFamily
#print axioms GQ2.Dyadic.EvenEndpoint.EvenEndpointMFamily
#print axioms GQ2.Dyadic.EvenEndpoint.EvenEndpointNFlip
#print axioms GQ2.Dyadic.EvenEndpoint.EvenEndpointMFlipOffTwo
#print axioms GQ2.Dyadic.StageGeneric.EvenFlipNSlotZeroDeep
#print axioms GQ2.Dyadic.StageGeneric.EvenFlipMSlotZeroDeep

-- §4 the two corrected bundles, against the four published ones
#print axioms EvenRouteCarriedDeepN
#print axioms EvenRouteCarriedDeepM
#print axioms GQ2.Dyadic.EvenEndpoint.EvenRouteCarriedN
#print axioms GQ2.Dyadic.EvenEndpoint.EvenRouteCarriedM
#print axioms GQ2.Dyadic.EvenEndpoint.EvenRouteCarriedNTwo
#print axioms GQ2.Dyadic.EvenEndpoint.EvenRouteCarriedMTwo
#print axioms evenRouteCarried_deepN_of_carriedN
#print axioms evenRouteCarried_deepM_of_carriedM
#print axioms evenRouteCarried_deepN_of_slotZeroDeep
#print axioms evenRouteCarried_deepM_of_slotZeroDeep
#print axioms evenRouteCarried_deepN_of_atDepth
#print axioms evenRouteCarried_deepM_of_atDepth
#print axioms evenRouteCarried_deepN_iff_atDepth
#print axioms evenRouteCarried_deepM_iff_atDepth
#print axioms evenRouteCarried_deepN_of_two
#print axioms evenRouteCarried_deepM_of_two

-- §5 the endpoints, against every statement they supersede
#print axioms evenRouteCarried_orientedEquivN_atDepth
#print axioms GQ2.Dyadic.StageGeneric.evenFlip_orientedEquivN_atDepth
#print axioms GQ2.Dyadic.EvenEndpoint.evenEndpoint_orientedEquivN_atDepth
#print axioms evenRouteCarried_orientedEquivM_atDepth
#print axioms GQ2.Dyadic.StageGeneric.evenFlip_orientedEquivM_atDepth
#print axioms GQ2.Dyadic.EvenEndpoint.evenEndpoint_orientedEquivM_atDepth
#print axioms evenRouteCarried_orientedEquivN
#print axioms GQ2.Dyadic.StageGeneric.evenFlip_orientedEquivN
#print axioms GQ2.Dyadic.EvenEndpoint.evenRoute_orientedEquivN
#print axioms evenRouteCarried_orientedEquivM
#print axioms GQ2.Dyadic.StageGeneric.evenFlip_orientedEquivM
#print axioms GQ2.Dyadic.EvenEndpoint.evenRoute_orientedEquivM
#print axioms evenRouteCarried_orientedEquivN_dichotomy
#print axioms evenRouteCarried_orientedEquivM_dichotomy

-- §6 the retraction
#print axioms evenRouteCarried_nTuple_two
#print axioms evenRouteCarried_mTuple_two
#print axioms evenRouteCarried_not_carriedN
#print axioms evenRouteCarried_not_carriedM
#print axioms evenRouteCarried_not_carriedNTwo
#print axioms evenRouteCarried_not_carriedMTwo
#print axioms evenRouteCarried_flipTwo_of_deepN
#print axioms evenRouteCarried_flipTwo_of_deepM
#print axioms evenRouteCarried_alphaTwo_retraction

end AxiomPins

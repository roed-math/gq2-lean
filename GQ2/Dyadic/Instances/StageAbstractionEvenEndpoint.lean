/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenFrameDeep
import GQ2.Dyadic.Instances.StageAbstractionEvenDigit

/-!
# W54-COMPOSE: the composed even endpoints, and the honest input list of the even route

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

**Both advances compose with no conflict, and three further inputs fall.**  The composed
endpoints are §6's `evenEndpoint_orientedEquiv{N,M}` with the strata
`evenEndpoint_orientedEquiv{N,M}_two`, and the even route's carried list after this lane is:

| branch | before this lane (wave-53 best) | after this lane |
| --- | --- | --- |
| `N`, every `α ≥ 2` | `Hbase`, `Hfam`, flips; binder `κ ≠ 0` at `α = 2` | `Hfam`, flips |
| `M`, every `α ≥ 2` | `Hbase` or (`κ ≠ 0` and `Hiso`), `Hfam`, `Hup` | `Hfam`, flips off slot `2`, `Hiso` |
| `N`, `α = 2` | `Hfam`, flips; binders `B`, `κ ≠ 0` | `Hfam`, flips |
| `M`, `α = 2` | `Hfam`, flips; binders `B`, `κ ≠ 0` | `Hfam`, flips off slot `2` |

So at `α = 2` **both** branches now carry exactly the odd route's two inputs, with the
raw-to-bracket half reduced to one digit per slot and, on `M`, one slot fewer than that; and
the `N` branch carries those same two inputs at **every** `α ≥ 2`.  The only input the `M`
branch owes above `α = 2` that the `N` branch does not is the isotropy, and W53-KAPPA §5
proves it necessary.

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
4. **The `α ≥ 1` quantifier of the carried supplies, tightened to `α ≥ 2` (§5).**  Every
   committed per-`K` input (`EvenPerK{N,M}StageBase`, `…FamilySupply`, `…RawToBracket`,
   `EvenPerK{N,M}DigitFlip`) quantifies over every `α ≥ 1`, while the range identity produces
   one `α`, and that `α` is `≥ 2`.  The endpoints below carry the `α ≥ 2` forms, which is
   strictly less.  (This is also what forced W53-KAPPA to re-assemble rather than instantiate:
   `EvenPerKMStageBase` at `α = 1` is unreachable from the identity.  With the tightened
   binder the re-assembly is no longer forced, and §6 records that.)

**Refused: the isotropy on `M`.**  `EvenDeepMIsotropicSupply` is not removable, and this is a
theorem, not a judgement: W53-KAPPA §5's `evenFrameDeep_isotropic_of_frame` derives it from the
mere existence of an `M`-row cup-adapted frame, so any route to the `M` base through a frame
pays it.  §7 restates that as the sharp statement about this file's own `M` endpoint.  The `N`
analogue is free precisely because `evenDeep_digit_imChiN` makes the `N` depth class `κ` itself,
whose isotropy is `evenFrameCup_kappa_self`, a parity corollary at even degree.

**Also dropped, and worth naming: the marked reciprocity bundle `B`.**  Every committed even
endpoint carries a `MarkedRecip R K`, and every one of them uses it for exactly one thing:
producing `α` from `evenRange_range_eq_imChi{N,M}`.  The level-three station carries `B`
unused (`evenLevelThreeN_stageBase`'s docstring says so).  Since §2's base is built without
the station, the at-depth endpoints of §5 and the strata of §7 carry no bundle at all.

## Composition audit: the two advances do not conflict

The only place where a conflict could have arisen is the shape of the depth binder: W53-KAPPA
states its isotropy supply at `2 ≤ alpha` and W53-HUP states its flip supplies at `1 ≤ alpha`,
and the two are fed to the same `α` produced by the identity.  Since `1 ≤ alpha` implies
`2 ≤ alpha` nowhere, the honest joint form is the `2 ≤ alpha` one, which is what §5 carries;
the wave-53 files' `1 ≤ alpha` forms imply it (`evenEndpoint_nFlip_of_perK`,
`evenEndpoint_mFlip_of_perK`), so nothing is strengthened and every wave-53 consumer still
applies.  Beyond that the two advances touch disjoint machinery: KAPPA re-cuts the frame that
produces the level-three base, HUP re-cuts the residual supply of the climb above it, and the
committed `evenPerK_forwardGeneratorData{N,M}` is the unchanged seam between them.

## Numbering

1. the ramified-`i` binder, discharged on both branches;
2. the `N`-row frame from the deep seam, with no new input;
3. the `N` level-three base;
4. the reduced `M` flip supply;
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
particular no branch depth is needed. -/
theorem evenEndpoint_kappa_of_negOne
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom) :
    cyclotomicModFourClassKTwo (K := K) ≠ 0 :=
  evenEndpoint_kappa_of_value hneg evenDegreeM_parity_negOne

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

end OffTwo

end

end GQ2.Dyadic.EvenEndpoint

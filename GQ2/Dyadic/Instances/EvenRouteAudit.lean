/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenAlphaTwo
import GQ2.Dyadic.Instances.EvenRouteCarried
import GQ2.Dyadic.Instances.EvenSlotZero
import GQ2.Dyadic.SqCore.GradedFourMirror
import GQ2.Dyadic.SqCore.GradedLatticeWide

/-!
# W57-REAUDIT: what the wave-56 lanes proved about each other, and did not compose

This file carries the Lean the wave-57 re-audit produced.  Its subject is not new mathematics:
every ingredient below was committed by a wave-56 lane.  What is new is the **composition**, and
in two places the composition inverts a published conclusion.  The wave-56 lanes are pairwise
independent in the import graph (`EvenRouteCarried`, `EvenSlotZero`, `EvenAlphaTwo`,
`GradedFourMirror`, `GradedLatticeWide`: no one of the five reaches any other), so no lane could
see what its siblings had proved, and the orchestrator merged them in an order that never
re-checked the earlier ones.  This is the wave-55 "two lanes never met" pattern, at wave-56
scale.

## §1 The corrected artefact is refuted above the stratum it was corrected for

`EvenRouteCarried.lean` (W56-RECUT, merged first) publishes `EvenRouteCarriedDeep{N,M}` as the
corrected paper-facing list, retracting the wave-54 bundles on the `α = 2` stratum and stating
the corrected ones at `α ≥ 3` with two fields: `Hfam` and **the slot-`0` flip demand**, guarded
by the range identity.  `EvenSlotZero.lean` (W56-SLOTZERO, merged two commits later) then refutes
`EvenDigitFlipSupplySlotZero α` at **every** `α ≥ 2` on both branches as soon as one stage tuple
exists.

The two compose, and the composition is `evenRouteAudit_not_carriedDeep{N,M}`: at every field
whose branch depth is `α ≥ 3` the corrected bundle is **false**, because the level-three base is
built rather than carried (`evenEndpoint_nStageBase`, `evenDeepIsotropy_mStageBase`) and supplies
the tuple the refutation needs.  Hence

* `evenRouteCarried_orientedEquiv{N,M}` have unsatisfiable hypothesis sets outright
  (`evenRouteAudit_orientedEquiv{N,M}_vacuous`), their `hnotTwo` binder having excluded the one
  stratum where the bundle can hold;
* `evenRouteCarried_orientedEquiv{N,M}_dichotomy` retain content only at branch depth `2`, where
  their conclusion is empty: `evenRouteAudit_dichotomy{N,M}_forces_two` shows the bundle forces
  the produced depth to be `2`.

Nothing here contradicts a committed *statement*.  `EvenRouteCarried.lean` §6.1 is right that the
`α = 2` instance is vacuous at a deep field; what it does not say, because it could not see it,
is that the `α ≥ 3` instances are refuted there.  The file's own before/after table (`α ≥ 3`
carries "`Hfam` and the slot-`0` flip") and its §6 sentence "the corrected artefact is true where
the published one is false" are the passages that need correction.

## §2 The residual supply is a one-digit demand, and the mechanism does reach it

`EvenAlphaTwo.lean` §6.1 argues that the slot-`0` obstruction "has no force against the neutral
corrections the residual supply quantifies over", and the campaign records this as
"nothing in the tree refutes `EvenClimbResidualSupply`".  The first half is true and the second
is true; the *reason* given is too strong, and the sharpest-bound doctrine of wave 56 asks for
the reason to be checked.

Three statements here, in increasing sharpness.

1. `evenRouteAudit_residual_iff_actualDefect`: the `∀ Wc` in `EvenClimbResidualSupply` is **not**
   an over-quantification.  By the torsor criterion the supply is *equivalent* to "an actual
   defect supply exists at every level `k ≥ 3`", which is exactly what `evenClimb_defectReachable`
   consumes.  So the wave-52 and wave-56 binder defects are not present here.
2. `evenRouteAudit_neutral_meets_refined_digit`: the non-collision, against the **sharpest** bound
   the tree owns rather than the generic one.  `evenAlphaTwo_neutral_slotZero_digit` states only
   `2 ^ (k + 1) ∣ χ(g) − 1`, which is the wave-55 (`α = 2`) form; at `s = α − 1` neutrality gives
   `2 ^ (k + 1 + s)`, so the wave-56 refined bound `2 ^ (k + (α − 1))` of `evenSlotZero_digit` is
   met with a digit to spare.  The conclusion of §6.1 survives its own sharpest bound.
3. **But the mechanism reaches the supply anyway.**  `evenRouteAudit_dbar_slotZero_sq` is
   `evenFlip_slotZero_sq_mem_commutator` with its `dbar = 1` hypothesis removed: the shift word
   of *any* depth correction is its slot-`0` square modulo commutators.  Feeding a neutral
   correction through it gives `evenRouteAudit_residual_digit_necessary`: the supply forces the
   residual's own character to be trivial to `k + α` digits.  And
   `evenRouteAudit_residual_digit_automatic` says the tower already gives `k + α − 1`, because the
   residual lies in `λ_k`.

   **The residual supply is therefore a one-digit character demand at coordinate `0`** - the same
   coordinate, the same one digit, and the same square as the two refutations the campaign has
   already met.  This is **not** a refutation: nothing here shows the residual's character is
   sharp at level `k + α − 1`, and if it is deeper the demand is met.  It is a statement of where
   the decisive question actually sits, and it is one level finer than "nothing refutes it".

## §3 The class-four soundness is stated over less than the tree's own `γ₂(im Φ)`

`GradedLatticeWide` (W56-WIDEN, merged last) fixes the campaign's meaning of the honest achievable
object: `γ₂(im Φ) = ⟨⁅im Φ, im Φ⁆, Φ(x₁)²⟩`, the `x₁`-square being "the only non-commutator
generator", and its `selGaTwoIm` adjoins that square explicitly.  `GradedFourRow` and
`GradedFourMirror` (W56-MIRROR, merged one commit earlier) state their model-independent soundness
over `rowGaTwoOf (…)` alone, which is the commutator subgroup **without** the square, while
describing it as "the whole commutator subgroup `γ₂(im Φ)` … the sigma-slot dressing needs no
constraint whatsoever".

The gap is real as a matter of statement and empty as a matter of substance: all four markings
carry `sigFourY` in the `x₁` slot, and `evenRouteAudit_sigFourY_sq_mem` puts its square in
`rowGaTwoSub`.  So `evenRouteAudit_{rowFour,mirFour,dblFour,rowWide}_gaTwoIm_le` extend the four
committed soundness statements to the `GradedLatticeWide`-shaped object at no cost.  A consumer
should cite these rather than the four `_commutator_le` statements.

## Numbering

1. the corrected bundle refuted above the stratum, and the endpoints it makes vacuous;
2. the residual supply: shape, non-vacuity, and the one-digit demand;
3. the class-four `γ₂` scope, closed at the three row points;
4. axiom pins.
-/

namespace GQ2.Dyadic.EvenRouteAudit

noncomputable section

open GQ2 ContCoh
open GQ2.Roe.Labute
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
open scoped commutatorElement

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The coefficient action at `G_K(2)`, as everywhere on this route. -/
local instance evenRouteAuditScalar {K : IntermediateField ℚ_[2] ℚ̄₂} [CompactSpace (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] :
    DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

/-- Continuity of that action. -/
local instance evenRouteAuditContinuousScalar {K : IntermediateField ℚ_[2] ℚ̄₂}
    [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-! ## §1 The corrected artefact, above the stratum it was corrected for

`EvenRouteDeepFlip{N,M}` demands `EvenDigitFlipSupplySlotZero α` at every branch depth `α ≥ 3`
the field's range identity produces.  W56-SLOTZERO refutes that demand at every `α ≥ 2` once one
stage tuple exists, and at a field of depth `α` the level-three base is a theorem, not a
hypothesis.  So the demand is refuted exactly where it is non-vacuous. -/

section Recut

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The corrected `N` flip input is false at a deep field.** -/
theorem evenRouteAudit_not_deepFlipN {alpha h : ℕ} (halpha : 3 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    ¬ EvenRouteDeepFlipN h K := by
  intro H
  obtain ⟨T⟩ := evenEndpoint_nStageBase (α := alpha) (h := h) (by omega) hev hrange
  exact evenSlotZero_not_nAtDepth (by omega) (le_refl 3) hrange T (H alpha halpha hrange)

/-- **The corrected `M` flip input is false at a deep field.** -/
theorem evenRouteAudit_not_deepFlipM {alpha h : ℕ} (halpha : 3 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    ¬ EvenRouteDeepFlipM h K := by
  intro H
  obtain ⟨T⟩ := evenDeepIsotropy_mStageBase (α := alpha) (h := h) (by omega) hev
    (evenEndpoint_kappa_of_rangeM hrange) hrange
  exact evenSlotZero_not_mAtDepth (by omega) (le_refl 3) hrange T (H alpha halpha hrange)

/-- ⭐ **The corrected `N` bundle is FALSE at every field of branch depth `α ≥ 3`.**  The
retraction of `EvenRouteCarried.lean` §6 covers the depth-`2` stratum; this covers all the
others, so no field of either kind satisfies the published corrected list. -/
theorem evenRouteAudit_not_carriedDeepN {alpha h : ℕ} (halpha : 3 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    ¬ EvenRouteCarriedDeepN h K := fun C ↦
  evenRouteAudit_not_deepFlipN halpha hrange hev C.flip

/-- ⭐ **The corrected `M` bundle is FALSE at every field of branch depth `α ≥ 3`.** -/
theorem evenRouteAudit_not_carriedDeepM {alpha h : ℕ} (halpha : 3 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    ¬ EvenRouteCarriedDeepM h K := fun C ↦
  evenRouteAudit_not_deepFlipM halpha hrange hev C.flip

/-- ⭐⭐ **`evenRouteCarried_orientedEquivN` is vacuous**: its own binders, with the `hnotTwo`
that puts the field off the retracted stratum, already refute the bundle it consumes. -/
theorem evenRouteAudit_orientedEquivN_vacuous {R : LocalReciprocity} (B : MarkedRecip R K)
    (deltaI : ℚ̄₂) (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI)
    (hneg : (-1 : ℤ_[2]ˣ) ∉ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (hnotTwo : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom ≠ imChiN 2)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    ¬ EvenRouteCarriedDeepN h K := by
  obtain ⟨alpha, halpha, hrange⟩ := evenRange_range_eq_imChiN B deltaI hdeltaI hram hneg
  have h3 : 3 ≤ alpha := by
    by_contra hlt
    exact hnotTwo (by rw [hrange, show alpha = 2 by omega])
  exact evenRouteAudit_not_carriedDeepN h3 hrange hev

/-- ⭐⭐ **`evenRouteCarried_orientedEquivM` is vacuous**, the same way. -/
theorem evenRouteAudit_orientedEquivM_vacuous {R : LocalReciprocity} (B : MarkedRecip R K)
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (hnotTwo : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom ≠ imChiM 2)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    ¬ EvenRouteCarriedDeepM h K := by
  obtain ⟨alpha, halpha, hrange⟩ := evenRange_range_eq_imChiM B hneg
  have h3 : 3 ≤ alpha := by
    by_contra hlt
    exact hnotTwo (by rw [hrange, show alpha = 2 by omega])
  exact evenRouteAudit_not_carriedDeepM h3 hrange hev

/-- ⭐ **The `N` dichotomy endpoint keeps content only on the retracted stratum.**  Holding the
corrected bundle forces the produced branch depth to be `2`, where the dichotomy's conclusion is
the empty implication. -/
theorem evenRouteAudit_dichotomyN_forces_two {R : LocalReciprocity} (B : MarkedRecip R K)
    (deltaI : ℚ̄₂) (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI)
    (hneg : (-1 : ℤ_[2]ˣ) ∉ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    {h : ℕ} (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) (C : EvenRouteCarriedDeepN h K) :
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN 2 := by
  obtain ⟨alpha, halpha, hrange⟩ := evenRange_range_eq_imChiN B deltaI hdeltaI hram hneg
  by_cases h3 : 3 ≤ alpha
  · exact absurd C (evenRouteAudit_not_carriedDeepN h3 hrange hev)
  · rwa [show alpha = 2 by omega] at hrange

/-- ⭐ **The `M` dichotomy endpoint keeps content only on the retracted stratum.** -/
theorem evenRouteAudit_dichotomyM_forces_two {R : LocalReciprocity} (B : MarkedRecip R K)
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    {h : ℕ} (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) (C : EvenRouteCarriedDeepM h K) :
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM 2 := by
  obtain ⟨alpha, halpha, hrange⟩ := evenRange_range_eq_imChiM B hneg
  by_cases h3 : 3 ≤ alpha
  · exact absurd C (evenRouteAudit_not_carriedDeepM h3 hrange hev)
  · rwa [show alpha = 2 by omega] at hrange

end Recut

/-! ## §2 The residual supply

§2.1 the shape, §2.2 the non-collision at the sharpest bound, §2.3 the one-digit demand. -/

section ResidualShape

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h s : ℕ}
variable {W : StageWord (MarkedCore.coreRank h)} {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}

/-- **The `∀ Wc` is not an over-quantification.**  By the torsor criterion of
`StageAbstractionEvenSharpHandles.lean` §7 the residual supply is equivalent to "an actual-defect
supply exists at every level `k ≥ 3`", which is exactly what `evenClimb_defectReachable`
consumes.  So the supply neither over-quantifies (as the wave-52 uniform `Hrange` did) nor
under-quantifies. -/
theorem evenRouteAudit_residual_iff_actualDefect :
    EvenClimbResidualSupply s W v G chi ↔
      ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple W v G chi k, Nonempty (EvenSharpActualDefectSupply s T) := by
  constructor
  · intro H k hk T
    obtain ⟨Wc⟩ := evenSharpDeepAdmissible_nonempty s T
    exact (nonempty_evenSharpActualDefectSupply_iff_residual hk Wc).mpr (H k hk T Wc)
  · intro H k hk T Wc
    exact (nonempty_evenSharpActualDefectSupply_iff_residual hk Wc).mp (H k hk T)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **The demand is instantiated whenever one stage tuple exists.**  The supply is not vacuous in
its correction binder: depth-`s` admissible corrections always exist. -/
theorem evenRouteAudit_residual_correction_nonempty {k : ℕ} (T : Tuple W v G chi k) :
    Nonempty (DeepSharpAdmissibleCorrection s T) :=
  evenSharpDeepAdmissible_nonempty s T

end ResidualShape

section Neutral

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {s h k : ℕ}

/-- Neutrality at full strength: `2 ^ (k + 1 + s)`, not the `2 ^ (k + 1)` that
`evenAlphaTwo_neutral_slotZero_digit` records. -/
theorem evenRouteAudit_neutral_digit_sharp (N : EvenSharpNeutralCorrection s G chi h k)
    (i : Fin (MarkedCore.coreRank h)) :
    ∃ g : G, N.correction i = levelMk G (k + 1) g ∧
      (2 : ℤ_[2]) ^ (k + 1 + s) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  obtain ⟨g, hg, hchi⟩ := N.neutral i
  exact ⟨g, hg, evenSharp_mem_ker_iff.mp (MonoidHom.mem_ker.mpr hchi)⟩

/-- ⭐ **The non-collision, checked against the sharpest bound the tree owns.**  At the depth the
climb uses, `s = α − 1`, every coordinate of a neutral correction satisfies the wave-56 *refined*
divisibility `2 ^ (k + (α − 1)) ∣ χ(g) − 1` of `evenSlotZero_digit`, with a digit to spare.  So
`EvenAlphaTwo.lean` §6.1's conclusion survives the sharpest-bound check, even though the lemma it
cites is the generic wave-55 one. -/
theorem evenRouteAudit_neutral_meets_refined_digit {α : ℕ}
    (N : EvenSharpNeutralCorrection (α - 1) G chi h k) (i : Fin (MarkedCore.coreRank h)) :
    ∃ g : G, N.correction i = levelMk G (k + 1) g ∧
      (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  obtain ⟨g, hg, hdvd⟩ := evenRouteAudit_neutral_digit_sharp N i
  exact ⟨g, hg, (pow_dvd_pow (2 : ℤ_[2]) (by omega : k + (α - 1) ≤ k + 1 + (α - 1))).trans hdvd⟩

end Neutral

section Dbar

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h k : ℕ}

private theorem evenRouteAudit_commP_mem {H : Type*} [Group H] (x y : H) :
    commP x y ∈ commutator H := by
  rw [show commP x y = ⁅x⁻¹, y⁻¹⁆ from by simp only [commP, commutatorElement_def, inv_inv]]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private theorem evenRouteAudit_handle_mem
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) :
    evenRawHandleDbarWord base correction ∈ commutator (levelQuot G (k + 1)) := by
  rw [evenRawHandleDbarWord]
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨j, _, rfl⟩ := hx
  exact Subgroup.mul_mem _ (evenRouteAudit_commP_mem _ _) (evenRouteAudit_commP_mem _ _)

/-- ⭐ **The shift word is the slot-`0` square modulo commutators, with no hypothesis on the
word.**  `evenFlip_slotZero_sq_mem_commutator` is the special case `dbar = 1`, and dropping that
hypothesis is what lets the slot-`0` mechanism reach a supply that never asks for a trivial shift
word. -/
theorem evenRouteAudit_dbar_slotZero_sq
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) :
    (correction 0 ^ 2)⁻¹ * evenRawDbarWord base correction
      ∈ commutator (levelQuot G (k + 1)) := by
  set X := commP (correction 0) (base 0) *
    (commP (correction 1) (base 0) * commP (correction 0) (base 1)) *
    (commP (correction 3) (base 2) * commP (correction 2) (base 3)) *
    evenRawHandleDbarWord base correction with hX
  have hXmem : X ∈ commutator (levelQuot G (k + 1)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (evenRouteAudit_commP_mem _ _)
      (Subgroup.mul_mem _ (evenRouteAudit_commP_mem _ _) (evenRouteAudit_commP_mem _ _)))
      (Subgroup.mul_mem _ (evenRouteAudit_commP_mem _ _) (evenRouteAudit_commP_mem _ _)))
      (evenRouteAudit_handle_mem base correction)
  have heq : (correction 0 ^ 2)⁻¹ * evenRawDbarWord base correction = X := by
    rw [evenRawDbarWord, evenRawCoreDbarWord, hX]
    group
  rw [heq]
  exact hXmem

end Dbar

section ResidualDigit

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h k α : ℕ}
variable {W : StageWord (MarkedCore.coreRank h)} {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- ⭐⭐ **The slot-`0` mechanism DOES reach the residual supply.**  If the residual of a
depth-`(α − 1)` admissible correction is a neutral literal shift, then the residual's *own*
character is trivial to `k + α` digits: the shift word is the slot-`0` square modulo commutators
(§2.3's first lemma), the slot-`0` coordinate of a neutral correction is trivial to `k + α`
digits, and a character kills commutators.

So `EvenClimbResidualSupply (α − 1)` is a character-digit condition on the residual, of exactly
the shape that refuted the flip route.  It is not refuted here: see the companion statement for
what the tower gives automatically, and the module docstring for what is and is not concluded. -/
theorem evenRouteAudit_residual_digit_necessary (hα : 2 ≤ α) (hk : 3 ≤ k)
    (hbound : ∀ g : G, EvenSharpPmOne α (chi g)) {T : Tuple W v G chi k}
    (Wc : DeepSharpAdmissibleCorrection (α - 1) T)
    (H : EvenSharpNeutralResidualReachable Wc) {r : G}
    (hr : evenSharpNeutralResidualElement Wc = levelMk G (k + 1) r) :
    (2 : ℤ_[2]) ^ (k + α) ∣ ((chi r : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  obtain ⟨N, hN⟩ := H
  have hdec := evenRouteAudit_dbar_slotZero_sq
    (fun i ↦ canonLift G k (T.generators i)) N.correction
  rw [hN] at hdec
  have hmapc : commutator (levelQuot G (k + 1)) =
      Subgroup.map (levelMk G (k + 1)) (commutator G) := by
    rw [commutator, commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (levelMk_surjective G (k + 1))]
  rw [hmapc] at hdec
  obtain ⟨y, hy, hyeq⟩ := hdec
  obtain ⟨g₀, hg₀, hg₀chi⟩ := N.neutral 0
  rw [hr, hg₀, ← map_pow, ← map_inv, ← map_mul] at hyeq
  have hker : (g₀ ^ 2)⁻¹ * r * y⁻¹ ∈ twoCentralSeries G (k + 1) := by
    have : levelMk G (k + 1) ((g₀ ^ 2)⁻¹ * r * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hyeq, mul_inv_cancel]
    rwa [levelMk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  have hdeep := evenSharp_map_le_deep (chi := chi) (by omega : 1 ≤ α) hbound (k + 1) (by omega)
    (Subgroup.mem_map_of_mem _ hker)
  have hchiy : chi.toMonoidHom y = 1 := by
    have hle : commutator G ≤ (chi.toMonoidHom).ker := by
      rw [commutator_eq_closure]
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨g₁, g₂, rfl⟩
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, commutatorElement_def, map_mul, map_inv]
      exact mul_inv_eq_one.mpr (by rw [mul_comm]; group)
    exact hle hy
  have hg₀mem : chi g₀ ∈ (Units.map (PadicInt.toZModPow (k + 1 + (α - 1))).toMonoidHom).ker :=
    MonoidHom.mem_ker.mpr hg₀chi
  rw [show k + 1 + (α - 1) = k + α by omega] at hg₀mem hdeep
  have hmid : chi.toMonoidHom ((g₀ ^ 2)⁻¹ * r * y⁻¹)
      = (chi.toMonoidHom g₀ ^ 2)⁻¹ * chi.toMonoidHom r := by
    rw [map_mul, map_mul, map_inv, map_inv, map_pow, hchiy, inv_one, mul_one]
  have hgoal : chi.toMonoidHom r
      = chi.toMonoidHom g₀ ^ 2 * chi.toMonoidHom ((g₀ ^ 2)⁻¹ * r * y⁻¹) := by
    rw [hmid, mul_inv_cancel_left]
  refine evenSharp_mem_ker_iff.mp ?_
  show chi.toMonoidHom r ∈ _
  rw [hgoal]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hg₀mem 2) hdeep

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The residual sits in the central involutive layer `zLayer G k = lambdaImage G k (k + 1)`. -/
theorem evenRouteAudit_residual_mem_zLayer (hk : 3 ≤ k) {T : Tuple W v G chi k}
    (Wc : DeepSharpAdmissibleCorrection (α - 1) T) :
    evenSharpNeutralResidualElement Wc ∈ zLayer G k :=
  Subgroup.mul_mem _
    (Subgroup.inv_mem _ (evenRawDbarWord_mem_zLayer h k hk _ _ Wc.depth))
    (Subgroup.inv_mem _ (stageDefect_mem_zLayer W k T.relation))

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- ⭐⭐ **What the tower gives without the supply**: `k + α − 1` digits, because the residual
lies in `λ_k`.  Against the previous statement's `k + α`, the residual supply is a **one-digit**
character demand at coordinate `0` - the same coordinate, the same digit and the same square as
`evenSlotZero_digit`.  Whether that digit is available is open: nothing in the tree pins the
residual's own character level, and if it is deeper than `k + α − 1` the demand is met. -/
theorem evenRouteAudit_residual_digit_automatic (hα : 2 ≤ α) (hk : 3 ≤ k)
    (hbound : ∀ g : G, EvenSharpPmOne α (chi g)) {T : Tuple W v G chi k}
    (Wc : DeepSharpAdmissibleCorrection (α - 1) T) {r : G}
    (hr : evenSharpNeutralResidualElement Wc = levelMk G (k + 1) r) :
    (2 : ℤ_[2]) ^ (k + α - 1) ∣ ((chi r : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  obtain ⟨w, hw, hwq⟩ := evenRouteAudit_residual_mem_zLayer (α := α) hk Wc
  have hker : r * w⁻¹ ∈ twoCentralSeries G (k + 1) := by
    have : levelMk G (k + 1) (r * w⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hr, hwq, mul_inv_cancel]
    rwa [levelMk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  have hrmem : r ∈ twoCentralSeries G k := by
    have := Subgroup.mul_mem _ (twoCentralSeries_antitone G (by omega : k ≤ k + 1) hker) hw
    simpa using this
  have hd := evenSharp_map_le_deep (chi := chi) (by omega : 1 ≤ α) hbound k (by omega)
    (Subgroup.mem_map_of_mem _ hrmem)
  rw [evenSharp_mem_ker_iff] at hd
  rwa [show k + (α - 1) = k + α - 1 by omega] at hd

end ResidualDigit

end

end GQ2.Dyadic.EvenRouteAudit

/-! ## §3 The class-four `γ₂` scope at the three row points -/

namespace GQ2.Dyadic.SqCore

open MarkedCore

/-- The `x₁`-square, the one non-commutator generator `GradedLatticeWide` adjoins to
`⁅im Φ, im Φ⁆` to obtain the honest `γ₂(im Φ)`, lands in `rowGaTwoSub`.  All four class-four row
markings carry `sigFourY` in the `x₁` slot, so this one computation closes the scope gap at every
one of them. -/
theorem evenRouteAudit_sigFourY_sq_mem : sigFourY * sigFourY ∈ rowGaTwoSub gr3R := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, 2, ?_⟩ <;> decide

section RowPoints

variable {h : ℕ} {j : Fin h}

/-- ⭐ `GradedFourRow`'s soundness, over the object `GradedLatticeWide` calls `γ₂(im Φ)`: the
commutator subgroup **together with** the `x₁`-square. -/
theorem evenRouteAudit_rowFour_gaTwoIm_le (c : gr3R) :
    rowGaTwoOf (Subgroup.closure (Set.range (rowFourMark c)))
        ⊔ Subgroup.closure {rowFourMark c 2 * rowFourMark c 2} ≤ rowGaTwoSub gr3R := by
  refine sup_le (rowFour_commutator_le c) ?_
  rw [Subgroup.closure_le]
  rintro z rfl
  rw [rowFourMark_two]
  exact evenRouteAudit_sigFourY_sq_mem

/-- ⭐ The same at the mirror row. -/
theorem evenRouteAudit_mirFour_gaTwoIm_le (c : gr3R) :
    rowGaTwoOf (Subgroup.closure (Set.range (mirFourMark h j c)))
        ⊔ Subgroup.closure {mirFourMark h j c 2 * mirFourMark h j c 2} ≤ rowGaTwoSub gr3R := by
  refine sup_le (mirFour_commutator_le c) ?_
  rw [Subgroup.closure_le]
  rintro z rfl
  rw [mirFourMark_two]
  exact evenRouteAudit_sigFourY_sq_mem

/-- ⭐ The same at the doubly-uncleared row. -/
theorem evenRouteAudit_dblFour_gaTwoIm_le (c : gr3R) :
    rowGaTwoOf (Subgroup.closure (Set.range (dblFourMark h j c)))
        ⊔ Subgroup.closure {dblFourMark h j c 2 * dblFourMark h j c 2} ≤ rowGaTwoSub gr3R := by
  refine sup_le (dblFour_commutator_le c) ?_
  rw [Subgroup.closure_le]
  rintro z rfl
  rw [dblFourMark_two]
  exact evenRouteAudit_sigFourY_sq_mem

/-- ⭐ The same at the widened uncleared row. -/
theorem evenRouteAudit_rowWide_gaTwoIm_le (c : gr3R) :
    rowGaTwoOf (Subgroup.closure (Set.range (rowWideMark h j c)))
        ⊔ Subgroup.closure {rowWideMark h j c 2 * rowWideMark h j c 2} ≤ rowGaTwoSub gr3R := by
  refine sup_le (rowWide_commutator_le c) ?_
  rw [Subgroup.closure_le]
  rintro z rfl
  rw [rowWideMark_two]
  exact evenRouteAudit_sigFourY_sq_mem

end RowPoints

end GQ2.Dyadic.SqCore

/-! ## §4 Axiom pins

Every public declaration of this file.  §1's statements are field-level and print the endpoint
chain's committed set `S` = std-3 together with the four census axioms
`hilbertSymbol_normCriterion_finiteDyadic`, `tateDualityAt`,
`absGalQ2_isTopologicallyFinitelyGenerated` and `absGalQ2_localEulerCharacteristic`, which is
exactly what `evenRouteCarried_orientedEquivN` prints.  §2 and §3 are arithmetic-free and print
std-3 or a subset.  No new axiom, no `sorry`, no `native_decide`; every `decide` is on
`SqU5 (ZMod 8)`. -/

section AxiomPins

open GQ2.Dyadic.EvenRouteAudit
open GQ2.Dyadic.SqCore

-- §1 the corrected artefact
#print axioms evenRouteAudit_not_deepFlipN
#print axioms evenRouteAudit_not_deepFlipM
#print axioms evenRouteAudit_not_carriedDeepN
#print axioms evenRouteAudit_not_carriedDeepM
#print axioms evenRouteAudit_orientedEquivN_vacuous
#print axioms evenRouteAudit_orientedEquivM_vacuous
#print axioms evenRouteAudit_dichotomyN_forces_two
#print axioms evenRouteAudit_dichotomyM_forces_two

-- §2 the residual supply
#print axioms evenRouteAudit_residual_iff_actualDefect
#print axioms evenRouteAudit_residual_correction_nonempty
#print axioms evenRouteAudit_neutral_digit_sharp
#print axioms evenRouteAudit_neutral_meets_refined_digit
#print axioms evenRouteAudit_dbar_slotZero_sq
#print axioms evenRouteAudit_residual_digit_necessary
#print axioms evenRouteAudit_residual_mem_zLayer
#print axioms evenRouteAudit_residual_digit_automatic

-- §3 the class-four `γ₂` scope
#print axioms evenRouteAudit_sigFourY_sq_mem
#print axioms evenRouteAudit_rowFour_gaTwoIm_le
#print axioms evenRouteAudit_mirFour_gaTwoIm_le
#print axioms evenRouteAudit_dblFour_gaTwoIm_le
#print axioms evenRouteAudit_rowWide_gaTwoIm_le

end AxiomPins

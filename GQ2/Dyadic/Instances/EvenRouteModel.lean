/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenAlphaTwo
import GQ2.Dyadic.Instances.EvenRouteCarried
import GQ2.Dyadic.Instances.EvenSlotZero

/-!
# W57-MODEL: the even route's field models, re-cut onto the one surviving input

## The headline

The lane was sent to restore a non-vacuous `N`-branch field model at a branch depth `α ≥ 3`,
in the corrected wave-56 form `EvenRouteCarriedDeepN`.  **That form cannot carry a model, at
any field.**  §1 proves it, by composing two wave-56 lanes that never met in the import graph.
What the lane delivers instead is the model over the *live* input, at three fields, and §2 shows
that input costs strictly less than the campaign has been paying for it.

## §1: why the commissioned form is impossible

`EvenRouteCarried.lean` (W56-RECUT) published `EvenRouteCarriedDeep{N,M}`, whose second field is
the coordinate-`0` flip demand at the depths `α ≥ 3` the field's range identity produces.
`EvenSlotZero.lean` (W56-SLOTZERO) then refuted that demand **at every depth**, not only at
`α = 2` where wave 55 had stopped.  The two files are siblings: `EvenSlotZero.lean` imports
`StageAbstractionEvenFlip.lean` and so does `EvenRouteCarried.lean`, so neither sees the other and
no committed statement composes them.  Composed here, with the stage tuple supplied by wave 54's
own level-three base rather than assumed, they give

  `evenRouteModel_deep{N,M}_iff_depth_two` :
      at a field with a branch depth `α₀ ≥ 2` and even degree,
      `EvenRouteCarriedDeep{N,M} h K  ↔  α₀ = 2`.

So the corrected bundle is true exactly where wave 56 proved it *vacuous* and false everywhere
else.  A model in that form is therefore not merely hard to find: at a depth-`2` field it exists
and says nothing, and at a depth-`≥ 3` field it does not exist.  `evenRouteCarried_orientedEquiv
{N,M}_atDepth` have unsatisfiable hypothesis sets at every field, which is the same verdict
wave 56 delivered on the four *published* bundles, now delivered on the two corrected ones.

The same composition widens wave 56's retraction of the *published* bundles.  Wave 56 proved
`EvenRouteCarried{N,M}` false on the depth-`2` stratum, because that is where wave 55's
refutation reached; with W56-SLOTZERO in its place the argument runs at every depth, so
`evenRouteModel_not_carried{N,M}` say the wave-54 artefacts have no model at **any** even-degree
dyadic field carrying a branch identification.  The stratum qualifier can be deleted.

This is the third instance in three waves of the same defect, and it is worth naming: two lanes
of one wave landed in sibling modules, one of them refuting an input the other was publishing as
carried, and the wave closed without the composite being stated.

## §2: what is left, and what it costs

The live input is `EvenClimbResidualSupply`, onto which W56-ALPHA2 re-cut both endpoints.  That
lane stated the re-cut only on the `α = 2` stratum and paid for its stage base with the B5-K
axiom `markedRecipAt` and the ramified-`i` binder `κ ≠ 0`.  Neither is necessary.
`evenEndpoint_nStageBase` and `evenDeepIsotropy_mStageBase` build the level-three base at
**every** depth `α ≥ 2` from the range identity and the degree alone, so §2 states the endpoint
at every depth on both branches with

  * no marked reciprocity bundle, hence **no `markedRecipAt`**,
  * no ramification datum and no sign condition,
  * one hypothesis beyond the two arithmetic binders: `EvenClimbResidualSupply (α - 1)`.

That answers the audit question the wave-55 note raised about the models it built: the bundle
those models consumed "only as an axiom" is not consumed here at all.

## §3 and §4: the fields

Three models, at three fields, in the shape of §2.

* **`ℚ₂(√−2)`, `h = 0`, depth `2`**: the wave-55 `N` pilot, whose wave-55 model wave 56 made
  vacuous.  Restored: same field, live input, and the measured depth is now the *right* one for
  the statement rather than the wrong one.
* **`ℚ₂(√2)`, `h = 0`, depth `3`**: the `M` pilot.  §1 answers the lane's check question: the
  existing `M` model does **not** suffice in the corrected form, because at this field
  (depth `3`) the corrected `M` bundle is false, and so is the wave-54 input list its published
  model carries (`evenRouteModel_not_endpointMFlipOffTwo_sqrtTwo`).
* **`ℚ₂(β)` with `β⁴ + 4β² + 2 = 0`, `h = 1`, depth `3`**: new to the tree, and the field the
  lane was sent for: the wave-56 census's unique `N`-branch entry at depth `≥ 3`.  §3 constructs
  it, proves `[K : ℚ₂] = 4 = 2 + 2·1` from Eisenstein irreducibility, and proves that
  `β² + 2` is a square root of `2`, which is the field side of the wave-56 depth criterion
  `α ≥ 3 ↔ √2 ∈ K`.  No `N`-branch field of depth `≥ 3` can have smaller degree: `imChiN α` has
  index `2 ^ (α - 1) ≥ 4` in `ℤ₂ˣ`, that index is the degree of `K ∩ ℚ₂(μ_{2^∞})`, and that
  degree divides `[K : ℚ₂]`.  (Classical, not Lean; the census sees the same thing, having no
  `N`-branch quadratic above depth `2`.)

`β = ζ₁₆ − ζ₁₆⁻¹`, so `β² = √2 − 2` and `K` is the quartic subfield of `ℚ₂(ζ₁₆)` fixed by
`σ₇`; its range is `{u : u ≡ 1, 7 (mod 16)} = imChiN 3`.

`scripts/w57_model/quartic_model.m` certifies every claim about that field that Lean does not
prove, by the wave-56 census's own method and with its own cross-check
(`results/quartic_model.txt`, all assertions passed): `[K : ℚ₂] = 4` with `e = 4`, `f = 1`;
`i ∉ K` and `K(i)/K` ramified, so `K` is in class; `√2 ∈ K` and `(β² + 2)² = 2`;
`range χ mod 32 = {1, 7, 17, 23} = imChiN 3 mod 32`, and `≠ imChiN 2`, `≠ imChiN 4`; the
class-field-theory cross-check, that the unit parts of actual norms from `K` generate exactly
that subgroup; and uniqueness, that of Magma's 63 quartics exactly one is in class with branch
`N` and depth `≥ 3`, namely the census's degree-`4` entry `43`, and `X⁴ + 4X² + 2` has a root
in it.

## Proved / measured / carried

Per model, exactly.  **Proved in Lean**: the field itself, its degree, the parity binder
`finrank = 2 + 2h`, and at the quartic the criterion input `√2 ∈ K`; the level-three stage base;
the whole endpoint chain from the base and the residual supply.  **Measured** (Magma,
`scripts/w57_model/`, and wave 56's census): the branch identification `hrange`, which is local
class field theory at a named field and is not in the tree at any even degree; and, at the
quartic, that `i ∉ K` and `K(i)/K` is ramified, i.e. that the field is in the even route's class.
**Carried**: `EvenClimbResidualSupply (α − 1)`, the campaign's single decisive question.

**Axiomatic inputs: none beyond the ambient three and the committed census axioms already in the
endpoint chain.**  In particular no model here consumes `markedRecipAt` or `localReciprocity`,
which the wave-55 models did consume; §5 measures that.

## Numbering

1. the corrected wave-56 bundles hold exactly on the stratum where they are vacuous, and the
   published wave-54 bundles are false at every depth;
2. the endpoints at every depth, over the residual supply, with no bundle;
3. the quartic;
4. the three models;
5. the ledger and the axiom pins.
-/

namespace GQ2.Dyadic.EvenRouteModel

noncomputable section

open GQ2 ContCoh Polynomial IntermediateField
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
open GQ2.Dyadic.EvenRouteWitness
open GQ2.Dyadic.EvenRouteCarried
open GQ2.Dyadic.Fields

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The coefficient action at `G_K(2)`, as everywhere on this route. -/
local instance evenRouteModelScalar {K : IntermediateField ℚ_[2] ℚ̄₂} [CompactSpace (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] :
    DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

/-- Continuity of that action. -/
local instance evenRouteModelContinuousScalar {K : IntermediateField ℚ_[2] ℚ̄₂}
    [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-! ## §1 The corrected wave-56 bundles carry no model

W56-RECUT's guard was correct and is not in question: the bundles ask only at the depths a field
actually has.  What defeats them is that W56-SLOTZERO, landing four commits later in a sibling
module, refuted the guarded demand at every one of those depths.  The composite is below.

The stage tuple the refutation needs is not an assumption: `evenEndpoint_nStageBase` and
`evenDeepIsotropy_mStageBase` build one at level `3` from the range identity and the degree, at
every depth `α ≥ 2`.  On the `M` side the ramified-`i` binder is read off the identification by
`evenEndpoint_kappa_of_rangeM`. -/

section Refuted

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The corrected `N` flip demand is false at a field of branch depth `α ≥ 3`.**  W56-RECUT's
`EvenRouteDeepFlipN` against W56-SLOTZERO's `evenSlotZero_not_slotZeroSupply_N`, with the tuple
supplied by wave 54's level-three base. -/
theorem evenRouteModel_not_deepFlipN {alpha h : ℕ} (halpha : 3 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) : ¬ EvenRouteDeepFlipN h K := by
  obtain ⟨T⟩ := evenEndpoint_nStageBase (by omega) hev hrange
  exact fun H ↦ evenSlotZero_not_slotZeroSupply_N (by omega) (le_refl 3) hrange T
    (H alpha halpha hrange)

/-- **The corrected `M` flip demand is false at a field of branch depth `α ≥ 3`.** -/
theorem evenRouteModel_not_deepFlipM {alpha h : ℕ} (halpha : 3 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) : ¬ EvenRouteDeepFlipM h K := by
  obtain ⟨T⟩ := evenDeepIsotropy_mStageBase (by omega) hev
    (evenEndpoint_kappa_of_rangeM hrange) hrange
  exact fun H ↦ evenSlotZero_not_slotZeroSupply_M (by omega) (le_refl 3) hrange T
    (H alpha halpha hrange)

/-- **The corrected `N` bundle is FALSE at a field of branch depth `α ≥ 3`.**  So
`evenRouteCarried_orientedEquivN_atDepth` has an unsatisfiable hypothesis set wherever its
arithmetic binders hold. -/
theorem evenRouteModel_not_carriedDeepN {alpha h : ℕ} (halpha : 3 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) : ¬ EvenRouteCarriedDeepN h K :=
  fun C ↦ evenRouteModel_not_deepFlipN halpha hrange hev C.flip

/-- **The corrected `M` bundle is FALSE at a field of branch depth `α ≥ 3`.** -/
theorem evenRouteModel_not_carriedDeepM {alpha h : ℕ} (halpha : 3 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) : ¬ EvenRouteCarriedDeepM h K :=
  fun C ↦ evenRouteModel_not_deepFlipM halpha hrange hev C.flip

/-- **The corrected `N` bundle holds exactly on the stratum where it is vacuous.**  At a field
with an `N` branch depth `α₀ ≥ 2` and even degree, `EvenRouteCarriedDeepN h K` is equivalent to
`α₀ = 2`, where wave 56 proved it holds because the guard reaches no instance.  So the bundle is
never a non-vacuous carrier: it is either empty of content or false. -/
theorem evenRouteModel_deepN_iff_depth_two {alpha₀ h : ℕ} (halpha₀ : 2 ≤ alpha₀)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha₀)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    EvenRouteCarriedDeepN h K ↔ alpha₀ = 2 := by
  refine ⟨fun C ↦ ?_, fun h2 ↦ evenRouteCarried_deepN_of_two (h2 ▸ hrange)⟩
  by_contra hne
  exact evenRouteModel_not_carriedDeepN (alpha := alpha₀) (by omega) hrange hev C

/-- **The corrected `M` bundle holds exactly on the stratum where it is vacuous.** -/
theorem evenRouteModel_deepM_iff_depth_two {alpha₀ h : ℕ} (halpha₀ : 2 ≤ alpha₀)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha₀)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    EvenRouteCarriedDeepM h K ↔ alpha₀ = 2 := by
  refine ⟨fun C ↦ ?_, fun h2 ↦ evenRouteCarried_deepM_of_two (h2 ▸ hrange)⟩
  by_contra hne
  exact evenRouteModel_not_carriedDeepM (alpha := alpha₀) (by omega) hrange hev C

/-- **The wave-54 `M` input list is false at a depth-`3` field too.**  The lane's check question
for the published `M` model `evenRouteWitness_orientedEquivM_sqrtTwo`: its `Hflip` argument is
`EvenEndpointMFlipOffTwo`, and wave 56 refuted that only at depth `2`, which is not where the
`M` pilot sits.  It is false at the pilot's depth as well. -/
theorem evenRouteModel_not_endpointMFlipOffTwo {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    ¬ EvenEndpoint.EvenEndpointMFlipOffTwo h K := by
  obtain ⟨T⟩ := evenDeepIsotropy_mStageBase halpha hev (evenEndpoint_kappa_of_rangeM hrange) hrange
  exact fun H ↦ evenSlotZero_not_flipSupply_M halpha (le_refl 3) hrange T
    (evenEndpoint_mFlip_of_offTwo halpha (H alpha halpha))

/-- **The wave-54 `N` input list is false at every depth.**  The `N` twin, for the published
model `evenRouteWitness_orientedEquivN_sqrtNegTwo`. -/
theorem evenRouteModel_not_endpointNFlip {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) : ¬ EvenEndpoint.EvenEndpointNFlip h K := by
  obtain ⟨T⟩ := evenEndpoint_nStageBase halpha hev hrange
  exact fun H ↦ evenSlotZero_not_flipSupply_N halpha (le_refl 3) hrange T (H alpha halpha)

/-- **The published `N` bundle is false at *every* field on the route.**  Wave 56 proved
`evenRouteCarried_not_carriedN` on the depth-`2` stratum, using wave 55's depth-`2` refutation;
with W56-SLOTZERO's refutation in its place the same argument runs at every depth the range
identity produces.  So the wave-54 `N` artefact has no model at any even-degree dyadic field
carrying the `N` identification, not merely none at the depth-`2` ones. -/
theorem evenRouteModel_not_carriedN {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) : ¬ EvenEndpoint.EvenRouteCarriedN h K :=
  fun C ↦ evenRouteModel_not_endpointNFlip halpha hrange hev C.flip

/-- **The published `M` bundle is false at every field on the route.** -/
theorem evenRouteModel_not_carriedM {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) : ¬ EvenEndpoint.EvenRouteCarriedM h K :=
  fun C ↦ evenRouteModel_not_endpointMFlipOffTwo halpha hrange hev C.flip

end Refuted

/-! ## §2 The endpoints at every depth, over the residual supply

W56-ALPHA2 re-cut the two `α = 2` endpoints onto `EvenClimbResidualSupply 1` and proved that the
wave-55 refutation mechanism cannot reach it.  Its two package lemmas
(`evenAlphaTwo_forwardGeneratorData{N,M}_of_residual`) are already stated at every depth; only the
endpoints were restricted, because the stage base they used
(`evenPerK_stageBase{N,M}_two`) is an `α = 2` statement that costs a marked reciprocity bundle.

The at-depth bases cost neither.  `evenEndpoint_nStageBase` needs the range identity and the
degree; `evenDeepIsotropy_mStageBase` needs those and `κ ≠ 0`, which
`evenEndpoint_kappa_of_rangeM` reads off the identification.  So both endpoints hold at every
depth with **one** hypothesis beyond the two arithmetic binders. -/

section Live

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The even `N` endpoint at every branch depth, over the one live input.**  Compare
`evenAlphaTwo_orientedEquivN_two_of_residual`, which is this at `α = 2` with a marked reciprocity
bundle and the ramified-`i` binder additionally carried. -/
theorem evenRouteModel_orientedEquivN_atDepth {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hres : EvenClimbResidualSupply (alpha - 1)
      (nStageWord alpha h (Nat.le_of_succ_le halpha)) (vN alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) := by
  obtain ⟨base⟩ := evenEndpoint_nStageBase halpha hev hrange
  exact nonempty_orientedEquivN_evenDegree_of_forwardGeneratorData alpha h (by omega) hev
    (EvenDemushkin.evenDem_nModelDemushkin alpha h halpha)
    (EvenAlphaTwo.evenAlphaTwo_forwardGeneratorDataN_of_residual halpha hrange base Hres)

/-- **The even `M` endpoint at every branch depth, over the one live input.** -/
theorem evenRouteModel_orientedEquivM_atDepth {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hres : EvenClimbResidualSupply (alpha - 1)
      (mStageWord alpha h (Nat.le_of_succ_le halpha)) (vM alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) := by
  obtain ⟨base⟩ := evenDeepIsotropy_mStageBase halpha hev
    (evenEndpoint_kappa_of_rangeM hrange) hrange
  exact nonempty_orientedEquivM_evenDegree_of_forwardGeneratorData alpha h (by omega) hev
    (EvenDemushkin.evenDem_mModelDemushkin alpha h halpha)
    (EvenAlphaTwo.evenAlphaTwo_forwardGeneratorDataM_of_residual halpha hrange base Hres)

end Live

/-! ## §3 The quartic `ℚ₂(β)`, `β⁴ + 4β² + 2 = 0`

The wave-56 census found exactly one in-class field of branch `N` and depth `≥ 3` among the
degrees `1, 2, 3, 4, 6`: a totally ramified quartic, named there only by its position in Magma's
enumeration.  It is `ℚ₂(ζ₁₆ − ζ₁₆⁻¹)`: with `β = ζ₁₆ − ζ₁₆⁻¹` one has `β² = ζ₈ + ζ₈⁻¹ − 2 =
√2 − 2`, hence `(β² + 2)² = 2` and `β⁴ + 4β² + 2 = 0`.  That polynomial is Eisenstein at `2`, so
the field it defines has degree `4 = 2 + 2·1` and sits at handle count `h = 1`.

Nothing here needs the cyclotomic description: the construction is the Eisenstein quartic, the
degree is proved from it, and `√2 ∈ K` is proved as the identity `(β² + 2)² = 2`, which is the
field side of the wave-56 criterion `α ≥ 3 ↔ √2 ∈ K`.  The criterion's other side, the branch
identification itself, is measured in `scripts/w57_model/`. -/

section Quartic

/-- `X⁴ + 4X² + 2` over `ℤ₂`, where the Eisenstein test lives. -/
def evenRouteModelPolyZ : ℤ_[2][X] := X ^ 4 + C 4 * X ^ 2 + C 2

/-- `X⁴ + 4X² + 2` over `ℚ₂`, the minimal polynomial of `β`. -/
def evenRouteModelPoly : ℚ_[2][X] := X ^ 4 + C 4 * X ^ 2 + C 2

theorem evenRouteModelPolyZ_monic : evenRouteModelPolyZ.Monic := by
  unfold evenRouteModelPolyZ; monicity!

theorem evenRouteModelPolyZ_degree : evenRouteModelPolyZ.degree = 4 := by
  unfold evenRouteModelPolyZ; compute_degree!

theorem evenRouteModelPoly_monic : evenRouteModelPoly.Monic := by
  unfold evenRouteModelPoly; monicity!

theorem evenRouteModelPoly_natDegree : evenRouteModelPoly.natDegree = 4 := by
  unfold evenRouteModelPoly; compute_degree!

theorem evenRouteModelPoly_degree : evenRouteModelPoly.degree = 4 := by
  unfold evenRouteModelPoly; compute_degree!

/-- The maximal ideal of `ℤ₂`, in the form the Eisenstein criterion consumes. -/
theorem evenRouteModel_span_two_isPrime : (Ideal.span {(2 : ℤ_[2])}).IsPrime := by
  rw [Ideal.span_singleton_prime (by norm_num)]
  exact PadicInt.prime_p

/-- **The quartic is irreducible over `ℤ₂`**, by Eisenstein at `2`: the three lower coefficients
`0, 4, 0` are divisible by `2` and the constant term `2` is not divisible by `4`. -/
theorem evenRouteModelPolyZ_irreducible : Irreducible evenRouteModelPolyZ := by
  refine irreducible_of_eisenstein_criterion evenRouteModel_span_two_isPrime ?_ ?_
    (by rw [evenRouteModelPolyZ_degree]; norm_num) ?_ evenRouteModelPolyZ_monic.isPrimitive
  · rw [evenRouteModelPolyZ_monic.leadingCoeff, Ideal.mem_span_singleton]
    exact evenRouteWitness_not_two_dvd_one
  · intro n hn
    rw [evenRouteModelPolyZ_degree] at hn
    have hn' : n < 4 := by exact_mod_cast hn
    interval_cases n <;>
      simp [evenRouteModelPolyZ, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
        Ideal.mem_span_singleton]
    exact ⟨2, by norm_num⟩
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simp only [evenRouteModelPolyZ, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C]
    norm_num
    intro hdvd
    rw [show (4 : ℤ_[2]) = 2 * 2 by norm_num] at hdvd
    exact evenRouteWitness_not_two_dvd_one
      ((mul_dvd_mul_iff_left (a := (2 : ℤ_[2])) two_ne_zero).mp (by rw [mul_one]; exact hdvd))

theorem evenRouteModelPolyZ_map :
    evenRouteModelPolyZ.map (algebraMap ℤ_[2] ℚ_[2]) = evenRouteModelPoly := by
  simp only [evenRouteModelPolyZ, evenRouteModelPoly, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_mul, Polynomial.map_ofNat, map_ofNat]

/-- **The quartic is irreducible over `ℚ₂`.**  Gauss's lemma for the integrally closed `ℤ₂`
transports the Eisenstein irreducibility to the fraction field. -/
theorem evenRouteModelPoly_irreducible : Irreducible evenRouteModelPoly := by
  rw [← evenRouteModelPolyZ_map]
  exact (evenRouteModelPolyZ_monic.irreducible_iff_irreducible_map_fraction_map
    (K := ℚ_[2])).mp evenRouteModelPolyZ_irreducible

/-- **`β`**, a chosen root of `X⁴ + 4X² + 2` in `ℚ̄₂`.  Up to the four conjugates it is
`ζ₁₆ − ζ₁₆⁻¹`. -/
def evenRouteModelBeta : ℚ̄₂ :=
  Classical.choose (IsAlgClosed.exists_aeval_eq_zero ℚ̄₂ evenRouteModelPoly
    (by rw [evenRouteModelPoly_degree]; norm_num))

theorem evenRouteModel_aeval_beta : aeval evenRouteModelBeta evenRouteModelPoly = 0 :=
  Classical.choose_spec (IsAlgClosed.exists_aeval_eq_zero ℚ̄₂ evenRouteModelPoly
    (by rw [evenRouteModelPoly_degree]; norm_num))

theorem evenRouteModelBeta_isIntegral : IsIntegral ℚ_[2] evenRouteModelBeta :=
  ⟨evenRouteModelPoly, evenRouteModelPoly_monic, evenRouteModel_aeval_beta⟩

theorem evenRouteModel_minpoly_beta :
    minpoly ℚ_[2] evenRouteModelBeta = evenRouteModelPoly :=
  (minpoly.eq_of_irreducible_of_monic evenRouteModelPoly_irreducible evenRouteModel_aeval_beta
    evenRouteModelPoly_monic).symm

/-- **`K₃ = ℚ₂(β)`**, the `N`-branch model field: the unique in-class field of branch `N` and
branch depth `3` of degree at most six, and the smallest one there can be. -/
def KQuarticN : IntermediateField ℚ_[2] ℚ̄₂ := ℚ_[2]⟮evenRouteModelBeta⟯

instance : FiniteDimensional ℚ_[2] KQuarticN :=
  IntermediateField.adjoin.finiteDimensional evenRouteModelBeta_isIntegral

/-- **The degree binder, discharged.**  `[ℚ₂(β) : ℚ₂] = 4`, so `ℚ₂(β)` sits on the even route at
handle count `h = 1`. -/
theorem finrank_KQuarticN : Module.finrank ℚ_[2] KQuarticN = 4 := by
  rw [KQuarticN, IntermediateField.adjoin.finrank evenRouteModelBeta_isIntegral,
    evenRouteModel_minpoly_beta, evenRouteModelPoly_natDegree]

/-- **The even-degree binder in the shape the endpoints consume**, at `h = 1`. -/
theorem finrank_KQuarticN_even : Module.finrank ℚ_[2] KQuarticN = 2 + 2 * 1 := by
  rw [finrank_KQuarticN]

theorem evenRouteModelBeta_mem : evenRouteModelBeta ∈ KQuarticN :=
  IntermediateField.mem_adjoin_simple_self _ _

/-- **`√2 ∈ ℚ₂(β)`**, in the explicit form `(β² + 2)² = 2`.  This is the field side of the
wave-56 depth criterion `α ≥ 3 ↔ √2 ∈ K` (`evenAlphaTwo_three_le_iff` plus the arithmetic
translation), so the model field satisfies the criterion's necessary condition inside Lean rather
than by measurement. -/
theorem evenRouteModel_beta_sq_add_two_sq : (evenRouteModelBeta ^ 2 + 2) ^ 2 = 2 := by
  have h := evenRouteModel_aeval_beta
  simp only [evenRouteModelPoly, map_add, map_pow, aeval_X, map_mul, map_ofNat] at h
  linear_combination h

/-- **The square root of `2` produced above lies in `ℚ₂(β)`.** -/
theorem evenRouteModel_sqrtTwo_mem :
    ∃ s ∈ KQuarticN, s ^ 2 = 2 := by
  refine ⟨evenRouteModelBeta ^ 2 + 2, add_mem (pow_mem evenRouteModelBeta_mem 2) ?_,
    evenRouteModel_beta_sq_add_two_sq⟩
  exact_mod_cast (2 : KQuarticN).2

end Quartic

/-! ## §4 The three models

Each is §2's endpoint at a literal field, with the degree binder discharged and the branch
identification carried.  What each carries beyond `hrange` is exactly one supply.

The `hrange` binder is the honest residue and is the same residue the wave-55 models had.
(Superseded at wave 67: `EvenRangeModelFields.lean` now computes the range at the named
fields, `hrangeFinal_sqrtNegTwo` proving `imChiN 2` at `ℚ₂(√−2)` outright and
`hrangeFinal_sqrtTwo` proving `imChiM 3` at `ℚ₂(√2)` over a base reciprocity bundle; the
quartic stays measured, two named costs recorded there.)  Wave 56 measured it at the two
pilot fields, and `scripts/w57_model/` measures it at the quartic. -/

section Models

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **The `N` model at the quartic `ℚ₂(β)`, at branch depth `3` and handle count `1`.**  The
field the lane was sent for: the wave-56 census's unique `N`-branch entry of depth `≥ 3`.  Degree
and the level-three base are constructed; the branch identification is measured; the residual
supply is the campaign's live question, and is the only thing carried. -/
theorem evenRouteModel_orientedEquivN_quartic [T2Space (GalK KQuarticN)]
    (hrange : MonoidHom.range (chiCycKTwo (K := KQuarticN)).toMonoidHom = imChiN 3)
    (Hres : EvenClimbResidualSupply 2 (nStageWord 3 1 (by omega)) (vN 3)
      (maxProPQuotient 2 (GalK KQuarticN)) (chiCycKTwo (K := KQuarticN))) :
    Nonempty (OrientedContinuousMulEquiv (chiN 3 1) (chiCycKTwo (K := KQuarticN))) :=
  evenRouteModel_orientedEquivN_atDepth (by omega) hrange finrank_KQuarticN_even Hres

/-- **The `N` model at `ℚ₂(√−2)`, at branch depth `2` and handle count `0`.**  The wave-55 pilot,
whose wave-55 model wave 56 made vacuous by measuring its depth.  Restored over the live input:
the depth wave 56 measured is now the depth the statement is about. -/
theorem evenRouteModel_orientedEquivN_sqrtNegTwo [T2Space (GalK KSqrtNegTwo)]
    (hrange : MonoidHom.range (chiCycKTwo (K := KSqrtNegTwo)).toMonoidHom = imChiN 2)
    (Hres : EvenClimbResidualSupply 1 (nStageWord 2 0 (by omega)) (vN 2)
      (maxProPQuotient 2 (GalK KSqrtNegTwo)) (chiCycKTwo (K := KSqrtNegTwo))) :
    Nonempty (OrientedContinuousMulEquiv (chiN 2 0) (chiCycKTwo (K := KSqrtNegTwo))) :=
  evenRouteModel_orientedEquivN_atDepth (le_refl 2) hrange
    (by rw [finrank_KSqrtNegTwo]) Hres

/-- **The `M` model at `ℚ₂(√2)`, at branch depth `3` and handle count `0`.**  The lane's check
question, answered: the published `M` model does not suffice in any flip-carrying form, because
`evenRouteModel_not_endpointMFlipOffTwo` and `evenRouteModel_not_carriedDeepM` are both false at
this field's measured depth.  This is the `M` model over the live input instead. -/
theorem evenRouteModel_orientedEquivM_sqrtTwo [T2Space (GalK KSqrtTwo)]
    (hrange : MonoidHom.range (chiCycKTwo (K := KSqrtTwo)).toMonoidHom = imChiM 3)
    (Hres : EvenClimbResidualSupply 2 (mStageWord 3 0 (by omega)) (vM 3)
      (maxProPQuotient 2 (GalK KSqrtTwo)) (chiCycKTwo (K := KSqrtTwo))) :
    Nonempty (OrientedContinuousMulEquiv (chiM 3 0) (chiCycKTwo (K := KSqrtTwo))) :=
  evenRouteModel_orientedEquivM_atDepth (by omega) hrange (by rw [finrank_KSqrtTwo]) Hres

/-- **The published `N` model's input list is false at its own field**, given the depth wave 56
measured.  Stated at the pilot field so the retraction is on the page next to the replacement. -/
theorem evenRouteModel_not_endpointNFlip_sqrtNegTwo [T2Space (GalK KSqrtNegTwo)]
    (hrange : MonoidHom.range (chiCycKTwo (K := KSqrtNegTwo)).toMonoidHom = imChiN 2) :
    ¬ EvenEndpoint.EvenEndpointNFlip 0 KSqrtNegTwo :=
  evenRouteModel_not_endpointNFlip (le_refl 2) hrange (by rw [finrank_KSqrtNegTwo])

/-- **The published `M` model's input list is false at its own field.** -/
theorem evenRouteModel_not_endpointMFlipOffTwo_sqrtTwo [T2Space (GalK KSqrtTwo)]
    (hrange : MonoidHom.range (chiCycKTwo (K := KSqrtTwo)).toMonoidHom = imChiM 3) :
    ¬ EvenEndpoint.EvenEndpointMFlipOffTwo 0 KSqrtTwo :=
  evenRouteModel_not_endpointMFlipOffTwo (by omega) hrange (by rw [finrank_KSqrtTwo])

end Models

end

end GQ2.Dyadic.EvenRouteModel

/-! ## §5 The ledger, and the axiom pins

### The ledger, per model

| input | `ℚ₂(√−2)`, `N`, `α = 2` | `ℚ₂(√2)`, `M`, `α = 3` | `ℚ₂(β)`, `N`, `α = 3` |
| --- | --- | --- | --- |
| the field | constructed (`Fields.lean`) | constructed (`Fields.lean`) | **constructed here** |
| `[K : ℚ₂] = 2 + 2h` | proved | proved | **proved** (Eisenstein) |
| `√2 ∈ K` | false, and correctly so | not applicable | **proved** |
| level-three stage base | constructed | constructed | constructed |
| branch identification `hrange` | **measured** (w56 census) | **measured** (w56 census) | **measured** (`scripts/w57_model/`) |
| `i ∉ K`, `K(i)/K` ramified | proved in `Fields.lean` | proved in `Fields.lean` | **measured** |
| `EvenClimbResidualSupply (α−1)` | **carried** | **carried** | **carried** |
| marked reciprocity bundle | not consumed | not consumed | not consumed |

The last row is the wave-55 audit's open item.  Its own models supplied the `MarkedRecip` binder
from the B5-K axiom `markedRecipAt`, which the audit recorded as never constructed in the repo;
the same is true of `evenAlphaTwo_orientedEquiv{N,M}_two_of_residual`.  **No model in this file
consumes it**, because the at-depth stage bases do not need it.  That is an improvement on the
existing models and not an inheritance.

### The pins

Write `std-3` for `[propext, Classical.choice, Quot.sound]` and `S` for the seven-element set
the even endpoint chain prints,

  `[propext, Classical.choice, hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt,
   Quot.sound, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic]`.

**Measured**, at this tip, all 44 prints below: 23 print **std-3** (the twenty-one declarations
of §3 and the two coefficient-action instances), 19 print **`S`** (all of §1, §2 and §4, and the
two W56-ALPHA2 endpoints §2 generalises), and exactly two print anything else, namely the two wave-55
models, which print `S` together with `markedRecipAt` and `localReciprocity`.

So no model or refutation in this file adds an axiom, and the three models of §4 pin to a
**strict subset** of what the two wave-55 models they replace pin to.  That is the census form of
the ledger's last row, and it is why the wave-55 models are printed here beside them. -/

section AxiomPins

open GQ2.Dyadic.EvenRouteModel

-- the two coefficient-action instances
#print axioms evenRouteModelScalar
#print axioms evenRouteModelContinuousScalar

-- §1 the corrected wave-56 bundles carry no model
#print axioms evenRouteModel_not_deepFlipN
#print axioms evenRouteModel_not_deepFlipM
#print axioms evenRouteModel_not_carriedDeepN
#print axioms evenRouteModel_not_carriedDeepM
#print axioms evenRouteModel_deepN_iff_depth_two
#print axioms evenRouteModel_deepM_iff_depth_two
#print axioms evenRouteModel_not_endpointMFlipOffTwo
#print axioms evenRouteModel_not_endpointNFlip
#print axioms evenRouteModel_not_carriedN
#print axioms evenRouteModel_not_carriedM

-- §2 the endpoints at every depth, against the `α = 2` forms they generalise
#print axioms evenRouteModel_orientedEquivN_atDepth
#print axioms evenRouteModel_orientedEquivM_atDepth
#print axioms GQ2.Dyadic.EvenAlphaTwo.evenAlphaTwo_orientedEquivN_two_of_residual
#print axioms GQ2.Dyadic.EvenAlphaTwo.evenAlphaTwo_orientedEquivM_two_of_residual

-- §3 the quartic
#print axioms evenRouteModelPolyZ
#print axioms evenRouteModelPoly
#print axioms evenRouteModelPolyZ_monic
#print axioms evenRouteModelPolyZ_degree
#print axioms evenRouteModelPoly_monic
#print axioms evenRouteModelPoly_natDegree
#print axioms evenRouteModelPoly_degree
#print axioms evenRouteModel_span_two_isPrime
#print axioms evenRouteModelPolyZ_irreducible
#print axioms evenRouteModelPolyZ_map
#print axioms evenRouteModelPoly_irreducible
#print axioms evenRouteModelBeta
#print axioms evenRouteModel_aeval_beta
#print axioms evenRouteModelBeta_isIntegral
#print axioms evenRouteModel_minpoly_beta
#print axioms KQuarticN
#print axioms finrank_KQuarticN
#print axioms finrank_KQuarticN_even
#print axioms evenRouteModelBeta_mem
#print axioms evenRouteModel_beta_sq_add_two_sq
#print axioms evenRouteModel_sqrtTwo_mem

-- §4 the three models, against the two wave-55 models they replace
#print axioms evenRouteModel_orientedEquivN_quartic
#print axioms evenRouteModel_orientedEquivN_sqrtNegTwo
#print axioms evenRouteModel_orientedEquivM_sqrtTwo
#print axioms GQ2.Dyadic.EvenRouteWitness.evenRouteWitness_orientedEquivN_sqrtNegTwo
#print axioms GQ2.Dyadic.EvenRouteWitness.evenRouteWitness_orientedEquivM_sqrtTwo
#print axioms evenRouteModel_not_endpointNFlip_sqrtNegTwo
#print axioms evenRouteModel_not_endpointMFlipOffTwo_sqrtTwo

end AxiomPins

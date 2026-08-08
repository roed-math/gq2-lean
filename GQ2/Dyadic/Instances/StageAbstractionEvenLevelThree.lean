/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenFrattiniFrameM
import GQ2.Dyadic.Instances.StageAbstractionEvenFrattiniFrameN
import GQ2.Dyadic.Instances.StageAbstractionEvenTransgression
import GQ2.Dyadic.Instances.StageAbstractionEvenFinite

/-!
# W51-EV3C2E, part 2: the even level-three base

Ticket **EV-3e** of `docs/dyadic/ev4b-stage-abstraction.md` §4, at both even cores.  This file
contains no arithmetic and no linear algebra: it is the composition station where the two finite
supplies of EV-3c and EV-3d meet `Frame.toLevelThree`, mirroring the committed odd-degree
`oddDegree_sqCyclotomicStageTuple_levelThree_of_finiteRealization`
(`GammaLSylowPreimageFieldLabuteLevelThreeSeed.lean:194`), which is four lines for the same
reason.

## The composition

Per core, three inputs and one engine:

| input | supplied by |
|---|---|
| `Frame (v _ α) (maxProPQuotient 2 (GalK K)) chiCycKTwo` plus `IsCupAdapted` | EV-3c (`N`: `evenDegreeNCyclotomicFrattiniFrameSupply_holds`; `M`: `evenDegreeMCyclotomicFrattiniFrameSupply_holds`) |
| `Frame.LevelThreeRelation` from cup-adaptedness | EV-3d (`…LevelThreeRelationRealization_fieldCup`) |
| `IsTopologicallyFinGen`, `IsProP 2` of `G_K(2)` | committed (`maxProTwoGalK_isTopologicallyFinGen`, `isProP_maxProPQuotient`) |
| the engine | `StageGeneric.Frame.toLevelThree` |

The **Gram seam** between EV-3c and EV-3d closes definitionally: EV-3c's adapter `evenFrameGram`
was written in the shape of EV-3d's word-independent predicate `IsEvenGram`, so §1's witness is
`fun _ ↦ rfl`, and the **pairing seam** closes the same way, because `evenFramePairing` is by
definition the field cup form spelling EV-3d's endpoints are stated against
(`evenFramePairing_fieldCup`, a `rfl`).  Neither seam costs a hypothesis.

## The `α = 2` `M` case is *not* gated

EV-3c2 landed the `M` row for every `α ≥ 2`, the `α = 2` case through a second Witt refinement
rather than through the `ω`-scalar route (which is refutable there,
`evenDegreeM_no_omegaScalar_two`).  So the `M` side of this file has the same `α` range as the `N`
side, and the only asymmetry is one extra carried binder, the `α = 2` attainment seam
`EvenDegreeMModEightRowAttained`, which is free for `α ≥ 3`
(`evenDegreeM_rowAttained_of_ge`).

## Fit against the `EvenFinite` contracts, and the adapter

`StageAbstractionEvenFinite.lean`'s `EvenFiniteLevel{N,M}StageBaseSupply` are stated with **no**
binders beyond the field, its topology instances, `h`, and the degree equation: they assert
`Nonempty (Tuple …)` outright.  §2's endpoints, like the odd twin they mirror, carry five (`N`)
resp. six (`M`) further binders, so they do not literally *equal* the contracts, and §4's
adapters are what closes the gap: each carried binder is re-stated once, universally quantified
over the field, as a named `Prop`, and the adapter consumes those and produces the contract on
the nose.  Nothing is weakened in the process; the adapter is bookkeeping, and its hypotheses are
exactly the per-field binders with `∀ K` in front.

The quantified inputs, and who owns them:

* `EvenLevelThreeRecipSupply` — a `MarkedRecip` bundle per field.  The even lane never *uses* the
  bundle (both EV-3c supplies discharge with it unused, exactly as the odd supply's docstring
  predicts), but the supply statements carry it for shape parity with the odd twin, so the
  adapter must produce one.  A caller holding its own bundles supplies this without touching
  `markedRecipAt`, which is the whole point of carrying the binder rather than summoning it.
* `EvenLevelThreeRamifiedSupply` — the campaign's standing ramified-`i` binder in the form
  `κ ≠ 0`; `FieldDataEven.kappaK_eq_zero_iff` is the stated interface.
* `EvenLevelThree{N,M}FrameInputSupply α` — EV-4a's row-relative lift supply together with the
  EV-3c mod-eight orientation seams of the corresponding row.

## What is proved and what is owed

Proved: both level-three bases, both adapters, no `sorry`, no new axiom.  The four endpoints print
exactly the axiom set of the `N` and `M` frame supplies, which is the odd level-three base's set;
verified side by side in the campaign record.  Owed: the four `Prop`s above, none of which is an
admitted goal.
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2 ContCoh
open GQ2.Roe.Labute
open GQ2.Dyadic.LSquare
open GQ2.Dyadic.LSquare.FrattiniFrameSupply

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 The Gram seam

EV-3d's realization endpoints take an abstract `gram` with an `IsEvenGram` proof.  EV-3c's
adapter is one, definitionally. -/

/-- **The EV-3c adapter is an `IsEvenGram`.**  The promised one-line discharge: `evenFrameGram`
was defined as the right-hand side of `IsEvenGram`, which is itself the right-hand side of the
committed `IsCupCocycle.nRelWord_centLift_fib`.  Both even cores use this one witness, since they
share a Gram. -/
theorem evenLevelThree_isEvenGram (h : ℕ) :
    evenTransgression.IsEvenGram (h := h) (evenFrameGram h) := fun _ ↦ rfl

/-! ## §2 The two level-three bases

The statement shape is the even spelling of the odd
`oddDegree_sqCyclotomicStageTuple_levelThree_of_finiteRealization`: the same ambient binders, the
`MarkedRecip` bundle carried and unused, the degree hypothesis in the even lane's `2 + 2h`
spelling (so `h` is `([K:ℚ₂] − 2)/2`), and the conclusion `Nonempty (Tuple … 3)` at the committed
row table. -/

section EvenLevelThree

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance evenLevelThreeScalar : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance evenLevelThreeContinuousScalar :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- **The even level-three base at the `N` core.**  Every even-degree `K` carrying the
ramified-`i` binder, the `N`-row mod-eight orientation hypothesis, and EV-4a's row-relative lift
supply has a level-three stage tuple at the committed `N` row table.

The `MarkedRecip` bundle `B` is a binder, not an axiom; it is threaded to EV-3c's supply, which
carries it for parity with the odd twin and does not consume it. -/
theorem evenLevelThreeN_stageBase {α : ℕ} (hα : 2 ≤ α) {R : LocalReciprocity}
    (B : MarkedRecip R K) (h : ℕ)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (hkappa : cyclotomicModFourClassKTwo (K := K) ≠ 0)
    (himg : EvenDegreeNModEightImage (K := K) α)
    (hrow : RowExactLevelFibreLiftSupply (vN (h := h) α) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K))) :
    Nonempty (Tuple (nStageWord α h (Nat.le_of_succ_le hα)) (vN α)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) 3) := by
  obtain ⟨F, hcup⟩ :=
    evenDegreeNCyclotomicFrattiniFrameSupply_holds α K B h hα hdeg hkappa himg hrow
  exact ⟨F.toLevelThree
    (evenTransgression.nLevelThreeRelationRealization_fieldCup K hα
      (evenLevelThree_isEvenGram h) F hcup)
    (maxProTwoGalK_isTopologicallyFinGen K) isProP_maxProPQuotient⟩

/-- **The even level-three base at the `M` core.**  The `N` twin plus the one extra binder the
`M` row needs, `EvenDegreeMModEightRowAttained`, which is what makes the `α = 2` frame exist and
is free for `α ≥ 3`.  In particular the `M` side is proved on the same `α` range as the `N` side:
nothing is gated at `α = 2`. -/
theorem evenLevelThreeM_stageBase {α : ℕ} (hα : 2 ≤ α) {R : LocalReciprocity}
    (B : MarkedRecip R K) (h : ℕ)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (hkappa : cyclotomicModFourClassKTwo (K := K) ≠ 0)
    (himg : EvenDegreeMModEightImage (K := K) α)
    (hatt : EvenDegreeMModEightRowAttained (K := K) α)
    (hrow : RowExactLevelFibreLiftSupply (vM (h := h) α) (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K))) :
    Nonempty (Tuple (mStageWord α h (Nat.le_of_succ_le hα)) (vM α)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) 3) := by
  obtain ⟨F, hcup⟩ :=
    evenDegreeMCyclotomicFrattiniFrameSupply_holds α K B h hα hdeg hkappa himg hatt hrow
  exact ⟨F.toLevelThree
    (evenTransgression.mLevelThreeRelationRealization_fieldCup K hα
      (evenLevelThree_isEvenGram h) F hcup)
    (maxProTwoGalK_isTopologicallyFinGen K) isProP_maxProPQuotient⟩

/-! ## §3 The quantified inputs

Each carried binder of §2, once, with `∀ K` in front.  These are the adapter's price and the
whole of it; see the module docstring for who owns each. -/

/-- **A marked reciprocity bundle per field.**  Owned by the caller (or by B5-K).  The even lane
does not consume the bundle; it carries it so that consumers pass their own rather than summoning
`markedRecipAt`, which is what keeps the endpoints' axiom prints where they are. -/
def EvenLevelThreeRecipSupply : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
    ∃ R : LocalReciprocity, Nonempty (MarkedRecip R K)

/-- **The ramified-`i` binder per field**, in the form the frame construction uses.
`FieldDataEven.kappaK_eq_zero_iff` is the stated interface for deriving it from `K(i)/K`
ramified; that file records that nothing in `GQ2/Dyadic/` currently derives it. -/
def EvenLevelThreeRamifiedSupply : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
    cyclotomicModFourClassKTwo (K := K) ≠ 0

/-- **The `N`-row frame inputs per field**: EV-3c's mod-eight orientation seam and EV-4a's
row-relative exact lift supply. -/
def EvenLevelThreeNFrameInputSupply (α : ℕ) : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] (h : ℕ),
    Module.finrank ℚ_[2] K = 2 + 2 * h →
      EvenDegreeNModEightImage (K := K) α ∧
        RowExactLevelFibreLiftSupply (vN (h := h) α) (maxProPQuotient 2 (GalK K))
          (chiCycKTwo (K := K))

/-- **The `M`-row frame inputs per field**: the `N` twin's two, plus the `α = 2` attainment seam.
All three follow from the image identity `MonoidHom.range chiCycKTwo = MarkedCore.imChiM α`
together with EV-4a. -/
def EvenLevelThreeMFrameInputSupply (α : ℕ) : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] (h : ℕ),
    Module.finrank ℚ_[2] K = 2 + 2 * h →
      EvenDegreeMModEightImage (K := K) α ∧ EvenDegreeMModEightRowAttained (K := K) α ∧
        RowExactLevelFibreLiftSupply (vM (h := h) α) (maxProPQuotient 2 (GalK K))
          (chiCycKTwo (K := K))

/-! ## §4 The adapters into the `EvenFinite` contracts

The conclusions are the committed `EvenFiniteLevel{N,M}StageBaseSupply` on the nose, so
`StageAbstractionEvenFinite.lean`'s
`evenForwardGeneratorData{N,M}_supply_of_base_and_corrections` consume them directly, with only
EV-3f's correction supply and the fin-gen supply still to come.

The `1 ≤ α` proof argument of the contract is irrelevant (`Prop`), so a caller may instantiate at
its own proof term. -/

/-- **EV-3e's `N` deliverable**, in the shape `StageAbstractionEvenFinite.lean` consumes. -/
theorem evenLevelThreeN_finiteStageBaseSupply {α : ℕ} (hα : 2 ≤ α)
    (hrec : EvenLevelThreeRecipSupply) (hram : EvenLevelThreeRamifiedSupply)
    (hin : EvenLevelThreeNFrameInputSupply α) :
    EvenFiniteLevelNStageBaseSupply α (Nat.le_of_succ_le hα) := by
  intro K _ _ _ _ h hdeg
  obtain ⟨R, ⟨B⟩⟩ := hrec K
  obtain ⟨himg, hrow⟩ := hin K h hdeg
  exact evenLevelThreeN_stageBase hα B h hdeg (hram K) himg hrow

/-- **EV-3e's `M` deliverable**, in the shape `StageAbstractionEvenFinite.lean` consumes.  Same
`α` range as the `N` deliverable. -/
theorem evenLevelThreeM_finiteStageBaseSupply {α : ℕ} (hα : 2 ≤ α)
    (hrec : EvenLevelThreeRecipSupply) (hram : EvenLevelThreeRamifiedSupply)
    (hin : EvenLevelThreeMFrameInputSupply α) :
    EvenFiniteLevelMStageBaseSupply α (Nat.le_of_succ_le hα) := by
  intro K _ _ _ _ h hdeg
  obtain ⟨R, ⟨B⟩⟩ := hrec K
  obtain ⟨himg, hatt, hrow⟩ := hin K h hdeg
  exact evenLevelThreeM_stageBase hα B h hdeg (hram K) himg hatt hrow

end EvenLevelThree

end

end GQ2.Dyadic.StageGeneric

/-! ## §5 Axiom pins -/

#print axioms GQ2.Dyadic.StageGeneric.evenLevelThree_isEvenGram
#print axioms GQ2.Dyadic.StageGeneric.evenLevelThreeN_stageBase
#print axioms GQ2.Dyadic.StageGeneric.evenLevelThreeM_stageBase
#print axioms GQ2.Dyadic.StageGeneric.EvenLevelThreeRecipSupply
#print axioms GQ2.Dyadic.StageGeneric.EvenLevelThreeRamifiedSupply
#print axioms GQ2.Dyadic.StageGeneric.EvenLevelThreeNFrameInputSupply
#print axioms GQ2.Dyadic.StageGeneric.EvenLevelThreeMFrameInputSupply
#print axioms GQ2.Dyadic.StageGeneric.evenLevelThreeN_finiteStageBaseSupply
#print axioms GQ2.Dyadic.StageGeneric.evenLevelThreeM_finiteStageBaseSupply

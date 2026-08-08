/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenLevelThree
import GQ2.Dyadic.Instances.StageAbstractionEvenKernelAdapted
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteHilbertTail

/-!
# W51-EV3F2 §E: EV-3h, the even forward route assembled

Ticket **EV-3h** of `docs/dyadic/ev4b-stage-abstraction.md` §4, the board's final ticket.  It
composes the three even stations into the uniform forward-generator supplies and then into the
even oriented-equivalence endpoints:

* **EV-3e**, the level-three bases, through C2E's adapters
  `evenLevelThree{N,M}_finiteStageBaseSupply`;
* **EV-3f**, the stage climb, through `evenClimb_{n,m}CorrectionSupply`
  (`StageAbstractionEvenStageClimb.lean` §4);
* **EV-3g**, the finite-level layer, through
  `evenForwardGeneratorData{N,M}_supply_of_base_and_corrections`
  (`StageAbstractionEvenFinite.lean` §6);

and finally the committed `orientedEquiv{N,M}_of_supplies`.

## Where the finite-generation axiom enters

`EvenFiniteLevelGalKFinGenSupply` is discharged here, once, by the committed
`LSquare.maxProTwoGalK_isTopologicallyFinGen`.  §1 is therefore the single point at which this
route acquires `absGalQ2_isTopologicallyFinitelyGenerated`, exactly as the odd route does at
the same station.  Every station below §1 was deliberately kept arithmetic-free so that this
is visible in one place and in one place only.

## The named hypotheses that remain

None of the following is discharged here; each is a live ticket in another lane, and every
endpoint statement below carries them explicitly.

1. `hmodel : ∀ h, NModelDemushkin α h` (resp. `MModelDemushkin`) — **EV-1e**, the model-side
   Demushkin property of the presented even cores.  A different lane entirely.
2. `hrec : EvenLevelThreeRecipSupply` — the **Recip bundle** supply, a marked local
   reciprocity datum at every even-degree dyadic field.
3. `hram : EvenLevelThreeRamifiedSupply` — the ramification input of the level-three frame.
4. `hin : EvenLevelThreeNFrameInputSupply α` (resp. `M`) — the level-three frame inputs,
   which is where the **mod-8 image seam** lives; the `M` variant additionally carries the
   **attained** seam.
5. `Hrange` — the **EV-4a** identification of the image of `chiCycKTwo` in even degree, with
   `imChiN α` on the `N` branch and `imChiM α` on the `M` branch.
6. `Hres` — the **EV-3f residual supply**, the gap `StageAbstractionEvenStageClimb.lean` §1
   isolates and `StageAbstractionEvenKernelAdapted.lean` §3 reduces to two boundaries.

Items 1-4 are inputs the board always intended to remain named at this station; items 5 and 6
are this lane's own open boundaries.

## Numbering

1. the finite-generation supply, discharged;
2. the uniform forward-generator supplies, `N` and `M`;
3. the even oriented-equivalence endpoints.
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.Dyadic.EvenForward
open GQ2.Dyadic.MarkedCore

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 The finite-generation supply

The one arithmetic input of this file, discharged once.  Compare the odd route, which acquires
`absGalQ2_isTopologicallyFinitelyGenerated` at the same station and for the same reason. -/

/-- **Topological finite generation of `G_K(2)`, uniformly in `K`.**  This is the committed
`LSquare.maxProTwoGalK_isTopologicallyFinGen`, repackaged in the shape
`StageAbstractionEvenFinite.lean` §6 names. -/
theorem evenAssembly_finGenSupply : EvenFiniteLevelGalKFinGenSupply :=
  fun K _ _ _ _ ↦ LSquare.maxProTwoGalK_isTopologicallyFinGen K

/-! ## §2 The uniform forward-generator supplies

EV-3e + EV-3f + EV-3g, composed.  Both branches are one application of the finite-level
endpoint to the level-three base and the stage climb. -/

section Supplies

/-- **The even `N` forward-generator supply**, from the level-three base and the stage climb. -/
theorem evenAssembly_nForwardSupply {α : ℕ} (hα : 2 ≤ α)
    (hrec : EvenLevelThreeRecipSupply) (hram : EvenLevelThreeRamifiedSupply)
    (hin : EvenLevelThreeNFrameInputSupply α)
    (Hrange : ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
      [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
      MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN α)
    (Hres : ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
      [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] (h : ℕ),
      EvenClimbResidualSupply (α - 1) (nStageWord α h (Nat.le_of_succ_le hα)) (vN α)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    EvenDegreeGalKNForwardGeneratorSupply α :=
  evenForwardGeneratorDataN_supply_of_base_and_corrections α (Nat.le_of_succ_le hα)
    evenAssembly_finGenSupply
    (evenLevelThreeN_finiteStageBaseSupply hα hrec hram hin)
    (evenClimb_nCorrectionSupply hα (Nat.le_of_succ_le hα) Hrange Hres)

/-- **The even `M` forward-generator supply**, the same composition on the `M` branch. -/
theorem evenAssembly_mForwardSupply {α : ℕ} (hα : 2 ≤ α)
    (hrec : EvenLevelThreeRecipSupply) (hram : EvenLevelThreeRamifiedSupply)
    (hin : EvenLevelThreeMFrameInputSupply α)
    (Hrange : ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
      [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
      MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α)
    (Hres : ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
      [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] (h : ℕ),
      EvenClimbResidualSupply (α - 1) (mStageWord α h (Nat.le_of_succ_le hα)) (vM α)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    EvenDegreeGalKMForwardGeneratorSupply α :=
  evenForwardGeneratorDataM_supply_of_base_and_corrections α (Nat.le_of_succ_le hα)
    evenAssembly_finGenSupply
    (evenLevelThreeM_finiteStageBaseSupply hα hrec hram hin)
    (evenClimb_mCorrectionSupply hα (Nat.le_of_succ_le hα) Hrange Hres)

end Supplies

/-! ## §3 The even oriented-equivalence endpoints

The board's final statement on each branch: every even-degree dyadic field whose degree is
`2 + 2h` has its maximal pro-`2` Galois group oriented-isomorphic to the presented even core
of rank `h`.  Modulo, and only modulo, the six named hypotheses listed in the module
docstring. -/

section Endpoints

/-- **EV-3h on the `N` branch.**  Every even-degree dyadic field of degree `2 + 2h` is
`N`-classified, given the six named inputs.  See the module docstring for what each is and
which lane owns it. -/
theorem evenAssembly_orientedEquivN {α : ℕ} (hα : 2 ≤ α)
    (hmodel : ∀ h : ℕ, NModelDemushkin α h)
    (hrec : EvenLevelThreeRecipSupply) (hram : EvenLevelThreeRamifiedSupply)
    (hin : EvenLevelThreeNFrameInputSupply α)
    (Hrange : ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
      [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
      MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN α)
    (Hres : ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
      [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] (h : ℕ),
      EvenClimbResidualSupply (α - 1) (nStageWord α h (Nat.le_of_succ_le hα)) (vN α)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)))
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    Nonempty (OrientedContinuousMulEquiv (chiN α h) (chiCycKTwo (K := K))) :=
  orientedEquivN_of_supplies α (Nat.le_of_succ_le hα) hmodel
    (evenAssembly_nForwardSupply hα hrec hram hin Hrange Hres) K h hev

/-- **EV-3h on the `M` branch.**  The `M` frame input additionally carries the attained
seam. -/
theorem evenAssembly_orientedEquivM {α : ℕ} (hα : 2 ≤ α)
    (hmodel : ∀ h : ℕ, MModelDemushkin α h)
    (hrec : EvenLevelThreeRecipSupply) (hram : EvenLevelThreeRamifiedSupply)
    (hin : EvenLevelThreeMFrameInputSupply α)
    (Hrange : ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
      [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
      MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α)
    (Hres : ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
      [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] (h : ℕ),
      EvenClimbResidualSupply (α - 1) (mStageWord α h (Nat.le_of_succ_le hα)) (vM α)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)))
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    Nonempty (OrientedContinuousMulEquiv (chiM α h) (chiCycKTwo (K := K))) :=
  orientedEquivM_of_supplies α (Nat.le_of_succ_le hα) hmodel
    (evenAssembly_mForwardSupply hα hrec hram hin Hrange Hres) K h hev

end Endpoints

end

end GQ2.Dyadic.StageGeneric

/-! ## §4 Axiom pins

Every public declaration of this file, printed.  §1 and everything above it acquire the census
axioms of the committed finite-generation input; the prints are expected to match the odd
route's assembly at the same station exactly, and are compared side by side in the agent
report. -/

section AxiomPins

open GQ2.Dyadic.StageGeneric

-- §1 the finite-generation supply
#print axioms evenAssembly_finGenSupply

-- §2 the forward-generator supplies
#print axioms evenAssembly_nForwardSupply
#print axioms evenAssembly_mForwardSupply

-- §3 the oriented-equivalence endpoints
#print axioms evenAssembly_orientedEquivN
#print axioms evenAssembly_orientedEquivM

end AxiomPins

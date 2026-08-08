/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenSharpHandles
import GQ2.Dyadic.Instances.StageAbstractionEvenFinite

/-!
# W51-EV3F2 §C: the even stage climb, assembled

Ticket **EV-3f** of `docs/dyadic/ev4b-stage-abstraction.md` §4, assembly half, cut against
`docs/dyadic/w51-ev3f-seam.md` §2.  This is the even clone of the L template's
`GammaLSylowPreimageFieldLabuteVariableStageTwo.lean`, and it closes the chain onto the exact
interface `StageAbstractionEvenFinite.lean` §6 demands.

The chain, end to end:

```
  §A §4  a depth-s admissible correction exists          (unconditional)
  §A §7  it repairs to an actual-defect supply           iff its residual is a neutral shift
  §A §5  the literal shift word is the relator shift     (crux i, one word for N and M)
  §A §6  an actual-defect supply gives DefectReachable   (deep seam, crux ii)
  here   ==> Tuple.DefectReachable at every k >= 3, packaged as
             EvenFiniteLevelNCorrectionSupply / EvenFiniteLevelMCorrectionSupply
```

Three things are worth stating plainly about how this differs from the L template.

* **The endpoint is `Tuple.DefectReachable`, not the L endpoint.**  The L
  `VariableStageTwo.lean` concludes `SharpCyclotomicInflationPrimitiveResidualVanishing`,
  because the odd route reaches its classification through the transgression engine.  The even
  finite-level layer instead asks for `Tuple.DefectReachable` directly
  (`StageAbstractionEvenFinite.lean:859`), which is the committed predicate the deep
  correction layer was built to land in.  So the last step here is
  `EvenSharpActualDefectSupply.toDefectReachable`, not a transgression call.
* **`Function.Surjective chiCycKTwo` is gone.**  The L clone of the crux takes it as a
  hypothesis (`stageResidual_exists_primitiveVanishing_of_kernelAdaptedSupply`), and it is
  false in even degree.  Board crux (ii) replaces it with the deep row supply at `s = α - 1`,
  which §3 below discharges from the image identification on either branch.
* **The residual supply is the one open station.**  Everything between §A's criterion and the
  endpoint is one `Prop`, `EvenClimbResidualSupply`, isolated in §1.  §B identifies it with a
  membership in the even bracket span; discharging that membership is the derivation-family
  station (the L `KernelAdaptedSupply.lean`), which this run does not reach.

## Numbering

1. the residual supply, the single open station of the even climb;
2. the climb theorem, generic in the word datum;
3. discharging the deep row supply from the branch image identifications;
4. the two endpoints, packaged exactly as `StageAbstractionEvenFinite.lean` §6 demands.
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.Dyadic.EvenRowSupply
open GQ2.Dyadic.MarkedCore

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 The residual supply

The one station of the even climb this run does not discharge.  It says: for every level and
every stage, the residual of *some* (equivalently, by §A §7, of *any*) depth-`s` admissible
correction is the literal shift of a neutral correction.

By §A §7 this is exactly equivalent to `Nonempty (EvenSharpActualDefectSupply s T)`, so
nothing is lost by isolating it here; it is the even analogue of the span-membership
statement the L template proves in `KernelAdaptedSupply.lean` from a coordinate derivation
family, and §B rewrites it as membership in the even bracket span. -/

section ResidualSupply

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h : ℕ}

/-- **The residual supply.**  Uniformly over levels `k ≥ 3` and stages, the residual of a
depth-`s` admissible correction is reachable by a neutral correction. -/
def EvenClimbResidualSupply (s : ℕ) (W : StageWord (MarkedCore.coreRank h))
    (v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ) (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (chi : ContinuousMonoidHom G ℤ_[2]ˣ) : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ (T : Tuple W v G chi k) (Wc : DeepSharpAdmissibleCorrection s T),
    EvenSharpNeutralResidualReachable Wc

end ResidualSupply

/-! ## §2 The climb

Generic in the word datum, so that the `N` and `M` branches share it verbatim: by §A §5 the
only branch-dependent input, the crossed-derivation comparison, is already an interface. -/

section Climb

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h k s : ℕ}
variable {W : StageWord (MarkedCore.coreRank h)} {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}

/-- **The even stage climb.**  At every level `k ≥ 3` every stage has a reachable actual
defect, given the residual supply, the crossed-derivation comparison, and the depth-`s` row
supply.  The proof is the whole of §A in four lines: take any depth-`s` correction, repair it
by the criterion, and cash the repair through the deep seam. -/
theorem evenClimb_defectReachable (hk : 3 ≤ k) (T : Tuple W v G chi k)
    (Hres : EvenClimbResidualSupply s W v G chi)
    (Hshift : EvenSharpDbarShiftSupply W G k)
    (Hlift : EvenRowDeepFibreLiftSupply s v G chi) :
    Tuple.DefectReachable T := by
  obtain ⟨Wc⟩ := evenSharpDeepAdmissible_nonempty s T
  obtain ⟨S⟩ := (nonempty_evenSharpActualDefectSupply_iff_residual hk Wc).mpr (Hres k hk T Wc)
  exact S.toDefectReachable (by omega) Hshift Hlift

end Climb

/-! ## §3 The deep row supply from the branch image identifications

Board crux (ii), discharged.  `EvenRowDeepFibreLiftSupply (α - 1)` is unconditional on each
branch once the character's image is identified, which is the EV-4a interface: the two
committed sufficiency theorems `evenRow_deepSupply_imChiN` and
`evenRow_deepSupply_imChiM_of_two_le` both land at the *same* depth `α - 1` for every
`α ≥ 2`, which is the uniformity the orchestrator recorded.

The row-value side conditions are discharged here rather than carried, so the only hypothesis
left on each branch is the image identification itself. -/

section RowSupply

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ}

omit [IsTopologicalGroup G] in
/-- Every `vN α` row value is a character value once the image is `imChiN α`. -/
theorem evenClimb_vN_mem_range {α h : ℕ}
    (hrange : MonoidHom.range chi.toMonoidHom = imChiN α)
    (i : Fin (MarkedCore.coreRank h)) : vN α i ∈ Set.range chi := by
  refine evenIndex_cases (P := fun i ↦ vN α i ∈ Set.range chi) ?_ ?_ ?_ ?_ ?_ ?_ i
  · rw [vN_zero]; exact evenRow_one_mem_range
  · rw [vN_one]; exact evenRow_nUnit_mem_range_of_imChiN hrange
  · rw [vN_two]; exact evenRow_one_mem_range
  · rw [vN_three]; exact evenRow_one_mem_range
  · intro j; rw [vN_handleU]; exact evenRow_one_mem_range
  · intro j; rw [vN_handleV]; exact evenRow_one_mem_range

omit [IsTopologicalGroup G] in
/-- Every `vM α` row value is a character value once the image is `imChiM α`. -/
theorem evenClimb_vM_mem_range {α h : ℕ}
    (hrange : MonoidHom.range chi.toMonoidHom = imChiM α)
    (i : Fin (MarkedCore.coreRank h)) : vM α i ∈ Set.range chi := by
  refine evenIndex_cases (P := fun i ↦ vM α i ∈ Set.range chi) ?_ ?_ ?_ ?_ ?_ ?_ i
  · rw [vM_zero]; exact evenRow_one_mem_range
  · rw [vM_one]; exact evenRow_neg_one_mem_range_of_imChiM hrange
  · rw [vM_two]; exact evenRow_one_mem_range
  · rw [vM_three]; exact evenRow_mUnit_mem_range_of_imChiM hrange
  · intro j; rw [vM_handleU]; exact evenRow_one_mem_range
  · intro j; rw [vM_handleV]; exact evenRow_one_mem_range

/-- **Crux (ii) on the `N` branch**: the deep row supply at depth `α - 1`. -/
theorem evenClimb_deepRowSupply_n {α h : ℕ} (hα : 2 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiN α) :
    EvenRowDeepFibreLiftSupply (α - 1) (vN α (h := h)) G chi :=
  evenRow_deepSupply_imChiN hα hrange (evenClimb_vN_mem_range hrange)

/-- **Crux (ii) on the `M` branch**: the same depth, by the strengthened `M` sufficiency. -/
theorem evenClimb_deepRowSupply_m {α h : ℕ} (hα : 2 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiM α) :
    EvenRowDeepFibreLiftSupply (α - 1) (vM α (h := h)) G chi :=
  evenRow_deepSupply_imChiM_of_two_le hα hrange (evenClimb_vM_mem_range hrange)

end RowSupply

/-! ## §4 The endpoints

Packaged exactly as `StageAbstractionEvenFinite.lean` §6 demands, so that
`evenForwardGeneratorDataN_supply_of_base_and_corrections` and its `M` twin consume these with
no adapter.  Each carries exactly two named hypotheses:

* `Hrange`, the EV-4a-side identification of the image of `chiCycKTwo` in even degree, uniform
  in `K`.  This is the branch condition, and it is the *only* character input left: crux (ii)
  turns it into the deep row supply in §3.
* `Hres`, the residual supply of §1, the single station of the even climb this run leaves
  open.

Nothing else is assumed.  In particular `Function.Surjective chiCycKTwo`, which the L clone of
this station takes and which is false in even degree, does not appear. -/

section Endpoints

/-- **The even stage climb at the `N` core**, in the exact shape
`EvenFiniteLevelNCorrectionSupply` asks for. -/
theorem evenClimb_nCorrectionSupply {α : ℕ} (hα : 2 ≤ α) (hα₁ : 1 ≤ α)
    (Hrange : ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
      [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
      MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN α)
    (Hres : ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
      [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] (h : ℕ),
      EvenClimbResidualSupply (α - 1) (nStageWord α h hα₁) (vN α)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    EvenFiniteLevelNCorrectionSupply α hα₁ := by
  intro K _ _ _ _ h _hev k hk T
  exact evenClimb_defectReachable hk T (Hres K h) (evenSharpDbarShiftSupply_n hα hα₁ hk)
    (evenClimb_deepRowSupply_n hα (Hrange K))

/-- **The even stage climb at the `M` core**, the same theorem against the `M` word datum and
the `M` image identification. -/
theorem evenClimb_mCorrectionSupply {α : ℕ} (hα : 2 ≤ α) (hα₁ : 1 ≤ α)
    (Hrange : ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
      [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
      MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α)
    (Hres : ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
      [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] (h : ℕ),
      EvenClimbResidualSupply (α - 1) (mStageWord α h hα₁) (vM α)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    EvenFiniteLevelMCorrectionSupply α hα₁ := by
  intro K _ _ _ _ h _hev k hk T
  exact evenClimb_defectReachable hk T (Hres K h) (evenSharpDbarShiftSupply_m hα hα₁ hk)
    (evenClimb_deepRowSupply_m hα (Hrange K))

end Endpoints

end

end GQ2.Dyadic.StageGeneric

/-! ## §5 Axiom pins

Every public declaration of this file, printed.  All are expected at std-3,
`[propext, Classical.choice, Quot.sound]`.

Against the L template this is a *reduction*, and deliberately so.  The corresponding L file
`GammaLSylowPreimageFieldLabuteVariableStageTwo.lean` prints
`absGalQ2_isTopologicallyFinitelyGenerated` on three of its five pins and additionally
`dyadicOrientation` on `sqKernelAdaptedDefectSupply_bot`, because the L station discharges its
own base case and its own finite-generation input.  Here both are hypotheses of the finite
level layer (`EvenFiniteLevelGalKFinGenSupply`, `EvenFiniteLevelNStageBaseSupply`), so this
station stays arithmetic-free and the pins may not exceed std-3. -/

section AxiomPins

open GQ2.Dyadic.StageGeneric

-- §1 the residual supply
#print axioms EvenClimbResidualSupply

-- §2 the climb
#print axioms evenClimb_defectReachable

-- §3 the deep row supply, crux (ii)
#print axioms evenClimb_vN_mem_range
#print axioms evenClimb_vM_mem_range
#print axioms evenClimb_deepRowSupply_n
#print axioms evenClimb_deepRowSupply_m

-- §4 the endpoints
#print axioms evenClimb_nCorrectionSupply
#print axioms evenClimb_mCorrectionSupply

end AxiomPins

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.GammaLNuKummerIdentification
import GQ2.Dyadic.Instances.GammaLSylowPreimageRealizationBypass
import GQ2.Dyadic.Instances.OddDegreeFieldWitness

/-!
# The odd-degree `L`-row pro-2 block: `ν`-endpoint wiring and realization

The two files this one joins were written against each other but never composed:

* `GammaLNuKummerIdentification` discharges the cup residual `NuUrOmegaCupOne B`
  unconditionally in odd degree (`nuUrOmegaCupOne_of_odd`);
* `GammaLSylowPreimageRealizationBypass` turns the marked forward supply into the full L-row
  pro-2 block `MarkedCoreRealization (DSq h) (lNu h)` over the χ-free clearing binder alone
  (`markedCoreRealization_of_cupOne_of_presentation`), and its own docstring records the
  composition as "a one-line follow-up left to the next assembly pass".

This file is that pass, and it also removes the level binder: `B.r = 0` is not an input at odd
degree either, it is `MarkedRecip.level_eq_zero_of_odd_finrank` against any dyadic unit
filtration (`OddDegreeFieldWitness`).  What is left on the odd-degree L row is therefore

| input | status |
|---|---|
| `SqCupAdaptedFramePresentation K` | the stage lane's frame-tracking residual |
| `SqNuClearHypothesis ((n − 1) / 2)` | the χ-free clearing binder; a theorem at `h = 0` |

and nothing else: no `ν`-row, no cup datum, no level equation, no handle stratum.

At `[K : ℚ₂] = 1` the clearing binder is `sqNuClearHypothesis_zero`, so the block costs exactly
the frame residual (`markedCoreRealization_oddDegree_degreeOne`).
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Dyadic SqCore

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

section OddDegreeBlock

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **The `ν`-endpoint wiring.**  For every odd-degree `K` the marked forward supply costs only
the stage-lane frame residual: the cup datum is `nuUrOmegaCupOne_of_odd` and the level equation
`B.r = 0` is `level_eq_zero_of_odd_finrank`. -/
theorem sqMarkedForwardSupply_oddDegree (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (hpres : MarkedFrame.SqCupAdaptedFramePresentation K) :
    SqMarkedForwardSupply B ((Module.finrank ℚ_[2] K - 1) / 2) :=
  NuKummer.sqMarkedForwardSupply_of_presentation B hodd
    (B.level_eq_zero_of_odd_finrank FF hodd) hpres

/-- **The odd-degree L-row pro-2 block.**  Over the frame residual and the χ-free clearing
binder alone, every odd-degree `K` carries `MarkedCoreRealization (DSq h) (lNu h)` at its own
handle count `h = ([K : ℚ₂] − 1) / 2`. -/
theorem markedCoreRealization_oddDegree (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (hclear : SqNuClearHypothesis ((Module.finrank ℚ_[2] K - 1) / 2))
    (hpres : MarkedFrame.SqCupAdaptedFramePresentation K) :
    Nonempty (MarkedCoreRealization (K := K) (B := B)
      (DSq ((Module.finrank ℚ_[2] K - 1) / 2))
      (Instances.LSquareCore.lNu ((Module.finrank ℚ_[2] K - 1) / 2))) :=
  markedCoreRealization_of_cupOne_of_presentation B hodd
    (B.level_eq_zero_of_odd_finrank FF hodd) hclear
    (NuKummer.nuUrOmegaCupOne_of_odd B hodd (B.level_eq_zero_of_odd_finrank FF hodd)) hpres

omit [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] [CompactSpace AbsGalQ2]
  [TotallyDisconnectedSpace AbsGalQ2] in
/-- The handle count of a degree-one field is `0`. -/
theorem handleCount_eq_zero_of_finrank_eq_one (hdeg : Module.finrank ℚ_[2] K = 1) :
    (Module.finrank ℚ_[2] K - 1) / 2 = 0 := by
  rw [hdeg]

/-- **The `h = 0` instance, binder-free apart from the frame residual.**  At `[K : ℚ₂] = 1` the
χ-free clearing hypothesis is the theorem `sqNuClearHypothesis_zero`, so the rank-three pro-2
block is supplied by `SqCupAdaptedFramePresentation K` alone. -/
theorem markedCoreRealization_oddDegree_degreeOne (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) (hdeg : Module.finrank ℚ_[2] K = 1)
    (hpres : MarkedFrame.SqCupAdaptedFramePresentation K) :
    Nonempty (MarkedCoreRealization (K := K) (B := B) (DSq 0)
      (Instances.LSquareCore.lNu 0)) := by
  have h0 : (Module.finrank ℚ_[2] K - 1) / 2 = 0 := handleCount_eq_zero_of_finrank_eq_one hdeg
  have hodd : Odd (Module.finrank ℚ_[2] K) := by rw [hdeg]; exact odd_one
  have hblock := markedCoreRealization_oddDegree B FF hodd
    (by rw [h0]; exact sqNuClearHypothesis_zero) hpres
  rwa [h0] at hblock

end OddDegreeBlock

end

#print axioms GQ2.Dyadic.LSquare.sqMarkedForwardSupply_oddDegree
#print axioms GQ2.Dyadic.LSquare.markedCoreRealization_oddDegree
#print axioms GQ2.Dyadic.LSquare.markedCoreRealization_oddDegree_degreeOne

end GQ2.Dyadic.LSquare

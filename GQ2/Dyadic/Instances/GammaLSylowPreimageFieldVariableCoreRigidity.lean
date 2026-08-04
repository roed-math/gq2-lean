/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldRigidity
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldRealizationCore

/-!
# Forward rigidity and variable-rank GammaL Sylow cores

The corrected GammaL Tate route uses a square core whose handle count grows with the odd index
of the chosen Sylow preimage.  This file connects that variable-core architecture to the new
forward-only field presentation theorem.

The principal point is that forward generator data already gives the oriented odd-degree field
classification by Demushkin epimorphism rigidity.  Consequently the variable-core field route
does not need a reverse presentation, a separate abstract Labute classification, or even a
separate `demushkinQ = 2` premise at this seam.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.ContCoh

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## Uniform forward-presentation supplies -/

/-- A field-uniform supply of the literal improved forward generator table. -/
def OddDegreeGalKSqForwardGeneratorSupply : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
    Odd (Module.finrank ℚ_[2] K) →
      Nonempty (SqCyclotomicForwardGeneratorData
        ((Module.finrank ℚ_[2] K - 1) / 2) (chiCycKTwo (K := K)))

/-- The stronger oriented classification obtained directly from forward data.  Unlike the
historical Labute seam, no separate `demushkinQ = 2` premise is needed: the target is already a
local maximal pro-two Galois group, and rigidity uses its proved Demushkin rank. -/
def OddDegreeGalKSqOrientedForwardClassification : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
    Odd (Module.finrank ℚ_[2] K) →
      Nonempty (OrientedContinuousMulEquiv
        (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2))
        (chiCycKTwo (K := K)))

/-- Equal-rank Demushkin rigidity upgrades the supplied forward map without changing its
constructor rows or its cyclotomic orientation values. -/
theorem oddDegreeGalKSqOrientedForwardClassification_of_forwardGeneratorSupply
    (S : OddDegreeGalKSqForwardGeneratorSupply) :
    OddDegreeGalKSqOrientedForwardClassification := by
  intro K _ _ _ _ hodd
  exact nonempty_orientedEquiv_oddDegree_of_forwardGeneratorData hodd (S K hodd)

/-- Compatibility adapter for consumers still phrased through the older conditional Labute
classification interface. -/
theorem oddDegreeGalKSqOrientedLabuteClassification_of_forwardGeneratorSupply
    (S : OddDegreeGalKSqForwardGeneratorSupply) :
    OddDegreeGalKSqOrientedLabuteClassification := by
  intro K _ _ _ _ hodd _hq
  exact oddDegreeGalKSqOrientedForwardClassification_of_forwardGeneratorSupply S K hodd

/-! ## The direct variable-core field route -/

/-- A field identification and the forward-only classification give the variable square core
at the index predicted by Reidemeister--Schreier. -/
theorem gammaLOpenSubgroupVariableCorePresentation_of_fieldIdentification_forward
    {h q : ℕ} (U' : Subgroup (gamma h q : Type)) [CompactSpace U']
    (hodd : Odd U'.index) (F : GammaLOpenSubgroupFieldIdentification U')
    (hforward : OddDegreeGalKSqOrientedForwardClassification) :
    Nonempty (ContinuousMulEquiv
      (maxProPQuotient 2 U')
      (SqCore.DSq (gammaLOpenSubgroupHandleCount U'))) := by
  letI : FiniteDimensional ℚ_[2] F.K := F.finiteDimensional
  letI : CompactSpace (GalK F.K) := F.compactSpace
  letI : T2Space (GalK F.K) := F.t2Space
  letI : TotallyDisconnectedSpace (GalK F.K) := F.totallyDisconnectedSpace
  have hdegreeOdd : Odd (Module.finrank ℚ_[2] F.K) := by
    rw [F.degree_eq]
    exact hodd.mul ⟨h, by omega⟩
  obtain ⟨eField⟩ := hforward F.K hdegreeOdd
  have hhandle : (Module.finrank ℚ_[2] F.K - 1) / 2 =
      gammaLOpenSubgroupHandleCount U' := by
    rw [F.degree_eq, gammaLOpenSubgroupHandleCount]
    congr 2
    ring
  let eCarrier := eField.1.symm
  rw [hhandle] at eCarrier
  exact ⟨(maxProPQuotientCongr F.equivGalK).trans eCarrier⟩

/-- The field-identification supply and the forward presentation close the corrected
variable-core presentation uniformly over odd-index open subgroups. -/
theorem gammaLOddIndexOpenSubgroupVariableCorePresentationSupply_of_field_forward
    {h q : ℕ} (hfield : GammaLOddIndexOpenSubgroupFieldIdentificationSupply h q)
    (hforward : OddDegreeGalKSqOrientedForwardClassification) :
    GammaLOddIndexOpenSubgroupVariableCorePresentationSupply h q := by
  intro U' _ hUopen hodd
  obtain ⟨F⟩ := hfield U' hUopen hodd
  exact gammaLOpenSubgroupVariableCorePresentation_of_fieldIdentification_forward
    U' hodd F hforward

/-- Field-realization spelling of the preceding theorem.  The only presentation input is the
literal forward generator supply discharged by the corrected stage campaign. -/
theorem gammaLOddIndexOpenSubgroupVariableCorePresentationSupply_of_fieldRealization_forward
    {h q : ℕ} (R : GammaLFieldRealization h q)
    (S : OddDegreeGalKSqForwardGeneratorSupply) :
    GammaLOddIndexOpenSubgroupVariableCorePresentationSupply h q :=
  gammaLOddIndexOpenSubgroupVariableCorePresentationSupply_of_field_forward
    (gammaLOddIndexOpenSubgroupFieldIdentificationSupply_of_fieldRealization R)
    (oddDegreeGalKSqOrientedForwardClassification_of_forwardGeneratorSupply S)

#print axioms oddDegreeGalKSqOrientedForwardClassification_of_forwardGeneratorSupply
#print axioms gammaLOpenSubgroupVariableCorePresentation_of_fieldIdentification_forward
#print axioms gammaLOddIndexOpenSubgroupVariableCorePresentationSupply_of_fieldRealization_forward

end

end GQ2.Dyadic.LSquare

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.FieldBranchIdentification

/-!
# Field-facing tied even selectors

The original field-facing even selectors discard the canonical marking equality supplied by
`genAsm_branch_of_evenN_tied` and `genAsm_branch_of_evenM_tied`.  This module retains that
`HEq`, in exactly the form consumed by the corrected compact-N and compact-M tied residual
wrappers.
-/

namespace GQ2.Dyadic.Instances.FieldBranchIdentificationTied

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.FieldBranchId
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SelectedCoreLeavesRN

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  {Rec : LocalReciprocity}

/-- The field-facing even-N selector, retaining the canonical compact-N marking. -/
theorem fieldId_genAsmBranch_of_orientedN_tied (B : MarkedRecip Rec K) (alpha h : ℕ)
    (hdeg : Module.finrank ℚ_[2] K = (SelectedPresentation.N0 alpha h).degree)
    (e : OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K)))
    (hpair : IsUnit (Multiplicative.toAdd (nuUrKTwo B (e.1 (dnSigma alpha h)))) ∨
      IsUnit (Multiplicative.toAdd (nuUrKTwo B (e.1 (dnX2 alpha h))))) :
    ∃ G : GenAsmBranch K B, G.pres = .N0 alpha h ∧ HEq G.nuP (nNuZtwo alpha h) :=
  genAsm_branch_of_evenN_tied alpha h hdeg (nNuZtwo alpha h)
    (genCertNNuZtwo_surjective alpha h) (fieldId_ztwoIota_nNuZtwo alpha h) e hpair

/-- The field-facing even-M selector, retaining the canonical compact-M marking. -/
theorem fieldId_genAsmBranch_of_orientedM_tied (B : MarkedRecip Rec K) (alpha h : ℕ)
    (halpha : 2 ≤ alpha)
    (hdeg : Module.finrank ℚ_[2] K = (SelectedPresentation.M0 alpha h).degree)
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (hpivot : IsUnit (Multiplicative.toAdd (nuUrKTwo B (e.1 (dmC alpha h))))) :
    ∃ G : GenAsmBranch K B, G.pres = .M0 alpha h ∧
      HEq G.nuP (fieldId_mNuZtwo alpha h (by omega)) :=
  genAsm_branch_of_evenM_tied alpha h (by omega) hdeg
    (fieldId_mNuZtwo alpha h (by omega)) (fieldId_mNuZtwo_surjective alpha h (by omega))
    (fieldId_ztwoIota_mNuZtwo alpha h (by omega)) e (mMixHypothesis alpha h halpha) hpivot

#print axioms fieldId_genAsmBranch_of_orientedN_tied
#print axioms fieldId_genAsmBranch_of_orientedM_tied

end GQ2.Dyadic.Instances.FieldBranchIdentificationTied

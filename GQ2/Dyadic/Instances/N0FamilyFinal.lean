/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.N0GeneralLevelZero
import GQ2.Dyadic.Instances.WordPhaseCompactNGeneric

/-!
# Final compact-N family-selection wrappers

On a selected `N0` branch, validity supplies `2 <= alpha`, the selector's level equation supplies
`B.r = 0`, and its degree equation pins the displayed handle count to the field degree. An
oriented equivalence is therefore the only surviving mathematical premise of the general-handle
level-zero realization.

This module packages that realization as a tied `GenAsmBranch` at the canonical compact-N
marking, then applies the uniform compact-N corrected word certificate to produce
`GenAsmRowResidualRN`. No determinant, primitive-pair, or handle-normalization premise remains.
-/

namespace GQ2.Dyadic.Instances.N0FamilyFinal

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.Words
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.Instances.N0GeneralLevelZero
open GQ2.Dyadic.Instances.WordPhaseCompactNGeneric

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- A selected N0 branch and an oriented equivalence determine the tied field branch at the
canonical compact-N marking. -/
theorem n0GenAsmBranch_of_familySelection_tied
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .N0 alpha)
    (e : OrientedContinuousMulEquiv
      (chiN alpha (handleCount FP (.N0 alpha))) (chiCycKTwo (K := K))) :
    ∃ G : GenAsmBranch K B,
      G.pres = .N0 alpha (handleCount FP (.N0 alpha)) ∧
        HEq G.nuP (nNuZtwo alpha (handleCount FP (.N0 alpha))) := by
  have hvalid := S.valid
  rw [hbranch] at hvalid
  have hr : B.r = 0 := by
    have h := S.level_eq
    rw [hbranch] at h
    exact h.symm
  have hdeg : Module.finrank ℚ_[2] K =
      (SelectedPresentation.N0 alpha (handleCount FP (.N0 alpha))).degree := by
    have h := S.degree_eq_field
    rw [hbranch] at h
    exact h.symm
  obtain ⟨M⟩ := markedCoreRealizationN_of_level_zero_general B hvalid hr e
  exact ⟨{
    pres := .N0 alpha (handleCount FP (.N0 alpha))
    hdeg := hdeg
    nuP := nNuZtwo alpha (handleCount FP (.N0 alpha))
    hnuP := genCertNNuZtwo_surjective alpha (handleCount FP (.N0 alpha))
    realization := M }, rfl, HEq.rfl⟩

/-- The selected N0 branch acquires the uniform corrected compact-N row residual. -/
theorem n0RowResidualRN_of_familySelection
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .N0 alpha)
    (e : OrientedContinuousMulEquiv
      (chiN alpha (handleCount FP (.N0 alpha))) (chiCycKTwo (K := K))) :
    ∃ G : GenAsmBranch K B,
      G.pres = .N0 alpha (handleCount FP (.N0 alpha)) ∧
        Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  have hvalid := S.valid
  rw [hbranch] at hvalid
  obtain ⟨G, hp, hnu⟩ := n0GenAsmBranch_of_familySelection_tied B FF S hbranch e
  exact ⟨G, hp, wPcN_rowResidualRN_of_tied B G hvalid hp hnu⟩

#print axioms n0GenAsmBranch_of_familySelection_tied
#print axioms n0RowResidualRN_of_familySelection

end
end GQ2.Dyadic.Instances.N0FamilyFinal

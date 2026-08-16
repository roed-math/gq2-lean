/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcCertificateLevel
import GQ2.Dyadic.Instances.NpcFieldSelectorAudit
import GQ2.Dyadic.Instances.NpcCandidateFinal
import GQ2.Dyadic.Instances.NpcDeterminantFinal

/-!
# Final procyclic-N family-selection wrappers

The corrected family selector supplies the selected Npc display, degree, level, and eta
equation. `NpcCertificateLevel` converts those facts and an oriented equivalence into the
canonical field-side realization, retaining exactly the primitive-plane condition on the
transported `(sigma, x2)` coordinates.

This module first packages that realization as a tied `GenAsmBranch`. It then combines the tied
branch with the unconditional arbitrary-unit Npc determinant to produce the corrected
`GenAsmRowResidualRN`. The remaining `NpcPlanePrimitiveAtLevel` premise is explicit; no field
selector or primitive-plane theorem is asserted here.
-/

namespace GQ2.Dyadic.Instances.NpcFamilyFinal

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.Words GQ2.Dyadic.Words.Npc
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.Instances.NpcCert
open GQ2.Dyadic.Instances.NpcCertificateLevel
open GQ2.Dyadic.Instances.NpcFieldSelectorAudit
open GQ2.Dyadic.Instances.NpcCandidateFinal
open GQ2.Dyadic.Instances.NpcDeterminantFinal

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]

/-- The family selector, positive-level realization, and tied adapter compose without any
candidate-side input. -/
theorem npcGenAsmBranch_of_familySelection_tied
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Npc alpha r eta)
    (e : OrientedContinuousMulEquiv
      (chiN alpha (handleCount FP (.Npc alpha r eta))) (chiCycKTwo (K := K)))
    (hplane : NpcPlanePrimitiveAtLevel alpha r
      (handleCount FP (.Npc alpha r eta))
      (npcCert_transport (nuUrKTwo B).toMonoidHom e.1
        ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun))) :
    let d : NpcDisplayFor eta :=
      Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
    ∃ G : GenAsmBranch K B,
      G.pres = .Npc alpha r (handleCount FP (.Npc alpha r eta)) d.data ∧
        HEq G.nuP (npcNu alpha r (handleCount FP (.Npc alpha r eta)) eta) := by
  obtain ⟨M⟩ := npcMarkedCoreRealization_of_familySelection B FF S hbranch e hplane
  exact familyNpc_branch_of_realization_tied S hbranch M

/-- The selected Npc branch acquires its corrected row residual from the unconditional
arbitrary-unit determinant. -/
theorem npcRowResidualRN_of_familySelection
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Npc alpha r eta)
    (e : OrientedContinuousMulEquiv
      (chiN alpha (handleCount FP (.Npc alpha r eta))) (chiCycKTwo (K := K)))
    (hplane : NpcPlanePrimitiveAtLevel alpha r
      (handleCount FP (.Npc alpha r eta))
      (npcCert_transport (nuUrKTwo B).toMonoidHom e.1
        ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun))) :
    let d : NpcDisplayFor eta :=
      Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
    ∃ G : GenAsmBranch K B,
      G.pres = .Npc alpha r (handleCount FP (.Npc alpha r eta)) d.data ∧
        Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  let d : NpcDisplayFor eta :=
    Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
  have hvalid := S.valid
  rw [hbranch] at hvalid
  obtain ⟨G, hp, hnu⟩ := npcGenAsmBranch_of_familySelection_tied
    B FF S hbranch e hplane
  refine ⟨G, hp, ?_⟩
  exact npcRowResidualRN_of_tied_determinant B G d hvalid.1 hp hnu
    (npcAffineDeterminantCertificate alpha r
      (handleCount FP (.Npc alpha r eta)) (qOf K FF) d hvalid.1
      (qOf_ne_zero K FF) (even_qOf K FF))

#print axioms npcGenAsmBranch_of_familySelection_tied
#print axioms npcRowResidualRN_of_familySelection

end
end GQ2.Dyadic.Instances.NpcFamilyFinal

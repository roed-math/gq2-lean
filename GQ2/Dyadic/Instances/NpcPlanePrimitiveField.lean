/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcPlanePrimitive
import GQ2.Dyadic.Instances.NpcFamilyFinal

/-!
# Field-side positive-level Npc plane normalization

The marked reciprocity bundle attains `2^r` on the cyclotomic kernel.  After transport to an
oriented `DN` core, `NpcPlanePrimitive.exists_dnPlanePrimitive_of_level_exact` moves the resulting
primitive divided coordinate into the `(sigma,x2)` plane by a chi-preserving automorphism.

This removes the last `NpcPlanePrimitiveAtLevel` premise from the family-selected Npc lane.  The
four public endpoints respectively produce the adjusted oriented equivalence, the marked-core
realization, the tied general-assembly branch, and the corrected RN row residual.

No new axiom is introduced.  Every declaration has the standard axiom set
`[propext, Classical.choice, Quot.sound]`.
-/

namespace GQ2.Dyadic.Instances.NpcPlanePrimitiveField

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.NpcCert
open GQ2.Dyadic.Instances.NpcCertificateLevel
open GQ2.Dyadic.Instances.NpcPlanePrimitive
open GQ2.Dyadic.Instances.NpcFamilyFinal
open GQ2.Dyadic.Instances.NpcFieldSelectorAudit
open GQ2.Dyadic.SelectedCoreLeavesRN

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- Adjust an oriented field equivalence so its transported Npc plane row is primitive. -/
theorem exists_orientedEquiv_npcPlanePrimitive
    (B : MarkedRecip Rec K) {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (e : OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) :
    ∃ e' : OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K)),
      NpcPlanePrimitiveAtLevel alpha B.r h
        (npcCert_transport (nuUrKTwo B).toMonoidHom e'.1
          ((nuUrKTwo B).continuous_toFun.comp e'.1.continuous_toFun)) := by
  let nu' : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]) :=
    npcCert_transport (nuUrKTwo B).toMonoidHom e.1
      ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun)
  have hlev : NpcChiKerLevel alpha B.r h nu' :=
    npcChiKerLevel_of_level B rfl e
  obtain ⟨gbar, hgchi, hgnu⟩ := B.nu_ker_chi_ge 1
  obtain ⟨g, rfl⟩ := surjective_toAbK K gbar
  let x : (DN alpha h : Type) := e.1.symm (maxProPMk 2 (GalK K) g)
  have hxchi : chiN alpha h x = 1 := by
    have he : chiCycKTwo (K := K) (e.1 x) = chiN alpha h x := e.2 x
    rw [e.1.apply_symm_apply, chiCycKTwo_maxProPMk, ← chiCycKAb_toAbK] at he
    exact he.symm.trans hgchi
  have hxnu : toAdd (nu' x) = 2 ^ B.r := by
    change toAdd (nuUrKTwo B (e.1 (e.1.symm (maxProPMk 2 (GalK K) g)))) = _
    rw [e.1.apply_symm_apply, nuUrKTwo_maxProPMk, hgnu, mul_one]
  obtain ⟨Psi, hchi, hplane⟩ :=
    exists_dnPlanePrimitive_of_level_exact halpha nu' hlev x hxchi hxnu
  let e' : OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K)) :=
    ⟨Psi.trans e.1, fun z => (e.2 (Psi z)).trans (hchi z)⟩
  refine ⟨e', ?_⟩
  change NpcPlanePrimitiveAtLevel alpha B.r h (nu'.comp (autHom Psi))
  exact hplane

/-- The family-selected Npc row has a marked-core realization with no residual plane premise. -/
theorem npcMarkedCoreRealization_of_familySelection_exactLevel
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Npc alpha r eta)
    (e : OrientedContinuousMulEquiv
      (chiN alpha (handleCount FP (.Npc alpha r eta))) (chiCycKTwo (K := K))) :
    Nonempty (MarkedCoreRealization (K := K) (B := B)
      (DN alpha (handleCount FP (.Npc alpha r eta)))
      (npcNu alpha r (handleCount FP (.Npc alpha r eta)) eta)) := by
  have hvalid := S.valid
  rw [hbranch] at hvalid
  obtain ⟨e', hplane⟩ := exists_orientedEquiv_npcPlanePrimitive B hvalid.1 e
  have hr : B.r = r := by
    have hlevel := S.level_eq
    rw [hbranch] at hlevel
    exact hlevel.symm
  rw [hr] at hplane
  exact NpcCertificateLevel.npcMarkedCoreRealization_of_familySelection
    B FF S hbranch e' hplane

/-- Premise-free tied branch for the selected Npc row. -/
theorem npcGenAsmBranch_of_familySelection_tied_exactLevel
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Npc alpha r eta)
    (e : OrientedContinuousMulEquiv
      (chiN alpha (handleCount FP (.Npc alpha r eta))) (chiCycKTwo (K := K))) :
    let d : NpcDisplayFor eta :=
      Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
    ∃ G : GenAsmBranch K B,
      G.pres = .Npc alpha r (handleCount FP (.Npc alpha r eta)) d.data ∧
        HEq G.nuP (npcNu alpha r (handleCount FP (.Npc alpha r eta)) eta) := by
  obtain ⟨M⟩ := npcMarkedCoreRealization_of_familySelection_exactLevel
    B FF S hbranch e
  exact familyNpc_branch_of_realization_tied S hbranch M

/-- The selected Npc row has its corrected RN residual with no plane-coordinate premise. -/
theorem npcRowResidualRN_of_familySelection_exactLevel
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Npc alpha r eta)
    (e : OrientedContinuousMulEquiv
      (chiN alpha (handleCount FP (.Npc alpha r eta))) (chiCycKTwo (K := K))) :
    let d : NpcDisplayFor eta :=
      Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
    ∃ G : GenAsmBranch K B,
      G.pres = .Npc alpha r (handleCount FP (.Npc alpha r eta)) d.data ∧
        Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  have hvalid := S.valid
  rw [hbranch] at hvalid
  obtain ⟨e', hplane⟩ := exists_orientedEquiv_npcPlanePrimitive B hvalid.1 e
  have hr : B.r = r := by
    have hlevel := S.level_eq
    rw [hbranch] at hlevel
    exact hlevel.symm
  rw [hr] at hplane
  exact NpcFamilyFinal.npcRowResidualRN_of_familySelection
    B FF S hbranch e' hplane

#print axioms exists_orientedEquiv_npcPlanePrimitive
#print axioms npcMarkedCoreRealization_of_familySelection_exactLevel
#print axioms npcGenAsmBranch_of_familySelection_tied_exactLevel
#print axioms npcRowResidualRN_of_familySelection_exactLevel

end
end GQ2.Dyadic.Instances.NpcPlanePrimitiveField

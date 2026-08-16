/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.CertificateSupplyFamilyRN
import GQ2.Dyadic.GeneralAssembly

/-!
# The field-side tied Npc selector boundary

The corrected family selector and `SemanticSelectedCoreLeavesRN.ofNpc` determine the Npc
presentation, its canonical marking `npcNu`, the displayed `sigma`/wild normalization, and the
field degree.  This module records the exact remaining field-side boundary without claiming a
selector that has not been proved.

The missing datum is

```
MarkedCoreRealization (DN alpha h) (npcNu alpha r h eta)
```

and, substantively, its `nu_equiv` field.  The compact-N adapter
`MarkedCoreRealization.ofCertificateN` cannot supply it: that adapter requires identification
with `nuN`, whereas `npcNu` already differs from `nuN` at `dnX1`.  At positive level the existing
compact marked-matching route also cannot normalize the Npc `(sigma, x2)` row `(2^r, 0)` through
its primitive-pair premise.  Closing the field-side Npc endpoint therefore requires a genuine
positive-level Npc marked-core certificate, analogous to the procyclic-M certificate, followed
by an adapter to `MarkedCoreRealization`.

The two branch constructors below assume exactly that realization.  They add no surrogate
classification, orientation, or marked-data hypotheses.
-/

namespace GQ2.Dyadic.Instances.NpcFieldSelectorAudit

noncomputable section

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.Instances.NProcyclicCore

/-- The canonical Npc marking is onto: its displayed `sigma` maps to `ztwoOne`. -/
theorem npcNu_surjective (alpha r h : ℕ) (eta : ℤ_[2]ˣ) (d : NpcDisplayFor eta) :
    Function.Surjective (npcNu alpha r h eta) :=
  Instances.NuWitness.surjective_of_ztwoOne_mem_range _
    ⟨_, npcNu_sigma alpha r h eta d⟩

/-- The compact-N realization adapter cannot be reused at the Npc marking: its required
pointwise identification with `nuN` fails on `x₁`, where Npc has the unit `eta` and compact N
has zero. -/
theorem not_npcNu_matches_nuN (alpha r h : ℕ) (eta : ℤ_[2]ˣ) :
    ¬ (∀ x : (DN alpha h : Type),
      ztwoIota (npcNu alpha r h eta x) = nuN alpha h x) := by
  intro hmatch
  have hx := hmatch (dnX1 alpha h)
  change ztwoIota (ztwoIota.symm
    (npcNuPadic alpha r h eta (dnGen alpha h 1))) = nuN alpha h (dnX1 alpha h) at hx
  rw [ztwoIota.apply_symm_apply, npcNuPadic_gen_one, nuN_dnX1] at hx
  have hz : (eta : ℤ_[2]) = 0 := congrArg Multiplicative.toAdd hx
  exact eta.ne_zero hz

section Field

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  {B : MarkedRecip Rec K}

/-- Package the exact tied Npc branch once its field-side marked-core realization is supplied. -/
theorem genAsm_branch_of_Npc_realization_tied
    (alpha r h : ℕ) (eta : ℤ_[2]ˣ) (d : NpcDisplayFor eta)
    (hdeg : Module.finrank ℚ_[2] K =
      (SelectedPresentation.Npc alpha r h d.data).degree)
    (M : MarkedCoreRealization (K := K) (B := B) (DN alpha h)
      (npcNu alpha r h eta)) :
    ∃ G : GenAsmBranch K B,
      G.pres = .Npc alpha r h d.data ∧ HEq G.nuP (npcNu alpha r h eta) := by
  exact ⟨{ pres := .Npc alpha r h d.data
           hdeg := hdeg
           nuP := npcNu alpha r h eta
           hnuP := npcNu_surjective alpha r h eta d
           realization := M }, rfl, HEq.rfl⟩

/-- The corrected family selector supplies the degree and display of the tied package.  Its
exact remaining input is a realization at the selected Npc marking. -/
theorem familyNpc_branch_of_realization_tied
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)}
    {W : FamilyFieldBranchWitness FP Q}
    (S : FamilyFieldBranchSelection K FP Q W)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Npc alpha r eta)
    (M : MarkedCoreRealization (K := K) (B := B)
      (DN alpha (handleCount FP (.Npc alpha r eta)))
      (npcNu alpha r (handleCount FP (.Npc alpha r eta)) eta)) :
    let d : NpcDisplayFor eta :=
      Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
    ∃ G : GenAsmBranch K B,
      G.pres = .Npc alpha r (handleCount FP (.Npc alpha r eta)) d.data ∧
        HEq G.nuP (npcNu alpha r (handleCount FP (.Npc alpha r eta)) eta) := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      dsimp only
      apply genAsm_branch_of_Npc_realization_tied
      exact degree_field.symm
      exact M

end Field

#print axioms npcNu_surjective
#print axioms not_npcNu_matches_nuN
#print axioms genAsm_branch_of_Npc_realization_tied
#print axioms familyNpc_branch_of_realization_tied

end
end GQ2.Dyadic.Instances.NpcFieldSelectorAudit

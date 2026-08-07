/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.MpcRamifiedRow
import GQ2.Dyadic.Instances.MpcSelectedScalar

/-!
# The procyclic-`M` seam, with no residual binder

`MpcSelectedScalar` reduces the row's uniform residue to the single input
`RamifiedNormalPairingSeparates` (`MProcyclicExact.uniformPushedHsimp_of_ramified_wf`), and
`MpcRamifiedRow` supplies that input, for every display and every simple elementary coefficient
with `tau` fixed-point free, at `1 ≤ α`.  The seam's own validity field already carries `2 ≤ α`,
so nothing has to be threaded: the two producers below bind `hbranch` and `Even q` alone, exactly
as their procyclic-`N` counterparts do.

The end-to-end corrected-family handoffs for the row live here too, rather than beside their `L`
and `Npc` analogues in `CertificateSupplyFamilyRN`, because that file is upstream of
`MpcRamifiedRow` and so cannot name the producers below.  Their statements are otherwise exactly
the `Npc` ones: branch equation, `q ≠ 0`, `Even q`, and the leaves.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.Dyadic.Words.Mpc

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- **The procyclic-`M` Stokes residue at the semantic seam, unconditionally.**  The row's three
second-order inputs are all theorems now: `hpair` and `hsc` from `MpcSelectedScalar`, and `hsep`
from `MProcyclicExact.ramifiedNormalPairingSeparates`. -/
theorem SemanticSelectedHsimpRN.of_Mpc {FP : FieldParameters}
    {S : SemanticSelectionView FP} {q alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta) (hqe : Even q) :
    SemanticSelectedHsimpRN S q := by
  have hvalid := S.valid
  rw [hbranch] at hvalid
  change 2 ≤ alpha ∧ 1 ≤ r at hvalid
  obtain ⟨hα, -⟩ := hvalid
  exact .MpcUniform alpha r epsilon eta hbranch
    (MProcyclicExact.uniformPushedHsimp_of_ramified_wf hα hqe (hbranch ▸ S.display).wf
      (hbranch ▸ S.display).represents
      (MProcyclicExact.ramifiedNormalPairingSeparates (by omega)))

/-- **The field-level procyclic-`M` seam, unconditionally** — the `Npc`-shaped statement. -/
theorem SelectedHsimp.of_Mpc
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FieldBranchWitness FP Q}
    {S : FieldBranchSelection K FP Q W} {q alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta) (hqe : Even q) :
    SelectedHsimp S q := by
  have hvalid := S.valid
  rw [hbranch] at hvalid
  change 2 ≤ alpha ∧ 1 ≤ r at hvalid
  obtain ⟨hα, -⟩ := hvalid
  exact .MpcUniform alpha r epsilon eta hbranch
    (MProcyclicExact.uniformPushedHsimp_of_ramified_wf hα hqe (hbranch ▸ S.display).wf
      (hbranch ▸ S.display).represents
      (MProcyclicExact.ramifiedNormalPairingSeparates (by omega)))

/-! ## The end-to-end corrected-family handoffs for the row -/

/-- Action-image corrected-family handoff for the selected procyclic-`M` row.  Exactly as on the
`L` and `Npc` rows, this consumes **no** Stokes residue input: the branch equation and `Even q`
are enough, since `BranchData.Valid (.Mpc α r ε η)` supplies `2 ≤ α` and every one of the row's
second-order statements is a theorem.  So the selected-`Mpc` certificate needs only the
structural and analytic leaves. -/
noncomputable def wordCertificateRN_of_familyFieldSelection_actionImageMpc
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)} {W : FamilyFieldBranchWitness FP Q}
    (S : FamilyFieldBranchSelection K FP Q W) {q alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (L : SemanticSelectedWordLeavesRN
      (SemanticSelectionView.ofFamilyFieldBranchSelection S) q P hP nuP hq0 hqe) :
    WordCertificateRN S.semantic.degree q S.semantic.word P hP nuP
      (standardNumerics S.semantic.degree) :=
  wordCertificateRN_of_familyFieldSelection S
    (.of_Mpc hbranch hqe) hq0 hqe L

/-- End-to-end selector handoff on the procyclic-`M` row with the Stokes residue supplied
theorem-side: whenever the corrected selector picks `.Mpc α r ε η`, even `q` alone feeds the row's
uniform residue into the five-row assembler. -/
noncomputable def wordCertificateRN_of_familyFieldBranch_actionImageMpc
    {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
    [FiniteDimensional ℚ_[2] K] (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (W : FamilyFieldBranchWitness D.params (B.fieldMarkedPair FF)) {q alpha r : ℕ}
    {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : (selectFieldBranchFamily B FF D RI W).branch = .Mpc alpha r epsilon eta)
    (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (L : SemanticSelectedWordLeavesRN
      (SemanticSelectionView.ofFamilyFieldBranchSelection
        (selectFieldBranchFamily B FF D RI W)) q P hP nuP hq0 hqe) :
    WordCertificateRN
      (selectFieldBranchFamily B FF D RI W).semantic.degree q
      (selectFieldBranchFamily B FF D RI W).semantic.word P hP nuP
      (standardNumerics (selectFieldBranchFamily B FF D RI W).semantic.degree) :=
  wordCertificateRN_of_familyFieldSelection_actionImageMpc
    (selectFieldBranchFamily B FF D RI W) hbranch hq0 hqe L

end

end GQ2.Dyadic

/-! ## Axiom audit -/

section AxiomAudit

#print axioms GQ2.Dyadic.SemanticSelectedHsimpRN.of_Mpc
#print axioms GQ2.Dyadic.SelectedHsimp.of_Mpc
#print axioms GQ2.Dyadic.wordCertificateRN_of_familyFieldSelection_actionImageMpc
#print axioms GQ2.Dyadic.wordCertificateRN_of_familyFieldBranch_actionImageMpc

end AxiomAudit

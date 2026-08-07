/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.MpcRamifiedRow
import GQ2.Dyadic.Instances.MpcSelectedScalar

/-!
# The procyclic-`M` seam, with no residual binder

`MpcSelectedScalar` reduced the two seam producers `SemanticSelectedHsimpRN.of_Mpc_ramified` and
`SelectedHsimp.of_Mpc_ramified` to the single input `RamifiedNormalPairingSeparates`, and noted
that "the `Npc`-shaped statement with no residual binder at all is one `hsep` away".

`MpcRamifiedRow` supplies that `hsep`, for every display and every simple elementary coefficient
with `tau` fixed-point free, at `1 ≤ α`.  The seam's own validity field already carries `2 ≤ α`,
so nothing has to be threaded: the two producers below bind `hbranch` and `Even q` alone, exactly
as their procyclic-`N` counterparts do.
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
  exact SemanticSelectedHsimpRN.of_Mpc_ramified hbranch hqe
    (MProcyclicExact.ramifiedNormalPairingSeparates (by omega))

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
  exact SelectedHsimp.of_Mpc_ramified hbranch hqe
    (MProcyclicExact.ramifiedNormalPairingSeparates (by omega))

end

end GQ2.Dyadic

/-! ## Axiom audit -/

section AxiomAudit

#print axioms GQ2.Dyadic.SemanticSelectedHsimpRN.of_Mpc
#print axioms GQ2.Dyadic.SelectedHsimp.of_Mpc

end AxiomAudit

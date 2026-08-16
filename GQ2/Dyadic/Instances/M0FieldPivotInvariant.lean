/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.M0C0PivotAutomorphism
import GQ2.Dyadic.Instances.M0FamilyFinal

/-!
# The compact-M field pivot is intrinsic

W164 proves that a continuous automorphism preserving `chiM` cannot change the unitness of the
canonical C0 pivot.  This file applies that theorem to two oriented equivalences from the same
compact-M core to a dyadic field group.  Their ratio is a `chiM`-preserving automorphism, so the
transported unramified marking has unit C0 value for one equivalence exactly when it does for the
other.

`M0FieldPivotUnit` packages the resulting choice-independent field condition.  No existence
claim is made: proving this intrinsic condition, or replacing the pivot-based realization, is
the remaining selected-M0 field problem.
-/

namespace GQ2.Dyadic.Instances.M0FieldPivotInvariant

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.M0FamilyField
open GQ2.Dyadic.Instances.M0FamilyFinal
open GQ2.Dyadic.Instances.M0C0PivotAutomorphism

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- The compact-M pivot is independent of the chosen oriented equivalence. -/
theorem m0_pivot_isUnit_congr_oriented (B : MarkedRecip Rec K)
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (e₁ e₂ : OrientedContinuousMulEquiv
      (chiM alpha h) (chiCycKTwo (K := K))) :
    IsUnit (Multiplicative.toAdd (nuUrKTwo B (e₁.1 (dmC alpha h)))) ↔
      IsUnit (Multiplicative.toAdd (nuUrKTwo B (e₂.1 (dmC alpha h)))) := by
  let Ψ : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type) :=
    e₁.1.trans e₂.1.symm
  have hchi : ∀ x, chiM alpha h (Ψ x) = chiM alpha h x := by
    intro x
    calc
      chiM alpha h (Ψ x) = chiCycKTwo (K := K) (e₂.1 (Ψ x)) := (e₂.2 (Ψ x)).symm
      _ = chiCycKTwo (K := K) (e₁.1 x) := by
        rw [show e₂.1 (Ψ x) = e₁.1 x by
          change e₂.1 (e₂.1.symm (e₁.1 x)) = e₁.1 x
          exact e₂.1.apply_symm_apply (e₁.1 x)]
      _ = chiM alpha h x := e₁.2 x
  have hInv := isUnit_dmC_aut_iff halpha Ψ hchi (m0Transport B e₂)
  change IsUnit (Multiplicative.toAdd (nuUrKTwo B (e₂.1 (Ψ (dmC alpha h))))) ↔
    IsUnit (Multiplicative.toAdd (nuUrKTwo B (e₂.1 (dmC alpha h)))) at hInv
  simpa only [Ψ, ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.apply_symm_apply] using hInv

/-- The intrinsic field-side compact-M pivot condition.  The existential choice of oriented
equivalence is immaterial by `m0_pivot_isUnit_congr_oriented`. -/
def M0FieldPivotUnit (B : MarkedRecip Rec K) (alpha h : ℕ) : Prop :=
  ∃ e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)),
    IsUnit (Multiplicative.toAdd (nuUrKTwo B (e.1 (dmC alpha h))))

theorem m0FieldPivotUnit_iff (B : MarkedRecip Rec K)
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) :
    M0FieldPivotUnit B alpha h ↔
      IsUnit (Multiplicative.toAdd (nuUrKTwo B (e.1 (dmC alpha h)))) := by
  constructor
  · rintro ⟨e', he'⟩
    exact (m0_pivot_isUnit_congr_oriented B halpha e' e).mp he'
  · intro he
    exact ⟨e, he⟩

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The family-selected corrected residual from the single intrinsic pivot condition. -/
theorem m0RowResidualRN_of_familySelection_of_fieldPivot
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha)
    (hpivot : M0FieldPivotUnit B alpha (handleCount FP (.M0 alpha))) :
    ∃ G : GenAsmBranch K B,
      G.pres = .M0 alpha (handleCount FP (.M0 alpha)) ∧
        Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  obtain ⟨e, he⟩ := hpivot
  exact m0RowResidualRN_of_familySelection B FF S hbranch e he

#print axioms m0_pivot_isUnit_congr_oriented
#print axioms M0FieldPivotUnit
#print axioms m0FieldPivotUnit_iff
#print axioms m0RowResidualRN_of_familySelection_of_fieldPivot

end
end GQ2.Dyadic.Instances.M0FieldPivotInvariant

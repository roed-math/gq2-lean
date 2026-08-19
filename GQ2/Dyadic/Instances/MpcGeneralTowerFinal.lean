/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.MpcGeneralTowerBase

/-!
# The general Mpc tower and selected epsilon-true family

The marked finite-stage argument, parity reduction, uniform square propagation, and one
class-four Jacobi calculation prove the M6 pivot shift simultaneously for every degree and
handle count.  This is the general argument: no nilpotency class is singled out.

For a selected epsilon-true Mpc family, its exact `B` row and the uniform pivot shift produce
the exact `C` pivot.  The already-landed arbitrary-display determinant and realization then
give the corrected RN residual without a separate shift premise.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralTowerFinal

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcGeneralTowerBase

/-- Uniform M6 pivot shift in every degree and handle count. -/
theorem mpcPivShiftH_all (alpha h : ℕ) (halpha : 2 ≤ alpha) :
    MpcPivShiftH alpha h :=
  mpcPivShiftH_general alpha h halpha

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])}
  [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)]
  [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

omit [T2Space (GalK K)] in
/-- A selected epsilon-true Mpc family has its corrected RN residual in arbitrary degree and
handle count.  The only field-side input left is an oriented presentation equivalence. -/
theorem mpcRowResidualRN_of_familySelection_true
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r true eta)
    (horient : Nonempty (OrientedContinuousMulEquiv
      (chiM alpha (handleCount FP (.Mpc alpha r true eta)))
      (chiCycKTwo (K := K)))) :
    let d : MpcDisplayFor eta :=
      Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
    ∃ G : GenAsmBranch K B,
      G.pres = .Mpc alpha r true d.display
        (handleCount FP (.Mpc alpha r true eta)) ∧
      Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  have halpha : 2 ≤ alpha := by
    have hv := S.valid
    rw [hbranch] at hv
    exact hv.1
  exact mpcRowResidualRN_of_familySelection_true_of_shiftH
    B FF S hbranch horient
      (mpcPivShiftH_all alpha (handleCount FP (.Mpc alpha r true eta)) halpha)

#print axioms mpcPivShiftH_all
#print axioms mpcRowResidualRN_of_familySelection_true

end
end GQ2.Dyadic.Instances.MpcGeneralTowerFinal

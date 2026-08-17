/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcTrueFilteredPlacement
import GQ2.Dyadic.Instances.MpcMarkedUniform

/-!
# The selected epsilon-true rank-four Mpc residual

This module corrects the stale conclusion in `MpcTrueFilteredPlacement` that `MpcPivShift 2`
was still open.  That audit followed the historical reduction in `MpcOrbit`, but missed the
later unconditional theorem `MpcMk.mpcMk_pivShift` in `MpcMarkedUniform`.  The uniform marked
ladder has therefore already closed the odd-shear orbit seam.

Composing that shift with `mpcOddShearOrbit_of_shift` and the epsilon-true placement
equivalence constructs an adjusted rank-four oriented equivalence whose divided `C` digit is
one.  The filtered pivot criterion converts it to an exact level-`r` pivot, and the canonical
scaling consumer then supplies the corrected RN residual.

As on the epsilon-false branch, rank four remains an honest handle-count equation: the branch
tag does not determine the field degree.  The final consumer needs only nonemptiness of the
rank-four oriented-equivalence type, not a distinguished choice.
-/

namespace GQ2.Dyadic.Instances.MpcTrueRankFourResidual

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.Instances.MpcGeneralHandleCertificate
open GQ2.Dyadic.Instances.MpcGeneralHandleFamilyCanonical
open GQ2.Dyadic.Instances.MpcFieldPivotFiltered
open GQ2.Dyadic.Instances.MpcTrueFilteredPlacement

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  [T2Space (GalK K)] in
/-- The unconditional marked shift adjusts any base orientation to one with divided digit one
on an epsilon-true rank-four selection. -/
theorem mpc_familySelection_true_rankFour_exists_digit
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc 2 r true eta)
    (e : OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := K))) :
    ∃ hr : B.r = r, 1 ≤ r ∧
      ∃ e' : OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := K)),
        mpcFieldPivotDigit B hr e' = 1 := by
  obtain ⟨hr, hrpos, hplace⟩ :=
    mpc_familySelection_true_rankFour_exists_digit_iff B FF S hbranch
  refine ⟨hr, hrpos, ?_⟩
  apply (hplace e).mpr
  exact Or.inr (mpcOddShearOrbit_of_shift MpcMk.mpcMk_pivShift _)

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  [T2Space (GalK K)] in
/-- The adjusted orientation has the exact transported `C` pivot required by the Mpc
certificate. -/
theorem mpc_familySelection_true_rankFour_exists_exactPivot
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc 2 r true eta)
    (e : OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := K))) :
    ∃ _hr : B.r = r, 1 ≤ r ∧
      ∃ e' : OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := K)),
        ∃ gamma : ℤ_[2]ˣ,
          toAdd (transport (nuUrKTwo B).toMonoidHom e'.1
            ((nuUrKTwo B).continuous_toFun.comp e'.1.continuous_toFun) (dmC 2 0)) =
              (gamma : ℤ_[2]) * 2 ^ r := by
  obtain ⟨hr, hrpos, e', hdigit⟩ :=
    mpc_familySelection_true_rankFour_exists_digit B FF S hbranch e
  exact ⟨hr, hrpos, e', (mpcFieldExactPivot_iff_digit B hr e').mpr hdigit⟩

omit [T2Space (GalK K)] in
/-- A selected rank-four epsilon-true Mpc branch has a corrected RN residual.  The exact pivot
is produced by the unconditional marked odd shear rather than assumed. -/
theorem mpcRowResidualRN_of_familySelection_true_rankFour
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc 2 r true eta)
    (hhandle : handleCount FP (.Mpc 2 r true eta) = 0)
    (horient : Nonempty
      (OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := K)))) :
    let d : MpcDisplayFor eta :=
      Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
    ∃ G : GenAsmBranch K B,
      G.pres = .Mpc 2 r true d.display 0 ∧
      Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  obtain ⟨e⟩ := horient
  obtain ⟨_hr, _hrpos, e', hpivot⟩ :=
    mpc_familySelection_true_rankFour_exists_exactPivot B FF S hbranch e
  have hpivotFamily :
      ∃ e'' : OrientedContinuousMulEquiv
          (chiM 2 (handleCount FP (.Mpc 2 r true eta)))
          (chiCycKTwo (K := K)),
        ∃ gamma : ℤ_[2]ˣ,
          toAdd (transport (nuUrKTwo B).toMonoidHom e''.1
            ((nuUrKTwo B).continuous_toFun.comp e''.1.continuous_toFun)
              (dmC 2 (handleCount FP (.Mpc 2 r true eta)))) =
            (gamma : ℤ_[2]) * 2 ^ r := by
    rw [hhandle]
    exact ⟨e', hpivot⟩
  obtain ⟨e'', hpivot''⟩ := hpivotFamily
  simpa only [hhandle] using
    (mpcRowResidualRN_of_familySelection_canonicalScaling
      B FF S hbranch e'' hpivot'')

#print axioms mpc_familySelection_true_rankFour_exists_digit
#print axioms mpc_familySelection_true_rankFour_exists_exactPivot
#print axioms mpcRowResidualRN_of_familySelection_true_rankFour

end
end GQ2.Dyadic.Instances.MpcTrueRankFourResidual

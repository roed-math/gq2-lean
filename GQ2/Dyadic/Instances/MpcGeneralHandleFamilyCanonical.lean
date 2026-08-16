/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcGeneralHandleFamilyClosed
import GQ2.Dyadic.Instances.M0FieldPivotCup

/-!
# Canonical scaling at the selected procyclic-M endpoint

The general-h M scaling face is already a theorem: `mScalingHypothesis` constructs it from the
repository's canonical peripheral cyclotomic action.  Consequently the family-selected Mpc
endpoint does not need an explicit `MScalingHypothesis`; after the analytic certificate closes,
its only field-coordinate premise beyond the oriented equivalence is the exact transported `C`
pivot.

The mod-two cup used by the compact-M pivot does not characterize this exact positive-level
condition.  Indeed an Mpc pivot has value `unit * 2^r` with `r >= 1`, so its parity, and hence
the transported-`D`/unramified cup, is zero.  Detecting exact level `r` would require a filtered
or divided-kernel invariant rather than the existing mod-two cup form.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralHandleFamilyCanonical

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.Instances.M0FieldPivotCup
open GQ2.Dyadic.Instances.MpcGeneralHandleCertificate
open GQ2.Dyadic.Instances.MpcGeneralHandleFamilyClosed

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- At positive level, the exact Mpc pivot has trivial ordinary mod-two pivot cup.  Thus the
M0 cup criterion cannot distinguish exact Mpc level from deeper divisibility. -/
theorem mpcPivotCupValue_eq_zero_of_exactPivot (B : MarkedRecip Rec K)
    {alpha r h : ℕ} (halpha : 2 ≤ alpha) (hr : 1 ≤ r)
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (hpivot : ∃ gamma : ℤ_[2]ˣ,
      Multiplicative.toAdd (nuUrKTwo B (e.1 (dmC alpha h))) =
        (gamma : ℤ_[2]) * 2 ^ r) :
    m0PivotCupValue B e.1 = 0 := by
  obtain ⟨gamma, hgamma⟩ := hpivot
  rw [m0PivotCupValue_eq_parity B halpha e, hgamma,
    GQ2.Dyadic.MarkedCore.mParityZ_eq_zero_iff]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  refine ⟨(gamma : ℤ_[2]) * 2 ^ k, ?_⟩
  rw [pow_succ]
  ring

omit [T2Space (GalK K)] in
/-- The family-selected arbitrary-display Mpc residual with the globally constructed scaling
face discharged.  The exact transported `C` pivot remains explicit and honest. -/
theorem mpcRowResidualRN_of_familySelection_canonicalScaling
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta)
    (e : OrientedContinuousMulEquiv
      (chiM alpha (handleCount FP (.Mpc alpha r epsilon eta)))
      (chiCycKTwo (K := K)))
    (hpivot : ∃ gamma : ℤ_[2]ˣ,
      Multiplicative.toAdd (transport (nuUrKTwo B).toMonoidHom e.1
        ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun)
          (dmC alpha (handleCount FP (.Mpc alpha r epsilon eta)))) =
        (gamma : ℤ_[2]) * 2 ^ r) :
    let d : MpcDisplayFor eta :=
      Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
    ∃ G : GenAsmBranch K B,
      G.pres = .Mpc alpha r epsilon d.display
        (handleCount FP (.Mpc alpha r epsilon eta)) ∧
      Nonempty (GenAsmRowResidualRN (FF := FF) G) :=
  mpcRowResidualRN_of_familySelection_closed B FF S hbranch e
    (mScalingHypothesis alpha (handleCount FP (.Mpc alpha r epsilon eta))) hpivot

#print axioms mpcPivotCupValue_eq_zero_of_exactPivot
#print axioms mpcRowResidualRN_of_familySelection_canonicalScaling

end
end GQ2.Dyadic.Instances.MpcGeneralHandleFamilyCanonical

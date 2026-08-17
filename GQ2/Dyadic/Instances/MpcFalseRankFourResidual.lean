/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcFieldPivotDigitProducer

/-!
# The selected epsilon-false rank-four Mpc residual

An `epsilon = false` family selection forces the divided transported `C` digit to be one at
every rank-four oriented equivalence.  The filtered pivot criterion turns that digit into the
exact positive-level pivot required by the canonical-scaling Mpc consumer.  Thus no separate
pivot, scaling, level, residue, or display premise remains.

Rank four is recorded honestly by the equation `handleCount ... = 0`: the branch parameters
`alpha = 2` and `epsilon = false` do not determine the field degree or handle count.  The proof
packages the rank-four equivalence together with its exact pivot before transporting both across
that equation, avoiding any choice-dependent equality between oriented equivalences.
-/

namespace GQ2.Dyadic.Instances.MpcFalseRankFourResidual

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.Instances.MpcGeneralHandleCertificate
open GQ2.Dyadic.Instances.MpcGeneralHandleFamilyCanonical
open GQ2.Dyadic.Instances.MpcFieldPivotFiltered
open GQ2.Dyadic.Instances.MpcFieldPivotDigitProducer

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

omit [T2Space (GalK K)] in
/-- A selected rank-four `epsilon = false` Mpc branch has a corrected RN residual at every
oriented field equivalence, with the exact pivot supplied by its forced divided digit. -/
theorem mpcRowResidualRN_of_familySelection_false_rankFour
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc 2 r false eta)
    (hhandle : handleCount FP (.Mpc 2 r false eta) = 0)
    (e : OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := K))) :
    let d : MpcDisplayFor eta :=
      Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
    ∃ G : GenAsmBranch K B,
      G.pres = .Mpc 2 r false d.display 0 ∧
      Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  obtain ⟨hr, hall⟩ :=
    mpc_familySelection_false_rankFour_digit_all B FF S hbranch
  have hpivot := (mpcFieldExactPivot_iff_digit B hr e).mpr (hall e)
  have hpivotFamily :
      ∃ e' : OrientedContinuousMulEquiv
          (chiM 2 (handleCount FP (.Mpc 2 r false eta)))
          (chiCycKTwo (K := K)),
        ∃ gamma : ℤ_[2]ˣ,
          toAdd (transport (nuUrKTwo B).toMonoidHom e'.1
            ((nuUrKTwo B).continuous_toFun.comp e'.1.continuous_toFun)
              (dmC 2 (handleCount FP (.Mpc 2 r false eta)))) =
            (gamma : ℤ_[2]) * 2 ^ r := by
    rw [hhandle]
    exact ⟨e, hpivot⟩
  obtain ⟨e', hpivot'⟩ := hpivotFamily
  simpa only [hhandle] using
    (mpcRowResidualRN_of_familySelection_canonicalScaling
      B FF S hbranch e' hpivot')

#print axioms mpcRowResidualRN_of_familySelection_false_rankFour

end
end GQ2.Dyadic.Instances.MpcFalseRankFourResidual

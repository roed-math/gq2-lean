/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.Instances.WordPhase

/-!
# The compact phase normal form  (dyadic campaign, lane W87-NORMAL)

W86-PHASE reduced both compact rows' determinant clauses to a single branch-free statement,
`wPhBranchFreeSupply`, and then reduced that to one residual, `wPhCompactPhaseModel`: per
boundary lift, a `SourceWordPhaseComparison` against the even endpoint form.  Its §5 records
that none of the four `L`-side ingredients feeding the odd-degree comparison has a compact
counterpart anywhere in the tree.  This module works that residual, and instantiates the
one row whose acceptance statement W86-PHASE left unstated.

* **§1, the `ℚ₂(√2)` row.**  `M0 3 0`.  Every clause `RecordBlocks` and `WordPhase` prove is
  stated at general `(α, h, q)`, so the row is a transcription at `α = 3`, `h = 0` over the
  branch-free binder.

* **§2 onwards, the phase normal form.**  What `wPhCompactPhaseModel` needs, built where it can
  be built and named where it cannot.

Sections are added as the lane lands them; the axiom pins at the end carry the honest split.
-/

namespace GQ2.Dyadic.Instances.WordPhaseModel

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Instances
open GQ2.Dyadic.Instances.WordPhase

/-! ## §1 The `ℚ₂(√2)` row at the branch-free binder (ticket T1)

W86-PHASE §1's table records that the `M0 3 0` row "inherits every clause because W85-BLOCKS' §3
and §5 are stated at general `(α, h, q)`, but its acceptance statement was never instantiated".
This section instantiates it.  The only difference from the `ℚ₂(√5)` row is `α = 3` in place of
`α = 2`, which every clause consumes through `2 ≤ α`, plus the degree pin, which is
`finrank_KSqrtTwo` in place of `finrank_KSqrtFive`.  Both rows are `h = 0`, so both sit at the
same degree `2 * 0 + 2 = 2` and take **the same** `wPhBranchFreeSupply` shape.

| `M0 3 0` obligation | before this lane | after |
| --- | --- | --- |
| `cand` `exactLifting` at `Γ_R` | `askCStageVanishing` at `Γ_R` (`rowCl_mCand_exactLifting_iff`) | unchanged |
| `cand` `scalar` at `Γ_R` | discharged (`rowCl_mCand_scalar`) | discharged |
| `cand` `stokes` at `Γ_R` | proved at general `α` (`recBl_mCand_stokes`), never instantiated | instantiated |
| `cand` `determinant` at `Γ_R` | `wPhBranchFreeSupply`, never instantiated | instantiated |
| `ASK` `exactLifting` at `G_K` | `askCStageVanishing` at `G_K` | unchanged |
| `ASK` `stokes` at `G_K` | discharged | discharged |

So the `√2` row costs exactly what the other two compact rows cost: **one word-phase supply,
shared with them, and two instances of one coefficient `Prop`.** -/

section SqrtTwoRow

open GQ2.Dyadic.Instances.CanonicalRecords GQ2.Dyadic.FieldBranchId GQ2.Dyadic.Fields
open GQ2.Dyadic.Instances.MCompactCore
open GQ2.Dyadic.MCompact GQ2.Dyadic.Words.MCompact TameSpec MarkedCore

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] {R : LocalReciprocity}

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- `[ℚ₂(√2) : ℚ₂]` is the row's degree.  The `M0 3 0` twin of `rowCl_hdeg_sqrtFive`. -/
theorem wPm_hdeg_sqrtTwo :
    Module.finrank ℚ_[2] KSqrtTwo = (SelectedPresentation.M0 3 0).degree := by
  rw [finrank_KSqrtTwo]; rfl

/-- **The `ℚ₂(√2)` row's residual.**  Compare `canRec_rowResidual_sqrtTwo`, whose `cand` binder
is the whole `CAND` certificate: here the `stokes` and `scalar` clauses are gone outright, the
`exactLifting` clause is the coefficient `Prop`, and the `determinant` clause is W86-PHASE's
branch-free supply. -/
theorem wPm_rowResidual_sqrtTwo [T2Space (GalK KSqrtTwo)]
    (B : MarkedRecip R KSqrtTwo) {FF : DyadicUnitFiltration KSqrtTwo}
    (F : GenAsmFieldInputs KSqrtTwo B FF (SelectedPresentation.M0 3 0).degree)
    (Sdet : wPhBranchFreeSupply (2 * 0 + 2) (q := qOf KSqrtTwo FF)
      (fieldId_mNuZtwo 3 0 (by omega))
      (tameOfSpec (2 + 2 * 0) (qOf KSqrtTwo FF) (mCompactW 3 0)
        (mTameSpecializes 3 0 (qOf KSqrtTwo FF) (qOf_ne_zero KSqrtTwo FF)
          (even_qOf KSqrtTwo FF)))
      (mPro2 3 0 (qOf KSqrtTwo FF) (by omega) (qOf_ne_zero KSqrtTwo FF)
        (even_qOf KSqrtTwo FF))
      (mCompat 3 0 (qOf KSqrtTwo FF) (by omega) (qOf_ne_zero KSqrtTwo FF)
        (even_qOf KSqrtTwo FF)
        (mTameSpecializes 3 0 (qOf KSqrtTwo FF) (qOf_ne_zero KSqrtTwo FF)
          (even_qOf KSqrtTwo FF))
        (fieldId_mNuZtwo 3 0 (by omega)) (canRec_mNuZtwo_sigma 3 0 (by omega))
        (canRec_mNuZtwo_wild 3 0 (by omega))))
    (hvanCand : askCStageVanishing (GammaR (2 + 2 * 0) (qOf KSqrtTwo FF) (mCompactW 3 0))
      (qOf KSqrtTwo FF) (DM 3 0) (fieldId_mNuZtwo 3 0 (by omega)))
    (hvanK : askCStageVanishing (galKProfinite KSqrtTwo) (qOf KSqrtTwo FF)
      (genAsmCore (.M0 3 0)) (fieldId_mNuZtwo 3 0 (by omega))) :
    ∃ G : GenAsmBranch KSqrtTwo B, G.pres = .M0 3 0 ∧ Nonempty (GenAsmRowResidual G F.T) :=
  canRec_rowResidual_M0_of_analytic 3 0 (by omega) (canRec_branch_sqrtTwo B) F
    ((RowClauses.rowCl_mCand_exactLifting_iff (by omega) (qOf_ne_zero KSqrtTwo FF)
      (even_qOf KSqrtTwo FF)).mpr hvanCand)
    (RecordBlocks.recBl_mCand_stokes (by omega) (qOf_ne_zero KSqrtTwo FF)
      (even_qOf KSqrtTwo FF))
    (RowClauses.rowCl_mCand_scalar (by omega) (qOf_ne_zero KSqrtTwo FF)
      (even_qOf KSqrtTwo FF))
    (RecordBlocks.recBl_determinant_standard_congr (by omega)
      (RecordBlocks.recBl_mCand_determinant_of_wordPhaseSupply (by omega) _ _ _ _
        (wPh_recBlWordPhaseSupply_of_branchFree _ _ _ _ Sdet)))
    (askC_exactLiftingSemantics_galK wPm_hdeg_sqrtTwo hvanK)
    (askC_stokes_galK wPm_hdeg_sqrtTwo)

/-- **The acceptance statement at `ℚ₂(√2)`.**  The candidate group over the `M0 3 0` word at
`q_K` presents `G_{ℚ₂(√2)}`, given the branch-free word-phase supply and the coefficient `Prop`
at each of the row's two carriers.  The `α = 3` twin of
`wPh_candidate_equiv_galK_sqrtFive_branchFree`, at literally the same supply binder. -/
theorem wPm_candidate_equiv_galK_sqrtTwo_branchFree [T2Space (GalK KSqrtTwo)]
    (B : MarkedRecip R KSqrtTwo) {FF : DyadicUnitFiltration KSqrtTwo}
    (F : GenAsmFieldInputs KSqrtTwo B FF (SelectedPresentation.M0 3 0).degree)
    (Sdet : wPhBranchFreeSupply (2 * 0 + 2) (q := qOf KSqrtTwo FF)
      (fieldId_mNuZtwo 3 0 (by omega))
      (tameOfSpec (2 + 2 * 0) (qOf KSqrtTwo FF) (mCompactW 3 0)
        (mTameSpecializes 3 0 (qOf KSqrtTwo FF) (qOf_ne_zero KSqrtTwo FF)
          (even_qOf KSqrtTwo FF)))
      (mPro2 3 0 (qOf KSqrtTwo FF) (by omega) (qOf_ne_zero KSqrtTwo FF)
        (even_qOf KSqrtTwo FF))
      (mCompat 3 0 (qOf KSqrtTwo FF) (by omega) (qOf_ne_zero KSqrtTwo FF)
        (even_qOf KSqrtTwo FF)
        (mTameSpecializes 3 0 (qOf KSqrtTwo FF) (qOf_ne_zero KSqrtTwo FF)
          (even_qOf KSqrtTwo FF))
        (fieldId_mNuZtwo 3 0 (by omega)) (canRec_mNuZtwo_sigma 3 0 (by omega))
        (canRec_mNuZtwo_wild 3 0 (by omega))))
    (hvanCand : askCStageVanishing (GammaR (2 + 2 * 0) (qOf KSqrtTwo FF) (mCompactW 3 0))
      (qOf KSqrtTwo FF) (DM 3 0) (fieldId_mNuZtwo 3 0 (by omega)))
    (hvanK : askCStageVanishing (galKProfinite KSqrtTwo) (qOf KSqrtTwo FF)
      (genAsmCore (.M0 3 0)) (fieldId_mNuZtwo 3 0 (by omega))) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (SelectedPresentation.M0 3 0).degree (qOf KSqrtTwo FF)
        (SelectedPresentation.M0 3 0).word : ProfiniteGrp) : Type) (GalK KSqrtTwo)) :=
  RowClauses.rowCl_equiv_of_rowResidual F
    (wPm_rowResidual_sqrtTwo B F Sdet hvanCand hvanK)

end SqrtTwoRow

/-! ## Axiom audit

One `#print axioms` line per declaration, measured against the mirror. -/

section AxiomPins

#print axioms wPm_hdeg_sqrtTwo
#print axioms wPm_rowResidual_sqrtTwo
#print axioms wPm_candidate_equiv_galK_sqrtTwo_branchFree

end AxiomPins

end GQ2.Dyadic.Instances.WordPhaseModel

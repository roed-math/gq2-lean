/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.M0FamilyField
import GQ2.Dyadic.Instances.WordPhaseCompactMFinalBase
import GQ2.Dyadic.Instances.WordPhaseCompactMHandleBoundary

/-!
# Final arbitrary-h compact-M family endpoint

The arbitrary-h branch-free compact-M supply closes the affine determinant and corrected word
certificate with only the structural inputs `2 <= alpha`, `q != 0`, and `Even q`.

On a family-selected `M0` row, validity, degree, level, and the canonical tame-head data are
automatic. The field-side wrapper therefore retains exactly the oriented equivalence and the
canonical `C0`-pivot unit required by `M0FamilyField`; no determinant premise survives.
-/

namespace GQ2.Dyadic.Instances.M0FamilyFinal

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseCompactMFinalBase
open GQ2.Dyadic.Instances.WordPhaseCompactMHandleBoundary
open GQ2.Dyadic.Instances.M0FamilyField
open GQ2.Dyadic.Instances.CanonicalRecords
open GQ2.Dyadic.Instances.MCompactCore
open GQ2.Dyadic.FieldBranchId
open GQ2.Dyadic.MCompact GQ2.Dyadic.Words.MCompact
open TameSpec MarkedCore

/-- The unconditional arbitrary-h compact-M affine determinant certificate. -/
theorem wPcMAffineDeterminantCertificate_handles
    (alpha h q : ℕ) (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q) :
    AffineDeterminantCertificate
      (GammaR (2 + 2 * h) q (mCompactW alpha h)) (2 + 2 * h) q (DM alpha h)
      (fieldId_mNuZtwo alpha h (by omega)) (standardNumerics (2 + 2 * h))
      (tameOfSpec (2 + 2 * h) q (mCompactW alpha h)
        (mTameSpecializes alpha h q hq0 hqe))
      (mPro2 alpha h q (by omega) hq0 hqe)
      (mCompat alpha h q (by omega) hq0 hqe
        (mTameSpecializes alpha h q hq0 hqe)
        (fieldId_mNuZtwo alpha h (by omega))
        (canRec_mNuZtwo_sigma alpha h (by omega))
        (canRec_mNuZtwo_wild alpha h (by omega)))
      (scalarActionZmodTwo _) :=
  wPcM_affineDeterminantCertificate_of_supply halpha hq0 hqe
    (wPcM_branchFreeSupply_handles
      (fieldId_mNuZtwo alpha h (by omega))
      (tameOfSpec (2 + 2 * h) q (mCompactW alpha h)
        (mTameSpecializes alpha h q hq0 hqe))
      (mPro2 alpha h q (by omega) hq0 hqe)
      (mCompat alpha h q (by omega) hq0 hqe
        (mTameSpecializes alpha h q hq0 hqe)
        (fieldId_mNuZtwo alpha h (by omega))
        (canRec_mNuZtwo_sigma alpha h (by omega))
        (canRec_mNuZtwo_wild alpha h (by omega)))
      (TameSpec.tameOfSpec_gammaGen _ .sigma)
      (TameSpec.tameOfSpec_gammaGen _ .tau)
      (fun i ↦ TameSpec.tameOfSpec_gammaGen _ (.wild i)) halpha)

/-- The unconditional arbitrary-h corrected compact-M word certificate. -/
noncomputable def wPcMWordCertificateRN_handles
    (alpha h q : ℕ) (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q) :
    WordCertificateRN (2 + 2 * h) q (mCompactW alpha h) (DM alpha h)
      (isProP_DM alpha h) (fieldId_mNuZtwo alpha h (by omega))
      (standardNumerics (2 + 2 * h)) :=
  wPcMWordCertificateRN_of_supply alpha h q halpha hq0 hqe
    (wPcM_branchFreeSupply_handles
      (fieldId_mNuZtwo alpha h (by omega))
      (tameOfSpec (2 + 2 * h) q (mCompactW alpha h)
        (mTameSpecializes alpha h q hq0 hqe))
      (mPro2 alpha h q (by omega) hq0 hqe)
      (mCompat alpha h q (by omega) hq0 hqe
        (mTameSpecializes alpha h q hq0 hqe)
        (fieldId_mNuZtwo alpha h (by omega))
        (canRec_mNuZtwo_sigma alpha h (by omega))
        (canRec_mNuZtwo_wild alpha h (by omega)))
      (TameSpec.tameOfSpec_gammaGen _ .sigma)
      (TameSpec.tameOfSpec_gammaGen _ .tau)
      (fun i ↦ TameSpec.tameOfSpec_gammaGen _ (.wild i)) halpha)

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- A family-selected compact-M row acquires its corrected residual. The oriented equivalence
and canonical `C0`-pivot unit are exactly the field-realization premises. -/
theorem m0RowResidualRN_of_familySelection
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha)
    (e : OrientedContinuousMulEquiv
      (chiM alpha (handleCount FP (.M0 alpha))) (chiCycKTwo (K := K)))
    (hpivot : IsUnit (Multiplicative.toAdd
      (nuUrKTwo B (e.1 (dmC alpha (handleCount FP (.M0 alpha))))))) :
    ∃ G : GenAsmBranch K B,
      G.pres = .M0 alpha (handleCount FP (.M0 alpha)) ∧
        Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  have hvalid := S.valid
  rw [hbranch] at hvalid
  obtain ⟨G, hp, hnu⟩ :=
    m0GenAsmBranch_of_familySelection_tied B FF S hbranch e hpivot
  refine ⟨G, hp, ?_⟩
  exact wPcM_rowResidualRN_of_tied B G hvalid hp hnu
    (wPcM_branchFreeSupply_handles
      (fieldId_mNuZtwo alpha (handleCount FP (.M0 alpha))
        (le_trans (by omega) hvalid))
      (tameOfSpec (2 + 2 * handleCount FP (.M0 alpha)) (qOf K FF)
        (mCompactW alpha (handleCount FP (.M0 alpha)))
        (mTameSpecializes alpha (handleCount FP (.M0 alpha)) (qOf K FF)
          (qOf_ne_zero K FF) (even_qOf K FF)))
      (mPro2 alpha (handleCount FP (.M0 alpha)) (qOf K FF)
        (le_trans (by omega) hvalid) (qOf_ne_zero K FF) (even_qOf K FF))
      (mCompat alpha (handleCount FP (.M0 alpha)) (qOf K FF)
        (le_trans (by omega) hvalid) (qOf_ne_zero K FF) (even_qOf K FF)
        (mTameSpecializes alpha (handleCount FP (.M0 alpha)) (qOf K FF)
          (qOf_ne_zero K FF) (even_qOf K FF))
        (fieldId_mNuZtwo alpha (handleCount FP (.M0 alpha))
          (le_trans (by omega) hvalid))
        (canRec_mNuZtwo_sigma alpha (handleCount FP (.M0 alpha))
          (le_trans (by omega) hvalid))
        (canRec_mNuZtwo_wild alpha (handleCount FP (.M0 alpha))
          (le_trans (by omega) hvalid)))
      (TameSpec.tameOfSpec_gammaGen _ .sigma)
      (TameSpec.tameOfSpec_gammaGen _ .tau)
      (fun i ↦ TameSpec.tameOfSpec_gammaGen _ (.wild i)) hvalid)

#print axioms wPcMAffineDeterminantCertificate_handles
#print axioms wPcMWordCertificateRN_handles
#print axioms m0RowResidualRN_of_familySelection

end
end GQ2.Dyadic.Instances.M0FamilyFinal

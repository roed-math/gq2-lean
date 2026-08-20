import GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate
import GQ2.Dyadic.Instances.M0FamilyFinal

/-!
# Corrected compact-M certificates at flexible cores

The compact-M analytic proof is natural in the boundary maps.  Consequently it supplies the
complete corrected certificate at every presented pro-2 core whose marking has the normalized
sigma and wild rows; it is not tied to the canonical C-pivot realization.
-/

namespace GQ2.Dyadic.Instances.MCompactFlexibleCertificate

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words
open GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseCompactMHandleBoundary
open GQ2.Dyadic.Instances.MCompactCore
open GQ2.Dyadic.MCompact GQ2.Dyadic.Words.MCompact
open TameSpec MarkedCore

/-- The compact-M determinant at an arbitrary presented pro-2 core with normalized marking. -/
theorem wPcMAffineDeterminantCertificate_flexible
    {alpha h q : ℕ} (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (C : FlexibleCoreLeavesRN (2 + 2 * h) (mCompactW alpha h) P nuP) :
    AffineDeterminantCertificate
      (GammaR (2 + 2 * h) q (mCompactW alpha h)) (2 + 2 * h) q P nuP
      (standardNumerics (2 + 2 * h))
      (tameOfSpec (2 + 2 * h) q (mCompactW alpha h)
        (mTameSpecializes alpha h q hq0 hqe))
      (C.pro2 hq0 hqe)
      (C.compat hq0 hqe (mTameSpecializes alpha h q hq0 hqe))
      (scalarActionZmodTwo _) := by
  apply RecordBlocks.recBl_determinant_standard_congr
    (n := 2 * h + 2) (m := 2 + 2 * h) (by omega)
  apply RecordBlocks.recBl_mCand_determinant_of_wordPhaseSupply halpha
  apply wPh_recBlWordPhaseSupply_of_branchFree
  exact wPcM_branchFreeSupply_handles nuP
    (tameOfSpec (2 + 2 * h) q (mCompactW alpha h)
      (mTameSpecializes alpha h q hq0 hqe))
    (C.pro2 hq0 hqe)
    (C.compat hq0 hqe (mTameSpecializes alpha h q hq0 hqe))
    (TameSpec.tameOfSpec_gammaGen _ .sigma)
    (TameSpec.tameOfSpec_gammaGen _ .tau)
    (fun i ↦ TameSpec.tameOfSpec_gammaGen _ (.wild i)) halpha

/-- All non-routine compact-M certificate leaves at an arbitrary presented marked core. -/
noncomputable def mCompactFlexibleCertificateLeavesRN
    {alpha h q : ℕ} (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} (hP : IsProP 2 P) {nuP : ContinuousMonoidHom P Ztwo}
    (C : FlexibleCoreLeavesRN (2 + 2 * h) (mCompactW alpha h) P nuP) :
    FlexibleCertificateLeavesRN (2 + 2 * h) q (mCompactW alpha h) P hP nuP
      (standardNumerics (2 + 2 * h)) hq0 hqe where
  tameSpecialization := mTameSpecializes alpha h q hq0 hqe
  core := C
  exactLifting := RowClauses.rowCl_mCand_exactLiftingRN halpha hq0 hqe nuP
  stokes := RecordBlocks.recBl_mCand_stokes halpha hq0 hqe
  scalar := RowClauses.rowCl_mCand_scalar halpha hq0 hqe
  determinant := wPcMAffineDeterminantCertificate_flexible halpha hq0 hqe C

/-- A normalized presented compact-M core has a complete corrected certificate. -/
noncomputable def mCompactWordCertificateRN_flexible
    {alpha h q : ℕ} (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} (hP : IsProP 2 P) {nuP : ContinuousMonoidHom P Ztwo}
    (C : FlexibleCoreLeavesRN (2 + 2 * h) (mCompactW alpha h) P nuP) :
    WordCertificateRN (2 + 2 * h) q (mCompactW alpha h) P hP nuP
      (standardNumerics (2 + 2 * h)) :=
  wordCertificateRN_of_flexibleLeaves
    (mCompactFlexibleCertificateLeavesRN halpha hq0 hqe hP C)

#print axioms wPcMAffineDeterminantCertificate_flexible
#print axioms mCompactFlexibleCertificateLeavesRN
#print axioms mCompactWordCertificateRN_flexible

end

end GQ2.Dyadic.Instances.MCompactFlexibleCertificate

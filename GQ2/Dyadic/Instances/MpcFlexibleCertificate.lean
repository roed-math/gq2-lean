import GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate
import GQ2.Dyadic.Instances.MpcGeneralHandleFamilyClosed

/-!
# Corrected procyclic-M certificates at flexible cores

The arbitrary-display, arbitrary-h procyclic-M analysis is also natural in the boundary maps.
This module packages it at every normalized presented pro-2 core, without assuming the
canonical distinguished-C realization.
-/

namespace GQ2.Dyadic.Instances.MpcFlexibleCertificate

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate
open GQ2.Dyadic.Instances.MpcCandidateScalar
open GQ2.Dyadic.Instances.MpcCandidateStokes
open GQ2.Dyadic.Instances.MpcHandleDeterminant
open GQ2.Dyadic.MProcyclicExact
open TameSpec

/-- The displayed Mpc determinant at any normalized presented pro-2 core. -/
theorem mpcAffineDeterminantCertificate_flexible
    {alpha r h q : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta)
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (C : FlexibleCoreLeavesRN (2 + 2 * h)
      (mpcW alpha r (p epsilon r) d.display h) P nuP) :
    AffineDeterminantCertificate
      (GammaR (2 + 2 * h) q (mpcW alpha r (p epsilon r) d.display h))
      (2 + 2 * h) q P nuP (standardNumerics (2 + 2 * h))
      (tameOfSpec (2 + 2 * h) q (mpcW alpha r (p epsilon r) d.display h)
        (Count.tameSpecializes_mpcW hq0 hqe (by omega)
          r (p epsilon r) d.display h))
      (C.pro2 hq0 hqe)
      (C.compat hq0 hqe (Count.tameSpecializes_mpcW hq0 hqe (by omega)
        r (p epsilon r) d.display h))
      (scalarActionZmodTwo _) := by
  apply RecordBlocks.recBl_determinant_standard_congr
    (n := 2 * h + 2) (m := 2 + 2 * h) (by omega)
  apply mpcAffineDeterminantCertificate_handles d halpha hr hqe
    nuP
    (tameOfSpec (2 + 2 * h) q (mpcW alpha r (p epsilon r) d.display h)
      (Count.tameSpecializes_mpcW hq0 hqe (by omega)
        r (p epsilon r) d.display h))
    (C.pro2 hq0 hqe)
    (C.compat hq0 hqe (Count.tameSpecializes_mpcW hq0 hqe (by omega)
      r (p epsilon r) d.display h))
  · exact TameSpec.tameOfSpec_gammaGen _ .sigma
  · exact TameSpec.tameOfSpec_gammaGen _ .tau
  · exact fun i ↦ TameSpec.tameOfSpec_gammaGen _ (.wild i)

/-- All non-routine displayed Mpc leaves at any normalized presented pro-2 core. -/
noncomputable def mpcFlexibleCertificateLeavesRN
    {alpha r h q : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta)
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} (hP : IsProP 2 P) {nuP : ContinuousMonoidHom P Ztwo}
    (C : FlexibleCoreLeavesRN (2 + 2 * h)
      (mpcW alpha r (p epsilon r) d.display h) P nuP) :
    FlexibleCertificateLeavesRN (2 + 2 * h) q
      (mpcW alpha r (p epsilon r) d.display h) P hP nuP
      (standardNumerics (2 + 2 * h)) hq0 hqe := by
  let tame := Count.tameSpecializes_mpcW hq0 hqe (by omega : 1 ≤ alpha)
    r (p epsilon r) d.display h
  refine
    { tameSpecialization := tame
      core := C
      exactLifting := ?_
      stokes := ?_
      scalar := mpcCandidate_scalar d halpha hr hqe
      determinant := mpcAffineDeterminantCertificate_flexible d halpha hr hq0 hqe C }
  · have H := RecordBlocks.recBl_mpc_exactLiftingRN
      (alpha := alpha) (r := r) (h := h) (q := q) (epsilon := epsilon)
      d halpha hr hqe nuP
    rw [MProcyclicExact.gamma_sign_eq_display alpha r h q epsilon d] at H
    exact NProcyclic.exactLiftingRN_standard_congr (by omega) H
  · apply RecordBlocks.recBl_stokes_standard_congr
      (n := 2 * h + 2) (m := 2 + 2 * h) (by omega)
    exact mpcCand_stokes_displayed
      (alpha := alpha) (r := r) (pp := p epsilon r) (h := h) (q := q)
      d halpha hr hqe (P := P) (nuP := nuP)

/-- A normalized displayed Mpc core has a complete corrected certificate. -/
noncomputable def mpcWordCertificateRN_flexible
    {alpha r h q : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta)
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} (hP : IsProP 2 P) {nuP : ContinuousMonoidHom P Ztwo}
    (C : FlexibleCoreLeavesRN (2 + 2 * h)
      (mpcW alpha r (p epsilon r) d.display h) P nuP) :
    WordCertificateRN (2 + 2 * h) q
      (mpcW alpha r (p epsilon r) d.display h) P hP nuP
      (standardNumerics (2 + 2 * h)) :=
  wordCertificateRN_of_flexibleLeaves
    (mpcFlexibleCertificateLeavesRN d halpha hr hq0 hqe hP C)

#print axioms mpcAffineDeterminantCertificate_flexible
#print axioms mpcFlexibleCertificateLeavesRN
#print axioms mpcWordCertificateRN_flexible

end

end GQ2.Dyadic.Instances.MpcFlexibleCertificate

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MOrientationCharacteristic

/-!
# General M pivot consumers with characteristic orientation discharged

The characteristic-orientation theorem is uniform in the depth and handle count.
These wrappers remove that formerly explicit premise from the realized compact-M
and Mpc certificate consumers.
-/

namespace GQ2.Dyadic.Instances.MOrientationCharacteristicFinal

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MOrientationCharacteristic
open GQ2.Dyadic.Instances.MRealizedCertificatePivotBoundary
open GQ2.Dyadic.Instances.MFieldCanonicalOrientationBoundary
open GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary
open GQ2.Dyadic.Instances.MFieldStrictHandleNormalForm
open GQ2.Dyadic.Instances.M0FamilyField
open GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.Words.Mpc

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {alpha h q : ℕ}

omit [T2Space (GalK K)] in
/-- Every realized compact-M word certificate forces the canonical field pivot. -/
theorem mFieldCPivotAtLevel_zero_of_wordCertificateRN_general
    (B : MarkedRecip Rec K)
    (e0 : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (M : MarkedCoreRealization (K := K) (B := B) (DM alpha h) nuP)
    (W : WordCertificateRN (2 + 2 * h) q (mCompactW alpha h)
      (DM alpha h) (isProP_DM alpha h) nuP (standardNumerics (2 + 2 * h))) :
    MFieldCPivotAtLevel B alpha 0 h := by
  exact mFieldCPivotAtLevel_zero_of_wordCertificateRN B e0 halpha hq0 hqe
    (mCoreOrientationCharacteristic_all (by omega)) nuP M W

omit [T2Space (GalK K)] in
/-- Every realized arbitrary-display Mpc word certificate forces the canonical field pivot. -/
theorem mFieldCPivotAtLevel_of_mpcWordCertificateRN_general
    (B : MarkedRecip Rec K) {r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta)
    (e0 : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r) (hq0 : q ≠ 0) (hqe : Even q)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (M : MarkedCoreRealization (K := K) (B := B) (DM alpha h) nuP)
    (W : WordCertificateRN (2 + 2 * h) q
      (mpcW alpha r (p epsilon r) d.display h)
      (DM alpha h) (isProP_DM alpha h) nuP (standardNumerics (2 + 2 * h))) :
    MFieldCPivotAtLevel B alpha r h := by
  exact mFieldCPivotAtLevel_of_mpcWordCertificateRN B d e0 halpha hr hq0 hqe
    (mCoreOrientationCharacteristic_all (by omega)) nuP M W

omit [T2Space (GalK K)] in
/-- The compact realized-certificate packet forces the pivot with no orientation premise. -/
theorem mFieldCPivotAtLevel_zero_of_realizedWordCertificateRN_general
    (B : MarkedRecip Rec K)
    (e0 : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (H : M0RealizedWordCertificateRN B alpha h q) :
    MFieldCPivotAtLevel B alpha 0 h := by
  exact mFieldCPivotAtLevel_zero_of_realizedWordCertificateRN
    B e0 halpha hq0 hqe (mCoreOrientationCharacteristic_all (by omega)) H

omit [T2Space (GalK K)] in
/-- The arbitrary-display Mpc realized packet forces the pivot with no orientation premise. -/
theorem mFieldCPivotAtLevel_of_mpcRealizedWordCertificateRN_general
    (B : MarkedRecip Rec K) {r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta)
    (e0 : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r) (hq0 : q ≠ 0) (hqe : Even q)
    (H : MpcRealizedWordCertificateRN B alpha r q epsilon h d) :
    MFieldCPivotAtLevel B alpha r h := by
  exact mFieldCPivotAtLevel_of_mpcRealizedWordCertificateRN
    B d e0 halpha hr hq0 hqe (mCoreOrientationCharacteristic_all (by omega)) H

omit [T2Space (GalK K)] in
/-- A strict handle form is incompatible with every realized compact-M certificate. -/
theorem no_mCompact_realizedWordCertificateRN_of_strictHandle_general
    (B : MarkedRecip Rec K)
    (e0 : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (Hstrict : StrictNormalizedMHandlePivotAtLevel (r := 0) (m0Transport B e0))
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (M : MarkedCoreRealization (K := K) (B := B) (DM alpha h) nuP) :
    ¬ Nonempty (WordCertificateRN (2 + 2 * h) q (mCompactW alpha h)
      (DM alpha h) (isProP_DM alpha h) nuP (standardNumerics (2 + 2 * h))) := by
  exact no_mCompact_realizedWordCertificateRN_of_strictHandle
    B e0 halpha hq0 hqe (mCoreOrientationCharacteristic_all (by omega)) Hstrict nuP M

#print axioms mFieldCPivotAtLevel_zero_of_wordCertificateRN_general
#print axioms mFieldCPivotAtLevel_of_mpcWordCertificateRN_general
#print axioms mFieldCPivotAtLevel_zero_of_realizedWordCertificateRN_general
#print axioms mFieldCPivotAtLevel_of_mpcRealizedWordCertificateRN_general
#print axioms no_mCompact_realizedWordCertificateRN_of_strictHandle_general

end

end GQ2.Dyadic.Instances.MOrientationCharacteristicFinal

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MWordCertificateOrbit

/-!
# Realized M certificates already contain the canonical pivot

W314 shows that a corrected word certificate fixes the marking up to a continuous core
automorphism.  This module transports a field realization along that automorphism.  For both
compact M and arbitrary-display, arbitrary-handle Mpc, a realized corrected certificate
therefore produces the canonical marked-core realization.

Under field orientation rigidity, the canonical realization forces the exact distinguished-C
pivot.  Equivalently, assuming characteristic core orientation and one oriented field
equivalence, any realized corrected M certificate already contains a solution of the general
field-pivot problem.  Constructing an alternate certificate at W313's handle marking cannot
bypass that problem.  In the compact-M strict form it is outright impossible.
-/

namespace GQ2.Dyadic.Instances.MRealizedCertificatePivotBoundary

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MWordCertificateOrbit
open GQ2.Dyadic.Instances.MFieldCanonicalOrientationBoundary
open GQ2.Dyadic.Instances.MFieldCanonicalRealizationBoundary
open GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary
open GQ2.Dyadic.Instances.MFieldStrictHandleNormalForm
open GQ2.Dyadic.Instances.M0FamilyField
open GQ2.Dyadic.Instances.MCompactCore
open GQ2.Dyadic.Instances.CanonicalRecords
open GQ2.Dyadic.FieldBranchId
open GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Instances.MpcGeneralHandleFamilyClosed

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- Transport a corrected core realization along an automorphism which compares markings. -/
noncomputable def markedCoreRealizationOfMarkingOrbit
    {B : MarkedRecip Rec K} {P : ProfiniteGrp}
    {nu₁ nu₂ : ContinuousMonoidHom (P : Type) Ztwo}
    (M : MarkedCoreRealization (K := K) (B := B) P nu₂)
    (Psi : ContinuousMulEquiv (P : Type) (P : Type))
    (hPsi : ∀ x, nu₂ (Psi x) = nu₁ x) :
    MarkedCoreRealization (K := K) (B := B) P nu₁ where
  equiv := Psi.trans M.equiv
  nu_equiv x := by
    rw [← hPsi x]
    exact M.nu_equiv (Psi x)

variable {alpha h q : ℕ}

/-- A compact-M candidate certificate tied to an actual field realization, but with no
canonical marking assumption. -/
def M0RealizedWordCertificateRN (B : MarkedRecip Rec K)
    (alpha h q : ℕ) : Prop :=
  ∃ nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo,
    Nonempty (MarkedCoreRealization (K := K) (B := B) (DM alpha h) nuP) ∧
      Nonempty (WordCertificateRN (2 + 2 * h) q (mCompactW alpha h)
        (DM alpha h) (isProP_DM alpha h) nuP (standardNumerics (2 + 2 * h)))

/-- The analogous realized-certificate packet for an arbitrary displayed Mpc word. -/
def MpcRealizedWordCertificateRN (B : MarkedRecip Rec K)
    (alpha r q : ℕ) (epsilon : Bool) (h : ℕ) {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta) : Prop :=
  ∃ nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo,
    Nonempty (MarkedCoreRealization (K := K) (B := B) (DM alpha h) nuP) ∧
      Nonempty (WordCertificateRN (2 + 2 * h) q
        (mpcW alpha r (p epsilon r) d.display h)
        (DM alpha h) (isProP_DM alpha h) nuP (standardNumerics (2 + 2 * h)))

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
/-- A compact-M word certificate and a field realization at its marking together yield the
canonical compact-M realization. -/
theorem m0CanonicalMarkedCoreRealization_of_wordCertificateRN
    (B : MarkedRecip Rec K) (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (M : MarkedCoreRealization (K := K) (B := B) (DM alpha h) nuP)
    (W : WordCertificateRN (2 + 2 * h) q (mCompactW alpha h)
      (DM alpha h) (isProP_DM alpha h) nuP (standardNumerics (2 + 2 * h))) :
    M0CanonicalMarkedCoreRealization B alpha h := by
  obtain ⟨Psi, hPsi⟩ :=
    mCompact_markingOrbit_of_wordCertificateRN halpha hq0 hqe nuP W
  refine ⟨by omega, ⟨?_⟩⟩
  exact markedCoreRealizationOfMarkingOrbit M Psi hPsi

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
/-- The same orbit argument is uniform for every positive-level Mpc display and handle count:
a realized Mpc word certificate yields the canonical displayed realization. -/
theorem mpcCanonicalMarkedCoreRealization_of_wordCertificateRN
    (B : MarkedRecip Rec K) {r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta) (halpha : 2 ≤ alpha) (hr : 1 ≤ r)
    (hq0 : q ≠ 0) (hqe : Even q)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (M : MarkedCoreRealization (K := K) (B := B) (DM alpha h) nuP)
    (W : WordCertificateRN (2 + 2 * h) q
      (mpcW alpha r (p epsilon r) d.display h)
      (DM alpha h) (isProP_DM alpha h) nuP (standardNumerics (2 + 2 * h))) :
    MpcCanonicalMarkedCoreRealization B alpha r h epsilon eta := by
  let W0 := mpcWordCertificateRN_of_display
    alpha r q epsilon h d halpha hr hq0 hqe
  obtain ⟨Psi, hPsi⟩ := wordCertificateRN_markingOrbit W0 W
  refine ⟨by omega, ⟨?_⟩⟩
  exact markedCoreRealizationOfMarkingOrbit M Psi hPsi

omit [T2Space (GalK K)] in
/-- Field orientation rigidity makes any realized compact-M certificate force the exact
canonical C pivot. -/
theorem mFieldCPivotAtLevel_zero_of_wordCertificateRN_of_orientationRigidity
    (B : MarkedRecip Rec K)
    (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (Hrigid : MFieldOrientationRigidityAt (K := K) alpha h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (M : MarkedCoreRealization (K := K) (B := B) (DM alpha h) nuP)
    (W : WordCertificateRN (2 + 2 * h) q (mCompactW alpha h)
      (DM alpha h) (isProP_DM alpha h) nuP (standardNumerics (2 + 2 * h))) :
    MFieldCPivotAtLevel B alpha 0 h := by
  apply m0_cPivot_of_canonicalRealization_of_orientationRigidity B Hrigid
  exact m0CanonicalMarkedCoreRealization_of_wordCertificateRN
    B halpha hq0 hqe nuP M W

omit [T2Space (GalK K)] in
/-- Characteristic core orientation plus one oriented field equivalence supplies the preceding
orientation-rigidity boundary. -/
theorem mFieldCPivotAtLevel_zero_of_wordCertificateRN
    (B : MarkedRecip Rec K)
    (e0 : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (Hchar : MCoreOrientationCharacteristic alpha h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (M : MarkedCoreRealization (K := K) (B := B) (DM alpha h) nuP)
    (W : WordCertificateRN (2 + 2 * h) q (mCompactW alpha h)
      (DM alpha h) (isProP_DM alpha h) nuP (standardNumerics (2 + 2 * h))) :
    MFieldCPivotAtLevel B alpha 0 h := by
  apply mFieldCPivotAtLevel_zero_of_wordCertificateRN_of_orientationRigidity
    B halpha hq0 hqe
  · exact (mCoreOrientationCharacteristic_iff_fieldOrientationRigidityAt e0).mp Hchar
  · exact M
  · exact W

omit [T2Space (GalK K)] in
/-- Under field orientation rigidity, any realized arbitrary-display Mpc certificate already
forces the canonical exact C pivot. -/
theorem mFieldCPivotAtLevel_of_mpcWordCertificateRN_of_orientationRigidity
    (B : MarkedRecip Rec K) {r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta)
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r) (hq0 : q ≠ 0) (hqe : Even q)
    (Hrigid : MFieldOrientationRigidityAt (K := K) alpha h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (M : MarkedCoreRealization (K := K) (B := B) (DM alpha h) nuP)
    (W : WordCertificateRN (2 + 2 * h) q
      (mpcW alpha r (p epsilon r) d.display h)
      (DM alpha h) (isProP_DM alpha h) nuP (standardNumerics (2 + 2 * h))) :
    MFieldCPivotAtLevel B alpha r h := by
  apply mpc_cPivot_of_canonicalRealization_of_orientationRigidity B Hrigid
  exact mpcCanonicalMarkedCoreRealization_of_wordCertificateRN
    B d halpha hr hq0 hqe nuP M W

omit [T2Space (GalK K)] in
/-- Characteristic core orientation supplies the arbitrary-display Mpc pivot boundary after
one oriented field equivalence is fixed. -/
theorem mFieldCPivotAtLevel_of_mpcWordCertificateRN
    (B : MarkedRecip Rec K) {r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta)
    (e0 : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r) (hq0 : q ≠ 0) (hqe : Even q)
    (Hchar : MCoreOrientationCharacteristic alpha h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (M : MarkedCoreRealization (K := K) (B := B) (DM alpha h) nuP)
    (W : WordCertificateRN (2 + 2 * h) q
      (mpcW alpha r (p epsilon r) d.display h)
      (DM alpha h) (isProP_DM alpha h) nuP (standardNumerics (2 + 2 * h))) :
    MFieldCPivotAtLevel B alpha r h := by
  apply mFieldCPivotAtLevel_of_mpcWordCertificateRN_of_orientationRigidity
    B d halpha hr hq0 hqe
  · exact (mCoreOrientationCharacteristic_iff_fieldOrientationRigidityAt e0).mp Hchar
  · exact M
  · exact W

omit [T2Space (GalK K)] in
/-- The compact realized-certificate packet forces the field pivot under characteristic
orientation. -/
theorem mFieldCPivotAtLevel_zero_of_realizedWordCertificateRN
    (B : MarkedRecip Rec K)
    (e0 : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (Hchar : MCoreOrientationCharacteristic alpha h)
    (H : M0RealizedWordCertificateRN B alpha h q) :
    MFieldCPivotAtLevel B alpha 0 h := by
  obtain ⟨nuP, ⟨M⟩, ⟨W⟩⟩ := H
  exact mFieldCPivotAtLevel_zero_of_wordCertificateRN
    B e0 halpha hq0 hqe Hchar nuP M W

omit [T2Space (GalK K)] in
/-- Uniformly in the display and handle count, the Mpc realized-certificate packet forces the
field pivot under characteristic orientation. -/
theorem mFieldCPivotAtLevel_of_mpcRealizedWordCertificateRN
    (B : MarkedRecip Rec K) {r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta)
    (e0 : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r) (hq0 : q ≠ 0) (hqe : Even q)
    (Hchar : MCoreOrientationCharacteristic alpha h)
    (H : MpcRealizedWordCertificateRN B alpha r q epsilon h d) :
    MFieldCPivotAtLevel B alpha r h := by
  obtain ⟨nuP, ⟨M⟩, ⟨W⟩⟩ := H
  exact mFieldCPivotAtLevel_of_mpcWordCertificateRN
    B d e0 halpha hr hq0 hqe Hchar nuP M W

omit [T2Space (GalK K)] in
/-- Characteristic orientation makes the strict handle form incompatible with any realized
compact-M word certificate, even when the certificate initially uses an arbitrary marking. -/
theorem no_mCompact_realizedWordCertificateRN_of_strictHandle
    (B : MarkedRecip Rec K)
    (e0 : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (Hchar : MCoreOrientationCharacteristic alpha h)
    (Hstrict : StrictNormalizedMHandlePivotAtLevel (r := 0) (m0Transport B e0))
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (M : MarkedCoreRealization (K := K) (B := B) (DM alpha h) nuP) :
    ¬ Nonempty (WordCertificateRN (2 + 2 * h) q (mCompactW alpha h)
      (DM alpha h) (isProP_DM alpha h) nuP (standardNumerics (2 + 2 * h))) := by
  intro hW
  obtain ⟨W⟩ := hW
  obtain ⟨_j, _hU, _hV, qC, hC⟩ := Hstrict
  norm_num at hC
  have hnot : ¬ IsUnit (toAdd ((m0Transport B e0) (dmC alpha h))) := by
    intro hunit
    have hpar := mParityZ_of_isUnit hunit
    rw [hC, mParityZ_two_mul] at hpar
    exact zero_ne_one hpar
  obtain ⟨eP, gamma, hgamma⟩ :=
    mFieldCPivotAtLevel_zero_of_wordCertificateRN
      B e0 halpha hq0 hqe Hchar nuP M W
  let Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type) :=
    eP.1.trans e0.1.symm
  apply M0C0PivotAutomorphism.no_oriented_dmC_unitizer
    halpha (m0Transport B e0) hnot
  refine ⟨Psi, Hchar Psi, ?_⟩
  have hunitP : IsUnit (toAdd ((m0Transport B eP) (dmC alpha h))) := by
    change IsUnit (toAdd (nuUrKTwo B (eP.1 (dmC alpha h))))
    rw [hgamma, pow_zero, mul_one]
    exact gamma.isUnit
  have heq : (m0Transport B e0) (Psi (dmC alpha h)) =
      (m0Transport B eP) (dmC alpha h) := by
    change nuUrKTwo B (e0.1 (e0.1.symm (eP.1 (dmC alpha h)))) =
      nuUrKTwo B (eP.1 (dmC alpha h))
    rw [e0.1.apply_symm_apply]
  rw [heq]
  exact hunitP

#print axioms markedCoreRealizationOfMarkingOrbit
#print axioms M0RealizedWordCertificateRN
#print axioms MpcRealizedWordCertificateRN
#print axioms m0CanonicalMarkedCoreRealization_of_wordCertificateRN
#print axioms mpcCanonicalMarkedCoreRealization_of_wordCertificateRN
#print axioms mFieldCPivotAtLevel_zero_of_wordCertificateRN_of_orientationRigidity
#print axioms mFieldCPivotAtLevel_zero_of_wordCertificateRN
#print axioms mFieldCPivotAtLevel_of_mpcWordCertificateRN_of_orientationRigidity
#print axioms mFieldCPivotAtLevel_of_mpcWordCertificateRN
#print axioms mFieldCPivotAtLevel_zero_of_realizedWordCertificateRN
#print axioms mFieldCPivotAtLevel_of_mpcRealizedWordCertificateRN
#print axioms no_mCompact_realizedWordCertificateRN_of_strictHandle

end

end GQ2.Dyadic.Instances.MRealizedCertificatePivotBoundary

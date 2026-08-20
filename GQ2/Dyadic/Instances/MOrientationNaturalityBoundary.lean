/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MRealizedCertificatePivotBoundary

/-!
# The finite naturality boundary for the canonical M orientation

The repository already proves that the four Labute values and triviality on every handle
characterize `chiM`.  This module shows that the remaining characteristic-orientation theorem
is exactly the naturality of that finite presentation predicate.  On the field side, it is
equivalent to checking the same finite rows for the pullback of the cyclotomic character along
every abstract core equivalence.

Thus no integral dualizing-module object is hidden in the downstream campaign.  Such a theory
must prove precisely these finite pullback rows; once it does, the uniform compact-M and Mpc
certificate consumers force the distinguished-C pivot.
-/

namespace GQ2.Dyadic.Instances.MOrientationNaturalityBoundary

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MFieldCanonicalOrientationBoundary
open GQ2.Dyadic.Instances.MRealizedCertificatePivotBoundary
open GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary
open GQ2.Dyadic.Instances.M0FamilyField
open GQ2.Dyadic.Instances.CanonicalRecords
open GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.Words.Mpc

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The finite presentation predicate remains true after pulling `chiM` back along every core
automorphism. -/
def MCoreOrientationRowsInvariant (alpha h : ℕ) : Prop :=
  ∀ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
    IsPresentedOrientationM alpha h (pullbackCharacter (chiM alpha h) Psi)

/-- Pullback naturality of the complete finite `M` presentation predicate on the standard
core itself. -/
def MCorePresentedOrientationNatural (alpha h : ℕ) : Prop :=
  PullbackNatural (IsPresentedOrientationM alpha h)
    (IsPresentedOrientationM alpha h)

/-- For `alpha >= 1`, the finite pulled-back rows are exactly characteristic orientation. -/
theorem mCoreOrientationRowsInvariant_iff_characteristic
    {alpha h : ℕ} (halpha : 1 ≤ alpha) :
    MCoreOrientationRowsInvariant alpha h ↔
      MCoreOrientationCharacteristic alpha h := by
  constructor
  · intro H Psi x
    have heq := (isPresentedOrientationM_iff halpha
      (pullbackCharacter (chiM alpha h) Psi)).mp (H Psi)
    exact DFunLike.congr_fun heq x
  · intro H Psi
    apply (isPresentedOrientationM_iff halpha _).mpr
    apply ContinuousMonoidHom.ext
    intro x
    exact H Psi x

/-- Since the finite predicate uniquely characterizes `chiM`, its self-naturality is already
equivalent to checking the pullback of that one character. -/
theorem mCorePresentedOrientationNatural_iff_rowsInvariant
    {alpha h : ℕ} (halpha : 1 ≤ alpha) :
    MCorePresentedOrientationNatural alpha h ↔
      MCoreOrientationRowsInvariant alpha h := by
  constructor
  · intro H Psi
    exact H Psi (chiM alpha h) (isPresentedOrientationM_chiM h halpha)
  · intro H Psi chi hchi
    have heq : chi = chiM alpha h :=
      (isPresentedOrientationM_iff halpha chi).mp hchi
    rw [heq]
    exact H Psi

/-- The intrinsic orientation theorem has the exact categorical spelling: naturality of the
finite presentation predicate under core automorphisms. -/
theorem mCorePresentedOrientationNatural_iff_characteristic
    {alpha h : ℕ} (halpha : 1 ≤ alpha) :
    MCorePresentedOrientationNatural alpha h ↔
      MCoreOrientationCharacteristic alpha h := by
  rw [mCorePresentedOrientationNatural_iff_rowsInvariant halpha,
    mCoreOrientationRowsInvariant_iff_characteristic halpha]

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The concrete field-side boundary: along every abstract equivalence, the cyclotomic
character has the four canonical Labute values and value one on every handle. -/
def MFieldCyclotomicRowsAt (alpha h : ℕ) : Prop :=
  ∀ e : ContinuousMulEquiv (DM alpha h : Type)
      (maxProPQuotient 2 (GalK K)),
    IsPresentedOrientationM alpha h
      (pullbackCharacter (chiCycKTwo (K := K)) e)

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The finite cyclotomic row calculation is equivalent to full field-orientation rigidity. -/
theorem mFieldCyclotomicRowsAt_iff_orientationRigidity
    {alpha h : ℕ} (halpha : 1 ≤ alpha) :
    MFieldCyclotomicRowsAt (K := K) alpha h ↔
      MFieldOrientationRigidityAt (K := K) alpha h := by
  constructor
  · intro H e x
    have heq := (isPresentedOrientationM_iff halpha
      (pullbackCharacter (chiCycKTwo (K := K)) e)).mp (H e)
    exact DFunLike.congr_fun heq x
  · intro H e
    apply (isPresentedOrientationM_iff halpha _).mpr
    apply ContinuousMonoidHom.ext
    intro x
    exact H e x

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- After fixing one oriented field equivalence, the intrinsic finite naturality statement and
the field-side finite cyclotomic rows are equivalent. -/
theorem mCoreOrientationRowsInvariant_iff_fieldCyclotomicRowsAt
    {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (e0 : OrientedContinuousMulEquiv
      (chiM alpha h) (chiCycKTwo (K := K))) :
    MCoreOrientationRowsInvariant alpha h ↔
      MFieldCyclotomicRowsAt (K := K) alpha h := by
  rw [mCoreOrientationRowsInvariant_iff_characteristic halpha,
    mFieldCyclotomicRowsAt_iff_orientationRigidity halpha,
    mCoreOrientationCharacteristic_iff_fieldOrientationRigidityAt e0]

variable {alpha h q : ℕ}

omit [T2Space (GalK K)] in
/-- The finite cyclotomic rows feed the uniform compact-M realized-certificate pivot theorem
directly; no separate abstract orientation premise remains. -/
theorem mFieldCPivotAtLevel_zero_of_wordCertificateRN_of_cyclotomicRows
    (B : MarkedRecip Rec K)
    (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (Hrows : MFieldCyclotomicRowsAt (K := K) alpha h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (M : MarkedCoreRealization (K := K) (B := B) (DM alpha h) nuP)
    (W : WordCertificateRN (2 + 2 * h) q (mCompactW alpha h)
      (DM alpha h) (isProP_DM alpha h) nuP (standardNumerics (2 + 2 * h))) :
    MFieldCPivotAtLevel B alpha 0 h := by
  apply mFieldCPivotAtLevel_zero_of_wordCertificateRN_of_orientationRigidity
    B halpha hq0 hqe
  · exact (mFieldCyclotomicRowsAt_iff_orientationRigidity (by omega)).mp Hrows
  · exact M
  · exact W

omit [T2Space (GalK K)] in
/-- The same finite row boundary feeds the arbitrary-display, arbitrary-handle Mpc pivot
theorem. -/
theorem mFieldCPivotAtLevel_of_mpcWordCertificateRN_of_cyclotomicRows
    (B : MarkedRecip Rec K) {r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta)
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r) (hq0 : q ≠ 0) (hqe : Even q)
    (Hrows : MFieldCyclotomicRowsAt (K := K) alpha h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (M : MarkedCoreRealization (K := K) (B := B) (DM alpha h) nuP)
    (W : WordCertificateRN (2 + 2 * h) q
      (mpcW alpha r (p epsilon r) d.display h)
      (DM alpha h) (isProP_DM alpha h) nuP (standardNumerics (2 + 2 * h))) :
    MFieldCPivotAtLevel B alpha r h := by
  apply mFieldCPivotAtLevel_of_mpcWordCertificateRN_of_orientationRigidity
    B d halpha hr hq0 hqe
  · exact (mFieldCyclotomicRowsAt_iff_orientationRigidity (by omega)).mp Hrows
  · exact M
  · exact W

#print axioms MCoreOrientationRowsInvariant
#print axioms MCorePresentedOrientationNatural
#print axioms mCoreOrientationRowsInvariant_iff_characteristic
#print axioms mCorePresentedOrientationNatural_iff_rowsInvariant
#print axioms mCorePresentedOrientationNatural_iff_characteristic
#print axioms MFieldCyclotomicRowsAt
#print axioms mFieldCyclotomicRowsAt_iff_orientationRigidity
#print axioms mCoreOrientationRowsInvariant_iff_fieldCyclotomicRowsAt
#print axioms mFieldCPivotAtLevel_zero_of_wordCertificateRN_of_cyclotomicRows
#print axioms mFieldCPivotAtLevel_of_mpcWordCertificateRN_of_cyclotomicRows

end

end GQ2.Dyadic.Instances.MOrientationNaturalityBoundary

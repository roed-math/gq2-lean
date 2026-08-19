/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MFieldStrictHandleNormalForm
import GQ2.Dyadic.Instances.MFieldCanonicalOrientationBoundary

/-!
# Word certificates determine a marking orbit

Two continuous epimorphisms of a profinite group with the same kernel differ by a continuous
automorphism of their common target.  Applied to corrected word certificates, this says that
two certificates for the same word and core cannot choose unrelated markings: their markings
belong to the same continuous automorphism orbit.

For compact M, comparison with the canonical core map makes this orbit explicit.  Under
characteristic M orientation, a marking whose distinguished C row is nonunit therefore cannot
support the current compact-M word certificate.  In particular, W313's strict handle form is
not an analytic case that can be closed by silently reusing the canonical certificate after a
coordinate rename; it needs either a genuinely different presentation or an arithmetic
elimination of the handle alternative.
-/

namespace GQ2.Dyadic.Instances.MWordCertificateOrbit

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MCompactCore
open GQ2.Dyadic.Instances.CanonicalRecords
open GQ2.Dyadic.FieldBranchId
open GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.Instances.MFieldCanonicalOrientationBoundary
open GQ2.Dyadic.Instances.M0C0PivotAutomorphism
open GQ2.Dyadic.Instances.MFieldCanonicalMarkingTransitivity
open GQ2.Dyadic.Instances.MFieldStrictHandleNormalForm
open GQ2.Dyadic.Instances.M0FamilyField

/-- A continuous epimorphism of profinite groups identifies its kernel quotient with the
target as a topological group. -/
noncomputable def quotientKerContinuousEquivOfSurjective
    {A B : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [CompactSpace B] [T2Space B]
    (f : ContinuousMonoidHom A B) (hf : Function.Surjective f) :
    A ⧸ f.toMonoidHom.ker ≃ₜ* B := by
  let e : A ⧸ f.toMonoidHom.ker ≃* B :=
    QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom hf
  have he : Continuous e := by
    apply (QuotientGroup.isQuotientMap_mk f.toMonoidHom.ker).continuous_iff.mpr
    exact f.continuous_toFun
  exact
    { e with
      continuous_toFun := he
      continuous_invFun :=
        (e.toEquiv.toHomeomorphOfContinuousClosed he he.isClosedMap).continuous_invFun }

@[simp] theorem quotientKerContinuousEquivOfSurjective_mk
    {A B : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [CompactSpace B] [T2Space B]
    (f : ContinuousMonoidHom A B) (hf : Function.Surjective f) (x : A) :
    quotientKerContinuousEquivOfSurjective f hf (QuotientGroup.mk x) = f x := rfl

/-- Equality of closed normal subgroups gives the evident continuous quotient equivalence. -/
noncomputable def quotientContinuousMulEquivOfEq
    {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (N₁ N₂ : Subgroup A) [N₁.Normal] [N₂.Normal]
    [IsClosed (N₁ : Set A)] [IsClosed (N₂ : Set A)] (hN : N₁ = N₂) :
    A ⧸ N₁ ≃ₜ* A ⧸ N₂ := by
  subst N₂
  exact ContinuousMulEquiv.refl _

@[simp] theorem quotientContinuousMulEquivOfEq_mk
    {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (N₁ N₂ : Subgroup A) [N₁.Normal] [N₂.Normal]
    [IsClosed (N₁ : Set A)] [IsClosed (N₂ : Set A)] (hN : N₁ = N₂)
    (x : A) :
    quotientContinuousMulEquivOfEq N₁ N₂ hN (QuotientGroup.mk x) =
      QuotientGroup.mk x := by
  cases hN
  rfl

/-- Two continuous epimorphisms of a profinite group with the same kernel differ by a target
automorphism. -/
theorem exists_continuousMulEquiv_of_surjective_of_ker_eq
    {A B : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [CompactSpace B] [T2Space B] [TotallyDisconnectedSpace B]
    (f g : ContinuousMonoidHom A B) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (hker : f.toMonoidHom.ker = g.toMonoidHom.ker) :
    ∃ Psi : ContinuousMulEquiv B B, ∀ x, Psi (f x) = g x := by
  haveI : IsClosed (f.toMonoidHom.ker : Set A) := by
    rw [MonoidHom.coe_ker]
    exact IsClosed.preimage f.continuous_toFun isClosed_singleton
  haveI : IsClosed (g.toMonoidHom.ker : Set A) := by
    rw [MonoidHom.coe_ker]
    exact IsClosed.preimage g.continuous_toFun isClosed_singleton
  let ef := quotientKerContinuousEquivOfSurjective f hf
  let eg := quotientKerContinuousEquivOfSurjective g hg
  let ek := quotientContinuousMulEquivOfEq
    f.toMonoidHom.ker g.toMonoidHom.ker hker
  let Psi := ef.symm.trans (ek.trans eg)
  refine ⟨Psi, fun x => ?_⟩
  have hfinv : ef.symm (f x) = QuotientGroup.mk x := by
    calc
      ef.symm (f x) = ef.symm (ef (QuotientGroup.mk x)) := by rfl
      _ = QuotientGroup.mk x := ef.symm_apply_apply _
  change eg (ek (ef.symm (f x))) = g x
  rw [hfinv]
  have hek : ek (QuotientGroup.mk x) = QuotientGroup.mk x :=
    quotientContinuousMulEquivOfEq_mk _ _ hker x
  rw [hek]
  rfl

/-- Two corrected word certificates for the same word and pro-2 core have markings in the
same continuous automorphism orbit. -/
theorem wordCertificateRN_markingOrbit
    {n q : ℕ} {R : PWord (Generator n)} {P : ProfiniteGrp}
    {hP : IsProP 2 P} {nu₁ nu₂ : ContinuousMonoidHom (P : Type) Ztwo}
    {SN : SourceNumerics n}
    (W₁ : WordCertificateRN n q R P hP nu₁ SN)
    (W₂ : WordCertificateRN n q R P hP nu₂ SN) :
    ∃ Psi : ContinuousMulEquiv (P : Type) (P : Type),
      ∀ x, nu₂ (Psi x) = nu₁ x := by
  have hker : W₁.pro2.toMonoidHom.ker = W₂.pro2.toMonoidHom.ker := by
    rw [W₁.ker_pro2, W₂.ker_pro2]
  obtain ⟨Psi, hPsi⟩ := exists_continuousMulEquiv_of_surjective_of_ker_eq
    W₁.pro2 W₂.pro2 W₁.hpro2 W₂.hpro2 hker
  refine ⟨Psi, fun x => ?_⟩
  obtain ⟨g, rfl⟩ := W₁.hpro2 x
  rw [hPsi]
  rw [← W₂.compat, ← W₁.compat]

variable {alpha h q : ℕ}

/-- Any corrected compact-M word certificate forces its marking into the canonical marking
orbit.  This follows solely from the two presentation epimorphisms and tame compatibility. -/
theorem mCompact_markingOrbit_of_wordCertificateRN
    (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (W : WordCertificateRN (2 + 2 * h) q (mCompactW alpha h)
      (DM alpha h) (isProP_DM alpha h) nuP (standardNumerics (2 + 2 * h))) :
    ∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      ∀ x, nuP (Psi x) = fieldId_mNuZtwo alpha h (by omega) x := by
  have hker : (mPro2 alpha h q (by omega) hq0 hqe).toMonoidHom.ker =
      W.pro2.toMonoidHom.ker := by
    rw [ker_mPro2, W.ker_pro2]
  obtain ⟨Psi, hPsi⟩ := exists_continuousMulEquiv_of_surjective_of_ker_eq
    (mPro2 alpha h q (by omega) hq0 hqe) W.pro2
    (mPro2_surjective alpha h q (by omega) hq0 hqe) W.hpro2 hker
  refine ⟨Psi, fun x => ?_⟩
  obtain ⟨g, rfl⟩ := mPro2_surjective alpha h q (by omega) hq0 hqe x
  rw [hPsi]
  rw [← W.compat]
  rw [mCompat alpha h q (by omega) hq0 hqe W.tameSpecialization
    (fieldId_mNuZtwo alpha h (by omega))
    (canRec_mNuZtwo_sigma alpha h (by omega))
    (canRec_mNuZtwo_wild alpha h (by omega))]

/-- Under characteristic M orientation, a compact-M certificate cannot use a marking whose
distinguished C row is nonunit. -/
theorem no_mCompact_wordCertificateRN_of_nonunit_C_of_orientationCharacteristic
    (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (Hchar : MCoreOrientationCharacteristic alpha h)
    (hC : ¬ IsUnit (toAdd (ztwoIota (nuP (dmC alpha h))))) :
    ¬ Nonempty (WordCertificateRN (2 + 2 * h) q (mCompactW alpha h)
      (DM alpha h) (isProP_DM alpha h) nuP (standardNumerics (2 + 2 * h))) := by
  rintro ⟨W⟩
  obtain ⟨Psi, hPsi⟩ :=
    mCompact_markingOrbit_of_wordCertificateRN halpha hq0 hqe nuP W
  let nuZ : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]) :=
    ⟨ztwoIota.toMulEquiv.toMonoidHom.comp nuP.toMonoidHom,
      ztwoIota.continuous_toFun.comp nuP.continuous_toFun⟩
  apply no_oriented_dmC_unitizer halpha nuZ hC
  refine ⟨Psi, Hchar Psi, ?_⟩
  have hm := congrArg ztwoIota (hPsi (dmC alpha h))
  rw [fieldId_mNuZtwo_dmC, ztwoIota_ztwoOne] at hm
  change IsUnit (toAdd (ztwoIota (nuP (Psi (dmC alpha h)))))
  rw [hm, toAdd_ofAdd]
  exact isUnit_one

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

omit [T2Space (GalK K)] in
/-- In field coordinates, the strict normalized handle alternative cannot carry the current
compact-M word certificate when the M orientation is characteristic. -/
theorem no_mCompact_wordCertificateRN_mFieldTransportZ_of_strictHandle
    (B : MarkedRecip Rec K) (e : OrientedContinuousMulEquiv
      (chiM alpha h) (chiCycKTwo (K := K)))
    (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (Hchar : MCoreOrientationCharacteristic alpha h)
    (Hstrict : StrictNormalizedMHandlePivotAtLevel (r := 0) (m0Transport B e)) :
    ¬ Nonempty (WordCertificateRN (2 + 2 * h) q (mCompactW alpha h)
      (DM alpha h) (isProP_DM alpha h) (mFieldTransportZ B e.1)
      (standardNumerics (2 + 2 * h))) := by
  obtain ⟨_j, _hU, _hV, qC, hC⟩ := Hstrict
  apply no_mCompact_wordCertificateRN_of_nonunit_C_of_orientationCharacteristic
    halpha hq0 hqe (mFieldTransportZ B e.1) Hchar
  intro hunit
  have hpar := mParityZ_of_isUnit hunit
  have hvalue : toAdd (ztwoIota (mFieldTransportZ B e.1 (dmC alpha h))) =
      2 * qC := by
    rw [ztwoIota_mFieldTransportZ]
    exact hC
  rw [hvalue, mParityZ_two_mul] at hpar
  exact zero_ne_one hpar

#print axioms quotientKerContinuousEquivOfSurjective
#print axioms quotientContinuousMulEquivOfEq
#print axioms exists_continuousMulEquiv_of_surjective_of_ker_eq
#print axioms wordCertificateRN_markingOrbit
#print axioms mCompact_markingOrbit_of_wordCertificateRN
#print axioms no_mCompact_wordCertificateRN_of_nonunit_C_of_orientationCharacteristic
#print axioms no_mCompact_wordCertificateRN_mFieldTransportZ_of_strictHandle

end

end GQ2.Dyadic.Instances.MWordCertificateOrbit

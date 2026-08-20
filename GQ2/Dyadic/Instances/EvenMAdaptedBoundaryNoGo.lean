/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMMobileSourceModel
import GQ2.Dyadic.Instances.MWordCertificateOrbit
import GQ2.Dyadic.Instances.MOrientationCharacteristic
import GQ2.Dyadic.Instances.MFieldCanonicalOrientationBoundary
import GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary
import GQ2.Dyadic.Instances.MpcGeneralHandleFamilyFinal
import GQ2.Dyadic.Count.WildDischarge

/-!
# Adapted even-M boundaries preserve the pivot obstruction

W340 separated the corrected analytic core from its tame/pro-2 boundary, leaving open the
possibility that a noncanonical boundary on the intrinsic field marking might avoid the
distinguished-`C` placement condition.  This module proves uniformly that it cannot.

Every surjective tame coordinate on the same `GammaR` with pro-2 kernel has the canonical wild
kernel.  Every surjective pro-2 coordinate in a corrected boundary has the canonical maximal
pro-2 kernel.  Quotienting by these two kernels therefore identifies any adapted boundary with
the canonical one up to automorphisms of `Tq`, the pro-2 core, and `Ztwo`.  A continuous
automorphism of `Ztwo` is multiplication by a 2-adic unit, so it preserves both unitness and
every exact `2^r` level.

Consequently an adapted compact-M boundary still forces the level-zero `C` pivot, and an
adapted arbitrary-display, arbitrary-handle Mpc boundary still forces the selected level-`r`
pivot.  The mobile-boundary route is thus a general no-go, not a missing analytic calculation.
Any remaining field whose intrinsic marking lacks the pivot needs a different selector branch
or presentation normal form rather than a coordinate-wise boundary replacement.
-/

namespace GQ2.Dyadic.Instances.EvenMAdaptedBoundaryNoGo

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.Count
open GQ2.Dyadic.Instances.MWordCertificateOrbit
open GQ2.Dyadic.Instances.MOrientationCharacteristic
open GQ2.Dyadic.Instances.MFieldCanonicalOrientationBoundary
open GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary
open GQ2.Dyadic.Instances.MpcGeneralHandleFamilyFinal
open GQ2.Dyadic.Instances.SourceBoundaryReplacementRN
open GQ2.Dyadic.Instances.EvenMMobileSourceModel
open GQ2.Dyadic.Instances.FieldFlexibleEvenMFinal
open GQ2.Dyadic.Instances.MCompactCore
open GQ2.Dyadic.Instances.CanonicalRecords
open GQ2.Dyadic.FieldBranchId
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.Words.MCompact GQ2.Dyadic.Words.Mpc
open TameSpec

/-- A continuous automorphism of `Ztwo` sends its distinguished topological generator to a
`2`-adic unit. -/
theorem isUnit_ztwoIota_apply_ztwoOne (Psi : ContinuousMulEquiv Ztwo Ztwo) :
    IsUnit (toAdd (ztwoIota (Psi ztwoOne))) := by
  let F : ContinuousMonoidHom (Multiplicative ℤ_[2]) (Multiplicative ℤ_[2]) :=
    (ztwoIota : ContinuousMonoidHom Ztwo (Multiplicative ℤ_[2])).comp
      ((Psi : ContinuousMonoidHom Ztwo Ztwo).comp
        (ztwoIota.symm : ContinuousMonoidHom (Multiplicative ℤ_[2]) Ztwo))
  let a : ℤ_[2] := toAdd (F (ofAdd (1 : ℤ_[2])))
  obtain ⟨u, hu⟩ := Psi.surjective (ztwoIota.symm (ofAdd (1 : ℤ_[2])))
  let v : Multiplicative ℤ_[2] := ztwoIota u
  have hFv : F v = ofAdd (1 : ℤ_[2]) := by
    change ztwoIota (Psi (ztwoIota.symm (ztwoIota u))) = ofAdd (1 : ℤ_[2])
    rw [ztwoIota.symm_apply_apply, hu, ztwoIota.apply_symm_apply]
  have hF : F.toMonoidHom = (zpowZtwoHom
      PropOneOne.isProP_two_multPadicInt (ofAdd a)).toMonoidHom := by
    apply multPadicIntHom_ext F.continuous_toFun
      (zpowZtwoHom PropOneOne.isProP_two_multPadicInt (ofAdd a)).continuous_toFun
    change F (ofAdd (1 : ℤ_[2])) =
      zpowZtwo PropOneOne.isProP_two_multPadicInt (ofAdd a) 1
    rw [zpowZtwo_one_exp]
    exact (ofAdd_toAdd _).symm
  have hav : a * toAdd v = 1 := by
    have := hFv
    rw [show F v = zpowZtwo PropOneOne.isProP_two_multPadicInt (ofAdd a) (toAdd v) by
      change F.toMonoidHom v = _
      rw [hF]
      rfl, SectionThree.zpowZtwo_ofAdd] at this
    exact ofAdd.injective this
  have ha : IsUnit a := IsUnit.of_mul_eq_one (toAdd v) hav
  have hone : ztwoIota.symm (ofAdd (1 : ℤ_[2])) = ztwoOne := by
    apply ztwoIota.injective
    rw [ztwoIota.apply_symm_apply, ztwoIota_ztwoOne]
  change IsUnit (toAdd (ztwoIota (Psi ztwoOne)))
  simpa [F, a, hone] using ha

/-- Every continuous automorphism of `Ztwo` is multiplication by a `2`-adic unit in the
standard additive coordinate. -/
theorem exists_unit_scale_ztwoEquiv (Psi : ContinuousMulEquiv Ztwo Ztwo) :
    ∃ a : ℤ_[2]ˣ, ∀ z,
      toAdd (ztwoIota (Psi z)) = (a : ℤ_[2]) * toAdd (ztwoIota z) := by
  let F : ContinuousMonoidHom (Multiplicative ℤ_[2]) (Multiplicative ℤ_[2]) :=
    (ztwoIota : ContinuousMonoidHom Ztwo (Multiplicative ℤ_[2])).comp
      ((Psi : ContinuousMonoidHom Ztwo Ztwo).comp
        (ztwoIota.symm : ContinuousMonoidHom (Multiplicative ℤ_[2]) Ztwo))
  have hu : IsUnit (toAdd (F (ofAdd (1 : ℤ_[2])))) := by
    have hgen : F (ofAdd (1 : ℤ_[2])) = ztwoIota (Psi ztwoOne) := by
      change ztwoIota (Psi (ztwoIota.symm (ofAdd (1 : ℤ_[2])))) = _
      congr 2
      apply ztwoIota.injective
      rw [ztwoIota.apply_symm_apply, ztwoIota_ztwoOne]
    rw [hgen]
    exact isUnit_ztwoIota_apply_ztwoOne Psi
  refine ⟨hu.unit, fun z => ?_⟩
  have hF := mMultHom_ofAdd F.toMonoidHom F.continuous_toFun (toAdd (ztwoIota z))
  have hz : ofAdd (toAdd (ztwoIota z)) = ztwoIota z := ofAdd_toAdd _
  have hgen : toAdd (F (ofAdd (1 : ℤ_[2]))) = (hu.unit : ℤ_[2]) := hu.unit_spec.symm
  have hFz : F (ztwoIota z) = ztwoIota (Psi z) := by
    simp [F]
  rw [← hFz]
  calc
    toAdd (F (ztwoIota z)) = toAdd (F (ofAdd (toAdd (ztwoIota z)))) := by rw [hz]
    _ = toAdd (F (ofAdd (1 : ℤ_[2]))) * toAdd (ztwoIota z) := by
      have hF' : F (ofAdd (toAdd (ztwoIota z))) =
          ofAdd (toAdd (F (ofAdd (1 : ℤ_[2]))) * toAdd (ztwoIota z)) := hF
      simpa only [toAdd_ofAdd] using congrArg toAdd hF'
    _ = (hu.unit : ℤ_[2]) * toAdd (ztwoIota z) :=
      congrArg (fun w : ℤ_[2] => w * toAdd (ztwoIota z)) hgen

/-- Every surjective tame coordinate with pro-2 kernel on `GammaR` has the canonical wild
kernel. -/
theorem ker_tame_eq_wildPartR_of_surjective_of_isProP
    {n q : ℕ} {R : PWord (Generator n)} (hq2 : 2 ≤ q) (hqe : Even q)
    (hspec : TameSpecializes n q R)
    (tame : ContinuousMonoidHom (GammaR n q R) (Tq q))
    (htame : Function.Surjective tame)
    (hwild : IsProP 2 tame.toMonoidHom.ker) :
    tame.toMonoidHom.ker = wildPartR n q R := by
  apply le_antisymm
  · exact prop_3_4_one_of_spec hq2 hqe hspec _ inferInstance hwild
  · haveI : Fact (2 ≤ q) := ⟨hq2⟩
    let W : Subgroup (GammaR n q R) := wildPartR n q R
    let M : Subgroup (Tq q) := W.map tame.toMonoidHom
    haveI : W.Normal := inferInstance
    have hWn : W.Normal := inferInstance
    haveI hMn : M.Normal := Subgroup.Normal.map hWn _ htame
    have hM : M = ⊥ := by
      apply o2_Tq_eq_bot hqe
      intro G _ _ _ _ f hf
      rw [show M = W.map tame.toMonoidHom from rfl, Subgroup.map_map]
      refine SectionThree.isPGroup_map_of_isProP (isProP_wildPartR n q R) _ ?_
      rw [MonoidHom.coe_comp]
      exact hf.comp tame.continuous_toFun
    intro x hx
    have hxM : tame x ∈ M := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hM, Subgroup.mem_bot] at hxM
    exact hxM

/-- The pro-2 character induced by an automorphism of `Tq` differs from `nuTq` by a continuous
automorphism of `Ztwo`. -/
theorem exists_ztwoEquiv_nuTq_comp
    {q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
    (A : ContinuousMulEquiv (Tq q) (Tq q)) :
    ∃ U : ContinuousMulEquiv Ztwo Ztwo,
      ∀ x, U (nuTq q x) = nuTq q (A x) := by
  have hnu : (nuTq q).toMonoidHom.ker = proPKernel 2 (Tq q) := by
    apply le_antisymm (ker_nuTq_le_proPKernel hq0 hqe)
    exact proPKernel_le_ker isProP_maxProPQuotient (nuTq q)
  let g : ContinuousMonoidHom (Tq q) Ztwo :=
    (nuTq q).comp (A : ContinuousMonoidHom (Tq q) (Tq q))
  have hgker : g.toMonoidHom.ker = (nuTq q).toMonoidHom.ker := by
    rw [hnu]
    exact ker_comp_continuousMulEquiv A (nuTq q) hnu
  obtain ⟨U, hU⟩ := exists_continuousMulEquiv_of_surjective_of_ker_eq
    (nuTq q) g (nuTq_surjective q)
    ((nuTq_surjective q).comp A.surjective) hgker.symm
  exact ⟨U, hU⟩

/-- The same-kernel quotient construction with distinct target groups. -/
theorem exists_continuousMulEquiv_of_surjective_of_ker_eq_two
    {A B C : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [CompactSpace B] [T2Space B] [TotallyDisconnectedSpace B]
    [Group C] [TopologicalSpace C] [IsTopologicalGroup C]
    [CompactSpace C] [T2Space C] [TotallyDisconnectedSpace C]
    (f : ContinuousMonoidHom A B) (g : ContinuousMonoidHom A C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : f.toMonoidHom.ker = g.toMonoidHom.ker) :
    ∃ Psi : ContinuousMulEquiv B C, ∀ x, Psi (f x) = g x := by
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
      ef.symm (f x) = ef.symm (ef (QuotientGroup.mk x)) := by
        rw [quotientKerContinuousEquivOfSurjective_mk]
      _ = QuotientGroup.mk x := ef.symm_apply_apply _
  change eg (ek (ef.symm (f x))) = g x
  rw [hfinv]
  have hek : ek (QuotientGroup.mk x) = QuotientGroup.mk x :=
    quotientContinuousMulEquivOfEq_mk _ _ hker x
  rw [hek]
  exact quotientKerContinuousEquivOfSurjective_mk g hg x

/-- Two surjective compatible boundary pairs with the same two kernels differ by a core
equivalence and an automorphism of the unramified `Ztwo` coordinate. -/
theorem exists_boundary_marking_orbit
    {q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
    {Gamma P₀ P₁ : ProfiniteGrp}
    (t₀ t₁ : ContinuousMonoidHom Gamma (Tq q))
    (p₀ : ContinuousMonoidHom Gamma P₀) (p₁ : ContinuousMonoidHom Gamma P₁)
    (nu₀ : ContinuousMonoidHom P₀ Ztwo) (nu₁ : ContinuousMonoidHom P₁ Ztwo)
    (ht₀ : Function.Surjective t₀) (ht₁ : Function.Surjective t₁)
    (hp₀ : Function.Surjective p₀) (hp₁ : Function.Surjective p₁)
    (hkt : t₀.toMonoidHom.ker = t₁.toMonoidHom.ker)
    (hkp : p₀.toMonoidHom.ker = p₁.toMonoidHom.ker)
    (hc₀ : ∀ g, nuTq q (t₀ g) = nu₀ (p₀ g))
    (hc₁ : ∀ g, nuTq q (t₁ g) = nu₁ (p₁ g)) :
    ∃ Phi : ContinuousMulEquiv P₀ P₁, ∃ U : ContinuousMulEquiv Ztwo Ztwo,
      ∀ x, nu₁ (Phi x) = U (nu₀ x) := by
  obtain ⟨At, hAt⟩ := exists_continuousMulEquiv_of_surjective_of_ker_eq
    t₀ t₁ ht₀ ht₁ hkt
  obtain ⟨Phi, hPhi⟩ := exists_continuousMulEquiv_of_surjective_of_ker_eq_two
    p₀ p₁ hp₀ hp₁ hkp
  obtain ⟨U, hU⟩ := exists_ztwoEquiv_nuTq_comp hq0 hqe At
  refine ⟨Phi, U, fun x => ?_⟩
  obtain ⟨g, rfl⟩ := hp₀ x
  rw [hPhi, ← hc₁, ← hAt, ← hU, hc₀]

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- An adapted compact-M boundary with pro-2 tame kernel still forces the intrinsic field
marking to have the canonical distinguished-`C` unit pivot. -/
theorem mCompact_mobileBoundary_forces_cPivot
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (e0 : OrientedContinuousMulEquiv
      (chiM alpha h) (chiCycKTwo (K := K)))
    (D : SourceAnalyticBoundaryRN
      (mCompactAnalyticCoreRN (alpha := alpha) (h := h) (q := qOf K FF)
        halpha (qOf_ne_zero K FF) (even_qOf K FF)
        (maxProPQuotient 2 (GalK K)) isProP_maxProPQuotient
        (fieldCoreNuZtwo B)))
    (hwild : IsProP 2 D.tame.toMonoidHom.ker) :
    MFieldCPivotAtLevel B alpha 0 h := by
  let q := qOf K FF
  let hs := mTameSpecializes alpha h q (qOf_ne_zero K FF) (even_qOf K FF)
  let t0 := tameOfSpec (2 + 2 * h) q (mCompactW alpha h) hs
  let p0 := mPro2 alpha h q (by omega) (qOf_ne_zero K FF) (even_qOf K FF)
  let A := mCompactAnalyticCoreRN (alpha := alpha) (h := h) (q := q)
    halpha (qOf_ne_zero K FF) (even_qOf K FF)
    (maxProPQuotient 2 (GalK K)) isProP_maxProPQuotient (fieldCoreNuZtwo B)
  let S := SourceAnalyticCoreRN.toSource A D
  have ht0 : Function.Surjective t0 := tameOfSpec_surjective hs
  have ht1 : Function.Surjective D.tame :=
    SourceDataRN.tame_surjective_of_nuP S (fieldCoreNuZtwo_surjective B FF)
  have hp0 : Function.Surjective p0 :=
    mPro2_surjective alpha h q (by omega) (qOf_ne_zero K FF) (even_qOf K FF)
  have hp1 : Function.Surjective D.pro2 := S.pro2_surjective
  have hkt : t0.toMonoidHom.ker = D.tame.toMonoidHom.ker := by
    rw [show t0.toMonoidHom.ker = wildPartR (2 + 2 * h) q (mCompactW alpha h) from
      ker_tameOfSpec hs]
    exact (ker_tame_eq_wildPartR_of_surjective_of_isProP
      (two_le_qOf K FF) (even_qOf K FF) hs D.tame ht1 hwild).symm
  have hkp : p0.toMonoidHom.ker = D.pro2.toMonoidHom.ker := by
    rw [show p0.toMonoidHom.ker = proPKernel 2 (GammaR (2 + 2 * h) q
      (mCompactW alpha h)) from
        ker_mPro2 alpha h q (by omega) (qOf_ne_zero K FF) (even_qOf K FF)]
    exact D.ker_pro2.symm
  have hc0 : ∀ g, nuTq q (t0 g) = fieldId_mNuZtwo alpha h (by omega) (p0 g) :=
    mCompat alpha h q (by omega) (qOf_ne_zero K FF) (even_qOf K FF) hs
      (fieldId_mNuZtwo alpha h (by omega))
      (canRec_mNuZtwo_sigma alpha h (by omega))
      (canRec_mNuZtwo_wild alpha h (by omega))
  obtain ⟨Phi, U, hmark⟩ := exists_boundary_marking_orbit
    (qOf_ne_zero K FF) (even_qOf K FF)
    t0 D.tame p0 D.pro2 (fieldId_mNuZtwo alpha h (by omega))
    (fieldCoreNuZtwo B) ht0 ht1 hp0 hp1 hkt hkp hc0 D.compat
  have hrigid : MFieldOrientationRigidityAt (K := K) alpha h :=
    (mCoreOrientationCharacteristic_iff_fieldOrientationRigidityAt e0).mp
      (mCoreOrientationCharacteristic_all (by omega))
  let e : OrientedContinuousMulEquiv
      (chiM alpha h) (chiCycKTwo (K := K)) := ⟨Phi, hrigid Phi⟩
  have hu : IsUnit (toAdd (ztwoIota (U ztwoOne))) :=
    isUnit_ztwoIota_apply_ztwoOne U
  refine ⟨e, hu.unit, ?_⟩
  have hm := congrArg ztwoIota (hmark (dmC alpha h))
  rw [ztwoIota_fieldCoreNuZtwo, fieldId_mNuZtwo_dmC] at hm
  change toAdd (nuUrKTwo B (e.1 (dmC alpha h))) = _
  rw [hm, pow_zero, mul_one, hu.unit_spec]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The same orbit argument preserves every positive `2`-adic level, so an adapted displayed
Mpc boundary also forces the canonical distinguished-`C` pivot. -/
theorem mpc_mobileBoundary_forces_cPivot
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha r h : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta) (halpha : 2 ≤ alpha) (hr : 1 ≤ r)
    (e0 : OrientedContinuousMulEquiv
      (chiM alpha h) (chiCycKTwo (K := K)))
    (D : SourceAnalyticBoundaryRN
      (mpcAnalyticCoreRN (alpha := alpha) (r := r) (h := h) (q := qOf K FF)
        (epsilon := epsilon) d halpha hr (even_qOf K FF)
        (maxProPQuotient 2 (GalK K)) isProP_maxProPQuotient
        (fieldCoreNuZtwo B)))
    (hwild : IsProP 2 D.tame.toMonoidHom.ker) :
    MFieldCPivotAtLevel B alpha r h := by
  let q := qOf K FF
  let hs := Count.tameSpecializes_mpcW (qOf_ne_zero K FF) (even_qOf K FF)
    (by omega : 1 ≤ alpha) r (p epsilon r) d.display h
  let C := mpcCorePresentationDisplay alpha r (p epsilon r) h d (by omega)
  let nu0 := mpcNu alpha r (p epsilon r) h eta (by omega)
  let t0 := tameOfSpec (2 + 2 * h) q
    (mpcW alpha r (p epsilon r) d.display h) hs
  let p0 := C.coreHom (qOf_ne_zero K FF) (even_qOf K FF)
  let A := mpcAnalyticCoreRN (alpha := alpha) (r := r) (h := h) (q := q)
    (epsilon := epsilon) d halpha hr (even_qOf K FF)
    (maxProPQuotient 2 (GalK K)) isProP_maxProPQuotient (fieldCoreNuZtwo B)
  let S := SourceAnalyticCoreRN.toSource A D
  have ht0 : Function.Surjective t0 := tameOfSpec_surjective hs
  have ht1 : Function.Surjective D.tame :=
    SourceDataRN.tame_surjective_of_nuP S (fieldCoreNuZtwo_surjective B FF)
  have hp0 : Function.Surjective p0 :=
    C.coreHom_surjective (qOf_ne_zero K FF) (even_qOf K FF)
  have hp1 : Function.Surjective D.pro2 := S.pro2_surjective
  have hkt : t0.toMonoidHom.ker = D.tame.toMonoidHom.ker := by
    rw [show t0.toMonoidHom.ker = wildPartR (2 + 2 * h) q
      (mpcW alpha r (p epsilon r) d.display h) from ker_tameOfSpec hs]
    exact (ker_tame_eq_wildPartR_of_surjective_of_isProP
      (two_le_qOf K FF) (even_qOf K FF) hs D.tame ht1 hwild).symm
  have hkp : p0.toMonoidHom.ker = D.pro2.toMonoidHom.ker := by
    rw [show p0.toMonoidHom.ker = proPKernel 2 (GammaR (2 + 2 * h) q
      (mpcW alpha r (p epsilon r) d.display h)) from
        C.ker_coreHom (qOf_ne_zero K FF) (even_qOf K FF)]
    exact D.ker_pro2.symm
  have hc0 : ∀ g, nuTq q (t0 g) = nu0 (p0 g) :=
    C.nu_compat_coreHom (qOf_ne_zero K FF) (even_qOf K FF) hs nu0
      (mpcNu_sigma alpha r (p epsilon r) h eta (by omega))
      (mpcNu_wild alpha r (p epsilon r) h eta (by omega))
  obtain ⟨Phi, U, hmark⟩ := exists_boundary_marking_orbit
    (qOf_ne_zero K FF) (even_qOf K FF)
    t0 D.tame p0 D.pro2 nu0 (fieldCoreNuZtwo B)
    ht0 ht1 hp0 hp1 hkt hkp hc0 D.compat
  obtain ⟨a, hU⟩ := exists_unit_scale_ztwoEquiv U
  have hrigid : MFieldOrientationRigidityAt (K := K) alpha h :=
    (mCoreOrientationCharacteristic_iff_fieldOrientationRigidityAt e0).mp
      (mCoreOrientationCharacteristic_all (by omega))
  let e : OrientedContinuousMulEquiv
      (chiM alpha h) (chiCycKTwo (K := K)) := ⟨Phi, hrigid Phi⟩
  refine ⟨e, a, ?_⟩
  have hm := congrArg (fun z : Ztwo => toAdd (ztwoIota z)) (hmark (dmC alpha h))
  rw [ztwoIota_fieldCoreNuZtwo] at hm
  calc
    toAdd (nuUrKTwo B (e.1 (dmC alpha h))) =
        toAdd (ztwoIota (U (nu0 (dmC alpha h)))) := hm
    _ = (a : ℤ_[2]) * toAdd (ztwoIota (nu0 (dmC alpha h))) := hU _
    _ = (a : ℤ_[2]) * 2 ^ r := by
      simp [nu0, mpcNu, dmC, s]

#print axioms isUnit_ztwoIota_apply_ztwoOne
#print axioms exists_unit_scale_ztwoEquiv
#print axioms ker_tame_eq_wildPartR_of_surjective_of_isProP
#print axioms exists_ztwoEquiv_nuTq_comp
#print axioms exists_continuousMulEquiv_of_surjective_of_ker_eq_two
#print axioms exists_boundary_marking_orbit
#print axioms mCompact_mobileBoundary_forces_cPivot
#print axioms mpc_mobileBoundary_forces_cPivot

end

end GQ2.Dyadic.Instances.EvenMAdaptedBoundaryNoGo

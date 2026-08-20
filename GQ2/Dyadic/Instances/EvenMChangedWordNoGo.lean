/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMChangedWordFieldFinal
import GQ2.Dyadic.Instances.MOrientationCharacteristicFinal

/-!
# A changed even-M word does not bypass canonical pivot placement

The W334 changed-word packets are useful transport interfaces, but their existence is
still strong enough to force the canonical field pivot.  Indeed, composing the adapted
core boundary with the inverse candidate-group equivalence produces a corrected
certificate for the standard compact-M or Mpc word on the intrinsic field core.
Transporting that core back through any oriented M equivalence lets characteristic
orientation apply, forcing the distinguished C pivot.

Thus changing the word does not solve the obstructed family unless one has already solved
the underlying core-automorphism/pivot-placement problem.  This is uniform in depth and
handle count and rules out another apparent way around W323.
-/

namespace GQ2.Dyadic.Instances.EvenMChangedWordNoGo

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Instances.EvenMChangedWordCertificate
open GQ2.Dyadic.Instances.EvenMChangedWordFieldFinal
open GQ2.Dyadic.Instances.FieldFlexibleEvenMFinal
open GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate
open GQ2.Dyadic.Instances.MOrientationCharacteristicFinal
open GQ2.Dyadic.Instances.MFieldCanonicalOrientationBoundary
open GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Words.MCompact GQ2.Dyadic.Words.Mpc
open TameSpec

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [T2Space (GalK K)] in
/-- Every changed compact-M field packet still forces the canonical C pivot. -/
theorem mFieldCPivotAtLevel_zero_of_changedWordData
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (e0 : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (D : MCompactChangedWordFieldData B FF alpha h) :
    MFieldCPivotAtLevel B alpha 0 h := by
  let q := qOf K FF
  let p1 := D.core.pro2 (q := q) (qOf_ne_zero K FF) (even_qOf K FF)
  let p0 : ContinuousMonoidHom
      ((GammaR (2 + 2 * h) q (mCompactW alpha h)) : Type)
      (maxProPQuotient 2 (GalK K)) :=
    p1.comp (D.equiv.symm : ContinuousMonoidHom _ _)
  have hcompat0 : ∀ g, nuTq q
      (tameOfSpec (2 + 2 * h) q (mCompactW alpha h)
        (GQ2.Dyadic.Instances.MCompactCore.mTameSpecializes
          alpha h q (qOf_ne_zero K FF) (even_qOf K FF)) g) =
        fieldCoreNuZtwo B (p0 g) := by
    intro g
    have hg := D.core.compat (q := q) (qOf_ne_zero K FF)
      (even_qOf K FF) D.tameSpecialization (D.equiv.symm g)
    rw [DFunLike.congr_fun D.tame_eq (D.equiv.symm g)] at hg
    simpa [p0, p1] using hg
  let W0 := mCompactWordCertificateRN_of_boundary halpha
    (qOf_ne_zero K FF) (even_qOf K FF) isProP_maxProPQuotient p0
    (ker_comp_continuousMulEquiv D.equiv.symm p1
      (D.core.ker_pro2 (q := q) (qOf_ne_zero K FF) (even_qOf K FF)))
    ((D.core.hpro2 (q := q) (qOf_ne_zero K FF) (even_qOf K FF)).comp
      D.equiv.symm.surjective) hcompat0
  let nuDM : ContinuousMonoidHom (DM alpha h : Type) Ztwo :=
    (fieldCoreNuZtwo B).comp
      (e0.1 : ContinuousMonoidHom (DM alpha h : Type)
        (maxProPQuotient 2 (GalK K)))
  let M : MarkedCoreRealization (K := K) (B := B) (DM alpha h) nuDM :=
    { equiv := e0.1
      nu_equiv := fun x => ztwoIota_fieldCoreNuZtwo B (e0.1 x) }
  let Wdm : WordCertificateRN (2 + 2 * h) q (mCompactW alpha h)
      (DM alpha h) (isProP_DM alpha h) nuDM
      (standardNumerics (2 + 2 * h)) :=
    W0.genCertTransportRN (isProP_DM alpha h) e0.1.symm
      (fun x => by
        change fieldCoreNuZtwo B (e0.1 (e0.1.symm x)) = fieldCoreNuZtwo B x
        rw [e0.1.apply_symm_apply])
  exact mFieldCPivotAtLevel_zero_of_wordCertificateRN_general
    B e0 halpha (qOf_ne_zero K FF) (even_qOf K FF) nuDM M Wdm

omit [T2Space (GalK K)] in
/-- Every changed displayed-Mpc field packet still forces the canonical C pivot. -/
theorem mFieldCPivotAtLevel_of_mpcChangedWordData
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha r h : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta) (halpha : 2 ≤ alpha) (hr : 1 ≤ r)
    (e0 : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (D : MpcChangedWordFieldData B FF alpha r h epsilon d) :
    MFieldCPivotAtLevel B alpha r h := by
  let q := qOf K FF
  let R0 := mpcW alpha r (p epsilon r) d.display h
  let p1 := D.core.pro2 (q := q) (qOf_ne_zero K FF) (even_qOf K FF)
  let p0 : ContinuousMonoidHom ((GammaR (2 + 2 * h) q R0) : Type)
      (maxProPQuotient 2 (GalK K)) :=
    p1.comp (D.equiv.symm : ContinuousMonoidHom _ _)
  have hcompat0 : ∀ g, nuTq q
      (tameOfSpec (2 + 2 * h) q R0
        (Count.tameSpecializes_mpcW (qOf_ne_zero K FF) (even_qOf K FF)
          D.one_le_alpha r (p epsilon r) d.display h) g) =
        fieldCoreNuZtwo B (p0 g) := by
    intro g
    have hg := D.core.compat (q := q) (qOf_ne_zero K FF)
      (even_qOf K FF) D.tameSpecialization (D.equiv.symm g)
    rw [DFunLike.congr_fun D.tame_eq (D.equiv.symm g)] at hg
    simpa [p0, p1, R0] using hg
  let W0 := mpcWordCertificateRN_of_boundary d halpha hr
    (qOf_ne_zero K FF) (even_qOf K FF) isProP_maxProPQuotient p0
    (ker_comp_continuousMulEquiv D.equiv.symm p1
      (D.core.ker_pro2 (q := q) (qOf_ne_zero K FF) (even_qOf K FF)))
    ((D.core.hpro2 (q := q) (qOf_ne_zero K FF) (even_qOf K FF)).comp
      D.equiv.symm.surjective) hcompat0
  let nuDM : ContinuousMonoidHom (DM alpha h : Type) Ztwo :=
    (fieldCoreNuZtwo B).comp
      (e0.1 : ContinuousMonoidHom (DM alpha h : Type)
        (maxProPQuotient 2 (GalK K)))
  let M : MarkedCoreRealization (K := K) (B := B) (DM alpha h) nuDM :=
    { equiv := e0.1
      nu_equiv := fun x => ztwoIota_fieldCoreNuZtwo B (e0.1 x) }
  let Wdm : WordCertificateRN (2 + 2 * h) q R0
      (DM alpha h) (isProP_DM alpha h) nuDM
      (standardNumerics (2 + 2 * h)) :=
    W0.genCertTransportRN (isProP_DM alpha h) e0.1.symm
      (fun x => by
        change fieldCoreNuZtwo B (e0.1 (e0.1.symm x)) = fieldCoreNuZtwo B x
        rw [e0.1.apply_symm_apply])
  exact mFieldCPivotAtLevel_of_mpcWordCertificateRN_general
    B d e0 halpha hr (qOf_ne_zero K FF) (even_qOf K FF) nuDM M Wdm

omit [T2Space (GalK K)] in
/-- Without the compact-M C pivot there is no changed-word packet of W334's shape. -/
theorem not_mCompactChangedWordFieldData_of_not_cPivot
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (e0 : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (hnot : ¬ MFieldCPivotAtLevel B alpha 0 h) :
    ¬ Nonempty (MCompactChangedWordFieldData B FF alpha h) := by
  rintro ⟨D⟩
  exact hnot (mFieldCPivotAtLevel_zero_of_changedWordData B FF halpha e0 D)

#print axioms mFieldCPivotAtLevel_zero_of_changedWordData
#print axioms mFieldCPivotAtLevel_of_mpcChangedWordData
#print axioms not_mCompactChangedWordFieldData_of_not_cPivot

end

end GQ2.Dyadic.Instances.EvenMChangedWordNoGo

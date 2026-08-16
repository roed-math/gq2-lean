/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcCandidateRN
import GQ2.Dyadic.Instances.CanonicalRecords
import GQ2.Dyadic.Instances.MpcPivot

/-!
# Corrected procyclic-M final endpoints

The full procyclic-M Stokes certificate leaves the affine determinant as the sole analytic
candidate premise.  This file transports the resulting corrected word certificate through a
generic tied branch and records the two canonical quadratic endpoints.  The `sqrt(10)` selector
is unconditional; the tied `sqrt(-10)` selector retains exactly `MpcPivShift 2`.
-/

namespace GQ2.Dyadic.Instances.MpcCandidateFinal

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Instances.MProcyclicCore
open GQ2.Dyadic.Instances.MpcCandidateRN
open GQ2.Dyadic.Instances.CanonicalRecords
open GQ2.Dyadic.Instances.MpcPiv
open GQ2.Dyadic.Fields GQ2.Dyadic.MarkedCore GQ2.Dyadic.TameSpec

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {R : LocalReciprocity}

/-- The determinant-only corrected Mpc residual feeds the general RN assembly at any tied
branch. -/
theorem mpc_candidate_equiv_galKRN_of_tied_determinant
    {alpha r : ℕ} {epsilon : Bool}
    {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
    [T2Space (GalK K)] (B : MarkedRecip R K) {FF : DyadicUnitFiltration K}
    (G : GenAsmBranch K B) (hα : 2 ≤ alpha) (hα1 : 1 ≤ alpha) (hr : 1 ≤ r)
    (hp : G.pres = .Mpc alpha r epsilon .one 0)
    (hnu : HEq G.nuP (mpcNu alpha r (p epsilon r) hα1))
    (F : GenAsmFieldInputs K B FF G.degree)
    (determinant : AffineDeterminantCertificate
      (GammaR 2 (qOf K FF) (mpcW alpha r (p epsilon r) .one 0)) 2 (qOf K FF)
      (DM alpha 0) (mpcNu alpha r (p epsilon r) hα1) (standardNumerics 2)
      (tameOfSpec 2 (qOf K FF) (mpcW alpha r (p epsilon r) .one 0)
        (mpcTameSpecializes alpha r (p epsilon r) (qOf K FF) hα1
          (qOf_ne_zero K FF) (even_qOf K FF)))
      (mpcPro2 alpha r (p epsilon r) (qOf K FF) hα1
        (qOf_ne_zero K FF) (even_qOf K FF))
      (mpcCompat alpha r (p epsilon r) (qOf K FF) hα1
        (qOf_ne_zero K FF) (even_qOf K FF)
        (mpcTameSpecializes alpha r (p epsilon r) (qOf K FF) hα1
          (qOf_ne_zero K FF) (even_qOf K FF))
        (mpcNu alpha r (p epsilon r) hα1)
        (mpcNu_sigma alpha r (p epsilon r) hα1)
        (mpcNu_wild alpha r (p epsilon r) hα1))
      (scalarActionZmodTwo _)) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup G.degree (qOf K FF) G.word : ProfiniteGrp) : Type) (GalK K)) := by
  obtain ⟨S⟩ := mpcRowResidualRN_of_tied_determinant
    B G hα hα1 hr hp hnu determinant
  exact genAsm_candidate_equiv_galKRN G F S

/-- The unconditional tied sqrt(10) selector acquires the corrected residual from determinant
data alone. -/
theorem mpc_rowResidualRN_sqrtTen [T2Space (GalK KSqrtTen)]
    (B : MarkedRecip R KSqrtTen) {FF : DyadicUnitFiltration KSqrtTen}
    (determinant : AffineDeterminantCertificate
      (GammaR 2 (qOf KSqrtTen FF) (mpcW 2 1 (p false 1) .one 0)) 2
      (qOf KSqrtTen FF) (DM 2 0) (mpcNu 2 1 (p false 1) (by omega))
      (standardNumerics 2)
      (tameOfSpec 2 (qOf KSqrtTen FF) (mpcW 2 1 (p false 1) .one 0)
        (mpcTameSpecializes 2 1 (p false 1) (qOf KSqrtTen FF) (by omega)
          (qOf_ne_zero KSqrtTen FF) (even_qOf KSqrtTen FF)))
      (mpcPro2 2 1 (p false 1) (qOf KSqrtTen FF) (by omega)
        (qOf_ne_zero KSqrtTen FF) (even_qOf KSqrtTen FF))
      (mpcCompat 2 1 (p false 1) (qOf KSqrtTen FF) (by omega)
        (qOf_ne_zero KSqrtTen FF) (even_qOf KSqrtTen FF)
        (mpcTameSpecializes 2 1 (p false 1) (qOf KSqrtTen FF) (by omega)
          (qOf_ne_zero KSqrtTen FF) (even_qOf KSqrtTen FF))
        (mpcNu 2 1 (p false 1) (by omega))
        (mpcNu_sigma 2 1 (p false 1) (by omega))
        (mpcNu_wild 2 1 (p false 1) (by omega)))
      (scalarActionZmodTwo _)) :
    ∃ G : GenAsmBranch KSqrtTen B, G.pres = .Mpc 2 1 false .one 0 ∧
      Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  obtain ⟨G, hp, hnu⟩ := canRec_branch_sqrtTen B
  refine ⟨G, hp, ?_⟩
  exact mpcRowResidualRN_of_tied_determinant
    B G (le_refl 2) (by omega) (le_refl 1) hp hnu determinant

/-- The corrected sqrt(10) candidate presents its Galois group once its determinant is
supplied. -/
theorem mpc_candidate_equiv_galKRN_sqrtTen [T2Space (GalK KSqrtTen)]
    (B : MarkedRecip R KSqrtTen) {FF : DyadicUnitFiltration KSqrtTen}
    (F : GenAsmFieldInputs KSqrtTen B FF
      (SelectedPresentation.Mpc 2 1 false .one 0).degree)
    (determinant : AffineDeterminantCertificate
      (GammaR 2 (qOf KSqrtTen FF) (mpcW 2 1 (p false 1) .one 0)) 2
      (qOf KSqrtTen FF) (DM 2 0) (mpcNu 2 1 (p false 1) (by omega))
      (standardNumerics 2)
      (tameOfSpec 2 (qOf KSqrtTen FF) (mpcW 2 1 (p false 1) .one 0)
        (mpcTameSpecializes 2 1 (p false 1) (qOf KSqrtTen FF) (by omega)
          (qOf_ne_zero KSqrtTen FF) (even_qOf KSqrtTen FF)))
      (mpcPro2 2 1 (p false 1) (qOf KSqrtTen FF) (by omega)
        (qOf_ne_zero KSqrtTen FF) (even_qOf KSqrtTen FF))
      (mpcCompat 2 1 (p false 1) (qOf KSqrtTen FF) (by omega)
        (qOf_ne_zero KSqrtTen FF) (even_qOf KSqrtTen FF)
        (mpcTameSpecializes 2 1 (p false 1) (qOf KSqrtTen FF) (by omega)
          (qOf_ne_zero KSqrtTen FF) (even_qOf KSqrtTen FF))
        (mpcNu 2 1 (p false 1) (by omega))
        (mpcNu_sigma 2 1 (p false 1) (by omega))
        (mpcNu_wild 2 1 (p false 1) (by omega)))
      (scalarActionZmodTwo _)) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (SelectedPresentation.Mpc 2 1 false .one 0).degree
        (qOf KSqrtTen FF) (SelectedPresentation.Mpc 2 1 false .one 0).word :
        ProfiniteGrp) : Type) (GalK KSqrtTen)) := by
  obtain ⟨G, hp, ⟨S⟩⟩ := mpc_rowResidualRN_sqrtTen B determinant
  obtain ⟨pres, hdeg, nu, hnuP, realization⟩ := G
  subst hp
  exact genAsm_candidate_equiv_galKRN
    { pres := .Mpc 2 1 false .one 0
      hdeg := hdeg
      nuP := nu
      hnuP := hnuP
      realization := realization }
    F S

/-- The sqrt(-10) tied selector has exactly the pivot-shift premise; after selection, only the
determinant remains analytic. -/
theorem mpc_rowResidualRN_sqrtNegTen [T2Space (GalK KSqrtNegTen)]
    (hshift : MpcPivShift 2) (B : MarkedRecip R KSqrtNegTen)
    {FF : DyadicUnitFiltration KSqrtNegTen}
    (determinant : AffineDeterminantCertificate
      (GammaR 2 (qOf KSqrtNegTen FF) (mpcW 2 1 (p true 1) .one 0)) 2
      (qOf KSqrtNegTen FF) (DM 2 0) (mpcNu 2 1 (p true 1) (by omega))
      (standardNumerics 2)
      (tameOfSpec 2 (qOf KSqrtNegTen FF) (mpcW 2 1 (p true 1) .one 0)
        (mpcTameSpecializes 2 1 (p true 1) (qOf KSqrtNegTen FF) (by omega)
          (qOf_ne_zero KSqrtNegTen FF) (even_qOf KSqrtNegTen FF)))
      (mpcPro2 2 1 (p true 1) (qOf KSqrtNegTen FF) (by omega)
        (qOf_ne_zero KSqrtNegTen FF) (even_qOf KSqrtNegTen FF))
      (mpcCompat 2 1 (p true 1) (qOf KSqrtNegTen FF) (by omega)
        (qOf_ne_zero KSqrtNegTen FF) (even_qOf KSqrtNegTen FF)
        (mpcTameSpecializes 2 1 (p true 1) (qOf KSqrtNegTen FF) (by omega)
          (qOf_ne_zero KSqrtNegTen FF) (even_qOf KSqrtNegTen FF))
        (mpcNu 2 1 (p true 1) (by omega))
        (mpcNu_sigma 2 1 (p true 1) (by omega))
        (mpcNu_wild 2 1 (p true 1) (by omega)))
      (scalarActionZmodTwo _)) :
    ∃ G : GenAsmBranch KSqrtNegTen B, G.pres = .Mpc 2 1 true .one 0 ∧
      Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  obtain ⟨G, hp, hnu⟩ := mpcPiv_genAsmBranch_sqrtNegTen_of_shift hshift B
  refine ⟨G, hp, ?_⟩
  exact mpcRowResidualRN_of_tied_determinant
    B G (le_refl 2) (by omega) (le_refl 1) hp hnu determinant

/-- Under the exact pivot-shift selector premise, the corrected sqrt(-10) candidate presents
its Galois group once its determinant is supplied. -/
theorem mpc_candidate_equiv_galKRN_sqrtNegTen [T2Space (GalK KSqrtNegTen)]
    (hshift : MpcPivShift 2) (B : MarkedRecip R KSqrtNegTen)
    {FF : DyadicUnitFiltration KSqrtNegTen}
    (F : GenAsmFieldInputs KSqrtNegTen B FF
      (SelectedPresentation.Mpc 2 1 true .one 0).degree)
    (determinant : AffineDeterminantCertificate
      (GammaR 2 (qOf KSqrtNegTen FF) (mpcW 2 1 (p true 1) .one 0)) 2
      (qOf KSqrtNegTen FF) (DM 2 0) (mpcNu 2 1 (p true 1) (by omega))
      (standardNumerics 2)
      (tameOfSpec 2 (qOf KSqrtNegTen FF) (mpcW 2 1 (p true 1) .one 0)
        (mpcTameSpecializes 2 1 (p true 1) (qOf KSqrtNegTen FF) (by omega)
          (qOf_ne_zero KSqrtNegTen FF) (even_qOf KSqrtNegTen FF)))
      (mpcPro2 2 1 (p true 1) (qOf KSqrtNegTen FF) (by omega)
        (qOf_ne_zero KSqrtNegTen FF) (even_qOf KSqrtNegTen FF))
      (mpcCompat 2 1 (p true 1) (qOf KSqrtNegTen FF) (by omega)
        (qOf_ne_zero KSqrtNegTen FF) (even_qOf KSqrtNegTen FF)
        (mpcTameSpecializes 2 1 (p true 1) (qOf KSqrtNegTen FF) (by omega)
          (qOf_ne_zero KSqrtNegTen FF) (even_qOf KSqrtNegTen FF))
        (mpcNu 2 1 (p true 1) (by omega))
        (mpcNu_sigma 2 1 (p true 1) (by omega))
        (mpcNu_wild 2 1 (p true 1) (by omega)))
      (scalarActionZmodTwo _)) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (SelectedPresentation.Mpc 2 1 true .one 0).degree
        (qOf KSqrtNegTen FF) (SelectedPresentation.Mpc 2 1 true .one 0).word :
        ProfiniteGrp) : Type) (GalK KSqrtNegTen)) := by
  obtain ⟨G, hp, ⟨S⟩⟩ := mpc_rowResidualRN_sqrtNegTen hshift B determinant
  obtain ⟨pres, hdeg, nu, hnuP, realization⟩ := G
  subst hp
  exact genAsm_candidate_equiv_galKRN
    { pres := .Mpc 2 1 true .one 0
      hdeg := hdeg
      nuP := nu
      hnuP := hnuP
      realization := realization }
    F S

#print axioms mpc_candidate_equiv_galKRN_of_tied_determinant
#print axioms mpc_rowResidualRN_sqrtTen
#print axioms mpc_candidate_equiv_galKRN_sqrtTen
#print axioms mpc_rowResidualRN_sqrtNegTen
#print axioms mpc_candidate_equiv_galKRN_sqrtNegTen

end

end GQ2.Dyadic.Instances.MpcCandidateFinal

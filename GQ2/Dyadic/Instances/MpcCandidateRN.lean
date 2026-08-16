import GQ2.Dyadic.Instances.MpcCandidateScalar

/-!
# Corrected procyclic-M candidate scaffolding

This module assembles a corrected procyclic-M word certificate once the full
Stokes-duality and affine-determinant certificates are supplied, and transports
that certificate to a field branch already tied to the canonical marking.
-/

namespace GQ2.Dyadic.Instances.MpcCandidateRN

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.MProcyclicExact
open GQ2.Dyadic.Count.PilotN
open GQ2.CardH2GammaA
open GQ2.Dyadic.Instances.MProcyclicCore
open GQ2.Dyadic.Instances.MpcCandidateScalar
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.TameSpec

/-- A corrected procyclic-M word certificate with exact lifting and scalar count discharged. -/
noncomputable def mpcWordCertificateRN_of_stokes_determinant
    (alpha r q : ℕ) (epsilon : Bool) (hα : 2 ≤ alpha) (hα1 : 1 ≤ alpha) (hr : 1 ≤ r)
    (hq0 : q ≠ 0) (hqe : Even q)
    (stokes : StokesDualityCertificate
      (GammaR 2 q (mpcW alpha r (p epsilon r) .one 0)) 2 q (DM alpha 0)
      (mpcNu alpha r (p epsilon r) hα1) (standardNumerics 2)
      (scalarActionZmodTwo _))
    (determinant : AffineDeterminantCertificate
      (GammaR 2 q (mpcW alpha r (p epsilon r) .one 0)) 2 q (DM alpha 0)
      (mpcNu alpha r (p epsilon r) hα1) (standardNumerics 2)
      (tameOfSpec 2 q (mpcW alpha r (p epsilon r) .one 0)
        (mpcTameSpecializes alpha r (p epsilon r) q hα1 hq0 hqe))
      (mpcPro2 alpha r (p epsilon r) q hα1 hq0 hqe)
      (mpcCompat alpha r (p epsilon r) q hα1 hq0 hqe
        (mpcTameSpecializes alpha r (p epsilon r) q hα1 hq0 hqe)
        (mpcNu alpha r (p epsilon r) hα1)
        (mpcNu_sigma alpha r (p epsilon r) hα1)
        (mpcNu_wild alpha r (p epsilon r) hα1))
      (scalarActionZmodTwo _)) :
    WordCertificateRN 2 q (mpcW alpha r (p epsilon r) .one 0) (DM alpha 0)
      (isProP_DM alpha 0) (mpcNu alpha r (p epsilon r) hα1)
      (standardNumerics 2) where
  tameSpecialization := mpcTameSpecializes alpha r (p epsilon r) q hα1 hq0 hqe
  coreRel := mpcCoreRel alpha r (p epsilon r)
  proTwoWord := fun G _ _ _ _ _ t ↦ mpcProTwoWord alpha r (p epsilon r) hα1 G t
  pro2 := mpcPro2 alpha r (p epsilon r) q hα1 hq0 hqe
  ker_pro2 := ker_mpcPro2 alpha r (p epsilon r) q hα1 hq0 hqe
  hpro2 := mpcPro2_surjective alpha r (p epsilon r) q hα1 hq0 hqe
  compat := mpcCompat alpha r (p epsilon r) q hα1 hq0 hqe
    (mpcTameSpecializes alpha r (p epsilon r) q hα1 hq0 hqe)
    (mpcNu alpha r (p epsilon r) hα1)
    (mpcNu_sigma alpha r (p epsilon r) hα1)
    (mpcNu_wild alpha r (p epsilon r) hα1)
  tfg := Count.gammaR_topologicallyFinitelyGenerated _ _ _
  smulZmod2 := scalarActionZmodTwo _
  contSMulZmod2 := scalarActionZmodTwo_continuousSMul _
  htriv := scalarActionZmodTwo_triv _
  exactLifting := by
    have H := RecordBlocks.recBl_mpc_exactLiftingRN
      (alpha := alpha) (r := r) (q := q) (epsilon := epsilon) (h := 0)
      MpcDisplayFor.one hα hr hqe
      (mpcNu alpha r (p epsilon r) hα1)
    rw [MProcyclicExact.gamma_sign_eq_display alpha r 0 q epsilon MpcDisplayFor.one] at H
    change ExactLiftingSemanticsRN
      (GammaR 2 q (mpcW alpha r (p epsilon r) .one 0)) 2 q (DM alpha 0)
        (mpcNu alpha r (p epsilon r) hα1) (standardNumerics 2) at H
    exact H
  stokes := stokes
  scalar := by
    have H := mpcCandidate_scalar (alpha := alpha) (r := r) (pp := p epsilon r)
      (h := 0) (q := q) MpcDisplayFor.one hα hr hqe
    change ScalarHilbertCertificate
      (GammaR 2 q (mpcW alpha r (p epsilon r) .one 0)) 2
        (standardNumerics 2) (scalarActionZmodTwo _) at H
    exact H
  determinant := determinant
  htame := Count.htame_of_tameSpecializes
    (mpcTameSpecializes alpha r (p epsilon r) q hα1 hq0 hqe)
  hwild := Count.hwild_of_tameSpecializes
    (mpcTameSpecializes alpha r (p epsilon r) q hα1 hq0 hqe)

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {R : LocalReciprocity}

/-- Any branch already tied to the canonical Mpc marking gets the corrected residual. -/
theorem mpcRowResidualRN_of_tied
    {alpha r : ℕ} {epsilon : Bool}
    {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
    (B : MarkedRecip R K) {FF : DyadicUnitFiltration K} (G : GenAsmBranch K B)
    (hα : 2 ≤ alpha) (hα1 : 1 ≤ alpha) (hr : 1 ≤ r)
    (hp : G.pres = .Mpc alpha r epsilon .one 0)
    (hnu : HEq G.nuP (mpcNu alpha r (p epsilon r) hα1))
    (stokes : StokesDualityCertificate
      (GammaR 2 (qOf K FF) (mpcW alpha r (p epsilon r) .one 0)) 2 (qOf K FF)
      (DM alpha 0) (mpcNu alpha r (p epsilon r) hα1) (standardNumerics 2)
      (scalarActionZmodTwo _))
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
    Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  obtain ⟨pres, hdeg, nu, hnuP, realization⟩ := G
  subst hp
  obtain rfl : nu = mpcNu alpha r (p epsilon r) hα1 := eq_of_heq hnu
  exact ⟨⟨mpcWordCertificateRN_of_stokes_determinant alpha r (qOf K FF) epsilon
    hα hα1 hr (qOf_ne_zero K FF) (even_qOf K FF) stokes determinant⟩⟩

#print axioms mpcWordCertificateRN_of_stokes_determinant
#print axioms mpcRowResidualRN_of_tied

end


end GQ2.Dyadic.Instances.MpcCandidateRN

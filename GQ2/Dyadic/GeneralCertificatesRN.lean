import GQ2.Dyadic.GeneralCertificates
import GQ2.Dyadic.SourceDataRN

/-!
# Core transport for corrected word certificates

The frozen certificate API already transports its cohomological clauses across a
marking-compatible equivalence of pro-2 cores.  This module supplies the corrected RN analogue.
The extra `zRN` coefficient is independent of the core, so the existing pullback maps transport
the exact-lifting, Stokes, scalar, and determinant clauses without a new analytic argument.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open TameSpec MarkedCore

section ClauseTransportRN

variable {q : ℕ} {P₁ P₂ : ProfiniteGrp} {nu₁ : ContinuousMonoidHom P₁ Ztwo}
  {nu₂ : ContinuousMonoidHom P₂ Ztwo} {n : ℕ} {SN : SourceNumerics n} {Gam : ProfiniteGrp}
  (e : ContinuousMulEquiv (P₁ : Type) (P₂ : Type)) (hnu : ∀ x, nu₂ (e x) = nu₁ x)

include hnu in
/-- The corrected exact-lifting clause transports along a marking-compatible core equivalence. -/
theorem genCert_exactLiftingSemanticsRN_pull
    (Hyp : ExactLiftingSemanticsRN Gam n q P₁ nu₁ SN) :
    ExactLiftingSemanticsRN Gam n q P₂ nu₂ SN := by
  refine ⟨fun RF b F r => ?_, Hyp.2.1, fun hE2 hRK hR2 b F => ?_⟩
  · exact Hyp.1 RF (genCertBdPull e hnu b) (genCertFramePull (genCertHomOfEquiv e) F)
      ((genCertBdLiftEquiv (genCertFrameMap_pull e hnu F b) RF.TC).symm r)
  · have h := Hyp.2.2 hE2 hRK hR2 (genCertBdPull e hnu b)
      (genCertFramePull (genCertHomOfEquiv e) F)
    simpa only [genCert_exactImageCountK_congr (genCertFrameMap_pull e hnu F b),
      genCert_mBK_congr (genCertFrameMap_pull e hnu F b)] using h

end ClauseTransportRN

section RecordTransportRN

variable {n q : ℕ} {R : PWord (Generator n)} {P₁ P₂ : ProfiniteGrp}
  {hP₁ : IsProP 2 P₁} {nu₁ : ContinuousMonoidHom P₁ Ztwo}
  {nu₂ : ContinuousMonoidHom P₂ Ztwo} {SN : SourceNumerics n}

/-- Transport a corrected word certificate along a marking-compatible equivalence of cores. -/
noncomputable def WordCertificateRN.genCertTransportRN
    (W : WordCertificateRN n q R P₁ hP₁ nu₁ SN)
    (hP₂ : IsProP 2 P₂) (e : ContinuousMulEquiv (P₁ : Type) (P₂ : Type))
    (hnu : ∀ x, nu₂ (e x) = nu₁ x) : WordCertificateRN n q R P₂ hP₂ nu₂ SN where
  tameSpecialization := W.tameSpecialization
  coreRel := W.coreRel
  proTwoWord := W.proTwoWord
  pro2 := (genCertHomOfEquiv e).comp W.pro2
  ker_pro2 := by
    rw [← W.ker_pro2]
    ext g
    simp only [MonoidHom.mem_ker]
    constructor
    · intro hg
      have h1 : e (W.pro2 g) = 1 := hg
      have h2 := congrArg e.symm h1
      rwa [e.symm_apply_apply, map_one] at h2
    · intro hg
      have h1 : W.pro2 g = 1 := hg
      show e (W.pro2 g) = 1
      rw [h1, map_one]
  hpro2 := e.surjective.comp W.hpro2
  compat := genCertCompat e hnu W.compat
  tfg := W.tfg
  smulZmod2 := W.smulZmod2
  contSMulZmod2 := W.contSMulZmod2
  htriv := W.htriv
  exactLifting := genCert_exactLiftingSemanticsRN_pull e hnu W.exactLifting
  stokes := genCert_stokes_pull e hnu W.smulZmod2 W.stokes
  scalar := W.scalar
  determinant := genCert_determinant_pull e hnu W.smulZmod2 W.determinant
  htame := W.htame
  hwild := W.hwild

end RecordTransportRN

#print axioms genCert_exactLiftingSemanticsRN_pull
#print axioms WordCertificateRN.genCertTransportRN

end

end GQ2.Dyadic

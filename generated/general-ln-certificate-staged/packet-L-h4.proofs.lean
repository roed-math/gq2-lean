import GQ2.Dyadic.Word.GeneralTemplateLN
import GQ2.Dyadic.Word.GeneralTemplateLNCanonical
import GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary
import GQ2.Dyadic.Words.L
import GQ2.Dyadic.Certificates.LFox
import GQ2.Dyadic.Certificates.LJacobian
import GQ2.Dyadic.Certificates.L
import GQ2.Dyadic.Instances.GammaLReconstruction
import GQ2.Dyadic.Instances.GammaLAnalyticLeaves
import GQ2.Dyadic.Instances.GammaLSourceArfGeneral
import GQ2.Dyadic.Instances.GammaLOddDegreeGrandAssembly
import GQ2.Dyadic.Instances.LHessianCertificates
import GQ2.Dyadic.Instances.LBoundaryHessianCertificates

open Lean

private def packetPins : List Name := [
  ``GQ2.Dyadic.Certificates.LSq.foxD_lSq_ram
  , ``GQ2.Dyadic.Certificates.LSq.foxD_lSq_unram
  , ``GQ2.Dyadic.Certificates.LSq.lSqJacobianCertRam
  , ``GQ2.Dyadic.Certificates.LSq.lSqJacobianCertScalar
  , ``GQ2.Dyadic.Certificates.LSq.lSqJacobianCertUnram
  , ``GQ2.Dyadic.Certificates.LSq.lSqRamNormalForm
  , ``GQ2.Dyadic.Certificates.LSq.lSqRamOps
  , ``GQ2.Dyadic.Certificates.LSq.lSqUnramNormalForm
  , ``GQ2.Dyadic.Certificates.LSqStokes.hessRelZ_lSq
  , ``GQ2.Dyadic.GeneralTemplateLN.canon_rawLsq
  , ``GQ2.Dyadic.GeneralTemplateLN.denote_canon_rawLsq
  , ``GQ2.Dyadic.GeneralTemplateLN.denote_rawLsq
  , ``GQ2.Dyadic.Instances.LBoundaryHessianCertificates.lBoundaryHessian
  , ``GQ2.Dyadic.Instances.LHessianCertificates.ramifiedHessian
  , ``GQ2.Dyadic.Instances.LHessianCertificates.ramifiedHessian_baseSign
  , ``GQ2.Dyadic.Instances.LHessianCertificates.unramifiedHessian
  , ``GQ2.Dyadic.Instances.LHessianCertificates.unramifiedHessian_baseSign
  , ``GQ2.Dyadic.LSquare.determinantResidue_lSq_pow
  , ``GQ2.Dyadic.LSquare.lCanonicalTameSpecialization
  , ``GQ2.Dyadic.LSquare.lSquareAnalyticLeavesRN_pow
  , ``GQ2.Dyadic.LSquare.stokesDualityCertificate_of_actionImage
  , ``GQ2.Dyadic.LSquare.wordCertificateRN_lSq_pow
  , ``GQ2.Dyadic.LSquare.wordCertificateRN_lSq_qOf
  , ``GQ2.Dyadic.Words.LSq.eval_pro2_lSqW_eq_sqRelWord
  , ``GQ2.Dyadic.Words.LSq.lSqW
  , ``GQ2.Dyadic.Words.LSq.rawLsq
  , ``GQ2.Dyadic.Words.LSq.wf_rawLsq
  ]

private def standingPins : List Name := [
  ``GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary.hasSelectedRowResidualRN_l
  ]

run_cmd do
  let env ← getEnv
  for decl in packetPins do
    unless env.contains decl do
      throwError "packet declaration missing: {decl}"
    let axioms ← collectAxioms decl
    let extra := axioms.filter (fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a))
    unless extra.isEmpty do
      throwError "packet nonstandard axioms: {decl}: {extra}"
    IO.println s!"PACKET_PIN_OK|{decl}|{axioms.size}"
  for decl in standingPins do
    unless env.contains decl do
      throwError "packet standing declaration missing: {decl}"
    let axioms ← collectAxioms decl
    let extra := axioms.filter (fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a))
    IO.println s!"PACKET_STANDING_PIN|{decl}|{extra.size}|{extra}"
  IO.println s!"LN_PACKET_PROOF_REPLAY_PASS|{packetPins.length}|{standingPins.length}"

#check @GQ2.Dyadic.Certificates.LSq.foxD_lSq_ram
#check @GQ2.Dyadic.Certificates.LSq.foxD_lSq_unram
#check @GQ2.Dyadic.Certificates.LSq.lSqJacobianCertRam
#check @GQ2.Dyadic.Certificates.LSq.lSqJacobianCertScalar
#check @GQ2.Dyadic.Certificates.LSq.lSqJacobianCertUnram
#check @GQ2.Dyadic.Certificates.LSq.lSqRamNormalForm
#check @GQ2.Dyadic.Certificates.LSq.lSqRamOps
#check @GQ2.Dyadic.Certificates.LSq.lSqUnramNormalForm
#check @GQ2.Dyadic.Certificates.LSqStokes.hessRelZ_lSq
#check @GQ2.Dyadic.GeneralTemplateLN.canon_rawLsq
#check @GQ2.Dyadic.GeneralTemplateLN.denote_canon_rawLsq
#check @GQ2.Dyadic.GeneralTemplateLN.denote_rawLsq
#check @GQ2.Dyadic.Instances.LBoundaryHessianCertificates.lBoundaryHessian
#check @GQ2.Dyadic.Instances.LHessianCertificates.ramifiedHessian
#check @GQ2.Dyadic.Instances.LHessianCertificates.ramifiedHessian_baseSign
#check @GQ2.Dyadic.Instances.LHessianCertificates.unramifiedHessian
#check @GQ2.Dyadic.Instances.LHessianCertificates.unramifiedHessian_baseSign
#check @GQ2.Dyadic.LSquare.determinantResidue_lSq_pow
#check @GQ2.Dyadic.LSquare.lCanonicalTameSpecialization
#check @GQ2.Dyadic.LSquare.lSquareAnalyticLeavesRN_pow
#check @GQ2.Dyadic.LSquare.stokesDualityCertificate_of_actionImage
#check @GQ2.Dyadic.LSquare.wordCertificateRN_lSq_pow
#check @GQ2.Dyadic.LSquare.wordCertificateRN_lSq_qOf
#check @GQ2.Dyadic.Words.LSq.eval_pro2_lSqW_eq_sqRelWord
#check @GQ2.Dyadic.Words.LSq.lSqW
#check @GQ2.Dyadic.Words.LSq.rawLsq
#check @GQ2.Dyadic.Words.LSq.wf_rawLsq
#check @GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary.hasSelectedRowResidualRN_l

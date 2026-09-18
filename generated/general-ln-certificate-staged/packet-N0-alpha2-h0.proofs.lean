import GQ2.Dyadic.Word.GeneralTemplateLN
import GQ2.Dyadic.Word.GeneralTemplateLNCanonical
import GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary
import GQ2.Dyadic.Words.N0
import GQ2.Dyadic.GeneralCertificates
import GQ2.Dyadic.Certificates.N0Fox
import GQ2.Dyadic.Certificates.N0
import GQ2.Dyadic.Instances.WordPhase
import GQ2.Dyadic.Instances.WordPhaseCompactNFinal
import GQ2.Dyadic.Instances.CompactNHessianCertificates
import GQ2.Dyadic.Instances.CompactNBoundaryHessianCertificates

open Lean

private def packetPins : List Name := [
  ``GQ2.Dyadic.Certificates.foxD_nCompact_ram
  , ``GQ2.Dyadic.Certificates.foxD_nCompact_unram
  , ``GQ2.Dyadic.Certificates.hessRelZ_nCompact
  , ``GQ2.Dyadic.Certificates.nCompactJacobianCertRam
  , ``GQ2.Dyadic.Certificates.nCompactJacobianCertUnram
  , ``GQ2.Dyadic.Certificates.nCompactRamNormalForm
  , ``GQ2.Dyadic.Certificates.nCompactRamOps
  , ``GQ2.Dyadic.Certificates.nCompactUnramNormalForm
  , ``GQ2.Dyadic.Certificates.nCompactUnramOps
  , ``GQ2.Dyadic.GeneralTemplateLN.canon_rawNCompact
  , ``GQ2.Dyadic.GeneralTemplateLN.denote_canon_rawNCompact
  , ``GQ2.Dyadic.GeneralTemplateLN.denote_rawNCompact
  , ``GQ2.Dyadic.Instances.CompactNBoundaryHessianCertificates.compactNBoundaryHessian
  , ``GQ2.Dyadic.Instances.CompactNHessianCertificates.compactNRamifiedComparison_add
  , ``GQ2.Dyadic.Instances.CompactNHessianCertificates.compactNRamifiedHessian
  , ``GQ2.Dyadic.Instances.CompactNHessianCertificates.compactNUnramifiedComparison_add
  , ``GQ2.Dyadic.Instances.CompactNHessianCertificates.compactNUnramifiedHessian
  , ``GQ2.Dyadic.Instances.WordPhase.wPh_nCand_stokes
  , ``GQ2.Dyadic.Instances.WordPhaseCompactNFinal.wPcNWordCertificateRN
  , ``GQ2.Dyadic.Instances.WordPhaseCompactNFinal.wPcN_affineDeterminantCertificate
  , ``GQ2.Dyadic.Words.eval_pro2_nCompact
  , ``GQ2.Dyadic.Words.nCompactW
  , ``GQ2.Dyadic.Words.pro2_nCompact
  , ``GQ2.Dyadic.Words.rawNCompact
  , ``GQ2.Dyadic.Words.wf_rawNCompact
  , ``GQ2.Dyadic.genCertNProTwoWord
  , ``GQ2.Dyadic.genCertNTameSpecializes
  ]

private def standingPins : List Name := [
  ``GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary.hasSelectedRowResidualRN_n0
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

#check @GQ2.Dyadic.Certificates.foxD_nCompact_ram
#check @GQ2.Dyadic.Certificates.foxD_nCompact_unram
#check @GQ2.Dyadic.Certificates.hessRelZ_nCompact
#check @GQ2.Dyadic.Certificates.nCompactJacobianCertRam
#check @GQ2.Dyadic.Certificates.nCompactJacobianCertUnram
#check @GQ2.Dyadic.Certificates.nCompactRamNormalForm
#check @GQ2.Dyadic.Certificates.nCompactRamOps
#check @GQ2.Dyadic.Certificates.nCompactUnramNormalForm
#check @GQ2.Dyadic.Certificates.nCompactUnramOps
#check @GQ2.Dyadic.GeneralTemplateLN.canon_rawNCompact
#check @GQ2.Dyadic.GeneralTemplateLN.denote_canon_rawNCompact
#check @GQ2.Dyadic.GeneralTemplateLN.denote_rawNCompact
#check @GQ2.Dyadic.Instances.CompactNBoundaryHessianCertificates.compactNBoundaryHessian
#check @GQ2.Dyadic.Instances.CompactNHessianCertificates.compactNRamifiedComparison_add
#check @GQ2.Dyadic.Instances.CompactNHessianCertificates.compactNRamifiedHessian
#check @GQ2.Dyadic.Instances.CompactNHessianCertificates.compactNUnramifiedComparison_add
#check @GQ2.Dyadic.Instances.CompactNHessianCertificates.compactNUnramifiedHessian
#check @GQ2.Dyadic.Instances.WordPhase.wPh_nCand_stokes
#check @GQ2.Dyadic.Instances.WordPhaseCompactNFinal.wPcNWordCertificateRN
#check @GQ2.Dyadic.Instances.WordPhaseCompactNFinal.wPcN_affineDeterminantCertificate
#check @GQ2.Dyadic.Words.eval_pro2_nCompact
#check @GQ2.Dyadic.Words.nCompactW
#check @GQ2.Dyadic.Words.pro2_nCompact
#check @GQ2.Dyadic.Words.rawNCompact
#check @GQ2.Dyadic.Words.wf_rawNCompact
#check @GQ2.Dyadic.genCertNProTwoWord
#check @GQ2.Dyadic.genCertNTameSpecializes
#check @GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary.hasSelectedRowResidualRN_n0

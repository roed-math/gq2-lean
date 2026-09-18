import GQ2.Dyadic.Word.GeneralTemplateLN
import GQ2.Dyadic.Word.GeneralTemplateLNCanonical
import GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary
import GQ2.Dyadic.Words.Npc
import GQ2.Dyadic.SelectedEta
import GQ2.Dyadic.Certificates.NpcFox
import GQ2.Dyadic.Instances.NpcCore
import GQ2.Dyadic.Instances.NpcCandidateRN
import GQ2.Dyadic.Instances.NpcCandidateStokes
import GQ2.Dyadic.Instances.NpcDeterminantFinal
import GQ2.Dyadic.Instances.NpcUnramifiedFullOffsetHessian
import GQ2.Dyadic.Instances.NpcRamifiedFullOffsetHessian
import GQ2.Dyadic.Instances.NpcUnramifiedComparison
import GQ2.Dyadic.Instances.NpcHessianCertificates
import GQ2.Dyadic.Instances.NpcBoundaryHessianCertificates

open Lean

private def packetPins : List Name := [
  ``GQ2.Dyadic.Certificates.Npc.foxD_npc_ram
  , ``GQ2.Dyadic.Certificates.Npc.foxD_npc_unram
  , ``GQ2.Dyadic.Certificates.Npc.npcBlockRow
  , ``GQ2.Dyadic.Certificates.Npc.npcJacobianCertRam
  , ``GQ2.Dyadic.Certificates.Npc.npcJacobianCertUnram
  , ``GQ2.Dyadic.Certificates.Npc.npcRamOps
  , ``GQ2.Dyadic.Certificates.Npc.npcUnramOps
  , ``GQ2.Dyadic.Certificates.Npc.tameRow
  , ``GQ2.Dyadic.Certificates.Npc.tameUnramRow
  , ``GQ2.Dyadic.GeneralTemplateLN.canon_rawNpc
  , ``GQ2.Dyadic.GeneralTemplateLN.denote_canon_rawNpc
  , ``GQ2.Dyadic.GeneralTemplateLN.denote_canon_rawNpc_display
  , ``GQ2.Dyadic.GeneralTemplateLN.denote_rawNpc
  , ``GQ2.Dyadic.GeneralTemplateLN.denote_rawNpc_display
  , ``GQ2.Dyadic.GeneralTemplateLN.wf_rawNpc_display
  , ``GQ2.Dyadic.Instances.NProcyclicCore.npcProTwoWordUnit
  , ``GQ2.Dyadic.Instances.NpcBoundaryHessianCertificates.npcBoundaryHessian
  , ``GQ2.Dyadic.Instances.NpcCandidateRN.npcWordCertificateRN_of_determinant
  , ``GQ2.Dyadic.Instances.NpcCandidateStokes.npcCand_stokes
  , ``GQ2.Dyadic.Instances.NpcCandidateStokes.npcCand_stokes_displayed
  , ``GQ2.Dyadic.Instances.NpcDeterminantFinal.npcAffineDeterminantCertificate
  , ``GQ2.Dyadic.Instances.NpcDeterminantFinal.npcWordCertificateRN
  , ``GQ2.Dyadic.Instances.NpcHessianCertificates.nonempty_npcRamifiedHeadHessian
  , ``GQ2.Dyadic.Instances.NpcHessianCertificates.npcUnramifiedHeadHessian
  , ``GQ2.Dyadic.Instances.NpcRamifiedFullOffsetHessian.hessRelZ_npcW_evenTwistedNormal
  , ``GQ2.Dyadic.Instances.NpcUnramifiedComparison.wPnpcPhiCoordsEquiv
  , ``GQ2.Dyadic.Instances.NpcUnramifiedFullOffsetHessian.hessRelZ_npcW_evenPhiNormal
  , ``GQ2.Dyadic.Words.Npc.eval_pro2_npcW
  , ``GQ2.Dyadic.Words.Npc.npcW
  , ``GQ2.Dyadic.Words.Npc.npcWUnit
  , ``GQ2.Dyadic.Words.Npc.npcWUnit_eq_display
  , ``GQ2.Dyadic.Words.Npc.rawNpc
  , ``GQ2.Dyadic.Words.Npc.wf_rawNpc
  ]

private def standingPins : List Name := [
  ``GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary.hasSelectedRowResidualRN_npc
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

#check @GQ2.Dyadic.Certificates.Npc.foxD_npc_ram
#check @GQ2.Dyadic.Certificates.Npc.foxD_npc_unram
#check @GQ2.Dyadic.Certificates.Npc.npcBlockRow
#check @GQ2.Dyadic.Certificates.Npc.npcJacobianCertRam
#check @GQ2.Dyadic.Certificates.Npc.npcJacobianCertUnram
#check @GQ2.Dyadic.Certificates.Npc.npcRamOps
#check @GQ2.Dyadic.Certificates.Npc.npcUnramOps
#check @GQ2.Dyadic.Certificates.Npc.tameRow
#check @GQ2.Dyadic.Certificates.Npc.tameUnramRow
#check @GQ2.Dyadic.GeneralTemplateLN.canon_rawNpc
#check @GQ2.Dyadic.GeneralTemplateLN.denote_canon_rawNpc
#check @GQ2.Dyadic.GeneralTemplateLN.denote_canon_rawNpc_display
#check @GQ2.Dyadic.GeneralTemplateLN.denote_rawNpc
#check @GQ2.Dyadic.GeneralTemplateLN.denote_rawNpc_display
#check @GQ2.Dyadic.GeneralTemplateLN.wf_rawNpc_display
#check @GQ2.Dyadic.Instances.NProcyclicCore.npcProTwoWordUnit
#check @GQ2.Dyadic.Instances.NpcBoundaryHessianCertificates.npcBoundaryHessian
#check @GQ2.Dyadic.Instances.NpcCandidateRN.npcWordCertificateRN_of_determinant
#check @GQ2.Dyadic.Instances.NpcCandidateStokes.npcCand_stokes
#check @GQ2.Dyadic.Instances.NpcCandidateStokes.npcCand_stokes_displayed
#check @GQ2.Dyadic.Instances.NpcDeterminantFinal.npcAffineDeterminantCertificate
#check @GQ2.Dyadic.Instances.NpcDeterminantFinal.npcWordCertificateRN
#check @GQ2.Dyadic.Instances.NpcHessianCertificates.nonempty_npcRamifiedHeadHessian
#check @GQ2.Dyadic.Instances.NpcHessianCertificates.npcUnramifiedHeadHessian
#check @GQ2.Dyadic.Instances.NpcRamifiedFullOffsetHessian.hessRelZ_npcW_evenTwistedNormal
#check @GQ2.Dyadic.Instances.NpcUnramifiedComparison.wPnpcPhiCoordsEquiv
#check @GQ2.Dyadic.Instances.NpcUnramifiedFullOffsetHessian.hessRelZ_npcW_evenPhiNormal
#check @GQ2.Dyadic.Words.Npc.eval_pro2_npcW
#check @GQ2.Dyadic.Words.Npc.npcW
#check @GQ2.Dyadic.Words.Npc.npcWUnit
#check @GQ2.Dyadic.Words.Npc.npcWUnit_eq_display
#check @GQ2.Dyadic.Words.Npc.rawNpc
#check @GQ2.Dyadic.Words.Npc.wf_rawNpc
#check @GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary.hasSelectedRowResidualRN_npc

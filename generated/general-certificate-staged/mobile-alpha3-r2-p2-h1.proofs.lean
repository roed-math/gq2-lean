import GQ2.Dyadic.Word.GeneralTemplateSplice
import GQ2.Dyadic.Word.GeneralTemplateEval
import GQ2.Dyadic.Word.GeneralPhaseTemplate
import GQ2.Dyadic.Word.GeneralPhaseCoverTemplate
import GQ2.Dyadic.Instances.TameSpliceFoxTemplateBinding
import GQ2.Dyadic.Instances.TameSpliceFoxTemplateInputBinding
import GQ2.Dyadic.Instances.TameSpliceBoundaryHessianCertificates

open Lean

private def packetPins : List Name := [
  ``GQ2.Dyadic.GeneralFoxTemplate.ramified_mobile_input
  , ``GQ2.Dyadic.GeneralFoxTemplate.ramified_mobile_signature
  , ``GQ2.Dyadic.GeneralFoxTemplate.scalar_mobile_input
  , ``GQ2.Dyadic.GeneralFoxTemplate.scalar_mobile_signature
  , ``GQ2.Dyadic.GeneralFoxTemplate.unramified_mobile_input
  , ``GQ2.Dyadic.GeneralFoxTemplate.unramified_mobile_signature
  , ``GQ2.Dyadic.GeneralPhaseCoverTemplate.compactTemplate_agrees
  , ``GQ2.Dyadic.GeneralPhaseTemplate.compactPhaseCover_tree
  , ``GQ2.Dyadic.GeneralPhaseTemplate.denote_compactPhase
  , ``GQ2.Dyadic.GeneralPhaseTemplate.polar_denote_compactPhase
  , ``GQ2.Dyadic.GeneralPhaseTemplate.sourceHessian_cov_eq_denote
  , ``GQ2.Dyadic.GeneralPhaseTemplate.sourcePhase_eq_denote
  , ``GQ2.Dyadic.GeneralTemplate.Tree.eval_eq_pinned
  , ``GQ2.Dyadic.GeneralTemplate.denote_mobileSplice
  , ``GQ2.Dyadic.Instances.MpcMobileNuSource.mpcMobileTameCorrectedW_specializes
  , ``GQ2.Dyadic.Instances.MpcMobileSpliceBoundary.mpcMobileTameSplice_determinant
  , ``GQ2.Dyadic.Instances.MpcMobileSpliceSupply.mpcMobileTameSplice_core
  , ``GQ2.Dyadic.Instances.MpcMobileSpliceSupply.mpcMobileTameSplice_uniformStokesSupply
  , ``GQ2.Dyadic.Instances.MpcMobileUnramifiedPhase.hessRelZ_mpcUnit_unramified_compactPhase_of_sigma2_one
  , ``GQ2.Dyadic.Instances.TameSpliceBoundaryHessianCertificates.mobileBoundaryHessian
  , ``GQ2.Dyadic.Instances.TameSpliceRamifiedFoxNormal.tameSplice_ramified_rows
  , ``GQ2.Dyadic.Instances.TameSpliceScalarFoxNormal.mobileSplice_scalar_rows
  , ``GQ2.Dyadic.Instances.TameSpliceUnramifiedFoxRows.mobileSplice_unramified_rows
  , ``GQ2.Dyadic.Instances.WordPhaseCompactCertificates.compactPhaseCover
  , ``GQ2.Dyadic.Instances.WordPhaseCompactCertificates.sourceCompactHessianOfComparison_cov_apply
  , ``GQ2.Dyadic.Instances.WordPhasePolarNormal.reducedCoefficientMatrix_mul_inverse
  , ``GQ2.Dyadic.eval_pro2_tameSplice
  , ``GQ2.Dyadic.hessEvalZ_tameSplice_ramified
  , ``GQ2.Dyadic.tameSpecializes_tameSplice
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
  IO.println s!"PACKET_PROOF_REPLAY_PASS|{packetPins.length}"

#check GQ2.Dyadic.GeneralFoxTemplate.ramified_mobile_input
#check GQ2.Dyadic.GeneralFoxTemplate.ramified_mobile_signature
#check GQ2.Dyadic.GeneralFoxTemplate.scalar_mobile_input
#check GQ2.Dyadic.GeneralFoxTemplate.scalar_mobile_signature
#check GQ2.Dyadic.GeneralFoxTemplate.unramified_mobile_input
#check GQ2.Dyadic.GeneralFoxTemplate.unramified_mobile_signature
#check GQ2.Dyadic.GeneralPhaseCoverTemplate.compactTemplate_agrees
#check GQ2.Dyadic.GeneralPhaseTemplate.compactPhaseCover_tree
#check GQ2.Dyadic.GeneralPhaseTemplate.denote_compactPhase
#check GQ2.Dyadic.GeneralPhaseTemplate.polar_denote_compactPhase
#check GQ2.Dyadic.GeneralPhaseTemplate.sourceHessian_cov_eq_denote
#check GQ2.Dyadic.GeneralPhaseTemplate.sourcePhase_eq_denote
#check GQ2.Dyadic.GeneralTemplate.Tree.eval_eq_pinned
#check GQ2.Dyadic.GeneralTemplate.denote_mobileSplice
#check GQ2.Dyadic.Instances.MpcMobileNuSource.mpcMobileTameCorrectedW_specializes
#check GQ2.Dyadic.Instances.MpcMobileSpliceBoundary.mpcMobileTameSplice_determinant
#check GQ2.Dyadic.Instances.MpcMobileSpliceSupply.mpcMobileTameSplice_core
#check GQ2.Dyadic.Instances.MpcMobileSpliceSupply.mpcMobileTameSplice_uniformStokesSupply
#check GQ2.Dyadic.Instances.MpcMobileUnramifiedPhase.hessRelZ_mpcUnit_unramified_compactPhase_of_sigma2_one
#check GQ2.Dyadic.Instances.TameSpliceBoundaryHessianCertificates.mobileBoundaryHessian
#check GQ2.Dyadic.Instances.TameSpliceRamifiedFoxNormal.tameSplice_ramified_rows
#check GQ2.Dyadic.Instances.TameSpliceScalarFoxNormal.mobileSplice_scalar_rows
#check GQ2.Dyadic.Instances.TameSpliceUnramifiedFoxRows.mobileSplice_unramified_rows
#check GQ2.Dyadic.Instances.WordPhaseCompactCertificates.compactPhaseCover
#check GQ2.Dyadic.Instances.WordPhaseCompactCertificates.sourceCompactHessianOfComparison_cov_apply
#check GQ2.Dyadic.Instances.WordPhasePolarNormal.reducedCoefficientMatrix_mul_inverse
#check GQ2.Dyadic.eval_pro2_tameSplice
#check GQ2.Dyadic.hessEvalZ_tameSplice_ramified
#check GQ2.Dyadic.tameSpecializes_tameSplice

import GQ2.Dyadic.Word.GeneralTemplateSplice
import GQ2.Dyadic.Word.GeneralTemplateEval
import GQ2.Dyadic.Word.GeneralPhaseTemplate
import GQ2.Dyadic.Word.GeneralPhaseCoverTemplate
import GQ2.Dyadic.Instances.TameSpliceFoxTemplateBinding
import GQ2.Dyadic.Instances.TameSpliceFoxTemplateInputBinding
import GQ2.Dyadic.Instances.TameSpliceBoundaryHessianCertificates

open Lean

private def packetPins : List Name := [
  ``GQ2.Dyadic.GeneralFoxTemplate.ramified_pair_input
  , ``GQ2.Dyadic.GeneralFoxTemplate.ramified_pair_signature
  , ``GQ2.Dyadic.GeneralFoxTemplate.scalar_pair_input
  , ``GQ2.Dyadic.GeneralFoxTemplate.scalar_pair_signature
  , ``GQ2.Dyadic.GeneralFoxTemplate.unramified_pair_input
  , ``GQ2.Dyadic.GeneralFoxTemplate.unramified_pair_signature
  , ``GQ2.Dyadic.GeneralPhaseCoverTemplate.compactTemplate_agrees
  , ``GQ2.Dyadic.GeneralPhaseTemplate.compactPhaseCover_tree
  , ``GQ2.Dyadic.GeneralPhaseTemplate.denote_compactPhase
  , ``GQ2.Dyadic.GeneralPhaseTemplate.polar_denote_compactPhase
  , ``GQ2.Dyadic.GeneralPhaseTemplate.sourceHessian_cov_eq_denote
  , ``GQ2.Dyadic.GeneralPhaseTemplate.sourcePhase_eq_denote
  , ``GQ2.Dyadic.GeneralTemplate.Tree.eval_eq_pinned
  , ``GQ2.Dyadic.GeneralTemplate.denote_pairSplice
  , ``GQ2.Dyadic.Instances.EvenMHeadHandlePairProjectedPhase.QZero_headHandlePairSplice_unramified_compactPhase
  , ``GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceBoundary.headHandlePairSplice_determinant
  , ``GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceSupply.flexibleCore_headHandlePairSplice
  , ``GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceSupply.headHandlePairSpliceW_specializes
  , ``GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceSupply.uniformStokesSupply_headHandlePairSplice
  , ``GQ2.Dyadic.Instances.TameSpliceBoundaryHessianCertificates.pairBoundaryHessian
  , ``GQ2.Dyadic.Instances.TameSpliceRamifiedFoxNormal.tameSplice_ramified_rows
  , ``GQ2.Dyadic.Instances.TameSpliceScalarFoxNormal.pairSplice_scalar_rows
  , ``GQ2.Dyadic.Instances.TameSpliceUnramifiedFoxRows.pairSplice_unramified_rows
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

#check GQ2.Dyadic.GeneralFoxTemplate.ramified_pair_input
#check GQ2.Dyadic.GeneralFoxTemplate.ramified_pair_signature
#check GQ2.Dyadic.GeneralFoxTemplate.scalar_pair_input
#check GQ2.Dyadic.GeneralFoxTemplate.scalar_pair_signature
#check GQ2.Dyadic.GeneralFoxTemplate.unramified_pair_input
#check GQ2.Dyadic.GeneralFoxTemplate.unramified_pair_signature
#check GQ2.Dyadic.GeneralPhaseCoverTemplate.compactTemplate_agrees
#check GQ2.Dyadic.GeneralPhaseTemplate.compactPhaseCover_tree
#check GQ2.Dyadic.GeneralPhaseTemplate.denote_compactPhase
#check GQ2.Dyadic.GeneralPhaseTemplate.polar_denote_compactPhase
#check GQ2.Dyadic.GeneralPhaseTemplate.sourceHessian_cov_eq_denote
#check GQ2.Dyadic.GeneralPhaseTemplate.sourcePhase_eq_denote
#check GQ2.Dyadic.GeneralTemplate.Tree.eval_eq_pinned
#check GQ2.Dyadic.GeneralTemplate.denote_pairSplice
#check GQ2.Dyadic.Instances.EvenMHeadHandlePairProjectedPhase.QZero_headHandlePairSplice_unramified_compactPhase
#check GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceBoundary.headHandlePairSplice_determinant
#check GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceSupply.flexibleCore_headHandlePairSplice
#check GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceSupply.headHandlePairSpliceW_specializes
#check GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceSupply.uniformStokesSupply_headHandlePairSplice
#check GQ2.Dyadic.Instances.TameSpliceBoundaryHessianCertificates.pairBoundaryHessian
#check GQ2.Dyadic.Instances.TameSpliceRamifiedFoxNormal.tameSplice_ramified_rows
#check GQ2.Dyadic.Instances.TameSpliceScalarFoxNormal.pairSplice_scalar_rows
#check GQ2.Dyadic.Instances.TameSpliceUnramifiedFoxRows.pairSplice_unramified_rows
#check GQ2.Dyadic.Instances.WordPhaseCompactCertificates.compactPhaseCover
#check GQ2.Dyadic.Instances.WordPhaseCompactCertificates.sourceCompactHessianOfComparison_cov_apply
#check GQ2.Dyadic.Instances.WordPhasePolarNormal.reducedCoefficientMatrix_mul_inverse
#check GQ2.Dyadic.eval_pro2_tameSplice
#check GQ2.Dyadic.hessEvalZ_tameSplice_ramified
#check GQ2.Dyadic.tameSpecializes_tameSplice

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcWordPhaseModel

/-!
# Generic procyclic-N determinant consumer

A complete `wPnpcPhaseModel` already contains the branchwise source comparison and evaluates
its varying quadratic diagonal through `wPnpc_branchFree_of_phaseModel`.  This file consumes
that branch-free supply in both affine determinant clauses.  No separate Gauss-sum premise is
retained.
-/

namespace GQ2.Dyadic.Instances.NpcDeterminantBase

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.Words GQ2.Dyadic.Words.Npc
open GQ2.Dyadic.NProcyclic GQ2.Dyadic.NProcyclicUnram
open GQ2.Dyadic.LSquare
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.NpcWordPhaseModel

/-- A branch-free Npc phase supply discharges both affine determinant clauses.  The Gauss
evaluation is already part of `wPnpc_branchFree_of_phaseModel`, so no diagonal-specific Gauss
premise appears here. -/
theorem npcAffineDeterminantCertificate_of_branchFree
    {alpha r h q : ℕ} {d : EtaData} (hsimp : UniformHsimp alpha r h q d)
    (halpha : 2 ≤ alpha) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (displayedGamma alpha r h q d) (Tq q))
    (pro2 : ContinuousMonoidHom (displayedGamma alpha r h q d) P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (S : wPhBranchFreeSupply (2 * h + 2) nuP tame pro2 compat) :
    AffineDeterminantCertificate (displayedGamma alpha r h q d) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) tame pro2 compat (scalarActionZmodTwo _) := by
  letI := scalarActionZmodTwo ((displayedGamma alpha r h q d : Type))
  haveI := scalarActionZmodTwo_continuousSMul ((displayedGamma alpha r h q d : Type))
  constructor
  · exact fun T Blk _ _ _ hE2 hq0' hqe' F hsimple hVne hnt m hm hcard l hl _ ↦ by
      let En := blockEnrichmentDK T Blk hE2 hq0' hqe' F
      apply gaussZResidueK_of_wordPhase
        (sourceBoundaryMapK tame pro2 compat) F En l hl (scalarActionZmodTwo_triv _)
      · intro rho
        apply (Nat.card_ne_zero.mp ?_).2
        rw [NpcCandidateStokes.npcCand_hZcard hsimp
          (by omega) hqe (sourceBoundaryMapK tame pro2 compat) F En l hl
          hsimple hVne hnt rho]
        exact Nat.mul_ne_zero Nat.card_pos.ne' (Nat.pow_pos Nat.card_pos).ne'
      · intro rho v hfixed
        apply hfix_of_simple_nt (hsimple := hsimple) (hnt := hnt) ?_ v hfixed
        intro c0
        obtain ⟨g, hg⟩ := rho.1.2 c0
        exact ⟨g, (rho0_descData_rhoPrimeK
          (sourceBoundaryMapK tame pro2 compat) F En l hl rho g).trans hg⟩
      · rw [wPh_gauss_targets_eq h m]
        exact S T Blk hE2 hq0' hqe' F hsimple hVne hnt m hm hcard l hl
  · exact fun T Blk _ _ _ hE2 hq0' hqe' F hsimple hVne hnt m hm hcard l hl _ ↦ by
      let En := blockEnrichmentDK T Blk hE2 hq0' hqe' F
      apply gaussZResidueK_of_wordPhase
        (sourceBoundaryMapK tame pro2 compat) F En l hl (scalarActionZmodTwo_triv _)
      · intro rho
        apply (Nat.card_ne_zero.mp ?_).2
        rw [NpcCandidateStokes.npcCand_hZcard hsimp
          (by omega) hqe (sourceBoundaryMapK tame pro2 compat) F En l hl
          hsimple hVne hnt rho]
        exact Nat.mul_ne_zero Nat.card_pos.ne' (Nat.pow_pos Nat.card_pos).ne'
      · intro rho v hfixed
        apply hfix_of_simple_nt (hsimple := hsimple) (hnt := hnt) ?_ v hfixed
        intro c0
        obtain ⟨g, hg⟩ := rho.1.2 c0
        exact ⟨g, (rho0_descData_rhoPrimeK
          (sourceBoundaryMapK tame pro2 compat) F En l hl rho g).trans hg⟩
      · exact S T Blk hE2 hq0' hqe' F hsimple hVne hnt m hm hcard l hl

/-- The phase-model-to-determinant endpoint.  Its only model-specific input is the source
comparison package quantified by `wPnpcPhaseModel`. -/
theorem npcAffineDeterminantCertificate_of_phaseModel
    {alpha r h q : ℕ} {d : EtaData} (hsimp : UniformHsimp alpha r h q d)
    (halpha : 2 ≤ alpha) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (displayedGamma alpha r h q d) (Tq q))
    (pro2 : ContinuousMonoidHom (displayedGamma alpha r h q d) P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (M : wPnpcPhaseModel h nuP tame pro2 compat) :
    AffineDeterminantCertificate (displayedGamma alpha r h q d) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) tame pro2 compat (scalarActionZmodTwo _) :=
  npcAffineDeterminantCertificate_of_branchFree hsimp halpha hqe nuP tame pro2 compat
    (wPnpc_branchFree_of_phaseModel h nuP tame pro2 compat M)


#print axioms npcAffineDeterminantCertificate_of_branchFree
#print axioms npcAffineDeterminantCertificate_of_phaseModel

end
end GQ2.Dyadic.Instances.NpcDeterminantBase

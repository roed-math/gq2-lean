/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcHandleBoundary
import GQ2.Dyadic.Instances.MpcCandidateStokes

namespace GQ2.Dyadic.Instances.MpcHandleDeterminant

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.MProcyclicExact
open GQ2.Dyadic.LSquare
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.MpcHandleBoundary
open GQ2.Dyadic.Instances.MpcCandidateStokes

/-- A branch-free displayed Mpc supply discharges both affine determinant clauses. -/
theorem mpcAffineDeterminantCertificate_of_branchFree_handles
    {alpha r pp h q : ℕ} {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta)
    (halpha : 2 ≤ alpha) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom
      (displayedGamma alpha r pp h q d.display) (Tq q))
    (pro2 : ContinuousMonoidHom
      (displayedGamma alpha r pp h q d.display) P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (S : wPhBranchFreeSupply (2 * h + 2) nuP tame pro2 compat) :
    AffineDeterminantCertificate
      (displayedGamma alpha r pp h q d.display) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) tame pro2 compat (scalarActionZmodTwo _) := by
  letI := scalarActionZmodTwo
    ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type)
  haveI := scalarActionZmodTwo_continuousSMul
    ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type)
  have hsimp : UniformHsimp alpha r pp h q d.display :=
    RecordBlocks.recBl_mpc_uniformPushedHsimp halpha hqe d
  constructor
  · exact fun T Blk _ _ _ hE2 hq0' hqe' F hsimple hVne hnt m hm hcard l hl _ ↦ by
      let En := blockEnrichmentDK T Blk hE2 hq0' hqe' F
      apply gaussZResidueK_of_wordPhase
        (sourceBoundaryMapK tame pro2 compat) F En l hl (scalarActionZmodTwo_triv _)
      · intro rho
        apply (Nat.card_ne_zero.mp ?_).2
        rw [mpcCand_hZcard hsimp (by omega) hqe
          (sourceBoundaryMapK tame pro2 compat) F En l hl hsimple hVne hnt rho]
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
        rw [mpcCand_hZcard hsimp (by omega) hqe
          (sourceBoundaryMapK tame pro2 compat) F En l hl hsimple hVne hnt rho]
        exact Nat.mul_ne_zero Nat.card_pos.ne' (Nat.pow_pos Nat.card_pos).ne'
      · intro rho v hfixed
        apply hfix_of_simple_nt (hsimple := hsimple) (hnt := hnt) ?_ v hfixed
        intro c0
        obtain ⟨g, hg⟩ := rho.1.2 c0
        exact ⟨g, (rho0_descData_rhoPrimeK
          (sourceBoundaryMapK tame pro2 compat) F En l hl rho g).trans hg⟩
      · exact S T Blk hE2 hq0' hqe' F hsimple hVne hnt m hm hcard l hl

/-- Honest displayed Mpc head data gives the arbitrary-h affine determinant certificate. -/
theorem mpcAffineDeterminantCertificate_handles
    {alpha r pp h q : ℕ} {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta)
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom
      (displayedGamma alpha r pp h q d.display) (Tq q))
    (pro2 : ContinuousMonoidHom
      (displayedGamma alpha r pp h q d.display) P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame
      (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .sigma) = tqSigma q)
    (htameTau : tame
      (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .tau) = tqTau q)
    (htameWild : ∀ i : Fin (2 + 2 * h + 1), tame
      (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) (.wild i)) = 1) :
    AffineDeterminantCertificate
      (displayedGamma alpha r pp h q d.display) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) tame pro2 compat (scalarActionZmodTwo _) := by
  apply mpcAffineDeterminantCertificate_of_branchFree_handles d halpha hqe
  exact wPmpc_branchFreeSupply_handles d nuP tame pro2 compat
    htameSigma htameTau htameWild halpha hr

#print axioms mpcAffineDeterminantCertificate_of_branchFree_handles
#print axioms mpcAffineDeterminantCertificate_handles

end
end GQ2.Dyadic.Instances.MpcHandleDeterminant

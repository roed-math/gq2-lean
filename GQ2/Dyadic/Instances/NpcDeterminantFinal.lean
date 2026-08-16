/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcBoundaryFinal
import GQ2.Dyadic.Instances.NpcDeterminantBase
import GQ2.Dyadic.Instances.NpcCandidateRN

/-!
# Final procyclic-N determinant and corrected certificate

The branch-free boundary supply closes both affine determinant clauses for every selected Npc
display.  The resulting corrected `WordCertificateRN` retains only the structural bounds
`2 ≤ alpha`, `q ≠ 0`, and `Even q`; no analytic premise survives.
-/

namespace GQ2.Dyadic.Instances.NpcDeterminantFinal

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.Words GQ2.Dyadic.Words.Npc
open GQ2.Dyadic.NProcyclic GQ2.Dyadic.NProcyclicUnram
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.NProcyclicCore
open GQ2.Dyadic.Instances.NpcBoundaryFinal
open GQ2.Dyadic.Instances.NpcCandidateRN
open GQ2.Dyadic.Instances.NpcDeterminantBase
open GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.TameSpec

/-- Presentation equality transports the displayed determinant theorem without dependent
rewrites through the tame and pro-2 maps. -/
theorem npcAffineDeterminantCertificate_of_word_eq
    {alpha r h q : ℕ} {d : EtaData}
    {R : PWord (Generator (2 + 2 * h))}
    (hR : R = npcW alpha r h d)
    (hsimp : UniformHsimp alpha r h q d) (halpha : 2 ≤ alpha) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (GammaR (2 + 2 * h) q R) (Tq q))
    (pro2 : ContinuousMonoidHom (GammaR (2 + 2 * h) q R) P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame (gammaGen (2 + 2 * h) q R .sigma) = tqSigma q)
    (htameTau : tame (gammaGen (2 + 2 * h) q R .tau) = tqTau q)
    (htameWild : ∀ i : Fin (2 + 2 * h + 1),
      tame (gammaGen (2 + 2 * h) q R (.wild i)) = 1) :
    AffineDeterminantCertificate (GammaR (2 + 2 * h) q R) (2 + 2 * h) q P nuP
      (standardNumerics (2 + 2 * h)) tame pro2 compat (scalarActionZmodTwo _) := by
  subst R
  apply RecordBlocks.recBl_determinant_standard_congr
    (n := 2 * h + 2) (m := 2 + 2 * h) (by omega)
  apply npcAffineDeterminantCertificate_of_branchFree hsimp halpha hqe
  exact wPnpc_branchFreeSupply
    (alpha := alpha) (r := r) (h := h) (q := q) (d := d)
    hsimp halpha nuP tame pro2 compat htameSigma htameTau htameWild

/-- The unconditional analytic determinant endpoint for every selected Npc display. -/
theorem npcAffineDeterminantCertificate
    (alpha r h q : ℕ) {eta : ℤ_[2]ˣ} (d : NpcDisplayFor eta)
    (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q) :
    AffineDeterminantCertificate
      (GammaR (2 + 2 * h) q (npcWUnit alpha r h eta)) (2 + 2 * h) q
      (DN alpha h) (npcNu alpha r h eta) (standardNumerics (2 + 2 * h))
      (tameOfSpec (2 + 2 * h) q (npcWUnit alpha r h eta)
        (npcCandidate_tameSpecializes alpha r h q d hq0 hqe))
      (npcCandidate_pro2 alpha r h q d hq0 hqe)
      (npcCandidate_compat alpha r h q d hq0 hqe)
      (scalarActionZmodTwo _) := by
  obtain ⟨z, hz⟩ := d.exists_toPadic_eq_one_add_two_mul
  have hsimp : UniformHsimp alpha r h q d.data :=
    NProcyclicUnram.uniformPushedHsimp halpha hqe z hz
  apply npcAffineDeterminantCertificate_of_word_eq
    (npcWUnit_eq_display alpha r h d) hsimp halpha hqe
  · exact TameSpec.tameOfSpec_gammaGen _ .sigma
  · exact TameSpec.tameOfSpec_gammaGen _ .tau
  · intro i
    exact TameSpec.tameOfSpec_gammaGen _ (.wild i)

/-- The determinant closes the corrected semantic Npc word certificate unconditionally. -/
noncomputable def npcWordCertificateRN
    (alpha r h q : ℕ) {eta : ℤ_[2]ˣ} (d : NpcDisplayFor eta)
    (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q) :
    WordCertificateRN (2 + 2 * h) q (npcWUnit alpha r h eta) (DN alpha h)
      (isProP_DN alpha h) (npcNu alpha r h eta) (standardNumerics (2 + 2 * h)) :=
  npcWordCertificateRN_of_determinant alpha r h q d halpha hq0 hqe
    (npcAffineDeterminantCertificate alpha r h q d halpha hq0 hqe)

#print axioms npcAffineDeterminantCertificate_of_word_eq
#print axioms npcAffineDeterminantCertificate
#print axioms npcWordCertificateRN

end
end GQ2.Dyadic.Instances.NpcDeterminantFinal

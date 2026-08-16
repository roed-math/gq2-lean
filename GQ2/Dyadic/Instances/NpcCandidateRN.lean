/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcCandidateStokes
import GQ2.Dyadic.CertificateSupplyRN

/-!
# Corrected procyclic-N candidate scaffolding

This module assembles the semantic arbitrary-unit, general-handle procyclic-N
`WordCertificateRN`.  Exact lifting, the full four-clause Stokes certificate, the scalar
certificate, and all structural fields are discharged; the affine determinant certificate is
the sole remaining input.

No frozen tied Npc row is asserted: the campaign has no such selector endpoint.
-/

namespace GQ2.Dyadic.Instances.NpcCandidateRN

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.Words GQ2.Dyadic.Words.Npc
open GQ2.Dyadic.NProcyclic GQ2.Dyadic.NProcyclicUnram
open GQ2.Dyadic.Instances.NProcyclicCore
open GQ2.Dyadic.Instances.NpcCandidateScalar
open GQ2.Dyadic.Instances.NpcCandidateStokes
open GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.TameSpec

/-- The semantic arbitrary-unit Npc word has the usual tame specialization. -/
theorem npcCandidate_tameSpecializes (alpha r h q : ℕ) {eta : ℤ_[2]ˣ}
    (d : NpcDisplayFor eta) (hq0 : q ≠ 0) (hqe : Even q) :
    TameSpecializes (2 + 2 * h) q (npcWUnit alpha r h eta) := by
  rw [npcWUnit_eq_display alpha r h d]
  exact Count.tameSpecializes_npcW hq0 hqe alpha r h d.data

/-- The canonical map from the semantic Npc candidate to its presented pro-2 core. -/
noncomputable def npcCandidate_pro2 (alpha r h q : ℕ) {eta : ℤ_[2]ˣ}
    (d : NpcDisplayFor eta) (hq0 : q ≠ 0) (hqe : Even q) :
    ContinuousMonoidHom
      ((GammaR (2 + 2 * h) q (npcWUnit alpha r h eta) : ProfiniteGrp) : Type)
      (DN alpha h) :=
  Count.CorePresentation.coreHom (npcCorePresentationUnit alpha r h eta d) hq0 hqe

/-- Cyclotomic compatibility for the canonical arbitrary-unit Npc orientation. -/
theorem npcCandidate_compat (alpha r h q : ℕ) {eta : ℤ_[2]ˣ}
    (d : NpcDisplayFor eta) (hq0 : q ≠ 0) (hqe : Even q) :
    ∀ g : ((GammaR (2 + 2 * h) q (npcWUnit alpha r h eta) : ProfiniteGrp) : Type),
      nuTq q (tameOfSpec (2 + 2 * h) q (npcWUnit alpha r h eta)
        (npcCandidate_tameSpecializes alpha r h q d hq0 hqe) g) =
        npcNu alpha r h eta (npcCandidate_pro2 alpha r h q d hq0 hqe g) :=
  Count.CorePresentation.nu_compat_coreHom (npcCorePresentationUnit alpha r h eta d)
    hq0 hqe (npcCandidate_tameSpecializes alpha r h q d hq0 hqe)
    (npcNu alpha r h eta) (npcNu_sigma alpha r h eta d) (npcNu_wild alpha r h eta d)

/-- The corrected semantic arbitrary-unit procyclic-N word certificate.  Its sole analytic
input is the affine determinant certificate. -/
noncomputable def npcWordCertificateRN_of_determinant
    (alpha r h q : ℕ) {eta : ℤ_[2]ˣ} (d : NpcDisplayFor eta)
    (hα : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (determinant : AffineDeterminantCertificate
      (GammaR (2 + 2 * h) q (npcWUnit alpha r h eta)) (2 + 2 * h) q
      (DN alpha h) (npcNu alpha r h eta) (standardNumerics (2 + 2 * h))
      (tameOfSpec (2 + 2 * h) q (npcWUnit alpha r h eta)
        (npcCandidate_tameSpecializes alpha r h q d hq0 hqe))
      (npcCandidate_pro2 alpha r h q d hq0 hqe)
      (npcCandidate_compat alpha r h q d hq0 hqe)
      (scalarActionZmodTwo _)) :
    WordCertificateRN (2 + 2 * h) q (npcWUnit alpha r h eta) (DN alpha h)
      (isProP_DN alpha h) (npcNu alpha r h eta) (standardNumerics (2 + 2 * h)) where
  tameSpecialization := npcCandidate_tameSpecializes alpha r h q d hq0 hqe
  coreRel := fun G _ _ _ _ _ t ↦ t.eval (pro2 (npcWUnit alpha r h eta))
  proTwoWord := fun _ _ _ _ _ _ _ ↦ rfl
  pro2 := npcCandidate_pro2 alpha r h q d hq0 hqe
  ker_pro2 := Count.CorePresentation.ker_coreHom
    (npcCorePresentationUnit alpha r h eta d) hq0 hqe
  hpro2 := Count.CorePresentation.coreHom_surjective
    (npcCorePresentationUnit alpha r h eta d) hq0 hqe
  compat := npcCandidate_compat alpha r h q d hq0 hqe
  tfg := Count.gammaR_topologicallyFinitelyGenerated _ _ _
  smulZmod2 := scalarActionZmodTwo _
  contSMulZmod2 := scalarActionZmodTwo_continuousSMul _
  htriv := scalarActionZmodTwo_triv _
  exactLifting := by
    apply exactLiftingRN_standard_congr
      (n := 2 * h + 2) (m := 2 + 2 * h) (by omega)
    obtain ⟨z, hz⟩ := d.exists_toPadic_eq_one_add_two_mul
    exact exactLiftingRN_of_uniformPushed d
      (uniformPushedHsimp hα hqe z hz) (by omega) hqe (npcNu alpha r h eta)
  stokes := by
    have H := npcCand_stokes (alpha := alpha) (r := r) (h := h) (q := q)
      d hα hqe (P := DN alpha h) (nuP := npcNu alpha r h eta)
    change StokesDualityCertificate
      (GammaR (2 + 2 * h) q (npcWUnit alpha r h eta)) (2 * h + 2) q
      (DN alpha h) (npcNu alpha r h eta) (standardNumerics (2 * h + 2))
      (scalarActionZmodTwo _) at H
    rw [show 2 * h + 2 = 2 + 2 * h by omega] at H
    exact H
  scalar := by
    have H := npcCandidate_scalar (alpha := alpha) (r := r) (h := h) (q := q)
      d hα hqe
    change ScalarHilbertCertificate
      (GammaR (2 + 2 * h) q (npcWUnit alpha r h eta)) (2 * h + 2)
      (standardNumerics (2 * h + 2)) (scalarActionZmodTwo _) at H
    rw [show 2 * h + 2 = 2 + 2 * h by omega] at H
    exact H
  determinant := determinant
  htame := Count.htame_of_tameSpecializes _
  hwild := Count.hwild_of_tameSpecializes _

#print axioms npcCandidate_tameSpecializes
#print axioms npcCandidate_pro2
#print axioms npcCandidate_compat
#print axioms npcWordCertificateRN_of_determinant

end

end GQ2.Dyadic.Instances.NpcCandidateRN

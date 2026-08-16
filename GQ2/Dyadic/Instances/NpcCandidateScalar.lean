/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcUnramifiedScalar

/-!
# Scalar certificates for procyclic-N candidates

The corrected procyclic-`N` action-image analysis already supplies an unconditional uniform
pushed Stokes residue for every valid selected display.  This module feeds that residue through
the scalar count route and packages the complete `ScalarHilbertCertificate`, uniformly in the
handle count.

The selected arbitrary-unit endpoint uses only the honest display package: its represented
`2`-adic unit is `1 + 2z`, which is exactly the remaining input to
`NProcyclicUnram.uniformPushedHsimp`.  No determinant, source phase, frozen row, or field
identification is asserted here.  In particular `Npc` still has no frozen tied row.

No `sorry`, new axiom, `native_decide`, heartbeat override, or recursion override is used.
-/

namespace GQ2.Dyadic.Instances.NpcCandidateScalar

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.Npc
open GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.NProcyclic GQ2.Dyadic.NProcyclicUnram
open GQ2.Dyadic.Count.PilotN GQ2.CardH2GammaA

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-- The scalar character count for a displayed procyclic-`N` candidate, from its uniform
pushed residue. -/
theorem npcCandidate_homCard_of_uniformPushed
    {alpha r h q : ℕ} {d : EtaData}
    (hsimp : NProcyclic.UniformHsimp alpha r h q d)
    (hα : 1 ≤ alpha) (hqe : Even q) :
    Nat.card (ContinuousMonoidHom
      ((NProcyclic.displayedGamma alpha r h q d : Type)) (Multiplicative (ZMod 2))) =
      (standardNumerics (2 * h + 2)).homScalar := by
  letI : TopologicalSpace Base := ⊥
  letI : DiscreteTopology Base := ⟨rfl⟩
  letI : DiscreteTopology (Base ⧸ datum.M) := discreteTopology_quotient datum
  letI := scalarActionZmodTwo (Base ⧸ datum.M)
  set rho := NProcyclic.datumRho alpha r h q d with hrho
  have hb := NProcyclic.resolvesAt_and_endpoint_uniformHeis
    (C := Base ⧸ datum.M) (A := ZMod 2)
    (alpha := alpha) (r := r) (h := h) (q := q)
    (by decide : ∀ a : ZMod 2, a + a = 0) hα hqe d
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (npcW alpha r h d))
      (NProcyclic.resolvedFamily alpha r h q d
        (4 * Monoid.exponent (Base ⧸ datum.M)))
      (WordLift (ZMod 2) (Base ⧸ datum.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (ZMod 2) (Base ⧸ datum.M))
        (HeisLift (ZMod 2) (Base ⧸ datum.M)) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisPrim_injective
  exact Count.homCard_field_goal rho (fun _ ↦ rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (npcW alpha r h d)) hres
    (isWildTwo_of_gammaGen rho
      (NProcyclic.datumRho_surjective alpha r h q d) (fun _ ↦ rfl))
    (nCompact_degree h)
    (hsimp (Base ⧸ datum.M) rho (ZMod 2)
      (by decide : ∀ a : ZMod 2, a + a = 0))
    hb.2

/-- The complete scalar Hilbert certificate for a displayed procyclic-`N` candidate. -/
theorem npcCandidate_scalar_of_uniformPushed
    {alpha r h q : ℕ} {d : EtaData}
    (hsimp : NProcyclic.UniformHsimp alpha r h q d)
    (hα : 1 ≤ alpha) (hqe : Even q) :
    ScalarHilbertCertificate (NProcyclic.displayedGamma alpha r h q d) (2 * h + 2)
      (standardNumerics (2 * h + 2)) (scalarActionZmodTwo _) :=
  ⟨npcCandidate_homCard_of_uniformPushed hsimp hα hqe,
   NProcyclic.cardH2_of_uniformPushed hsimp hα hqe⟩

/-- The scalar certificate for every valid selected arbitrary-unit procyclic-`N` display. -/
theorem npcCandidate_scalar {alpha r h q : ℕ} {eta : ℤ_[2]ˣ}
    (d : NpcDisplayFor eta) (hα : 2 ≤ alpha) (hqe : Even q) :
    ScalarHilbertCertificate (NProcyclic.gamma alpha r h q eta) (2 * h + 2)
      (standardNumerics (2 * h + 2)) (scalarActionZmodTwo _) := by
  rw [NProcyclic.gamma_eq_display alpha r h q d]
  obtain ⟨z, hz⟩ := d.exists_toPadic_eq_one_add_two_mul
  exact npcCandidate_scalar_of_uniformPushed
    (NProcyclicUnram.uniformPushedHsimp hα hqe z hz) (by omega) hqe

/-! ## Axiom audit -/

#print axioms npcCandidate_homCard_of_uniformPushed
#print axioms npcCandidate_scalar_of_uniformPushed
#print axioms npcCandidate_scalar

end

end GQ2.Dyadic.Instances.NpcCandidateScalar

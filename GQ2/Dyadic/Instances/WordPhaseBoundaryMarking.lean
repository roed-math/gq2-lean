/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhaseCompactMHandleBoundary

/-!
# Word-independent boundary head markings

The projected wild BASE entries in the phase calculation are one because of the actual
boundary-lift equations, not merely because wild generators act trivially. These statements
isolate that distinction for an arbitrary source carrier and arbitrary marked generators.
-/

namespace GQ2.Dyadic.Instances.WordPhaseBoundaryMarking
noncomputable section
open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count

section Boundary
variable {Γ P : ProfiniteGrp} {q : ℕ} {nuP : ContinuousMonoidHom P Ztwo}
  {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
  {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
  [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
  (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
  (F : BoundaryFrameK q P H E)
  (tame : ContinuousMonoidHom Γ (Tq q)) (pro2 : ContinuousMonoidHom Γ P)
  (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
  (l : (SectionNine.blockFrame T Blk hE2).DR)
  (hl : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
  (rho : BoundaryLiftsK (sourceBoundaryMapK tame pro2 compat) F
    (SectionNine.blockFrame T Blk hE2).TC)

/-- The projected lower map is exactly the tame head map on every source element. -/
theorem projectedHead_eq (g : Γ) :
    let En := blockEnrichmentDK T Blk hE2 hq0 hqe F
    let DD := En.descData l hl
    let rhoM := rhoPrimeK (SectionNine.blockFrame T Blk hE2)
      (sourceBoundaryMapK tame pro2 compat) F (En.radData l hl) rfl rho
    SectionNine.blockProjF T Blk (rho0 DD rhoM g) = headTameSurjK T Blk F (tame g) := by
  dsimp only
  rw [rho0_descData_rhoPrimeK (sourceBoundaryMapK tame pro2 compat) F
    (blockEnrichmentDK T Blk hE2 hq0 hqe F) l hl rho g]
  exact congrArg (⇑(QuotientGroup.mk' (SectionNine.headActKer T Blk)))
    (boundaryLift_headK T Blk hE2 (sourceBoundaryMapK tame pro2 compat) F rho g)

/-- An arbitrary generator marking with canonical tame coordinates has canonical projected
head coordinates, including actual identity wild entries. -/
theorem projectedHead_marking {n : ℕ} (gen : Generator n → Γ)
    (hsigma : tame (gen .sigma) = tqSigma q)
    (htau : tame (gen .tau) = tqTau q)
    (hwild : ∀ i, tame (gen (.wild i)) = 1) :
    let En := blockEnrichmentDK T Blk hE2 hq0 hqe F
    let DD := En.descData l hl
    let rhoM := rhoPrimeK (SectionNine.blockFrame T Blk hE2)
      (sourceBoundaryMapK tame pro2 compat) F (En.radData l hl) rfl rho
    let c := fun a ↦ SectionNine.blockProjF T Blk (rho0 DD rhoM (gen a))
    c .sigma = hvSigmaK T Blk F ∧ c .tau = hvTauK T Blk F ∧
      ∀ i, c (.wild i) = 1 := by
  dsimp only
  have heq := projectedHead_eq T Blk hE2 hq0 hqe F tame pro2 compat l hl rho
  refine ⟨?_, ?_, ?_⟩
  · rw [heq, hsigma]
    rfl
  · rw [heq, htau]
    rfl
  · intro i
    rw [heq, hwild i, map_one]

end Boundary

#print axioms projectedHead_eq
#print axioms projectedHead_marking

end
end GQ2.Dyadic.Instances.WordPhaseBoundaryMarking

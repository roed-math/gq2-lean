/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcCandidateRN
import GQ2.Dyadic.Instances.WordPhase

/-!
# Twisted-head phase model for procyclic N

The arbitrary-unit Npc Hessian is not an affine-linear perturbation of the compact plus form.
The unit changes both the quadratic diagonal `npcQ0` and the cross operator `lcOp`; after an
inverse change of variables the head has shape `plusFormD d0 q`, for a genuinely varying
quadratic form `d0`.  Consequently `PlusFormLinearShift` is not the relevant reduction.

This file proves that the varying diagonal does not alter the Gauss value and packages the
narrowest comparison residue implying `wPhBranchFreeSupply`.  It does not assert that residue.
The ramified lane can use the existing general-h `npcW_hessRelZTarget_handles` after supplying
quadraticity and an inverse to `lcOp`.  The unramified lane remains blocked on a new full-offset
Hessian formula: its normal cochain has `x2 = Phi x0`, while the landed Npc Hessian theorem
assumes `x2 = 0`.
-/

namespace GQ2.Dyadic.Instances.NpcWordPhaseModel

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.LSquare
open GQ2.QuadraticFp2

/-- The Npc endpoint after inverting its cross operator: a twisted plus-form head and the
standard hyperbolic handle tail. -/
def wPnpcWallHandlePhase {V : Type} [AddCommGroup V]
    (d0 q : V → ZMod 2) (h : ℕ) :
    (V × V) × (Fin h → V × V) → ZMod 2 :=
  fun p ↦ plusFormD d0 q p.1 + ∑ j, polar q (p.2 j).1 (p.2 j).2

/-- The twisted diagonal does not affect the positive Gauss value. -/
theorem wPnpc_wallHandlePhase_gaussSum_standardRam
    {V : Type} [AddCommGroup V] [Fintype V] {d0 q : V → ZMod 2}
    (hd0 : IsQuadraticFp2 d0) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    {m : ℕ} (hcard : Fintype.card V = 2 ^ (2 * m)) (h : ℕ) :
    QuadraticFp2.gaussSum (wPnpcWallHandlePhase d0 q h) =
      (standardNumerics (2 * h + 2)).gaussRam m := by
  have hsplit : wPnpcWallHandlePhase d0 q h =
      fun p : (V × V) × (Fin h → V × V) ↦
        plusFormD d0 q p.1 + ∑ j, plusFormD (fun _ ↦ 0) q (p.2 j) := by
    funext p
    refine congrArg (HAdd.hAdd (plusFormD d0 q p.1))
      (Finset.sum_congr rfl fun j _ ↦ ?_)
    simp [plusFormD]
  rw [hsplit, gaussSum_prod_add (plusFormD d0 q)
      (fun w : Fin h → V × V ↦ ∑ j, plusFormD (fun _ ↦ 0) q (w j)),
    gaussSum_plusFormD hd0 hq hns, gaussSum_pi_sum,
    gaussSum_plusFormD (isQuadraticFp2_zero (V := V)) hq hns, hcard]
  push_cast
  rw [← pow_mul, ← pow_add]
  show (2 : ℤ) ^ (2 * m + 2 * m * h) = 2 ^ ((2 * h + 2) * m)
  congr 1
  ring

/-- The narrow comparison residue for Npc: the diagonal may vary with the boundary action,
while the polar form and handle planes are fixed by `DescData`. -/
def wPnpcPhaseModel {Gam : ProfiniteGrp} {q : ℕ} (h : ℕ) {P : ProfiniteGrp}
    (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom Gam (Tq q))
    (pro2 : ContinuousMonoidHom Gam P)
    (compat : ∀ g : (Gam : Type), nuTq q (tame g) = nuP (pro2 g)) : Prop :=
  letI := scalarActionZmodTwo ((Gam : Type))
  ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
    (F : BoundaryFrameK q P H E)
    (l : (SectionNine.blockFrame T Blk hE2).DR)
    (hl : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
    (rho : BoundaryLiftsK (sourceBoundaryMapK tame pro2 compat) F
      (SectionNine.blockFrame T Blk hE2).TC),
    let DD := (blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    ∃ d0 : DD.Vmod → ZMod 2, IsQuadraticFp2 d0 ∧
      Nonempty (SourceWordPhaseComparison DD
        (rhoPrimeK (SectionNine.blockFrame T Blk hE2)
          (sourceBoundaryMapK tame pro2 compat) F
          ((blockEnrichmentDK T Blk hE2 hq0 hqe F).radData l hl) rfl rho)
        (scalarActionZmodTwo_triv _)
        ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
        (wPnpcWallHandlePhase d0 DD.qbar h))

/-- Once the twisted-head comparison is known, no branch-specific Gauss input remains. -/
theorem wPnpc_branchFree_of_phaseModel
    {Gam : ProfiniteGrp} {q : ℕ} (h : ℕ) {P : ProfiniteGrp}
    (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom Gam (Tq q))
    (pro2 : ContinuousMonoidHom Gam P)
    (compat : ∀ g : (Gam : Type), nuTq q (tame g) = nuP (pro2 g))
    (M : wPnpcPhaseModel h nuP tame pro2 compat) :
    wPhBranchFreeSupply (2 * h + 2) nuP tame pro2 compat := by
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk _ _ _ hE2 hq0 hqe F
    hsimple hVne hnt m hm hcard l hl rho
  let DD := (blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  obtain ⟨d0, hd0, C⟩ := M T Blk hE2 hq0 hqe F l hl rho
  refine ⟨(DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod), inferInstance,
    wPnpcWallHandlePhase d0 DD.qbar h, C, ?_⟩
  exact wPnpc_wallHandlePhase_gaussSum_standardRam hd0 DD.hquad DD.hns
    ((Nat.card_eq_fintype_card (α := DD.Vmod)).symm.trans hcard) h

#print axioms wPnpcWallHandlePhase
#print axioms wPnpc_wallHandlePhase_gaussSum_standardRam
#print axioms wPnpcPhaseModel
#print axioms wPnpc_branchFree_of_phaseModel

end
end GQ2.Dyadic.Instances.NpcWordPhaseModel

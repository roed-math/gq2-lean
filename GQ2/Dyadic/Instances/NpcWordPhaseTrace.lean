/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhaseSeam
import GQ2.Dyadic.Instances.NpcUnramifiedScalar

/-!
# The scalar word-H² trace seam for procyclic N

This module records the blocker-independent scalar part of the Npc determinant route.
For the uniform resolver, the resolved word family has the tau coordinate in both
Heisenberg rows, so the generic word-H² trace seam produces a canonical trace
equivalence.

The result does not identify `QZero` with a graph-Hessian trace and does not prove the
unramified full-offset Hessian formula. Those are deliberately left to later layers.
-/

namespace GQ2.Dyadic.Instances.NpcWordPhaseTrace

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.Words.Npc
open GQ2.Dyadic.Certificates GQ2.Dyadic.NProcyclic
open GQ2.Dyadic.Instances.WordPhaseSeam

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-- At scalar coefficients the resolved Npc family is the same tau column in both rows. -/
theorem wPnpc_heisD1_resolvedFamily_apply
    {alpha r h q : ℕ} {d : EtaData}
    {C : Type} [Group C] [Finite C] [DistribMulAction C (ZMod 2)]
    (t : Marking (2 + 2 * h) C) (hα : 1 ≤ alpha) (hq : Even q)
    (x : Generator (2 + 2 * h) → ZMod 2) :
    heisD1 (A := ZMod 2) ⇑t
        (resolvedFamily alpha r h q d (4 * Monoid.exponent C)) x =
      ![x .tau, x .tau] :=
  GQ2.Dyadic.NProcyclicUnram.heisD1_npcFam_tauRow_of_split
    t (by decide) (fun g a ↦ ResidueLift.htriv_zmod2 (t g) a) hq hα x

/-- The scalar word-H2 trace for every displayed Npc family at the uniform resolver. -/
def wPnpcWordH2TraceEquiv
    {alpha r h q : ℕ} {d : EtaData}
    {C : Type} [Group C] [Finite C] [DistribMulAction C (ZMod 2)]
    (t : Marking (2 + 2 * h) C) (hα : 1 ≤ alpha) (hq : Even q)
    (hr : ∀ k, FreeGroup.lift ⇑t
      (resolvedFamily alpha r h q d (4 * Monoid.exponent C) k) = 1) :
    WordH2 ⇑t (resolvedFamily alpha r h q d (4 * Monoid.exponent C)) (ZMod 2) ≃+
      ZMod 2 :=
  wPsWordH2TraceEquiv ⇑t _ hr
    (resolvesAt_and_endpoint_uniformHeis
      (C := C) (A := ZMod 2) (by decide) hα hq d).2
    ⟨wPsCompactTauBasis h, by
      rw [wPnpc_heisD1_resolvedFamily_apply t hα hq]
      simp [wPsCompactTauBasis]⟩

#print axioms wPnpc_heisD1_resolvedFamily_apply
#print axioms wPnpcWordH2TraceEquiv

end
end GQ2.Dyadic.Instances.NpcWordPhaseTrace

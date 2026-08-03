/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoRelationModule
import GQ2.Dyadic.Count.HTwoModuleSurjectivity

/-!
# Transporting finite-target relation-module realizations to a profinite presentation

The Schreier transgression in `HTwoRelationModule` naturally constructs a cocycle on the
finite action target itself.  The global continuous-to-word comparison is phrased instead at a
finite quotient of the profinite source.  This file closes that harmless mismatch: for a finite
target map `rho`, use the open normal subgroup `ker rho` and pull the target cocycle back along
`G / ker rho -> C`.

No cohomological-dimension, duality, Euler-characteristic, or field-realization input is used.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2 GQ2.FoxH GQ2.Dyadic

section TargetTransport

variable {iota rel : Type*} [Fintype iota] [Fintype rel] [DecidableEq iota]
  {G A C : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction G A] [ContinuousSMul G A] [DistribMulAction C A]
  {gen : iota → G} {W : rel → PWord iota} {w : rel → FreeGroup iota}
  {c : iota → C}

local instance relationModuleGlobalQuotientDiscreteTopology
    (V : OpenNormalSubgroup G) : DiscreteTopology (G ⧸ V.toSubgroup) :=
  Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul V.toOpenSubgroup

omit [Fintype iota] [Fintype rel] [DecidableEq iota]
  [TotallyDisconnectedSpace G]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A] in
/-- Realization by cocycles on the finite action target gives the quotient-level realization
required by the global continuous-to-word comparison.  The witnessing quotient is `G / ker rho`.
-/
theorem moduleRelatorRealization_of_target
    (rho : ContinuousMonoidHom G C)
    (hc : ∀ i, rho (gen i) = c i)
    (htarget : ∀ r : rel → A, ∃ z : ModuleTwoCocycle C A,
      (fun k => moduleRel (W k) c z) - r ∈
        (heisD1 (A := A) c w).range) :
    ModuleRelatorRealization (A := A) W gen rho c w := by
  intro r
  have hopen : IsOpen ((rho.toMonoidHom.ker : Subgroup G) : Set G) :=
    (isOpen_discrete ({1} : Set C)).preimage rho.continuous_toFun
  let V : OpenNormalSubgroup G :=
    { toSubgroup := rho.toMonoidHom.ker
      isOpen' := hopen }
  have hV : V.toSubgroup ≤ rho.toMonoidHom.ker := by
    intro g hg
    exact hg
  let rhoV : (G ⧸ V.toSubgroup) →* C := quotientActionHom rho V hV
  letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A rhoV
  obtain ⟨z, hz⟩ := htarget r
  let zV : ModuleTwoCocycle (G ⧸ V.toSubgroup) A :=
    z.comap rhoV (fun _ _ => rfl)
  refine ⟨V, hV, zV, ?_⟩
  have hm : (fun i => rhoV (QuotientGroup.mk' V.toSubgroup (gen i))) = c := by
    funext i
    rw [quotientActionHom_mk]
    exact hc i
  have hrel :
      (fun k => moduleRel (W k)
        (fun i => QuotientGroup.mk' V.toSubgroup (gen i)) zV) =
        fun k => moduleRel (W k) c z := by
    funext k
    change moduleRel (W k)
      (fun i => QuotientGroup.mk' V.toSubgroup (gen i))
        (z.comap rhoV (fun _ _ => rfl)) = moduleRel (W k) c z
    rw [← moduleRel_comap (W k)
      (fun i => QuotientGroup.mk' V.toSubgroup (gen i)) z rhoV (fun _ _ => rfl), hm]
  rw [hrel]
  exact hz

end TargetTransport

end

end GQ2.Dyadic.Count

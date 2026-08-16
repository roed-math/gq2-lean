/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/

import GQ2.Dyadic.Instances.MpcMarkedHeadCompletion
import GQ2.Dyadic.Instances.MpcInitialRelatorBaseTrace

/-!
# Five cutoff-four initial-relator witnesses

The checked trace equalities are converted here into five concrete witnesses in the
range of `mpcMkCost 2`. These are the base cases for square-tower propagation.
-/

namespace GQ2.Dyadic.Instances.MpcInitialRelatorBase

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcOrb GQ2.Dyadic.Instances.MpcBld
open GQ2.Dyadic.Instances.MpcSx GQ2.Dyadic.Instances.MpcMk
open GQ2.Dyadic.Instances.MpcInitialRelatorBaseTrace
open GQ2.Roe.Labute GQ2.Dyadic.SqCore
open scoped commutatorElement

noncomputable section

private abbrev A : (DM 2 0 : Type) := dmA 2 0
private abbrev B : (DM 2 0 : Type) := dmB 2 0
private abbrev C : (DM 2 0 : Type) := dmC 2 0
private abbrev D : (DM 2 0 : Type) := dmD 2 0

private theorem gen_mem_one (x : (DM 2 0 : Type)) :
    x ∈ twoCentralSeries (DM 2 0 : Type) 1 := by simp

private theorem sq_mem_two (x : (DM 2 0 : Type)) :
    x ^ 2 ∈ twoCentralSeries (DM 2 0 : Type) 2 :=
  sq_mem_twoCentralSeries_succ _ (gen_mem_one x)

private theorem comm_kill_two (x y : (DM 2 0 : Type)) :
    commP x y ∈ mpcSxKill 2 :=
  mpcSx_commP_mem_kill x y (cfour_commP_mem_two x y)

private theorem comm_pivot_two (x y : (DM 2 0 : Type)) :
    commP x y ∈ mpcMkPivotKill 2 :=
  ⟨Subgroup.subset_closure ⟨x, y, rfl⟩, cfour_commP_mem_two x y⟩

private theorem B_sq_kill_two : B ^ 2 ∈ mpcSxKill 2 := by
  have h := mpcSx_pow_mem_kill 0
  norm_num at h ⊢
  exact h

private def rawUt (x : (DM 2 0 : Type))
    (hx : x ∈ twoCentralSeries (DM 2 0 : Type) 2) : MpcMkRawSource 2 :=
  (1, ⟨x, hx⟩, 1, 1)

private def rawUm (x : (DM 2 0 : Type))
    (hx : x ∈ twoCentralSeries (DM 2 0 : Type) 2) : MpcMkRawSource 2 :=
  (1, 1, ⟨x, hx⟩, 1)

private def rawUn (x : (DM 2 0 : Type))
    (hx : x ∈ twoCentralSeries (DM 2 0 : Type) 2) : MpcMkRawSource 2 :=
  (1, 1, 1, ⟨x, hx⟩)

def baseUtCSource : MpcMkRawSource 2 := rawUt (C ^ 2) (sq_mem_two C)
def baseUtDSource : MpcMkRawSource 2 := rawUt (D ^ 2) (sq_mem_two D)
def baseUmBSource : MpcMkRawSource 2 := rawUm (B ^ 2) (sq_mem_two B)
def baseUmCSource : MpcMkRawSource 2 := rawUm (C ^ 2) (sq_mem_two C)
def baseUnDSource : MpcMkRawSource 2 := rawUn (D ^ 2) (sq_mem_two D)

private def utCWitness : MpcMkCostDomain 2 :=
  (⟨commP A C, comm_kill_two A C⟩,
    ⟨commP A C * commP B C,
      Subgroup.mul_mem _ (comm_kill_two A C) (comm_kill_two B C)⟩,
    1,
    ⟨commP A B * commP A C,
      Subgroup.mul_mem _ (comm_kill_two A B) (comm_kill_two A C)⟩)

theorem base_utC_mem :
    mpcMkRawCost 2 (by omega) 1 1 baseUtCSource ∈
      MonoidHom.range (mpcMkCost 2 (by omega) 1 1) := by
  refine ⟨utCWitness, ?_⟩
  apply Subtype.ext
  rw [mpcMkRawCost_apply]
  exact level_utC2.symm

private def utDWitness : MpcMkCostDomain 2 :=
  (⟨commP A D, comm_kill_two A D⟩,
    ⟨commP A D * commP B D,
      Subgroup.mul_mem _ (comm_kill_two A D) (comm_kill_two B D)⟩,
    ⟨commP A B * commP A D,
      Subgroup.mul_mem _ (comm_pivot_two A B) (comm_pivot_two A D)⟩,
    1)

theorem base_utD_mem :
    mpcMkRawCost 2 (by omega) 1 1 baseUtDSource ∈
      MonoidHom.range (mpcMkCost 2 (by omega) 1 1) := by
  refine ⟨utDWitness, ?_⟩
  apply Subtype.ext
  rw [mpcMkRawCost_apply]
  exact level_utD2.symm

private def umBWitness : MpcMkCostDomain 2 :=
  (⟨commP A D * commP B D,
      Subgroup.mul_mem _ (comm_kill_two A D) (comm_kill_two B D)⟩,
    1, ⟨commP C D, comm_pivot_two C D⟩, 1)

theorem base_umB_mem :
    mpcMkRawCost 2 (by omega) 1 1 baseUmBSource ∈
      MonoidHom.range (mpcMkCost 2 (by omega) 1 1) := by
  refine ⟨umBWitness, ?_⟩
  apply Subtype.ext
  rw [mpcMkRawCost_apply]
  exact level_umB2.symm

private def umCWitness : MpcMkCostDomain 2 :=
  (⟨((commP A B * commP A C) * commP B C) * commP C D,
      Subgroup.mul_mem _
        (Subgroup.mul_mem _
          (Subgroup.mul_mem _ (comm_kill_two A B) (comm_kill_two A C))
          (comm_kill_two B C))
        (comm_kill_two C D)⟩,
    ⟨commP A B, comm_kill_two A B⟩,
    1, ⟨B ^ 2, B_sq_kill_two⟩)

theorem base_umC_mem :
    mpcMkRawCost 2 (by omega) 1 1 baseUmCSource ∈
      MonoidHom.range (mpcMkCost 2 (by omega) 1 1) := by
  refine ⟨umCWitness, ?_⟩
  apply Subtype.ext
  rw [mpcMkRawCost_apply]
  exact level_umC2.symm

private def unDWitness : MpcMkCostDomain 2 :=
  (⟨commP A B * commP C D,
      Subgroup.mul_mem _ (comm_kill_two A B) (comm_kill_two C D)⟩,
    ⟨commP A B, comm_kill_two A B⟩,
    ⟨commP C D, comm_pivot_two C D⟩,
    1)

theorem base_unD_mem :
    mpcMkRawCost 2 (by omega) 1 1 baseUnDSource ∈
      MonoidHom.range (mpcMkCost 2 (by omega) 1 1) := by
  refine ⟨unDWitness, ?_⟩
  apply Subtype.ext
  rw [mpcMkRawCost_apply]
  exact level_unD2.symm

#print axioms base_utC_mem
#print axioms base_utD_mem
#print axioms base_umB_mem
#print axioms base_umC_mem
#print axioms base_unD_mem

end
end GQ2.Dyadic.Instances.MpcInitialRelatorBase

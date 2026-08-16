/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/

import GQ2.Dyadic.Instances.MpcMarkedHeadCompletion
import GQ2.Dyadic.SqCore.GradedUniformTower

/-!
# Square-tower propagation for marked costs

This module proves that squaring a marked source advances its cost by the graded
square operation. It supplies the structural propagation step used by initial
relator absorption.
-/

namespace GQ2.Dyadic.Instances.MpcMk

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcWord GQ2.Dyadic.Instances.MpcBld
open GQ2.Dyadic.Instances.MpcLad GQ2.Dyadic.Instances.MpcSx
open GQ2.Roe.Labute GQ2.Dyadic.SqCore

noncomputable section

def mpcMkRawSquare {r : Nat} (u : MpcMkRawSource r) : MpcMkRawSource (r + 1) :=
  (⟨u.1 ^ 2, sq_mem_twoCentralSeries_succ _ u.1.2⟩,
    ⟨u.2.1 ^ 2, sq_mem_twoCentralSeries_succ _ u.2.1.2⟩,
    ⟨u.2.2.1 ^ 2, sq_mem_twoCentralSeries_succ _ u.2.2.1.2⟩,
    ⟨u.2.2.2 ^ 2, sq_mem_twoCentralSeries_succ _ u.2.2.2.2⟩)

def mpcMkMarkedSquare {r : Nat} (u : MpcMkCostDomain r) :
    MpcMkCostDomain (r + 1) :=
  (⟨u.1 ^ 2,
      ⟨Subgroup.pow_mem _ u.1.2.1 2,
        sq_mem_twoCentralSeries_succ _ u.1.2.2⟩⟩,
    ⟨u.2.1 ^ 2,
      ⟨Subgroup.pow_mem _ u.2.1.2.1 2,
        sq_mem_twoCentralSeries_succ _ u.2.1.2.2⟩⟩,
    ⟨u.2.2.1 ^ 2,
      ⟨Subgroup.pow_mem _ u.2.2.1.2.1 2,
        sq_mem_twoCentralSeries_succ _ u.2.2.1.2.2⟩⟩,
    ⟨u.2.2.2 ^ 2,
      ⟨Subgroup.pow_mem _ u.2.2.2.2.1 2,
        sq_mem_twoCentralSeries_succ _ u.2.2.2.2.2⟩⟩)

theorem mpcMk_incr_mem_succ {r : Nat}
    {us ut um un : (DM 2 0 : Type)}
    (hs : us ∈ twoCentralSeries (DM 2 0 : Type) r)
    (ht : ut ∈ twoCentralSeries (DM 2 0 : Type) r)
    (hm : um ∈ twoCentralSeries (DM 2 0 : Type) r)
    (hn : un ∈ twoCentralSeries (DM 2 0 : Type) r) :
    mpcBldIncr 1 1 us ut um un ∈
      twoCentralSeries (DM 2 0 : Type) (r + 1) := by
  have hs2 := sq_mem_twoCentralSeries_succ (DM 2 0 : Type) hs
  have hsA := cfive_commP_mem_succ hs (dmA 2 0)
  have hsB := cfive_commP_mem_succ hs (dmB 2 0)
  have hmD := cfive_commP_mem_succ hm (dmD 2 0)
  have hAut : commP (dmA 2 0) ut ∈
      twoCentralSeries (DM 2 0 : Type) (r + 1) := by
    rw [mpcSx_swap]
    exact Subgroup.inv_mem _ (cfive_commP_mem_succ ht (dmA 2 0))
  have hCun : commP (dmC 2 0) un ∈
      twoCentralSeries (DM 2 0 : Type) (r + 1) := by
    rw [mpcSx_swap]
    exact Subgroup.inv_mem _ (cfive_commP_mem_succ hn (dmC 2 0))
  simp only [mpcBldIncr, mpcWordLetB, mpcWordLetD, mul_one]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _
      (Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ hs2 hsA) hsB) hmD)
      hAut)
    hCun

theorem mpcMk_incr_square {r : Nat} (hr : 2 ≤ r)
    {us ut um un : (DM 2 0 : Type)}
    (hs : us ∈ twoCentralSeries (DM 2 0 : Type) r)
    (ht : ut ∈ twoCentralSeries (DM 2 0 : Type) r)
    (hm : um ∈ twoCentralSeries (DM 2 0 : Type) r)
    (hn : un ∈ twoCentralSeries (DM 2 0 : Type) r) :
    levelMk (DM 2 0 : Type) (r + 3)
        (mpcBldIncr 1 1 (us ^ 2) (ut ^ 2) (um ^ 2) (un ^ 2)) =
      levelMk (DM 2 0 : Type) (r + 3)
        ((mpcBldIncr 1 1 us ut um un) ^ 2) := by
  let f := levelMk (DM 2 0 : Type) (r + 3)
  let p1 := us ^ 2 * commP us (dmA 2 0)
  let p2 := commP us (dmB 2 0)
  let p3 := commP um (dmD 2 0)
  let p4 := commP (dmA 2 0) ut
  let p5 := commP (dmC 2 0) un
  have hp1 : p1 ∈ twoCentralSeries (DM 2 0 : Type) (r + 1) :=
    Subgroup.mul_mem _ (sq_mem_twoCentralSeries_succ _ hs)
      (cfive_commP_mem_succ hs (dmA 2 0))
  have hp2 : p2 ∈ twoCentralSeries (DM 2 0 : Type) (r + 1) :=
    cfive_commP_mem_succ hs (dmB 2 0)
  have hp3 : p3 ∈ twoCentralSeries (DM 2 0 : Type) (r + 1) :=
    cfive_commP_mem_succ hm (dmD 2 0)
  have hp4 : p4 ∈ twoCentralSeries (DM 2 0 : Type) (r + 1) := by
    dsimp only [p4]
    rw [mpcSx_swap]
    exact Subgroup.inv_mem _ (cfive_commP_mem_succ ht (dmA 2 0))
  have hp5 : p5 ∈ twoCentralSeries (DM 2 0 : Type) (r + 1) := by
    dsimp only [p5]
    rw [mpcSx_swap]
    exact Subgroup.inv_mem _ (cfive_commP_mem_succ hn (dmC 2 0))
  have hp12 : p1 * p2 ∈ twoCentralSeries (DM 2 0 : Type) (r + 1) :=
    Subgroup.mul_mem _ hp1 hp2
  have hp123 : (p1 * p2) * p3 ∈
      twoCentralSeries (DM 2 0 : Type) (r + 1) :=
    Subgroup.mul_mem _ hp12 hp3
  have hp1234 : ((p1 * p2) * p3) * p4 ∈
      twoCentralSeries (DM 2 0 : Type) (r + 1) :=
    Subgroup.mul_mem _ hp123 hp4
  have hb := gTower_engine_bundle (G := (DM 2 0 : Type)) hr hs (dmA 2 0)
  have h2 := gTower_engine_bracket (G := (DM 2 0 : Type)) hr hs (dmB 2 0)
  have h3 := gTower_engine_bracket (G := (DM 2 0 : Type)) hr hm (dmD 2 0)
  have h4 := gTower_engine_bracket' (G := (DM 2 0 : Type)) hr ht (dmA 2 0)
  have h5 := gTower_engine_bracket' (G := (DM 2 0 : Type)) hr hn (dmC 2 0)
  have hs5 := gTower_sq_congr (G := (DM 2 0 : Type))
    (k := r + 1) (by omega) hp1234 hp5
  have hs4 := gTower_sq_congr (G := (DM 2 0 : Type))
    (k := r + 1) (by omega) hp123 hp4
  have hs3 := gTower_sq_congr (G := (DM 2 0 : Type))
    (k := r + 1) (by omega) hp12 hp3
  have hs2 := gTower_sq_congr (G := (DM 2 0 : Type))
    (k := r + 1) (by omega) hp1 hp2
  simp only [map_mul] at hb h2 h3 h4 h5 hs5 hs4 hs3 hs2
  simp only [mpcBldIncr, mpcWordLetB, mpcWordLetD, mul_one, map_mul]
  rw [hb, h2, h3, h4, h5]
  rw [hs5, hs4, hs3, hs2]

theorem mpcMk_level_square_congr {r : Nat} (hr : 2 ≤ r)
    {x y : (DM 2 0 : Type)}
    (_hx : x ∈ twoCentralSeries (DM 2 0 : Type) (r + 1))
    (hy : y ∈ twoCentralSeries (DM 2 0 : Type) (r + 1))
    (hxy : levelMk (DM 2 0 : Type) (r + 2) x =
      levelMk (DM 2 0 : Type) (r + 2) y) :
    levelMk (DM 2 0 : Type) (r + 3) (x ^ 2) =
      levelMk (DM 2 0 : Type) (r + 3) (y ^ 2) := by
  have hd : y⁻¹ * x ∈ twoCentralSeries (DM 2 0 : Type) (r + 2) := by
    apply (lim_mem_twoCentralSeries_iff_levelMk (G := (DM 2 0 : Type))
      (r + 2) (y⁻¹ * x)).mpr
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have hs := gTower_sq_slack (G := (DM 2 0 : Type))
    (k := r + 1) (by omega) hy hd
  rw [show x = y * (y⁻¹ * x) by group]
  exact hs

#print axioms mpcMk_incr_square

end
end GQ2.Dyadic.Instances.MpcMk

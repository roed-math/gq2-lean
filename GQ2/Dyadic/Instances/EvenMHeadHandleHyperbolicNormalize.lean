/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.MarkedCore.HandleMixInst
import GQ2.Dyadic.MarkedCore.M

/-!
# Normalizing the hyperbolic head in the unit-handle branch

The hyperbolic forward marking sends the new sigma letter to `U C⁻¹`. Starting with
unramified rows `nu(U) = 1`, `nu(V) = 0`, and even `nu(C) = c`, the existing lifted
handle-plane diagonal move changes the U row to `1 + c`, keeps V zero, and preserves
every other row. Consequently the new hyperbolic head already has value one.

This adjusts the core equivalence before applying the fixed hyperbolic word. It avoids
a separate power substitution on sigma, and hence introduces no such analytic transport
obligation. The result is restricted to the unit-handle branch: a positive-level handle
of value `2^r` is not a unit head when `r > 0`. It supplies neither the subsequent
wild-shear Stokes theorem nor a complete source certificate.
-/

namespace GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicNormalize

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore

/-- A unit handle can be adjusted so that the hyperbolic head `U C⁻¹` has
unramified value one, without powering the new sigma letter. All non-selected
unramified rows, including the C row, are preserved. -/
theorem exists_hyperbolicUnitHead_of_strictHandle
    {alpha h : ℕ}
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (j : Fin h)
    (hU : toAdd (nu (dmGen alpha h (handleIdxU j))) = 1)
    (hV : nu (dmGen alpha h (handleIdxV j)) = 1)
    (qC : ℤ_[2]) (hC : toAdd (nu (dmC alpha h)) = 2 * qC) :
    ∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
      toAdd (nu (Psi (dmGen alpha h (handleIdxU j)))) =
        1 + toAdd (nu (dmC alpha h)) ∧
      nu (Psi (dmGen alpha h (handleIdxV j))) = 1 ∧
      (∀ i : Fin (coreRank h), i ≠ handleIdxU j → i ≠ handleIdxV j →
        nu (Psi (dmGen alpha h i)) = nu (dmGen alpha h i)) ∧
      toAdd (nu (Psi (dmGen alpha h (handleIdxU j)) *
        (Psi (dmC alpha h))⁻¹)) = 1 := by
  let w : ℤ_[2]ˣ := (GQ2.isUnit_one_add_two_mul qC).unit
  have hw : (w : ℤ_[2]) = 1 + 2 * qC :=
    (GQ2.isUnit_one_add_two_mul qC).unit_spec
  let F : Function.End (Fin (coreRank h) → ℤ_[2]) :=
    frameEnd (frameTheta j w)
  have hF : F ∈ Submonoid.closure (frameClearGens h) :=
    frameTheta_mem_clearGens j w
  obtain ⟨Psi, hmem, hbridge⟩ := exists_dmRealizes alpha h hF
  have hu : toAdd (nu (Psi (dmGen alpha h (handleIdxU j)))) =
      1 + toAdd (nu (dmC alpha h)) := by
    have H := congrFun (hbridge nu) (handleIdxU j)
    change toAdd (nu (Psi (dmGen alpha h (handleIdxU j)))) =
      frameTheta j w (nuFrame nu (dmGen alpha h)) (handleIdxU j) at H
    rw [frameTheta_handleU_self, smul_eq_mul] at H
    simp only [nuFrame_apply] at H
    rw [H, hU, mul_one, hw, hC]
  have hv : nu (Psi (dmGen alpha h (handleIdxV j))) = 1 := by
    apply Multiplicative.toAdd.injective
    have H := congrFun (hbridge nu) (handleIdxV j)
    change toAdd (nu (Psi (dmGen alpha h (handleIdxV j)))) =
      frameTheta j w (nuFrame nu (dmGen alpha h)) (handleIdxV j) at H
    rw [frameTheta_handleV_self, smul_eq_mul] at H
    simp only [nuFrame_apply] at H
    rw [H, hV, toAdd_one, mul_zero]
  have hfix : ∀ i : Fin (coreRank h), i ≠ handleIdxU j → i ≠ handleIdxV j →
      nu (Psi (dmGen alpha h i)) = nu (dmGen alpha h i) := by
    intro i hiU hiV
    apply Multiplicative.toAdd.injective
    have H := congrFun (hbridge nu) i
    change toAdd (nu (Psi (dmGen alpha h i))) =
      frameTheta j w (nuFrame nu (dmGen alpha h)) i at H
    rw [frameTheta_of_ne j _ w hiU hiV] at H
    exact H
  refine ⟨Psi, chiM_of_mem_dmClearAuts alpha h hmem, hu, hv, hfix, ?_⟩
  have hc : nu (Psi (dmC alpha h)) = nu (dmC alpha h) :=
    hfix 2
      (Fin.ne_of_val_ne (by rw [coreVal_two, handleIdxU_val]; omega))
      (Fin.ne_of_val_ne (by rw [coreVal_two, handleIdxV_val]; omega))
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hu, hc]
  ring

#print axioms exists_hyperbolicUnitHead_of_strictHandle

end
end GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicNormalize

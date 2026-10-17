/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.StokesNielsen
import GQ2.Dyadic.Instances.EvenHeisPure

/-!
# Word evaluations with zero generator jets

When every generator lift has zero primal and dual jet, all first jets vanish and the central
coordinate is exactly the mod-two exponent character of the generator charges. This is the
rank-generic cancellation used by tame averaging shadows; no base action is required trivial.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.FoxH

variable {X C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]

/-- The full lift, not just its central coordinate, splits into its zero-central
normalization and the central exponent character. -/
theorem heisWord_central_normalization
    (p : X → HeisLift A C) (r : FreeGroup X) :
    FreeGroup.lift p r =
      FreeGroup.lift (fun i ↦ ⟨(p i).a, (p i).l, 0, (p i).g⟩) r *
        HeisLift.zcHom (FreeGroup.lift (fun i ↦ Multiplicative.ofAdd (p i).z) r) := by
  let q : X → HeisLift A C := fun i ↦ ⟨(p i).a, (p i).l, 0, (p i).g⟩
  let eps : X → Multiplicative (ZMod 2) := fun i ↦ Multiplicative.ofAdd (p i).z
  let rhs : FreeGroup X →* HeisLift A C := {
    toFun w := FreeGroup.lift q w * HeisLift.zcHom (FreeGroup.lift eps w)
    map_one' := by simp
    map_mul' u v := by
      simp only [map_mul]
      exact Commute.mul_mul_mul_comm
        (HeisLift.zcHom_comm (FreeGroup.lift eps u) (FreeGroup.lift q v)).symm _ _
  }
  have H : FreeGroup.lift p = rhs := by
    apply FreeGroup.ext_hom
    intro i
    simp only [FreeGroup.lift_apply_of]
    ext <;> simp [rhs, q, eps, HeisLift.zcHom, HeisLift.zc]
  exact DFunLike.congr_fun H r

/-- Vanishing of the normalized word and the charged exponent slots kills the full lift. -/
theorem heisWord_eq_one_of_central_normalization
    [Fintype X] [DecidableEq X]
    (p : X → HeisLift A C) (r : FreeGroup X)
    (hnorm : FreeGroup.lift (fun i ↦
      (⟨(p i).a, (p i).l, 0, (p i).g⟩ : HeisLift A C)) r = 1)
    (heven : ∀ i, heisEps i r = 1 ∨ (p i).z = 0) :
    FreeGroup.lift p r = 1 := by
  rw [heisWord_central_normalization, hnorm, one_mul]
  have hz : FreeGroup.lift (fun i ↦ Multiplicative.ofAdd (p i).z) r = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_freeGroup_lift_zmod2]
    change (∑ i, Multiplicative.toAdd (heisEps i r) * (p i).z) = 0
    apply Finset.sum_eq_zero
    intro i _
    rcases heven i with hi | hi
    · simp [hi]
    · rw [hi, mul_zero]
  rw [hz, map_one]

theorem heisWord_mem_jetZero
    (p : X → HeisLift A C) (hp : ∀ i, p i ∈ heisJetZero A C) (r : FreeGroup X) :
    FreeGroup.lift p r ∈ heisJetZero A C := by
  induction r using FreeGroup.induction_on with
  | one => simp
  | of i => simpa using hp i
  | inv_of r ih => simpa using inv_mem ih
  | mul r s hr hs => simpa using mul_mem hr hs

theorem heisWord_z_of_jetZero
    [Fintype X] [DecidableEq X]
    (p : X → HeisLift A C) (hp : ∀ i, p i ∈ heisJetZero A C) (r : FreeGroup X) :
    (FreeGroup.lift p r).z =
      ∑ i, Multiplicative.toAdd (heisEps i r) * (p i).z := by
  rw [lift_central_normalization_z, toAdd_freeGroup_lift_zmod2]
  have hnorm : (fun i ↦ (⟨(p i).a, (p i).l, 0, (p i).g⟩ : HeisLift A C)) =
      heisGen (fun i ↦ (p i).g) 0 0 := by
    funext i
    rw [(hp i).1, (hp i).2]
    rfl
  rw [hnorm, (heisWord_zero_prim (fun i ↦ (p i).g) 0 r).2, zero_add]
  rfl

/-- An even exponent in every charged slot kills the central character. -/
theorem heisWord_z_eq_zero_of_jetZero
    [Fintype X] [DecidableEq X]
    (p : X → HeisLift A C) (hp : ∀ i, p i ∈ heisJetZero A C) (r : FreeGroup X)
    (heven : ∀ i, heisEps i r = 1 ∨ (p i).z = 0) :
    (FreeGroup.lift p r).z = 0 := by
  rw [heisWord_z_of_jetZero p hp r]
  apply Finset.sum_eq_zero
  intro i _
  rcases heven i with hi | hi
  · simp [hi]
  · rw [hi, mul_zero]

#print axioms heisWord_mem_jetZero
#print axioms heisWord_z_of_jetZero
#print axioms heisWord_z_eq_zero_of_jetZero
#print axioms heisWord_central_normalization
#print axioms heisWord_eq_one_of_central_normalization

end
end GQ2.Dyadic

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteReverse
import GQ2.Transgression

/-!
# Degree-two cohomology of finite elementary abelian two-groups

This file constructs the diagonal invariant from continuous inhomogeneous `H²` to quadratic
maps.  A cocycle is first normalized by subtracting its value at `(1,1)`; its diagonal is a
quadratic map and its polar form is the symmetrization of the normalized cocycle.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 ContCoh

section Normalized

variable (V : Type) [CommGroup V] [TopologicalSpace V] [IsTopologicalGroup V]
  [DiscreteTopology V] [Finite V]

local instance : DistribMulAction V (ZMod 2) := scalarActionZmodTwo V
local instance : ContinuousSMul V (ZMod 2) := scalarActionZmodTwo_continuousSMul V

/-- Normalize a two-cocycle by subtracting its common value on pairs involving the identity. -/
def elementaryNormalizedCocycle (z : Z2 V (ZMod 2))
    (v w : Additive V) : ZMod 2 :=
  z.1 (v.toMul, w.toMul) - z.1 (1, 1)

@[simp] theorem elementaryNormalizedCocycle_zero_left
    (z : Z2 V (ZMod 2)) (v : Additive V) :
    elementaryNormalizedCocycle V z 0 v = 0 := by
  have h := (mem_Z2_iff.mp z.2).2 1 1 v.toMul
  rw [scalarActionZmodTwo_triv V] at h
  change z.1 (1, v.toMul) - z.1 (1, 1) = 0
  rw [show z.1 (1, v.toMul) = z.1 (1, 1) by
    apply add_left_cancel (a := z.1 (1, v.toMul))
    simpa using h]
  exact sub_self _

@[simp] theorem elementaryNormalizedCocycle_zero_right
    (z : Z2 V (ZMod 2)) (v : Additive V) :
    elementaryNormalizedCocycle V z v 0 = 0 := by
  have h := (mem_Z2_iff.mp z.2).2 v.toMul 1 1
  rw [scalarActionZmodTwo_triv V] at h
  change z.1 (v.toMul, 1) - z.1 (1, 1) = 0
  rw [show z.1 (v.toMul, 1) = z.1 (1, 1) by
    apply add_right_cancel (b := z.1 (v.toMul, 1))
    simpa using h.symm]
  exact sub_self _

/-- The normalized cocycle identity, written additively on the elementary abelian group. -/
theorem elementaryNormalizedCocycle_identity
    (z : Z2 V (ZMod 2)) (u v w : Additive V) :
    elementaryNormalizedCocycle V z (u + v) w +
        elementaryNormalizedCocycle V z u v =
      elementaryNormalizedCocycle V z u (v + w) +
        elementaryNormalizedCocycle V z v w := by
  have h := (mem_Z2_iff.mp z.2).2 u.toMul v.toMul w.toMul
  rw [scalarActionZmodTwo_triv V] at h
  dsimp [elementaryNormalizedCocycle]
  linear_combination -h

end Normalized

section Quadratic

variable (V : Type) [CommGroup V] [TopologicalSpace V] [IsTopologicalGroup V]
  [DiscreteTopology V] [Finite V] [Fact (∀ v : V, v ^ 2 = 1)]

local instance : DistribMulAction V (ZMod 2) := scalarActionZmodTwo V
local instance : ContinuousSMul V (ZMod 2) := scalarActionZmodTwo_continuousSMul V

private theorem additive_exponent_two (v : Additive V) : v + v = 0 := by
  apply Additive.toMul.injective
  change v.toMul * v.toMul = 1
  simpa [pow_two] using (Fact.out : ∀ x : V, x ^ 2 = 1) v.toMul

local instance : Module (ZMod 2) (Additive V) :=
  AddCommGroup.zmodModule (fun v => by
    rw [two_nsmul]
    exact additive_exponent_two V v)

/-- The normalized diagonal of a cocycle. -/
def elementaryCocycleDiagonal (z : Z2 V (ZMod 2)) (v : Additive V) : ZMod 2 :=
  elementaryNormalizedCocycle V z v v

/-- The symmetrization of a normalized cocycle; this will be the polar form of its diagonal. -/
def elementaryCocyclePolar (z : Z2 V (ZMod 2)) (v w : Additive V) : ZMod 2 :=
  elementaryNormalizedCocycle V z v w + elementaryNormalizedCocycle V z w v

@[simp] theorem elementaryCocycleDiagonal_zero (z : Z2 V (ZMod 2)) :
    elementaryCocycleDiagonal V z 0 = 0 := by
  simp [elementaryCocycleDiagonal]

theorem elementaryCocyclePolar_comm (z : Z2 V (ZMod 2)) (v w : Additive V) :
    elementaryCocyclePolar V z v w = elementaryCocyclePolar V z w v := by
  simp only [elementaryCocyclePolar, add_comm]

/-- The normalized diagonal polarizes to the symmetrized cocycle. -/
theorem elementaryCocycleDiagonal_add (z : Z2 V (ZMod 2)) (v w : Additive V) :
    elementaryCocycleDiagonal V z (v + w) =
      elementaryCocycleDiagonal V z v + elementaryCocycleDiagonal V z w +
        elementaryCocyclePolar V z v w := by
  have h₁ := elementaryNormalizedCocycle_identity V z v w (v + w)
  have h₂ := elementaryNormalizedCocycle_identity V z w w v
  have hwvw : w + (v + w) = v := by
    calc
      w + (v + w) = v + (w + w) := by ac_rfl
      _ = v := by rw [additive_exponent_two V w, add_zero]
  rw [hwvw] at h₁
  rw [additive_exponent_two V w, elementaryNormalizedCocycle_zero_left,
    zero_add, add_comm w v] at h₂
  simp only [elementaryCocycleDiagonal, elementaryCocyclePolar]
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h₁ + h₂

theorem elementaryCocyclePolar_add_left (z : Z2 V (ZMod 2)) (u v w : Additive V) :
    elementaryCocyclePolar V z (u + v) w =
      elementaryCocyclePolar V z u w + elementaryCocyclePolar V z v w := by
  have h₁ := elementaryNormalizedCocycle_identity V z u v w
  have h₂ := elementaryNormalizedCocycle_identity V z w u v
  have h₃ := elementaryNormalizedCocycle_identity V z u w v
  rw [add_comm w u] at h₂
  rw [add_comm w v] at h₃
  simp only [elementaryCocyclePolar]
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h₁ + h₂ + h₃

theorem elementaryCocyclePolar_add_right (z : Z2 V (ZMod 2)) (u v w : Additive V) :
    elementaryCocyclePolar V z u (v + w) =
      elementaryCocyclePolar V z u v + elementaryCocyclePolar V z u w := by
  rw [elementaryCocyclePolar_comm V z u (v + w),
    elementaryCocyclePolar_add_left V z v w u,
    elementaryCocyclePolar_comm V z v u,
    elementaryCocyclePolar_comm V z w u]

/-- A cocycle determines a quadratic map through its normalized diagonal. -/
def elementaryCocycleQuadraticMap (z : Z2 V (ZMod 2)) :
    QuadraticMap (ZMod 2) (Additive V) (ZMod 2) := by
  let B : LinearMap.BilinForm (ZMod 2) (Additive V) :=
    AddMonoidHom.toZModLinearMap 2
      (AddMonoidHom.mk'
        (fun v => AddMonoidHom.toZModLinearMap 2
          (AddMonoidHom.mk' (elementaryCocyclePolar V z v)
            (elementaryCocyclePolar_add_right V z v)))
        (fun v w => by
          apply LinearMap.ext
          intro u
          exact elementaryCocyclePolar_add_left V z v w u))
  exact
    { toFun := elementaryCocycleDiagonal V z
      toFun_smul := by
        intro a v
        rcases ZMod.eq_zero_or_eq_one a with rfl | rfl
        · simp
        · simp
      exists_companion' := ⟨B, fun v w => by
        change elementaryCocycleDiagonal V z (v + w) =
          elementaryCocycleDiagonal V z v + elementaryCocycleDiagonal V z w +
            elementaryCocyclePolar V z v w
        exact elementaryCocycleDiagonal_add V z v w⟩ }

@[simp] theorem elementaryCocycleQuadraticMap_apply
    (z : Z2 V (ZMod 2)) (v : Additive V) :
    elementaryCocycleQuadraticMap V z v = elementaryNormalizedCocycle V z v v := rfl

/-- The normalized-diagonal construction is additive in the cocycle. -/
def elementaryCocycleQuadraticZ2 :
    Z2 V (ZMod 2) →+ QuadraticMap (ZMod 2) (Additive V) (ZMod 2) :=
  { toFun := elementaryCocycleQuadraticMap V
    map_zero' := by
      apply QuadraticMap.ext
      intro v
      simp [elementaryCocycleQuadraticMap_apply, elementaryNormalizedCocycle]
    map_add' := by
      intro z w
      apply QuadraticMap.ext
      intro v
      change (z.1 (v.toMul, v.toMul) + w.1 (v.toMul, v.toMul)) -
          (z.1 (1, 1) + w.1 (1, 1)) =
        (z.1 (v.toMul, v.toMul) - z.1 (1, 1)) +
          (w.1 (v.toMul, v.toMul) - w.1 (1, 1))
      abel }

/-- Coboundaries have zero normalized diagonal. -/
theorem elementaryCocycleQuadraticZ2_vanishes_on_B2
    (z : Z2 V (ZMod 2))
    (hz : z ∈ (B2 V (ZMod 2)).addSubgroupOf (Z2 V (ZMod 2))) :
    elementaryCocycleQuadraticZ2 V z = 0 := by
  rw [AddSubgroup.mem_addSubgroupOf] at hz
  obtain ⟨psi, hpsi, hdz⟩ := hz
  apply QuadraticMap.ext
  intro v
  have hv2 : v.toMul * v.toMul = 1 := by
    simpa [pow_two] using (Fact.out : ∀ x : V, x ^ 2 = 1) v.toMul
  have hdv := congrFun hdz (v.toMul, v.toMul)
  have hd1 := congrFun hdz (1, 1)
  dsimp only [dOne, AddMonoidHom.coe_mk] at hdv hd1
  change v.toMul • psi v.toMul - psi (v.toMul * v.toMul) + psi v.toMul =
    z.1 (v.toMul, v.toMul) at hdv
  change (1 : V) • psi 1 - psi (1 * 1) + psi 1 = z.1 (1, 1) at hd1
  rw [scalarActionZmodTwo_triv V, hv2] at hdv
  rw [scalarActionZmodTwo_triv V, one_mul] at hd1
  change z.1 (v.toMul, v.toMul) - z.1 (1, 1) = 0
  rw [← hdv, ← hd1]
  ring_nf
  simp [show (2 : ZMod 2) = 0 by decide, CharTwo.neg_eq]

/-- The well-defined normalized-diagonal map from cohomology classes to quadratic maps. -/
def elementaryH2ToQuadratic :
    H2 V (ZMod 2) →+ QuadraticMap (ZMod 2) (Additive V) (ZMod 2) :=
  QuotientAddGroup.lift _ (elementaryCocycleQuadraticZ2 V)
    (elementaryCocycleQuadraticZ2_vanishes_on_B2 V)

@[simp] theorem elementaryH2ToQuadratic_H2mk (z : Z2 V (ZMod 2)) :
    elementaryH2ToQuadratic V (H2mk V (ZMod 2) z) =
      elementaryCocycleQuadraticMap V z := by
  exact QuotientAddGroup.lift_mk' _ _ z

/-- A cocycle with zero normalized diagonal is a coboundary.  Its normalization is symmetric
by the polarization identity, so `Transgression.symm_cocycle_is_coboundary` applies. -/
theorem H2mk_eq_zero_of_elementaryCocycleQuadraticMap_eq_zero
    (z : Z2 V (ZMod 2)) (hz : elementaryCocycleQuadraticMap V z = 0) :
    H2mk V (ZMod 2) z = 0 := by
  let S : Additive V → Additive V → ZMod 2 := elementaryNormalizedCocycle V z
  have hdiag : ∀ v : Additive V, S v v = 0 := by
    intro v
    have h := QuadraticMap.congr_fun hz v
    change elementaryNormalizedCocycle V z v v = (0 :
      QuadraticMap (ZMod 2) (Additive V) (ZMod 2)) v at h
    simpa [S] using h
  have hsymm : ∀ v w : Additive V, S v w = S w v := by
    intro v w
    have h := elementaryCocycleDiagonal_add V z v w
    change S (v + w) (v + w) = S v v + S w w + (S v w + S w v) at h
    rw [hdiag v, hdiag w, hdiag (v + w), zero_add] at h
    have hp : S v w + S w v = 0 := by
      simpa [elementaryCocyclePolar, S] using h.symm
    exact (eq_neg_of_add_eq_zero_left hp).trans (CharTwo.neg_eq _)
  obtain ⟨theta, _htheta0, htheta⟩ :=
    GQ2.Transgression.symm_cocycle_is_coboundary
      (additive_exponent_two V) S
      (elementaryNormalizedCocycle_identity V z) hsymm hdiag
  let psi : C1 V (ZMod 2) :=
    ⟨fun v => theta (Additive.ofMul v) + z.1 (1, 1), continuous_of_discreteTopology⟩
  have hdpsi : dOne V (ZMod 2) psi.1 = z.1 := by
    funext p
    obtain ⟨v, w⟩ := p
    have h := htheta (Additive.ofMul v) (Additive.ofMul w)
    dsimp [S, elementaryNormalizedCocycle] at h
    change v • psi.1 w - psi.1 (v * w) + psi.1 v = z.1 (v, w)
    rw [scalarActionZmodTwo_triv V]
    dsimp [psi]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) -h
  apply (QuotientAddGroup.eq_zero_iff z).mpr
  rw [AddSubgroup.mem_addSubgroupOf]
  exact ⟨psi.1, psi.2, hdpsi⟩

/-- The normalized diagonal is injective on `H²`. -/
theorem elementaryH2ToQuadratic_injective :
    Function.Injective (elementaryH2ToQuadratic V) := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hmap : elementaryH2ToQuadratic V (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ := H2mk_surjective (G := V) (M := ZMod 2) (x - y)
  rw [← hz]
  apply H2mk_eq_zero_of_elementaryCocycleQuadraticMap_eq_zero V z
  have hmapz : elementaryH2ToQuadratic V (H2mk V (ZMod 2) z) = 0 := by
    rw [hz]
    exact hmap
  rwa [elementaryH2ToQuadratic_H2mk] at hmapz

end Quadratic

#print axioms elementaryNormalizedCocycle_identity
#print axioms elementaryCocycleQuadraticMap
#print axioms elementaryH2ToQuadratic
#print axioms elementaryH2ToQuadratic_injective

end

end GQ2.Dyadic.LSquare

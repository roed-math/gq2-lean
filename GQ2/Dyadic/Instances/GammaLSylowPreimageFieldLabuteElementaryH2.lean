/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteReverse
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteTransgression
import GQ2.Dyadic.Count.H3CompletedQuadraticRelation
import GQ2.Transgression
import Mathlib.Data.Finset.Sym

/-!
# Degree-two cohomology of finite elementary abelian two-groups

This file constructs the diagonal invariant from continuous inhomogeneous `H²` to quadratic
maps.  A cocycle is first normalized by subtracting its value at `(1,1)`; its diagonal is a
quadratic map and its polar form is the symmetrization of the normalized cocycle.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Roe.Labute ContCoh

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

local instance : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite

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

/-- The bilinear refinement selected from a basis turns a quadratic map back into a cocycle. -/
def elementaryQuadraticCocycle
    (Q : QuadraticMap (ZMod 2) (Additive V) (ZMod 2)) : Z2 V (ZMod 2) := by
  let bm := Module.finBasis (ZMod 2) (Additive V)
  let B := Q.toBilin bm
  refine ⟨fun p => B (Additive.ofMul p.1) (Additive.ofMul p.2), ?_⟩
  apply mem_Z2_iff.mpr
  refine ⟨continuous_of_discreteTopology, ?_⟩
  intro g h k
  rw [scalarActionZmodTwo_triv V]
  change B (Additive.ofMul h) (Additive.ofMul k) +
      B (Additive.ofMul g) (Additive.ofMul (h * k)) =
    B (Additive.ofMul (g * h)) (Additive.ofMul k) +
      B (Additive.ofMul g) (Additive.ofMul h)
  change B (Additive.ofMul h) (Additive.ofMul k) +
      B (Additive.ofMul g) (Additive.ofMul h + Additive.ofMul k) =
    B (Additive.ofMul g + Additive.ofMul h) (Additive.ofMul k) +
      B (Additive.ofMul g) (Additive.ofMul h)
  simp only [map_add, LinearMap.add_apply]
  abel

/-- The cocycle built from a quadratic map has that map as normalized diagonal. -/
@[simp] theorem elementaryCocycleQuadraticMap_elementaryQuadraticCocycle
    (Q : QuadraticMap (ZMod 2) (Additive V) (ZMod 2)) :
    elementaryCocycleQuadraticMap V (elementaryQuadraticCocycle V Q) = Q := by
  let bm := Module.finBasis (ZMod 2) (Additive V)
  apply QuadraticMap.ext
  intro v
  change Q.toBilin bm v v - Q.toBilin bm 0 0 = Q v
  rw [map_zero, sub_zero]
  exact DFunLike.congr_fun (QuadraticMap.toQuadraticMap_toBilin Q bm) v

/-- Every quadratic map occurs as the normalized diagonal of an `H²` class. -/
theorem elementaryH2ToQuadratic_surjective :
    Function.Surjective (elementaryH2ToQuadratic V) := by
  intro Q
  refine ⟨H2mk V (ZMod 2) (elementaryQuadraticCocycle V Q), ?_⟩
  simp

/-- Cohomology of a finite elementary abelian two-group is additively equivalent to its
quadratic maps. -/
def elementaryH2EquivQuadratic :
    H2 V (ZMod 2) ≃+ QuadraticMap (ZMod 2) (Additive V) (ZMod 2) :=
  AddEquiv.ofBijective (elementaryH2ToQuadratic V)
    ⟨elementaryH2ToQuadratic_injective V, elementaryH2ToQuadratic_surjective V⟩

/-! ### Coordinates and counting quadratic maps -/

/-- The canonical finite basis used to coordinatize quadratic maps. -/
def elementaryQuadraticBasis :
    Module.Basis (Fin (Module.finrank (ZMod 2) (Additive V))) (ZMod 2) (Additive V) :=
  Module.finBasis (ZMod 2) (Additive V)

/-- Coordinates of a quadratic map, indexed by unordered pairs of basis vectors. -/
def elementaryQuadraticBasisCode
    (Q : QuadraticMap (ZMod 2) (Additive V) (ZMod 2)) :
    Sym2 (Fin (Module.finrank (ZMod 2) (Additive V))) → ZMod 2 :=
  Sym2.lift ⟨fun i j =>
    Q.toBilin (elementaryQuadraticBasis V)
      (elementaryQuadraticBasis V (min i j))
      (elementaryQuadraticBasis V (max i j)), by
        intro i j
        change Q.toBilin (elementaryQuadraticBasis V)
            (elementaryQuadraticBasis V (min i j))
            (elementaryQuadraticBasis V (max i j)) =
          Q.toBilin (elementaryQuadraticBasis V)
            (elementaryQuadraticBasis V (min j i))
            (elementaryQuadraticBasis V (max j i))
        rw [min_comm i j, max_comm i j]⟩

/-- The upper-triangular bilinear map with prescribed unordered-pair coordinates. -/
def elementaryUpperBilin
    (f : Sym2 (Fin (Module.finrank (ZMod 2) (Additive V))) → ZMod 2) :
    LinearMap.BilinForm (ZMod 2) (Additive V) :=
  (elementaryQuadraticBasis V).constr (ZMod 2) fun i =>
    (elementaryQuadraticBasis V).constr (ZMod 2) fun j =>
      if i ≤ j then f s(i, j) else 0

@[simp] theorem elementaryUpperBilin_basis
    (f : Sym2 (Fin (Module.finrank (ZMod 2) (Additive V))) → ZMod 2)
    (i j : Fin (Module.finrank (ZMod 2) (Additive V))) :
    elementaryUpperBilin V f (elementaryQuadraticBasis V i)
        (elementaryQuadraticBasis V j) =
      if i ≤ j then f s(i, j) else 0 := by
  unfold elementaryUpperBilin
  rw [(elementaryQuadraticBasis V).constr_basis,
    (elementaryQuadraticBasis V).constr_basis]

/-- Decode unordered-pair coordinates as the diagonal of their upper-triangular bilinear map. -/
def elementaryQuadraticOfBasisCode
    (f : Sym2 (Fin (Module.finrank (ZMod 2) (Additive V))) → ZMod 2) :
    QuadraticMap (ZMod 2) (Additive V) (ZMod 2) :=
  (elementaryUpperBilin V f).toQuadraticMap

theorem elementaryUpperBilin_basisCode
    (Q : QuadraticMap (ZMod 2) (Additive V) (ZMod 2)) :
    elementaryUpperBilin V (elementaryQuadraticBasisCode V Q) =
      Q.toBilin (elementaryQuadraticBasis V) := by
  apply (elementaryQuadraticBasis V).ext
  intro i
  apply (elementaryQuadraticBasis V).ext
  intro j
  obtain hij | rfl | hij := lt_trichotomy i j
  · simp [elementaryQuadraticBasisCode, QuadraticMap.toBilin_apply, hij, hij.le,
      hij.ne, hij.ne']
  · simp [elementaryQuadraticBasisCode, QuadraticMap.toBilin_apply]
  · simp [elementaryQuadraticBasisCode, QuadraticMap.toBilin_apply, hij,
      not_le_of_gt hij, not_lt_of_ge hij.le, hij.ne, hij.ne']

@[simp] theorem elementaryQuadraticOfBasisCode_basisCode
    (Q : QuadraticMap (ZMod 2) (Additive V) (ZMod 2)) :
    elementaryQuadraticOfBasisCode V (elementaryQuadraticBasisCode V Q) = Q := by
  rw [elementaryQuadraticOfBasisCode, elementaryUpperBilin_basisCode,
    QuadraticMap.toQuadraticMap_toBilin]

theorem elementaryToBilin_quadraticOfBasisCode
    (f : Sym2 (Fin (Module.finrank (ZMod 2) (Additive V))) → ZMod 2) :
    (elementaryQuadraticOfBasisCode V f).toBilin (elementaryQuadraticBasis V) =
      elementaryUpperBilin V f := by
  apply (elementaryQuadraticBasis V).ext
  intro i
  apply (elementaryQuadraticBasis V).ext
  intro j
  obtain hij | rfl | hij := lt_trichotomy i j
  · simp [elementaryQuadraticOfBasisCode, QuadraticMap.toBilin_apply, hij, hij.le,
      hij.ne, hij.ne', LinearMap.BilinMap.polar_toQuadraticMap, not_le_of_gt hij]
  · simp [elementaryQuadraticOfBasisCode, QuadraticMap.toBilin_apply]
  · simp [elementaryQuadraticOfBasisCode, QuadraticMap.toBilin_apply, hij,
      not_le_of_gt hij, not_lt_of_ge hij.le, hij.ne, hij.ne']

@[simp] theorem elementaryQuadraticBasisCode_quadraticOfBasisCode
    (f : Sym2 (Fin (Module.finrank (ZMod 2) (Additive V))) → ZMod 2) :
    elementaryQuadraticBasisCode V (elementaryQuadraticOfBasisCode V f) = f := by
  funext p
  induction p using Sym2.ind with
  | _ i j =>
      change (elementaryQuadraticOfBasisCode V f).toBilin (elementaryQuadraticBasis V)
          (elementaryQuadraticBasis V (min i j))
          (elementaryQuadraticBasis V (max i j)) = f s(i, j)
      rw [elementaryToBilin_quadraticOfBasisCode, elementaryUpperBilin_basis]
      rcases le_total i j with hij | hji
      · simp [min_eq_left hij, max_eq_right hij, hij]
      · simp [min_eq_right hji, max_eq_left hji, hji, Sym2.eq_swap]

/-- Quadratic maps are freely parametrized by unordered pairs of basis indices. -/
def elementaryQuadraticEquivBasisCode :
    QuadraticMap (ZMod 2) (Additive V) (ZMod 2) ≃
      (Sym2 (Fin (Module.finrank (ZMod 2) (Additive V))) → ZMod 2) where
  toFun := elementaryQuadraticBasisCode V
  invFun := elementaryQuadraticOfBasisCode V
  left_inv := elementaryQuadraticOfBasisCode_basisCode V
  right_inv := elementaryQuadraticBasisCode_quadraticOfBasisCode V

/-- There are `2^(d(d+1)/2)` quadratic maps on an elementary abelian two-group of
`F₂`-dimension `d`. -/
theorem card_elementaryQuadraticMap :
    Nat.card (QuadraticMap (ZMod 2) (Additive V) (ZMod 2)) =
      2 ^ lowerTwoCentralQuadraticDimension
        (Module.finrank (ZMod 2) (Additive V)) := by
  let d := Module.finrank (ZMod 2) (Additive V)
  have hsym : Nat.card (Sym2 (Fin d)) = Nat.choose (d + 1) 2 := by
    rw [Nat.card_eq_fintype_card]
    change (Finset.univ : Finset (Sym2 (Fin d))).card = Nat.choose (d + 1) 2
    rw [show (Finset.univ : Finset (Sym2 (Fin d))) =
        (Finset.univ : Finset (Fin d)).sym2 by ext p; simp]
    rw [Finset.card_sym2, Finset.card_univ, Fintype.card_fin]
  rw [Nat.card_congr (elementaryQuadraticEquivBasisCode V), Nat.card_fun,
    Nat.card_zmod, hsym]
  dsimp only [d]
  unfold lowerTwoCentralQuadraticDimension
  rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm]

/-- Degree-two mod-`2` cohomology of a finite elementary abelian two-group has the expected
cardinality.  The dimension is recovered from the asserted order of the group. -/
theorem card_H2_finiteElementary (d : ℕ) (hcard : Nat.card V = 2 ^ d) :
    Nat.card (H2 V (ZMod 2)) =
      2 ^ lowerTwoCentralQuadraticDimension d := by
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive V) = 2 ^ d := by
    rw [← hcard, ← Nat.card_congr Additive.toMul]
    simpa using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)).symm
  have hdim : Module.finrank (ZMod 2) (Additive V) = d :=
    Nat.pow_right_injective (by omega) hpow
  calc
    Nat.card (H2 V (ZMod 2)) =
        Nat.card (QuadraticMap (ZMod 2) (Additive V) (ZMod 2)) :=
      Nat.card_congr (elementaryH2EquivQuadratic V).toEquiv
    _ = 2 ^ lowerTwoCentralQuadraticDimension
          (Module.finrank (ZMod 2) (Additive V)) := card_elementaryQuadraticMap V
    _ = 2 ^ lowerTwoCentralQuadraticDimension d := by rw [hdim]

end Quadratic

/-- The standard finite elementary-abelian `H²` cardinal formula, discharged internally by
normalized cocycles and quadratic maps. -/
theorem finiteElementaryAbelianTwoH2CardFormula :
    FiniteElementaryAbelianTwoH2CardFormula := by
  intro V _ _ _ _ _ htwo d hcard
  letI : Fact (∀ v : V, v ^ 2 = 1) := ⟨htwo⟩
  exact card_H2_finiteElementary V d hcard

/-! ### The literal improved one-relator model in degree two -/

/-- The improved square word is a Frattini relator: it dies under every elementary-abelian
`2`-marking.  This uses the literal square/commutator presentation, not an abstract
one-relator hypothesis. -/
theorem sqNatWord_isFrattini (h : ℕ) :
    (MarkedCore.sqNatWord h).IsFrattini := by
  intro nu
  change SqCore.sqRelWord nu = 1
  rw [SqCore.sqRelWord_comm]
  have hsquare (x : Multiplicative (ZMod 2)) : x ^ 2 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul, Count.zmod2_add_self]
  rw [show 4 = 2 * 2 by omega, pow_mul, hsquare, hsquare]
  simp

/-- The literal improved relation together with the canonical marked generators is a marked
relator in the generic one-relator cohomology API. -/
theorem markedRelator_DSq (h : ℕ) :
    WordCoh.MarkedRelator (SqCore.DSq h : Type)
      (MarkedCore.sqNatWord h) (SqCore.sqGen h) :=
  ⟨sqNatWord_isFrattini h, SqCore.dsq_relation h⟩

/-- The generic marked-presentation API is supplied directly by the defining universal
property of `DSq h`. -/
noncomputable def presentedBy_DSq (h : ℕ) :
    WordCoh.PresentedBy (SqCore.DSq h : Type)
      (MarkedCore.sqNatWord h) (SqCore.sqGen h) where
  liftHom := fun hP nu hnu => SqCore.sqLiftHom h hP nu hnu
  liftHom_mark := fun hP nu hnu i => SqCore.sqLiftHom_gen h hP nu hnu i
  hom_ext := fun phi psi hgen => SqCore.dsq_hom_ext phi psi hgen

/-- The `Y²` coefficient functional on the literal quadratic initial form. -/
def dsqYQuadraticMatrix (h : ℕ)
    (i j : Fin (SqCore.sqRank h)) : ZMod 2 :=
  if i = 2 ∧ j = 2 then 1 else 0

private theorem sqZero_ne_two (h : ℕ) :
    (0 : Fin (SqCore.sqRank h)) ≠ 2 := by
  intro heq
  have := congrArg Fin.val heq
  rw [SqCore.sqVal_zero, SqCore.sqVal_two] at this
  omega

private theorem sqOne_ne_two (h : ℕ) :
    (1 : Fin (SqCore.sqRank h)) ≠ 2 := by
  intro heq
  have := congrArg Fin.val heq
  rw [SqCore.sqVal_one, SqCore.sqVal_two] at this
  omega

private theorem sqHandleIdxU_ne_two {h : ℕ} (j : Fin h) :
    SqCore.sqHandleIdxU j ≠ (2 : Fin (SqCore.sqRank h)) := by
  intro heq
  have := congrArg Fin.val heq
  rw [SqCore.sqHandleIdxU_val, SqCore.sqVal_two] at this
  omega

private theorem sqHandleIdxV_ne_two {h : ℕ} (j : Fin h) :
    SqCore.sqHandleIdxV j ≠ (2 : Fin (SqCore.sqRank h)) := by
  intro heq
  have := congrArg Fin.val heq
  rw [SqCore.sqHandleIdxV_val, SqCore.sqVal_two] at this
  omega

/-- The constructor table reads the `Y²` coefficient as one.  This is the nonzero entry of
the improved relator used below to detect the unique nonzero `H²` class. -/
theorem sqRelatorQuadraticInitialGram_dsqY (h : ℕ) :
    sqRelatorQuadraticInitialGram h (dsqYQuadraticMatrix h) = 1 := by
  rw [sqRelatorQuadraticInitialGram]
  simp [dsqYQuadraticMatrix, sqZero_ne_two h, sqOne_ne_two h,
    sqHandleIdxU_ne_two, sqHandleIdxV_ne_two]

/-- The detector associated to the `Y²` matrix is simply the cup cocycle of the
`Y`-coordinate character. -/
theorem sqQuadraticDetectorCocycle_dsqY (h : ℕ)
    (p q : SqQuadraticDetectorBase h) :
    (sqQuadraticDetectorCocycle h (dsqYQuadraticMatrix h)).κ p q =
      Multiplicative.toAdd p 2 * Multiplicative.toAdd q 2 := by
  classical
  change (∑ i, ∑ j, Multiplicative.toAdd p i * Multiplicative.toAdd q j *
      dsqYQuadraticMatrix h i j) = _
  rw [Finset.sum_eq_single (2 : Fin (SqCore.sqRank h))]
  · rw [Finset.sum_eq_single (2 : Fin (SqCore.sqRank h))]
    · simp [dsqYQuadraticMatrix]
    · intro j hj hne
      simp [dsqYQuadraticMatrix, hne]
    · simp
  · intro i hi hne
    apply Finset.sum_eq_zero
    intro j hj
    simp [dsqYQuadraticMatrix, hne]
  · simp

/-- The degree-one `Y`-coordinate character of the elementary-abelian Magnus quotient. -/
noncomputable def dsqYCharacter (h : ℕ) :
    ContinuousMonoidHom (SqCore.DSq h : Type) (Multiplicative (ZMod 2)) where
  toFun g := Multiplicative.ofAdd
    (sqMagnusOneCoordinate h 2 (Multiplicative.toAdd (sqMagnusOneHom h g)))
  map_one' := by simp
  map_mul' g k := by
    apply Multiplicative.toAdd.injective
    simp
  continuous_toFun := by
    exact (continuous_of_discreteTopology : Continuous fun q : SqMagnusOneTarget h =>
      sqMagnusOneCoordinate h 2 (Multiplicative.toAdd q)).comp
        (sqMagnusOneHom h).continuous_toFun

local instance (h : ℕ) : DistribMulAction (SqCore.DSq h : Type) (ZMod 2) :=
  scalarActionZmodTwo _

local instance (h : ℕ) : ContinuousSMul (SqCore.DSq h : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- The corresponding normalized continuous `1`-cocycle. -/
noncomputable def dsqYZOne (h : ℕ) : Z1 (SqCore.DSq h : Type) (ZMod 2) :=
  Count.homEquivZ1 (dsqYCharacter h)

/-- The corresponding degree-one cohomology class. -/
noncomputable def dsqYHOne (h : ℕ) : H1 (SqCore.DSq h : Type) (ZMod 2) :=
  H1mk _ _ (dsqYZOne h)

/-- A cocycle representative for the cup square of the `Y`-coordinate class. -/
noncomputable def dsqYCupZTwo (h : ℕ) : Z2 (SqCore.DSq h : Type) (ZMod 2) :=
  ⟨cup11Fun AddMonoidHom.mul (dsqYZOne h).1 (dsqYZOne h).1,
    cup11_mem_Z2 AddMonoidHom.mul (fun _ _ _ => rfl) (dsqYZOne h) (dsqYZOne h)⟩

/-- The literal cup square is represented by `dsqYCupZTwo`. -/
theorem dsqYHOne_cup_self (h : ℕ) :
    trivialCupPairing 2 (SqCore.DSq h : Type) (fun _ _ => rfl)
        (dsqYHOne h) (dsqYHOne h) =
      H2mk (SqCore.DSq h : Type) (ZMod 2) (dsqYCupZTwo h) := by
  rfl

/-- The one-relator obstruction evaluates the `Y` cup square to one.  The calculation is
the constructor table of the literal improved relator: its quadratic initial form contains
`Y²` with coefficient one. -/
theorem obsH2_DSq_dsqYCup (h : ℕ) :
    WordCoh.obsH2 (fun _ _ => rfl) (MarkedCore.sqNatWord h)
        (SqCore.sqGen h) (markedRelator_DSq h)
        (H2mk (SqCore.DSq h : Type) (ZMod 2) (dsqYCupZTwo h)) = 1 := by
  let rho := (sqMagnusOneHom h).toMonoidHom
  let c := sqQuadraticDetectorCocycle h (dsqYQuadraticMatrix h)
  have hfactor : ∀ g k : (SqCore.DSq h : Type),
      (dsqYCupZTwo h).1 (g, k) =
        (WordCoh.ofDRCoh c).κ (rho g) (rho k) := by
    intro g k
    change (dsqYCupZTwo h).1 (g, k) = c.κ (rho g) (rho k)
    rw [sqQuadraticDetectorCocycle_dsqY]
    simp [dsqYCupZTwo, cup11Fun, dsqYZOne, dsqYCharacter, c, rho,
      scalarActionZmodTwo_triv]
    rfl
  rw [WordCoh.obsH2_eq_of_factor (fun _ _ => rfl)
    (MarkedCore.sqNatWord h) (SqCore.sqGen h) (markedRelator_DSq h)
    (dsqYCupZTwo h) rho (WordCoh.ofDRCoh c) hfactor]
  have hmark : (fun i => rho (SqCore.sqGen h i)) = sqMagnusOneMark h := by
    funext i
    exact sqMagnusOneHom_gen h i
  rw [hmark, WordCoh.relZ_ofDRCoh]
  change (SqCore.sqRelWord (fun i => MarkedCore.centLift c (sqMagnusOneMark h i))).fib = 1
  rw [sqRelWord_centLift_fib_eq_quadraticInitialGram
      (sqQuadraticDetectorCocycle_isCup h (dsqYQuadraticMatrix h)),
    show (fun i j => c.κ (sqMagnusOneMark h i) (sqMagnusOneMark h j)) =
        dsqYQuadraticMatrix h from funext fun i => funext fun j =>
          sqQuadraticDetectorCocycle_mark h (dsqYQuadraticMatrix h) i j,
    sqRelatorQuadraticInitialGram_dsqY]

/-- The `Y` cup square is a nonzero class in the cohomology of the literal improved model. -/
theorem dsqYHOne_cup_self_ne_zero (h : ℕ) :
    trivialCupPairing 2 (SqCore.DSq h : Type) (fun _ _ => rfl)
        (dsqYHOne h) (dsqYHOne h) ≠ 0 := by
  rw [dsqYHOne_cup_self]
  intro hzero
  have hobs := congrArg
    (WordCoh.obsH2 (fun _ _ => rfl) (MarkedCore.sqNatWord h)
      (SqCore.sqGen h) (markedRelator_DSq h)) hzero
  rw [obsH2_DSq_dsqYCup, map_zero] at hobs
  exact one_ne_zero hobs

/-- The completed improved one-relator model has one-dimensional mod-`2` `H²`. -/
theorem card_H2_DSq (h : ℕ) :
    Nat.card (H2 (SqCore.DSq h : Type) (ZMod 2)) = 2 := by
  letI : Finite (H2 (SqCore.DSq h : Type) (ZMod 2)) :=
    WordCoh.finite_H2 (fun _ _ => rfl) (MarkedCore.sqNatWord h)
      (SqCore.sqGen h) (markedRelator_DSq h) (presentedBy_DSq h)
      (SqCore.isProP_DSq h)
  have hle : Nat.card (H2 (SqCore.DSq h : Type) (ZMod 2)) ≤ 2 :=
    WordCoh.card_H2_le_two (fun _ _ => rfl) (MarkedCore.sqNatWord h)
      (SqCore.sqGen h) (markedRelator_DSq h) (presentedBy_DSq h)
      (SqCore.isProP_DSq h)
  letI : Nontrivial (H2 (SqCore.DSq h : Type) (ZMod 2)) :=
    ⟨trivialCupPairing 2 (SqCore.DSq h : Type) (fun _ _ => rfl)
        (dsqYHOne h) (dsqYHOne h), 0, dsqYHOne_cup_self_ne_zero h⟩
  have hgt : 1 < Nat.card (H2 (SqCore.DSq h : Type) (ZMod 2)) :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  omega

/-- The cohomological generator rank of the improved model is its literal marking rank. -/
theorem demushkinRank_DSq (h : ℕ) :
    demushkinRank 2 (SqCore.DSq h : Type) = SqCore.sqRank h := by
  rw [← lowerTwoCentralHilbertCoefficient_zero_eq_demushkinRank
    (dsqFinsetTopGen h) (SqCore.isProP_DSq h)]
  exact dsq_lowerTwoCentralHilbertCoefficient_zero h

/-- Inflation from the Frattini quotient onto model `H²` is surjective.  The explicit
nonzero `Y` cup square supplies the sole nonzero target class. -/
theorem lowerTwoCentralH2InflationSurjective_DSq (h : ℕ) :
    LowerTwoCentralH2InflationSurjective (SqCore.DSq h : Type) := by
  let Q := levelQuot (SqCore.DSq h : Type) 2
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  dsimp only [LowerTwoCentralH2InflationSurjective]
  obtain ⟨yQ, hyQ⟩ := lowerTwoCentralH1Inflation_surjective
    (SqCore.DSq h : Type) (dsqYHOne h)
  let cupQ := trivialCupPairing 2 Q (fun _ _ => rfl) yQ yQ
  have hcupImage : lowerTwoCentralH2Inflation (SqCore.DSq h : Type) cupQ =
      trivialCupPairing 2 (SqCore.DSq h : Type) (fun _ _ => rfl)
        (dsqYHOne h) (dsqYHOne h) := by
    dsimp only [cupQ]
    rw [lowerTwoCentralH2Inflation_trivialCupPairing, hyQ]
  letI : Finite (H2 (SqCore.DSq h : Type) (ZMod 2)) :=
    Nat.finite_of_card_ne_zero (by rw [card_H2_DSq]; decide)
  obtain ⟨w, hw, hwuniq⟩ :=
    (Nat.card_eq_two_iff' (0 : H2 (SqCore.DSq h : Type) (ZMod 2))).mp
      (card_H2_DSq h)
  intro z
  by_cases hz : z = 0
  · exact ⟨0, by rw [map_zero, hz]⟩
  · have hcupw : trivialCupPairing 2 (SqCore.DSq h : Type) (fun _ _ => rfl)
        (dsqYHOne h) (dsqYHOne h) = w :=
      hwuniq _ (dsqYHOne_cup_self_ne_zero h)
    have hzw : z = w := hwuniq z hz
    refine ⟨cupQ, ?_⟩
    rw [hcupImage, hcupw, hzw]

/-- The elementary Frattini quotient of the improved model has the expected degree-two
cohomology cardinality. -/
theorem lowerTwoCentralElementaryH2CardFormula_DSq (h : ℕ) :
    LowerTwoCentralElementaryH2CardFormula (SqCore.DSq h : Type)
      (SqCore.sqRank h) := by
  apply lowerTwoCentralElementaryH2CardFormula_of_finiteElementary
    finiteElementaryAbelianTwoH2CardFormula (SqCore.DSq h : Type)
    (dsqFinsetTopGen h) (SqCore.isProP_DSq h)
  calc
    Nat.card (levelQuot (SqCore.DSq h : Type) 2) =
        Nat.card (zLayer (SqCore.DSq h : Type) 1) := by
      rw [zLayer_one_eq_top]
      exact (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
    _ = 2 ^ SqCore.sqRank h := card_zLayer_one_dsq h

/-- The universal transgression sequence, the explicit nonzero cup square, and the finite
elementary-abelian computation give the exact five-term cardinal identity for `DSq h`. -/
theorem lowerTwoCentralFiveTermCardFormula_DSq (h : ℕ) :
    LowerTwoCentralFiveTermCardFormula (SqCore.DSq h : Type) := by
  apply lowerTwoCentralFiveTermCardFormula_of_kernelDuality
    (SqCore.DSq h : Type) (dsqFinsetTopGen h) (SqCore.isProP_DSq h)
  · exact lowerTwoCentralFiveTermKernelDuality (SqCore.DSq h : Type)
      (dsqFinsetTopGen h) (SqCore.isProP_DSq h)
  · exact lowerTwoCentralH2InflationSurjective_DSq h
  · rw [demushkinRank_DSq]
    exact lowerTwoCentralElementaryH2CardFormula_DSq h

/-- Every improved square model has the one-relator degree-two lower-central cardinality. -/
theorem lowerTwoCentralDegreeTwoExpectedCard_DSq (h : ℕ) :
    LowerTwoCentralDegreeTwoExpectedCard (SqCore.DSq h : Type)
      (SqCore.sqRank h) := by
  let d := SqCore.sqRank h
  have hmul : 2 ≤ d * (d + 1) := by
    dsimp [d, SqCore.sqRank]
    nlinarith
  have hquad : 0 < lowerTwoCentralQuadraticDimension d :=
    Nat.div_pos hmul (by omega)
  have hsplit : lowerTwoCentralQuadraticDimension d =
      lowerTwoCentralOneRelatorQuadraticDimension d + 1 := by
    rw [lowerTwoCentralOneRelatorQuadraticDimension]
    omega
  have hfive := lowerTwoCentralFiveTermCardFormula_DSq h
  unfold LowerTwoCentralFiveTermCardFormula at hfive
  rw [demushkinRank_DSq, card_H2_DSq] at hfive
  change Nat.card (zLayer (SqCore.DSq h : Type) 2) =
    2 ^ lowerTwoCentralOneRelatorQuadraticDimension d
  have hcancel : Nat.card (zLayer (SqCore.DSq h : Type) 2) * 2 =
      2 ^ lowerTwoCentralOneRelatorQuadraticDimension d * 2 := by
    rw [← pow_succ, ← hsplit]
    exact hfive
  exact Nat.mul_right_cancel (m := 2) (by omega) hcancel

/-- Discharged model-side degree-two supply for all handle counts. -/
theorem sqLowerTwoCentralDegreeTwoExpectedCardSupply :
    SqLowerTwoCentralDegreeTwoExpectedCardSupply :=
  lowerTwoCentralDegreeTwoExpectedCard_DSq

/-! ### Closing the lower-two-central five-term seam -/

/-- Every positive-rank finitely generated Demushkin pro-`2` group satisfies the exact
lower-two-central five-term cardinal formula. -/
theorem lowerTwoCentralFiveTermCardFormula_of_demushkin
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : IsTopologicallyFinGen G)
    (hD :
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
      IsDemushkin 2 G)
    (hrank :
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      0 < demushkinRank 2 G) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    LowerTwoCentralFiveTermCardFormula G := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  exact lowerTwoCentralFiveTermCardFormula_of_kernelDuality_finiteElementary
    finiteElementaryAbelianTwoH2CardFormula G hfg hD hrank
    (lowerTwoCentralFiveTermKernelDuality G hfg hD.isProP)

/-- Consequently the first quadratic lower-two-central layer of a positive-rank finitely
generated Demushkin group has the one-relator cardinality. -/
theorem lowerTwoCentralDegreeTwoExpectedCard_of_demushkin
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : IsTopologicallyFinGen G)
    (hD :
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
      IsDemushkin 2 G)
    (hrank :
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      0 < demushkinRank 2 G) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    LowerTwoCentralDegreeTwoExpectedCard G (demushkinRank 2 G) := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  exact lowerTwoCentralDegreeTwoExpectedCard_of_fiveTerm hD hrank
    (lowerTwoCentralFiveTermCardFormula_of_demushkin G hfg hD hrank)

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- Exact five-term cardinality for the maximal pro-`2` Galois group of any finite dyadic
field.  No odd-degree or `q = 2` hypothesis is needed. -/
theorem maxProTwoGalK_lowerTwoCentralFiveTermCardFormula
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) :
    let Q := maxProPQuotient 2 (GalK K)
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    LowerTwoCentralFiveTermCardFormula Q := by
  let Q := maxProPQuotient 2 (GalK K)
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  apply lowerTwoCentralFiveTermCardFormula_of_demushkin Q hfg
    (isDemushkin_maxProTwoGalK (K := K))
  rw [demushkinRank_maxProTwoGalK (K := K)]
  omega

/-- The arithmetic quadratic layer therefore has the exact one-relator order for every finite
dyadic field. -/
theorem maxProTwoGalK_lowerTwoCentralDegreeTwoExpectedCard
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) :
    LowerTwoCentralDegreeTwoExpectedCard (maxProPQuotient 2 (GalK K))
      (Module.finrank ℚ_[2] K + 2) := by
  exact maxProTwoGalK_lowerTwoCentralDegreeTwoExpectedCard_of_fiveTerm K
    (maxProTwoGalK_lowerTwoCentralFiveTermCardFormula K hfg)

/-- In degree one, the improved rank-three model and the arithmetic group now agree on their
quadratic lower-two-central layers with no cohomological premise. -/
theorem degreeOneGalKSq_zLayer_two_cardAgreement
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hone : Module.finrank ℚ_[2] K = 1)
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) :
    Nat.card (zLayer (SqCore.DSq 0 : Type) 2) =
      Nat.card (zLayer (maxProPQuotient 2 (GalK K)) 2) :=
  degreeOneGalKSq_zLayer_two_cardAgreement_of_fiveTerm K hone
    (maxProTwoGalK_lowerTwoCentralFiveTermCardFormula K hfg)

/-! ### The remaining all-level reverse boundary -/

/-- Agreement of the lower-two-central Hilbert coefficients strictly beyond the quadratic
coefficient.  The coefficients `0` and `1` are intentionally absent: they are supplied by
generator rank and the elementary-abelian `H²` calculation above. -/
def SqTwoCentralHilbertTailAgreement
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ℕ) : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    lowerTwoCentralHilbertCoefficient (SqCore.DSq h : Type) n =
      lowerTwoCentralHilbertCoefficient G n

/-- With a forward improved-relator map fixed, the full reverse finite-quotient family reduces
to two model-side inputs: the expected quadratic-layer order and equality of Hilbert
coefficients from degree `2` onward.  The arithmetic quadratic coefficient is unconditional. -/
theorem SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_of_modelDegreeTwo_and_hilbertTail
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    {h : ℕ}
    (D : SqCyclotomicForwardGeneratorData h (chiCycKTwo (K := K)))
    (hrank : SqCore.sqRank h = Module.finrank ℚ_[2] K + 2)
    (hmodel : LowerTwoCentralDegreeTwoExpectedCard
      (SqCore.DSq h : Type) (SqCore.sqRank h))
    (htail : SqTwoCentralHilbertTailAgreement
      (maxProPQuotient 2 (GalK K)) h) :
    SqReverseFiniteQuotientSurjections (maxProPQuotient 2 (GalK K)) h := by
  let Q := maxProPQuotient 2 (GalK K)
  have hfg : IsTopologicallyFinGen Q :=
    IsTopologicallyFinGen.of_surjective
      (D.forward isProP_maxProPQuotient).toMonoidHom
      (D.forward isProP_maxProPQuotient).continuous_toFun
      (D.forward_surjective isProP_maxProPQuotient) (dsqFinsetTopGen h)
  have hfield : LowerTwoCentralDegreeTwoExpectedCard Q
      (Module.finrank ℚ_[2] K + 2) :=
    maxProTwoGalK_lowerTwoCentralDegreeTwoExpectedCard K hfg
  have hzero :
      lowerTwoCentralHilbertCoefficient (SqCore.DSq h : Type) 0 =
        lowerTwoCentralHilbertCoefficient Q 0 := by
    rw [dsq_lowerTwoCentralHilbertCoefficient_zero,
      maxProTwoGalK_lowerTwoCentralHilbertCoefficient_zero K hfg, hrank]
  have hone :
      lowerTwoCentralHilbertCoefficient (SqCore.DSq h : Type) 1 =
        lowerTwoCentralHilbertCoefficient Q 1 := by
    apply congrArg (padicValNat 2)
    change Nat.card (zLayer (SqCore.DSq h : Type) 2) = Nat.card (zLayer Q 2)
    unfold LowerTwoCentralDegreeTwoExpectedCard at hmodel hfield
    rw [hmodel, hfield, hrank]
  have hseries : SqTwoCentralHilbertSeriesAgreement Q h := by
    intro n
    rcases lt_trichotomy n 1 with hn | rfl | hn
    · have : n = 0 := by omega
      simpa [this] using hzero
    · exact hone
    · exact htail n (by omega)
  apply D.reverseFiniteQuotientSurjections_of_layerCardAgreement
    isProP_maxProPQuotient
  exact (twoCentralHilbertSeriesAgreement_iff_layerCardAgreement hfg
    isProP_maxProPQuotient).mp hseries

/-- Odd-degree specialization of the preceding reverse reduction, with the improved model rank
`3 + 2 * (([K : ℚ₂] - 1) / 2)` simplified automatically to `[K : ℚ₂] + 2`. -/
theorem SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_oddDegree_of_modelDegreeTwo_and_hilbertTail
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (D : SqCyclotomicForwardGeneratorData
      ((Module.finrank ℚ_[2] K - 1) / 2) (chiCycKTwo (K := K)))
    (hmodel : LowerTwoCentralDegreeTwoExpectedCard
      (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type)
      (SqCore.sqRank ((Module.finrank ℚ_[2] K - 1) / 2)))
    (htail : SqTwoCentralHilbertTailAgreement
      (maxProPQuotient 2 (GalK K)) ((Module.finrank ℚ_[2] K - 1) / 2)) :
    SqReverseFiniteQuotientSurjections (maxProPQuotient 2 (GalK K))
      ((Module.finrank ℚ_[2] K - 1) / 2) := by
  apply D.reverseFiniteQuotientSurjections_of_modelDegreeTwo_and_hilbertTail K
  · obtain ⟨m, hm⟩ := hodd
    rw [hm]
    simp only [SqCore.sqRank]
    omega
  · exact hmodel
  · exact htail

#print axioms elementaryNormalizedCocycle_identity
#print axioms elementaryCocycleQuadraticMap
#print axioms elementaryH2ToQuadratic
#print axioms elementaryH2ToQuadratic_injective
#print axioms elementaryH2ToQuadratic_surjective
#print axioms elementaryH2EquivQuadratic
#print axioms card_elementaryQuadraticMap
#print axioms card_H2_finiteElementary
#print axioms finiteElementaryAbelianTwoH2CardFormula
#print axioms markedRelator_DSq
#print axioms presentedBy_DSq
#print axioms obsH2_DSq_dsqYCup
#print axioms card_H2_DSq
#print axioms lowerTwoCentralH2InflationSurjective_DSq
#print axioms lowerTwoCentralFiveTermCardFormula_DSq
#print axioms lowerTwoCentralDegreeTwoExpectedCard_DSq
#print axioms sqLowerTwoCentralDegreeTwoExpectedCardSupply
#print axioms lowerTwoCentralFiveTermCardFormula_of_demushkin
#print axioms lowerTwoCentralDegreeTwoExpectedCard_of_demushkin
#print axioms maxProTwoGalK_lowerTwoCentralFiveTermCardFormula
#print axioms maxProTwoGalK_lowerTwoCentralDegreeTwoExpectedCard
#print axioms degreeOneGalKSq_zLayer_two_cardAgreement
#print axioms SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_of_modelDegreeTwo_and_hilbertTail
#print axioms SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_oddDegree_of_modelDegreeTwo_and_hilbertTail

end

end GQ2.Dyadic.LSquare

/-
Copyright (c) 2026 Geoffrey Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Roe
-/
import GQ2.Devissage.ElemDualPack
import GQ2.Dyadic.Instances.LHandleCoordinates

/-!
# Perfectness of the `L_sq` handle block

The handle part of the middle Stokes map is the standard hyperbolic pairing.  This file bundles
that pairing as an additive equivalence from primal handle coordinates to the dual of the dual
handle coordinates.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.FoxH

/-- The `2h` ordered handle coordinates, with `0` the `U` slot and `1` the `V` slot. -/
abbrev LSqHandleCoords (h : ℕ) (A : Type*) := Fin h × Fin 2 → A

/-- The standard hyperbolic pairing on the handle coordinates. -/
def lSqHandleHyperbolicMap {h : ℕ} {A : Type*} [AddCommGroup A] :
    LSqHandleCoords h A →+ ElemDual (LSqHandleCoords h (ElemDual A)) where
  toFun x :=
    { toFun := fun y ↦ ∑ j, (y (j, 0) (x (j, 1)) + y (j, 1) (x (j, 0)))
      map_zero' := by simp
      map_add' := by
        intro y z
        change (∑ j, ((y + z) (j, 0) (x (j, 1)) + (y + z) (j, 1) (x (j, 0)))) =
          (∑ j, (y (j, 0) (x (j, 1)) + y (j, 1) (x (j, 0)))) +
          ∑ j, (z (j, 0) (x (j, 1)) + z (j, 1) (x (j, 0)))
        simp only [Pi.add_apply, ElemDual.add_apply]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        abel }
  map_zero' := by
    apply ElemDual.ext
    intro y
    change (∑ j, (y (j, 0) (0 : A) + y (j, 1) (0 : A))) = 0
    simp
  map_add' x z := by
    apply ElemDual.ext
    intro y
    change (∑ j, (y (j, 0) ((x + z) (j, 1)) + y (j, 1) ((x + z) (j, 0)))) =
      (∑ j, (y (j, 0) (x (j, 1)) + y (j, 1) (x (j, 0)))) +
      ∑ j, (y (j, 0) (z (j, 1)) + y (j, 1) (z (j, 0)))
    simp only [Pi.add_apply, map_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    abel

@[simp] theorem lSqHandleHyperbolicMap_apply {h : ℕ} {A : Type*} [AddCommGroup A]
    (x : LSqHandleCoords h A) (y : LSqHandleCoords h (ElemDual A)) :
    lSqHandleHyperbolicMap x y =
      ∑ j, (y (j, 0) (x (j, 1)) + y (j, 1) (x (j, 0))) := rfl

@[simp] theorem lSqHandleHyperbolicMap_single_zero {h : ℕ} {A : Type*} [AddCommGroup A]
    (x : LSqHandleCoords h A) (j : Fin h) (lam : ElemDual A) :
    lSqHandleHyperbolicMap x (Pi.single (j, 0) lam) = lam (x (j, 1)) := by
  classical
  rw [lSqHandleHyperbolicMap_apply, Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    have h0 : (k, (0 : Fin 2)) ≠ (j, 0) := fun hp ↦ hkj (congrArg Prod.fst hp)
    have h1 : (k, (1 : Fin 2)) ≠ (j, 0) := by simp
    simp [h0, h1]
  · simp

@[simp] theorem lSqHandleHyperbolicMap_single_one {h : ℕ} {A : Type*} [AddCommGroup A]
    (x : LSqHandleCoords h A) (j : Fin h) (lam : ElemDual A) :
    lSqHandleHyperbolicMap x (Pi.single (j, 1) lam) = lam (x (j, 0)) := by
  classical
  rw [lSqHandleHyperbolicMap_apply, Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    have h0 : (k, (0 : Fin 2)) ≠ (j, 1) := by simp
    have h1 : (k, (1 : Fin 2)) ≠ (j, 1) := fun hp ↦ hkj (congrArg Prod.fst hp)
    simp [h0, h1]
  · simp

theorem lSqHandleHyperbolicMap_injective {h : ℕ} {A : Type*} [AddCommGroup A]
    (hA₂ : ∀ a : A, a + a = 0) : Function.Injective (lSqHandleHyperbolicMap (h := h) (A := A)) := by
  intro x z hxz
  funext p
  rcases p with ⟨j, k⟩
  fin_cases k
  · have hcoord : x (j, 0) = z (j, 0) := by
      by_contra hne
      obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ (sub_ne_zero_of_ne hne)
      have heval := DFunLike.congr_fun hxz (Pi.single (j, 1) lam)
      rw [lSqHandleHyperbolicMap_single_one, lSqHandleHyperbolicMap_single_one] at heval
      apply hlam
      rw [map_sub, heval, sub_self]
    simpa using hcoord
  · have hcoord : x (j, 1) = z (j, 1) := by
      by_contra hne
      obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ (sub_ne_zero_of_ne hne)
      have heval := DFunLike.congr_fun hxz (Pi.single (j, 0) lam)
      rw [lSqHandleHyperbolicMap_single_zero, lSqHandleHyperbolicMap_single_zero] at heval
      apply hlam
      rw [map_sub, heval, sub_self]
    simpa using hcoord

theorem lSqHandleHyperbolicMap_bijective {h : ℕ} {A : Type*} [AddCommGroup A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) : Function.Bijective (lSqHandleHyperbolicMap (h := h) (A := A)) := by
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨lSqHandleHyperbolicMap_injective hA₂, ?_⟩
  have hH₂ : ∀ y : LSqHandleCoords h (ElemDual A), y + y = 0 := fun y ↦ by
    funext p
    exact (y p).add_self_eq_zero
  calc
    Nat.card (LSqHandleCoords h A) = Nat.card A ^ Nat.card (Fin h × Fin 2) := Nat.card_fun
    _ = Nat.card (ElemDual A) ^ Nat.card (Fin h × Fin 2) := by rw [card_elemDual hA₂]
    _ = Nat.card (LSqHandleCoords h (ElemDual A)) := Nat.card_fun.symm
    _ = Nat.card (ElemDual (LSqHandleCoords h (ElemDual A))) := (card_elemDual hH₂).symm

/-- The standard hyperbolic handle block is a perfect pairing. -/
noncomputable def lSqHandleHyperbolicAddEquiv {h : ℕ} {A : Type*}
    [AddCommGroup A] [Finite A] (hA₂ : ∀ a : A, a + a = 0) :
    LSqHandleCoords h A ≃+ ElemDual (LSqHandleCoords h (ElemDual A)) :=
  AddEquiv.ofBijective lSqHandleHyperbolicMap (lSqHandleHyperbolicMap_bijective hA₂)

end GQ2.Dyadic

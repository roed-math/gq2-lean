/-
Copyright (c) 2026 Geoffrey Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Roe
-/
import GQ2.Dyadic.Certificates.LFox

/-!
# Core and handle coordinates for the odd-degree `L_sq` alphabet

The alphabet in degree `2h + 1` is the disjoint union of its four-letter degree-one core and
`h` ordered handle pairs.  This file bundles that decomposition as equivalences and records the
coordinate formulae used by handle stabilization.
-/

namespace GQ2.Dyadic

open GQ2
open Certificates.LSq Words.LSq

/-- Split the `2h + 2` wild indices into the two core indices and `h` ordered pairs. -/
def lSqWildEquiv (h : ℕ) : Fin (2 * h + 2) ≃ Fin 2 ⊕ (Fin h × Fin 2) :=
  (finCongr (by omega)).trans <|
    finSumFinEquiv.symm.trans <|
      (Equiv.refl (Fin 2)).sumCongr finProdFinEquiv.symm

@[simp] theorem lSqWildEquiv_zero (h : ℕ) :
    lSqWildEquiv h ⟨0, by omega⟩ = Sum.inl 0 := by
  rw [lSqWildEquiv]
  simp only [Equiv.trans_apply]
  have hc : (finCongr (show 2 * h + 2 = 2 + h * 2 by omega)) ⟨0, by omega⟩
      = Fin.castAdd (h * 2) (0 : Fin 2) := by apply Fin.ext; rfl
  rw [hc]
  rfl

@[simp] theorem lSqWildEquiv_one (h : ℕ) :
    lSqWildEquiv h ⟨1, by omega⟩ = Sum.inl 1 := by
  rw [lSqWildEquiv]
  simp only [Equiv.trans_apply]
  have hc : (finCongr (show 2 * h + 2 = 2 + h * 2 by omega)) ⟨1, by omega⟩
      = Fin.castAdd (h * 2) (1 : Fin 2) := by apply Fin.ext; rfl
  rw [hc]
  rfl

@[simp] theorem lSqWildEquiv_handleU {h : ℕ} (j : Fin h) :
    lSqWildEquiv h ⟨2 + 2 * (j : ℕ), by omega⟩ = Sum.inr (j, 0) := by
  rw [lSqWildEquiv]
  simp only [Equiv.trans_apply]
  have hc : (finCongr (show 2 * h + 2 = 2 + h * 2 by omega))
        ⟨2 + 2 * (j : ℕ), by omega⟩ = Fin.natAdd 2 (finProdFinEquiv (j, 0)) := by
    apply Fin.ext
    simp [finProdFinEquiv]
  rw [hc]
  simp

@[simp] theorem lSqWildEquiv_handleV {h : ℕ} (j : Fin h) :
    lSqWildEquiv h ⟨3 + 2 * (j : ℕ), by omega⟩ = Sum.inr (j, 1) := by
  rw [lSqWildEquiv]
  simp only [Equiv.trans_apply]
  have hc : (finCongr (show 2 * h + 2 = 2 + h * 2 by omega))
        ⟨3 + 2 * (j : ℕ), by omega⟩ = Fin.natAdd 2 (finProdFinEquiv (j, 1)) := by
    apply Fin.ext
    simp [finProdFinEquiv]
    omega
  rw [hc]
  simp

/-- The full alphabet is its degree-one core plus the ordered handle coordinates. -/
def lSqAlphabetEquiv (h : ℕ) :
    Generator (2 * h + 1) ≃ Generator 1 ⊕ (Fin h × Fin 2) :=
  (Generator.equivSum (2 * h + 1)).trans <|
    ((Equiv.refl Bool).sumCongr (lSqWildEquiv h)).trans <|
      (Equiv.sumAssoc Bool (Fin 2) (Fin h × Fin 2)).symm |>.trans <|
        (Generator.equivSum 1).symm.sumCongr (Equiv.refl _)

@[simp] theorem lSqAlphabetEquiv_core (h : ℕ) (g : Generator 1) :
    lSqAlphabetEquiv h (coreEmbed h g) = Sum.inl g := by
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i => fin_cases i <;> rfl

@[simp] theorem lSqAlphabetEquiv_handleU {h : ℕ} (j : Fin h) :
    lSqAlphabetEquiv h (handleU j) = Sum.inr (j, 0) := by
  change Sum.map (Generator.equivSum 1).symm id
    ((Equiv.sumAssoc Bool (Fin 2) (Fin h × Fin 2)).symm
      (Sum.inr (lSqWildEquiv h ⟨2 + 2 * (j : ℕ), by omega⟩))) = _
  rw [lSqWildEquiv_handleU]
  rfl

@[simp] theorem lSqAlphabetEquiv_handleV {h : ℕ} (j : Fin h) :
    lSqAlphabetEquiv h (handleV j) = Sum.inr (j, 1) := by
  change Sum.map (Generator.equivSum 1).symm id
    ((Equiv.sumAssoc Bool (Fin 2) (Fin h × Fin 2)).symm
      (Sum.inr (lSqWildEquiv h ⟨3 + 2 * (j : ℕ), by omega⟩))) = _
  rw [lSqWildEquiv_handleV]
  rfl

/-- Split functions on a disjoint union, preserving their pointwise additive structure. -/
def sumArrowAddEquiv (X Y A : Type*) [Add A] :
    (X ⊕ Y → A) ≃+ (X → A) × (Y → A) where
  __ := Equiv.sumArrowEquivProdArrow X Y A
  map_add' _ _ := rfl

/-- Additive core/handle coordinates on offset vectors. -/
def lSqCoreHandleAddEquiv (h : ℕ) (A : Type*) [AddCommGroup A] :
    (Generator (2 * h + 1) → A) ≃+ (Generator 1 → A) × (Fin h × Fin 2 → A) :=
  (AddEquiv.arrowCongr (lSqAlphabetEquiv h) (AddEquiv.refl A)).trans
    (sumArrowAddEquiv (Generator 1) (Fin h × Fin 2) A)

@[simp] theorem lSqCoreHandleAddEquiv_fst (h : ℕ) (A : Type*) [AddCommGroup A]
    (x : Generator (2 * h + 1) → A) :
    (lSqCoreHandleAddEquiv h A x).1 = coreRestrict h A x := by
  funext g
  change x ((lSqAlphabetEquiv h).symm (Sum.inl g)) = x (coreEmbed h g)
  congr 1
  apply (lSqAlphabetEquiv h).injective
  rw [(lSqAlphabetEquiv h).apply_symm_apply, lSqAlphabetEquiv_core]

@[simp] theorem lSqCoreHandleAddEquiv_snd_zero (h : ℕ) (A : Type*) [AddCommGroup A]
    (x : Generator (2 * h + 1) → A) (j : Fin h) :
    (lSqCoreHandleAddEquiv h A x).2 (j, 0) = x (handleU j) := by
  change x ((lSqAlphabetEquiv h).symm (Sum.inr (j, 0))) = _
  congr 1
  apply (lSqAlphabetEquiv h).injective
  rw [(lSqAlphabetEquiv h).apply_symm_apply, lSqAlphabetEquiv_handleU]

@[simp] theorem lSqCoreHandleAddEquiv_snd_one (h : ℕ) (A : Type*) [AddCommGroup A]
    (x : Generator (2 * h + 1) → A) (j : Fin h) :
    (lSqCoreHandleAddEquiv h A x).2 (j, 1) = x (handleV j) := by
  change x ((lSqAlphabetEquiv h).symm (Sum.inr (j, 1))) = _
  congr 1
  apply (lSqAlphabetEquiv h).injective
  rw [(lSqAlphabetEquiv h).apply_symm_apply, lSqAlphabetEquiv_handleV]

end GQ2.Dyadic

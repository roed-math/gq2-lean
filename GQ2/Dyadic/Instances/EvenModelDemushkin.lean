/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenModelH2
import GQ2.Dyadic.Instances.EvenForwardRouteSkeleton

/-!
# EV-1d/EV-1e: the even dual-vector map, and `IsDemushkin` at the two even cores

Tickets **EV-1d** and **EV-1e** of the even-degree forward route
(`GQ2/Dyadic/Instances/EvenForwardRouteSkeleton.lean`).  This file finishes the two model-side
obligations `NModelDemushkin` / `MModelDemushkin` named there.

## EV-1d: there is no even partner permutation

On the odd `L_sq` row the relator Gram is a sum of hyperbolic blocks plus a single `Y²`, and its
inverse is again a permutation matrix, so the dual basis is realized by the *involution*
`sqInitialPartner : Equiv.Perm` (`GQ2/Dyadic/Count/H3SqRowInitialForms.lean:108`).  The even rows
have head block

`[[1, 1], [1, 0]]`,  with inverse  `[[0, 1], [1, 1]]`,

so the dual vector of slot `1` is `e₀ + e₁`, **not** a basis vector, and no permutation can do the
job.  `evenDualMap` below is the replacement: the honest inverse-Gram linear map

`(evenDualMap h u) k = u (evenPartner k) + [k = 1] · u 1`,

where `evenPartner` is the index involution `i ↦ i XOR 1` (`0 ↔ 1`, `2 ↔ 3`, `Uⱼ ↔ Vⱼ`) — the
permutation part of the inverse Gram — and the extra `[k = 1]·u 1` term is exactly the `(1,1)`
entry that the odd row does not have.  `evenCupForm_evenDualMap` is the statement that it really
does invert the whole Gram: pairing against it turns the cup form into the standard dot product
`evenDot`.

## EV-1e

`isDemushkin_DN` / `isDemushkin_DM` assemble `IsDemushkin 2` from EV-1a (`card_H2_*`), EV-1c
(`finite_H1_*`) and EV-1d (nondegeneracy on both sides, using that the even Gram is symmetric).
`nModelDemushkin` / `mModelDemushkin` are the resulting inhabitants of the skeleton's two named
obligations, so `EvenForward.orientedEquivN_of_supplies` / `…M…` now rest on the forward-generator
supply alone.

The hypothesis `2 ≤ α` is essential and not an artifact: it is what `diagCoeff_two_pow` needs, and
at `α = 1` the shared Gram is a different matrix on each row — the `N` head exponent becomes
`2 + 2ᵅ = 4 ≡ 0 (mod 4)` and its diagonal entry dies, while the `M` row picks up a second diagonal
entry at slot `2` from `c^{2^α} = c²`.  Whether the `α = 1` cores are Demushkin is not decided
here; the inverse Gram of §2 is simply not their inverse Gram.
-/

namespace GQ2.Dyadic.EvenModel

noncomputable section

open GQ2 GQ2.Dyadic.MarkedCore ContCoh

local instance evenScalarActionDN' (α h : ℕ) : DistribMulAction (DN α h : Type) (ZMod 2) :=
  scalarActionZmodTwo _

local instance evenContinuousScalarDN' (α h : ℕ) : ContinuousSMul (DN α h : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

local instance evenScalarActionDM' (α h : ℕ) : DistribMulAction (DM α h : Type) (ZMod 2) :=
  scalarActionZmodTwo _

local instance evenContinuousScalarDM' (α h : ℕ) : ContinuousSMul (DM α h : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-! ## §1 The index involution `i ↦ i XOR 1` -/

/-- **The even partner involution.**  `coreRank h = 4 + 2h` is even and the Gram's blocks are the
consecutive pairs `(0,1), (2,3), (4,5), …`, i.e. exactly `handleIdxU j = 4 + 2j` paired with
`handleIdxV j = 5 + 2j`.  So the permutation part of the inverse Gram is "flip the last bit". -/
def evenPartner {h : ℕ} (i : Fin (coreRank h)) : Fin (coreRank h) :=
  ⟨if (i : ℕ) % 2 = 0 then (i : ℕ) + 1 else (i : ℕ) - 1, by
    have hi := i.isLt
    simp only [coreRank] at hi ⊢
    split <;> omega⟩

theorem evenPartner_val {h : ℕ} (i : Fin (coreRank h)) :
    ((evenPartner i : Fin (coreRank h)) : ℕ) =
      if (i : ℕ) % 2 = 0 then (i : ℕ) + 1 else (i : ℕ) - 1 := rfl

@[simp] theorem evenPartner_zero (h : ℕ) : evenPartner (0 : Fin (coreRank h)) = 1 := by
  apply Fin.val_injective
  rw [evenPartner_val, coreVal_zero, coreVal_one, if_pos (by omega)]

@[simp] theorem evenPartner_one (h : ℕ) : evenPartner (1 : Fin (coreRank h)) = 0 := by
  apply Fin.val_injective
  rw [evenPartner_val, coreVal_zero, coreVal_one, if_neg (by omega)]

@[simp] theorem evenPartner_two (h : ℕ) : evenPartner (2 : Fin (coreRank h)) = 3 := by
  apply Fin.val_injective
  rw [evenPartner_val, coreVal_two, coreVal_three, if_pos (by omega)]

@[simp] theorem evenPartner_three (h : ℕ) : evenPartner (3 : Fin (coreRank h)) = 2 := by
  apply Fin.val_injective
  rw [evenPartner_val, coreVal_two, coreVal_three, if_neg (by omega)]

@[simp] theorem evenPartner_handleU {h : ℕ} (j : Fin h) :
    evenPartner (handleIdxU j) = handleIdxV j := by
  apply Fin.val_injective
  rw [evenPartner_val, handleIdxU_val, handleIdxV_val, if_pos (by omega)]
  omega

@[simp] theorem evenPartner_handleV {h : ℕ} (j : Fin h) :
    evenPartner (handleIdxV j) = handleIdxU j := by
  apply Fin.val_injective
  rw [evenPartner_val, handleIdxV_val, handleIdxU_val, if_neg (by omega)]
  omega

/-! ### Index distinctness, once -/

private theorem even_ne_of_val_ne {h : ℕ} {i k : Fin (coreRank h)}
    (hne : (i : ℕ) ≠ (k : ℕ)) : i ≠ k := fun e => hne (congrArg Fin.val e)

private theorem evenSingle_off {h : ℕ} {i k : Fin (coreRank h)} (hne : (k : ℕ) ≠ (i : ℕ)) :
    (Pi.single i 1 : Fin (coreRank h) → ZMod 2) k = 0 :=
  Pi.single_eq_of_ne (even_ne_of_val_ne hne) 1

private theorem handleIdxU_ne_one {h : ℕ} (j : Fin h) :
    handleIdxU j ≠ (1 : Fin (coreRank h)) :=
  even_ne_of_val_ne (by rw [handleIdxU_val, coreVal_one]; omega)

private theorem handleIdxV_ne_one {h : ℕ} (j : Fin h) :
    handleIdxV j ≠ (1 : Fin (coreRank h)) :=
  even_ne_of_val_ne (by rw [handleIdxV_val, coreVal_one]; omega)

/-! ## §2 The inverse-Gram linear map (EV-1d) -/

/-- **The even dual-vector map** — the inverse Gram, as an `𝔽₂`-linear map.  The permutation part
is `evenPartner`; the extra `[k = 1]·u 1` term is the `(1,1)` entry of the inverse head block
`[[0,1],[1,1]]`, which is why the odd row's `sqInitialPartner : Equiv.Perm` has no even
analogue. -/
def evenDualMap (h : ℕ) :
    (Fin (coreRank h) → ZMod 2) →ₗ[ZMod 2] (Fin (coreRank h) → ZMod 2) where
  toFun u := fun k ↦ u (evenPartner k) + (if k = 1 then u 1 else 0)
  map_add' u u' := by
    funext k
    by_cases hk : k = 1
    · simp only [hk, Pi.add_apply, evenPartner_one, if_true]
      ring
    · simp [hk]
  map_smul' a u := by
    funext k
    by_cases hk : k = 1
    · simp only [hk, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, evenPartner_one,
        if_true]
      ring
    · simp [hk]

theorem evenDualMap_apply (h : ℕ) (u : Fin (coreRank h) → ZMod 2) (k : Fin (coreRank h)) :
    evenDualMap h u k = u (evenPartner k) + (if k = 1 then u 1 else 0) := rfl

/-- The standard `𝔽₂` dot product, written in the same core-plus-handles shape as
`evenCupForm`. -/
def evenDot {h : ℕ} (v u : Fin (coreRank h) → ZMod 2) : ZMod 2 :=
  v 0 * u 0 + v 1 * u 1 + (v 2 * u 2 + v 3 * u 3)
    + ∑ j, (v (handleIdxU j) * u (handleIdxU j) + v (handleIdxV j) * u (handleIdxV j))

/-- **EV-1d, the inversion identity.**  `evenDualMap` inverts the full even Gram: pairing any
covector against `evenDualMap u` in the cup form returns the plain dot product with `u`.  In
matrix terms this is `G · G⁻¹ = 1`, with `G⁻¹` the map built above. -/
theorem evenCupForm_evenDualMap {h : ℕ} (v u : Fin (coreRank h) → ZMod 2) :
    evenCupForm v (evenDualMap h u) = evenDot v u := by
  have h2 : ∀ z : ZMod 2, z + z = 0 := by decide
  have w0 : evenDualMap h u 0 = u 1 := by
    rw [evenDualMap_apply, evenPartner_zero, if_neg (even_ne_of_val_ne
      (by rw [coreVal_zero, coreVal_one]; omega)), add_zero]
  have w1 : evenDualMap h u 1 = u 0 + u 1 := by
    rw [evenDualMap_apply, evenPartner_one, if_pos rfl]
  have w2 : evenDualMap h u 2 = u 3 := by
    rw [evenDualMap_apply, evenPartner_two, if_neg (even_ne_of_val_ne
      (by rw [coreVal_two, coreVal_one]; omega)), add_zero]
  have w3 : evenDualMap h u 3 = u 2 := by
    rw [evenDualMap_apply, evenPartner_three, if_neg (even_ne_of_val_ne
      (by rw [coreVal_three, coreVal_one]; omega)), add_zero]
  have wU : ∀ j : Fin h, evenDualMap h u (handleIdxU j) = u (handleIdxV j) := fun j => by
    rw [evenDualMap_apply, evenPartner_handleU, if_neg (handleIdxU_ne_one j), add_zero]
  have wV : ∀ j : Fin h, evenDualMap h u (handleIdxV j) = u (handleIdxU j) := fun j => by
    rw [evenDualMap_apply, evenPartner_handleV, if_neg (handleIdxV_ne_one j), add_zero]
  have hsum : (∑ j, (v (handleIdxU j) * evenDualMap h u (handleIdxV j) +
      v (handleIdxV j) * evenDualMap h u (handleIdxU j))) =
        ∑ j, (v (handleIdxU j) * u (handleIdxU j) + v (handleIdxV j) * u (handleIdxV j)) :=
    Finset.sum_congr rfl fun j _ => by rw [wU j, wV j]
  simp only [evenCupForm, evenDot, w0, w1, w2, w3, hsum]
  linear_combination (h2 (v 0 * u 1))

/-! ## §3 The dual vector of a slot -/

/-- The dual vector of slot `i`: the `i`-th column of the inverse Gram.  On slots `0, 2, 3` and
every handle slot this is the basis vector of the partner index; on slot `1` it is `e₀ + e₁`. -/
def evenDualVector {h : ℕ} (i : Fin (coreRank h)) : Fin (coreRank h) → ZMod 2 :=
  evenDualMap h (Pi.single i 1)

/-- The dot product against a coordinate basis vector extracts that coordinate. -/
theorem evenDot_single {h : ℕ} (v : Fin (coreRank h) → ZMod 2) (i : Fin (coreRank h)) :
    evenDot v (Pi.single i 1) = v i := by
  classical
  rcases nCoreIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have e1 : (Pi.single (0 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) 1 = 0 :=
      evenSingle_off (by rw [coreVal_zero, coreVal_one]; omega)
    have e2 : (Pi.single (0 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) 2 = 0 :=
      evenSingle_off (by rw [coreVal_zero, coreVal_two]; omega)
    have e3 : (Pi.single (0 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) 3 = 0 :=
      evenSingle_off (by rw [coreVal_zero, coreVal_three]; omega)
    have eU : ∀ j : Fin h,
        (Pi.single (0 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) (handleIdxU j) = 0 :=
      fun j => evenSingle_off (by rw [coreVal_zero, handleIdxU_val]; omega)
    have eV : ∀ j : Fin h,
        (Pi.single (0 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) (handleIdxV j) = 0 :=
      fun j => evenSingle_off (by rw [coreVal_zero, handleIdxV_val]; omega)
    simp [evenDot, Pi.single_eq_same, e1, e2, e3, eU, eV]
  · have e0 : (Pi.single (1 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) 0 = 0 :=
      evenSingle_off (by rw [coreVal_zero, coreVal_one]; omega)
    have e2 : (Pi.single (1 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) 2 = 0 :=
      evenSingle_off (by rw [coreVal_one, coreVal_two]; omega)
    have e3 : (Pi.single (1 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) 3 = 0 :=
      evenSingle_off (by rw [coreVal_one, coreVal_three]; omega)
    have eU : ∀ j : Fin h,
        (Pi.single (1 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) (handleIdxU j) = 0 :=
      fun j => evenSingle_off (by rw [coreVal_one, handleIdxU_val]; omega)
    have eV : ∀ j : Fin h,
        (Pi.single (1 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) (handleIdxV j) = 0 :=
      fun j => evenSingle_off (by rw [coreVal_one, handleIdxV_val]; omega)
    simp [evenDot, Pi.single_eq_same, e0, e2, e3, eU, eV]
  · have e0 : (Pi.single (2 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) 0 = 0 :=
      evenSingle_off (by rw [coreVal_zero, coreVal_two]; omega)
    have e1 : (Pi.single (2 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) 1 = 0 :=
      evenSingle_off (by rw [coreVal_one, coreVal_two]; omega)
    have e3 : (Pi.single (2 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) 3 = 0 :=
      evenSingle_off (by rw [coreVal_two, coreVal_three]; omega)
    have eU : ∀ j : Fin h,
        (Pi.single (2 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) (handleIdxU j) = 0 :=
      fun j => evenSingle_off (by rw [coreVal_two, handleIdxU_val]; omega)
    have eV : ∀ j : Fin h,
        (Pi.single (2 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) (handleIdxV j) = 0 :=
      fun j => evenSingle_off (by rw [coreVal_two, handleIdxV_val]; omega)
    simp [evenDot, Pi.single_eq_same, e0, e1, e3, eU, eV]
  · have e0 : (Pi.single (3 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) 0 = 0 :=
      evenSingle_off (by rw [coreVal_zero, coreVal_three]; omega)
    have e1 : (Pi.single (3 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) 1 = 0 :=
      evenSingle_off (by rw [coreVal_one, coreVal_three]; omega)
    have e2 : (Pi.single (3 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) 2 = 0 :=
      evenSingle_off (by rw [coreVal_two, coreVal_three]; omega)
    have eU : ∀ j : Fin h,
        (Pi.single (3 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) (handleIdxU j) = 0 :=
      fun j => evenSingle_off (by rw [coreVal_three, handleIdxU_val]; omega)
    have eV : ∀ j : Fin h,
        (Pi.single (3 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) (handleIdxV j) = 0 :=
      fun j => evenSingle_off (by rw [coreVal_three, handleIdxV_val]; omega)
    simp [evenDot, Pi.single_eq_same, e0, e1, e2, eU, eV]
  · have ecore : ∀ k : Fin (coreRank h), (k : ℕ) < 4 →
        (Pi.single (handleIdxU j) 1 : Fin (coreRank h) → ZMod 2) k = 0 := fun k hk =>
      evenSingle_off (by rw [handleIdxU_val]; omega)
    have e0 := ecore 0 (by rw [coreVal_zero]; omega)
    have e1 := ecore 1 (by rw [coreVal_one]; omega)
    have e2 := ecore 2 (by rw [coreVal_two]; omega)
    have e3 := ecore 3 (by rw [coreVal_three]; omega)
    have eV : ∀ j' : Fin h,
        (Pi.single (handleIdxU j) 1 : Fin (coreRank h) → ZMod 2) (handleIdxV j') = 0 := fun j' =>
      evenSingle_off (by rw [handleIdxU_val, handleIdxV_val]; omega)
    have eU : ∀ j' : Fin h,
        (Pi.single (handleIdxU j) 1 : Fin (coreRank h) → ZMod 2) (handleIdxU j') =
        if j' = j then 1 else 0 := fun j' => by
      by_cases hjj : j' = j
      · rw [hjj, Pi.single_eq_same, if_pos rfl]
      · rw [evenSingle_off (by
          rw [handleIdxU_val, handleIdxU_val]
          have : (j' : ℕ) ≠ (j : ℕ) := fun e => hjj (Fin.val_injective e)
          omega), if_neg hjj]
    simp [evenDot, e0, e1, e2, e3, eU, eV]
  · have ecore : ∀ k : Fin (coreRank h), (k : ℕ) < 4 →
        (Pi.single (handleIdxV j) 1 : Fin (coreRank h) → ZMod 2) k = 0 := fun k hk =>
      evenSingle_off (by rw [handleIdxV_val]; omega)
    have e0 := ecore 0 (by rw [coreVal_zero]; omega)
    have e1 := ecore 1 (by rw [coreVal_one]; omega)
    have e2 := ecore 2 (by rw [coreVal_two]; omega)
    have e3 := ecore 3 (by rw [coreVal_three]; omega)
    have eU : ∀ j' : Fin h,
        (Pi.single (handleIdxV j) 1 : Fin (coreRank h) → ZMod 2) (handleIdxU j') = 0 := fun j' =>
      evenSingle_off (by rw [handleIdxV_val, handleIdxU_val]; omega)
    have eV : ∀ j' : Fin h,
        (Pi.single (handleIdxV j) 1 : Fin (coreRank h) → ZMod 2) (handleIdxV j') =
        if j' = j then 1 else 0 := fun j' => by
      by_cases hjj : j' = j
      · rw [hjj, Pi.single_eq_same, if_pos rfl]
      · rw [evenSingle_off (by
          rw [handleIdxV_val, handleIdxV_val]
          have : (j' : ℕ) ≠ (j : ℕ) := fun e => hjj (Fin.val_injective e)
          omega), if_neg hjj]
    simp [evenDot, e0, e1, e2, e3, eU, eV]

/-- **EV-1d, coordinate form.**  Pairing a covector against the dual vector of slot `i` in the
even cup form extracts the `i`-th coordinate. -/
theorem evenCupForm_evenDualVector {h : ℕ} (v : Fin (coreRank h) → ZMod 2)
    (i : Fin (coreRank h)) : evenCupForm v (evenDualVector i) = v i := by
  rw [evenDualVector, evenCupForm_evenDualMap, evenDot_single]

/-- The left-slot form, by symmetry of the even Gram. -/
theorem evenCupForm_evenDualVector_left {h : ℕ} (w : Fin (coreRank h) → ZMod 2)
    (i : Fin (coreRank h)) : evenCupForm (evenDualVector i) w = w i := by
  rw [evenCupForm_comm, evenCupForm_evenDualVector]

/-! ## §4 EV-1e: the two cores are Demushkin -/

/-- **EV-1e, `N` row.**  The even `N_α` core is a Demushkin pro-`2` group for every handle count
and every branch depth `α ≥ 2`.  Nondegeneracy is the inverse-Gram map of §2. -/
theorem isDemushkin_DN (α h : ℕ) (hα2 : 2 ≤ α) : IsDemushkin 2 (DN α h : Type) := by
  have hα : 1 ≤ α := le_trans one_le_two hα2
  exact
    { smul_trivial := fun _ _ => rfl
      isProP := isProP_DN α h
      finiteH1 := finite_H1_DN α h hα
      cardH2 := card_H2_DN α h hα2
      nondegen_left := by
        intro x hx
        obtain ⟨v, rfl⟩ := (dnCoordinateHOne_bijective α h hα).surjective x
        have hv : v ≠ 0 := (dnCoordinateHOne_ne_zero_iff α h hα v).mp hx
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
        refine ⟨dnCoordinateHOne α h hα (evenDualVector i), ?_⟩
        refine dnCoordinateHOne_cup_ne_zero_of_gram α h hα hα2 ?_
        rw [evenCupForm_evenDualVector]
        exact hi
      nondegen_right := by
        intro y hy
        obtain ⟨w, rfl⟩ := (dnCoordinateHOne_bijective α h hα).surjective y
        have hw : w ≠ 0 := (dnCoordinateHOne_ne_zero_iff α h hα w).mp hy
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
        refine ⟨dnCoordinateHOne α h hα (evenDualVector i), ?_⟩
        refine dnCoordinateHOne_cup_ne_zero_of_gram α h hα hα2 ?_
        rw [evenCupForm_evenDualVector_left]
        exact hi }

/-- **EV-1e, `M` row.**  Same Gram, same argument. -/
theorem isDemushkin_DM (α h : ℕ) (hα2 : 2 ≤ α) : IsDemushkin 2 (DM α h : Type) := by
  have hα : 1 ≤ α := le_trans one_le_two hα2
  exact
    { smul_trivial := fun _ _ => rfl
      isProP := isProP_DM α h
      finiteH1 := finite_H1_DM α h hα
      cardH2 := card_H2_DM α h hα2
      nondegen_left := by
        intro x hx
        obtain ⟨v, rfl⟩ := (dmCoordinateHOne_bijective α h hα).surjective x
        have hv : v ≠ 0 := (dmCoordinateHOne_ne_zero_iff α h hα v).mp hx
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
        refine ⟨dmCoordinateHOne α h hα (evenDualVector i), ?_⟩
        refine dmCoordinateHOne_cup_ne_zero_of_gram α h hα hα2 ?_
        rw [evenCupForm_evenDualVector]
        exact hi
      nondegen_right := by
        intro y hy
        obtain ⟨w, rfl⟩ := (dmCoordinateHOne_bijective α h hα).surjective y
        have hw : w ≠ 0 := (dmCoordinateHOne_ne_zero_iff α h hα w).mp hy
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
        refine ⟨dmCoordinateHOne α h hα (evenDualVector i), ?_⟩
        refine dmCoordinateHOne_cup_ne_zero_of_gram α h hα hα2 ?_
        rw [evenCupForm_evenDualVector_left]
        exact hi }

/-! ## §5 The two skeleton obligations, discharged -/

/-- **The `N`-row model obligation of the even forward route**, discharged: `D_N` is Demushkin at
the literal marking rank `coreRank h = 4 + 2h`. -/
theorem nModelDemushkin (α h : ℕ) (hα2 : 2 ≤ α) : EvenForward.NModelDemushkin α h :=
  ⟨isDemushkin_DN α h hα2, demushkinRank_DN α h (le_trans one_le_two hα2)⟩

/-- **The `M`-row model obligation of the even forward route**, discharged. -/
theorem mModelDemushkin (α h : ℕ) (hα2 : 2 ≤ α) : EvenForward.MModelDemushkin α h :=
  ⟨isDemushkin_DM α h hα2, demushkinRank_DM α h (le_trans one_le_two hα2)⟩

/-! ## §6 The even-degree classifications, with the model side gone

The skeleton's uniform statements, restated with `hmodel` discharged: the only remaining input is
the forward-generator supply. -/

/-- The uniform even-degree `N` classification, with the model obligation discharged. -/
theorem orientedEquivN_of_supply (α : ℕ) (hα2 : 2 ≤ α)
    (hsupply : EvenForward.EvenDegreeGalKNForwardGeneratorSupply α)
    (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    Nonempty (OrientedContinuousMulEquiv (chiN α h) (chiCycKTwo (K := K))) :=
  EvenForward.orientedEquivN_of_supplies α (le_trans one_le_two hα2)
    (fun h => nModelDemushkin α h hα2) hsupply K h hev

/-- The uniform even-degree `M` classification, with the model obligation discharged. -/
theorem orientedEquivM_of_supply (α : ℕ) (hα2 : 2 ≤ α)
    (hsupply : EvenForward.EvenDegreeGalKMForwardGeneratorSupply α)
    (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    Nonempty (OrientedContinuousMulEquiv (chiM α h) (chiCycKTwo (K := K))) :=
  EvenForward.orientedEquivM_of_supplies α (le_trans one_le_two hα2)
    (fun h => mModelDemushkin α h hα2) hsupply K h hev

/-! ## §7 Axiom hygiene

Every declaration in this file is std-3 (`propext`, `Classical.choice`, `Quot.sound`).  Neither
Labute's classification nor any census axiom enters: the two obligations are discharged by the
one-relator `H²` bound plus the explicit inverse Gram. -/

#print axioms evenCupForm_evenDualMap
#print axioms evenDot_single
#print axioms evenCupForm_evenDualVector
#print axioms isDemushkin_DN
#print axioms isDemushkin_DM
#print axioms nModelDemushkin
#print axioms mModelDemushkin
#print axioms orientedEquivN_of_supply
#print axioms orientedEquivM_of_supply

end

end GQ2.Dyadic.EvenModel

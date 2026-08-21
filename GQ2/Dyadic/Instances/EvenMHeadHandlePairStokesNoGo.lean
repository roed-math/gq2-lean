/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/

import GQ2.Dyadic.Instances.EvenMHeadHandlePairNormal
import GQ2.Dyadic.Instances.NpcRamifiedRow

namespace GQ2.Dyadic


/-!
# A uniform Stokes obstruction for the pure head-handle pair exchange

The pair exchange moves the free ramified `x₂` coordinate into a selected handle.  If the
original `sigma` acts trivially, the selected dual handle coordinate is forced to vanish.
The displaced coordinate is therefore in the radical of the full traced pairing, including
both relators.  Consequently the raw pair family is not Stokes-dual on any nonzero finite
coefficient module.

This is an all-rank obstruction.  It rules out the pure pair exchange as the general source;
it is not a class-by-class counterexample.  A replacement must retain a second-order partner
for the displaced `x₂` coordinate in the sigma-trivial ramified branch.
-/

noncomputable section

open GQ2 GQ2.FoxH
open Count Certificates Words Certificates.MProcyclic
open Instances.EvenMHeadHandleSource
open Instances.EvenMHeadHandlePairSource
open Instances.EvenMHeadHandlePairCore
open Instances.EvenMHeadHandlePairNormalize

namespace Instances.EvenMHeadHandlePairNoGo

variable {X C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]

def PrimalZero (x : X → A) : PWord X → Prop
  | .one => True
  | .gen g => x g = 0
  | .mul u v => PrimalZero x u ∧ PrimalZero x v
  | .inv u => PrimalZero x u
  | .conj u v => PrimalZero x u ∧ PrimalZero x v
  | .comm u v => PrimalZero x u ∧ PrimalZero x v
  | .zpow u _ => PrimalZero x u
  | .z2pow u _ => PrimalZero x u
  | .profPow u _ => PrimalZero x u

theorem heisEvalZ_mem_heisPrimPure_of_primalZero
    (mu : X → C) (x : X → A) (y : X → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    ∀ w, PrimalZero x w →
      heisEvalZ mu x y E E₂ w ∈ NProcyclicRam.heisPrimPure A C := by
  intro w hw
  induction w with
  | one => exact (NProcyclicRam.heisPrimPure A C).one_mem
  | gen g =>
      rw [heisEvalZ_gen]
      exact ⟨hw, rfl⟩
  | mul u v hu hv =>
      rw [heisEvalZ_mul]
      exact mul_mem (hu hw.1) (hv hw.2)
  | inv u hu =>
      rw [heisEvalZ_inv]
      exact inv_mem (hu hw)
  | conj u v hu hv =>
      rw [heisEvalZ_conj, conjR]
      exact mul_mem (mul_mem (inv_mem (hv hw.2)) (hu hw.1)) (hv hw.2)
  | comm u v hu hv =>
      rw [heisEvalZ_comm, commR]
      exact mul_mem (mul_mem (mul_mem (inv_mem (hu hw.1)) (inv_mem (hv hw.2)))
        (hu hw.1)) (hv hw.2)
  | zpow u k hu =>
      rw [heisEvalZ_zpow]
      exact zpow_mem (hu hw) k
  | z2pow u z hu =>
      change PWord.evalZ (heisGen mu x y) E E₂ (.z2pow u z) ∈
        NProcyclicRam.heisPrimPure A C
      rw [PWord.evalZ_z2pow]
      exact zpow_mem (hu hw) (E₂ z)
  | profPow u z hu =>
      rw [heisEvalZ_profPow]
      exact zpow_mem (hu hw) (E z)

theorem primalZero_prodList (x : X → A) :
    ∀ ws, PrimalZero x (PWord.prodList ws) ↔ ∀ w ∈ ws, PrimalZero x w := by
  intro ws
  induction ws with
  | nil => simp [PWord.prodList, PrimalZero]
  | cons w ws ih => simp [PWord.prodList, PrimalZero, ih]

variable {h : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]

def pairVSlot (j : Fin h) (v : A) : Fin h × Fin 2 → A :=
  Function.update 0 (j, 1) v

theorem pairVSlot_self (j : Fin h) (v : A) : pairVSlot j v (j, 1) = v := by
  simp [pairVSlot]

theorem pairVSlot_zero (j : Fin h) (v : A) (k : Fin h) : pairVSlot j v (k, 0) = 0 := by
  simp [pairVSlot]

theorem pairV_primalZero_mFactors
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A)
    (hs : ∀ a : A, t.σ • a = a) (alpha : ℕ) :
    let x := headHandlePairRamNormal t j 0 0 (pairVSlot j v)
    let b := fun g ↦ x (headHandlePairSwap j g)
    PrimalZero b (PWord.prodList (Words.MCompact.mFactors alpha h)) := by
  dsimp only
  have hsInv : ∀ a : A, t.σ⁻¹ • a = a := fun a => inv_smul_eq_iff.mpr (hs a).symm
  rw [primalZero_prodList]
  intro w hw
  simp only [Words.MCompact.mFactors, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [PrimalZero, Words.MCompact.a0W, sigma2W,
      PWord.omega2Pow, Words.MCompact.j2W, Words.MCompact.eRevW,
      Words.MCompact.deltaC, headHandlePairSwap, hsInv, pairVSlot]

theorem pairSwap_wild_trivial
    (t : Marking (2 + 2 * h) C) (j : Fin h)
    (hs : ∀ a : A, t.σ • a = a)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a) :
    ∀ (i : Fin (2 + 2 * h + 1)) (a : A),
      t (headHandlePairSwap j (.wild i)) • a = a := by
  intro i a
  cases H : headHandlePairSwap j (.wild i) with
  | sigma => exact hs a
  | tau =>
      exfalso
      have E := (headHandlePairSwap j).injective
        (H.trans (headHandlePairSwap_tau j).symm)
      simp at E
  | wild k => exact hwild k a

theorem pairV_compact_handleU
    (t : Marking (2 + 2 * h) C) (j k : Fin h) (v : A) :
    headHandlePairRamNormal t j 0 0 (pairVSlot j v)
      (headHandlePairSwap j (handleU k)) = 0 := by
  by_cases hkj : k = j
  · subst k
    simp
  · have hswap : headHandlePairSwap j (handleU k) = handleU k := by
      simp [headHandlePairSwap, hkj]
    rw [hswap, headHandlePairRamNormal_handleU]
    exact pairVSlot_zero j v k

theorem pairV_compact_handleV
    (t : Marking (2 + 2 * h) C) (j k : Fin h) (v : A) :
    headHandlePairRamNormal t j 0 0 (pairVSlot j v)
      (headHandlePairSwap j (handleV k)) = if k = j then v else 0 := by
  by_cases hkj : k = j
  · subst k
    simp [pairVSlot]
  · have hswap : headHandlePairSwap j (handleV k) = handleV k := by
      simp [headHandlePairSwap, hkj]
    rw [hswap, headHandlePairRamNormal_handleV_of_ne t j k hkj]
    simp [pairVSlot, hkj]

theorem heisZ_pairV_compact_zero
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A)
    (y : Generator (2 + 2 * h) → ElemDual A)
    (hs : ∀ a : A, t.σ • a = a)
    (hyσ : y .sigma = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha : ℕ) :
    let x := headHandlePairRamNormal t j 0 0 (pairVSlot j v)
    let s : Marking (2 + 2 * h) C := ⟨fun g ↦ t (headHandlePairSwap j g)⟩
    let b := fun g ↦ x (headHandlePairSwap j g)
    let c := fun g ↦ y (headHandlePairSwap j g)
    (heisEvalZ ⇑s b c E E₂ (Words.MCompact.mCompactW alpha h)).z = 0 := by
  let x := headHandlePairRamNormal t j 0 0 (pairVSlot j v)
  let s : Marking (2 + 2 * h) C := ⟨fun g ↦ t (headHandlePairSwap j g)⟩
  let b := fun g ↦ x (headHandlePairSwap j g)
  let c := fun g ↦ y (headHandlePairSwap j g)
  change (heisEvalZ ⇑s b c E E₂ (Words.MCompact.mCompactW alpha h)).z = 0
  have hswild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), s.x i • a = a := by
    exact pairSwap_wild_trivial t j hs hwild
  have hP := heisEvalZ_mem_heisPrimPure_of_primalZero ⇑s b c E E₂
    (PWord.prodList (Words.MCompact.mFactors alpha h))
    (pairV_primalZero_mFactors t j v hs alpha)
  have hPz : ((Words.MCompact.mFactors alpha h).map
      (heisEvalZ ⇑s b c E E₂)).prod.z = 0 := by
    rw [← heisEvalZ_prodList]
    exact hP.2
  have hH := Certificates.MCompact.heisF_handlesW_mem s b c E E₂ hswild
  have hHz := Certificates.MCompact.heisF_handlesW_z s b c E E₂ hswild
  have hbU : ∀ k, b (handleU k) = 0 := fun k => pairV_compact_handleU t j k v
  have hbV : ∀ k, b (handleV k) = if k = j then v else 0 :=
    fun k => pairV_compact_handleV t j k v
  have hcU : c (handleU j) = 0 := by
    simp [c, hyσ]
  have hsum : (∑ k, (c (handleU k) (b (handleV k))
      + c (handleV k) (b (handleU k)))) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [hbU, map_zero, add_zero, hbV]
    split
    · rename_i hk
      subst k
      rw [hcU, ElemDual.zero_apply]
    · rw [map_zero]
  rw [Words.MCompact.mCompactW, heisEvalZ_prodList, List.map_append, List.prod_append,
    Certificates.MCompact.heisEvalZ_handleTailW]
  rw [heisMul_z_of_a_eq_zero _ _ hH.1, hPz, hHz, hsum, zero_add]

theorem heisEvalZ_headHandlePairCompactW_eq
    (t : Marking (2 + 2 * h) C)
    (x : Generator (2 + 2 * h) → A)
    (y : Generator (2 + 2 * h) → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha : ℕ) (j : Fin h) :
    heisEvalZ ⇑t x y E E₂ (headHandlePairCompactW alpha j) =
      heisEvalZ (fun g ↦ t (headHandlePairSwap j g))
        (fun g ↦ x (headHandlePairSwap j g))
        (fun g ↦ y (headHandlePairSwap j g)) E E₂
        (Words.MCompact.mCompactW alpha h) := by
  rw [headHandlePairCompactW_eq_nielsenBackward]
  change PWord.evalZ (heisGen ⇑t x y) E E₂
      (PWord.subst (headHandlePairNielsen j).backward
        (Words.MCompact.mCompactW alpha h)) = _
  rw [PWord.evalZ_subst]
  congr 1
  funext g
  change PWord.evalZ (heisGen ⇑t x y) E E₂
      (.gen ((headHandlePairSwap j).symm g)) = _
  rw [PWord.evalZ_gen, headHandlePairSwap_symm]
  rfl

theorem heisEta1_pairV_headHandlePairRawFamily_eq_zero
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha q : ℕ)
    (hs : ∀ a : A, t.σ • a = a)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (r : ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A)) :
    heisEta1 ⇑t (headHandlePairRawFamily E E₂ alpha h q j)
      (headHandlePairRamNormal t j 0 0 (pairVSlot j v))
      (headHandlePairRamNormal t j r.1 r.2.1 r.2.2) = 0 := by
  rw [heisEta1_apply, Fin.sum_univ_two]
  change (FreeGroup.lift (heisGen ⇑t
      (headHandlePairRamNormal t j 0 0 (pairVSlot j v))
      (headHandlePairRamNormal t j r.1 r.2.1 r.2.2))
      (heisToFree E E₂ (Certificates.tameRelW (2 + 2 * h) q))).z
    + (FreeGroup.lift (heisGen ⇑t
      (headHandlePairRamNormal t j 0 0 (pairVSlot j v))
      (headHandlePairRamNormal t j r.1 r.2.1 r.2.2))
      (heisToFree E E₂ (headHandlePairCompactW alpha j))).z = 0
  rw [← heisEvalZ_eq_lift, ← heisEvalZ_eq_lift]
  rw [heisZ_tameRelW_eq_zero_of_tame_offsets_zero t _ _ E E₂
      (by simp) (by simp) (by simp) (by simp),
    zero_add, heisEvalZ_headHandlePairCompactW_eq]
  exact heisZ_pairV_compact_zero t j v _ hs (by simp) hwild E E₂ alpha

theorem heisEta1_pairV_headHandlePairRawFamily_cocycle_eq_zero
    [Finite A] (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha q : ℕ)
    (hs : ∀ a : A, t.σ • a = a)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hr : ∀ k, FreeGroup.lift ⇑t (headHandlePairRawFamily E E₂ alpha h q j k) = 1)
    (hend : IsStokesEndpoint (headHandlePairRawFamily E E₂ alpha h q j))
    (hrowA : IsHeadHandlePairRamRow (q := q) t
      (headHandlePairRawFamily E E₂ alpha h q j) j A)
    (hrowD : IsHeadHandlePairRamRow (q := q) t
      (headHandlePairRawFamily E E₂ alpha h q j) j (ElemDual A))
    (y : Generator (2 + 2 * h) → ElemDual A)
    (hy : heisD1 (A := ElemDual A) ⇑t
      (headHandlePairRawFamily E E₂ alpha h q j) y = 0) :
    heisEta1 ⇑t (headHandlePairRawFamily E E₂ alpha h q j)
      (headHandlePairRamNormal t j 0 0 (pairVSlot j v)) y = 0 := by
  let x := headHandlePairRamNormal t j 0 0 (pairVSlot j v)
  have hwildD : ∀ (i : Fin (2 + 2 * h + 1)) (lam : ElemDual A),
      t.x i • lam = lam := fun i lam ↦ elemDual_smul_eq_self (hwild i) lam
  have hτfpfD : ∀ lam : ElemDual A, t.τ • lam = lam → lam = 0 :=
    fun lam hlam ↦ elemDual_fpf hτfpf lam hlam
  obtain ⟨r, hrange, -⟩ := headHandlePairRamNormalForm_of_row
    (A := ElemDual A) t (headHandlePairRawFamily E E₂ alpha h q j) j
      hrowD hwildD hτfpfD hr y hy
  obtain ⟨u, hu⟩ := hrange
  have hyrepr : y = headHandlePairRamNormal t j r.1 r.2.1 r.2.2 + heisD0 ⇑t u := by
    rw [hu]
    abel
  have hx : heisD1 ⇑t (headHandlePairRawFamily E E₂ alpha h q j) x = 0 :=
    heisD1_headHandlePairRamNormal_eq_zero t _ j hrowA 0 0 (pairVSlot j v)
  rw [hyrepr, map_add,
    heisEta1_pairV_headHandlePairRawFamily_eq_zero t j v E E₂ alpha q hs hwild r,
    ← heisEta2_comp_d1 ⇑t (headHandlePairRawFamily E E₂ alpha h q j)
      hr hend x u,
    hx]
  simp

theorem not_stokesDuality_headHandlePairRawFamily_of_sigma_trivial
    [Finite A] (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) (hv : v ≠ 0)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha q : ℕ)
    (hs : ∀ a : A, t.σ • a = a)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hr : ∀ k, FreeGroup.lift ⇑t (headHandlePairRawFamily E E₂ alpha h q j k) = 1)
    (hend : IsStokesEndpoint (headHandlePairRawFamily E E₂ alpha h q j))
    (hrowA : IsHeadHandlePairRamRow (q := q) t
      (headHandlePairRawFamily E E₂ alpha h q j) j A)
    (hrowD : IsHeadHandlePairRamRow (q := q) t
      (headHandlePairRawFamily E E₂ alpha h q j) j (ElemDual A)) :
    ¬ StokesDuality ⇑t (headHandlePairRawFamily E E₂ alpha h q j) A := by
  intro hd
  let x := headHandlePairRamNormal t j 0 0 (pairVSlot j v)
  have hx : heisD1 ⇑t (headHandlePairRawFamily E E₂ alpha h q j) x = 0 :=
    heisD1_headHandlePairRamNormal_eq_zero t _ j hrowA 0 0 (pairVSlot j v)
  obtain ⟨u, hu⟩ := hd.pairing_vanish_left x hx
    (heisEta1_pairV_headHandlePairRawFamily_cocycle_eq_zero t j v E E₂ alpha q
      hs hwild hτfpf hr hend hrowA hrowD)
  have hc := congrFun hu (coreLetter h 2)
  have hcore : t (coreLetter h 2) • u = u := hwild _ u
  rw [heisD0_apply, hcore, sub_self] at hc
  have hx2 : x (coreLetter h 2) = v := by
    simp [x, pairVSlot]
  exact hv (hx2.symm.trans hc.symm)

end EvenMHeadHandlePairNoGo
end Instances
end
end GQ2.Dyadic

section AxiomAudit

open GQ2.Dyadic.Instances.EvenMHeadHandlePairNoGo

#print axioms heisEta1_pairV_headHandlePairRawFamily_cocycle_eq_zero
#print axioms not_stokesDuality_headHandlePairRawFamily_of_sigma_trivial

end AxiomAudit

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandleMixedNielsen
import GQ2.Dyadic.Instances.EvenMHeadHandlePairStokesNoGo
import GQ2.Dyadic.Instances.EvenMRamifiedRow

namespace GQ2.Dyadic

/-!
# The repaired head-handle pairing

The pure head-handle exchange has a rank-uniform Stokes radical.  The mixed Nielsen repair
adds the old free `x₀` letter to the promoted handle.  On the formerly radical displaced
`x₂` coordinate, the compact ramified formula then has exactly one surviving handle-plane
term, namely `lam v`.

Both relators are included in the final theorem.  The tame relator vanishes because the
normal offsets have zero `sigma` and `tau` coordinates; the wild relator supplies `lam v`.
No ramification-class enumeration occurs.
-/

noncomputable section

open GQ2 GQ2.FoxH
open Count Certificates Words Certificates.MProcyclic
open Instances.EvenMHeadHandleMixed
open Instances.EvenMHeadHandlePairCore
open Instances.EvenMHeadHandlePairNormalize
open Instances.EvenMHeadHandlePairNoGo

namespace Instances.EvenMHeadHandleMixedPairing

variable {h : ℕ} {C A : Type*} [Group C] [AddCommGroup A]
  [DistribMulAction C A]

def mixedPairX (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) :
    Generator (2 + 2 * h) → A :=
  headHandlePairRamNormal t j 0 0 (pairVSlot j v)

def mixedPairY (t : Marking (2 + 2 * h) C) (j : Fin h) (lam : ElemDual A) :
    Generator (2 + 2 * h) → ElemDual A :=
  headHandlePairRamNormal t j lam 0 0

private def mixedPairHeis (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A)
    (lam : ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (g : Generator (2 + 2 * h)) : HeisLift A C :=
  heisEvalZ ⇑t (mixedPairX t j v) (mixedPairY t j lam) E E₂
    ((headHandleMixedNielsen j).backward g)

private theorem mixedPairHeis_z_eq_zero
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (g : Generator (2 + 2 * h)) :
    (mixedPairHeis t j v lam E E₂ g).z = 0 := by
  by_cases hg : g = handleU j
  · subst g
    rw [mixedPairHeis, headHandleMixedNielsen_backward_handleU, heisEvalZ_mul,
      heisEvalZ_gen, heisEvalZ_gen]
    simp [mixedPairX, mixedPairY, pairVSlot, HeisLift.mul_z]
  · rw [mixedPairHeis, headHandleMixedNielsen_backward_of_ne j g hg,
      heisEvalZ_gen]

private def mixedPairMark (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A)
    (lam : ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    Marking (2 + 2 * h) C :=
  ⟨fun g ↦ (mixedPairHeis t j v lam E E₂ g).g⟩

private def mixedPairPrimal (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A)
    (lam : ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    Generator (2 + 2 * h) → A :=
  fun g ↦ (mixedPairHeis t j v lam E E₂ g).a

private def mixedPairDual (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A)
    (lam : ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    Generator (2 + 2 * h) → ElemDual A :=
  fun g ↦ (mixedPairHeis t j v lam E E₂ g).l

private theorem mixedPairHeis_eq_heisGen
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    mixedPairHeis t j v lam E E₂ =
      heisGen ⇑(mixedPairMark t j v lam E E₂)
        (mixedPairPrimal t j v lam E E₂)
        (mixedPairDual t j v lam E E₂) := by
  funext g
  apply HeisLift.ext <;> simp [mixedPairMark, mixedPairPrimal, mixedPairDual,
    mixedPairHeis_z_eq_zero]

@[simp] private theorem mixedPairPrimal_sigma
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    mixedPairPrimal t j v lam E E₂ .sigma = 0 := by
  rw [mixedPairPrimal, mixedPairHeis, headHandleMixedNielsen_backward_sigma,
    heisEvalZ_gen]
  simp [mixedPairX, pairVSlot_zero]

@[simp] private theorem mixedPairDual_sigma
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    mixedPairDual t j v lam E E₂ .sigma = 0 := by
  rw [mixedPairDual, mixedPairHeis, headHandleMixedNielsen_backward_sigma,
    heisEvalZ_gen]
  simp [mixedPairY]

@[simp] private theorem mixedPairPrimal_tau
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    mixedPairPrimal t j v lam E E₂ .tau = 0 := by
  rw [mixedPairPrimal, mixedPairHeis, headHandleMixedNielsen_backward_tau,
    heisEvalZ_gen]
  simp [mixedPairX]

@[simp] private theorem mixedPairDual_tau
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    mixedPairDual t j v lam E E₂ .tau = 0 := by
  rw [mixedPairDual, mixedPairHeis, headHandleMixedNielsen_backward_tau,
    heisEvalZ_gen]
  simp [mixedPairY]

@[simp] private theorem mixedPairPrimal_coreTwo
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (hs : ∀ a : A, t.σ • a = a) :
    mixedPairPrimal t j v lam E E₂ (coreLetter h 2) = 0 := by
  have hsInv : t.σ⁻¹ • v = v := inv_smul_eq_iff.mpr (hs v).symm
  rw [mixedPairPrimal, mixedPairHeis, headHandleMixedNielsen_backward_coreTwo,
    heisEvalZ_gen]
  simp [mixedPairX, pairVSlot, hsInv]

@[simp] private theorem mixedPairDual_coreTwo
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    mixedPairDual t j v lam E E₂ (coreLetter h 2) = 0 := by
  rw [mixedPairDual, mixedPairHeis, headHandleMixedNielsen_backward_coreTwo,
    heisEvalZ_gen]
  simp [mixedPairY]

@[simp] private theorem mixedPairPrimal_handleU
    (t : Marking (2 + 2 * h) C) (j k : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    mixedPairPrimal t j v lam E E₂ (handleU k) = 0 := by
  by_cases hk : k = j
  · subst k
    rw [mixedPairPrimal, mixedPairHeis, headHandleMixedNielsen_backward_handleU,
      heisEvalZ_mul, heisEvalZ_gen, heisEvalZ_gen]
    simp [mixedPairX]
  · have hne : handleU k ≠ handleU j := by
      intro H
      have H' := congrArg (Generator.equivFin (2 + 2 * h)) H
      simp [handleU, Generator.equivFin] at H'
      exact hk (Fin.ext (by omega))
    rw [mixedPairPrimal, mixedPairHeis,
      headHandleMixedNielsen_backward_of_ne j (handleU k) hne, heisEvalZ_gen]
    simp [mixedPairX, headHandlePairSwap, pairVSlot_zero, hk]

@[simp] private theorem mixedPairDual_handleV
    (t : Marking (2 + 2 * h) C) (j k : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    mixedPairDual t j v lam E E₂ (handleV k) = 0 := by
  by_cases hk : k = j
  · subst k
    rw [mixedPairDual, mixedPairHeis, headHandleMixedNielsen_backward_handleV,
      heisEvalZ_gen]
    simp [mixedPairY]
  · have hne : handleV k ≠ handleU j := by
      intro H
      have H' := congrArg (Generator.equivFin (2 + 2 * h)) H
      simp [handleV, handleU, Generator.equivFin] at H'
      omega
    rw [mixedPairDual, mixedPairHeis,
      headHandleMixedNielsen_backward_of_ne j (handleV k) hne, heisEvalZ_gen]
    simp [mixedPairY, headHandlePairSwap, hk]

@[simp] private theorem mixedPairPrimal_handleV
    (t : Marking (2 + 2 * h) C) (j k : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    mixedPairPrimal t j v lam E E₂ (handleV k) = if k = j then v else 0 := by
  by_cases hk : k = j
  · subst k
    rw [mixedPairPrimal, mixedPairHeis, headHandleMixedNielsen_backward_handleV,
      heisEvalZ_gen]
    simp [mixedPairX, pairVSlot]
  · have hne : handleV k ≠ handleU j := by
      intro H
      have H' := congrArg (Generator.equivFin (2 + 2 * h)) H
      simp [handleV, handleU, Generator.equivFin] at H'
      omega
    rw [mixedPairPrimal, mixedPairHeis,
      headHandleMixedNielsen_backward_of_ne j (handleV k) hne, heisEvalZ_gen]
    simp [mixedPairX, headHandlePairSwap, pairVSlot, hk]

@[simp] private theorem mixedPairDual_handleU
    (t : Marking (2 + 2 * h) C) (j k : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (hs : ∀ a : A, t.σ • a = a) :
    mixedPairDual t j v lam E E₂ (handleU k) = if k = j then lam else 0 := by
  by_cases hk : k = j
  · subst k
    rw [mixedPairDual, mixedPairHeis, headHandleMixedNielsen_backward_handleU,
      heisEvalZ_mul, heisEvalZ_gen, heisEvalZ_gen]
    have hsD : t.σ • lam = lam := elemDual_smul_eq_self hs lam
    simp [mixedPairY, hsD]
  · have hne : handleU k ≠ handleU j := by
      intro H
      have H' := congrArg (Generator.equivFin (2 + 2 * h)) H
      simp [handleU, Generator.equivFin] at H'
      exact hk (Fin.ext (by omega))
    rw [mixedPairDual, mixedPairHeis,
      headHandleMixedNielsen_backward_of_ne j (handleU k) hne, heisEvalZ_gen]
    simp [mixedPairY, headHandlePairSwap, hk]

@[simp] private theorem mixedPairPrimal_coreZero
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    mixedPairPrimal t j v lam E E₂ (coreLetter h 0) = 0 := by
  rw [mixedPairPrimal, mixedPairHeis, headHandleMixedNielsen_backward_coreZero,
    heisEvalZ_gen]
  simp [mixedPairX]

@[simp] private theorem mixedPairPrimal_coreOne
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    mixedPairPrimal t j v lam E E₂ (coreLetter h 1) = 0 := by
  rw [mixedPairPrimal, mixedPairHeis, headHandleMixedNielsen_backward_coreOne,
    heisEvalZ_gen]
  simp [mixedPairX]

@[simp] private theorem mixedPairDual_coreZero
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    mixedPairDual t j v lam E E₂ (coreLetter h 0) = lam := by
  rw [mixedPairDual, mixedPairHeis, headHandleMixedNielsen_backward_coreZero,
    heisEvalZ_gen]
  simp [mixedPairY]

@[simp] private theorem mixedPairDual_coreOne
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    mixedPairDual t j v lam E E₂ (coreLetter h 1) = 0 := by
  rw [mixedPairDual, mixedPairHeis, headHandleMixedNielsen_backward_coreOne,
    heisEvalZ_gen]
  simp [mixedPairY]

@[simp] private theorem mixedPairMark_tau
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    (mixedPairMark t j v lam E E₂).τ = t.τ := by
  change (mixedPairHeis t j v lam E E₂ .tau).g = t.τ
  rw [mixedPairHeis,
    headHandleMixedNielsen_backward_tau, heisEvalZ_gen]
  rfl

private theorem mixedPairMark_wild_trivial
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hs : ∀ a : A, t.σ • a = a)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a) :
    ∀ (i : Fin (2 + 2 * h + 1)) (a : A),
      (mixedPairMark t j v lam E E₂).x i • a = a := by
  intro i a
  change (mixedPairHeis t j v lam E E₂ (.wild i)).g • a = a
  by_cases hi : (Generator.wild i : Generator (2 + 2 * h)) = handleU j
  · rw [hi, mixedPairHeis,
      headHandleMixedNielsen_backward_handleU, heisEvalZ_mul,
      heisEvalZ_gen, heisEvalZ_gen]
    change (t.σ * t (coreLetter h 0)) • a = a
    rw [mul_smul, hs]
    exact hwild ⟨0, by omega⟩ a
  · rw [mixedPairHeis,
      headHandleMixedNielsen_backward_of_ne j (.wild i) hi, heisEvalZ_gen]
    exact pairSwap_wild_trivial t j hs hwild i a

theorem heisZ_headHandleMixedW_pair
    [Finite C] [Finite A]
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha : ℕ)
    (hA₂ : ∀ a : A, a + a = 0)
    (hs : ∀ a : A, t.σ • a = a)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (hresA : ResolverLifts E (WordLift A C))
    (hresD : ResolverLifts E (WordLift (ElemDual A) C))
    (hres : ResolverLifts E C) :
    (heisEvalZ ⇑t (mixedPairX t j v) (mixedPairY t j lam) E E₂
      (headHandleMixedW alpha j)).z = lam v := by
  rw [headHandleMixedW]
  change (PWord.evalZ (heisGen ⇑t (mixedPairX t j v)
      (mixedPairY t j lam)) E E₂
    (PWord.subst (headHandleMixedNielsen j).backward
      (Words.MCompact.mCompactW alpha h))).z = lam v
  rw [PWord.evalZ_subst]
  change (PWord.evalZ (mixedPairHeis t j v lam E E₂) E E₂
    (Words.MCompact.mCompactW alpha h)).z = lam v
  rw [mixedPairHeis_eq_heisGen]
  change (heisEvalZ ⇑(mixedPairMark t j v lam E E₂)
    (mixedPairPrimal t j v lam E E₂)
    (mixedPairDual t j v lam E E₂) E E₂
    (Words.MCompact.mCompactW alpha h)).z = lam v
  rw [MCompactRam.heisZ_mCompact_ram
    (t := mixedPairMark t j v lam E E₂)
    (x := mixedPairPrimal t j v lam E E₂)
    (y := mixedPairDual t j v lam E E₂)
    (E := E) (E₂ := E₂) (α := alpha) hA₂
    (mixedPairMark_wild_trivial t j v lam E E₂ hs hwild)
    (by simpa using hτfpf)
    (by simpa using hTodd)
    (mixedPairPrimal_sigma t j v lam E E₂)
    (mixedPairDual_sigma t j v lam E E₂)
    (mixedPairPrimal_tau t j v lam E E₂)
    (mixedPairDual_tau t j v lam E E₂)
    (mixedPairPrimal_coreTwo t j v lam E E₂ hs)
    (mixedPairDual_coreTwo t j v lam E E₂)
    hresA hresD hres]
  simp only [mixedPairPrimal_coreOne, mixedPairDual_coreOne,
    mixedPairPrimal_coreZero, mixedPairDual_coreZero, map_zero, zero_add]
  rw [Finset.sum_eq_single j]
  · simp [mixedPairPrimal_handleU, mixedPairDual_handleU,
      mixedPairPrimal_handleV, mixedPairDual_handleV, hs]
  · intro k _ hk
    simp [mixedPairPrimal_handleU, mixedPairDual_handleU,
      mixedPairPrimal_handleV, mixedPairDual_handleV, hs, hk]
  · simp

def headHandleMixedRawFamily (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (alpha h q : ℕ) (j : Fin h) :
    Fin 2 → FreeGroup (Generator (2 + 2 * h)) :=
  fun l ↦ heisToFree E E₂
    (gammaFam (2 + 2 * h) q (headHandleMixedW alpha j) l)

theorem heisEta1_headHandleMixedRawFamily_pair
    [Finite C] [Finite A]
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha q : ℕ)
    (hA₂ : ∀ a : A, a + a = 0)
    (hs : ∀ a : A, t.σ • a = a)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (hresA : ResolverLifts E (WordLift A C))
    (hresD : ResolverLifts E (WordLift (ElemDual A) C))
    (hres : ResolverLifts E C) :
    heisEta1 ⇑t (headHandleMixedRawFamily E E₂ alpha h q j)
      (mixedPairX t j v) (mixedPairY t j lam) = lam v := by
  rw [heisEta1_apply, Fin.sum_univ_two]
  change (FreeGroup.lift (heisGen ⇑t (mixedPairX t j v)
      (mixedPairY t j lam))
      (heisToFree E E₂ (tameRelW (2 + 2 * h) q))).z
    + (FreeGroup.lift (heisGen ⇑t (mixedPairX t j v)
      (mixedPairY t j lam))
      (heisToFree E E₂ (headHandleMixedW alpha j))).z = lam v
  rw [← heisEvalZ_eq_lift, ← heisEvalZ_eq_lift]
  rw [heisZ_tameRelW_eq_zero_of_tame_offsets_zero t _ _ E E₂
      (by simp [mixedPairX]) (by simp [mixedPairX])
      (by simp [mixedPairY]) (by simp [mixedPairY]),
    zero_add]
  exact heisZ_headHandleMixedW_pair t j v lam E E₂ alpha hA₂ hs
    hwild hτfpf hTodd hresA hresD hres

end EvenMHeadHandleMixedPairing
end Instances
end
end GQ2.Dyadic

section AxiomAudit

open GQ2.Dyadic.Instances.EvenMHeadHandleMixedPairing

#print axioms mixedPairX
#print axioms mixedPairY
#print axioms heisZ_headHandleMixedW_pair
#print axioms headHandleMixedRawFamily
#print axioms heisEta1_headHandleMixedRawFamily_pair

end AxiomAudit

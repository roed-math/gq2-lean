/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicStokes

/-!
# Ramified Stokes duality after the full hyperbolic Nielsen transport

The full Nielsen transport of the two compact-`M` relators has ramified Stokes duality in every
handle rank.  The proof evaluates the transported family at its induced marking and applies the
landed compact-`M` theorem.  In particular, the head-handle source needs no separate Hessian or
nilpotency-class calculation.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH
open Count Certificates Words Certificates.MProcyclic
open Instances.GammaRPWordNielsen
open Instances.GammaRPWordNielsenElementary
open Instances.EvenMHeadHandleSource
open Instances.EvenMHeadHandlePairSource
open Instances.EvenMHeadHandlePairCore
open Instances.EvenMHeadHandlePairNoGo
open Instances.EvenMHeadHandleMixed
open Instances.EvenMHeadHandleHyperbolic
open Instances.EvenMHeadHandlePairNormalize
open Instances.EvenMHeadHandleHyperbolicStokes

namespace Instances.EvenMHeadHandleHyperbolicRamifiedStokes

private def inducedMark
    {h : ℕ} {C : Type*} [Group C]
    (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (j : Fin h) : Marking (2 + 2 * h) C :=
  ⟨freeSubstMark ⇑t (fun g ↦
    heisToFree E E₂ ((headHandleHyperbolicNielsen j).backward g))⟩

@[simp] private theorem inducedMark_tau
    {h : ℕ} {C : Type*} [Group C]
    (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (j : Fin h) :
    (inducedMark t E E₂ j).τ = t.τ := by
  change FreeGroup.lift ⇑t
    (heisToFree E E₂ ((headHandleHyperbolicNielsen j).backward .tau)) = t .tau
  rw [headHandleHyperbolicNielsen_backward_tau]
  simp [heisToFree]

@[simp] private theorem inducedMark_sigma
    {h : ℕ} {C : Type*} [Group C]
    (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (j : Fin h) :
    (inducedMark t E E₂ j).σ = t (handleU j) := by
  change FreeGroup.lift ⇑t
    (heisToFree E E₂ ((headHandleHyperbolicNielsen j).backward .sigma)) = _
  rw [headHandleHyperbolicNielsen_backward_sigma]
  simp [heisToFree]

private theorem inducedMark_wild_trivial
    {h : ℕ} {C A : Type*} [Group C] [AddCommGroup A]
    [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (j : Fin h)
    (hs : ∀ a : A, t.σ • a = a)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a) :
    ∀ (i : Fin (2 + 2 * h + 1)) (a : A),
      (inducedMark t E E₂ j).x i • a = a := by
  intro i a
  change FreeGroup.lift ⇑t
      (heisToFree E E₂ ((headHandleHyperbolicNielsen j).backward (.wild i))) • a = a
  by_cases hi : (Generator.wild i : Generator (2 + 2 * h)) = handleU j
  · rw [hi, headHandleHyperbolicNielsen_backward_handleU]
    simp [heisToFree, mul_smul]
    rw [hs]
    exact hwild ⟨3 + 2 * (j : ℕ), by have := j.isLt; omega⟩ a
  · rw [headHandleHyperbolicNielsen_backward_of_ne j (.wild i) hi]
    simp [heisToFree]
    exact pairSwap_wild_trivial t j hs hwild i a

private theorem lift_fullFamily_eq_induced
    {h alpha q : ℕ} {C : Type*} [Group C]
    (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (j : Fin h) (k : Fin 2) :
    FreeGroup.lift ⇑t
        (headHandleHyperbolicFullFamily E E₂ alpha h q j k) =
      FreeGroup.lift ⇑(inducedMark t E E₂ j)
        (heisToFree E E₂
          (gammaFam (2 + 2 * h) q (Words.MCompact.mCompactW alpha h) k)) := by
  rw [headHandleHyperbolicFullFamily, heisToFree_subst, lift_lift_freeSubst]
  rfl

/-- Ramified Stokes duality for the full transported family, uniform in all parameters. -/
theorem stokesDuality_headHandleHyperbolicFullFamily_ramified
    {h alpha q : ℕ} {C A : Type} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (j : Fin h)
    (hA₂ : ∀ a : A, a + a = 0) (hq : Even q)
    (hs : ∀ a : A, t.σ • a = a)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (hr : ∀ k, FreeGroup.lift ⇑t
      (headHandleHyperbolicFullFamily
        (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
        (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ)) alpha h q j k) = 1) :
    StokesDuality ⇑t
      (headHandleHyperbolicFullFamily
        (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
        (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ)) alpha h q j) A := by
  let e := omega2Exp (4 * Monoid.exponent C)
  let E : Zhat → ℤ := fun _ ↦ (e : ℤ)
  let E₂ : ℤ_[2] → ℤ := fun _ ↦ (e : ℤ)
  let s := inducedMark t E E₂ j
  have he : Odd e := odd_omega2Exp
    (fourMulExponent_ne_zero_and_even C).1
    (fourMulExponent_ne_zero_and_even C).2
  have hswild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), s.x i • a = a :=
    inducedMark_wild_trivial t E E₂ j hs hwild
  have hsτfpf : ∀ a : A, s.τ • a = a → a = 0 := by
    simpa [s] using hτfpf
  have hsTodd : ∀ a : A, powOmega2 s.τ • a = a := by
    simpa [s] using hTodd
  have hrel : ∀ k, FreeGroup.lift ⇑s
      (heisToFree E E₂
        (gammaFam (2 + 2 * h) q (Words.MCompact.mCompactW alpha h) k)) = 1 := by
    intro k
    rw [← lift_fullFamily_eq_induced t E E₂ j k]
    simpa [E, E₂, e] using hr k
  have ht : s.TameRelAt q := by
    have hzero := hrel 0
    simp only [gammaFam_zero] at hzero
    have hz : PWord.evalZ ⇑s E E₂ (tameRelW (2 + 2 * h) q) = 1 :=
      (lift_heisToFree_eq_one_iff ⇑s E E₂ _).mp hzero
    rw [tameRelW, PWord.evalZ_mul, PWord.evalZ_conj,
      PWord.evalZ_inv, PWord.evalZ_zpow, PWord.evalZ_gen,
      PWord.evalZ_gen, zpow_natCast] at hz
    exact mul_inv_eq_one.mp hz
  have hM : PWord.evalZ ⇑s E E₂ (Words.MCompact.mCompactW alpha h) = 1 := by
    have hone := hrel 1
    simp only [gammaFam_one] at hone
    exact (lift_heisToFree_eq_one_iff ⇑s E E₂ _).mp hone
  have hsep : ∀ p : A × A × (Fin h × Fin 2 → A), p ≠ 0 →
      ∃ r : ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A),
        heisEta1 ⇑s (Certificates.MCompact.mCompactFam alpha h q e)
          (evenNormal h p.1 p.2.1 p.2.2)
          (evenNormal h r.1 r.2.1 r.2.2) ≠ 0 := by
    intro p hp
    simpa [e] using
      (MCompactRam.mCompactFam_normal_pairing_separates_left
        (h := h) (α := alpha) (q := q) (C := C) (A := A)
        s hA₂ hswild hsτfpf hsTodd p hp)
  have hcompact : StokesDuality ⇑s
      (Certificates.MCompact.mCompactFam alpha h q e) A :=
    mCompactStokesDuality_ramified_of_separation
      s hA₂ hq ht hswild hsτfpf hsTodd (by simpa [E, E₂, e] using hM) hsep
  have hend : IsStokesEndpoint (fun l : Fin 2 ↦ heisToFree E E₂
      (gammaFam (2 + 2 * h) q (Words.MCompact.mCompactW alpha h) l)) :=
    EvenMHeadHandlePairNormalize.mCompactOf_isStokesEndpoint hq (by simpa [E, e] using he)
  apply (stokesDuality_headHandleHyperbolicFullFamily_iff t E E₂ j hend).mpr
  have hsfun : ⇑s = freeSubstMark ⇑t (fun g ↦
      heisToFree E E₂ ((headHandleHyperbolicNielsen j).backward g)) := rfl
  have hfam : Certificates.MCompact.mCompactFam alpha h q e =
      fun l ↦ heisToFree E E₂
        (gammaFam (2 + 2 * h) q (Words.MCompact.mCompactW alpha h) l) := by
    funext l
    fin_cases l <;> rfl
  rw [← hsfun, ← hfam]
  exact hcompact

#print axioms stokesDuality_headHandleHyperbolicFullFamily_ramified

end Instances.EvenMHeadHandleHyperbolicRamifiedStokes
end
end GQ2.Dyadic

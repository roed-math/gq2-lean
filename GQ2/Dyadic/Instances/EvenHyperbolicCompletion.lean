/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.FoxHeisenberg.Basic

/-!
# Completing a normal pairing by a hyperbolic plane

A pairing may have arbitrary cross terms involving one distinguished U coordinate.  If its
restriction to U = 0 is the compact-M core form plus the remaining handle planes, and the
pure U/V cross pairings are evaluation, then the whole pairing separates primal vectors.
This algebraic argument is uniform in the number of handles and the coefficient group.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2.FoxH

namespace HyperbolicCompletion

abbrev Coordinates (h : ℕ) (A : Type*) := A × A × (Fin h × Fin 2 → A)

def pureU {h : ℕ} {A : Type*} [Zero A] (j : Fin h) (a : A) : Coordinates h A :=
  (0, 0, Pi.single (j, 0) a)

def pureV {h : ℕ} {A : Type*} [Zero A] (j : Fin h) (a : A) : Coordinates h A :=
  (0, 0, Pi.single (j, 1) a)

variable {h : ℕ} {A : Type*} [AddCommGroup A]

/-- Separation survives arbitrary cross terms through one coordinate, provided its partner
is radical on the complementary subspace and the two cross terms form a hyperbolic plane. -/
theorem separates_of_zeroU_and_cross
    (j : Fin h)
    (B : Coordinates h A →+ (Coordinates h (ElemDual A) →+ ZMod 2))
    (hseparate : ∀ a : A, a ≠ 0 → ∃ lam : ElemDual A, lam a ≠ 0)
    (hzero : ∀ (p : Coordinates h A) (r : Coordinates h (ElemDual A)),
      p.2.2 (j, 0) = 0 → r.2.2 (j, 0) = 0 →
      B p r = r.2.1 p.2.1 + (r.1 p.2.1 + r.2.1 p.1)
        + ∑ k, (r.2.2 (k, 0) (p.2.2 (k, 1)) + r.2.2 (k, 1) (p.2.2 (k, 0))))
    (hUV : ∀ (a : A) (lam : ElemDual A), B (pureU j a) (pureV j lam) = lam a)
    (hVU : ∀ (a : A) (lam : ElemDual A), B (pureV j a) (pureU j lam) = lam a)
    (p : Coordinates h A) (hp : p ≠ 0) :
    ∃ r : Coordinates h (ElemDual A), B p r ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have hU : p.2.2 (j, 0) = 0 := by
    by_contra hU
    obtain ⟨lam, hlam⟩ := hseparate _ hU
    let p₀ := p - pureU j (p.2.2 (j, 0))
    have hp₀ : p₀.2.2 (j, 0) = 0 := by simp [p₀, pureU]
    have hpair : B p₀ (pureV j lam) = 0 := by
      rw [hzero p₀ (pureV j lam) hp₀ (by simp [pureV])]
      have hsum : (∑ k, ((pureV j lam).2.2 (k, 0) (p₀.2.2 (k, 1))
          + (pureV j lam).2.2 (k, 1) (p₀.2.2 (k, 0)))) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        by_cases hk : k = j
        · subst k; simp [pureV, hp₀]
        · simp [pureV, hk]
      rw [hsum]
      simp [pureV]
    have heq : B p₀ (pureV j lam) = -lam (p.2.2 (j, 0)) := by
      change B (p - pureU j (p.2.2 (j, 0))) (pureV j lam) = _
      rw [map_sub, AddMonoidHom.sub_apply, hn, hUV, zero_sub]
    exact hlam (neg_eq_zero.mp (heq.symm.trans hpair))
  have h1 : p.2.1 = 0 := by
    by_contra hp1
    obtain ⟨lam, hlam⟩ := hseparate _ hp1
    have heq := hzero p (lam, 0, 0) hU (by simp)
    simp [hn] at heq
    exact hlam heq.symm
  have h0 : p.1 = 0 := by
    by_contra hp0
    obtain ⟨lam, hlam⟩ := hseparate _ hp0
    have heq := hzero p (0, lam, 0) hU (by simp)
    simp [hn, h1] at heq
    exact hlam heq.symm
  have hother : ∀ k : Fin h, k ≠ j → ∀ l : Fin 2, p.2.2 (k, l) = 0 := by
    intro k hkj l
    by_contra hkl
    obtain ⟨lam, hlam⟩ := hseparate _ hkl
    fin_cases l
    · have hpair := hzero p (pureV k lam) hU (by simp [pureV])
      have hsum : (∑ b, ((pureV k lam).2.2 (b, 0) (p.2.2 (b, 1))
          + (pureV k lam).2.2 (b, 1) (p.2.2 (b, 0)))) = lam (p.2.2 (k, 0)) := by
        rw [Finset.sum_eq_single k]
        · simp [pureV]
        · intro b _ hbk; simp [pureV, hbk]
        · simp
      rw [hsum] at hpair
      simp [hn, pureV, h0, h1] at hpair
      exact hlam hpair.symm
    · have hpair := hzero p (pureU k lam) hU (by simp [pureU, Ne.symm hkj])
      have hsum : (∑ b, ((pureU k lam).2.2 (b, 0) (p.2.2 (b, 1))
          + (pureU k lam).2.2 (b, 1) (p.2.2 (b, 0)))) = lam (p.2.2 (k, 1)) := by
        rw [Finset.sum_eq_single k]
        · simp [pureU]
        · intro b _ hbk; simp [pureU, hbk]
        · simp
      rw [hsum] at hpair
      simp [hn, pureU, h0, h1] at hpair
      exact hlam hpair.symm
  have hpV : p = pureV j (p.2.2 (j, 1)) := by
    apply Prod.ext h0
    apply Prod.ext h1
    funext kl
    rcases kl with ⟨k, l⟩
    by_cases hk : k = j
    · subst k
      fin_cases l <;> simp [pureV, hU]
    · simp [pureV, hk, hother k hk l]
  have hV : p.2.2 (j, 1) = 0 := by
    by_contra hv
    obtain ⟨lam, hlam⟩ := hseparate _ hv
    have heq := hn (pureU j lam)
    rw [hpV, hVU] at heq
    exact hlam heq
  apply hp
  rw [hpV, hV]
  simp [pureV]

#print axioms separates_of_zeroU_and_cross

private def swapCoordinates : Coordinates h A ≃+ Coordinates h A where
  toFun p := (p.1, p.2.1, fun kl ↦ p.2.2 (kl.1, kl.2.rev))
  invFun p := (p.1, p.2.1, fun kl ↦ p.2.2 (kl.1, kl.2.rev))
  left_inv p := by simp
  right_inv p := by simp
  map_add' _ _ := rfl

private theorem swapCoordinates_pureU (j : Fin h) (a : A) :
    swapCoordinates (pureU j a) = pureV j a := by
  refine Prod.ext ?_ ?_
  · rfl
  refine Prod.ext ?_ ?_
  · rfl
  funext kl
  rcases kl with ⟨k, l⟩
  by_cases hkj : k = j
  · subst k
    fin_cases l <;> simp [swapCoordinates, pureU, pureV]
  · fin_cases l <;> simp [swapCoordinates, pureU, pureV, Pi.single, hkj]

private theorem swapCoordinates_pureV (j : Fin h) (a : A) :
    swapCoordinates (pureV j a) = pureU j a := by
  refine Prod.ext ?_ ?_
  · rfl
  refine Prod.ext ?_ ?_
  · rfl
  funext kl
  rcases kl with ⟨k, l⟩
  by_cases hkj : k = j
  · subst k
    fin_cases l <;> simp [swapCoordinates, pureU, pureV]
  · fin_cases l <;> simp [swapCoordinates, pureU, pureV, Pi.single, hkj]

/-- The same completion criterion with the distinguished V coordinate removed. -/
theorem separates_of_zeroV_and_cross
    (j : Fin h)
    (B : Coordinates h A →+ (Coordinates h (ElemDual A) →+ ZMod 2))
    (hseparate : ∀ a : A, a ≠ 0 → ∃ lam : ElemDual A, lam a ≠ 0)
    (hzero : ∀ (p : Coordinates h A) (r : Coordinates h (ElemDual A)),
      p.2.2 (j, 1) = 0 → r.2.2 (j, 1) = 0 →
      B p r = r.2.1 p.2.1 + (r.1 p.2.1 + r.2.1 p.1)
        + ∑ k, (r.2.2 (k, 0) (p.2.2 (k, 1)) + r.2.2 (k, 1) (p.2.2 (k, 0))))
    (hUV : ∀ (a : A) (lam : ElemDual A), B (pureU j a) (pureV j lam) = lam a)
    (hVU : ∀ (a : A) (lam : ElemDual A), B (pureV j a) (pureU j lam) = lam a)
    (p : Coordinates h A) (hp : p ≠ 0) :
    ∃ r : Coordinates h (ElemDual A), B p r ≠ 0 := by
  let B' : Coordinates h A →+ (Coordinates h (ElemDual A) →+ ZMod 2) :=
    { toFun x := (B (swapCoordinates x)).comp swapCoordinates.toAddMonoidHom
      map_zero' := by ext r; simp
      map_add' _ _ := by ext r; simp }
  have hzero' : ∀ (x : Coordinates h A) (y : Coordinates h (ElemDual A)),
      x.2.2 (j, 0) = 0 → y.2.2 (j, 0) = 0 →
      B' x y = y.2.1 x.2.1 + (y.1 x.2.1 + y.2.1 x.1)
        + ∑ k, (y.2.2 (k, 0) (x.2.2 (k, 1)) + y.2.2 (k, 1) (x.2.2 (k, 0))) := by
    intro x y hx hy
    have H := hzero (swapCoordinates x) (swapCoordinates y)
      (by simpa [swapCoordinates] using hx) (by simpa [swapCoordinates] using hy)
    simpa [B', swapCoordinates, add_comm] using H
  obtain ⟨r, hr⟩ := separates_of_zeroU_and_cross j B' hseparate hzero'
    (by intro a lam; simpa [B', swapCoordinates_pureU, swapCoordinates_pureV] using hVU a lam)
    (by intro a lam; simpa [B', swapCoordinates_pureU, swapCoordinates_pureV] using hUV a lam)
    (swapCoordinates.symm p) (by simpa using hp)
  refine ⟨swapCoordinates r, ?_⟩
  simpa [B'] using hr

#print axioms separates_of_zeroV_and_cross

end HyperbolicCompletion
end
end GQ2.Dyadic

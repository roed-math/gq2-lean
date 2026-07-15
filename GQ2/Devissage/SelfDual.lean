/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Devissage.Chi1

@[expose] public section

/-!
# §5.11 dévissage: word-internal self-duality and the four lemma

Part of the §5.11 dévissage development (split from `GQ2/Devissage.lean`).
-/

namespace GQ2.FoxH

open scoped Pointwise

variable {C : Type*} [Group C]

/-! ## Word-internal self-duality

The marking-internal form of the `IsSelfDual` package: `#H⁰w(A^∨)` in place of
`#fixedPts C (A^∨)`.  For a *generating* marking (`t.Generates`) the two agree — `ker d⁰` is then
exactly the `C`-fixed points; `lemma_5_11`'s dévissage propagates the internal form, and the
`fixedPts`-form follows wherever generation is available. -/

section SelfDualW

variable {A : Type*} [AddCommGroup A] [DistribMulAction C A] [Finite A] [Finite C]

/-- **Word-internal self-duality** (the `IsSelfDual` package with the invariants of the dual
replaced by the word-complex `H⁰w` of the dual). -/
def IsSelfDualW (t : Marking C) (A : Type*) [AddCommGroup A] [DistribMulAction C A]
    [Finite A] : Prop :=
  (Nat.card (H2w (A := A) t) = Nat.card (H0w (A := ElemDual A) t)) ∧
  (Nat.card (Z1w (A := A) t) = Nat.card A ^ 2 * Nat.card (H0w (A := ElemDual A) t)) ∧
  ∃ P : H1w (A := A) t → H1w (A := ElemDual A) t → ZMod 2,
    (∀ (x : Z1w (A := A) t) (y : Z1w (A := ElemDual A) t),
        P (h1wMk t x) (h1wMk t y) = mixedB t x.val y.val) ∧
    (∀ h, h ≠ 0 → ∃ h', P h h' ≠ 0) ∧
    (∀ h', h' ≠ 0 → ∃ h, P h h' ≠ 0)

/-- `IsSelfDualW` in `χ`-language: `χ²` bijective and `χ¹`, `χ¹ᵀ` injective.  (The second card
clause is rank-nullity; the pairing clause is `pairing_clause_iff`.) -/
theorem isSelfDualW_iff (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hA₂ : ∀ a : A, a + a = 0) :
    IsSelfDualW t A ↔
      (Function.Bijective (chi2 (A := A) t ht hw) ∧
        Function.Injective (chi1 (A := A) t ht hw) ∧
        Function.Injective (chi1T (A := A) t ht hw)) := by
  have : Finite (H2w (A := A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have hED : Nat.card (ElemDual (H0w (A := ElemDual A) t))
      = Nat.card (H0w (A := ElemDual A) t) :=
    card_elemDual (A := H0w (A := ElemDual A) t)
      (H0w_two_torsion t ElemDual.add_self_eq_zero)
  constructor
  · rintro ⟨hc1, -, hpair⟩
    refine ⟨?_, (pairing_clause_iff t ht hw).mp hpair⟩
    rw [Nat.bijective_iff_surjective_and_card]
    exact ⟨chi2_surjective t ht hw hA₂, hc1.trans hED.symm⟩
  · rintro ⟨hbij, hinj, hinjT⟩
    have hc1 : Nat.card (H2w (A := A) t) = Nat.card (H0w (A := ElemDual A) t) :=
      (Nat.card_eq_of_bijective _ hbij).trans hED
    exact ⟨hc1, by rw [card_Z1w_eq_sq_mul_card_H2w, hc1],
      (pairing_clause_iff t ht hw).mpr ⟨hinj, hinjT⟩⟩

/-- From a `IsSelfDualW`-package, **all six** `χ`-maps are bijective (the free halves plus the
Euler-characteristic swap `#H⁰w(A) = #H²w(A^∨)`). -/
theorem chi_bij_of_selfdualW (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hA₂ : ∀ a : A, a + a = 0) (hsd : IsSelfDualW t A) :
    Function.Bijective (chi2 (A := A) t ht hw) ∧
      Function.Bijective (chi2T (A := A) t ht hw) ∧
      Function.Bijective (chi0 (A := A) t ht hw) ∧
      Function.Bijective (chi0T (A := A) t ht hw) ∧
      Function.Bijective (chi1 (A := A) t ht hw) ∧
      Function.Bijective (chi1T (A := A) t ht hw) := by
  have : Finite (H1w (A := A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1w (A := ElemDual A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2w (A := A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2w (A := ElemDual A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have hD₂ : ∀ lam : ElemDual A, lam + lam = 0 := ElemDual.add_self_eq_zero
  obtain ⟨hbij2, hinj1, hinj1T⟩ := (isSelfDualW_iff t ht hw hA₂).mp hsd
  obtain ⟨hbij1, hbij1T, h11⟩ := chi1_bij_of_inj t ht hw hA₂ hinj1 hinj1T
  -- The card package.
  have hc1 : Nat.card (H2w (A := A) t) = Nat.card (H0w (A := ElemDual A) t) := hsd.1
  have hAD : Nat.card (ElemDual A) = Nat.card A := card_elemDual hA₂
  -- Euler swap: `#H⁰w(A) = #H²w(A^∨)`.
  have hswap : Nat.card (H0w (A := A) t) = Nat.card (H2w (A := ElemDual A) t) := by
    have e1 := card_H1w_eq (A := A) t ht hw
    have e2 := card_H1w_eq (A := ElemDual A) t ht hw
    have hprod : Nat.card A * (Nat.card (H0w (A := A) t) * Nat.card (H2w (A := A) t))
        = Nat.card A * (Nat.card (H0w (A := ElemDual A) t)
            * Nat.card (H2w (A := ElemDual A) t)) := by
      calc Nat.card A * (Nat.card (H0w (A := A) t) * Nat.card (H2w (A := A) t))
          = Nat.card (H1w (A := A) t) := by rw [e1]; ring
        _ = Nat.card (H1w (A := ElemDual A) t) := h11
        _ = Nat.card (ElemDual A) * (Nat.card (H0w (A := ElemDual A) t)
              * Nat.card (H2w (A := ElemDual A) t)) := by rw [e2]; ring
        _ = Nat.card A * (Nat.card (H0w (A := ElemDual A) t)
              * Nat.card (H2w (A := ElemDual A) t)) := by rw [hAD]
    have hcancel := Nat.eq_of_mul_eq_mul_left Nat.card_pos hprod
    rw [hc1, mul_comm] at hcancel
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hcancel
  -- The four evaluation bijectivities.
  refine ⟨hbij2, ?_, ?_, ?_, hbij1, hbij1T⟩
  · -- `χ²ᵀ : H²w(A^∨) → (H⁰w(A))^∨`: always surjective; cards by the swap.
    rw [Nat.bijective_iff_surjective_and_card]
    refine ⟨chi2T_surjective t ht hw hA₂, ?_⟩
    rw [hswap.symm, (card_elemDual (A := H0w (A := A) t) (H0w_two_torsion t hA₂)).symm]
  · -- `χ⁰ : H⁰w(A) → (H²w(A^∨))^∨`: always injective; cards by the swap.
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨chi0_injective t ht hw hA₂, ?_⟩
    rw [hswap, (card_elemDual (A := H2w (A := ElemDual A) t)
      (H2w_two_torsion t hD₂)).symm]
  · -- `χ⁰ᵀ : H⁰w(A^∨) → (H²w(A))^∨`: always injective; cards by clause (i).
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨chi0T_injective t ht hw, ?_⟩
    rw [← hc1, (card_elemDual (A := H2w (A := A) t) (H2w_two_torsion t hA₂)).symm]

end SelfDualW

/-! ## The four lemma (injectivity form)

The standard diagram chase, hand-rolled for `AddMonoidHom`s with pointwise exactness data — the
engine that turns the ladder squares into the conditional halves of the `χ`-bijectivities. -/

section FourLemma

variable {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type*}
  [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃] [AddCommGroup A₄]
  [AddCommGroup B₁] [AddCommGroup B₂] [AddCommGroup B₃] [AddCommGroup B₄]

/-- **Four lemma, injectivity**: in a commuting ladder with exact rows, if `m₁` is surjective and
`m₂`, `m₄` are injective, then `m₃` is injective.  (Exactness is taken pointwise; only the
`ker ⊆ im` direction is needed on the bottom row.) -/
theorem four_lemma_inj (a₁ : A₁ →+ A₂) (a₂ : A₂ →+ A₃) (a₃ : A₃ →+ A₄)
    (b₁ : B₁ →+ B₂) (b₂ : B₂ →+ B₃) (b₃ : B₃ →+ B₄)
    (m₁ : A₁ →+ B₁) (m₂ : A₂ →+ B₂) (m₃ : A₃ →+ B₃) (m₄ : A₄ →+ B₄)
    (sq₁ : ∀ x, m₂ (a₁ x) = b₁ (m₁ x))
    (sq₂ : ∀ x, m₃ (a₂ x) = b₂ (m₂ x))
    (sq₃ : ∀ x, m₄ (a₃ x) = b₃ (m₃ x))
    (htop₂ : ∀ x : A₂, a₂ x = 0 ↔ x ∈ a₁.range)
    (htop₃ : ∀ x : A₃, a₃ x = 0 ↔ x ∈ a₂.range)
    (hbot₂ : ∀ y : B₂, b₂ y = 0 → y ∈ b₁.range)
    (hm₁ : Function.Surjective m₁) (hm₂ : Function.Injective m₂)
    (hm₄ : Function.Injective m₄) :
    Function.Injective m₃ := by
  rw [injective_iff_map_eq_zero]
  intro x₃ hx₃
  -- `m₄ (a₃ x₃) = b₃ (m₃ x₃) = 0` and `m₄` injective, so `a₃ x₃ = 0`, so `x₃ = a₂ x₂`.
  have ha₃ : a₃ x₃ = 0 := by
    have h := sq₃ x₃
    rw [hx₃, map_zero] at h
    exact (injective_iff_map_eq_zero m₄).mp hm₄ _ h
  obtain ⟨x₂, rfl⟩ := AddMonoidHom.mem_range.mp ((htop₃ _).mp ha₃)
  -- `b₂ (m₂ x₂) = m₃ (a₂ x₂) = 0`, so `m₂ x₂ = b₁ (m₁ x₁) = m₂ (a₁ x₁)`, so `x₂ = a₁ x₁`.
  have h1 : b₂ (m₂ x₂) = 0 := by rw [← sq₂]; exact hx₃
  obtain ⟨y₁, hy₁⟩ := AddMonoidHom.mem_range.mp (hbot₂ _ h1)
  obtain ⟨x₁, rfl⟩ := hm₁ y₁
  have h2 : x₂ = a₁ x₁ := hm₂ (by rw [sq₁, hy₁])
  -- Hence `x₃ = a₂ (a₁ x₁) = 0` by top exactness at `A₂`.
  rw [h2]
  exact (htop₂ _).mpr (AddMonoidHom.mem_range.mpr ⟨x₁, rfl⟩)

end FourLemma

end GQ2.FoxH

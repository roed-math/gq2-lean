/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.Devissage.Chi1
public import GQ2.Devissage.SelfDual

@[expose] public section

/-!
# §5.11 dévissage on the `r_R` spine: word-internal self-duality

Mechanical R-spine clone of `GQ2/Devissage/SelfDual.lean` (campaign decision,
`docs/orchestration/roe-r20-recon.md`); proofs ported verbatim.  Spine renames `Z1w → Z1wR`, `H1w →
H1wR`, `H2w → H2wR`, `d1Fun → d1FunR`, `d1 → d1R`, `mixedB → mixedB_R`, `WildRel → WildRelR`,
`IsSelfDual(W) → IsSelfDual(W)_R`, with R-suffixed public names.  The generic four lemma
`four_lemma_inj` and `H0w_two_torsion` are reused from `GQ2.Devissage.*`, never cloned.
-/

namespace GQ2.FoxH

open scoped Pointwise

variable {C : Type*} [Group C]

/-! ## Word-internal self-duality

The marking-internal form of the `IsSelfDual_R` package: `#H⁰w(A^∨)` in place of
`#fixedPts C (A^∨)`.  For a *generating* marking (`t.Generates`) the two agree — `ker d⁰` is then
exactly the `C`-fixed points; `lemma_5_11_R`'s dévissage propagates the internal form, and the
`fixedPts`-form follows wherever generation is available. -/

section SelfDualW

variable {A : Type*} [AddCommGroup A] [DistribMulAction C A] [Finite A] [Finite C]

/-- **Word-internal self-duality** (the `IsSelfDual_R` package with the invariants of the dual
replaced by the word-complex `H⁰w` of the dual). -/
def IsSelfDualW_R (t : Marking C) (A : Type*) [AddCommGroup A] [DistribMulAction C A]
    [Finite A] : Prop :=
  (Nat.card (H2wR (A := A) t) = Nat.card (H0w (A := ElemDual A) t)) ∧
  (Nat.card (Z1wR (A := A) t) = Nat.card A ^ 2 * Nat.card (H0w (A := ElemDual A) t)) ∧
  ∃ P : H1wR (A := A) t → H1wR (A := ElemDual A) t → ZMod 2,
    (∀ (x : Z1wR (A := A) t) (y : Z1wR (A := ElemDual A) t),
        P (h1wMkR t x) (h1wMkR t y) = mixedB_R t x.val y.val) ∧
    (∀ h, h ≠ 0 → ∃ h', P h h' ≠ 0) ∧
    (∀ h', h' ≠ 0 → ∃ h, P h h' ≠ 0)

/-- `IsSelfDualW_R` in `χ`-language: `χ²` bijective and `χ¹`, `χ¹ᵀ` injective.  (The second card
clause is rank-nullity; the pairing clause is `pairing_clause_iff_R`.) -/
theorem isSelfDualW_iff_R (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (hA₂ : ∀ a : A, a + a = 0) :
    IsSelfDualW_R t A ↔
      (Function.Bijective (chi2_R (A := A) t ht hw) ∧
        Function.Injective (chi1_R (A := A) t ht hw) ∧
        Function.Injective (chi1T_R (A := A) t ht hw)) := by
  have : Finite (H2wR (A := A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have hED : Nat.card (ElemDual (H0w (A := ElemDual A) t))
      = Nat.card (H0w (A := ElemDual A) t) :=
    card_elemDual (A := H0w (A := ElemDual A) t)
      (H0w_two_torsion t ElemDual.add_self_eq_zero)
  constructor
  · rintro ⟨hc1, -, hpair⟩
    refine ⟨?_, (pairing_clause_iff_R t ht hw).mp hpair⟩
    rw [Nat.bijective_iff_surjective_and_card]
    exact ⟨chi2_surjective_R t ht hw hA₂, hc1.trans hED.symm⟩
  · rintro ⟨hbij, hinj, hinjT⟩
    have hc1 : Nat.card (H2wR (A := A) t) = Nat.card (H0w (A := ElemDual A) t) :=
      (Nat.card_eq_of_bijective _ hbij).trans hED
    exact ⟨hc1, by rw [card_Z1w_eq_sq_mul_card_H2w_R, hc1],
      (pairing_clause_iff_R t ht hw).mpr ⟨hinj, hinjT⟩⟩

/-- From a `IsSelfDualW_R`-package, **all six** `χ`-maps are bijective (the free halves plus the
Euler-characteristic swap `#H⁰w(A) = #H²w(A^∨)`). -/
theorem chi_bij_of_selfdualW_R (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (hA₂ : ∀ a : A, a + a = 0) (hsd : IsSelfDualW_R t A) :
    Function.Bijective (chi2_R (A := A) t ht hw) ∧
      Function.Bijective (chi2T_R (A := A) t ht hw) ∧
      Function.Bijective (chi0_R (A := A) t ht hw) ∧
      Function.Bijective (chi0T_R (A := A) t ht hw) ∧
      Function.Bijective (chi1_R (A := A) t ht hw) ∧
      Function.Bijective (chi1T_R (A := A) t ht hw) := by
  have : Finite (H1wR (A := A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H1wR (A := ElemDual A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2wR (A := A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have : Finite (H2wR (A := ElemDual A) t) := inferInstanceAs (Finite (_ ⧸ _))
  have hD₂ : ∀ lam : ElemDual A, lam + lam = 0 := ElemDual.add_self_eq_zero
  obtain ⟨hbij2, hinj1, hinj1T⟩ := (isSelfDualW_iff_R t ht hw hA₂).mp hsd
  obtain ⟨hbij1, hbij1T, h11⟩ := chi1_bij_of_inj_R t ht hw hA₂ hinj1 hinj1T
  -- The card package.
  have hc1 : Nat.card (H2wR (A := A) t) = Nat.card (H0w (A := ElemDual A) t) := hsd.1
  have hAD : Nat.card (ElemDual A) = Nat.card A := card_elemDual hA₂
  -- Euler swap: `#H⁰w(A) = #H²w(A^∨)`.
  have hswap : Nat.card (H0w (A := A) t) = Nat.card (H2wR (A := ElemDual A) t) := by
    have e1 := card_H1w_eq_R (A := A) t ht hw
    have e2 := card_H1w_eq_R (A := ElemDual A) t ht hw
    have hprod : Nat.card A * (Nat.card (H0w (A := A) t) * Nat.card (H2wR (A := A) t))
        = Nat.card A * (Nat.card (H0w (A := ElemDual A) t)
            * Nat.card (H2wR (A := ElemDual A) t)) := by
      calc Nat.card A * (Nat.card (H0w (A := A) t) * Nat.card (H2wR (A := A) t))
          = Nat.card (H1wR (A := A) t) := by rw [e1]; ring
        _ = Nat.card (H1wR (A := ElemDual A) t) := h11
        _ = Nat.card (ElemDual A) * (Nat.card (H0w (A := ElemDual A) t)
              * Nat.card (H2wR (A := ElemDual A) t)) := by rw [e2]; ring
        _ = Nat.card A * (Nat.card (H0w (A := ElemDual A) t)
              * Nat.card (H2wR (A := ElemDual A) t)) := by rw [hAD]
    have hcancel := Nat.eq_of_mul_eq_mul_left Nat.card_pos hprod
    rw [hc1, mul_comm] at hcancel
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hcancel
  -- The four evaluation bijectivities.
  refine ⟨hbij2, ?_, ?_, ?_, hbij1, hbij1T⟩
  · -- `χ²ᵀ : H²w(A^∨) → (H⁰w(A))^∨`: always surjective; cards by the swap.
    rw [Nat.bijective_iff_surjective_and_card]
    refine ⟨chi2T_surjective_R t ht hw hA₂, ?_⟩
    rw [hswap.symm, (card_elemDual (A := H0w (A := A) t) (H0w_two_torsion t hA₂)).symm]
  · -- `χ⁰ : H⁰w(A) → (H²w(A^∨))^∨`: always injective; cards by the swap.
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨chi0_injective_R t ht hw hA₂, ?_⟩
    rw [hswap, (card_elemDual (A := H2wR (A := ElemDual A) t)
      (H2w_two_torsion_R t hD₂)).symm]
  · -- `χ⁰ᵀ : H⁰w(A^∨) → (H²w(A))^∨`: always injective; cards by clause (i).
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨chi0T_injective_R t ht hw, ?_⟩
    rw [← hc1, (card_elemDual (A := H2wR (A := A) t) (H2w_two_torsion_R t hA₂)).symm]

end SelfDualW

/-! ## The four lemma (injectivity form)

The standard diagram chase, hand-rolled for `AddMonoidHom`s with pointwise exactness data — the
engine that turns the ladder squares into the conditional halves of the `χ`-bijectivities. -/

section FourLemma

variable {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type*}
  [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃] [AddCommGroup A₄]
  [AddCommGroup B₁] [AddCommGroup B₂] [AddCommGroup B₃] [AddCommGroup B₄]

end FourLemma

end GQ2.FoxH

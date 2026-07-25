/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.Devissage
public import GQ2.Roe.TrivialSelfDual
public import GQ2.DevissageInduction

@[expose] public section

/-!
# The dévissage induction on the `r_R` spine: `prop_5_15_R` from the simple case

Mechanical R-spine clone of `GQ2/DevissageInduction.lean` (campaign decision,
`docs/orchestration/roe-r20-recon.md`).  `prop_5_15_of_simple_R`: if `IsSelfDual_R t B` holds for
every **simple** finite elementary-2 `C`-module `B`, then it holds for every finite elementary-2
`C`-module `A`.  Strong induction on `Nat.card A`; the induction step forwards `hw : t.WildRelR`
to `lemma_5_11_R` along `0 → W → A → A ⧸ W → 0`, and the subsingleton (zero-module) base case is
R25's `trivialSelfDual_R` (`GQ2/Roe/TrivialSelfDual.lean`) — exactly as the `Γ_A` capstone uses
`trivialSelfDual`.  Proof ported **verbatim**.

The self-duality predicate `IsSelfDual_R` and the base case `trivialSelfDual_R` are R25's
(`GQ2/Roe/TrivialSelfDual.lean`), reused here per the campaign convention (recon §1.5); the
reusable induction infrastructure `stableSubAction`/`stableQuotAction`/`two_torsion_sub`/
`two_torsion_quot`/`card_lt_of_ne_top`/`card_quot_lt_of_ne_bot` (all `(A)`-generic, word-free) is
reused from `GQ2.DevissageInduction`, never cloned.
-/

namespace GQ2

namespace FoxH

universe u

variable {C : Type*} [Group C] [Finite C]

/-- **Prop 5.15, dévissage half (the Prop. 5.15 proof), on the `r_R` spine**: `IsSelfDual_R` for
*all* finite elementary-2 `C`-modules, parameterized over the simple case (`hsimp`).  R-spine clone
of `prop_5_15_of_simple`; proof ported verbatim.  The induction step is `lemma_5_11_R` along
`0 → W → A → A ⧸ W → 0` for a `C`-stable `W ∉ {⊥, ⊤}`; the subsingleton base is R25's
`trivialSelfDual_R`. -/
theorem prop_5_15_of_simple_R (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (hgen : t.Generates)
    (hsimp : ∀ (B : Type u) [AddCommGroup B] [DistribMulAction C B] [Finite B],
      (∀ b : B, b + b = 0) → IsSimpleModTwo C B → IsSelfDual_R t B)
    {A : Type u} [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) : IsSelfDual_R t A := by
  suffices h : ∀ (n : ℕ) (A : Type u) [AddCommGroup A] [DistribMulAction C A] [Finite A],
      Nat.card A = n → (∀ a : A, a + a = 0) → IsSelfDual_R t A by
    exact h (Nat.card A) A rfl hA₂
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro A instAdd instAct instFin hcard hA₂
    rcases subsingleton_or_nontrivial A with hsub | hnt
    · -- zero module: the action is trivial (R25's `trivialSelfDual_R`)
      exact trivialSelfDual_R t ht hw (fun _ _ => Subsingleton.elim _ _) hA₂
    · by_cases hsimple : IsSimpleModTwo C A
      · exact hsimp A hA₂ hsimple
      · -- extract a proper nonzero `C`-stable subgroup
        rw [IsSimpleModTwo] at hsimple
        push Not at hsimple
        obtain ⟨W, hWstable, hWbot, hWtop⟩ := hsimple hnt
        -- transported actions
        letI := stableSubAction W hWstable
        letI := stableQuotAction W hWstable
        -- char-2 on the subquotients
        have hW₂ : ∀ w : ↥W, w + w = 0 := two_torsion_sub W hA₂
        have hQ₂ : ∀ q : A ⧸ W, q + q = 0 := two_torsion_quot W hA₂
        -- strict cardinality drops
        have hltW : Nat.card ↥W < n := hcard ▸ card_lt_of_ne_top W hWtop
        have hltQ : Nat.card (A ⧸ W) < n := hcard ▸ card_quot_lt_of_ne_bot W hWbot
        -- inductive hypotheses on the ends
        have ihW : IsSelfDual_R t ↥W := IH _ hltW ↥W rfl hW₂
        have ihQ : IsSelfDual_R t (A ⧸ W) := IH _ hltQ (A ⧸ W) rfl hQ₂
        -- dévissage (the dévissage proof) along `0 → W → A → A ⧸ W → 0`
        exact (lemma_5_11_R t ht hw hgen hA₂ W.subtype (QuotientAddGroup.mk' W)
          (stableSubAction_subtype_equivariant W hWstable)
          (stableQuotAction_mk'_equivariant W hWstable)
          (AddSubgroup.subtype_injective W)
          (QuotientAddGroup.mk'_surjective W)
          (subtype_range_eq_mk'_ker W)).1 ⟨ihW, ihQ⟩

end FoxH

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * Prop 5.15 (dévissage half) = ⟦prop:duality⟧ — `prop_5_15_of_simple_R` is the source-generic
    reduction of self-duality to the simple case; R26b's `selfDual_of_simple_R` /
    `prop_5_15_R` (`GQ2/Roe/DualityAssembly.lean`) feed the simple case.
-/

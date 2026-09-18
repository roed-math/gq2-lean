/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Word.GeneralTemplate
import GQ2.Dyadic.Instances.OmegaPinnedLevelResolver

/-!
# Integer and finite evaluation of the same staged tree

The evaluator takes integer representatives of typed exponent expressions.
It does not attempt to compute arbitrary two-adic parameters. With the exact
Lean environment and the campaign's pinned finite resolver, it agrees with
the profinite denotation at every finite target and every valid common level.
-/

namespace GQ2.Dyadic.GeneralTemplate

open GQ2

/-- Direct integer evaluation of the staged syntax, with the same right-conjugation
and commutator conventions as `PWord.evalZ`. -/
def Tree.evalZ {Gen G : Type*} [Group G] (mu : Gen → G)
    (E : ProfiniteTerm → ℤ) (E₂ : PadicTerm → ℤ) : Tree Gen → G
  | .one => 1
  | .gen g => mu g
  | .mul u v => u.evalZ mu E E₂ * v.evalZ mu E E₂
  | .inv u => (u.evalZ mu E E₂)⁻¹
  | .conj u v => conjR (u.evalZ mu E E₂) (v.evalZ mu E E₂)
  | .comm u v => commR (u.evalZ mu E E₂) (v.evalZ mu E E₂)
  | .zpow u k => u.evalZ mu E E₂ ^ k
  | .z2pow u k => u.evalZ mu E E₂ ^ E₂ k
  | .profPow u k => u.evalZ mu E E₂ ^ E k

/-- Resolving after exact symbolic binding is exactly the existing integer evaluator. -/
theorem Tree.evalZ_eq_denote {Gen G : Type*} [Group G] (env : Environment)
    (mu : Gen → G) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (w : Tree Gen) :
    w.evalZ mu (fun e => E (e.denote env)) (fun e => E₂ (e.denote env)) =
      PWord.evalZ mu E E₂ (w.denote env) := by
  induction w <;> simp_all [Tree.evalZ, Tree.denote]

/-- Finite agreement, uniform in every symbolic parameter and without numerical
approximation: the common level must kill all elements of the target group. -/
theorem Tree.eval_eq_pinned {Gen Q : Type} [Group Q] [TopologicalSpace Q]
    [DiscreteTopology Q] [Finite Q] {N : ℕ} (hN : N ≠ 0)
    (hord : ∀ x : Q, orderOf x ∣ N) (env : Environment) (mu : Gen → Q) (w : Tree Gen) :
    PWord.eval mu (w.denote env) = w.evalZ mu
      (fun e => omegaPinnedLevelZhatResolver N (e.denote env))
      (fun e => omegaPinnedLevelZtwoResolver N (e.denote env)) := by
  rw [Tree.evalZ_eq_denote]
  exact PWord.eval_eq_evalZ mu _ _ _
    (resolvedAt_omegaPinnedLevelResolvers hN hord mu (w.denote env))

#print axioms Tree.evalZ
#print axioms Tree.evalZ_eq_denote
#print axioms Tree.eval_eq_pinned

end GQ2.Dyadic.GeneralTemplate

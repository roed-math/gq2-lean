/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3CompletedAugmentationPowers

/-!
# The low-degree lower-two-central to augmentation map

This file starts the actual Jennings comparison, rather than packaging it as an interface.
For an ordinary finite group algebra over `F₂`, it proves the easy inclusion

`g ∈ λₙ(Q)  →  [g] - 1 ∈ I(Q)^n`.

The proof follows the defining recursion of the lower `2`-central series.  Squares raise
augmentation order because `([g]-1)^2 = [g²]-1` in characteristic two, while commutators
raise it by multiplying the degree-`n` and degree-one differences.  Finiteness is used only
to pass through the topological closure in the repository's definition of `λₙ`.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2.Roe.Labute
open scoped commutatorElement

universe u

variable (Q : Type u) [Group Q]

/-- The group-like difference `[q]-1` in the ordinary mod-two group algebra. -/
def modTwoFiniteGroupDifference (q : Q) : MonoidAlgebra (ZMod 2) Q :=
  MonoidAlgebra.of (ZMod 2) Q q - 1

@[simp] theorem modTwoFiniteGroupDifference_one :
    modTwoFiniteGroupDifference Q 1 = 0 := by
  rw [modTwoFiniteGroupDifference, map_one]
  exact sub_self 1

/-- Product rule for group-like differences. -/
theorem modTwoFiniteGroupDifference_mul (a b : Q) :
    modTwoFiniteGroupDifference Q (a * b) =
      MonoidAlgebra.of (ZMod 2) Q a * modTwoFiniteGroupDifference Q b +
        modTwoFiniteGroupDifference Q a := by
  simp only [modTwoFiniteGroupDifference, map_mul]
  noncomm_ring

/-- Inverse rule for group-like differences. -/
theorem modTwoFiniteGroupDifference_inv (a : Q) :
    modTwoFiniteGroupDifference Q a⁻¹ =
      -MonoidAlgebra.of (ZMod 2) Q a⁻¹ * modTwoFiniteGroupDifference Q a := by
  simp only [modTwoFiniteGroupDifference]
  have hunit : MonoidAlgebra.of (ZMod 2) Q a⁻¹ *
      MonoidAlgebra.of (ZMod 2) Q a = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  calc
    MonoidAlgebra.of (ZMod 2) Q a⁻¹ - 1 =
        MonoidAlgebra.of (ZMod 2) Q a⁻¹ -
          MonoidAlgebra.of (ZMod 2) Q a⁻¹ *
            MonoidAlgebra.of (ZMod 2) Q a := by rw [hunit]
    _ = -MonoidAlgebra.of (ZMod 2) Q a⁻¹ *
        (MonoidAlgebra.of (ZMod 2) Q a - 1) := by noncomm_ring

/-- Every group-like difference lies in the finite augmentation ideal. -/
theorem modTwoFiniteGroupDifference_mem_augmentation (q : Q) :
    modTwoFiniteGroupDifference Q q ∈ modTwoFiniteAugmentationIdeal Q := by
  simpa [modTwoFiniteGroupDifference] using
    modTwoFiniteAugmentationIdeal_single_sub_one Q q

/-- The `n`th mod-two dimension subgroup, defined by augmentation order. -/
def modTwoFiniteDimensionSubgroup (n : ℕ) : Subgroup Q where
  carrier := {q | modTwoFiniteGroupDifference Q q ∈
    modTwoFiniteAugmentationIdeal Q ^ n}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change modTwoFiniteGroupDifference Q (a * b) ∈
      modTwoFiniteAugmentationIdeal Q ^ n
    rw [modTwoFiniteGroupDifference_mul]
    exact (modTwoFiniteAugmentationIdeal Q ^ n).add_mem
      ((modTwoFiniteAugmentationIdeal Q ^ n).mul_mem_left _ hb) ha
  inv_mem' := by
    intro a ha
    change modTwoFiniteGroupDifference Q a⁻¹ ∈
      modTwoFiniteAugmentationIdeal Q ^ n
    rw [modTwoFiniteGroupDifference_inv]
    exact (modTwoFiniteAugmentationIdeal Q ^ n).mul_mem_left _ ha

@[simp] theorem mem_modTwoFiniteDimensionSubgroup {n : ℕ} {q : Q} :
    q ∈ modTwoFiniteDimensionSubgroup Q n ↔
      modTwoFiniteGroupDifference Q q ∈ modTwoFiniteAugmentationIdeal Q ^ n :=
  Iff.rfl

/-- In characteristic two, squaring a group-like element squares its difference. -/
theorem modTwoFiniteGroupDifference_sq (q : Q) :
    modTwoFiniteGroupDifference Q (q ^ 2) =
      modTwoFiniteGroupDifference Q q * modTwoFiniteGroupDifference Q q := by
  let A := MonoidAlgebra (ZMod 2) Q
  have hdouble (x : A) : x + x = 0 := by
    ext a
    exact CharTwo.add_self_eq_zero (x a)
  have hneg (x : A) : -x = x := by
    ext a
    exact CharTwo.neg_eq (x a)
  simp only [modTwoFiniteGroupDifference, pow_two, map_mul, sub_eq_add_neg, hneg]
  let x := MonoidAlgebra.of (ZMod 2) Q q
  change x * x + 1 = (x + 1) * (x + 1)
  symm
  calc
    (x + 1) * (x + 1) = x * x + x + (x + 1) := by
      rw [add_mul, mul_add, mul_one, one_mul]
    _ = x * x + (x + x) + 1 := by abel
    _ = x * x + 1 := by rw [hdouble, add_zero]

/-- A square of an `n`th dimension-subgroup element has augmentation order `n+1`. -/
theorem modTwoFiniteGroupDifference_sq_mem_succ {n : ℕ} (hn : 1 ≤ n)
    {q : Q} (hq : q ∈ modTwoFiniteDimensionSubgroup Q n) :
    modTwoFiniteGroupDifference Q (q ^ 2) ∈
      modTwoFiniteAugmentationIdeal Q ^ (n + 1) := by
  rw [modTwoFiniteGroupDifference_sq, Submodule.pow_succ]
  exact Ideal.mul_mem_mul hq (modTwoFiniteGroupDifference_mem_augmentation Q q)

/-- The difference of a group commutator is the degree-`(n,1)` commutator of differences,
up to multiplication by group-like units on the right. -/
theorem modTwoFiniteGroupDifference_commutator (a b : Q) :
    modTwoFiniteGroupDifference Q ⁅a, b⁆ =
      (modTwoFiniteGroupDifference Q a * modTwoFiniteGroupDifference Q b -
          modTwoFiniteGroupDifference Q b * modTwoFiniteGroupDifference Q a) *
        MonoidAlgebra.of (ZMod 2) Q a⁻¹ *
          MonoidAlgebra.of (ZMod 2) Q b⁻¹ := by
  simp only [modTwoFiniteGroupDifference, commutatorElement_def, map_mul]
  let A := MonoidAlgebra.of (ZMod 2) Q a
  let B := MonoidAlgebra.of (ZMod 2) Q b
  let Ai := MonoidAlgebra.of (ZMod 2) Q a⁻¹
  let Bi := MonoidAlgebra.of (ZMod 2) Q b⁻¹
  have ha : MonoidAlgebra.of (ZMod 2) Q a *
      MonoidAlgebra.of (ZMod 2) Q a⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hb : MonoidAlgebra.of (ZMod 2) Q b *
      MonoidAlgebra.of (ZMod 2) Q b⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  change A * B * Ai * Bi - 1 = ((A - 1) * (B - 1) - (B - 1) * (A - 1)) * Ai * Bi
  have hreduce : (A * B - B * A) * Ai * Bi = A * B * Ai * Bi - 1 := by
    rw [sub_mul, sub_mul]
    simp only [mul_assoc]
    rw [← mul_assoc A Ai Bi, show A * Ai = 1 from ha, one_mul,
      show B * Bi = 1 from hb]
  rw [← hreduce]
  congr 2
  noncomm_ring

/-- A commutator with an `n`th dimension-subgroup element has augmentation order `n+1`. -/
theorem modTwoFiniteGroupDifference_commutator_mem_succ {n : ℕ} (hn : 1 ≤ n)
    {a : Q} (ha : a ∈ modTwoFiniteDimensionSubgroup Q n) (b : Q) :
    modTwoFiniteGroupDifference Q ⁅a, b⁆ ∈
      modTwoFiniteAugmentationIdeal Q ^ (n + 1) := by
  letI : (modTwoFiniteAugmentationIdeal Q).IsTwoSided := by
    unfold modTwoFiniteAugmentationIdeal
    infer_instance
  let I := modTwoFiniteAugmentationIdeal Q
  have hb : modTwoFiniteGroupDifference Q b ∈ I :=
    modTwoFiniteGroupDifference_mem_augmentation Q b
  have hab : modTwoFiniteGroupDifference Q a * modTwoFiniteGroupDifference Q b ∈
      I ^ (n + 1) := by
    rw [Submodule.pow_succ]
    exact Ideal.mul_mem_mul ha hb
  have hba : modTwoFiniteGroupDifference Q b * modTwoFiniteGroupDifference Q a ∈
      I ^ (n + 1) := by
    rw [I.pow_succ' (by omega : n ≠ 0)]
    exact Ideal.mul_mem_mul hb ha
  rw [modTwoFiniteGroupDifference_commutator]
  exact (I ^ (n + 1)).mul_mem_right _
    ((I ^ (n + 1)).mul_mem_right _ ((I ^ (n + 1)).sub_mem hab hba))

section Finite

variable [TopologicalSpace Q] [IsTopologicalGroup Q] [T1Space Q] [Finite Q]

/-- In a finite topological group every mod-two dimension subgroup is closed. -/
theorem isClosed_modTwoFiniteDimensionSubgroup (n : ℕ) :
    IsClosed ((modTwoFiniteDimensionSubgroup Q n : Subgroup Q) : Set Q) :=
  Set.toFinite _ |>.isClosed

/-- **Easy half of Jennings in every degree for finite groups.**  The lower two-central
series is contained in the mod-two dimension filtration. -/
theorem twoCentralSeries_le_modTwoFiniteDimensionSubgroup (n : ℕ) :
    twoCentralSeries Q n ≤ modTwoFiniteDimensionSubgroup Q n := by
  induction n with
  | zero =>
      intro q hq
      rw [mem_modTwoFiniteDimensionSubgroup, Submodule.pow_zero, Ideal.one_eq_top]
      exact Set.mem_univ _
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        intro q hq
        rw [mem_modTwoFiniteDimensionSubgroup, Submodule.pow_one]
        exact modTwoFiniteGroupDifference_mem_augmentation Q q
      · rw [twoCentralSeries_succ Q (by omega), twoCentralSucc]
        refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_)
          (isClosed_modTwoFiniteDimensionSubgroup Q (n + 1))
        · rw [Subgroup.closure_le]
          rintro _ ⟨q, hq, rfl⟩
          exact modTwoFiniteGroupDifference_sq_mem_succ Q (by omega) (ih hq)
        · rw [Subgroup.commutator_le]
          intro a ha b hb
          exact modTwoFiniteGroupDifference_commutator_mem_succ Q (by omega) (ih ha) b

end Finite

end

end GQ2.ContCoh

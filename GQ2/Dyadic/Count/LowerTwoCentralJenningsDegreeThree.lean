/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3CompletedAugmentationPowers
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldCore
import GQ2.Roe.Labute.SpanFoundation

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

open GQ2.Roe GQ2.Roe.Labute
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

/-- Squaring doubles augmentation order.  The weaker successor bound above is the one needed
for the easy lower-two-central containment, but the exact doubled bound is essential in degree
three: squares of second-layer elements already vanish modulo `I^4`. -/
theorem modTwoFiniteGroupDifference_sq_mem_double {n : ℕ} (hn : n ≠ 0)
    {q : Q} (hq : q ∈ modTwoFiniteDimensionSubgroup Q n) :
    modTwoFiniteGroupDifference Q (q ^ 2) ∈
      modTwoFiniteAugmentationIdeal Q ^ (n + n) := by
  rw [modTwoFiniteGroupDifference_sq,
    Submodule.pow_add (modTwoFiniteAugmentationIdeal Q) hn]
  exact Ideal.mul_mem_mul hq hq

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

/-! ## The actual finite augmentation layer and its dimension-subgroup map -/

/-- The additive quotient of the finite group algebra modulo `I^(n+1)`. -/
abbrev ModTwoFiniteAugmentationTruncation (n : ℕ) :=
  MonoidAlgebra (ZMod 2) Q ⧸
    (modTwoFiniteAugmentationIdeal Q ^ (n + 1)).toAddSubgroup

/-- The actual augmentation layer `I^n/I^(n+1)`, represented as the image of `I^n` in the
additive quotient of the whole finite group algebra by `I^(n+1)`. -/
def modTwoFiniteAugmentationLayer (n : ℕ) :
    AddSubgroup (ModTwoFiniteAugmentationTruncation Q n) :=
  AddSubgroup.map
    (QuotientAddGroup.mk'
      (modTwoFiniteAugmentationIdeal Q ^ (n + 1)).toAddSubgroup)
    (modTwoFiniteAugmentationIdeal Q ^ n).toAddSubgroup

/-- The group-like difference of an `n`th dimension-subgroup element, viewed in the actual
augmentation layer `I^n/I^(n+1)`. -/
def modTwoFiniteDimensionToAugmentationLayer (n : ℕ) (hn : 1 ≤ n) :
    Additive (modTwoFiniteDimensionSubgroup Q n) →+
      modTwoFiniteAugmentationLayer Q n where
  toFun q := ⟨QuotientAddGroup.mk'
      (modTwoFiniteAugmentationIdeal Q ^ (n + 1)).toAddSubgroup
      (modTwoFiniteGroupDifference Q q.toMul.1),
    ⟨modTwoFiniteGroupDifference Q q.toMul.1, q.toMul.2, rfl⟩⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' := by
    intro a b
    apply Subtype.ext
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    change modTwoFiniteGroupDifference Q (a.toMul.1 * b.toMul.1) -
        (modTwoFiniteGroupDifference Q a.toMul.1 +
          modTwoFiniteGroupDifference Q b.toMul.1) ∈
      (modTwoFiniteAugmentationIdeal Q ^ (n + 1)).toAddSubgroup
    have hdiff : modTwoFiniteGroupDifference Q (a.toMul.1 * b.toMul.1) -
          (modTwoFiniteGroupDifference Q a.toMul.1 +
            modTwoFiniteGroupDifference Q b.toMul.1) =
        modTwoFiniteGroupDifference Q a.toMul.1 *
          modTwoFiniteGroupDifference Q b.toMul.1 := by
      rw [modTwoFiniteGroupDifference_mul]
      unfold modTwoFiniteGroupDifference
      noncomm_ring
    rw [hdiff]
    change modTwoFiniteGroupDifference Q a.toMul.1 *
        modTwoFiniteGroupDifference Q b.toMul.1 ∈
      modTwoFiniteAugmentationIdeal Q ^ (n + 1)
    rw [Submodule.pow_succ]
    exact Ideal.mul_mem_mul a.toMul.2
      (modTwoFiniteGroupDifference_mem_augmentation Q b.toMul.1)

/-- The dimension-subgroup map vanishes exactly one augmentation step deeper.  Thus its
injectivity after quotienting is precisely the reverse Jennings containment. -/
theorem modTwoFiniteDimensionToAugmentationLayer_eq_zero_iff
    (n : ℕ) (hn : 1 ≤ n) (q : Additive (modTwoFiniteDimensionSubgroup Q n)) :
    modTwoFiniteDimensionToAugmentationLayer Q n hn q = 0 ↔
      q.toMul.1 ∈ modTwoFiniteDimensionSubgroup Q (n + 1) := by
  constructor
  · intro hq
    have hval := congrArg Subtype.val hq
    change QuotientAddGroup.mk'
        (modTwoFiniteAugmentationIdeal Q ^ (n + 1)).toAddSubgroup
        (modTwoFiniteGroupDifference Q q.toMul.1) = 0 at hval
    exact (QuotientAddGroup.eq_zero_iff _).mp hval
  · intro hq
    apply Subtype.ext
    change QuotientAddGroup.mk'
        (modTwoFiniteAugmentationIdeal Q ^ (n + 1)).toAddSubgroup
        (modTwoFiniteGroupDifference Q q.toMul.1) = 0
    exact (QuotientAddGroup.eq_zero_iff _).mpr hq

/-- Two dimension-subgroup elements have the same augmentation-layer class whenever their
quotient lies one step deeper.  This is the choice-independence lemma used for layer lifts. -/
theorem modTwoFiniteDimensionToAugmentationLayer_eq_of_mul_inv_mem_succ
    (n : ℕ) (hn : 1 ≤ n)
    (a b : modTwoFiniteDimensionSubgroup Q n)
    (hab : a.1 * b.1⁻¹ ∈ modTwoFiniteDimensionSubgroup Q (n + 1)) :
    modTwoFiniteDimensionToAugmentationLayer Q n hn (Additive.ofMul a) =
      modTwoFiniteDimensionToAugmentationLayer Q n hn (Additive.ofMul b) := by
  apply sub_eq_zero.mp
  rw [← map_sub,
    modTwoFiniteDimensionToAugmentationLayer_eq_zero_iff Q n hn]
  rw [toMul_sub]
  simpa only [toMul_ofMul, div_eq_mul_inv, Subgroup.coe_mul,
    Subgroup.coe_inv] using hab

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

/-! ## The first three `DSq` layers inside the finite fourth quotient -/

open GQ2.Dyadic.SqCore
open GQ2.Dyadic.LSquare

/-- The finite fourth lower-two-central quotient of the improved square presentation. -/
abbrev SqFourthLevel (h : ℕ) := levelQuot (DSq h : Type) 4

/-- Choose a representative in `λₙ(DSq h)` for a class in `Zₙ = λₙ/λₙ₊₁`. -/
noncomputable def dsqZLayerRepresentative (h n : ℕ)
    (z : zLayer (DSq h : Type) n) : (DSq h : Type) :=
  Classical.choose z.2

theorem dsqZLayerRepresentative_mem (h n : ℕ)
    (z : zLayer (DSq h : Type) n) :
    dsqZLayerRepresentative h n z ∈ twoCentralSeries (DSq h : Type) n :=
  (Classical.choose_spec z.2).1

theorem levelMk_dsqZLayerRepresentative (h n : ℕ)
    (z : zLayer (DSq h : Type) n) :
    levelMk (DSq h : Type) (n + 1) (dsqZLayerRepresentative h n z) = z.1 :=
  (Classical.choose_spec z.2).2

/-- Lift a lower-two-central class to the common finite quotient `Q₄`. -/
noncomputable def dsqZLayerFourthLift (h n : ℕ)
    (z : zLayer (DSq h : Type) n) : SqFourthLevel h :=
  levelMk (DSq h : Type) 4 (dsqZLayerRepresentative h n z)

/-- A lifted `Zₙ` class lies in `λₙ(Q₄)`. -/
theorem dsqZLayerFourthLift_mem_twoCentral (h n : ℕ)
    (z : zLayer (DSq h : Type) n) :
    dsqZLayerFourthLift h n z ∈ twoCentralSeries (SqFourthLevel h) n := by
  letI : DiscreteTopology (SqFourthLevel h) :=
    discreteTopology_levelQuot (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) 4
  rw [← lambdaImage_eq_twoCentralSeries_levelQuot
    (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) n 4]
  exact ⟨dsqZLayerRepresentative h n z, dsqZLayerRepresentative_mem h n z, rfl⟩

/-- Hence a lifted `Zₙ` class has augmentation order at least `n` in `F₂[Q₄]`. -/
theorem dsqZLayerFourthLift_mem_dimension (h n : ℕ)
    (z : zLayer (DSq h : Type) n) :
    dsqZLayerFourthLift h n z ∈
      modTwoFiniteDimensionSubgroup (SqFourthLevel h) n := by
  letI : DiscreteTopology (SqFourthLevel h) :=
    discreteTopology_levelQuot (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) 4
  letI : Finite (SqFourthLevel h) :=
    finite_levelQuot (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) 4
  exact twoCentralSeries_le_modTwoFiniteDimensionSubgroup (SqFourthLevel h) n
    (dsqZLayerFourthLift_mem_twoCentral h n z)

/-- The lifted class, bundled in the `n`th dimension subgroup of `Q₄`. -/
noncomputable def dsqZLayerFourthDimensionLift (h n : ℕ)
    (z : zLayer (DSq h : Type) n) :
    modTwoFiniteDimensionSubgroup (SqFourthLevel h) n :=
  ⟨dsqZLayerFourthLift h n z, dsqZLayerFourthLift_mem_dimension h n z⟩

/-- The chosen representative of the identity class is one lower-two-central step deeper. -/
theorem dsqZLayerRepresentative_one_mem_succ (h n : ℕ) :
    dsqZLayerRepresentative h n (1 : zLayer (DSq h : Type) n) ∈
      twoCentralSeries (DSq h : Type) (n + 1) := by
  rw [← QuotientGroup.eq_one_iff]
  exact levelMk_dsqZLayerRepresentative h n 1

/-- The multiplicative defect of the chosen representatives is one layer deeper. -/
theorem dsqZLayerRepresentative_mul_defect_mem_succ (h n : ℕ)
    (z w : zLayer (DSq h : Type) n) :
    dsqZLayerRepresentative h n (z * w) *
        (dsqZLayerRepresentative h n z * dsqZLayerRepresentative h n w)⁻¹ ∈
      twoCentralSeries (DSq h : Type) (n + 1) := by
  rw [← QuotientGroup.eq_one_iff]
  change levelMk (DSq h : Type) (n + 1)
    (dsqZLayerRepresentative h n (z * w) *
      (dsqZLayerRepresentative h n z * dsqZLayerRepresentative h n w)⁻¹) = 1
  rw [map_mul, map_inv, map_mul,
    levelMk_dsqZLayerRepresentative, levelMk_dsqZLayerRepresentative,
    levelMk_dsqZLayerRepresentative]
  exact mul_inv_cancel (z.1 * w.1)

/-- The identity lift dies in the next dimension subgroup of `Q₄`. -/
theorem dsqZLayerFourthLift_one_mem_dimension_succ (h n : ℕ) :
    dsqZLayerFourthLift h n (1 : zLayer (DSq h : Type) n) ∈
      modTwoFiniteDimensionSubgroup (SqFourthLevel h) (n + 1) := by
  letI : DiscreteTopology (SqFourthLevel h) :=
    discreteTopology_levelQuot (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) 4
  letI : Finite (SqFourthLevel h) :=
    finite_levelQuot (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) 4
  apply twoCentralSeries_le_modTwoFiniteDimensionSubgroup (SqFourthLevel h) (n + 1)
  rw [← lambdaImage_eq_twoCentralSeries_levelQuot
    (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) (n + 1) 4]
  exact ⟨dsqZLayerRepresentative h n 1,
    dsqZLayerRepresentative_one_mem_succ h n, rfl⟩

/-- The multiplicative defect of fourth-level lifts dies in the next dimension subgroup. -/
theorem dsqZLayerFourthLift_mul_defect_mem_dimension_succ (h n : ℕ)
    (z w : zLayer (DSq h : Type) n) :
    dsqZLayerFourthLift h n (z * w) *
        (dsqZLayerFourthLift h n z * dsqZLayerFourthLift h n w)⁻¹ ∈
      modTwoFiniteDimensionSubgroup (SqFourthLevel h) (n + 1) := by
  letI : DiscreteTopology (SqFourthLevel h) :=
    discreteTopology_levelQuot (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) 4
  letI : Finite (SqFourthLevel h) :=
    finite_levelQuot (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) 4
  apply twoCentralSeries_le_modTwoFiniteDimensionSubgroup (SqFourthLevel h) (n + 1)
  rw [← lambdaImage_eq_twoCentralSeries_levelQuot
    (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) (n + 1) 4]
  exact ⟨dsqZLayerRepresentative h n (z * w) *
      (dsqZLayerRepresentative h n z * dsqZLayerRepresentative h n w)⁻¹,
    dsqZLayerRepresentative_mul_defect_mem_succ h n z w, by
      simp only [dsqZLayerFourthLift, map_mul, map_inv]⟩

/-- The induced `g ↦ [g]-1` homomorphism from `Zₙ(DSq h)` to the common finite
augmentation layer `I(Q₄)^n/I(Q₄)^(n+1)`. -/
noncomputable def dsqZLayerToFourthAugmentationLayer (h n : ℕ) (hn : 1 ≤ n) :
    Additive (zLayer (DSq h : Type) n) →+
      modTwoFiniteAugmentationLayer (SqFourthLevel h) n where
  toFun z := modTwoFiniteDimensionToAugmentationLayer (SqFourthLevel h) n hn
    (Additive.ofMul (dsqZLayerFourthDimensionLift h n z.toMul))
  map_zero' := by
    apply (modTwoFiniteDimensionToAugmentationLayer_eq_zero_iff
      (SqFourthLevel h) n hn _).2
    exact dsqZLayerFourthLift_one_mem_dimension_succ h n
  map_add' := by
    intro z w
    let a := dsqZLayerFourthDimensionLift h n z.toMul
    let b := dsqZLayerFourthDimensionLift h n w.toMul
    let c := dsqZLayerFourthDimensionLift h n (z + w).toMul
    have hdef : c.1 * (a * b).1⁻¹ ∈
        modTwoFiniteDimensionSubgroup (SqFourthLevel h) (n + 1) := by
      exact dsqZLayerFourthLift_mul_defect_mem_dimension_succ h n z.toMul w.toMul
    calc
      modTwoFiniteDimensionToAugmentationLayer (SqFourthLevel h) n hn
          (Additive.ofMul c) =
          modTwoFiniteDimensionToAugmentationLayer (SqFourthLevel h) n hn
            (Additive.ofMul (a * b)) :=
        modTwoFiniteDimensionToAugmentationLayer_eq_of_mul_inv_mem_succ
          (SqFourthLevel h) n hn c (a * b) hdef
      _ = modTwoFiniteDimensionToAugmentationLayer (SqFourthLevel h) n hn
            (Additive.ofMul a) +
          modTwoFiniteDimensionToAugmentationLayer (SqFourthLevel h) n hn
            (Additive.ofMul b) := by rw [ofMul_mul, map_add]

/-- Degree-one contribution to the third-order finite Jennings calculation. -/
noncomputable def dsqZLayerOneToFourthAugmentationLayer (h : ℕ) :=
  dsqZLayerToFourthAugmentationLayer h 1 (by omega)

/-- Degree-two contribution to the third-order finite Jennings calculation. -/
noncomputable def dsqZLayerTwoToFourthAugmentationLayer (h : ℕ) :=
  dsqZLayerToFourthAugmentationLayer h 2 (by omega)

/-- Degree-three primitive contribution to the third-order finite Jennings calculation. -/
noncomputable def dsqZLayerThreeToFourthAugmentationLayer (h : ℕ) :=
  dsqZLayerToFourthAugmentationLayer h 3 (by omega)

/-- Kernel formula for the induced layer map.  Proving its right side forces `z=0` is exactly
the reverse dimension-subgroup containment still needed for injectivity. -/
theorem dsqZLayerToFourthAugmentationLayer_eq_zero_iff
    (h n : ℕ) (hn : 1 ≤ n) (z : Additive (zLayer (DSq h : Type) n)) :
    dsqZLayerToFourthAugmentationLayer h n hn z = 0 ↔
      dsqZLayerFourthLift h n z.toMul ∈
        modTwoFiniteDimensionSubgroup (SqFourthLevel h) (n + 1) :=
  modTwoFiniteDimensionToAugmentationLayer_eq_zero_iff
    (SqFourthLevel h) n hn (Additive.ofMul (dsqZLayerFourthDimensionLift h n z.toMul))

/-! ## The degree-three filtration mismatch

The lower exponent-two series used by `zLayer` assigns weight three to a square from
`lambda_2`.  The augmentation filtration assigns that square order at least four.  Thus the
degree-three map above necessarily kills the whole square contribution from `Z_2`; it is not
the primitive-layer injection required by the Zassenhaus Jennings formula. -/

/-- The square of a chosen representative of a second lower-two-central layer class, viewed in
the third layer. -/
noncomputable def dsqZLayerTwoSquareToThree (h : ℕ)
    (z : zLayer (DSq h : Type) 2) : zLayer (DSq h : Type) 3 :=
  ⟨levelMk (DSq h : Type) 4 (dsqZLayerRepresentative h 2 z ^ 2),
    ⟨dsqZLayerRepresentative h 2 z ^ 2,
      sq_mem_twoCentralSeries_succ (DSq h : Type)
        (dsqZLayerRepresentative_mem h 2 z), rfl⟩⟩

/-- In degree three the common fourth-level lift is literally the underlying layer value. -/
theorem dsqZLayerFourthLift_three_eq_val (h : ℕ)
    (z : zLayer (DSq h : Type) 3) :
    dsqZLayerFourthLift h 3 z = z.1 := by
  exact levelMk_dsqZLayerRepresentative h 3 z

/-- Every square coming from `Z_2` is killed by the proposed degree-three augmentation-layer
map: its group-like difference has order at least `2 + 2 = 4`. -/
theorem dsqZLayerThreeToFourthAugmentationLayer_square_eq_zero (h : ℕ)
    (z : zLayer (DSq h : Type) 2) :
    dsqZLayerThreeToFourthAugmentationLayer h
        (Additive.ofMul (dsqZLayerTwoSquareToThree h z)) = 0 := by
  rw [dsqZLayerThreeToFourthAugmentationLayer,
    dsqZLayerToFourthAugmentationLayer_eq_zero_iff]
  rw [dsqZLayerFourthLift_three_eq_val]
  change levelMk (DSq h : Type) 4 (dsqZLayerRepresentative h 2 z ^ 2) ∈
    modTwoFiniteDimensionSubgroup (SqFourthLevel h) 4
  rw [map_pow]
  have hzTwo : levelMk (DSq h : Type) 4 (dsqZLayerRepresentative h 2 z) ∈
      modTwoFiniteDimensionSubgroup (SqFourthLevel h) 2 := by
    exact dsqZLayerFourthLift_mem_dimension h 2 z
  exact modTwoFiniteGroupDifference_sq_mem_double (SqFourthLevel h) (by omega) hzTwo

/-- If the degree-three map were injective, the lower-two-central square operation from
`Z_2` to `Z_3` would have to vanish identically. -/
theorem dsqZLayerTwoSquareToThree_eq_one_of_injective (h : ℕ)
    (hinj : Function.Injective (dsqZLayerThreeToFourthAugmentationLayer h))
    (z : zLayer (DSq h : Type) 2) :
    dsqZLayerTwoSquareToThree h z = 1 := by
  have hz : Additive.ofMul (dsqZLayerTwoSquareToThree h z) = 0 := by
    apply hinj
    simpa using dsqZLayerThreeToFourthAugmentationLayer_square_eq_zero h z
  exact congrArg Additive.toMul hz

/-- The square of `sigma` in the second lower-two-central layer. -/
def dsqSigmaSquareClass (h : ℕ) : zLayer (DSq h : Type) 2 :=
  ⟨levelMk (DSq h : Type) 3 (dsqSigma h ^ 2),
    ⟨dsqSigma h ^ 2,
      sq_mem_twoCentralSeries_succ (DSq h : Type)
        (Subgroup.mem_top (dsqSigma h)), rfl⟩⟩

/-- The explicit fourth-power class of the distinguished `sigma` generator in `Z_3`. -/
def dsqSigmaFourthClass (h : ℕ) : zLayer (DSq h : Type) 3 :=
  ⟨levelMk (DSq h : Type) 4 (dsqSigma h ^ 4),
    ⟨dsqSigma h ^ 4, by
      rw [show 4 = 2 * 2 by omega, pow_mul]
      exact sq_mem_twoCentralSeries_succ (DSq h : Type)
        (sq_mem_twoCentralSeries_succ (DSq h : Type)
          (Subgroup.mem_top (dsqSigma h))), rfl⟩⟩

/-- The explicit fourth-power witness is genuinely in the image of the layer-square
operation, independently of the representatives chosen to define that operation. -/
theorem dsqZLayerTwoSquareToThree_sigmaSquare (h : ℕ) :
    dsqZLayerTwoSquareToThree h (dsqSigmaSquareClass h) =
      dsqSigmaFourthClass h := by
  apply Subtype.ext
  change levelMk (DSq h : Type) 4
      (dsqZLayerRepresentative h 2 (dsqSigmaSquareClass h) ^ 2) =
    levelMk (DSq h : Type) 4 (dsqSigma h ^ 4)
  rw [map_pow]
  have hpow : dsqSigma h ^ 4 = (dsqSigma h ^ 2) ^ 2 := by
    rw [show 4 = 2 * 2 by omega, pow_mul]
  rw [hpow, map_pow,
    sq_levelMk_eq_sq_canonLift (DSq h : Type) 3
      (dsqZLayerRepresentative h 2 (dsqSigmaSquareClass h)),
    sq_levelMk_eq_sq_canonLift (DSq h : Type) 3 (dsqSigma h ^ 2),
    levelMk_dsqZLayerRepresentative]
  rfl

/-- The mod-`32` value of the distinguished orientation coordinate is `29`. -/
theorem Sval_toZModPow_five :
    PadicInt.toZModPow 5 (SvalUnit : ℤ_[2]) = 29 := by
  rw [val_SvalUnit]
  have h := congrArg (PadicInt.toZModPow (p := 2) 5) Sval_mul_denom
  simp only [map_mul, map_add, map_pow, map_one, map_neg] at h
  rw [rootX_toZModPow_five] at h
  exact (by decide : ∀ z : ZMod (2 ^ 5),
    z * ((21 : ZMod (2 ^ 5)) ^ 2 + 21 + 1) = -(21 : ZMod (2 ^ 5)) ^ 3 →
      z = 29) _ h

/-- The fourth power of `sigma` is not in the fourth lower-two-central subgroup.  Its
cyclotomic value is `29^4 = 17`, not `1`, modulo `32`, whereas every element of `lambda_4`
has trivial mod-`32` cyclotomic shadow. -/
theorem dsqSigma_pow_four_not_mem_twoCentralSeries_four (h : ℕ) :
    dsqSigma h ^ 4 ∉ twoCentralSeries (DSq h : Type) 4 := by
  intro hs
  have himage : chiSq h (dsqSigma h ^ 4) ∈ twoCentralSeries ℤ_[2]ˣ 4 :=
    map_twoCentralSeries_le (chiSq h).toMonoidHom (chiSq h).continuous_toFun 4
      ⟨dsqSigma h ^ 4, hs, rfl⟩
  have hker := twoCentralSeries_units_le 4 (by omega) himage
  have hunit := MonoidHom.mem_ker.mp hker
  have hval := congrArg Units.val hunit
  change PadicInt.toZModPow 5 ((chiSq h (dsqSigma h ^ 4) : ℤ_[2]ˣ) : ℤ_[2]) = 1 at hval
  rw [map_pow, chiSq_sigma, Units.val_pow_eq_pow_val,
    map_pow, Sval_toZModPow_five] at hval
  exact (by decide : (707281 : ZMod (2 ^ 5)) ≠ 1) hval

/-- Consequently the explicit fourth-power class is nonzero in `Z_3`. -/
theorem dsqSigmaFourthClass_ne_one (h : ℕ) : dsqSigmaFourthClass h ≠ 1 := by
  intro hs
  apply dsqSigma_pow_four_not_mem_twoCentralSeries_four h
  rw [← QuotientGroup.eq_one_iff]
  exact congrArg Subtype.val hs

/-- In particular, the layer-square operation itself is nonzero on the distinguished
second-layer square class. -/
theorem dsqZLayerTwoSquareToThree_sigmaSquare_ne_one (h : ℕ) :
    dsqZLayerTwoSquareToThree h (dsqSigmaSquareClass h) ≠ 1 := by
  rw [dsqZLayerTwoSquareToThree_sigmaSquare]
  exact dsqSigmaFourthClass_ne_one h

/-- The subgroup of the third lower-two-central layer generated by squares from the second
layer.  This is the extra lower-series term that the Zassenhaus cubic quotient does not see.
No claim about its full rank is made here. -/
def dsqZLayerTwoSquareImage (h : ℕ) : Subgroup (zLayer (DSq h : Type) 3) :=
  Subgroup.closure (Set.range (dsqZLayerTwoSquareToThree h))

/-- The distinguished fourth-power class belongs to the square-image term. -/
theorem dsqSigmaFourthClass_mem_zLayerTwoSquareImage (h : ℕ) :
    dsqSigmaFourthClass h ∈ dsqZLayerTwoSquareImage h := by
  apply Subgroup.subset_closure
  exact ⟨dsqSigmaSquareClass h, dsqZLayerTwoSquareToThree_sigmaSquare h⟩

/-- The extra lower-series square-image term is nontrivial for every improved model. -/
theorem dsqZLayerTwoSquareImage_ne_bot (h : ℕ) :
    dsqZLayerTwoSquareImage h ≠ ⊥ := by
  intro hbot
  have hmem := dsqSigmaFourthClass_mem_zLayerTwoSquareImage h
  rw [hbot, Subgroup.mem_bot] at hmem
  exact dsqSigmaFourthClass_ne_one h hmem

/-- Formal lower bound on the extra square-image term: it has at least two elements. -/
theorem two_le_card_dsqZLayerTwoSquareImage (h : ℕ) :
    2 ≤ Nat.card (dsqZLayerTwoSquareImage h) := by
  letI : Finite (SqFourthLevel h) :=
    finite_levelQuot (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) 4
  haveI : Finite (zLayer (DSq h : Type) 3) := by infer_instance
  exact (dsqZLayerTwoSquareImage h).one_lt_card_iff_ne_bot.mpr
    (dsqZLayerTwoSquareImage_ne_bot h)

/-- Consequently the third lower exponent-two central layer itself has at least two elements.
This is the strongest unconditional cardinal statement supplied by the single explicit square
witness; computing the full square-image rank remains a separate theorem. -/
theorem two_le_card_zLayer_three_dsq (h : ℕ) :
    2 ≤ Nat.card (zLayer (DSq h : Type) 3) := by
  letI : Finite (SqFourthLevel h) :=
    finite_levelQuot (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) 4
  haveI : Finite (zLayer (DSq h : Type) 3) := by infer_instance
  exact (two_le_card_dsqZLayerTwoSquareImage h).trans
    (dsqZLayerTwoSquareImage h).card_le_card_group

/-- The explicit nonzero fourth-power class is nevertheless killed by the degree-three
augmentation-layer map. -/
theorem dsqZLayerThreeToFourthAugmentationLayer_sigmaFourth_eq_zero (h : ℕ) :
    dsqZLayerThreeToFourthAugmentationLayer h
        (Additive.ofMul (dsqSigmaFourthClass h)) = 0 := by
  rw [dsqZLayerThreeToFourthAugmentationLayer,
    dsqZLayerToFourthAugmentationLayer_eq_zero_iff,
    dsqZLayerFourthLift_three_eq_val]
  change levelMk (DSq h : Type) 4 (dsqSigma h ^ 4) ∈
    modTwoFiniteDimensionSubgroup (SqFourthLevel h) 4
  have hpow : dsqSigma h ^ 4 = (dsqSigma h ^ 2) ^ 2 := by
    rw [show 4 = 2 * 2 by omega, pow_mul]
  rw [hpow, map_pow]
  letI : DiscreteTopology (SqFourthLevel h) :=
    discreteTopology_levelQuot (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) 4
  letI : Finite (SqFourthLevel h) :=
    finite_levelQuot (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) 4
  have hsTwo : levelMk (DSq h : Type) 4 (dsqSigma h ^ 2) ∈
      modTwoFiniteDimensionSubgroup (SqFourthLevel h) 2 := by
    apply twoCentralSeries_le_modTwoFiniteDimensionSubgroup (SqFourthLevel h) 2
    rw [← lambdaImage_eq_twoCentralSeries_levelQuot
      (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) 2 4]
    exact ⟨dsqSigma h ^ 2,
      sq_mem_twoCentralSeries_succ (DSq h : Type)
        (Subgroup.mem_top (dsqSigma h)), rfl⟩
  exact modTwoFiniteGroupDifference_sq_mem_double (SqFourthLevel h) (by omega) hsTwo

/-- The fourth-power witness belongs to the fourth mod-two dimension subgroup of `Q_4`. -/
theorem dsqSigmaFourthClass_mem_dimension_four (h : ℕ) :
    (dsqSigmaFourthClass h).1 ∈
      modTwoFiniteDimensionSubgroup (SqFourthLevel h) 4 := by
  have hmem := (dsqZLayerToFourthAugmentationLayer_eq_zero_iff h 3 (by omega)
    (Additive.ofMul (dsqSigmaFourthClass h))).1
      (dsqZLayerThreeToFourthAugmentationLayer_sigmaFourth_eq_zero h)
  rwa [dsqZLayerFourthLift_three_eq_val] at hmem

/-- The fourth dimension subgroup of `Q_4` is nontrivial. -/
theorem modTwoFiniteDimensionSubgroup_four_sqFourthLevel_ne_bot (h : ℕ) :
    modTwoFiniteDimensionSubgroup (SqFourthLevel h) 4 ≠ ⊥ := by
  intro hbot
  have hmem := dsqSigmaFourthClass_mem_dimension_four h
  rw [hbot, Subgroup.mem_bot] at hmem
  apply dsqSigmaFourthClass_ne_one h
  exact Subtype.ext hmem

/-- Sharp filtration regression: at degree four the mod-two dimension/Zassenhaus filtration
and the lower exponent-two central filtration on `Q_4` are different. -/
theorem modTwoFiniteDimensionSubgroup_four_ne_twoCentralSeries_sqFourthLevel (h : ℕ) :
    modTwoFiniteDimensionSubgroup (SqFourthLevel h) 4 ≠
      twoCentralSeries (SqFourthLevel h) 4 := by
  intro heq
  apply modTwoFiniteDimensionSubgroup_four_sqFourthLevel_ne_bot h
  rw [heq]
  letI : DiscreteTopology (SqFourthLevel h) :=
    discreteTopology_levelQuot (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) 4
  exact twoCentralSeries_levelQuot_self (DSq h : Type)
    (dsqFinsetTopGen h) (isProP_DSq h) 4

/-- Regression: the proposed degree-three lower-two-central augmentation map is not
injective. -/
theorem not_injective_dsqZLayerThreeToFourthAugmentationLayer (h : ℕ) :
    ¬ Function.Injective (dsqZLayerThreeToFourthAugmentationLayer h) := by
  intro hinj
  exact dsqZLayerTwoSquareToThree_sigmaSquare_ne_one h
    (dsqZLayerTwoSquareToThree_eq_one_of_injective h hinj (dsqSigmaSquareClass h))

/-- The tempting supply asserting injectivity of all degree-three lower-two-central layer
maps.  It is isolated as a named proposition so that the truncated Jennings seam cannot
silently assume it. -/
def SqDegreeThreeLowerTwoCentralAugmentationInjectionSupply : Prop :=
  ∀ h : ℕ, Function.Injective (dsqZLayerThreeToFourthAugmentationLayer h)

/-- The lower-two-central augmentation-injection supply is false, already for every individual
improved square presentation. -/
theorem not_sqDegreeThreeLowerTwoCentralAugmentationInjectionSupply :
    ¬ SqDegreeThreeLowerTwoCentralAugmentationInjectionSupply := by
  intro H
  exact not_injective_dsqZLayerThreeToFourthAugmentationLayer 0 (H 0)

#print axioms modTwoFiniteDimensionToAugmentationLayer
#print axioms modTwoFiniteDimensionToAugmentationLayer_eq_zero_iff
#print axioms dsqZLayerToFourthAugmentationLayer
#print axioms dsqZLayerToFourthAugmentationLayer_eq_zero_iff
#print axioms dsqZLayerThreeToFourthAugmentationLayer_square_eq_zero
#print axioms dsqZLayerTwoSquareToThree_sigmaSquare_ne_one
#print axioms dsqZLayerTwoSquareImage_ne_bot
#print axioms two_le_card_dsqZLayerTwoSquareImage
#print axioms two_le_card_zLayer_three_dsq
#print axioms modTwoFiniteDimensionSubgroup_four_ne_twoCentralSeries_sqFourthLevel
#print axioms not_injective_dsqZLayerThreeToFourthAugmentationLayer
#print axioms not_sqDegreeThreeLowerTwoCentralAugmentationInjectionSupply

end

end GQ2.ContCoh

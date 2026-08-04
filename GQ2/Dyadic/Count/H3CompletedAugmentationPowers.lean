/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3CompletedAugmentationGenerators

/-!
# Monomial generation of every completed augmentation power

The completed Cayley-boundary theorem decomposes every element of the square augmentation
ideal in the improved generator differences.  Iterating that decomposition inside the
two-sided powers of the ideal shows that every element of `J^n` is a completed-coefficient
linear combination of length-`n` words in those differences.

This is the surjective half of the all-degree Magnus coefficient theorem before imposing the
quadratic relation and reducing arbitrary words to PBW normal words.  The remaining exact
all-degree issue is the kernel: identifying precisely which monomial combinations land in
`J^(n+1)`.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2 GQ2.FoxH GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.SqCore

universe uR uI

/-! ## A finite recursive type of words -/

/-- Length-`n` words in an alphabet `I`, represented recursively by appending the final
letter.  This representation makes the induction on ideal powers literal. -/
abbrev FiniteGeneratorWord (I : Type uI) : ℕ → Type uI
  | 0 => PUnit
  | n + 1 => FiniteGeneratorWord I n × I

instance finiteGeneratorWordFintype (I : Type uI) [Fintype I] :
    ∀ n, Fintype (FiniteGeneratorWord I n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => by
      letI := finiteGeneratorWordFintype I n
      exact inferInstanceAs (Fintype (FiniteGeneratorWord I n × I))

/-- Evaluate a recursive word as an ordered product of its letters. -/
def finiteGeneratorWordProduct {R : Type uR} [Monoid R]
    {I : Type uI} (g : I → R) : ∀ n, FiniteGeneratorWord I n → R
  | 0, _ => 1
  | n + 1, w => finiteGeneratorWordProduct g n w.1 * g w.2

@[simp] theorem finiteGeneratorWordProduct_zero
    {R : Type uR} [Monoid R] {I : Type uI} (g : I → R)
    (w : FiniteGeneratorWord I 0) :
    finiteGeneratorWordProduct g 0 w = 1 := rfl

@[simp] theorem finiteGeneratorWordProduct_succ
    {R : Type uR} [Monoid R] {I : Type uI} (g : I → R)
    (n : ℕ) (w : FiniteGeneratorWord I n) (i : I) :
    finiteGeneratorWordProduct g (n + 1) (w, i) =
      finiteGeneratorWordProduct g n w * g i := rfl

/-- The left-coefficient monomial map in degree `n`. -/
def finiteGeneratorMonomialMap
    {R : Type uR} [Ring R] {I : Type uI} [Fintype I]
    (g : I → R) (n : ℕ) :
    (FiniteGeneratorWord I n → R) →ₗ[R] R where
  toFun c := ∑ w, c w * finiteGeneratorWordProduct g n w
  map_add' c d := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r c := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc,
      RingHom.id_apply]

@[simp] theorem finiteGeneratorMonomialMap_apply
    {R : Type uR} [Ring R] {I : Type uI} [Fintype I]
    (g : I → R) (n : ℕ) (c : FiniteGeneratorWord I n → R) :
    finiteGeneratorMonomialMap g n c =
      ∑ w, c w * finiteGeneratorWordProduct g n w := rfl

/-- Degree-zero regression: the monomial map is the single empty-word coefficient. -/
@[simp] theorem finiteGeneratorMonomialMap_zero
    {R : Type uR} [Ring R] {I : Type uI} [Fintype I]
    (g : I → R) (c : FiniteGeneratorWord I 0 → R) :
    finiteGeneratorMonomialMap g 0 c = c PUnit.unit := by
  simp [finiteGeneratorMonomialMap]

/-- Degree-one regression: recursive words are just the marked letters. -/
theorem finiteGeneratorMonomialMap_one
    {R : Type uR} [Ring R] {I : Type uI} [Fintype I]
    (g : I → R) (c : FiniteGeneratorWord I 1 → R) :
    finiteGeneratorMonomialMap g 1 c =
      ∑ i, c (PUnit.unit, i) * g i := by
  change (∑ w : PUnit × I, c w * (1 * g w.2)) = _
  rw [Fintype.sum_prod_type]
  simp

/-! ## Generic power-generation theorem -/

/-- If every element of a two-sided ideal is a finite left-coefficient combination of a
finite row `g`, then every element of `J^n` is a left-coefficient combination of the
length-`n` words in `g`. -/
theorem idealPower_exists_finiteGeneratorMonomial
    {R : Type uR} [Ring R] {I : Type uI} [Fintype I]
    (J : Ideal R) [J.IsTwoSided] (g : I → R)
    (hlift : ∀ x : R, x ∈ J → ∃ c : I → R, x = ∑ i, c i * g i) :
    ∀ (n : ℕ) (x : R), x ∈ J ^ n →
      ∃ c : FiniteGeneratorWord I n → R,
        x = finiteGeneratorMonomialMap g n c := by
  intro n
  induction n with
  | zero =>
      intro x hx
      refine ⟨fun _ => x, ?_⟩
      simp [finiteGeneratorMonomialMap]
  | succ n ih =>
      intro x hx
      rw [Submodule.pow_succ] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        obtain ⟨d, hd⟩ := hlift b hb
        have hadi : ∀ i, a * d i ∈ J ^ n := by
          intro i
          exact Ideal.mul_mem_right (d i) (J ^ n) ha
        choose c hc using fun i => ih (a * d i) (hadi i)
        refine ⟨fun w => c w.2 w.1, ?_⟩
        rw [hd, Finset.mul_sum]
        change (∑ i, a * (d i * g i)) =
          ∑ w : FiniteGeneratorWord I n × I,
            c w.2 w.1 * (finiteGeneratorWordProduct g n w.1 * g w.2)
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← mul_assoc, hc i, finiteGeneratorMonomialMap_apply,
          Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro w hw
        rw [mul_assoc]
      · intro a b
        rintro ⟨c, hc⟩ ⟨d, hd⟩
        refine ⟨c + d, ?_⟩
        rw [map_add, ← hc, ← hd]

/-- A length-`n` generator word belongs to `J^n`. -/
theorem finiteGeneratorWordProduct_mem_idealPower
    {R : Type uR} [Ring R] {I : Type uI} [Fintype I]
    (J : Ideal R) [J.IsTwoSided] (g : I → R)
    (hg : ∀ i, g i ∈ J) :
    ∀ (n : ℕ) (w : FiniteGeneratorWord I n),
      finiteGeneratorWordProduct g n w ∈ J ^ n := by
  intro n
  induction n with
  | zero =>
      intro w
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      exact Set.mem_univ _
  | succ n ih =>
      rintro ⟨w, i⟩
      change finiteGeneratorWordProduct g n w * g i ∈ J ^ n * J
      exact Ideal.mul_mem_mul (ih w) (hg i)

/-- The monomial map lands in the corresponding ideal power. -/
theorem finiteGeneratorMonomialMap_mem_idealPower
    {R : Type uR} [Ring R] {I : Type uI} [Fintype I]
    (J : Ideal R) [J.IsTwoSided] (g : I → R)
    (hg : ∀ i, g i ∈ J) (n : ℕ)
    (c : FiniteGeneratorWord I n → R) :
    finiteGeneratorMonomialMap g n c ∈ J ^ n := by
  apply Ideal.sum_mem
  intro w hw
  exact (J ^ n).mul_mem_left _
    (finiteGeneratorWordProduct_mem_idealPower J g hg n w)

/-- The degree-`n` monomial map with its codomain restricted to `J^n`. -/
def finiteGeneratorMonomialToIdealPower
    {R : Type uR} [Ring R] {I : Type uI} [Fintype I]
    (J : Ideal R) [J.IsTwoSided] (g : I → R)
    (hg : ∀ i, g i ∈ J) (n : ℕ) :
    (FiniteGeneratorWord I n → R) →ₗ[R] ↑(J ^ n) :=
  (finiteGeneratorMonomialMap g n).codRestrict (J ^ n)
    (finiteGeneratorMonomialMap_mem_idealPower J g hg n)

/-- The generic monomial power theorem, packaged as surjectivity onto `J^n`. -/
theorem finiteGeneratorMonomialToIdealPower_surjective
    {R : Type uR} [Ring R] {I : Type uI} [Fintype I]
    (J : Ideal R) [J.IsTwoSided] (g : I → R)
    (hg : ∀ i, g i ∈ J)
    (hlift : ∀ x : R, x ∈ J → ∃ c : I → R, x = ∑ i, c i * g i)
    (n : ℕ) :
    Function.Surjective (finiteGeneratorMonomialToIdealPower J g hg n) := by
  rintro ⟨x, hx⟩
  obtain ⟨c, hc⟩ := idealPower_exists_finiteGeneratorMonomial J g hlift n x hx
  refine ⟨c, Subtype.ext ?_⟩
  exact hc.symm

/-! ## Improved square specialization -/

/-- The completed improved generator differences. -/
def sqCompletedGeneratorDifference (h : ℕ) (i : Fin (sqRank h)) :
    ModTwoCompletedGroupAlgebra (DSq h : Type) :=
  ModTwoCompletedGroupAlgebra.of (DSq h : Type) (sqGen h i) - 1

/-- The chosen completed augmentation coordinate is multiplicative. -/
theorem modTwoCompletedAugmentationCoordinate_mul
    (h : ℕ) (x y : ModTwoCompletedGroupAlgebra (DSq h : Type)) :
    modTwoCompletedAugmentationCoordinate (DSq h : Type)
        (sqMagnusOneKernel h) (x * y) =
      modTwoCompletedAugmentationCoordinate (DSq h : Type)
          (sqMagnusOneKernel h) x *
        modTwoCompletedAugmentationCoordinate (DSq h : Type)
          (sqMagnusOneKernel h) y := by
  simp [modTwoCompletedAugmentationCoordinate]

/-- Degree-zero exactness makes the algebraic completed augmentation ideal two-sided. -/
instance sqModTwoCompletedAugmentationIdealIsTwoSided (h : ℕ) :
    (modTwoCompletedAugmentationIdeal (DSq h : Type)).IsTwoSided where
  mul_mem_of_left b ha := by
    apply sqCompletedDegreeZero_reverse h
    rw [modTwoCompletedAugmentationCoordinate_mul,
      modTwoCompletedAugmentationCoordinate_eq_zero_of_mem
        (DSq h : Type) (sqMagnusOneKernel h) ha, zero_mul]

/-- Every element of the completed square augmentation ideal has completed coefficients in
the improved generator differences. -/
theorem sqCompletedAugmentationIdeal_exists_generatorCoefficients
    (h : ℕ) (x : ModTwoCompletedGroupAlgebra (DSq h : Type))
    (hx : x ∈ modTwoCompletedAugmentationIdeal (DSq h : Type)) :
    ∃ c : Fin (sqRank h) → ModTwoCompletedGroupAlgebra (DSq h : Type),
      x = ∑ i, c i * sqCompletedGeneratorDifference h i := by
  apply completedAugmentationGeneratorLifting_sq h (sqMagnusOneKernel h) x
  exact modTwoCompletedAugmentationCoordinate_eq_zero_of_mem
    (DSq h : Type) (sqMagnusOneKernel h) hx

/-- Each improved completed generator difference lies in the completed augmentation ideal. -/
theorem sqCompletedGeneratorDifference_mem (h : ℕ) (i : Fin (sqRank h)) :
    sqCompletedGeneratorDifference h i ∈
      modTwoCompletedAugmentationIdeal (DSq h : Type) := by
  rw [sqCompletedGeneratorDifference, modTwoCompletedAugmentationIdeal]
  exact Submodule.subset_span ⟨sqGen h i, rfl⟩

/-- **All-power monomial lifting for the improved square presentation.** -/
theorem sqCompletedAugmentationPower_exists_monomialCoefficients
    (h n : ℕ) (x : ModTwoCompletedGroupAlgebra (DSq h : Type))
    (hx : x ∈ modTwoCompletedAugmentationIdeal (DSq h : Type) ^ n) :
    ∃ c : FiniteGeneratorWord (Fin (sqRank h)) n →
        ModTwoCompletedGroupAlgebra (DSq h : Type),
      x = finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) n c :=
  idealPower_exists_finiteGeneratorMonomial
    (modTwoCompletedAugmentationIdeal (DSq h : Type))
    (sqCompletedGeneratorDifference h)
    (sqCompletedAugmentationIdeal_exists_generatorCoefficients h) n x hx

/-- The concrete degree-`n` monomial map onto the square completed augmentation power. -/
def sqCompletedGeneratorMonomialToAugmentationPower (h n : ℕ) :
    (FiniteGeneratorWord (Fin (sqRank h)) n →
        ModTwoCompletedGroupAlgebra (DSq h : Type)) →ₗ[ZMod 2]
      (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ n).toAddSubgroup := by
  let M := finiteGeneratorMonomialToIdealPower
    (modTwoCompletedAugmentationIdeal (DSq h : Type))
    (sqCompletedGeneratorDifference h)
    (sqCompletedGeneratorDifference_mem h) n
  exact M.restrictScalars (ZMod 2)

/-- **Surjective monomial coordinates in every completed augmentation degree.** -/
theorem sqCompletedGeneratorMonomialToAugmentationPower_surjective (h n : ℕ) :
    Function.Surjective (sqCompletedGeneratorMonomialToAugmentationPower h n) := by
  intro x
  obtain ⟨c, hc⟩ := finiteGeneratorMonomialToIdealPower_surjective
    (modTwoCompletedAugmentationIdeal (DSq h : Type))
    (sqCompletedGeneratorDifference h)
    (sqCompletedGeneratorDifference_mem h)
    (sqCompletedAugmentationIdeal_exists_generatorCoefficients h) n x
  exact ⟨c, hc⟩

end

end GQ2.ContCoh

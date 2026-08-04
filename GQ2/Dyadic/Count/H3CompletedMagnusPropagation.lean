/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3CompletedQuadraticRelation

/-!
# Propagating the completed Magnus--Labute kernel identity

This file isolates the exact one-step input needed to pass from degree `n` to degree `n+1`.
Every word of length `n+1` has a unique last letter.  Thus its completed monomial value is a
sum `∑_i a_i (g_i - 1)` with `a_i ∈ J^n`, while its quadratic initial form is the
corresponding sum of the degree-`n` normal coefficients times the quadratic letters.

The predicate `SqCompletedLastLetterKernelExact` says exactly that these two last-letter
kernels agree.  The main theorem below turns it into the successor kernel identity, and an
all-degree constructor starts the induction with the now-unconditional degrees `0`, `1`, and
`2`.  This makes the remaining higher-degree obstruction explicit: one needs the complete
last-letter syzygy theorem, not merely cancellation by the single safe letter `Y`.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2 GQ2.FoxH GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.SqCore

universe uI

/-! ## Splitting a coefficient family by its last letter -/

/-- The degree-`n` coefficient family obtained by fixing the last letter of a
degree-`n+1` family. -/
def finiteGeneratorLastCoefficient {R I : Type*} {n : ℕ}
    (c : FiniteGeneratorWord I (n + 1) → R) (i : I) :
    FiniteGeneratorWord I n → R :=
  fun w => c (w, i)

/-- A coefficient family is the sum of its disjoint fixed-last-letter pieces. -/
theorem finiteGenerator_sum_appendCoefficient_lastCoefficient
    {R I : Type*} [AddCommMonoid R] [Fintype I] [DecidableEq I]
    {n : ℕ} (c : FiniteGeneratorWord I (n + 1) → R) :
    ∑ i, finiteGeneratorAppendCoefficient
        (finiteGeneratorLastCoefficient c i) i = c := by
  funext w
  rcases w with ⟨w, j⟩
  simp [finiteGeneratorAppendCoefficient, finiteGeneratorLastCoefficient]

/-- Splitting by the final letter turns the degree-`n+1` monomial map into the
last-letter multiplication row on degree `n`. -/
theorem finiteGeneratorMonomialMap_lastCoefficient
    {R I : Type*} [Ring R] [Fintype I] [DecidableEq I]
    (g : I → R) {n : ℕ}
    (c : FiniteGeneratorWord I (n + 1) → R) :
    finiteGeneratorMonomialMap g (n + 1) c =
      ∑ i, finiteGeneratorMonomialMap g n
          (finiteGeneratorLastCoefficient c i) * g i := by
  calc
    finiteGeneratorMonomialMap g (n + 1) c =
        finiteGeneratorMonomialMap g (n + 1)
          (∑ i, finiteGeneratorAppendCoefficient
            (finiteGeneratorLastCoefficient c i) i) := by
      rw [finiteGenerator_sum_appendCoefficient_lastCoefficient]
    _ = ∑ i, finiteGeneratorMonomialMap g (n + 1)
          (finiteGeneratorAppendCoefficient
            (finiteGeneratorLastCoefficient c i) i) := by
      rw [map_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact finiteGeneratorMonomialMap_appendCoefficient g
        (finiteGeneratorLastCoefficient c i) i

/-- The same last-letter splitting after homogeneous PBW evaluation. -/
theorem sqQuadraticHomogeneousEval_monomialPBWNormal_lastCoefficient
    (h n : ℕ)
    (c : FiniteGeneratorWord (Fin (sqRank h)) (n + 1) →
      ModTwoCompletedGroupAlgebra (DSq h : Type)) :
    sqQuadraticHomogeneousEval h (n + 1)
        (sqCompletedMonomialPBWNormalMap h (n + 1) c) =
      ∑ i, sqQuadraticHomogeneousEval h n
          (sqCompletedMonomialPBWNormalMap h n
            (finiteGeneratorLastCoefficient c i)) *
        sqQuadraticQuotientLetter h i := by
  calc
    sqQuadraticHomogeneousEval h (n + 1)
        (sqCompletedMonomialPBWNormalMap h (n + 1) c) =
      sqQuadraticHomogeneousEval h (n + 1)
        (sqCompletedMonomialPBWNormalMap h (n + 1)
          (∑ i, finiteGeneratorAppendCoefficient
            (finiteGeneratorLastCoefficient c i) i)) := by
      rw [finiteGenerator_sum_appendCoefficient_lastCoefficient]
    _ = ∑ i, sqQuadraticHomogeneousEval h (n + 1)
          (sqCompletedMonomialPBWNormalMap h (n + 1)
            (finiteGeneratorAppendCoefficient
              (finiteGeneratorLastCoefficient c i) i)) := by
      rw [map_sum, map_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact sqQuadraticHomogeneousEval_monomialPBWNormal_append h n
        (finiteGeneratorLastCoefficient c i) i

/-! ## The exact successor obstruction -/

/-- Exactness of the last-letter multiplication row on the `n`th completed augmentation
layer.  The degree-`n` kernel identity makes the normal coefficient of every `a_i ∈ J^n`
canonical.  This predicate asks that a quadratic last-letter syzygy occur exactly when the
corresponding completed sum gains one additional augmentation order.

This is the missing higher-degree syzygy statement.  Cancellation by the safe `Y` proves only
the special case in which every component except the `Y` component vanishes. -/
def SqCompletedLastLetterKernelExact (h n : ℕ)
    (Hn : SqCompletedMonomialPBWKernelIdentity h n) : Prop :=
  ∀ a : Fin (sqRank h) →
      (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ n).toAddSubgroup,
    (∑ i, sqQuadraticHomogeneousEval h n
          (sqCompletedMagnusNormalCoefficient h n Hn (a i)) *
        sqQuadraticQuotientLetter h i = 0) ↔
      ∑ i, (a i).1 * sqCompletedGeneratorDifference h i ∈
        modTwoCompletedAugmentationIdeal (DSq h : Type) ^ (n + 2)

/-- Exactness of the last-letter row propagates the completed Magnus--Labute kernel identity
by one degree. -/
theorem sqCompletedMonomialPBWKernelIdentity_succ_of_lastLetterKernelExact
    (h n : ℕ) (Hn : SqCompletedMonomialPBWKernelIdentity h n)
    (Hlast : SqCompletedLastLetterKernelExact h n Hn) :
    SqCompletedMonomialPBWKernelIdentity h (n + 1) := by
  intro c
  let cLast : Fin (sqRank h) →
      FiniteGeneratorWord (Fin (sqRank h)) n →
        ModTwoCompletedGroupAlgebra (DSq h : Type) :=
    fun i => finiteGeneratorLastCoefficient c i
  let a : Fin (sqRank h) →
      (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ n).toAddSubgroup :=
    fun i => sqCompletedGeneratorMonomialToAugmentationPower h n (cLast i)
  have hcoeff (i : Fin (sqRank h)) :
      sqCompletedMagnusNormalCoefficient h n Hn (a i) =
        sqCompletedMonomialPBWNormalMap h n (cLast i) := by
    exact sqCompletedMagnusNormalCoefficient_monomial h n Hn (cLast i)
  have heval :
      sqQuadraticHomogeneousEval h (n + 1)
          (sqCompletedMonomialPBWNormalMap h (n + 1) c) =
        ∑ i, sqQuadraticHomogeneousEval h n
            (sqCompletedMagnusNormalCoefficient h n Hn (a i)) *
          sqQuadraticQuotientLetter h i := by
    rw [sqQuadraticHomogeneousEval_monomialPBWNormal_lastCoefficient h n c]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcoeff]
  have hmonomial :
      finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) (n + 1) c =
        ∑ i, (a i).1 * sqCompletedGeneratorDifference h i := by
    rw [finiteGeneratorMonomialMap_lastCoefficient]
    rfl
  constructor
  · intro hc
    rw [hmonomial, show n + 1 + 1 = n + 2 by omega]
    apply (Hlast a).1
    rw [← heval, hc, map_zero]
  · intro hc
    apply sqQuadraticHomogeneousEval_injective h (n + 1)
    rw [map_zero, heval]
    apply (Hlast a).2
    rw [← hmonomial, ← show n + 1 + 1 = n + 2 by omega]
    exact hc

/-- Conversely, the successor kernel identity implies exactness of the last-letter row.
Consequently `SqCompletedLastLetterKernelExact` is an exact reformulation of the new
degree-`n+1` input, expressed on the already-understood degree-`n` augmentation layer. -/
theorem sqCompletedLastLetterKernelExact_of_kernelIdentity_succ
    (h n : ℕ) (Hn : SqCompletedMonomialPBWKernelIdentity h n)
    (Hsucc : SqCompletedMonomialPBWKernelIdentity h (n + 1)) :
    SqCompletedLastLetterKernelExact h n Hn := by
  intro a
  classical
  let cLast : Fin (sqRank h) →
      FiniteGeneratorWord (Fin (sqRank h)) n →
        ModTwoCompletedGroupAlgebra (DSq h : Type) :=
    fun i => Classical.choose
      (sqCompletedGeneratorMonomialToAugmentationPower_surjective h n (a i))
  have hcLast (i : Fin (sqRank h)) :
      sqCompletedGeneratorMonomialToAugmentationPower h n (cLast i) = a i :=
    Classical.choose_spec
      (sqCompletedGeneratorMonomialToAugmentationPower_surjective h n (a i))
  let c : FiniteGeneratorWord (Fin (sqRank h)) (n + 1) →
      ModTwoCompletedGroupAlgebra (DSq h : Type) :=
    ∑ i, finiteGeneratorAppendCoefficient (cLast i) i
  have heval :
      sqQuadraticHomogeneousEval h (n + 1)
          (sqCompletedMonomialPBWNormalMap h (n + 1) c) =
        ∑ i, sqQuadraticHomogeneousEval h n
            (sqCompletedMagnusNormalCoefficient h n Hn (a i)) *
          sqQuadraticQuotientLetter h i := by
    dsimp [c]
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      sqQuadraticHomogeneousEval h (n + 1)
          (sqCompletedMonomialPBWNormalMap h (n + 1)
            (finiteGeneratorAppendCoefficient (cLast i) i)) =
        sqQuadraticHomogeneousEval h n
            (sqCompletedMonomialPBWNormalMap h n (cLast i)) *
          sqQuadraticQuotientLetter h i :=
        sqQuadraticHomogeneousEval_monomialPBWNormal_append h n (cLast i) i
      _ = _ := by
        rw [← sqCompletedMagnusNormalCoefficient_monomial h n Hn (cLast i),
          hcLast]
  have hmonomial :
      finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) (n + 1) c =
        ∑ i, (a i).1 * sqCompletedGeneratorDifference h i := by
    dsimp [c]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [finiteGeneratorMonomialMap_appendCoefficient]
    have hiVal := congrArg Subtype.val (hcLast i)
    change finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) n
        (cLast i) = (a i).1 at hiVal
    rw [hiVal]
  constructor
  · intro hz
    have hc0 : sqCompletedMonomialPBWNormalMap h (n + 1) c = 0 := by
      apply sqQuadraticHomogeneousEval_injective h (n + 1)
      rw [map_zero, heval]
      exact hz
    have hm := (Hsucc c).1 hc0
    rwa [hmonomial, show n + 1 + 1 = n + 2 by omega] at hm
  · intro hm
    have hcmem :
        finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) (n + 1) c ∈
          modTwoCompletedAugmentationIdeal (DSq h : Type) ^ (n + 1 + 1) := by
      rwa [hmonomial, show n + 1 + 1 = n + 2 by omega]
    have hc0 := (Hsucc c).2 hcmem
    rw [← heval, hc0, map_zero]

/-- The last-letter condition is precisely equivalent to the successor kernel identity once
the degree-`n` identity has supplied canonical normal coefficients. -/
theorem sqCompletedMonomialPBWKernelIdentity_succ_iff_lastLetterKernelExact
    (h n : ℕ) (Hn : SqCompletedMonomialPBWKernelIdentity h n) :
    SqCompletedMonomialPBWKernelIdentity h (n + 1) ↔
      SqCompletedLastLetterKernelExact h n Hn :=
  ⟨sqCompletedLastLetterKernelExact_of_kernelIdentity_succ h n Hn,
    sqCompletedMonomialPBWKernelIdentity_succ_of_lastLetterKernelExact h n Hn⟩

/-- The first open higher-degree obstruction, stated without any conditional degree-`2`
hypothesis: exactness of the last-letter row from `J²/J³` to `J³/J⁴`. -/
def SqCompletedCubicLastLetterKernelExact (h : ℕ) : Prop :=
  SqCompletedLastLetterKernelExact h 2
    (sqCompletedMonomialPBWKernelIdentity_two h)

/-- The cubic completed Magnus--Labute identity is exactly the cubic last-letter obstruction.
Thus the unconditional quadratic theorem reduces the next degree to one explicit row-kernel
calculation. -/
theorem sqCompletedMonomialPBWKernelIdentity_three_iff (h : ℕ) :
    SqCompletedMonomialPBWKernelIdentity h 3 ↔
      SqCompletedCubicLastLetterKernelExact h := by
  simpa [SqCompletedCubicLastLetterKernelExact] using
    sqCompletedMonomialPBWKernelIdentity_succ_iff_lastLetterKernelExact h 2
      (sqCompletedMonomialPBWKernelIdentity_two h)

/-! ## A local form of the completed Fox-row law -/

/-- The completed Fox-row multiplication law only needs kernel identities in the two adjacent
degrees involved.  The earlier all-degree version is convenient for packaging a full
coefficient system, but is stronger than the proof itself requires. -/
theorem sqCompletedMagnusNormalCoefficient_mul_foxRow_of_adjacent
    (h n : ℕ)
    (Hn : SqCompletedMonomialPBWKernelIdentity h n)
    (Hsucc : SqCompletedMonomialPBWKernelIdentity h (n + 1))
    (a : (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ n).toAddSubgroup)
    (i : Fin (sqRank h)) :
    sqQuadraticHomogeneousEval h (n + 1)
        (sqCompletedMagnusNormalCoefficient h (n + 1) Hsucc
          ⟨a.1 * sqCompletedModTwoFoxDerivativeRow h i, by
            change a.1 * sqCompletedModTwoFoxDerivativeRow h i ∈
              modTwoCompletedAugmentationIdeal (DSq h : Type) ^ n *
                modTwoCompletedAugmentationIdeal (DSq h : Type)
            exact Ideal.mul_mem_mul a.2
              (sqCompletedModTwoFoxDerivativeRow_mem_augmentation h i)⟩) =
      sqQuadraticHomogeneousEval h n
          (sqCompletedMagnusNormalCoefficient h n Hn a) *
        sqQuadraticQuotientFoxRow h i := by
  let J := modTwoCompletedAugmentationIdeal (DSq h : Type)
  let d := sqCompletedModTwoFoxDerivativeRow h i
  let g := sqCompletedGeneratorDifference h (sqInitialPartner h i)
  have hdJ : d ∈ J := sqCompletedModTwoFoxDerivativeRow_mem_augmentation h i
  have hgJ : g ∈ J := sqCompletedGeneratorDifference_mem h (sqInitialPartner h i)
  have hxJ : a.1 * d ∈ J ^ (n + 1) := by
    change a.1 * d ∈ J ^ n * J
    exact Ideal.mul_mem_mul a.2 hdJ
  have hyJ : a.1 * g ∈ J ^ (n + 1) := by
    change a.1 * g ∈ J ^ n * J
    exact Ideal.mul_mem_mul a.2 hgJ
  let x : (J ^ (n + 1)).toAddSubgroup := ⟨a.1 * d, hxJ⟩
  let y : (J ^ (n + 1)).toAddSubgroup := ⟨a.1 * g, hyJ⟩
  have hxy : (x - y : (J ^ (n + 1)).toAddSubgroup).1 ∈
      J ^ ((n + 1) + 1) := by
    change a.1 * d - a.1 * g ∈ J ^ ((n + 1) + 1)
    rw [← mul_sub]
    have herr : d - g ∈ J ^ 2 :=
      sqCompletedFoxRow_sub_partnerDifference_mem_augmentation_sq h i
    rw [show (n + 1) + 1 = n + 2 by omega,
      Submodule.pow_add J (by omega : 2 ≠ 0)]
    exact Ideal.mul_mem_mul a.2 herr
  have hcoeff :
      sqCompletedMagnusNormalCoefficient h (n + 1) Hsucc x =
        sqCompletedMagnusNormalCoefficient h (n + 1) Hsucc y := by
    have hz := (sqCompletedMagnusNormalCoefficient_eq_zero_iff
      h (n + 1) Hsucc (x - y)).2 hxy
    rw [map_sub] at hz
    exact sub_eq_zero.mp hz
  obtain ⟨c, hc⟩ :=
    sqCompletedGeneratorMonomialToAugmentationPower_surjective h n a
  have hcval := congrArg Subtype.val hc
  change finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) n c = a.1 at hcval
  let c' := finiteGeneratorAppendCoefficient c (sqInitialPartner h i)
  have hc' : sqCompletedGeneratorMonomialToAugmentationPower h (n + 1) c' = y := by
    apply Subtype.ext
    change finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) (n + 1) c' =
      a.1 * g
    rw [show c' = finiteGeneratorAppendCoefficient c (sqInitialPartner h i) from rfl,
      finiteGeneratorMonomialMap_appendCoefficient, hcval]
  change sqQuadraticHomogeneousEval h (n + 1)
      (sqCompletedMagnusNormalCoefficient h (n + 1) Hsucc x) = _
  calc
    _ = sqQuadraticHomogeneousEval h (n + 1)
        (sqCompletedMagnusNormalCoefficient h (n + 1) Hsucc y) :=
      congrArg (sqQuadraticHomogeneousEval h (n + 1)) hcoeff
    _ = sqQuadraticHomogeneousEval h (n + 1)
        (sqCompletedMonomialPBWNormalMap h (n + 1) c') := by
      rw [← sqCompletedMagnusNormalCoefficient_monomial h (n + 1) Hsucc c', hc']
    _ = sqQuadraticHomogeneousEval h n
          (sqCompletedMonomialPBWNormalMap h n c) *
        sqQuadraticQuotientLetter h (sqInitialPartner h i) := by
      exact sqQuadraticHomogeneousEval_monomialPBWNormal_append h n c
        (sqInitialPartner h i)
    _ = sqQuadraticHomogeneousEval h n
          (sqCompletedMagnusNormalCoefficient h n Hn a) *
        sqQuadraticQuotientFoxRow h i := by
      rw [← sqCompletedMagnusNormalCoefficient_monomial h n Hn c, hc]
      rfl

/-! ## The 0/1/2-based all-degree constructor -/

/-- The strongest direct constructor supplied by the present formalization: degrees `0`, `1`,
and `2` are unconditional, so it is enough to establish last-letter exactness at every layer
starting with layer `2`. -/
theorem sqCompletedMonomialPBWKernelIdentityAll_of_lastLetterKernelExact
    (h : ℕ)
    (Hstep : ∀ n (Hn : SqCompletedMonomialPBWKernelIdentity h n), 2 ≤ n →
      SqCompletedLastLetterKernelExact h n Hn) :
    SqCompletedMonomialPBWKernelIdentityAll h := by
  have Htail : ∀ k, SqCompletedMonomialPBWKernelIdentity h (k + 2) := by
    intro k
    induction k with
    | zero =>
        simpa using sqCompletedMonomialPBWKernelIdentity_two h
    | succ k ih =>
        have hs := sqCompletedMonomialPBWKernelIdentity_succ_of_lastLetterKernelExact
          h (k + 2) ih (Hstep (k + 2) ih (by omega))
        simpa [Nat.add_assoc] using hs
  intro n
  by_cases hn : n < 2
  · interval_cases n
    · exact sqCompletedMonomialPBWKernelIdentity_zero h
    · exact sqCompletedMonomialPBWKernelIdentity_one h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hn)
    simpa [Nat.add_comm] using Htail k

end

end GQ2.ContCoh

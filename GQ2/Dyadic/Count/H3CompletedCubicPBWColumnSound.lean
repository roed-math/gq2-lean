/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3CompletedCubicAlgebraDetector

/-!
# Soundness of the cubic PBW columns

This file proves the forward half of the cubic Magnus comparison.  The explicit Diamond
normalizer only uses the quadratic rewrite `X S -> YY + S X + handles`.  In the completed
group algebra, the discrepancy of that rewrite is the already-proved element
`sqCompletedQuadraticRelationPolynomial h ∈ J³`.  In a homogeneous word of degree `n+1`,
every use of the rewrite has a context of degree `n-1`, so its discrepancy lies in `J^(n+2)`.

We first evaluate full PBW normal forms in the completed group algebra and prove this filtered
soundness directly for the recursive normalizer.  Degree three then gives the finite column
theorem and `SqCompletedCubicPBWColumnSound h`.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2 GQ2.FoxH GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.SqCore
open SqCubicMagnusAlgebraCertificate

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

/-! ## Completed evaluation of normal words -/

/-- Evaluate a finite combination of quadratic normal words at the completed marked
generator differences. -/
def sqCompletedQuadraticNormalEval (h : ℕ) :
    SqQuadraticNormalSpace h →ₗ[ZMod 2]
      ModTwoCompletedGroupAlgebra (DSq h : Type) :=
  Finsupp.linearCombination (ZMod 2) fun w =>
    quadraticWordEval (ModTwoCompletedGroupAlgebra (DSq h : Type))
      (sqCompletedGeneratorDifference h) w.1

@[simp] theorem sqCompletedQuadraticNormalEval_single (h : ℕ)
    (w : SqQuadraticNormalWord h) (a : ZMod 2) :
    sqCompletedQuadraticNormalEval h (Finsupp.single w a) =
      a • quadraticWordEval (ModTwoCompletedGroupAlgebra (DSq h : Type))
        (sqCompletedGeneratorDifference h) w.1 := by
  simp [sqCompletedQuadraticNormalEval]

/-- Exact compatibility with prepending a nonleading letter. -/
theorem sqCompletedQuadraticNormalEval_prependNonleading (h : ℕ)
    (i : Fin (sqRank h)) (hi : i ≠ 1) (f : SqQuadraticNormalSpace h) :
    sqCompletedQuadraticNormalEval h
        (quadraticNormalPrependLinear (ZMod 2) i hi f) =
      sqCompletedGeneratorDifference h i *
        sqCompletedQuadraticNormalEval h f := by
  induction f using Finsupp.induction with
  | zero => simp
  | single_add w a f hw ha ih =>
      have hs : sqCompletedQuadraticNormalEval h
          (quadraticNormalPrependLinear (ZMod 2) i hi (Finsupp.single w a)) =
        sqCompletedGeneratorDifference h i *
          sqCompletedQuadraticNormalEval h (Finsupp.single w a) := by
        rw [quadraticNormalPrependLinear_single,
          sqCompletedQuadraticNormalEval_single,
          sqCompletedQuadraticNormalEval_single,
          QuadraticNormalWord.prependNonleading_val]
        change a • (sqCompletedGeneratorDifference h i *
            quadraticWordEval (ModTwoCompletedGroupAlgebra (DSq h : Type))
              (sqCompletedGeneratorDifference h) w.1) =
          sqCompletedGeneratorDifference h i *
            (a • quadraticWordEval
              (ModTwoCompletedGroupAlgebra (DSq h : Type))
              (sqCompletedGeneratorDifference h) w.1)
        exact (Algebra.mul_smul_comm a _ _).symm
      rw [map_add, map_add, hs, ih, map_add, mul_add]

/-- Exact completed evaluation of the nonrecursive terms in the `X S` rewrite. -/
theorem sqCompletedQuadraticNormalEval_reductionExtras (h : ℕ)
    (w : SqQuadraticNormalWord h) :
    sqCompletedQuadraticNormalEval h (sqNormalReductionExtras h w) =
      sqCompletedGeneratorDifference h 2 * sqCompletedGeneratorDifference h 2 *
          quadraticWordEval (ModTwoCompletedGroupAlgebra (DSq h : Type))
            (sqCompletedGeneratorDifference h) w.1 +
        ∑ j, (sqCompletedGeneratorDifference h (sqHandleIdxU j) *
              sqCompletedGeneratorDifference h (sqHandleIdxV j) *
              quadraticWordEval (ModTwoCompletedGroupAlgebra (DSq h : Type))
                (sqCompletedGeneratorDifference h) w.1 +
          sqCompletedGeneratorDifference h (sqHandleIdxV j) *
              sqCompletedGeneratorDifference h (sqHandleIdxU j) *
              quadraticWordEval (ModTwoCompletedGroupAlgebra (DSq h : Type))
                (sqCompletedGeneratorDifference h) w.1) := by
  simp only [sqNormalReductionExtras, map_add, map_sum,
    sqCompletedQuadraticNormalEval_single, one_smul, sqNormalPrependPair_val]
  simp only [quadraticWordEval, List.map_cons, List.prod_cons, mul_assoc]

/-- The completed value of the oriented quadratic right-hand side. -/
def sqCompletedQuadraticReductionRHS (h : ℕ) :
    ModTwoCompletedGroupAlgebra (DSq h : Type) :=
  sqCompletedGeneratorDifference h 2 * sqCompletedGeneratorDifference h 2 +
    sqCompletedGeneratorDifference h 0 * sqCompletedGeneratorDifference h 1 +
    ∑ j, (sqCompletedGeneratorDifference h (sqHandleIdxU j) *
        sqCompletedGeneratorDifference h (sqHandleIdxV j) +
      sqCompletedGeneratorDifference h (sqHandleIdxV j) *
        sqCompletedGeneratorDifference h (sqHandleIdxU j))

/-- The previously certified completed polynomial is literally `X*S - RHS`. -/
theorem sqCompletedQuadraticRelationPolynomial_eq (h : ℕ) :
    sqCompletedQuadraticRelationPolynomial h =
      sqCompletedGeneratorDifference h 1 * sqCompletedGeneratorDifference h 0 -
        sqCompletedQuadraticReductionRHS h := by
  rfl

/-- Adding the recursive `S X` term to the extras recovers the full oriented right-hand
side, multiplied by the normal tail. -/
theorem sqCompletedQuadraticNormalEval_extras_add_SX (h : ℕ)
    (w : SqQuadraticNormalWord h) :
    sqCompletedQuadraticNormalEval h (sqNormalReductionExtras h w) +
        sqCompletedGeneratorDifference h 0 *
          (sqCompletedGeneratorDifference h 1 *
            quadraticWordEval (ModTwoCompletedGroupAlgebra (DSq h : Type))
              (sqCompletedGeneratorDifference h) w.1) =
      sqCompletedQuadraticReductionRHS h *
        quadraticWordEval (ModTwoCompletedGroupAlgebra (DSq h : Type))
          (sqCompletedGeneratorDifference h) w.1 := by
  rw [sqCompletedQuadraticNormalEval_reductionExtras,
    sqCompletedQuadraticReductionRHS]
  simp only [add_mul, Finset.sum_mul, mul_assoc]
  abel

/-! ## Ideal bookkeeping for word contexts -/

/-- A word in completed marked differences has the expected augmentation order. -/
theorem sqCompletedQuadraticWordEval_mem_power (h : ℕ) :
    ∀ l : List (Fin (sqRank h)),
      quadraticWordEval (ModTwoCompletedGroupAlgebra (DSq h : Type))
          (sqCompletedGeneratorDifference h) l ∈
        modTwoCompletedAugmentationIdeal (DSq h : Type) ^ l.length := by
  intro l
  induction l with
  | nil =>
      simpa [quadraticWordEval, Submodule.pow_zero]
  | cons i l ih =>
      change sqCompletedGeneratorDifference h i *
          quadraticWordEval (ModTwoCompletedGroupAlgebra (DSq h : Type))
            (sqCompletedGeneratorDifference h) l ∈ _
      rw [List.length_cons, show l.length + 1 = 1 + l.length by omega]
      by_cases hl : l.length = 0
      · have : l = [] := List.eq_nil_of_length_eq_zero hl
        subst l
        simpa [Submodule.pow_one] using sqCompletedGeneratorDifference_mem h i
      · rw [Submodule.pow_add _ hl, Submodule.pow_one]
        exact Ideal.mul_mem_mul (sqCompletedGeneratorDifference_mem h i) ih

/-- Multiplying the certified quadratic discrepancy by a word of length `n` raises it to
augmentation order `n+3`. -/
theorem sqCompletedQuadraticRelation_mul_word_mem (h : ℕ)
    (l : List (Fin (sqRank h))) :
    sqCompletedQuadraticRelationPolynomial h *
        quadraticWordEval (ModTwoCompletedGroupAlgebra (DSq h : Type))
          (sqCompletedGeneratorDifference h) l ∈
      modTwoCompletedAugmentationIdeal (DSq h : Type) ^ (l.length + 3) := by
  let J := modTwoCompletedAugmentationIdeal (DSq h : Type)
  have hq : sqCompletedQuadraticRelationPolynomial h ∈ J ^ 3 :=
    sqCompletedQuadraticRelationPolynomial_mem_augmentation_cube h
  have hw := sqCompletedQuadraticWordEval_mem_power h l
  rw [show l.length + 3 = 3 + l.length by omega]
  by_cases hl : l.length = 0
  · have : l = [] := List.eq_nil_of_length_eq_zero hl
    subst l
    simpa [quadraticWordEval] using hq
  · rw [Submodule.pow_add _ hl]
    exact Ideal.mul_mem_mul hq hw

/-! ## Filtered soundness of the Diamond normalizer -/

/-- Normalizing `X w` changes its completed value only in augmentation order
`length(w)+2`. -/
theorem sqCompletedQuadraticNormalEval_leftXWord_sub_mem (h : ℕ)
    (w : SqQuadraticNormalWord h) :
    sqCompletedQuadraticNormalEval h (sqNormalLeftXWord h w) -
        sqCompletedGeneratorDifference h 1 *
          quadraticWordEval (ModTwoCompletedGroupAlgebra (DSq h : Type))
            (sqCompletedGeneratorDifference h) w.1 ∈
      modTwoCompletedAugmentationIdeal (DSq h : Type) ^ (w.1.length + 2) := by
  rcases w with ⟨l, hl⟩
  induction l with
  | nil =>
      rw [sqNormalLeftXWord_nil, sqCompletedQuadraticNormalEval_single]
      simp [quadraticWordEval]
  | cons a l ih =>
      by_cases ha : a = 0
      · subst a
        let J := modTwoCompletedAugmentationIdeal (DSq h : Type)
        let T := quadraticWordEval
          (ModTwoCompletedGroupAlgebra (DSq h : Type))
          (sqCompletedGeneratorDifference h) l
        let N := sqCompletedQuadraticNormalEval h
          (sqNormalLeftXWord h
            ⟨l, AvoidsQuadraticLeadingPair.tail hl⟩)
        let E := sqCompletedQuadraticNormalEval h
          (sqNormalReductionExtras h
            ⟨l, AvoidsQuadraticLeadingPair.tail hl⟩)
        have hrec : N - sqCompletedGeneratorDifference h 1 * T ∈
            J ^ (l.length + 2) := by
          simpa [N, T, sqNormalLeftXWord] using
            ih (AvoidsQuadraticLeadingPair.tail hl)
        have hleft : sqCompletedGeneratorDifference h 0 *
              (N - sqCompletedGeneratorDifference h 1 * T) ∈
            J ^ ((0 :: l).length + 2) := by
          rw [show (0 :: l).length + 2 = 1 + (l.length + 2) by
              simp only [List.length_cons]
              omega,
            Submodule.pow_add J (by omega : l.length + 2 ≠ 0),
            Submodule.pow_one]
          exact Ideal.mul_mem_mul (sqCompletedGeneratorDifference_mem h 0) hrec
        have hright : sqCompletedQuadraticRelationPolynomial h * T ∈
            J ^ ((0 :: l).length + 2) := by
          simpa [J, T] using sqCompletedQuadraticRelation_mul_word_mem h l
        have hextras : E + sqCompletedGeneratorDifference h 0 *
              (sqCompletedGeneratorDifference h 1 * T) =
            sqCompletedQuadraticReductionRHS h * T := by
          simpa [E, T] using sqCompletedQuadraticNormalEval_extras_add_SX h
            ⟨l, AvoidsQuadraticLeadingPair.tail hl⟩
        have heq :
            E + sqCompletedGeneratorDifference h 0 * N -
                sqCompletedGeneratorDifference h 1 *
                  (sqCompletedGeneratorDifference h 0 * T) =
              sqCompletedGeneratorDifference h 0 *
                  (N - sqCompletedGeneratorDifference h 1 * T) -
                sqCompletedQuadraticRelationPolynomial h * T := by
          rw [sqCompletedQuadraticRelationPolynomial_eq]
          have hE : E = sqCompletedQuadraticReductionRHS h * T -
              sqCompletedGeneratorDifference h 0 *
                (sqCompletedGeneratorDifference h 1 * T) :=
            eq_sub_of_add_eq hextras
          rw [hE]
          simp only [mul_sub, sub_mul, mul_assoc]
          abel
        change sqCompletedQuadraticNormalEval h
              (sqNormalLeftXList h (0 :: l) hl) -
            sqCompletedGeneratorDifference h 1 *
              (sqCompletedGeneratorDifference h 0 * T) ∈ _
        rw [sqNormalLeftXList.eq_2, dif_pos rfl, map_add,
          sqCompletedQuadraticNormalEval_prependNonleading]
        change E + sqCompletedGeneratorDifference h 0 * N -
            sqCompletedGeneratorDifference h 1 *
              (sqCompletedGeneratorDifference h 0 * T) ∈ _
        rw [heq]
        exact Ideal.sub_mem _ hleft hright
      · change sqCompletedQuadraticNormalEval h
            (sqNormalLeftXList h (a :: l) hl) -
          sqCompletedGeneratorDifference h 1 *
            (sqCompletedGeneratorDifference h a *
              quadraticWordEval (ModTwoCompletedGroupAlgebra (DSq h : Type))
                (sqCompletedGeneratorDifference h) l) ∈ _
        rw [sqNormalLeftXList.eq_2, dif_neg ha,
          sqCompletedQuadraticNormalEval_single, one_smul]
        simp only [quadraticWordEval, List.map_cons, List.prod_cons]
        rw [sub_self]
        exact Ideal.zero_mem _

/-- Linear filtered soundness of the normalized `X` action on a homogeneous normal vector. -/
theorem sqCompletedQuadraticNormalEval_leftX_sub_mem (h n : ℕ)
    (f : SqQuadraticNormalSpace h)
    (hf : SqQuadraticNormalSupportedInDegree h n f) :
    sqCompletedQuadraticNormalEval h (sqNormalLeftX h f) -
        sqCompletedGeneratorDifference h 1 *
          sqCompletedQuadraticNormalEval h f ∈
      modTwoCompletedAugmentationIdeal (DSq h : Type) ^ (n + 2) := by
  classical
  induction f using Finsupp.induction with
  | zero => simp
  | single_add w a f hw ha ih =>
      have hwdeg : w.1.length = n := by
        apply hf w
        have hfw : f w = 0 := by
          simpa [Finsupp.mem_support_iff] using hw
        simp [Finsupp.mem_support_iff, hfw, ha]
      have hfdeg : SqQuadraticNormalSupportedInDegree h n f := by
        intro v hv
        apply hf v
        rw [Finsupp.mem_support_iff] at hv ⊢
        by_cases e : v = w
        · subst v
          exact (hw (Finsupp.mem_support_iff.mpr hv)).elim
        · simp [e, hv]
      have hsingle :
          sqCompletedQuadraticNormalEval h
                (sqNormalLeftX h (Finsupp.single w a)) -
              sqCompletedGeneratorDifference h 1 *
                sqCompletedQuadraticNormalEval h (Finsupp.single w a) ∈
            modTwoCompletedAugmentationIdeal (DSq h : Type) ^ (n + 2) := by
        have hb := sqCompletedQuadraticNormalEval_leftXWord_sub_mem h w
        rw [hwdeg] at hb
        rw [sqNormalLeftX_single, map_smul,
          sqCompletedQuadraticNormalEval_single,
          Algebra.mul_smul_comm]
        have hab := Submodule.smul_mem
          (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ (n + 2))
          (algebraMap (ZMod 2)
            (ModTwoCompletedGroupAlgebra (DSq h : Type)) a) hb
        change (algebraMap (ZMod 2)
            (ModTwoCompletedGroupAlgebra (DSq h : Type)) a) *
            (sqCompletedQuadraticNormalEval h (sqNormalLeftXWord h w) -
              sqCompletedGeneratorDifference h 1 *
                quadraticWordEval
                  (ModTwoCompletedGroupAlgebra (DSq h : Type))
                  (sqCompletedGeneratorDifference h) w.1) ∈ _ at hab
        rw [mul_sub] at hab
        simpa only [Algebra.smul_def] using hab
      have htail := ih hfdeg
      rw [map_add, map_add, map_add, mul_add]
      have heq :
          (sqCompletedQuadraticNormalEval h
                (sqNormalLeftX h (Finsupp.single w a)) +
              sqCompletedQuadraticNormalEval h (sqNormalLeftX h f)) -
            (sqCompletedGeneratorDifference h 1 *
                sqCompletedQuadraticNormalEval h (Finsupp.single w a) +
              sqCompletedGeneratorDifference h 1 *
                sqCompletedQuadraticNormalEval h f) =
          (sqCompletedQuadraticNormalEval h
                (sqNormalLeftX h (Finsupp.single w a)) -
              sqCompletedGeneratorDifference h 1 *
                sqCompletedQuadraticNormalEval h (Finsupp.single w a)) +
            (sqCompletedQuadraticNormalEval h (sqNormalLeftX h f) -
              sqCompletedGeneratorDifference h 1 *
                sqCompletedQuadraticNormalEval h f) := by abel
      rw [heq]
      exact Ideal.add_mem _ hsingle htail

/-- Every normalized left-letter action is filtered-sound on homogeneous normal vectors. -/
theorem sqCompletedQuadraticNormalEval_leftLetter_sub_mem (h n : ℕ)
    (i : Fin (sqRank h)) (f : SqQuadraticNormalSpace h)
    (hf : SqQuadraticNormalSupportedInDegree h n f) :
    sqCompletedQuadraticNormalEval h (sqNormalLeftLetter h i f) -
        sqCompletedGeneratorDifference h i *
          sqCompletedQuadraticNormalEval h f ∈
      modTwoCompletedAugmentationIdeal (DSq h : Type) ^ (n + 2) := by
  by_cases hi : i = 1
  · subst i
    rw [sqNormalLeftLetter_X]
    exact sqCompletedQuadraticNormalEval_leftX_sub_mem h n f hf
  · rw [sqNormalLeftLetter_of_ne_X h i hi,
      sqCompletedQuadraticNormalEval_prependNonleading, sub_self]
    exact Ideal.zero_mem _

/-- A word and its explicit Diamond normal form have the same completed value modulo the next
augmentation power. -/
theorem sqCompletedQuadraticNormalEval_repr_word_sub_mem (h : ℕ)
    (l : List (Fin (sqRank h))) :
    sqCompletedQuadraticNormalEval h
          (sqQuadraticNormalRepr h
            (quadraticWordEval (SqQuadraticAlgebra h)
              (sqQuadraticQuotientLetter h) l)) -
        quadraticWordEval (ModTwoCompletedGroupAlgebra (DSq h : Type))
          (sqCompletedGeneratorDifference h) l ∈
      modTwoCompletedAugmentationIdeal (DSq h : Type) ^ (l.length + 1) := by
  induction l with
  | nil =>
      have hr := sqQuadraticNormalRepr_word h (sqQuadraticNormalEmpty h)
      change sqQuadraticNormalRepr h
          (quadraticWordEval (SqQuadraticAlgebra h)
            (sqQuadraticQuotientLetter h) []) = _ at hr
      rw [hr, sqCompletedQuadraticNormalEval_single]
      simp [sqQuadraticNormalEmpty, quadraticWordEval]
  | cons i l ih =>
      let f := sqQuadraticNormalRepr h
        (quadraticWordEval (SqQuadraticAlgebra h)
          (sqQuadraticQuotientLetter h) l)
      let N := sqCompletedQuadraticNormalEval h f
      let T := quadraticWordEval
        (ModTwoCompletedGroupAlgebra (DSq h : Type))
        (sqCompletedGeneratorDifference h) l
      let J := modTwoCompletedAugmentationIdeal (DSq h : Type)
      have hf : SqQuadraticNormalSupportedInDegree h l.length f := by
        exact sqQuadraticNormalRepr_word_supported h l
      have haction :
          sqCompletedQuadraticNormalEval h (sqNormalLeftLetter h i f) -
              sqCompletedGeneratorDifference h i * N ∈
            J ^ ((i :: l).length + 1) := by
        simpa [N, J] using
          sqCompletedQuadraticNormalEval_leftLetter_sub_mem h l.length i f hf
      have htail : N - T ∈ J ^ (l.length + 1) := by
        simpa [N, T, J, f] using ih
      have hmul : sqCompletedGeneratorDifference h i * (N - T) ∈
          J ^ ((i :: l).length + 1) := by
        rw [show (i :: l).length + 1 = 1 + (l.length + 1) by
            simp only [List.length_cons]
            omega,
          Submodule.pow_add J (by omega : l.length + 1 ≠ 0),
          Submodule.pow_one]
        exact Ideal.mul_mem_mul (sqCompletedGeneratorDifference_mem h i) htail
      change sqCompletedQuadraticNormalEval h
            (sqQuadraticNormalRepr h
              (sqQuadraticQuotientLetter h i *
                quadraticWordEval (SqQuadraticAlgebra h)
                  (sqQuadraticQuotientLetter h) l)) -
          sqCompletedGeneratorDifference h i * T ∈ _
      rw [sqQuadraticNormalRepr_letter_mul]
      change sqCompletedQuadraticNormalEval h (sqNormalLeftLetter h i f) -
          sqCompletedGeneratorDifference h i * T ∈ _
      have heq :
          sqCompletedQuadraticNormalEval h (sqNormalLeftLetter h i f) -
              sqCompletedGeneratorDifference h i * T =
            (sqCompletedQuadraticNormalEval h (sqNormalLeftLetter h i f) -
                sqCompletedGeneratorDifference h i * N) +
              sqCompletedGeneratorDifference h i * (N - T) := by
        rw [mul_sub]
        abel
      rw [heq]
      exact Ideal.add_mem _ haction hmul

/-! ## Homogeneous columns and cubic summation -/

/-- Evaluate homogeneous normal words in the completed group algebra. -/
def sqCompletedQuadraticHomogeneousNormalEval (h n : ℕ) :
    SqQuadraticHomogeneousNormalSpace h n →ₗ[ZMod 2]
      ModTwoCompletedGroupAlgebra (DSq h : Type) :=
  (sqCompletedQuadraticNormalEval h).comp (sqQuadraticHomogeneousInclude h n)

/-- Word-level filtered PBW soundness. -/
theorem sqCompletedQuadraticHomogeneousNormalEval_wordPBWNormal_sub_mem
    (h n : ℕ) (w : FiniteGeneratorWord (Fin (sqRank h)) n) :
    sqCompletedQuadraticHomogeneousNormalEval h n
          (sqQuadraticWordPBWNormal h n w) -
        finiteGeneratorWordProduct (sqCompletedGeneratorDifference h) n w ∈
      modTwoCompletedAugmentationIdeal (DSq h : Type) ^ (n + 1) := by
  rw [sqCompletedQuadraticHomogeneousNormalEval, LinearMap.comp_apply,
    sqQuadraticWordPBWNormal,
    sqQuadraticHomogeneousInclude_project_of_supported h n]
  · rw [finiteGeneratorWordProduct_eq_quadraticWordEval]
    simpa [finiteGeneratorWordList_length] using
      sqCompletedQuadraticNormalEval_repr_word_sub_mem h
        (finiteGeneratorWordList n w)
  · simpa [finiteGeneratorWordList_length] using
      sqQuadraticNormalRepr_word_supported h (finiteGeneratorWordList n w)

/-- **Cubic PBW column regression.**  Every literal cubic word equals the completed evaluation
of its PBW-normal column modulo `J⁴`. -/
theorem sqCompletedCubicPBW_wordColumn_sound (h : ℕ)
    (w : FiniteGeneratorWord (Fin (sqRank h)) 3) :
    sqCompletedQuadraticHomogeneousNormalEval h 3
          (sqQuadraticWordPBWNormal h 3 w) -
        finiteGeneratorWordProduct (sqCompletedGeneratorDifference h) 3 w ∈
      modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 4 := by
  simpa using
    sqCompletedQuadraticHomogeneousNormalEval_wordPBWNormal_sub_mem h 3 w

/-- The forward cubic PBW column calculation. -/
theorem sqCompletedCubicPBWColumnSound (h : ℕ) :
    SqCompletedCubicPBWColumnSound h := by
  intro a ha
  have hsum :
      ∑ w, a w •
          (sqCompletedQuadraticHomogeneousNormalEval h 3
              (sqQuadraticWordPBWNormal h 3 w) -
            finiteGeneratorWordProduct (sqCompletedGeneratorDifference h) 3 w) ∈
        modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 4 := by
    apply Ideal.sum_mem
    intro w hw
    have hs := Submodule.smul_mem
      (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 4)
      (algebraMap (ZMod 2)
        (ModTwoCompletedGroupAlgebra (DSq h : Type)) (a w))
      (sqCompletedCubicPBW_wordColumn_sound h w)
    simpa only [Algebra.smul_def, smul_eq_mul] using hs
  have heq :
      ∑ w, a w •
          (sqCompletedQuadraticHomogeneousNormalEval h 3
              (sqQuadraticWordPBWNormal h 3 w) -
            finiteGeneratorWordProduct (sqCompletedGeneratorDifference h) 3 w) =
        sqCompletedQuadraticHomogeneousNormalEval h 3
            (sqCubicScalarPBWNormalMap h a) -
          sqCompletedCubicScalarMonomial h a := by
    rw [sqCubicScalarPBWNormalMap_apply, map_sum,
      sqCompletedCubicScalarMonomial, finiteGeneratorMonomialMap_apply]
    simp only [map_smul, smul_sub, Finset.sum_sub_distrib]
    apply congrArg₂ (· - ·)
    · rfl
    · apply Finset.sum_congr rfl
      intro w hw
      simp [Algebra.smul_def]
  rw [heq, ha, map_zero, zero_sub] at hsum
  exact (Ideal.neg_mem_iff _).mp hsum

end

end GQ2.ContCoh

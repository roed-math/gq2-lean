/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3SqQuadraticPBW

/-!
# The overlap-free normal representation of the square quadratic algebra

This file starts the constructive Diamond-lemma proof for the single rewrite

`X S ↦ Y Y + S X + ∑ j, (U_j V_j + V_j U_j)`.

Instead of assuming confluence, it constructs the normal left action explicitly.  Left
multiplication by `X` moves through an initial string of `S`'s; the recursive call is on the
strictly shorter tail.  All other letters simply prepend themselves.  The resulting operators
satisfy the quadratic relation on the nose.  This is the key independence half of PBW: once the
operator identity is packaged through the quadratic quotient, applying a normal monomial to the
empty word recovers its basis vector.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2.Dyadic GQ2.Dyadic.SqCore

/-! ## Prepending non-leading letters -/

theorem AvoidsQuadraticLeadingPair.tail {I : Type*} {x s : I} {w : List I}
    (hw : AvoidsQuadraticLeadingPair x s w) :
    AvoidsQuadraticLeadingPair x s w.tail := by
  cases w with
  | nil => trivial
  | cons a w =>
      cases w with
      | nil => trivial
      | cons b w => exact hw.2

/-- A letter different from the first letter `x` can always be prepended to a normal word. -/
def QuadraticNormalWord.prependNonleading {I : Type*} {x s : I}
    (i : I) (hi : i ≠ x) (w : QuadraticNormalWord x s) :
    QuadraticNormalWord x s := by
  refine ⟨i :: w.1, ?_⟩
  cases w with
  | mk val property =>
      cases val with
      | nil => trivial
      | cons a val =>
          exact ⟨fun hp => hi hp.1, property⟩

@[simp] theorem QuadraticNormalWord.prependNonleading_val {I : Type*} {x s : I}
    (i : I) (hi : i ≠ x) (w : QuadraticNormalWord x s) :
    (w.prependNonleading i hi).1 = i :: w.1 :=
  rfl

/-- Linear extension of prepending a non-leading letter. -/
def quadraticNormalPrependLinear (R : Type*) [Semiring R]
    {I : Type*} {x s : I} (i : I) (hi : i ≠ x) :
    QuadraticNormalFormSpace R x s →ₗ[R] QuadraticNormalFormSpace R x s :=
  Finsupp.lmapDomain R R (QuadraticNormalWord.prependNonleading i hi)

@[simp] theorem quadraticNormalPrependLinear_single (R : Type*) [Semiring R]
    {I : Type*} {x s : I} (i : I) (hi : i ≠ x)
    (w : QuadraticNormalWord x s) (a : R) :
    quadraticNormalPrependLinear R i hi (Finsupp.single w a) =
      Finsupp.single (w.prependNonleading i hi) a := by
  simp [quadraticNormalPrependLinear]

/-! ## Square-index inequalities -/

private theorem sqFin_zero_ne_one (h : ℕ) :
    (0 : Fin (sqRank h)) ≠ 1 := by
  intro e
  have hv : ((1 : Fin (sqRank h)) : Nat) = 1 := by
    change 1 % sqRank h = 1
    apply Nat.mod_eq_of_lt
    rw [sqRank]
    omega
  have he := congrArg Fin.val e
  rw [hv] at he
  simp at he

private theorem sqFin_two_ne_one (h : ℕ) :
    (2 : Fin (sqRank h)) ≠ 1 := by
  intro e
  have hv₁ : ((1 : Fin (sqRank h)) : Nat) = 1 := by
    change 1 % sqRank h = 1
    apply Nat.mod_eq_of_lt
    rw [sqRank]
    omega
  have hv₂ : ((2 : Fin (sqRank h)) : Nat) = 2 := by
    change 2 % sqRank h = 2
    apply Nat.mod_eq_of_lt
    rw [sqRank]
    omega
  have he := congrArg Fin.val e
  rw [hv₁, hv₂] at he
  omega

private theorem sqHandleIdxU_ne_one {h : ℕ} (j : Fin h) :
    sqHandleIdxU j ≠ (1 : Fin (sqRank h)) := by
  intro e
  have he := congrArg (sqInitialAlphabetEquiv h) e
  simp at he

private theorem sqHandleIdxV_ne_one {h : ℕ} (j : Fin h) :
    sqHandleIdxV j ≠ (1 : Fin (sqRank h)) := by
  intro e
  have he := congrArg (sqInitialAlphabetEquiv h) e
  simp at he

/-! ## The terminating `X` action -/

abbrev SqQuadraticNormalWord (h : ℕ) :=
  QuadraticNormalWord (1 : Fin (sqRank h)) 0

abbrev SqQuadraticNormalSpace (h : ℕ) :=
  QuadraticNormalFormSpace (ZMod 2) (1 : Fin (sqRank h)) 0

/-- Prefix a normal word by two letters which are both different from `X`. -/
def sqNormalPrependPair (h : ℕ) (a b : Fin (sqRank h))
    (ha : a ≠ 1) (hb : b ≠ 1) (w : SqQuadraticNormalWord h) :
    SqQuadraticNormalWord h :=
  (w.prependNonleading b hb).prependNonleading a ha

@[simp] theorem sqNormalPrependPair_val (h : ℕ) (a b : Fin (sqRank h))
    (ha : a ≠ 1) (hb : b ≠ 1) (w : SqQuadraticNormalWord h) :
    (sqNormalPrependPair h a b ha hb w).1 = a :: b :: w.1 :=
  rfl

/-- The non-`S X` terms in the reduction of `X S w`. -/
def sqNormalReductionExtras (h : ℕ) (w : SqQuadraticNormalWord h) :
    SqQuadraticNormalSpace h :=
  Finsupp.single
      (sqNormalPrependPair h 2 2 (sqFin_two_ne_one h) (sqFin_two_ne_one h) w) 1 +
    ∑ j, (Finsupp.single
        (sqNormalPrependPair h (sqHandleIdxU j) (sqHandleIdxV j)
          (sqHandleIdxU_ne_one j) (sqHandleIdxV_ne_one j) w) 1 +
      Finsupp.single
        (sqNormalPrependPair h (sqHandleIdxV j) (sqHandleIdxU j)
          (sqHandleIdxV_ne_one j) (sqHandleIdxU_ne_one j) w) 1)

/-- List-level recursion underlying normalization of `X w`. -/
def sqNormalLeftXList (h : ℕ) :
    (w : List (Fin (sqRank h))) →
      AvoidsQuadraticLeadingPair (1 : Fin (sqRank h)) 0 w →
      SqQuadraticNormalSpace h
  | [], _ => Finsupp.single ⟨[1], trivial⟩ 1
  | a :: w, hw =>
      if ha : a = 0 then
        sqNormalReductionExtras h ⟨w, AvoidsQuadraticLeadingPair.tail hw⟩ +
          quadraticNormalPrependLinear (ZMod 2) 0 (sqFin_zero_ne_one h)
            (sqNormalLeftXList h w (AvoidsQuadraticLeadingPair.tail hw))
      else
        Finsupp.single ⟨1 :: a :: w, ⟨fun hp => ha hp.2, hw⟩⟩ 1

/-- Normalization of `X w` for a normal word `w`.  When `w` starts with `S`, use the relation;
the `S X` summand is `S` times the recursive normalization of `X` on the shorter tail. -/
def sqNormalLeftXWord (h : ℕ) (w : SqQuadraticNormalWord h) :
    SqQuadraticNormalSpace h :=
  sqNormalLeftXList h w.1 w.2

@[simp] theorem sqNormalLeftXWord_nil (h : ℕ) :
    sqNormalLeftXWord h ⟨[], trivial⟩ =
      Finsupp.single ⟨[1], trivial⟩ 1 :=
  by rw [sqNormalLeftXWord, sqNormalLeftXList]

@[simp] theorem sqNormalLeftXWord_cons_S (h : ℕ) (w : SqQuadraticNormalWord h) :
    sqNormalLeftXWord h (w.prependNonleading 0 (sqFin_zero_ne_one h)) =
      sqNormalReductionExtras h w +
        quadraticNormalPrependLinear (ZMod 2) 0 (sqFin_zero_ne_one h)
          (sqNormalLeftXWord h w) := by
  change sqNormalLeftXList h (0 :: w.1) _ = _
  rw [sqNormalLeftXList.eq_2, dif_pos rfl, sqNormalLeftXWord]
  have ht : (⟨w.1, _⟩ : SqQuadraticNormalWord h) = w := Subtype.ext rfl
  rw [ht]

/-! ## Linear left-letter operators -/

/-- Linear extension of the terminating `X` normalization. -/
def sqNormalLeftX (h : ℕ) :
    SqQuadraticNormalSpace h →ₗ[ZMod 2] SqQuadraticNormalSpace h :=
  Finsupp.lsum (ZMod 2) fun w =>
    LinearMap.toSpanSingleton (ZMod 2) (SqQuadraticNormalSpace h)
      (sqNormalLeftXWord h w)

@[simp] theorem sqNormalLeftX_single (h : ℕ)
    (w : SqQuadraticNormalWord h) (a : ZMod 2) :
    sqNormalLeftX h (Finsupp.single w a) = a • sqNormalLeftXWord h w := by
  simp [sqNormalLeftX]

/-- Left multiplication by a marked letter on normal forms. -/
def sqNormalLeftLetter (h : ℕ) (i : Fin (sqRank h)) :
    Module.End (ZMod 2) (SqQuadraticNormalSpace h) :=
  if hi : i = 1 then
    hi ▸ sqNormalLeftX h
  else
    quadraticNormalPrependLinear (ZMod 2) i hi

@[simp] theorem sqNormalLeftLetter_X (h : ℕ) :
    sqNormalLeftLetter h 1 = sqNormalLeftX h := by
  simp [sqNormalLeftLetter]

@[simp] theorem sqNormalLeftLetter_of_ne_X (h : ℕ) (i : Fin (sqRank h))
    (hi : i ≠ 1) :
    sqNormalLeftLetter h i = quadraticNormalPrependLinear (ZMod 2) i hi := by
  simp [sqNormalLeftLetter, hi]

@[simp] theorem sqNormalLeftLetter_single_of_ne_X (h : ℕ)
    (i : Fin (sqRank h)) (hi : i ≠ 1) (w : SqQuadraticNormalWord h)
    (a : ZMod 2) :
    sqNormalLeftLetter h i (Finsupp.single w a) =
      Finsupp.single (w.prependNonleading i hi) a := by
  rw [sqNormalLeftLetter_of_ne_X h i hi]
  exact quadraticNormalPrependLinear_single (ZMod 2) i hi w a

@[simp] theorem sqNormalLeftLetter_pair_single_of_ne_X (h : ℕ)
    (i k : Fin (sqRank h)) (hi : i ≠ 1) (hk : k ≠ 1)
    (w : SqQuadraticNormalWord h) (a : ZMod 2) :
    sqNormalLeftLetter h i (sqNormalLeftLetter h k (Finsupp.single w a)) =
      Finsupp.single (sqNormalPrependPair h i k hi hk w) a := by
  rw [sqNormalLeftLetter_single_of_ne_X h k hk,
    sqNormalLeftLetter_single_of_ne_X h i hi]
  rfl

/-- The terminating normal operators satisfy the square quadratic relation on every normal
basis word.  This is the overlap-free Diamond calculation: the `S X` summand is exactly the
recursive call in `sqNormalLeftXWord`. -/
theorem sqNormal_quadraticRelation_single (h : ℕ)
    (w : SqQuadraticNormalWord h) :
    sqNormalLeftLetter h 1
        (sqNormalLeftLetter h 0 (Finsupp.single w 1)) =
      sqNormalLeftLetter h 2
          (sqNormalLeftLetter h 2 (Finsupp.single w 1)) +
        sqNormalLeftLetter h 0
          (sqNormalLeftLetter h 1 (Finsupp.single w 1)) +
        ∑ j, (sqNormalLeftLetter h (sqHandleIdxU j)
            (sqNormalLeftLetter h (sqHandleIdxV j) (Finsupp.single w 1)) +
          sqNormalLeftLetter h (sqHandleIdxV j)
            (sqNormalLeftLetter h (sqHandleIdxU j) (Finsupp.single w 1))) := by
  rw [sqNormalLeftLetter_X,
    sqNormalLeftLetter_single_of_ne_X h 0 (sqFin_zero_ne_one h),
    sqNormalLeftX_single, one_smul,
    sqNormalLeftXWord_cons_S,
    sqNormalLeftLetter_pair_single_of_ne_X h 2 2
      (sqFin_two_ne_one h) (sqFin_two_ne_one h),
    sqNormalLeftX_single, one_smul,
    sqNormalLeftLetter_of_ne_X h 0 (sqFin_zero_ne_one h)]
  simp only [sqNormalReductionExtras]
  simp_rw [sqNormalLeftLetter_pair_single_of_ne_X h
      (sqHandleIdxU _) (sqHandleIdxV _)
        (sqHandleIdxU_ne_one _) (sqHandleIdxV_ne_one _),
    sqNormalLeftLetter_pair_single_of_ne_X h
      (sqHandleIdxV _) (sqHandleIdxU _)
        (sqHandleIdxV_ne_one _) (sqHandleIdxU_ne_one _)]
  simp only [sqNormalPrependPair]
  abel

/-- Operator form of the quadratic relation. -/
theorem sqNormal_quadraticRelation (h : ℕ) :
    sqNormalLeftLetter h 1 * sqNormalLeftLetter h 0 =
      sqNormalLeftLetter h 2 * sqNormalLeftLetter h 2 +
        sqNormalLeftLetter h 0 * sqNormalLeftLetter h 1 +
        ∑ j, (sqNormalLeftLetter h (sqHandleIdxU j) *
            sqNormalLeftLetter h (sqHandleIdxV j) +
          sqNormalLeftLetter h (sqHandleIdxV j) *
            sqNormalLeftLetter h (sqHandleIdxU j)) := by
  apply Finsupp.lhom_ext
  intro w a
  rw [← Finsupp.smul_single_one]
  simp only [map_smul]
  simp only [Module.End.mul_apply, LinearMap.add_apply]
  rw [show
    (∑ j, (sqNormalLeftLetter h (sqHandleIdxU j) *
        sqNormalLeftLetter h (sqHandleIdxV j) +
      sqNormalLeftLetter h (sqHandleIdxV j) *
        sqNormalLeftLetter h (sqHandleIdxU j))) (Finsupp.single w 1) =
      ∑ j, (sqNormalLeftLetter h (sqHandleIdxU j) *
          sqNormalLeftLetter h (sqHandleIdxV j) +
        sqNormalLeftLetter h (sqHandleIdxV j) *
          sqNormalLeftLetter h (sqHandleIdxU j)) (Finsupp.single w 1) by simp]
  have hr := congrArg (fun z : SqQuadraticNormalSpace h => a • z)
    (sqNormal_quadraticRelation_single h w)
  simpa only [Module.End.mul_apply, LinearMap.add_apply, Finset.sum_apply] using hr

/-! ## Factoring the normal representation through the quadratic quotient -/

/-- The free-algebra representation generated by the normal left-letter operators. -/
def sqQuadraticFreeNormalRepresentation (h : ℕ) :
    FreeAlgebra (ZMod 2) (Fin (sqRank h)) →ₐ[ZMod 2]
      Module.End (ZMod 2) (SqQuadraticNormalSpace h) :=
  FreeAlgebra.lift (ZMod 2) (sqNormalLeftLetter h)

@[simp] theorem sqQuadraticFreeNormalRepresentation_letter (h : ℕ)
    (i : Fin (sqRank h)) :
    sqQuadraticFreeNormalRepresentation h (sqQuadraticFreeLetter h i) =
      sqNormalLeftLetter h i := by
  simp [sqQuadraticFreeNormalRepresentation, sqQuadraticFreeLetter]

/-- The relation polynomial acts by zero in the normal representation. -/
theorem sqQuadraticFreeNormalRepresentation_relation (h : ℕ) :
    sqQuadraticFreeNormalRepresentation h (sqQuadraticRelationPolynomial h) = 0 := by
  simp only [sqQuadraticRelationPolynomial, sqQuadraticReductionRHS,
    map_sub, map_add, map_mul, map_sum,
    sqQuadraticFreeNormalRepresentation_letter]
  rw [sqNormal_quadraticRelation h, sub_self]

/-- The two-sided relation ideal lies in the kernel of the free normal representation. -/
theorem sqQuadraticRelationIdeal_mapsTo_zero (h : ℕ)
    (a : FreeAlgebra (ZMod 2) (Fin (sqRank h)))
    (ha : a ∈ sqQuadraticRelationIdeal h) :
    sqQuadraticFreeNormalRepresentation h a = 0 := by
  rw [sqQuadraticRelationIdeal] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
      rcases ha with ⟨⟨u, v⟩, rfl⟩
      rw [map_mul, map_mul, sqQuadraticFreeNormalRepresentation_relation,
        mul_zero, zero_mul]
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy, add_zero]
  | smul r x hx ih =>
      change sqQuadraticFreeNormalRepresentation h (r * x) = 0
      rw [map_mul, ih, mul_zero]

/-- The normal representation of the actual quadratic quotient. -/
def sqQuadraticNormalRepresentation (h : ℕ) :
    SqQuadraticAlgebra h →ₐ[ZMod 2]
      Module.End (ZMod 2) (SqQuadraticNormalSpace h) :=
  Ideal.Quotient.liftₐ (sqQuadraticRelationIdeal h)
    (sqQuadraticFreeNormalRepresentation h)
    (sqQuadraticRelationIdeal_mapsTo_zero h)

@[simp] theorem sqQuadraticNormalRepresentation_mk (h : ℕ)
    (a : FreeAlgebra (ZMod 2) (Fin (sqRank h))) :
    sqQuadraticNormalRepresentation h
        (Ideal.Quotient.mkₐ (ZMod 2) (sqQuadraticRelationIdeal h) a) =
      sqQuadraticFreeNormalRepresentation h a := by
  rw [sqQuadraticNormalRepresentation, Ideal.Quotient.liftₐ_apply,
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.lift_mk]
  rfl

@[simp] theorem sqQuadraticNormalRepresentation_letter (h : ℕ)
    (i : Fin (sqRank h)) :
    sqQuadraticNormalRepresentation h (sqQuadraticQuotientLetter h i) =
      sqNormalLeftLetter h i := by
  rw [sqQuadraticQuotientLetter, sqQuadraticNormalRepresentation_mk,
    sqQuadraticFreeNormalRepresentation_letter]

/-! ## Evaluation at the empty word and independence -/

/-- The empty normal word. -/
def sqQuadraticNormalEmpty (h : ℕ) : SqQuadraticNormalWord h :=
  ⟨[], trivial⟩

/-- The empty-word basis vector. -/
def sqQuadraticNormalEmptyVector (h : ℕ) : SqQuadraticNormalSpace h :=
  Finsupp.single (sqQuadraticNormalEmpty h) 1

/-- A marked letter acting on a normal tail produces the expected longer basis word whenever
the longer word is normal. -/
theorem sqNormalLeftLetter_single_tail (h : ℕ)
    (i : Fin (sqRank h)) (w : List (Fin (sqRank h)))
    (hw : AvoidsQuadraticLeadingPair (1 : Fin (sqRank h)) 0 (i :: w)) :
    sqNormalLeftLetter h i
        (Finsupp.single ⟨w, AvoidsQuadraticLeadingPair.tail hw⟩ 1) =
      Finsupp.single ⟨i :: w, hw⟩ 1 := by
  by_cases hi : i = 1
  · subst i
    rw [sqNormalLeftLetter_X, sqNormalLeftX_single, one_smul]
    cases w with
    | nil =>
        rw [sqNormalLeftXWord_nil]
    | cons a w =>
        have ha : a ≠ 0 := by
          intro e
          exact hw.1 ⟨rfl, e⟩
        rw [sqNormalLeftXWord, sqNormalLeftXList.eq_2, dif_neg ha]
  · rw [sqNormalLeftLetter_single_of_ne_X h i hi]
    apply congrArg (fun v : SqQuadraticNormalWord h => Finsupp.single v 1)
    apply Subtype.ext
    rfl

/-- A normal quotient monomial acts on the empty vector as its own normal basis vector. -/
theorem sqQuadraticNormalRepresentation_word_empty (h : ℕ)
    (w : List (Fin (sqRank h)))
    (hw : AvoidsQuadraticLeadingPair (1 : Fin (sqRank h)) 0 w) :
    sqQuadraticNormalRepresentation h
        (quadraticWordEval (SqQuadraticAlgebra h)
          (sqQuadraticQuotientLetter h) w)
        (sqQuadraticNormalEmptyVector h) =
      Finsupp.single ⟨w, hw⟩ 1 := by
  induction w with
  | nil =>
      simp [sqQuadraticNormalEmptyVector, sqQuadraticNormalEmpty]
  | cons i w ih =>
      rw [show quadraticWordEval (SqQuadraticAlgebra h)
          (sqQuadraticQuotientLetter h) (i :: w) =
        sqQuadraticQuotientLetter h i *
          quadraticWordEval (SqQuadraticAlgebra h)
            (sqQuadraticQuotientLetter h) w by
              rfl,
        map_mul, Module.End.mul_apply,
        sqQuadraticNormalRepresentation_letter,
        ih (AvoidsQuadraticLeadingPair.tail hw),
        sqNormalLeftLetter_single_tail]

/-- Evaluate a finitely supported combination of normal words in the quadratic quotient. -/
def sqQuadraticNormalEval (h : ℕ) :
    SqQuadraticNormalSpace h →ₗ[ZMod 2] SqQuadraticAlgebra h :=
  Finsupp.lsum (ZMod 2) fun w =>
    LinearMap.toSpanSingleton (ZMod 2) (SqQuadraticAlgebra h)
      (quadraticWordEval (SqQuadraticAlgebra h)
        (sqQuadraticQuotientLetter h) w.1)

@[simp] theorem sqQuadraticNormalEval_single (h : ℕ)
    (w : SqQuadraticNormalWord h) (a : ZMod 2) :
    sqQuadraticNormalEval h (Finsupp.single w a) =
      a • quadraticWordEval (SqQuadraticAlgebra h)
        (sqQuadraticQuotientLetter h) w.1 := by
  simp [sqQuadraticNormalEval]

/-- Apply the quotient representation to the empty basis vector. -/
def sqQuadraticNormalRepr (h : ℕ) :
    SqQuadraticAlgebra h →ₗ[ZMod 2] SqQuadraticNormalSpace h where
  toFun a := sqQuadraticNormalRepresentation h a (sqQuadraticNormalEmptyVector h)
  map_add' a b := by simp
  map_smul' r a := by
    rw [map_smul]
    rfl

@[simp] theorem sqQuadraticNormalRepr_word (h : ℕ)
    (w : SqQuadraticNormalWord h) :
    sqQuadraticNormalRepr h
        (quadraticWordEval (SqQuadraticAlgebra h)
          (sqQuadraticQuotientLetter h) w.1) =
      Finsupp.single w 1 := by
  rw [sqQuadraticNormalRepr]
  exact sqQuadraticNormalRepresentation_word_empty h w.1 w.2

/-- **Independence half of the Diamond lemma.**  Evaluation at the empty word is a left
inverse to normal-word evaluation. -/
theorem sqQuadraticNormalRepr_eval (h : ℕ) (f : SqQuadraticNormalSpace h) :
    sqQuadraticNormalRepr h (sqQuadraticNormalEval h f) = f := by
  induction f using Finsupp.induction with
  | zero => simp
  | single_add w a f hw ha ih =>
      rw [map_add]
      rw [sqQuadraticNormalEval_single]
      have hsingle : sqQuadraticNormalRepr h
          (a • quadraticWordEval (SqQuadraticAlgebra h)
            (sqQuadraticQuotientLetter h) w.1) = Finsupp.single w a := by
        rw [map_smul, sqQuadraticNormalRepr_word,
          Finsupp.smul_single_one]
      calc
        sqQuadraticNormalRepr h
            (a • quadraticWordEval (SqQuadraticAlgebra h)
                (sqQuadraticQuotientLetter h) w.1 +
              sqQuadraticNormalEval h f) =
          sqQuadraticNormalRepr h
              (a • quadraticWordEval (SqQuadraticAlgebra h)
                (sqQuadraticQuotientLetter h) w.1) +
            sqQuadraticNormalRepr h (sqQuadraticNormalEval h f) :=
              map_add _ _ _
        _ = Finsupp.single w a + f := by rw [hsingle, ih]

/-- Normal-word evaluation in the actual quadratic quotient is injective. -/
theorem sqQuadraticNormalEval_injective (h : ℕ) :
    Function.Injective (sqQuadraticNormalEval h) :=
  Function.LeftInverse.injective (sqQuadraticNormalRepr_eval h)

/-! ## Spanning by normal words -/

/-- Display the defining quotient relation entirely in marked quotient letters. -/
theorem sqQuadraticQuotient_relation_expanded (h : ℕ) :
    sqQuadraticQuotientLetter h 1 * sqQuadraticQuotientLetter h 0 =
      sqQuadraticQuotientLetter h 2 * sqQuadraticQuotientLetter h 2 +
        sqQuadraticQuotientLetter h 0 * sqQuadraticQuotientLetter h 1 +
        ∑ j, (sqQuadraticQuotientLetter h (sqHandleIdxU j) *
            sqQuadraticQuotientLetter h (sqHandleIdxV j) +
          sqQuadraticQuotientLetter h (sqHandleIdxV j) *
            sqQuadraticQuotientLetter h (sqHandleIdxU j)) := by
  rw [sqQuadraticQuotient_relation]
  simp only [sqQuadraticReductionRHS, map_add, map_mul, map_sum,
    sqQuadraticQuotientLetter]

/-- Evaluation intertwines prepending any non-`X` letter with left multiplication by that
marked quotient letter. -/
theorem sqQuadraticNormalEval_prependNonleading (h : ℕ)
    (i : Fin (sqRank h)) (hi : i ≠ 1) (f : SqQuadraticNormalSpace h) :
    sqQuadraticNormalEval h
        (quadraticNormalPrependLinear (ZMod 2) i hi f) =
      sqQuadraticQuotientLetter h i * sqQuadraticNormalEval h f := by
  induction f using Finsupp.induction with
  | zero => simp
  | single_add w a f hw ha ih =>
      have hs : sqQuadraticNormalEval h
          (quadraticNormalPrependLinear (ZMod 2) i hi (Finsupp.single w a)) =
        sqQuadraticQuotientLetter h i *
          sqQuadraticNormalEval h (Finsupp.single w a) := by
        rw [quadraticNormalPrependLinear_single,
          sqQuadraticNormalEval_single, sqQuadraticNormalEval_single,
          QuadraticNormalWord.prependNonleading_val]
        change a • (sqQuadraticQuotientLetter h i *
            quadraticWordEval (SqQuadraticAlgebra h)
              (sqQuadraticQuotientLetter h) w.1) =
          sqQuadraticQuotientLetter h i *
            (a • quadraticWordEval (SqQuadraticAlgebra h)
              (sqQuadraticQuotientLetter h) w.1)
        exact (Algebra.mul_smul_comm a _ _).symm
      rw [map_add, map_add, hs, ih]
      rw [map_add, mul_add]

/-- Evaluation of the nonrecursive terms in the `X S` reduction. -/
theorem sqQuadraticNormalEval_reductionExtras (h : ℕ)
    (w : SqQuadraticNormalWord h) :
    sqQuadraticNormalEval h (sqNormalReductionExtras h w) =
      sqQuadraticQuotientLetter h 2 * sqQuadraticQuotientLetter h 2 *
          quadraticWordEval (SqQuadraticAlgebra h)
            (sqQuadraticQuotientLetter h) w.1 +
        ∑ j, (sqQuadraticQuotientLetter h (sqHandleIdxU j) *
              sqQuadraticQuotientLetter h (sqHandleIdxV j) *
              quadraticWordEval (SqQuadraticAlgebra h)
                (sqQuadraticQuotientLetter h) w.1 +
          sqQuadraticQuotientLetter h (sqHandleIdxV j) *
              sqQuadraticQuotientLetter h (sqHandleIdxU j) *
              quadraticWordEval (SqQuadraticAlgebra h)
                (sqQuadraticQuotientLetter h) w.1) := by
  simp only [sqNormalReductionExtras, map_add, map_sum,
    sqQuadraticNormalEval_single, one_smul, sqNormalPrependPair_val]
  simp only [quadraticWordEval, List.map_cons, List.prod_cons, mul_assoc]

/-- Normalization of `X w` is sound in the quadratic quotient. -/
theorem sqQuadraticNormalEval_leftXWord (h : ℕ)
    (w : SqQuadraticNormalWord h) :
    sqQuadraticNormalEval h (sqNormalLeftXWord h w) =
      sqQuadraticQuotientLetter h 1 *
        quadraticWordEval (SqQuadraticAlgebra h)
          (sqQuadraticQuotientLetter h) w.1 := by
  rcases w with ⟨w, hw⟩
  induction w with
  | nil =>
      rw [sqNormalLeftXWord_nil, sqQuadraticNormalEval_single]
      simp [quadraticWordEval]
  | cons a w ih =>
      by_cases ha : a = 0
      · subst a
        have iht := ih (AvoidsQuadraticLeadingPair.tail hw)
        rw [sqNormalLeftXWord] at iht
        change sqQuadraticNormalEval h (sqNormalLeftXList h (0 :: w) hw) = _
        rw [sqNormalLeftXList.eq_2, dif_pos rfl, map_add,
          sqQuadraticNormalEval_reductionExtras,
          sqQuadraticNormalEval_prependNonleading,
          iht]
        rw [show quadraticWordEval (SqQuadraticAlgebra h)
            (sqQuadraticQuotientLetter h) (0 :: w) =
          sqQuadraticQuotientLetter h 0 *
            quadraticWordEval (SqQuadraticAlgebra h)
              (sqQuadraticQuotientLetter h) w by rfl]
        conv_rhs =>
          rw [← mul_assoc, sqQuadraticQuotient_relation_expanded]
        simp only [add_mul, Finset.sum_mul, mul_assoc]
        abel
      · change sqQuadraticNormalEval h (sqNormalLeftXList h (a :: w) hw) = _
        rw [sqNormalLeftXList.eq_2, dif_neg ha,
          sqQuadraticNormalEval_single, one_smul]
        rfl

/-- Linear form of soundness for the terminating `X` action. -/
theorem sqQuadraticNormalEval_leftX (h : ℕ) (f : SqQuadraticNormalSpace h) :
    sqQuadraticNormalEval h (sqNormalLeftX h f) =
      sqQuadraticQuotientLetter h 1 * sqQuadraticNormalEval h f := by
  induction f using Finsupp.induction with
  | zero => simp
  | single_add w a f hw ha ih =>
      have hs : sqQuadraticNormalEval h
          (sqNormalLeftX h (Finsupp.single w a)) =
        sqQuadraticQuotientLetter h 1 *
          sqQuadraticNormalEval h (Finsupp.single w a) := by
        rw [sqNormalLeftX_single, map_smul, sqQuadraticNormalEval_leftXWord,
          sqQuadraticNormalEval_single]
        exact (Algebra.mul_smul_comm a _ _).symm
      rw [map_add, map_add, hs, ih]
      rw [map_add, mul_add]

/-- Evaluation intertwines every normal left-letter operator with left multiplication in the
quadratic quotient. -/
theorem sqQuadraticNormalEval_leftLetter (h : ℕ)
    (i : Fin (sqRank h)) (f : SqQuadraticNormalSpace h) :
    sqQuadraticNormalEval h (sqNormalLeftLetter h i f) =
      sqQuadraticQuotientLetter h i * sqQuadraticNormalEval h f := by
  by_cases hi : i = 1
  · subst i
    rw [sqNormalLeftLetter_X, sqQuadraticNormalEval_leftX]
  · rw [sqNormalLeftLetter_of_ne_X h i hi,
      sqQuadraticNormalEval_prependNonleading]

theorem sqQuadraticNormalRepr_letter_mul (h : ℕ)
    (i : Fin (sqRank h)) (a : SqQuadraticAlgebra h) :
    sqQuadraticNormalRepr h (sqQuadraticQuotientLetter h i * a) =
      sqNormalLeftLetter h i (sqQuadraticNormalRepr h a) := by
  rw [sqQuadraticNormalRepr]
  change sqQuadraticNormalRepresentation h
      (sqQuadraticQuotientLetter h i * a) (sqQuadraticNormalEmptyVector h) = _
  rw [map_mul, Module.End.mul_apply, sqQuadraticNormalRepresentation_letter]
  rfl

/-- Every quotient word is recovered after normalizing by the representation and evaluating
the resulting normal combination. -/
theorem sqQuadraticNormalEval_repr_word (h : ℕ)
    (w : List (Fin (sqRank h))) :
    sqQuadraticNormalEval h
        (sqQuadraticNormalRepr h
          (quadraticWordEval (SqQuadraticAlgebra h)
            (sqQuadraticQuotientLetter h) w)) =
      quadraticWordEval (SqQuadraticAlgebra h)
        (sqQuadraticQuotientLetter h) w := by
  induction w with
  | nil =>
      simp [sqQuadraticNormalRepr, sqQuadraticNormalEmptyVector,
        sqQuadraticNormalEmpty, sqQuadraticNormalEval, quadraticWordEval]
  | cons i w ih =>
      change sqQuadraticNormalEval h
          (sqQuadraticNormalRepr h
            (sqQuadraticQuotientLetter h i *
              quadraticWordEval (SqQuadraticAlgebra h)
                (sqQuadraticQuotientLetter h) w)) = _
      rw [sqQuadraticNormalRepr_letter_mul,
        sqQuadraticNormalEval_leftLetter, ih]
      rfl

end

end GQ2.ContCoh

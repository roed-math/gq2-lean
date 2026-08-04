/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3SqRowInitialForms

/-!
# The PBW target for the improved square relation

The homogeneous quadratic relation attached to the improved square presentation is

`Y Y + S X + X S + ∑ j, (U_j V_j + V_j U_j)`.

Orient it with leading word `X S`.  This file makes the corresponding Diamond-lemma target
precise.  It proves the word-theoretic part which does not depend on a hidden associated-graded
identification:

* `X S` is unbordered, so two leading occurrences cannot overlap;
* normal words are the words avoiding the adjacent pair `X S`;
* appending the normal letter `Y` preserves normality and is injective;
* for any algebra having the advertised normal words as a PBW basis, right multiplication by
  `Y` is injective.

The final section defines the actual quadratic quotient by its two-sided relation ideal, records its defining
equation, and applies the generic PBW adapter to the formal square Fox row.  Thus the remaining
Diamond step is exactly the construction of `SqQuadraticPBW h`; no theorem below assumes that
the completed group algebra has this associated graded, or that its Fox row is already regular.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2.Dyadic GQ2.Dyadic.SqCore

universe uI uR uA

/-! ## Normal words for one quadratic leading monomial -/

/-- A word avoids the adjacent pair `x s`.  This recursive definition is deliberately local:
it is the normal-word predicate for the single rewrite whose leading monomial is `x s`. -/
def AvoidsQuadraticLeadingPair {I : Type uI} (x s : I) : List I → Prop
  | [] => True
  | [_] => True
  | a :: b :: w => ¬ (a = x ∧ b = s) ∧ AvoidsQuadraticLeadingPair x s (b :: w)

@[simp] theorem avoidsQuadraticLeadingPair_nil {I : Type uI} (x s : I) :
    AvoidsQuadraticLeadingPair x s [] :=
  trivial

@[simp] theorem avoidsQuadraticLeadingPair_singleton {I : Type uI} (x s a : I) :
    AvoidsQuadraticLeadingPair x s [a] :=
  trivial

@[simp] theorem avoidsQuadraticLeadingPair_cons_cons {I : Type uI}
    (x s a b : I) (w : List I) :
    AvoidsQuadraticLeadingPair x s (a :: b :: w) ↔
      ¬ (a = x ∧ b = s) ∧ AvoidsQuadraticLeadingPair x s (b :: w) :=
  Iff.rfl

/-- Appending a letter other than the second letter of the leading pair cannot create a new
reducible subword. -/
theorem AvoidsQuadraticLeadingPair.append_singleton_of_ne_second
    {I : Type uI} {x s y : I} (hy : y ≠ s) {w : List I}
    (hw : AvoidsQuadraticLeadingPair x s w) :
    AvoidsQuadraticLeadingPair x s (w ++ [y]) := by
  induction w with
  | nil => simp
  | cons a w ih =>
      cases w with
      | nil =>
          change ¬ (a = x ∧ y = s) ∧ True
          exact ⟨fun hpair => hy hpair.2, trivial⟩
      | cons b w =>
          simp only [List.cons_append,
            avoidsQuadraticLeadingPair_cons_cons] at hw ⊢
          exact ⟨hw.1, ih hw.2⟩

/-- The normal words for a leading pair `x s`. -/
def QuadraticNormalWord {I : Type uI} (x s : I) :=
  {w : List I // AvoidsQuadraticLeadingPair x s w}

/-- Append a safe letter to a normal word. -/
def QuadraticNormalWord.appendSafe {I : Type uI} {x s : I}
    (y : I) (hy : y ≠ s) :
    QuadraticNormalWord x s → QuadraticNormalWord x s :=
  fun w => ⟨w.1 ++ [y], w.2.append_singleton_of_ne_second hy⟩

@[simp] theorem QuadraticNormalWord.appendSafe_val {I : Type uI} {x s : I}
    (y : I) (hy : y ≠ s) (w : QuadraticNormalWord x s) :
    (w.appendSafe y hy).1 = w.1 ++ [y] :=
  rfl

/-- Appending a safe letter is injective on normal words. -/
theorem QuadraticNormalWord.appendSafe_injective {I : Type uI} {x s : I}
    (y : I) (hy : y ≠ s) :
    Function.Injective (QuadraticNormalWord.appendSafe y hy :
      QuadraticNormalWord x s → QuadraticNormalWord x s) := by
  intro w v h
  apply Subtype.ext
  exact List.append_left_injective [y] (congrArg Subtype.val h)

/-- The leading word `x s` has no nontrivial self-overlap when `x ≠ s`: its one-letter
suffix is not its one-letter prefix.  For a quadratic monomial this is exactly the unbordered
condition used in the Diamond lemma. -/
theorem quadraticLeadingPair_unbordered {I : Type uI} {x s : I} (hxs : x ≠ s) :
    ([x, s] : List I).drop 1 ≠ ([x, s] : List I).take 1 := by
  simpa using hxs.symm

/-- Two occurrences of an unbordered quadratic leading word cannot overlap in one letter.
This is the only possible proper overlap between two length-two words. -/
theorem quadraticLeadingPair_no_oneLetterOverlap {I : Type uI} {x s : I}
    (hxs : x ≠ s) {a : I} (hleft : [a, x] = [x, s])
    (_hright : [x, s] = [x, a]) : False := by
  apply hxs
  simpa using congrArg List.tail hleft

/-! ## Linear normal forms and the safe-letter shift -/

/-- The free module on the normal words. -/
abbrev QuadraticNormalFormSpace (R : Type uR) [Semiring R]
    {I : Type uI} (x s : I) :=
  QuadraticNormalWord x s →₀ R

/-- Linear extension of appending a safe letter to every normal monomial. -/
def quadraticNormalAppendLinear (R : Type uR) [Semiring R]
    {I : Type uI} {x s : I} (y : I) (hy : y ≠ s) :
    QuadraticNormalFormSpace R x s →ₗ[R] QuadraticNormalFormSpace R x s :=
  Finsupp.lmapDomain R R (QuadraticNormalWord.appendSafe y hy)

@[simp] theorem quadraticNormalAppendLinear_apply (R : Type uR) [Semiring R]
    {I : Type uI} {x s : I} (y : I) (hy : y ≠ s)
    (f : QuadraticNormalFormSpace R x s) :
    quadraticNormalAppendLinear R y hy f =
      Finsupp.mapDomain (QuadraticNormalWord.appendSafe y hy) f :=
  rfl

@[simp] theorem quadraticNormalAppendLinear_single (R : Type uR) [Semiring R]
    {I : Type uI} {x s : I} (y : I) (hy : y ≠ s)
    (w : QuadraticNormalWord x s) (a : R) :
    quadraticNormalAppendLinear R y hy (Finsupp.single w a) =
      Finsupp.single (w.appendSafe y hy) a := by
  simp [quadraticNormalAppendLinear]

/-- The safe-letter shift on the free normal-form module is injective. -/
theorem quadraticNormalAppendLinear_injective (R : Type uR) [Semiring R]
    {I : Type uI} {x s : I} (y : I) (hy : y ≠ s) :
    Function.Injective (quadraticNormalAppendLinear R y hy :
      QuadraticNormalFormSpace R x s → QuadraticNormalFormSpace R x s) :=
  Finsupp.mapDomain_injective (QuadraticNormalWord.appendSafe_injective y hy)

/-! ## A reusable PBW-to-regularity adapter -/

section PBWAdapter

variable (R : Type uR) [CommSemiring R]
variable {I : Type uI} (x s : I)
variable (A : Type uA) [Semiring A] [Algebra R A]

/-- Evaluation of a word in a marked algebra. -/
def quadraticWordEval (letter : I → A) (w : List I) : A :=
  (w.map letter).prod

@[simp] theorem quadraticWordEval_nil (letter : I → A) :
    quadraticWordEval A letter [] = 1 :=
  rfl

@[simp] theorem quadraticWordEval_append (letter : I → A) (u v : List I) :
    quadraticWordEval A letter (u ++ v) =
      quadraticWordEval A letter u * quadraticWordEval A letter v := by
  simp [quadraticWordEval]

@[simp] theorem quadraticWordEval_append_singleton (letter : I → A)
    (w : List I) (y : I) :
    quadraticWordEval A letter (w ++ [y]) =
      quadraticWordEval A letter w * letter y := by
  simp [quadraticWordEval]

/-- Honest PBW data for the one-leading-word presentation: the normal monomials form a basis,
expressed as a linear equivalence to finitely supported coefficient functions. -/
structure QuadraticPBW (letter : I → A) where
  repr : A ≃ₗ[R] QuadraticNormalFormSpace R x s
  repr_normalWord : ∀ w : QuadraticNormalWord x s,
    repr (quadraticWordEval A letter w.1) = Finsupp.single w 1

namespace QuadraticPBW

variable {R x s A} {letter : I → A}

@[simp] theorem symm_single (pbw : QuadraticPBW R x s A letter)
    (w : QuadraticNormalWord x s) (a : R) :
    pbw.repr.symm (Finsupp.single w a) =
      a • quadraticWordEval A letter w.1 := by
  apply pbw.repr.injective
  rw [pbw.repr.apply_symm_apply, map_smul, pbw.repr_normalWord]
  simp

/-- Under a PBW normal-word basis, multiplication on the right by a safe letter is represented
by the injective append map on normal words. -/
theorem repr_mul_safe (pbw : QuadraticPBW R x s A letter)
    (y : I) (hy : y ≠ s) (a : A) :
    pbw.repr (a * letter y) =
      quadraticNormalAppendLinear R y hy (pbw.repr a) := by
  have hf : ∀ f : QuadraticNormalFormSpace R x s,
      pbw.repr (pbw.repr.symm f * letter y) =
        quadraticNormalAppendLinear R y hy f := by
    intro f
    induction f using Finsupp.induction with
    | zero => simp
    | single_add w r f hw hr ih =>
        have heval := pbw.repr_normalWord (w.appendSafe y hy)
        rw [QuadraticNormalWord.appendSafe_val,
          quadraticWordEval_append_singleton] at heval
        rw [map_add, pbw.symm_single, add_mul, smul_mul_assoc,
          map_add, map_smul, heval, ih]
        rw [map_add, quadraticNormalAppendLinear_single]
        simp
  simpa using hf (pbw.repr a)

/-- **PBW cancellation theorem.**  A safe normal letter is right-regular in every algebra with
the advertised quadratic PBW basis. -/
theorem rightMul_safe_injective (pbw : QuadraticPBW R x s A letter)
    (y : I) (hy : y ≠ s) :
    Function.Injective (fun a : A => a * letter y) := by
  intro a b hab
  change a * letter y = b * letter y at hab
  apply pbw.repr.injective
  apply quadraticNormalAppendLinear_injective R y hy
  rw [← pbw.repr_mul_safe y hy, ← pbw.repr_mul_safe y hy]
  exact congrArg pbw.repr hab

end QuadraticPBW

end PBWAdapter

/-! ## The actual square quadratic quotient -/

variable (h : ℕ)

/-- A generator in the free associative algebra on the square alphabet. -/
abbrev sqQuadraticFreeLetter (i : Fin (sqRank h)) :
    FreeAlgebra (ZMod 2) (Fin (sqRank h)) :=
  FreeAlgebra.ι (ZMod 2) i

/-- The right-hand side after orienting the homogeneous square relation with leading word
`X S`.  In characteristic two this is equivalent to
`Y Y + S X + X S + Σ(UV+VU) = 0`. -/
def sqQuadraticReductionRHS : FreeAlgebra (ZMod 2) (Fin (sqRank h)) :=
  sqQuadraticFreeLetter h 2 * sqQuadraticFreeLetter h 2 +
    sqQuadraticFreeLetter h 0 * sqQuadraticFreeLetter h 1 +
    ∑ j, (sqQuadraticFreeLetter h (sqHandleIdxU j) *
      sqQuadraticFreeLetter h (sqHandleIdxV j) +
      sqQuadraticFreeLetter h (sqHandleIdxV j) *
        sqQuadraticFreeLetter h (sqHandleIdxU j))

/-- The monic relation polynomial, oriented with leading word `X S`. -/
def sqQuadraticRelationPolynomial :
    FreeAlgebra (ZMod 2) (Fin (sqRank h)) :=
  sqQuadraticFreeLetter h 1 * sqQuadraticFreeLetter h 0 -
    sqQuadraticReductionRHS h

/-- The two-sided ideal generated by the quadratic relation.  Mathlib's `Ideal` is a left
ideal in the noncommutative setting, so the generating set explicitly includes both contexts. -/
def sqQuadraticRelationIdeal :
    Ideal (FreeAlgebra (ZMod 2) (Fin (sqRank h))) :=
  Ideal.span (Set.range fun p :
    FreeAlgebra (ZMod 2) (Fin (sqRank h)) ×
      FreeAlgebra (ZMod 2) (Fin (sqRank h)) =>
        p.1 * sqQuadraticRelationPolynomial h * p.2)

instance sqQuadraticRelationIdeal_isTwoSided :
    (sqQuadraticRelationIdeal h).IsTwoSided where
  mul_mem_of_left {a} b ha := by
    change a * b ∈ sqQuadraticRelationIdeal h
    rw [sqQuadraticRelationIdeal] at ha ⊢
    induction ha using Submodule.span_induction with
    | mem z hz =>
        rcases hz with ⟨⟨d, c⟩, rfl⟩
        apply Submodule.subset_span
        exact ⟨(d, c * b), by simp only [mul_assoc]⟩
    | zero => simp
    | add x y hx hy ihx ihy =>
        rw [add_mul]
        exact Submodule.add_mem _ ihx ihy
    | smul a x hx ih =>
        change (a * x) * b ∈ _
        rw [mul_assoc]
        exact Submodule.smul_mem _ a ih

/-- The free associative `F₂`-algebra modulo the homogeneous quadratic relation of the
improved square presentation. -/
abbrev SqQuadraticAlgebra :=
  FreeAlgebra (ZMod 2) (Fin (sqRank h)) ⧸ sqQuadraticRelationIdeal h

/-- The marked letters in the quadratic quotient. -/
def sqQuadraticQuotientLetter (i : Fin (sqRank h)) : SqQuadraticAlgebra h :=
  Ideal.Quotient.mkₐ (ZMod 2) (sqQuadraticRelationIdeal h)
    (sqQuadraticFreeLetter h i)

/-- The defining oriented relation holds in the quadratic quotient. -/
theorem sqQuadraticQuotient_relation :
    sqQuadraticQuotientLetter h 1 * sqQuadraticQuotientLetter h 0 =
      Ideal.Quotient.mkₐ (ZMod 2) (sqQuadraticRelationIdeal h)
        (sqQuadraticReductionRHS h) := by
  change (Ideal.Quotient.mkₐ (ZMod 2) (sqQuadraticRelationIdeal h))
      (sqQuadraticFreeLetter h 1) *
      (Ideal.Quotient.mkₐ (ZMod 2) (sqQuadraticRelationIdeal h))
        (sqQuadraticFreeLetter h 0) =
    (Ideal.Quotient.mkₐ (ZMod 2) (sqQuadraticRelationIdeal h))
      (sqQuadraticReductionRHS h)
  rw [← map_mul]
  apply (Ideal.Quotient.eq).2
  change sqQuadraticRelationPolynomial h ∈ sqQuadraticRelationIdeal h
  rw [sqQuadraticRelationIdeal]
  apply Submodule.subset_span
  exact ⟨(1, 1), by simp⟩

/-- The concrete Diamond-lemma target: normal words for `X S` form a basis of the actual
quadratic quotient.  This definition contains only the PBW basis assertion; it does not mention
completed group algebras, Fox injectivity, or cohomology. -/
abbrev SqQuadraticPBW : Type :=
  QuadraticPBW (ZMod 2) (1 : Fin (sqRank h)) (0 : Fin (sqRank h))
    (SqQuadraticAlgebra h) (sqQuadraticQuotientLetter h)

private theorem sqFin_one_ne_zero :
    (1 : Fin (sqRank h)) ≠ 0 := by
  intro e
  have hv : ((1 : Fin (sqRank h)) : Nat) = 1 := by
    change 1 % sqRank h = 1
    apply Nat.mod_eq_of_lt
    rw [sqRank]
    omega
  have he := congrArg Fin.val e
  rw [hv] at he
  simp at he

private theorem sqFin_two_ne_zero :
    (2 : Fin (sqRank h)) ≠ 0 := by
  intro e
  have hv : ((2 : Fin (sqRank h)) : Nat) = 2 := by
    change 2 % sqRank h = 2
    apply Nat.mod_eq_of_lt
    rw [sqRank]
    omega
  have he := congrArg Fin.val e
  rw [hv] at he
  simp at he

/-- The actual leading word `X S` is unbordered. -/
theorem sqQuadraticLeadingWord_unbordered :
    ([1, 0] : List (Fin (sqRank h))).drop 1 ≠
      ([1, 0] : List (Fin (sqRank h))).take 1 :=
  quadraticLeadingPair_unbordered (sqFin_one_ne_zero h)

/-- `Y` is a safe normal letter for the `X S` rewrite. -/
def sqQuadraticNormalWord_appendY
    (w : QuadraticNormalWord (1 : Fin (sqRank h)) 0) :
    QuadraticNormalWord (1 : Fin (sqRank h)) 0 :=
  w.appendSafe 2 (sqFin_two_ne_zero h)

/-- A completed Diamond/PBW construction makes `Y` right-regular in the actual quadratic
quotient. -/
theorem sqQuadraticQuotient_rightMulY_injective (pbw : SqQuadraticPBW h) :
    Function.Injective (fun a : SqQuadraticAlgebra h =>
      a * sqQuadraticQuotientLetter h 2) :=
  pbw.rightMul_safe_injective 2 (sqFin_two_ne_zero h)

/-- The formal degree-one Fox row inside the quadratic quotient. -/
def sqQuadraticQuotientFoxRow (i : Fin (sqRank h)) : SqQuadraticAlgebra h :=
  sqQuadraticQuotientLetter h (sqInitialPartner h i)

@[simp] theorem sqQuadraticQuotientFoxRow_Y :
    sqQuadraticQuotientFoxRow h 2 = sqQuadraticQuotientLetter h 2 := by
  rw [sqQuadraticQuotientFoxRow, sqInitialPartner_two]

/-- **Connection to the Fox common-annihilator target.**  The PBW theorem for the actual
quadratic quotient kills the common left annihilator of its formal Fox initial row: the `Y`
entry alone suffices. -/
theorem sqQuadraticQuotientFoxRow_commonLeftAnnihilatorFree
    (pbw : SqQuadraticPBW h) :
    RowCommonLeftAnnihilatorFree (sqQuadraticQuotientFoxRow h) := by
  intro a ha
  apply (sqQuadraticQuotient_rightMulY_injective h pbw)
  change a * sqQuadraticQuotientLetter h 2 =
    0 * sqQuadraticQuotientLetter h 2
  rw [zero_mul, ← sqQuadraticQuotientFoxRow_Y h]
  exact ha 2

end

end GQ2.ContCoh

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3CompletedAugmentationPowers

/-!
# The completed Magnus--Labute kernel identity

The completed augmentation-power theorem supplies arbitrary completed coefficients on words in
the improved generator differences.  This file constructs the canonical degree-`n` PBW normal
vector attached to such a coefficient family: first augment every completed coefficient, then
evaluate its word in the quadratic algebra, normalize by the unconditional Diamond theorem, and
retain the degree-`n` normal words.

The exact remaining Magnus--Labute assertion is then a single kernel identity: this normal vector
vanishes exactly when the corresponding completed monomial combination lies in `J^(n+1)`.  The
statement is phrased on the already-surjective monomial presentation of `J^n`, so it is precisely
what is needed to descend normal coefficients to the completed augmentation layer.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2 GQ2.FoxH GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.SqCore

universe uI

/-! ## Recursive words as lists -/

/-- The list underlying a recursive finite generator word. -/
def finiteGeneratorWordList {I : Type uI} :
    ∀ n : ℕ, FiniteGeneratorWord I n → List I
  | 0, _ => []
  | n + 1, w => finiteGeneratorWordList n w.1 ++ [w.2]

@[simp] theorem finiteGeneratorWordList_zero {I : Type uI}
    (w : FiniteGeneratorWord I 0) :
    finiteGeneratorWordList 0 w = [] :=
  rfl

@[simp] theorem finiteGeneratorWordList_succ {I : Type uI}
    (n : ℕ) (w : FiniteGeneratorWord I n) (i : I) :
    finiteGeneratorWordList (n + 1) (w, i) =
      finiteGeneratorWordList n w ++ [i] :=
  rfl

@[simp] theorem finiteGeneratorWordList_length {I : Type uI} :
    ∀ (n : ℕ) (w : FiniteGeneratorWord I n),
      (finiteGeneratorWordList n w).length = n := by
  intro n
  induction n with
  | zero => intro w; rfl
  | succ n ih =>
      rintro ⟨w, i⟩
      simp [ih]

/-- Transporting the certified length of a recursive word does not change its underlying list. -/
theorem finiteGeneratorWordList_cast {I : Type uI} {n m : ℕ}
    (e : n = m) (w : FiniteGeneratorWord I n) :
    finiteGeneratorWordList m (e ▸ w) = finiteGeneratorWordList n w := by
  subst m
  rfl

/-- Every list of length `n` comes from a recursive finite generator word. -/
theorem finiteGeneratorWordList_exists {I : Type uI} :
    ∀ (n : ℕ) (l : List I), l.length = n →
      ∃ w : FiniteGeneratorWord I n, finiteGeneratorWordList n w = l := by
  intro n
  induction n with
  | zero =>
      intro l hl
      have : l = [] := List.eq_nil_of_length_eq_zero hl
      subst l
      exact ⟨PUnit.unit, rfl⟩
  | succ n ih =>
      intro l hl
      have hlne : l ≠ [] := by
        intro e
        subst l
        simp at hl
      let p := l.dropLast
      let i := l.getLast hlne
      have hdecomp : p ++ [i] = l := List.dropLast_append_getLast hlne
      have hp : p.length = n := by
        have hlen := congrArg List.length hdecomp
        simp only [List.length_append, List.length_singleton] at hlen
        omega
      obtain ⟨w, hw⟩ := ih p hp
      refine ⟨(w, i), ?_⟩
      rw [finiteGeneratorWordList_succ, hw, hdecomp]

/-- Recursive word evaluation agrees with the usual list word evaluation. -/
theorem finiteGeneratorWordProduct_eq_quadraticWordEval
    {R : Type*} [Semiring R] {I : Type uI} (g : I → R) :
    ∀ (n : ℕ) (w : FiniteGeneratorWord I n),
      finiteGeneratorWordProduct g n w =
        quadraticWordEval R g (finiteGeneratorWordList n w) := by
  intro n
  induction n with
  | zero => intro w; rfl
  | succ n ih =>
      rintro ⟨w, i⟩
      rw [finiteGeneratorWordProduct_succ, finiteGeneratorWordList_succ,
        quadraticWordEval_append_singleton, ih]

/-! ## PBW normalization of completed monomial coefficients -/

/-- Project the full PBW normal space to its degree-`n` normal words. -/
def sqQuadraticHomogeneousProject (h n : ℕ) :
    SqQuadraticNormalSpace h →ₗ[ZMod 2]
      SqQuadraticHomogeneousNormalSpace h n :=
  Finsupp.lcomapDomain
    (fun w : SqQuadraticHomogeneousNormalWord h n => w.1)
    (fun _ _ e => Subtype.ext e)

@[simp] theorem sqQuadraticHomogeneousProject_apply (h n : ℕ)
    (f : SqQuadraticNormalSpace h) (w : SqQuadraticHomogeneousNormalWord h n) :
    sqQuadraticHomogeneousProject h n f w = f w.1 :=
  rfl

@[simp] theorem sqQuadraticHomogeneousProject_include (h n : ℕ)
    (f : SqQuadraticHomogeneousNormalSpace h n) :
    sqQuadraticHomogeneousProject h n (sqQuadraticHomogeneousInclude h n f) = f := by
  exact Finsupp.leftInverse_lcomapDomain_mapDomain _ _ f

/-- The degree-`n` PBW normal form of an arbitrary word of length `n`. -/
def sqQuadraticWordPBWNormal (h n : ℕ)
    (w : FiniteGeneratorWord (Fin (sqRank h)) n) :
    SqQuadraticHomogeneousNormalSpace h n :=
  sqQuadraticHomogeneousProject h n
    (sqQuadraticNormalRepr h
      (quadraticWordEval (SqQuadraticAlgebra h)
        (sqQuadraticQuotientLetter h) (finiteGeneratorWordList n w)))

/-- Augment the completed coefficient of every length-`n` word and attach the PBW-normalized
homogeneous word vector. -/
def sqCompletedMonomialPBWNormalMap (h n : ℕ) :
    (FiniteGeneratorWord (Fin (sqRank h)) n →
        ModTwoCompletedGroupAlgebra (DSq h : Type)) →ₗ[ZMod 2]
      SqQuadraticHomogeneousNormalSpace h n where
  toFun c := ∑ w,
    modTwoCompletedAugmentationCoordinate (DSq h : Type)
        (sqMagnusOneKernel h) (c w) •
      sqQuadraticWordPBWNormal h n w
  map_add' c d := by
    simp only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
  map_smul' r c := by
    simp only [Pi.smul_apply, map_smul, smul_assoc, RingHom.id_apply,
      Finset.smul_sum]

@[simp] theorem sqCompletedMonomialPBWNormalMap_apply (h n : ℕ)
    (c : FiniteGeneratorWord (Fin (sqRank h)) n →
      ModTwoCompletedGroupAlgebra (DSq h : Type)) :
    sqCompletedMonomialPBWNormalMap h n c = ∑ w,
      modTwoCompletedAugmentationCoordinate (DSq h : Type)
          (sqMagnusOneKernel h) (c w) •
        sqQuadraticWordPBWNormal h n w :=
  rfl

/-! ## The exact remaining identity -/

/-- The degree-`n` completed Magnus--Labute kernel identity.

It says exactly that augmenting completed monomial coefficients and reducing their words to
homogeneous PBW normal form detects the next augmentation power. -/
def SqCompletedMonomialPBWKernelIdentity (h n : ℕ) : Prop :=
  ∀ c : FiniteGeneratorWord (Fin (sqRank h)) n →
      ModTwoCompletedGroupAlgebra (DSq h : Type),
    sqCompletedMonomialPBWNormalMap h n c = 0 ↔
      finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) n c ∈
        modTwoCompletedAugmentationIdeal (DSq h : Type) ^ (n + 1)

/-- The all-degree completed Magnus--Labute identity theorem. -/
def SqCompletedMonomialPBWKernelIdentityAll (h : ℕ) : Prop :=
  ∀ n, SqCompletedMonomialPBWKernelIdentity h n

end

end GQ2.ContCoh

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

/-- The degree-one homogeneous normal word consisting of one marked letter. -/
def sqQuadraticHomogeneousLetter (h : ℕ) (i : Fin (sqRank h)) :
    SqQuadraticHomogeneousNormalWord h 1 :=
  ⟨⟨[i], trivial⟩, rfl⟩

theorem sqQuadraticHomogeneousLetter_injective (h : ℕ) :
    Function.Injective (sqQuadraticHomogeneousLetter h) := by
  intro i j e
  have := congrArg (fun w : SqQuadraticHomogeneousNormalWord h 1 => w.1.1) e
  simpa [sqQuadraticHomogeneousLetter] using this

@[simp] theorem sqQuadraticWordPBWNormal_zero (h : ℕ)
    (w : FiniteGeneratorWord (Fin (sqRank h)) 0) :
    sqQuadraticWordPBWNormal h 0 w =
      Finsupp.single (sqQuadraticHomogeneousEmpty h) 1 := by
  rcases w with ⟨⟩
  change sqQuadraticHomogeneousProject h 0
      (sqQuadraticNormalRepr h
        (quadraticWordEval (SqQuadraticAlgebra h)
          (sqQuadraticQuotientLetter h) [])) = _
  have hr := sqQuadraticNormalRepr_word h (sqQuadraticNormalEmpty h)
  change sqQuadraticNormalRepr h
      (quadraticWordEval (SqQuadraticAlgebra h)
        (sqQuadraticQuotientLetter h) []) = _ at hr
  rw [hr]
  ext v
  by_cases hv : v = sqQuadraticHomogeneousEmpty h
  · subst v
    simp [sqQuadraticHomogeneousProject, sqQuadraticHomogeneousEmpty,
      sqQuadraticNormalEmpty]
  · have hv' : v.1 ≠ sqQuadraticNormalEmpty h := by
      intro e
      apply hv
      exact Subtype.ext e
    simp [sqQuadraticHomogeneousProject, hv, hv']

@[simp] theorem sqQuadraticWordPBWNormal_one (h : ℕ)
    (i : Fin (sqRank h)) :
    sqQuadraticWordPBWNormal h 1 (PUnit.unit, i) =
      Finsupp.single (sqQuadraticHomogeneousLetter h i) 1 := by
  change sqQuadraticHomogeneousProject h 1
      (sqQuadraticNormalRepr h
        (quadraticWordEval (SqQuadraticAlgebra h)
          (sqQuadraticQuotientLetter h) [i])) = _
  have hr := sqQuadraticNormalRepr_word h
    (sqQuadraticHomogeneousLetter h i).1
  change sqQuadraticNormalRepr h
      (quadraticWordEval (SqQuadraticAlgebra h)
        (sqQuadraticQuotientLetter h) [i]) = _ at hr
  rw [hr]
  ext v
  by_cases hv : v = sqQuadraticHomogeneousLetter h i
  · subst v
    simp [sqQuadraticHomogeneousProject]
  · have hv' : v.1 ≠ (sqQuadraticHomogeneousLetter h i).1 := by
      intro e
      apply hv
      exact Subtype.ext e
    simp [sqQuadraticHomogeneousProject, hv]

/-- Every homogeneous normal basis word occurs among the normalized recursive words. -/
theorem sqQuadraticWordPBWNormal_hits_single (h n : ℕ)
    (v : SqQuadraticHomogeneousNormalWord h n) :
    ∃ w : FiniteGeneratorWord (Fin (sqRank h)) n,
      sqQuadraticWordPBWNormal h n w = Finsupp.single v 1 := by
  obtain ⟨w, hw⟩ := finiteGeneratorWordList_exists n v.1.1 v.2
  refine ⟨w, ?_⟩
  rw [sqQuadraticWordPBWNormal, hw,
    sqQuadraticNormalRepr_word h v.1]
  ext u
  by_cases hu : u = v
  · subst u
    simp [sqQuadraticHomogeneousProject]
  · have hu' : u.1 ≠ v.1 := by
      intro e
      apply hu
      exact Subtype.ext e
    simp [sqQuadraticHomogeneousProject, hu]

/-- The explicit PBW-normal map on completed monomial coefficients is onto. -/
theorem sqCompletedMonomialPBWNormalMap_surjective (h n : ℕ) :
    Function.Surjective (sqCompletedMonomialPBWNormalMap h n) := by
  classical
  intro f
  induction f using Finsupp.induction with
  | zero => exact ⟨0, map_zero _⟩
  | single_add v a f hv ha ih =>
      obtain ⟨w, hw⟩ := sqQuadraticWordPBWNormal_hits_single h n v
      obtain ⟨c, hc⟩ := ih
      let d : FiniteGeneratorWord (Fin (sqRank h)) n →
          ModTwoCompletedGroupAlgebra (DSq h : Type) :=
        Pi.single w (a • (1 : ModTwoCompletedGroupAlgebra (DSq h : Type)))
      refine ⟨d + c, ?_⟩
      rw [map_add, hc]
      have hd : sqCompletedMonomialPBWNormalMap h n d = Finsupp.single v a := by
        rw [sqCompletedMonomialPBWNormalMap_apply, Finset.sum_eq_single w]
        · simp [d, hw]
        · intro x hx hxw
          simp [d, hxw]
        · simp
      rw [hd]

/-- Degree zero of the PBW-normal monomial map is ordinary completed augmentation. -/
theorem sqCompletedMonomialPBWNormalMap_zero (h : ℕ)
    (c : FiniteGeneratorWord (Fin (sqRank h)) 0 →
      ModTwoCompletedGroupAlgebra (DSq h : Type)) :
    sqCompletedMonomialPBWNormalMap h 0 c =
      Finsupp.single (sqQuadraticHomogeneousEmpty h)
        (modTwoCompletedAugmentationCoordinate (DSq h : Type)
          (sqMagnusOneKernel h) (c PUnit.unit)) := by
  simp [sqCompletedMonomialPBWNormalMap]

/-- Degree one of the PBW-normal monomial map is the vector of coefficient augmentations. -/
theorem sqCompletedMonomialPBWNormalMap_one (h : ℕ)
    (c : FiniteGeneratorWord (Fin (sqRank h)) 1 →
      ModTwoCompletedGroupAlgebra (DSq h : Type)) :
    sqCompletedMonomialPBWNormalMap h 1 c =
      ∑ i, Finsupp.single (sqQuadraticHomogeneousLetter h i)
        (modTwoCompletedAugmentationCoordinate (DSq h : Type)
          (sqMagnusOneKernel h) (c (PUnit.unit, i))) := by
  rw [sqCompletedMonomialPBWNormalMap_apply]
  change (∑ w : PUnit × Fin (sqRank h), _) = _
  rw [Fintype.sum_prod_type, Fintype.sum_unique]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sqQuadraticWordPBWNormal_one, Finsupp.smul_single_one]

/-- In degree one, PBW-normal vanishing is exactly vanishing of every augmented completed
coefficient. -/
theorem sqCompletedMonomialPBWNormalMap_one_eq_zero_iff (h : ℕ)
    (c : FiniteGeneratorWord (Fin (sqRank h)) 1 →
      ModTwoCompletedGroupAlgebra (DSq h : Type)) :
    sqCompletedMonomialPBWNormalMap h 1 c = 0 ↔
      (fun i => modTwoCompletedAugmentationCoordinate (DSq h : Type)
        (sqMagnusOneKernel h) (c (PUnit.unit, i))) = 0 := by
  classical
  rw [sqCompletedMonomialPBWNormalMap_one]
  constructor
  · intro hz
    funext i
    have hi := congrArg
      (Finsupp.lapply (R := ZMod 2) (M := ZMod 2)
        (sqQuadraticHomogeneousLetter h i)) hz
    simp only [map_sum, map_zero, Finsupp.lapply_apply] at hi
    rw [Finset.sum_eq_single i] at hi
    · simpa using hi
    · intro j hj hji
      simp only [Finsupp.single_apply,
        if_neg ((sqQuadraticHomogeneousLetter_injective h).ne hji)]
    · simp
  · intro hz
    have hi : ∀ i, modTwoCompletedAugmentationCoordinate (DSq h : Type)
        (sqMagnusOneKernel h) (c (PUnit.unit, i)) = 0 := by
      intro i
      exact congrFun hz i
    simp [hi]

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

/-! ## Degree-zero and degree-one regressions -/

/-- The actual first moment of a degree-one recursive monomial combination is the vector of
augmentations of its completed coefficients. -/
theorem sqCompletedFirstMomentMap_finiteGeneratorMonomialMap_one (h : ℕ)
    (c : FiniteGeneratorWord (Fin (sqRank h)) 1 →
      ModTwoCompletedGroupAlgebra (DSq h : Type)) :
    sqCompletedFirstMomentMap h
        (finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) 1 c) =
      fun i => modTwoCompletedAugmentationCoordinate (DSq h : Type)
        (sqMagnusOneKernel h) (c (PUnit.unit, i)) := by
  rw [finiteGeneratorMonomialMap_one]
  simpa [sqCompletedGeneratorDifference] using
    sqCompletedFirstMomentMap_generatorExpansion h
      (fun i => c (PUnit.unit, i))

/-- The completed Magnus--Labute kernel identity is already unconditional in degree zero. -/
theorem sqCompletedMonomialPBWKernelIdentity_zero (h : ℕ) :
    SqCompletedMonomialPBWKernelIdentity h 0 := by
  intro c
  rw [sqCompletedMonomialPBWNormalMap_zero,
    Finsupp.single_eq_zero, finiteGeneratorMonomialMap_zero]
  rw [Submodule.pow_one]
  exact (sqCompletedMagnusDegreeZeroOneExact h).1 (c PUnit.unit)

/-- The completed Magnus--Labute kernel identity is already unconditional in degree one. -/
theorem sqCompletedMonomialPBWKernelIdentity_one (h : ℕ) :
    SqCompletedMonomialPBWKernelIdentity h 1 := by
  intro c
  rw [sqCompletedMonomialPBWNormalMap_one_eq_zero_iff,
    ← sqCompletedFirstMomentMap_finiteGeneratorMonomialMap_one]
  have hx : finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) 1 c ∈
      modTwoCompletedAugmentationIdeal (DSq h : Type) := by
    simpa only [Submodule.pow_one] using finiteGeneratorMonomialMap_mem_idealPower
      (modTwoCompletedAugmentationIdeal (DSq h : Type))
      (sqCompletedGeneratorDifference h)
      (sqCompletedGeneratorDifference_mem h) 1 c
  simpa using (sqCompletedMagnusDegreeZeroOneExact h).2.2
    (finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) 1 c) hx

/-! ## Descent to the completed augmentation layers -/

/-- The kernel identity makes the kernel of the monomial presentation lie in the kernel of
PBW normalization. -/
theorem sqCompletedGeneratorMonomial_ker_le_PBWNormal_ker
    (h n : ℕ) (H : SqCompletedMonomialPBWKernelIdentity h n) :
    LinearMap.ker (sqCompletedGeneratorMonomialToAugmentationPower h n) ≤
      LinearMap.ker (sqCompletedMonomialPBWNormalMap h n) := by
  intro c hc
  rw [LinearMap.mem_ker] at hc ⊢
  apply (H c).2
  have hcval := congrArg Subtype.val hc
  change finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) n c = 0 at hcval
  rw [hcval]
  exact Ideal.zero_mem _

/-- Descend PBW-normal monomial coefficients through the surjective presentation of `J^n`. -/
def sqCompletedMagnusNormalCoefficient (h n : ℕ)
    (H : SqCompletedMonomialPBWKernelIdentity h n) :
    (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ n).toAddSubgroup →ₗ[ZMod 2]
      SqQuadraticHomogeneousNormalSpace h n :=
  let q := sqCompletedGeneratorMonomialToAugmentationPower h n
  let p := sqCompletedMonomialPBWNormalMap h n
  (LinearMap.ker q).liftQ p
      (sqCompletedGeneratorMonomial_ker_le_PBWNormal_ker h n H) ∘ₗ
    (q.quotKerEquivOfSurjective
      (sqCompletedGeneratorMonomialToAugmentationPower_surjective h n)).symm.toLinearMap

/-- The descended coefficient map agrees with explicit PBW normalization on every monomial
coefficient family. -/
theorem sqCompletedMagnusNormalCoefficient_monomial
    (h n : ℕ) (H : SqCompletedMonomialPBWKernelIdentity h n)
    (c : FiniteGeneratorWord (Fin (sqRank h)) n →
      ModTwoCompletedGroupAlgebra (DSq h : Type)) :
    sqCompletedMagnusNormalCoefficient h n H
        (sqCompletedGeneratorMonomialToAugmentationPower h n c) =
      sqCompletedMonomialPBWNormalMap h n c := by
  rw [sqCompletedMagnusNormalCoefficient]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-- The descended normal coefficient map remains onto. -/
theorem sqCompletedMagnusNormalCoefficient_surjective
    (h n : ℕ) (H : SqCompletedMonomialPBWKernelIdentity h n) :
    Function.Surjective (sqCompletedMagnusNormalCoefficient h n H) := by
  intro y
  obtain ⟨c, hc⟩ := sqCompletedMonomialPBWNormalMap_surjective h n y
  refine ⟨sqCompletedGeneratorMonomialToAugmentationPower h n c, ?_⟩
  rw [sqCompletedMagnusNormalCoefficient_monomial, hc]

/-- The kernel of the descended normal coefficient map is exactly `J^(n+1)`. -/
theorem sqCompletedMagnusNormalCoefficient_eq_zero_iff
    (h n : ℕ) (H : SqCompletedMonomialPBWKernelIdentity h n)
    (a : (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ n).toAddSubgroup) :
    sqCompletedMagnusNormalCoefficient h n H a = 0 ↔
      a.1 ∈ modTwoCompletedAugmentationIdeal (DSq h : Type) ^ (n + 1) := by
  obtain ⟨c, hc⟩ :=
    sqCompletedGeneratorMonomialToAugmentationPower_surjective h n a
  subst a
  rw [sqCompletedMagnusNormalCoefficient_monomial, H c]
  change finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) n c ∈
      modTwoCompletedAugmentationIdeal (DSq h : Type) ^ (n + 1) ↔
    finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) n c ∈
      modTwoCompletedAugmentationIdeal (DSq h : Type) ^ (n + 1)
  rfl

/-- In degree zero, the descended coefficient of one is the empty normal word. -/
theorem sqCompletedMagnusNormalCoefficient_one (h : ℕ) :
    sqCompletedMagnusNormalCoefficient h 0
        (sqCompletedMonomialPBWKernelIdentity_zero h)
        ⟨1, by
          rw [Submodule.pow_zero, Ideal.one_eq_top]
          exact Set.mem_univ 1⟩ =
      Finsupp.single (sqQuadraticHomogeneousEmpty h) 1 := by
  let c : FiniteGeneratorWord (Fin (sqRank h)) 0 →
      ModTwoCompletedGroupAlgebra (DSq h : Type) := fun _ => 1
  have hc : sqCompletedGeneratorMonomialToAugmentationPower h 0 c =
      ⟨1, by
        rw [Submodule.pow_zero, Ideal.one_eq_top]
        exact Set.mem_univ 1⟩ := by
    apply Subtype.ext
    simp [sqCompletedGeneratorMonomialToAugmentationPower, c,
      finiteGeneratorMonomialToIdealPower, finiteGeneratorMonomialMap]
  rw [← hc, sqCompletedMagnusNormalCoefficient_monomial,
    sqCompletedMonomialPBWNormalMap_zero]
  simp [c]

end

end GQ2.ContCoh

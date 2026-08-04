/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3CompletedMagnusPropagation

/-!
# The finite cubic Magnus matrix

The quadratic detector campaign settles `J²/J³`, but those detector moments are quadratic
functions and therefore vanish already on `J³`; they contain no information about `J³/J⁴`.
This file isolates the first genuinely cubic calculation as a finite matrix problem.

Both the source (length-three words in the finite improved alphabet) and the PBW target
(normal length-three words avoiding `X S`) are finite-dimensional over `𝔽₂`.  There are two
explicit linear maps out of the source:

* cubic PBW normalization;
* evaluation in the completed group algebra, followed by reduction modulo `J⁴`.

A `SqCompletedCubicPBWMatrixCertificate` is an injective matrix from cubic PBW normal
coordinates to the completed `J³/J⁴` truncation whose columns commute with these two maps.
Thus it separates only the finitely many normal cubic columns.  The main theorem proves that
this finite full-column-rank calculation is equivalent to the cubic Magnus--Labute identity.
The final regression records every column explicitly on a length-three word.

The natural next implementation is a finite algebra-group detector: use the units `1+N` in
the degree-`<4` noncommutative Magnus algebra quotiented by the *inhomogeneous* literal relator
expansion.  Quotienting only by the quadratic initial form is insufficient because the literal
relator has a nonzero cubic correction.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2 GQ2.FoxH GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.SqCore

/-! ## Finiteness of the normal-word matrix index -/

/-- Forget normality but retain the certified length of a homogeneous normal word. -/
def sqQuadraticHomogeneousNormalWordToVector (h n : ℕ) :
    SqQuadraticHomogeneousNormalWord h n → List.Vector (Fin (sqRank h)) n :=
  fun w => ⟨w.1.1, w.2⟩

theorem sqQuadraticHomogeneousNormalWordToVector_injective (h n : ℕ) :
    Function.Injective (sqQuadraticHomogeneousNormalWordToVector h n) := by
  intro u v huv
  have hl : u.1.1 = v.1.1 :=
    congrArg (fun z : List.Vector (Fin (sqRank h)) n => z.1) huv
  apply Subtype.ext
  apply Subtype.ext
  exact hl

/-- Homogeneous PBW-normal words form a finite index set. -/
instance sqQuadraticHomogeneousNormalWord_finite (h n : ℕ) :
    Finite (SqQuadraticHomogeneousNormalWord h n) :=
  Finite.of_injective (sqQuadraticHomogeneousNormalWordToVector h n)
    (sqQuadraticHomogeneousNormalWordToVector_injective h n)

noncomputable instance sqQuadraticHomogeneousNormalWord_fintype (h n : ℕ) :
    Fintype (SqQuadraticHomogeneousNormalWord h n) :=
  Fintype.ofFinite _

instance sqQuadraticHomogeneousNormalSpace_finiteDimensional (h n : ℕ) :
    FiniteDimensional (ZMod 2) (SqQuadraticHomogeneousNormalSpace h n) := by
  infer_instance

/-! ## Scalar cubic maps -/

/-- Replace each completed cubic coefficient by its scalar augmentation. -/
def sqCompletedCubicScalarizedCoefficient (h : ℕ)
    (c : FiniteGeneratorWord (Fin (sqRank h)) 3 →
      ModTwoCompletedGroupAlgebra (DSq h : Type)) :
    FiniteGeneratorWord (Fin (sqRank h)) 3 →
      ModTwoCompletedGroupAlgebra (DSq h : Type) :=
  fun w => modTwoCompletedAugmentationCoordinate (DSq h : Type)
    (sqMagnusOneKernel h) (c w) • 1

@[simp] theorem sqCompletedCubicScalarizedCoefficient_augmentation
    (h : ℕ)
    (c : FiniteGeneratorWord (Fin (sqRank h)) 3 →
      ModTwoCompletedGroupAlgebra (DSq h : Type))
    (w : FiniteGeneratorWord (Fin (sqRank h)) 3) :
    modTwoCompletedAugmentationCoordinate (DSq h : Type)
        (sqMagnusOneKernel h)
        (sqCompletedCubicScalarizedCoefficient h c w) =
      modTwoCompletedAugmentationCoordinate (DSq h : Type)
        (sqMagnusOneKernel h) (c w) := by
  simp [sqCompletedCubicScalarizedCoefficient]

/-- Scalar cubic PBW normalization as a finite linear matrix. -/
def sqCubicScalarPBWNormalMap (h : ℕ) :
    (FiniteGeneratorWord (Fin (sqRank h)) 3 → ZMod 2) →ₗ[ZMod 2]
      SqQuadraticHomogeneousNormalSpace h 3 where
  toFun a := ∑ w, a w • sqQuadraticWordPBWNormal h 3 w
  map_add' a b := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r a := by
    simp only [Pi.smul_apply, smul_assoc, RingHom.id_apply, Finset.smul_sum]

@[simp] theorem sqCubicScalarPBWNormalMap_apply (h : ℕ)
    (a : FiniteGeneratorWord (Fin (sqRank h)) 3 → ZMod 2) :
    sqCubicScalarPBWNormalMap h a =
      ∑ w, a w • sqQuadraticWordPBWNormal h 3 w :=
  rfl

/-- A scalar cubic word combination in the completed group algebra. -/
def sqCompletedCubicScalarMonomial (h : ℕ)
    (a : FiniteGeneratorWord (Fin (sqRank h)) 3 → ZMod 2) :
    ModTwoCompletedGroupAlgebra (DSq h : Type) :=
  finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) 3
    (fun w => a w • 1)

/-- The scalar cubic word map, before quotienting by `J⁴`. -/
def sqCompletedCubicScalarMonomialMap (h : ℕ) :
    (FiniteGeneratorWord (Fin (sqRank h)) 3 → ZMod 2) →ₗ[ZMod 2]
      ModTwoCompletedGroupAlgebra (DSq h : Type) where
  toFun := sqCompletedCubicScalarMonomial h
  map_add' a b := by
    change finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) 3
        (fun w => (a w + b w) • 1) =
      finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) 3
          (fun w => a w • 1) +
        finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) 3
          (fun w => b w • 1)
    rw [show (fun w => (a w + b w) •
        (1 : ModTwoCompletedGroupAlgebra (DSq h : Type))) =
      (fun w => a w • 1) + (fun w => b w • 1) by
        funext w
        exact add_smul (a w) (b w) 1, map_add]
  map_smul' r a := by
    change finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) 3
        (fun w => (r * a w) • 1) =
      r • finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) 3
        (fun w => a w • 1)
    have heq : (fun w => (r * a w) •
        (1 : ModTwoCompletedGroupAlgebra (DSq h : Type))) =
      (algebraMap (ZMod 2) (ModTwoCompletedGroupAlgebra (DSq h : Type)) r) •
        (fun w => a w • 1) := by
      funext w
      simp [Algebra.smul_def]
    rw [heq, map_smul]
    simp [Algebra.smul_def]

/-- The completed group algebra truncated immediately after cubic order. -/
abbrev SqCompletedCubicTruncation (h : ℕ) :=
  ModTwoCompletedGroupAlgebra (DSq h : Type) ⧸
    (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 4)

/-- Evaluate scalar cubic words in the completed algebra modulo `J⁴`. -/
def sqCompletedCubicScalarTruncationMap (h : ℕ) :
    (FiniteGeneratorWord (Fin (sqRank h)) 3 → ZMod 2) →ₗ[ZMod 2]
      SqCompletedCubicTruncation h :=
  (Ideal.Quotient.mkₐ (ZMod 2)
      (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 4)).toLinearMap.comp
    (sqCompletedCubicScalarMonomialMap h)

@[simp] theorem sqCompletedCubicScalarTruncationMap_apply (h : ℕ)
    (a : FiniteGeneratorWord (Fin (sqRank h)) 3 → ZMod 2) :
    sqCompletedCubicScalarTruncationMap h a =
      Ideal.Quotient.mk
        (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 4)
        (sqCompletedCubicScalarMonomial h a) :=
  rfl

/-- The finite scalar cubic kernel calculation. -/
def SqCompletedCubicScalarKernelExact (h : ℕ) : Prop :=
  ∀ a : FiniteGeneratorWord (Fin (sqRank h)) 3 → ZMod 2,
    sqCubicScalarPBWNormalMap h a = 0 ↔
      sqCompletedCubicScalarMonomial h a ∈
        modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 4

/-! ## Scalarization reduces the full cubic theorem to the finite matrix -/

/-- Scalarizing completed coefficients in a cubic monomial changes its value only in `J⁴`. -/
theorem sqCompletedCubicMonomial_sub_scalarized_mem_fourth (h : ℕ)
    (c : FiniteGeneratorWord (Fin (sqRank h)) 3 →
      ModTwoCompletedGroupAlgebra (DSq h : Type)) :
    finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) 3 c -
        finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) 3
          (sqCompletedCubicScalarizedCoefficient h c) ∈
      modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 4 := by
  let J := modTwoCompletedAugmentationIdeal (DSq h : Type)
  rw [← map_sub, finiteGeneratorMonomialMap_apply]
  apply Ideal.sum_mem
  intro w hw
  change (c w - sqCompletedCubicScalarizedCoefficient h c w) *
      finiteGeneratorWordProduct (sqCompletedGeneratorDifference h) 3 w ∈ J ^ 4
  rw [show 4 = 1 + 3 by omega, Submodule.pow_add J (by omega : 3 ≠ 0),
    Submodule.pow_one]
  exact Ideal.mul_mem_mul
    (sqCompletedCoefficient_sub_augmentationScalar_mem h (c w))
    (finiteGeneratorWordProduct_mem_idealPower J
      (sqCompletedGeneratorDifference h)
      (sqCompletedGeneratorDifference_mem h) 3 w)

/-- PBW normalization sees only the scalar augmentation of each completed coefficient. -/
theorem sqCompletedMonomialPBWNormalMap_three_eq_scalar (h : ℕ)
    (c : FiniteGeneratorWord (Fin (sqRank h)) 3 →
      ModTwoCompletedGroupAlgebra (DSq h : Type)) :
    sqCompletedMonomialPBWNormalMap h 3 c =
      sqCubicScalarPBWNormalMap h
        (fun w => modTwoCompletedAugmentationCoordinate (DSq h : Type)
          (sqMagnusOneKernel h) (c w)) := by
  rw [sqCompletedMonomialPBWNormalMap_apply, sqCubicScalarPBWNormalMap_apply]

/-- The full cubic completed kernel identity is equivalent to the finite scalar cubic
calculation. -/
theorem sqCompletedMonomialPBWKernelIdentity_three_iff_scalar (h : ℕ) :
    SqCompletedMonomialPBWKernelIdentity h 3 ↔
      SqCompletedCubicScalarKernelExact h := by
  constructor
  · intro H a
    let c : FiniteGeneratorWord (Fin (sqRank h)) 3 →
        ModTwoCompletedGroupAlgebra (DSq h : Type) := fun w => a w • 1
    have hnormal := sqCompletedMonomialPBWNormalMap_three_eq_scalar h c
    have hnormal' : sqCompletedMonomialPBWNormalMap h 3 c =
        sqCubicScalarPBWNormalMap h a := by
      simpa [c] using hnormal
    rw [← hnormal']
    simpa [c, sqCompletedCubicScalarMonomial] using H c
  · intro H c
    let a : FiniteGeneratorWord (Fin (sqRank h)) 3 → ZMod 2 := fun w =>
      modTwoCompletedAugmentationCoordinate (DSq h : Type)
        (sqMagnusOneKernel h) (c w)
    let c₀ := sqCompletedCubicScalarizedCoefficient h c
    have hnormal : sqCompletedMonomialPBWNormalMap h 3 c =
        sqCubicScalarPBWNormalMap h a := by
      exact sqCompletedMonomialPBWNormalMap_three_eq_scalar h c
    have hscalar : sqCompletedCubicScalarMonomial h a =
        finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) 3 c₀ := by
      rfl
    have hdiff := sqCompletedCubicMonomial_sub_scalarized_mem_fourth h c
    rw [hnormal, H a, hscalar]
    change finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) 3 c₀ ∈
        modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 4 ↔
      finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) 3 c ∈
        modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 4
    constructor
    · intro hc₀
      have := (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 4).add_mem hdiff hc₀
      simpa only [c₀, sub_add_cancel] using this
    · intro hc
      have := (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 4).sub_mem hc hdiff
      simpa only [c₀, sub_sub_cancel] using this

/-! ## The finite PBW matrix certificate -/

/-- Scalar cubic PBW normalization is onto the normal cubic coordinate space. -/
theorem sqCubicScalarPBWNormalMap_surjective (h : ℕ) :
    Function.Surjective (sqCubicScalarPBWNormalMap h) := by
  classical
  intro f
  induction f using Finsupp.induction with
  | zero => exact ⟨0, map_zero _⟩
  | single_add v a f hv ha ih =>
      obtain ⟨w, hw⟩ := sqQuadraticWordPBWNormal_hits_single h 3 v
      obtain ⟨c, hc⟩ := ih
      let d : FiniteGeneratorWord (Fin (sqRank h)) 3 → ZMod 2 := Pi.single w a
      refine ⟨d + c, ?_⟩
      rw [map_add, hc]
      have hd : sqCubicScalarPBWNormalMap h d = Finsupp.single v a := by
        rw [sqCubicScalarPBWNormalMap_apply, Finset.sum_eq_single w]
        · simp [d, hw]
        · intro x hx hxw
          simp [d, hxw]
        · simp
      rw [hd]

/-- A finite matrix certificate for cubic exactness.  `commutes` gives the finitely many
column equations (one per marked cubic word); `fullColumnRank` is separation of the normal
cubic columns modulo `J⁴`. -/
structure SqCompletedCubicPBWMatrixCertificate (h : ℕ) where
  matrix : SqQuadraticHomogeneousNormalSpace h 3 →ₗ[ZMod 2]
    SqCompletedCubicTruncation h
  commutes : matrix.comp (sqCubicScalarPBWNormalMap h) =
    sqCompletedCubicScalarTruncationMap h
  fullColumnRank : Function.Injective matrix

/-- A matrix certificate gives the scalar cubic kernel calculation. -/
theorem SqCompletedCubicPBWMatrixCertificate.scalarKernelExact
    {h : ℕ} (C : SqCompletedCubicPBWMatrixCertificate h) :
    SqCompletedCubicScalarKernelExact h := by
  intro a
  have hcomm := LinearMap.congr_fun C.commutes a
  change C.matrix (sqCubicScalarPBWNormalMap h a) =
    sqCompletedCubicScalarTruncationMap h a at hcomm
  constructor
  · intro hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← sqCompletedCubicScalarTruncationMap_apply, ← hcomm, hp, map_zero]
  · intro hm
    apply C.fullColumnRank
    rw [map_zero, hcomm, sqCompletedCubicScalarTruncationMap_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hm

/-- The finite cubic matrix induced by a scalar kernel calculation. -/
def sqCompletedCubicPBWMatrixOfScalarKernelExact
    (h : ℕ) (H : SqCompletedCubicScalarKernelExact h) :
    SqQuadraticHomogeneousNormalSpace h 3 →ₗ[ZMod 2]
      SqCompletedCubicTruncation h :=
  let p := sqCubicScalarPBWNormalMap h
  let m := sqCompletedCubicScalarTruncationMap h
  let hker : LinearMap.ker p ≤ LinearMap.ker m := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (H a).1 ha
  (LinearMap.ker p).liftQ m hker ∘ₗ
    (p.quotKerEquivOfSurjective
      (sqCubicScalarPBWNormalMap_surjective h)).symm.toLinearMap

/-- The induced matrix has the required cubic word columns. -/
theorem sqCompletedCubicPBWMatrixOfScalarKernelExact_commutes
    (h : ℕ) (H : SqCompletedCubicScalarKernelExact h) :
    (sqCompletedCubicPBWMatrixOfScalarKernelExact h H).comp
        (sqCubicScalarPBWNormalMap h) =
      sqCompletedCubicScalarTruncationMap h := by
  ext a
  rw [sqCompletedCubicPBWMatrixOfScalarKernelExact]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-- Exactness forces the induced cubic PBW matrix to have full column rank. -/
theorem sqCompletedCubicPBWMatrixOfScalarKernelExact_injective
    (h : ℕ) (H : SqCompletedCubicScalarKernelExact h) :
    Function.Injective (sqCompletedCubicPBWMatrixOfScalarKernelExact h H) := by
  intro x y hxy
  have hz : sqCompletedCubicPBWMatrixOfScalarKernelExact h H (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨a, ha⟩ := sqCubicScalarPBWNormalMap_surjective h (x - y)
  have hm : sqCompletedCubicScalarTruncationMap h a = 0 := by
    rw [← sqCompletedCubicPBWMatrixOfScalarKernelExact_commutes h H,
      LinearMap.comp_apply, ha]
    exact hz
  have hmem : sqCompletedCubicScalarMonomial h a ∈
      modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 4 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mp hm
  have hp : sqCubicScalarPBWNormalMap h a = 0 := (H a).2 hmem
  apply sub_eq_zero.mp
  rw [← ha, hp]

/-- Package the matrix supplied by scalar cubic exactness. -/
def sqCompletedCubicPBWMatrixCertificateOfScalarKernelExact
    (h : ℕ) (H : SqCompletedCubicScalarKernelExact h) :
    SqCompletedCubicPBWMatrixCertificate h where
  matrix := sqCompletedCubicPBWMatrixOfScalarKernelExact h H
  commutes := sqCompletedCubicPBWMatrixOfScalarKernelExact_commutes h H
  fullColumnRank := sqCompletedCubicPBWMatrixOfScalarKernelExact_injective h H

/-- **Exact finite reduction.**  The cubic Magnus--Labute identity is equivalent to existence
of the finite PBW matrix with its explicit columns and full column rank. -/
theorem sqCompletedMonomialPBWKernelIdentity_three_iff_matrix (h : ℕ) :
    SqCompletedMonomialPBWKernelIdentity h 3 ↔
      Nonempty (SqCompletedCubicPBWMatrixCertificate h) := by
  rw [sqCompletedMonomialPBWKernelIdentity_three_iff_scalar]
  constructor
  · intro H
    exact ⟨sqCompletedCubicPBWMatrixCertificateOfScalarKernelExact h H⟩
  · rintro ⟨C⟩
    exact C.scalarKernelExact

/-- Column regression: on every marked cubic word, the certified matrix sends its PBW-normal
column to the literal completed cubic monomial modulo `J⁴`. -/
theorem SqCompletedCubicPBWMatrixCertificate.wordColumn
    {h : ℕ} (C : SqCompletedCubicPBWMatrixCertificate h)
    (w : FiniteGeneratorWord (Fin (sqRank h)) 3) :
    C.matrix (sqQuadraticWordPBWNormal h 3 w) =
      Ideal.Quotient.mk
        (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 4)
        (finiteGeneratorWordProduct (sqCompletedGeneratorDifference h) 3 w) := by
  classical
  let e : FiniteGeneratorWord (Fin (sqRank h)) 3 → ZMod 2 := Pi.single w 1
  have hcomm := LinearMap.congr_fun C.commutes e
  change C.matrix (sqCubicScalarPBWNormalMap h e) =
    sqCompletedCubicScalarTruncationMap h e at hcomm
  have hePBW : sqCubicScalarPBWNormalMap h e =
      sqQuadraticWordPBWNormal h 3 w := by
    rw [sqCubicScalarPBWNormalMap_apply, Finset.sum_eq_single w]
    · simp [e]
    · intro v hv hvw
      simp [e, hvw]
    · simp
  have heActual : sqCompletedCubicScalarTruncationMap h e =
      Ideal.Quotient.mk
        (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 4)
        (finiteGeneratorWordProduct (sqCompletedGeneratorDifference h) 3 w) := by
    rw [sqCompletedCubicScalarTruncationMap_apply,
      sqCompletedCubicScalarMonomial, finiteGeneratorMonomialMap_apply,
      Finset.sum_eq_single w]
    · simp [e]
    · intro v hv hvw
      simp [e, hvw]
    · simp
  rwa [hePBW, heActual] at hcomm

end

end GQ2.ContCoh

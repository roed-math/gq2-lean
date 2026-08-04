/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3CompletedMagnusKernelIdentity

/-!
# Degree-two detector quotients for the completed square presentation

This file constructs the finite two-step quotients which replace the full free completed
Magnus theorem in degrees at most two.  An arbitrary bilinear form on the elementary abelian
generator space defines a central extension.  If the form kills the certified quadratic
initial relator, the actual `DSq` presentation maps to that extension.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SqCore Multiplicative

/-- The elementary abelian generator space used by all quadratic detectors. -/
abbrev SqQuadraticDetectorBase (h : ℕ) :=
  Multiplicative (Fin (sqRank h) → ZMod 2)

/-- The bilinear cocycle attached to a matrix of quadratic coefficients. -/
def sqQuadraticDetectorCocycle (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2) :
    GQ2.DRCoh.TwoCocycle (SqQuadraticDetectorBase h) where
  κ p q := ∑ i, ∑ j, toAdd p i * toAdd q j * κ i j
  norm := by simp
  cocyc p q r := by
    simp only [toAdd_mul, Pi.add_apply, add_mul, mul_add,
      Finset.sum_add_distrib]
    ring

/-- The detector cocycle is a cup cocycle on the elementary abelian base. -/
theorem sqQuadraticDetectorCocycle_isCup (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2) :
    IsCupCocycle (sqQuadraticDetectorCocycle h κ) where
  comm p q := by
    apply toAdd.injective
    exact add_comm _ _
  expTwo p := by
    apply toAdd.injective
    simp only [toAdd_mul, toAdd_one]
    funext i
    exact CharTwo.add_self_eq_zero (toAdd p i)
  addLeft p q r := by
    simp [sqQuadraticDetectorCocycle, add_mul, Finset.sum_add_distrib]
  addRight p q r := by
    simp only [sqQuadraticDetectorCocycle, toAdd_mul, Pi.add_apply, mul_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring

/-- On marked basis vectors, the detector cocycle reads the chosen matrix entry. -/
@[simp] theorem sqQuadraticDetectorCocycle_mark (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2)
    (i j : Fin (sqRank h)) :
    (sqQuadraticDetectorCocycle h κ).κ
        (sqMagnusOneMark h i) (sqMagnusOneMark h j) = κ i j := by
  classical
  simp [sqQuadraticDetectorCocycle, sqMagnusOneMark, Pi.single_apply]

/-- The square relator dies in the elementary abelian detector base. -/
theorem sqMagnusOneMark_relator_eq_one (h : ℕ) :
    sqRelWord (sqMagnusOneMark h) = 1 := by
  rw [sqRelWord_comm]
  have hsq (z : SqQuadraticDetectorBase h) : z ^ 2 = 1 := by
    apply toAdd.injective
    simp only [pow_two, toAdd_mul, toAdd_one]
    funext i
    exact CharTwo.add_self_eq_zero (toAdd z i)
  rw [show 4 = 2 * 2 by omega, pow_mul, hsq, hsq]
  simp

/-- If a bilinear form annihilates the certified initial relator, its offset-zero central
extension marking satisfies the actual square relator. -/
theorem sqQuadraticDetector_relator_eq_one (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2)
    (hκ : sqRelatorQuadraticInitialGram h κ = 0) :
    sqRelWord (fun i => GQ2.Dyadic.MarkedCore.centLift
      (sqQuadraticDetectorCocycle h κ) (sqMagnusOneMark h i)) = 1 := by
  apply GQ2.DRCoh.CentExt.ext
  · have hmap := map_sqRelWord
      (GQ2.DRCoh.CentExt.proj (sqQuadraticDetectorCocycle h κ))
      (fun i => GQ2.Dyadic.MarkedCore.centLift
        (sqQuadraticDetectorCocycle h κ) (sqMagnusOneMark h i))
    change (GQ2.DRCoh.CentExt.proj (sqQuadraticDetectorCocycle h κ))
      (sqRelWord (fun i => GQ2.Dyadic.MarkedCore.centLift
        (sqQuadraticDetectorCocycle h κ) (sqMagnusOneMark h i))) = 1
    rw [hmap]
    exact sqMagnusOneMark_relator_eq_one h
  · rw [sqRelWord_centLift_fib_eq_quadraticInitialGram
      (sqQuadraticDetectorCocycle_isCup h κ)]
    simpa using hκ

/-- Every element of a quadratic detector central extension has fourth power one. -/
theorem sqQuadraticDetector_pow_four_eq_one (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2)
    (p : GQ2.DRCoh.CentExt (sqQuadraticDetectorCocycle h κ)) :
    p ^ 4 = 1 := by
  apply GQ2.DRCoh.CentExt.ext
  · change (p.base ^ 4) = 1
    have hsq : p.base ^ 2 = 1 := by
      apply toAdd.injective
      simp only [pow_two, toAdd_mul, toAdd_one]
      funext i
      exact CharTwo.add_self_eq_zero (toAdd p.base i)
    rw [show 4 = 2 * 2 by omega, pow_mul, hsq, one_pow]
  · change (p ^ 4).fib = (0 : ZMod 2)
    rw [show 4 = 2 * 2 by omega, pow_mul, pow_two,
      GQ2.DRCoh.CentExt.mul_fib]
    change (p ^ 2).fib + (p ^ 2).fib +
      (sqQuadraticDetectorCocycle h κ).κ (p ^ 2).base (p ^ 2).base = 0
    have hbase : (p ^ 2).base = 1 := by
      change p.base ^ 2 = 1
      apply toAdd.injective
      simp only [pow_two, toAdd_mul, toAdd_one]
      funext i
      exact CharTwo.add_self_eq_zero (toAdd p.base i)
    rw [hbase, (sqQuadraticDetectorCocycle h κ).κ_one_left]
    simpa only [add_zero] using
      (CharTwo.add_self_eq_zero (p ^ 2).fib)

/-- A detector central extension is a finite pro-`2` group. -/
theorem sqQuadraticDetector_isProP (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2) :
    IsProP 2 (GQ2.DRCoh.CentExt (sqQuadraticDetectorCocycle h κ)) := by
  apply isProP_of_isPGroup
  intro p
  exact ⟨2, by simpa using sqQuadraticDetector_pow_four_eq_one h κ p⟩

/-- The presentation map from `DSq` to a quadratic detector whose form kills the certified
initial relator. -/
def sqQuadraticDetectorHom (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2)
    (hκ : sqRelatorQuadraticInitialGram h κ = 0) :
    ContinuousMonoidHom (DSq h : Type)
      (GQ2.DRCoh.CentExt (sqQuadraticDetectorCocycle h κ)) :=
  sqLiftHom h (sqQuadraticDetector_isProP h κ)
    (fun i => GQ2.Dyadic.MarkedCore.centLift
      (sqQuadraticDetectorCocycle h κ) (sqMagnusOneMark h i))
    (sqQuadraticDetector_relator_eq_one h κ hκ)

@[simp] theorem sqQuadraticDetectorHom_gen (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2)
    (hκ : sqRelatorQuadraticInitialGram h κ = 0)
    (i : Fin (sqRank h)) :
    sqQuadraticDetectorHom h κ hκ (sqGen h i) =
      GQ2.Dyadic.MarkedCore.centLift
        (sqQuadraticDetectorCocycle h κ) (sqMagnusOneMark h i) := by
  exact sqLiftHom_gen h (sqQuadraticDetector_isProP h κ)
    (fun i => GQ2.Dyadic.MarkedCore.centLift
      (sqQuadraticDetectorCocycle h κ) (sqMagnusOneMark h i))
    (sqQuadraticDetector_relator_eq_one h κ hκ) i

/-! ## The finite detector coordinate -/

/-- The open normal kernel of a quadratic detector. -/
def sqQuadraticDetectorKernel (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2)
    (hκ : sqRelatorQuadraticInitialGram h κ = 0) :
    OpenNormalSubgroup (DSq h : Type) where
  toSubgroup := (sqQuadraticDetectorHom h κ hκ).toMonoidHom.ker
  isOpen' := by
    exact (isOpen_discrete ({1} : Set
      (GQ2.DRCoh.CentExt (sqQuadraticDetectorCocycle h κ)))).preimage
        (sqQuadraticDetectorHom h κ hκ).continuous_toFun

/-- The faithful map from the finite detector coordinate into its central extension. -/
def sqQuadraticDetectorQuotientHom (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2)
    (hκ : sqRelatorQuadraticInitialGram h κ = 0) :
    ((DSq h : Type) ⧸ (sqQuadraticDetectorKernel h κ hκ).toSubgroup) →*
      GQ2.DRCoh.CentExt (sqQuadraticDetectorCocycle h κ) :=
  QuotientGroup.lift (sqQuadraticDetectorKernel h κ hκ).toSubgroup
    (sqQuadraticDetectorHom h κ hκ).toMonoidHom (by
      change (sqQuadraticDetectorHom h κ hκ).toMonoidHom.ker ≤
        (sqQuadraticDetectorHom h κ hκ).toMonoidHom.ker
      exact le_rfl)

@[simp] theorem sqQuadraticDetectorQuotientHom_mk_gen (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2)
    (hκ : sqRelatorQuadraticInitialGram h κ = 0)
    (i : Fin (sqRank h)) :
    sqQuadraticDetectorQuotientHom h κ hκ
        (QuotientGroup.mk' (sqQuadraticDetectorKernel h κ hκ).toSubgroup
          (sqGen h i)) =
      GQ2.Dyadic.MarkedCore.centLift
        (sqQuadraticDetectorCocycle h κ) (sqMagnusOneMark h i) := by
  change sqQuadraticDetectorHom h κ hκ (sqGen h i) = _
  exact sqQuadraticDetectorHom_gen h κ hκ i

/-! ## Fibre-coordinate moments -/

/-- The additive moment on a group algebra obtained by weighting each group element by a
function. -/
def modTwoGroupAlgebraFunctionMoment {Q : Type} [Group Q] (f : Q → ZMod 2) :
    MonoidAlgebra (ZMod 2) Q →+ ZMod 2 :=
  MonoidAlgebra.liftNC (AddMonoidHom.id (ZMod 2)) f

@[simp] theorem modTwoGroupAlgebraFunctionMoment_single {Q : Type} [Group Q]
    (f : Q → ZMod 2) (q : Q) (a : ZMod 2) :
    modTwoGroupAlgebraFunctionMoment f (MonoidAlgebra.single q a) = a * f q := by
  exact MonoidAlgebra.liftNC_single _ _ q a

/-- Function moments are linear over the coefficient field. -/
theorem modTwoGroupAlgebraFunctionMoment_smul {Q : Type} [Group Q]
    (f : Q → ZMod 2) (a : ZMod 2) (x : MonoidAlgebra (ZMod 2) Q) :
    modTwoGroupAlgebraFunctionMoment f (a • x) =
      a * modTwoGroupAlgebraFunctionMoment f x := by
  induction x using MonoidAlgebra.induction_on generalizing a with
  | hM q =>
      rw [MonoidAlgebra.smul_of]
      change modTwoGroupAlgebraFunctionMoment f (MonoidAlgebra.single q a) = _
      simp
  | hadd x y hx hy =>
      rw [smul_add, map_add, map_add, hx, hy]
      ring
  | hsmul b x ih =>
      rw [smul_smul, ih, ih]
      ring

/-- The fibre-coordinate moment on the finite detector quotient. -/
def sqQuadraticDetectorMoment (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2)
    (hκ : sqRelatorQuadraticInitialGram h κ = 0) :
    ModTwoGroupAlgebraLevel (DSq h : Type) (sqQuadraticDetectorKernel h κ hκ) →+
      ZMod 2 :=
  modTwoGroupAlgebraFunctionMoment
    (fun q => (sqQuadraticDetectorQuotientHom h κ hκ q).fib)

@[simp] theorem sqQuadraticDetectorMoment_single (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2)
    (hκ : sqRelatorQuadraticInitialGram h κ = 0)
    (q : (DSq h : Type) ⧸ (sqQuadraticDetectorKernel h κ hκ).toSubgroup)
    (a : ZMod 2) :
    sqQuadraticDetectorMoment h κ hκ (MonoidAlgebra.single q a) =
      a * (sqQuadraticDetectorQuotientHom h κ hκ q).fib := by
  exact modTwoGroupAlgebraFunctionMoment_single _ q a

/-- The second finite difference of a fibre-coordinate moment is the defining cocycle. -/
theorem modTwoGroupAlgebraFunctionMoment_two_differences
    {Q L : Type} [Group Q] [Group L] {c : GQ2.DRCoh.TwoCocycle L}
    (φ : Q →* GQ2.DRCoh.CentExt c) (x y : Q) :
    modTwoGroupAlgebraFunctionMoment (fun q => (φ q).fib)
      ((MonoidAlgebra.single x 1 - 1) *
        (MonoidAlgebra.single y 1 - 1)) =
      c.κ (φ x).base (φ y).base := by
  have hexpand :
      (MonoidAlgebra.single x (1 : ZMod 2) - 1) *
          (MonoidAlgebra.single y (1 : ZMod 2) - 1) =
        MonoidAlgebra.single (x * y) (1 : ZMod 2) -
          MonoidAlgebra.single x (1 : ZMod 2) -
          MonoidAlgebra.single y (1 : ZMod 2) +
          MonoidAlgebra.single 1 (1 : ZMod 2) := by
    calc
      _ = MonoidAlgebra.single x (1 : ZMod 2) *
            MonoidAlgebra.single y (1 : ZMod 2) -
          MonoidAlgebra.single x (1 : ZMod 2) -
          MonoidAlgebra.single y (1 : ZMod 2) +
          (1 : MonoidAlgebra (ZMod 2) Q) := by
            noncomm_ring
      _ = _ := by
        simp only [MonoidAlgebra.single_mul_single, one_mul]
        rfl
  rw [hexpand]
  simp only [map_add, map_sub, modTwoGroupAlgebraFunctionMoment_single,
    one_mul, map_mul, GQ2.DRCoh.CentExt.mul_fib]
  have hzero : (φ (1 : Q)).fib = 0 := by simp
  rw [hzero]
  ring_nf

/-- On marked generator differences, the detector moment reads the selected matrix entry. -/
theorem sqQuadraticDetectorMoment_generatorPair (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2)
    (hκ : sqRelatorQuadraticInitialGram h κ = 0)
    (i j : Fin (sqRank h)) :
    sqQuadraticDetectorMoment h κ hκ
        (ModTwoCompletedGroupAlgebra.coordinate (DSq h : Type)
          (sqQuadraticDetectorKernel h κ hκ)
          (sqCompletedGeneratorDifference h i *
            sqCompletedGeneratorDifference h j)) = κ i j := by
  rw [map_mul]
  simp only [sqCompletedGeneratorDifference, map_sub,
    ModTwoCompletedGroupAlgebra.coordinate_of, map_one]
  change modTwoGroupAlgebraFunctionMoment
      (fun q => (sqQuadraticDetectorQuotientHom h κ hκ q).fib)
      ((MonoidAlgebra.single
          (QuotientGroup.mk'
            (sqQuadraticDetectorKernel h κ hκ).toSubgroup (sqGen h i)) 1 - 1) *
        (MonoidAlgebra.single
          (QuotientGroup.mk'
            (sqQuadraticDetectorKernel h κ hκ).toSubgroup (sqGen h j)) 1 - 1)) = κ i j
  rw [modTwoGroupAlgebraFunctionMoment_two_differences]
  change (sqQuadraticDetectorCocycle h κ).κ
      (sqQuadraticDetectorQuotientHom h κ hκ
        (QuotientGroup.mk'
          (sqQuadraticDetectorKernel h κ hκ).toSubgroup (sqGen h i))).base
      (sqQuadraticDetectorQuotientHom h κ hκ
        (QuotientGroup.mk'
          (sqQuadraticDetectorKernel h κ hκ).toSubgroup (sqGen h j))).base = κ i j
  rw [sqQuadraticDetectorQuotientHom_mk_gen,
    sqQuadraticDetectorQuotientHom_mk_gen]
  exact sqQuadraticDetectorCocycle_mark h κ i j

/-- The fibre coordinate of a central extension by a bi-additive cocycle is a quadratic
function: its third multiplicative finite difference vanishes. -/
theorem centExtFib_thirdDifference
    {Q L : Type} [Group Q] [Group L] {c : GQ2.DRCoh.TwoCocycle L}
    (hc : IsCupCocycle c) (φ : Q →* GQ2.DRCoh.CentExt c)
    (t x y z : Q) :
    (φ (t * x * y * z)).fib + (φ (t * x * y)).fib +
      (φ (t * x * z)).fib + (φ (t * x)).fib +
      (φ (t * y * z)).fib + (φ (t * y)).fib +
      (φ (t * z)).fib + (φ t).fib = 0 := by
  simp only [map_mul, GQ2.DRCoh.CentExt.mul_fib,
    GQ2.DRCoh.CentExt.mul_base]
  simp_rw [hc.addLeft]
  ring_nf
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h4 : (4 : ZMod 2) = 0 := by decide
  have h8 : (8 : ZMod 2) = 0 := by decide
  simp [h2, h4, h8]

/-- A fibre-coordinate moment kills a left translate of a product of three group-like
differences.  This is the group-algebra form of `centExtFib_thirdDifference`. -/
theorem modTwoGroupAlgebraFunctionMoment_single_mul_three_differences
    {Q L : Type} [Group Q] [Group L] {c : GQ2.DRCoh.TwoCocycle L}
    (hc : IsCupCocycle c) (φ : Q →* GQ2.DRCoh.CentExt c)
    (t x y z : Q) :
    modTwoGroupAlgebraFunctionMoment (fun q => (φ q).fib)
      (MonoidAlgebra.single t 1 *
        (MonoidAlgebra.single x 1 - 1) *
        (MonoidAlgebra.single y 1 - 1) *
        (MonoidAlgebra.single z 1 - 1)) = 0 := by
  let T : Q → MonoidAlgebra (ZMod 2) Q := fun q => MonoidAlgebra.single q 1
  have hexpand :
      T t * (T x - 1) * (T y - 1) * (T z - 1) =
        T (t * x * y * z) - T (t * y * z) - T (t * x * z) +
          T (t * z) - T (t * x * y) + T (t * y) + T (t * x) - T t := by
    calc
      _ = T t * T x * T y * T z - T t * T y * T z -
          T t * T x * T z + T t * T z - T t * T x * T y +
          T t * T y + T t * T x - T t := by
            noncomm_ring
      _ = _ := by
        dsimp only [T]
        simp only [MonoidAlgebra.single_mul_single, one_mul]
  dsimp only [T] at hexpand
  rw [hexpand]
  simp only [map_sub, map_add,
    modTwoGroupAlgebraFunctionMoment_single, one_mul]
  have hd := centExtFib_thirdDifference hc φ t x y z
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hd

/-! ## Annihilation of the finite augmentation cube -/

/-- At a finite group, every augmentation-zero element is a left-coefficient combination
of all group-like differences. -/
theorem modTwoFiniteAugmentationIdeal_exists_groupDifferenceCoefficients
    {Q : Type} [Group Q] [Fintype Q]
    (x : MonoidAlgebra (ZMod 2) Q) (hx : x ∈ modTwoFiniteAugmentationIdeal Q) :
    ∃ d : Q → MonoidAlgebra (ZMod 2) Q,
      x = ∑ q, d q * (MonoidAlgebra.single q 1 - 1) := by
  classical
  let g : Q → MonoidAlgebra (ZMod 2) Q := fun q =>
    MonoidAlgebra.single q 1 - 1
  have heq : modTwoMarkedAugmentationIdeal (fun q : Q => q) =
      modTwoFiniteAugmentationIdeal Q :=
    modTwoMarkedAugmentationIdeal_eq_finiteAugmentationIdeal
      (fun q : Q => q) (by simp)
  have hx' : x ∈ Ideal.span (Set.range g) := by
    change x ∈ modTwoMarkedAugmentationIdeal (fun q : Q => q)
    rw [heq]
    exact hx
  clear hx heq
  induction hx' using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨q, rfl⟩
      refine ⟨Pi.single q 1, ?_⟩
      rw [Finset.sum_eq_single q]
      · simp [g]
      · intro b hb hbq
        simp [Pi.single_apply, hbq]
      · simp
  | zero =>
      exact ⟨0, by simp⟩
  | add y z hy hz iy iz =>
      rcases iy with ⟨d, hd⟩
      rcases iz with ⟨e, he⟩
      refine ⟨d + e, ?_⟩
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      rw [← hd, ← he]
  | smul a y hy iy =>
      rcases iy with ⟨d, hd⟩
      refine ⟨fun q => a * d q, ?_⟩
      rw [smul_eq_mul, hd, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [mul_assoc]

/-- A fibre-coordinate moment associated to a cup cocycle vanishes on the third power of the
ordinary finite-group augmentation ideal. -/
theorem modTwoGroupAlgebraFunctionMoment_eq_zero_of_mem_augmentation_cube
    {Q L : Type} [Group Q] [Fintype Q] [Group L]
    {c : GQ2.DRCoh.TwoCocycle L}
    (hc : IsCupCocycle c) (φ : Q →* GQ2.DRCoh.CentExt c)
    (x : MonoidAlgebra (ZMod 2) Q)
    (hx : x ∈ modTwoFiniteAugmentationIdeal Q ^ 3) :
    modTwoGroupAlgebraFunctionMoment (fun q => (φ q).fib) x = 0 := by
  classical
  letI : (modTwoFiniteAugmentationIdeal Q).IsTwoSided := by
    change (RingHom.ker (modTwoFiniteAugmentation Q).toRingHom).IsTwoSided
    infer_instance
  let g : Q → MonoidAlgebra (ZMod 2) Q := fun q =>
    MonoidAlgebra.single q 1 - 1
  obtain ⟨d, hd⟩ := idealPower_exists_finiteGeneratorMonomial
    (modTwoFiniteAugmentationIdeal Q) g
    (modTwoFiniteAugmentationIdeal_exists_groupDifferenceCoefficients) 3 x hx
  rw [hd, finiteGeneratorMonomialMap_apply, map_sum]
  apply Finset.sum_eq_zero
  rintro ⟨⟨⟨u, q₁⟩, q₂⟩, q₃⟩ hw
  rcases u with ⟨⟩
  have hprod : finiteGeneratorWordProduct g 3
      (((PUnit.unit, q₁), q₂), q₃) =
      (MonoidAlgebra.single q₁ 1 - 1) *
        (MonoidAlgebra.single q₂ 1 - 1) *
        (MonoidAlgebra.single q₃ 1 - 1) := by
    simp [finiteGeneratorWordProduct, g]
  rw [hprod]
  induction d (((PUnit.unit, q₁), q₂), q₃) using MonoidAlgebra.induction_on with
  | hM t =>
      rw [show MonoidAlgebra.of (ZMod 2) Q t =
        MonoidAlgebra.single t 1 by rfl]
      simpa only [mul_assoc] using
        modTwoGroupAlgebraFunctionMoment_single_mul_three_differences
        hc φ t q₁ q₂ q₃
  | hadd a b ha hb =>
      rw [add_mul, map_add, ha, hb, add_zero]
  | hsmul a y hy =>
      rw [smul_mul_assoc, modTwoGroupAlgebraFunctionMoment_smul, hy, mul_zero]

/-! ## Detector evaluation on completed quadratic monomials -/

/-- A detector evaluates a scalar quadratic monomial by contracting its coefficient matrix
against the chosen bilinear form. -/
theorem sqQuadraticDetectorMoment_scalarMonomial_coordinate (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2)
    (hκ : sqRelatorQuadraticInitialGram h κ = 0)
    (a : FiniteGeneratorWord (Fin (sqRank h)) 2 → ZMod 2) :
    sqQuadraticDetectorMoment h κ hκ
        (ModTwoCompletedGroupAlgebra.coordinate (DSq h : Type)
          (sqQuadraticDetectorKernel h κ hκ)
          (sqCompletedQuadraticScalarMonomial h a)) =
      ∑ w, a w * κ w.1.2 w.2 := by
  rw [sqCompletedQuadraticScalarMonomial,
    finiteGeneratorMonomialMap_apply, map_sum, map_sum]
  apply Finset.sum_congr rfl
  rintro ⟨⟨u, i⟩, j⟩ hw
  rcases u with ⟨⟩
  simp only [finiteGeneratorWordProduct, one_mul]
  rw [map_mul]
  have hscalar :
      ModTwoCompletedGroupAlgebra.coordinate (DSq h : Type)
          (sqQuadraticDetectorKernel h κ hκ)
          ((a ((PUnit.unit, i), j)) •
            (1 : ModTwoCompletedGroupAlgebra (DSq h : Type))) =
        a ((PUnit.unit, i), j) •
          (1 : ModTwoGroupAlgebraLevel (DSq h : Type)
            (sqQuadraticDetectorKernel h κ hκ)) := by
    exact map_smul _ _ _
  rw [hscalar, smul_mul_assoc, one_mul]
  change modTwoGroupAlgebraFunctionMoment
      (fun q => (sqQuadraticDetectorQuotientHom h κ hκ q).fib)
      (a ((PUnit.unit, i), j) •
        ModTwoCompletedGroupAlgebra.coordinate (DSq h : Type)
          (sqQuadraticDetectorKernel h κ hκ)
          (sqCompletedGeneratorDifference h i *
            sqCompletedGeneratorDifference h j)) = _
  rw [modTwoGroupAlgebraFunctionMoment_smul]
  change a ((PUnit.unit, i), j) *
      sqQuadraticDetectorMoment h κ hκ
        (ModTwoCompletedGroupAlgebra.coordinate (DSq h : Type)
          (sqQuadraticDetectorKernel h κ hκ)
          (sqCompletedGeneratorDifference h i *
            sqCompletedGeneratorDifference h j)) = _
  rw [sqQuadraticDetectorMoment_generatorPair h κ hκ i j]

/-- Every admissible detector annihilates the coefficient matrix of a completed quadratic
monomial which lies in the completed augmentation cube. -/
theorem sqQuadraticDetector_contraction_eq_zero_of_mem_cube (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2)
    (hκ : sqRelatorQuadraticInitialGram h κ = 0)
    (a : FiniteGeneratorWord (Fin (sqRank h)) 2 → ZMod 2)
    (ha : sqCompletedQuadraticScalarMonomial h a ∈
      modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3) :
    ∑ w, a w * κ w.1.2 w.2 = 0 := by
  letI : Fintype
      ((DSq h : Type) ⧸ (sqQuadraticDetectorKernel h κ hκ).toSubgroup) :=
    Fintype.ofFinite _
  have hcoord := modTwoCompletedAugmentationIdealPow_coordinate
    (DSq h : Type) (sqQuadraticDetectorKernel h κ hκ) 3 ha
  have hzero := modTwoGroupAlgebraFunctionMoment_eq_zero_of_mem_augmentation_cube
    (sqQuadraticDetectorCocycle_isCup h κ)
    (sqQuadraticDetectorQuotientHom h κ hκ)
    (ModTwoCompletedGroupAlgebra.coordinate (DSq h : Type)
      (sqQuadraticDetectorKernel h κ hκ)
      (sqCompletedQuadraticScalarMonomial h a)) hcoord
  change sqQuadraticDetectorMoment h κ hκ
      (ModTwoCompletedGroupAlgebra.coordinate (DSq h : Type)
        (sqQuadraticDetectorKernel h κ hκ)
        (sqCompletedQuadraticScalarMonomial h a)) = 0 at hzero
  rw [sqQuadraticDetectorMoment_scalarMonomial_coordinate h κ hκ a] at hzero
  exact hzero

/-! ## Separation modulo the certified quadratic relation -/

/-- The matrix obtained by evaluating degree-two marked monomials with a linear functional on
the abstract quadratic quotient. -/
def sqQuadraticDetectorMatrixOfDual (h : ℕ)
    (ℓ : Module.Dual (ZMod 2) (SqQuadraticAlgebra h))
    (i j : Fin (sqRank h)) : ZMod 2 :=
  ℓ (sqQuadraticQuotientLetter h i * sqQuadraticQuotientLetter h j)

/-- Every dual functional on the abstract quadratic quotient gives an admissible detector:
the defining quotient relation says exactly that its matrix kills the certified Gram form. -/
theorem sqQuadraticDetectorMatrixOfDual_gram_eq_zero (h : ℕ)
    (ℓ : Module.Dual (ZMod 2) (SqQuadraticAlgebra h)) :
    sqRelatorQuadraticInitialGram h (sqQuadraticDetectorMatrixOfDual h ℓ) = 0 := by
  have hre := congrArg ℓ (sqQuadraticQuotient_relation_expanded h)
  simp only [map_add, map_sum] at hre
  rw [sqRelatorQuadraticInitialGram]
  change
    ℓ (sqQuadraticQuotientLetter h 2 * sqQuadraticQuotientLetter h 2) +
        (ℓ (sqQuadraticQuotientLetter h 0 * sqQuadraticQuotientLetter h 1) +
          ℓ (sqQuadraticQuotientLetter h 1 * sqQuadraticQuotientLetter h 0)) +
        ∑ j, (ℓ (sqQuadraticQuotientLetter h (sqHandleIdxU j) *
              sqQuadraticQuotientLetter h (sqHandleIdxV j)) +
            ℓ (sqQuadraticQuotientLetter h (sqHandleIdxV j) *
              sqQuadraticQuotientLetter h (sqHandleIdxU j))) = 0
  rw [hre]
  convert CharTwo.add_self_eq_zero
    (ℓ (sqQuadraticQuotientLetter h 2 * sqQuadraticQuotientLetter h 2) +
      ℓ (sqQuadraticQuotientLetter h 0 * sqQuadraticQuotientLetter h 1) +
      ∑ j, (ℓ (sqQuadraticQuotientLetter h (sqHandleIdxU j) *
            sqQuadraticQuotientLetter h (sqHandleIdxV j)) +
          ℓ (sqQuadraticQuotientLetter h (sqHandleIdxV j) *
            sqQuadraticQuotientLetter h (sqHandleIdxU j)))) using 1 <;> ring

/-- Evaluating a scalar quadratic word combination by a dual functional is the contraction
of its coefficient matrix against the associated detector. -/
theorem sqQuadraticScalarWordCombination_dual_eq_contraction (h : ℕ)
    (ℓ : Module.Dual (ZMod 2) (SqQuadraticAlgebra h))
    (a : FiniteGeneratorWord (Fin (sqRank h)) 2 → ZMod 2) :
    ℓ (sqQuadraticScalarWordCombination h a) =
      ∑ w, a w * sqQuadraticDetectorMatrixOfDual h ℓ w.1.2 w.2 := by
  rw [sqQuadraticScalarWordCombination, map_sum]
  apply Finset.sum_congr rfl
  rintro ⟨⟨u, i⟩, j⟩ hw
  rcases u with ⟨⟩
  simp [finiteGeneratorWordList, quadraticWordEval,
    sqQuadraticDetectorMatrixOfDual]

/-- The finite detector family separates all degree-two completed relations: membership in
the completed augmentation cube forces the corresponding abstract quadratic class to vanish. -/
theorem sqQuadraticScalarWordCombination_eq_zero_of_completed_mem_cube (h : ℕ)
    (a : FiniteGeneratorWord (Fin (sqRank h)) 2 → ZMod 2)
    (ha : sqCompletedQuadraticScalarMonomial h a ∈
      modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3) :
    sqQuadraticScalarWordCombination h a = 0 := by
  by_contra hne
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2) hne
  let κ := sqQuadraticDetectorMatrixOfDual h ℓ
  have hκ : sqRelatorQuadraticInitialGram h κ = 0 :=
    sqQuadraticDetectorMatrixOfDual_gram_eq_zero h ℓ
  have hzero := sqQuadraticDetector_contraction_eq_zero_of_mem_cube
    h κ hκ a ha
  have heval := sqQuadraticScalarWordCombination_dual_eq_contraction h ℓ a
  apply hℓ
  rw [heval, hzero]

/-! ## The actual relation in the completed augmentation cube -/

/-- Under the rank-one regular-module/group-algebra equivalence, the marked one-boundary is
the usual Fox contraction by the marked group-like differences. -/
theorem regularUnitGroupAlgebraEquiv_finiteMarkedBoundaryOne
    {Q I : Type} [Group Q] [Fintype I] [DecidableEq I]
    (m : I → Q) (c : RegularModTwoRelationModule Q I) :
    regularUnitGroupAlgebraEquiv Q (finiteMarkedBoundaryOne m c) =
      ∑ i, regularModTwoComponent i c *
        (MonoidAlgebra.single (m i) 1 - 1) := by
  classical
  have hsingle (g : Q) (j : I) (a : ZMod 2) :
      regularUnitGroupAlgebraEquiv Q
          (finiteMarkedBoundaryOne m (Finsupp.single (g, j) a)) =
        ∑ i, regularModTwoComponent i (Finsupp.single (g, j) a) *
          (MonoidAlgebra.single (m i) 1 - 1) := by
    simp only [finiteMarkedBoundaryOne_single, map_add,
      regularUnitGroupAlgebraEquiv_single]
    rw [Finset.sum_eq_single j]
    · simp only [regularModTwoComponent_single, if_pos]
      rw [mul_sub, mul_one, MonoidAlgebra.single_mul_single, mul_one]
      ext q
      simp [sub_eq_add_neg, ZModModule.neg_eq_self, add_comm, add_left_comm,
        add_assoc]
    · intro i hi hij
      simp [regularModTwoComponent_single, Ne.symm hij]
    · simp [regularModTwoComponent_single]
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨g, j⟩
      rw [map_add, map_add, ih, hsingle]
      simp_rw [map_add, add_mul]
      rw [Finset.sum_add_distrib]

/-- The completed Fox fundamental identity for the literal improved square relator. -/
theorem sqCompletedFoxFundamentalIdentity (h : ℕ) :
    ∑ i, sqCompletedModTwoFoxDerivativeRow h i *
        sqCompletedGeneratorDifference h i = 0 := by
  apply ModTwoCompletedGroupAlgebra.ext (DSq h : Type)
  intro U
  simp only [map_sum, map_mul,
    sqCompletedModTwoFoxDerivativeRow_coordinate,
    sqCompletedGeneratorDifference, map_sub,
    ModTwoCompletedGroupAlgebra.coordinate_of, map_one]
  let m := sqOpenQuotientMarking h U
  have hboundary := finiteMarkedBoundaryOne_modTwoFoxDerivative_eq_zero
    m (sqDiscreteRelator h) (sqOpenQuotientMarking_sqDiscreteRelator h U)
  have hcontract := regularUnitGroupAlgebraEquiv_finiteMarkedBoundaryOne
    m (modTwoFoxDerivative m (sqDiscreteRelator h))
  rw [hboundary, map_zero] at hcontract
  exact hcontract.symm

/-- Replacing every literal completed Fox derivative in the fundamental identity by its
certified degree-one partner changes the result only by an element of `J³`. -/
theorem sqCompletedPartnerQuadraticSum_mem_augmentation_cube (h : ℕ) :
    ∑ i, sqCompletedGeneratorDifference h (sqInitialPartner h i) *
        sqCompletedGeneratorDifference h i ∈
      modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3 := by
  let J := modTwoCompletedAugmentationIdeal (DSq h : Type)
  have herr : ∑ i,
      (sqCompletedModTwoFoxDerivativeRow h i -
          sqCompletedGeneratorDifference h (sqInitialPartner h i)) *
        sqCompletedGeneratorDifference h i ∈ J ^ 3 := by
    apply Ideal.sum_mem
    intro i hi
    rw [show 3 = 2 + 1 by omega, Submodule.pow_add J (by omega : 1 ≠ 0),
      Submodule.pow_one]
    exact Ideal.mul_mem_mul
      (sqCompletedFoxRow_sub_partnerDifference_mem_augmentation_sq h i)
      (sqCompletedGeneratorDifference_mem h i)
  have hfund := sqCompletedFoxFundamentalIdentity h
  have heq : ∑ i,
      (sqCompletedModTwoFoxDerivativeRow h i -
          sqCompletedGeneratorDifference h (sqInitialPartner h i)) *
        sqCompletedGeneratorDifference h i =
      - ∑ i, sqCompletedGeneratorDifference h (sqInitialPartner h i) *
        sqCompletedGeneratorDifference h i := by
    simp only [sub_mul, Finset.sum_sub_distrib, hfund, zero_sub]
  rw [heq] at herr
  simpa only [neg_neg] using Submodule.neg_mem _ herr

/-- Split a sum over the improved square alphabet into its three core letters and handle
pairs. -/
theorem sqSum_eq_core_add_handles {M : Type} [AddCommMonoid M]
    (h : ℕ) (f : Fin (sqRank h) → M) :
    ∑ i, f i = f 0 + f 1 + f 2 +
      ∑ j, (f (sqHandleIdxU j) + f (sqHandleIdxV j)) := by
  rw [← Equiv.sum_comp (sqInitialAlphabetEquiv h).symm f,
    Fintype.sum_sum_type, Fin.sum_univ_three, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  have hzero : (sqInitialAlphabetEquiv h).symm (Sum.inl 0) = 0 := by
    apply (sqInitialAlphabetEquiv h).injective
    simp
  have hone : (sqInitialAlphabetEquiv h).symm (Sum.inl 1) = 1 := by
    apply (sqInitialAlphabetEquiv h).injective
    simp
  have htwo : (sqInitialAlphabetEquiv h).symm (Sum.inl 2) = 2 := by
    apply (sqInitialAlphabetEquiv h).injective
    simp
  have hU (j : Fin h) :
      (sqInitialAlphabetEquiv h).symm (Sum.inr (j, 0)) = sqHandleIdxU j := by
    apply (sqInitialAlphabetEquiv h).injective
    simp
  have hV (j : Fin h) :
      (sqInitialAlphabetEquiv h).symm (Sum.inr (j, 1)) = sqHandleIdxV j := by
    apply (sqInitialAlphabetEquiv h).injective
    simp
  rw [hzero, hone, htwo]
  simp_rw [hU, hV]

/-- The explicit completed evaluation of the defining quadratic polynomial. -/
def sqCompletedQuadraticRelationPolynomial (h : ℕ) :
    ModTwoCompletedGroupAlgebra (DSq h : Type) :=
  sqCompletedGeneratorDifference h 1 * sqCompletedGeneratorDifference h 0 -
    (sqCompletedGeneratorDifference h 2 * sqCompletedGeneratorDifference h 2 +
      sqCompletedGeneratorDifference h 0 * sqCompletedGeneratorDifference h 1 +
      ∑ j, (sqCompletedGeneratorDifference h (sqHandleIdxU j) *
          sqCompletedGeneratorDifference h (sqHandleIdxV j) +
        sqCompletedGeneratorDifference h (sqHandleIdxV j) *
          sqCompletedGeneratorDifference h (sqHandleIdxU j)))

/-- The literal completed Fox identity proves that the defining improved quadratic relation
vanishes modulo the completed augmentation cube. -/
theorem sqCompletedQuadraticRelationPolynomial_mem_augmentation_cube (h : ℕ) :
    sqCompletedQuadraticRelationPolynomial h ∈
      modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3 := by
  have hp := sqCompletedPartnerQuadraticSum_mem_augmentation_cube h
  rw [sqSum_eq_core_add_handles h] at hp
  simp only [sqInitialPartner_zero, sqInitialPartner_one,
    sqInitialPartner_two, sqInitialPartner_handleU,
    sqInitialPartner_handleV] at hp
  have heq :
      sqCompletedQuadraticRelationPolynomial h =
        sqCompletedGeneratorDifference h 1 * sqCompletedGeneratorDifference h 0 +
          sqCompletedGeneratorDifference h 0 * sqCompletedGeneratorDifference h 1 +
          sqCompletedGeneratorDifference h 2 * sqCompletedGeneratorDifference h 2 +
          ∑ j, (sqCompletedGeneratorDifference h (sqHandleIdxV j) *
              sqCompletedGeneratorDifference h (sqHandleIdxU j) +
            sqCompletedGeneratorDifference h (sqHandleIdxU j) *
              sqCompletedGeneratorDifference h (sqHandleIdxV j)) := by
    rw [sqCompletedQuadraticRelationPolynomial]
    rw [sub_eq_add_neg]
    rw [show
      -(sqCompletedGeneratorDifference h 2 * sqCompletedGeneratorDifference h 2 +
          sqCompletedGeneratorDifference h 0 * sqCompletedGeneratorDifference h 1 +
          ∑ j, (sqCompletedGeneratorDifference h (sqHandleIdxU j) *
              sqCompletedGeneratorDifference h (sqHandleIdxV j) +
            sqCompletedGeneratorDifference h (sqHandleIdxV j) *
              sqCompletedGeneratorDifference h (sqHandleIdxU j))) =
        (sqCompletedGeneratorDifference h 2 * sqCompletedGeneratorDifference h 2 +
          sqCompletedGeneratorDifference h 0 * sqCompletedGeneratorDifference h 1 +
          ∑ j, (sqCompletedGeneratorDifference h (sqHandleIdxU j) *
              sqCompletedGeneratorDifference h (sqHandleIdxV j) +
            sqCompletedGeneratorDifference h (sqHandleIdxV j) *
              sqCompletedGeneratorDifference h (sqHandleIdxU j))) by
        apply ModTwoCompletedGroupAlgebra.ext (DSq h : Type)
        intro U
        exact ZModModule.neg_eq_self _]
    have hsum :
        (∑ j, (sqCompletedGeneratorDifference h (sqHandleIdxU j) *
              sqCompletedGeneratorDifference h (sqHandleIdxV j) +
            sqCompletedGeneratorDifference h (sqHandleIdxV j) *
              sqCompletedGeneratorDifference h (sqHandleIdxU j))) =
          ∑ j, (sqCompletedGeneratorDifference h (sqHandleIdxV j) *
              sqCompletedGeneratorDifference h (sqHandleIdxU j) +
            sqCompletedGeneratorDifference h (sqHandleIdxU j) *
              sqCompletedGeneratorDifference h (sqHandleIdxV j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact add_comm _ _
    rw [hsum]
    let A := sqCompletedGeneratorDifference h 1 *
      sqCompletedGeneratorDifference h 0
    let B := sqCompletedGeneratorDifference h 0 *
      sqCompletedGeneratorDifference h 1
    let C := sqCompletedGeneratorDifference h 2 *
      sqCompletedGeneratorDifference h 2
    let S := ∑ j, (sqCompletedGeneratorDifference h (sqHandleIdxV j) *
        sqCompletedGeneratorDifference h (sqHandleIdxU j) +
      sqCompletedGeneratorDifference h (sqHandleIdxU j) *
        sqCompletedGeneratorDifference h (sqHandleIdxV j))
    change A + (C + B + S) = A + B + C + S
    rw [add_comm C B]
    simp only [add_assoc]
  rw [heq]
  exact hp

/-! ## Factorization through the degree-two completed truncation -/

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

/-- The completed group algebra truncated modulo the third augmentation power. -/
abbrev SqCompletedQuadraticTruncation (h : ℕ) :=
  ModTwoCompletedGroupAlgebra (DSq h : Type) ⧸
    (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3)

/-- The free-algebra evaluation which sends each abstract letter to the corresponding completed
generator difference modulo `J³`. -/
def sqQuadraticToCompletedTruncationFreeHom (h : ℕ) :
    FreeAlgebra (ZMod 2) (Fin (sqRank h)) →ₐ[ZMod 2]
      SqCompletedQuadraticTruncation h :=
  FreeAlgebra.lift (ZMod 2) fun i =>
    Ideal.Quotient.mkₐ (ZMod 2)
      (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3)
      (sqCompletedGeneratorDifference h i)

@[simp] theorem sqQuadraticToCompletedTruncationFreeHom_letter
    (h : ℕ) (i : Fin (sqRank h)) :
    sqQuadraticToCompletedTruncationFreeHom h (sqQuadraticFreeLetter h i) =
      Ideal.Quotient.mkₐ (ZMod 2)
        (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3)
        (sqCompletedGeneratorDifference h i) := by
  simp [sqQuadraticToCompletedTruncationFreeHom, sqQuadraticFreeLetter]

/-- The explicit quadratic polynomial maps to zero in the completed truncation. -/
theorem sqQuadraticToCompletedTruncationFreeHom_relation (h : ℕ) :
    sqQuadraticToCompletedTruncationFreeHom h
      (sqQuadraticRelationPolynomial h) = 0 := by
  simp only [sqQuadraticRelationPolynomial, sqQuadraticReductionRHS,
    map_sub, map_add, map_mul, map_sum,
    sqQuadraticToCompletedTruncationFreeHom_letter]
  have heval : Ideal.Quotient.mkₐ (ZMod 2)
        (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3)
        (sqCompletedQuadraticRelationPolynomial h) =
      Ideal.Quotient.mkₐ (ZMod 2)
          (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3)
          (sqCompletedGeneratorDifference h 1) *
        Ideal.Quotient.mkₐ (ZMod 2)
          (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3)
          (sqCompletedGeneratorDifference h 0) -
        (Ideal.Quotient.mkₐ (ZMod 2)
              (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3)
              (sqCompletedGeneratorDifference h 2) *
            Ideal.Quotient.mkₐ (ZMod 2)
              (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3)
              (sqCompletedGeneratorDifference h 2) +
          Ideal.Quotient.mkₐ (ZMod 2)
              (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3)
              (sqCompletedGeneratorDifference h 0) *
            Ideal.Quotient.mkₐ (ZMod 2)
              (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3)
              (sqCompletedGeneratorDifference h 1) +
          ∑ j, (Ideal.Quotient.mkₐ (ZMod 2)
                (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3)
                (sqCompletedGeneratorDifference h (sqHandleIdxU j)) *
              Ideal.Quotient.mkₐ (ZMod 2)
                (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3)
                (sqCompletedGeneratorDifference h (sqHandleIdxV j)) +
            Ideal.Quotient.mkₐ (ZMod 2)
                (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3)
                (sqCompletedGeneratorDifference h (sqHandleIdxV j)) *
              Ideal.Quotient.mkₐ (ZMod 2)
                (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3)
                (sqCompletedGeneratorDifference h (sqHandleIdxU j)))) := by
    simp [sqCompletedQuadraticRelationPolynomial]
  rw [← heval]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (sqCompletedQuadraticRelationPolynomial_mem_augmentation_cube h)

/-- The two-sided abstract quadratic relation ideal is killed by completed evaluation modulo
`J³`. -/
theorem sqQuadraticToCompletedTruncationFreeHom_relationIdeal_mapsTo_zero
    (h : ℕ) (a : FreeAlgebra (ZMod 2) (Fin (sqRank h)))
    (ha : a ∈ sqQuadraticRelationIdeal h) :
    (sqQuadraticToCompletedTruncationFreeHom h).toRingHom a = 0 := by
  rw [sqQuadraticRelationIdeal] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
      rcases ha with ⟨⟨u, v⟩, rfl⟩
      rw [map_mul, map_mul]
      have hr : (sqQuadraticToCompletedTruncationFreeHom h).toRingHom
          (sqQuadraticRelationPolynomial h) = 0 :=
        sqQuadraticToCompletedTruncationFreeHom_relation h
      rw [hr, mul_zero, zero_mul]
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy, add_zero]
  | smul r x hx ih =>
      change sqQuadraticToCompletedTruncationFreeHom h (r * x) = 0
      rw [map_mul]
      have ih' : sqQuadraticToCompletedTruncationFreeHom h x = 0 := ih
      rw [ih', mul_zero]

/-- Evaluation of the abstract quadratic quotient in the actual completed algebra modulo
`J³`. -/
def sqQuadraticToCompletedTruncationHom (h : ℕ) :
    SqQuadraticAlgebra h →ₐ[ZMod 2] SqCompletedQuadraticTruncation h :=
  Ideal.Quotient.liftₐ (sqQuadraticRelationIdeal h)
    (sqQuadraticToCompletedTruncationFreeHom h)
    (sqQuadraticToCompletedTruncationFreeHom_relationIdeal_mapsTo_zero h)

@[simp] theorem sqQuadraticToCompletedTruncationHom_mk
    (h : ℕ) (a : FreeAlgebra (ZMod 2) (Fin (sqRank h))) :
    sqQuadraticToCompletedTruncationHom h
        (Ideal.Quotient.mkₐ (ZMod 2) (sqQuadraticRelationIdeal h) a) =
      sqQuadraticToCompletedTruncationFreeHom h a := by
  rw [sqQuadraticToCompletedTruncationHom, Ideal.Quotient.liftₐ_apply,
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.lift_mk]
  rfl

@[simp] theorem sqQuadraticToCompletedTruncationHom_letter
    (h : ℕ) (i : Fin (sqRank h)) :
    sqQuadraticToCompletedTruncationHom h (sqQuadraticQuotientLetter h i) =
      Ideal.Quotient.mkₐ (ZMod 2)
        (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3)
        (sqCompletedGeneratorDifference h i) := by
  rw [sqQuadraticQuotientLetter,
    sqQuadraticToCompletedTruncationHom_mk,
    sqQuadraticToCompletedTruncationFreeHom_letter]

/-- Abstract word evaluation maps to the same word in completed generator differences modulo
`J³`. -/
theorem sqQuadraticToCompletedTruncationHom_word (h : ℕ)
    (w : List (Fin (sqRank h))) :
    sqQuadraticToCompletedTruncationHom h
        (quadraticWordEval (SqQuadraticAlgebra h)
          (sqQuadraticQuotientLetter h) w) =
      Ideal.Quotient.mkₐ (ZMod 2)
        (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3)
        (quadraticWordEval (ModTwoCompletedGroupAlgebra (DSq h : Type))
          (sqCompletedGeneratorDifference h) w) := by
  induction w with
  | nil => simp [quadraticWordEval]
  | cons i w ih =>
      change sqQuadraticToCompletedTruncationHom h
          (sqQuadraticQuotientLetter h i *
            quadraticWordEval (SqQuadraticAlgebra h)
              (sqQuadraticQuotientLetter h) w) = _
      rw [map_mul, sqQuadraticToCompletedTruncationHom_letter, ih]
      exact (map_mul
        (Ideal.Quotient.mkₐ (ZMod 2)
          (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3))
        (sqCompletedGeneratorDifference h i)
        (quadraticWordEval (ModTwoCompletedGroupAlgebra (DSq h : Type))
          (sqCompletedGeneratorDifference h) w)).symm

/-- The truncation hom sends a scalar abstract quadratic combination to the class of the
corresponding completed quadratic monomial. -/
theorem sqQuadraticToCompletedTruncationHom_scalarWordCombination (h : ℕ)
    (a : FiniteGeneratorWord (Fin (sqRank h)) 2 → ZMod 2) :
    sqQuadraticToCompletedTruncationHom h
        (sqQuadraticScalarWordCombination h a) =
      Ideal.Quotient.mkₐ (ZMod 2)
        (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3)
        (sqCompletedQuadraticScalarMonomial h a) := by
  rw [sqQuadraticScalarWordCombination, map_sum,
    sqCompletedQuadraticScalarMonomial,
    finiteGeneratorMonomialMap_apply, map_sum]
  apply Finset.sum_congr rfl
  rintro ⟨⟨u, i⟩, j⟩ hw
  rcases u with ⟨⟩
  simp only [finiteGeneratorWordList, finiteGeneratorWordProduct, one_mul]
  rw [map_smul, sqQuadraticToCompletedTruncationHom_word]
  have hword :
      quadraticWordEval (ModTwoCompletedGroupAlgebra (DSq h : Type))
          (sqCompletedGeneratorDifference h) ([] ++ [i] ++ [j]) =
        sqCompletedGeneratorDifference h i *
          sqCompletedGeneratorDifference h j := by
    simp [quadraticWordEval]
  rw [hword]
  simp only [map_mul, map_smul, map_one, smul_mul_assoc, one_mul]

/-- Vanishing in the abstract quadratic quotient forces the corresponding completed scalar
monomial into `J³`. -/
theorem sqCompletedQuadraticScalarMonomial_mem_cube_of_wordCombination_eq_zero
    (h : ℕ) (a : FiniteGeneratorWord (Fin (sqRank h)) 2 → ZMod 2)
    (ha : sqQuadraticScalarWordCombination h a = 0) :
    sqCompletedQuadraticScalarMonomial h a ∈
      modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3 := by
  have hz := congrArg (sqQuadraticToCompletedTruncationHom h) ha
  rw [map_zero,
    sqQuadraticToCompletedTruncationHom_scalarWordCombination h a] at hz
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

/-! ## Exact degree-two completed Magnus comparison -/

/-- The scalar quadratic relations in the actual completed group algebra are exactly the
relations generated by the certified improved quadratic initial form. -/
theorem sqCompletedQuadraticRelationIdealExact (h : ℕ) :
    SqCompletedQuadraticRelationIdealExact h := by
  intro a
  constructor
  · exact sqCompletedQuadraticScalarMonomial_mem_cube_of_wordCombination_eq_zero h a
  · exact sqQuadraticScalarWordCombination_eq_zero_of_completed_mem_cube h a

/-- Unconditional degree-two Magnus--Labute kernel identity for the improved square
presentation. -/
theorem sqCompletedMonomialPBWKernelIdentity_two (h : ℕ) :
    SqCompletedMonomialPBWKernelIdentity h 2 :=
  sqCompletedMonomialPBWKernelIdentity_two_of_relationIdealExact h
    (sqCompletedQuadraticRelationIdealExact h)

/-- Regression form of the exact degree-two comparison. -/
theorem sqCompletedMonomialPBWKernelIdentity_two_regression (h : ℕ)
    (c : FiniteGeneratorWord (Fin (sqRank h)) 2 →
      ModTwoCompletedGroupAlgebra (DSq h : Type)) :
    sqCompletedMonomialPBWNormalMap h 2 c = 0 ↔
      finiteGeneratorMonomialMap (sqCompletedGeneratorDifference h) 2 c ∈
        modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 3 :=
  sqCompletedMonomialPBWKernelIdentity_two h c

end

end GQ2.ContCoh

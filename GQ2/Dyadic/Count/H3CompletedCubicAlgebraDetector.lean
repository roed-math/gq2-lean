/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3CompletedCubicObstruction

/-!
# A finite algebra-group target for the cubic Magnus detector

This file packages the exact finite algebra which remains to be constructed for the cubic
Magnus theorem.  The intended algebra is the noncommutative Magnus algebra truncated below
degree four and quotiented by the full inhomogeneous degree-two-plus-degree-three expansion of
the literal improved relator.

The generic part below proves the group-theoretic side of the construction.  For any finite
`𝔽₂`-algebra with an augmentation whose kernel has fourth power zero, the augmentation-one
units form a finite `2`-group.  Hence any marked family of such units satisfying the literal
square relator receives a canonical map from `DSq h`.

`SqCubicMagnusAlgebraCertificate` then states the sharp finite rewrite obligation: the marked
letters have augmentation zero, the literal relator dies on `1 + letter`, fourfold products in
the augmentation kernel vanish, literal cubic words evaluate according to the finite PBW
rewrite table, and the cubic PBW-normal words remain linearly independent.  These are precisely
the termination/confluence and inhomogeneous-relator checks for the proposed degree-`<4`
quotient; no completed group algebra or broad Magnus kernel identity occurs in the certificate.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2 GQ2.FoxH GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.SqCore

/-! ## A discrete wrapper for a finite algebra group -/

/-- A type synonym carrying the discrete topology, without changing its algebraic data. -/
def CubicDiscrete (A : Type) := A

def cubicDiscreteEquiv (A : Type) : CubicDiscrete A ≃ A := Equiv.refl A

instance CubicDiscrete.instGroup {A : Type} [Group A] : Group (CubicDiscrete A) :=
  Equiv.group (cubicDiscreteEquiv A)

instance CubicDiscrete.instFinite {A : Type} [Finite A] : Finite (CubicDiscrete A) :=
  Finite.of_equiv A (cubicDiscreteEquiv A).symm

instance CubicDiscrete.instTopologicalSpace (A : Type) :
    TopologicalSpace (CubicDiscrete A) := ⊥

instance CubicDiscrete.instDiscreteTopology (A : Type) :
    DiscreteTopology (CubicDiscrete A) := ⟨rfl⟩

instance CubicDiscrete.instIsTopologicalGroup {A : Type} [Group A] :
    IsTopologicalGroup (CubicDiscrete A) := by infer_instance

instance CubicDiscrete.instCompactSpace {A : Type} [Finite A] :
    CompactSpace (CubicDiscrete A) := by infer_instance

instance CubicDiscrete.instT2Space (A : Type) : T2Space (CubicDiscrete A) := by
  infer_instance

instance CubicDiscrete.instTotallyDisconnectedSpace (A : Type) :
    TotallyDisconnectedSpace (CubicDiscrete A) := by infer_instance

/-! ## Augmentation-one algebra groups -/

/-- Units whose augmentation is one. -/
abbrev AugmentationOneUnits {A : Type} [Ring A] [Algebra (ZMod 2) A]
    (augmentation : A →ₐ[ZMod 2] ZMod 2) :=
  (Units.map augmentation.toMonoidHom).ker

/-- In characteristic two, `1+x` is a unit as soon as `x⁴=0`. -/
theorem one_add_sq_charTwo {A : Type} [Ring A] [Algebra (ZMod 2) A]
    (x : A) : (1 + x) ^ 2 = 1 + x ^ 2 := by
  have hxx : x + x = 0 := by
    simpa only [two_nsmul] using ZModModule.char_nsmul_eq_zero 2 x
  simp only [pow_two, mul_add, add_mul, one_mul, mul_one]
  rw [show 1 + x + (x + x * x) = 1 + (x + x) + x * x by
    abel, hxx, add_zero]

def oneAddUnitOfPowFourZero {A : Type} [Ring A] [Algebra (ZMod 2) A]
    (x : A) (hx : x ^ 4 = 0) : Aˣ where
  val := 1 + x
  inv := 1 + x + x ^ 2 + x ^ 3
  val_inv := by
    have hneg (z : A) : -z = z := ZModModule.neg_eq_self z
    calc
      (1 + x) * (1 + x + x ^ 2 + x ^ 3) =
          (1 - x) * (1 + x + x ^ 2 + x ^ 3) := by
        rw [sub_eq_add_neg, hneg]
      _ = 1 - x ^ 4 := by noncomm_ring
      _ = 1 + x ^ 4 := by rw [sub_eq_add_neg, hneg]
      _ = 1 := by rw [hx, add_zero]
  inv_val := by
    have hneg (z : A) : -z = z := ZModModule.neg_eq_self z
    calc
      (1 + x + x ^ 2 + x ^ 3) * (1 + x) =
          (1 + x + x ^ 2 + x ^ 3) * (1 - x) := by
        rw [sub_eq_add_neg, hneg]
      _ = 1 - x ^ 4 := by noncomm_ring
      _ = 1 + x ^ 4 := by rw [sub_eq_add_neg, hneg]
      _ = 1 := by rw [hx, add_zero]

@[simp] theorem oneAddUnitOfPowFourZero_val
    {A : Type} [Ring A] [Algebra (ZMod 2) A]
    (x : A) (hx : x ^ 4 = 0) :
    ↑(oneAddUnitOfPowFourZero x hx) = 1 + x :=
  rfl

/-- A fourth-nilpotent augmentation kernel makes every augmentation-one unit fourth torsion. -/
theorem augmentationOneUnit_pow_four_eq_one
    {A : Type} [Ring A] [Algebra (ZMod 2) A]
    (augmentation : A →ₐ[ZMod 2] ZMod 2)
    (hfour : ∀ x : A, augmentation x = 0 → x ^ 4 = 0)
    (u : AugmentationOneUnits augmentation) : u ^ 4 = 1 := by
  apply Subtype.ext
  apply Units.ext
  let x : A := (u.1 : A) - 1
  have haug : augmentation x = 0 := by
    change augmentation ((u.1 : A) - 1) = 0
    rw [map_sub, map_one]
    have hu : Units.map augmentation.toMonoidHom u.1 = 1 := u.2
    have huval := congrArg Units.val hu
    change augmentation (u.1 : A) = 1 at huval
    rw [huval, sub_self]
  have hx : x ^ 4 = 0 := hfour x haug
  change (u.1 : A) ^ 4 = 1
  have hu : (u.1 : A) = 1 + x := by
    simp [x]
  rw [hu]
  calc
    (1 + x) ^ 4 = ((1 + x) ^ 2) ^ 2 := by
      rw [show 4 = 2 * 2 by omega, pow_mul]
    _ = (1 + x ^ 2) ^ 2 := by rw [one_add_sq_charTwo]
    _ = 1 + (x ^ 2) ^ 2 := one_add_sq_charTwo (x ^ 2)
    _ = 1 + x ^ 4 := by rw [← pow_mul]
    _ = 1 := by rw [hx, add_zero]

/-- The augmentation-one units of a fourth-nilpotent finite algebra form a finite `2`-group. -/
theorem augmentationOneUnits_isPGroup
    {A : Type} [Ring A] [Algebra (ZMod 2) A]
    (augmentation : A →ₐ[ZMod 2] ZMod 2)
    (hfour : ∀ x : A, augmentation x = 0 → x ^ 4 = 0) :
    IsPGroup 2 (AugmentationOneUnits augmentation) := by
  intro u
  exact ⟨2, by simpa using augmentationOneUnit_pow_four_eq_one augmentation hfour u⟩

/-- Fourfold vanishing in an augmentation kernel implies the pointwise fourth-power
condition used to construct the units `1+x`.  The fourfold form, unlike the pointwise form,
is strong enough to annihilate the fourth power of a noncommutative augmentation ideal. -/
theorem pow_four_zero_of_augmentation_product_four_zero
    {A : Type} [Ring A] [Algebra (ZMod 2) A]
    (augmentation : A →ₐ[ZMod 2] ZMod 2)
    (hprod : ∀ a b c d : A,
      augmentation a = 0 → augmentation b = 0 →
      augmentation c = 0 → augmentation d = 0 →
      a * b * c * d = 0)
    (x : A) (hx : augmentation x = 0) : x ^ 4 = 0 := by
  simpa [pow_succ, mul_assoc] using hprod x x x x hx hx hx hx

/-! ## The finite inhomogeneous Magnus-algebra certificate -/

/-- The exact finite algebra/rewrite data needed for a cubic detector.

The intended model has basis the words of length `<4`, with the full literal relator expansion
oriented by the unbordered leading word `X S`.  `cubic_normalization` is the finite rewrite
table, while `normal_independent` is its full-column-rank check in degree three. -/
structure SqCubicMagnusAlgebraCertificate (h : ℕ) (A : Type)
    [Ring A] [Algebra (ZMod 2) A] [Finite A] where
  augmentation : A →ₐ[ZMod 2] ZMod 2
  letter : Fin (sqRank h) → A
  letter_augmentation : ∀ i, augmentation (letter i) = 0
  augmentation_product_four_zero : ∀ a b c d : A,
    augmentation a = 0 → augmentation b = 0 →
    augmentation c = 0 → augmentation d = 0 →
    a * b * c * d = 0
  relator : sqRelWord (fun i => oneAddUnitOfPowFourZero (letter i)
    (pow_four_zero_of_augmentation_product_four_zero augmentation
      augmentation_product_four_zero (letter i) (letter_augmentation i))) = 1
  cubic_normalization : ∀ w : FiniteGeneratorWord (Fin (sqRank h)) 3,
    quadraticWordEval A letter (finiteGeneratorWordList 3 w) =
      Finsupp.linearCombination (ZMod 2)
        (fun v : SqQuadraticHomogeneousNormalWord h 3 =>
          quadraticWordEval A letter v.1.1)
        (sqQuadraticWordPBWNormal h 3 w)
  normal_independent : LinearIndependent (ZMod 2)
    (fun w : SqQuadraticHomogeneousNormalWord h 3 =>
      quadraticWordEval A letter w.1.1)

namespace SqCubicMagnusAlgebraCertificate

variable {h : ℕ} {A : Type} [Ring A] [Algebra (ZMod 2) A] [Finite A]
    (C : SqCubicMagnusAlgebraCertificate h A)

/-- Every element of the augmentation kernel has fourth power zero. -/
theorem augmentation_fourth_zero (x : A) (hx : C.augmentation x = 0) :
    x ^ 4 = 0 :=
  pow_four_zero_of_augmentation_product_four_zero C.augmentation
    C.augmentation_product_four_zero x hx

/-- The marked generator unit belongs to the augmentation-one subgroup. -/
def markedUnit (i : Fin (sqRank h)) : AugmentationOneUnits C.augmentation :=
  ⟨oneAddUnitOfPowFourZero (C.letter i)
      (C.augmentation_fourth_zero (C.letter i) (C.letter_augmentation i)), by
    apply Units.ext
    change C.augmentation (1 + C.letter i) = 1
    rw [map_add, map_one, C.letter_augmentation, add_zero]⟩

@[simp] theorem markedUnit_val (i : Fin (sqRank h)) :
    ((C.markedUnit i).1 : A) = 1 + C.letter i :=
  rfl

/-- The literal relator also dies in the augmentation-one subgroup. -/
theorem relator_markedUnit : sqRelWord C.markedUnit = 1 := by
  apply Subtype.ext
  change (AugmentationOneUnits C.augmentation).subtype
      (sqRelWord C.markedUnit) =
    (AugmentationOneUnits C.augmentation).subtype 1
  rw [map_sqRelWord, map_one]
  exact C.relator

/-- The finite algebra group is pro-`2` with its discrete topology. -/
theorem discreteAugmentationOneUnits_isProP :
    IsProP 2 (CubicDiscrete (AugmentationOneUnits C.augmentation)) := by
  apply isProP_of_isPGroup
  exact augmentationOneUnits_isPGroup C.augmentation C.augmentation_fourth_zero

/-- The cubic algebra certificate therefore gives a presentation map from `DSq h`. -/
def detectorHom : ContinuousMonoidHom (DSq h : Type)
    (CubicDiscrete (AugmentationOneUnits C.augmentation)) :=
  sqLiftHom h C.discreteAugmentationOneUnits_isProP C.markedUnit C.relator_markedUnit

@[simp] theorem detectorHom_gen (i : Fin (sqRank h)) :
    C.detectorHom (sqGen h i) = C.markedUnit i := by
  exact sqLiftHom_gen h C.discreteAugmentationOneUnits_isProP
    C.markedUnit C.relator_markedUnit i

/-! ## The finite detector coordinate and its group-algebra evaluation -/

/-- The open normal kernel of the cubic algebra-group detector. -/
def detectorKernel : OpenNormalSubgroup (DSq h : Type) where
  toSubgroup := C.detectorHom.toMonoidHom.ker
  isOpen' := by
    exact (isOpen_discrete ({1} : Set
      (CubicDiscrete (AugmentationOneUnits C.augmentation)))).preimage
        C.detectorHom.continuous_toFun

/-- The detector map factored through its finite quotient coordinate. -/
def detectorQuotientHom :
    ((DSq h : Type) ⧸ C.detectorKernel.toSubgroup) →*
      CubicDiscrete (AugmentationOneUnits C.augmentation) :=
  QuotientGroup.lift C.detectorKernel.toSubgroup C.detectorHom.toMonoidHom (by
    change C.detectorHom.toMonoidHom.ker ≤ C.detectorHom.toMonoidHom.ker
    exact le_rfl)

@[simp] theorem detectorQuotientHom_mk_gen (i : Fin (sqRank h)) :
    C.detectorQuotientHom
        (QuotientGroup.mk' C.detectorKernel.toSubgroup (sqGen h i)) =
      C.markedUnit i := by
  change C.detectorHom (sqGen h i) = C.markedUnit i
  exact C.detectorHom_gen i

/-- Forget the discrete topology wrapper while retaining multiplication. -/
def cubicDiscreteToMonoidHom (G : Type) [Group G] : CubicDiscrete G →* G where
  toFun := id
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The finite detector quotient represented by units of the Magnus algebra. -/
def detectorQuotientUnitHom :
    ((DSq h : Type) ⧸ C.detectorKernel.toSubgroup) →* Aˣ :=
  (AugmentationOneUnits C.augmentation).subtype.comp
    ((cubicDiscreteToMonoidHom (AugmentationOneUnits C.augmentation)).comp
      C.detectorQuotientHom)

/-- The multiplicative evaluation of a detector quotient element in the finite algebra. -/
def detectorQuotientAlgebraHom :
    ((DSq h : Type) ⧸ C.detectorKernel.toSubgroup) →* A :=
  (Units.coeHom A).comp C.detectorQuotientUnitHom

@[simp] theorem detectorQuotientAlgebraHom_mk_gen (i : Fin (sqRank h)) :
    C.detectorQuotientAlgebraHom
        (QuotientGroup.mk' C.detectorKernel.toSubgroup (sqGen h i)) =
      1 + C.letter i := by
  change ((((cubicDiscreteToMonoidHom (AugmentationOneUnits C.augmentation))
      (C.detectorQuotientHom
        (QuotientGroup.mk' C.detectorKernel.toSubgroup (sqGen h i))) :
          AugmentationOneUnits C.augmentation) : Aˣ) : A) = _
  rw [C.detectorQuotientHom_mk_gen]
  rfl

/-- Every represented detector element has augmentation one. -/
theorem detectorQuotientAlgebraHom_augmentation
    (q : (DSq h : Type) ⧸ C.detectorKernel.toSubgroup) :
    C.augmentation (C.detectorQuotientAlgebraHom q) = 1 := by
  let u : AugmentationOneUnits C.augmentation :=
    cubicDiscreteToMonoidHom (AugmentationOneUnits C.augmentation)
      (C.detectorQuotientHom q)
  have hu : Units.map C.augmentation.toMonoidHom u.1 = 1 := u.2
  have huval := congrArg Units.val hu
  change C.augmentation (u.1 : A) = 1 at huval
  exact huval

/-- Extend the detector quotient multiplicatively to its mod-two group algebra. -/
def detectorAlgebraEval :
    ModTwoGroupAlgebraLevel (DSq h : Type) C.detectorKernel →ₐ[ZMod 2] A :=
  MonoidAlgebra.lift (ZMod 2) A
    ((DSq h : Type) ⧸ C.detectorKernel.toSubgroup)
    C.detectorQuotientAlgebraHom

@[simp] theorem detectorAlgebraEval_single (q :
    (DSq h : Type) ⧸ C.detectorKernel.toSubgroup) (a : ZMod 2) :
    C.detectorAlgebraEval (MonoidAlgebra.single q a) =
      a • C.detectorQuotientAlgebraHom q := by
  exact MonoidAlgebra.lift_single _ q a

/-- On a marked generator difference, the finite group-algebra evaluation is the
corresponding Magnus letter. -/
@[simp] theorem detectorAlgebraEval_generatorDifference (i : Fin (sqRank h)) :
    C.detectorAlgebraEval
        (ModTwoCompletedGroupAlgebra.coordinate (DSq h : Type) C.detectorKernel
          (sqCompletedGeneratorDifference h i)) = C.letter i := by
  simp only [sqCompletedGeneratorDifference, map_sub,
    ModTwoCompletedGroupAlgebra.coordinate_of, map_one,
    detectorAlgebraEval_single, one_smul]
  rw [detectorQuotientAlgebraHom_mk_gen]
  change (1 + C.letter i) - 1 = C.letter i
  noncomm_ring

/-- The algebra value of every group-like difference lies in the augmentation kernel. -/
theorem detectorAlgebraEval_groupDifference_augmentation_zero
    (q : (DSq h : Type) ⧸ C.detectorKernel.toSubgroup) :
    C.augmentation
        (C.detectorAlgebraEval (MonoidAlgebra.single q 1 - 1)) = 0 := by
  rw [map_sub, map_one, C.detectorAlgebraEval_single, one_smul, map_sub,
    map_one, C.detectorQuotientAlgebraHom_augmentation, sub_self]

/-- The finite Magnus evaluation kills the fourth power of the ordinary finite-group
augmentation ideal.  This is the exact point at which fourfold, rather than merely
pointwise, nilpotence is required. -/
theorem detectorAlgebraEval_eq_zero_of_mem_augmentation_fourth
    (x : ModTwoGroupAlgebraLevel (DSq h : Type) C.detectorKernel)
    (hx : x ∈ modTwoFiniteAugmentationIdeal
        ((DSq h : Type) ⧸ C.detectorKernel.toSubgroup) ^ 4) :
    C.detectorAlgebraEval x = 0 := by
  classical
  let Q := (DSq h : Type) ⧸ C.detectorKernel.toSubgroup
  letI : Fintype Q := Fintype.ofFinite _
  letI : (modTwoFiniteAugmentationIdeal Q).IsTwoSided := by
    change (RingHom.ker (modTwoFiniteAugmentation Q).toRingHom).IsTwoSided
    infer_instance
  let g : Q → MonoidAlgebra (ZMod 2) Q := fun q =>
    MonoidAlgebra.single q 1 - 1
  obtain ⟨d, hd⟩ := idealPower_exists_finiteGeneratorMonomial
    (modTwoFiniteAugmentationIdeal Q) g
    modTwoFiniteAugmentationIdeal_exists_groupDifferenceCoefficients 4 x hx
  rw [hd, finiteGeneratorMonomialMap_apply, map_sum]
  apply Finset.sum_eq_zero
  rintro ⟨⟨⟨⟨u, q₁⟩, q₂⟩, q₃⟩, q₄⟩ hw
  rcases u with ⟨⟩
  have hprod : finiteGeneratorWordProduct g 4
      ((((PUnit.unit, q₁), q₂), q₃), q₄) =
      (MonoidAlgebra.single q₁ 1 - 1) *
        (MonoidAlgebra.single q₂ 1 - 1) *
        (MonoidAlgebra.single q₃ 1 - 1) *
        (MonoidAlgebra.single q₄ 1 - 1) := by
    simp [finiteGeneratorWordProduct, g]
  rw [hprod, map_mul]
  have hfour :
      C.detectorAlgebraEval (MonoidAlgebra.single q₁ 1 - 1) *
          C.detectorAlgebraEval (MonoidAlgebra.single q₂ 1 - 1) *
          C.detectorAlgebraEval (MonoidAlgebra.single q₃ 1 - 1) *
          C.detectorAlgebraEval (MonoidAlgebra.single q₄ 1 - 1) = 0 :=
    C.augmentation_product_four_zero _ _ _ _
      (C.detectorAlgebraEval_groupDifference_augmentation_zero q₁)
      (C.detectorAlgebraEval_groupDifference_augmentation_zero q₂)
      (C.detectorAlgebraEval_groupDifference_augmentation_zero q₃)
      (C.detectorAlgebraEval_groupDifference_augmentation_zero q₄)
  rw [map_mul, map_mul, map_mul, hfour, mul_zero]

/-! ## Evaluation of cubic words -/

/-- Coordinate projection followed by the finite Magnus evaluation sends a completed marked
word to the same word in the certificate letters. -/
theorem detectorAlgebraEval_coordinate_wordProduct :
    ∀ (n : ℕ) (w : FiniteGeneratorWord (Fin (sqRank h)) n),
      C.detectorAlgebraEval
          (ModTwoCompletedGroupAlgebra.coordinate (DSq h : Type) C.detectorKernel
            (finiteGeneratorWordProduct (sqCompletedGeneratorDifference h) n w)) =
        quadraticWordEval A C.letter (finiteGeneratorWordList n w) := by
  intro n
  induction n with
  | zero =>
      intro w
      simp
  | succ n ih =>
      rintro ⟨w, i⟩
      rw [finiteGeneratorWordProduct_succ, map_mul, map_mul, ih w,
        finiteGeneratorWordList_succ, quadraticWordEval_append_singleton,
        C.detectorAlgebraEval_generatorDifference]

/-- A scalar cubic monomial evaluates as the corresponding finite linear combination of
literal cubic words in the detector algebra. -/
theorem detectorAlgebraEval_scalarMonomial_coordinate
    (a : FiniteGeneratorWord (Fin (sqRank h)) 3 → ZMod 2) :
    C.detectorAlgebraEval
        (ModTwoCompletedGroupAlgebra.coordinate (DSq h : Type) C.detectorKernel
          (sqCompletedCubicScalarMonomial h a)) =
      ∑ w, a w • quadraticWordEval A C.letter
        (finiteGeneratorWordList 3 w) := by
  rw [sqCompletedCubicScalarMonomial, finiteGeneratorMonomialMap_apply,
    map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [map_mul]
  have hscalar :
      ModTwoCompletedGroupAlgebra.coordinate (DSq h : Type) C.detectorKernel
          (a w • (1 : ModTwoCompletedGroupAlgebra (DSq h : Type))) =
        a w • (1 : ModTwoGroupAlgebraLevel (DSq h : Type) C.detectorKernel) := by
    exact map_smul _ _ _
  rw [hscalar, map_mul, map_smul, map_one, smul_mul_assoc, one_mul,
    C.detectorAlgebraEval_coordinate_wordProduct]

/-- Membership in completed `J⁴` forces the detector evaluation of a scalar cubic monomial
to vanish. -/
theorem detectorAlgebraEval_scalarMonomial_eq_zero_of_mem_fourth
    (a : FiniteGeneratorWord (Fin (sqRank h)) 3 → ZMod 2)
    (ha : sqCompletedCubicScalarMonomial h a ∈
      modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 4) :
    ∑ w, a w • quadraticWordEval A C.letter
        (finiteGeneratorWordList 3 w) = 0 := by
  letI : Fintype ((DSq h : Type) ⧸ C.detectorKernel.toSubgroup) :=
    Fintype.ofFinite _
  have hcoord := modTwoCompletedAugmentationIdealPow_coordinate
    (DSq h : Type) C.detectorKernel 4 ha
  have hzero := C.detectorAlgebraEval_eq_zero_of_mem_augmentation_fourth
    (ModTwoCompletedGroupAlgebra.coordinate (DSq h : Type) C.detectorKernel
      (sqCompletedCubicScalarMonomial h a)) hcoord
  rw [C.detectorAlgebraEval_scalarMonomial_coordinate] at hzero
  exact hzero

/-! ## The exact detector/column split -/

/-- Cubic PBW normalization is respected by evaluation in the certificate algebra.  This is
the finite rewrite table: one equality for each literal length-three word. -/
theorem detectorCubicWordSum_eq_normalLinearCombination
    (a : FiniteGeneratorWord (Fin (sqRank h)) 3 → ZMod 2) :
    ∑ w, a w • quadraticWordEval A C.letter (finiteGeneratorWordList 3 w) =
      Finsupp.linearCombination (ZMod 2)
        (fun v : SqQuadraticHomogeneousNormalWord h 3 =>
          quadraticWordEval A C.letter v.1.1)
        (sqCubicScalarPBWNormalMap h a) := by
  rw [sqCubicScalarPBWNormalMap_apply, map_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [map_smul, C.cubic_normalization]

include C

/-- The finite algebra detector proves the difficult direction of cubic exactness: no
nonzero PBW-normal cubic combination can disappear in completed `J³/J⁴`. -/
theorem scalarPBWNormal_eq_zero_of_monomial_mem_fourth
    (a : FiniteGeneratorWord (Fin (sqRank h)) 3 → ZMod 2)
    (ha : sqCompletedCubicScalarMonomial h a ∈
      modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 4) :
    sqCubicScalarPBWNormalMap h a = 0 := by
  have heval := detectorAlgebraEval_scalarMonomial_eq_zero_of_mem_fourth C a ha
  rw [detectorCubicWordSum_eq_normalLinearCombination C] at heval
  exact (linearIndependent_iff.mp C.normal_independent)
    (sqCubicScalarPBWNormalMap h a) heval

/-- The complementary, purely completed-algebra column obligation.  It says that every
finite PBW dependency is sound modulo completed `J⁴`; unlike detector separation, it follows
from multiplying the already-proved quadratic relation in `J³` by one marked difference. -/
def SqCompletedCubicPBWColumnSound (h : ℕ) : Prop :=
  ∀ a : FiniteGeneratorWord (Fin (sqRank h)) 3 → ZMod 2,
    sqCubicScalarPBWNormalMap h a = 0 →
      sqCompletedCubicScalarMonomial h a ∈
        modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 4

/-- Separation of completed cubic columns: completed `J⁴` contains no nonzero PBW-normal
cubic vector. -/
def SqCompletedCubicPBWColumnSeparated (h : ℕ) : Prop :=
  ∀ a : FiniteGeneratorWord (Fin (sqRank h)) 3 → ZMod 2,
    sqCompletedCubicScalarMonomial h a ∈
        modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 4 →
      sqCubicScalarPBWNormalMap h a = 0

omit C

/-- Exact bookkeeping: scalar cubic exactness is precisely column soundness plus column
separation. -/
theorem sqCompletedCubicScalarKernelExact_iff_sound_and_separated (h : ℕ) :
    SqCompletedCubicScalarKernelExact h ↔
      SqCompletedCubicPBWColumnSound h ∧
        SqCompletedCubicPBWColumnSeparated h := by
  constructor
  · intro H
    exact ⟨fun a => (H a).1, fun a => (H a).2⟩
  · rintro ⟨Hsound, Hseparated⟩ a
    exact ⟨Hsound a, Hseparated a⟩

/-- Consequently the full completed cubic theorem has the same exact two-part split. -/
theorem sqCompletedCubicKernelIdentity_iff_sound_and_separated (h : ℕ) :
    SqCompletedMonomialPBWKernelIdentity h 3 ↔
      SqCompletedCubicPBWColumnSound h ∧
        SqCompletedCubicPBWColumnSeparated h := by
  rw [sqCompletedMonomialPBWKernelIdentity_three_iff_scalar,
    sqCompletedCubicScalarKernelExact_iff_sound_and_separated]

include C

/-- A finite inhomogeneous Magnus-algebra certificate supplies column separation. -/
theorem columnSeparated : SqCompletedCubicPBWColumnSeparated h :=
  fun a => scalarPBWNormal_eq_zero_of_monomial_mem_fourth C a

/-- Column soundness plus one finite inhomogeneous Magnus-algebra detector gives the exact
scalar cubic kernel theorem. -/
theorem scalarKernelExact_of_columnSound
    (Hsound : SqCompletedCubicPBWColumnSound h) :
    SqCompletedCubicScalarKernelExact h := by
  intro a
  exact ⟨Hsound a, scalarPBWNormal_eq_zero_of_monomial_mem_fourth C a⟩

/-- Constructor from the two concrete finite obligations to the cubic PBW matrix certificate. -/
def pbwMatrixCertificateOfColumnSound
    (Hsound : SqCompletedCubicPBWColumnSound h) :
    SqCompletedCubicPBWMatrixCertificate h :=
  sqCompletedCubicPBWMatrixCertificateOfScalarKernelExact h
    (scalarKernelExact_of_columnSound C Hsound)

/-- The same two obligations establish the full completed cubic Magnus--Labute identity. -/
theorem completedCubicKernelIdentity_of_columnSound
    (Hsound : SqCompletedCubicPBWColumnSound h) :
    SqCompletedMonomialPBWKernelIdentity h 3 :=
  (sqCompletedMonomialPBWKernelIdentity_three_iff_scalar h).2
    (scalarKernelExact_of_columnSound C Hsound)

/-- **Sharp reduction after constructing the detector.**  With a finite inhomogeneous
Magnus-algebra certificate in hand, the full completed cubic theorem is equivalent to the
forward finite column-rewrite check alone. -/
theorem completedCubicKernelIdentity_iff_columnSound :
    SqCompletedMonomialPBWKernelIdentity h 3 ↔
      SqCompletedCubicPBWColumnSound h := by
  constructor
  · intro H a ha
    exact ((sqCompletedMonomialPBWKernelIdentity_three_iff_scalar h).1 H a).1 ha
  · exact completedCubicKernelIdentity_of_columnSound C

/-- Equivalently, after constructing the detector, existence of the requested full-rank PBW
matrix is exactly the forward column-rewrite check. -/
theorem nonempty_pbwMatrixCertificate_iff_columnSound :
    Nonempty (SqCompletedCubicPBWMatrixCertificate h) ↔
      SqCompletedCubicPBWColumnSound h := by
  rw [← completedCubicKernelIdentity_iff_columnSound C,
    sqCompletedMonomialPBWKernelIdentity_three_iff_matrix]

end SqCubicMagnusAlgebraCertificate

end

end GQ2.ContCoh

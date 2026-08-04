/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3FoxMagnusJet
import GQ2.Dyadic.Count.H3SqQuadraticDiamond
import GQ2.Dyadic.Count.H3AugmentationSeparation

/-!
# From finite Fox moments to completed associated-graded regularity

This file isolates the remaining algebraic comparison between the literal completed Fox row
and the quadratic Magnus algebra.  There are two parts.

First, a character of a finite group defines a canonical first Magnus moment on its mod-two
group algebra.  The moment satisfies the Leibniz rule with respect to augmentation and hence
vanishes on the square of the augmentation ideal.  Thus it is genuinely a coordinate on the
cotangent quotient `I / I^2`, not merely a functional on a chosen Fox representative.  For the
elementary-abelian marking of the improved square relator, the already-proved word-level
Fox--Magnus theorem computes every such coordinate of the actual derivative row.

Second, `CompletedMagnusGradedIdentification` records the purely algebraic all-layer statement
still needed to transport that first jet to the completed group algebra: each augmentation
layer embeds in a graded algebra, the next layer is exactly its kernel, and multiplication by
the actual row is multiplication by a specified homogeneous row.  It has no cohomology,
injectivity, or exactness field.  A row which is common-annihilator-free in the graded algebra
then gives `CompletedRowAugmentationInitialRegular` formally.  Specializing to the square
quadratic algebra reduces the completed initial-regularity theorem to this one honest graded
identification.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2 GQ2.FoxH GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.SqCore GQ2.Dyadic.MarkedCore
open Multiplicative

/-! ## The canonical finite first Magnus moment -/

variable {Q I : Type} [Group Q]

/-- The coefficient-weighted first moment on `F₂[Q]` attached to a mod-two character.
On a basis element `[q]` it has value `chi(q)`. -/
def modTwoGroupAlgebraLinearMoment (chi : Q →* Multiplicative (ZMod 2)) :
    MonoidAlgebra (ZMod 2) Q →ₗ[ZMod 2] ZMod 2 :=
  Finsupp.lsum (ZMod 2) fun q =>
    LinearMap.toSpanSingleton (ZMod 2) (ZMod 2) (toAdd (chi q))

@[simp] theorem modTwoGroupAlgebraLinearMoment_single
    (chi : Q →* Multiplicative (ZMod 2)) (q : Q) (a : ZMod 2) :
    modTwoGroupAlgebraLinearMoment chi (MonoidAlgebra.single q a) =
      a * toAdd (chi q) := by
  change ((Finsupp.lsum (ZMod 2) fun q =>
      LinearMap.toSpanSingleton (ZMod 2) (ZMod 2) (toAdd (chi q))) :
        (Q →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2) (Finsupp.single q a) = _
  rw [Finsupp.lsum_single]
  simp [LinearMap.toSpanSingleton_apply, smul_eq_mul]

@[simp] theorem modTwoGroupAlgebraLinearMoment_of
    (chi : Q →* Multiplicative (ZMod 2)) (q : Q) :
    modTwoGroupAlgebraLinearMoment chi (MonoidAlgebra.of (ZMod 2) Q q) =
      toAdd (chi q) := by
  change modTwoGroupAlgebraLinearMoment chi (MonoidAlgebra.single q 1) = _
  simp

/-- The first moment satisfies the augmentation Leibniz rule. -/
theorem modTwoGroupAlgebraLinearMoment_mul
    (chi : Q →* Multiplicative (ZMod 2))
    (x y : MonoidAlgebra (ZMod 2) Q) :
    modTwoGroupAlgebraLinearMoment chi (x * y) =
      modTwoGroupAlgebraLinearMoment chi x * modTwoFiniteAugmentation Q y +
        modTwoFiniteAugmentation Q x * modTwoGroupAlgebraLinearMoment chi y := by
  induction x using MonoidAlgebra.induction_on with
  | hM q =>
      induction y using MonoidAlgebra.induction_on with
      | hM r =>
          simp only [modTwoGroupAlgebraLinearMoment_of,
            modTwoFiniteAugmentation]
          simp [MonoidAlgebra.lift_single, toAdd_mul]
      | hadd y z hy hz =>
          simp only [mul_add, map_add, hy, hz]
          ring
      | hsmul a y hy =>
          rw [mul_smul_comm, map_smul, map_smul, map_smul, hy]
          simp only [smul_eq_mul]
          ring
  | hadd x z hx hz =>
      simp only [add_mul, map_add, hx, hz]
      ring
  | hsmul a x hx =>
      rw [smul_mul_assoc, map_smul, map_smul, map_smul, hx]
      simp only [smul_eq_mul]
      ring

/-- The finite moment of one group-algebra component is the existing relation-module moment. -/
theorem modTwoGroupAlgebraLinearMoment_regularModTwoComponent
    [DecidableEq I]
    (chi : Q →* Multiplicative (ZMod 2)) (i : I)
    (c : RegularModTwoRelationModule Q I) :
    modTwoGroupAlgebraLinearMoment chi (regularModTwoComponent i c) =
      regularModTwoLinearMoment chi i c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨q, j⟩
      simp only [map_add, regularModTwoComponent_single,
        regularModTwoLinearMoment_single, ih]
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]

/-- Component extraction followed by group-algebra augmentation is the coefficient-sum
augmentation already used on regular relation modules. -/
theorem modTwoFiniteAugmentation_regularModTwoComponent
    [DecidableEq I] (i : I) (c : RegularModTwoRelationModule Q I) :
    modTwoFiniteAugmentation Q (regularModTwoComponent i c) =
      regularModTwoComponentAugmentation i c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp [regularModTwoComponentAugmentation]
  | single_add p a c hp ha ih =>
      rcases p with ⟨q, j⟩
      simp only [map_add, regularModTwoComponent_single,
        regularModTwoComponentAugmentation_single, ih]
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]

/-- A first moment vanishes on a product of two augmentation-zero elements. -/
theorem modTwoGroupAlgebraLinearMoment_mul_eq_zero_of_mem_augmentation
    (chi : Q →* Multiplicative (ZMod 2))
    {x y : MonoidAlgebra (ZMod 2) Q}
    (hx : x ∈ modTwoFiniteAugmentationIdeal Q)
    (hy : y ∈ modTwoFiniteAugmentationIdeal Q) :
    modTwoGroupAlgebraLinearMoment chi (x * y) = 0 := by
  rw [modTwoGroupAlgebraLinearMoment_mul]
  rw [modTwoFiniteAugmentationIdeal, RingHom.mem_ker] at hx hy
  change modTwoFiniteAugmentation Q x = 0 at hx
  change modTwoFiniteAugmentation Q y = 0 at hy
  rw [hx, hy, mul_zero, zero_mul, add_zero]

/-- Consequently every character moment kills `I²`, so it descends to the canonical first
augmentation quotient. -/
theorem modTwoGroupAlgebraLinearMoment_eq_zero_of_mem_augmentation_sq
    (chi : Q →* Multiplicative (ZMod 2))
    {x : MonoidAlgebra (ZMod 2) Q}
    (hx : x ∈ modTwoFiniteAugmentationIdeal Q ^ 2) :
    modTwoGroupAlgebraLinearMoment chi x = 0 := by
  rw [Submodule.pow_succ] at hx
  simp only [Submodule.pow_one] at hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro a ha b hb
    exact modTwoGroupAlgebraLinearMoment_mul_eq_zero_of_mem_augmentation chi ha hb
  · intro a b ha hb
    rw [map_add, ha, hb, add_zero]

/-- The actual improved square Fox row has exactly the formal degree-one coefficient table in
the finite cotangent coordinate attached to every elementary-abelian coordinate character. -/
theorem modTwoFoxDerivative_sqDiscreteRelator_firstAugmentationCoordinate
    (h : ℕ) (i a : Fin (sqRank h)) :
    modTwoGroupAlgebraLinearMoment
        (multiplicativeModTwoCharacter (sqMagnusOneCoordinate h a))
        (regularModTwoComponent i
          (modTwoFoxDerivative (sqMagnusOneMark h) (sqDiscreteRelator h))) =
      sqQuadraticFoxLinearInitialCoefficient h i a := by
  rw [modTwoGroupAlgebraLinearMoment_regularModTwoComponent]
  exact modTwoFoxDerivative_sqDiscreteRelator_linearMoment h i a

/-- Each entry of the literal elementary-abelian square Fox row lies in the finite augmentation
ideal, so the preceding coordinate really is evaluated on `I / I²`. -/
theorem regularModTwoComponent_sqDiscreteRelator_mem_augmentation
    (h : ℕ) (i : Fin (sqRank h)) :
    regularModTwoComponent i
        (modTwoFoxDerivative (sqMagnusOneMark h) (sqDiscreteRelator h)) ∈
      modTwoFiniteAugmentationIdeal
        (Multiplicative (Fin (sqRank h) → ZMod 2)) := by
  rw [modTwoFiniteAugmentationIdeal, RingHom.mem_ker]
  change modTwoFiniteAugmentation
      (Multiplicative (Fin (sqRank h) → ZMod 2))
        (regularModTwoComponent i
          (modTwoFoxDerivative (sqMagnusOneMark h) (sqDiscreteRelator h))) = 0
  rw [modTwoFiniteAugmentation_regularModTwoComponent,
    regularModTwoComponentAugmentation_modTwoFoxDerivative]
  have hu := congrArg
    (regularModTwoComponentAugmentation (L := Unit) i)
    (modTwoFoxDerivative_sqDiscreteRelator_unit h)
  rw [map_zero,
    regularModTwoComponentAugmentation_modTwoFoxDerivative] at hu
  exact hu

/-! ## The actual completed first-layer coordinate -/

/-- The elementary-abelian target carrying all first Magnus coordinates at once. -/
abbrev SqMagnusOneTarget (h : ℕ) :=
  Multiplicative (Fin (sqRank h) → ZMod 2)

/-- The improved square relator dies under the universal elementary-abelian marking. -/
theorem sqMagnusOneMark_relator (h : ℕ) :
    sqRelWord (sqMagnusOneMark h) = 1 := by
  rw [sqRelWord_comm]
  have hsquare (z : SqMagnusOneTarget h) : z ^ 2 = 1 := by
    rw [pow_two]
    apply toAdd.injective
    ext i
    exact CharTwo.add_self_eq_zero _
  have hfourth (z : SqMagnusOneTarget h) : z ^ 4 = 1 := by
    rw [show 4 = 2 * 2 by omega, pow_mul, hsquare]
  rw [hfourth, hsquare]
  simp

/-- The simultaneous elementary-abelian first Magnus quotient of `DSq h`. -/
noncomputable def sqMagnusOneHom (h : ℕ) :
    ContinuousMonoidHom (DSq h : Type) (SqMagnusOneTarget h) :=
  sqLiftHom h
    (isProP_of_isPGroup (IsPGroup.of_card (p := 2) (n := sqRank h) (by
      rw [Nat.card_eq_fintype_card]
      simp [SqMagnusOneTarget])))
    (sqMagnusOneMark h) (sqMagnusOneMark_relator h)

@[simp] theorem sqMagnusOneHom_gen (h : ℕ) (i : Fin (sqRank h)) :
    sqMagnusOneHom h (sqGen h i) = sqMagnusOneMark h i := by
  rw [sqMagnusOneHom, sqLiftHom_gen]

/-- The open-normal kernel defining the actual finite quotient used for the completed first
Magnus coordinate. -/
noncomputable def sqMagnusOneKernel (h : ℕ) :
    OpenNormalSubgroup (DSq h : Type) where
  toSubgroup := (sqMagnusOneHom h).toMonoidHom.ker
  isOpen' := by
    change IsOpen ((sqMagnusOneHom h) ⁻¹'
      ({1} : Set (SqMagnusOneTarget h)))
    exact (isOpen_discrete ({1} : Set (SqMagnusOneTarget h))).preimage
      (sqMagnusOneHom h).continuous_toFun

/-- The induced homomorphism from the kernel quotient to the simultaneous Magnus target. -/
noncomputable def sqMagnusOneQuotientHom (h : ℕ) :
    ((DSq h : Type) ⧸ (sqMagnusOneKernel h).toSubgroup) →*
      SqMagnusOneTarget h :=
  QuotientGroup.lift (sqMagnusOneKernel h).toSubgroup
    (sqMagnusOneHom h).toMonoidHom (by
      change (sqMagnusOneHom h).toMonoidHom.ker ≤ _
      exact le_refl _)

@[simp] theorem sqMagnusOneQuotientHom_marking
    (h : ℕ) (i : Fin (sqRank h)) :
    sqMagnusOneQuotientHom h
        (QuotientGroup.mk' (sqMagnusOneKernel h).toSubgroup (sqGen h i)) =
      sqMagnusOneMark h i := by
  exact (QuotientGroup.lift_mk' _ _ (sqGen h i)).trans
    (sqMagnusOneHom_gen h i)

/-- First moments commute with pushforward of group algebras. -/
theorem modTwoGroupAlgebraLinearMoment_mapDomain
    {Q' : Type} [Group Q'] (phi : Q →* Q')
    (chi : Q' →* Multiplicative (ZMod 2))
    (x : MonoidAlgebra (ZMod 2) Q) :
    modTwoGroupAlgebraLinearMoment chi
        (MonoidAlgebra.mapDomainAlgHom (ZMod 2) (ZMod 2) phi x) =
      modTwoGroupAlgebraLinearMoment (chi.comp phi) x := by
  induction x using MonoidAlgebra.induction_on with
  | hM q => simp
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | hsmul a x hx => simp only [map_smul, hx]

/-- **Actual completed first jet.**  Evaluate the completed Fox row at the canonical open
elementary-abelian quotient, then apply any coordinate character.  The result is exactly the
formal quadratic coefficient table.  Together with
`modTwoGroupAlgebraLinearMoment_eq_zero_of_mem_augmentation_sq`, this identifies the row's
finite-coordinate class modulo the square of the augmentation ideal. -/
theorem sqCompletedModTwoFoxDerivativeRow_firstAugmentationCoordinate
    (h : ℕ) (i a : Fin (sqRank h)) :
    modTwoGroupAlgebraLinearMoment
        ((multiplicativeModTwoCharacter (sqMagnusOneCoordinate h a)).comp
          (sqMagnusOneQuotientHom h))
        (ModTwoCompletedGroupAlgebra.coordinate (DSq h : Type)
          (sqMagnusOneKernel h) (sqCompletedModTwoFoxDerivativeRow h i)) =
      sqQuadraticFoxLinearInitialCoefficient h i a := by
  rw [sqCompletedModTwoFoxDerivativeRow_coordinate]
  let m : Fin (sqRank h) →
      ((DSq h : Type) ⧸ (sqMagnusOneKernel h).toSubgroup) :=
    fun k => QuotientGroup.mk' (sqMagnusOneKernel h).toSubgroup (sqGen h k)
  let phi := sqMagnusOneQuotientHom h
  let chi := multiplicativeModTwoCharacter (sqMagnusOneCoordinate h a)
  calc
    modTwoGroupAlgebraLinearMoment (chi.comp phi)
        (regularModTwoComponent i
          (modTwoFoxDerivative m (sqDiscreteRelator h))) =
      modTwoGroupAlgebraLinearMoment chi
        (MonoidAlgebra.mapDomainAlgHom (ZMod 2) (ZMod 2) phi
          (regularModTwoComponent i
            (modTwoFoxDerivative m (sqDiscreteRelator h)))) := by
              rw [modTwoGroupAlgebraLinearMoment_mapDomain]
    _ = modTwoGroupAlgebraLinearMoment chi
        (regularModTwoComponent i
          (regularModTwoPushforward phi (Fin (sqRank h))
            (modTwoFoxDerivative m (sqDiscreteRelator h)))) := by
              rw [regularModTwoComponent_pushforward]
    _ = modTwoGroupAlgebraLinearMoment chi
        (regularModTwoComponent i
          (modTwoFoxDerivative (sqMagnusOneMark h) (sqDiscreteRelator h))) := by
              rw [regularModTwoPushforward_modTwoFoxDerivative]
              congr 3
              funext k
              exact sqMagnusOneQuotientHom_marking h k
    _ = sqQuadraticFoxLinearInitialCoefficient h i a :=
      modTwoFoxDerivative_sqDiscreteRelator_firstAugmentationCoordinate h i a

/-- The actual completed first-layer functional kills the square of the completed augmentation
ideal.  This is the finite-coordinate quotient statement needed before constructing all graded
layers. -/
theorem sqCompletedFirstMoment_eq_zero_of_mem_augmentation_sq
    (h : ℕ) (a : Fin (sqRank h))
    {x : ModTwoCompletedGroupAlgebra (DSq h : Type)}
    (hx : x ∈ modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 2) :
    modTwoGroupAlgebraLinearMoment
        ((multiplicativeModTwoCharacter (sqMagnusOneCoordinate h a)).comp
          (sqMagnusOneQuotientHom h))
        (ModTwoCompletedGroupAlgebra.coordinate (DSq h : Type)
          (sqMagnusOneKernel h) x) = 0 := by
  apply modTwoGroupAlgebraLinearMoment_eq_zero_of_mem_augmentation_sq
  exact modTwoCompletedAugmentationIdealPow_coordinate
    (DSq h : Type) (sqMagnusOneKernel h) 2 hx

/-! ## Algebraic realization of literal completed Fox derivatives -/

/-- Send the ordinary group algebra `F₂[G]` to the explicit completed group algebra by sending
each basis group element to its compatible family of finite-quotient basis elements. -/
def modTwoGroupAlgebraToCompleted
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] :
    MonoidAlgebra (ZMod 2) G →ₐ[ZMod 2] ModTwoCompletedGroupAlgebra G :=
  MonoidAlgebra.lift (ZMod 2) (ModTwoCompletedGroupAlgebra G) G
    (ModTwoCompletedGroupAlgebra.of G)

@[simp] theorem modTwoGroupAlgebraToCompleted_of
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (g : G) :
    modTwoGroupAlgebraToCompleted G (MonoidAlgebra.of (ZMod 2) G g) =
      ModTwoCompletedGroupAlgebra.of G g := by
  simp [modTwoGroupAlgebraToCompleted]

/-- At every finite level, the algebraic-to-completed map is ordinary pushforward along the
quotient homomorphism. -/
theorem modTwoGroupAlgebraToCompleted_coordinate
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (U : OpenNormalSubgroup G) (x : MonoidAlgebra (ZMod 2) G) :
    ModTwoCompletedGroupAlgebra.coordinate G U
        (modTwoGroupAlgebraToCompleted G x) =
      MonoidAlgebra.mapDomainAlgHom (ZMod 2) (ZMod 2)
        (QuotientGroup.mk' U.toSubgroup) x := by
  induction x using MonoidAlgebra.induction_on with
  | hM g =>
      rw [modTwoGroupAlgebraToCompleted_of,
        ModTwoCompletedGroupAlgebra.coordinate_of]
      change MonoidAlgebra.single (QuotientGroup.mk' U.toSubgroup g) 1 =
        MonoidAlgebra.mapDomainAlgHom (ZMod 2) (ZMod 2)
          (QuotientGroup.mk' U.toSubgroup) (MonoidAlgebra.single g 1)
      rw [MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single]
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | hsmul a x hx => simp only [map_smul, hx]

/-- A literal completed Fox derivative is the image of the same finite-support Fox derivative
computed directly in `F₂[G]`. -/
theorem completedModTwoFoxDerivativeRow_eq_toCompleted
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    {I : Type} (m : I → G) (w : FreeGroup I) (i : I) :
    completedModTwoFoxDerivativeRow G m w i =
      modTwoGroupAlgebraToCompleted G
        (regularModTwoComponent i (modTwoFoxDerivative m w)) := by
  apply ModTwoCompletedGroupAlgebra.ext G
  intro U
  rw [completedModTwoFoxDerivativeRow_coordinate,
    modTwoGroupAlgebraToCompleted_coordinate,
    ← regularModTwoComponent_pushforward,
    regularModTwoPushforward_modTwoFoxDerivative]

/-- Every ordinary group-algebra element differs from its augmentation scalar by an element
which maps into the algebraic completed augmentation ideal. -/
theorem modTwoGroupAlgebraToCompleted_sub_augmentation_mem
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (x : MonoidAlgebra (ZMod 2) G) :
    modTwoGroupAlgebraToCompleted G x -
        algebraMap (ZMod 2) (ModTwoCompletedGroupAlgebra G)
          (modTwoFiniteAugmentation G x) ∈
      modTwoCompletedAugmentationIdeal G := by
  induction x using MonoidAlgebra.induction_on with
  | hM g =>
      have haug : modTwoFiniteAugmentation G
          (MonoidAlgebra.of (ZMod 2) G g) = 1 := by
        simp [modTwoFiniteAugmentation]
      rw [modTwoGroupAlgebraToCompleted_of, haug, map_one]
      rw [modTwoCompletedAugmentationIdeal]
      apply Submodule.subset_span
      exact ⟨g, rfl⟩
  | hadd x y hx hy =>
      simp only [map_add]
      convert (modTwoCompletedAugmentationIdeal G).add_mem hx hy using 1
      abel
  | hsmul a x hx =>
      simp only [map_smul]
      have hm := (modTwoCompletedAugmentationIdeal G).mul_mem_left
        (algebraMap (ZMod 2) (ModTwoCompletedGroupAlgebra G) a) hx
      simpa [Algebra.smul_def, mul_sub] using hm

/-- Augmentation-zero ordinary group-algebra elements therefore map into the algebraic
completed augmentation ideal. -/
theorem modTwoGroupAlgebraToCompleted_mem_augmentation_of_aug_eq_zero
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    {x : MonoidAlgebra (ZMod 2) G} (hx : modTwoFiniteAugmentation G x = 0) :
    modTwoGroupAlgebraToCompleted G x ∈ modTwoCompletedAugmentationIdeal G := by
  have h := modTwoGroupAlgebraToCompleted_sub_augmentation_mem G x
  rw [hx, map_zero, sub_zero] at h
  exact h

/-- The actual completed improved-square Fox row lies in augmentation degree one. -/
theorem sqCompletedModTwoFoxDerivativeRow_mem_augmentation
    (h : ℕ) (i : Fin (sqRank h)) :
    sqCompletedModTwoFoxDerivativeRow h i ∈
      modTwoCompletedAugmentationIdeal (DSq h : Type) := by
  rw [sqCompletedModTwoFoxDerivativeRow,
    completedModTwoFoxDerivativeRow_eq_toCompleted]
  apply modTwoGroupAlgebraToCompleted_mem_augmentation_of_aug_eq_zero
  rw [modTwoFiniteAugmentation_regularModTwoComponent,
    regularModTwoComponentAugmentation_modTwoFoxDerivative]
  have hu := congrArg
    (regularModTwoComponentAugmentation (L := Unit) i)
    (modTwoFoxDerivative_sqDiscreteRelator_unit h)
  rw [map_zero,
    regularModTwoComponentAugmentation_modTwoFoxDerivative] at hu
  exact hu

/-! ## Unconditional degree-zero and degree-one maps -/

/-- Augmentation of a completed group algebra, evaluated at one finite coordinate.  Transition
compatibility implies the same scalar is obtained at every coordinate; the present form is the
one needed for the canonical square Magnus quotient. -/
def modTwoCompletedAugmentationCoordinate
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (U : OpenNormalSubgroup G) :
    ModTwoCompletedGroupAlgebra G →ₗ[ZMod 2] ZMod 2 :=
  (modTwoFiniteAugmentation (G ⧸ U.toSubgroup)).toLinearMap.comp
    (ModTwoCompletedGroupAlgebra.coordinate G U).toLinearMap

@[simp] theorem modTwoCompletedAugmentationCoordinate_one
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (U : OpenNormalSubgroup G) :
    modTwoCompletedAugmentationCoordinate G U 1 = 1 := by
  simp [modTwoCompletedAugmentationCoordinate]

/-- The algebraic completed augmentation ideal is contained in the kernel of every finite
coordinate augmentation.  Equality is the genuine degree-zero generation theorem. -/
theorem modTwoCompletedAugmentationCoordinate_eq_zero_of_mem
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (U : OpenNormalSubgroup G) {x : ModTwoCompletedGroupAlgebra G}
    (hx : x ∈ modTwoCompletedAugmentationIdeal G) :
    modTwoCompletedAugmentationCoordinate G U x = 0 := by
  have hcoord := modTwoCompletedAugmentationIdeal_coordinate G U hx
  change modTwoFiniteAugmentation (G ⧸ U.toSubgroup)
    (ModTwoCompletedGroupAlgebra.coordinate G U x) = 0 at hcoord
  exact hcoord

/-- Every finite-coordinate completed augmentation is onto. -/
theorem modTwoCompletedAugmentationCoordinate_surjective
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (U : OpenNormalSubgroup G) :
    Function.Surjective (modTwoCompletedAugmentationCoordinate G U) := by
  intro r
  refine ⟨r • (1 : ModTwoCompletedGroupAlgebra G), ?_⟩
  simp

/-- The simultaneous actual first-moment map on the completed square group algebra. -/
def sqCompletedFirstMomentMap (h : ℕ) :
    ModTwoCompletedGroupAlgebra (DSq h : Type) →ₗ[ZMod 2]
      (Fin (sqRank h) → ZMod 2) where
  toFun x a :=
    modTwoGroupAlgebraLinearMoment
      ((multiplicativeModTwoCharacter (sqMagnusOneCoordinate h a)).comp
        (sqMagnusOneQuotientHom h))
      (ModTwoCompletedGroupAlgebra.coordinate (DSq h : Type)
        (sqMagnusOneKernel h) x)
  map_add' x y := by
    funext a
    simp
  map_smul' r x := by
    funext a
    simp

/-- The degree-one map kills the square of the completed augmentation ideal. -/
theorem sqCompletedFirstMomentMap_eq_zero_of_mem_augmentation_sq
    (h : ℕ) {x : ModTwoCompletedGroupAlgebra (DSq h : Type)}
    (hx : x ∈ modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 2) :
    sqCompletedFirstMomentMap h x = 0 := by
  funext a
  exact sqCompletedFirstMoment_eq_zero_of_mem_augmentation_sq h a hx

/-- The degree-one map sends every literal completed Fox derivative to its certified formal
linear initial form. -/
theorem sqCompletedFirstMomentMap_foxRow (h : ℕ) (i : Fin (sqRank h)) :
    sqCompletedFirstMomentMap h (sqCompletedModTwoFoxDerivativeRow h i) =
      sqQuadraticFoxLinearInitialCoefficient h i := by
  funext a
  exact sqCompletedModTwoFoxDerivativeRow_firstAugmentationCoordinate h i a

/-- The literal Fox rows map to a permuted standard basis, so the actual completed first-moment
map is onto unconditionally. -/
theorem sqCompletedFirstMomentMap_surjective (h : ℕ) :
    Function.Surjective (sqCompletedFirstMomentMap h) := by
  intro v
  refine ⟨∑ a, v a •
    sqCompletedModTwoFoxDerivativeRow h (sqInitialPartner h a), ?_⟩
  rw [map_sum]
  simp_rw [map_smul, sqCompletedFirstMomentMap_foxRow]
  funext b
  simp [sqQuadraticFoxLinearInitialCoefficient_eq]

/-- Restrict the completed first-moment map to the actual augmentation ideal. -/
def sqCompletedFirstMomentOnAugmentationIdeal (h : ℕ) :
    (modTwoCompletedAugmentationIdeal (DSq h : Type)).toAddSubgroup →ₗ[ZMod 2]
      (Fin (sqRank h) → ZMod 2) where
  toFun x := sqCompletedFirstMomentMap h x.1
  map_add' x y := by simp
  map_smul' r x := by simp

/-- Because every literal completed Fox row lies in `J`, their permuted-basis calculation makes
the degree-one map onto even after restricting its domain to the augmentation ideal. -/
theorem sqCompletedFirstMomentOnAugmentationIdeal_surjective (h : ℕ) :
    Function.Surjective (sqCompletedFirstMomentOnAugmentationIdeal h) := by
  intro v
  let x : ModTwoCompletedGroupAlgebra (DSq h : Type) :=
    ∑ a, v a • sqCompletedModTwoFoxDerivativeRow h (sqInitialPartner h a)
  have hx : x ∈ modTwoCompletedAugmentationIdeal (DSq h : Type) := by
    apply Ideal.sum_mem
    intro a ha
    rw [Algebra.smul_def]
    exact (modTwoCompletedAugmentationIdeal (DSq h : Type)).mul_mem_left _
      (sqCompletedModTwoFoxDerivativeRow_mem_augmentation h
        (sqInitialPartner h a))
  refine ⟨⟨x, hx⟩, ?_⟩
  change sqCompletedFirstMomentMap h x = v
  rw [show x = ∑ a, v a •
      sqCompletedModTwoFoxDerivativeRow h (sqInitialPartner h a) from rfl,
    map_sum]
  simp_rw [map_smul, sqCompletedFirstMomentMap_foxRow]
  funext b
  simp [sqQuadraticFoxLinearInitialCoefficient_eq]

/-- The exact remaining degree-zero/one theorem.  The forward kernel containments are proved
above; the reverse containments assert finite generation of the completed augmentation ideal
and completeness of the simultaneous first moments. -/
def SqCompletedMagnusDegreeZeroOneExact (h : ℕ) : Prop :=
  (∀ x : ModTwoCompletedGroupAlgebra (DSq h : Type),
      modTwoCompletedAugmentationCoordinate (DSq h : Type) (sqMagnusOneKernel h) x = 0 ↔
        x ∈ modTwoCompletedAugmentationIdeal (DSq h : Type)) ∧
  Function.Surjective (sqCompletedFirstMomentMap h) ∧
  (∀ (x : ModTwoCompletedGroupAlgebra (DSq h : Type)),
      x ∈ modTwoCompletedAugmentationIdeal (DSq h : Type) →
      (sqCompletedFirstMomentMap h x = 0 ↔
        x ∈ modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 2))

/-- Only the two reverse kernel containments remain in the degree-zero/one theorem: all forward
containments and both surjectivity statements are now unconditional. -/
theorem sqCompletedMagnusDegreeZeroOneExact_of_reverseKernels
    (h : ℕ)
    (hzero : ∀ x : ModTwoCompletedGroupAlgebra (DSq h : Type),
      modTwoCompletedAugmentationCoordinate (DSq h : Type) (sqMagnusOneKernel h) x = 0 →
        x ∈ modTwoCompletedAugmentationIdeal (DSq h : Type))
    (hone : ∀ x : ModTwoCompletedGroupAlgebra (DSq h : Type),
      x ∈ modTwoCompletedAugmentationIdeal (DSq h : Type) →
      sqCompletedFirstMomentMap h x = 0 →
        x ∈ modTwoCompletedAugmentationIdeal (DSq h : Type) ^ 2) :
    SqCompletedMagnusDegreeZeroOneExact h := by
  refine ⟨?_, sqCompletedFirstMomentMap_surjective h, ?_⟩
  · intro x
    exact ⟨hzero x, modTwoCompletedAugmentationCoordinate_eq_zero_of_mem
      (DSq h : Type) (sqMagnusOneKernel h)⟩
  · intro x hx
    exact ⟨hone x hx, sqCompletedFirstMomentMap_eq_zero_of_mem_augmentation_sq h⟩

/-! ## An honest all-layer completed Magnus interface -/

section GradedIdentification

universe uG uA

variable (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]
variable {J : Type}
variable (A : Type uA) [Ring A] [Algebra (ZMod 2) A]

private abbrev completedAugmentationPower (n : ℕ) :=
  modTwoCompletedAugmentationIdeal G ^ n

/-- Algebraic associated-graded comparison for a completed row.

`leading n` embeds the `n`th completed augmentation layer into a graded comparison algebra;
`leading_eq_zero_iff` says its kernel is exactly the next layer.  The last field is the
Fox--Magnus compatibility in every degree.  In particular, this is strictly lower-level than
`CompletedRowAugmentationInitialRegular`: it does not assert regularity of either row, and it
has no cohomological or completed-boundary field. -/
structure CompletedMagnusGradedIdentification
    (d : J → ModTwoCompletedGroupAlgebra G) (initialRow : J → A) where
  row_mem : ∀ i, d i ∈ modTwoCompletedAugmentationIdeal G
  leading : ∀ n : ℕ,
    (completedAugmentationPower G n).toAddSubgroup →ₗ[ZMod 2] A
  leading_eq_zero_iff : ∀ (n : ℕ)
      (a : (completedAugmentationPower G n).toAddSubgroup),
    leading n a = 0 ↔ (a.1 ∈ completedAugmentationPower G (n + 1))
  leading_one : leading 0 ⟨1, by
      change (1 : ModTwoCompletedGroupAlgebra G) ∈
        modTwoCompletedAugmentationIdeal G ^ 0
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      exact Set.mem_univ 1⟩ = 1
  leading_mul_row : ∀ (n : ℕ)
      (a : (completedAugmentationPower G n).toAddSubgroup) (i : J),
    leading (n + 1) ⟨a.1 * d i, by
        change a.1 * d i ∈
          modTwoCompletedAugmentationIdeal G ^ n * modTwoCompletedAugmentationIdeal G
        exact Ideal.mul_mem_mul a.2 (row_mem i)⟩ =
      leading n a * initialRow i

namespace CompletedMagnusGradedIdentification

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]
variable {J : Type}
variable {A : Type uA} [Ring A] [Algebra (ZMod 2) A]
variable {d : J → ModTwoCompletedGroupAlgebra G} {initialRow : J → A}

/-- Membership of the actual row in augmentation degree one is already part of a graded
identification. -/
theorem row_mem_filtration
    (M : CompletedMagnusGradedIdentification G A d initialRow) (i : J) :
    d i ∈ modTwoCompletedAugmentationFiltration G 1 := by
  change d i ∈ modTwoCompletedAugmentationIdeal G ^ 1
  simpa only [Submodule.pow_one] using M.row_mem i

/-- The degree-one leading form of the literal completed row is the specified formal row. -/
theorem leading_row
    (M : CompletedMagnusGradedIdentification G A d initialRow) (i : J) :
    M.leading 1 ⟨d i, by
        change d i ∈ modTwoCompletedAugmentationIdeal G ^ 1
        simpa only [Submodule.pow_one] using M.row_mem i⟩ = initialRow i := by
  have hmul := M.leading_mul_row 0
    ⟨(1 : ModTwoCompletedGroupAlgebra G), by
      change (1 : ModTwoCompletedGroupAlgebra G) ∈
        modTwoCompletedAugmentationIdeal G ^ 0
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      exact Set.mem_univ 1⟩ i
  simpa only [zero_add, one_mul, M.leading_one, one_mul] using hmul

/-- The all-layer comparison automatically gives the advertised filtration shift. -/
theorem rowRespectsFiltrationAtShift
    (M : CompletedMagnusGradedIdentification G A d initialRow) :
    RowRespectsFiltrationAtShift
      (modTwoCompletedAugmentationFiltration G) 1 d := by
  intro n a ha i
  change a * d i ∈ modTwoCompletedAugmentationIdeal G ^ (n + 1)
  change a ∈ modTwoCompletedAugmentationIdeal G ^ n at ha
  change a * d i ∈
    modTwoCompletedAugmentationIdeal G ^ n * modTwoCompletedAugmentationIdeal G
  exact Ideal.mul_mem_mul ha (M.row_mem i)

/-- Cancellation of the initial row in the comparison algebra transports to every completed
augmentation layer. -/
theorem rowLayerRegular
    (M : CompletedMagnusGradedIdentification G A d initialRow)
    (hfree : RowCommonLeftAnnihilatorFree initialRow) :
    RowLayerRegular (modTwoCompletedAugmentationFiltration G) 1 d := by
  intro n a ha hnext
  change a ∈ modTwoCompletedAugmentationIdeal G ^ (n + 1)
  change a ∈ modTwoCompletedAugmentationIdeal G ^ n at ha
  let an : (completedAugmentationPower G n).toAddSubgroup := ⟨a, ha⟩
  have hzero : M.leading n an = 0 := by
    apply hfree
    intro i
    rw [← M.leading_mul_row n an i]
    apply (M.leading_eq_zero_iff (n + 1)
      ⟨a * d i, by
        change a * d i ∈
          modTwoCompletedAugmentationIdeal G ^ n * modTwoCompletedAugmentationIdeal G
        exact Ideal.mul_mem_mul ha (M.row_mem i)⟩).2
    simpa [modTwoCompletedAugmentationFiltration, add_assoc] using hnext i
  exact (M.leading_eq_zero_iff n an).1 hzero

/-- **All-layer graded transport.**  An honest Magnus associated-graded identification and
graded row cancellation imply the exact completed initial-regularity target. -/
theorem completedRowAugmentationInitialRegular
    (M : CompletedMagnusGradedIdentification G A d initialRow)
    (hfree : RowCommonLeftAnnihilatorFree initialRow) :
    CompletedRowAugmentationInitialRegular G d := by
  exact ⟨M.rowRespectsFiltrationAtShift, M.rowLayerRegular hfree⟩

end CompletedMagnusGradedIdentification

end GradedIdentification

/-! ## The improved square specialization -/

/-- The exact remaining completed algebra statement for the improved square presentation.
It identifies every augmentation layer of `F₂[[DSq h]]` with its image in the actual quadratic
Magnus algebra, and identifies multiplication by the literal completed Fox row with the formal
quadratic Fox row. -/
abbrev SqCompletedMagnusGradedIdentification (h : ℕ) : Type :=
  CompletedMagnusGradedIdentification (DSq h : Type) (SqQuadraticAlgebra h)
    (sqCompletedModTwoFoxDerivativeRow h) (sqQuadraticQuotientFoxRow h)

/-! ## Exact homogeneous normal-coefficient theorem -/

/-- A normal quadratic word of homogeneous degree `n`. -/
abbrev SqQuadraticHomogeneousNormalWord (h n : ℕ) :=
  {w : SqQuadraticNormalWord h // w.1.length = n}

/-- Finitely supported coefficients on the degree-`n` normal words.  This is the PBW model of
the degree-`n` piece of the quadratic algebra. -/
abbrev SqQuadraticHomogeneousNormalSpace (h n : ℕ) :=
  SqQuadraticHomogeneousNormalWord h n →₀ ZMod 2

/-- Forget homogeneity and include degree-`n` normal coefficients in the full normal space. -/
def sqQuadraticHomogeneousInclude (h n : ℕ) :
    SqQuadraticHomogeneousNormalSpace h n →ₗ[ZMod 2]
      SqQuadraticNormalSpace h :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2)
    (fun w : SqQuadraticHomogeneousNormalWord h n => w.1)

theorem sqQuadraticHomogeneousInclude_injective (h n : ℕ) :
    Function.Injective (sqQuadraticHomogeneousInclude h n) := by
  apply Finsupp.mapDomain_injective
  intro w v hwv
  exact Subtype.ext hwv

/-- Evaluate homogeneous normal coefficients in the actual quadratic quotient. -/
def sqQuadraticHomogeneousEval (h n : ℕ) :
    SqQuadraticHomogeneousNormalSpace h n →ₗ[ZMod 2]
      SqQuadraticAlgebra h :=
  (sqQuadraticNormalEval h).comp (sqQuadraticHomogeneousInclude h n)

/-- PBW makes evaluation injective on every homogeneous normal layer. -/
theorem sqQuadraticHomogeneousEval_injective (h n : ℕ) :
    Function.Injective (sqQuadraticHomogeneousEval h n) :=
  (sqQuadraticNormalEval_injective h).comp
    (sqQuadraticHomogeneousInclude_injective h n)

/-- The unique empty homogeneous normal word. -/
def sqQuadraticHomogeneousEmpty (h : ℕ) :
    SqQuadraticHomogeneousNormalWord h 0 :=
  ⟨sqQuadraticNormalEmpty h, rfl⟩

@[simp] theorem sqQuadraticHomogeneousEval_empty (h : ℕ) :
    sqQuadraticHomogeneousEval h 0
        (Finsupp.single (sqQuadraticHomogeneousEmpty h) 1) = 1 := by
  simp [sqQuadraticHomogeneousEval, sqQuadraticHomogeneousInclude,
    sqQuadraticHomogeneousEmpty, sqQuadraticNormalEmpty,
    sqQuadraticNormalEval, quadraticWordEval]

/-- The exact tensor/normal-word coefficient theorem whose construction supplies the missing
completed associated graded.

For every `n`, `coefficient n` identifies `J^n/J^(n+1)` with the degree-`n` PBW normal-word
space: it is onto and its kernel is exactly the next augmentation power.  The final field is
the all-degree Fox--Magnus multiplication law for the actual completed row.  These fields are
purely algebraic; in particular they do not assert completed Fox injectivity or cohomology. -/
structure SqCompletedMagnusNormalCoefficientSystem (h : ℕ) where
  row_mem : ∀ i, sqCompletedModTwoFoxDerivativeRow h i ∈
    modTwoCompletedAugmentationIdeal (DSq h : Type)
  coefficient : ∀ n : ℕ,
    (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ n).toAddSubgroup →ₗ[ZMod 2]
      SqQuadraticHomogeneousNormalSpace h n
  coefficient_surjective : ∀ n, Function.Surjective (coefficient n)
  coefficient_eq_zero_iff : ∀ (n : ℕ)
      (a : (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ n).toAddSubgroup),
    coefficient n a = 0 ↔
      a.1 ∈ modTwoCompletedAugmentationIdeal (DSq h : Type) ^ (n + 1)
  coefficient_one : coefficient 0 ⟨1, by
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      exact Set.mem_univ 1⟩ =
    Finsupp.single (sqQuadraticHomogeneousEmpty h) 1
  coefficient_mul_row : ∀ (n : ℕ)
      (a : (modTwoCompletedAugmentationIdeal (DSq h : Type) ^ n).toAddSubgroup)
      (i : Fin (sqRank h)),
    sqQuadraticHomogeneousEval h (n + 1)
        (coefficient (n + 1) ⟨a.1 * sqCompletedModTwoFoxDerivativeRow h i, by
          change a.1 * sqCompletedModTwoFoxDerivativeRow h i ∈
            modTwoCompletedAugmentationIdeal (DSq h : Type) ^ n *
              modTwoCompletedAugmentationIdeal (DSq h : Type)
          exact Ideal.mul_mem_mul a.2 (row_mem i)⟩) =
      sqQuadraticHomogeneousEval h n (coefficient n a) *
        sqQuadraticQuotientFoxRow h i

namespace SqCompletedMagnusNormalCoefficientSystem

/-- The exact homogeneous coefficient theorem constructs the previously isolated completed
graded identification. -/
def toGradedIdentification {h : ℕ}
    (C : SqCompletedMagnusNormalCoefficientSystem h) :
    SqCompletedMagnusGradedIdentification h where
  row_mem := C.row_mem
  leading n := (sqQuadraticHomogeneousEval h n).comp (C.coefficient n)
  leading_eq_zero_iff n a := by
    constructor
    · intro hz
      apply (C.coefficient_eq_zero_iff n a).1
      apply sqQuadraticHomogeneousEval_injective h n
      simpa only [LinearMap.comp_apply, map_zero] using hz
    · intro ha
      change sqQuadraticHomogeneousEval h n (C.coefficient n a) = 0
      rw [(C.coefficient_eq_zero_iff n a).2 ha, map_zero]
  leading_one := by
    rw [LinearMap.comp_apply, C.coefficient_one,
      sqQuadraticHomogeneousEval_empty]
  leading_mul_row n a i := by
    exact C.coefficient_mul_row n a i

/-- Thus the exact normal-coefficient theorem is sufficient for the completed initial-form
regularity target, using the unconditional square PBW theorem. -/
theorem completedRowAugmentationInitialRegular {h : ℕ}
    (C : SqCompletedMagnusNormalCoefficientSystem h) :
    CompletedRowAugmentationInitialRegular (DSq h : Type)
      (sqCompletedModTwoFoxDerivativeRow h) :=
  C.toGradedIdentification.completedRowAugmentationInitialRegular
    (sqQuadraticQuotientFoxRow_commonLeftAnnihilatorFree' h)

end SqCompletedMagnusNormalCoefficientSystem

/-- **Capstone graded adapter.**  Once the completed Magnus graded identification is built,
the now-formalized quadratic PBW cancellation supplies the actual completed initial regularity
without any additional cohomological input. -/
theorem completedRowAugmentationInitialRegular_sq_of_gradedIdentification
    (h : ℕ) (M : SqCompletedMagnusGradedIdentification h)
    (pbw : SqQuadraticPBW h) :
    CompletedRowAugmentationInitialRegular (DSq h : Type)
      (sqCompletedModTwoFoxDerivativeRow h) :=
  M.completedRowAugmentationInitialRegular
    (sqQuadraticQuotientFoxRow_commonLeftAnnihilatorFree h pbw)

/-- Unconditional PBW form of the capstone adapter.  The only remaining hypothesis is the
completed associated-graded identification itself. -/
theorem completedRowAugmentationInitialRegular_sq
    (h : ℕ) (M : SqCompletedMagnusGradedIdentification h) :
    CompletedRowAugmentationInitialRegular (DSq h : Type)
      (sqCompletedModTwoFoxDerivativeRow h) :=
  M.completedRowAugmentationInitialRegular
    (sqQuadraticQuotientFoxRow_commonLeftAnnihilatorFree' h)

end

end GQ2.ContCoh

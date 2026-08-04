/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3CompletedFoxReduction

/-!
# Coordinatewise separation of the completed augmentation filtration

This file reduces separation of the algebraic augmentation powers in the explicit inverse-limit
model of `F₂[[G]]` to the classical finite-group-algebra statement that the augmentation ideal
of a finite `2`-group is nilpotent.

Mathlib's `Ideal` is a *left* ideal for a noncommutative ring.  Consequently the usual
commutative identity `Ideal.map f (I ^ n) = Ideal.map f I ^ n` is not available for group
algebras.  The first lemma below proves exactly the membership implication that is needed,
directly from the definition of ideal products.  In particular, no commutativity of `G` or of a
finite quotient is assumed.

The remaining finite theorem is isolated as `FiniteTwoGroupModTwoAugmentationNilpotence`.  It is
not a disguised completed-ring separation hypothesis: it quantifies only over ordinary finite
`2`-groups and their finite-dimensional group algebras.  Once that classical algebra result is
supplied, coordinate nilpotence and joint injectivity of the inverse limit prove separation for
every pro-`2` group, hence in particular for the improved square core `DSq h`.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2.Dyadic.Count GQ2.Dyadic.SqCore

universe u v

/-! ## Powers of left ideals under a ring homomorphism -/

/-- A ring homomorphism that carries a left ideal `I` into a left ideal `J` carries every
power `I ^ n` into `J ^ n`.

This is the noncommutative membership statement needed below.  Its proof uses only that the
image of a product is a product; it does not use a nonexistent noncommutative `Ideal.map_pow`
identity. -/
theorem idealPow_mapsTo_of_mapsTo
    {R : Type u} {S : Type v} [Semiring R] [Semiring S]
    (f : R →+* S) (I : Ideal R) (J : Ideal S)
    (hIJ : Set.MapsTo f I J) (n : ℕ) :
    Set.MapsTo f (I ^ n : Ideal R) (J ^ n : Ideal S) := by
  induction n with
  | zero =>
      intro x hx
      rw [Submodule.pow_zero] at hx ⊢
      rw [Ideal.one_eq_top]
      exact (show f x ∈ (⊤ : Ideal S) from Set.mem_univ (f x))
  | succ n ih =>
      intro x hx
      rw [Submodule.pow_succ] at hx ⊢
      apply (show I ^ n * I ≤ Ideal.comap f (J ^ n * J) from ?_) hx
      rw [Ideal.mul_le]
      intro a ha b hb
      change f (a * b) ∈ J ^ n * J
      rw [map_mul]
      exact Ideal.mul_mem_mul (ih ha) (hIJ hb)

/-! ## Finite-level augmentation ideals -/

/-- The coefficient-sum augmentation `F₂[Q] → F₂`. -/
def modTwoFiniteAugmentation (Q : Type u) [Group Q] :
    MonoidAlgebra (ZMod 2) Q →ₐ[ZMod 2] ZMod 2 :=
  MonoidAlgebra.lift (ZMod 2) (ZMod 2) Q (1 : Q →* ZMod 2)

@[simp]
theorem modTwoFiniteAugmentation_single (Q : Type u) [Group Q]
    (q : Q) (a : ZMod 2) :
    modTwoFiniteAugmentation Q (MonoidAlgebra.single q a) = a := by
  simp [modTwoFiniteAugmentation, MonoidAlgebra.lift_single]

/-- The ordinary mod-two augmentation ideal in `F₂[Q]`, defined canonically as the kernel of
the coefficient-sum augmentation.  Unlike a bare left-span presentation, this definition
automatically carries Mathlib's `Ideal.IsTwoSided` instance. -/
def modTwoFiniteAugmentationIdeal (Q : Type u) [Group Q] :
    Ideal (MonoidAlgebra (ZMod 2) Q) :=
  RingHom.ker (modTwoFiniteAugmentation Q).toRingHom

@[simp]
theorem modTwoFiniteAugmentationIdeal_single_sub_one
    (Q : Type u) [Group Q] (q : Q) :
    MonoidAlgebra.single q 1 - 1 ∈ modTwoFiniteAugmentationIdeal Q := by
  rw [modTwoFiniteAugmentationIdeal, RingHom.mem_ker]
  change modTwoFiniteAugmentation Q (MonoidAlgebra.single q 1 - 1) = 0
  rw [map_sub, modTwoFiniteAugmentation_single, map_one, sub_self]

/-- The augmentation ideal at the open-normal quotient `G/U`. -/
abbrev modTwoFiniteLevelAugmentationIdeal
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (U : OpenNormalSubgroup G) : Ideal (ModTwoGroupAlgebraLevel G U) :=
  modTwoFiniteAugmentationIdeal (G ⧸ U.toSubgroup)

/-- Every generator of the completed augmentation ideal maps into the ordinary augmentation
ideal at `U`; hence so does the whole completed left ideal. -/
theorem modTwoCompletedAugmentationIdeal_coordinate
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (U : OpenNormalSubgroup G) :
    Set.MapsTo (ModTwoCompletedGroupAlgebra.coordinate G U)
      (modTwoCompletedAugmentationIdeal G)
      (modTwoFiniteLevelAugmentationIdeal G U) := by
  intro x hx
  apply (show modTwoCompletedAugmentationIdeal G ≤
      Ideal.comap (ModTwoCompletedGroupAlgebra.coordinate G U).toRingHom
        (modTwoFiniteLevelAugmentationIdeal G U) from ?_) hx
  rw [modTwoCompletedAugmentationIdeal, Ideal.span_le]
  rintro _ ⟨g, rfl⟩
  change ModTwoCompletedGroupAlgebra.coordinate G U
      (ModTwoCompletedGroupAlgebra.of G g - 1) ∈
    modTwoFiniteLevelAugmentationIdeal G U
  rw [map_sub, ModTwoCompletedGroupAlgebra.coordinate_of, map_one]
  exact modTwoFiniteAugmentationIdeal_single_sub_one
    (G ⧸ U.toSubgroup) (QuotientGroup.mk' U.toSubgroup g)

/-- Coordinate maps carry the `n`th completed augmentation power into the `n`th ordinary
finite-level augmentation power. -/
theorem modTwoCompletedAugmentationIdealPow_coordinate
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (U : OpenNormalSubgroup G) (n : ℕ) :
    Set.MapsTo (ModTwoCompletedGroupAlgebra.coordinate G U)
      (modTwoCompletedAugmentationIdeal G ^ n : Ideal (ModTwoCompletedGroupAlgebra G))
      (modTwoFiniteLevelAugmentationIdeal G U ^ n :
        Ideal (ModTwoGroupAlgebraLevel G U)) :=
  idealPow_mapsTo_of_mapsTo
    (ModTwoCompletedGroupAlgebra.coordinate G U).toRingHom
    (modTwoCompletedAugmentationIdeal G)
    (modTwoFiniteLevelAugmentationIdeal G U)
    (modTwoCompletedAugmentationIdeal_coordinate G U) n

/-! ## The exact finite nilpotence input -/

/-- The classical finite group-algebra input: for every finite `2`-group `Q`, the augmentation
ideal of `F₂[Q]` is nilpotent.

This statement is deliberately finite and algebraic.  Mathlib currently has no theorem proving
it; the usual proof inducts through a central subgroup of order `2`, or identifies the
augmentation ideal with the Jacobson radical of the finite group algebra. -/
def FiniteTwoGroupModTwoAugmentationNilpotence : Prop :=
  ∀ (Q : Type u) [Group Q] [Finite Q], IsPGroup 2 Q →
    IsNilpotent (modTwoFiniteAugmentationIdeal Q)

/-- The concrete quotientwise finite condition attached to one profinite group `G`: every
ordinary augmentation ideal `ker(F₂[G/U] → F₂)` is nilpotent. -/
def ModTwoFiniteLevelAugmentationNilpotence
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] : Prop :=
  ∀ U : OpenNormalSubgroup G,
    IsNilpotent (modTwoFiniteLevelAugmentationIdeal G U)

/-- A pro-`2` group has quotientwise nilpotent finite augmentation ideals as soon as the
classical finite `2`-group algebra theorem is available. -/
theorem finiteLevelAugmentationNilpotence_of_isProTwo
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (hpro : IsProP 2 G)
    (hnil : FiniteTwoGroupModTwoAugmentationNilpotence.{u}) :
    ModTwoFiniteLevelAugmentationNilpotence G :=
  fun U => hnil (G ⧸ U.toSubgroup) (hpro U)

/-- **Coordinatewise augmentation separation.**  Nilpotence of the finite quotient
augmentation ideals implies separation of the algebraic augmentation powers in the explicit
inverse-limit group algebra. -/
theorem modTwoCompletedAugmentationSeparated_of_finiteLevelNilpotence
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (hnil : ModTwoFiniteLevelAugmentationNilpotence G) :
    ModTwoCompletedAugmentationSeparated (G := G) := by
  intro x hx
  apply ModTwoCompletedGroupAlgebra.ext G
  intro U
  obtain ⟨n, hn⟩ := hnil U
  have hcoord := modTwoCompletedAugmentationIdealPow_coordinate G U n (hx n)
  rw [hn] at hcoord
  exact Ideal.mem_bot.mp hcoord

/-- Universal finite `2`-group augmentation nilpotence therefore separates the completed
augmentation filtration of every pro-`2` group. -/
theorem modTwoCompletedAugmentationSeparated_of_finiteTwoGroupNilpotence
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (hpro : IsProP 2 G)
    (hnil : FiniteTwoGroupModTwoAugmentationNilpotence.{u}) :
    ModTwoCompletedAugmentationSeparated (G := G) :=
  modTwoCompletedAugmentationSeparated_of_finiteLevelNilpotence G
    (finiteLevelAugmentationNilpotence_of_isProTwo G hpro hnil)

/-- The improved square core has separated completed augmentation powers, conditional only on
the classical theorem for finite `2`-group algebras. -/
theorem modTwoCompletedAugmentationSeparated_DSq_of_finiteTwoGroupNilpotence
    (h : ℕ) (hnil : FiniteTwoGroupModTwoAugmentationNilpotence.{0}) :
    ModTwoCompletedAugmentationSeparated (G := DSq h) :=
  modTwoCompletedAugmentationSeparated_of_finiteTwoGroupNilpotence
    (DSq h : Type) (isProP_DSq h) hnil

/-! ## Connection to the completed-Fox capstone -/

/-- Finite `2`-group augmentation nilpotence discharges the separation field in the completed
Fox reduction.  The remaining hypotheses are exactly initial-form regularity of the improved
Fox row and the finite-to-completed bar--Fox assembly. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_finiteAugmentationNilpotence_barFox
    (h : ℕ)
    (hnil : FiniteTwoGroupModTwoAugmentationNilpotence.{0})
    (hregular : CompletedRowAugmentationInitialRegular (DSq h : Type)
      (sqCompletedModTwoFoxDerivativeRow h))
    (assembly : SqFiniteToCompletedBarFoxAssembly h) :
    FiniteElementaryH2RightExactSupply (DSq h : Type) :=
  finiteElementaryH2RightExactSupply_DSq_of_augmentation_barFox h
    (modTwoCompletedAugmentationSeparated_DSq_of_finiteTwoGroupNilpotence h hnil)
    hregular assembly

end

end GQ2.ContCoh

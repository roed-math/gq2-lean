/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3FiniteBarFoxChainHomotopy
import Mathlib.Algebra.Module.ZMod
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Data.Finsupp.Fintype
import Mathlib.LinearAlgebra.StdBasis

/-!
# Lifting the universal relation-kernel comparison to the completed one-relator module

The concrete reverse finite comparison lands in the free relation kernel at each quotient.  The
remaining one-relator step is not another bar calculation: it must replace those universal
relation coefficients by a compatible family of coefficients of the single improved relator,
without changing their Fox boundary.

This file formalizes that exact lift.  The universal relation kernels themselves form an inverse
system: under `U ≤ U'`, a word which dies at `G/U` also dies at `G/U'`.  A compatible universal
bar syzygy is required to be literally the output of `finiteBarToUniversalRelationTwo` at every
coordinate.  Its universal Fox images assemble into the completed generator module.

A `SqCompatibleUniversalBarRelationLiftAt` is precisely a compatible single-relator coefficient
with that completed Fox image.  Together with the still-separate `d³` factorization of the
universal image, it constructs `SqFiniteInputCompletedSyzygyBoundaryAt`.  Completed Fox
injectivity proves uniqueness of such a lift, but deliberately supplies no existence.  A final
finite lemma records what abstract normal-closure generation does prove: pointwise Fox-range
membership.  Additive and inverse-system-compatible choice remains a separate theorem.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.ContCoh GQ2.FoxH
open GQ2.Dyadic.SqCore
open CategoryTheory

private abbrev SqInputThree (h : ℕ)
    (V : OpenNormalSubgroup (DSq h : Type)) :=
  FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ V.toSubgroup)

private abbrev SqInputThreeBasisIndex (h : ℕ)
    (V : OpenNormalSubgroup (DSq h : Type)) :=
  ((DSq h : Type) ⧸ V.toSubgroup) ×
    ((DSq h : Type) ⧸ V.toSubgroup) ×
      ((DSq h : Type) ⧸ V.toSubgroup)

/-! ## The inverse system of universal relation kernels -/

/-- A relation word at a finer quotient remains a relation word at every coarser quotient. -/
def sqOpenQuotientFreeRelationKernelMap
    (h : ℕ) {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U') :
    FreeRelationKernel (sqOpenQuotientMarking h U) →
      FreeRelationKernel (sqOpenQuotientMarking h U') :=
  fun r ↦ ⟨r.1, by
    have hmark : sqOpenQuotientMarking h U' = fun i ↦
        modTwoQuotientTransition (DSq h : Type) hUU'
          (sqOpenQuotientMarking h U i) := by
      funext i
      rfl
    rw [hmark]
    change FreeGroup.lift (fun i ↦
      modTwoQuotientTransition (DSq h : Type) hUU'
        (sqOpenQuotientMarking h U i)) r.1 = 1
    calc
      _ = modTwoQuotientTransition (DSq h : Type) hUU'
          (FreeGroup.lift (sqOpenQuotientMarking h U) r.1) :=
        (map_freeGroup_lift
          (modTwoQuotientTransition (DSq h : Type) hUU')
          (sqOpenQuotientMarking h U) r.1).symm
      _ = 1 := by rw [r.2, map_one]⟩

@[simp] theorem sqOpenQuotientFreeRelationKernelMap_coe
    (h : ℕ) {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U')
    (r : FreeRelationKernel (sqOpenQuotientMarking h U)) :
    (sqOpenQuotientFreeRelationKernelMap h hUU' r).1 = r.1 :=
  rfl

/-- Push a universal relation chain from a finer quotient to a coarser one, including its
relation-kernel basis label. -/
def sqUniversalRelationModuleTransition
    (h : ℕ) {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U') :
    RegularModTwoRelationModule
        ((DSq h : Type) ⧸ U.toSubgroup)
        (FreeRelationKernel (sqOpenQuotientMarking h U)) →ₗ[ZMod 2]
      RegularModTwoRelationModule
        ((DSq h : Type) ⧸ U'.toSubgroup)
        (FreeRelationKernel (sqOpenQuotientMarking h U')) :=
  regularModTwoMap (modTwoQuotientTransition (DSq h : Type) hUU')
    (sqOpenQuotientFreeRelationKernelMap h hUU')

@[simp] theorem sqUniversalRelationModuleTransition_single
    (h : ℕ) {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U')
    (g : (DSq h : Type) ⧸ U.toSubgroup)
    (r : FreeRelationKernel (sqOpenQuotientMarking h U)) (a : ZMod 2) :
    sqUniversalRelationModuleTransition h hUU' (Finsupp.single (g, r) a) =
      Finsupp.single
        (modTwoQuotientTransition (DSq h : Type) hUU' g,
          sqOpenQuotientFreeRelationKernelMap h hUU' r) a :=
  regularModTwoMap_single _ _ _ _ _

/-- The universal Fox boundary is natural for the preceding relation-kernel transition. -/
theorem sqUniversalRelationFoxBoundary_natural
    (h : ℕ) {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U')
    (c : RegularModTwoRelationModule
      ((DSq h : Type) ⧸ U.toSubgroup)
      (FreeRelationKernel (sqOpenQuotientMarking h U))) :
    modTwoRegularModuleTransition (DSq h : Type) hUU' (Fin (sqRank h))
        ((finiteUniversalRelationFoxBoundary
          (sqOpenQuotientMarking h U)).map c) =
      (finiteUniversalRelationFoxBoundary
          (sqOpenQuotientMarking h U')).map
        (sqUniversalRelationModuleTransition h hUU' c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨g, r⟩
      have hsingle :
          modTwoRegularModuleTransition (DSq h : Type) hUU' (Fin (sqRank h))
              ((finiteUniversalRelationFoxBoundary
                (sqOpenQuotientMarking h U)).map
                (Finsupp.single (g, r) a)) =
            (finiteUniversalRelationFoxBoundary
                (sqOpenQuotientMarking h U')).map
              (sqUniversalRelationModuleTransition h hUU'
                (Finsupp.single (g, r) a)) := by
        simp only [finiteUniversalRelationFoxBoundary,
          finiteLevelModTwoFoxBoundary_single,
          sqUniversalRelationModuleTransition_single, map_smul]
        rw [modTwoRegularModuleTransition,
          regularModTwoPushforward_translate,
          regularModTwoPushforward_modTwoFoxDerivative]
        congr 2
      calc
        modTwoRegularModuleTransition (DSq h : Type) hUU' (Fin (sqRank h))
            ((finiteUniversalRelationFoxBoundary
              (sqOpenQuotientMarking h U)).map
              (Finsupp.single (g, r) a + c)) =
          modTwoRegularModuleTransition (DSq h : Type) hUU' (Fin (sqRank h))
              ((finiteUniversalRelationFoxBoundary
                (sqOpenQuotientMarking h U)).map (Finsupp.single (g, r) a)) +
            modTwoRegularModuleTransition (DSq h : Type) hUU' (Fin (sqRank h))
              ((finiteUniversalRelationFoxBoundary
                (sqOpenQuotientMarking h U)).map c) := by rw [map_add, map_add]
        _ = (finiteUniversalRelationFoxBoundary
                (sqOpenQuotientMarking h U')).map
              (sqUniversalRelationModuleTransition h hUU'
                (Finsupp.single (g, r) a)) +
            (finiteUniversalRelationFoxBoundary
                (sqOpenQuotientMarking h U')).map
              (sqUniversalRelationModuleTransition h hUU' c) := by
          rw [hsingle, ih]
        _ = (finiteUniversalRelationFoxBoundary
                (sqOpenQuotientMarking h U')).map
              (sqUniversalRelationModuleTransition h hUU'
                (Finsupp.single (g, r) a + c)) := by rw [map_add, map_add]

/-! ## Compatible universal bar outputs and their completed Fox image -/

/-- Universal relation syzygies for one finite input, coordinatewise realized by the concrete
reverse map on bar two-chains.  Compatibility is imposed only on those actual universal outputs,
not on arbitrary elements of the full relation modules. -/
structure SqCompatibleFiniteUniversalBarSyzygyAt
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type)) where
  /-- The bar two-chain whose concrete reverse image is retained at each quotient. -/
  barChain : ∀ U : OpenNormalSubgroup (DSq h : Type),
    SqInputThree h V →+
      FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup)
  /-- Those universal relation-kernel outputs form a compatible family. -/
  compatible : ∀ {U U' : OpenNormalSubgroup (DSq h : Type)}
    (hUU' : U ≤ U') (c : SqInputThree h V),
    sqUniversalRelationModuleTransition h hUU'
        (sqOpenQuotientBarToUniversalRelationTwo h U (barChain U c)) =
      sqOpenQuotientBarToUniversalRelationTwo h U' (barChain U' c)

/-- The actual universal relation-kernel output at one coordinate. -/
def SqCompatibleFiniteUniversalBarSyzygyAt.coordinate
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleFiniteUniversalBarSyzygyAt h V)
    (U : OpenNormalSubgroup (DSq h : Type)) :
    SqInputThree h V →+
      RegularModTwoRelationModule
        ((DSq h : Type) ⧸ U.toSubgroup)
        (FreeRelationKernel (sqOpenQuotientMarking h U)) :=
  (sqOpenQuotientBarToUniversalRelationTwo h U).toAddMonoidHom.comp
    (S.barChain U)

/-- Apply the universal Fox boundary coordinatewise and assemble the compatible images into the
completed generator module. -/
def SqCompatibleFiniteUniversalBarSyzygyAt.toCompletedFox
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleFiniteUniversalBarSyzygyAt h V) :
    SqInputThree h V →+
      ModTwoCompletedRegularModule (DSq h : Type) (Fin (sqRank h)) where
  toFun c := ⟨fun U ↦
      (finiteUniversalRelationFoxBoundary
        (sqOpenQuotientMarking h U)).map (S.coordinate U c), by
    intro U U' hUU'
    rw [sqUniversalRelationFoxBoundary_natural]
    exact congrArg
      (finiteUniversalRelationFoxBoundary (sqOpenQuotientMarking h U')).map
      (S.compatible hUU' c)⟩
  map_zero' := by
    apply ModTwoCompletedRegularModule.ext (DSq h : Type) (Fin (sqRank h))
    intro U
    simp [SqCompatibleFiniteUniversalBarSyzygyAt.coordinate]
  map_add' c d := by
    apply ModTwoCompletedRegularModule.ext (DSq h : Type) (Fin (sqRank h))
    intro U
    simp [SqCompatibleFiniteUniversalBarSyzygyAt.coordinate]

@[simp] theorem SqCompatibleFiniteUniversalBarSyzygyAt.coordinate_toCompletedFox
    {h : ℕ} {V U : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleFiniteUniversalBarSyzygyAt h V) (c : SqInputThree h V) :
    ModTwoCompletedRegularModule.coordinate (DSq h : Type)
        (Fin (sqRank h)) U (S.toCompletedFox c) =
      (finiteUniversalRelationFoxBoundary
        (sqOpenQuotientMarking h U)).map (S.coordinate U c) :=
  rfl

/-! ## The exact single-relator lift and its residual constructor -/

/-- A compatible lift of the concrete universal relation outputs to coefficients of the single
improved relator, preserving their completed Fox image. -/
structure SqCompatibleUniversalBarRelationLiftAt
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleFiniteUniversalBarSyzygyAt h V) where
  relationSyzygy : SqCompatibleFiniteRelationSyzygyAt h V
  fox_lift : ∀ c,
    (sqCompletedModTwoFoxBoundary h).map (relationSyzygy.toCompleted c) =
      S.toCompletedFox c

/-- Coordinatewise regression for a compatible lift: the literal improved-square Fox row sends
the chosen single-relator coefficient to the universal Fox image of the concrete reverse bar
output. -/
theorem SqCompatibleUniversalBarRelationLiftAt.fox_lift_coordinate
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    {S : SqCompatibleFiniteUniversalBarSyzygyAt h V}
    (L : SqCompatibleUniversalBarRelationLiftAt S)
    (U : OpenNormalSubgroup (DSq h : Type)) (c : SqInputThree h V) :
    (sqFiniteLevelModTwoFoxBoundary h (sqOpenQuotientMarking h U)).map
        (L.relationSyzygy.coordinate U c) =
      (finiteUniversalRelationFoxBoundary
        (sqOpenQuotientMarking h U)).map (S.coordinate U c) := by
  have hcoordinate := congrArg
    (fun z : ModTwoCompletedRegularModule (DSq h : Type) (Fin (sqRank h)) ↦
      ModTwoCompletedRegularModule.coordinate (DSq h : Type)
        (Fin (sqRank h)) U z)
    (L.fox_lift c)
  rw [sqCompletedModTwoFoxBoundary_coordinate,
    L.relationSyzygy.coordinate_toCompleted,
    S.coordinate_toCompletedFox] at hcoordinate
  exact hcoordinate

/-- Pure completed-module formulation of existence: the universal Fox-image map factors through
the completed improved-square Fox boundary by an additive map. -/
def SqUniversalBarFoxImageHasCompletedLift
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleFiniteUniversalBarSyzygyAt h V) : Prop :=
  ∃ R : SqInputThree h V →+
      ModTwoCompletedRegularModule (DSq h : Type) Unit,
    ∀ c, (sqCompletedModTwoFoxBoundary h).map (R c) = S.toCompletedFox c

/-- **Exact existence criterion.** A compatible finite-coordinate lift is the same as an
additive factorization through the completed Fox boundary. -/
theorem nonempty_sqCompatibleUniversalBarRelationLiftAt_iff
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleFiniteUniversalBarSyzygyAt h V) :
    Nonempty (SqCompatibleUniversalBarRelationLiftAt S) ↔
      SqUniversalBarFoxImageHasCompletedLift S := by
  constructor
  · rintro ⟨L⟩
    exact ⟨L.relationSyzygy.toCompleted, L.fox_lift⟩
  · rintro ⟨R, hR⟩
    refine ⟨{
      relationSyzygy := sqCompatibleFiniteRelationSyzygyAtOfCompleted R
      fox_lift := fun c ↦ ?_
    }⟩
    simpa using hR c

/-! ## Finite inverse-limit compactness for affine Fox fibers -/

/-- The affine fiber of the finite improved-square Fox boundary over the `U`-coordinate of a
completed generator coefficient. -/
def SqCompletedFoxFiber (h : ℕ)
    (y : ModTwoCompletedRegularModule (DSq h : Type) (Fin (sqRank h)))
    (U : OpenNormalSubgroup (DSq h : Type)) :=
  {d : RegularModTwoRelationModule ((DSq h : Type) ⧸ U.toSubgroup) Unit //
    (sqFiniteLevelModTwoFoxBoundary h (sqOpenQuotientMarking h U)).map d =
      ModTwoCompletedRegularModule.coordinate (DSq h : Type)
        (Fin (sqRank h)) U y}

/-- Push an affine Fox-fiber point to a coarser quotient. -/
def sqCompletedFoxFiberTransition
    (h : ℕ)
    (y : ModTwoCompletedRegularModule (DSq h : Type) (Fin (sqRank h)))
    {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U') :
    SqCompletedFoxFiber h y U → SqCompletedFoxFiber h y U' :=
  fun d ↦ ⟨modTwoRegularModuleTransition (DSq h : Type) hUU' Unit d.1, by
    have hproj : modTwoQuotientTransition (DSq h : Type) hUU' =
        openNormalQuotientProj hUU' := by rfl
    calc
      (sqFiniteLevelModTwoFoxBoundary h (sqOpenQuotientMarking h U')).map
          (modTwoRegularModuleTransition (DSq h : Type) hUU' Unit d.1) =
        modTwoRegularModuleTransition (DSq h : Type) hUU' (Fin (sqRank h))
          ((sqFiniteLevelModTwoFoxBoundary h
            (sqOpenQuotientMarking h U)).map d.1) := by
              symm
              simpa [modTwoRegularModuleTransition, hproj] using
                sqOpenQuotientFoxBoundary_natural h hUU' d.1
      _ = modTwoRegularModuleTransition (DSq h : Type) hUU' (Fin (sqRank h))
          (ModTwoCompletedRegularModule.coordinate (DSq h : Type)
            (Fin (sqRank h)) U y) := congrArg _ d.2
      _ = ModTwoCompletedRegularModule.coordinate (DSq h : Type)
          (Fin (sqRank h)) U' y :=
        ModTwoCompletedRegularModule.coordinate_compatible
          (DSq h : Type) (Fin (sqRank h)) y hUU'⟩

/-- The affine fibers and their quotient pushforwards form a cofiltered functor of finite
types. -/
def sqCompletedFoxFiberFunctor
    (h : ℕ)
    (y : ModTwoCompletedRegularModule (DSq h : Type) (Fin (sqRank h))) :
    OpenNormalSubgroup (DSq h : Type) ⥤ Type where
  obj U := SqCompletedFoxFiber h y U
  map f := ↾(sqCompletedFoxFiberTransition h y (leOfHom f))
  map_id U := by
    ext d
    apply Subtype.ext
    change modTwoRegularModuleTransition (DSq h : Type) (le_refl U) Unit d.1 = d.1
    rw [modTwoRegularModuleTransition]
    have htransition :
        modTwoQuotientTransition (DSq h : Type) (le_refl U) =
          MonoidHom.id ((DSq h : Type) ⧸ U.toSubgroup) := by
      ext g
      rfl
    rw [htransition, regularModTwoPushforward_id]
  map_comp f g := by
    ext d
    apply Subtype.ext
    exact (modTwoRegularModuleTransition_comp (DSq h : Type)
      (leOfHom f) (leOfHom g) Unit d.1).symm

/-- Cofinal finite-level range condition for one completed generator coefficient.  Detection is
allowed only after passage to a finer quotient `W ≤ U`. -/
def SqCompletedFoxCofinalRange
    (h : ℕ)
    (y : ModTwoCompletedRegularModule (DSq h : Type) (Fin (sqRank h))) : Prop :=
  ∀ U : OpenNormalSubgroup (DSq h : Type),
    ∃ W : OpenNormalSubgroup (DSq h : Type), W ≤ U ∧
      ModTwoCompletedRegularModule.coordinate (DSq h : Type)
          (Fin (sqRank h)) W y ∈
        (sqFiniteLevelModTwoFoxBoundary h
          (sqOpenQuotientMarking h W)).map.range

/-- The weaker finite-refinement condition actually needed by compactness.  A coefficient may
be constructed at a finer quotient `W`; only its pushforward Fox image is required to equal the
prescribed coordinate at `U`.  This is the natural target of an eventual normal-closure
approximation argument. -/
def SqCompletedFoxEventualRange
    (h : ℕ)
    (y : ModTwoCompletedRegularModule (DSq h : Type) (Fin (sqRank h))) : Prop :=
  ∀ U : OpenNormalSubgroup (DSq h : Type),
    ∃ W : OpenNormalSubgroup (DSq h : Type), ∃ hWU : W ≤ U,
      ∃ d : RegularModTwoRelationModule
          ((DSq h : Type) ⧸ W.toSubgroup) Unit,
        modTwoRegularModuleTransition (DSq h : Type) hWU (Fin (sqRank h))
            ((sqFiniteLevelModTwoFoxBoundary h
              (sqOpenQuotientMarking h W)).map d) =
          ModTwoCompletedRegularModule.coordinate (DSq h : Type)
            (Fin (sqRank h)) U y

/-- A cofinal range witness makes every affine fiber nonempty by pushing a finer preimage down
to the prescribed quotient. -/
theorem sqCompletedFoxFiber_nonempty_of_cofinalRange
    (h : ℕ)
    (y : ModTwoCompletedRegularModule (DSq h : Type) (Fin (sqRank h)))
    (hy : SqCompletedFoxCofinalRange h y)
    (U : OpenNormalSubgroup (DSq h : Type)) :
    Nonempty (SqCompletedFoxFiber h y U) := by
  obtain ⟨W, hWU, d, hd⟩ := hy U
  refine ⟨sqCompletedFoxFiberTransition h y hWU ⟨d, ?_⟩⟩
  exact hd

/-- An eventual finer-level preimage pushes down to an element of the prescribed affine fiber. -/
theorem sqCompletedFoxFiber_nonempty_of_eventualRange
    (h : ℕ)
    (y : ModTwoCompletedRegularModule (DSq h : Type) (Fin (sqRank h)))
    (hy : SqCompletedFoxEventualRange h y)
    (U : OpenNormalSubgroup (DSq h : Type)) :
    Nonempty (SqCompletedFoxFiber h y U) := by
  obtain ⟨W, hWU, d, hd⟩ := hy U
  refine ⟨⟨modTwoRegularModuleTransition (DSq h : Type) hWU Unit d, ?_⟩⟩
  have hproj : modTwoQuotientTransition (DSq h : Type) hWU =
      openNormalQuotientProj hWU := by rfl
  calc
    (sqFiniteLevelModTwoFoxBoundary h (sqOpenQuotientMarking h U)).map
        (modTwoRegularModuleTransition (DSq h : Type) hWU Unit d) =
      modTwoRegularModuleTransition (DSq h : Type) hWU (Fin (sqRank h))
        ((sqFiniteLevelModTwoFoxBoundary h
          (sqOpenQuotientMarking h W)).map d) := by
            symm
            simpa [modTwoRegularModuleTransition, hproj] using
              sqOpenQuotientFoxBoundary_natural h hWU d
    _ = ModTwoCompletedRegularModule.coordinate (DSq h : Type)
        (Fin (sqRank h)) U y := hd

/-- **Finite inverse-limit compactness.** Nonemptiness of every finite affine fiber produces a
compatible completed preimage under the improved-square Fox boundary.  No transition map between
individual fibers is assumed surjective.  This is the reusable compactness core. -/
theorem exists_sqCompletedFox_preimage_of_nonempty_fibers
    (h : ℕ)
    (y : ModTwoCompletedRegularModule (DSq h : Type) (Fin (sqRank h)))
    (hy : ∀ U : OpenNormalSubgroup (DSq h : Type),
      Nonempty (SqCompletedFoxFiber h y U)) :
    ∃ x : ModTwoCompletedRegularModule (DSq h : Type) Unit,
      (sqCompletedModTwoFoxBoundary h).map x = y := by
  classical
  let F := sqCompletedFoxFiberFunctor h y
  letI (U : OpenNormalSubgroup (DSq h : Type)) : Nonempty (F.obj U) :=
    hy U
  letI (U : OpenNormalSubgroup (DSq h : Type)) : Finite (F.obj U) := by
    dsimp [F, sqCompletedFoxFiberFunctor, SqCompletedFoxFiber]
    letI : Finite ((DSq h : Type) ⧸ U.toSubgroup) :=
      Subgroup.quotient_finite_of_isOpen U.toSubgroup U.isOpen'
    letI : Fintype ((DSq h : Type) ⧸ U.toSubgroup) := Fintype.ofFinite _
    letI : Fintype
        (RegularModTwoRelationModule ((DSq h : Type) ⧸ U.toSubgroup) Unit) :=
      Finsupp.fintype
    exact Finite.of_injective Subtype.val Subtype.val_injective
  obtain ⟨sec, hsec⟩ := nonempty_sections_of_finite_cofiltered_system F
  let x : ModTwoCompletedRegularModule (DSq h : Type) Unit :=
    ⟨fun U ↦ (sec U).1, by
      intro U U' hUU'
      have hs := hsec (homOfLE hUU')
      exact congrArg Subtype.val hs⟩
  refine ⟨x, ?_⟩
  apply ModTwoCompletedRegularModule.ext (DSq h : Type) (Fin (sqRank h))
  intro U
  rw [sqCompletedModTwoFoxBoundary_coordinate]
  exact (sec U).2

/-- The stronger exact cofinal-range condition implies a completed Fox preimage. -/
theorem exists_sqCompletedFox_preimage_of_cofinalRange
    (h : ℕ)
    (y : ModTwoCompletedRegularModule (DSq h : Type) (Fin (sqRank h)))
    (hy : SqCompletedFoxCofinalRange h y) :
    ∃ x : ModTwoCompletedRegularModule (DSq h : Type) Unit,
      (sqCompletedModTwoFoxBoundary h).map x = y :=
  exists_sqCompletedFox_preimage_of_nonempty_fibers h y
    (sqCompletedFoxFiber_nonempty_of_cofinalRange h y hy)

/-- The weaker eventual-refinement range condition also implies a completed Fox preimage. -/
theorem exists_sqCompletedFox_preimage_of_eventualRange
    (h : ℕ)
    (y : ModTwoCompletedRegularModule (DSq h : Type) (Fin (sqRank h)))
    (hy : SqCompletedFoxEventualRange h y) :
    ∃ x : ModTwoCompletedRegularModule (DSq h : Type) Unit,
      (sqCompletedModTwoFoxBoundary h).map x = y :=
  exists_sqCompletedFox_preimage_of_nonempty_fibers h y
    (sqCompletedFoxFiber_nonempty_of_eventualRange h y hy)

/-- Cofinal range for every output of one compatible universal bar syzygy. -/
def SqUniversalBarFoxCofinalRange
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleFiniteUniversalBarSyzygyAt h V) : Prop :=
  ∀ c, SqCompletedFoxCofinalRange h (S.toCompletedFox c)

/-- Eventual-refinement range for every output of one compatible universal bar syzygy. -/
def SqUniversalBarFoxEventualRange
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleFiniteUniversalBarSyzygyAt h V) : Prop :=
  ∀ c, SqCompletedFoxEventualRange h (S.toCompletedFox c)

/-- Basiswise completed Fox preimages suffice to build an additive lift.  This avoids using
completed Fox injectivity: the finite input is the function space on a finite quotient cube, and
the standard `F₂`-basis extends arbitrary chosen basis preimages uniquely to a linear map. -/
noncomputable def sqCompatibleUniversalBarRelationLiftAtOfBasisPreimages
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleFiniteUniversalBarSyzygyAt h V)
    (hpreimage : ∀ i : SqInputThreeBasisIndex h V,
      ∃ x : ModTwoCompletedRegularModule (DSq h : Type) Unit,
        (sqCompletedModTwoFoxBoundary h).map x =
          S.toCompletedFox (Pi.basisFun (ZMod 2) (SqInputThreeBasisIndex h V) i)) :
    SqCompatibleUniversalBarRelationLiftAt S := by
  classical
  letI : Finite ((DSq h : Type) ⧸ V.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen V.toSubgroup V.isOpen'
  choose lift hlift using hpreimage
  let Rlin : SqInputThree h V →ₗ[ZMod 2]
      ModTwoCompletedRegularModule (DSq h : Type) Unit :=
    (Pi.basisFun (ZMod 2) (SqInputThreeBasisIndex h V)).constr (ZMod 2) lift
  let R : SqInputThree h V →+
      ModTwoCompletedRegularModule (DSq h : Type) Unit := Rlin.toAddMonoidHom
  have hlinear : (sqCompletedModTwoFoxBoundary h).map.comp Rlin =
      S.toCompletedFox.toZModLinearMap 2 := by
    apply (Pi.basisFun (ZMod 2) (SqInputThreeBasisIndex h V)).ext
    intro i
    change (sqCompletedModTwoFoxBoundary h).map
        (Rlin (Pi.basisFun (ZMod 2) (SqInputThreeBasisIndex h V) i)) =
      S.toCompletedFox (Pi.basisFun (ZMod 2) (SqInputThreeBasisIndex h V) i)
    rw [show Rlin (Pi.basisFun (ZMod 2) (SqInputThreeBasisIndex h V) i) =
        lift i from
      (Pi.basisFun (ZMod 2) (SqInputThreeBasisIndex h V)).constr_basis
        (ZMod 2) lift i]
    exact hlift i
  refine {
    relationSyzygy := sqCompatibleFiniteRelationSyzygyAtOfCompleted R
    fox_lift := fun c ↦ ?_
  }
  rw [toCompleted_sqCompatibleFiniteRelationSyzygyAtOfCompleted]
  exact LinearMap.congr_fun hlinear c

/-- **Compactness construction of the compatible lift.** Cofinal finite-level range gives
completed preimages of the standard basis.  Extending those choices linearly constructs the
additive compatible lift, without any injectivity hypothesis on completed Fox. -/
noncomputable def sqCompatibleUniversalBarRelationLiftAtOfCofinalRange
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleFiniteUniversalBarSyzygyAt h V)
    (hrange : SqUniversalBarFoxCofinalRange S) :
    SqCompatibleUniversalBarRelationLiftAt S :=
  sqCompatibleUniversalBarRelationLiftAtOfBasisPreimages S fun i ↦
    exists_sqCompletedFox_preimage_of_cofinalRange h
      (S.toCompletedFox (Pi.basisFun (ZMod 2) (SqInputThreeBasisIndex h V) i))
      (hrange _)

/-- The weaker eventual-refinement condition likewise constructs the compatible lift.  This is
the endpoint expected from profinite normal-closure approximation. -/
noncomputable def sqCompatibleUniversalBarRelationLiftAtOfEventualRange
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleFiniteUniversalBarSyzygyAt h V)
    (hrange : SqUniversalBarFoxEventualRange S) :
    SqCompatibleUniversalBarRelationLiftAt S :=
  sqCompatibleUniversalBarRelationLiftAtOfBasisPreimages S fun i ↦
    exists_sqCompletedFox_preimage_of_eventualRange h
      (S.toCompletedFox (Pi.basisFun (ZMod 2) (SqInputThreeBasisIndex h V) i))
      (hrange _)

/-- The universal Fox image factors through `d³`, before making any single-relator lift.  This is
the chain-map identity that the next-degree universal bar comparison must supply. -/
structure SqFiniteInputUniversalSyzygyBoundaryAt
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type)) where
  universalSyzygy : SqCompatibleFiniteUniversalBarSyzygyAt h V
  boundaryDefect :
    FiniteModTwoBarCochainFour ((DSq h : Type) ⧸ V.toSubgroup) →+
      ModTwoCompletedRegularModule (DSq h : Type) (Fin (sqRank h))
  boundary_universalSyzygy : ∀ c,
    universalSyzygy.toCompletedFox c =
      boundaryDefect (finiteModTwoBarDThree _ c)

/-- A compatible lift of the universal relation-kernel output constructs exactly the residual
completed single-relator syzygy/boundary datum. -/
def SqFiniteInputCompletedSyzygyBoundaryAt.ofUniversalLift
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (U : SqFiniteInputUniversalSyzygyBoundaryAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt U.universalSyzygy) :
    SqFiniteInputCompletedSyzygyBoundaryAt h V where
  relationSyzygy := L.relationSyzygy
  boundaryDefect := U.boundaryDefect
  boundary_relationSyzygy c :=
    (L.fox_lift c).trans (U.boundary_universalSyzygy c)

/-- Eventual finite-refinement Fox range closes the single-relator lifting part of the residual
boundary constructor.  The independent universal `d³` factorization remains packaged in `U`. -/
noncomputable def SqFiniteInputCompletedSyzygyBoundaryAt.ofUniversalEventualRange
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (U : SqFiniteInputUniversalSyzygyBoundaryAt h V)
    (hrange : SqUniversalBarFoxEventualRange U.universalSyzygy) :
    SqFiniteInputCompletedSyzygyBoundaryAt h V :=
  .ofUniversalLift U
    (sqCompatibleUniversalBarRelationLiftAtOfEventualRange U.universalSyzygy hrange)

/-! ## Injectivity gives uniqueness, not existence -/

/-- If the completed improved-square Fox boundary is injective, two compatible lifts of the
same universal outputs induce the same completed relation-syzygy map. -/
theorem SqCompatibleUniversalBarRelationLiftAt.toCompleted_unique
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    {S : SqCompatibleFiniteUniversalBarSyzygyAt h V}
    (hinjective : Function.Injective (sqCompletedModTwoFoxBoundary h).map)
    (L L' : SqCompatibleUniversalBarRelationLiftAt S) :
    L.relationSyzygy.toCompleted = L'.relationSyzygy.toCompleted := by
  apply AddMonoidHom.ext
  intro c
  apply hinjective
  rw [L.fox_lift c, L'.fox_lift c]

/-- Equivalently, completed Fox injectivity makes the compatible finite-coordinate lift itself
unique. -/
theorem SqCompatibleUniversalBarRelationLiftAt.relationSyzygy_unique
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    {S : SqCompatibleFiniteUniversalBarSyzygyAt h V}
    (hinjective : Function.Injective (sqCompletedModTwoFoxBoundary h).map)
    (L L' : SqCompatibleUniversalBarRelationLiftAt S) :
    L.relationSyzygy = L'.relationSyzygy := by
  apply (sqCompatibleFiniteRelationSyzygyAtEquiv h V).injective
  exact L.toCompleted_unique hinjective L'

/-! ## What abstract normal-closure generation supplies -/

/-- If every word in a finite universal relation kernel lies in the abstract normal closure of
the improved relator, the universal Fox image of every relation chain lies in the finite
single-relator Fox range.  This is pointwise existence only; it does not choose additive lifts or
prove compatibility over quotient transitions. -/
theorem sqUniversalRelationFoxBoundary_mem_sqFoxRange_of_normalClosure
    (h : ℕ) (U : OpenNormalSubgroup (DSq h : Type))
    (hnormal : ∀ r : FreeRelationKernel (sqOpenQuotientMarking h U),
      r.1 ∈ Subgroup.normalClosure (Set.range (fun _ : Unit ↦ sqDiscreteRelator h)))
    (c : RegularModTwoRelationModule
      ((DSq h : Type) ⧸ U.toSubgroup)
      (FreeRelationKernel (sqOpenQuotientMarking h U))) :
    (finiteUniversalRelationFoxBoundary (sqOpenQuotientMarking h U)).map c ∈
      (modTwoFoxRelationMatrixLinear (sqOpenQuotientMarking h U)
        (fun _ : Unit ↦ sqDiscreteRelator h)).range := by
  classical
  induction c using Finsupp.induction with
  | zero => exact Submodule.zero_mem _
  | single_add p a c hp ha ih =>
      rcases p with ⟨g, r⟩
      rw [map_add]
      apply Submodule.add_mem _
      · simp only [finiteUniversalRelationFoxBoundary,
          finiteLevelModTwoFoxBoundary_single]
        apply Submodule.smul_mem
        exact modTwoFoxRelationMatrixLinear_range_translate
          (sqOpenQuotientMarking h U)
          (fun _ : Unit ↦ sqDiscreteRelator h) g
          (modTwoFoxDerivative_mem_range_of_mem_normalClosure
            (sqOpenQuotientMarking h U)
            (fun _ : Unit ↦ sqDiscreteRelator h)
            (fun _ ↦ sqOpenQuotientMarking_sqDiscreteRelator h U)
            (hnormal r))
      · exact ih

/-- Normal-closure generation therefore gives a single-relator coefficient for each individual
finite universal relation chain.  No compatibility or additivity of these choices is asserted. -/
theorem exists_sqRelationCoefficient_for_universal_of_normalClosure
    (h : ℕ) (U : OpenNormalSubgroup (DSq h : Type))
    (hnormal : ∀ r : FreeRelationKernel (sqOpenQuotientMarking h U),
      r.1 ∈ Subgroup.normalClosure (Set.range (fun _ : Unit ↦ sqDiscreteRelator h)))
    (c : RegularModTwoRelationModule
      ((DSq h : Type) ⧸ U.toSubgroup)
      (FreeRelationKernel (sqOpenQuotientMarking h U))) :
    ∃ d : RegularModTwoRelationModule
        ((DSq h : Type) ⧸ U.toSubgroup) Unit,
      (sqFiniteLevelModTwoFoxBoundary h (sqOpenQuotientMarking h U)).map d =
        (finiteUniversalRelationFoxBoundary (sqOpenQuotientMarking h U)).map c := by
  obtain ⟨d, hd⟩ :=
    sqUniversalRelationFoxBoundary_mem_sqFoxRange_of_normalClosure
      h U hnormal c
  refine ⟨d, ?_⟩
  simpa [modTwoFoxRelationMatrixLinear_apply,
    sqFiniteLevelModTwoFoxBoundary] using hd

/-- In particular, the preceding pointwise lift applies to the concrete universal relation
output of every bar two-chain. -/
theorem exists_sqRelationCoefficient_for_barToUniversal_of_normalClosure
    (h : ℕ) (U : OpenNormalSubgroup (DSq h : Type))
    (hnormal : ∀ r : FreeRelationKernel (sqOpenQuotientMarking h U),
      r.1 ∈ Subgroup.normalClosure (Set.range (fun _ : Unit ↦ sqDiscreteRelator h)))
    (b : FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup)) :
    ∃ d : RegularModTwoRelationModule
        ((DSq h : Type) ⧸ U.toSubgroup) Unit,
      (sqFiniteLevelModTwoFoxBoundary h (sqOpenQuotientMarking h U)).map d =
        (finiteUniversalRelationFoxBoundary (sqOpenQuotientMarking h U)).map
          (sqOpenQuotientBarToUniversalRelationTwo h U b) :=
  exists_sqRelationCoefficient_for_universal_of_normalClosure h U hnormal _

/-! ## Eventual relation efficiency -/

/-- The weakest uniform word-level input used below.  For every target quotient `U`, after
passing to a sufficiently fine `W ≤ U`, every relation word at level `W` has its `U`-level
mod-two Fox derivative in the single-relator row.  Membership in `modTwoFoxRangeKernel` also
records the automatic fact that the word dies at `U`. -/
def SqEventualRelationFoxGeneration (h : ℕ) : Prop :=
  ∀ U : OpenNormalSubgroup (DSq h : Type),
    ∃ W : OpenNormalSubgroup (DSq h : Type), ∃ _hWU : W ≤ U,
      ∀ r : FreeRelationKernel (sqOpenQuotientMarking h W),
        r.1 ∈ modTwoFoxRangeKernel (sqOpenQuotientMarking h U)
          (fun _ : Unit ↦ sqDiscreteRelator h)

/-- A more recognizably presentation-theoretic sufficient input.  At a fine enough quotient,
each relation word has the same target-level Fox derivative as an abstract product of conjugates
of the improved relator.  Proving this from the pro-2 presentation is the remaining relation-
efficiency theorem; it is strictly stronger than the exact Fox-generation condition above. -/
def SqEventualNormalClosureApproximation (h : ℕ) : Prop :=
  ∀ U : OpenNormalSubgroup (DSq h : Type),
    ∃ W : OpenNormalSubgroup (DSq h : Type), ∃ _hWU : W ≤ U,
      ∀ r : FreeRelationKernel (sqOpenQuotientMarking h W),
        ∃ n : FreeGroup (Fin (sqRank h)),
          n ∈ Subgroup.normalClosure
              (Set.range (fun _ : Unit ↦ sqDiscreteRelator h)) ∧
            modTwoFoxDerivative (sqOpenQuotientMarking h U) r.1 =
              modTwoFoxDerivative (sqOpenQuotientMarking h U) n

/-- Eventual normal-closure approximation implies the exact eventual Fox-generation input. -/
theorem sqEventualRelationFoxGeneration_of_normalClosureApproximation
    (h : ℕ) (hnormal : SqEventualNormalClosureApproximation h) :
    SqEventualRelationFoxGeneration h := by
  intro U
  obtain ⟨W, hWU, hW⟩ := hnormal U
  refine ⟨W, hWU, fun r ↦ ?_⟩
  constructor
  · exact (sqOpenQuotientFreeRelationKernelMap h hWU r).2
  · obtain ⟨n, hn, hderiv⟩ := hW r
    rw [hderiv]
    exact modTwoFoxDerivative_mem_range_of_mem_normalClosure
      (sqOpenQuotientMarking h U)
      (fun _ : Unit ↦ sqDiscreteRelator h)
      (fun _ ↦ sqOpenQuotientMarking_sqDiscreteRelator h U) hn

/-- Uniform eventual Fox generation sends every universal relation chain at the fine level into
the single-relator Fox range after pushforward to the target quotient. -/
theorem sqUniversalRelationFoxBoundary_push_mem_sqFoxRange_of_eventualGeneration
    (h : ℕ) {W U : OpenNormalSubgroup (DSq h : Type)} (hWU : W ≤ U)
    (hgen : ∀ r : FreeRelationKernel (sqOpenQuotientMarking h W),
      r.1 ∈ modTwoFoxRangeKernel (sqOpenQuotientMarking h U)
        (fun _ : Unit ↦ sqDiscreteRelator h))
    (c : RegularModTwoRelationModule
      ((DSq h : Type) ⧸ W.toSubgroup)
      (FreeRelationKernel (sqOpenQuotientMarking h W))) :
    modTwoRegularModuleTransition (DSq h : Type) hWU (Fin (sqRank h))
        ((finiteUniversalRelationFoxBoundary
          (sqOpenQuotientMarking h W)).map c) ∈
      (modTwoFoxRelationMatrixLinear (sqOpenQuotientMarking h U)
        (fun _ : Unit ↦ sqDiscreteRelator h)).range := by
  classical
  rw [sqUniversalRelationFoxBoundary_natural]
  induction c using Finsupp.induction with
  | zero => exact Submodule.zero_mem _
  | single_add p a c hp ha ih =>
      rcases p with ⟨g, r⟩
      rw [map_add, map_add]
      apply Submodule.add_mem _
      · simp only [sqUniversalRelationModuleTransition_single,
          finiteUniversalRelationFoxBoundary,
          finiteLevelModTwoFoxBoundary_single]
        apply Submodule.smul_mem
        exact modTwoFoxRelationMatrixLinear_range_translate
          (sqOpenQuotientMarking h U)
          (fun _ : Unit ↦ sqDiscreteRelator h)
          (modTwoQuotientTransition (DSq h : Type) hWU g) (hgen r).2
      · exact ih

/-- Eventual relation efficiency supplies the stronger exact cofinal-range premise for every
compatible universal bar syzygy. -/
theorem sqUniversalBarFoxCofinalRange_of_eventualRelationGeneration
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleFiniteUniversalBarSyzygyAt h V)
    (hgen : SqEventualRelationFoxGeneration h) :
    SqUniversalBarFoxCofinalRange S := by
  intro c U
  obtain ⟨W, hWU, hW⟩ := hgen U
  have hmem :=
    sqUniversalRelationFoxBoundary_push_mem_sqFoxRange_of_eventualGeneration
      h hWU hW (S.coordinate W c)
  have hcoordinate :
      modTwoRegularModuleTransition (DSq h : Type) hWU (Fin (sqRank h))
          ((finiteUniversalRelationFoxBoundary
            (sqOpenQuotientMarking h W)).map (S.coordinate W c)) =
        ModTwoCompletedRegularModule.coordinate (DSq h : Type)
          (Fin (sqRank h)) U (S.toCompletedFox c) := by
    calc
      _ = (finiteUniversalRelationFoxBoundary
            (sqOpenQuotientMarking h U)).map
          (sqUniversalRelationModuleTransition h hWU (S.coordinate W c)) :=
        sqUniversalRelationFoxBoundary_natural h hWU (S.coordinate W c)
      _ = (finiteUniversalRelationFoxBoundary
            (sqOpenQuotientMarking h U)).map (S.coordinate U c) := by
        congr 1
        exact S.compatible hWU c
      _ = _ := rfl
  rw [hcoordinate] at hmem
  refine ⟨U, le_rfl, ?_⟩
  simpa [sqFiniteLevelModTwoFoxBoundary,
    modTwoFoxRelationMatrixLinear_apply] using hmem

/-- Every exact cofinal-range witness is, in particular, an eventual-pushdown witness. -/
theorem sqCompletedFoxEventualRange_of_cofinalRange
    (h : ℕ)
    (y : ModTwoCompletedRegularModule (DSq h : Type) (Fin (sqRank h)))
    (hy : SqCompletedFoxCofinalRange h y) :
    SqCompletedFoxEventualRange h y := by
  intro U
  obtain ⟨W, hWU, d, hd⟩ := hy U
  refine ⟨W, hWU, d, ?_⟩
  calc
    modTwoRegularModuleTransition (DSq h : Type) hWU (Fin (sqRank h))
        ((sqFiniteLevelModTwoFoxBoundary h
          (sqOpenQuotientMarking h W)).map d) =
      modTwoRegularModuleTransition (DSq h : Type) hWU (Fin (sqRank h))
        (ModTwoCompletedRegularModule.coordinate (DSq h : Type)
          (Fin (sqRank h)) W y) := congrArg _ hd
    _ = ModTwoCompletedRegularModule.coordinate (DSq h : Type)
        (Fin (sqRank h)) U y :=
      ModTwoCompletedRegularModule.coordinate_compatible
        (DSq h : Type) (Fin (sqRank h)) y hWU

/-- Consequently, the weakest eventual relation-generation condition discharges the exact
eventual-range premise used by the compactness constructor. -/
theorem sqUniversalBarFoxEventualRange_of_eventualRelationGeneration
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleFiniteUniversalBarSyzygyAt h V)
    (hgen : SqEventualRelationFoxGeneration h) :
    SqUniversalBarFoxEventualRange S :=
  fun c ↦ sqCompletedFoxEventualRange_of_cofinalRange h (S.toCompletedFox c)
    (sqUniversalBarFoxCofinalRange_of_eventualRelationGeneration S hgen c)

end

end GQ2.Dyadic.Count

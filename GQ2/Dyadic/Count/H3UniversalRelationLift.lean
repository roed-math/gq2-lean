/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3FiniteBarFoxChainHomotopy

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

private abbrev SqInputThree (h : ℕ)
    (V : OpenNormalSubgroup (DSq h : Type)) :=
  FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ V.toSubgroup)

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

end

end GQ2.Dyadic.Count

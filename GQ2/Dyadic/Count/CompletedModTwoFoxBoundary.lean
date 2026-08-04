/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.CompletedModTwoGroupAlgebra
import GQ2.Dyadic.Count.H3FiniteLevelFoxBoundary

/-!
# Completed regular mod-two modules and the square Fox boundary

For a compact topological group `G` and a basis type `J`, this file constructs the completed
regular module

`F₂[[G]]^(J) = lim_U F₂[G/U]^(J)`

as the submodule of compatible families over the open normal subgroups of `G`.  Its transition
maps are the finite regular-module pushforwards already used by the finite Fox construction.
The completion has coordinate projections, coordinatewise extensionality, and the regular
`G`-action.

The natural finite-level Fox matrices therefore assemble without any new premise into a genuine
`ModTwoFoxBoundary` between completed modules.  The final constructor uses the canonical marking
of the improved square presentation `D_sq(h)`, and the regression theorem identifies every one of
its coordinates with `sqFiniteLevelModTwoFoxBoundary`.

No injectivity is asserted here: the completed injectivity theorem is the remaining
one-relator/asphericity input.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2.Dyadic.Count GQ2.Dyadic.SqCore

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]

/-! ## The completed regular module -/

/-- The finite regular mod-two module on `J` at the open-normal level `U`. -/
abbrev ModTwoRegularModuleLevel (U : OpenNormalSubgroup G) (J : Type) :=
  RegularModTwoRelationModule (G ⧸ U.toSubgroup) J

/-- Pushforward of a finite regular module along `G/U → G/V`. -/
def modTwoRegularModuleTransition {U V : OpenNormalSubgroup G} (h : U ≤ V)
    (J : Type) :
    ModTwoRegularModuleLevel G U J →ₗ[ZMod 2] ModTwoRegularModuleLevel G V J :=
  regularModTwoPushforward (modTwoQuotientTransition G h) J

@[simp]
theorem modTwoRegularModuleTransition_single {U V : OpenNormalSubgroup G} (h : U ≤ V)
    (J : Type) (g : G ⧸ U.toSubgroup) (j : J) (a : ZMod 2) :
    modTwoRegularModuleTransition G h J (Finsupp.single (g, j) a) =
      Finsupp.single (modTwoQuotientTransition G h g, j) a :=
  regularModTwoPushforward_single (modTwoQuotientTransition G h) J g j a

/-- The transition homomorphisms between quotient groups compose as expected. -/
theorem modTwoQuotientTransition_comp {U V W : OpenNormalSubgroup G}
    (hUV : U ≤ V) (hVW : V ≤ W) :
    (modTwoQuotientTransition G hVW).comp (modTwoQuotientTransition G hUV) =
      modTwoQuotientTransition G (hUV.trans hVW) := by
  ext g
  rfl

/-- Functoriality of completed-regular-module transition maps. -/
theorem modTwoRegularModuleTransition_comp
    {U V W : OpenNormalSubgroup G} (hUV : U ≤ V) (hVW : V ≤ W)
    (J : Type) (c : ModTwoRegularModuleLevel G U J) :
    modTwoRegularModuleTransition G hVW J
        (modTwoRegularModuleTransition G hUV J c) =
      modTwoRegularModuleTransition G (hUV.trans hVW) J c := by
  rw [modTwoRegularModuleTransition, modTwoRegularModuleTransition,
    modTwoRegularModuleTransition, regularModTwoPushforward_comp,
    modTwoQuotientTransition_comp G hUV hVW]

/-- Compatible finite regular-module coordinates, as a submodule of their product. -/
def modTwoCompletedRegularModuleSubmodule (J : Type) :
    Submodule (ZMod 2)
      (∀ U : OpenNormalSubgroup G, ModTwoRegularModuleLevel G U J) where
  carrier := {x | ∀ (U V : OpenNormalSubgroup G) (h : U ≤ V),
    modTwoRegularModuleTransition G h J (x U) = x V}
  zero_mem' := by intro U V h; simp [modTwoRegularModuleTransition]
  add_mem' := by
    intro x y hx hy U V h
    change modTwoRegularModuleTransition G h J (x U + y U) = x V + y V
    rw [map_add, hx U V h, hy U V h]
  smul_mem' := by
    intro a x hx U V h
    change modTwoRegularModuleTransition G h J (a • x U) = a • x V
    rw [map_smul, hx U V h]

/-- The completed free regular mod-two `G`-module on the basis `J`. -/
abbrev ModTwoCompletedRegularModule (J : Type) :=
  modTwoCompletedRegularModuleSubmodule G J

/-- Projection of a completed regular module to its `U`-coordinate. -/
def ModTwoCompletedRegularModule.coordinate (J : Type) (U : OpenNormalSubgroup G) :
    ModTwoCompletedRegularModule G J →ₗ[ZMod 2] ModTwoRegularModuleLevel G U J :=
  (LinearMap.proj U).comp (modTwoCompletedRegularModuleSubmodule G J).subtype

@[simp]
theorem ModTwoCompletedRegularModule.coordinate_apply
    (J : Type) (U : OpenNormalSubgroup G) (x : ModTwoCompletedRegularModule G J) :
    coordinate G J U x = x.1 U :=
  rfl

/-- Coordinates of a completed regular-module element satisfy the transition relation. -/
theorem ModTwoCompletedRegularModule.coordinate_compatible
    (J : Type) (x : ModTwoCompletedRegularModule G J)
    {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    modTwoRegularModuleTransition G h J (coordinate G J U x) = coordinate G J V x :=
  x.2 U V h

/-- Equality in a completed regular module is detected at every finite quotient. -/
@[ext]
theorem ModTwoCompletedRegularModule.ext
    (J : Type) {x y : ModTwoCompletedRegularModule G J}
    (h : ∀ U : OpenNormalSubgroup G, coordinate G J U x = coordinate G J U y) :
    x = y := by
  apply Subtype.ext
  funext U
  exact h U

/-- The coordinates of a completed regular module are jointly injective. -/
theorem ModTwoCompletedRegularModule.coordinate_jointly_injective (J : Type) :
    Function.Injective (fun x : ModTwoCompletedRegularModule G J =>
      fun U : OpenNormalSubgroup G => coordinate G J U x) := by
  intro x y h
  exact ModTwoCompletedRegularModule.ext G J (congrFun h)

/-! ## The regular action -/

/-- The left regular `G`-action on compatible families of finite regular modules. -/
instance ModTwoCompletedRegularModule.instDistribMulAction (J : Type) :
    DistribMulAction G (ModTwoCompletedRegularModule G J) where
  smul g x :=
    ⟨fun U => regularModTwoTranslate (G ⧸ U.toSubgroup) J
        (QuotientGroup.mk' U.toSubgroup g) (x.1 U), by
      intro U V h
      rw [modTwoRegularModuleTransition, regularModTwoPushforward_translate,
        modTwoQuotientTransition_mk]
      have hx := x.2 U V h
      change regularModTwoPushforward (modTwoQuotientTransition G h) J (x.1 U) =
        x.1 V at hx
      rw [hx]⟩
  one_smul x := by
    apply ModTwoCompletedRegularModule.ext G J
    intro U
    change (1 : G ⧸ U.toSubgroup) • x.1 U = x.1 U
    exact one_smul _ _
  mul_smul g h x := by
    apply ModTwoCompletedRegularModule.ext G J
    intro U
    change (QuotientGroup.mk' U.toSubgroup (g * h)) • x.1 U =
      (QuotientGroup.mk' U.toSubgroup g) •
        (QuotientGroup.mk' U.toSubgroup h) • x.1 U
    rw [map_mul, mul_smul]
  smul_zero g := by
    apply ModTwoCompletedRegularModule.ext G J
    intro U
    change regularModTwoTranslate (G ⧸ U.toSubgroup) J
      (QuotientGroup.mk' U.toSubgroup g) 0 = 0
    exact (regularModTwoTranslate (G ⧸ U.toSubgroup) J
      (QuotientGroup.mk' U.toSubgroup g)).map_zero
  smul_add g x y := by
    apply ModTwoCompletedRegularModule.ext G J
    intro U
    change regularModTwoTranslate (G ⧸ U.toSubgroup) J
        (QuotientGroup.mk' U.toSubgroup g) (x.1 U + y.1 U) =
      regularModTwoTranslate (G ⧸ U.toSubgroup) J
          (QuotientGroup.mk' U.toSubgroup g) (x.1 U) +
        regularModTwoTranslate (G ⧸ U.toSubgroup) J
          (QuotientGroup.mk' U.toSubgroup g) (y.1 U)
    exact (regularModTwoTranslate (G ⧸ U.toSubgroup) J
      (QuotientGroup.mk' U.toSubgroup g)).map_add _ _

/-- Every finite-level coordinate projection is equivariant for the regular action. -/
@[simp]
theorem ModTwoCompletedRegularModule.coordinate_smul
    (J : Type) (U : OpenNormalSubgroup G) (g : G)
    (x : ModTwoCompletedRegularModule G J) :
    coordinate G J U (g • x) =
      regularModTwoTranslate (G ⧸ U.toSubgroup) J
        (QuotientGroup.mk' U.toSubgroup g) (coordinate G J U x) :=
  rfl

/-! ## Assembly of finite Fox boundaries -/

variable {G}

/-- The completed Fox boundary assembled from the compatible finite-level Fox matrices. -/
def completedModTwoFoxBoundary
    {I rel : Type}
    (m : I → G) (word : rel → FreeGroup I) :
    ModTwoFoxBoundary G
      (ModTwoCompletedRegularModule G rel)
      (ModTwoCompletedRegularModule G I) where
  map :=
    { toFun := fun c =>
        ⟨fun U =>
            (finiteLevelModTwoFoxBoundary
              (fun i => QuotientGroup.mk' U.toSubgroup (m i)) word).map
              (ModTwoCompletedRegularModule.coordinate G rel U c), by
          intro U V h
          calc
            modTwoRegularModuleTransition G h I
                ((finiteLevelModTwoFoxBoundary
                  (fun i => QuotientGroup.mk' U.toSubgroup (m i)) word).map
                  (ModTwoCompletedRegularModule.coordinate G rel U c)) =
              (finiteLevelModTwoFoxBoundary
                  (fun i => modTwoQuotientTransition G h
                    (QuotientGroup.mk' U.toSubgroup (m i))) word).map
                (modTwoRegularModuleTransition G h rel
                  (ModTwoCompletedRegularModule.coordinate G rel U c)) :=
                finiteLevelModTwoFoxBoundary_natural
                  (modTwoQuotientTransition G h)
                  (fun i => QuotientGroup.mk' U.toSubgroup (m i)) word _
            _ = (finiteLevelModTwoFoxBoundary
                  (fun i => QuotientGroup.mk' V.toSubgroup (m i)) word).map
                (ModTwoCompletedRegularModule.coordinate G rel V c) := by
              rw [ModTwoCompletedRegularModule.coordinate_compatible G rel c h]
              rfl⟩
      map_add' := by
        intro x y
        apply ModTwoCompletedRegularModule.ext G I
        intro U
        change (finiteLevelModTwoFoxBoundary
            (fun i => QuotientGroup.mk' U.toSubgroup (m i)) word).map
              (ModTwoCompletedRegularModule.coordinate G rel U x +
                ModTwoCompletedRegularModule.coordinate G rel U y) =
          (finiteLevelModTwoFoxBoundary
            (fun i => QuotientGroup.mk' U.toSubgroup (m i)) word).map
              (ModTwoCompletedRegularModule.coordinate G rel U x) +
          (finiteLevelModTwoFoxBoundary
            (fun i => QuotientGroup.mk' U.toSubgroup (m i)) word).map
              (ModTwoCompletedRegularModule.coordinate G rel U y)
        exact map_add _ _ _
      map_smul' := by
        intro a x
        apply ModTwoCompletedRegularModule.ext G I
        intro U
        change (finiteLevelModTwoFoxBoundary
            (fun i => QuotientGroup.mk' U.toSubgroup (m i)) word).map
              (a • ModTwoCompletedRegularModule.coordinate G rel U x) =
          a • (finiteLevelModTwoFoxBoundary
            (fun i => QuotientGroup.mk' U.toSubgroup (m i)) word).map
              (ModTwoCompletedRegularModule.coordinate G rel U x)
        exact map_smul _ _ _ }
  equivariant := by
    intro g c
    apply ModTwoCompletedRegularModule.ext G I
    intro U
    exact (finiteLevelModTwoFoxBoundary
      (fun i => QuotientGroup.mk' U.toSubgroup (m i)) word).equivariant
        (QuotientGroup.mk' U.toSubgroup g)
        (ModTwoCompletedRegularModule.coordinate G rel U c)

/-- Coordinate formula for the assembled completed boundary. -/
@[simp]
theorem completedModTwoFoxBoundary_coordinate
    {I rel : Type}
    (m : I → G) (word : rel → FreeGroup I)
    (U : OpenNormalSubgroup G) (c : ModTwoCompletedRegularModule G rel) :
    ModTwoCompletedRegularModule.coordinate G I U
        ((completedModTwoFoxBoundary m word).map c) =
      (finiteLevelModTwoFoxBoundary
        (fun i => QuotientGroup.mk' U.toSubgroup (m i)) word).map
        (ModTwoCompletedRegularModule.coordinate G rel U c) :=
  rfl

/-! ## The actual improved square presentation -/

/-- The completed mod-two Fox boundary for the canonical generators of `D_sq(h)`. -/
def sqCompletedModTwoFoxBoundary (h : ℕ) :
    ModTwoFoxBoundary (DSq h : Type)
      (ModTwoCompletedRegularModule (DSq h : Type) Unit)
      (ModTwoCompletedRegularModule (DSq h : Type) (Fin (sqRank h))) :=
  completedModTwoFoxBoundary (sqGen h) (fun _ : Unit => sqDiscreteRelator h)

/-- Regression: every coordinate of the completed improved-square boundary is exactly the
previously constructed finite-level improved-square Fox boundary. -/
@[simp]
theorem sqCompletedModTwoFoxBoundary_coordinate
    (h : ℕ) (U : OpenNormalSubgroup (DSq h : Type))
    (c : ModTwoCompletedRegularModule (DSq h : Type) Unit) :
    ModTwoCompletedRegularModule.coordinate (DSq h : Type) (Fin (sqRank h)) U
        ((sqCompletedModTwoFoxBoundary h).map c) =
      (sqFiniteLevelModTwoFoxBoundary h
        (fun i => QuotientGroup.mk' U.toSubgroup (sqGen h i))).map
        (ModTwoCompletedRegularModule.coordinate (DSq h : Type) Unit U c) :=
  rfl

end

end GQ2.ContCoh

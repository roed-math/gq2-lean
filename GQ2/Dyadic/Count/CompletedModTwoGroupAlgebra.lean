/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3OneRelatorAsphericity
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

/-!
# The mod-two completed group algebra

For a profinite group `G`, this file constructs `F₂[[G]]` as the algebra of compatible
families in the finite group algebras

`F₂[G/U]`, for `U : OpenNormalSubgroup G`.

The transition map for `U ≤ V` is induced by the quotient homomorphism `G/U → G/V`.
Defining the completion as a `Subalgebra` of the product gives its additive, multiplicative,
and `F₂`-module structures without postulating any completed-ring object.  The coordinate maps
are algebra maps, compatibility is exposed as a theorem, and equality is detected coordinatewise.

The last section constructs the left regular `G`-action and proves that every coordinate map is
equivariant.  Thus this type is a concrete possible carrier for both `R` and the components of
`X` in `ModTwoFoxBoundary`.
-/

namespace GQ2.ContCoh

noncomputable section

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]

/-- The finite group algebra at the open-normal level `U`. -/
abbrev ModTwoGroupAlgebraLevel (U : OpenNormalSubgroup G) :=
  MonoidAlgebra (ZMod 2) (G ⧸ U.toSubgroup)

/-- The quotient homomorphism `G/U → G/V` for `U ≤ V`. -/
def modTwoQuotientTransition {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    (G ⧸ U.toSubgroup) →* (G ⧸ V.toSubgroup) :=
  QuotientGroup.map U.toSubgroup V.toSubgroup (MonoidHom.id G) h

@[simp]
theorem modTwoQuotientTransition_mk {U V : OpenNormalSubgroup G} (h : U ≤ V) (g : G) :
    modTwoQuotientTransition G h (QuotientGroup.mk' U.toSubgroup g) =
      QuotientGroup.mk' V.toSubgroup g :=
  rfl

/-- The algebra transition map `F₂[G/U] → F₂[G/V]` for `U ≤ V`. -/
def modTwoGroupAlgebraTransition {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    ModTwoGroupAlgebraLevel G U →ₐ[ZMod 2] ModTwoGroupAlgebraLevel G V :=
  MonoidAlgebra.mapDomainAlgHom (ZMod 2) (ZMod 2) (modTwoQuotientTransition G h)

@[simp]
theorem modTwoGroupAlgebraTransition_single {U V : OpenNormalSubgroup G} (h : U ≤ V)
    (x : G ⧸ U.toSubgroup) (a : ZMod 2) :
    modTwoGroupAlgebraTransition G h (MonoidAlgebra.single x a) =
      MonoidAlgebra.single (modTwoQuotientTransition G h x) a := by
  simp [modTwoGroupAlgebraTransition]

@[simp]
theorem modTwoGroupAlgebraTransition_refl (U : OpenNormalSubgroup G) :
    modTwoGroupAlgebraTransition G (le_refl U) = AlgHom.id (ZMod 2) _ := by
  ext x
  simp [modTwoGroupAlgebraTransition, modTwoQuotientTransition]

theorem modTwoGroupAlgebraTransition_comp {U V W : OpenNormalSubgroup G}
    (hUV : U ≤ V) (hVW : V ≤ W) :
    modTwoGroupAlgebraTransition G (hUV.trans hVW) =
      (modTwoGroupAlgebraTransition G hVW).comp (modTwoGroupAlgebraTransition G hUV) := by
  ext x
  simp [modTwoGroupAlgebraTransition, modTwoQuotientTransition]

/-- The inverse-limit subalgebra of compatible finite-level group-algebra coordinates. -/
def modTwoCompletedGroupAlgebraSubalgebra :
    Subalgebra (ZMod 2) (∀ U : OpenNormalSubgroup G, ModTwoGroupAlgebraLevel G U) where
  carrier := {x | ∀ (U V : OpenNormalSubgroup G) (h : U ≤ V),
    modTwoGroupAlgebraTransition G h (x U) = x V}
  zero_mem' := by intro U V h; simp
  one_mem' := by intro U V h; simp
  add_mem' := by
    intro x y hx hy U V h
    change modTwoGroupAlgebraTransition G h (x U + y U) = x V + y V
    rw [map_add, hx U V h, hy U V h]
  mul_mem' := by
    intro x y hx hy U V h
    change modTwoGroupAlgebraTransition G h (x U * y U) = x V * y V
    rw [map_mul, hx U V h, hy U V h]
  algebraMap_mem' := by intro a U V h; simp

/-- The explicit mod-two completed group algebra `F₂[[G]]`. -/
abbrev ModTwoCompletedGroupAlgebra := modTwoCompletedGroupAlgebraSubalgebra G

/-- An open-normal quotient of a compact topological group is finite. -/
instance modTwoGroupAlgebraLevel_finite (U : OpenNormalSubgroup G) :
    Finite (G ⧸ U.toSubgroup) :=
  U.toSubgroup.quotient_finite_of_isOpen U.isOpen'

/-- Projection from the completed group algebra to its `U`-coordinate. -/
def ModTwoCompletedGroupAlgebra.coordinate (U : OpenNormalSubgroup G) :
    ModTwoCompletedGroupAlgebra G →ₐ[ZMod 2] ModTwoGroupAlgebraLevel G U :=
  (Pi.evalAlgHom (ZMod 2) _ U).comp (modTwoCompletedGroupAlgebraSubalgebra G).val

@[simp]
theorem ModTwoCompletedGroupAlgebra.coordinate_apply
    (U : OpenNormalSubgroup G) (x : ModTwoCompletedGroupAlgebra G) :
    coordinate G U x = x.1 U :=
  rfl

/-- Coordinates of a completed group-algebra element satisfy the transition relation. -/
theorem ModTwoCompletedGroupAlgebra.coordinate_compatible
    (x : ModTwoCompletedGroupAlgebra G) {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    modTwoGroupAlgebraTransition G h (coordinate G U x) = coordinate G V x :=
  x.2 U V h

/-- Equality in the completion is detected at every finite quotient. -/
@[ext]
theorem ModTwoCompletedGroupAlgebra.ext
    {x y : ModTwoCompletedGroupAlgebra G}
    (h : ∀ U : OpenNormalSubgroup G, coordinate G U x = coordinate G U y) : x = y := by
  apply Subtype.ext
  funext U
  exact h U

/-- The coordinate maps are jointly injective. -/
theorem ModTwoCompletedGroupAlgebra.coordinate_jointly_injective :
    Function.Injective (fun x : ModTwoCompletedGroupAlgebra G =>
      fun U : OpenNormalSubgroup G => coordinate G U x) := by
  intro x y h
  exact ModTwoCompletedGroupAlgebra.ext G (congrFun h)

/-- The canonical group-like element `[g]` of `F₂[[G]]`. -/
def ModTwoCompletedGroupAlgebra.of : G →* ModTwoCompletedGroupAlgebra G where
  toFun g :=
    ⟨fun U => MonoidAlgebra.single (QuotientGroup.mk' U.toSubgroup g) 1, by
      intro U V h
      rw [modTwoGroupAlgebraTransition_single, modTwoQuotientTransition_mk]⟩
  map_one' := by
    apply ModTwoCompletedGroupAlgebra.ext G
    intro U
    change MonoidAlgebra.single 1 1 = 1
    exact MonoidAlgebra.one_def.symm
  map_mul' g h := by
    apply Subtype.ext
    funext U
    simp only [Subalgebra.coe_mul, Pi.mul_apply]
    change MonoidAlgebra.single (QuotientGroup.mk' U.toSubgroup (g * h)) 1 =
      MonoidAlgebra.single (QuotientGroup.mk' U.toSubgroup g) 1 *
        MonoidAlgebra.single (QuotientGroup.mk' U.toSubgroup h) 1
    rw [map_mul, MonoidAlgebra.single_mul_single]
    simp

@[simp]
theorem ModTwoCompletedGroupAlgebra.coordinate_of
    (U : OpenNormalSubgroup G) (g : G) :
    coordinate G U (of G g) =
      MonoidAlgebra.single (QuotientGroup.mk' U.toSubgroup g) 1 :=
  rfl

/-! ## The regular action -/

/-- Left multiplication by `g` on the finite quotient group algebra at level `U`. -/
def modTwoGroupAlgebraLevelRegularAction (U : OpenNormalSubgroup G) (g : G)
    (x : ModTwoGroupAlgebraLevel G U) : ModTwoGroupAlgebraLevel G U :=
  MonoidAlgebra.single (QuotientGroup.mk' U.toSubgroup g) 1 * x

@[simp]
theorem modTwoGroupAlgebraLevelRegularAction_zero (U : OpenNormalSubgroup G) (g : G) :
    modTwoGroupAlgebraLevelRegularAction G U g 0 = 0 := by
  simp [modTwoGroupAlgebraLevelRegularAction]

@[simp]
theorem modTwoGroupAlgebraLevelRegularAction_add (U : OpenNormalSubgroup G) (g : G)
    (x y : ModTwoGroupAlgebraLevel G U) :
    modTwoGroupAlgebraLevelRegularAction G U g (x + y) =
      modTwoGroupAlgebraLevelRegularAction G U g x +
        modTwoGroupAlgebraLevelRegularAction G U g y := by
  simp [modTwoGroupAlgebraLevelRegularAction, mul_add]

@[simp]
theorem modTwoGroupAlgebraLevelRegularAction_one (U : OpenNormalSubgroup G)
    (x : ModTwoGroupAlgebraLevel G U) :
    modTwoGroupAlgebraLevelRegularAction G U 1 x = x := by
  change MonoidAlgebra.single 1 1 * x = x
  rw [← MonoidAlgebra.one_def, one_mul]

theorem modTwoGroupAlgebraLevelRegularAction_mul (U : OpenNormalSubgroup G) (g h : G)
    (x : ModTwoGroupAlgebraLevel G U) :
    modTwoGroupAlgebraLevelRegularAction G U (g * h) x =
      modTwoGroupAlgebraLevelRegularAction G U g
        (modTwoGroupAlgebraLevelRegularAction G U h x) := by
  simp only [modTwoGroupAlgebraLevelRegularAction, map_mul]
  rw [← mul_assoc, MonoidAlgebra.single_mul_single]
  simp

/-- Transition maps intertwine the left regular action. -/
theorem modTwoGroupAlgebraTransition_regularAction {U V : OpenNormalSubgroup G}
    (h : U ≤ V) (g : G) (x : ModTwoGroupAlgebraLevel G U) :
    modTwoGroupAlgebraTransition G h (modTwoGroupAlgebraLevelRegularAction G U g x) =
      modTwoGroupAlgebraLevelRegularAction G V g (modTwoGroupAlgebraTransition G h x) := by
  change modTwoGroupAlgebraTransition G h
      (MonoidAlgebra.single (QuotientGroup.mk' U.toSubgroup g) 1 * x) = _
  rw [map_mul, modTwoGroupAlgebraTransition_single]
  rfl

/-- The left regular action of `G` on its completed mod-two group algebra. -/
instance ModTwoCompletedGroupAlgebra.instDistribMulAction :
    DistribMulAction G (ModTwoCompletedGroupAlgebra G) where
  smul g x :=
    ⟨fun U => modTwoGroupAlgebraLevelRegularAction G U g (x.1 U), by
      intro U V h
      rw [modTwoGroupAlgebraTransition_regularAction, x.2 U V h]⟩
  one_smul x := by
    apply ModTwoCompletedGroupAlgebra.ext G
    intro U
    exact modTwoGroupAlgebraLevelRegularAction_one G U (x.1 U)
  mul_smul g h x := by
    apply ModTwoCompletedGroupAlgebra.ext G
    intro U
    exact modTwoGroupAlgebraLevelRegularAction_mul G U g h (x.1 U)
  smul_zero g := by
    apply ModTwoCompletedGroupAlgebra.ext G
    intro U
    exact modTwoGroupAlgebraLevelRegularAction_zero G U g
  smul_add g x y := by
    apply ModTwoCompletedGroupAlgebra.ext G
    intro U
    exact modTwoGroupAlgebraLevelRegularAction_add G U g (x.1 U) (y.1 U)

/-- Every finite-level coordinate map is equivariant for the regular action. -/
@[simp]
theorem ModTwoCompletedGroupAlgebra.coordinate_smul
    (U : OpenNormalSubgroup G) (g : G) (x : ModTwoCompletedGroupAlgebra G) :
    coordinate G U (g • x) = modTwoGroupAlgebraLevelRegularAction G U g (coordinate G U x) :=
  rfl

/-- The regular action is left multiplication by the canonical group-like element. -/
theorem ModTwoCompletedGroupAlgebra.smul_eq_mul_of
    (g : G) (x : ModTwoCompletedGroupAlgebra G) :
    g • x = of G g * x := by
  apply ModTwoCompletedGroupAlgebra.ext G
  intro U
  rfl

/-- The completed group algebra gives a concrete, non-postulated carrier for a mod-two Fox
boundary.  This zero boundary is only a type-and-action regression constructor; the actual Fox
derivative is the next mathematical construction. -/
def ModTwoCompletedGroupAlgebra.zeroFoxBoundary
    (G₀ : Type) [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀] [CompactSpace G₀] :
    ModTwoFoxBoundary G₀ (ModTwoCompletedGroupAlgebra G₀) (ModTwoCompletedGroupAlgebra G₀) where
  map := 0
  equivariant := by intro g x; simp

end

end GQ2.ContCoh

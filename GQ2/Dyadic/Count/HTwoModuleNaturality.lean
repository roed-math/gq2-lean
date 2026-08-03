/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoModuleGlobal

/-!
# Coefficient naturality of the module-valued degree-two obstruction

The module obstruction is obtained by evaluating the intrinsic relators in the twisted
extension attached to a normalized cocycle.  Pushing the coefficient module through an
equivariant additive homomorphism pushes that extension, and hence every relator fibre,
coordinatewise.  This is the cochain-level naturality needed by the `(0,2)` and `(2,0)`
continuous-cup/word-Stokes comparison squares.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic ContCoh

namespace ModuleExt

variable {L : Type*} {A B : Type} [Group L]
  [AddCommGroup A] [DistribMulAction L A]
  [AddCommGroup B] [DistribMulAction L B]

/-- Push the fibre coordinate of a twisted extension through an equivariant additive map. -/
def mapCoeff (f : A →+ B) (hf : ∀ (g : L) (a : A), f (g • a) = g • f a)
    (z : ModuleTwoCocycle L A) : ModuleExt z →* ModuleExt (z.map f hf) where
  toFun p := ⟨f p.u, p.g⟩
  map_one' := by
    apply ModuleExt.ext
    · exact map_zero f
    · rfl
  map_mul' p q := by
    apply ModuleExt.ext
    · simp only [mul_u, ModuleTwoCocycle.map_κ, map_add, hf]
    · rfl

@[simp] theorem mapCoeff_u (f : A →+ B) (hf) (z : ModuleTwoCocycle L A)
    (p : ModuleExt z) : (mapCoeff f hf z p).u = f p.u := rfl

@[simp] theorem mapCoeff_g (f : A →+ B) (hf) (z : ModuleTwoCocycle L A)
    (p : ModuleExt z) : (mapCoeff f hf z p).g = p.g := rfl

@[simp] theorem mapCoeff_lift {X : Type*} (f : A →+ B) (hf)
    (z : ModuleTwoCocycle L A) (m : X → L) (x : X) :
    mapCoeff f hf z (lift z m x) = lift (z.map f hf) m x := by
  apply ModuleExt.ext <;> simp [mapCoeff, lift]

end ModuleExt

section Relator

variable {X : Type*} {L A B : Type} [Group L] [TopologicalSpace L] [DiscreteTopology L] [Finite L]
  [AddCommGroup A] [DistribMulAction L A] [Finite A]
  [AddCommGroup B] [DistribMulAction L B] [Finite B]

/-- Relator fibres commute with an equivariant coefficient map. -/
theorem moduleRel_map (W : PWord X) (m : X → L) (z : ModuleTwoCocycle L A)
    (f : A →+ B) (hf : ∀ (g : L) (a : A), f (g • a) = g • f a) :
    moduleRel (A := B) W m (z.map f hf) =
      f (moduleRel (A := A) W m z) := by
  let F : ContinuousMonoidHom (ModuleExt z) (ModuleExt (z.map f hf)) :=
    ⟨ModuleExt.mapCoeff f hf z, continuous_of_discreteTopology⟩
  have h := PWord.map_eval F (ModuleExt.lift z m) W
  have hgen : (fun x ↦ F (ModuleExt.lift z m x)) = ModuleExt.lift (z.map f hf) m := by
    funext x
    exact ModuleExt.mapCoeff_lift f hf z m x
  have hu := congrArg ModuleExt.u h
  rw [hgen] at hu
  exact hu.symm

end Relator

section Global

variable {iota rel : Type*}
  {G C A B : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A] [DistribMulAction G A] [ContinuousSMul G A]
  [DistribMulAction C A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [DiscreteTopology B] [Finite B] [DistribMulAction G B] [ContinuousSMul G B]
  [DistribMulAction C B]

local instance moduleNaturalityQuotientDiscreteTopology (V : OpenNormalSubgroup G) :
    DiscreteTopology (G ⧸ V.toSubgroup) :=
  Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul V.toOpenSubgroup

/-- Normalization commutes pointwise with an equivariant coefficient map. -/
theorem moduleNormalize_map (f : A →+ B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) (z : G × G → A) :
    moduleNormalize (fun p ↦ f (z p)) = fun p ↦ f (moduleNormalize z p) := by
  funext p
  simp only [moduleNormalize, map_sub, hf]

/-- **Global coefficient naturality of the relator obstruction.**  This is proved at the
chosen finite factor of `z`; its image under `f` is a factor of the pushed cocycle at the
same level, and `moduleRel_map` identifies every relator fibre. -/
theorem moduleObsFun_mapCoeff (W : rel → PWord iota) (gen : iota → G)
    (rho : ContinuousMonoidHom G C)
    (hcompatA : ∀ (g : G) (a : A), g • a = rho g • a)
    (hcompatB : ∀ (g : G) (b : B), g • b = rho g • b)
    (f : A →+ B)
    (hfG : ∀ (g : G) (a : A), f (g • a) = g • f a)
    (z : Z2 G A) :
    moduleObsFun W gen rho hcompatB
        (Z2comap (ContinuousMonoidHom.id G) f continuous_of_discreteTopology hfG z) =
      fun k ↦ f (moduleObsFun W gen rho hcompatA z k) := by
  let zB : Z2 G B :=
    Z2comap (ContinuousMonoidHom.id G) f continuous_of_discreteTopology hfG z
  let FA := (nonempty_moduleLevelFactor rho hcompatA z).some
  letI : DistribMulAction (G ⧸ FA.V.toSubgroup) A :=
    DistribMulAction.compHom A (quotientActionHom rho FA.V FA.hV)
  letI : DistribMulAction (G ⧸ FA.V.toSubgroup) B :=
    DistribMulAction.compHom B (quotientActionHom rho FA.V FA.hV)
  have hfV : ∀ (g : G ⧸ FA.V.toSubgroup) (a : A), f (g • a) = g • f a := by
    intro g a
    induction g using QuotientGroup.induction_on with
    | H g =>
        change f (rho g • a) = rho g • f a
        rw [← hcompatA, ← hcompatB, hfG]
  let FB : ModuleLevelFactor rho (moduleNormalize zB.1) :=
    { V := FA.V
      hV := FA.hV
      z := FA.z.map f hfV
      hfact := by
        intro x y
        change moduleNormalize (fun p ↦ f (z.1 p)) (x, y) =
          f (FA.z.κ (QuotientGroup.mk' FA.V.toSubgroup x)
            (QuotientGroup.mk' FA.V.toSubgroup y))
        rw [congrFun (moduleNormalize_map f hfG z.1) (x, y), FA.hfact x y] }
  rw [moduleObsFun_eq W gen rho hcompatB zB FB,
    moduleObsFun_eq W gen rho hcompatA z FA]
  funext k
  exact moduleRel_map (W k)
    (fun i ↦ QuotientGroup.mk' FA.V.toSubgroup (gen i)) FA.z f hfV

end Global

end GQ2.Dyadic.Count

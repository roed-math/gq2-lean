/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLDirectAsphericity

/-!
# Finite-extension asphericity through the image of an arbitrary target map

For an arbitrary finite map `rho : GammaL → C`, the source sees only the subgroup
`rho.range`.  Restricting the `C`-action to this image makes the range-restricted map surjective,
so the direct simple theorem applies whenever the coefficient remains simple after restriction.
The resulting finite-extension witnesses transport back to the original target because the two
action-compatible quotient actions are equal.

The restricted-simplicity hypothesis is real: a simple module for `C` need not remain simple for
an arbitrary subgroup.  Thus this file gives the strongest action-image provider justified by
the existing direct dichotomy without adding a false restriction-of-scalars claim.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG

private theorem continuousSMul_comp_imageAsphericity
    {G C A : Type} [Monoid G] [TopologicalSpace G]
    [Monoid C] [TopologicalSpace C] [DiscreteTopology C]
    [TopologicalSpace A] [DiscreteTopology A] [SMul C A]
    (rho : ContinuousMonoidHom G C) [SMul G A]
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a) : ContinuousSMul G A := by
  constructor
  have hfac : (fun p : G × A ↦ p.1 • p.2) =
      (fun p : C × A ↦ p.1 • p.2) ∘ (fun p : G × A ↦ (rho p.1, p.2)) := by
    funext p
    exact hcompat p.1 p.2
  rw [hfac]
  exact continuous_of_discreteTopology.comp
    ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)

section ImageDefinitions

variable {h q : ℕ} {C A : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [DistribMulAction C A] [Finite A]

local notation "GammaL" => (gamma h q : Type)

/-- The actual image of an arbitrary finite target map. -/
abbrev FiniteTargetImage (rho : ContinuousMonoidHom GammaL C) : Type :=
  ↥rho.toMonoidHom.range

/-- The range-restricted target map, which is surjective by construction. -/
def finiteTargetImageHom (rho : ContinuousMonoidHom GammaL C) :
    ContinuousMonoidHom GammaL (FiniteTargetImage rho) where
  toMonoidHom := rho.toMonoidHom.rangeRestrict
  continuous_toFun := rho.continuous_toFun.subtype_mk _

/-- Simplicity after restricting the coefficient action from `C` to the subgroup actually seen
by `GammaL`. -/
def IsSimpleOnTargetImage (rho : ContinuousMonoidHom GammaL C) : Prop :=
  letI : DistribMulAction (FiniteTargetImage rho) A :=
    DistribMulAction.compHom A rho.toMonoidHom.range.subtype
  IsSimpleModTwo (FiniteTargetImage rho) A

/-- Restriction from `C` to the subgroup actually reached by `rho` preserves every simple
finite coefficient.  This is the precise extra condition needed to turn the imagewise theorem
into a provider for an arbitrary, possibly non-surjective, target map. -/
def SimpleRestrictionToTargetImage (rho : ContinuousMonoidHom GammaL C) : Prop :=
  ∀ (B : Type) [AddCommGroup B] [DistribMulAction C B] [Finite B],
    IsSimpleModTwo C B → IsSimpleOnTargetImage (A := B) rho

/-- Surjective target maps satisfy the image-restriction condition.  This recovers the direct
generating-target theorem as a special case of the action-image result. -/
theorem simpleRestrictionToTargetImage_of_surjective
    (rho : ContinuousMonoidHom GammaL C) (hrho : Function.Surjective rho) :
    SimpleRestrictionToTargetImage rho := by
  intro B _ _ _ hsimple
  letI : DistribMulAction (FiniteTargetImage rho) B :=
    DistribMulAction.compHom B rho.toMonoidHom.range.subtype
  refine ⟨hsimple.1, fun W hW ↦ hsimple.2 W ?_⟩
  intro c b hb
  obtain ⟨g, hg⟩ := hrho c
  have himage : c ∈ rho.toMonoidHom.range := ⟨g, hg⟩
  have hmem := hW (⟨c, himage⟩ : FiniteTargetImage rho) b hb
  change c • b ∈ W at hmem
  exact hmem

end ImageDefinitions

section AsphericityTransport

variable {h q : ℕ} {C A : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [DistribMulAction C A] [Finite A]

local notation "GammaL" => (gamma h q : Type)
local notation "WL" => gammaFam (2 * h + 1) q (Words.LSq.lSqW h)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)

/-- Transport a relation-level extension witness across equality of the ambient action.
Keeping the actions explicit here avoids relying on typeclass elaboration to rewrite a hidden
`DistribMulAction` argument. -/
private noncomputable def finiteRelatorExtensionWitness_castAction
    {iota rel L B : Type} [Group L] [AddCommGroup B]
    (act₁ act₂ : DistribMulAction L B) (hact : act₁ = act₂)
    {W : rel → PWord iota} {m : iota → L} {r : rel → B}
    (D : @FiniteRelatorExtensionWitness iota rel L B _ _ act₁ W m r) :
    @FiniteRelatorExtensionWitness iota rel L B _ _ act₂ W m r := by
  subst act₂
  exact D

/-- The range-restricted and original maps have the same kernel. -/
theorem finiteTargetImageHom_ker
    (rho : ContinuousMonoidHom GammaL C) :
    (finiteTargetImageHom rho).toMonoidHom.ker = rho.toMonoidHom.ker := by
  ext g
  constructor
  · intro hg
    exact congrArg Subtype.val hg
  · intro hg
    exact Subtype.ext hg

/-- Finite-extension asphericity over the actual image transports to the original finite target.
The proof identifies the two quotient actions, so the extension and its chosen relator lifts are
transported without changing their underlying data. -/
theorem lModuleFiniteExtensionAsphericity_of_targetImage
    (rho : ContinuousMonoidHom GammaL C)
    (hasph :
      letI : DistribMulAction (FiniteTargetImage rho) A :=
        DistribMulAction.compHom A rho.toMonoidHom.range.subtype
      LModuleFiniteExtensionAsphericity (A := A) (finiteTargetImageHom rho)) :
    LModuleFiniteExtensionAsphericity (A := A) rho := by
  intro r
  letI actImage : DistribMulAction (FiniteTargetImage rho) A :=
    DistribMulAction.compHom A rho.toMonoidHom.range.subtype
  obtain ⟨V, hVimage, hD⟩ := hasph r
  have hV : V.toSubgroup ≤ rho.toMonoidHom.ker := by
    rw [← finiteTargetImageHom_ker rho]
    exact hVimage
  let actQImage : DistribMulAction (GammaL ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A (quotientActionHom (finiteTargetImageHom rho) V hVimage)
  let actQ : DistribMulAction (GammaL ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A (quotientActionHom rho V hV)
  have hact : actQImage = actQ := by
    apply DistribMulAction.ext
    funext x a
    induction x using QuotientGroup.induction_on with
    | H g =>
        change rho g • a = rho g • a
        rfl
  letI : DistribMulAction (GammaL ⧸ V.toSubgroup) A := actQImage
  change Nonempty (FiniteRelatorExtensionWitness WL
    (fun i ↦ QuotientGroup.mk' V.toSubgroup (genL i)) r) at hD
  exact ⟨V, hV, hD.map
    (finiteRelatorExtensionWitness_castAction actQImage actQ hact)⟩

end AsphericityTransport

section ImageSimple

variable {h q : ℕ} {C V : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [DiscreteTopology V] [Finite V]
  [DistribMulAction ((gamma h q : Type)) V]
  [ContinuousSMul ((gamma h q : Type)) V]
  [DistribMulAction C V]

local notation "GammaL" => (gamma h q : Type)

/-- Direct finite-extension asphericity for an arbitrary finite target map, provided simplicity
survives restriction to its actual image. -/
theorem lUniform_simpleFiniteExtensionAsphericity_of_imageSimple
    (rho : ContinuousMonoidHom GammaL C)
    (hcompat : ∀ (g : GammaL) (v : V), g • v = rho g • v)
    (hV₂ : ∀ v : V, v + v = 0)
    (hsimpleImage : IsSimpleOnTargetImage (A := V) rho)
    (hq : Even q) :
    LModuleFiniteExtensionAsphericity (A := V) rho := by
  letI actImage : DistribMulAction (FiniteTargetImage rho) V :=
    DistribMulAction.compHom V rho.toMonoidHom.range.subtype
  have hcompatImage : ∀ (g : GammaL) (v : V),
      g • v = finiteTargetImageHom rho g • v := by
    intro g v
    exact hcompat g v
  have hasphImage :
      LModuleFiniteExtensionAsphericity (A := V) (finiteTargetImageHom rho) :=
    lUniform_simpleFiniteExtensionAsphericity_of_surjective
      (finiteTargetImageHom rho) rho.toMonoidHom.rangeRestrict_surjective
      hcompatImage hV₂ hsimpleImage hq
  exact lModuleFiniteExtensionAsphericity_of_targetImage rho hasphImage

/-- Provider form of the sharp action-image theorem.  Unlike surjectivity, the hypothesis only
asks that restriction along the actual image preserve the simple coefficients under
consideration. -/
theorem uniformSimpleExtensionAsphericitySingleProvider_of_simpleRestriction
    (rho : ContinuousMonoidHom GammaL C)
    (hrestrict : SimpleRestrictionToTargetImage rho)
    (hq : Even q) : UniformSimpleExtensionAsphericitySingleProvider rho := by
  intro A _ _ _ hA₂ hsimple
  have hsimpleImage : IsSimpleOnTargetImage (A := A) rho := hrestrict A hsimple
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : IsTopologicalAddGroup A := by infer_instance
  letI : DistribMulAction GammaL A :=
    DistribMulAction.compHom A rho.toMonoidHom
  letI : ContinuousSMul GammaL A :=
    continuousSMul_comp_imageAsphericity rho (fun _ _ ↦ rfl)
  exact lUniform_simpleFiniteExtensionAsphericity_of_imageSimple
    rho (fun _ _ ↦ rfl) hA₂ hsimpleImage hq

end ImageSimple

end

end GQ2.Dyadic.LSquare

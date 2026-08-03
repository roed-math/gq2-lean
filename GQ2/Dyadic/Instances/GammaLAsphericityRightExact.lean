/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLActionImage
import GQ2.Dyadic.Instances.GammaLH2RightExact
import GQ2.Dyadic.Instances.GammaLRelatorRealization
import GQ2.Dyadic.Instances.GammaLSimpleDirectSurjectivity
import GQ2.Dyadic.Instances.LH2ComparisonDevissage

/-!
# Finite-extension asphericity and the continuous H² right-exact tail

This file identifies the exact strengthening of the direct simple-coefficient
finite-extension theorem which is needed for cohomological dimension two.

For a surjective finite action target, ask for relator realization for **every** finite
elementary coefficient, rather than only for simple coefficients.  This all-coefficient
condition implies `GammaLH2RightExactSupply`: lift a target word-H² representative
coordinatewise across the coefficient quotient, realize the lift by a continuous H² class,
and use naturality plus injectivity of the target comparison.

Conversely, when `q` is even, the existing direct simple theorem and coefficient devissage show
that `GammaLH2RightExactSupply` implies precisely this all-coefficient realization condition.
Thus the passage from the presently proved simple finite-extension asphericity to an
all-elementary relation-module theorem is not merely sufficient for the CD-2 tail; in the
current presentation API it is equivalent to it.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG
open GQ2.Dyadic.Certificates.LSqStokes

/-! ## The elementary word-H² diagram chase -/

section WordSurjectivity

variable {iota rel C A B : Type} [Group C]
  [AddCommGroup A] [DistribMulAction C A]
  [AddCommGroup B] [DistribMulAction C B]

/-- A surjective coefficient homomorphism induces a surjection on the degree-two word
cokernel.  No exact sequence or cohomology is involved: lift a representative
coordinatewise. -/
theorem moduleWordH2Map_surjective
    (c : iota → C) (w : rel → FreeGroup iota) (f : A →+ B)
    (hfC : ∀ (g : C) (a : A), f (g • a) = g • f a)
    (hf : Function.Surjective f) :
    Function.Surjective (moduleWordH2Map c w f hfC) := by
  intro y
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective y
  let a : rel → A := fun k ↦ (hf (z k)).choose
  refine ⟨QuotientAddGroup.mk a, ?_⟩
  rw [moduleWordH2Map_mk]
  congr 1
  funext k
  exact (hf (z k)).choose_spec

end WordSurjectivity

section ComparisonChase

variable {h q e : ℕ} {C A B : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction ((gamma h q : Type)) A]
  [ContinuousSMul ((gamma h q : Type)) A]
  [DistribMulAction C A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [DiscreteTopology B] [Finite B]
  [DistribMulAction ((gamma h q : Type)) B]
  [ContinuousSMul ((gamma h q : Type)) B]
  [DistribMulAction C B]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "WL" => gammaFam (2 * h + 1) q (Words.LSq.lSqW h)
local notation "wL" => lSqFam h q e

/-- Surjectivity of the source comparison forces continuous H² right-exactness along a
surjective coefficient map.  The target comparison need only be injective, which is already a
theorem for the improved L presentation. -/
theorem H2RightExactAt.of_lModuleH2WordFlexible_surjective
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatB : ∀ (g : GammaL) (b : B), g • b = rho g • b)
    (hA₂ : ∀ a : A, a + a = 0) (hB₂ : ∀ b : B, b + b = 0)
    (hresA : ResolvesAt WL wL (WordLift A C))
    (hresB : ResolvesAt WL wL (WordLift B C))
    (f : A →+ B)
    (hfG : ∀ (g : GammaL) (a : A), f (g • a) = g • f a)
    (hfC : ∀ (c : C) (a : A), f (c • a) = c • f a)
    (hf : Function.Surjective f)
    (hsource : Function.Surjective
      (lModuleH2WordFlexible rho hcompatA hA₂ hresA)) :
    H2RightExactAt f continuous_of_discreteTopology hfG := by
  intro y
  let cmpA := lModuleH2WordFlexible rho hcompatA hA₂ hresA
  let cmpB := lModuleH2WordFlexible rho hcompatB hB₂ hresB
  let wordMap := moduleWordH2Map (fun i ↦ rho (genL i)) wL f hfC
  obtain ⟨wordA, hwordA⟩ :=
    moduleWordH2Map_surjective (fun i ↦ rho (genL i)) wL f hfC hf (cmpB y)
  obtain ⟨x, hx⟩ := hsource wordA
  refine ⟨x, lModuleH2WordFlexible_injective rho hcompatB hB₂ hresB ?_⟩
  have hnat := lModuleH2WordFlexible_natural rho hcompatA hcompatB hA₂ hB₂
    hresA hresB f hfG hfC x
  change cmpB (mapCoeff2 f continuous_of_discreteTopology hfG x) = cmpB y
  calc
    cmpB (mapCoeff2 f continuous_of_discreteTopology hfG x) = wordMap (cmpA x) := hnat.symm
    _ = wordMap wordA := congrArg wordMap hx
    _ = cmpB y := hwordA

/-- Finite relator realization for the source coefficient is enough for the preceding
diagram chase. -/
theorem H2RightExactAt.of_lModuleRelatorRealization
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatB : ∀ (g : GammaL) (b : B), g • b = rho g • b)
    (hA₂ : ∀ a : A, a + a = 0) (hB₂ : ∀ b : B, b + b = 0)
    (hresA : ResolvesAt WL wL (WordLift A C))
    (hresB : ResolvesAt WL wL (WordLift B C))
    (f : A →+ B)
    (hfG : ∀ (g : GammaL) (a : A), f (g • a) = g • f a)
    (hfC : ∀ (c : C) (a : A), f (c • a) = c • f a)
    (hf : Function.Surjective f)
    (hreal : LModuleRelatorRealization (A := A) (e := e) rho) :
    H2RightExactAt f continuous_of_discreteTopology hfG :=
  H2RightExactAt.of_lModuleH2WordFlexible_surjective rho hcompatA hcompatB
    hA₂ hB₂ hresA hresB f hfG hfC hf
      (lModuleH2WordFlexible_surjective_of_relatorRealization
        rho hcompatA hA₂ hresA hreal)

end ComparisonChase

/-! ## A common finite action target for a coefficient quotient -/

section PairActionImage

variable {h q : ℕ} {A B : Type}
  [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction ((gamma h q : Type)) A]
  [ContinuousSMul ((gamma h q : Type)) A]
  [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [Finite B]
  [DistribMulAction ((gamma h q : Type)) B]
  [ContinuousSMul ((gamma h q : Type)) B]

local notation "GammaL" => (gamma h q : Type)

/-- The simultaneous action on two coefficients. -/
noncomputable def pairFiniteActionHom : ContinuousMonoidHom GammaL
    (Multiplicative (AddAut A) × Multiplicative (AddAut B)) :=
  (finiteActionHom (G := GammaL) (M := A)).prod
    (finiteActionHom (G := GammaL) (M := B))

/-- The actual finite image of the simultaneous action on two coefficients. -/
noncomputable abbrev PairFiniteActionImage : Type :=
  ↥((pairFiniteActionHom (h := h) (q := q) (A := A) (B := B)).toMonoidHom.range)

/-- The source map to the simultaneous finite action image. -/
noncomputable def pairFiniteActionImageHom : ContinuousMonoidHom GammaL
    (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)) where
  toMonoidHom :=
    (pairFiniteActionHom (h := h) (q := q) (A := A) (B := B)).toMonoidHom.rangeRestrict
  continuous_toFun :=
    (pairFiniteActionHom (h := h) (q := q) (A := A) (B := B)).continuous_toFun.subtype_mk _

/-- Projection of the simultaneous action image to the first coefficient action. -/
noncomputable def pairFiniteActionImageFst :
    PairFiniteActionImage (h := h) (q := q) (A := A) (B := B) →*
      Multiplicative (AddAut A) where
  toFun c := c.1.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Projection of the simultaneous action image to the second coefficient action. -/
noncomputable def pairFiniteActionImageSnd :
    PairFiniteActionImage (h := h) (q := q) (A := A) (B := B) →*
      Multiplicative (AddAut B) where
  toFun c := c.1.2
  map_one' := rfl
  map_mul' _ _ := rfl

theorem pairFiniteActionImageHom_surjective : Function.Surjective
    (pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B)) :=
  (pairFiniteActionHom (h := h) (q := q) (A := A) (B := B)).toMonoidHom
    |>.rangeRestrict_surjective

@[simp] theorem pairFiniteActionImageHom_smul_fst
    (g : GammaL) (a : A) :
    letI : DistribMulAction
        (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)) A :=
      DistribMulAction.compHom A
        (pairFiniteActionImageFst (h := h) (q := q) (A := A) (B := B))
    pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B) g • a = g • a :=
  rfl

@[simp] theorem pairFiniteActionImageHom_smul_snd
    (g : GammaL) (b : B) :
    letI : DistribMulAction
        (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)) B :=
      DistribMulAction.compHom B
        (pairFiniteActionImageSnd (h := h) (q := q) (A := A) (B := B))
    pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B) g • b = g • b :=
  rfl

/-- A source-equivariant coefficient map is equivariant for the simultaneous finite action
image. -/
theorem pairFiniteActionImage_equivariant
    (f : A →+ B)
    (hf : ∀ (g : GammaL) (a : A), f (g • a) = g • f a) :
    letI : DistribMulAction
        (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)) A :=
      DistribMulAction.compHom A
        (pairFiniteActionImageFst (h := h) (q := q) (A := A) (B := B))
    letI : DistribMulAction
        (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)) B :=
      DistribMulAction.compHom B
        (pairFiniteActionImageSnd (h := h) (q := q) (A := A) (B := B))
    ∀ (c : PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)) (a : A),
      f (c • a) = c • f a := by
  intro c a
  obtain ⟨g, hg⟩ := c.property
  have hgA : c.1.1 = finiteActionHom (G := GammaL) (M := A) g :=
    congrArg Prod.fst hg.symm
  have hgB : c.1.2 = finiteActionHom (G := GammaL) (M := B) g :=
    congrArg Prod.snd hg.symm
  change f (c.1.1 • a) = c.1.2 • f a
  rw [hgA, hgB, finiteActionHom_smul, finiteActionHom_smul]
  exact hf g a

end PairActionImage

/-! ## The exact all-elementary relation-module interface -/

section UniformAllElementary

variable {h q : ℕ}

local notation "GammaL" => (gamma h q : Type)

/-- Relator realization for every finite elementary coefficient at every *surjective* finite
action target.  Compared with the currently proved direct theorem, the only strengthening is
`simple` to arbitrary elementary coefficients. -/
noncomputable abbrev UniformElementaryRelatorRealizationSurjectiveSupply : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom GammaL C), Function.Surjective rho →
    ∀ (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A],
      (∀ a : A, a + a = 0) →
        LModuleRelatorRealization (A := A)
          (e := omega2Exp (4 * Monoid.exponent C)) rho

/-- The corresponding all-elementary finite-extension asphericity supply. -/
noncomputable abbrev UniformElementaryExtensionAsphericitySurjectiveSupply : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom GammaL C), Function.Surjective rho →
    ∀ (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A],
      (∀ a : A, a + a = 0) →
        LModuleFiniteExtensionAsphericity (A := A) rho

/-- All-elementary finite-extension asphericity gives all-elementary relator realization. -/
theorem uniformElementaryRelatorRealizationSurjectiveSupply_of_extensionAsphericity
    (hasph : UniformElementaryExtensionAsphericitySurjectiveSupply (h := h) (q := q)) :
    UniformElementaryRelatorRealizationSurjectiveSupply (h := h) (q := q) := by
  intro C _ _ _ _ rho hrho A _ _ _ hA₂
  exact lModuleRelatorRealization_of_extensionAsphericity rho
    (lUniform_wordLift_resolver hA₂) (hasph C rho hrho A hA₂)

private theorem continuousSMul_comp_asphericityRightExact
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

/-- The all-elementary relator-realization supply proves the continuous H² right-exact tail.

For each coefficient quotient, the common target is the actual image of the simultaneous
action on source and target.  This makes the quotient map equivariant for the finite target,
so the comparison naturality square applies. -/
theorem gammaLH2RightExactSupply_of_allElementaryRelatorRealization
    (hreal : UniformElementaryRelatorRealizationSurjectiveSupply (h := h) (q := q)) :
    GammaLH2RightExactSupply h q := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ g _hg hgG hA₂ hB₂ hsurj
  let C := PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)
  let rho : ContinuousMonoidHom GammaL C :=
    pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B)
  letI : DistribMulAction C A := DistribMulAction.compHom A
    (pairFiniteActionImageFst (h := h) (q := q) (A := A) (B := B))
  letI : DistribMulAction C B := DistribMulAction.compHom B
    (pairFiniteActionImageSnd (h := h) (q := q) (A := A) (B := B))
  have hcompatA : ∀ (x : GammaL) (a : A), x • a = rho x • a := by
    intro x a
    exact (pairFiniteActionImageHom_smul_fst x a).symm
  have hcompatB : ∀ (x : GammaL) (b : B), x • b = rho x • b := by
    intro x b
    exact (pairFiniteActionImageHom_smul_snd x b).symm
  have hgC : ∀ (c : C) (a : A), g (c • a) = c • g a :=
    pairFiniteActionImage_equivariant g hgG
  let e := omega2Exp (4 * Monoid.exponent C)
  exact H2RightExactAt.of_lModuleRelatorRealization rho hcompatA hcompatB
    hA₂ hB₂ (lUniform_wordLift_resolver hA₂)
    (lUniform_wordLift_resolver hB₂) g hgG hgC hsurj
      (hreal C rho pairFiniteActionImageHom_surjective A hA₂)

/-- All-elementary finite-extension asphericity therefore proves the continuous H²
right-exact tail, without Tate duality or a field-realization axiom. -/
theorem gammaLH2RightExactSupply_of_allElementaryExtensionAsphericity
    (hasph : UniformElementaryExtensionAsphericitySurjectiveSupply (h := h) (q := q)) :
    GammaLH2RightExactSupply h q :=
  gammaLH2RightExactSupply_of_allElementaryRelatorRealization
    (uniformElementaryRelatorRealizationSurjectiveSupply_of_extensionAsphericity hasph)

/-- Conversely, for even `q`, the H² right-exact tail upgrades the direct simple comparison
theorem to relator realization for every finite elementary coefficient at every surjective
finite action target. -/
theorem allElementaryRelatorRealization_of_gammaLH2RightExactSupply
    (hq : Even q) (hright : GammaLH2RightExactSupply h q) :
    UniformElementaryRelatorRealizationSurjectiveSupply (h := h) (q := q) := by
  intro C _ _ _ _ rho hrho A _ _ _ hA₂
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : DistribMulAction GammaL A := DistribMulAction.compHom A rho.toMonoidHom
  letI : ContinuousSMul GammaL A :=
    continuousSMul_comp_asphericityRightExact rho (fun _ _ ↦ rfl)
  have hsimple : UniformSimpleH2SurjectiveSingleProvider rho :=
    uniformSimpleH2SurjectiveSingleProvider_of_surjective rho hrho hq
  have hbij := lModuleH2WordFlexible_bijective_of_simple_and_rightExact
    rho hsimple hright A hA₂
  exact moduleRelatorRealization_of_surjective
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h))
    rho (fun _ _ ↦ rfl) (fun U ↦ hwildLevel_gammaR U) hA₂
      (lFlexibleResolverSystem rho (lUniform_wordLift_resolver hA₂)) hbij.2

/-- At even `q`, all-elementary relator realization at generating finite targets is exactly
the continuous CD-2 tail used by coefficient devissage. -/
theorem gammaLH2RightExactSupply_iff_allElementaryRelatorRealization
    (hq : Even q) :
    GammaLH2RightExactSupply h q ↔
      UniformElementaryRelatorRealizationSurjectiveSupply (h := h) (q := q) :=
  ⟨allElementaryRelatorRealization_of_gammaLH2RightExactSupply hq,
    gammaLH2RightExactSupply_of_allElementaryRelatorRealization⟩

end UniformAllElementary

end

end GQ2.Dyadic.LSquare

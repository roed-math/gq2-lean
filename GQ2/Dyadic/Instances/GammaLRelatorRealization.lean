/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoModuleAsphericity
import GQ2.Dyadic.Instances.GammaLSimpleDualSurjectivity

/-!
# Finite relator realization for the improved L presentation

This file specializes `Count.ModuleRelatorRealizationAt` to the improved two-relator
L presentation and its fixed coefficient-independent word
`lSqFam h q (omega2Exp (4 * exponent C))`.

It closes every formal step after the missing relation-module theorem:

* a realization witness at one action-compatible finite quotient makes the canonical
  flexible L comparison surjective;
* a realization provider for simple modules supplies the existing one-map and paired
  uniform H²-surjectivity interfaces;
* consequently it feeds the established corrected exact-lifting regression.

Thus the remaining mathematical statement is finite and presentation-theoretic.  For
each simple elementary coefficient and each relator vector, construct a normalized
module cocycle on one finite quotient whose two L relator fibres agree with that vector
modulo the image of the fixed Fox differential.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG
open GQ2.Dyadic.Certificates.LSqStokes

private theorem continuousSMul_comp_finite_extensionAsphericity
    {G D A : Type} [Monoid G] [TopologicalSpace G]
    [Monoid D] [TopologicalSpace D] [DiscreteTopology D]
    [TopologicalSpace A] [DiscreteTopology A] [SMul D A]
    (rho : ContinuousMonoidHom G D) [SMul G A]
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a) : ContinuousSMul G A := by
  constructor
  have hfac : (fun p : G × A ↦ p.1 • p.2) =
      (fun p : D × A ↦ p.1 • p.2) ∘ (fun p : G × A ↦ (rho p.1, p.2)) := by
    funext p
    exact hcompat p.1 p.2
  rw [hfac]
  exact continuous_of_discreteTopology.comp
    ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)

section LRealizationAt

variable {h q e : ℕ} {C A : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction ((gamma h q : Type)) A]
  [ContinuousSMul ((gamma h q : Type)) A]
  [DistribMulAction C A]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "WL" => gammaFam (2 * h + 1) q (Words.LSq.lSqW h)
local notation "wL" => lSqFam h q e

/-- The finite relation-level realization condition for the improved L presentation at
one coefficient and one action-compatible quotient. -/
abbrev LModuleRelatorRealizationAt
    (rho : ContinuousMonoidHom GammaL C)
    (V : OpenNormalSubgroup GammaL)
    (hV : V.toSubgroup ≤ rho.toMonoidHom.ker) : Prop :=
  ModuleRelatorRealizationAt (A := A) WL genL rho (fun i ↦ rho (genL i)) wL V hV

/-- The weakest finite relation-level realization condition for the improved L
presentation: the action-compatible quotient may depend on the requested relator
vector. -/
abbrev LModuleRelatorRealization
    (rho : ContinuousMonoidHom GammaL C) : Prop :=
  ModuleRelatorRealization (A := A) WL genL rho (fun i ↦ rho (genL i)) wL

/-- The finite-extension asphericity condition for the improved L presentation.
For each requested pair of relator fibres it asks for an actual finite extension
of an action-compatible quotient in which lifted generators realize those fibres.
It contains no cocycles or cohomology groups. -/
abbrev LModuleFiniteExtensionAsphericity
    (rho : ContinuousMonoidHom GammaL C) : Prop :=
  ModuleFiniteExtensionAsphericity (A := A) WL genL rho

omit [TopologicalSpace A] [IsTopologicalAddGroup A] [DiscreteTopology A]
  [DistribMulAction GammaL A] [ContinuousSMul GammaL A] in
/-- Finite-extension asphericity implies the finite-cocycle relator realization
criterion for the improved L presentation. -/
theorem lModuleRelatorRealization_of_extensionAsphericity
    (rho : ContinuousMonoidHom GammaL C)
    (hres : ResolvesAt WL wL (WordLift A C))
    (hasph : LModuleFiniteExtensionAsphericity (A := A) rho) :
    LModuleRelatorRealization (A := A) (e := e) rho := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : DistribMulAction GammaL A :=
    DistribMulAction.compHom A rho.toMonoidHom
  letI : ContinuousSMul GammaL A :=
    continuousSMul_comp_finite_extensionAsphericity rho (fun _ _ ↦ rfl)
  exact moduleRelatorRealization_of_extensionAsphericity WL genL rho
    (fun i ↦ rho (genL i)) wL (lFlexibleResolverSystem rho hres) hasph

/-- Vector-dependent finite relator realization makes the canonical flexible L H²
comparison surjective. -/
theorem lModuleH2WordFlexible_surjective_of_relatorRealization
    (rho : ContinuousMonoidHom GammaL C)
    (hcompat : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt WL wL (WordLift A C))
    (hreal : LModuleRelatorRealization (A := A) (e := e) rho) :
    Function.Surjective (lModuleH2WordFlexible rho hcompat hA₂ hres) :=
  globalModuleH2WordFlexible_surjective_of_relatorRealization
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h))
    rho hcompat (fun U ↦ hwildLevel_gammaR U) hA₂
      (lFlexibleResolverSystem rho hres) hreal

/-- One finite relation-level realization witness makes the canonical flexible L H²
comparison surjective.  Admissibility, wildness, and all quotient-dependent resolver
obligations are discharged by the proved L presentation APIs. -/
theorem lModuleH2WordFlexible_surjective_of_relatorRealizationAt
    (rho : ContinuousMonoidHom GammaL C)
    (hcompat : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt WL wL (WordLift A C))
    (V : OpenNormalSubgroup GammaL)
    (hV : V.toSubgroup ≤ rho.toMonoidHom.ker)
    (hreal : LModuleRelatorRealizationAt (A := A) (e := e) rho V hV) :
    Function.Surjective (lModuleH2WordFlexible rho hcompat hA₂ hres) :=
  globalModuleH2WordFlexible_surjective_of_relatorRealizationAt
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h))
    rho hcompat (fun U ↦ hwildLevel_gammaR U) hA₂
      (lFlexibleResolverSystem rho hres) V hV hreal

end LRealizationAt

section UniformSimpleRealization

variable {h q : ℕ} {C : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

local notation "GammaL" => (gamma h q : Type)
local notation "eC" => omega2Exp (4 * Monoid.exponent C)

/-- A simple coefficient's relator vectors are realized on action-compatible finite
quotients, at the fixed uniform L word.  The quotient may depend on the vector. -/
abbrev UniformSimpleRelatorRealizationSingleAt
    (rho : ContinuousMonoidHom GammaL C)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A] : Prop :=
  LModuleRelatorRealization (A := A) (e := eC) rho

/-- The finite relation-module-shaped input, uniformly over simple elementary
coefficients of each finite quotient of `GammaL`. -/
abbrev UniformSimpleRelatorRealizationSingleProvider
    (rho : ContinuousMonoidHom GammaL C) : Prop :=
  ∀ (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A],
    (∀ a : A, a + a = 0) → IsSimpleModTwo C A →
      UniformSimpleRelatorRealizationSingleAt rho A

/-- The finite relation-level provider at every finite quotient of `GammaL`. -/
abbrev UniformSimpleRelatorRealizationSingleSupply : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom GammaL C),
      UniformSimpleRelatorRealizationSingleProvider rho

/-- Finite-extension asphericity for one simple coefficient at one finite action
quotient, using the fixed coefficient-independent L word. -/
abbrev UniformSimpleExtensionAsphericitySingleAt
    (rho : ContinuousMonoidHom GammaL C)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A] : Prop :=
  LModuleFiniteExtensionAsphericity (A := A) rho

/-- The relation-module-shaped finite-extension input, uniformly over simple
elementary coefficients of one finite quotient. -/
abbrev UniformSimpleExtensionAsphericitySingleProvider
    (rho : ContinuousMonoidHom GammaL C) : Prop :=
  ∀ (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A],
    (∀ a : A, a + a = 0) → IsSimpleModTwo C A →
      UniformSimpleExtensionAsphericitySingleAt rho A

/-- Finite-extension asphericity at every finite quotient of `GammaL`.  This is
the precise remaining input expected from a profinite relation-module theorem. -/
abbrev UniformSimpleExtensionAsphericitySingleSupply : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom GammaL C),
      UniformSimpleExtensionAsphericitySingleProvider rho

/-- Uniform finite-extension asphericity supplies uniform finite relator
realization.  Factor-set cocycles and the Fox-image congruence are constructed by
`moduleRelatorRealization_of_extensionAsphericity`. -/
theorem uniformSimpleRelatorRealizationSingleSupply_of_extensionAsphericity
    (hasph : UniformSimpleExtensionAsphericitySingleSupply (h := h) (q := q)) :
    UniformSimpleRelatorRealizationSingleSupply (h := h) (q := q) := by
  intro C _ _ _ _ rho A _ _ _ hA₂ hsimple
  exact lModuleRelatorRealization_of_extensionAsphericity rho
    (lUniform_wordLift_resolver hA₂) (hasph C rho A hA₂ hsimple)

/-- Uniform finite relator realization supplies the established one-map H²
surjectivity interface.  The source action may be any discrete action compatible with
`rho`; the finite realization condition itself only uses the descended quotient action. -/
theorem uniformSimpleH2SurjectiveSingleSupply_of_relatorRealization
    (hreal : UniformSimpleRelatorRealizationSingleSupply (h := h) (q := q)) :
    UniformSimpleH2SurjectiveSingleSupply (h := h) (q := q) := by
  intro C _ _ _ _ rho A _ _ _ _ _ _ _ hcompat hA₂ hsimple
  exact lModuleH2WordFlexible_surjective_of_relatorRealization
    rho hcompat hA₂ (lUniform_wordLift_resolver hA₂)
      (hreal C rho A hA₂ hsimple)

/-- The finite-extension asphericity supply therefore proves the canonical
continuous-to-word H² surjectivity interface for all simple coefficients. -/
theorem uniformSimpleH2SurjectiveSingleSupply_of_extensionAsphericity
    (hasph : UniformSimpleExtensionAsphericitySingleSupply (h := h) (q := q)) :
    UniformSimpleH2SurjectiveSingleSupply (h := h) (q := q) :=
  uniformSimpleH2SurjectiveSingleSupply_of_relatorRealization
    (uniformSimpleRelatorRealizationSingleSupply_of_extensionAsphericity hasph)

/-- Uniform finite relator realization supplies the paired primal/dual H²
surjectivity interface used by the corrected L campaign.  Dual simplicity is handled
by the already-proved one-map reduction. -/
theorem uniformSimpleH2SurjectiveSupply_of_relatorRealization
    (hreal : UniformSimpleRelatorRealizationSingleSupply (h := h) (q := q)) :
    UniformSimpleH2SurjectiveSupply (h := h) (q := q) :=
  uniformSimpleH2SurjectiveSupply_of_single
    (uniformSimpleH2SurjectiveSingleSupply_of_relatorRealization hreal)

/-- Finite-extension asphericity also supplies the paired primal/dual H²
surjectivity interface used by the exact-lifting theorem. -/
theorem uniformSimpleH2SurjectiveSupply_of_extensionAsphericity
    (hasph : UniformSimpleExtensionAsphericitySingleSupply (h := h) (q := q)) :
    UniformSimpleH2SurjectiveSupply (h := h) (q := q) :=
  uniformSimpleH2SurjectiveSupply_of_relatorRealization
    (uniformSimpleRelatorRealizationSingleSupply_of_extensionAsphericity hasph)

/-- End-to-end corrected L regression from Tate duality and the finite
relation-module-shaped realization supply. -/
theorem exactLiftingRN_of_uniformRelatorRealization_tateDuality
    [DistribMulAction GammaL (MuN 2)] [ContinuousSMul GammaL (MuN 2)]
    (hq : Even q) (D : TateDualityG GammaL 2)
    (hreal : UniformSimpleRelatorRealizationSingleSupply (h := h) (q := q))
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (gamma h q) (2 * h + 1) q P nuP
      (standardNumerics (2 * h + 1)) :=
  exactLiftingRN_of_uniformSingleH2Surjective_tateDuality hq D
    (uniformSimpleH2SurjectiveSingleSupply_of_relatorRealization hreal) nuP

/-- End-to-end corrected L regression from Tate duality and the purely
finite-extension asphericity supply. -/
theorem exactLiftingRN_of_uniformExtensionAsphericity_tateDuality
    [DistribMulAction GammaL (MuN 2)] [ContinuousSMul GammaL (MuN 2)]
    (hq : Even q) (D : TateDualityG GammaL 2)
    (hasph : UniformSimpleExtensionAsphericitySingleSupply (h := h) (q := q))
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (gamma h q) (2 * h + 1) q P nuP
      (standardNumerics (2 * h + 1)) :=
  exactLiftingRN_of_uniformRelatorRealization_tateDuality hq D
    (uniformSimpleRelatorRealizationSingleSupply_of_extensionAsphericity hasph) nuP

end UniformSimpleRealization

end

end GQ2.Dyadic.LSquare

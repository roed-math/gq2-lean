/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoModuleSurjectivity
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

/-- Uniform finite relator realization supplies the paired primal/dual H²
surjectivity interface used by the corrected L campaign.  Dual simplicity is handled
by the already-proved one-map reduction. -/
theorem uniformSimpleH2SurjectiveSupply_of_relatorRealization
    (hreal : UniformSimpleRelatorRealizationSingleSupply (h := h) (q := q)) :
    UniformSimpleH2SurjectiveSupply (h := h) (q := q) :=
  uniformSimpleH2SurjectiveSupply_of_single
    (uniformSimpleH2SurjectiveSingleSupply_of_relatorRealization hreal)

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

end UniformSimpleRealization

end

end GQ2.Dyadic.LSquare

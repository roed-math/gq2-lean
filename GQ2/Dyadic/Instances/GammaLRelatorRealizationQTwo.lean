/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLRelatorRealization
import GQ2.Dyadic.Instances.GammaLRealizationRoute
import GQ2.Dyadic.Instances.LSourceComposition

/-!
# Finite relator realization at the Q₂ L row

This file proves the complete finite relator-realization supply at the already-known
base row `(h,q) = (0,2)`.

The proof is a regression and not the missing arbitrary-`K` relation-module theorem.
It uses the independently completed Q₂ presentation to realize `GammaL(0,2)` as
`G_Q₂`; the resulting local Euler characteristic gives equality of the continuous
and word `H²` cardinalities for every finite elementary coefficient.  Since the
canonical flexible comparison is already injective, it is therefore surjective.
`Count.moduleRelatorRealization_of_surjective` then factors a chosen cocycle
representative through an action-compatible finite quotient and extracts the requested
finite relator-realization witness.

Consequently the base row proves exactly the same finite realization statement now
isolated for general L presentations, but by arithmetic reconstruction downstream of
the Q₂ theorem.  The general campaign still needs a presentation-theoretic proof that
does not first identify the candidate group with an arithmetic Galois group.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH
open ContCoh
open GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.Words.LSq GQ2.Dyadic.Certificates.LSqStokes

local notation "GammaL" => (gamma 0 2 : Type)
local notation "genL" => gammaGen 1 2 (lSqW 0)
local notation "WL" => gammaFam 1 2 (lSqW 0)

section ArbitraryCoefficient

variable {C A : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction GammaL A] [ContinuousSMul GammaL A]
  [DistribMulAction C A]

local notation "eC" => omega2Exp (4 * Monoid.exponent C)
local notation "wC" => Certificates.LSqStokes.lSqFam 0 2 eC

/-- Every elementary finite coefficient at the Q₂ L row has finite relator
realization at the coefficient-independent uniform word.

The finite quotient and normalized module cocycle may depend on the requested relator
vector.  They are extracted from the canonical continuous `H²` class supplied by the
Q₂ local-Euler cardinality comparison. -/
theorem lModuleRelatorRealization_zero_two
    (rho : ContinuousMonoidHom GammaL C)
    (hcompat : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hA₂ : ∀ a : A, a + a = 0) :
    LModuleRelatorRealization (A := A) (e := eC) rho := by
  let hres : ResolvesAt WL wC (WordLift A C) :=
    lUniform_wordLift_resolver (C := C) (h := 0) (q := 2) hA₂
  apply moduleRelatorRealization_of_surjective
    (isAdmissibleMarkedPresentation_gammaR 1 2 (lSqW 0)) rho hcompat
    (fun V ↦ hwildLevel_gammaR V) hA₂
    (lFlexibleResolverSystem rho hres)
  exact (lModuleH2EquivFlexible_of_localEulerChar rho hcompat hA₂ hres
    (gammaL_localEulerChar gammaLFieldRealization_zero_two)).surjective

end ArbitraryCoefficient

private theorem continuousSMul_comp_finite_relatorBase
    {G D A : Type*} [Monoid G] [TopologicalSpace G]
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

/-- The full coefficient-independent finite relator-realization supply at `(h,q) =
(0,2)`.  The simple-module hypothesis is not needed: the preceding theorem works for
every finite elementary module. -/
theorem uniformSimpleRelatorRealizationSingleSupply_zero_two :
    UniformSimpleRelatorRealizationSingleSupply (h := 0) (q := 2) := by
  intro C _ _ _ _ rho A _ _ _ hA₂ _hsimple
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : DistribMulAction GammaL A :=
    DistribMulAction.compHom A rho.toMonoidHom
  letI : ContinuousSMul GammaL A :=
    continuousSMul_comp_finite_relatorBase rho (fun _ _ ↦ rfl)
  exact lModuleRelatorRealization_zero_two rho (fun _ _ ↦ rfl) hA₂

/-- Regression in the exact canonical-map interface used by the general L campaign. -/
theorem uniformSimpleH2SurjectiveSingleSupply_zero_two :
    UniformSimpleH2SurjectiveSingleSupply (h := 0) (q := 2) :=
  uniformSimpleH2SurjectiveSingleSupply_of_relatorRealization
    uniformSimpleRelatorRealizationSingleSupply_zero_two

end

end GQ2.Dyadic.LSquare

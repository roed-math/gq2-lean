/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoRelationBasis
import GQ2.Dyadic.Instances.GammaLRelationModuleGlobal

/-!
# A strongly-free relation-basis boundary for the improved L presentation

This file specializes the explicit mod-two regular-basis criterion to the two improved L
relators.  Its uniform hypothesis is coefficient-independent: at every surjective finite target,
the conjugates of the two resolved relators admit equivariant coordinates in the free regular
module on `C × Fin 2` and the displayed relators have the two standard coordinates.

That is the precise conclusion expected from a strongly-free/mildness theorem.  It is strictly
stronger than the relation-character supply: the latter follows for every elementary module by
evaluating the same coordinates at arbitrary requested relator values.  The resulting pipeline
reaches the existing H²-right-exactness and Tate-duality endpoints.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.Certificates.LSqStokes

section FixedTarget

variable {h q : ℕ} {C A : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [DistribMulAction C A] [Finite A]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "wC" => lSqFam h q (omega2Exp (4 * Monoid.exponent C))

omit [Finite A] in
/-- A strongly-free coordinate system at one finite target supplies relation characters with
arbitrary prescribed values in every exponent-two coefficient module. -/
theorem lRelationModuleRelatorSurjective_of_modTwoRelationBasis
    (rho : ContinuousMonoidHom GammaL C)
    (B : ModTwoRelationBasisCoordinates
      (m := fun i => rho (genL i)) wC (lUniform_rel_death rho))
    (hA₂ : ∀ a : A, a + a = 0) :
    RelationModuleRelatorSurjective (A := A) wC
      (lUniform_rel_death rho) :=
  relationModuleRelatorSurjective_of_modTwoRelationBasis B hA₂

end FixedTarget

section UniformSupply

variable {h q : ℕ}

local notation "GammaL" => (gamma h q : Type)

/-- Coefficient-independent strongly-free coordinates for the improved L relators at every
surjective finite target.  Unlike the downstream relation-module supply, this quantifies over no
coefficient group: a single regular-basis coordinate system works for all elementary modules. -/
noncomputable abbrev UniformModTwoRelationBasisSupply : Type _ :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom GammaL C), Function.Surjective rho →
      ModTwoRelationBasisCoordinates
        (m := fun i => rho (gammaGen (2 * h + 1) q (Words.LSq.lSqW h) i))
        (lSqFam h q (omega2Exp (4 * Monoid.exponent C)))
        (lUniform_rel_death rho)

/-- Strongly-free coordinates imply the uniform classical relation-character theorem. -/
theorem uniformElementaryRelationModuleSurjectiveSupply_of_modTwoRelationBasis
    (hB : UniformModTwoRelationBasisSupply (h := h) (q := q)) :
    UniformElementaryRelationModuleSurjectiveSupply (h := h) (q := q) := by
  intro C _ _ _ _ rho hrho A _ _ _ hA₂
  exact relationModuleRelatorSurjective_of_modTwoRelationBasis
    (hB C rho hrho) hA₂

/-- The strongly-free relation-basis supply gives the continuous H² right-exact/CD2 tail. -/
theorem gammaLH2RightExactSupply_of_modTwoRelationBasis
    (hB : UniformModTwoRelationBasisSupply (h := h) (q := q)) :
    GammaLH2RightExactSupply h q :=
  gammaLH2RightExactSupply_of_relationModule
    (uniformElementaryRelationModuleSurjectiveSupply_of_modTwoRelationBasis hB)

/-- At even `q`, strongly-free coordinates give the full Tate-duality package for the improved
L presentation. -/
noncomputable def tateDualityG_of_modTwoRelationBasis
    (hq : Even q)
    [DistribMulAction GammaL (MuN 2)] [ContinuousSMul GammaL (MuN 2)]
    (hB : UniformModTwoRelationBasisSupply (h := h) (q := q)) :
    TateDualityG GammaL 2 :=
  tateDualityG_of_relationModule hq
    (uniformElementaryRelationModuleSurjectiveSupply_of_modTwoRelationBasis hB)

end UniformSupply

end

end GQ2.Dyadic.LSquare

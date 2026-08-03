/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoFoxStronglyFree
import GQ2.Dyadic.Instances.GammaLRelationBasis

/-!
# Strong freeness for the improved L presentation: the exact remaining boundary

This file states the classical relation-module theorem still needed for the improved two-relator
presentation.  At every finite target, the regular module on the tame and improved L relator
orbits must occur as a split equivariant summand of the explicit quotient `R / (R²[R,R])`.

This is the more explicit classical form of `UniformModTwoRelationBasisSupply`: it includes the
canonical embedding of the regular relator module and proves that the coordinate map is its
retraction.  Because every target marking here is generating, the generic theory proves the two
existence statements equivalent.  Either form then feeds the existing relation-module, H², and
Tate-duality pipeline unchanged.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.Certificates.LSqStokes

section UniformSupply

variable {h q : ℕ}

local notation "GammaL" => (gamma h q : Type)

/-- The coefficient-independent, literature-shaped strong-freeness statement for the improved
L presentation.  It asserts that, at every surjective finite target, the two displayed relator
orbits form a split regular summand in the elementary relation module. -/
noncomputable abbrev UniformStronglyFreeModTwoRelatorSummandSupply : Type _ :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom GammaL C), Function.Surjective rho →
      StronglyFreeModTwoRelatorSummand
        (m := fun i => rho (gammaGen (2 * h + 1) q (Words.LSq.lSqW h) i))
        (lSqFam h q (omega2Exp (4 * Monoid.exponent C)))
        (lUniform_rel_death rho)

/-- A uniform equivariant retraction of the universal Fox matrices gives the explicit
strongly-free split summand for the two improved L relators. -/
noncomputable def uniformStronglyFreeModTwoRelatorSummandSupply_of_foxRetraction
    (hR : UniformModTwoFoxRelationRetractionSupply (h := h) (q := q)) :
    UniformStronglyFreeModTwoRelatorSummandSupply (h := h) (q := q) := by
  intro C _ _ _ _ rho hrho
  have hgen : Subgroup.closure
      (Set.range (fun i => rho
        (gammaGen (2 * h + 1) q (Words.LSq.lSqW h) i))) = ⊤ :=
    closure_range_lower_eq_top rho (fun _ => rfl)
      (isAdmissibleMarkedPresentation_gammaR
        (2 * h + 1) q (Words.LSq.lSqW h)) hrho
  have heval : Function.Surjective
      (FreeGroup.lift (fun i => rho
        (gammaGen (2 * h + 1) q (Words.LSq.lSqW h) i))) :=
    freeGroup_lift_surjective_of_closure hgen
  exact (hR C rho hrho).toStronglyFreeModTwoRelatorSummand
    (lUniform_rel_death rho) heval

/-- A uniform strongly-free split summand constructs the exact coordinate supply isolated by
the previous reduction. -/
noncomputable def uniformModTwoRelationBasisSupply_of_stronglyFreeSummand
    (hSF : UniformStronglyFreeModTwoRelatorSummandSupply (h := h) (q := q)) :
    UniformModTwoRelationBasisSupply (h := h) (q := q) := by
  intro C _ _ _ _ rho hrho
  exact (hSF C rho hrho).toModTwoRelationBasisCoordinates

/-- The classical strongly-free summand theorem implies the uniform relation-character
realization statement for all elementary coefficient modules. -/
theorem uniformElementaryRelationModuleSurjectiveSupply_of_stronglyFreeSummand
    (hSF : UniformStronglyFreeModTwoRelatorSummandSupply (h := h) (q := q)) :
    UniformElementaryRelationModuleSurjectiveSupply (h := h) (q := q) :=
  uniformElementaryRelationModuleSurjectiveSupply_of_modTwoRelationBasis
    (uniformModTwoRelationBasisSupply_of_stronglyFreeSummand hSF)

/-- The classical strongly-free summand theorem gives the continuous H² right-exact/CD2
tail for the improved L presentation. -/
theorem gammaLH2RightExactSupply_of_stronglyFreeSummand
    (hSF : UniformStronglyFreeModTwoRelatorSummandSupply (h := h) (q := q)) :
    GammaLH2RightExactSupply h q :=
  gammaLH2RightExactSupply_of_modTwoRelationBasis
    (uniformModTwoRelationBasisSupply_of_stronglyFreeSummand hSF)

/-- At even `q`, the classical strongly-free summand theorem gives the full Tate-duality
package for the improved L presentation. -/
noncomputable def tateDualityG_of_stronglyFreeSummand
    (hq : Even q)
    [DistribMulAction GammaL (MuN 2)] [ContinuousSMul GammaL (MuN 2)]
    (hSF : UniformStronglyFreeModTwoRelatorSummandSupply (h := h) (q := q)) :
    TateDualityG GammaL 2 :=
  tateDualityG_of_modTwoRelationBasis hq
    (uniformModTwoRelationBasisSupply_of_stronglyFreeSummand hSF)

end UniformSupply

end

end GQ2.Dyadic.LSquare

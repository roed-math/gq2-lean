/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoFoxCounterexample
import GQ2.Dyadic.Instances.GammaLRelationBasis
import GQ2.Dyadic.Instances.GammaLStronglyFree

/-!
# Exact uniform relation-coordinate supplies for the improved L presentation are empty

The trivial finite quotient is already a counterexample.  Its universal Fox matrix is the
mod-two exponent matrix.  The existing Stokes endpoint theorem says that the two columns of
this matrix sum to zero, and hence coincide.  Therefore the matrix has no left inverse.

At the trivial target the relation kernel is the whole free group.  Thus every elementary
relation character factors through mod-two abelianization and must also take equal values on
the two relators.  Consequently the proposed exact relation-character, coordinate, and split
summand supplies fail as well.

This does not contradict the known `Q₂` relation-realization or Tate-duality theorems.  Cocycle
relator realization is only required modulo `heisD1.range`; at the trivial target that quotient
kills the common diagonal relation which obstructs exact independent coordinates.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.Certificates.LSqStokes

variable {h q : ℕ}

local notation "GammaL" => (gamma h q : Type)

/-- For even `q`, the proposed uniform Fox-retraction supply is false: its instance at the
trivial finite quotient cannot exist. -/
theorem not_nonempty_uniformModTwoFoxRelationRetractionSupply
    (hq : Even q) :
    ¬ Nonempty (UniformModTwoFoxRelationRetractionSupply (h := h) (q := q)) := by
  rintro ⟨S⟩
  let rho : ContinuousMonoidHom GammaL PUnit.{1} :=
    { toFun := fun _ => 1
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      continuous_toFun := continuous_const }
  have hrho : Function.Surjective rho := fun y => ⟨1, Subsingleton.elim _ y⟩
  have R := S PUnit.{1} rho hrho
  have he : Odd (omega2Exp (4 * Monoid.exponent PUnit.{1})) :=
    odd_omega2Exp (fourMulExponent_ne_zero_and_even PUnit.{1}).1
      (fourMulExponent_ne_zero_and_even PUnit.{1}).2
  have hend : IsStokesEndpoint
      (lSqFam h q (omega2Exp (4 * Monoid.exponent PUnit.{1}))) :=
    lSq_isStokesEndpoint hq he
  apply not_nonempty_modTwoFoxRelationRetraction_punit hend
  refine ⟨?_⟩
  simpa [rho] using R

/-- For even `q`, exact arbitrary elementary relation-character values on the two relators
cannot be supplied uniformly: the requested values `(0,1)` already fail at the trivial target
with coefficients `ZMod 2`. -/
theorem not_uniformElementaryRelationModuleSurjectiveSupply
    (hq : Even q) :
    ¬ UniformElementaryRelationModuleSurjectiveSupply (h := h) (q := q) := by
  intro S
  let rho : ContinuousMonoidHom GammaL PUnit.{1} :=
    { toFun := fun _ => 1
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      continuous_toFun := continuous_const }
  have hrho : Function.Surjective rho := fun y => ⟨1, Subsingleton.elim _ y⟩
  have hRM := S PUnit.{1} rho hrho (ZMod 2)
    (fun x : ZMod 2 => CharTwo.add_self_eq_zero x)
  have he : Odd (omega2Exp (4 * Monoid.exponent PUnit.{1})) :=
    odd_omega2Exp (fourMulExponent_ne_zero_and_even PUnit.{1}).1
      (fourMulExponent_ne_zero_and_even PUnit.{1}).2
  have hend : IsStokesEndpoint
      (lSqFam h q (omega2Exp (4 * Monoid.exponent PUnit.{1}))) :=
    lSq_isStokesEndpoint hq he
  have hrel : ∀ k, FreeGroup.lift
      (fun _ : Generator (2 * h + 1) => (1 : PUnit))
      (lSqFam h q (omega2Exp (4 * Monoid.exponent PUnit.{1})) k) = 1 := by
    simpa [rho] using lUniform_rel_death rho
  apply not_relationModuleRelatorSurjective_punit hend hrel
  simpa [rho] using hRM

/-- Hence the uniform exact mod-two relation-basis coordinate supply is empty. -/
theorem not_nonempty_uniformModTwoRelationBasisSupply
    (hq : Even q) :
    ¬ Nonempty (UniformModTwoRelationBasisSupply (h := h) (q := q)) := by
  rintro ⟨B⟩
  exact not_uniformElementaryRelationModuleSurjectiveSupply hq
    (uniformElementaryRelationModuleSurjectiveSupply_of_modTwoRelationBasis B)

/-- Hence the more explicit uniform strongly-free split-summand supply is empty too. -/
theorem not_nonempty_uniformStronglyFreeModTwoRelatorSummandSupply
    (hq : Even q) :
    ¬ Nonempty
      (UniformStronglyFreeModTwoRelatorSummandSupply (h := h) (q := q)) := by
  rintro ⟨S⟩
  exact not_nonempty_uniformModTwoRelationBasisSupply hq
    ⟨uniformModTwoRelationBasisSupply_of_stronglyFreeSummand S⟩

end

end GQ2.Dyadic.LSquare

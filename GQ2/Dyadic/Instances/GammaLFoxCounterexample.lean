/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoFoxCounterexample
import GQ2.Dyadic.Instances.GammaLRelationBasis

/-!
# The uniform Fox-retraction supply for the improved L presentation is empty

The trivial finite quotient is already a counterexample.  Its universal Fox matrix is the
mod-two exponent matrix.  The existing Stokes endpoint theorem says that the two columns of
this matrix sum to zero, and hence coincide.  Therefore the matrix has no left inverse.

This does not contradict the known `Q₂` relation-realization or Tate-duality theorems.  The Fox
criterion asks for a splitting in the free generator module, strictly before restricting to the
relation kernel; that extra condition is what fails here.
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

end

end GQ2.Dyadic.LSquare

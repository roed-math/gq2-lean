/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoRelationFox

/-!
# The Stokes endpoint obstructs the universal Fox retraction at the trivial target

For a two-relator family, the Stokes endpoint says that the two mod-two exponent vectors
sum to zero.  At the trivial target the universal Fox derivative is exactly this exponent
vector.  Consequently the two columns of the universal Fox relation matrix coincide, so the
matrix is not injective and cannot admit a left inverse.

This obstruction is specific to the universal Fox criterion.  It does not rule out relation
characters or Tate duality: those only require coordinates on the relation kernel, while the
Fox criterion asks the two relator columns to split already inside the free generator module.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.FoxH

section TrivialTarget

variable {I : Type} [DecidableEq I]

/-- At the trivial target, a coordinate of the universal mod-two Fox derivative is the
corresponding mod-two exponent sum. -/
theorem modTwoFoxDerivative_punit_apply (f : FreeGroup I) (i : I) :
    modTwoFoxDerivative (fun _ : I => (1 : PUnit)) f ((1 : PUnit), i) =
      Multiplicative.toAdd (heisEps i f) := by
  let m : I → PUnit := fun _ => 1
  let ker : FreeGroup I →* FreeRelationKernel m :=
    { toFun := fun r => ⟨r, Subsingleton.elim _ _⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let coord : RegularModTwoRelationModule PUnit I →+ ZMod 2 :=
    { toFun := fun c => c ((1 : PUnit), i)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let lhs : FreeGroup I →* Multiplicative (ZMod 2) :=
    (AddMonoidHom.toMultiplicative coord).comp ((modTwoRelationFoxMap m).comp ker)
  have hlhs : lhs = heisEps i := by
    apply FreeGroup.ext_hom
    intro j
    by_cases hji : j = i <;>
      simp [lhs, ker, coord, m, modTwoRelationFoxMap, modTwoFoxGenerator, heisEps, hji]
  have hf := DFunLike.congr_fun hlhs f
  apply Multiplicative.ofAdd.injective
  simpa [lhs, coord, ker, m, modTwoRelationFoxMap] using hf

variable {w : Fin 2 → FreeGroup I}

/-- At the trivial target, the two columns of a two-relator Stokes-endpoint Fox matrix are
equal. -/
theorem modTwoFoxRelationMatrix_punit_basis_zero_eq_one
    (hend : IsStokesEndpoint w) :
    modTwoFoxRelationMatrix (fun _ : I => (1 : PUnit)) w
        (Finsupp.single ((1 : PUnit), (0 : Fin 2)) 1) =
      modTwoFoxRelationMatrix (fun _ : I => (1 : PUnit)) w
        (Finsupp.single ((1 : PUnit), (1 : Fin 2)) 1) := by
  rw [modTwoFoxRelationMatrix_basis, modTwoFoxRelationMatrix_basis]
  ext p
  rcases p with ⟨g, i⟩
  have hg : g = (1 : PUnit) := Subsingleton.elim _ _
  subst g
  rw [modTwoFoxDerivative_punit_apply, modTwoFoxDerivative_punit_apply]
  have hi := hend i
  rw [Fin.sum_univ_two] at hi
  let a := Multiplicative.toAdd (heisEps i (w 0))
  let b := Multiplicative.toAdd (heisEps i (w 1))
  change a + b = 0 at hi
  have hbb : b + b = 0 := CharTwo.add_self_eq_zero b
  calc
    a = a + 0 := (add_zero a).symm
    _ = a + (b + b) := congrArg (a + ·) hbb.symm
    _ = (a + b) + b := (add_assoc a b b).symm
    _ = 0 + b := congrArg (· + b) hi
    _ = b := zero_add b

/-- The universal Fox relation matrix of a two-relator Stokes endpoint is not injective at the
trivial target. -/
theorem not_injective_modTwoFoxRelationMatrix_punit
    (hend : IsStokesEndpoint w) :
    ¬ Function.Injective
      (modTwoFoxRelationMatrix (fun _ : I => (1 : PUnit)) w) := by
  intro hinj
  have heq := hinj (modTwoFoxRelationMatrix_punit_basis_zero_eq_one hend)
  have hcoord := congrArg
    (fun c : RegularModTwoRelationModule PUnit (Fin 2) => c ((1 : PUnit), (0 : Fin 2))) heq
  simpa using hcoord

/-- Hence no equivariant left inverse of the universal Fox relation matrix can exist at the
trivial target. -/
theorem not_nonempty_modTwoFoxRelationRetraction_punit
    (hend : IsStokesEndpoint w) :
    ¬ Nonempty (ModTwoFoxRelationRetraction (fun _ : I => (1 : PUnit)) w) := by
  rintro ⟨R⟩
  exact not_injective_modTwoFoxRelationMatrix_punit hend R.leftInverse.injective

end TrivialTarget

end

end GQ2.Dyadic.Count

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoRelationFox
import GQ2.Dyadic.Count.HTwoStronglyFree

/-!
# The Stokes endpoint obstructs the universal Fox retraction at the trivial target

For a two-relator family, the Stokes endpoint says that the two mod-two exponent vectors
sum to zero.  At the trivial target the universal Fox derivative is exactly this exponent
vector.  Consequently the two columns of the universal Fox relation matrix coincide, so the
matrix is not injective and cannot admit a left inverse.

At the trivial target the relation kernel is the entire free group, so the same parity
calculation also rules out *exact* arbitrary relation-character coordinates on the two
relators.  It does not rule out Tate duality, or cocycle relator realization modulo the image
of the word differential: those quotient-valued statements can kill the common diagonal
relation that obstructs exact coordinates.
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

/-- At the trivial target, every elementary relation character takes the same value on the two
relators of a Stokes endpoint.  Unlike the Fox obstruction, this is an obstruction intrinsic to
the relation kernel: at the trivial target that kernel is the entire free group. -/
theorem FreeRelationCharacter.val_zero_eq_val_one_of_stokesEndpoint_punit
    (hend : IsStokesEndpoint w)
    (chi : FreeRelationCharacter (fun _ : I => (1 : PUnit)) (ZMod 2)) :
    chi.val ⟨w 0, Subsingleton.elim _ _⟩ =
      chi.val ⟨w 1, Subsingleton.elim _ _⟩ := by
  let m : I → PUnit := fun _ => 1
  let ker : FreeGroup I →* FreeRelationKernel m :=
    { toFun := fun r => ⟨r, Subsingleton.elim _ _⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let chiHom : FreeGroup I →* Multiplicative (ZMod 2) := chi.toMonoidHom.comp ker
  let a : I → ZMod 2 := fun i => Multiplicative.toAdd (chiHom (FreeGroup.of i))
  let foxHom : FreeGroup I →* Multiplicative (ZMod 2) :=
    { toFun := fun f => Multiplicative.ofAdd (FreeGroup.lift (foxLift m a) f).u
      map_one' := by simp
      map_mul' := by
        intro f g
        simp only [map_mul, WordLift.mul_u]
        have hone : (FreeGroup.lift (foxLift m a) f).g = (1 : PUnit) :=
          Subsingleton.elim _ _
        rw [hone, one_smul, ofAdd_add] }
  have hfox : foxHom = chiHom := by
    apply FreeGroup.ext_hom
    intro i
    simp [foxHom, chiHom, ker, a, m, foxLift]
  have hderiv :
      modTwoFoxDerivative m (w 0) = modTwoFoxDerivative m (w 1) := by
    have h := modTwoFoxRelationMatrix_punit_basis_zero_eq_one hend
    rw [modTwoFoxRelationMatrix_basis, modTwoFoxRelationMatrix_basis] at h
    exact h
  have heval := congrArg
    (regularModTwoRelationEval
      (fun x : ZMod 2 => CharTwo.add_self_eq_zero x) a) hderiv
  rw [regularModTwoRelationEval_modTwoFoxDerivative,
    regularModTwoRelationEval_modTwoFoxDerivative] at heval
  have hfoxValues : foxHom (w 0) = foxHom (w 1) := congrArg Multiplicative.ofAdd heval
  rw [hfox] at hfoxValues
  exact congrArg Multiplicative.toAdd hfoxValues

/-- Consequently exact relation-character evaluation on the two relators is not surjective at
the trivial target: the requested vector `(0,1)` cannot be realized. -/
theorem not_relationModuleRelatorSurjective_punit
    (hend : IsStokesEndpoint w)
    (hrel : ∀ k, FreeGroup.lift (fun _ : I => (1 : PUnit)) (w k) = 1) :
    ¬ RelationModuleRelatorSurjective (A := ZMod 2) w hrel := by
  intro hsurj
  let r : Fin 2 → ZMod 2 := ![0, 1]
  obtain ⟨chi, hchi⟩ := hsurj r
  have heq :=
    FreeRelationCharacter.val_zero_eq_val_one_of_stokesEndpoint_punit hend chi
  rw [hchi 0, hchi 1] at heq
  exact zero_ne_one heq

/-- A Stokes endpoint therefore cannot admit relation-basis coordinates at the trivial target. -/
theorem not_nonempty_modTwoRelationBasisCoordinates_punit
    (hend : IsStokesEndpoint w)
    (hrel : ∀ k, FreeGroup.lift (fun _ : I => (1 : PUnit)) (w k) = 1) :
    ¬ Nonempty (ModTwoRelationBasisCoordinates w hrel) := by
  rintro ⟨B⟩
  exact not_relationModuleRelatorSurjective_punit hend hrel
    (relationModuleRelatorSurjective_of_modTwoRelationBasis B
      (fun x : ZMod 2 => CharTwo.add_self_eq_zero x))

/-- Nor can the two relator orbits form a split strongly-free summand at the trivial target. -/
theorem not_nonempty_stronglyFreeModTwoRelatorSummand_punit
    (hend : IsStokesEndpoint w)
    (hrel : ∀ k, FreeGroup.lift (fun _ : I => (1 : PUnit)) (w k) = 1) :
    ¬ Nonempty (StronglyFreeModTwoRelatorSummand w hrel) := by
  rintro ⟨B⟩
  exact not_nonempty_modTwoRelationBasisCoordinates_punit hend hrel
    ⟨B.toModTwoRelationBasisCoordinates⟩

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

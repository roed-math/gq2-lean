/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Certificates.L
import GQ2.Dyadic.Count.HTwoRelationFox

/-!
# The tame `L_sq` Fox row at the trivial target

The first resolved relator in `lSqFam h q e` is the tame word
`tau^sigma * (tau^q)^-1`.  At a one-element target its universal mod-two Fox derivative is
the single regular-module basis vector in the `tau` column whenever `q` is even.  In
particular, this row does not depend on the resolver `e`.

The proof transports the existing word-level calculation `foxD_tameRelW_unram` across
`evalZ_eq_lift_heisToFree`; no Fox formula is recomputed here.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.FoxH GQ2.Dyadic
open GQ2.Dyadic.Certificates
open GQ2.Dyadic.Certificates.LSqStokes

/-- At any finite subsingleton group, the tame row of `lSqFam` is exactly the `tau` basis
vector.  This is the reusable form; the concrete `Unit` and `PUnit` statements below are
immediate specializations. -/
theorem modTwoFoxDerivative_lSqFam_zero_of_subsingleton
    {h q e : ℕ} {C : Type} [Group C] [Finite C] [Subsingleton C]
    (hq : Even q) :
    modTwoFoxDerivative
        (fun _ : Generator (2 * h + 1) ↦ (1 : C))
        (lSqFam h q e 0) =
      (Finsupp.single
        ((1 : C), Generator.tau (n := 2 * h + 1)) (1 : ZMod 2) :
          RegularModTwoRelationModule C (Generator (2 * h + 1))) := by
  letI := Fintype.ofFinite C
  let m : Generator (2 * h + 1) → C := fun _ ↦ 1
  let a : Generator (2 * h + 1) →
      RegularModTwoRelationModule C (Generator (2 * h + 1)) :=
    modTwoFoxGenerator
  let t : Marking (2 * h + 1) C := ⟨m⟩
  change (FreeGroup.lift (foxLift m a) (lSqFam h q e 0)).u = _
  rw [lSqFam_zero, ← evalZ_eq_lift_heisToFree]
  have heval :
      PWord.evalZ (foxLift m a) (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ))
          (tameRelW (2 * h + 1) q) =
        PWord.evalFin (foxLift m a) (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ))
          (tameRelW (2 * h + 1) q) := by
    simp [tameRelW]
  rw [heval]
  change foxD ⇑t a (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ))
      (tameRelW (2 * h + 1) q) = _
  rw [foxD_tameRelW_unram t (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ))
    (fun v ↦ regularModTwoRelationModule_add_self C _ v)
    (by intro v; rw [Subsingleton.elim t.τ 1, one_smul]) hq]
  rw [Subsingleton.elim t.σ 1, inv_one, one_smul]
  rfl

/-- Concrete singleton-target form using `Unit`. -/
theorem modTwoFoxDerivative_lSqFam_zero_unit
    {h q e : ℕ} (hq : Even q) :
    modTwoFoxDerivative
        (fun _ : Generator (2 * h + 1) ↦ (1 : Unit))
        (lSqFam h q e 0) =
      (Finsupp.single
        ((1 : Unit), Generator.tau (n := 2 * h + 1)) (1 : ZMod 2) :
          RegularModTwoRelationModule Unit (Generator (2 * h + 1))) :=
  modTwoFoxDerivative_lSqFam_zero_of_subsingleton hq

/-- Concrete singleton-target form using `PUnit`, in the spelling used by the relation-module
counterexample. -/
theorem modTwoFoxDerivative_lSqFam_zero_punit
    {h q e : ℕ} (hq : Even q) :
    modTwoFoxDerivative
        (fun _ : Generator (2 * h + 1) ↦ PUnit.unit)
        (lSqFam h q e 0) =
      (Finsupp.single
        (PUnit.unit, Generator.tau (n := 2 * h + 1)) (1 : ZMod 2) :
          RegularModTwoRelationModule PUnit (Generator (2 * h + 1))) :=
  modTwoFoxDerivative_lSqFam_zero_of_subsingleton hq

end
end GQ2.Dyadic.Count

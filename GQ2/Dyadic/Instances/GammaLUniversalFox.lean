/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoRelationFox
import GQ2.Dyadic.Instances.LScalarTrace

/-!
# The improved L Fox row at the trivial target

At the trivial finite target the regular mod-two generator module is just the mod-two exponent
module.  The improved L relator has exponent vector supported only at `tau`, with coefficient
one for every odd resolver.  Thus its universal Fox row is the standard `tau` basis vector.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.Words GQ2.Dyadic.Words.LSq
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes

section TrivialFox

variable {I : Type} [DecidableEq I]

/-- Evaluation at the scalar delta function extracts the corresponding coordinate of the
regular module over the trivial group. -/
theorem regularModTwoRelationEval_piSingle_unit
    (i : I) (c : RegularModTwoRelationModule Unit I) :
    regularModTwoRelationEval (L := Unit)
        (fun a : ZMod 2 => CharTwo.add_self_eq_zero a) (Pi.single i 1) c =
      c (1, i) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨⟨⟩, j⟩
      rw [map_add, regularModTwoRelationEval_single, ih, Finsupp.add_apply,
        Finsupp.single_apply]
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]

variable [Fintype I]

/-- At the trivial target, the universal mod-two Fox derivative is the mod-two exponent vector. -/
theorem modTwoFoxDerivative_unit_apply_eq_heisEps
    (f : FreeGroup I) (i : I) :
    modTwoFoxDerivative (fun _ : I => (1 : Unit)) f (1, i) =
      Multiplicative.toAdd (heisEps i f) := by
  classical
  let a : I → ZMod 2 := Pi.single i 1
  let w : Unit → FreeGroup I := fun _ => f
  calc
    modTwoFoxDerivative (fun _ : I => (1 : Unit)) f (1, i) =
        regularModTwoRelationEval (L := Unit)
          (fun z : ZMod 2 => CharTwo.add_self_eq_zero z) a
          (modTwoFoxDerivative (fun _ : I => (1 : Unit)) f) :=
      (regularModTwoRelationEval_piSingle_unit i _).symm
    _ = (FreeGroup.lift (foxLift (fun _ : I => (1 : Unit)) a) f).u :=
      regularModTwoRelationEval_modTwoFoxDerivative
        (fun z : ZMod 2 => CharTwo.add_self_eq_zero z)
        (fun _ : I => (1 : Unit)) a f
    _ = heisD1 (A := ZMod 2) (fun _ : I => (1 : Unit)) w a 1 :=
      (heisD1_eq_lift_foxLift_u (fun _ : I => (1 : Unit)) w a 1).symm
    _ = Multiplicative.toAdd (heisEps i f) := by
      rw [heisD1_zmod2_apply_eq_eps, Finset.sum_eq_single i]
      · simp [a, w]
      · intro j _ hji
        simp [a, hji]
      · simp

variable {h q e : ℕ}

/-- The mod-two exponent vector of the resolved improved L relator: every odd resolver leaves
exactly the `tau` coordinate. -/
theorem lSqFam_one_heisEps_eq_tau (he : Odd e)
    (i : Generator (2 * h + 1)) :
    Multiplicative.toAdd (heisEps i (lSqFam h q e 1)) =
      if i = Generator.tau then 1 else 0 := by
  have hform :
      heisEps i (lSqFam h q e 1) =
        (heisEps i (FreeGroup.of (coreLetter h 0)))⁻¹ *
          ((heisEps i (FreeGroup.of (coreLetter h 0)) ^ (-3 : ℤ) *
              heisEps i (FreeGroup.of Generator.tau)) ^ (e : ℤ) *
            heisEps i (FreeGroup.of (coreLetter h 1)) ^ (2 : ℤ)) := by
    rw [lSqFam_one, heisToFree, evalZ_lSqW]
    simp only [lSqCore, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [map_mul, heisEps_lSqHandles, mul_one, map_mul, map_mul, map_mul,
      PWord.evalZ_inv, PWord.evalZ_conj, PWord.evalZ_gen, PWord.evalZ_gen, map_inv,
      map_conjR, conjR_eq_self_of_comm, PWord.omega2Pow, PWord.evalZ_profPow, map_zpow,
      PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, PWord.evalZ_mul,
      PWord.evalZ_mul, PWord.evalZ_zpow, PWord.evalZ_gen, PWord.evalZ_gen,
      PWord.evalZ_one, mul_one, map_mul, map_zpow, PWord.evalZ_zpow,
      PWord.evalZ_gen, map_zpow, PWord.evalZ_comm, monoidHom_commR_eq_one, mul_one]
  rw [hform]
  have hez : Odd (e : ℤ) := by exact_mod_cast he
  simp only [toAdd_mul, toAdd_inv, toAdd_zpow]
  rw [zsmul_zmod2_odd hez]
  simp only [heisEps, FreeGroup.lift_apply_of, toAdd_ofAdd]
  by_cases hiτ : i = Generator.tau
  · subst i
    simp [LSq.coreLetter]
  · have hτi : (Generator.tau : Generator (2 * h + 1)) ≠ i := Ne.symm hiτ
    rw [if_neg hiτ]
    simp only [if_neg hτi]
    ring_nf
    split_ifs <;> decide

/-- The universal mod-two Fox derivative of the improved L relator at the trivial target is the
standard regular basis vector at `tau`. -/
theorem modTwoFoxDerivative_lSqFam_one_unit
    (he : Odd e) :
    modTwoFoxDerivative
        (fun _ : Generator (2 * h + 1) => (1 : Unit))
        (lSqFam h q e 1) =
      Finsupp.single ((1 : Unit), Generator.tau) (1 : ZMod 2) := by
  classical
  ext p
  rcases p with ⟨⟨⟩, i⟩
  rw [modTwoFoxDerivative_unit_apply_eq_heisEps,
    lSqFam_one_heisEps_eq_tau he]
  by_cases hi : i = Generator.tau
  · subst i
    simp
  · simp [hi]

end TrivialFox

end

end GQ2.Dyadic.LSquare

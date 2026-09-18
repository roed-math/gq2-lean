/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.SigmaNormalKernelTransport

/-!
# Explicit row elimination from normalized Fox coefficients

This gives an operator-valued matrix certificate, uniform in the wild alphabet. If the
tame row is `U x_tau`, the sigma column vanishes, and the second row on sigma=tau=0 is
`D x_j`, the actual matrix is `[U,0; L,D]` on the tau and selected wild columns. Here L is
the actual tau column of the supplied differential, not an unspecified existence witness.

The three row operations are: invert U on the first row; subtract L times that new row
from the second row; invert D on the second row. Their inverse is displayed explicitly.
No equality of the two full differentials is inferred merely from equality of kernels.
-/

namespace GQ2.Dyadic.SigmaNormalFoxElimination
noncomputable section
open GQ2 GQ2.Dyadic

variable {A : Type*} [AddCommGroup A]

/-- Explicit invertible row operations for the lower triangular operator matrix. -/
def rowElimination (U D : A ≃+ A) (L : A →+ A) : (Fin 2 → A) ≃+ (Fin 2 → A) where
  toFun z := ![U.symm (z 0), D.symm (z 1 - L (U.symm (z 0)))]
  invFun z := ![U (z 0), L (z 0) + D (z 1)]
  left_inv z := by
    funext i
    fin_cases i <;> simp
  right_inv z := by
    funext i
    fin_cases i <;> simp
  map_add' x y := by
    funext i
    fin_cases i
    · simp
    · change D.symm (x 1 + y 1 - L (U.symm (x 0 + y 0))) =
        D.symm (x 1 - L (U.symm (x 0))) + D.symm (y 1 - L (U.symm (y 0)))
      simp only [map_add, map_sub]
      abel

@[simp] theorem rowElimination_rows (U D : A ≃+ A) (L : A →+ A) (a b : A) :
    rowElimination U D L ![U a, L a + D b] = ![a, b] := by
  funext i
  fin_cases i <;> simp [rowElimination]

variable {n : ℕ}

/-- The actual second-row tau coefficient of a Fox differential. -/
def tauColumn (d : (Generator n → A) →+ (Fin 2 → A)) : A →+ A where
  toFun a := d (Pi.single .tau a) 1
  map_zero' := by simp
  map_add' a b := by simp [Pi.single_add]

/-- A normalized row identity determines every entry once the sigma column is known to vanish.
The tau coefficient is read from the original differential and is retained literally. -/
theorem full_rows_of_normal
    (d : (Generator n → A) →+ (Fin 2 → A)) (U D : A ≃+ A) (j : Fin (n+1))
    (hfirst : ∀ x, d x 0 = U (x .tau))
    (hsigma : ∀ a, d (Pi.single .sigma a) = 0)
    (hnormal : ∀ x, x .sigma = 0 → x .tau = 0 → d x 1 = D (x (.wild j)))
    (x : Generator n → A) :
    d x = ![U (x .tau), tauColumn d (x .tau) + D (x (.wild j))] := by
  let y := x - Pi.single .sigma (x .sigma) - Pi.single .tau (x .tau)
  have hys : y .sigma = 0 := by simp [y]
  have hyt : y .tau = 0 := by simp [y]
  have hyj : y (.wild j) = x (.wild j) := by simp [y]
  have hy := hnormal y hys hyt
  rw [hyj] at hy
  have hsecond : d x 1 = tauColumn d (x .tau) + D (x (.wild j)) := by
    change (d (x - Pi.single .sigma (x .sigma) - Pi.single .tau (x .tau))) 1 = _ at hy
    rw [map_sub, map_sub, hsigma] at hy
    change d x 1 - 0 - tauColumn d (x .tau) = D (x (.wild j)) at hy
    have hy' : d x 1 - tauColumn d (x .tau) = D (x (.wild j)) := by simpa using hy
    exact (sub_eq_iff_eq_add.mp hy').trans (add_comm _ _)
  funext i
  fin_cases i
  · exact hfirst x
  · exact hsecond

/-- The reduced normal matrix has identity entries in precisely the two pivot columns. -/
theorem reduced_rows_of_normal
    (d : (Generator n → A) →+ (Fin 2 → A)) (U D : A ≃+ A) (j : Fin (n+1))
    (hfirst : ∀ x, d x 0 = U (x .tau))
    (hsigma : ∀ a, d (Pi.single .sigma a) = 0)
    (hnormal : ∀ x, x .sigma = 0 → x .tau = 0 → d x 1 = D (x (.wild j)))
    (x : Generator n → A) :
    rowElimination U D (tauColumn d) (d x) = ![x .tau, x (.wild j)] := by
  rw [full_rows_of_normal d U D j hfirst hsigma hnormal]
  exact rowElimination_rows U D (tauColumn d) _ _

#print axioms rowElimination
#print axioms full_rows_of_normal
#print axioms reduced_rows_of_normal

end
end GQ2.Dyadic.SigmaNormalFoxElimination

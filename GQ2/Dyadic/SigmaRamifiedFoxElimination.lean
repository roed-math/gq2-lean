/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.SigmaNormalFoxRows

/-!
# Explicit ramified Fox column elimination and row scaling

For the actual operator row `[U*x_sigma + L*x_tau, D*x_j]`, subtract `U⁻¹ L*x_tau`
from the sigma column and then scale the two rows by U⁻¹ and D⁻¹. Both operations
are additive equivalences with displayed inverses. The result has identity pivots
at sigma and the selected wild column, with all other entries zero.

The ramified specialization uses U=S⁻¹(T-1), D=-S⁻¹, L=S⁻¹-N_q(T). Only the
first pivot uses finiteness and fixed-point-freeness of T. No source-certificate
premise or ledger-acceptance contract is changed by this additive artifact.
-/

namespace GQ2.Dyadic.SigmaRamifiedFoxElimination
noncomputable section
open GQ2 GQ2.FoxH GQ2.Dyadic
open SigmaNormalFoxElimination

variable {A : Type*} [AddCommGroup A] {n : ℕ}

/-- The elementary domain shear; its inverse adds the same tau-dependent term. -/
def columnShear (U : A ≃+ A) (L : A →+ A) :
    (Generator n → A) ≃+ (Generator n → A) where
  toFun x
    | .sigma => x .sigma - U.symm (L (x .tau))
    | .tau => x .tau
    | .wild i => x (.wild i)
  invFun x
    | .sigma => x .sigma + U.symm (L (x .tau))
    | .tau => x .tau
    | .wild i => x (.wild i)
  left_inv x := by funext g; cases g <;> simp
  right_inv x := by funext g; cases g <;> simp
  map_add' x y := by
    funext g
    cases g with
    | sigma =>
        change x .sigma + y .sigma - U.symm (L (x .tau + y .tau)) =
          (x .sigma - U.symm (L (x .tau))) + (y .sigma - U.symm (L (y .tau)))
        simp only [map_add]
        abel
    | tau => rfl
    | wild i => rfl

@[simp] theorem columnShear_sigma (U : A ≃+ A) (L : A →+ A) (x : Generator n → A) :
    columnShear U L x .sigma = x .sigma - U.symm (L (x .tau)) := rfl
@[simp] theorem columnShear_tau (U : A ≃+ A) (L : A →+ A) (x : Generator n → A) :
    columnShear U L x .tau = x .tau := rfl
@[simp] theorem columnShear_wild (U : A ≃+ A) (L : A →+ A) (x : Generator n → A)
    (i : Fin (n+1)) : columnShear U L x (.wild i) = x (.wild i) := rfl
@[simp] theorem columnShear_symm_sigma (U : A ≃+ A) (L : A →+ A) (x : Generator n → A) :
    (columnShear U L).symm x .sigma = x .sigma + U.symm (L (x .tau)) := rfl

/-- Diagonal row scaling with inverse multiplication by the original pivots. -/
def rowScaling (U D : A ≃+ A) : (Fin 2 → A) ≃+ (Fin 2 → A) where
  toFun z := ![U.symm (z 0), D.symm (z 1)]
  invFun z := ![U (z 0), D (z 1)]
  left_inv z := by funext i; fin_cases i <;> simp
  right_inv z := by funext i; fin_cases i <;> simp
  map_add' x y := by funext i; fin_cases i <;> simp

@[simp] theorem rowScaling_rows (U D : A ≃+ A) (a b : A) :
    rowScaling U D ![U a, D b] = ![a, b] := by
  funext i
  fin_cases i <;> simp [rowScaling]

/-- The complete ramified elimination identity, on all cochains rather than just cocycles. -/
theorem reduced_rows_of_ramified
    (d : (Generator n → A) →+ (Fin 2 → A)) (U D : A ≃+ A) (L : A →+ A)
    (j : Fin (n+1))
    (hrow : ∀ x, d x = ![U (x .sigma) + L (x .tau), D (x (.wild j))])
    (x : Generator n → A) :
    rowScaling U D (d (columnShear U L x)) = ![x .sigma, x (.wild j)] := by
  rw [hrow]
  simp only [columnShear_sigma, columnShear_tau, columnShear_wild,
    map_sub, AddEquiv.apply_symm_apply, sub_add_cancel]
  exact rowScaling_rows U D _ _

/-- Kernel identification in the explicitly transformed coordinates. -/
theorem kernel_columnShear_iff
    (d : (Generator n → A) →+ (Fin 2 → A)) (U D : A ≃+ A) (L : A →+ A)
    (j : Fin (n+1))
    (hrow : ∀ x, d x = ![U (x .sigma) + L (x .tau), D (x (.wild j))])
    (x : Generator n → A) :
    d (columnShear U L x) = 0 ↔ x .sigma = 0 ∧ x (.wild j) = 0 := by
  have heq := reduced_rows_of_ramified d U D L j hrow x
  constructor
  · intro hx
    rw [hx, map_zero] at heq
    exact ⟨(congrFun heq 0).symm, (congrFun heq 1).symm⟩
  · rintro ⟨hs, hj⟩
    apply (rowScaling U D).injective
    rw [map_zero, heq, hs, hj]
    funext i
    fin_cases i <;> rfl

variable {C : Type*} [Group C] [DistribMulAction C A]

/-- T-1 is invertible on a finite fixed-point-free coefficient group. -/
def tauSubOne [Finite A] (tau : C)
    (hfpf : ∀ a : A, tau • a = a → a = 0) : A ≃+ A := by
  let d : A →+ A := (actionEquiv (A := A) tau).toAddMonoidHom - AddMonoidHom.id A
  have hs : Function.Surjective d := surjective_smul_sub_of_fixedPointFree hfpf
  exact AddEquiv.ofBijective d ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

@[simp] theorem tauSubOne_apply [Finite A] (tau : C)
    (hfpf : ∀ a : A, tau • a = a → a = 0) (a : A) :
    tauSubOne tau hfpf a = tau • a - a := rfl

/-- U=S⁻¹(T-1), with inverse `(T-1)⁻¹ S`. -/
def sigmaPivot [Finite A] (sigma tau : C)
    (hfpf : ∀ a : A, tau • a = a → a = 0) : A ≃+ A :=
  (tauSubOne tau hfpf).trans (actionEquiv sigma⁻¹)

@[simp] theorem sigmaPivot_apply [Finite A] (sigma tau : C)
    (hfpf : ∀ a : A, tau • a = a → a = 0) (a : A) :
    sigmaPivot sigma tau hfpf a = sigma⁻¹ • (tau • a - a) := rfl

theorem sigmaPivot_symm_apply [Finite A] (sigma tau : C)
    (hfpf : ∀ a : A, tau • a = a → a = 0) (a : A) :
    (sigmaPivot sigma tau hfpf).symm a = (tauSubOne tau hfpf).symm (sigma • a) := by
  simp [sigmaPivot, actionEquiv]

/-- D=-S⁻¹, with the explicit inverse -S. -/
def wildPivot (sigma : C) : A ≃+ A :=
  (actionEquiv (A := A) sigma⁻¹).trans (AddEquiv.neg A)

@[simp] theorem wildPivot_apply (sigma : C) (a : A) :
    wildPivot sigma a = -(sigma⁻¹ • a) := rfl

theorem wildPivot_symm_apply (sigma : C) (a : A) :
    (wildPivot sigma).symm a = -(sigma • a) := by
  simp [wildPivot, actionEquiv]

/-- The actual tau coefficient L=S⁻¹-N_q(T), including the complete tame norm sum. -/
def tauCoefficient (sigma tau : C) (q : ℕ) : A →+ A where
  toFun a := sigma⁻¹ • a - ∑ i ∈ Finset.range q, (tau ^ i) • a
  map_zero' := by simp
  map_add' a b := by simp only [smul_add, Finset.sum_add_distrib]; abel

@[simp] theorem tauCoefficient_apply (sigma tau : C) (q : ℕ) (a : A) :
    tauCoefficient sigma tau q a = sigma⁻¹ • a - ∑ i ∈ Finset.range q, (tau ^ i) • a := rfl

/-- Conversion from the literal tame/compact row to its U,L,D operator blocks. -/
theorem ramified_row_operators [Finite A]
    (t : Marking n C) (q : ℕ) (j : Fin (n+1))
    (hfpf : ∀ a : A, t.τ • a = a → a = 0) (x : Generator n → A) :
    ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
        - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
      -(t.σ⁻¹ • x (.wild j))] =
    ![sigmaPivot t.σ t.τ hfpf (x .sigma) + tauCoefficient t.σ t.τ q (x .tau),
      wildPivot t.σ (x (.wild j))] := by
  funext i
  fin_cases i
  · change t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
        - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau =
      sigmaPivot t.σ t.τ hfpf (x .sigma) + tauCoefficient t.σ t.τ q (x .tau)
    simp only [sigmaPivot_apply, tauCoefficient_apply, smul_add, smul_sub]
    abel
  · rfl

/-- Explicit action-valued elimination for any differential with the shared ramified row. -/
theorem reduced_rows_of_action_row [Finite A]
    (t : Marking n C) (q : ℕ) (j : Fin (n+1))
    (hfpf : ∀ a : A, t.τ • a = a → a = 0)
    (d : (Generator n → A) →+ (Fin 2 → A))
    (hrow : ∀ x, d x =
      ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
          - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
        -(t.σ⁻¹ • x (.wild j))])
    (x : Generator n → A) :
    rowScaling (sigmaPivot t.σ t.τ hfpf) (wildPivot t.σ)
      (d (columnShear (sigmaPivot t.σ t.τ hfpf) (tauCoefficient t.σ t.τ q) x)) =
      ![x .sigma, x (.wild j)] :=
  reduced_rows_of_ramified d _ _ _ j
    (fun y => (hrow y).trans (ramified_row_operators t q j hfpf y)) x

#print axioms columnShear
#print axioms rowScaling
#print axioms reduced_rows_of_ramified
#print axioms kernel_columnShear_iff
#print axioms tauSubOne
#print axioms sigmaPivot
#print axioms sigmaPivot_symm_apply
#print axioms wildPivot_symm_apply
#print axioms tauCoefficient
#print axioms reduced_rows_of_action_row

end
end GQ2.Dyadic.SigmaRamifiedFoxElimination

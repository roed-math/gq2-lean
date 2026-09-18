import GQ2.Dyadic.MarkedCore.N

/-!
# Weak N scaling and the obstruction to a naive handle-scaling realization

The weak sigma-row scaling already follows from the exact SL2 action, with no
peripheral axiom. The stronger plane predicate fixes every other character row.
A candidate scaling a genuine handle row by a nontrivial unit therefore cannot
realize any such plane matrix. This does not refute existence of another candidate.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative

/-- Weak N row scaling is an exact determinant-one plane move: the partner row
may scale inversely because this weaker predicate does not constrain it. -/
theorem nScalingHypothesis_of_sl2 (alpha h : ℕ) : NScalingHypothesis alpha h := by
  intro kappa
  have hdet : (planeDiag kappa).det = 1 := by
    rw [planeDiag, Matrix.det_fin_two]
    norm_num [← Units.val_mul]
  obtain ⟨Psi, hchi, hframe⟩ := nCorePlane_sl2_lift alpha h hdet
  refine ⟨Psi, hchi, fun f => ?_⟩
  have hrow := congrFun (hframe f) 2
  simpa [nuFrame_apply, nCoreMat_two, planeDiag, smul_eq_mul,
    show dnSigma alpha h = dnGen alpha h 2 from rfl] using hrow

/-- A continuous coordinate character at any handle-U slot, at every rank
where that slot exists. The N relator dies because its x0 coordinate is zero. -/
def nHandleUCharacter (alpha h : ℕ) (j : Fin h) :
    ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]) :=
  nLiftHom alpha h PropOneOne.isProP_two_multPadicInt
    (fun i => if i = handleIdxU j then ofAdd (1 : ℤ_[2]) else 1) (by
      rw [nRelWord_comm]
      have hj : (0 : Fin (coreRank h)) ≠ handleIdxU j :=
        (handleIdxU_ne_of_val_lt j (by rw [coreVal_zero]; omega)).symm
      simp [hj])

@[simp] theorem nHandleUCharacter_gen (alpha h : ℕ) (j : Fin h)
    (i : Fin (coreRank h)) :
    nHandleUCharacter alpha h j (dnGen alpha h i) =
      if i = handleIdxU j then ofAdd (1 : ℤ_[2]) else 1 := by
  exact nLiftHom_gen _ _ _ _ _ _

@[simp] theorem nHandleUCharacter_self (alpha h : ℕ) (j : Fin h) :
    toAdd (nHandleUCharacter alpha h j (dnGen alpha h (handleIdxU j))) = 1 := by
  simp

/-- Every plane realization leaves all handle character rows fixed, regardless
of the chosen plane matrix. -/
theorem NPlaneRealizes.handleU_fixed {alpha h : ℕ}
    {Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type)}
    {T : Matrix (Fin 2) (Fin 2) ℤ_[2]} (hPsi : NPlaneRealizes alpha h Psi T)
    (j : Fin h)
    (f : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2])) :
    toAdd (f (Psi (dnGen alpha h (handleIdxU j)))) =
      toAdd (f (dnGen alpha h (handleIdxU j))) := by
  have hrow := congrFun (hPsi.2 f) (handleIdxU j)
  rw [nCoreMat_of_ne _ _
    (handleIdxU_ne_of_val_lt j (by rw [coreVal_two]; omega))
    (handleIdxU_ne_three j)] at hrow
  exact hrow

/-- A nontrivially scaled handle character row contradicts the stronger plane
predicate. This is a candidate obstruction, not a nonexistence theorem for it. -/
theorem not_nPlaneRealizes_of_handleU_scaled {alpha h : ℕ}
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type))
    (j : Fin h) (kappa : ℤ_[2]ˣ) (hkappa : kappa ≠ 1)
    (hscale : ∀ f : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]),
      toAdd (f (Psi (dnGen alpha h (handleIdxU j)))) =
        (kappa : ℤ_[2]) * toAdd (f (dnGen alpha h (handleIdxU j))))
    (T : Matrix (Fin 2) (Fin 2) ℤ_[2]) : ¬ NPlaneRealizes alpha h Psi T := by
  intro hPsi
  have hfix := hPsi.handleU_fixed j (nHandleUCharacter alpha h j)
  have hsc := hscale (nHandleUCharacter alpha h j)
  rw [hfix, nHandleUCharacter_self, mul_one] at hsc
  apply hkappa
  apply Units.ext
  exact hsc.symm

/-- In particular, sending a handle-U generator to any conjugate of its
nontrivial unit power cannot realize a core-only plane transformation. -/
theorem not_nPlaneRealizes_of_handleU_conj_power {alpha h : ℕ}
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type))
    (j : Fin h) (kappa : ℤ_[2]ˣ) (hkappa : kappa ≠ 1) (c : DN alpha h)
    (himage : Psi (dnGen alpha h (handleIdxU j)) =
      conjP (zpowZtwo (isProP_DN alpha h) (dnGen alpha h (handleIdxU j))
        (kappa : ℤ_[2])) c)
    (T : Matrix (Fin 2) (Fin 2) ℤ_[2]) : ¬ NPlaneRealizes alpha h Psi T := by
  apply not_nPlaneRealizes_of_handleU_scaled Psi j kappa hkappa ?_ T
  intro f
  rw [himage]
  have hconj : f (conjP
      (zpowZtwo (isProP_DN alpha h) (dnGen alpha h (handleIdxU j)) (kappa : ℤ_[2])) c) =
      f (zpowZtwo (isProP_DN alpha h) (dnGen alpha h (handleIdxU j)) (kappa : ℤ_[2])) := by
    simp [conjP, map_mul, map_inv, mul_comm]
  rw [hconj, toAdd_map_zpowZtwo]

#print axioms nScalingHypothesis_of_sl2
#print axioms nHandleUCharacter
#print axioms nHandleUCharacter_gen
#print axioms nHandleUCharacter_self
#print axioms NPlaneRealizes.handleU_fixed
#print axioms not_nPlaneRealizes_of_handleU_scaled
#print axioms not_nPlaneRealizes_of_handleU_conj_power

end
end GQ2.Dyadic.MarkedCore

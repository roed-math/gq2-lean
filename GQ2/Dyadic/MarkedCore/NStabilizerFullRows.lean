import GQ2.Dyadic.MarkedCore.NFrameExists
import GQ2.Dyadic.Instances.EvenModelDemushkin
import GQ2.Dyadic.Instances.DNAutomorphismCup

/-!
The actual N automorphism cup form recovers the torsion coordinates omitted by
ordinary Z2 characters.  The final result realizes exactly the distinguished
rank-four `NStabParam.rows`, with identity on every handle coordinate.  It is
not a classification of arbitrary handle-mixing stabilizers.  The remaining
free torsion entry is explicit as `htau`, supplied by the separate exact N1
adjustment; no cup or unknown matrix premise is assumed.
-/

namespace GQ2.Dyadic.MarkedCore.NStabilizerFullRows
open Multiplicative GQ2.SectionThree GQ2.Dyadic.EvenModel
open GQ2.Dyadic.Instances.DNAutomorphismCup
open scoped GQ2.SectionThree.TopAbInstances
noncomputable section

variable {alpha h : Nat}

def nAbHom (alpha h : Nat) :
    ContinuousMonoidHom (DN alpha h : Type) (topAbelianization (DN alpha h : Type)) :=
  { toMonoidHom := abMk, continuous_toFun := continuous_abMk }

def torsionChar (ha : 1 ≤ alpha) (h : Nat) :
    ContinuousMonoidHom (DN alpha h : Type) (Multiplicative (ZMod 2)) :=
  (nTHom ha h).comp (nAbHom alpha h)

@[simp] theorem torsionChar_gen (ha : 1 ≤ alpha) (i : Fin (coreRank h)) :
    toAdd (torsionChar ha h (dnGen alpha h i)) =
      (Pi.single (0 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) i := by
  classical
  change toAdd (nTHom ha h (abMk (dnGen alpha h i))) = _
  rw [nTHom, nCoordHom_gen]
  by_cases hi : i = 0
  · subst i; simp
  · have hv : i.val ≠ 0 := fun hh => hi (Fin.ext (hh.trans (coreVal_zero h).symm))
    simp [coreMark, hv, hi]

def ordinaryChar (k : Fin (coreRank h)) (hk : k ≠ 0) :
    ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]) :=
  nLiftHom alpha h PropOneOne.isProP_two_multPadicInt
    (fun i => ofAdd ((Pi.single k 1 : Fin (coreRank h) → ℤ_[2]) i)) (by
      classical
      rw [nRelWord_comm]
      simp [Ne.symm hk])

@[simp] theorem ordinaryChar_gen (k : Fin (coreRank h)) (hk : k ≠ 0)
    (i : Fin (coreRank h)) :
    toAdd (ordinaryChar (alpha := alpha) k hk (dnGen alpha h i)) =
      (Pi.single k 1 : Fin (coreRank h) → ℤ_[2]) i := by
  rw [ordinaryChar, nLiftHom_gen, toAdd_ofAdd]

theorem ordinaryChar_aut (P : NStabParam)
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type))
    (H : ∀ f : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]),
      nuFrame f (fun i => Psi (dnGen alpha h i)) = P.nuAction (nuFrame f (dnGen alpha h)))
    (k : Fin (coreRank h)) (hk : k ≠ 0) (i : Fin (coreRank h)) :
    toAdd (ordinaryChar (alpha := alpha) k hk (Psi (dnGen alpha h i))) =
      P.nuAction (Pi.single k 1) i := by
  have hh := congrFun (H (ordinaryChar (alpha := alpha) k hk)) i
  have hb : nuFrame (ordinaryChar (alpha := alpha) k hk) (dnGen alpha h) = Pi.single k 1 := by
    funext j
    exact ordinaryChar_gen k hk j
  rw [hb] at hh
  exact hh

theorem nuAction_single_fixed (P : NStabParam) (k : Fin (coreRank h))
    (h2 : k ≠ 2) (h3 : k ≠ 3) :
    P.nuAction (Pi.single k 1 : Fin (coreRank h) → ℤ_[2]) = Pi.single k 1 := by
  classical
  have h13 : (1 : Fin (coreRank h)) ≠ 3 := by
    apply Fin.ne_of_val_ne; rw [coreVal_one, coreVal_three]; omega
  have hz2 : (Pi.single k 1 : Fin (coreRank h) → ℤ_[2]) 2 = 0 := by simp [Ne.symm h2]
  have hz3 : (Pi.single k 1 : Fin (coreRank h) → ℤ_[2]) 3 = 0 := by simp [Ne.symm h3]
  have hu2 : Function.update (Pi.single k 1 : Fin (coreRank h) → ℤ_[2]) 2 0 = Pi.single k 1 := by
    rw [← hz2, Function.update_eq_self]
  have hu3 : Function.update (Pi.single k 1 : Fin (coreRank h) → ℤ_[2]) 3 0 = Pi.single k 1 := by
    rw [← hz3, Function.update_eq_self]
  simp [NStabParam.nuAction, nCoreMat, nFrameMix, hz2, hz3, nCoreTwo_ne_one,
    Ne.symm h13, Function.update_eq_self, hu2, hu3]

theorem partner_involutive : Function.Involutive (@evenPartner h) := by
  intro i
  rcases nCoreIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩ <;> simp

theorem dualVector_partner_eq_single (k : Fin (coreRank h)) (hk : k ≠ 0) :
    evenDualVector (evenPartner k) = (Pi.single k 1 : Fin (coreRank h) → ZMod 2) := by
  classical
  funext i
  have hk' : evenPartner k ≠ 1 := by
    intro hh
    have := congrArg evenPartner hh
    rw [partner_involutive k, evenPartner_one] at this
    exact hk this
  simp only [evenDualVector, evenDualMap_apply]
  have hmain : (Pi.single (evenPartner k) 1 : Fin (coreRank h) → ZMod 2) (evenPartner i) =
      (Pi.single k 1 : Fin (coreRank h) → ZMod 2) i := by
    simp [Pi.single_apply, partner_involutive.injective.eq_iff]
  rw [hmain]
  simp [Ne.symm hk']

theorem cup_single_right (a : Fin (coreRank h) → ZMod 2)
    (k : Fin (coreRank h)) (hk : k ≠ 0) :
    evenCupForm a (Pi.single k 1) = a (evenPartner k) := by
  rw [← dualVector_partner_eq_single k hk, evenCupForm_evenDualVector]

def reduceChar (f : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2])) :
    ContinuousMonoidHom (DN alpha h : Type) (Multiplicative (ZMod 2)) where
  toMonoidHom := (AddMonoidHom.toMultiplicative nRed.toAddMonoidHom).comp f.toMonoidHom
  continuous_toFun := continuous_ofAdd.comp (continuous_nRed.comp (continuous_toAdd.comp f.continuous))

theorem reduced_ordinaryChar_gen (k : Fin (coreRank h)) (hk : k ≠ 0)
    (i : Fin (coreRank h)) :
    toAdd (reduceChar (ordinaryChar (alpha := alpha) k hk) (dnGen alpha h i)) =
      (Pi.single k 1 : Fin (coreRank h) → ZMod 2) i := by
  classical
  change nRed (toAdd (ordinaryChar k hk (dnGen alpha h i))) = _
  rw [ordinaryChar_gen]
  by_cases hi : i = k <;> simp [hi]

theorem torsion_cup_equation (ha : 2 ≤ alpha) (P : NStabParam)
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type))
    (H : ∀ f : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]),
      nuFrame f (fun i => Psi (dnGen alpha h i)) = P.nuAction (nuFrame f (dnGen alpha h)))
    (k : Fin (coreRank h)) (hk : k ≠ 0) :
    evenCupForm (fun i => toAdd (torsionChar (by omega : 1 ≤ alpha) h (Psi (dnGen alpha h i))))
      (fun i => nRed (P.nuAction (Pi.single k 1) i)) =
      (Pi.single (0 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) (evenPartner k) := by
  have hh := evenCupForm_comp_dn_aut ha Psi (torsionChar (by omega) h)
    (reduceChar (ordinaryChar (alpha := alpha) k hk))
  have he : (fun i => toAdd ((reduceChar (ordinaryChar (alpha := alpha) k hk)).comp (autHom Psi)
      (dnGen alpha h i))) = (fun i => nRed (P.nuAction (Pi.single k 1) i)) := by
    funext i
    change nRed (toAdd (ordinaryChar k hk (Psi (dnGen alpha h i)))) = _
    rw [ordinaryChar_aut P Psi H]
  rw [he] at hh
  change evenCupForm (fun i => toAdd (torsionChar (by omega : 1 ≤ alpha) h (Psi (dnGen alpha h i))))
    (fun i => nRed (P.nuAction (Pi.single k 1) i)) = _ at hh
  simpa only [torsionChar_gen, reduced_ordinaryChar_gen, cup_single_right _ k hk] using hh

theorem torsion_fixed_partner (ha : 2 ≤ alpha) (P : NStabParam)
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type))
    (H : ∀ f : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]),
      nuFrame f (fun i => Psi (dnGen alpha h i)) = P.nuAction (nuFrame f (dnGen alpha h)))
    (k : Fin (coreRank h)) (hk : k ≠ 0) (h2 : k ≠ 2) (h3 : k ≠ 3) :
    toAdd (torsionChar (by omega : 1 ≤ alpha) h (Psi (dnGen alpha h (evenPartner k)))) =
      (Pi.single (0 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) (evenPartner k) := by
  have hh := torsion_cup_equation ha P Psi H k hk
  rw [nuAction_single_fixed P k h2 h3] at hh
  have he : (fun i => nRed ((Pi.single k 1 : Fin (coreRank h) → ℤ_[2]) i)) =
      (Pi.single k 1 : Fin (coreRank h) → ZMod 2) := by
    classical
    funext i
    by_cases hi : i = k <;> simp [hi]
  rw [he, cup_single_right _ k hk] at hh
  exact hh

theorem torsionChar_aut_zero (ha : 2 ≤ alpha) (P : NStabParam)
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type))
    (H : ∀ f : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]),
      nuFrame f (fun i => Psi (dnGen alpha h i)) = P.nuAction (nuFrame f (dnGen alpha h))) :
    toAdd (torsionChar (by omega : 1 ≤ alpha) h (Psi (dnGen alpha h 0))) = 1 := by
  have hh := torsion_fixed_partner ha P Psi H 1
    (Ne.symm nCoreZero_ne_one) nCoreOne_ne_two
    (by apply Fin.ne_of_val_ne; rw [coreVal_one, coreVal_three]; omega)
  simpa using hh

theorem torsionChar_aut_handleU (ha : 2 ≤ alpha) (P : NStabParam)
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type))
    (H : ∀ f : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]),
      nuFrame f (fun i => Psi (dnGen alpha h i)) = P.nuAction (nuFrame f (dnGen alpha h)))
    (j : Fin h) :
    toAdd (torsionChar (by omega : 1 ≤ alpha) h (Psi (dnGen alpha h (handleIdxU j)))) = 0 := by
  have hh := torsion_fixed_partner ha P Psi H (handleIdxV j)
    (handleIdxV_ne_of_val_lt j (by rw [coreVal_zero]; omega))
    (handleIdxV_ne_of_val_lt j (by rw [coreVal_two]; omega))
    (handleIdxV_ne_of_val_lt j (by rw [coreVal_three]; omega))
  simpa [handleIdxU_ne_of_val_lt j (by rw [coreVal_zero]; omega)] using hh

theorem torsionChar_aut_handleV (ha : 2 ≤ alpha) (P : NStabParam)
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type))
    (H : ∀ f : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]),
      nuFrame f (fun i => Psi (dnGen alpha h i)) = P.nuAction (nuFrame f (dnGen alpha h)))
    (j : Fin h) :
    toAdd (torsionChar (by omega : 1 ≤ alpha) h (Psi (dnGen alpha h (handleIdxV j)))) = 0 := by
  have hh := torsion_fixed_partner ha P Psi H (handleIdxU j)
    (handleIdxU_ne_of_val_lt j (by rw [coreVal_zero]; omega))
    (handleIdxU_ne_of_val_lt j (by rw [coreVal_two]; omega))
    (handleIdxU_ne_of_val_lt j (by rw [coreVal_three]; omega))
  simpa [handleIdxV_ne_of_val_lt j (by rw [coreVal_zero]; omega)] using hh

theorem cup_action_two (P : NStabParam) (a : Fin (coreRank h) → ZMod 2)
    (h0 : a 0 = 1) (hU : ∀ j, a (handleIdxU j) = 0) (hV : ∀ j, a (handleIdxV j) = 0) :
    evenCupForm a (fun i => nRed (P.nuAction (Pi.single (2 : Fin (coreRank h)) 1) i)) =
      nRed P.p + a 2 * nRed (P.g 0 1) + a 3 * nRed (P.g 0 0) := by
  classical
  have h03 : (0 : Fin (coreRank h)) ≠ 3 := by
    apply Fin.ne_of_val_ne; rw [coreVal_zero, coreVal_three]; omega
  have h13 : (1 : Fin (coreRank h)) ≠ 3 := by
    apply Fin.ne_of_val_ne; rw [coreVal_one, coreVal_three]; omega
  have hr : coreRank h ≠ 1 := by unfold coreRank; omega
  simp [evenCupForm, hU, hV, h0, NStabParam.nuAction, nCoreMat, nFrameMix,
    hr, nCoreZero_ne_two, h03, nCoreOne_ne_two, h13,
    nCoreTwo_ne_one, nCoreThree_ne_one, nCoreThree_ne_two, coreTwo_ne_three,
    Matrix.transpose_apply, smul_eq_mul, add_assoc, Function.update_apply]

theorem cup_action_three (P : NStabParam) (a : Fin (coreRank h) → ZMod 2)
    (h0 : a 0 = 1) (hU : ∀ j, a (handleIdxU j) = 0) (hV : ∀ j, a (handleIdxV j) = 0) :
    evenCupForm a (fun i => nRed (P.nuAction (Pi.single (3 : Fin (coreRank h)) 1) i)) =
      nRed P.q + a 2 * nRed (P.g 1 1) + a 3 * nRed (P.g 1 0) := by
  classical
  have h03 : (0 : Fin (coreRank h)) ≠ 3 := by
    apply Fin.ne_of_val_ne; rw [coreVal_zero, coreVal_three]; omega
  have h13 : (1 : Fin (coreRank h)) ≠ 3 := by
    apply Fin.ne_of_val_ne; rw [coreVal_one, coreVal_three]; omega
  have hr : coreRank h ≠ 1 := by unfold coreRank; omega
  simp [evenCupForm, hU, hV, h0, NStabParam.nuAction, nCoreMat, nFrameMix,
    hr, nCoreZero_ne_two, h03, nCoreOne_ne_two, h13,
    nCoreTwo_ne_one, nCoreThree_ne_one, coreTwo_ne_three,
    Matrix.transpose_apply, smul_eq_mul, add_assoc, Function.update_apply]

theorem torsionChar_aut_plane (ha : 2 ≤ alpha) (P : NStabParam) (hP : P.Admissible)
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type))
    (H : ∀ f : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]),
      nuFrame f (fun i => Psi (dnGen alpha h i)) = P.nuAction (nuFrame f (dnGen alpha h))) :
    toAdd (torsionChar (by omega : 1 ≤ alpha) h (Psi (dnGen alpha h 2))) = P.tauSigma ∧
    toAdd (torsionChar (by omega : 1 ≤ alpha) h (Psi (dnGen alpha h 3))) = P.tauX2 := by
  let a : Fin (coreRank h) → ZMod 2 := fun i =>
    toAdd (torsionChar (by omega : 1 ≤ alpha) h (Psi (dnGen alpha h i)))
  have h0 : a 0 = 1 := torsionChar_aut_zero ha P Psi H
  have hU : ∀ j, a (handleIdxU j) = 0 := torsionChar_aut_handleU ha P Psi H
  have hV : ∀ j, a (handleIdxV j) = 0 := torsionChar_aut_handleV ha P Psi H
  have hp := torsion_cup_equation ha P Psi H 2 (Ne.symm nCoreZero_ne_two)
  have h03 : (0 : Fin (coreRank h)) ≠ 3 := by
    apply Fin.ne_of_val_ne; rw [coreVal_zero, coreVal_three]; omega
  have hq := torsion_cup_equation ha P Psi H 3 (Ne.symm h03)
  change evenCupForm a _ = _ at hp hq
  rw [cup_action_two P a h0 hU hV] at hp
  rw [cup_action_three P a h0 hU hV] at hq
  simp only [evenPartner_two, evenPartner_three, Pi.single_eq_of_ne (Ne.symm h03),
    Pi.single_eq_of_ne (Ne.symm nCoreZero_ne_two)] at hp hq
  have hcalc : ∀ p u v : ZMod 2, p + u + v = 0 → p = v + u := by decide
  have hadm : NStabParam.Admissible ⟨P.tau, P.p, P.q, a 2, a 3, P.g⟩ :=
    ⟨hP.det, hcalc _ _ _ hp, hcalc _ _ _ hq⟩
  obtain ⟨st, _, hu⟩ := nStabParam_tauSolve_unique P.tau P.p P.q hP.det
  have he : (a 2, a 3) = (P.tauSigma, P.tauX2) :=
    (hu _ hadm).trans (hu _ hP).symm
  exact Prod.mk.inj he

def fullFrameMark (P : NStabParam) (h : Nat) (i : Fin (coreRank h)) : NFrameModel h :=
  coreMark (ofAdd (1, 0, 0, 0, 0)) (ofAdd (P.tau, 1, P.p, P.q, 0))
      (ofAdd (P.tauSigma, 0, P.g 0 0, P.g 1 0, 0))
      (ofAdd (P.tauX2, 0, P.g 0 1, P.g 1 1, 0)) i *
    ofAdd (0, 0, 0, 0, fun k => toAdd (mHandleMark k (ofAdd (1 : ℤ_[2])) i))

theorem coordHom_aut (P : NStabParam)
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type))
    (H : ∀ f : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]),
      nuFrame f (fun i => Psi (dnGen alpha h i)) = P.nuAction (nuFrame f (dnGen alpha h)))
    (m : Fin (coreRank h) → Multiplicative ℤ_[2]) (hm : m 0 ^ (2 + 2 ^ alpha) = 1)
    (i : Fin (coreRank h)) :
    toAdd (nCoordHom alpha h PropOneOne.isProP_two_multPadicInt m hm
      (abMk (Psi (dnGen alpha h i)))) = P.nuAction (fun j => toAdd (m j)) i := by
  let f := (nCoordHom alpha h PropOneOne.isProP_two_multPadicInt m hm).comp (nAbHom alpha h)
  have hb : nuFrame f (dnGen alpha h) = fun j => toAdd (m j) := by
    funext j
    change toAdd (nCoordHom alpha h PropOneOne.isProP_two_multPadicInt m hm
      (abMk (dnGen alpha h j))) = _
    rw [nCoordHom_gen]
  have hh := congrFun (H f) i
  rw [hb] at hh
  exact hh

theorem nPhiHom_aut_coordinates (ha : 2 ≤ alpha) (P : NStabParam)
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type))
    (H : ∀ f : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]),
      nuFrame f (fun i => Psi (dnGen alpha h i)) = P.nuAction (nuFrame f (dnGen alpha h)))
    (i : Fin (coreRank h)) :
    nPhiHom ha h (abMk (Psi (dnGen alpha h i))) = ofAdd
      (toAdd (torsionChar (by omega : 1 ≤ alpha) h (Psi (dnGen alpha h i))),
        P.nuAction (fun j => toAdd (coreMark 1 (ofAdd (1 : ℤ_[2])) 1 1 j)) i,
        P.nuAction (fun j => toAdd (coreMark 1 1 (ofAdd (1 : ℤ_[2])) 1 j)) i,
        P.nuAction (fun j => toAdd (coreMark 1 1 1 (ofAdd (1 : ℤ_[2])) j)) i,
        fun k => P.nuAction (fun j => toAdd (mHandleMark k (ofAdd (1 : ℤ_[2])) j)) i) := by
  change ofAdd (_, _, _, _, _) = _
  congr 1
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · exact coordHom_aut P Psi H _ _ i
  · exact coordHom_aut P Psi H _ _ i
  · exact coordHom_aut P Psi H _ _ i
  · funext k
    exact coordHom_aut P Psi H _ _ i

theorem nPhiHom_aut_fullFrameMark (ha : 2 ≤ alpha) (P : NStabParam) (hP : P.Admissible)
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type))
    (H : ∀ f : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]),
      nuFrame f (fun i => Psi (dnGen alpha h i)) = P.nuAction (nuFrame f (dnGen alpha h)))
    (htau : toAdd (torsionChar (by omega : 1 ≤ alpha) h (Psi (dnGen alpha h 1))) = P.tau)
    (i : Fin (coreRank h)) :
    nPhiHom ha h (abMk (Psi (dnGen alpha h i))) = fullFrameMark P h i := by
  rw [nPhiHom_aut_coordinates ha P Psi H]
  obtain ⟨h2, h3⟩ := torsionChar_aut_plane ha P hP Psi H
  have h0 := torsionChar_aut_zero ha P Psi H
  have hU := torsionChar_aut_handleU ha P Psi H
  have hV := torsionChar_aut_handleV ha P Psi H
  have h03 : (0 : Fin (coreRank h)) ≠ 3 := by
    apply Fin.ne_of_val_ne; rw [coreVal_zero, coreVal_three]; omega
  have h13 : (1 : Fin (coreRank h)) ≠ 3 := by
    apply Fin.ne_of_val_ne; rw [coreVal_one, coreVal_three]; omega
  have hr : coreRank h ≠ 1 := by unfold coreRank; omega
  have hH0 (k : Fin (2*h)) : toAdd (mHandleMark k (ofAdd (1 : ℤ_[2])) (0 : Fin (coreRank h))) = 0 :=
    mHandleMark_toAdd_core 0 (by rw [coreVal_zero]; omega) k
  have hH1 (k : Fin (2*h)) : toAdd (mHandleMark k (ofAdd (1 : ℤ_[2])) (1 : Fin (coreRank h))) = 0 :=
    mHandleMark_toAdd_core 1 (by rw [coreVal_one]; omega) k
  have hH2 (k : Fin (2*h)) : toAdd (mHandleMark k (ofAdd (1 : ℤ_[2])) (2 : Fin (coreRank h))) = 0 :=
    mHandleMark_toAdd_core 2 (by rw [coreVal_two]; omega) k
  have hH3 (k : Fin (2*h)) : toAdd (mHandleMark k (ofAdd (1 : ℤ_[2])) (3 : Fin (coreRank h))) = 0 :=
    mHandleMark_toAdd_core 3 (by rw [coreVal_three]; omega) k
  have hu3 (j : Fin h) : handleIdxU j ≠ (3 : Fin (coreRank h)) :=
    handleIdxU_ne_of_val_lt j (by rw [coreVal_three]; omega)
  have hv3 (j : Fin h) : handleIdxV j ≠ (3 : Fin (coreRank h)) :=
    handleIdxV_ne_of_val_lt j (by rw [coreVal_three]; omega)
  rcases nCoreIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  all_goals simp [fullFrameMark, NStabParam.nuAction, nCoreMat, nFrameMix,
    h0, htau, h2, h3, hU, hV, hH0, hH1, hH2, hH3,
    hr, nCoreZero_ne_two, h03, nCoreOne_ne_two, h13, nCoreTwo_ne_one,
    nCoreThree_ne_one, coreTwo_ne_three, Matrix.transpose_apply, smul_eq_mul,
    nHandleIdxU_ne_one, nHandleIdxV_ne_one, nHandleIdxU_ne_two, nHandleIdxV_ne_two,
    hu3, hv3, ← ofAdd_add]

#print axioms nAbHom
#print axioms torsionChar
#print axioms torsionChar_gen
#print axioms ordinaryChar
#print axioms ordinaryChar_gen
#print axioms ordinaryChar_aut
#print axioms nuAction_single_fixed
#print axioms partner_involutive
#print axioms dualVector_partner_eq_single
#print axioms cup_single_right
#print axioms reduceChar
#print axioms reduced_ordinaryChar_gen
#print axioms torsion_cup_equation
#print axioms torsion_fixed_partner
#print axioms torsionChar_aut_zero
#print axioms torsionChar_aut_handleU
#print axioms torsionChar_aut_handleV
#print axioms cup_action_two
#print axioms cup_action_three
#print axioms torsionChar_aut_plane
#print axioms fullFrameMark
#print axioms coordHom_aut
#print axioms nPhiHom_aut_coordinates
#print axioms nPhiHom_aut_fullFrameMark

end
end GQ2.Dyadic.MarkedCore.NStabilizerFullRows

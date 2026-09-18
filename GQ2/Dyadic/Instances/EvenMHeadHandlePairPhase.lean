/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GQ2.Dyadic.Instances.EvenMHeadHandlePairCore
import GQ2.Dyadic.Instances.WordPhaseCompactMHandleData
import GQ2.Dyadic.Certificates.MpcJet

namespace GQ2.Dyadic.Instances.EvenMHeadHandlePairPhase

noncomputable section

open GQ2 GQ2.FoxH GQ2.QuadraticFp2 GQ2.SectionSix
open GQ2.Dyadic.Words GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.Certificates.MCompact GQ2.Dyadic.Certificates.MpcJet
open GQ2.Dyadic.Instances.WordPhase GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.EvenMHeadHandleSource
open GQ2.Dyadic.Instances.EvenMHeadHandlePairSource
open GQ2.Dyadic.Instances.EvenMHeadHandlePairCore

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q0 : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat)
  (hV2 : ∀ v : V, v + v = 0)

include hV2

private theorem slice_res_one (v : V) (z : ZMod 2) {e : ℕ} (he : e % 4 = 1) :
    hessSlice dat hdat v z ^ e = hessSlice dat hdat v z := by
  obtain ⟨t, ht⟩ : ∃ t, e = 4 * t + 1 := ⟨e / 4, by omega⟩
  rw [ht, show 4 * t + 1 = 2 * (2 * t) + 1 by ring,
    hessSlice_odd_pow dat hdat hV2, mul_nsmul, two_nsmul,
    CharTwo.add_self_eq_zero, nsmul_zero, add_zero]

private theorem slice_even_zpow (v : V) (z : ZMod 2) {k : ℤ} (hk : Even k) :
    ∃ a : ZMod 2, hessSlice dat hdat v z ^ k =
      WordCoh.CentExt.incl (kappa0Cocycle dat hdat) a := by
  obtain ⟨n, hn⟩ := hk
  have hs : hessSlice dat hdat v z ^ (2 : ℤ) =
      WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (q0 v) := by
    rw [show (2 : ℤ) = (2 : ℕ) from rfl, zpow_natCast, sq,
      hessSlice_sq dat hdat hV2]
  rw [hn, ← two_mul, zpow_mul, hs]
  let p := WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (q0 v) ^ n
  refine ⟨p.fib, (WordCoh.CentExt.base_eq_one_iff p).mp ?_⟩
  change WordCoh.CentExt.proj _ ((WordCoh.CentExt.incl _ (q0 v)) ^ n) = 1
  rw [map_zpow]
  change (1 : SemiProd C V) ^ n = 1
  exact one_zpow n

/-- The compact core with a slice in the sigma slot adds exactly the missing handle plane. -/
theorem evalZ_mFactors_sigma_slice {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (f : Generator (2 + 2 * h) → WordCoh.CentExt (kappa0Cocycle dat hdat))
    (u : V) (v : Fin 3 → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hsigma : f .sigma = hessSlice dat hdat u 0) (htau : f .tau = 1)
    (hcore : ∀ i, f (coreLetter h i) = hessSlice dat hdat (v i) 0)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    PWord.evalZ f E E₂ (PWord.prodList (mFactors alpha h)) =
      WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
        (q0 (v 0) + polar q0 (v 0) (v 1) + polar q0 u (v 2)) := by
  have hs2 : PWord.evalZ f E E₂ sigma2W = hessSlice dat hdat u 0 := by
    simp only [sigma2W, PWord.omega2Pow, PWord.evalZ_profPow, PWord.evalZ_gen,
      hsigma, hE, zpow_natCast]
    exact slice_res_one dat hdat hV2 u 0 he
  have hdelta (i : Fin 3) : PWord.evalZ f E E₂ (MCompact.deltaC h i) = 1 := by
    simp [MCompact.deltaC, PWord.omega2Pow, htau, hcore, hE,
      slice_res_one dat hdat hV2 _ _ he]
  have hrev : PWord.evalZ f E E₂ (eRevW alpha h) = 1 := by
    simp [eRevW, hdelta, conjR]
  obtain ⟨a, ha⟩ := slice_even_zpow dat hdat hV2 u 0 (even_neg_mOf halpha)
  obtain ⟨b, hb⟩ := slice_even_zpow dat hdat hV2 u 0 (even_mOf_int halpha)
  have ha0 : PWord.evalZ f E E₂ (a0W alpha h) =
      hessSlice dat hdat (v 0) (q0 (v 0)) * WordCoh.CentExt.incl _ a := by
    simp only [a0W, PWord.evalZ_prodList, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, PWord.evalZ_inv, PWord.evalZ_gen,
      PWord.evalZ_zpow, hcore, hs2, ha, mul_one]
    rw [hessSlice_inv dat hdat hV2, zero_add]
  have hlead : PWord.evalZ f E E₂ (.zpow (a0W alpha h) 2) =
      WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (q0 (v 0)) := by
    rw [PWord.evalZ_zpow, ha0, show (2 : ℤ) = (2 : ℕ) from rfl, zpow_natCast,
      sq_mul_incl, sq, hessSlice_sq dat hdat hV2]
  have hcomm : PWord.evalZ f E E₂ (.comm (a0W alpha h) (.gen (coreLetter h 1))) =
      WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (polar q0 (v 0) (v 1)) := by
    rw [PWord.evalZ_comm, ha0, PWord.evalZ_gen, hcore,
      commR_mul_right_of_commute (incl_commute _ _) (incl_commute _ _),
      hessSlice_commR dat hdat hV2]
  have hpow : PWord.evalZ f E E₂ (.zpow sigma2W (2 * (mOf alpha : ℤ))) = 1 := by
    rw [PWord.evalZ_zpow, hs2, mul_comm (2 : ℤ), zpow_mul, hb,
      show (2 : ℤ) = (2 : ℕ) from rfl, zpow_natCast, sq, centExt_incl_mul_self]
  have hj : PWord.evalZ f E E₂ (j2W h) =
      WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (polar q0 u (v 2)) := by
    simp only [j2W, PWord.evalZ_prodList, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, PWord.evalZ_inv, PWord.evalZ_conj, PWord.evalZ_gen, hcore,
      hsigma, PWord.omega2Pow, PWord.evalZ_profPow, htau, mul_one, hE, zpow_natCast]
    rw [slice_res_one dat hdat hV2 _ _ he]
    have hc : (conjR (hessSlice dat hdat (v 2) 0) (hessSlice dat hdat u 0))⁻¹ *
        hessSlice dat hdat (v 2) 0 =
        commR (hessSlice dat hdat u 0) (hessSlice dat hdat (v 2) 0) := by
      simp only [conjR, commR]
      group
    rw [hc, hessSlice_commR dat hdat hV2]
  simp only [mFactors, PWord.evalZ_prodList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, hlead, hcomm, hpow, hj, hrev, mul_one, one_mul]
  rw [centExt_incl_mul, centExt_incl_mul]
  congr 1
  abel

/-- At the compact normal coordinates the raw pair source has the complete plus-and-handles
phase, including the promoted handle. The lower sigma element is arbitrary. -/
theorem hessEvalZ_headHandlePair_normal {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (j : Fin h) (s : C) (p : (V × V) × (Fin h → V × V))
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    hessEvalZ
        (Certificates.hessMark s 1 (fun i => wPmCompactPhaseNormal h p (.wild i)))
        (kappa0Cocycle dat hdat) E E₂ (headHandlePairCompactW alpha j) =
      WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
        (wPhCompactWallHandlePhase q0 h p) := by
  classical
  let mu := WordCoh.lift
    (Certificates.hessMark s 1 (fun i => wPmCompactPhaseNormal h p (.wild i)))
    (kappa0Cocycle dat hdat)
  let f := fun g => mu (headHandlePairSwap j g)
  have hmuCore (i : Fin 3) : mu (coreLetter h i) =
      hessSlice dat hdat (![p.1.1, p.1.2, 0] i) 0 := by
    change hessSlice dat hdat (wPmCompactPhaseNormal h p (coreLetter h i)) 0 = _
    rw [wPmCompactPhaseNormal_coreLetter]
  have hmuU (k : Fin h) : mu (handleU k) = hessSlice dat hdat (p.2 k).1 0 := by
    change hessSlice dat hdat (wPmCompactPhaseNormal h p (handleU k)) 0 = _
    rw [wPmCompactPhaseNormal_handleU]
  have hmuV (k : Fin h) : mu (handleV k) = hessSlice dat hdat (p.2 k).2 0 := by
    change hessSlice dat hdat (wPmCompactPhaseNormal h p (handleV k)) 0 = _
    rw [wPmCompactPhaseNormal_handleV]
  have hcore (i : Fin 3) : f (coreLetter h i) =
      hessSlice dat hdat (![p.1.1, p.1.2, (p.2 j).2] i) 0 := by
    fin_cases i
    · simpa [f, headHandlePairSwap, headHandleSwap_coreLetter,
        tailHandleSwap_coreZero] using hmuCore 0
    · simpa [f, headHandlePairSwap, headHandleSwap_coreLetter,
        tailHandleSwap_coreOne] using hmuCore 1
    · simpa [f] using hmuV j
  have hsig : f .sigma = hessSlice dat hdat (p.2 j).1 0 := by
    simpa [f] using hmuU j
  have htau : f .tau = 1 := by
    simp only [f, headHandlePairSwap_tau]
    rfl
  have hcoreEval := evalZ_mFactors_sigma_slice dat hdat hV2 halpha f
    (p.2 j).1 ![p.1.1, p.1.2, (p.2 j).2] E E₂ hsig htau hcore hE he
  change PWord.evalZ f E E₂ (PWord.prodList (mFactors alpha h)) =
    WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
      (q0 p.1.1 + polar q0 p.1.1 p.1.2 + polar q0 (p.2 j).1 (p.2 j).2) at hcoreEval
  let B := fun k : Fin h => polar q0 (p.2 k).1 (p.2 k).2
  have hcomm (k : Fin h) : commR (f (handleU k)) (f (handleV k)) =
      WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (if k = j then 0 else B k) := by
    by_cases hkj : k = j
    · subst k
      simp only [f, headHandlePairSwap_handleU_self, headHandlePairSwap_handleV_self,
        hmuCore]
      change commR (mu .sigma) (hessSlice dat hdat 0 0) =
        WordCoh.CentExt.incl _ (if True then 0 else B j)
      simp [hessSlice_zero_zero, commR]
    · have hu : headHandlePairSwap j (handleU k) = handleU k := by
        simp [headHandlePairSwap, hkj]
      have hv : headHandlePairSwap j (handleV k) = handleV k := by
        simp [headHandlePairSwap, hkj]
      simp only [f, hu, hv, hmuU, hmuV, if_neg hkj]
      exact hessSlice_commR dat hdat hV2 _ _ _ _
  have hhandles : PWord.evalZ f E E₂ (handlesW h) =
      WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (∑ k, if k = j then 0 else B k) := by
    rw [handlesW, PWord.evalZ_prodList, List.map_map]
    change ((List.finRange h).map fun k => commR (f (handleU k)) (f (handleV k))).prod = _
    simp only [hcomm]
    rw [show ((List.finRange h).map fun k => WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
      (if k = j then 0 else B k)) =
      ((List.finRange h).map fun k => if k = j then 0 else B k).map
        (WordCoh.CentExt.incl (kappa0Cocycle dat hdat)) from List.map_map.symm,
      centExt_incl_list_prod, ← Fin.sum_univ_def]
  have htail : PWord.evalZ f E E₂ (PWord.prodList (handleTailW h)) =
      WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (∑ k, if k = j then 0 else B k) := by
    cases h with
    | zero => exact Fin.elim0 j
    | succ h => simpa [handleTailW] using hhandles
  have hmap : (fun g => PWord.evalZ mu E E₂ ((headHandlePairNielsen j).backward g)) = f := by
    funext g
    change mu ((headHandlePairSwap j).symm g) = f g
    rw [headHandlePairSwap_symm]
  change PWord.evalZ mu E E₂ _ = _
  rw [headHandlePairCompactW_eq_nielsenBackward, PWord.evalZ_subst, hmap,
    mCompactW, PWord.evalZ_prodList, List.map_append, List.prod_append]
  rw [← PWord.evalZ_prodList, ← PWord.evalZ_prodList, hcoreEval, htail, centExt_incl_mul]
  congr 1
  have hsum : B j + (∑ k, if k = j then 0 else B k) = ∑ k, B k := by
    have hj : (∑ k, if k = j then B k else 0) = B j := by simp
    rw [← hj]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs <;> simp
  change (q0 p.1.1 + polar q0 p.1.1 p.1.2 + B j) +
    (∑ k, if k = j then 0 else B k) = _
  rw [add_assoc, hsum]
  rfl

/-- The scalar Hessian form of the exact extraspecial pair-source evaluation. -/
theorem hessRelZ_headHandlePair_normal {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (j : Fin h) (s : C) (p : (V × V) × (Fin h → V × V))
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    hessRelZ
        (Certificates.hessMark s 1 (fun i => wPmCompactPhaseNormal h p (.wild i)))
        (kappa0Cocycle dat hdat) E E₂ (headHandlePairCompactW alpha j) =
      wPhCompactWallHandlePhase q0 h p := by
  rw [hessRelZ, hessEvalZ_headHandlePair_normal dat hdat hV2 halpha j s p E E₂ hE he]
  rfl

end
end GQ2.Dyadic.Instances.EvenMHeadHandlePairPhase

#print axioms GQ2.Dyadic.Instances.EvenMHeadHandlePairPhase.evalZ_mFactors_sigma_slice
#print axioms GQ2.Dyadic.Instances.EvenMHeadHandlePairPhase.hessEvalZ_headHandlePair_normal
#print axioms GQ2.Dyadic.Instances.EvenMHeadHandlePairPhase.hessRelZ_headHandlePair_normal

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcGeneralHandleRealization

/-!
# Full general-h procyclic-M marked certificate

The scaled handle layer reduces the general normalization to the exact rank-four `D` and `B`
transvections.  Keeping `MScalingHypothesis` explicit gives the completed certificate the
standard axiom footprint.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralHandleCertificate

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcGeneralHandleRealization
open GQ2.Dyadic.SelectedCoreLeavesRN

noncomputable section

/-- Full arbitrary-h and arbitrary-unit Mpc normalization, with scaling kept as an explicit
premise and all later corrections supplied by exact automorphisms. -/
theorem markedMatching_of_scaling {alpha : ℕ} (r pp h : ℕ) (eta : ℤ_[2]ˣ)
    (halpha : 2 ≤ alpha) (halpha1 : 1 ≤ alpha)
    (hscale : MScalingHypothesis alpha h)
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (hlev : MpcChiKerLevelH alpha r h nu)
    (hdata : MpcMarkedDataH alpha r pp h eta nu) :
    ∃ u : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (u x) = chiM alpha h x) ∧
        ∀ x, nu (u x) = mpcNuPadic alpha r pp h eta halpha1 x := by
  obtain ⟨u0, hu0chi, hc0, hU0, hV0⟩ :=
    exists_scaled_handle_correction hscale nu hlev hdata.1
  let nu1 := nu.comp (autHom u0)
  obtain ⟨wD, hwD⟩ := hdata.2.1
  obtain ⟨wB, hwB⟩ := hdata.2.2
  obtain ⟨yD, hyD⟩ := shift_mem_of_level hlev hu0chi (dmD alpha h)
  obtain ⟨yB, hyB⟩ := shift_mem_of_level hlev hu0chi (dmB alpha h)
  have hc1 : toAdd (nu1 (dmC alpha h)) = 2 ^ r := hc0
  have hd1 : toAdd (nu1 (dmD alpha h)) =
      (eta : ℤ_[2]) + 2 ^ r * (wD + yD) := by
    change toAdd (nu (u0 (dmD alpha h))) = _
    rw [hyD, hwD]
    ring
  have hb1 : toAdd (nu1 (dmB alpha h)) =
      (pp : ℤ_[2]) + 2 ^ r * (wB + yB) := by
    change toAdd (nu (u0 (dmB alpha h))) = _
    rw [hyB, hwB]
    ring
  let k : ℤ_[2] := -(wD + yD)
  let nu2 := nu1.comp (autHom (dmTauDEquiv alpha h k))
  have hc2 : toAdd (nu2 (dmC alpha h)) = 2 ^ r := by
    change toAdd (nu1 (dmTauDEquiv alpha h k (dmC alpha h))) = _
    rw [show dmC alpha h = dmGen alpha h 2 from rfl, dmTauDEquiv_gen, tauDMark_two]
    exact hc1
  have hd2 : toAdd (nu2 (dmD alpha h)) = (eta : ℤ_[2]) := by
    change toAdd (nu1 (dmTauDEquiv alpha h k (dmD alpha h))) = _
    rw [show dmD alpha h = dmGen alpha h 3 from rfl, dmTauDEquiv_gen,
      tauDMark_three, map_mul, toAdd_mul,
      toAdd_map_zpowZtwo (isProP_DM alpha h) nu1]
    change k * toAdd (nu1 (dmC alpha h)) + toAdd (nu1 (dmD alpha h)) = _
    rw [hc1, hd1]
    dsimp only [k]
    ring
  have hb2 : toAdd (nu2 (dmB alpha h)) =
      (pp : ℤ_[2]) + 2 ^ r * (wB + yB) := by
    change toAdd (nu1 (dmTauDEquiv alpha h k (dmB alpha h))) = _
    rw [show dmB alpha h = dmGen alpha h 1 from rfl, dmTauDEquiv_gen,
      tauDMark_of_ne _ _ _ (Fin.ne_of_val_ne (by rw [coreVal_one, coreVal_three]; omega))]
    exact hb1
  let b : ℤ_[2] := -(wB + yB)
  obtain ⟨u5, hu5chi, hu5frame⟩ := mMixFamily_coreMix alpha h halpha b
  refine ⟨u5.trans ((dmTauDEquiv alpha h k).trans u0), fun x => ?_, ?_⟩
  · show chiM alpha h (u0 (dmTauDEquiv alpha h k (u5 x))) = chiM alpha h x
    rw [hu0chi, chiM_dmTauDEquiv, hu5chi]
  · intro x
    have hext : nu2.comp (autHom u5) = mpcNuPadic alpha r pp h eta halpha1 := by
      refine dm_hom_ext _ _ fun i => ?_
      have hrow := congrFun (hu5frame nu2) i
      rw [nuFrame_apply, nFrameMixX1] at hrow
      apply Multiplicative.toAdd.injective
      change toAdd (nu2 (u5 (dmGen alpha h i))) =
        toAdd (mpcNuPadic alpha r pp h eta halpha1 (dmGen alpha h i))
      rcases nCoreIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [hrow, Function.update_of_ne nCoreZero_ne_one, nuFrame_apply,
          mpcNuPadic_gen_zero, toAdd_ofAdd]
        change toAdd (nu2 (dmA alpha h)) = -((m alpha : ℤ_[2]) * (s r : ℤ_[2]))
        have hA := nu_dmA_eq alpha h halpha1 nu2
        rw [hc2] at hA
        rw [hA]
        push_cast [m, s]
        ring
      · rw [hrow, Function.update_self, nuFrame_apply, nuFrame_apply,
          mpcNuPadic_gen_one, toAdd_ofAdd]
        change toAdd (nu2 (dmB alpha h)) + b * toAdd (nu2 (dmC alpha h)) =
          (pp : ℤ_[2])
        rw [hb2, hc2]
        dsimp only [b]
        ring
      · rw [hrow, Function.update_of_ne nCoreTwo_ne_one, nuFrame_apply,
          mpcNuPadic_gen_two, toAdd_ofAdd]
        change toAdd (nu2 (dmC alpha h)) = (s r : ℤ_[2])
        rw [hc2]
        push_cast [s]
        rfl
      · rw [hrow, Function.update_of_ne nCoreThree_ne_one, nuFrame_apply,
          mpcNuPadic_gen_three, toAdd_ofAdd]
        change toAdd (nu2 (dmD alpha h)) = (eta : ℤ_[2])
        exact hd2
      · have hne : handleIdxU j ≠ (1 : Fin (coreRank h)) :=
          Fin.ne_of_val_ne (by rw [handleIdxU_val, coreVal_one]; omega)
        rw [hrow, Function.update_of_ne hne, nuFrame_apply,
          mpcNuPadic_gen_handleU, toAdd_one]
        change toAdd (nu1 (dmTauDEquiv alpha h k
          (dmGen alpha h (handleIdxU j)))) = 0
        rw [dmTauDEquiv_gen, tauDMark_of_ne _ _ _ (handleIdxU_ne_three j)]
        change toAdd (nu (u0 (dmGen alpha h (handleIdxU j)))) = 0
        rw [hU0, toAdd_one]
      · have hne : handleIdxV j ≠ (1 : Fin (coreRank h)) :=
          Fin.ne_of_val_ne (by rw [handleIdxV_val, coreVal_one]; omega)
        rw [hrow, Function.update_of_ne hne, nuFrame_apply,
          mpcNuPadic_gen_handleV, toAdd_one]
        change toAdd (nu1 (dmTauDEquiv alpha h k
          (dmGen alpha h (handleIdxV j)))) = 0
        rw [dmTauDEquiv_gen, tauDMark_of_ne _ _ _ (handleIdxV_ne_three j)]
        change toAdd (nu (u0 (dmGen alpha h (handleIdxV j)))) = 0
        rw [hV0, toAdd_one]
    exact DFunLike.congr_fun hext x

/-- Pull a marking back to a general-h M core. -/
def transport {G : Type} [Group G] [TopologicalSpace G] {alpha h : ℕ}
    (nuG : G →* Multiplicative ℤ_[2])
    (e : ContinuousMulEquiv (DM alpha h : Type) G)
    (hcont : Continuous fun x => nuG (e x)) :
    ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]) where
  toFun x := nuG (e x)
  map_one' := by rw [map_one, map_one]
  map_mul' x y := by rw [map_mul, map_mul]
  continuous_toFun := hcont

/-- Produce the full general-h certificate from an oriented equivalence, explicit scaling, and
the exact level/residue data. -/
theorem certificate_of_oriented
    {G : Type} [Group G] [TopologicalSpace G]
    {alpha : ℕ} (r pp h : ℕ) (eta : ℤ_[2]ˣ) (halpha : 2 ≤ alpha)
    (halpha1 : 1 ≤ alpha) (hscale : MScalingHypothesis alpha h)
    (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2])
    (e : ContinuousMulEquiv (DM alpha h : Type) G)
    (hechi : ∀ x, chiG (e x) = chiM alpha h x)
    (hcont : Continuous fun x => nuG (e x))
    (hlev : MpcChiKerLevelH alpha r h
      (transport nuG e hcont))
    (hdata : MpcMarkedDataH alpha r pp h eta
      (transport nuG e hcont)) :
    Nonempty (Certificate alpha r pp h eta halpha1 chiG nuG) := by
  obtain ⟨u, huchi, hunu⟩ := markedMatching_of_scaling r pp h eta halpha halpha1
    hscale (transport nuG e hcont) hlev hdata
  exact ⟨⟨e, hechi, u, huchi, hunu⟩⟩

#print axioms markedMatching_of_scaling
#print axioms transport
#print axioms certificate_of_oriented

end

end GQ2.Dyadic.Instances.MpcGeneralHandleCertificate

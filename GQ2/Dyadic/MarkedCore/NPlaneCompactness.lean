/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.MarkedCore.N
import GQ2.Reconstruction
import GQ2.Roe.Labute.TwoCentralTower

/-!
# Exact-row compactness for the strong N-plane lifting problem

The stage sets live in the original compact group, with every ordinary Z2
character row already exact, exact orientation, and Frattini generation.
Only the relator is approximate. These closed sets are nested; no compatible
choice of stage witnesses is needed. Nonemptiness at every depth is equivalent
to the desired actual automorphism. This is a reduction, not a proof that the
stage sets are nonempty or a discharge of `NPlaneScalingHypothesis`.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Roe.Labute Multiplicative

variable (alpha h : ℕ)

/-- Generation modulo the Frattini subgroup, expressed by index-two tests. -/
def NPlaneModTwoIndep (m : Fin (coreRank h) → DN alpha h) : Prop :=
  ∀ M : OpenNormalSubgroup (DN alpha h : Type),
    M.toSubgroup.index = 2 → ∃ i, m i ∉ M.toSubgroup

theorem nPlane_finsetGen :
    ∃ s : Finset (DN alpha h : Type),
      (Subgroup.closure (s : Set (DN alpha h : Type))).topologicalClosure = ⊤ := by
  classical
  refine ⟨Finset.univ.image (dnGen alpha h), ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact dn_topGen alpha h

theorem nPlane_iInf_twoCentralSeries :
    ⨅ k, twoCentralSeries (DN alpha h : Type) k = ⊥ :=
  iInf_twoCentralSeries (G := (DN alpha h : Type))
    (nPlane_finsetGen alpha h) (isProP_DN alpha h)

/-- Exact simultaneous rows and orientation; only the relation sees the depth. -/
def nPlaneStageSet (T : Matrix (Fin 2) (Fin 2) ℤ_[2]) (k : ℕ) :
    Set (Fin (coreRank h) → DN alpha h) :=
  {m | (∀ i, chiN alpha h (m i) = chiN alpha h (dnGen alpha h i)) ∧
    (∀ f : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]),
      nuFrame f m = nCoreMat T (nuFrame f (dnGen alpha h))) ∧
    NPlaneModTwoIndep alpha h m ∧
    nRelWord alpha m ∈ twoCentralSeries (DN alpha h : Type) k}

theorem nPlaneStageSet_antitone (T : Matrix (Fin 2) (Fin 2) ℤ_[2]) :
    Antitone (nPlaneStageSet alpha h T) := by
  intro k l hkl m hm
  exact ⟨hm.1, hm.2.1, hm.2.2.1,
    twoCentralSeries_antitone (G := (DN alpha h : Type)) hkl hm.2.2.2⟩

theorem isClosed_nPlaneStageSet (T : Matrix (Fin 2) (Fin 2) ℤ_[2]) (k : ℕ) :
    IsClosed (nPlaneStageSet alpha h T k) := by
  have hchi : IsClosed {m : Fin (coreRank h) → DN alpha h |
      ∀ i, chiN alpha h (m i) = chiN alpha h (dnGen alpha h i)} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun i =>
      isClosed_eq ((chiN alpha h).continuous_toFun.comp (continuous_apply i)) continuous_const
  have hrow : IsClosed {m : Fin (coreRank h) → DN alpha h |
      ∀ f : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]),
        nuFrame f m = nCoreMat T (nuFrame f (dnGen alpha h))} := by
    rw [Set.setOf_forall]
    refine isClosed_iInter fun f => isClosed_eq ?_ continuous_const
    apply continuous_pi
    intro i
    exact continuous_toAdd.comp (f.continuous_toFun.comp (continuous_apply i))
  have hmod : IsClosed {m : Fin (coreRank h) → DN alpha h |
      NPlaneModTwoIndep alpha h m} := by
    have heq : {m : Fin (coreRank h) → DN alpha h | NPlaneModTwoIndep alpha h m} =
        ⋂ (M : OpenNormalSubgroup (DN alpha h : Type)) (_ : M.toSubgroup.index = 2),
          ⋃ i : Fin (coreRank h),
            {m : Fin (coreRank h) → DN alpha h | m i ∈ (M.toSubgroup : Set (DN alpha h : Type))ᶜ} := by
      ext m
      simp only [NPlaneModTwoIndep, Set.mem_setOf_eq, Set.mem_iInter,
        Set.mem_iUnion, Set.mem_compl_iff, SetLike.mem_coe]
    rw [heq]
    exact isClosed_iInter fun M => isClosed_iInter fun _ =>
      isClosed_iUnion_of_finite fun i =>
        M.isOpen'.isClosed_compl.preimage (continuous_apply i)
  have hword : Continuous fun m : Fin (coreRank h) → DN alpha h => nRelWord alpha m := by
    simp only [nRelWord]
    refine Continuous.mul ?_ ?_
    · simp only [nWord, commP]
      fun_prop
    · simp only [handleWord]
      refine continuous_list_prod _ fun j _ => ?_
      simp only [commP]
      fun_prop
  exact hchi.inter (hrow.inter (hmod.inter
    ((isClosed_twoCentralSeries (G := (DN alpha h : Type)) k).preimage hword)))

theorem nPlaneStageSet_iInter_nonempty (T : Matrix (Fin 2) (Fin 2) ℤ_[2])
    (H : ∀ k, (nPlaneStageSet alpha h T k).Nonempty) :
    (⋂ k, nPlaneStageSet alpha h T k).Nonempty := by
  apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
  · intro k l
    exact ⟨max k l, nPlaneStageSet_antitone alpha h T (le_max_left k l),
      nPlaneStageSet_antitone alpha h T (le_max_right k l)⟩
  · exact H
  · exact fun k => (isClosed_nPlaneStageSet alpha h T k).isCompact
  · exact isClosed_nPlaneStageSet alpha h T

theorem nPlaneLift_surjective {m : Fin (coreRank h) → DN alpha h}
    (hrel : nRelWord alpha m = 1) (hm : NPlaneModTwoIndep alpha h m) :
    Function.Surjective (nLiftHom alpha h (isProP_DN alpha h) m hrel) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine surjective_of_forall_not_le_index_p (p := 2) (isProP_DN alpha h) _ ?_
  intro M hM hle
  obtain ⟨i, hi⟩ := hm M hM
  exact hi (hle ⟨dnGen alpha h i, nLiftHom_gen _ _ _ _ _ _⟩)

/-- The limit and automorphism promotion require no new group-lifting axiom.
The premise is exact-row upstairs nonemptiness at every depth, not merely
solvability after reducing the characters modulo a power of two. -/
theorem exists_nPlaneRealizes_of_stages (T : Matrix (Fin 2) (Fin 2) ℤ_[2])
    (H : ∀ k, (nPlaneStageSet alpha h T k).Nonempty) :
    ∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
      NPlaneRealizes alpha h Psi T := by
  obtain ⟨m, hm⟩ := nPlaneStageSet_iInter_nonempty alpha h T H
  have hall := Set.mem_iInter.mp hm
  obtain ⟨hchi, hrow, hgen, -⟩ := hall 0
  have hrel : nRelWord alpha m = 1 := by
    have hh : nRelWord alpha m ∈ ⨅ k, twoCentralSeries (DN alpha h : Type) k :=
      Subgroup.mem_iInf.mpr fun k => (hall k).2.2.2
    rwa [nPlane_iInf_twoCentralSeries alpha h, Subgroup.mem_bot] at hh
  let phi := nLiftHom alpha h (isProP_DN alpha h) m hrel
  have hsurj : Function.Surjective phi := nPlaneLift_surjective alpha h hrel hgen
  let Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type) :=
    continuousMulEquivOfBijective phi
      ⟨profinite_hopfian (nPlane_finsetGen alpha h) phi hsurj, hsurj⟩
  have hPsi : ∀ i, Psi (dnGen alpha h i) = m i :=
    nLiftHom_gen alpha h (isProP_DN alpha h) m hrel
  refine ⟨Psi, ?_, ?_⟩
  · have hc : (chiN alpha h).comp (autHom Psi) = chiN alpha h := by
      apply dn_hom_ext
      intro i
      change chiN alpha h (Psi (dnGen alpha h i)) = _
      rw [hPsi, hchi]
    exact fun x => congrArg (fun f : ContinuousMonoidHom _ _ => f x) hc
  · intro f
    rw [show (fun i => Psi (dnGen alpha h i)) = m from funext hPsi]
    exact hrow f

theorem nPlaneModTwoIndep_of_equiv
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type)) :
    NPlaneModTwoIndep alpha h (fun i => Psi (dnGen alpha h i)) := by
  intro M hM
  by_contra hc
  have hmem : ∀ i, Psi (dnGen alpha h i) ∈ M.toSubgroup :=
    fun i => not_not.mp fun hni => hc ⟨i, hni⟩
  have hclosed : IsClosed ((M.toSubgroup.comap (autHom Psi).toMonoidHom :
      Subgroup (DN alpha h : Type)) : Set (DN alpha h : Type)) := by
    rw [Subgroup.coe_comap]
    exact (Subgroup.isClosed_of_isOpen _ M.isOpen').preimage (autHom Psi).continuous_toFun
  have hle : Subgroup.closure (Set.range (dnGen alpha h)) ≤
      M.toSubgroup.comap (autHom Psi).toMonoidHom :=
    (Subgroup.closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact hmem i)
  have htop := Subgroup.topologicalClosure_minimal _ hle hclosed
  rw [dn_topGen alpha h] at htop
  have hMtop : M.toSubgroup = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro y
    have hy : Psi (Psi.symm y) ∈ M.toSubgroup := htop (Subgroup.mem_top (Psi.symm y))
    rwa [Psi.apply_symm_apply] at hy
  rw [hMtop, Subgroup.index_top] at hM
  omega

/-- This is an exact reduction, not a strengthening that assumes compatible
stage witnesses or discards the integral character rows. -/
theorem exists_nPlaneRealizes_iff_stages (T : Matrix (Fin 2) (Fin 2) ℤ_[2]) :
    (∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
      NPlaneRealizes alpha h Psi T) ↔
      ∀ k, (nPlaneStageSet alpha h T k).Nonempty := by
  refine ⟨?_, exists_nPlaneRealizes_of_stages alpha h T⟩
  rintro ⟨Psi, hPsi⟩ k
  refine ⟨fun i => Psi (dnGen alpha h i),
    fun i => hPsi.1 (dnGen alpha h i), hPsi.2,
    nPlaneModTwoIndep_of_equiv alpha h Psi, ?_⟩
  have hrel : nRelWord alpha (fun i => Psi (dnGen alpha h i)) = 1 := by
    have hm := map_nRelWord (autHom Psi) alpha (dnGen alpha h)
    rw [dn_relation, map_one] at hm
    exact hm.symm
  rw [hrel]
  exact one_mem _

/-- The strong scaling hypothesis has exactly this uniform upstairs supply
as its remaining obligation. No producer of the right side is asserted. -/
theorem nPlaneScalingHypothesis_iff_stages :
    NPlaneScalingHypothesis alpha h ↔
      ∀ kappa : ℤ_[2]ˣ, ∀ k, (nPlaneStageSet alpha h (nPlaneDet kappa) k).Nonempty := by
  unfold NPlaneScalingHypothesis
  exact forall_congr' fun kappa => exists_nPlaneRealizes_iff_stages alpha h (nPlaneDet kappa)

#print axioms NPlaneModTwoIndep
#print axioms nPlane_finsetGen
#print axioms nPlane_iInf_twoCentralSeries
#print axioms nPlaneStageSet
#print axioms nPlaneStageSet_antitone
#print axioms isClosed_nPlaneStageSet
#print axioms nPlaneStageSet_iInter_nonempty
#print axioms nPlaneLift_surjective
#print axioms exists_nPlaneRealizes_of_stages
#print axioms nPlaneModTwoIndep_of_equiv
#print axioms exists_nPlaneRealizes_iff_stages
#print axioms nPlaneScalingHypothesis_iff_stages

end
end GQ2.Dyadic.MarkedCore

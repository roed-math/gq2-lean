import GQ2.Dyadic.MarkedCore.NPlaneCompactness
import GQ2.Dyadic.MarkedCore.NFrameExists

/-!
# Exact full-abelianization compactness for arbitrary N markings

Unlike the plane-only stage predicate, this interface retains every canonical
abelianization coordinate, including torsion and arbitrary handle mixing.
It assumes nonempty exact-marking stages, not their existence. The compact
limit produces one actual continuous automorphism with the entire marking.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 GQ2.SectionThree Roe.Labute Multiplicative
open scoped GQ2.SectionThree.TopAbInstances

/-- One actual N automorphism preserves orientation and realizes all specified
canonical abelianization columns. No identity-handle restriction is present. -/
def NFullFrameRealizes {alpha h : ℕ} (ha : 2 ≤ alpha)
    (Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type))
    (mark : Fin (coreRank h) → NFrameModel h) : Prop :=
  (∀ x, chiN alpha h (Psi x) = chiN alpha h x) ∧
    ∀ i, nPhiHom ha h (abMk (Psi (dnGen alpha h i))) = mark i

/-- Exact orientation, full marking and Frattini generation at every stage;
only the literal relator condition depends on the filtration depth. -/
def nFullFrameStageSet {alpha h : ℕ} (ha : 2 ≤ alpha)
    (mark : Fin (coreRank h) → NFrameModel h) (k : ℕ) :
    Set (Fin (coreRank h) → DN alpha h) :=
  {m | (∀ i, chiN alpha h (m i) = chiN alpha h (dnGen alpha h i)) ∧
    (∀ i, nPhiHom ha h (abMk (m i)) = mark i) ∧
    NPlaneModTwoIndep alpha h m ∧
    nRelWord alpha m ∈ twoCentralSeries (DN alpha h : Type) k}

theorem nFullFrameStageSet_antitone {alpha h : ℕ} (ha : 2 ≤ alpha)
    (mark : Fin (coreRank h) → NFrameModel h) :
    Antitone (nFullFrameStageSet ha mark) := by
  intro k l hkl m hm
  exact ⟨hm.1, hm.2.1, hm.2.2.1,
    twoCentralSeries_antitone (G := (DN alpha h : Type)) hkl hm.2.2.2⟩

set_option synthInstance.maxSize 256 in
theorem isClosed_nFullFrameStageSet {alpha h : ℕ} (ha : 2 ≤ alpha)
    (mark : Fin (coreRank h) → NFrameModel h) (k : ℕ) :
    IsClosed (nFullFrameStageSet ha mark k) := by
  have hchi : IsClosed {m : Fin (coreRank h) → DN alpha h |
      ∀ i, chiN alpha h (m i) = chiN alpha h (dnGen alpha h i)} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun i =>
      isClosed_eq ((chiN alpha h).continuous_toFun.comp (continuous_apply i)) continuous_const
  have hrow : IsClosed {m : Fin (coreRank h) → DN alpha h |
      ∀ i, nPhiHom ha h (abMk (m i)) = mark i} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_eq
      ((continuous_nPhiHom ha h).comp (continuous_abMk.comp (continuous_apply i)))
      continuous_const
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

theorem nFullFrameStageSet_iInter_nonempty {alpha h : ℕ} (ha : 2 ≤ alpha)
    (mark : Fin (coreRank h) → NFrameModel h)
    (H : ∀ k, (nFullFrameStageSet ha mark k).Nonempty) :
    (⋂ k, nFullFrameStageSet ha mark k).Nonempty := by
  apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
  · intro k l
    exact ⟨max k l, nFullFrameStageSet_antitone ha mark (le_max_left k l),
      nFullFrameStageSet_antitone ha mark (le_max_right k l)⟩
  · exact H
  · exact fun k => (isClosed_nFullFrameStageSet ha mark k).isCompact
  · exact isClosed_nFullFrameStageSet ha mark

/-- Actual full-frame automorphisms follow from exact upstairs stage supply.
There is no restriction to a plane matrix, no lost torsion row and no
compatible-choice assumption on the supplied witnesses. -/
theorem exists_nFullFrameRealizes_of_stages {alpha h : ℕ} (ha : 2 ≤ alpha)
    (mark : Fin (coreRank h) → NFrameModel h)
    (H : ∀ k, (nFullFrameStageSet ha mark k).Nonempty) :
    ∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
      NFullFrameRealizes ha Psi mark := by
  obtain ⟨m, hm⟩ := nFullFrameStageSet_iInter_nonempty ha mark H
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
  · intro i
    rw [hPsi]
    exact hrow i

theorem exists_nFullFrameRealizes_iff_stages {alpha h : ℕ} (ha : 2 ≤ alpha)
    (mark : Fin (coreRank h) → NFrameModel h) :
    (∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
      NFullFrameRealizes ha Psi mark) ↔
      ∀ k, (nFullFrameStageSet ha mark k).Nonempty := by
  refine ⟨?_, exists_nFullFrameRealizes_of_stages ha mark⟩
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

#print axioms NFullFrameRealizes
#print axioms nFullFrameStageSet
#print axioms nFullFrameStageSet_antitone
#print axioms isClosed_nFullFrameStageSet
#print axioms nFullFrameStageSet_iInter_nonempty
#print axioms exists_nFullFrameRealizes_of_stages
#print axioms exists_nFullFrameRealizes_iff_stages

end
end GQ2.Dyadic.MarkedCore

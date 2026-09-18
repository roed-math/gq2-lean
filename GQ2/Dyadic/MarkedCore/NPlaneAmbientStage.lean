import GQ2.Dyadic.MarkedCore.NPlaneFreeStageTransfer
import GQ2.Dyadic.MarkedCore.NPlaneCrossedDefect
import GQ2.Dyadic.Instances.EvenFamilyConstruct
import GQ2.Dyadic.Instances.StageAbstractionEvenDerivKer

/-!
# Unrestricted actual free-N stages in arbitrary rank

The old all-rank even derivation criterion applies on the free pro-two group
with a dummy constant-one StageWord. The dummy word supplies only the unrelated
Tuple container; the class tested by the criterion is the actual nonzero-target
N-relator defect. Coordinate crossed maps exist on every free basis, and both
actual relator words vanish under these maps at the canonical orientation.

The final theorem supplies arbitrary depth corrections, without claiming that
they preserve orientation or ordinary rows. Those are separate refinement steps.
-/

namespace GQ2.Dyadic.MarkedCore.NPlaneAmbientStage
noncomputable section
open GQ2 Roe.Labute FoxH StageGeneric EvenFamily
open GQ2.Dyadic.LSquare (IsChiShadowDeriv)

def oneWord (N : ℕ) : StageWord N where
  word _ := 1
  map_word φ _ := map_one φ
  zshift _ _ _ := rfl

theorem orientation_aut {α h : ℕ}
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (he : ∀ i, freeNOrientation α h (e (freeTwoRankGen (coreRank h) i)) =
      freeNOrientation α h (freeTwoRankGen (coreRank h) i))
    (z : FreeTwoRank (coreRank h)) :
    freeNOrientation α h (e z) = freeNOrientation α h z := by
  have H : (freeNOrientation α h).comp (autHom e) = freeNOrientation α h := by
    apply presPro2_hom_ext
    exact he
  exact DFunLike.congr_fun H z

def coordinateDeriv {α h : ℕ} (hα : 1 ≤ α) (N : ℕ) (hN : 1 ≤ N)
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (i : Fin (coreRank h)) : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) (WL N) :=
  ((evenFamDerivModelN α h hα hN (fun j => if j=i then 1 else 0)).comp
    (freeNProjection α h)).comp (autHom e.symm)

theorem coordinateDeriv_gen {α h : ℕ} (hα : 1 ≤ α) (N : ℕ) (hN : 1 ≤ N)
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type)) (i j : Fin (coreRank h)) :
    coordinateDeriv hα N hN e i (e (freeTwoRankGen (coreRank h) j)) =
      redWL N ⟨if j=i then 1 else 0, vN α j⟩ := by
  change evenFamDerivModelN α h hα hN _ (freeNProjection α h (e.symm (e _))) = _
  rw [e.symm_apply_apply, freeNProjection_gen, evenFamDerivModelN_gen]

theorem coordinateDeriv_base {α h : ℕ} (hα : 1 ≤ α) (N : ℕ) (hN : 1 ≤ N)
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (he : ∀ i, freeNOrientation α h (e (freeTwoRankGen (coreRank h) i)) =
      freeNOrientation α h (freeTwoRankGen (coreRank h) i))
    (i : Fin (coreRank h)) : IsChiShadowDeriv (freeNOrientation α h)
      (coordinateDeriv hα N hN e i) := by
  intro z
  change (evenFamDerivModelN α h hα hN _ (freeNProjection α h (e.symm z))).g = _
  rw [evenFamDerivModelN_isChiShadow, freeNProjection_orientation]
  have H := orientation_aut e he (e.symm z)
  rw [e.apply_symm_apply] at H
  rw [← H]

theorem finite_nRelWord_eq_one {α h N : ℕ} (hα : 1 ≤ α)
    (m : Fin (coreRank h) → WL N)
    (hm : ∀ i, (m i).g = Units.map (PadicInt.toZModPow N).toMonoidHom (vN α i)) :
    nRelWord α m = 1 := by
  let c : Fin (coreRank h) → ℤ_[2] := fun i => ((m i).u.val : ℤ_[2])
  have H : m = fun i => redWL N ⟨c i, vN α i⟩ := by
    funext i
    apply WordLift.ext
    · change (m i).u = PadicInt.toZModPow N ((m i).u.val : ℤ_[2])
      simp
    · exact hm i
  rw [H, ← map_nRelWord, evenFam_nRelWord_wordLift α hα, map_one]

theorem orientation_gen_vN (α h : ℕ) (i : Fin (coreRank h)) :
    freeNOrientation α h (freeTwoRankGen (coreRank h) i) = vN α i := by
  rw [← freeNProjection_orientation, freeNProjection_gen, evenFam_chiN_dnGen]

theorem coordinateDeriv_defect {α h : ℕ} (hα : 1 ≤ α) (N : ℕ) (hN : 1 ≤ N)
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (he : ∀ i, freeNOrientation α h (e (freeTwoRankGen (coreRank h) i)) =
      freeNOrientation α h (freeTwoRankGen (coreRank h) i))
    (i : Fin (coreRank h)) :
    coordinateDeriv hα N hN e i
      (nRelWord α (fun j => e (freeTwoRankGen (coreRank h) j)) *
        (nRelWord α (freeTwoRankGen (coreRank h)))⁻¹) = 1 := by
  rw [map_mul, map_inv, map_nRelWord, map_nRelWord]
  have H (y : Fin (coreRank h) → FreeTwoRank (coreRank h))
      (hy : ∀ j, freeNOrientation α h (y j) = vN α j) :
      nRelWord α (fun j => coordinateDeriv hα N hN e i (y j)) = 1 := by
    apply finite_nRelWord_eq_one hα
    intro j
    rw [coordinateDeriv_base hα N hN e he i, hy]
  rw [H _ (fun j => (he j).trans (orientation_gen_vN α h j)),
    H _ (orientation_gen_vN α h), inv_one, mul_one]

theorem free_finite_gen (N : ℕ) :
    ∃ s : Finset (FreeTwoRank N : Type),
      (Subgroup.closure (s : Set (FreeTwoRank N : Type))).topologicalClosure = ⊤ := by
  classical
  refine ⟨Finset.univ.image (freeTwoRankGen N), ?_⟩
  have ht : (↑(Finset.univ.image (freeTwoRankGen N)) : Set (FreeTwoRank N : Type)) =
      Set.range (freeTwoRankGen N) := by simp
  rw [ht]
  exact presPro2_topGen _

theorem basis_generates {h : ℕ}
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type)) (k : ℕ) :
    Subgroup.closure (Set.range fun i => levelMk (FreeTwoRank (coreRank h) : Type) k
      (e (freeTwoRankGen (coreRank h) i))) = ⊤ := by
  haveI := discreteTopology_levelQuot (FreeTwoRank (coreRank h) : Type)
    (free_finite_gen _) (isProP_presPro2 1) k
  let f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
      (levelQuot (FreeTwoRank (coreRank h) : Type) k) :=
    { toMonoidHom := (levelMk _ k).comp e.toMonoidHom
      continuous_toFun := (continuous_levelMk _ k).comp e.continuous }
  have hsurj : Function.Surjective f := (levelMk_surjective _ k).comp e.surjective
  have H := hsurj.denseRange.topologicalClosure_map_subgroup f.continuous_toFun
    (show (Subgroup.closure (Set.range (freeTwoRankGen (coreRank h)))).topologicalClosure = ⊤
      from presPro2_topGen 1)
  rw [MonoidHom.map_closure, ← Set.range_comp] at H
  have hc := Subgroup.topologicalClosure_minimal
    (Subgroup.closure (Set.range (f.toMonoidHom ∘ freeTwoRankGen (coreRank h))))
    le_rfl (isClosed_discrete _)
  rw [H] at hc
  exact top_unique hc

def basisTuple {α h : ℕ} (k : ℕ)
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (he : ∀ i, freeNOrientation α h (e (freeTwoRankGen (coreRank h) i)) =
      freeNOrientation α h (freeTwoRankGen (coreRank h) i)) :
    Tuple (oneWord (coreRank h)) (vN α) (FreeTwoRank (coreRank h) : Type)
      (freeNOrientation α h) k where
  generators i := levelMk _ k (e (freeTwoRankGen (coreRank h) i))
  rows i := ⟨e (freeTwoRankGen (coreRank h) i),
    (he i).trans (orientation_gen_vN α h i), rfl⟩
  relation := rfl
  topGen := basis_generates e k

def basisFamily {α h : ℕ} (hα : 1 ≤ α) (k : ℕ)
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (he : ∀ i, freeNOrientation α h (e (freeTwoRankGen (coreRank h) i)) =
      freeNOrientation α h (freeTwoRankGen (coreRank h) i)) :
    EvenKernelDerivationFamily (basisTuple k e he) where
  lifts i := e (freeTwoRankGen (coreRank h) i)
  lifts_chi i := (he i).trans (orientation_gen_vN α h i)
  lifts_level _ := rfl
  deriv i _ := coordinateDeriv hα (k+1) (by omega) e i
  deriv_base i _ := coordinateDeriv_base hα (k+1) (by omega) e he i
  deriv_diag i _ := by
    rw [coordinateDeriv_gen]
    change ¬ (2 : ZMod (2^(k+1))) ∣ PadicInt.toZModPow (k+1) (if i=i then 1 else 0)
    simp only [ite_true, map_one]
    rw [evenFam_two_dvd_iff_castHom_eq_zero (by omega), map_one]
    exact one_ne_zero
  deriv_off i _ j _ hj := by
    rw [coordinateDeriv_gen]
    change (2 : ZMod (2^(k+1))) ∣ PadicInt.toZModPow (k+1) (if j=i then 1 else 0)
    simp [hj]

theorem defect_mem_rawSpan {α h k : ℕ} (hα : 2 ≤ α) (hk : 3 ≤ k)
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (he : ∀ i, freeNOrientation α h (e (freeTwoRankGen (coreRank h) i)) =
      freeNOrientation α h (freeTwoRankGen (coreRank h) i))
    (herr : nRelWord α (fun i => e (freeTwoRankGen (coreRank h) i)) *
      (nRelWord α (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) k) :
    levelMk (FreeTwoRank (coreRank h) : Type) (k+1)
      (nRelWord α (fun i => e (freeTwoRankGen (coreRank h) i)) *
        (nRelWord α (freeTwoRankGen (coreRank h)))⁻¹) ∈
      evenRawShiftSpan (fun i => canonLift _ k ((basisTuple k e he).generators i)) hk := by
  apply evenDeriv_mem_rawShiftSpan_of_forall_derivKer (free_finite_gen _)
    (isProP_presPro2 1) hk (basisFamily (by omega) k e he)
    (fun i hi => evenKernel_vN_sub_one_dvd_four i hi)
    (evenKernel_vN_diagonal_add_one_dvd_four hα)
  · exact ⟨_, herr, rfl⟩
  · intro i hi
    refine ⟨_, herr, rfl, ?_⟩
    change (2 : ZMod (2^(k+1))) ^ k ∣
      (coordinateDeriv (by omega) (k+1) (by omega) e i _).u
    rw [coordinateDeriv_defect (by omega) (k+1) (by omega) e he i]
    exact dvd_zero _

theorem exists_ambient_stage {α h k : ℕ} (hα : 2 ≤ α) (hk : 3 ≤ k)
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (he : ∀ i, freeNOrientation α h (e (freeTwoRankGen (coreRank h) i)) =
      freeNOrientation α h (freeTwoRankGen (coreRank h) i))
    (herr : nRelWord α (fun i => e (freeTwoRankGen (coreRank h) i)) *
      (nRelWord α (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) k) :
    ∃ t : Fin (coreRank h) → FreeTwoRank (coreRank h),
      (∀ i, t i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (k-1)) ∧
      nRelWord α (fun i => e (freeTwoRankGen (coreRank h) i) * t i) *
        (nRelWord α (freeTwoRankGen (coreRank h)))⁻¹ ∈
          twoCentralSeries (FreeTwoRank (coreRank h) : Type) (k+1) := by
  let f := levelMk (FreeTwoRank (coreRank h) : Type) (k+1)
  let y := fun i => e (freeTwoRankGen (coreRank h) i)
  let x := freeTwoRankGen (coreRank h)
  have H := (evenRawShiftSpan _ hk).inv_mem (defect_mem_rawSpan hα hk e he herr)
  obtain ⟨z, ⟨V, hV⟩, hz⟩ := H
  subst z
  change evenRawDbarWord (fun i => canonLift _ k ((basisTuple k e he).generators i))
    V.correction = (f (nRelWord α y * (nRelWord α x)⁻¹))⁻¹ at hz
  rw [(basisFamily (by omega) k e he).evenDeriv_dbarWord_eq hk V.depth] at hz
  change evenRawDbarWord (fun i => f (y i)) V.correction =
    (f (nRelWord α y * (nRelWord α x)⁻¹))⁻¹ at hz
  choose t ht hp using V.depth
  refine ⟨t, ht, ?_⟩
  have htm : (fun i => f (t i)) = V.correction := funext hp
  have hshift := evenRawStageShift_n hα (by omega) h k hk
    (fun i => f (y i)) V.correction V.depth
  change (nRelWord α (fun i => f (y i)))⁻¹ *
    nRelWord α (fun i => f (y i) * V.correction i) =
      evenRawDbarWord (fun i => f (y i)) V.correction at hshift
  rw [← htm] at hshift
  simp only [← map_mul, ← map_nRelWord] at hshift
  rw [htm, hz] at hshift
  have hnew : f (nRelWord α (fun i => y i*t i)) =
      f (nRelWord α y) * (f (nRelWord α y * (nRelWord α x)⁻¹))⁻¹ := by
    exact (inv_mul_eq_iff_eq_mul).mp hshift
  have hcentral : f (nRelWord α y * (nRelWord α x)⁻¹) ∈
      zLayer (FreeTwoRank (coreRank h) : Type) k := ⟨_, herr, rfl⟩
  have hc := (zLayer_commute hcentral (f (nRelWord α y))).inv_left
  rw [← QuotientGroup.eq_one_iff]
  change f _ = 1
  rw [map_mul, map_inv, hnew, ← hc.eq, mul_assoc]
  simp only [map_mul, map_inv, x]
  group

#print axioms oneWord
#print axioms orientation_aut
#print axioms coordinateDeriv
#print axioms coordinateDeriv_gen
#print axioms coordinateDeriv_base
#print axioms finite_nRelWord_eq_one
#print axioms orientation_gen_vN
#print axioms coordinateDeriv_defect
#print axioms free_finite_gen
#print axioms basis_generates
#print axioms basisTuple
#print axioms basisFamily
#print axioms defect_mem_rawSpan
#print axioms exists_ambient_stage
end
end GQ2.Dyadic.MarkedCore.NPlaneAmbientStage

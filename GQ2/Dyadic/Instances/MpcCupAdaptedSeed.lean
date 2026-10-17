/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedLevelThree
import GQ2.Dyadic.Instances.M0C0PivotAutomorphism

/-!
# An unconditional cup-adapted one-handle seed

W201 reduced balanced depth three to a finite cup-adapted seed.  Here the four compact
letters are lifted, then their two handle coordinates are cleared modulo two.  The universal
`C + 2B` row makes the remaining `C`-handle coordinates even.  The cleared rank-six marking
therefore pulls every mod-two character back through the compact automorphism, and invariance
of `evenCupForm` supplies cup adaptation.

Thus every compact M6 witness produces a cup-adapted one-handle seed and an inhabitant of
`oneHandleBalancedSet Psi0 3`.  This closes the finite W201 boundary without assuming either
of the false fixed-`C` bracket-surjectivity statements; propagation beyond depth three remains
a separate graded problem.
-/

namespace GQ2.Dyadic.Instances.MpcCupAdaptedSeed

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.EvenModel
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedRowLift
open GQ2.Dyadic.Instances.MpcBalancedLevelThree
open GQ2.Dyadic.Instances.M0C0PivotAutomorphism

private theorem one_le_two : 1 ≤ 2 := by omega

private def modTwoCoordinate (h : ℕ) (x : DM 2 h)
    (i : Fin (coreRank h)) : ZMod 2 :=
  toAdd (dmCoordinateCharacter 2 h one_le_two (Pi.single i 1) x)

private theorem dmCoordinateCharacter_add
    {h : ℕ} (v w : Fin (coreRank h) → ZMod 2) :
    dmCoordinateCharacter 2 h one_le_two (v + w) =
      dmCoordinateCharacter 2 h one_le_two v *
        dmCoordinateCharacter 2 h one_le_two w := by
  apply dm_hom_ext
  intro i
  simp [dmCoordinateCharacter_gen]

private theorem dmCoordinateCharacter_zero {h : ℕ} :
    dmCoordinateCharacter 2 h one_le_two 0 = 1 := by
  apply dm_hom_ext
  intro i
  simp [dmCoordinateCharacter_gen]

private theorem dmCoordinateCharacter_sum
    {h : ℕ} (v : Fin (coreRank h) → ZMod 2)
    (s : Finset (Fin (coreRank h))) :
    dmCoordinateCharacter 2 h one_le_two
        (∑ i ∈ s, Pi.single i (v i)) =
      ∏ i ∈ s, dmCoordinateCharacter 2 h one_le_two (Pi.single i (v i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dmCoordinateCharacter_zero]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, Finset.prod_insert ha]
      rw [dmCoordinateCharacter_add, ih]

private theorem dmCoordinateCharacter_single_eval
    {h : ℕ} (v : Fin (coreRank h) → ZMod 2) (x : DM 2 h)
    (i : Fin (coreRank h)) :
    toAdd (dmCoordinateCharacter 2 h one_le_two (Pi.single i (v i)) x) =
      v i * modTwoCoordinate h x i := by
  have hval : (v i).val = 0 ∨ (v i).val = 1 := by
    have := ZMod.val_lt (v i)
    omega
  rcases hval with hval | hval
  · have hvi : v i = 0 := by
      apply ZMod.val_injective 2
      simpa using hval
    rw [hvi]
    have hzero : dmCoordinateCharacter 2 h one_le_two
        (Pi.single i (0 : ZMod 2)) = 1 := by
      apply dm_hom_ext
      intro j
      simp [dmCoordinateCharacter_gen]
    rw [hzero]
    simp
  · have hvi : v i = 1 := by
      apply ZMod.val_injective 2
      exact hval.trans (by decide)
    rw [hvi]
    simp [modTwoCoordinate]

private theorem toAdd_fintype_prod {I : Type*} [Fintype I]
    (f : I → Multiplicative (ZMod 2)) :
    toAdd (∏ i, f i) = ∑ i, toAdd (f i) := by
  classical
  have hs : ∀ s : Finset I,
      toAdd (∏ i ∈ s, f i) = ∑ i ∈ s, toAdd (f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simp only [Finset.prod_insert ha, Finset.sum_insert ha]
        rw [toAdd_mul, ih]
  exact hs Finset.univ

private theorem continuousHom_fintype_prod_apply
    {I G A : Type*} [Fintype I] [TopologicalSpace G] [Monoid G]
    [TopologicalSpace A] [CommMonoid A] [ContinuousMul A]
    (f : I → ContinuousMonoidHom G A) (x : G) :
    (∏ i, f i) x = ∏ i, f i x := by
  classical
  have hs : ∀ s : Finset I,
      (∏ i ∈ s, f i) x = ∏ i ∈ s, f i x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simp only [Finset.prod_insert ha, ContinuousMonoidHom.mul_apply, ih]
  exact hs Finset.univ

private theorem character_eval_eq_dot
    {h : ℕ} (c : ContinuousMonoidHom (DM 2 h) (Multiplicative (ZMod 2)))
    (x : DM 2 h) :
    toAdd (c x) =
      ∑ i, toAdd (c (dmGen 2 h i)) * modTwoCoordinate h x i := by
  classical
  let v : Fin (coreRank h) → ZMod 2 := fun i => toAdd (c (dmGen 2 h i))
  have hc : c = dmCoordinateCharacter 2 h one_le_two v := by
    apply dm_hom_ext
    intro i
    rw [dmCoordinateCharacter_gen]
    exact (ofAdd_toAdd _).symm
  change toAdd (c x) = ∑ i, v i * modTwoCoordinate h x i
  rw [hc]
  have hv : v = ∑ i, Pi.single i (v i) := by
    ext j
    simp
  have hchar : dmCoordinateCharacter 2 h one_le_two
      (∑ i, Pi.single i (v i)) =
        ∏ i, dmCoordinateCharacter 2 h one_le_two (Pi.single i (v i)) := by
    simpa using dmCoordinateCharacter_sum v Finset.univ
  rw [← hv] at hchar
  rw [hchar]
  rw [continuousHom_fintype_prod_apply]
  rw [toAdd_fintype_prod]
  apply Finset.sum_congr rfl
  intro i _
  exact dmCoordinateCharacter_single_eval v x i

private abbrev U : DM 2 1 := dmGen 2 1 (handleIdxU (0 : Fin 1))
private abbrev V : DM 2 1 := dmGen 2 1 (handleIdxV (0 : Fin 1))

private def clearModTwoHandles (x : DM 2 1) : DM 2 1 :=
  U ^ (modTwoCoordinate 1 x (handleIdxU 0)).val *
    V ^ (modTwoCoordinate 1 x (handleIdxV 0)).val * x

private theorem dmForgetHandles_clearModTwoHandles (x : DM 2 1) :
    dmForgetHandles 2 1 (clearModTwoHandles x) = dmForgetHandles 2 1 x := by
  simp [clearModTwoHandles, dmForgetHandles_handleU, dmForgetHandles_handleV]

set_option backward.isDefEq.respectTransparency false in
private theorem modTwoCoordinate_clearModTwoHandles
    (x : DM 2 1) (i : Fin (coreRank 1)) :
    modTwoCoordinate 1 (clearModTwoHandles x) i =
      if i = handleIdxU 0 ∨ i = handleIdxV 0 then 0
      else modTwoCoordinate 1 x i := by
  have huval : (modTwoCoordinate 1 x (handleIdxU 0)).val = 0 ∨
      (modTwoCoordinate 1 x (handleIdxU 0)).val = 1 := by
    have := ZMod.val_lt (modTwoCoordinate 1 x (handleIdxU 0))
    omega
  have hvval : (modTwoCoordinate 1 x (handleIdxV 0)).val = 0 ∨
      (modTwoCoordinate 1 x (handleIdxV 0)).val = 1 := by
    have := ZMod.val_lt (modTwoCoordinate 1 x (handleIdxV 0))
    omega
  rcases huval with huval | huval <;> rcases hvval with hvval | hvval
  all_goals
    fin_cases i <;>
      simp [clearModTwoHandles, modTwoCoordinate,
        dmCoordinateCharacter_gen, handleIdxU, handleIdxV,
        coreRank, map_mul, map_pow, toAdd_mul] <;>
      exact CharTwo.add_self_eq_zero _

private def coreCast (i : Fin (coreRank 0)) : Fin (coreRank 1) :=
  Fin.castLE (by simp [coreRank]) i

set_option backward.isDefEq.respectTransparency false in
private theorem dmCoordinateCharacter_core_comp_forget
    (i : Fin (coreRank 0)) :
    dmCoordinateCharacter 2 1 one_le_two (Pi.single (coreCast i) 1) =
      (dmCoordinateCharacter 2 0 one_le_two (Pi.single i 1)).comp
        (dmForgetHandles 2 1) := by
  apply dm_hom_ext
  intro j
  rcases mIdx_cases j with rfl | rfl | rfl | rfl | ⟨k, rfl⟩
  · change dmCoordinateCharacter 2 1 one_le_two (Pi.single (coreCast i) 1)
        (dmA 2 1) = dmCoordinateCharacter 2 0 one_le_two (Pi.single i 1)
          (dmForgetHandles 2 1 (dmA 2 1))
    rw [dmForgetHandles_dmA]
    rw [show dmA 2 1 = dmGen 2 1 0 from rfl,
      show dmA 2 0 = dmGen 2 0 0 from rfl,
      dmCoordinateCharacter_gen, dmCoordinateCharacter_gen]
    fin_cases i <;> simp [coreCast, Pi.single_apply, coreRank]
  · change dmCoordinateCharacter 2 1 one_le_two (Pi.single (coreCast i) 1)
        (dmB 2 1) = dmCoordinateCharacter 2 0 one_le_two (Pi.single i 1)
          (dmForgetHandles 2 1 (dmB 2 1))
    rw [dmForgetHandles_dmB]
    rw [show dmB 2 1 = dmGen 2 1 1 from rfl,
      show dmB 2 0 = dmGen 2 0 1 from rfl,
      dmCoordinateCharacter_gen, dmCoordinateCharacter_gen]
    fin_cases i <;> simp [coreCast, Pi.single_apply, coreRank]
  · change dmCoordinateCharacter 2 1 one_le_two (Pi.single (coreCast i) 1)
        (dmC 2 1) = dmCoordinateCharacter 2 0 one_le_two (Pi.single i 1)
          (dmForgetHandles 2 1 (dmC 2 1))
    rw [dmForgetHandles_dmC]
    rw [show dmC 2 1 = dmGen 2 1 2 from rfl,
      show dmC 2 0 = dmGen 2 0 2 from rfl,
      dmCoordinateCharacter_gen, dmCoordinateCharacter_gen]
    fin_cases i <;> simp [coreCast, Pi.single_apply, coreRank]
  · change dmCoordinateCharacter 2 1 one_le_two (Pi.single (coreCast i) 1)
        (dmD 2 1) = dmCoordinateCharacter 2 0 one_le_two (Pi.single i 1)
          (dmForgetHandles 2 1 (dmD 2 1))
    rw [dmForgetHandles_dmD]
    rw [show dmD 2 1 = dmGen 2 1 3 from rfl,
      show dmD 2 0 = dmGen 2 0 3 from rfl,
      dmCoordinateCharacter_gen, dmCoordinateCharacter_gen]
    fin_cases i <;> simp [coreCast, Pi.single_apply, coreRank]
  · rcases mHandleCoord_cases k with ⟨l, rfl⟩ | ⟨l, rfl⟩
    · fin_cases l
      change dmCoordinateCharacter 2 1 one_le_two (Pi.single (coreCast i) 1)
        U = dmCoordinateCharacter 2 0 one_le_two (Pi.single i 1)
          (dmForgetHandles 2 1 U)
      rw [dmForgetHandles_handleU]
      rw [show U = dmGen 2 1 (handleIdxU (0 : Fin 1)) from rfl,
        dmCoordinateCharacter_gen, map_one]
      fin_cases i <;> simp [coreCast, Pi.single_apply, coreRank] <;>
        exact handleIdxU_ne_of_val_lt 0 (by simp [coreRank])
    · fin_cases l
      change dmCoordinateCharacter 2 1 one_le_two (Pi.single (coreCast i) 1)
        V = dmCoordinateCharacter 2 0 one_le_two (Pi.single i 1)
          (dmForgetHandles 2 1 V)
      rw [dmForgetHandles_handleV]
      rw [show V = dmGen 2 1 (handleIdxV (0 : Fin 1)) from rfl,
        dmCoordinateCharacter_gen, map_one]
      fin_cases i <;> simp [coreCast, Pi.single_apply, coreRank] <;>
        exact handleIdxV_ne_of_val_lt 0 (by simp [coreRank])

private theorem modTwoCoordinate_forget (x : DM 2 1)
    (i : Fin (coreRank 0)) :
    modTwoCoordinate 0 (dmForgetHandles 2 1 x) i =
      modTwoCoordinate 1 x (coreCast i) := by
  have h := DFunLike.congr_fun (dmCoordinateCharacter_core_comp_forget i) x
  exact congrArg toAdd h.symm

private def coreCharacter
    (c : ContinuousMonoidHom (DM 2 1) (Multiplicative (ZMod 2))) :
    ContinuousMonoidHom (DM 2 0) (Multiplicative (ZMod 2)) :=
  dmCoordinateCharacter 2 0 one_le_two
    (fun i => toAdd (c (dmGen 2 1 (coreCast i))))

private theorem character_eval_eq_core_of_handle_zero
    (c : ContinuousMonoidHom (DM 2 1) (Multiplicative (ZMod 2)))
    (x : DM 2 1)
    (hU : modTwoCoordinate 1 x (handleIdxU 0) = 0)
    (hV : modTwoCoordinate 1 x (handleIdxV 0) = 0) :
    toAdd (c x) = toAdd (coreCharacter c (dmForgetHandles 2 1 x)) := by
  rw [character_eval_eq_dot, character_eval_eq_dot]
  simp only [coreCharacter, dmCoordinateCharacter_gen, toAdd_ofAdd]
  have h0 := modTwoCoordinate_forget x (0 : Fin (coreRank 0))
  have h1 := modTwoCoordinate_forget x (1 : Fin (coreRank 0))
  have h2 := modTwoCoordinate_forget x (2 : Fin (coreRank 0))
  have h3 := modTwoCoordinate_forget x (3 : Fin (coreRank 0))
  simp [coreRank, coreCast] at h0 h1 h2 h3
  change modTwoCoordinate 1 x
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0)))) = 0 at hU
  change modTwoCoordinate 1 x
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))) = 0 at hV
  change modTwoCoordinate 0 (dmForgetHandles 2 1 x) (0 : Fin 4) =
    modTwoCoordinate 1 x (0 : Fin 6) at h0
  change modTwoCoordinate 0 (dmForgetHandles 2 1 x) (Fin.succ 0) =
    modTwoCoordinate 1 x (Fin.succ 0) at h1
  change modTwoCoordinate 0 (dmForgetHandles 2 1 x) (Fin.succ (Fin.succ 0)) =
    modTwoCoordinate 1 x (Fin.succ (Fin.succ 0)) at h2
  change modTwoCoordinate 0 (dmForgetHandles 2 1 x)
      (Fin.succ (Fin.succ (Fin.succ 0))) =
    modTwoCoordinate 1 x (Fin.succ (Fin.succ (Fin.succ 0))) at h3
  change (∑ i : Fin 6,
      toAdd (c (dmGen 2 1 i)) * modTwoCoordinate 1 x i) =
    ∑ i : Fin 4,
      toAdd (c (dmGen 2 1 (coreCast i))) *
        modTwoCoordinate 0 (dmForgetHandles 2 1 x) i
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  have hc0 : coreCast (0 : Fin 4) = (0 : Fin 6) := rfl
  have hc1 : coreCast (Fin.succ 0 : Fin 4) = (Fin.succ 0 : Fin 6) := rfl
  have hc2 : coreCast (Fin.succ (Fin.succ 0) : Fin 4) =
      (Fin.succ (Fin.succ 0) : Fin 6) := rfl
  have hc3 : coreCast (Fin.succ (Fin.succ (Fin.succ 0)) : Fin 4) =
      (Fin.succ (Fin.succ (Fin.succ 0)) : Fin 6) := rfl
  simp only [hc0, hc1, hc2, hc3]
  rw [h0, h1, h2, h3, hU, hV]
  simp

private theorem standardHandleMark_cupAdapted_of_core_zero
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    {a b cc d : DM 2 1}
    (ha : dmForgetHandles 2 1 a = Psi0 (dmA 2 0))
    (hb : dmForgetHandles 2 1 b = Psi0 (dmB 2 0))
    (hc : dmForgetHandles 2 1 cc = Psi0 (dmC 2 0))
    (hd : dmForgetHandles 2 1 d = Psi0 (dmD 2 0))
    (haU : modTwoCoordinate 1 a (handleIdxU 0) = 0)
    (haV : modTwoCoordinate 1 a (handleIdxV 0) = 0)
    (hbU : modTwoCoordinate 1 b (handleIdxU 0) = 0)
    (hbV : modTwoCoordinate 1 b (handleIdxV 0) = 0)
    (hcU : modTwoCoordinate 1 cc (handleIdxU 0) = 0)
    (hcV : modTwoCoordinate 1 cc (handleIdxV 0) = 0)
    (hdU : modTwoCoordinate 1 d (handleIdxU 0) = 0)
    (hdV : modTwoCoordinate 1 d (handleIdxV 0) = 0) :
    OneHandleCupAdapted (standardHandleMark a b cc d) := by
  intro c e
  let c0 := coreCharacter c
  let e0 := coreCharacter e
  have hca : toAdd (c a) = toAdd (c0 (Psi0 (dmA 2 0))) := by
    rw [← ha]
    exact character_eval_eq_core_of_handle_zero c a haU haV
  have hcb : toAdd (c b) = toAdd (c0 (Psi0 (dmB 2 0))) := by
    rw [← hb]
    exact character_eval_eq_core_of_handle_zero c b hbU hbV
  have hcc : toAdd (c cc) = toAdd (c0 (Psi0 (dmC 2 0))) := by
    rw [← hc]
    exact character_eval_eq_core_of_handle_zero c cc hcU hcV
  have hcd : toAdd (c d) = toAdd (c0 (Psi0 (dmD 2 0))) := by
    rw [← hd]
    exact character_eval_eq_core_of_handle_zero c d hdU hdV
  have hea : toAdd (e a) = toAdd (e0 (Psi0 (dmA 2 0))) := by
    rw [← ha]
    exact character_eval_eq_core_of_handle_zero e a haU haV
  have heb : toAdd (e b) = toAdd (e0 (Psi0 (dmB 2 0))) := by
    rw [← hb]
    exact character_eval_eq_core_of_handle_zero e b hbU hbV
  have hec : toAdd (e cc) = toAdd (e0 (Psi0 (dmC 2 0))) := by
    rw [← hc]
    exact character_eval_eq_core_of_handle_zero e cc hcU hcV
  have hed : toAdd (e d) = toAdd (e0 (Psi0 (dmD 2 0))) := by
    rw [← hd]
    exact character_eval_eq_core_of_handle_zero e d hdU hdV
  have hcompact := evenCupForm_comp_dm_aut (alpha := 2) (h := 0)
    (by omega) Psi0 c0 e0
  simp only [evenCupForm] at hcompact ⊢
  simp only [Finset.univ_unique, Finset.sum_singleton]
  simp only [standardHandleMark_zero, standardHandleMark_one,
    standardHandleMark_two, standardHandleMark_three,
    standardHandleMark_handleU, standardHandleMark_handleV]
  rw [hca, hcb, hcc, hcd, hea, heb, hec, hed]
  have hcg (i : Fin (coreRank 0)) :
      toAdd (c0 (dmGen 2 0 i)) = toAdd (c (dmGen 2 1 (coreCast i))) := by
    exact congrArg toAdd (dmCoordinateCharacter_gen 2 0 one_le_two _ i)
  have heg (i : Fin (coreRank 0)) :
      toAdd (e0 (dmGen 2 0 i)) = toAdd (e (dmGen 2 1 (coreCast i))) := by
    exact congrArg toAdd (dmCoordinateCharacter_gen 2 0 one_le_two _ i)
  simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply, autHom_apply,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hcompact
  simp_rw [hcg, heg] at hcompact
  have hc0' : coreCast (0 : Fin (coreRank 0)) =
      (0 : Fin (coreRank 1)) := rfl
  have hc1' : coreCast (1 : Fin (coreRank 0)) =
      (1 : Fin (coreRank 1)) := rfl
  have hc2' : coreCast (2 : Fin (coreRank 0)) =
      (2 : Fin (coreRank 1)) := rfl
  have hc3' : coreCast (3 : Fin (coreRank 0)) =
      (3 : Fin (coreRank 1)) := rfl
  simp_rw [hc0', hc1', hc2', hc3'] at hcompact
  change _ = _
  simp only [dmA, dmB, dmC, dmD]
  linear_combination hcompact

private def handlePadic (k : Fin (2 * 1)) :
    ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]) :=
  (mHHom 2 (h := 1) k).comp (mAbMkHom 2 1)

@[simp] private theorem handlePadic_gen (k : Fin (2 * 1))
    (i : Fin (coreRank 1)) :
    handlePadic k (dmGen 2 1 i) =
      mHandleMark k (ofAdd (1 : ℤ_[2])) i := by
  change mHHom 2 k (mAbMkHom 2 1 (dmGen 2 1 i)) = _
  rw [mAbMkHom_apply, mHHom, mCoordHom_gen]

private def handleUPadic :
    ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]) :=
  handlePadic (mHandleCoordU (0 : Fin 1))

private def handleVPadic :
    ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]) :=
  handlePadic (mHandleCoordV (0 : Fin 1))

private theorem handleUPadic_dmB : toAdd (handleUPadic (dmB 2 1)) = 0 := by
  change toAdd (mHHom 2 (mHandleCoordU (0 : Fin 1))
    (GQ2.SectionThree.abMk (dmGen 2 1 1))) = 0
  rw [mHHom, mCoordHom_gen, mHandleMark_core]
  · rfl
  · norm_num [coreRank]

private theorem handleUPadic_dmC : toAdd (handleUPadic (dmC 2 1)) = 0 := by
  change toAdd (mHHom 2 (mHandleCoordU (0 : Fin 1))
    (GQ2.SectionThree.abMk (dmGen 2 1 2))) = 0
  rw [mHHom, mCoordHom_gen, mHandleMark_core]
  · rfl
  · norm_num [coreRank]

private theorem handleVPadic_dmB : toAdd (handleVPadic (dmB 2 1)) = 0 := by
  change toAdd (mHHom 2 (mHandleCoordV (0 : Fin 1))
    (GQ2.SectionThree.abMk (dmGen 2 1 1))) = 0
  rw [mHHom, mCoordHom_gen, mHandleMark_core]
  · rfl
  · norm_num [coreRank]

private theorem handleVPadic_dmC : toAdd (handleVPadic (dmC 2 1)) = 0 := by
  change toAdd (mHHom 2 (mHandleCoordV (0 : Fin 1))
    (GQ2.SectionThree.abMk (dmGen 2 1 2))) = 0
  rw [mHHom, mCoordHom_gen, mHandleMark_core]
  · rfl
  · norm_num [coreRank]

private def handleModTwoVector (k : Fin (2 * 1)) :
    Fin (coreRank 1) → ZMod 2 :=
  Pi.single (mHandleIdx (h := 1) k) 1

private theorem dmCoordinateCharacter_handle_eq (k : Fin (2 * 1)) :
    dmCoordinateCharacter 2 1 one_le_two
        (handleModTwoVector k) =
      dmModTwo.comp ((mHHom 2 (h := 1) k).comp (mAbMkHom 2 1)) := by
  apply dm_hom_ext
  intro i
  rw [dmCoordinateCharacter_gen]
  change (ofAdd (handleModTwoVector k i) : Multiplicative (ZMod 2)) =
    dmModTwo (handlePadic k (dmGen 2 1 i))
  rw [handlePadic_gen]
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd]
  by_cases hi : i = mHandleIdx (h := 1) k
  · subst i
    rw [handleModTwoVector, Pi.single_eq_same, mHandleMark_self,
      toAdd_dmModTwo, mParityZ_one]
  · rw [handleModTwoVector, Pi.single_eq_of_ne hi,
      mHandleMark_of_ne k _ hi, map_one, toAdd_one]

private theorem modTwoCoordinate_handleU_eq_parity (x : DM 2 1) :
    modTwoCoordinate 1 x (handleIdxU 0) =
      mParityZ (toAdd (handleUPadic x)) := by
  let f2 := dmCoordinateCharacter 2 1 one_le_two
    (Pi.single (handleIdxU 0) 1)
  have heq : f2 = dmModTwo.comp handleUPadic := by
    unfold f2 handleUPadic
    rw [← mHandleIdx_coordU (0 : Fin 1)]
    change dmCoordinateCharacter 2 1 one_le_two
      (handleModTwoVector (mHandleCoordU 0)) = _
    exact dmCoordinateCharacter_handle_eq (mHandleCoordU 0)
  change toAdd (f2 x) = _
  rw [heq, ContinuousMonoidHom.coe_comp, Function.comp_apply,
    ← ofAdd_toAdd (handleUPadic x), toAdd_dmModTwo]
  simp only [toAdd_ofAdd]

private theorem modTwoCoordinate_handleV_eq_parity (x : DM 2 1) :
    modTwoCoordinate 1 x (handleIdxV 0) =
      mParityZ (toAdd (handleVPadic x)) := by
  let f2 := dmCoordinateCharacter 2 1 one_le_two
    (Pi.single (handleIdxV 0) 1)
  have heq : f2 = dmModTwo.comp handleVPadic := by
    unfold f2 handleVPadic
    rw [← mHandleIdx_coordV (0 : Fin 1)]
    change dmCoordinateCharacter 2 1 one_le_two
      (handleModTwoVector (mHandleCoordV 0)) = _
    exact dmCoordinateCharacter_handle_eq (mHandleCoordV 0)
  change toAdd (f2 x) = _
  rw [heq, ContinuousMonoidHom.coe_comp, Function.comp_apply,
    ← ofAdd_toAdd (handleVPadic x), toAdd_dmModTwo]
  simp only [toAdd_ofAdd]

theorem exists_oneHandleCupAdaptedSeed
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0))) :
    OneHandleCupAdaptedSeed Psi0 := by
  obtain ⟨p, ha, hb, hc, hd, hz, _, hcrow⟩ :=
    exists_oneHandleBalancedSeed Psi0 hrow
  let a := clearModTwoHandles (balancedA p)
  let b := clearModTwoHandles (balancedB p)
  let d := clearModTwoHandles (balancedD p)
  let p' : OneHandleBalancedPoint := (a, b, balancedC p, d, 1)
  have ha' : dmForgetHandles 2 1 a = Psi0 (dmA 2 0) :=
    (dmForgetHandles_clearModTwoHandles _).trans ha
  have hb' : dmForgetHandles 2 1 b = Psi0 (dmB 2 0) :=
    (dmForgetHandles_clearModTwoHandles _).trans hb
  have hd' : dmForgetHandles 2 1 d = Psi0 (dmD 2 0) :=
    (dmForgetHandles_clearModTwoHandles _).trans hd
  have haU : modTwoCoordinate 1 a (handleIdxU 0) = 0 := by
    rw [modTwoCoordinate_clearModTwoHandles]
    simp
  have haV : modTwoCoordinate 1 a (handleIdxV 0) = 0 := by
    rw [modTwoCoordinate_clearModTwoHandles]
    simp
  have hbU : modTwoCoordinate 1 b (handleIdxU 0) = 0 := by
    rw [modTwoCoordinate_clearModTwoHandles]
    simp
  have hbV : modTwoCoordinate 1 b (handleIdxV 0) = 0 := by
    rw [modTwoCoordinate_clearModTwoHandles]
    simp
  have hdU : modTwoCoordinate 1 d (handleIdxU 0) = 0 := by
    rw [modTwoCoordinate_clearModTwoHandles]
    simp
  have hdV : modTwoCoordinate 1 d (handleIdxV 0) = 0 := by
    rw [modTwoCoordinate_clearModTwoHandles]
    simp
  have hcU : modTwoCoordinate 1 (balancedC p) (handleIdxU 0) = 0 := by
    rw [modTwoCoordinate_handleU_eq_parity]
    have hu := hcrow handleUPadic
    rw [handleUPadic_dmC, handleUPadic_dmB] at hu
    simp only [mul_zero, add_zero] at hu
    rw [hu, mParityZ_zero]
  have hcV : modTwoCoordinate 1 (balancedC p) (handleIdxV 0) = 0 := by
    rw [modTwoCoordinate_handleV_eq_parity]
    have hv := hcrow handleVPadic
    rw [handleVPadic_dmC, handleVPadic_dmB] at hv
    simp only [mul_zero, add_zero] at hv
    rw [hv, mParityZ_zero]
  refine ⟨p', ha', hb', hc, hd', map_one _, ?_, hcrow, ?_⟩
  · change OneHandleModTwoIndep
      (standardHandleMark a b (balancedC p) (1 * d))
    simpa using oneHandleModTwoIndep_of_fibers Psi0 ha' hb' hc hd'
  · change OneHandleCupAdapted
      (standardHandleMark a b (balancedC p) (1 * d))
    simpa using standardHandleMark_cupAdapted_of_core_zero Psi0
      ha' hb' hc hd' haU haV hbU hbV hcU hcV hdU hdV

theorem oneHandleBalancedSet_three_nonempty
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0))) :
    (oneHandleBalancedSet Psi0 3).Nonempty :=
  oneHandleBalancedSet_three_nonempty_of_cupAdaptedSeed Psi0
    (exists_oneHandleCupAdaptedSeed Psi0 hrow)

#print axioms exists_oneHandleCupAdaptedSeed
#print axioms oneHandleBalancedSet_three_nonempty

end
end GQ2.Dyadic.Instances.MpcCupAdaptedSeed

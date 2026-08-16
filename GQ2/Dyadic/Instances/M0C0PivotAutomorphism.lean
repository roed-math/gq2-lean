/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.M0C0PivotAudit
import GQ2.Dyadic.Instances.EvenModelCupForm
import GQ2.Dyadic.Instances.SqModelPresentingFrameCupAdapted
import GQ2.Dyadic.MarkedCore.MFrameExists
import GQ2.Dyadic.MarkedCore.MFrameApi

/-!
# The compact-M C0 pivot is invariant under oriented automorphisms

This file upgrades `M0C0PivotAudit` from its finite-dimensional cup statement to the group
automorphism level.  It transports the compact-M presentation along an arbitrary continuous
automorphism, uses uniqueness of the one-dimensional degree-two obstruction to prove invariance
of the full even cup form, and identifies the D-coordinate character with the cup-dual of C0.

An automorphism preserving `chiM` preserves the full additive D-coordinate.  Cup invariance then
forces every mod-two character to take the same value on C0 before and after the automorphism.
Consequently the unitness of any 2-adic marking at C0 is invariant.  In particular no
chi-preserving automorphism can manufacture the pivot premise still exposed by the selected
general-h compact-M residual.

No converse realization claim is made: the result applies to every actual continuous
automorphism and therefore gives the needed no-unitizer theorem directly.
-/

namespace GQ2.Dyadic.Instances.M0C0PivotAutomorphism

open Multiplicative GQ2.SectionThree GQ2.Dyadic.MarkedCore GQ2.Dyadic.EvenModel ContCoh

noncomputable section

local instance m0PivotScalarAction (alpha h : Nat) :
    DistribMulAction (DM alpha h : Type) (ZMod 2) :=
  scalarActionZmodTwo _

local instance m0PivotContinuousScalar (alpha h : Nat) :
    ContinuousSMul (DM alpha h : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

variable {alpha h : Nat}

/-- The image of the canonical compact-M marking under an automorphism is again a marked
relator. -/
theorem markedRelator_dm_aut (halpha : 1 <= alpha)
  (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type)) :
    WordCoh.MarkedRelator (DM alpha h : Type) (mNatWord alpha h)
      (fun i => Psi (dmGen alpha h i)) := by
  refine { frattini := (markedRelator_DM alpha h halpha).frattini
           holds := by
             show mRelWord alpha (fun i => Psi (dmGen alpha h i)) = 1
             rw [<- map_mRelWord, dm_relation, map_one] }

/-- Transport the compact-M presentation along an automorphism. -/
noncomputable def presentedBy_dm_aut
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type)) :
    WordCoh.PresentedBy (DM alpha h : Type) (mNatWord alpha h)
      (fun i => Psi (dmGen alpha h i)) where
  liftHom hP nu hnu :=
    ((presentedBy_DM alpha h).liftHom hP nu hnu).comp
      <| { toMonoidHom := Psi.symm.toMonoidHom
           continuous_toFun := Psi.symm.continuous_toFun }
  liftHom_mark hP nu hnu k := by
    show (presentedBy_DM alpha h).liftHom hP nu hnu
      (Psi.symm (Psi (dmGen alpha h k))) = nu k
    rw [Psi.symm_apply_apply]
    exact (presentedBy_DM alpha h).liftHom_mark hP nu hnu k
  hom_ext phi psi hgen := by
    have hcomp :
        phi.comp { toMonoidHom := Psi.toMonoidHom
                   continuous_toFun := Psi.continuous_toFun } =
          psi.comp { toMonoidHom := Psi.toMonoidHom
                     continuous_toFun := Psi.continuous_toFun } :=
      (presentedBy_DM alpha h).hom_ext _ _ hgen
    refine DFunLike.ext _ _ fun x => ?_
    have hx := DFunLike.congr_fun hcomp (Psi.symm x)
    change phi (Psi (Psi.symm x)) = psi (Psi (Psi.symm x)) at hx
    rwa [Psi.apply_symm_apply] at hx

/-- The obstruction functional attached to the automorphic compact-M marking. -/
noncomputable def dmAutObs (halpha : 1 <= alpha)
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type)) :
    H2 (DM alpha h : Type) (ZMod 2) →+ ZMod 2 :=
  WordCoh.obsH2 (fun _ _ => rfl) (mNatWord alpha h)
    (fun i => Psi (dmGen alpha h i)) (markedRelator_dm_aut halpha Psi)

theorem dmAutObs_injective (halpha : 1 <= alpha)
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type)) :
    Function.Injective (dmAutObs halpha Psi) :=
  WordCoh.obsH2_injective (fun _ _ => rfl) (mNatWord alpha h)
    (fun i => Psi (dmGen alpha h i)) (markedRelator_dm_aut halpha Psi)
    (presentedBy_dm_aut Psi) (isProP_DM alpha h)

theorem dmObs_eq_dmAutObs (halpha : 1 <= alpha)
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type)) :
    dmObs alpha h halpha = dmAutObs halpha Psi :=
  GQ2.Dyadic.LSquare.addMonoidHom_zmodTwo_eq_of_injective _ _
    (dmObs_injective alpha h halpha)
    (dmAutObs_injective halpha Psi)

/-- The full even cup form is invariant under every compact-M automorphism. -/
theorem evenCupForm_comp_dm_aut (halpha : 2 <= alpha)
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type))
    (c d : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative (ZMod 2))) :
    evenCupForm
        (fun i => toAdd ((c.comp (autHom Psi)) (dmGen alpha h i)))
        (fun i => toAdd ((d.comp (autHom Psi)) (dmGen alpha h i))) =
      evenCupForm (fun i => toAdd (c (dmGen alpha h i)))
        (fun i => toAdd (d (dmGen alpha h i))) := by
  have ha1 : 1 <= alpha := by omega
  have hPsi := obsH2_evenModel_mNatWord_characterCup
    (G := (DM alpha h : Type)) (fun _ _ => rfl) alpha h halpha
    (fun i => Psi (dmGen alpha h i)) (markedRelator_dm_aut ha1 Psi) c d
  have hid := dmFrattiniCupForm alpha h ha1 halpha c d
  have hobs : forall z, WordCoh.obsH2 (fun _ _ => rfl) (mNatWord alpha h)
      (fun i => Psi (dmGen alpha h i)) (markedRelator_dm_aut ha1 Psi) z =
        dmObs alpha h ha1 z := fun z =>
    congrArg (fun F : H2 (DM alpha h : Type) (ZMod 2) →+ ZMod 2 => F z)
      (dmObs_eq_dmAutObs ha1 Psi).symm
  exact hPsi.symm.trans ((hobs _).trans hid)

/-! ## The orientation's D-coordinate -/

/-- The canonical additive D-coordinate, before reduction modulo two. -/
noncomputable def dmDeltaD (alpha h : Nat) :
    ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]) :=
  (mDHom alpha h).comp (mAbMkHom alpha h)

/-- The canonical orientation read in the canonical general-rank M-frame. -/
theorem chiM_eq_mPhiHom (halpha : 1 <= alpha) (x : (DM alpha h : Type)) :
    chiM alpha h x =
      mFrameApiChiModel alpha h (mPhiHom halpha h (abMk x)) := by
  let rhs : ContinuousMonoidHom (DM alpha h : Type) ℤ_[2]ˣ :=
    (mFrameApiChiModelHom alpha h).comp
      (({ toMonoidHom := mPhiHom halpha h
          continuous_toFun := continuous_mPhiHom halpha h } :
          ContinuousMonoidHom (topAbelianization (DM alpha h : Type)) (MFrameModel h)).comp
        (mAbMkHom alpha h))
  have heq : chiM alpha h = rhs := by
    apply dm_hom_ext
    intro i
    rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
    · change chiM alpha h (dmA alpha h) =
        mFrameApiChiModel alpha h (mPhiHom halpha h (abMk (dmA alpha h)))
      rw [chiM_dmA, mPhiHom_A, mFrameApiChiModel_ofAdd, mSign_zero,
        zpowZtwo_zero, mul_one]
    · change chiM alpha h (dmB alpha h) =
        mFrameApiChiModel alpha h (mPhiHom halpha h (abMk (dmB alpha h)))
      rw [chiM_dmB, mPhiHom_B, mFrameApiChiModel_ofAdd, zpowZtwo_zero, mul_one]
      exact mSign_one.symm
    · change chiM alpha h (dmC alpha h) =
        mFrameApiChiModel alpha h (mPhiHom halpha h (abMk (dmC alpha h)))
      rw [chiM_dmC, mPhiHom_C, mFrameApiChiModel_ofAdd, mSign_zero,
        zpowZtwo_zero, mul_one]
    · change chiM alpha h (dmD alpha h) =
        mFrameApiChiModel alpha h (mPhiHom halpha h (abMk (dmD alpha h)))
      rw [chiM_dmD, mPhiHom_D, mFrameApiChiModel_ofAdd, mSign_zero,
        zpowZtwo_one_exp, one_mul]
    · rcases mHandleCoord_cases j with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · rw [mHandleIdx_coordU]
        change chiM alpha h (dmGen alpha h (handleIdxU k)) =
          mFrameApiChiModel alpha h
            (mPhiHom halpha h (abMk (dmGen alpha h (handleIdxU k))))
        rw [chiM_handleU, mPhiHom_U, mFrameApiChiModel_ofAdd, mSign_zero,
          zpowZtwo_zero, mul_one]
      · rw [mHandleIdx_coordV]
        change chiM alpha h (dmGen alpha h (handleIdxV k)) =
          mFrameApiChiModel alpha h
            (mPhiHom halpha h (abMk (dmGen alpha h (handleIdxV k))))
        rw [chiM_handleV, mPhiHom_V, mFrameApiChiModel_ofAdd, mSign_zero,
          zpowZtwo_zero, mul_one]
  exact DFunLike.congr_fun heq x

/-- A compact-M automorphism preserving the orientation preserves the full additive
D-coordinate, not merely its parity. -/
theorem dmDeltaD_aut_of_chiPreserving (halpha : 2 <= alpha)
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type))
    (hchi : forall x, chiM alpha h (Psi x) = chiM alpha h x)
    (x : (DM alpha h : Type)) : dmDeltaD alpha h (Psi x) = dmDeltaD alpha h x := by
  have ha1 : 1 <= alpha := by omega
  have hframe :
      mFrameApiChiModel alpha h (mPhiHom ha1 h (abMk (Psi x))) =
        mFrameApiChiModel alpha h (mPhiHom ha1 h (abMk x)) := by
    rw [<- chiM_eq_mPhiHom ha1, <- chiM_eq_mPhiHom ha1, hchi]
  have hrow := mChi_row_extract (α := alpha) halpha
    (b := (toAdd (mPhiHom ha1 h (abMk (Psi x)))).2.1)
    (d := (toAdd (mPhiHom ha1 h (abMk (Psi x)))).2.2.2.1)
    (w := (toAdd (mPhiHom ha1 h (abMk x))).2.2.2.1)
    (ε := mParityZ (toAdd (mPhiHom ha1 h (abMk x))).2.1) (by
      change mSign (toAdd (mPhiHom ha1 h (abMk (Psi x)))).2.1 * _ =
        mSign (toAdd (mPhiHom ha1 h (abMk x))).2.1 * _ at hframe
      exact hframe.trans (by rw [mSign_eq_pow_val]))
  exact congrArg ofAdd hrow.2

/-! ## The pivot parity -/

theorem evenDualVector_two_eq (h : Nat) :
    evenDualVector (2 : Fin (coreRank h)) =
      (Pi.single (3 : Fin (coreRank h)) 1 : Fin (coreRank h) → ZMod 2) := by
  classical
  funext i
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · have h01 : (0 : Fin (coreRank h)) ≠ 1 := by
      intro e; have he := congrArg Fin.val e
      rw [coreVal_zero, coreVal_one] at he
      omega
    have h12 : (1 : Fin (coreRank h)) ≠ 2 := by
      intro e; have he := congrArg Fin.val e
      rw [coreVal_one, coreVal_two] at he
      omega
    have h03 : (0 : Fin (coreRank h)) ≠ 3 := by
      intro e; have he := congrArg Fin.val e
      rw [coreVal_zero, coreVal_three] at he
      omega
    simp [evenDualVector, evenDualMap_apply, h01, h12, h03]
  · have h02 : (0 : Fin (coreRank h)) ≠ 2 := by
      intro e; have he := congrArg Fin.val e
      rw [coreVal_zero, coreVal_two] at he
      omega
    have h12 : (1 : Fin (coreRank h)) ≠ 2 := by
      intro e; have he := congrArg Fin.val e
      rw [coreVal_one, coreVal_two] at he
      omega
    have h13 : (1 : Fin (coreRank h)) ≠ 3 := by
      intro e; have he := congrArg Fin.val e
      rw [coreVal_one, coreVal_three] at he
      omega
    simp [evenDualVector, evenDualMap_apply, h02, h12, h13]
  · have h32 : (3 : Fin (coreRank h)) ≠ 2 := by
      intro e; have he := congrArg Fin.val e
      rw [coreVal_three, coreVal_two] at he
      omega
    have h21 : (2 : Fin (coreRank h)) ≠ 1 := by
      intro e; have he := congrArg Fin.val e
      rw [coreVal_two, coreVal_one] at he
      omega
    have h23 : (2 : Fin (coreRank h)) ≠ 3 := by
      intro e; have he := congrArg Fin.val e
      rw [coreVal_two, coreVal_three] at he
      omega
    simp [evenDualVector, evenDualMap_apply, h32, h21, h23]
  · have h31 : (3 : Fin (coreRank h)) ≠ 1 := by
      intro e; have he := congrArg Fin.val e
      rw [coreVal_three, coreVal_one] at he
      omega
    simp [evenDualVector, evenDualMap_apply, h31]
  · rcases mHandleCoord_cases j with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have hV2 : handleIdxV k ≠ (2 : Fin (coreRank h)) := by
        intro e; have he := congrArg Fin.val e
        rw [handleIdxV_val, coreVal_two] at he
        omega
      have hU1 : handleIdxU k ≠ (1 : Fin (coreRank h)) := by
        intro e; have he := congrArg Fin.val e
        rw [handleIdxU_val, coreVal_one] at he
        omega
      have hU3 : handleIdxU k ≠ (3 : Fin (coreRank h)) := by
        intro e; have he := congrArg Fin.val e
        rw [handleIdxU_val, coreVal_three] at he
        omega
      simp [mHandleIdx_coordU, evenDualVector, evenDualMap_apply,
        hV2, hU1, hU3]
    · have hU2 : handleIdxU k ≠ (2 : Fin (coreRank h)) := by
        intro e; have he := congrArg Fin.val e
        rw [handleIdxU_val, coreVal_two] at he
        omega
      have hV1 : handleIdxV k ≠ (1 : Fin (coreRank h)) := by
        intro e; have he := congrArg Fin.val e
        rw [handleIdxV_val, coreVal_one] at he
        omega
      have hV3 : handleIdxV k ≠ (3 : Fin (coreRank h)) := by
        intro e; have he := congrArg Fin.val e
        rw [handleIdxV_val, coreVal_three] at he
        omega
      simp [mHandleIdx_coordV, evenDualVector, evenDualMap_apply,
        hU2, hV1, hV3]

/-- Reduction of an additive 2-adic row modulo two. -/
noncomputable def dmModTwo :
    ContinuousMonoidHom (Multiplicative ℤ_[2]) (Multiplicative (ZMod 2)) :=
  zpowZtwoHom GQ2.SectionThree.isProP_two_multZMod2 (ofAdd (1 : ZMod 2))

theorem toAdd_dmModTwo (t : ℤ_[2]) :
    toAdd (dmModTwo (ofAdd t)) = mParityZ t := by
  change toAdd (zpowZtwo GQ2.SectionThree.isProP_two_multZMod2
    (ofAdd (1 : ZMod 2)) t) = mParityZ t
  rw [zpowZtwo_of_sq_eq_one GQ2.SectionThree.isProP_two_multZMod2
    (ofAdd (1 : ZMod 2)) (by decide) t]
  unfold mParityZ
  exact (by decide : forall z : ZMod 2,
    toAdd ((ofAdd (1 : ZMod 2)) ^ z.val) = (z.val : ZMod 2)) _

/-- The mod-two D-character. -/
noncomputable def dmDeltaDRed (alpha h : Nat) :
    ContinuousMonoidHom (DM alpha h : Type) (Multiplicative (ZMod 2)) :=
  dmModTwo.comp (dmDeltaD alpha h)

/-- The D-character is the cup-dual of the C0 slot. -/
theorem dmCoordinateCharacter_evenDual_two (halpha : 1 <= alpha) :
    dmCoordinateCharacter alpha h halpha (evenDualVector (2 : Fin (coreRank h))) =
      dmDeltaDRed alpha h := by
  apply dm_hom_ext
  intro i
  rw [dmCoordinateCharacter_gen, evenDualVector_two_eq]
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · change ofAdd (((Pi.single (3 : Fin (coreRank h)) 1 :
      Fin (coreRank h) → ZMod 2)) 0) =
      dmModTwo (mDHom alpha h (abMk (dmA alpha h)))
    rw [dmA, mDHom, mCoordHom_gen, coreMark_zero, map_one]
    have hne : (0 : Fin (coreRank h)) ≠ 3 := by
      intro e; have he := congrArg Fin.val e
      rw [coreVal_zero, coreVal_three] at he
      omega
    rw [Pi.single_eq_of_ne hne]
    rfl
  · change ofAdd (((Pi.single (3 : Fin (coreRank h)) 1 :
      Fin (coreRank h) → ZMod 2)) 1) =
      dmModTwo (mDHom alpha h (abMk (dmB alpha h)))
    rw [dmB, mDHom, mCoordHom_gen, coreMark_one, map_one]
    have hne : (1 : Fin (coreRank h)) ≠ 3 := by
      intro e; have he := congrArg Fin.val e
      rw [coreVal_one, coreVal_three] at he
      omega
    rw [Pi.single_eq_of_ne hne]
    rfl
  · change ofAdd (((Pi.single (3 : Fin (coreRank h)) 1 :
      Fin (coreRank h) → ZMod 2)) 2) =
      dmModTwo (mDHom alpha h (abMk (dmC alpha h)))
    rw [dmC, mDHom, mCoordHom_gen, coreMark_two, map_one]
    have hne : (2 : Fin (coreRank h)) ≠ 3 := by
      intro e; have he := congrArg Fin.val e
      rw [coreVal_two, coreVal_three] at he
      omega
    rw [Pi.single_eq_of_ne hne]
    rfl
  · change ofAdd (((Pi.single (3 : Fin (coreRank h)) 1 :
      Fin (coreRank h) → ZMod 2)) 3) =
      dmModTwo (mDHom alpha h (abMk (dmD alpha h)))
    rw [dmD, mDHom, mCoordHom_gen, coreMark_three]
    rw [Pi.single_eq_same, dmModTwo, zpowZtwoHom_ofAdd_one]
  · rcases mHandleCoord_cases j with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [mHandleIdx_coordU]
      change ofAdd (((Pi.single (3 : Fin (coreRank h)) 1 :
        Fin (coreRank h) → ZMod 2)) (handleIdxU k)) =
        dmModTwo (mDHom alpha h (abMk (dmGen alpha h (handleIdxU k))))
      rw [mDHom, mCoordHom_gen, coreMark_handleU, map_one]
      have hne : handleIdxU k ≠ (3 : Fin (coreRank h)) := by
        intro e; have he := congrArg Fin.val e
        rw [handleIdxU_val, coreVal_three] at he
        omega
      rw [Pi.single_eq_of_ne hne]
      rfl
    · rw [mHandleIdx_coordV]
      change ofAdd (((Pi.single (3 : Fin (coreRank h)) 1 :
        Fin (coreRank h) → ZMod 2)) (handleIdxV k)) =
        dmModTwo (mDHom alpha h (abMk (dmGen alpha h (handleIdxV k))))
      rw [mDHom, mCoordHom_gen, coreMark_handleV, map_one]
      have hne : handleIdxV k ≠ (3 : Fin (coreRank h)) := by
        intro e; have he := congrArg Fin.val e
        rw [handleIdxV_val, coreVal_three] at he
        omega
      rw [Pi.single_eq_of_ne hne]
      rfl

theorem dmDeltaDRed_aut_of_chiPreserving (halpha : 2 <= alpha)
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type))
    (hchi : forall x, chiM alpha h (Psi x) = chiM alpha h x) :
    (dmDeltaDRed alpha h).comp (autHom Psi) = dmDeltaDRed alpha h := by
  ext x
  change dmModTwo (dmDeltaD alpha h (Psi x)) = dmModTwo (dmDeltaD alpha h x)
  rw [dmDeltaD_aut_of_chiPreserving halpha Psi hchi x]

theorem dmCoordinateDualTwo_aut_of_chiPreserving (halpha : 2 <= alpha)
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type))
    (hchi : forall x, chiM alpha h (Psi x) = chiM alpha h x) :
    (dmCoordinateCharacter alpha h (by omega)
      (evenDualVector (2 : Fin (coreRank h)))).comp (autHom Psi) =
        dmCoordinateCharacter alpha h (by omega)
          (evenDualVector (2 : Fin (coreRank h))) := by
  rw [dmCoordinateCharacter_evenDual_two (alpha := alpha) (h := h) (by omega)]
  exact dmDeltaDRed_aut_of_chiPreserving halpha Psi hchi

/-- Pullback by an oriented compact-M automorphism fixes the C0 value of every mod-two
character. -/
theorem dmC_modTwo_aut (halpha : 2 <= alpha)
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type))
    (hchi : forall x, chiM alpha h (Psi x) = chiM alpha h x)
    (c : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative (ZMod 2))) :
    toAdd (c (Psi (dmC alpha h))) = toAdd (c (dmC alpha h)) := by
  let delta := dmCoordinateCharacter alpha h (by omega)
    (evenDualVector (2 : Fin (coreRank h)))
  have hinv := evenCupForm_comp_dm_aut halpha Psi delta c
  have hdelta : delta.comp (autHom Psi) = delta :=
    dmCoordinateDualTwo_aut_of_chiPreserving halpha Psi hchi
  rw [hdelta] at hinv
  simp only [delta, dmCoordinateCharacter_gen, toAdd_ofAdd] at hinv
  rw [evenCupForm_evenDualVector_left, evenCupForm_evenDualVector_left] at hinv
  exact hinv

/-- The compact-M C0 pivot's unitness is invariant under every orientation-preserving
continuous automorphism, at every handle count. -/
theorem isUnit_dmC_aut_iff (halpha : 2 <= alpha)
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type))
    (hchi : forall x, chiM alpha h (Psi x) = chiM alpha h x)
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2])) :
    IsUnit (toAdd (nu (Psi (dmC alpha h)))) ↔
      IsUnit (toAdd (nu (dmC alpha h))) := by
  have hmod := dmC_modTwo_aut halpha Psi hchi (dmModTwo.comp nu)
  change toAdd (dmModTwo (nu (Psi (dmC alpha h)))) =
    toAdd (dmModTwo (nu (dmC alpha h))) at hmod
  have hpar : mParityZ (toAdd (nu (Psi (dmC alpha h)))) =
      mParityZ (toAdd (nu (dmC alpha h))) := by
    rw [← toAdd_dmModTwo, ← toAdd_dmModTwo]
    simpa using hmod
  constructor
  · intro hu
    apply mIsUnit_of_parity_one
    rw [← hpar]
    exact mParityZ_of_isUnit hu
  · intro hu
    apply mIsUnit_of_parity_one
    rw [hpar]
    exact mParityZ_of_isUnit hu

theorem no_oriented_dmC_unitizer (halpha : 2 <= alpha)
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (hnot : ¬ IsUnit (toAdd (nu (dmC alpha h)))) :
    ¬ (∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
        IsUnit (toAdd (nu (Psi (dmC alpha h))))) := by
  rintro ⟨Psi, hchi, hunit⟩
  exact hnot ((isUnit_dmC_aut_iff halpha Psi hchi nu).mp hunit)

#print axioms markedRelator_dm_aut
#print axioms presentedBy_dm_aut
#print axioms dmAutObs_injective
#print axioms evenCupForm_comp_dm_aut
#print axioms chiM_eq_mPhiHom
#print axioms dmDeltaD_aut_of_chiPreserving
#print axioms evenDualVector_two_eq
#print axioms dmCoordinateCharacter_evenDual_two
#print axioms dmC_modTwo_aut
#print axioms isUnit_dmC_aut_iff
#print axioms no_oriented_dmC_unitizer

end

end GQ2.Dyadic.Instances.M0C0PivotAutomorphism

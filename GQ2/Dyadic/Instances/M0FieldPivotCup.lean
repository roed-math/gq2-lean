/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.M0FieldPivotInvariant

/-!
# Cup characterization of the compact-M field pivot

Level zero makes the mod-two unramified character nonzero on `ker chi`, but does not place that
nonzero value on the canonical `C0` line.  The even Demushkin cup form gives the exact missing
placement condition: `C0` is cup-dual to the distinguished `D` character.  Thus the compact-M
field pivot is a unit precisely when the cup of transported `D` with the mod-two unramified
character is `1`.

This is an intrinsic arithmetic characterization, not an existence theorem.  Replacing the cup
value by a Hilbert symbol would additionally require Kummer representatives and the repository's
explicit Tate--Kummer--Artin compatibility premise.
-/

namespace GQ2.Dyadic.Instances.M0FieldPivotCup

noncomputable section

open GQ2 GQ2.Dyadic ContCoh
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.EvenModel
open GQ2.Dyadic.Instances.M0C0PivotAutomorphism
open GQ2.Dyadic.Instances.M0FieldPivotInvariant

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
private theorem markedRelatorMOfEquiv {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (e : ContinuousMulEquiv (DM alpha h : Type) (maxProPQuotient 2 (GalK K))) :
    WordCoh.MarkedRelator (maxProPQuotient 2 (GalK K)) (mNatWord alpha h)
      (fun i => e (dmGen alpha h i)) :=
  ⟨(markedRelator_DM alpha h halpha).frattini, by
    show mRelWord alpha (fun i => e (dmGen alpha h i)) = 1
    rw [← map_mRelWord, dm_relation, map_one]⟩

private noncomputable def presentedByMOfEquiv {alpha h : ℕ}
    (e : ContinuousMulEquiv (DM alpha h : Type) (maxProPQuotient 2 (GalK K))) :
    WordCoh.PresentedBy (maxProPQuotient 2 (GalK K)) (mNatWord alpha h)
      (fun i => e (dmGen alpha h i)) where
  liftHom hP nu hnu :=
    ((presentedBy_DM alpha h).liftHom hP nu hnu).comp
      ⟨e.symm.toMonoidHom, e.symm.continuous_toFun⟩
  liftHom_mark hP nu hnu i := by
    show (presentedBy_DM alpha h).liftHom hP nu hnu
      (e.symm (e (dmGen alpha h i))) = nu i
    rw [e.symm_apply_apply]
    exact (presentedBy_DM alpha h).liftHom_mark hP nu hnu i
  hom_ext phi psi hgen := by
    have hcomp : phi.comp ⟨e.toMonoidHom, e.continuous_toFun⟩ =
        psi.comp ⟨e.toMonoidHom, e.continuous_toFun⟩ :=
      (presentedBy_DM alpha h).hom_ext _ _ hgen
    refine DFunLike.ext _ _ fun x => ?_
    have hx := DFunLike.congr_fun hcomp (e.symm x)
    change phi (e (e.symm x)) = psi (e (e.symm x)) at hx
    rwa [e.apply_symm_apply] at hx

private noncomputable def mFrameObs {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (e : ContinuousMulEquiv (DM alpha h : Type) (maxProPQuotient 2 (GalK K))) :
    H2 (maxProPQuotient 2 (GalK K)) (ZMod 2) →+ ZMod 2 :=
  WordCoh.obsH2 (fun _ _ => rfl) (mNatWord alpha h) (fun i => e (dmGen alpha h i))
    (markedRelatorMOfEquiv halpha e)

omit [FiniteDimensional ℚ_[2] K] in
private theorem mFrameObs_injective {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (e : ContinuousMulEquiv (DM alpha h : Type) (maxProPQuotient 2 (GalK K))) :
    Function.Injective (mFrameObs halpha e) :=
  WordCoh.obsH2_injective (fun _ _ => rfl) (mNatWord alpha h)
    (fun i => e (dmGen alpha h i)) (markedRelatorMOfEquiv halpha e)
    (presentedByMOfEquiv e) isProP_maxProPQuotient

private theorem maxProTwoInv_eq_mFrameObs {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (e : ContinuousMulEquiv (DM alpha h : Type) (maxProPQuotient 2 (GalK K))) :
    GQ2.Dyadic.LSquare.maxProTwoInv K = mFrameObs halpha e :=
  GQ2.Dyadic.LSquare.addMonoidHom_zmodTwo_eq_of_injective _ _
    (GQ2.Dyadic.LSquare.maxProTwoInv_injective (K := K))
    (mFrameObs_injective halpha e)

private theorem cupFormK_eq_evenCupForm_of_m_equiv {alpha h : ℕ}
    (halpha : 2 ≤ alpha)
    (e : ContinuousMulEquiv (DM alpha h : Type) (maxProPQuotient 2 (GalK K)))
    (c d : ContinuousMonoidHom
      (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2))) :
    FieldData.cupFormK K
        (h1MaxProTwoEquivGalK (K := K) (evenModelCharacterClass c))
        (h1MaxProTwoEquivGalK (K := K) (evenModelCharacterClass d)) =
      evenCupForm (fun i => Multiplicative.toAdd (c (e (dmGen alpha h i))))
        (fun i => Multiplicative.toAdd (d (e (dmGen alpha h i)))) := by
  rw [GQ2.Dyadic.LSquare.cupFormK_eq_maxProTwoInv,
    maxProTwoInv_eq_mFrameObs (by omega) e]
  exact obsH2_evenModel_mNatWord_characterCup (fun _ _ => rfl)
    alpha h halpha (fun i => e (dmGen alpha h i))
    (markedRelatorMOfEquiv (by omega) e) c d

/-- The distinguished `D` character transported from the compact-M core to the field group. -/
noncomputable def m0FieldDCharacter {alpha h : ℕ}
    (e : ContinuousMulEquiv (DM alpha h : Type) (maxProPQuotient 2 (GalK K))) :
    ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)) :=
  (dmDeltaDRed alpha h).comp ⟨e.symm.toMonoidHom, e.symm.continuous_toFun⟩

/-- The mod-two reduction of the field's unramified character. -/
noncomputable def m0FieldNuCharacter (B : MarkedRecip Rec K) :
    ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)) :=
  dmModTwo.comp (nuUrKTwo B)

/-- The intrinsic field cup whose nonvanishing is the compact-M pivot condition. -/
noncomputable def m0PivotCupValue (B : MarkedRecip Rec K) {alpha h : ℕ}
    (e : ContinuousMulEquiv (DM alpha h : Type) (maxProPQuotient 2 (GalK K))) : ZMod 2 :=
  FieldData.cupFormK K
    (h1MaxProTwoEquivGalK (K := K)
      (evenModelCharacterClass (m0FieldDCharacter e)))
    (h1MaxProTwoEquivGalK (K := K)
      (evenModelCharacterClass (m0FieldNuCharacter B)))

/-- The pivot cup is exactly the parity of the transported `C0` unramified value. -/
theorem m0PivotCupValue_eq_parity (B : MarkedRecip Rec K) {alpha h : ℕ}
    (halpha : 2 ≤ alpha)
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) :
    m0PivotCupValue B e.1 =
      mParityZ (Multiplicative.toAdd (nuUrKTwo B (e.1 (dmC alpha h)))) := by
  rw [m0PivotCupValue, cupFormK_eq_evenCupForm_of_m_equiv halpha]
  have hD :
      (fun i => Multiplicative.toAdd (m0FieldDCharacter e.1 (e.1 (dmGen alpha h i)))) =
        evenDualVector (2 : Fin (coreRank h)) := by
    funext i
    change Multiplicative.toAdd
      (dmDeltaDRed alpha h (e.1.symm (e.1 (dmGen alpha h i)))) = _
    rw [e.1.symm_apply_apply,
      ← dmCoordinateCharacter_evenDual_two (alpha := alpha) (h := h) (by omega),
      dmCoordinateCharacter_gen]
    rfl
  rw [hD, evenCupForm_evenDualVector_left]
  change Multiplicative.toAdd (dmModTwo (nuUrKTwo B (e.1 (dmC alpha h)))) = _
  simpa only [ofAdd_toAdd] using
    (toAdd_dmModTwo (Multiplicative.toAdd (nuUrKTwo B (e.1 (dmC alpha h)))))

/-- The sharp arithmetic characterization: the intrinsic M0 field pivot holds exactly when
the transported `D` class cups nontrivially with the mod-two unramified character. -/
theorem m0FieldPivotUnit_iff_cup (B : MarkedRecip Rec K) {alpha h : ℕ}
    (halpha : 2 ≤ alpha)
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) :
    M0FieldPivotUnit B alpha h ↔ m0PivotCupValue B e.1 = 1 := by
  rw [m0FieldPivotUnit_iff B halpha e, m0PivotCupValue_eq_parity B halpha e]
  exact ⟨mParityZ_of_isUnit, mIsUnit_of_parity_one⟩

/-- Exact family-selector audit: an M0 selection supplies level zero, while its remaining
field-pivot content is precisely the nonzero transported-D/unramified cup value. -/
theorem m0_familySelection_level_and_pivot_iff_cup
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha)
    (e : OrientedContinuousMulEquiv
      (chiM alpha (handleCount FP (.M0 alpha))) (chiCycKTwo (K := K))) :
    B.r = 0 ∧
      (M0FieldPivotUnit B alpha (handleCount FP (.M0 alpha)) ↔
        m0PivotCupValue B e.1 = 1) := by
  have hr := S.level_eq
  rw [hbranch] at hr
  have halpha := S.valid
  rw [hbranch] at halpha
  exact ⟨hr.symm, m0FieldPivotUnit_iff_cup B halpha e⟩

#print axioms m0FieldDCharacter
#print axioms m0FieldNuCharacter
#print axioms m0PivotCupValue
#print axioms m0PivotCupValue_eq_parity
#print axioms m0FieldPivotUnit_iff_cup
#print axioms m0_familySelection_level_and_pivot_iff_cup

end
end GQ2.Dyadic.Instances.M0FieldPivotCup

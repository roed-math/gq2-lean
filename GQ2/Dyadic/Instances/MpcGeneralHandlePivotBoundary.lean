/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcTrueRankFourResidual

/-!
# The general-h Mpc pivot boundary

The unconditional odd shear `MpcMk.mpcMk_pivShift` is a rank-four theorem: it constructs an
automorphism of `DM 2 0`.  There is no repository map lifting that automorphism to `DM alpha h`,
and an automorphism of the rank-four quotient does not by itself respect the relator with the
additional handle commutators.

The general-h correction APIs do not bridge this gap.  Canonical M scaling multiplies the `C`
row by a unit, which preserves exact-pivot existence, and scaled handle clearing fixes `C`.
Thus neither operation can create the missing divided digit.  This file packages the exact
remaining premise as `MpcPivShiftH alpha h` and proves the strongest resulting consumer.

For every epsilon-true selected row, at arbitrary `alpha` and handle count, the `B` row has exact
level `r - 1`.  Hence a general-h odd `2 B` shear adjusts any orientation to one with an exact
level-`r` `C` pivot.  The canonical scaling and handle-correction endpoint then supplies the
corrected RN residual.  At `(alpha,h) = (2,0)` the interface is definitionally the old
`MpcPivShift 2` and is discharged by `MpcMk.mpcMk_pivShift`; beyond rank four the shear premise
is the sharp unconstructed boundary.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.Instances.MpcGeneralHandleCertificate
open GQ2.Dyadic.Instances.MpcGeneralHandleFamily
open GQ2.Dyadic.Instances.MpcGeneralHandleFamilyCanonical
open GQ2.Dyadic.Instances.MpcGeneralHandleRealization
open GQ2.Dyadic.Instances.MpcPiv
open GQ2.Dyadic.Instances.MpcRow
open GQ2.Dyadic.FieldUnimod

/-- The odd M6 pivot shear at an arbitrary handle count. -/
def MpcPivShiftH (alpha h : ℕ) : Prop :=
  ∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
    (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
      ∀ f : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]),
        toAdd (f (Psi (dmC alpha h))) =
          toAdd (f (dmC alpha h)) + 2 * toAdd (f (dmB alpha h))

/-- At handle count zero, the general interface is exactly the existing Mpc pivot shift. -/
theorem mpcPivShiftH_zero_iff (alpha : ℕ) :
    MpcPivShiftH alpha 0 ↔ MpcPivShift alpha := Iff.rfl

/-- The marked M6 construction discharges precisely the compact `(2,0)` instance. -/
theorem mpcPivShiftH_two_zero : MpcPivShiftH 2 0 :=
  MpcMk.mpcMk_pivShift

/-- Multiplying the `C` row by a unit preserves, rather than creates, the exact pivot. -/
theorem exactPivot_comp_iff_of_unit_C {alpha r h : ℕ}
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type))
    (u : ℤ_[2]ˣ)
    (hC : toAdd (nu (Psi (dmC alpha h))) =
      (u : ℤ_[2]) * toAdd (nu (dmC alpha h))) :
    (∃ gamma : ℤ_[2]ˣ,
      toAdd (nu (Psi (dmC alpha h))) = (gamma : ℤ_[2]) * 2 ^ r) ↔
      ∃ gamma : ℤ_[2]ˣ,
        toAdd (nu (dmC alpha h)) = (gamma : ℤ_[2]) * 2 ^ r := by
  constructor
  · rintro ⟨gamma, hgamma⟩
    refine ⟨u⁻¹ * gamma, ?_⟩
    calc
      toAdd (nu (dmC alpha h)) =
          ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
            ((u : ℤ_[2]) * toAdd (nu (dmC alpha h))) := by
            rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      _ = ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) *
          toAdd (nu (Psi (dmC alpha h))) := by rw [hC]
      _ = ((u⁻¹ * gamma : ℤ_[2]ˣ) : ℤ_[2]) * 2 ^ r := by
        rw [hgamma, Units.val_mul]
        ring
  · rintro ⟨gamma, hgamma⟩
    refine ⟨u * gamma, ?_⟩
    rw [hC, hgamma, Units.val_mul]
    ring

variable {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])}
  [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-- Precompose a general-h orientation with a chi-preserving automorphism. -/
def mpcPivCompH {alpha h : ℕ}
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type))
    (hPsi : ∀ x, chiM alpha h (Psi x) = chiM alpha h x) :
    OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)) :=
  ⟨Psi.trans e.1, fun x => (e.2 (Psi x)).trans (hPsi x)⟩

omit [FiniteDimensional ℚ_[2] K] in
@[simp] theorem mpcPivCompH_apply {alpha h : ℕ}
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type))
    (hPsi : ∀ x, chiM alpha h (Psi x) = chiM alpha h x)
    (x : DM alpha h) :
    (mpcPivCompH e Psi hPsi).1 x = e.1 (Psi x) := rfl

/-- On an epsilon-true row, a general-h odd shear creates an exact pivot. -/
theorem exists_exactPivot_of_shiftH {alpha r h : ℕ}
    (hshift : MpcPivShiftH alpha h)
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (hlev : MpcChiKerLevelH alpha r h nu)
    (hB : ∃ beta : ℤ_[2]ˣ,
      toAdd (nu (dmB alpha h)) = (beta : ℤ_[2]) * 2 ^ (r - 1))
    (hr : 1 ≤ r) :
    ∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
        ∃ gamma : ℤ_[2]ˣ,
          toAdd (nu (Psi (dmC alpha h))) = (gamma : ℤ_[2]) * 2 ^ r := by
  obtain ⟨c, hc⟩ := hlev (dmC alpha h) (chiM_dmC alpha h)
  obtain ⟨beta, hbeta⟩ := hB
  have hpowR : (2 : ℤ_[2]) ^ r = 2 * 2 ^ (r - 1) := by
    calc
      (2 : ℤ_[2]) ^ r = 2 ^ ((r - 1) + 1) := by congr 1; omega
      _ = 2 ^ (r - 1) * 2 := pow_succ _ _
      _ = 2 * 2 ^ (r - 1) := by ring
  rcases mpcRow_even_or_odd c with ⟨z, hz⟩ | ⟨w, hw⟩
  · obtain ⟨Psi, hPsi, hrow⟩ := hshift
    have hunit : IsUnit (2 * z + (beta : ℤ_[2])) := by
      apply mIsUnit_of_parity_one
      rw [mParityZ_add, mParityZ_two_mul, zero_add, mParityZ_of_isUnit beta.isUnit]
    refine ⟨Psi, hPsi, hunit.unit, ?_⟩
    rw [hrow nu, hc, hz, hbeta, IsUnit.unit_spec, hpowR]
    ring
  · refine ⟨ContinuousMulEquiv.refl _, fun _ => rfl,
      (GQ2.isUnit_one_add_two_mul w).unit, ?_⟩
    rw [show (ContinuousMulEquiv.refl (DM alpha h : Type)) (dmC alpha h) =
      dmC alpha h from rfl, hc, hw, IsUnit.unit_spec]
    ring

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity} [T2Space (GalK K)]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  [T2Space (GalK K)] in
/-- The epsilon-true selected `B` row has exact level `r - 1`, at every handle count. -/
theorem mpc_familySelection_true_B_exact
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r true eta) :
    ∃ _hr : B.r = r, 1 ≤ r ∧
      ∀ e : OrientedContinuousMulEquiv
          (chiM alpha (handleCount FP (.Mpc alpha r true eta)))
          (chiCycKTwo (K := K)),
        ∃ beta : ℤ_[2]ˣ,
          toAdd (transport (nuUrKTwo B).toMonoidHom e.1
            ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun)
              (dmB alpha (handleCount FP (.Mpc alpha r true eta)))) =
            (beta : ℤ_[2]) * 2 ^ (r - 1) := by
  have hr : B.r = r := by
    have hs := S.level_eq
    rw [hbranch] at hs
    exact hs.symm
  have hrpos : 1 ≤ r := by
    have hv := S.valid
    rw [hbranch] at hv
    exact hv.2
  obtain ⟨hneg, _hunit, hnegrow, _hunitrow⟩ :=
    familyMpc_lambda_rows S hbranch
  refine ⟨hr, hrpos, fun e => ?_⟩
  obtain ⟨w, hw⟩ := residue_of_lambdaAt B FF hr hneg (p true r : ℤ_[2])
    hnegrow e (chiM_dmB alpha (handleCount FP (.Mpc alpha r true eta)))
  let beta : ℤ_[2]ˣ := (GQ2.isUnit_one_add_two_mul w).unit
  refine ⟨beta, ?_⟩
  rw [hw, p_true, IsUnit.unit_spec]
  have hpowR : (2 : ℤ_[2]) ^ r = 2 * 2 ^ (r - 1) := by
    calc
      (2 : ℤ_[2]) ^ r = 2 ^ ((r - 1) + 1) := by congr 1; omega
      _ = 2 ^ (r - 1) * 2 := pow_succ _ _
      _ = 2 * 2 ^ (r - 1) := by ring
  rw [hpowR]
  push_cast
  ring

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  [T2Space (GalK K)] in
/-- A general-h odd shear adjusts an epsilon-true selected orientation to an exact pivot. -/
theorem mpc_familySelection_true_exists_exactPivot_of_shiftH
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r true eta)
    (e : OrientedContinuousMulEquiv
      (chiM alpha (handleCount FP (.Mpc alpha r true eta)))
      (chiCycKTwo (K := K)))
    (hshift : MpcPivShiftH alpha (handleCount FP (.Mpc alpha r true eta))) :
    ∃ _hr : B.r = r, 1 ≤ r ∧
      ∃ e' : OrientedContinuousMulEquiv
        (chiM alpha (handleCount FP (.Mpc alpha r true eta)))
        (chiCycKTwo (K := K)),
        ∃ gamma : ℤ_[2]ˣ,
          toAdd (transport (nuUrKTwo B).toMonoidHom e'.1
            ((nuUrKTwo B).continuous_toFun.comp e'.1.continuous_toFun)
              (dmC alpha (handleCount FP (.Mpc alpha r true eta)))) =
            (gamma : ℤ_[2]) * 2 ^ r := by
  obtain ⟨hr, hrpos, hB⟩ := mpc_familySelection_true_B_exact B FF S hbranch
  let nu := transport (nuUrKTwo B).toMonoidHom e.1
    ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun)
  obtain ⟨Psi, hPsi, hpivot⟩ := exists_exactPivot_of_shiftH hshift nu
    (chiKerLevel_of_level B hr e) (hB e) hrpos
  exact ⟨hr, hrpos, mpcPivCompH e Psi hPsi, hpivot⟩

omit [T2Space (GalK K)] in
/-- Conditional arbitrary-h corrected RN residual.  The premise is exactly the missing
general-h odd shear; all handle correction and canonical scaling are discharged downstream. -/
theorem mpcRowResidualRN_of_familySelection_true_of_shiftH
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r true eta)
    (horient : Nonempty (OrientedContinuousMulEquiv
      (chiM alpha (handleCount FP (.Mpc alpha r true eta)))
      (chiCycKTwo (K := K))))
    (hshift : MpcPivShiftH alpha (handleCount FP (.Mpc alpha r true eta))) :
    let d : MpcDisplayFor eta :=
      Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
    ∃ G : GenAsmBranch K B,
      G.pres = .Mpc alpha r true d.display
        (handleCount FP (.Mpc alpha r true eta)) ∧
      Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  obtain ⟨e⟩ := horient
  obtain ⟨_hr, _hrpos, e', hpivot⟩ :=
    mpc_familySelection_true_exists_exactPivot_of_shiftH B FF S hbranch e hshift
  exact mpcRowResidualRN_of_familySelection_canonicalScaling
    B FF S hbranch e' hpivot

#print axioms MpcPivShiftH
#print axioms mpcPivShiftH_zero_iff
#print axioms mpcPivShiftH_two_zero
#print axioms exactPivot_comp_iff_of_unit_C
#print axioms mpcPivCompH
#print axioms exists_exactPivot_of_shiftH
#print axioms mpc_familySelection_true_B_exact
#print axioms mpc_familySelection_true_exists_exactPivot_of_shiftH
#print axioms mpcRowResidualRN_of_familySelection_true_of_shiftH

end
end GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary

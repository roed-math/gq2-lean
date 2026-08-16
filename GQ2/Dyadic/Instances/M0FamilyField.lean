/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.FieldBranchIdentificationTied

/-!
# General-h compact-M family field realization

On a family-selected `M0` branch, validity supplies `2 <= alpha`, the level equation supplies
`B.r = 0`, and the degree equation identifies the displayed handle count with the field degree.
At arbitrary handle count, level zero gives an intrinsic unit somewhere on `ker chiM`.

Unlike the compact-N plane, however, the compact-M canonical pivot cannot be created from a
handle-supported unit by the available chi-preserving frame moves: those moves fix `C0`, while
the compact-M core stabilizer preserves the parity of its value. Thus the general-h tied branch
constructor below honestly retains both the oriented equivalence and the canonical `C0`-pivot
unit. No determinant or corrected word-certificate claim is made here.
-/

namespace GQ2.Dyadic.Instances.M0FamilyField

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.FieldBranchId
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.FieldBranchIdentificationTied

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- The unramified marking transported to a general-handle compact-M core. -/
def m0Transport (B : MarkedRecip Rec K) {alpha h : ℕ}
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) :
    ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]) where
  toFun x := nuUrKTwo B (e.1 x)
  map_one' := by rw [map_one, map_one]
  map_mul' x y := by rw [map_mul, map_mul]
  continuous_toFun := (nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- Level zero supplies an intrinsic `ker chiM` unit at every handle count.

This does not imply that the value at `dmC` is a unit when handles are present. -/
theorem mChiKerUnimodular_of_level_zero_general
    (B : MarkedRecip Rec K) {alpha h : ℕ} (hr : B.r = 0)
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) :
    MChiKerUnimodular alpha h (m0Transport B e) := by
  obtain ⟨gbar, hgchi, hgnu⟩ := B.nu_ker_chi_ge 1
  obtain ⟨g, rfl⟩ := surjective_toAbK K gbar
  let q : maxProPQuotient 2 (GalK K) := maxProPMk 2 (GalK K) g
  let x : (DM alpha h : Type) := e.1.symm q
  refine ⟨x, ?_, ?_⟩
  · calc
      chiM alpha h x = chiCycKTwo (K := K) (e.1 x) := (e.2 x).symm
      _ = chiCycKAb K (toAbK K g) := by
        rw [e.1.apply_symm_apply, chiCycKAb_toAbK, chiCycKTwo_maxProPMk]
      _ = 1 := hgchi
  · change IsUnit (Multiplicative.toAdd (nuUrKTwo B (e.1 (e.1.symm q))))
    rw [e.1.apply_symm_apply]
    change IsUnit (Multiplicative.toAdd (nuUrKTwo B (maxProPMk 2 (GalK K) g)))
    rw [nuUrKTwo_maxProPMk, hgnu, hr, pow_zero, one_mul]
    exact isUnit_one

/-- A selected compact-M branch determines the tied canonical field branch once its canonical
`C0` pivot is assumed to have unit marking. -/
theorem m0GenAsmBranch_of_familySelection_tied
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha)
    (e : OrientedContinuousMulEquiv
      (chiM alpha (handleCount FP (.M0 alpha))) (chiCycKTwo (K := K)))
    (hpivot : IsUnit (Multiplicative.toAdd
      (nuUrKTwo B (e.1 (dmC alpha (handleCount FP (.M0 alpha))))))) :
    ∃ G : GenAsmBranch K B,
      G.pres = .M0 alpha (handleCount FP (.M0 alpha)) ∧
        HEq G.nuP
          (fieldId_mNuZtwo alpha (handleCount FP (.M0 alpha)) (by
            have hv : (BranchData.M0 alpha).Valid := hbranch ▸ S.valid
            exact le_trans (by omega) (BranchData.valid_M0_iff.mp hv))) := by
  have hvalid := S.valid
  rw [hbranch] at hvalid
  have hdeg : Module.finrank ℚ_[2] K =
      (SelectedPresentation.M0 alpha (handleCount FP (.M0 alpha))).degree := by
    have h := S.degree_eq_field
    rw [hbranch] at h
    exact h.symm
  exact fieldId_genAsmBranch_of_orientedM_tied B alpha
    (handleCount FP (.M0 alpha)) hvalid hdeg e hpivot

#print axioms m0Transport
#print axioms mChiKerUnimodular_of_level_zero_general
#print axioms m0GenAsmBranch_of_familySelection_tied

end
end GQ2.Dyadic.Instances.M0FamilyField

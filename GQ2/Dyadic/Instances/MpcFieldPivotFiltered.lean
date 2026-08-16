/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcGeneralHandleFamilyCanonical
import GQ2.Dyadic.Instances.MpcPivot

/-!
# The filtered field pivot for positive-level procyclic M rows

The family selector identifies the exact ideal `nu(ker chi) = 2^r Z_2`, but the distinguished
`C` coordinate lies inside `ker chi`.  Its image modulo `2^r` is therefore always zero.  The
first potentially nonzero datum is the next divided digit

`(nu(C) / 2^r) mod 2`.

This module defines that digit without a division operation, proves that it is `1` exactly when
the existing Mpc pivot holds, and records what the selector does and does not supply.  Exactness
of the bundle level produces some kernel element of value `2^r`; it does not force that value on
`C`.

The last section proves this boundary is sharp with a concrete core marking.  On `DM 2 0`, the
marking `mpcNuPadic 2 2 1 0 1` has `nu(B) = 1` and `nu(C) = 4`.  Its kernel image is nevertheless
exactly `2 Z_2`, because the odd `B` row supplies every value `2z`.  Thus exact level one and the
full lower level clause coexist with failure of the distinguished level-one pivot.
-/

namespace GQ2.Dyadic.Instances.MpcFieldPivotFiltered

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.Instances.MpcGeneralHandleRealization
open GQ2.Dyadic.Instances.MpcGeneralHandleFamily
open GQ2.Dyadic.Instances.MpcGeneralHandleCertificate
open GQ2.Dyadic.Instances.MpcPiv

/-! ## The divided pivot digit -/

/-- The unique coefficient left after dividing the distinguished `C` value by the level ideal.
The defining level clause supplies existence; cancellation in `Z_2` supplies uniqueness. -/
noncomputable def mpcFilteredPivotCoefficient {alpha r h : ℕ}
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (hlev : MpcChiKerLevelH alpha r h nu) : ℤ_[2] :=
  Classical.choose (hlev (dmC alpha h) (chiM_dmC alpha h))

theorem mpcFilteredPivotCoefficient_spec {alpha r h : ℕ}
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (hlev : MpcChiKerLevelH alpha r h nu) :
    toAdd (nu (dmC alpha h)) = 2 ^ r * mpcFilteredPivotCoefficient nu hlev :=
  Classical.choose_spec (hlev (dmC alpha h) (chiM_dmC alpha h))

/-- The first mod-two digit beyond the quotient seen by `lambdaAt`. -/
noncomputable def mpcFilteredPivotDigit {alpha r h : ℕ}
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (hlev : MpcChiKerLevelH alpha r h nu) : ZMod 2 :=
  mParityZ (mpcFilteredPivotCoefficient nu hlev)

/-- The digit is independent of the chosen factorization of the `C` value by `2^r`. -/
theorem mpcFilteredPivotDigit_eq_parity_of_factor {alpha r h : ℕ}
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (hlev : MpcChiKerLevelH alpha r h nu) (y : ℤ_[2])
    (hy : toAdd (nu (dmC alpha h)) = 2 ^ r * y) :
    mpcFilteredPivotDigit nu hlev = mParityZ y := by
  have hcancel : mpcFilteredPivotCoefficient nu hlev = y := by
    apply mul_left_cancel₀ (pow_ne_zero r (by norm_num : (2 : ℤ_[2]) ≠ 0))
    rw [← mpcFilteredPivotCoefficient_spec nu hlev, hy]
  rw [mpcFilteredPivotDigit, hcancel]

/-- The exact Mpc pivot is precisely nonvanishing of the first divided digit. -/
theorem mpcExactPivot_iff_filteredPivotDigit {alpha r h : ℕ}
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (hlev : MpcChiKerLevelH alpha r h nu) :
    (∃ gamma : ℤ_[2]ˣ,
      toAdd (nu (dmC alpha h)) = (gamma : ℤ_[2]) * 2 ^ r) ↔
      mpcFilteredPivotDigit nu hlev = 1 := by
  constructor
  · rintro ⟨gamma, hgamma⟩
    rw [mpcFilteredPivotDigit]
    apply mParityZ_of_isUnit
    have hcoeff : (gamma : ℤ_[2]) = mpcFilteredPivotCoefficient nu hlev := by
      apply mul_left_cancel₀ (pow_ne_zero r (by norm_num : (2 : ℤ_[2]) ≠ 0))
      calc
        2 ^ r * (gamma : ℤ_[2]) = (gamma : ℤ_[2]) * 2 ^ r := by ring
        _ = toAdd (nu (dmC alpha h)) := hgamma.symm
        _ = 2 ^ r * mpcFilteredPivotCoefficient nu hlev :=
          mpcFilteredPivotCoefficient_spec nu hlev
    rw [← hcoeff]
    exact gamma.isUnit
  · intro hdigit
    have hunit : IsUnit (mpcFilteredPivotCoefficient nu hlev) :=
      mIsUnit_of_parity_one (by simpa only [mpcFilteredPivotDigit] using hdigit)
    refine ⟨hunit.unit, ?_⟩
    rw [mpcFilteredPivotCoefficient_spec nu hlev, IsUnit.unit_spec]
    ring

/-! ## Field and selector audit -/

section Field

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- The divided pivot digit transported from a chosen oriented field equivalence. -/
noncomputable def mpcFieldPivotDigit (B : MarkedRecip Rec K) {alpha r h : ℕ}
    (hr : B.r = r)
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) : ZMod 2 :=
  mpcFilteredPivotDigit
    (transport (nuUrKTwo B).toMonoidHom e.1
      ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun))
    (chiKerLevel_of_level B hr e)

/-- The field-side exact pivot is exactly the transported divided digit. -/
theorem mpcFieldExactPivot_iff_digit (B : MarkedRecip Rec K) {alpha r h : ℕ}
    (hr : B.r = r)
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) :
    (∃ gamma : ℤ_[2]ˣ,
      toAdd (transport (nuUrKTwo B).toMonoidHom e.1
        ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun) (dmC alpha h)) =
          (gamma : ℤ_[2]) * 2 ^ r) ↔
      mpcFieldPivotDigit B hr e = 1 :=
  mpcExactPivot_iff_filteredPivotDigit _ (chiKerLevel_of_level B hr e)

/-- Exactness of the bundle level is attained somewhere on the transported core kernel. -/
theorem exists_mpcExactKernelValue (B : MarkedRecip Rec K) {alpha r h : ℕ}
    (hr : B.r = r)
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) :
    ∃ x : (DM alpha h : Type), chiM alpha h x = 1 ∧
      toAdd (transport (nuUrKTwo B).toMonoidHom e.1
        ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun) x) = 2 ^ r := by
  obtain ⟨gbar, hgchi, hgnu⟩ := B.nu_ker_chi_ge 1
  obtain ⟨g, rfl⟩ := surjective_toAbK K gbar
  refine ⟨e.1.symm (maxProPMk 2 (GalK K) g), ?_, ?_⟩
  · have he : chiCycKTwo (K := K) (e.1 (e.1.symm (maxProPMk 2 (GalK K) g))) =
        chiM alpha h (e.1.symm (maxProPMk 2 (GalK K) g)) := e.2 _
    rw [e.1.apply_symm_apply, chiCycKTwo_maxProPMk, ← chiCycKAb_toAbK] at he
    exact he.symm.trans hgchi
  · change toAdd (nuUrKTwo B
      (e.1 (e.1.symm (maxProPMk 2 (GalK K) g)))) = 2 ^ r
    rw [e.1.apply_symm_apply, nuUrKTwo_maxProPMk, hgnu, ← hr, mul_one]

/-- Exact selector audit.  Selection identifies `B.r = r` and the exact kernel image.  Its
remaining `C`-coordinate content is precisely nonvanishing of the next divided digit. -/
theorem mpc_familySelection_level_exact_and_pivot_iff_digit
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta)
    (e : OrientedContinuousMulEquiv
      (chiM alpha (handleCount FP (.Mpc alpha r epsilon eta)))
      (chiCycKTwo (K := K))) :
    ∃ hr : B.r = r,
      (∃ x : (DM alpha (handleCount FP (.Mpc alpha r epsilon eta)) : Type),
        chiM alpha (handleCount FP (.Mpc alpha r epsilon eta)) x = 1 ∧
          toAdd (transport (nuUrKTwo B).toMonoidHom e.1
            ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun) x) = 2 ^ r) ∧
      ((∃ gamma : ℤ_[2]ˣ,
        toAdd (transport (nuUrKTwo B).toMonoidHom e.1
          ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun)
            (dmC alpha (handleCount FP (.Mpc alpha r epsilon eta)))) =
              (gamma : ℤ_[2]) * 2 ^ r) ↔
        mpcFieldPivotDigit B hr e = 1) := by
  have hr : B.r = r := by
    have hs := S.level_eq
    rw [hbranch] at hs
    exact hs.symm
  exact ⟨hr, exists_mpcExactKernelValue B hr e,
    mpcFieldExactPivot_iff_digit B hr e⟩

end Field

/-! ## Exact-level counterexample -/

/-- A level-one kernel marking whose distinguished `C` coordinate has level two. -/
noncomputable def mpcFilteredLevelCounterexample :
    ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]) :=
  mpcNuPadic 2 2 1 0 1 (by omega)

@[simp] theorem mpcFilteredLevelCounterexample_dmB :
    toAdd (mpcFilteredLevelCounterexample (dmB 2 0)) = 1 := by
  change toAdd (mpcNuPadic 2 2 1 0 1 (by omega) (dmGen 2 0 1)) = 1
  rw [mpcNuPadic_gen_one, toAdd_ofAdd]
  norm_num

@[simp] theorem mpcFilteredLevelCounterexample_dmC :
    toAdd (mpcFilteredLevelCounterexample (dmC 2 0)) = 4 := by
  change toAdd (mpcNuPadic 2 2 1 0 1 (by omega) (dmGen 2 0 2)) = 4
  rw [mpcNuPadic_gen_two, toAdd_ofAdd]
  rfl

/-- The counterexample satisfies the complete level-one upper clause. -/
theorem mpcFilteredLevelCounterexample_chiKerLevel :
    MpcChiKerLevelH 2 1 0 mpcFilteredLevelCounterexample := by
  intro x hx
  obtain ⟨m, y, hmy⟩ := mpcPiv_kerChi_le mpcFilteredLevelCounterexample hx
  refine ⟨2 * m + y, ?_⟩
  rw [mpcFilteredLevelCounterexample_dmB, mpcFilteredLevelCounterexample_dmC] at hmy
  rw [pow_one]
  linear_combination hmy

/-- The counterexample also attains every value in the exact level-one ideal. -/
theorem mpcFilteredLevelCounterexample_exactKernel (z : ℤ_[2]) :
    ∃ x : (DM 2 0 : Type), chiM 2 0 x = 1 ∧
      toAdd (mpcFilteredLevelCounterexample x) = 2 * z := by
  apply mpcPiv_kerChi_full_of_odd_dmB mpcFilteredLevelCounterexample
  exact ⟨0, by rw [mpcFilteredLevelCounterexample_dmB]; ring⟩

/-- Despite exact kernel level one, the distinguished `C` value is not a unit times `2`. -/
theorem mpcFilteredLevelCounterexample_not_exactPivot :
    ¬ ∃ gamma : ℤ_[2]ˣ,
      toAdd (mpcFilteredLevelCounterexample (dmC 2 0)) =
        (gamma : ℤ_[2]) * 2 ^ 1 := by
  rintro ⟨gamma, hgamma⟩
  rw [mpcFilteredLevelCounterexample_dmC] at hgamma
  have hle := GQ2.Dyadic.Instances.MpcCert.mpcCert_le_of_two_pow_eq gamma.isUnit
    (r := 1) (s := 2) (y := 1) (by
      norm_num at hgamma ⊢
      exact hgamma.symm)
  omega

#print axioms mpcFilteredPivotCoefficient
#print axioms mpcFilteredPivotDigit
#print axioms mpcExactPivot_iff_filteredPivotDigit
#print axioms mpcFieldPivotDigit
#print axioms mpcFieldExactPivot_iff_digit
#print axioms exists_mpcExactKernelValue
#print axioms mpc_familySelection_level_exact_and_pivot_iff_digit
#print axioms mpcFilteredLevelCounterexample
#print axioms mpcFilteredLevelCounterexample_chiKerLevel
#print axioms mpcFilteredLevelCounterexample_exactKernel
#print axioms mpcFilteredLevelCounterexample_not_exactPivot

end
end GQ2.Dyadic.Instances.MpcFieldPivotFiltered

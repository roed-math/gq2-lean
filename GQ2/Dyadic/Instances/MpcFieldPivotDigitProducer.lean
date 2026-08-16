/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcFieldPivotFiltered

/-!
# Producers and boundaries for the filtered Mpc field pivot

The positive-level pivot digit has two complementary descriptions.  It is nonzero exactly when
the distinguished `C` value does not lie one ideal deeper, in `2^(r+1) Z_2`.  On the rank-four
core `DM 2 0`, the exact kernel image then forces this nonvanishing whenever the `B` row already
lies in `2^r Z_2`: otherwise both generators of the exact kernel image would be too deep.

For a field, `lambdaAt(-1) = 0` supplies precisely that `B` premise.  Consequently an
`epsilon = false` family selection forces the digit to be `1` at every rank-four oriented
equivalence.  This is the strongest unconditional selector producer currently visible: the
parallel `epsilon = true` row has an odd `B` residue, so its `B^2` column already supplies the
whole exact kernel ideal without constraining `C`.

The final counterexample makes that asymmetry formal.  The W169 marking has the complete
level-one, `epsilon = true`, `eta = 1` selector coordinate schema, including exact lower-level
attainment and both `B` and `D` residues, but its filtered pivot digit is zero.  Thus those data
cannot imply the pivot.  For arbitrary orientations the remaining positive statement is the
existing automorphism-orbit problem, recorded here directly in digit language.  A genuinely
cohomological replacement would have to identify this next kernel digit through a higher
restriction or transgression compatibility; the ordinary mod-two cup and `lambdaAt mod 2^r`
both lose it.
-/

namespace GQ2.Dyadic.Instances.MpcFieldPivotDigitProducer

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.Instances.MpcGeneralHandleRealization
open GQ2.Dyadic.Instances.MpcGeneralHandleFamily
open GQ2.Dyadic.Instances.MpcGeneralHandleCertificate
open GQ2.Dyadic.Instances.MpcFieldPivotFiltered
open GQ2.Dyadic.Instances.MpcPiv GQ2.Dyadic.Instances.MpcCert
open GQ2.Dyadic.FieldUnimod

/-! ## The next quotient layer -/

/-- Vanishing of the filtered digit is exactly divisibility of the `C` value by the next power
of two.  This is the quotient-level form of the W169 divided-coefficient definition. -/
theorem mpcFilteredPivotDigit_eq_zero_iff_deeper {alpha r h : ℕ}
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (hlev : MpcChiKerLevelH alpha r h nu) :
    mpcFilteredPivotDigit nu hlev = 0 ↔
      ∃ z : ℤ_[2], toAdd (nu (dmC alpha h)) = 2 ^ (r + 1) * z := by
  constructor
  · intro hdigit
    have hpar : mParityZ (mpcFilteredPivotCoefficient nu hlev) = 0 := by
      simpa only [mpcFilteredPivotDigit] using hdigit
    obtain ⟨z, hz⟩ := (mParityZ_eq_zero_iff _).mp hpar
    refine ⟨z, ?_⟩
    rw [mpcFilteredPivotCoefficient_spec nu hlev, hz, pow_succ]
    ring
  · rintro ⟨z, hz⟩
    rw [mpcFilteredPivotDigit]
    apply (mParityZ_eq_zero_iff _).mpr
    refine ⟨z, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero r (by norm_num : (2 : ℤ_[2]) ≠ 0))
    calc
      2 ^ r * mpcFilteredPivotCoefficient nu hlev =
          toAdd (nu (dmC alpha h)) := (mpcFilteredPivotCoefficient_spec nu hlev).symm
      _ = 2 ^ (r + 1) * z := hz
      _ = 2 ^ r * (2 * z) := by rw [pow_succ]; ring

/-- Nonvanishing of the filtered digit is the complementary sharp-divisibility statement. -/
theorem mpcFilteredPivotDigit_eq_one_iff_not_deeper {alpha r h : ℕ}
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (hlev : MpcChiKerLevelH alpha r h nu) :
    mpcFilteredPivotDigit nu hlev = 1 ↔
      ¬ ∃ z : ℤ_[2], toAdd (nu (dmC alpha h)) = 2 ^ (r + 1) * z := by
  rw [← mpcFilteredPivotDigit_eq_zero_iff_deeper nu hlev]
  constructor
  · intro hone hzero
    rw [hone] at hzero
    exact one_ne_zero hzero
  · intro hnot
    by_contra hone
    apply hnot
    revert hone
    generalize mpcFilteredPivotDigit nu hlev = z
    revert z
    decide

/-! ## Rank-four and field producers -/

/-- On `DM 2 0`, exact kernel level and a `B` row already in `2^r Z_2` force the exact `C`
pivot.  The exact kernel identity from `MpcPivot` is the only core-specific input. -/
theorem mpcExactPivot_of_deepB {r : ℕ}
    (nu : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]))
    (hlev : MpcChiKerLevelH 2 r 0 nu)
    (hB : ∃ beta : ℤ_[2], toAdd (nu (dmB 2 0)) = 2 ^ r * beta)
    (hexact : ∃ x : (DM 2 0 : Type),
      chiM 2 0 x = 1 ∧ toAdd (nu x) = 2 ^ r) :
    ∃ gamma : ℤ_[2]ˣ, toAdd (nu (dmC 2 0)) = (gamma : ℤ_[2]) * 2 ^ r := by
  obtain ⟨c, hc⟩ := hlev (dmC 2 0) (chiM_dmC 2 0)
  obtain ⟨beta, hbeta⟩ := hB
  obtain ⟨x, hxchi, hxnu⟩ := hexact
  obtain ⟨m, y, hmy⟩ := mpcPiv_kerChi_le nu hxchi
  rw [hxnu, hc, hbeta] at hmy
  have hcancel : (1 : ℤ_[2]) = m * c + 2 * y * beta := by
    apply mul_left_cancel₀ (pow_ne_zero r (by norm_num : (2 : ℤ_[2]) ≠ 0))
    calc
      2 ^ r * 1 = 2 ^ r := by ring
      _ = m * (2 ^ r * c) + 2 * y * (2 ^ r * beta) := hmy
      _ = 2 ^ r * (m * c + 2 * y * beta) := by ring
  have hmc : IsUnit (m * c) := by
    have heq : m * c = 1 + 2 * (-(y * beta)) := by
      linear_combination -hcancel
    rw [heq]
    exact isUnit_one_add_two_mul _
  have hcunit : IsUnit c := by
    apply isUnit_of_mul_isUnit_left
    rwa [mul_comm]
  refine ⟨hcunit.unit, ?_⟩
  rw [hc, IsUnit.unit_spec]
  ring

/-- Digit form of `mpcExactPivot_of_deepB`. -/
theorem mpcFilteredPivotDigit_eq_one_of_deepB {r : ℕ}
    (nu : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]))
    (hlev : MpcChiKerLevelH 2 r 0 nu)
    (hB : ∃ beta : ℤ_[2], toAdd (nu (dmB 2 0)) = 2 ^ r * beta)
    (hexact : ∃ x : (DM 2 0 : Type),
      chiM 2 0 x = 1 ∧ toAdd (nu x) = 2 ^ r) :
    mpcFilteredPivotDigit nu hlev = 1 :=
  (mpcExactPivot_iff_filteredPivotDigit nu hlev).mp
    (mpcExactPivot_of_deepB nu hlev hB hexact)

section Field

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- Field-side next-ideal characterization of the filtered pivot digit. -/
theorem mpcFieldPivotDigit_eq_one_iff_not_deeper
    (B : MarkedRecip Rec K) {r : ℕ} (hr : B.r = r)
    (e : OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := K))) :
    mpcFieldPivotDigit B hr e = 1 ↔
      ¬ ∃ z : ℤ_[2],
        toAdd (transport (nuUrKTwo B).toMonoidHom e.1
          ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun) (dmC 2 0)) =
            2 ^ (r + 1) * z :=
  mpcFilteredPivotDigit_eq_one_iff_not_deeper _ (chiKerLevel_of_level B hr e)

/-- Exact field level supplies the kernel witness, so a deep `B` row alone produces the digit. -/
theorem mpcFieldPivotDigit_eq_one_of_deepB (B : MarkedRecip Rec K) {r : ℕ}
    (hr : B.r = r)
    (e : OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := K)))
    (hB : ∃ beta : ℤ_[2],
      toAdd (transport (nuUrKTwo B).toMonoidHom e.1
        ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun) (dmB 2 0)) =
          2 ^ r * beta) :
    mpcFieldPivotDigit B hr e = 1 := by
  apply mpcFilteredPivotDigit_eq_one_of_deepB _ (chiKerLevel_of_level B hr e) hB
  exact exists_mpcExactKernelValue B hr e

/-- The intrinsic field equation `lambdaAt(-1) = 0` produces the filtered digit at every
rank-four oriented equivalence. -/
theorem mpcFieldPivotDigit_eq_one_of_lambdaAt_neg_one_eq_zero
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) {r : ℕ}
    (hr : B.r = r)
    (hneg : (-1 : ℤ_[2]ˣ) ∈ (B.fieldMarkedPair FF).C)
    (hlambda : (B.fieldMarkedPair FF).lambdaAt (-1) hneg = 0)
    (e : OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := K))) :
    mpcFieldPivotDigit B hr e = 1 := by
  apply mpcFieldPivotDigit_eq_one_of_deepB B hr e
  obtain ⟨w, hw⟩ := residue_of_lambdaAt B FF hr hneg 0
    (by simpa only [map_zero] using hlambda) e (chiM_dmB 2 0)
  exact ⟨w, by simpa only [zero_add] using hw⟩

/-- An `epsilon = false` selection has `lambdaAt(-1) = 0`; therefore its rank-four digit is
`1` for every choice of oriented equivalence. -/
theorem mpc_familySelection_false_rankFour_digit_all
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc 2 r false eta) :
    ∃ hr : B.r = r,
      ∀ e : OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := K)),
        mpcFieldPivotDigit B hr e = 1 := by
  have hr : B.r = r := by
    have hs := S.level_eq
    rw [hbranch] at hs
    exact hs.symm
  obtain ⟨hneg, _hunit, hnegrow, _hunitrow⟩ := familyMpc_lambda_rows S hbranch
  have hlambda : (B.fieldMarkedPair FF).lambdaAt (-1) hneg = 0 := by
    calc
      _ = PadicInt.toZModPow (B.fieldMarkedPair FF).r 0 := by
        simpa [p, epsVal] using hnegrow
      _ = 0 := map_zero _
  refine ⟨hr, fun e ↦ ?_⟩
  exact mpcFieldPivotDigit_eq_one_of_lambdaAt_neg_one_eq_zero
    B FF hr hneg hlambda e

/-- For a general rank-four field orientation, existence of some digit-one orientation is
exactly the established chi-preserving automorphism-orbit problem. -/
theorem mpc_exists_fieldPivotDigit_iff_orbit (B : MarkedRecip Rec K) {r : ℕ}
    (hr : B.r = r)
    (e : OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := K))) :
    (∃ e' : OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := K)),
      mpcFieldPivotDigit B hr e' = 1) ↔
      ∃ Psi : ContinuousMulEquiv (DM 2 0 : Type) (DM 2 0 : Type),
        (∀ x, chiM 2 0 (Psi x) = chiM 2 0 x) ∧
          ∃ gamma : ℤ_[2]ˣ,
            toAdd (fieldUni_nuPullbackM B e (Psi (dmC 2 0))) =
              (gamma : ℤ_[2]) * 2 ^ r := by
  constructor
  · rintro ⟨e', hdigit⟩
    apply (mpcPiv_pivot_iff_orbit B e).mp
    exact ⟨e', (mpcFieldExactPivot_iff_digit B hr e').mpr hdigit⟩
  · intro horbit
    obtain ⟨e', hpivot⟩ := (mpcPiv_pivot_iff_orbit B e).mpr horbit
    exact ⟨e', (mpcFieldExactPivot_iff_digit B hr e').mp hpivot⟩

end Field

/-! ## The `epsilon = true` no-go -/

@[simp] theorem mpcFilteredLevelCounterexample_dmD :
    toAdd (mpcFilteredLevelCounterexample (dmD 2 0)) = 1 := by
  change toAdd (mpcNuPadic 2 2 1 0 1 (by omega) (dmGen 2 0 3)) = 1
  rw [mpcNuPadic_gen_three, toAdd_ofAdd]
  norm_num

/-- The next digit of the W169 exact-level counterexample is zero. -/
theorem mpcFilteredLevelCounterexample_digit_eq_zero :
    mpcFilteredPivotDigit mpcFilteredLevelCounterexample
      mpcFilteredLevelCounterexample_chiKerLevel = 0 := by
  rw [mpcFilteredPivotDigit_eq_parity_of_factor
    mpcFilteredLevelCounterexample mpcFilteredLevelCounterexample_chiKerLevel 2 (by
      rw [mpcFilteredLevelCounterexample_dmC, pow_one]
      norm_num)]
  simpa only [mul_one] using mParityZ_two_mul 1

/-- The counterexample satisfies the complete level, lower-level, `D`, and `B` coordinate schema
of the selected `(alpha,r,epsilon,eta) = (2,1,true,1)` row, while its digit is zero. -/
theorem mpcFilteredLevelCounterexample_true_selector_schema :
    MpcChiKerLevelH 2 1 0 mpcFilteredLevelCounterexample ∧
      (∀ z : ℤ_[2], ∃ x : (DM 2 0 : Type),
        chiM 2 0 x = 1 ∧ toAdd (mpcFilteredLevelCounterexample x) = 2 * z) ∧
      (∃ w : ℤ_[2],
        toAdd (mpcFilteredLevelCounterexample (dmD 2 0)) = 1 + 2 ^ 1 * w) ∧
      (∃ w : ℤ_[2],
        toAdd (mpcFilteredLevelCounterexample (dmB 2 0)) =
          (p true 1 : ℤ_[2]) + 2 ^ 1 * w) ∧
      mpcFilteredPivotDigit mpcFilteredLevelCounterexample
        mpcFilteredLevelCounterexample_chiKerLevel = 0 := by
  refine ⟨mpcFilteredLevelCounterexample_chiKerLevel,
    mpcFilteredLevelCounterexample_exactKernel, ⟨0, ?_⟩, ⟨0, ?_⟩,
    mpcFilteredLevelCounterexample_digit_eq_zero⟩
  · rw [mpcFilteredLevelCounterexample_dmD]
    norm_num
  · rw [mpcFilteredLevelCounterexample_dmB]
    norm_num [p, epsVal]

#print axioms mpcFilteredPivotDigit_eq_zero_iff_deeper
#print axioms mpcFilteredPivotDigit_eq_one_iff_not_deeper
#print axioms mpcExactPivot_of_deepB
#print axioms mpcFilteredPivotDigit_eq_one_of_deepB
#print axioms mpcFieldPivotDigit_eq_one_iff_not_deeper
#print axioms mpcFieldPivotDigit_eq_one_of_deepB
#print axioms mpcFieldPivotDigit_eq_one_of_lambdaAt_neg_one_eq_zero
#print axioms mpc_familySelection_false_rankFour_digit_all
#print axioms mpc_exists_fieldPivotDigit_iff_orbit
#print axioms mpcFilteredLevelCounterexample_dmD
#print axioms mpcFilteredLevelCounterexample_digit_eq_zero
#print axioms mpcFilteredLevelCounterexample_true_selector_schema

end
end GQ2.Dyadic.Instances.MpcFieldPivotDigitProducer

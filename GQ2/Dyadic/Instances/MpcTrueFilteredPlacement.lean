/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcFieldPivotDigitProducer

/-!
# The epsilon-true filtered Mpc placement

On an `epsilon = true` selected Mpc row, the `B` value has exact level `r - 1` at every
rank-four oriented equivalence.  Consequently `B ^ 2` already supplies an exact level-`r`
element of `ker chi`; the level and lower-level arithmetic cannot constrain the divided `C`
digit.

This module identifies the remaining placement condition exactly.  An odd shear means that a
chi-preserving automorphism has a `C` row

`nu(Psi C) = m * nu(C) + 2 * y * nu(B)`

with odd `y`.  For an epsilon-true row, an exact pivot exists in the oriented-equivalence orbit
if and only if the current digit is already one or such an odd shear exists.  This disjunction
is independent of which base equivalence is used because its left side is existential over the
whole orbit.

The repository's open `MpcPivShift 2` supplies the odd shear uniformly, but no unconditional
producer of that shift is known.  Thus the selector, norm, lambda, and exact kernel APIs reduce
the true branch to this orbit problem; they do not solve it.
-/

namespace GQ2.Dyadic.Instances.MpcTrueFilteredPlacement

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.Instances.MpcGeneralHandleCertificate
open GQ2.Dyadic.Instances.MpcGeneralHandleFamily
open GQ2.Dyadic.Instances.MpcGeneralHandleRealization
open GQ2.Dyadic.Instances.MpcFieldPivotFiltered
open GQ2.Dyadic.Instances.MpcFieldPivotDigitProducer
open GQ2.Dyadic.Instances.MpcPiv
open GQ2.Dyadic.Instances.MpcRow
open GQ2.Dyadic.Instances.MpcCert
open GQ2.Dyadic.FieldUnimod

/-- A chi-preserving orbit element whose `C` row has an odd coefficient in the `2 B`
direction. -/
def MpcOddShearOrbit
    (nu : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2])) : Prop :=
  ∃ Psi : ContinuousMulEquiv (DM 2 0 : Type) (DM 2 0 : Type),
    (∀ x, chiM 2 0 (Psi x) = chiM 2 0 x) ∧
      ∃ m y w : ℤ_[2],
        toAdd (nu (Psi (dmC 2 0))) =
            m * toAdd (nu (dmC 2 0)) + 2 * y * toAdd (nu (dmB 2 0)) ∧
          y = 1 + 2 * w

/-- The unresolved uniform `M6` shift supplies an odd shear for every marking. -/
theorem mpcOddShearOrbit_of_shift (hshift : MpcPivShift 2)
    (nu : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2])) :
    MpcOddShearOrbit nu := by
  obtain ⟨Psi, hPsi, hrow⟩ := hshift
  refine ⟨Psi, hPsi, 1, 1, 0, ?_, ?_⟩
  · rw [hrow nu]
    ring
  · ring

/-- At positive level with the epsilon-true `B` row, orbit exactness is precisely the
dichotomy between an already nonzero divided digit and an odd `B` shear. -/
theorem mpcOrbitExactPivot_iff_digit_or_oddShear {r : ℕ}
    (nu : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]))
    (hr : 1 ≤ r) (hlev : MpcChiKerLevelH 2 r 0 nu)
    (hB : ∃ beta : ℤ_[2]ˣ,
      toAdd (nu (dmB 2 0)) = (beta : ℤ_[2]) * 2 ^ (r - 1)) :
    (∃ Psi : ContinuousMulEquiv (DM 2 0 : Type) (DM 2 0 : Type),
      (∀ x, chiM 2 0 (Psi x) = chiM 2 0 x) ∧
        ∃ gamma : ℤ_[2]ˣ,
          toAdd (nu (Psi (dmC 2 0))) = (gamma : ℤ_[2]) * 2 ^ r) ↔
      mpcFilteredPivotDigit nu hlev = 1 ∨ MpcOddShearOrbit nu := by
  obtain ⟨beta, hbeta⟩ := hB
  have hpow : (2 : ℤ_[2]) ^ (r + 1) = 4 * 2 ^ (r - 1) := by
    rw [show r + 1 = (r - 1) + 2 by omega, pow_add]
    norm_num
    ring
  have hpowR : (2 : ℤ_[2]) ^ r = 2 * 2 ^ (r - 1) := by
    calc
      (2 : ℤ_[2]) ^ r = 2 ^ ((r - 1) + 1) := by congr 1; omega
      _ = 2 ^ (r - 1) * 2 := pow_succ _ _
      _ = 2 * 2 ^ (r - 1) := by ring
  have oddShear_of_orbit
      (hdigit : mpcFilteredPivotDigit nu hlev = 0)
      {Psi : ContinuousMulEquiv (DM 2 0 : Type) (DM 2 0 : Type)}
      (hPsi : ∀ x, chiM 2 0 (Psi x) = chiM 2 0 x)
      {gamma : ℤ_[2]ˣ}
      (hgamma : toAdd (nu (Psi (dmC 2 0))) = (gamma : ℤ_[2]) * 2 ^ r) :
      MpcOddShearOrbit nu := by
    obtain ⟨z, hz⟩ :=
      (mpcFilteredPivotDigit_eq_zero_iff_deeper nu hlev).mp hdigit
    obtain ⟨m, y, hshape⟩ := mpcPiv_orbit_shape nu Psi hPsi
    refine ⟨Psi, hPsi, m, y, ?_⟩
    rcases mpcRow_even_or_odd y with ⟨y', hy⟩ | ⟨w, hw⟩
    · exfalso
      have hdeep : (gamma : ℤ_[2]) * 2 ^ r =
          2 ^ (r + 1) * (m * z + y' * (beta : ℤ_[2])) := by
        rw [← hgamma, hshape, hz, hbeta, hy, hpow]
        ring
      exact (by omega : ¬ r + 1 ≤ r)
        (mpcCert_le_of_two_pow_eq gamma.isUnit hdeep)
    · exact ⟨w, hshape, hw⟩
  have orbit_of_oddShear
      (hdigit : mpcFilteredPivotDigit nu hlev = 0)
      (hshear : MpcOddShearOrbit nu) :
      ∃ Psi : ContinuousMulEquiv (DM 2 0 : Type) (DM 2 0 : Type),
        (∀ x, chiM 2 0 (Psi x) = chiM 2 0 x) ∧
          ∃ gamma : ℤ_[2]ˣ,
            toAdd (nu (Psi (dmC 2 0))) = (gamma : ℤ_[2]) * 2 ^ r := by
    obtain ⟨z, hz⟩ :=
      (mpcFilteredPivotDigit_eq_zero_iff_deeper nu hlev).mp hdigit
    obtain ⟨Psi, hPsi, m, y, w, hshape, hy⟩ := hshear
    let coeff : ℤ_[2] := 2 * m * z + y * (beta : ℤ_[2])
    have hcoeff : IsUnit coeff := by
      apply mIsUnit_of_parity_one
      change mParityZ (2 * m * z + y * (beta : ℤ_[2])) = 1
      rw [mParityZ_add,
        show 2 * m * z = 2 * (m * z) by ring, mParityZ_two_mul, zero_add,
        mParityZ_mul, hy, mParityZ_add, mParityZ_one,
        mParityZ_two_mul, add_zero, mParityZ_of_isUnit beta.isUnit, one_mul]
    refine ⟨Psi, hPsi, hcoeff.unit, ?_⟩
    rw [hshape, hz, hbeta, hpow, IsUnit.unit_spec]
    change m * (4 * 2 ^ (r - 1) * z) +
        2 * y * ((beta : ℤ_[2]) * 2 ^ (r - 1)) = coeff * 2 ^ r
    rw [hpowR]
    simp only [coeff]
    ring
  constructor
  · rintro ⟨Psi, hPsi, gamma, hgamma⟩
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1)
        (mpcFilteredPivotDigit nu hlev) with hdigit | hdigit
    · exact Or.inr (oddShear_of_orbit hdigit hPsi hgamma)
    · exact Or.inl hdigit
  · rintro (hdigit | hshear)
    · exact ⟨ContinuousMulEquiv.refl _, fun _ ↦ rfl,
        (mpcExactPivot_iff_filteredPivotDigit nu hlev).mpr hdigit⟩
    · rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1)
          (mpcFilteredPivotDigit nu hlev) with hdigit | hdigit
      · exact orbit_of_oddShear hdigit hshear
      · exact ⟨ContinuousMulEquiv.refl _, fun _ ↦ rfl,
          (mpcExactPivot_iff_filteredPivotDigit nu hlev).mpr hdigit⟩

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  [T2Space (GalK K)] in
/-- The epsilon-true lambda row puts `B` at exact level `r - 1` for every rank-four
orientation. -/
theorem mpc_familySelection_true_rankFour_B_exact
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc 2 r true eta) :
    ∃ _hr : B.r = r, 1 ≤ r ∧
      ∀ e : OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := K)),
        ∃ beta : ℤ_[2]ˣ,
          toAdd (fieldUni_nuPullbackM B e (dmB 2 0)) =
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
  refine ⟨hr, hrpos, fun e ↦ ?_⟩
  obtain ⟨w, hw⟩ := residue_of_lambdaAt B FF hr hneg (p true r : ℤ_[2])
    hnegrow e (chiM_dmB 2 0)
  let beta : ℤ_[2]ˣ := (GQ2.isUnit_one_add_two_mul w).unit
  refine ⟨beta, ?_⟩
  change toAdd (fieldUni_nuPullbackM B e (dmB 2 0)) = _ at hw ⊢
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
/-- The exact kernel value on an epsilon-true row is already attained by `B ^ 2`, independently
of the `C` digit. -/
theorem mpc_familySelection_true_rankFour_B_sq_exactKernel
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc 2 r true eta) :
    ∃ _hr : B.r = r, 1 ≤ r ∧
      ∀ e : OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := K)),
        ∃ beta : ℤ_[2]ˣ,
          chiM 2 0 (dmB 2 0 ^ 2) = 1 ∧
            toAdd (fieldUni_nuPullbackM B e (dmB 2 0 ^ 2)) =
              (beta : ℤ_[2]) * 2 ^ r := by
  obtain ⟨hr, hrpos, hB⟩ :=
    mpc_familySelection_true_rankFour_B_exact B FF S hbranch
  refine ⟨hr, hrpos, fun e ↦ ?_⟩
  obtain ⟨beta, hbeta⟩ := hB e
  refine ⟨beta, ?_, ?_⟩
  · rw [map_pow, chiM_dmB]
    norm_num
  · rw [map_pow, toAdd_pow, hbeta]
    have hpowR : (2 : ℤ_[2]) ^ r = 2 * 2 ^ (r - 1) := by
      calc
        (2 : ℤ_[2]) ^ r = 2 ^ ((r - 1) + 1) := by congr 1; omega
        _ = 2 ^ (r - 1) * 2 := pow_succ _ _
        _ = 2 * 2 ^ (r - 1) := by ring
    rw [hpowR]
    ring

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  [T2Space (GalK K)] in
/-- The sharp choice-independent placement statement for an epsilon-true selection: a
digit-one orientation exists exactly when the base digit is one or its orbit has an odd shear.
-/
theorem mpc_familySelection_true_rankFour_exists_digit_iff
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc 2 r true eta) :
    ∃ hr : B.r = r, 1 ≤ r ∧
      ∀ e : OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := K)),
        (∃ e' : OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := K)),
          mpcFieldPivotDigit B hr e' = 1) ↔
            mpcFieldPivotDigit B hr e = 1 ∨
              MpcOddShearOrbit (fieldUni_nuPullbackM B e) := by
  obtain ⟨hr, hrpos, hB⟩ :=
    mpc_familySelection_true_rankFour_B_exact B FF S hbranch
  refine ⟨hr, hrpos, fun e ↦ ?_⟩
  exact (mpc_exists_fieldPivotDigit_iff_orbit B hr e).trans
    (mpcOrbitExactPivot_iff_digit_or_oddShear
      (fieldUni_nuPullbackM B e) hrpos (chiKerLevel_of_level B hr e) (hB e))

#print axioms MpcOddShearOrbit
#print axioms mpcOddShearOrbit_of_shift
#print axioms mpcOrbitExactPivot_iff_digit_or_oddShear
#print axioms mpc_familySelection_true_rankFour_B_exact
#print axioms mpc_familySelection_true_rankFour_B_sq_exactKernel
#print axioms mpc_familySelection_true_rankFour_exists_digit_iff

end
end GQ2.Dyadic.Instances.MpcTrueFilteredPlacement

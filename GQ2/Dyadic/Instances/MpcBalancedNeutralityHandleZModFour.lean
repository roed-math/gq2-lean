/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedNeutralityHandleRange

/-!
# The neutral relative quotient is `(ZMod 4)^2`

W223 identifies the one-handle relative source modulo exact row-neutral representatives with
the intrinsic range of its two finite handle coordinates.  This module computes that range.
At depth `k ≥ 3`, every relative handle coordinate is divisible by `2^(k-2)` modulo `2^k`,
and the pure powers of the standard `U` and `V` generators realize the two digits
independently.  Multiplication by `2^(k-2)` therefore embeds `ZMod 4` in each coordinate and
has exactly the required range.

The resulting equivalence identifies `OneHandleRelativeCModuloNeutral k hk` with two copies
of multiplicative `ZMod 4`; in particular the quotient has cardinality sixteen.  The theorem
does not assert that the handle-coordinate map fills its larger ambient
`ZMod (2^k) × ZMod (2^k)` target.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedNeutralityHandleZModFour

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcOneHandleDefectObstruction
open GQ2.Dyadic.Instances.MpcFixedCRelativeBracketObstruction
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Dyadic.Instances.MpcBalancedNeutralityTorsionRow
open GQ2.Dyadic.Instances.MpcBalancedNeutralitySourceQuotient
open GQ2.Dyadic.Instances.MpcBalancedNeutralityHandleRange
open GQ2.Roe.Labute

private abbrev U : DM 2 1 := dmGen 2 1 (handleIdxU (0 : Fin 1))
private abbrev V : DM 2 1 := dmGen 2 1 (handleIdxV (0 : Fin 1))

private theorem four_mul_two_pow_sub_two (k : ℕ) (hk : 3 ≤ k) :
    4 * 2 ^ (k - 2) = 2 ^ k := by
  conv_rhs => rw [show k = (k - 2) + 2 by omega]
  rw [pow_add]
  norm_num [mul_comm]

/-- The canonical copy of `ZMod 4` in the depth-`k` coordinate group. -/
noncomputable def deepDigitAddHom (k : ℕ) (hk : 3 ≤ k) :
    ZMod 4 →+ ZMod (2 ^ k) :=
  ZMod.lift 4 ⟨zmultiplesHom _ ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k)), by
    rw [zmultiplesHom_apply, natCast_zsmul]
    have h := congrArg (fun n : ℕ => (n : ZMod (2 ^ k)))
      (four_mul_two_pow_sub_two k hk)
    simpa [nsmul_eq_mul] using h⟩

@[simp] theorem deepDigitAddHom_one (k : ℕ) (hk : 3 ≤ k) :
    deepDigitAddHom k hk 1 = ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k)) := by
  rw [deepDigitAddHom, show (1 : ZMod 4) = (1 : ℤ) by norm_num, ZMod.lift_coe]
  simp [zmultiplesHom]

theorem deepDigitAddHom_natCast (k : ℕ) (hk : 3 ≤ k) (a : ℕ) :
    deepDigitAddHom k hk (a : ZMod 4) =
      ((a * 2 ^ (k - 2) : ℕ) : ZMod (2 ^ k)) := by
  rw [deepDigitAddHom, show (a : ZMod 4) = ((a : ℤ) : ZMod 4) by norm_num,
    ZMod.lift_coe, zmultiplesHom_apply, natCast_zsmul]
  simp [nsmul_eq_mul]

private theorem deepDigit_natCast_ne_zero
    (k : ℕ) (hk : 3 ≤ k) (a : ℕ) (ha0 : 0 < a) (ha4 : a < 4) :
    ((a * 2 ^ (k - 2) : ℕ) : ZMod (2 ^ k)) ≠ 0 := by
  intro hz
  have hdvd : 2 ^ k ∣ a * 2 ^ (k - 2) :=
    (ZMod.natCast_eq_zero_iff _ _).mp hz
  have hpos : 0 < a * 2 ^ (k - 2) := mul_pos ha0 (pow_pos (by omega) _)
  have hle : 2 ^ k ≤ a * 2 ^ (k - 2) := Nat.le_of_dvd hpos hdvd
  have hlt : a * 2 ^ (k - 2) < 4 * 2 ^ (k - 2) :=
    Nat.mul_lt_mul_of_pos_right ha4 (pow_pos (by omega) _)
  rw [four_mul_two_pow_sub_two k hk] at hlt
  omega

private theorem zmod_four_cases (z : ZMod 4) :
    z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem deepDigitAddHom_injective (k : ℕ) (hk : 3 ≤ k) :
    Function.Injective (deepDigitAddHom k hk) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  rcases zmod_four_cases z with rfl | rfl | rfl | rfl
  · rfl
  · exfalso
    change deepDigitAddHom k hk ((1 : ℕ) : ZMod 4) = 0 at hz
    rw [deepDigitAddHom_natCast] at hz
    exact (deepDigit_natCast_ne_zero k hk 1 (by omega) (by omega)) hz
  · exfalso
    change deepDigitAddHom k hk ((2 : ℕ) : ZMod 4) = 0 at hz
    rw [deepDigitAddHom_natCast] at hz
    exact (deepDigit_natCast_ne_zero k hk 2 (by omega) (by omega)) hz
  · exfalso
    change deepDigitAddHom k hk ((3 : ℕ) : ZMod 4) = 0 at hz
    rw [deepDigitAddHom_natCast] at hz
    exact (deepDigit_natCast_ne_zero k hk 3 (by omega) (by omega)) hz

private theorem four_dvd_two_pow (k : ℕ) (hk : 3 ≤ k) : 4 ∣ 2 ^ k :=
  ⟨2 ^ (k - 2), (four_mul_two_pow_sub_two k hk).symm⟩

private theorem deepDigitAddHom_castHom
    (k : ℕ) (hk : 3 ≤ k) (x : ZMod (2 ^ k)) :
    deepDigitAddHom k hk
        (ZMod.castHom (four_dvd_two_pow k hk) (ZMod 4) x) =
      ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k)) * x := by
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  rw [map_intCast]
  change deepDigitAddHom k hk ((n : ℤ) : ZMod 4) =
    ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k)) * (n : ZMod (2 ^ k))
  rw [deepDigitAddHom, ZMod.lift_coe, zmultiplesHom_apply]
  simp [mul_comm]

/-- The two canonical depth-`k` handle digits. -/
noncomputable def deepUVHom (k : ℕ) (hk : 3 ≤ k) :
    Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →*
      Multiplicative (ZMod (2 ^ k)) × Multiplicative (ZMod (2 ^ k)) :=
  (AddMonoidHom.toMultiplicative (deepDigitAddHom k hk)).prodMap
    (AddMonoidHom.toMultiplicative (deepDigitAddHom k hk))

theorem deepUVHom_injective (k : ℕ) (hk : 3 ≤ k) :
    Function.Injective (deepUVHom k hk) := by
  intro z w h
  apply Prod.ext
  · apply toAdd.injective
    apply deepDigitAddHom_injective k hk
    exact congrArg (fun p => toAdd p.1) h
  · apply toAdd.injective
    apply deepDigitAddHom_injective k hk
    exact congrArg (fun p => toAdd p.2) h

@[simp] private theorem oneHandleUMod_handleV (k : ℕ) :
    oneHandleUMod k V = 1 := by
  change ofAdd (PadicInt.toZModPow k
    (toAdd (oneHandleHandleUHom V))) = 1
  rw [oneHandleHandleUHom_V, map_zero]
  rfl

@[simp] private theorem oneHandleVMod_handleU (k : ℕ) :
    oneHandleVMod k U = 1 := by
  change ofAdd (PadicInt.toZModPow k
    (toAdd (oneHandleHandleVHom U))) = 1
  rw [oneHandleHandleVHom_U, map_zero]
  rfl

private def deepHandleWord (k : ℕ)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) : DM 2 1 :=
  U ^ (2 ^ (k - 2) * (toAdd z.1).val) *
    V ^ (2 ^ (k - 2) * (toAdd z.2).val)

private theorem deepHandleWord_mem (k : ℕ) (hk : 3 ≤ k)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :
    deepHandleWord k z ∈ twoCentralSeries (DM 2 1) (k - 1) := by
  apply Subgroup.mul_mem
  · rw [pow_mul]
    have h := Subgroup.pow_mem (twoCentralSeries (DM 2 1) (k - 2 + 1))
      (pow_two_pow_mem_twoCentralSeries_succ (G := (DM 2 1 : Type)) U (k - 2))
      (toAdd z.1).val
    simpa [show k - 2 + 1 = k - 1 by omega] using h
  · rw [pow_mul]
    have h := Subgroup.pow_mem (twoCentralSeries (DM 2 1) (k - 2 + 1))
      (pow_two_pow_mem_twoCentralSeries_succ (G := (DM 2 1 : Type)) V (k - 2))
      (toAdd z.2).val
    simpa [show k - 2 + 1 = k - 1 by omega] using h

private theorem dmForgetHandles_deepHandleWord (k : ℕ)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :
    dmForgetHandles 2 1 (deepHandleWord k z) = 1 := by
  rw [deepHandleWord, map_mul, map_pow, map_pow,
    dmForgetHandles_handleU, dmForgetHandles_handleV, one_pow, one_pow, mul_one]

private def deepHandleRelative (k : ℕ) (hk : 3 ≤ k)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :
    oneHandleRelativeLambdaImage (k - 1) (k + 1) :=
  ⟨levelMk (DM 2 1) (k + 1) (deepHandleWord k z),
    (mem_oneHandleRelativeLambdaImage_iff_exists_exact (by omega) _).mpr
      ⟨deepHandleWord k z, deepHandleWord_mem k hk z,
        dmForgetHandles_deepHandleWord k z, rfl⟩⟩

private theorem deepDigitAddHom_val (k : ℕ) (hk : 3 ≤ k) (z : ZMod 4) :
    deepDigitAddHom k hk z =
      ((2 ^ (k - 2) * z.val : ℕ) : ZMod (2 ^ k)) := by
  calc
    deepDigitAddHom k hk z = deepDigitAddHom k hk (z.val : ZMod 4) :=
      congrArg (deepDigitAddHom k hk) (ZMod.natCast_zmod_val z).symm
    _ = ((z.val * 2 ^ (k - 2) : ℕ) : ZMod (2 ^ k)) :=
      deepDigitAddHom_natCast k hk z.val
    _ = ((2 ^ (k - 2) * z.val : ℕ) : ZMod (2 ^ k)) := by rw [mul_comm]

@[simp] theorem oneHandleRelativeUVLevel_deepHandleRelative
    (k : ℕ) (hk : 3 ≤ k)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :
    oneHandleRelativeUVLevel k (deepHandleRelative k hk z) = deepUVHom k hk z := by
  apply Prod.ext
  · change oneHandleUMod k (deepHandleWord k z) =
      ofAdd (deepDigitAddHom k hk (toAdd z.1))
    rw [deepHandleWord, map_mul, map_pow, map_pow,
      oneHandleUMod_handleU, oneHandleUMod_handleV, one_pow, mul_one,
      ← ofAdd_nsmul, nsmul_eq_mul, deepDigitAddHom_val]
    simp
  · change oneHandleVMod k (deepHandleWord k z) =
      ofAdd (deepDigitAddHom k hk (toAdd z.2))
    rw [deepHandleWord, map_mul, map_pow, map_pow,
      oneHandleVMod_handleU, oneHandleVMod_handleV, one_pow, one_mul,
      ← ofAdd_nsmul, nsmul_eq_mul, deepDigitAddHom_val]
    simp

private theorem handleCoordinate_mem_deepPowerRange
    {k : ℕ}
    (f : ContinuousMonoidHom (DM 2 1) (Multiplicative (ZMod (2 ^ k))))
    (hk : 3 ≤ k) {e : DM 2 1}
    (he : e ∈ twoCentralSeries (DM 2 1) (k - 1)) :
    f e ∈ (powMonoidHom (2 ^ (k - 2))).range := by
  have him : f e ∈
      twoCentralSeries (Multiplicative (ZMod (2 ^ k))) (k - 1) :=
    map_twoCentralSeries_le f.toMonoidHom f.continuous_toFun (k - 1) ⟨e, he, rfl⟩
  have him' : f e ∈
      twoCentralSeries (Multiplicative (ZMod (2 ^ k))) (k - 2 + 1) := by
    simpa only [show k - 2 + 1 = k - 1 by omega] using him
  exact evenStratumShift_twoCentralSeries_le_pow (k - 2) him'

private theorem pow_eq_deepDigit_cast
    (k : ℕ) (hk : 3 ≤ k) (x : Multiplicative (ZMod (2 ^ k))) :
    x ^ (2 ^ (k - 2)) =
      ofAdd (deepDigitAddHom k hk
        (ZMod.castHom (four_dvd_two_pow k hk) (ZMod 4) (toAdd x))) := by
  apply toAdd.injective
  change (2 ^ (k - 2) : ℕ) • toAdd x =
    deepDigitAddHom k hk
      (ZMod.castHom (four_dvd_two_pow k hk) (ZMod 4) (toAdd x))
  rw [nsmul_eq_mul, deepDigitAddHom_castHom]

/-- The intrinsic handle-digit range is exactly the product of the two canonical deep
`ZMod 4` digits. -/
theorem oneHandleRelativeUVLevel_range_eq_deepUVHom_range
    (k : ℕ) (hk : 3 ≤ k) :
    (oneHandleRelativeUVLevel k).range = (deepUVHom k hk).range := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    obtain ⟨e, he, _, hex⟩ :=
      (mem_oneHandleRelativeLambdaImage_iff_exists_exact
        (by omega : k - 1 ≤ k + 1) x.1).mp x.2
    obtain ⟨u, hu⟩ := handleCoordinate_mem_deepPowerRange
      (oneHandleUMod k) hk he
    obtain ⟨v, hv⟩ := handleCoordinate_mem_deepPowerRange
      (oneHandleVMod k) hk he
    let z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) :=
      (ofAdd (ZMod.castHom (four_dvd_two_pow k hk) (ZMod 4) (toAdd u)),
        ofAdd (ZMod.castHom (four_dvd_two_pow k hk) (ZMod 4) (toAdd v)))
    refine ⟨z, ?_⟩
    change deepUVHom k hk z = oneHandleUVLevel k x.1
    rw [← hex]
    apply Prod.ext
    · change ofAdd (deepDigitAddHom k hk
          (ZMod.castHom (four_dvd_two_pow k hk) (ZMod 4) (toAdd u))) =
        oneHandleUMod k e
      rw [← hu]
      exact (pow_eq_deepDigit_cast k hk u).symm
    · change ofAdd (deepDigitAddHom k hk
          (ZMod.castHom (four_dvd_two_pow k hk) (ZMod 4) (toAdd v))) =
        oneHandleVMod k e
      rw [← hv]
      exact (pow_eq_deepDigit_cast k hk v).symm
  · rintro y ⟨z, rfl⟩
    exact ⟨deepHandleRelative k hk z,
      oneHandleRelativeUVLevel_deepHandleRelative k hk z⟩

/-- The pair of depth-`k` digits is multiplicatively equivalent to its intrinsic range. -/
noncomputable def deepUVEquivRange (k : ℕ) (hk : 3 ≤ k) :
    Multiplicative (ZMod 4) × Multiplicative (ZMod 4) ≃*
      (deepUVHom k hk).range := by
  apply MulEquiv.ofBijective (deepUVHom k hk).rangeRestrict
  constructor
  · intro z w h
    apply deepUVHom_injective k hk
    exact Subtype.ext_iff.mp h
  · rintro ⟨y, z, hz⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact hz

/-- The intrinsic handle-coordinate range is two independent copies of `ZMod 4`. -/
noncomputable def deepUVEquivRelativeRange (k : ℕ) (hk : 3 ≤ k) :
    Multiplicative (ZMod 4) × Multiplicative (ZMod 4) ≃*
      (oneHandleRelativeUVLevel k).range :=
  (deepUVEquivRange k hk).trans
    (MulEquiv.subgroupCongr
      (oneHandleRelativeUVLevel_range_eq_deepUVHom_range k hk).symm)

/-- The relative `C` source modulo exact neutral representatives is canonically
`(ZMod 4)^2`. -/
noncomputable def oneHandleRelativeCModuloNeutralEquivZModFourSq
    (k : ℕ) (hk : 3 ≤ k) :
    OneHandleRelativeCModuloNeutral k hk ≃*
      Multiplicative (ZMod 4) × Multiplicative (ZMod 4) :=
  (oneHandleRelativeCModuloNeutralEquivUVRange k hk).trans
    (deepUVEquivRelativeRange k hk).symm

/-- In particular, the relative source modulo neutral representatives has sixteen elements. -/
theorem natCard_oneHandleRelativeCModuloNeutral
    (k : ℕ) (hk : 3 ≤ k) :
    Nat.card (OneHandleRelativeCModuloNeutral k hk) = 16 := by
  rw [Nat.card_congr
    (oneHandleRelativeCModuloNeutralEquivZModFourSq k hk).toEquiv,
    Nat.card_prod]
  change Nat.card (ZMod 4) * Nat.card (ZMod 4) = 16
  norm_num [Nat.card_zmod]

#print axioms deepDigitAddHom
#print axioms deepDigitAddHom_natCast
#print axioms deepDigitAddHom_injective
#print axioms deepUVHom
#print axioms deepUVHom_injective
#print axioms oneHandleRelativeUVLevel_deepHandleRelative
#print axioms oneHandleRelativeUVLevel_range_eq_deepUVHom_range
#print axioms deepUVEquivRange
#print axioms deepUVEquivRelativeRange
#print axioms oneHandleRelativeCModuloNeutralEquivZModFourSq
#print axioms natCard_oneHandleRelativeCModuloNeutral

end
end GQ2.Dyadic.Instances.MpcBalancedNeutralityHandleZModFour

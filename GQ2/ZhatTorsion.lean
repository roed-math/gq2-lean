/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.ProfiniteOddReflection
import Mathlib.Data.ZMod.QuotientGroup

/-!
# The full profinite integers have no torsion

At a level of index `N`, examine the compatible coordinate at level `n*N`.
If the `n`th power vanishes there, the integer representative is divisible by
`N`, so the original coordinate vanishes.  This handles all primes at once.
-/

namespace GQ2

open CategoryTheory
open Multiplicative

noncomputable section

/-- A nonzero natural power detects identity in the full profinite integers. -/
theorem Zhat.eq_one_of_pow_eq_one (x : Zhat) {n : ℕ} (hn : n ≠ 0)
    (hx : x ^ n = 1) : x = 1 := by
  apply Subtype.ext
  funext H
  let N := H.toSubgroup.index
  have hN : N ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  let Msub : Subgroup (Multiplicative ℤ) :=
    (AddSubgroup.zmultiples ((n * N : ℕ) : ℤ)).toSubgroup
  have hMindex : Msub.index = n * N := by
    simp only [Msub, AddSubgroup.index_toSubgroup, Int.index_zmultiples, Int.natAbs_natCast]
  letI : Msub.FiniteIndex := ⟨by rw [hMindex]; exact mul_ne_zero hn hN⟩
  let M : FiniteIndexNormalSubgroup (GrpCat.of (Multiplicative ℤ)) :=
    { toSubgroup := Msub }
  have hMH : M ≤ H := by
    intro a ha
    let k : ℤ := (a : Multiplicative ℤ).toAdd
    change ofAdd k ∈ Msub at ha
    change ofAdd k ∈ H.toSubgroup
    rw [ofAdd_mem_iff_index_dvd] at ha ⊢
    rw [hMindex, Nat.cast_mul] at ha
    exact dvd_of_mul_left_dvd ha
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (x.val M)
  let k : ℤ := (a : Multiplicative ℤ).toAdd
  have hak : a = ofAdd k := rfl
  have hm : (QuotientGroup.mk a : Multiplicative ℤ ⧸ M.toSubgroup) ^ n = 1 := by
    rw [ha]
    exact congrArg (fun y : Zhat => y.val M) hx
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hm
  have hdiv : (Msub.index : ℤ) ∣ (n : ℤ) * k := by
    apply ofAdd_mem_iff_index_dvd.mp
    rw [hak, ← ofAdd_nsmul, nsmul_eq_mul] at hm
    exact hm
  rw [hMindex, Nat.cast_mul] at hdiv
  have haH : a ∈ H.toSubgroup := by
    rw [hak, ofAdd_mem_iff_index_dvd]
    exact (mul_dvd_mul_iff_left (Int.natCast_ne_zero.mpr hn)).mp hdiv
  have hcompat := x.property (show M ⟶ H from hMH.hom)
  change QuotientGroup.map M.toSubgroup H.toSubgroup (MonoidHom.id _) hMH
    (x.val M) = x.val H at hcompat
  rw [← hcompat, ← ha]
  exact (QuotientGroup.eq_one_iff a).mpr haH

/-- The integer generator acts as the identity on the full profinite exponents. -/
theorem Zhat.ofInt_one_zpowHat (x : Zhat) : (Zhat.ofInt 1) ^ᶻ x = x := by
  exact congrFun (Zhat.funext_ofInt (continuous_zpowHat _) continuous_id
    (fun n => by simp only [zpowHat_ofInt, Zhat.ofInt_one_zpow, id_eq])) x

/-- Exponentiation of an integer element is ordinary powering of the exponent. -/
theorem Zhat.ofInt_zpowHat (n : ℤ) (x : Zhat) : (Zhat.ofInt n) ^ᶻ x = x ^ n := by
  rw [← Zhat.ofInt_one_zpow, ← zpowHat_zpow, Zhat.ofInt_one_zpowHat]

/-- Profinite powering on the full profinite integers is symmetric in its two arguments. -/
theorem Zhat.zpowHat_comm (x y : Zhat) : x ^ᶻ y = y ^ᶻ x := by
  exact congrFun (Zhat.funext_ofInt (continuous_zpowHat_base y)
    (continuous_zpowHat y) (fun n => by rw [Zhat.ofInt_zpowHat, zpowHat_ofInt])) x

/-- A continuous endomorphism is determined by the integer generator. -/
theorem Zhat.endomorphism_eq_zpowHat (f : ContinuousMonoidHom Zhat Zhat) (x : Zhat) :
    f x = (f (Zhat.ofInt 1)) ^ᶻ x := by
  nth_rw 1 [← Zhat.ofInt_one_zpowHat x]
  exact map_zpowHat f _ _

/-- Continuous endomorphisms of the full profinite integers commute. -/
theorem Zhat.endomorphisms_commute (f g : ContinuousMonoidHom Zhat Zhat) (x : Zhat) :
    f (g x) = g (f x) := by
  rw [Zhat.endomorphism_eq_zpowHat g x, map_zpowHat,
    Zhat.endomorphism_eq_zpowHat f x, map_zpowHat]
  congr 1
  rw [Zhat.endomorphism_eq_zpowHat f (g (Zhat.ofInt 1)),
    Zhat.endomorphism_eq_zpowHat g (f (Zhat.ofInt 1))]
  exact Zhat.zpowHat_comm _ _

/-- A continuous endomorphism whose image contains a nonzero integer is injective.
In particular this applies when its image has finite index; no generator or sign
normalization is required. -/
theorem Zhat.endomorphism_injective_of_integer_mem_range
    (f : ContinuousMonoidHom Zhat Zhat) {n : ℕ} (hn : n ≠ 0)
    (hmem : Zhat.ofInt (n : ℤ) ∈ f.toMonoidHom.range) : Function.Injective f := by
  apply (injective_iff_map_eq_one f.toMonoidHom).mpr
  intro x hx
  change f x = 1 at hx
  obtain ⟨y, hy⟩ := hmem
  change f y = Zhat.ofInt (n : ℤ) at hy
  let g : ContinuousMonoidHom Zhat Zhat := (zpowHatHom y).hom
  have hcomm := Zhat.endomorphisms_commute f g x
  rw [hx, map_one] at hcomm
  change f (y ^ᶻ x) = 1 at hcomm
  rw [map_zpowHat, hy, Zhat.ofInt_zpowHat, zpow_natCast] at hcomm
  exact Zhat.eq_one_of_pow_eq_one x hn hcomm

/-- The finite-index-image form of the preceding criterion. -/
theorem Zhat.endomorphism_injective_of_finiteIndex_range
    (f : ContinuousMonoidHom Zhat Zhat) [f.toMonoidHom.range.FiniteIndex] :
    Function.Injective f := by
  have hcomm : ∀ x y : Zhat, x * y = y * x := by
    intro x y
    have hfirst : ∀ n : ℤ, Zhat.ofInt n * y = y * Zhat.ofInt n := by
      intro n
      exact congrFun (Zhat.funext_ofInt (continuous_const_mul _) (continuous_mul_const _)
        (fun m => by rw [← Zhat.ofInt_add, ← Zhat.ofInt_add, Int.add_comm])) y
    exact congrFun (Zhat.funext_ofInt (continuous_mul_const _) (continuous_const_mul _)
      hfirst) x
  letI : CommGroup Zhat := { (inferInstance : Group Zhat) with mul_comm := hcomm }
  apply Zhat.endomorphism_injective_of_integer_mem_range f
    (Subgroup.FiniteIndex.index_ne_zero (H := f.toMonoidHom.range))
  rw [← Zhat.ofInt_one_zpow, zpow_natCast]
  exact Subgroup.pow_index_mem _ _

#print axioms Zhat.eq_one_of_pow_eq_one
#print axioms Zhat.endomorphisms_commute
#print axioms Zhat.endomorphism_injective_of_integer_mem_range
#print axioms Zhat.endomorphism_injective_of_finiteIndex_range

end
end GQ2

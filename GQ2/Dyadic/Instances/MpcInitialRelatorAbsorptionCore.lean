/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/

import GQ2.Dyadic.Instances.MpcInitialRelatorBase
import GQ2.Dyadic.Instances.MpcInitialRelatorRange

/-!
# All-degree initial-relator absorption core

The five cutoff-four witnesses are propagated along the canonical square towers.
Continuous coordinates reduce an arbitrary `ℤ_[2]` coefficient to the canonical
power at each rung; the remaining exponent is absorbed one level deeper.
-/

namespace GQ2.Dyadic.Instances.MpcMk

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcWord GQ2.Dyadic.Instances.MpcBld
open GQ2.Dyadic.Instances.MpcLad GQ2.Dyadic.Instances.MpcSx
open GQ2.Dyadic.Instances.MpcOrb
open GQ2.Roe.Labute GQ2.Dyadic.SqCore

noncomputable section

private abbrev A : (DM 2 0 : Type) := dmA 2 0
private abbrev B : (DM 2 0 : Type) := dmB 2 0
private abbrev C : (DM 2 0 : Type) := dmC 2 0
private abbrev D : (DM 2 0 : Type) := dmD 2 0

def mpcMkRawUt {r : Nat} (x : (DM 2 0 : Type))
    (hx : x ∈ twoCentralSeries (DM 2 0 : Type) r) : MpcMkRawSource r :=
  (1, ⟨x, hx⟩, 1, 1)

def mpcMkRawUm {r : Nat} (x : (DM 2 0 : Type))
    (hx : x ∈ twoCentralSeries (DM 2 0 : Type) r) : MpcMkRawSource r :=
  (1, 1, ⟨x, hx⟩, 1)

def mpcMkRawUn {r : Nat} (x : (DM 2 0 : Type))
    (hx : x ∈ twoCentralSeries (DM 2 0 : Type) r) : MpcMkRawSource r :=
  (1, 1, 1, ⟨x, hx⟩)

def mpcMkCanonUtC : (k : Nat) → MpcMkRawSource (k + 2)
  | 0 => MpcInitialRelatorBase.baseUtCSource
  | k + 1 => mpcMkRawSquare (mpcMkCanonUtC k)

def mpcMkCanonUtD : (k : Nat) → MpcMkRawSource (k + 2)
  | 0 => MpcInitialRelatorBase.baseUtDSource
  | k + 1 => mpcMkRawSquare (mpcMkCanonUtD k)

def mpcMkCanonUmB : (k : Nat) → MpcMkRawSource (k + 2)
  | 0 => MpcInitialRelatorBase.baseUmBSource
  | k + 1 => mpcMkRawSquare (mpcMkCanonUmB k)

def mpcMkCanonUmC : (k : Nat) → MpcMkRawSource (k + 2)
  | 0 => MpcInitialRelatorBase.baseUmCSource
  | k + 1 => mpcMkRawSquare (mpcMkCanonUmC k)

def mpcMkCanonUnD : (k : Nat) → MpcMkRawSource (k + 2)
  | 0 => MpcInitialRelatorBase.baseUnDSource
  | k + 1 => mpcMkRawSquare (mpcMkCanonUnD k)

theorem mpcMkCanonUtC_value (k : Nat) :
    (mpcMkCanonUtC k).2.1.1 = C ^ (2 ^ (k + 1)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (mpcMkCanonUtC k).2.1.1 ^ 2 = C ^ (2 ^ (k + 2))
      rw [ih, ← pow_mul]
      congr 1

theorem mpcMkCanonUtD_value (k : Nat) :
    (mpcMkCanonUtD k).2.1.1 = D ^ (2 ^ (k + 1)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (mpcMkCanonUtD k).2.1.1 ^ 2 = D ^ (2 ^ (k + 2))
      rw [ih, ← pow_mul]
      congr 1

theorem mpcMkCanonUmB_value (k : Nat) :
    (mpcMkCanonUmB k).2.2.1.1 = B ^ (2 ^ (k + 1)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (mpcMkCanonUmB k).2.2.1.1 ^ 2 = B ^ (2 ^ (k + 2))
      rw [ih, ← pow_mul]
      congr 1

theorem mpcMkCanonUmC_value (k : Nat) :
    (mpcMkCanonUmC k).2.2.1.1 = C ^ (2 ^ (k + 1)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (mpcMkCanonUmC k).2.2.1.1 ^ 2 = C ^ (2 ^ (k + 2))
      rw [ih, ← pow_mul]
      congr 1

theorem mpcMkCanonUnD_value (k : Nat) :
    (mpcMkCanonUnD k).2.2.2.1 = D ^ (2 ^ (k + 1)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (mpcMkCanonUnD k).2.2.2.1 ^ 2 = D ^ (2 ^ (k + 2))
      rw [ih, ← pow_mul]
      congr 1

private def mpcMkRowDivSub
    (f : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]))
    (m : Nat) : Subgroup (DM 2 0 : Type) where
  carrier := {g | (2 ^ m : ℤ_[2]) ∣ toAdd (f g)}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_mul, toAdd_mul] at ha hb ⊢
    exact dvd_add ha hb
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, map_inv, toAdd_inv] at ha ⊢
    exact ha.neg_right

private theorem mpcMkRowDivSub_closed
    (f : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]))
    (m : Nat) : IsClosed ((mpcMkRowDivSub f m :
      Subgroup (DM 2 0 : Type)) : Set (DM 2 0 : Type)) := by
  have hset : ((mpcMkRowDivSub f m : Subgroup (DM 2 0 : Type)) :
      Set (DM 2 0 : Type)) =
      (fun g : (DM 2 0 : Type) ↦ toAdd (f g)) ⁻¹'
        {x : ℤ_[2] | (2 ^ m : ℤ_[2]) ∣ x} := rfl
  rw [hset]
  have hdiv : IsClosed {x : ℤ_[2] | (2 ^ m : ℤ_[2]) ∣ x} := by
    have himg : {x : ℤ_[2] | (2 ^ m : ℤ_[2]) ∣ x} =
        Set.range (fun y : ℤ_[2] ↦ (2 ^ m : ℤ_[2]) * y) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_range]
      exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩,
        fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩
    rw [himg]
    exact (isCompact_range (continuous_const_mul (2 ^ m : ℤ_[2]))).isClosed
  exact hdiv.preimage
    (continuous_toAdd.comp f.continuous)

theorem mpcMk_row_dvd
    (f : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]))
    {k : Nat} {g : (DM 2 0 : Type)}
    (hg : g ∈ twoCentralSeries (DM 2 0 : Type) k) :
    (2 ^ (k - 1) : ℤ_[2]) ∣ toAdd (f g) := by
  have hmain : ∀ m : Nat,
      twoCentralSeries (DM 2 0 : Type) (m + 1) ≤ mpcMkRowDivSub f m := by
    intro m
    induction m with
    | zero =>
      intro v _
      change (2 ^ 0 : ℤ_[2]) ∣ toAdd (f v)
      rw [pow_zero]
      exact one_dvd _
    | succ m ih =>
      rw [twoCentralSeries_succ (G := (DM 2 0 : Type)) (by omega),
        twoCentralSucc]
      refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_)
        (mpcMkRowDivSub_closed f (m + 1))
      · refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨v, hv, rfl⟩
        change (2 ^ (m + 1) : ℤ_[2]) ∣ toAdd (f (v ^ 2))
        rw [map_pow, toAdd_pow]
        obtain ⟨c, hc⟩ := ih hv
        refine ⟨c, ?_⟩
        rw [hc, pow_succ]
        ring
      · refine Subgroup.commutator_le.2 fun a _ b _ => ?_
        change (2 ^ (m + 1) : ℤ_[2]) ∣
          toAdd (f (a * b * a⁻¹ * b⁻¹))
        simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
        convert dvd_zero (2 ^ (m + 1) : ℤ_[2]) using 1
        all_goals ring
  match k with
  | 0 =>
    rw [Nat.zero_sub, pow_zero]
    exact one_dvd _
  | k + 1 =>
    rw [Nat.add_sub_cancel]
    exact hmain k hg

theorem mpcMk_zpow_dvd_mem
    {g : (DM 2 0 : Type)} {a : ℤ_[2]} {k : Nat}
    (hk : 1 ≤ k) (ha : (2 ^ (k - 1) : ℤ_[2]) ∣ a) :
    zpowZtwo (isProP_DM 2 0) g a ∈
      twoCentralSeries (DM 2 0 : Type) k := by
  obtain ⟨c, rfl⟩ := ha
  have hcast : (((2 ^ (k - 1) : Nat) : ℤ_[2])) =
      (2 : ℤ_[2]) ^ (k - 1) := by push_cast; ring
  have heq : zpowZtwo (isProP_DM 2 0) g
      ((2 : ℤ_[2]) ^ (k - 1) * c) =
      zpowZtwo (isProP_DM 2 0) g c ^ (2 ^ (k - 1)) := by
    rw [← zpowZtwo_natCast (isProP_DM 2 0)
      (zpowZtwo (isProP_DM 2 0) g c) (2 ^ (k - 1)),
      zpowZtwo_zpowZtwo, hcast]
    congr 1
    ring
  rw [heq, ← Nat.sub_add_cancel hk]
  exact pow_two_pow_mem_twoCentralSeries_succ
    (G := (DM 2 0 : Type)) _ (k - 1)

theorem mpcMk_tower_exp_dvd
    (f : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]))
    (g : (DM 2 0 : Type)) (hg : f g = ofAdd (1 : ℤ_[2]))
    {r : Nat} {a : ℤ_[2]}
    (ha : zpowZtwo (isProP_DM 2 0) g a ∈
      twoCentralSeries (DM 2 0 : Type) r) :
    (2 ^ (r - 1) : ℤ_[2]) ∣ a := by
  have h := mpcMk_row_dvd f ha
  rwa [toAdd_map_zpowZtwo (isProP_DM 2 0), hg, toAdd_ofAdd,
    mul_one] at h

theorem mpcMkRawUt_cost_congr {r : Nat} (hr : 2 ≤ r)
    {x y : (DM 2 0 : Type)}
    (hx : x ∈ twoCentralSeries (DM 2 0 : Type) r)
    (hy : y ∈ twoCentralSeries (DM 2 0 : Type) r)
    (hxy : x * y⁻¹ ∈ twoCentralSeries (DM 2 0 : Type) (r + 1)) :
    mpcMkRawCost r hr 1 1 (mpcMkRawUt x hx) =
      mpcMkRawCost r hr 1 1 (mpcMkRawUt y hy) := by
  apply Subtype.ext
  rw [mpcMkRawCost_apply, mpcMkRawCost_apply]
  apply mpcMk_rawCost_congr_of_mod_succ hr 1 1
      1 x 1 1 1 y 1 1
      (by simp) hx (by simp) (by simp)
      (by simp) hy (by simp) (by simp)
      (by simp) hxy (by simp) (by simp)

theorem mpcMkRawUm_cost_congr {r : Nat} (hr : 2 ≤ r)
    {x y : (DM 2 0 : Type)}
    (hx : x ∈ twoCentralSeries (DM 2 0 : Type) r)
    (hy : y ∈ twoCentralSeries (DM 2 0 : Type) r)
    (hxy : x * y⁻¹ ∈ twoCentralSeries (DM 2 0 : Type) (r + 1)) :
    mpcMkRawCost r hr 1 1 (mpcMkRawUm x hx) =
      mpcMkRawCost r hr 1 1 (mpcMkRawUm y hy) := by
  apply Subtype.ext
  rw [mpcMkRawCost_apply, mpcMkRawCost_apply]
  apply mpcMk_rawCost_congr_of_mod_succ hr 1 1
      1 1 x 1 1 1 y 1
      (by simp) (by simp) hx (by simp)
      (by simp) (by simp) hy (by simp)
      (by simp) (by simp) hxy (by simp)

theorem mpcMkRawUn_cost_congr {r : Nat} (hr : 2 ≤ r)
    {x y : (DM 2 0 : Type)}
    (hx : x ∈ twoCentralSeries (DM 2 0 : Type) r)
    (hy : y ∈ twoCentralSeries (DM 2 0 : Type) r)
    (hxy : x * y⁻¹ ∈ twoCentralSeries (DM 2 0 : Type) (r + 1)) :
    mpcMkRawCost r hr 1 1 (mpcMkRawUn x hx) =
      mpcMkRawCost r hr 1 1 (mpcMkRawUn y hy) := by
  apply Subtype.ext
  rw [mpcMkRawCost_apply, mpcMkRawCost_apply]
  apply mpcMk_rawCost_congr_of_mod_succ hr 1 1
      1 1 1 x 1 1 1 y
      (by simp) (by simp) (by simp) hx
      (by simp) (by simp) (by simp) hy
      (by simp) (by simp) (by simp) hxy

theorem mpcMkCanonUtC_other (k : Nat) :
    (mpcMkCanonUtC k).1.1 = 1 ∧
      (mpcMkCanonUtC k).2.2.1.1 = 1 ∧
      (mpcMkCanonUtC k).2.2.2.1 = 1 := by
  induction k with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
      rcases ih with ⟨hs, hm, hn⟩
      exact ⟨by change (mpcMkCanonUtC k).1.1 ^ 2 = 1; rw [hs, one_pow],
        by change (mpcMkCanonUtC k).2.2.1.1 ^ 2 = 1; rw [hm, one_pow],
        by change (mpcMkCanonUtC k).2.2.2.1 ^ 2 = 1; rw [hn, one_pow]⟩

theorem mpcMkCanonUtD_other (k : Nat) :
    (mpcMkCanonUtD k).1.1 = 1 ∧
      (mpcMkCanonUtD k).2.2.1.1 = 1 ∧
      (mpcMkCanonUtD k).2.2.2.1 = 1 := by
  induction k with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
      rcases ih with ⟨hs, hm, hn⟩
      exact ⟨by change (mpcMkCanonUtD k).1.1 ^ 2 = 1; rw [hs, one_pow],
        by change (mpcMkCanonUtD k).2.2.1.1 ^ 2 = 1; rw [hm, one_pow],
        by change (mpcMkCanonUtD k).2.2.2.1 ^ 2 = 1; rw [hn, one_pow]⟩

theorem mpcMkCanonUmB_other (k : Nat) :
    (mpcMkCanonUmB k).1.1 = 1 ∧
      (mpcMkCanonUmB k).2.1.1 = 1 ∧
      (mpcMkCanonUmB k).2.2.2.1 = 1 := by
  induction k with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
      rcases ih with ⟨hs, ht, hn⟩
      exact ⟨by change (mpcMkCanonUmB k).1.1 ^ 2 = 1; rw [hs, one_pow],
        by change (mpcMkCanonUmB k).2.1.1 ^ 2 = 1; rw [ht, one_pow],
        by change (mpcMkCanonUmB k).2.2.2.1 ^ 2 = 1; rw [hn, one_pow]⟩

theorem mpcMkCanonUmC_other (k : Nat) :
    (mpcMkCanonUmC k).1.1 = 1 ∧
      (mpcMkCanonUmC k).2.1.1 = 1 ∧
      (mpcMkCanonUmC k).2.2.2.1 = 1 := by
  induction k with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
      rcases ih with ⟨hs, ht, hn⟩
      exact ⟨by change (mpcMkCanonUmC k).1.1 ^ 2 = 1; rw [hs, one_pow],
        by change (mpcMkCanonUmC k).2.1.1 ^ 2 = 1; rw [ht, one_pow],
        by change (mpcMkCanonUmC k).2.2.2.1 ^ 2 = 1; rw [hn, one_pow]⟩

theorem mpcMkCanonUnD_other (k : Nat) :
    (mpcMkCanonUnD k).1.1 = 1 ∧
      (mpcMkCanonUnD k).2.1.1 = 1 ∧
      (mpcMkCanonUnD k).2.2.1.1 = 1 := by
  induction k with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
      rcases ih with ⟨hs, ht, hm⟩
      exact ⟨by change (mpcMkCanonUnD k).1.1 ^ 2 = 1; rw [hs, one_pow],
        by change (mpcMkCanonUnD k).2.1.1 ^ 2 = 1; rw [ht, one_pow],
        by change (mpcMkCanonUnD k).2.2.1.1 ^ 2 = 1; rw [hm, one_pow]⟩

theorem mpcMk_dvd_next_or_diff_canon {r : Nat} (hr : 2 ≤ r)
    {a : ℤ_[2]} (ha : (2 ^ (r - 1) : ℤ_[2]) ∣ a) :
    (2 ^ r : ℤ_[2]) ∣ a ∨
      (2 ^ r : ℤ_[2]) ∣ a - (2 ^ (r - 1) : ℤ_[2]) := by
  obtain ⟨c, hc⟩ := ha
  have hp : (2 ^ (r - 1) : ℤ_[2]) * 2 = (2 ^ r : ℤ_[2]) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  by_cases htwo : (2 : ℤ_[2]) ∣ c
  · obtain ⟨d, hd⟩ := htwo
    left
    refine ⟨d, ?_⟩
    calc
      a = (2 ^ (r - 1) : ℤ_[2]) * c := hc
      _ = (2 ^ (r - 1) : ℤ_[2]) * (2 * d) := by rw [hd]
      _ = ((2 ^ (r - 1) : ℤ_[2]) * 2) * d := by ring
      _ = (2 ^ r : ℤ_[2]) * d := by rw [hp]
  · obtain ⟨d, hd⟩ :=
      two_dvd_sub_one_of_isUnit (isUnit_of_not_two_dvd htwo)
    right
    refine ⟨d, ?_⟩
    calc
      a - (2 ^ (r - 1) : ℤ_[2]) =
          (2 ^ (r - 1) : ℤ_[2]) * (c - 1) := by rw [hc]; ring
      _ = (2 ^ (r - 1) : ℤ_[2]) * (2 * d) := by rw [hd]
      _ = ((2 ^ (r - 1) : ℤ_[2]) * 2) * d := by ring
      _ = (2 ^ r : ℤ_[2]) * d := by rw [hp]

theorem mpcMk_zpow_diff_mem {r : Nat}
    {g : (DM 2 0 : Type)} {a b : ℤ_[2]}
    (hab : (2 ^ r : ℤ_[2]) ∣ a - b) :
    zpowZtwo (isProP_DM 2 0) g a *
        (zpowZtwo (isProP_DM 2 0) g b)⁻¹ ∈
      twoCentralSeries (DM 2 0 : Type) (r + 1) := by
  have hinv : (zpowZtwo (isProP_DM 2 0) g b)⁻¹ =
      zpowZtwo (isProP_DM 2 0) g (-b) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← zpowZtwo_add, add_neg_cancel, GQ2.SectionThree.zpowZtwo_zero]
  rw [hinv, ← zpowZtwo_add]
  rw [← sub_eq_add_neg]
  apply mpcMk_zpow_dvd_mem (by omega)
  simpa only [Nat.add_sub_cancel] using hab

theorem mpcMk_absorb_ut_of_dvd (k : Nat) (g : (DM 2 0 : Type))
    (canon : MpcMkRawSource (k + 2))
    (hcanon : mpcMkRawCost (k + 2) (by omega) 1 1 canon ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1))
    (hvalue : canon.2.1.1 = g ^ (2 ^ (k + 1)))
    (hother : canon.1.1 = 1 ∧ canon.2.2.1.1 = 1 ∧
      canon.2.2.2.1 = 1)
    (a : ℤ_[2])
    (ha : zpowZtwo (isProP_DM 2 0) g a ∈
      twoCentralSeries (DM 2 0 : Type) (k + 2))
    (hdiv : (2 ^ (k + 1) : ℤ_[2]) ∣ a) :
    mpcMkRawCost (k + 2) (by omega) 1 1
        (mpcMkRawUt (zpowZtwo (isProP_DM 2 0) g a) ha) ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1) := by
  have hpMem : zpowZtwo (isProP_DM 2 0) g
      (2 ^ (k + 1) : ℤ_[2]) ∈
      twoCentralSeries (DM 2 0 : Type) (k + 2) :=
    mpcMk_zpow_dvd_mem (by omega) (by
      simpa only [show k + 2 - 1 = k + 1 by omega] using
        (dvd_refl (2 ^ (k + 1) : ℤ_[2])))
  have hzcanon : zpowZtwo (isProP_DM 2 0) g
      (2 ^ (k + 1) : ℤ_[2]) = g ^ (2 ^ (k + 1)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      zpowZtwo_natCast (isProP_DM 2 0) g (2 ^ (k + 1))
  have hsource : canon = mpcMkRawUt
      (zpowZtwo (isProP_DM 2 0) g (2 ^ (k + 1) : ℤ_[2])) hpMem := by
    apply Prod.ext
    · apply Subtype.ext
      exact hother.1
    · apply Prod.ext
      · apply Subtype.ext
        exact hvalue.trans hzcanon.symm
      · apply Prod.ext
        · apply Subtype.ext
          exact hother.2.1
        · apply Subtype.ext
          exact hother.2.2
  have hcanon' : mpcMkRawCost (k + 2) (by omega) 1 1
      (mpcMkRawUt
        (zpowZtwo (isProP_DM 2 0) g (2 ^ (k + 1) : ℤ_[2])) hpMem) ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1) := by
    rw [← hsource]
    exact hcanon
  have hpar := mpcMk_dvd_next_or_diff_canon (r := k + 2) (by omega) (by
    simpa only [show k + 2 - 1 = k + 1 by omega] using hdiv)
  rcases hpar with heven | hodd
  · have hdeep : zpowZtwo (isProP_DM 2 0) g a ∈
        twoCentralSeries (DM 2 0 : Type) (k + 3) := by
      apply mpcMk_zpow_dvd_mem (by omega)
      simpa only [show k + 3 - 1 = k + 2 by omega] using heven
    have heq := mpcMkRawUt_cost_congr (r := k + 2) (by omega)
      ha (show (1 : (DM 2 0 : Type)) ∈
        twoCentralSeries (DM 2 0 : Type) (k + 2) by simp) (by
          simpa only [inv_one, mul_one] using hdeep)
    rw [heq]
    change mpcMkRawCost (k + 2) (by omega) 1 1
      (1 : MpcMkRawSource (k + 2)) ∈ _
    rw [map_one]
    exact Subgroup.one_mem _
  · have hdiff := mpcMk_zpow_diff_mem (r := k + 2) (g := g)
      (a := a) (b := (2 ^ (k + 1) : ℤ_[2])) (by
        simpa only [show k + 2 - 1 = k + 1 by omega] using hodd)
    have heq := mpcMkRawUt_cost_congr (r := k + 2) (by omega)
      ha hpMem hdiff
    rw [heq]
    exact hcanon'

theorem mpcMk_absorb_um_of_dvd (k : Nat) (g : (DM 2 0 : Type))
    (canon : MpcMkRawSource (k + 2))
    (hcanon : mpcMkRawCost (k + 2) (by omega) 1 1 canon ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1))
    (hvalue : canon.2.2.1.1 = g ^ (2 ^ (k + 1)))
    (hother : canon.1.1 = 1 ∧ canon.2.1.1 = 1 ∧
      canon.2.2.2.1 = 1)
    (a : ℤ_[2])
    (ha : zpowZtwo (isProP_DM 2 0) g a ∈
      twoCentralSeries (DM 2 0 : Type) (k + 2))
    (hdiv : (2 ^ (k + 1) : ℤ_[2]) ∣ a) :
    mpcMkRawCost (k + 2) (by omega) 1 1
        (mpcMkRawUm (zpowZtwo (isProP_DM 2 0) g a) ha) ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1) := by
  have hpMem : zpowZtwo (isProP_DM 2 0) g
      (2 ^ (k + 1) : ℤ_[2]) ∈
      twoCentralSeries (DM 2 0 : Type) (k + 2) :=
    mpcMk_zpow_dvd_mem (by omega) (by
      simpa only [show k + 2 - 1 = k + 1 by omega] using
        (dvd_refl (2 ^ (k + 1) : ℤ_[2])))
  have hzcanon : zpowZtwo (isProP_DM 2 0) g
      (2 ^ (k + 1) : ℤ_[2]) = g ^ (2 ^ (k + 1)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      zpowZtwo_natCast (isProP_DM 2 0) g (2 ^ (k + 1))
  have hsource : canon = mpcMkRawUm
      (zpowZtwo (isProP_DM 2 0) g (2 ^ (k + 1) : ℤ_[2])) hpMem := by
    apply Prod.ext
    · apply Subtype.ext
      exact hother.1
    · apply Prod.ext
      · apply Subtype.ext
        exact hother.2.1
      · apply Prod.ext
        · apply Subtype.ext
          exact hvalue.trans hzcanon.symm
        · apply Subtype.ext
          exact hother.2.2
  have hcanon' : mpcMkRawCost (k + 2) (by omega) 1 1
      (mpcMkRawUm
        (zpowZtwo (isProP_DM 2 0) g (2 ^ (k + 1) : ℤ_[2])) hpMem) ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1) := by
    rw [← hsource]
    exact hcanon
  have hpar := mpcMk_dvd_next_or_diff_canon (r := k + 2) (by omega) (by
    simpa only [show k + 2 - 1 = k + 1 by omega] using hdiv)
  rcases hpar with heven | hodd
  · have hdeep : zpowZtwo (isProP_DM 2 0) g a ∈
        twoCentralSeries (DM 2 0 : Type) (k + 3) := by
      apply mpcMk_zpow_dvd_mem (by omega)
      simpa only [show k + 3 - 1 = k + 2 by omega] using heven
    have heq := mpcMkRawUm_cost_congr (r := k + 2) (by omega)
      ha (show (1 : (DM 2 0 : Type)) ∈
        twoCentralSeries (DM 2 0 : Type) (k + 2) by simp) (by
          simpa only [inv_one, mul_one] using hdeep)
    rw [heq]
    change mpcMkRawCost (k + 2) (by omega) 1 1
      (1 : MpcMkRawSource (k + 2)) ∈ _
    rw [map_one]
    exact Subgroup.one_mem _
  · have hdiff := mpcMk_zpow_diff_mem (r := k + 2) (g := g)
      (a := a) (b := (2 ^ (k + 1) : ℤ_[2])) (by
        simpa only [show k + 2 - 1 = k + 1 by omega] using hodd)
    have heq := mpcMkRawUm_cost_congr (r := k + 2) (by omega)
      ha hpMem hdiff
    rw [heq]
    exact hcanon'

theorem mpcMk_absorb_un_of_dvd (k : Nat) (g : (DM 2 0 : Type))
    (canon : MpcMkRawSource (k + 2))
    (hcanon : mpcMkRawCost (k + 2) (by omega) 1 1 canon ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1))
    (hvalue : canon.2.2.2.1 = g ^ (2 ^ (k + 1)))
    (hother : canon.1.1 = 1 ∧ canon.2.1.1 = 1 ∧
      canon.2.2.1.1 = 1)
    (a : ℤ_[2])
    (ha : zpowZtwo (isProP_DM 2 0) g a ∈
      twoCentralSeries (DM 2 0 : Type) (k + 2))
    (hdiv : (2 ^ (k + 1) : ℤ_[2]) ∣ a) :
    mpcMkRawCost (k + 2) (by omega) 1 1
        (mpcMkRawUn (zpowZtwo (isProP_DM 2 0) g a) ha) ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1) := by
  have hpMem : zpowZtwo (isProP_DM 2 0) g
      (2 ^ (k + 1) : ℤ_[2]) ∈
      twoCentralSeries (DM 2 0 : Type) (k + 2) :=
    mpcMk_zpow_dvd_mem (by omega) (by
      simpa only [show k + 2 - 1 = k + 1 by omega] using
        (dvd_refl (2 ^ (k + 1) : ℤ_[2])))
  have hzcanon : zpowZtwo (isProP_DM 2 0) g
      (2 ^ (k + 1) : ℤ_[2]) = g ^ (2 ^ (k + 1)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      zpowZtwo_natCast (isProP_DM 2 0) g (2 ^ (k + 1))
  have hsource : canon = mpcMkRawUn
      (zpowZtwo (isProP_DM 2 0) g (2 ^ (k + 1) : ℤ_[2])) hpMem := by
    apply Prod.ext
    · apply Subtype.ext
      exact hother.1
    · apply Prod.ext
      · apply Subtype.ext
        exact hother.2.1
      · apply Prod.ext
        · apply Subtype.ext
          exact hother.2.2
        · apply Subtype.ext
          exact hvalue.trans hzcanon.symm
  have hcanon' : mpcMkRawCost (k + 2) (by omega) 1 1
      (mpcMkRawUn
        (zpowZtwo (isProP_DM 2 0) g (2 ^ (k + 1) : ℤ_[2])) hpMem) ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1) := by
    rw [← hsource]
    exact hcanon
  have hpar := mpcMk_dvd_next_or_diff_canon (r := k + 2) (by omega) (by
    simpa only [show k + 2 - 1 = k + 1 by omega] using hdiv)
  rcases hpar with heven | hodd
  · have hdeep : zpowZtwo (isProP_DM 2 0) g a ∈
        twoCentralSeries (DM 2 0 : Type) (k + 3) := by
      apply mpcMk_zpow_dvd_mem (by omega)
      simpa only [show k + 3 - 1 = k + 2 by omega] using heven
    have heq := mpcMkRawUn_cost_congr (r := k + 2) (by omega)
      ha (show (1 : (DM 2 0 : Type)) ∈
        twoCentralSeries (DM 2 0 : Type) (k + 2) by simp) (by
          simpa only [inv_one, mul_one] using hdeep)
    rw [heq]
    change mpcMkRawCost (k + 2) (by omega) 1 1
      (1 : MpcMkRawSource (k + 2)) ∈ _
    rw [map_one]
    exact Subgroup.one_mem _
  · have hdiff := mpcMk_zpow_diff_mem (r := k + 2) (g := g)
      (a := a) (b := (2 ^ (k + 1) : ℤ_[2])) (by
        simpa only [show k + 2 - 1 = k + 1 by omega] using hodd)
    have heq := mpcMkRawUn_cost_congr (r := k + 2) (by omega)
      ha hpMem hdiff
    rw [heq]
    exact hcanon'

theorem mpcMkCanonUtC_range (k : Nat) :
    mpcMkRawCost (k + 2) (by omega) 1 1 (mpcMkCanonUtC k) ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1) := by
  induction k with
  | zero =>
      simpa only [mpcMkCanonUtC] using
        MpcInitialRelatorBase.base_utC_mem
  | succ k ih =>
      simpa only [mpcMkCanonUtC, Nat.succ_eq_add_one] using
        mpcMkRawCost_square_mem_of_mem (r := k + 2)
          (by omega) (by omega) (mpcMkCanonUtC k) ih

theorem mpcMkCanonUtD_range (k : Nat) :
    mpcMkRawCost (k + 2) (by omega) 1 1 (mpcMkCanonUtD k) ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1) := by
  induction k with
  | zero =>
      simpa only [mpcMkCanonUtD] using
        MpcInitialRelatorBase.base_utD_mem
  | succ k ih =>
      simpa only [mpcMkCanonUtD, Nat.succ_eq_add_one] using
        mpcMkRawCost_square_mem_of_mem (r := k + 2)
          (by omega) (by omega) (mpcMkCanonUtD k) ih

theorem mpcMkCanonUmB_range (k : Nat) :
    mpcMkRawCost (k + 2) (by omega) 1 1 (mpcMkCanonUmB k) ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1) := by
  induction k with
  | zero =>
      simpa only [mpcMkCanonUmB] using
        MpcInitialRelatorBase.base_umB_mem
  | succ k ih =>
      simpa only [mpcMkCanonUmB, Nat.succ_eq_add_one] using
        mpcMkRawCost_square_mem_of_mem (r := k + 2)
          (by omega) (by omega) (mpcMkCanonUmB k) ih

theorem mpcMkCanonUmC_range (k : Nat) :
    mpcMkRawCost (k + 2) (by omega) 1 1 (mpcMkCanonUmC k) ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1) := by
  induction k with
  | zero =>
      simpa only [mpcMkCanonUmC] using
        MpcInitialRelatorBase.base_umC_mem
  | succ k ih =>
      simpa only [mpcMkCanonUmC, Nat.succ_eq_add_one] using
        mpcMkRawCost_square_mem_of_mem (r := k + 2)
          (by omega) (by omega) (mpcMkCanonUmC k) ih

theorem mpcMkCanonUnD_range (k : Nat) :
    mpcMkRawCost (k + 2) (by omega) 1 1 (mpcMkCanonUnD k) ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1) := by
  induction k with
  | zero =>
      simpa only [mpcMkCanonUnD] using
        MpcInitialRelatorBase.base_unD_mem
  | succ k ih =>
      simpa only [mpcMkCanonUnD, Nat.succ_eq_add_one] using
        mpcMkRawCost_square_mem_of_mem (r := k + 2)
          (by omega) (by omega) (mpcMkCanonUnD k) ih

theorem mpcMk_absorb_utC (k : Nat) (a : ℤ_[2])
    (ha : mpcMkTowerC a ∈
      twoCentralSeries (DM 2 0 : Type) (k + 2)) :
    mpcMkRawCost (k + 2) (by omega) 1 1
        (mpcMkRawUt (mpcMkTowerC a) ha) ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1) := by
  apply mpcMk_absorb_ut_of_dvd k C (mpcMkCanonUtC k)
    (mpcMkCanonUtC_range k) (mpcMkCanonUtC_value k)
    (mpcMkCanonUtC_other k) a (by simpa only [mpcMkTowerC] using ha)
  have hdiv := mpcMk_tower_exp_dvd (nuM 2 0 (by omega)) C
    (nuM_dmC 2 0 (by omega)) (r := k + 2) (a := a) (by
      simpa only [mpcMkTowerC] using ha)
  simpa only [show k + 2 - 1 = k + 1 by omega] using hdiv

theorem mpcMk_absorb_utD (k : Nat) (a : ℤ_[2])
    (ha : mpcMkTowerD a ∈
      twoCentralSeries (DM 2 0 : Type) (k + 2)) :
    mpcMkRawCost (k + 2) (by omega) 1 1
        (mpcMkRawUt (mpcMkTowerD a) ha) ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1) := by
  apply mpcMk_absorb_ut_of_dvd k D (mpcMkCanonUtD k)
    (mpcMkCanonUtD_range k) (mpcMkCanonUtD_value k)
    (mpcMkCanonUtD_other k) a (by simpa only [mpcMkTowerD] using ha)
  have hdiv := mpcMk_tower_exp_dvd mpcMkDeltaD D mpcMkDeltaD_dmD
    (r := k + 2) (a := a) (by simpa only [mpcMkTowerD] using ha)
  simpa only [show k + 2 - 1 = k + 1 by omega] using hdiv

theorem mpcMk_absorb_umB (k : Nat) (a : ℤ_[2])
    (ha : mpcMkTowerB a ∈
      twoCentralSeries (DM 2 0 : Type) (k + 2)) :
    mpcMkRawCost (k + 2) (by omega) 1 1
        (mpcMkRawUm (mpcMkTowerB a) ha) ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1) := by
  let fB : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]) :=
    (mBHom 2 0).comp (mAbMkHom 2 0)
  have hfB : fB B = ofAdd (1 : ℤ_[2]) := by
    change mBHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 1)) =
      ofAdd (1 : ℤ_[2])
    rw [mBHom, mCoordHom_gen, coreMark_one]
  apply mpcMk_absorb_um_of_dvd k B (mpcMkCanonUmB k)
    (mpcMkCanonUmB_range k) (mpcMkCanonUmB_value k)
    (mpcMkCanonUmB_other k) a (by simpa only [mpcMkTowerB] using ha)
  have hdiv := mpcMk_tower_exp_dvd fB B hfB
    (r := k + 2) (a := a) (by simpa only [mpcMkTowerB] using ha)
  simpa only [show k + 2 - 1 = k + 1 by omega] using hdiv

theorem mpcMk_absorb_umC (k : Nat) (a : ℤ_[2])
    (ha : mpcMkTowerC a ∈
      twoCentralSeries (DM 2 0 : Type) (k + 2)) :
    mpcMkRawCost (k + 2) (by omega) 1 1
        (mpcMkRawUm (mpcMkTowerC a) ha) ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1) := by
  apply mpcMk_absorb_um_of_dvd k C (mpcMkCanonUmC k)
    (mpcMkCanonUmC_range k) (mpcMkCanonUmC_value k)
    (mpcMkCanonUmC_other k) a (by simpa only [mpcMkTowerC] using ha)
  have hdiv := mpcMk_tower_exp_dvd (nuM 2 0 (by omega)) C
    (nuM_dmC 2 0 (by omega)) (r := k + 2) (a := a) (by
      simpa only [mpcMkTowerC] using ha)
  simpa only [show k + 2 - 1 = k + 1 by omega] using hdiv

theorem mpcMk_absorb_unD (k : Nat) (a : ℤ_[2])
    (ha : mpcMkTowerD a ∈
      twoCentralSeries (DM 2 0 : Type) (k + 2)) :
    mpcMkRawCost (k + 2) (by omega) 1 1
        (mpcMkRawUn (mpcMkTowerD a) ha) ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1) := by
  apply mpcMk_absorb_un_of_dvd k D (mpcMkCanonUnD k)
    (mpcMkCanonUnD_range k) (mpcMkCanonUnD_value k)
    (mpcMkCanonUnD_other k) a (by simpa only [mpcMkTowerD] using ha)
  have hdiv := mpcMk_tower_exp_dvd mpcMkDeltaD D mpcMkDeltaD_dmD
    (r := k + 2) (a := a) (by simpa only [mpcMkTowerD] using ha)
  simpa only [show k + 2 - 1 = k + 1 by omega] using hdiv

theorem mpcMkCanonUtC_mem (k : Nat) :
    mpcMkRawCost (k + 2) (by omega) 1 1 (mpcMkCanonUtC k) ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1) := by
  induction k with
  | zero =>
      simpa only [mpcMkCanonUtC] using
        MpcInitialRelatorBase.base_utC_mem
  | succ k ih =>
      simpa only [mpcMkCanonUtC, Nat.succ_eq_add_one] using
        mpcMkRawCost_square_mem_of_mem (r := k + 2)
          (by omega) (by omega) (mpcMkCanonUtC k) ih

theorem mpcMkCanonUtD_mem (k : Nat) :
    mpcMkRawCost (k + 2) (by omega) 1 1 (mpcMkCanonUtD k) ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1) := by
  induction k with
  | zero =>
      simpa only [mpcMkCanonUtD] using
        MpcInitialRelatorBase.base_utD_mem
  | succ k ih =>
      simpa only [mpcMkCanonUtD, Nat.succ_eq_add_one] using
        mpcMkRawCost_square_mem_of_mem (r := k + 2)
          (by omega) (by omega) (mpcMkCanonUtD k) ih

theorem mpcMkCanonUmB_mem (k : Nat) :
    mpcMkRawCost (k + 2) (by omega) 1 1 (mpcMkCanonUmB k) ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1) := by
  induction k with
  | zero =>
      simpa only [mpcMkCanonUmB] using
        MpcInitialRelatorBase.base_umB_mem
  | succ k ih =>
      simpa only [mpcMkCanonUmB, Nat.succ_eq_add_one] using
        mpcMkRawCost_square_mem_of_mem (r := k + 2)
          (by omega) (by omega) (mpcMkCanonUmB k) ih

theorem mpcMkCanonUmC_mem (k : Nat) :
    mpcMkRawCost (k + 2) (by omega) 1 1 (mpcMkCanonUmC k) ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1) := by
  induction k with
  | zero =>
      simpa only [mpcMkCanonUmC] using
        MpcInitialRelatorBase.base_umC_mem
  | succ k ih =>
      simpa only [mpcMkCanonUmC, Nat.succ_eq_add_one] using
        mpcMkRawCost_square_mem_of_mem (r := k + 2)
          (by omega) (by omega) (mpcMkCanonUmC k) ih

theorem mpcMkCanonUnD_mem (k : Nat) :
    mpcMkRawCost (k + 2) (by omega) 1 1 (mpcMkCanonUnD k) ∈
      MonoidHom.range (mpcMkCost (k + 2) (by omega) 1 1) := by
  induction k with
  | zero =>
      simpa only [mpcMkCanonUnD] using
        MpcInitialRelatorBase.base_unD_mem
  | succ k ih =>
      simpa only [mpcMkCanonUnD, Nat.succ_eq_add_one] using
        mpcMkRawCost_square_mem_of_mem (r := k + 2)
          (by omega) (by omega) (mpcMkCanonUnD k) ih

#print axioms mpcMkCanonUtC_mem
#print axioms mpcMkCanonUtD_mem
#print axioms mpcMkCanonUmB_mem
#print axioms mpcMkCanonUmC_mem
#print axioms mpcMkCanonUnD_mem

end
end GQ2.Dyadic.Instances.MpcMk

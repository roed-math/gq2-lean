/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcMarkedExactness
import GQ2.Dyadic.Instances.StageAbstractionEvenDigit

/-!
# Head completion for the marked Mpc successor

This module reduces `MpcMkHeadCompletion` to five explicit tower-cost families.  Canonical
M-frame coordinates first replace each unrestricted tail input, modulo the next filtration
rung, by a marked carrier element and its `B`, `C`, and `D` tower coordinates.  Two tower
costs vanish formally: the `D` tower in the `um` slot and the `C` tower in the `un` slot.
The five costs that remain are

* the `C` and `D` towers in the `ut` slot;
* the `B` and `C` towers in the `um` slot; and
* the `D` tower in the `un` slot.

`MpcMkInitialRelatorAbsorption` packages exactly these five all-coefficient families.
The final equivalence `mpcMk_headCompletion_iff_initialRelatorAbsorption` is independent of
the permitted depth-two base pair.  The absorption predicate is deliberately not proved or
assumed here: it is the remaining all-degree restricted-Lie consequence of the initial
quadratic relator.

External finite `2`-quotient calculations provide falsification evidence only.  At
`r = 2, 3, 4`, the unrestricted target dimensions are respectively `25, 70, 214`, while
both the head-marked and fully marked images have dimensions `20, 65, 209`.  Those checks
motivate the five-family statement but are not used by any declaration below.

Declaration prefix `mpcMk` (namespace `GQ2.Dyadic.Instances.MpcMk`).  No `sorry`, no new
axiom, no `native_decide`, and no heartbeat or recursion override.
-/

namespace GQ2.Dyadic.Instances.MpcMk

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcWord GQ2.Dyadic.Instances.MpcBld
open GQ2.Dyadic.Instances.MpcLad GQ2.Dyadic.Instances.MpcSx
open GQ2.Roe.Labute GQ2.Dyadic.SqCore
open GQ2.Dyadic.StageGeneric

noncomputable section

def mpcMkFullToHead (r : Nat) :
    MpcMkCostDomain r →* MpcMkHeadMarkedSource r where
  toFun u :=
    (⟨u.1, u.1.2⟩,
      ⟨u.2.1, u.2.1.2.2⟩,
      ⟨u.2.2.1, u.2.2.1.2.2⟩,
      ⟨u.2.2.2, u.2.2.2.2.2⟩)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem mpcMk_headCost_fullToHead
    (r : Nat) (hr : 2 ≤ r) (t n : (DM 2 0 : Type))
    (u : MpcMkCostDomain r) :
    mpcMkHeadMarkedCost r hr t n (mpcMkFullToHead r u) =
      mpcMkCost r hr t n u := by
  rw [mpcMkHeadMarkedCost, MonoidHom.comp_apply]
  exact mpcMkRawCost_markedSource r hr t n u

theorem mpcMk_fullRange_le_headRange
    (r : Nat) (hr : 2 ≤ r) (t n : (DM 2 0 : Type)) :
    MonoidHom.range (mpcMkCost r hr t n) ≤
      MonoidHom.range (mpcMkHeadMarkedCost r hr t n) := by
  rintro _ ⟨u, rfl⟩
  exact ⟨mpcMkFullToHead r u, mpcMk_headCost_fullToHead r hr t n u⟩

def MpcMkHeadAbsorption (r : Nat) (hr : 2 ≤ r)
    (t n : (DM 2 0 : Type)) : Prop :=
  ∀ u : MpcMkHeadMarkedSource r,
    mpcMkHeadMarkedCost r hr t n u ∈
      MonoidHom.range (mpcMkCost r hr t n)

theorem mpcMk_headCompletion_iff_absorption
    (r : Nat) (hr : 2 ≤ r) (t n : (DM 2 0 : Type)) :
    MpcMkHeadCompletion r hr t n ↔ MpcMkHeadAbsorption r hr t n := by
  constructor
  · intro h u
    rw [MpcMkHeadCompletion] at h
    rw [← h]
    exact ⟨u, rfl⟩
  · intro h
    apply le_antisymm
    · rintro _ ⟨u, rfl⟩
      exact h u
    · exact mpcMk_fullRange_le_headRange r hr t n

def mpcMkTowerB (a : ℤ_[2]) : (DM 2 0 : Type) :=
  zpowZtwo (isProP_DM 2 0) (dmB 2 0) a

def mpcMkTowerC (a : ℤ_[2]) : (DM 2 0 : Type) :=
  zpowZtwo (isProP_DM 2 0) (dmC 2 0) a

def mpcMkTowerD (a : ℤ_[2]) : (DM 2 0 : Type) :=
  zpowZtwo (isProP_DM 2 0) (dmD 2 0) a

private def mpcMkCompletionRowSub
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

private theorem mpcMkCompletionRowSub_closed
    (f : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]))
    (m : Nat) : IsClosed ((mpcMkCompletionRowSub f m :
      Subgroup (DM 2 0 : Type)) : Set (DM 2 0 : Type)) := by
  have hset : ((mpcMkCompletionRowSub f m : Subgroup (DM 2 0 : Type)) :
      Set (DM 2 0 : Type)) =
      (fun g : (DM 2 0 : Type) => toAdd (f g)) ⁻¹'
        {x : ℤ_[2] | (2 ^ m : ℤ_[2]) ∣ x} := rfl
  rw [hset]
  have hdiv : IsClosed {x : ℤ_[2] | (2 ^ m : ℤ_[2]) ∣ x} := by
    have himg : {x : ℤ_[2] | (2 ^ m : ℤ_[2]) ∣ x} =
        Set.range (fun y : ℤ_[2] => (2 ^ m : ℤ_[2]) * y) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_range]
      exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩,
        fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩
    rw [himg]
    exact (isCompact_range (continuous_const_mul (2 ^ m : ℤ_[2]))).isClosed
  exact hdiv.preimage
    (continuous_toAdd.comp f.continuous)

private theorem mpcMkCompletion_row_dvd
    (f : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]))
    {k : Nat} {g : (DM 2 0 : Type)}
    (hg : g ∈ twoCentralSeries (DM 2 0 : Type) k) :
    (2 ^ (k - 1) : ℤ_[2]) ∣ toAdd (f g) := by
  have hmain : ∀ m : Nat,
      twoCentralSeries (DM 2 0 : Type) (m + 1) ≤
        mpcMkCompletionRowSub f m := by
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
        (mpcMkCompletionRowSub_closed f (m + 1))
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

private theorem mpcMkCompletion_zpow_dvd_mem
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

/-- Every deep element is, modulo the next rung, a marked element followed by its
`C`- and `D`-tower coordinates. -/
theorem mpcMk_exists_markedCD_approx
    {r : Nat} (hr : 2 ≤ r) {x : (DM 2 0 : Type)}
    (hx : x ∈ twoCentralSeries (DM 2 0 : Type) r) :
    ∃ y ∈ mpcSxKill r, ∃ c d : ℤ_[2],
      mpcMkTowerC c ∈ twoCentralSeries (DM 2 0 : Type) r ∧
      mpcMkTowerD d ∈ twoCentralSeries (DM 2 0 : Type) r ∧
      x * (y * mpcMkTowerC c * mpcMkTowerD d)⁻¹ ∈
        twoCentralSeries (DM 2 0 : Type) (r + 1) := by
  let c : ℤ_[2] := toAdd (nuM 2 0 (by omega) x)
  let d : ℤ_[2] := toAdd (mpcMkDeltaD x)
  have hcdiv : (2 ^ (r - 1) : ℤ_[2]) ∣ c :=
    mpcMkCompletion_row_dvd (nuM 2 0 (by omega)) hx
  have hddiv : (2 ^ (r - 1) : ℤ_[2]) ∣ d :=
    mpcMkCompletion_row_dvd mpcMkDeltaD hx
  have heC : mpcMkTowerC c ∈ twoCentralSeries (DM 2 0 : Type) r :=
    mpcMkCompletion_zpow_dvd_mem (by omega) hcdiv
  have heD : mpcMkTowerD d ∈ twoCentralSeries (DM 2 0 : Type) r :=
    mpcMkCompletion_zpow_dvd_mem (by omega) hddiv
  let e := mpcMkTowerC c * mpcMkTowerD d
  let z := x * e⁻¹
  have hzdepth : z ∈ twoCentralSeries (DM 2 0 : Type) r :=
    Subgroup.mul_mem _ hx (Subgroup.inv_mem _ (Subgroup.mul_mem _ heC heD))
  have hznu : nuM 2 0 (by omega) z = 1 := by
    apply Multiplicative.toAdd.injective
    dsimp only [z, e, mpcMkTowerC, mpcMkTowerD, c]
    rw [map_mul (nuM 2 0 (by omega)), map_inv (nuM 2 0 (by omega)),
      map_mul (nuM 2 0 (by omega)), toAdd_mul, toAdd_inv, toAdd_mul,
      toAdd_map_zpowZtwo (isProP_DM 2 0),
      toAdd_map_zpowZtwo (isProP_DM 2 0), nuM_dmC, nuM_dmD]
    simp only [toAdd_one, toAdd_ofAdd]
    ring
  have hzdelta : mpcMkDeltaD z = 1 := by
    apply Multiplicative.toAdd.injective
    dsimp only [z, e, mpcMkTowerC, mpcMkTowerD, d]
    rw [map_mul mpcMkDeltaD, map_inv mpcMkDeltaD,
      map_mul mpcMkDeltaD, toAdd_mul, toAdd_inv, toAdd_mul,
      toAdd_map_zpowZtwo (isProP_DM 2 0),
      toAdd_map_zpowZtwo (isProP_DM 2 0),
      mpcMkDeltaD_dmC, mpcMkDeltaD_dmD]
    simp only [toAdd_one, toAdd_ofAdd]
    ring
  have hznuMod : mpcMkNuMod r z = 1 := by
    change ofAdd (PadicInt.toZModPow r (toAdd (nuM 2 0 (by omega) z))) = 1
    rw [hznu, toAdd_one, map_zero, ofAdd_zero]
  have hzdeltaMod : mpcMkDeltaDMod r z = 1 := by
    change ofAdd (PadicInt.toZModPow r (toAdd (mpcMkDeltaD z))) = 1
    rw [hzdelta, toAdd_one, map_zero, ofAdd_zero]
  obtain ⟨y, hy, hzy⟩ :=
    mpcMk_exists_headCarrier_approx hr hzdepth hznuMod hzdeltaMod
  refine ⟨y, hy, c, d, heC, heD, ?_⟩
  have heq : x * (y * mpcMkTowerC c * mpcMkTowerD d)⁻¹ = z * y⁻¹ := by
    dsimp only [z, e]
    group
  rwa [heq]

private theorem mpcMkCompletion_torsion_eq_one
    {r : Nat} (hr : 2 ≤ r) {x : (DM 2 0 : Type)}
    (hx : x ∈ twoCentralSeries (DM 2 0 : Type) r) :
    (mTHom 2 0) (GQ2.SectionThree.abMk x) = 1 := by
  let f : ContinuousMonoidHom (DM 2 0 : Type)
      (Multiplicative (ZMod 2)) :=
    (mTHom 2 0).comp (mAbMkHom 2 0)
  have him : f x ∈ twoCentralSeries (Multiplicative (ZMod 2)) r :=
    map_twoCentralSeries_le f.toMonoidHom f.continuous_toFun r
      ⟨x, hx, rfl⟩
  have him2 : f x ∈ twoCentralSeries (Multiplicative (ZMod 2)) 2 :=
    twoCentralSeries_antitone (G := Multiplicative (ZMod 2)) hr him
  obtain ⟨a, ha⟩ := evenStratumShift_twoCentralSeries_le_pow 1 him2
  change f x = 1
  rw [← ha]
  obtain ⟨z, rfl⟩ : ∃ z : ZMod 2, ofAdd z = a := ⟨toAdd a, rfl⟩
  change ofAdd z ^ 2 = 1
  rw [← ofAdd_nsmul, show (2 : Nat) • z = 0 by
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul], ofAdd_zero]

/-- Every deep element is, modulo the next rung, a derived element followed by its
`B`-, `C`-, and `D`-tower coordinates. -/
theorem mpcMk_exists_derivedBCD_approx
    {r : Nat} (hr : 2 ≤ r) {x : (DM 2 0 : Type)}
    (hx : x ∈ twoCentralSeries (DM 2 0 : Type) r) :
    ∃ y ∈ mpcMkPivotKill r, ∃ b c d : ℤ_[2],
      mpcMkTowerB b ∈ twoCentralSeries (DM 2 0 : Type) r ∧
      mpcMkTowerC c ∈ twoCentralSeries (DM 2 0 : Type) r ∧
      mpcMkTowerD d ∈ twoCentralSeries (DM 2 0 : Type) r ∧
      x * (y * mpcMkTowerB b * mpcMkTowerC c * mpcMkTowerD d)⁻¹ ∈
        twoCentralSeries (DM 2 0 : Type) (r + 1) := by
  let fB : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]) :=
    (mBHom 2 0).comp (mAbMkHom 2 0)
  let b : ℤ_[2] := toAdd (fB x)
  let c : ℤ_[2] := toAdd (nuM 2 0 (by omega) x)
  let d : ℤ_[2] := toAdd (mpcMkDeltaD x)
  have hbdiv : (2 ^ (r - 1) : ℤ_[2]) ∣ b :=
    mpcMkCompletion_row_dvd fB hx
  have hcdiv : (2 ^ (r - 1) : ℤ_[2]) ∣ c :=
    mpcMkCompletion_row_dvd (nuM 2 0 (by omega)) hx
  have hddiv : (2 ^ (r - 1) : ℤ_[2]) ∣ d :=
    mpcMkCompletion_row_dvd mpcMkDeltaD hx
  have heB : mpcMkTowerB b ∈ twoCentralSeries (DM 2 0 : Type) r :=
    mpcMkCompletion_zpow_dvd_mem (by omega) hbdiv
  have heC : mpcMkTowerC c ∈ twoCentralSeries (DM 2 0 : Type) r :=
    mpcMkCompletion_zpow_dvd_mem (by omega) hcdiv
  have heD : mpcMkTowerD d ∈ twoCentralSeries (DM 2 0 : Type) r :=
    mpcMkCompletion_zpow_dvd_mem (by omega) hddiv
  let e := mpcMkTowerB b * mpcMkTowerC c * mpcMkTowerD d
  let z := x * e⁻¹
  have hzdepth : z ∈ twoCentralSeries (DM 2 0 : Type) r :=
    Subgroup.mul_mem _ hx (Subgroup.inv_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ heB heC) heD))
  have hTx := mpcMkCompletion_torsion_eq_one hr hx
  let fT : ContinuousMonoidHom (DM 2 0 : Type)
      (Multiplicative (ZMod 2)) :=
    (mTHom 2 0).comp (mAbMkHom 2 0)
  have hTB : fT (dmB 2 0) = 1 := by
    change mTHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 1)) = 1
    rw [mTHom, mCoordHom_gen, coreMark_one]
  have hTC : fT (dmC 2 0) = 1 := by
    change mTHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 2)) = 1
    rw [mTHom, mCoordHom_gen, coreMark_two]
  have hTD : fT (dmD 2 0) = 1 := by
    change mTHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 3)) = 1
    rw [mTHom, mCoordHom_gen, coreMark_three]
  have hBB : fB (dmB 2 0) = ofAdd (1 : ℤ_[2]) := by
    change mBHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 1)) =
      ofAdd (1 : ℤ_[2])
    rw [mBHom, mCoordHom_gen, coreMark_one]
  have hBC : fB (dmC 2 0) = 1 := by
    change mBHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 2)) = 1
    rw [mBHom, mCoordHom_gen, coreMark_two]
  have hBD : fB (dmD 2 0) = 1 := by
    change mBHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 3)) = 1
    rw [mBHom, mCoordHom_gen, coreMark_three]
  have hab : GQ2.SectionThree.abMk z = 1 := by
    apply mPhiHom_injective (by omega) 0
    rw [map_one]
    apply Multiplicative.toAdd.injective
    apply Prod.ext
    · change toAdd ((mTHom 2 0) (GQ2.SectionThree.abMk z)) = 0
      change toAdd (fT z) = 0
      dsimp only [z, e, mpcMkTowerB, mpcMkTowerC, mpcMkTowerD]
      rw [map_mul fT, map_inv fT, map_mul fT, map_mul fT,
        map_zpowZtwo (isProP_DM 2 0)
          GQ2.SectionThree.isProP_two_multZMod2,
        map_zpowZtwo (isProP_DM 2 0)
          GQ2.SectionThree.isProP_two_multZMod2,
        map_zpowZtwo (isProP_DM 2 0)
          GQ2.SectionThree.isProP_two_multZMod2,
        hTB, hTC, hTD]
      simp only [zpowZtwo_one_base, mul_one, inv_one]
      exact congrArg Multiplicative.toAdd hTx
    · apply Prod.ext
      · change toAdd ((mBHom 2 0) (GQ2.SectionThree.abMk z)) = 0
        change toAdd (fB z) = 0
        dsimp only [z, e, mpcMkTowerB, mpcMkTowerC, mpcMkTowerD]
        rw [map_mul fB, map_inv fB, map_mul fB, map_mul fB,
          toAdd_mul, toAdd_inv, toAdd_mul, toAdd_mul,
          toAdd_map_zpowZtwo (isProP_DM 2 0),
          toAdd_map_zpowZtwo (isProP_DM 2 0),
          toAdd_map_zpowZtwo (isProP_DM 2 0), hBB, hBC, hBD]
        change b + -(b * 1 + c * 0 + d * 0) = 0
        ring
      · apply Prod.ext
        · change toAdd ((mCHom (by omega) 0) (GQ2.SectionThree.abMk z)) = 0
          rw [← mpcMkNu_eq_mCHom_apply]
          dsimp only [z, e, mpcMkTowerB, mpcMkTowerC, mpcMkTowerD]
          rw [map_mul (nuM 2 0 (by omega)), map_inv (nuM 2 0 (by omega)),
            map_mul (nuM 2 0 (by omega)), map_mul (nuM 2 0 (by omega)),
            toAdd_mul, toAdd_inv, toAdd_mul, toAdd_mul,
            toAdd_map_zpowZtwo (isProP_DM 2 0),
            toAdd_map_zpowZtwo (isProP_DM 2 0),
            toAdd_map_zpowZtwo (isProP_DM 2 0),
            nuM_dmB, nuM_dmC, nuM_dmD]
          change c + -(b * 0 + c * 1 + d * 0) = 0
          ring
        · apply Prod.ext
          · change toAdd ((mDHom 2 0) (GQ2.SectionThree.abMk z)) = 0
            change toAdd (mpcMkDeltaD z) = 0
            dsimp only [z, e, mpcMkTowerB, mpcMkTowerC, mpcMkTowerD]
            rw [map_mul mpcMkDeltaD, map_inv mpcMkDeltaD,
              map_mul mpcMkDeltaD, map_mul mpcMkDeltaD,
              toAdd_mul, toAdd_inv, toAdd_mul, toAdd_mul,
              toAdd_map_zpowZtwo (isProP_DM 2 0),
              toAdd_map_zpowZtwo (isProP_DM 2 0),
              toAdd_map_zpowZtwo (isProP_DM 2 0),
              mpcMkDeltaD_dmB, mpcMkDeltaD_dmC, mpcMkDeltaD_dmD]
            change d + -(b * 0 + c * 0 + d * 1) = 0
            ring
          · exact funext fun i => absurd i.2 (by omega)
  have hztop : z ∈ (commutator (DM 2 0 : Type)).topologicalClosure := by
    apply (QuotientGroup.eq_one_iff z).mp
    exact hab
  obtain ⟨y, hy, hzy⟩ := mpcMk_exists_pivotKill_approx hzdepth hztop
  refine ⟨y, hy, b, c, d, heB, heC, heD, ?_⟩
  have heq : x *
      (y * mpcMkTowerB b * mpcMkTowerC c * mpcMkTowerD d)⁻¹ =
      z * y⁻¹ := by
    dsimp only [z, e]
    group
  rwa [heq]

private def rawUt {r : Nat} (x : (DM 2 0 : Type))
    (hx : x ∈ twoCentralSeries (DM 2 0 : Type) r) : MpcMkRawSource r :=
  (1, ⟨x, hx⟩, 1, 1)

private def rawUm {r : Nat} (x : (DM 2 0 : Type))
    (hx : x ∈ twoCentralSeries (DM 2 0 : Type) r) : MpcMkRawSource r :=
  (1, 1, ⟨x, hx⟩, 1)

private def rawUn {r : Nat} (x : (DM 2 0 : Type))
    (hx : x ∈ twoCentralSeries (DM 2 0 : Type) r) : MpcMkRawSource r :=
  (1, 1, 1, ⟨x, hx⟩)

/-- The five tower families omitted by the three tail carrier restrictions. -/
def MpcMkInitialRelatorAbsorption (r : Nat) (hr : 2 ≤ r) : Prop :=
  (∀ a (ha : mpcMkTowerC a ∈ twoCentralSeries (DM 2 0 : Type) r),
      mpcMkRawCost r hr 1 1 (rawUt (mpcMkTowerC a) ha) ∈
        MonoidHom.range (mpcMkCost r hr 1 1)) ∧
  (∀ a (ha : mpcMkTowerD a ∈ twoCentralSeries (DM 2 0 : Type) r),
      mpcMkRawCost r hr 1 1 (rawUt (mpcMkTowerD a) ha) ∈
        MonoidHom.range (mpcMkCost r hr 1 1)) ∧
  (∀ a (ha : mpcMkTowerB a ∈ twoCentralSeries (DM 2 0 : Type) r),
      mpcMkRawCost r hr 1 1 (rawUm (mpcMkTowerB a) ha) ∈
        MonoidHom.range (mpcMkCost r hr 1 1)) ∧
  (∀ a (ha : mpcMkTowerC a ∈ twoCentralSeries (DM 2 0 : Type) r),
      mpcMkRawCost r hr 1 1 (rawUm (mpcMkTowerC a) ha) ∈
        MonoidHom.range (mpcMkCost r hr 1 1)) ∧
  (∀ a (ha : mpcMkTowerD a ∈ twoCentralSeries (DM 2 0 : Type) r),
      mpcMkRawCost r hr 1 1 (rawUn (mpcMkTowerD a) ha) ∈
        MonoidHom.range (mpcMkCost r hr 1 1))

/-- Completion at the untwisted base forces each of the five omitted tower costs. -/
theorem mpcMk_initialRelatorAbsorption_of_headCompletion_one
    (r : Nat) (hr : 2 ≤ r)
    (hcomplete : MpcMkHeadCompletion r hr 1 1) :
    MpcMkInitialRelatorAbsorption r hr := by
  have hhead : ∀ u : MpcMkHeadMarkedSource r,
      mpcMkHeadMarkedCost r hr 1 1 u ∈
        MonoidHom.range (mpcMkCost r hr 1 1) := by
    intro u
    rw [MpcMkHeadCompletion] at hcomplete
    rw [← hcomplete]
    exact ⟨u, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    let u : MpcMkHeadMarkedSource r :=
      (1, ⟨mpcMkTowerC a, ha⟩, 1, 1)
    have heq : mpcMkHeadMarkedSource r u =
        rawUt (mpcMkTowerC a) ha := by
      ext <;> rfl
    simpa only [mpcMkHeadMarkedCost, MonoidHom.comp_apply, heq] using hhead u
  · intro a ha
    let u : MpcMkHeadMarkedSource r :=
      (1, ⟨mpcMkTowerD a, ha⟩, 1, 1)
    have heq : mpcMkHeadMarkedSource r u =
        rawUt (mpcMkTowerD a) ha := by
      ext <;> rfl
    simpa only [mpcMkHeadMarkedCost, MonoidHom.comp_apply, heq] using hhead u
  · intro a ha
    let u : MpcMkHeadMarkedSource r :=
      (1, 1, ⟨mpcMkTowerB a, ha⟩, 1)
    have heq : mpcMkHeadMarkedSource r u =
        rawUm (mpcMkTowerB a) ha := by
      ext <;> rfl
    simpa only [mpcMkHeadMarkedCost, MonoidHom.comp_apply, heq] using hhead u
  · intro a ha
    let u : MpcMkHeadMarkedSource r :=
      (1, 1, ⟨mpcMkTowerC a, ha⟩, 1)
    have heq : mpcMkHeadMarkedSource r u =
        rawUm (mpcMkTowerC a) ha := by
      ext <;> rfl
    simpa only [mpcMkHeadMarkedCost, MonoidHom.comp_apply, heq] using hhead u
  · intro a ha
    let u : MpcMkHeadMarkedSource r :=
      (1, 1, 1, ⟨mpcMkTowerD a, ha⟩)
    have heq : mpcMkHeadMarkedSource r u =
        rawUn (mpcMkTowerD a) ha := by
      ext <;> rfl
    simpa only [mpcMkHeadMarkedCost, MonoidHom.comp_apply, heq] using hhead u

/-- The five initial-relator tower absorptions imply completion at the untwisted base. -/
theorem mpcMk_headCompletion_one_of_initialRelatorAbsorption
    (r : Nat) (hr : 2 ≤ r)
    (habs : MpcMkInitialRelatorAbsorption r hr) :
    MpcMkHeadCompletion r hr 1 1 := by
  rw [mpcMk_headCompletion_iff_absorption]
  intro u
  obtain ⟨yt, hyt, ct, dt, hct, hdt, hut⟩ :=
    mpcMk_exists_markedCD_approx hr u.2.1.2
  obtain ⟨ym, hym, bm, cm, dm, hbm, hcm, hdm, hum⟩ :=
    mpcMk_exists_derivedBCD_approx hr u.2.2.1.2
  obtain ⟨yn, hyn, cn, dn, hcn, hdn, hun⟩ :=
    mpcMk_exists_markedCD_approx hr u.2.2.2.2
  let v : MpcMkCostDomain r :=
    (u.1, ⟨yt, hyt⟩, ⟨ym, hym⟩, ⟨yn, hyn⟩)
  let s0 : MpcMkRawSource r := mpcMkMarkedSource r v
  let sCt : MpcMkRawSource r := rawUt (mpcMkTowerC ct) hct
  let sDt : MpcMkRawSource r := rawUt (mpcMkTowerD dt) hdt
  let sBm : MpcMkRawSource r := rawUm (mpcMkTowerB bm) hbm
  let sCm : MpcMkRawSource r := rawUm (mpcMkTowerC cm) hcm
  let sDm : MpcMkRawSource r := rawUm (mpcMkTowerD dm) hdm
  let sCn : MpcMkRawSource r := rawUn (mpcMkTowerC cn) hcn
  let sDn : MpcMkRawSource r := rawUn (mpcMkTowerD dn) hdn
  let q : MpcMkRawSource r :=
    s0 * sCt * sDt * sBm * sCm * sDm * sCn * sDn
  have hsCongr :
      (mpcMkHeadMarkedSource r u).1.1 * q.1.1⁻¹ ∈
        twoCentralSeries (DM 2 0 : Type) (r + 1) := by
    simp [q, s0, sCt, sDt, sBm, sCm, sDm, sCn, sDn,
      v, rawUt, rawUm, rawUn, mpcMkMarkedSource, mpcMkHeadMarkedSource]
  have htCongr :
      (mpcMkHeadMarkedSource r u).2.1.1 * q.2.1.1⁻¹ ∈
        twoCentralSeries (DM 2 0 : Type) (r + 1) := by
    simpa [q, s0, sCt, sDt, sBm, sCm, sDm, sCn, sDn,
      v, rawUt, rawUm, rawUn, mpcMkMarkedSource, mpcMkHeadMarkedSource]
      using hut
  have hmCongr :
      (mpcMkHeadMarkedSource r u).2.2.1.1 * q.2.2.1.1⁻¹ ∈
        twoCentralSeries (DM 2 0 : Type) (r + 1) := by
    simpa [q, s0, sCt, sDt, sBm, sCm, sDm, sCn, sDn,
      v, rawUt, rawUm, rawUn, mpcMkMarkedSource, mpcMkHeadMarkedSource]
      using hum
  have hnCongr :
      (mpcMkHeadMarkedSource r u).2.2.2.1 * q.2.2.2.1⁻¹ ∈
        twoCentralSeries (DM 2 0 : Type) (r + 1) := by
    simpa [q, s0, sCt, sDt, sBm, sCm, sDm, sCn, sDn,
      v, rawUt, rawUm, rawUn, mpcMkMarkedSource, mpcMkHeadMarkedSource]
      using hun
  have hcostCongr :
      mpcMkRawCost r hr 1 1 (mpcMkHeadMarkedSource r u) =
        mpcMkRawCost r hr 1 1 q := by
    apply Subtype.ext
    rw [mpcMkRawCost_apply, mpcMkRawCost_apply]
    exact mpcMk_rawCost_congr_of_mod_succ hr 1 1
      (mpcMkHeadMarkedSource r u).1
      (mpcMkHeadMarkedSource r u).2.1
      (mpcMkHeadMarkedSource r u).2.2.1
      (mpcMkHeadMarkedSource r u).2.2.2
      q.1 q.2.1 q.2.2.1 q.2.2.2
      (mpcMkHeadMarkedSource r u).1.2
      (mpcMkHeadMarkedSource r u).2.1.2
      (mpcMkHeadMarkedSource r u).2.2.1.2
      (mpcMkHeadMarkedSource r u).2.2.2.2
      q.1.2 q.2.1.2 q.2.2.1.2 q.2.2.2.2
      hsCongr htCongr hmCongr hnCongr
  let R := MonoidHom.range (mpcMkCost r hr 1 1)
  have hs0 : mpcMkRawCost r hr 1 1 s0 ∈ R := by
    exact ⟨v, (mpcMkRawCost_markedSource r hr 1 1 v).symm⟩
  have hsCt : mpcMkRawCost r hr 1 1 sCt ∈ R := habs.1 ct hct
  have hsDt : mpcMkRawCost r hr 1 1 sDt ∈ R := habs.2.1 dt hdt
  have hsBm : mpcMkRawCost r hr 1 1 sBm ∈ R := habs.2.2.1 bm hbm
  have hsCm : mpcMkRawCost r hr 1 1 sCm ∈ R := habs.2.2.2.1 cm hcm
  have hsDn : mpcMkRawCost r hr 1 1 sDn ∈ R := habs.2.2.2.2 dn hdn
  have hsDm : mpcMkRawCost r hr 1 1 sDm = 1 := by
    apply Subtype.ext
    rw [mpcMkRawCost_apply]
    simp only [sDm, rawUm, mpcBldIncr, Subgroup.coe_one, one_pow,
      cfour_one_comm, one_mul, mul_one, mpcWordLetD]
    have hcomm : Commute (mpcMkTowerD dm) (dmD 2 0) := by
      exact commute_zpowZtwo_self (isProP_DM 2 0) (dmD 2 0) dm
    rw [commP_eq_one_of_commute hcomm]
    rw [show 1 * commP (dmA 2 0) 1 * commP (dmC 2 0) 1 = 1 by
      simp only [commP, inv_one, mul_one, inv_mul_cancel], map_one]
  have hsCn : mpcMkRawCost r hr 1 1 sCn = 1 := by
    apply Subtype.ext
    rw [mpcMkRawCost_apply]
    simp only [sCn, rawUn, mpcBldIncr, Subgroup.coe_one, one_pow,
      cfour_one_comm, one_mul, mul_one, mpcWordLetD]
    have hcomm : Commute (dmC 2 0) (mpcMkTowerC cn) := by
      exact mCommute_zpowZtwo (isProP_DM 2 0) (dmC 2 0) cn
    rw [commP_eq_one_of_commute hcomm]
    rw [show commP (dmA 2 0) 1 * 1 = 1 by
      simp only [commP, inv_one, mul_one, inv_mul_cancel], map_one]
  have hq : mpcMkRawCost r hr 1 1 q ∈ R := by
    have hmain := R.mul_mem
      (R.mul_mem
        (R.mul_mem
          (R.mul_mem
            (R.mul_mem hs0 hsCt) hsDt) hsBm) hsCm) hsDn
    simpa only [q, map_mul, hsDm, hsCn, mul_one] using hmain
  change mpcMkRawCost r hr 1 1 (mpcMkHeadMarkedSource r u) ∈ R
  rw [hcostCongr]
  exact hq

/-- The five untwisted tower absorptions imply completion for every permitted base pair. -/
theorem mpcMk_headCompletion_of_initialRelatorAbsorption
    (r : Nat) (hr : 2 ≤ r) {t n : (DM 2 0 : Type)}
    (ht : t ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (hn : n ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (habs : MpcMkInitialRelatorAbsorption r hr) :
    MpcMkHeadCompletion r hr t n := by
  have hraw := mpcMkRawCost_base_indep r hr ht hn
  have hhead :
      mpcMkHeadMarkedCost r hr t n = mpcMkHeadMarkedCost r hr 1 1 := by
    rw [mpcMkHeadMarkedCost, mpcMkHeadMarkedCost, hraw]
  have hfull : mpcMkCost r hr t n = mpcMkCost r hr 1 1 := by
    ext u
    rw [← mpcMkRawCost_markedSource r hr t n u,
      ← mpcMkRawCost_markedSource r hr 1 1 u, hraw]
  rw [MpcMkHeadCompletion, hhead, hfull]
  exact mpcMk_headCompletion_one_of_initialRelatorAbsorption r hr habs

/-- Head completion is exactly the five initial-relator tower absorptions. -/
theorem mpcMk_headCompletion_iff_initialRelatorAbsorption
    (r : Nat) (hr : 2 ≤ r) {t n : (DM 2 0 : Type)}
    (ht : t ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (hn : n ∈ twoCentralSeries (DM 2 0 : Type) 2) :
    MpcMkHeadCompletion r hr t n ↔ MpcMkInitialRelatorAbsorption r hr := by
  have hraw := mpcMkRawCost_base_indep r hr ht hn
  have hhead :
      mpcMkHeadMarkedCost r hr t n = mpcMkHeadMarkedCost r hr 1 1 := by
    rw [mpcMkHeadMarkedCost, mpcMkHeadMarkedCost, hraw]
  have hfull : mpcMkCost r hr t n = mpcMkCost r hr 1 1 := by
    ext u
    rw [← mpcMkRawCost_markedSource r hr t n u,
      ← mpcMkRawCost_markedSource r hr 1 1 u, hraw]
  rw [MpcMkHeadCompletion, hhead, hfull]
  exact ⟨mpcMk_initialRelatorAbsorption_of_headCompletion_one r hr,
    mpcMk_headCompletion_one_of_initialRelatorAbsorption r hr⟩

/-! ## Axiom pins -/

#print axioms mpcMkFullToHead
#print axioms mpcMk_headCompletion_iff_absorption
#print axioms mpcMk_exists_markedCD_approx
#print axioms mpcMk_exists_derivedBCD_approx
#print axioms MpcMkInitialRelatorAbsorption
#print axioms mpcMk_initialRelatorAbsorption_of_headCompletion_one
#print axioms mpcMk_headCompletion_one_of_initialRelatorAbsorption
#print axioms mpcMk_headCompletion_of_initialRelatorAbsorption
#print axioms mpcMk_headCompletion_iff_initialRelatorAbsorption

end
end GQ2.Dyadic.Instances.MpcMk

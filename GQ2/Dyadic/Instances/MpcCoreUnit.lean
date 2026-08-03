/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Count.ProTwo
import GQ2.Dyadic.Instances.NpcCore
import GQ2.Dyadic.SelectedEta

/-!
# The arbitrary-unit, arbitrary-handle procyclic-M core dictionary

This file supplies the forward half of the general procyclic-`M` presentation dictionary.  For
an alphabet marking `t`, first use the compact-`N` indexing

`(x0, x1, sigma, x2, handles)`

and then apply the triangular change of variables

`(A, B, C0, D) = (x0^-1 C0^-m, x1 sigma^p, x2 sigma^s, sigma^etaHat)`.

The handles are untouched.  The final theorem identifies the pro-`2` value of the semantic
word `mpcWUnit alpha r p eta h` with the defining `D_M` relator on that vector.  It is uniform
in the unit and in the handle count and does not replace the parameter `p` by a specialized
formula.

The inverse dictionary is used only in pro-`2` groups, where `sigma` is recovered by the
`eta⁻¹`-power.  This is enough to build `Count.CorePresentation` directly; no inverse-power
operation on arbitrary profinite groups is needed.
-/

namespace GQ2.Dyadic.Instances.MProcyclicCore

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Count.PilotN

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- The triangular procyclic-`M` change of core coordinates, for an arbitrary semantic unit.
The input vector is in compact-`N` order `(x0,x1,sigma,x2,handles)`; the output vector is in
`D_M` order `(A,B,C0,D,handles)`. -/
noncomputable def mpcUnitTwist (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (c : Fin (coreRank h) → G) : Fin (coreRank h) → G :=
  fun i ↦ if (i : ℕ) = 0 then
      (c 0)⁻¹ * ((c 3 * c 2 ^ s r) ^ m alpha)⁻¹
    else if (i : ℕ) = 1 then c 1 * c 2 ^ p
    else if (i : ℕ) = 2 then c 3 * c 2 ^ s r
    else if (i : ℕ) = 3 then c 2 ^ᶻ etaHatZ (eta : ℤ_[2])
    else c i

@[simp] theorem mpcUnitTwist_zero (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (c : Fin (coreRank h) → G) :
    mpcUnitTwist alpha r p eta h c 0 =
      (c 0)⁻¹ * ((c 3 * c 2 ^ s r) ^ m alpha)⁻¹ := by
  rw [mpcUnitTwist, if_pos (coreVal_zero h)]

@[simp] theorem mpcUnitTwist_one (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (c : Fin (coreRank h) → G) :
    mpcUnitTwist alpha r p eta h c 1 = c 1 * c 2 ^ p := by
  rw [mpcUnitTwist, if_neg (by rw [coreVal_one]; omega), if_pos (coreVal_one h)]

@[simp] theorem mpcUnitTwist_two (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (c : Fin (coreRank h) → G) :
    mpcUnitTwist alpha r p eta h c 2 = c 3 * c 2 ^ s r := by
  rw [mpcUnitTwist, if_neg (by rw [coreVal_two]; omega),
    if_neg (by rw [coreVal_two]; omega), if_pos (coreVal_two h)]

@[simp] theorem mpcUnitTwist_three (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (c : Fin (coreRank h) → G) :
    mpcUnitTwist alpha r p eta h c 3 = c 2 ^ᶻ etaHatZ (eta : ℤ_[2]) := by
  rw [mpcUnitTwist, if_neg (by rw [coreVal_three]; omega),
    if_neg (by rw [coreVal_three]; omega), if_neg (by rw [coreVal_three]; omega),
    if_pos (coreVal_three h)]

@[simp] theorem mpcUnitTwist_handleIdxU (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (c : Fin (coreRank h) → G) (j : Fin h) :
    mpcUnitTwist alpha r p eta h c (handleIdxU j) = c (handleIdxU j) := by
  rw [mpcUnitTwist, if_neg (by rw [handleIdxU_val]; omega),
    if_neg (by rw [handleIdxU_val]; omega), if_neg (by rw [handleIdxU_val]; omega),
    if_neg (by rw [handleIdxU_val]; omega)]

@[simp] theorem mpcUnitTwist_handleIdxV (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (c : Fin (coreRank h) → G) (j : Fin h) :
    mpcUnitTwist alpha r p eta h c (handleIdxV j) = c (handleIdxV j) := by
  rw [mpcUnitTwist, if_neg (by rw [handleIdxV_val]; omega),
    if_neg (by rw [handleIdxV_val]; omega), if_neg (by rw [handleIdxV_val]; omega),
    if_neg (by rw [handleIdxV_val]; omega)]

/-- The semantic arbitrary-unit `Mpc` core vector attached to an alphabet marking. -/
noncomputable def mpcCoreMarkUnit (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (t : Marking (2 + 2 * h) G) : Fin (coreRank h) → G :=
  mpcUnitTwist alpha r p eta h (fun i ↦ t (nIdx h i))

/-- The full `D_M` relator read through the arbitrary-unit dictionary. -/
noncomputable def mpcCoreRelUnit (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (t : Marking (2 + 2 * h) G) : G :=
  mRelWord alpha (mpcCoreMarkUnit alpha r p eta h t)

/-- **The arbitrary-unit, arbitrary-handle dictionary theorem.**  The semantic word's pro-`2`
value is the defining `D_M` relator on `(A,B,C0,D,handles)`. -/
theorem mpcProTwoWordUnit (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (halpha : 1 ≤ alpha) (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (mpcWUnit alpha r p eta h)) = mpcCoreRelUnit alpha r p eta h t := by
  rw [eval_pro2_mpcWUnit halpha r p eta h t]
  unfold mpcCoreRelUnit mpcCoreMarkUnit
  rw [mRelWord]
  simp only [mpcUnitTwist_zero, mpcUnitTwist_one, mpcUnitTwist_two,
    mpcUnitTwist_three, mpcUnitTwist_handleIdxU, mpcUnitTwist_handleIdxV, nIdx_zero,
    nIdx_one, nIdx_two, nIdx_three, nIdx_handleIdxU, nIdx_handleIdxV,
    Marking.apply_sigma]

/-- The same equality in the natural-word spelling consumed by the `D_M` presentation API. -/
theorem eval_pro2_mpcWUnit_eq_mNatWord (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (halpha : 1 ≤ alpha) (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (mpcWUnit alpha r p eta h)) =
      (mNatWord alpha h).ev (mpcCoreMarkUnit alpha r p eta h t) :=
  mpcProTwoWordUnit alpha r p eta h halpha t

/-! ## The inverse dictionary on pro-`2` groups -/

section ProTwoDictionary

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]

/-- Inverse triangular change of variables.  From `(A,B,C0,D,handles)`, recover
`sigma = D^(eta⁻¹)`, then `(x0,x1,sigma,x2,handles)`. -/
noncomputable def mpcUnitUntwist (hP : IsProP 2 P) (alpha r p : ℕ) (eta : ℤ_[2]ˣ)
    (h : ℕ) (c : Fin (coreRank h) → P) : Fin (coreRank h) → P :=
  let sigma := zpowZtwo hP (c 3) ((eta⁻¹ : ℤ_[2]ˣ) : ℤ_[2])
  fun i ↦ if (i : ℕ) = 0 then (c 0 * c 2 ^ m alpha)⁻¹
    else if (i : ℕ) = 1 then c 1 * sigma ^ (-(p : ℤ))
    else if (i : ℕ) = 2 then sigma
    else if (i : ℕ) = 3 then c 2 * sigma ^ (-(s r : ℤ))
    else c i

@[simp] theorem mpcUnitUntwist_zero (hP : IsProP 2 P) (alpha r p : ℕ)
    (eta : ℤ_[2]ˣ) (h : ℕ) (c : Fin (coreRank h) → P) :
    mpcUnitUntwist hP alpha r p eta h c 0 = (c 0 * c 2 ^ m alpha)⁻¹ := by
  simp only [mpcUnitUntwist]
  rw [if_pos (coreVal_zero h)]

@[simp] theorem mpcUnitUntwist_one (hP : IsProP 2 P) (alpha r p : ℕ)
    (eta : ℤ_[2]ˣ) (h : ℕ) (c : Fin (coreRank h) → P) :
    mpcUnitUntwist hP alpha r p eta h c 1 =
      c 1 * zpowZtwo hP (c 3) ((eta⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) ^ (-(p : ℤ)) := by
  simp only [mpcUnitUntwist]
  rw [if_neg (by rw [coreVal_one]; omega), if_pos (coreVal_one h)]

@[simp] theorem mpcUnitUntwist_two (hP : IsProP 2 P) (alpha r p : ℕ)
    (eta : ℤ_[2]ˣ) (h : ℕ) (c : Fin (coreRank h) → P) :
    mpcUnitUntwist hP alpha r p eta h c 2 =
      zpowZtwo hP (c 3) ((eta⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) := by
  simp only [mpcUnitUntwist]
  rw [if_neg (by rw [coreVal_two]; omega), if_neg (by rw [coreVal_two]; omega),
    if_pos (coreVal_two h)]

@[simp] theorem mpcUnitUntwist_three (hP : IsProP 2 P) (alpha r p : ℕ)
    (eta : ℤ_[2]ˣ) (h : ℕ) (c : Fin (coreRank h) → P) :
    mpcUnitUntwist hP alpha r p eta h c 3 =
      c 2 * zpowZtwo hP (c 3) ((eta⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) ^ (-(s r : ℤ)) := by
  simp only [mpcUnitUntwist]
  rw [if_neg (by rw [coreVal_three]; omega), if_neg (by rw [coreVal_three]; omega),
    if_neg (by rw [coreVal_three]; omega), if_pos (coreVal_three h)]

theorem mpcUnitUntwist_apply_ne (hP : IsProP 2 P) (alpha r p : ℕ)
    (eta : ℤ_[2]ˣ) (h : ℕ) (c : Fin (coreRank h) → P) {i : Fin (coreRank h)}
    (h0 : (i : ℕ) ≠ 0) (h1 : (i : ℕ) ≠ 1) (h2 : (i : ℕ) ≠ 2)
    (h3 : (i : ℕ) ≠ 3) : mpcUnitUntwist hP alpha r p eta h c i = c i := by
  simp only [mpcUnitUntwist, if_neg h0, if_neg h1, if_neg h2, if_neg h3]

omit [T2Space P] in
theorem mpcUnitTwist_apply_ne (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (c : Fin (coreRank h) → P) {i : Fin (coreRank h)}
    (h0 : (i : ℕ) ≠ 0) (h1 : (i : ℕ) ≠ 1) (h2 : (i : ℕ) ≠ 2)
    (h3 : (i : ℕ) ≠ 3) :
    mpcUnitTwist alpha r p eta h c i = c i := by
  simp only [mpcUnitTwist, if_neg h0, if_neg h1, if_neg h2, if_neg h3]

theorem mpcUnitTwist_mpcUnitUntwist (hP : IsProP 2 P) (alpha r p : ℕ)
    (eta : ℤ_[2]ˣ) (h : ℕ) (c : Fin (coreRank h) → P) :
    mpcUnitTwist alpha r p eta h (mpcUnitUntwist hP alpha r p eta h c) = c := by
  funext i
  by_cases h0 : (i : ℕ) = 0
  · have hi : i = 0 := Fin.ext (by rw [h0, coreVal_zero])
    subst hi
    rw [mpcUnitTwist_zero, mpcUnitUntwist_zero, mpcUnitUntwist_three,
      mpcUnitUntwist_two]
    group
  · by_cases h1 : (i : ℕ) = 1
    · have hi : i = 1 := Fin.ext (by rw [h1, coreVal_one])
      subst hi
      rw [mpcUnitTwist_one, mpcUnitUntwist_one, mpcUnitUntwist_two]
      group
    · by_cases h2 : (i : ℕ) = 2
      · have hi : i = 2 := Fin.ext (by rw [h2, coreVal_two])
        subst hi
        rw [mpcUnitTwist_two, mpcUnitUntwist_three, mpcUnitUntwist_two]
        group
      · by_cases h3 : (i : ℕ) = 3
        · have hi : i = 3 := Fin.ext (by rw [h3, coreVal_three])
          subst hi
          rw [mpcUnitTwist_three, mpcUnitUntwist_two,
            NProcyclicCore.zpowHat_etaHatZ_eq_zpowZtwo hP,
            NProcyclicCore.zpowZtwo_inv_unit_cancel]
        · rw [mpcUnitTwist_apply_ne alpha r p eta h _ h0 h1 h2 h3,
            mpcUnitUntwist_apply_ne hP alpha r p eta h _ h0 h1 h2 h3]

theorem mpcUnitUntwist_mpcUnitTwist (hP : IsProP 2 P) (alpha r p : ℕ)
    (eta : ℤ_[2]ˣ) (h : ℕ) (c : Fin (coreRank h) → P) :
    mpcUnitUntwist hP alpha r p eta h (mpcUnitTwist alpha r p eta h c) = c := by
  funext i
  by_cases h0 : (i : ℕ) = 0
  · have hi : i = 0 := Fin.ext (by rw [h0, coreVal_zero])
    subst hi
    rw [mpcUnitUntwist_zero, mpcUnitTwist_zero, mpcUnitTwist_two]
    group
  · by_cases h1 : (i : ℕ) = 1
    · have hi : i = 1 := Fin.ext (by rw [h1, coreVal_one])
      subst hi
      rw [mpcUnitUntwist_one, mpcUnitTwist_one, mpcUnitTwist_three,
        NProcyclicCore.zpowHat_etaHatZ_eq_zpowZtwo hP,
        NProcyclicCore.zpowZtwo_unit_inv_cancel]
      group
    · by_cases h2 : (i : ℕ) = 2
      · have hi : i = 2 := Fin.ext (by rw [h2, coreVal_two])
        subst hi
        rw [mpcUnitUntwist_two, mpcUnitTwist_three,
          NProcyclicCore.zpowHat_etaHatZ_eq_zpowZtwo hP,
          NProcyclicCore.zpowZtwo_unit_inv_cancel]
      · by_cases h3 : (i : ℕ) = 3
        · have hi : i = 3 := Fin.ext (by rw [h3, coreVal_three])
          subst hi
          rw [mpcUnitUntwist_three, mpcUnitTwist_two, mpcUnitTwist_three,
            NProcyclicCore.zpowHat_etaHatZ_eq_zpowZtwo hP,
            NProcyclicCore.zpowZtwo_unit_inv_cancel]
          group
        · rw [mpcUnitUntwist_apply_ne hP alpha r p eta h _ h0 h1 h2 h3,
            mpcUnitTwist_apply_ne alpha r p eta h _ h0 h1 h2 h3]

omit [T2Space P] in
theorem map_mpcUnitTwist {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]
    (f : ContinuousMonoidHom P Q) (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (c : Fin (coreRank h) → P) :
    (fun i ↦ f (mpcUnitTwist alpha r p eta h c i)) =
      mpcUnitTwist alpha r p eta h (fun i ↦ f (c i)) := by
  funext i
  by_cases h0 : (i : ℕ) = 0
  · simp only [mpcUnitTwist, if_pos h0, map_mul, map_inv, map_pow]
  · by_cases h1 : (i : ℕ) = 1
    · simp only [mpcUnitTwist, if_neg h0, if_pos h1, map_mul, map_pow]
    · by_cases h2 : (i : ℕ) = 2
      · simp only [mpcUnitTwist, if_neg h0, if_neg h1, if_pos h2, map_mul, map_pow]
      · by_cases h3 : (i : ℕ) = 3
        · simp only [mpcUnitTwist, if_neg h0, if_neg h1, if_neg h2, if_pos h3,
            map_zpowHat]
        · simp only [mpcUnitTwist, if_neg h0, if_neg h1, if_neg h2, if_neg h3]

theorem map_mpcUnitUntwist {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]
    (hP : IsProP 2 P) (hQ : IsProP 2 Q) (f : ContinuousMonoidHom P Q)
    (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ) (c : Fin (coreRank h) → P) :
    (fun i ↦ f (mpcUnitUntwist hP alpha r p eta h c i)) =
      mpcUnitUntwist hQ alpha r p eta h (fun i ↦ f (c i)) := by
  funext i
  by_cases h0 : (i : ℕ) = 0
  · simp only [mpcUnitUntwist, if_pos h0, map_inv, map_mul, map_pow]
  · by_cases h1 : (i : ℕ) = 1
    · simp only [mpcUnitUntwist, if_neg h0, if_pos h1, map_mul, map_zpow,
        map_zpowZtwo hP hQ]
    · by_cases h2 : (i : ℕ) = 2
      · simp only [mpcUnitUntwist, if_neg h0, if_neg h1, if_pos h2,
          map_zpowZtwo hP hQ]
      · by_cases h3 : (i : ℕ) = 3
        · simp only [mpcUnitUntwist, if_neg h0, if_neg h1, if_neg h2, if_pos h3,
            map_mul, map_zpow, map_zpowZtwo hP hQ]
        · simp only [mpcUnitUntwist, if_neg h0, if_neg h1, if_neg h2, if_neg h3]

/-- Alphabet marking to standard `D_M` core coordinates. -/
noncomputable def mpcToCoreUnit (_hP : IsProP 2 P) (alpha r p : ℕ) (eta : ℤ_[2]ˣ)
    (h : ℕ) (t : Marking (2 + 2 * h) P) : Fin (coreRank h) → P :=
  mpcUnitTwist alpha r p eta h ((nReindex h).toCore t)

/-- Standard `D_M` coordinates to the semantic arbitrary-unit alphabet marking. -/
noncomputable def mpcOfCoreUnit (hP : IsProP 2 P) (alpha r p : ℕ) (eta : ℤ_[2]ˣ)
    (h : ℕ) (c : Fin (coreRank h) → P) : Marking (2 + 2 * h) P :=
  (nReindex h).ofCore (mpcUnitUntwist hP alpha r p eta h c)

@[simp] theorem mpcOfCoreUnit_tau (hP : IsProP 2 P) (alpha r p : ℕ) (eta : ℤ_[2]ˣ)
    (h : ℕ) (c : Fin (coreRank h) → P) :
    (mpcOfCoreUnit hP alpha r p eta h c).τ = 1 :=
  (nReindex h).ofCore_tau _

theorem mpcToCoreUnit_ofCore (hP : IsProP 2 P) (alpha r p : ℕ) (eta : ℤ_[2]ˣ)
    (h : ℕ) (c : Fin (coreRank h) → P) :
    mpcToCoreUnit hP alpha r p eta h (mpcOfCoreUnit hP alpha r p eta h c) = c := by
  rw [mpcToCoreUnit, mpcOfCoreUnit, (nReindex h).toCore_ofCore,
    mpcUnitTwist_mpcUnitUntwist]

theorem mpcOfCoreUnit_toCore (hP : IsProP 2 P) (alpha r p : ℕ) (eta : ℤ_[2]ˣ)
    (h : ℕ) (t : Marking (2 + 2 * h) P) (ht : t.τ = 1) :
    mpcOfCoreUnit hP alpha r p eta h (mpcToCoreUnit hP alpha r p eta h t) = t := by
  rw [mpcOfCoreUnit, mpcToCoreUnit, mpcUnitUntwist_mpcUnitTwist,
    (nReindex h).ofCore_toCore t ht]

end ProTwoDictionary

/-! ## Universal property -/

theorem mpcProTwoWordUnit_toCore (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (halpha : 1 ≤ alpha) {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P] (hP : IsProP 2 P)
    (t : Marking (2 + 2 * h) P) :
    t.eval (pro2 (mpcWUnit alpha r p eta h)) =
      mRelWord alpha (mpcToCoreUnit hP alpha r p eta h t) :=
  mpcProTwoWordUnit alpha r p eta h halpha t

theorem mpcToCoreUnit_nat {P Q : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q] [T2Space Q]
    [TotallyDisconnectedSpace Q] (hP : IsProP 2 P) (hQ : IsProP 2 Q)
    (f : ContinuousMonoidHom P Q) (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (t : Marking (2 + 2 * h) P) :
    (fun i ↦ f (mpcToCoreUnit hP alpha r p eta h t i)) =
      mpcToCoreUnit hQ alpha r p eta h (t.map ⇑f) := by
  rw [mpcToCoreUnit, mpcToCoreUnit]
  calc
    (fun i ↦ f (mpcUnitTwist alpha r p eta h ((nReindex h).toCore t) i)) =
        mpcUnitTwist alpha r p eta h (fun i ↦ f ((nReindex h).toCore t i)) :=
      map_mpcUnitTwist f alpha r p eta h _
    _ = mpcUnitTwist alpha r p eta h ((nReindex h).toCore (t.map ⇑f)) := by
      congr 1

theorem mpcOfCoreUnit_nat {P Q : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q] [T2Space Q]
    [TotallyDisconnectedSpace Q] (hP : IsProP 2 P) (hQ : IsProP 2 Q)
    (f : ContinuousMonoidHom P Q) (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (c : Fin (coreRank h) → P) (g : Generator (2 + 2 * h)) :
    f (mpcOfCoreUnit hP alpha r p eta h c g) =
      mpcOfCoreUnit hQ alpha r p eta h (fun i ↦ f (c i)) g := by
  rw [mpcOfCoreUnit, mpcOfCoreUnit, (nReindex h).ofCore_nat]
  exact congrArg (fun v ↦ (nReindex h).ofCore v g)
    (map_mpcUnitUntwist hP hQ f alpha r p eta h c)

/-- The forward twist respects equality under two homomorphisms into an arbitrary profinite
codomain.  At slot `3`, this uses semantic `Zhat`-powering and `map_zpowHat`. -/
theorem mpcUnitTwist_hom_eq {P A : Type} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A] [T2Space A]
    [TotallyDisconnectedSpace A] (phi psi : ContinuousMonoidHom P A)
    (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ) (c : Fin (coreRank h) → P)
    (hc : ∀ i, phi (c i) = psi (c i)) :
    ∀ i, phi (mpcUnitTwist alpha r p eta h c i) =
      psi (mpcUnitTwist alpha r p eta h c i) := by
  intro i
  by_cases h0 : (i : ℕ) = 0
  · have hi : i = 0 := Fin.ext (by rw [h0, coreVal_zero])
    subst hi
    simp only [mpcUnitTwist_zero, map_mul, map_inv, map_pow]
    rw [hc 0, hc 2, hc 3]
  · by_cases h1 : (i : ℕ) = 1
    · have hi : i = 1 := Fin.ext (by rw [h1, coreVal_one])
      subst hi
      rw [mpcUnitTwist_one, map_mul, map_mul, map_pow, map_pow, hc, hc]
    · by_cases h2 : (i : ℕ) = 2
      · have hi : i = 2 := Fin.ext (by rw [h2, coreVal_two])
        subst hi
        rw [mpcUnitTwist_two, map_mul, map_mul, map_pow, map_pow, hc, hc]
      · by_cases h3 : (i : ℕ) = 3
        · have hi : i = 3 := Fin.ext (by rw [h3, coreVal_three])
          subst hi
          rw [mpcUnitTwist_three, map_zpowHat, map_zpowHat, hc]
        · rw [mpcUnitTwist_apply_ne alpha r p eta h c h0 h1 h2 h3]
          exact hc i

/-- The semantic arbitrary-unit, arbitrary-handle procyclic-`M` core presentation. -/
noncomputable def mpcCorePresentationUnit (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (halpha : 1 ≤ alpha) :
    CorePresentation (2 + 2 * h) (mpcWUnit alpha r p eta h) (DM alpha h) where
  isProP := isProP_DM alpha h
  mark := mpcOfCoreUnit (isProP_DM alpha h) alpha r p eta h (dmGen alpha h)
  mark_tau := mpcOfCoreUnit_tau _ _ _ _ _ _ _
  rel := by
    rw [mpcProTwoWordUnit_toCore alpha r p eta h halpha (isProP_DM alpha h),
      mpcToCoreUnit_ofCore, dm_relation]
  liftHom := fun hQ t _ hrel ↦
    (presentedBy_DM alpha h).liftHom hQ (mpcToCoreUnit hQ alpha r p eta h t) (by
      change mRelWord alpha (mpcToCoreUnit hQ alpha r p eta h t) = 1
      rw [← mpcProTwoWordUnit_toCore alpha r p eta h halpha hQ]
      exact hrel)
  liftHom_mark := fun hQ t ht hrel g ↦ by
    rw [mpcOfCoreUnit_nat (isProP_DM alpha h) hQ]
    have hpt : (fun i ↦ (presentedBy_DM alpha h).liftHom hQ
        (mpcToCoreUnit hQ alpha r p eta h t) (by
          change mRelWord alpha (mpcToCoreUnit hQ alpha r p eta h t) = 1
          rw [← mpcProTwoWordUnit_toCore alpha r p eta h halpha hQ]
          exact hrel) (dmGen alpha h i)) = mpcToCoreUnit hQ alpha r p eta h t := by
      funext i
      exact (presentedBy_DM alpha h).liftHom_mark hQ
        (mpcToCoreUnit hQ alpha r p eta h t) _ i
    rw [hpt, mpcOfCoreUnit_toCore _ _ _ _ _ _ t ht]
  hom_ext := fun phi psi heq ↦ (presentedBy_DM alpha h).hom_ext phi psi fun i ↦ by
    have hletters : ∀ k, phi ((nReindex h).toCore
        (mpcOfCoreUnit (isProP_DM alpha h) alpha r p eta h (dmGen alpha h)) k) =
        psi ((nReindex h).toCore
          (mpcOfCoreUnit (isProP_DM alpha h) alpha r p eta h (dmGen alpha h)) k) := by
      intro k
      exact heq (nIdx h k)
    have htwist := mpcUnitTwist_hom_eq phi psi alpha r p eta h
      ((nReindex h).toCore
        (mpcOfCoreUnit (isProP_DM alpha h) alpha r p eta h (dmGen alpha h))) hletters i
    have hcore := congrFun (mpcToCoreUnit_ofCore (isProP_DM alpha h) alpha r p eta h
      (dmGen alpha h)) i
    rw [mpcToCoreUnit] at hcore
    rw [hcore] at htwist
    exact htwist

end GQ2.Dyadic.Instances.MProcyclicCore

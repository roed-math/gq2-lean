/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.MpcGeneralHeadCompletion
import GQ2.Dyadic.Instances.EvenStratumShift

/-!
# Uniform abelian decomposition of the remaining `C` correction

At a general Mpc stage, head completion differs from full marking only in the `C` correction.
This module decomposes every deep, `chiM`-neutral element into a deep derived element and a
canonical word supported on `B`, `C`, and the handle generators.  The construction is uniform
in the degree, handle count, and filtration depth.

Thus the remaining absorption problem consists of `2 + 2h` tower families.  No nilpotency
class is selected.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralAbelianDecomposition

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralFiniteSpan
open GQ2.Dyadic.Instances.MpcGeneralHeadCompletion
open GQ2.Dyadic.Instances.MpcGeneralHeadReflection
open GQ2.Roe.Labute
open scoped GQ2.SectionThree.TopAbInstances

/-- The closed subgroup on which one additive `Z_2` row is divisible by `2^m`. -/
private def mpcGeneralRowDivSub {alpha h : ℕ}
    (f : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (m : ℕ) : Subgroup (DM alpha h : Type) where
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

private theorem mpcGeneralRowDivSub_closed {alpha h : ℕ}
    (f : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (m : ℕ) : IsClosed ((mpcGeneralRowDivSub f m : Subgroup (DM alpha h : Type)) :
      Set (DM alpha h : Type)) := by
  have hset : ((mpcGeneralRowDivSub f m : Subgroup (DM alpha h : Type)) :
      Set (DM alpha h : Type)) =
      (fun g : (DM alpha h : Type) ↦ toAdd (f g)) ⁻¹'
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
  exact hdiv.preimage (continuous_toAdd.comp f.continuous)

/-- Every additive row of a depth-`j` element is divisible by `2^(j-1)`, uniformly for
`DM alpha h`. -/
theorem mpcGeneral_row_dvd {alpha h : ℕ}
    (f : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    {j : ℕ} {g : (DM alpha h : Type)}
    (hg : g ∈ twoCentralSeries (DM alpha h : Type) j) :
    (2 ^ (j - 1) : ℤ_[2]) ∣ toAdd (f g) := by
  have hmain : ∀ m : ℕ,
      twoCentralSeries (DM alpha h : Type) (m + 1) ≤ mpcGeneralRowDivSub f m := by
    intro m
    induction m with
    | zero =>
      intro v _
      change (2 ^ 0 : ℤ_[2]) ∣ toAdd (f v)
      rw [pow_zero]
      exact one_dvd _
    | succ m ih =>
      rw [twoCentralSeries_succ (G := (DM alpha h : Type)) (by omega),
        twoCentralSucc]
      refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_)
        (mpcGeneralRowDivSub_closed f (m + 1))
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
  match j with
  | 0 =>
    rw [Nat.zero_sub, pow_zero]
    exact one_dvd _
  | j + 1 =>
    rw [Nat.add_sub_cancel]
    exact hmain j hg

/-- A `Z_2` power with exponent divisible by `2^(j-1)` lies in depth `j`. -/
theorem mpcGeneral_zpow_dvd_mem {alpha h : ℕ}
    {g : (DM alpha h : Type)} {a : ℤ_[2]} {j : ℕ}
    (hj : 1 ≤ j) (ha : (2 ^ (j - 1) : ℤ_[2]) ∣ a) :
    zpowZtwo (isProP_DM alpha h) g a ∈
      twoCentralSeries (DM alpha h : Type) j := by
  obtain ⟨c, rfl⟩ := ha
  have hcast : (((2 ^ (j - 1) : ℕ) : ℤ_[2])) =
      (2 : ℤ_[2]) ^ (j - 1) := by push_cast; ring
  have heq : zpowZtwo (isProP_DM alpha h) g
      ((2 : ℤ_[2]) ^ (j - 1) * c) =
      zpowZtwo (isProP_DM alpha h) g c ^ (2 ^ (j - 1)) := by
    rw [← zpowZtwo_natCast (isProP_DM alpha h)
      (zpowZtwo (isProP_DM alpha h) g c) (2 ^ (j - 1)),
      zpowZtwo_zpowZtwo, hcast]
    congr 1
    ring
  rw [heq, ← Nat.sub_add_cancel hj]
  exact pow_two_pow_mem_twoCentralSeries_succ
    (G := (DM alpha h : Type)) _ (j - 1)

/-- A group-level `Z_2`-power word in the marked generators. -/
def mpcGeneralGroupWord (alpha h : ℕ)
    (c : Fin (coreRank h) → ℤ_[2]) : (DM alpha h : Type) :=
  (List.ofFn fun i => zpowZtwo (isProP_DM alpha h) (dmGen alpha h i) (c i)).prod

/-- Abelianization of the group-level word is the M-frame word. -/
theorem abMk_mpcGeneralGroupWord (alpha h : ℕ)
    (c : Fin (coreRank h) → ℤ_[2]) :
    GQ2.SectionThree.abMk (mpcGeneralGroupWord alpha h c) = mAbWord alpha h c := by
  let F : ContinuousMonoidHom (DM alpha h : Type)
      (topAbelianization (DM alpha h : Type)) :=
    ⟨GQ2.SectionThree.abMk, GQ2.SectionThree.continuous_abMk⟩
  rw [mpcGeneralGroupWord, map_list_prod, List.map_ofFn, mAbWord]
  rw [Fin.prod_ofFn]
  exact Finset.prod_congr rfl fun i _ => by
    simp only [Function.comp_apply]
    change F (zpowZtwo (isProP_DM alpha h) (dmGen alpha h i) (c i)) = _
    rw [map_zpowZtwo (isProP_DM alpha h) (mIsProP_two_topAb_DM alpha h)]
    rfl

/-- Coordinate vector which discards torsion and the `D` row while preserving all other
M-frame coordinates. -/
def mpcGeneralChiNeutralVec {alpha h : ℕ} (halpha : 1 ≤ alpha) (x : DM alpha h) :
    Fin (coreRank h) → ℤ_[2] :=
  mSurjVec alpha 0
    (mBHom alpha h (GQ2.SectionThree.abMk x)).toAdd
    (mCHom halpha h (GQ2.SectionThree.abMk x)).toAdd
    0
    (fun k => (mHHom alpha k (GQ2.SectionThree.abMk x)).toAdd)

/-- At depth at least two, the order-two M-frame coordinate vanishes. -/
theorem mpcGeneral_torsion_eq_one_of_depth {alpha h j : ℕ} (hj : 2 ≤ j)
    {x : DM alpha h} (hx : x ∈ twoCentralSeries (DM alpha h : Type) j) :
    mTHom alpha h (GQ2.SectionThree.abMk x) = 1 := by
  let f : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative (ZMod 2)) :=
    (mTHom alpha h).comp (mAbMkHom alpha h)
  have him : f x ∈ twoCentralSeries (Multiplicative (ZMod 2)) j :=
    map_twoCentralSeries_le f.toMonoidHom f.continuous_toFun j ⟨x, hx, rfl⟩
  have him2 : f x ∈ twoCentralSeries (Multiplicative (ZMod 2)) 2 :=
    twoCentralSeries_antitone (G := Multiplicative (ZMod 2)) hj him
  obtain ⟨a, ha⟩ := evenStratumShift_twoCentralSeries_le_pow 1 him2
  change f x = 1
  rw [← ha]
  obtain ⟨z, rfl⟩ : ∃ z : ZMod 2, ofAdd z = a := ⟨toAdd a, rfl⟩
  change ofAdd z ^ 2 = 1
  rw [← ofAdd_nsmul, show (2 : ℕ) • z = 0 by
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul],
    ofAdd_zero]

/-- Every coordinate of the canonical `B,C,handles` word has the correct depth
divisibility. -/
theorem mpcGeneralChiNeutralVec_dvd {alpha h j : ℕ} (halpha : 1 ≤ alpha)
    {x : DM alpha h} (hx : x ∈ twoCentralSeries (DM alpha h : Type) j) :
    ∀ i, (2 ^ (j - 1) : ℤ_[2]) ∣ mpcGeneralChiNeutralVec halpha x i := by
  intro i
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨k, rfl⟩
  · rw [mpcGeneralChiNeutralVec, mSurjVec_zero]
    exact dvd_zero _
  · rw [mpcGeneralChiNeutralVec, mSurjVec_one]
    exact mpcGeneral_row_dvd
      ((mBHom alpha h).comp (mAbMkHom alpha h)) hx
  · rw [mpcGeneralChiNeutralVec, mSurjVec_two]
    simp only [ZMod.val_zero, Nat.cast_zero, mul_zero, add_zero]
    exact mpcGeneral_row_dvd
      ((mCHom halpha h).comp (mAbMkHom alpha h)) hx
  · rw [mpcGeneralChiNeutralVec, mSurjVec_three]
    exact dvd_zero _
  · rw [mpcGeneralChiNeutralVec, mSurjVec_handle]
    exact mpcGeneral_row_dvd
      ((mHHom alpha k).comp (mAbMkHom alpha h)) hx

/-- A coordinatewise divisible group word lies at the requested depth. -/
theorem mpcGeneralGroupWord_mem_depth {alpha h j : ℕ} (hj : 1 ≤ j)
    {c : Fin (coreRank h) → ℤ_[2]}
    (hc : ∀ i, (2 ^ (j - 1) : ℤ_[2]) ∣ c i) :
    mpcGeneralGroupWord alpha h c ∈ twoCentralSeries (DM alpha h : Type) j := by
  rw [mpcGeneralGroupWord]
  apply Subgroup.list_prod_mem
  intro y hy
  rw [List.mem_ofFn] at hy
  obtain ⟨i, rfl⟩ := hy
  exact mpcGeneral_zpow_dvd_mem hj (hc i)

/-- For a deep `chiM`-neutral element, the canonical `B,C,handles` word has exactly the same
topological abelianization. -/
theorem abMk_mpcGeneralChiNeutralWord_eq {alpha h j : ℕ} (halpha : 2 ≤ alpha)
    {x : DM alpha h} (hx : x ∈ twoCentralSeries (DM alpha h : Type) j)
    (hj : 2 ≤ j) (hchi : chiM alpha h x = 1) :
    GQ2.SectionThree.abMk
        (mpcGeneralGroupWord alpha h
          (mpcGeneralChiNeutralVec (by omega) x)) =
      GQ2.SectionThree.abMk x := by
  apply mPhiHom_injective (by omega : 1 ≤ alpha) h
  rw [abMk_mpcGeneralGroupWord, mPhiHom_word]
  have ht := mpcGeneral_torsion_eq_one_of_depth hj hx
  have hd := mpcGeneralDeltaD_eq_one_of_chi_eq_one halpha hchi
  change mDHom alpha h (GQ2.SectionThree.abMk x) = 1 at hd
  change ofAdd (_, _, _, _, _) =
    ofAdd ((mTHom alpha h (GQ2.SectionThree.abMk x)).toAdd,
      (mBHom alpha h (GQ2.SectionThree.abMk x)).toAdd,
      (mCHom (by omega) h (GQ2.SectionThree.abMk x)).toAdd,
      (mDHom alpha h (GQ2.SectionThree.abMk x)).toAdd,
      fun k => (mHHom alpha k (GQ2.SectionThree.abMk x)).toAdd)
  rw [mpcGeneralChiNeutralVec, mSurjVec_zero, mSurjVec_one,
    mSurjVec_two, mSurjVec_three]
  simp_rw [mSurjVec_handle]
  simp only [ZMod.val_zero, Nat.cast_zero, mul_zero, add_zero]
  rw [GQ2.SectionThree.zpowZtwo_zero, ht, hd]
  simp only [toAdd_one, zero_add]

/-- Uniform abelian decomposition: a depth-`j`, `chiM`-neutral element is a deep derived
element times a deep word supported only on `B`, `C`, and handles. -/
theorem exists_mpcGeneral_derived_mul_tower {alpha h j : ℕ} (halpha : 2 ≤ alpha)
    {x : DM alpha h} (hx : x ∈ twoCentralSeries (DM alpha h : Type) j)
    (hj : 2 ≤ j) (hchi : chiM alpha h x = 1) :
    ∃ d y : DM alpha h,
      d ∈ twoCentralSeries (DM alpha h : Type) j ∧
      GQ2.SectionThree.abMk d = 1 ∧
      y ∈ twoCentralSeries (DM alpha h : Type) j ∧
      x = d * y ∧
      y = mpcGeneralGroupWord alpha h
        (mpcGeneralChiNeutralVec (by omega) x) := by
  let y := mpcGeneralGroupWord alpha h
    (mpcGeneralChiNeutralVec (by omega : 1 ≤ alpha) x)
  let d := x * y⁻¹
  have hy : y ∈ twoCentralSeries (DM alpha h : Type) j :=
    mpcGeneralGroupWord_mem_depth (by omega)
      (mpcGeneralChiNeutralVec_dvd (by omega) hx)
  have hd : d ∈ twoCentralSeries (DM alpha h : Type) j :=
    Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hy)
  refine ⟨d, y, hd, ?_, hy, ?_, rfl⟩
  · dsimp only [d]
    rw [map_mul, map_inv, abMk_mpcGeneralChiNeutralWord_eq halpha hx hj hchi,
      mul_inv_cancel]
  · dsimp only [d]
    group

end

end GQ2.Dyadic.Instances.MpcGeneralAbelianDecomposition

section AxiomPins

open GQ2.Dyadic.Instances.MpcGeneralAbelianDecomposition

#print axioms mpcGeneral_row_dvd
#print axioms mpcGeneral_zpow_dvd_mem
#print axioms mpcGeneralGroupWord
#print axioms abMk_mpcGeneralGroupWord
#print axioms mpcGeneralChiNeutralVec
#print axioms mpcGeneral_torsion_eq_one_of_depth
#print axioms mpcGeneralChiNeutralVec_dvd
#print axioms mpcGeneralGroupWord_mem_depth
#print axioms abMk_mpcGeneralChiNeutralWord_eq
#print axioms exists_mpcGeneral_derived_mul_tower

end AxiomPins

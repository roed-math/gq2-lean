/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.MpcGeneralFrattiniBaseReduction
import GQ2.Dyadic.SqCore.GradedUniformTower

/-!
# Parity reduction for the general Mpc tower atoms

At depth `k - 1`, every canonical generator exponent is divisible by `2^(k-2)`.
Modulo the next layer its bracket with `D` therefore depends only on the parity of the
remaining `Z_2` coefficient.  An even coefficient vanishes; an odd coefficient is the
standard bracket of the canonical power `g^(2^(k-2))`.

Consequently the remaining tower theorem may be stated only for these canonical powers,
uniformly in `alpha`, the handle count, the rung, and the generator index.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralTowerParityReduction

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralAbelianDecomposition
open GQ2.Dyadic.Instances.MpcGeneralFrattiniBaseReduction
open GQ2.Dyadic.Instances.MpcGeneralMarkedSpan
open GQ2.Dyadic.Instances.MpcGeneralTowerAtoms
open GQ2.Roe.Labute
open GQ2.Dyadic.SqCore

/-- Exactly the generator indices which can occur with odd residual coefficient. -/
def mpcGeneralTowerIndexActive {h : ℕ} (i : Fin (coreRank h)) : Prop :=
  i ≠ 0 ∧ i ≠ 3

/-- The standard generator-power representative of the depth-`k-1` tower line. -/
def mpcGeneralCanonicalTowerAtom (alpha h k : ℕ)
    (i : Fin (coreRank h)) : DM alpha h :=
  zpowZtwo (isProP_DM alpha h) (dmGen alpha h i)
    ((2 : ℤ_[2]) ^ (k - 2))

/-- The standard tower representative has depth `k - 1`. -/
theorem mpcGeneralCanonicalTowerAtom_mem {alpha h k : ℕ}
    (hk : 3 ≤ k) (i : Fin (coreRank h)) :
    mpcGeneralCanonicalTowerAtom alpha h k i ∈
      twoCentralSeries (DM alpha h : Type) (k - 1) := by
  apply mpcGeneral_zpow_dvd_mem (by omega)
  rw [show (k - 1) - 1 = k - 2 by omega]

/-- An even residual coefficient pushes the complete tower atom one layer deeper. -/
theorem mpcGeneralTowerAtom_mem_succ_of_even {alpha h k : ℕ}
    (halpha : 2 ≤ alpha) (hk : 3 ≤ k) {x : DM alpha h}
    (_hx : x ∈ twoCentralSeries (DM alpha h : Type) (k - 1))
    (i : Fin (coreRank h))
    {q : ℤ_[2]}
    (hq : mpcGeneralChiNeutralVec (by omega : 1 ≤ alpha) x i =
      (2 : ℤ_[2]) ^ (k - 2) * q)
    (heven : mParityZ q = 0) :
    mpcGeneralTowerAtom (by omega : 1 ≤ alpha) x i ∈
      twoCentralSeries (DM alpha h : Type) k := by
  obtain ⟨y, hy⟩ := (mParityZ_eq_zero_iff q).mp heven
  apply mpcGeneral_zpow_dvd_mem (by omega)
  refine ⟨y, ?_⟩
  rw [hq, hy]
  have he : k - 1 = (k - 2) + 1 := by omega
  rw [he, pow_succ]
  ring

/-- An odd residual coefficient is the standard tower representative times a deeper
factor. -/
theorem exists_mpcGeneralTowerAtom_eq_canonical_mul_deeper
    {alpha h k : ℕ} (halpha : 2 ≤ alpha) (hk : 3 ≤ k)
    {x : DM alpha h}
    (i : Fin (coreRank h)) {q : ℤ_[2]}
    (hq : mpcGeneralChiNeutralVec (by omega : 1 ≤ alpha) x i =
      (2 : ℤ_[2]) ^ (k - 2) * q)
    (hodd : mParityZ q = 1) :
    ∃ u : DM alpha h,
      u ∈ twoCentralSeries (DM alpha h : Type) k ∧
      mpcGeneralTowerAtom (by omega : 1 ≤ alpha) x i =
        mpcGeneralCanonicalTowerAtom alpha h k i * u := by
  obtain ⟨y, hy⟩ := (mParityZ_eq_one_iff q).mp hodd
  let u := zpowZtwo (isProP_DM alpha h) (dmGen alpha h i)
    ((2 : ℤ_[2]) ^ (k - 1) * y)
  refine ⟨u, ?_, ?_⟩
  · apply mpcGeneral_zpow_dvd_mem (by omega)
    exact dvd_mul_right _ y
  · unfold mpcGeneralTowerAtom mpcGeneralCanonicalTowerAtom
    rw [hq, hy]
    rw [show (2 : ℤ_[2]) ^ (k - 2) * (1 + 2 * y) =
        (2 : ℤ_[2]) ^ (k - 2) + (2 : ℤ_[2]) ^ (k - 1) * y by
      have he : k - 1 = (k - 2) + 1 := by omega
      rw [he, pow_succ]
      ring]
    exact zpowZtwo_add (isProP_DM alpha h) _ _ _

/-- At the next quotient an odd-coefficient tower bracket is the canonical bracket. -/
theorem mpcGeneralTowerAtom_bracket_eq_canonical_of_odd
    {alpha h k : ℕ} (halpha : 2 ≤ alpha) (hk : 3 ≤ k)
    {x : DM alpha h}
    (i : Fin (coreRank h)) {q : ℤ_[2]}
    (hq : mpcGeneralChiNeutralVec (by omega : 1 ≤ alpha) x i =
      (2 : ℤ_[2]) ^ (k - 2) * q)
    (hodd : mParityZ q = 1) :
    levelMk (DM alpha h) (k + 1)
        (commP (mpcGeneralTowerAtom (by omega) x i) (dmD alpha h)) =
      levelMk (DM alpha h) (k + 1)
        (commP (mpcGeneralCanonicalTowerAtom alpha h k i) (dmD alpha h)) := by
  obtain ⟨u, hu, heq⟩ :=
    exists_mpcGeneralTowerAtom_eq_canonical_mul_deeper halpha hk i hq hodd
  have hu' : u ∈ twoCentralSeries (DM alpha h : Type) (k - 1 + 1) := by
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have H := gTower_comm_near_slack (G := DM alpha h) (k := k - 1)
    hu' (mpcGeneralTowerAtom (by omega) x i) (dmD alpha h) heq
  rwa [show k - 1 + 2 = k + 1 by omega] at H

/-- An odd residual coefficient cannot occur in the discarded `A` or `D` coordinates. -/
theorem mpcGeneralTowerIndexActive_of_odd
    {alpha h k : ℕ} (halpha : 2 ≤ alpha) (_hk : 3 ≤ k)
    {x : DM alpha h} (i : Fin (coreRank h)) {q : ℤ_[2]}
    (hq : mpcGeneralChiNeutralVec (by omega : 1 ≤ alpha) x i =
      (2 : ℤ_[2]) ^ (k - 2) * q)
    (hodd : mParityZ q = 1) : mpcGeneralTowerIndexActive i := by
  have hp : (2 : ℤ_[2]) ^ (k - 2) ≠ 0 := pow_ne_zero _ (by norm_num)
  constructor
  · intro hi
    subst i
    rw [mpcGeneralChiNeutralVec, mSurjVec_zero] at hq
    have hq0 : q = 0 := (mul_eq_zero.mp hq.symm).resolve_left hp
    rw [hq0, mParityZ_zero] at hodd
    exact zero_ne_one hodd
  · intro hi
    subst i
    rw [mpcGeneralChiNeutralVec, mSurjVec_three] at hq
    have hq0 : q = 0 := (mul_eq_zero.mp hq.symm).resolve_left hp
    rw [hq0, mParityZ_zero] at hodd
    exact zero_ne_one hodd

/-- The canonical-power bracket supply, with no arbitrary coefficient left. -/
def MpcGeneralCanonicalTowerBracketSupply (alpha h : ℕ) : Prop :=
  ∀ k (hk : 3 ≤ k) (i : Fin (coreRank h)), mpcGeneralTowerIndexActive i →
    (⟨commP
        (levelMk (DM alpha h) (k + 1)
          (mpcGeneralCanonicalTowerAtom alpha h k i))
        (levelMk (DM alpha h) (k + 1) (dmD alpha h)),
      commP_mem_zLayer k hk
        ⟨mpcGeneralCanonicalTowerAtom alpha h k i,
          mpcGeneralCanonicalTowerAtom_mem hk i, rfl⟩ _⟩ :
      zLayer (DM alpha h) k) ∈
        (mpcGeneralMarkedLevelShiftHom (dmGen alpha h) k hk).range

/-- Canonical-power supply absorbs every `Z_2` coefficient by parity. -/
theorem mpcGeneralStandardTowerAtomBracketSupply_of_canonical
    {alpha h : ℕ} (H : MpcGeneralCanonicalTowerBracketSupply alpha h) :
    MpcGeneralStandardTowerAtomBracketSupply alpha h := by
  intro halpha k hk x hx hchi i
  dsimp only
  have hdvd := mpcGeneralChiNeutralVec_dvd (by omega : 1 ≤ alpha) hx i
  rw [show (k - 1) - 1 = k - 2 by omega] at hdvd
  obtain ⟨q, hq⟩ := hdvd
  by_cases heven : mParityZ q = 0
  · have hatom := mpcGeneralTowerAtom_mem_succ_of_even halpha hk hx i hq heven
    refine ⟨1, ?_⟩
    rw [map_one]
    apply Subtype.ext
    change 1 = commP
      (levelMk (DM alpha h) (k + 1)
        (mpcGeneralTowerAtom (by omega) x i))
      (levelMk (DM alpha h) (k + 1) (dmGen alpha h 3))
    have hcomm : commP (mpcGeneralTowerAtom (by omega) x i) (dmD alpha h) ∈
        twoCentralSeries (DM alpha h : Type) (k + 1) :=
      cfive_commP_mem_succ hatom _
    have hz : levelMk (DM alpha h) (k + 1)
        (commP (mpcGeneralTowerAtom (by omega) x i) (dmD alpha h)) = 1 :=
      (lim_mem_twoCentralSeries_iff_levelMk (k + 1) _).mp hcomm
    change 1 = levelMk (DM alpha h) (k + 1)
      (commP (mpcGeneralTowerAtom (by omega) x i) (dmGen alpha h 3))
    rw [show dmGen alpha h 3 = dmD alpha h from rfl]
    exact hz.symm
  · have hodd : mParityZ q = 1 := by
      have hcases : mParityZ q = 0 ∨ mParityZ q = 1 := by
        exact (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (mParityZ q)
      exact hcases.resolve_left heven
    obtain ⟨E, hE⟩ := H k hk i
      (mpcGeneralTowerIndexActive_of_odd halpha hk i hq hodd)
    refine ⟨E, ?_⟩
    rw [hE]
    apply Subtype.ext
    change levelMk (DM alpha h) (k + 1)
        (commP (mpcGeneralCanonicalTowerAtom alpha h k i) (dmD alpha h)) =
      levelMk (DM alpha h) (k + 1)
        (commP (mpcGeneralTowerAtom (by omega) x i) (dmD alpha h))
    exact (mpcGeneralTowerAtom_bracket_eq_canonical_of_odd
      halpha hk i hq hodd).symm

/-- The canonical tower theorem alone proves the general pivot shift. -/
theorem mpcPivShiftH_of_generalCanonicalTowerBrackets
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (H : MpcGeneralCanonicalTowerBracketSupply alpha h) :
    GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary.MpcPivShiftH alpha h :=
  mpcPivShiftH_of_generalStandardTowerBrackets halpha
    (mpcGeneralStandardTowerAtomBracketSupply_of_canonical H)

end

end GQ2.Dyadic.Instances.MpcGeneralTowerParityReduction

section AxiomPins

open GQ2.Dyadic.Instances.MpcGeneralTowerParityReduction

#print axioms mpcGeneralCanonicalTowerAtom
#print axioms mpcGeneralTowerIndexActive
#print axioms mpcGeneralCanonicalTowerAtom_mem
#print axioms mpcGeneralTowerAtom_mem_succ_of_even
#print axioms exists_mpcGeneralTowerAtom_eq_canonical_mul_deeper
#print axioms mpcGeneralTowerAtom_bracket_eq_canonical_of_odd
#print axioms mpcGeneralTowerIndexActive_of_odd
#print axioms MpcGeneralCanonicalTowerBracketSupply
#print axioms mpcGeneralStandardTowerAtomBracketSupply_of_canonical
#print axioms mpcPivShiftH_of_generalCanonicalTowerBrackets

end AxiomPins

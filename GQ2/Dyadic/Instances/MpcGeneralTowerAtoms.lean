/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.MpcGeneralTowerReduction
import GQ2.Dyadic.MarkedCore.MFrameApi

/-!
# The uniform `B`, `C`, and handle absorption families

The canonical tower word is an ordered product of generator powers.  Every factor lies in the
same deep exact-character subgroup: the `A` and `D` exponents are zero, the `B` exponent is
even, and `C` and all handle generators are orientation-neutral.  Therefore the tower-word
absorption theorem follows from absorption of its individual atoms.

Only `2 + 2h` atoms are nontrivial.  This is a single parameterized family statement, not a
collection of nilpotency-class calculations.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralTowerAtoms

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralAbelianDecomposition
open GQ2.Dyadic.Instances.MpcGeneralFiniteSpan
open GQ2.Dyadic.Instances.MpcGeneralHeadSpan
open GQ2.Dyadic.Instances.MpcGeneralMarkedSpan
open GQ2.Dyadic.Instances.MpcGeneralTowerReduction
open GQ2.Roe.Labute

/-- One generator-power factor in the canonical tower word. -/
def mpcGeneralTowerAtom {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (x : DM alpha h) (i : Fin (coreRank h)) : DM alpha h :=
  zpowZtwo (isProP_DM alpha h) (dmGen alpha h i)
    (mpcGeneralChiNeutralVec halpha x i)

/-- Every canonical atom has the required depth and exact orientation. -/
theorem mpcGeneralTowerAtom_mem {alpha h k : ℕ} (halpha : 2 ≤ alpha)
    (hk : 3 ≤ k) {x : DM alpha h}
    (hx : x ∈ twoCentralSeries (DM alpha h : Type) (k - 1))
    (_hchi : chiM alpha h x = 1) (i : Fin (coreRank h)) :
    mpcGeneralTowerAtom (by omega) x i ∈
      twoCentralSeries (DM alpha h : Type) (k - 1) ⊓
        mpcGeneralChiKer alpha h := by
  refine ⟨mpcGeneral_zpow_dvd_mem (by omega)
    (mpcGeneralChiNeutralVec_dvd (by omega) hx i), ?_⟩
  apply MonoidHom.mem_ker.mpr
  change chiM alpha h (mpcGeneralTowerAtom (by omega) x i) = 1
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨l, rfl⟩
  · simp [mpcGeneralTowerAtom, mpcGeneralChiNeutralVec,
      GQ2.SectionThree.zpowZtwo_zero]
  · have hdvd := mpcGeneralChiNeutralVec_dvd (by omega : 1 ≤ alpha) hx
      (1 : Fin (coreRank h))
    obtain ⟨q, hq⟩ := hdvd
    have hexp : mpcGeneralChiNeutralVec (by omega : 1 ≤ alpha) x 1 =
        (2 : ℤ_[2]) * ((2 : ℤ_[2]) ^ (k - 3) * q) := by
      rw [hq]
      have he : (k - 1) - 1 = (k - 3) + 1 := by omega
      rw [he, pow_succ']
      ring
    rw [mpcGeneralTowerAtom,
      map_zpowZtwo (isProP_DM alpha h) isProP_two_unitsPadicInt,
      show dmGen alpha h 1 = dmB alpha h from rfl, chiM_dmB,
      mNegOne_zpow, hexp, mSign_two_mul]
  · rw [mpcGeneralTowerAtom,
      map_zpowZtwo (isProP_DM alpha h) isProP_two_unitsPadicInt,
      show dmGen alpha h 2 = dmC alpha h from rfl, chiM_dmC,
      zpowZtwo_one_base]
  · simp [mpcGeneralTowerAtom, mpcGeneralChiNeutralVec,
      GQ2.SectionThree.zpowZtwo_zero]
  · rcases mHandleCoord_cases l with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [mpcGeneralTowerAtom,
        map_zpowZtwo (isProP_DM alpha h) isProP_two_unitsPadicInt,
        mHandleIdx_coordU, chiM_handleU, zpowZtwo_one_base]
    · rw [mpcGeneralTowerAtom,
        map_zpowZtwo (isProP_DM alpha h) isProP_two_unitsPadicInt,
        mHandleIdx_coordV, chiM_handleV, zpowZtwo_one_base]

/-- The singleton-`C` construction as a homomorphism on the deep exact-character subgroup. -/
noncomputable def mpcGeneralHeadSingleCHom (alpha h k : ℕ) :
    ↥(twoCentralSeries (DM alpha h : Type) (k - 1) ⊓
      mpcGeneralChiKer alpha h) →*
      MpcGeneralHeadLevelCorrection alpha h k where
  toFun x := mpcGeneralHeadSingleC x.1 x.2.1 (MonoidHom.mem_ker.mp x.2.2)
  map_one' := by
    classical
    funext i
    apply Subtype.ext
    by_cases hi : i = 2
    · subst hi
      simp [mpcGeneralHeadSingleC]
    · simp [mpcGeneralHeadSingleC, hi]
  map_mul' x y := by
    have hxchi : chiM alpha h x = 1 := by
      have hxmem := x.property.right
      change x.1 ∈ (chiM alpha h).toMonoidHom.ker at hxmem
      exact MonoidHom.mem_ker.mp hxmem
    have hychi : chiM alpha h y = 1 := by
      have hymem := y.property.right
      change y.1 ∈ (chiM alpha h).toMonoidHom.ker at hymem
      exact MonoidHom.mem_ker.mp hymem
    exact mpcGeneralHeadSingleC_mul (alpha := alpha) (h := h) (k := k)
      x.1 y.1 x.2.1 y.2.1 hxchi hychi

/-- Atomic absorption: each canonical generator-power singleton shift is in the fully marked
range.  The `A` and `D` clauses are trivial; the substantive family has `2 + 2h` members. -/
def MpcGeneralTowerAtomAbsorptionSupply (alpha h : ℕ) : Prop :=
  ∀ (halpha : 2 ≤ alpha) k (hk : 3 ≤ k)
    (m : Fin (coreRank h) → (DM alpha h : Type))
    (x : DM alpha h) (hx : x ∈ twoCentralSeries (DM alpha h : Type) (k - 1))
    (hchi : chiM alpha h x = 1) (i : Fin (coreRank h)),
    mpcGeneralHeadLevelShiftHom m k hk
        (mpcGeneralHeadSingleCHom alpha h k
          ⟨mpcGeneralTowerAtom (by omega) x i,
            mpcGeneralTowerAtom_mem halpha hk hx hchi i⟩) ∈
      (mpcGeneralMarkedLevelShiftHom m k hk).range

/-- The ordered product of the canonical atoms is the canonical tower word. -/
theorem mpcGeneralTowerAtoms_prod {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (x : DM alpha h) :
    (List.ofFn fun i => mpcGeneralTowerAtom halpha x i).prod =
      mpcGeneralGroupWord alpha h (mpcGeneralChiNeutralVec halpha x) :=
  rfl

/-- Atomic absorption implies absorption of the complete canonical tower word. -/
theorem mpcGeneralTowerCAbsorptionSupply_of_atoms
    {alpha h : ℕ} (H : MpcGeneralTowerAtomAbsorptionSupply alpha h) :
    MpcGeneralTowerCAbsorptionSupply alpha h := by
  intro halpha k hk m x hx hchi
  let A : Fin (coreRank h) →
      ↥(twoCentralSeries (DM alpha h : Type) (k - 1) ⊓
        mpcGeneralChiKer alpha h) := fun i =>
    ⟨mpcGeneralTowerAtom (by omega) x i,
      mpcGeneralTowerAtom_mem halpha hk hx hchi i⟩
  have hprod : ((List.ofFn A).prod : DM alpha h) =
      mpcGeneralGroupWord alpha h
        (mpcGeneralChiNeutralVec (by omega) x) := by
    change (twoCentralSeries (DM alpha h : Type) (k - 1) ⊓
      mpcGeneralChiKer alpha h).subtype (List.ofFn A).prod = _
    rw [map_list_prod, List.map_ofFn]
    exact mpcGeneralTowerAtoms_prod (by omega) x
  have hychi : chiM alpha h
      (mpcGeneralGroupWord alpha h (mpcGeneralChiNeutralVec (by omega) x)) = 1 := by
    rw [← hchi]
    exact congrArg (GQ2.SectionThree.abLiftG (chiM alpha h))
      (abMk_mpcGeneralChiNeutralWord_eq halpha hx (by omega) hchi)
  change mpcGeneralHeadLevelShiftHom m k hk
      (mpcGeneralHeadSingleC _ _ _) ∈ _
  have hsingle : mpcGeneralHeadSingleC
      (mpcGeneralGroupWord alpha h (mpcGeneralChiNeutralVec (by omega) x))
        (mpcGeneralGroupWord_mem_depth (by omega)
          (mpcGeneralChiNeutralVec_dvd (by omega) hx))
        hychi = mpcGeneralHeadSingleCHom alpha h k (List.ofFn A).prod := by
    funext i
    apply Subtype.ext
    by_cases hi : i = 2
    · subst hi
      simpa [mpcGeneralHeadSingleC, mpcGeneralHeadSingleCHom] using
        congrArg (levelMk (DM alpha h) (k + 1)) hprod.symm
    · simp [mpcGeneralHeadSingleC, mpcGeneralHeadSingleCHom, hi]
  rw [hsingle, map_list_prod, map_list_prod]
  apply Subgroup.list_prod_mem
  intro z hz
  rw [List.mem_map] at hz
  obtain ⟨a, ha, rfl⟩ := hz
  rw [List.mem_map] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  rw [List.mem_ofFn] at hi
  obtain ⟨j, rfl⟩ := hi
  exact H halpha k hk m x hx hchi j

/-- The atomic family theorem proves the general pivot shift. -/
theorem mpcPivShiftH_of_generalTowerAtoms
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (H : MpcGeneralTowerAtomAbsorptionSupply alpha h) :
    MpcGeneralHandlePivotBoundary.MpcPivShiftH alpha h :=
  mpcPivShiftH_of_generalTowerCAbsorption halpha
    (mpcGeneralTowerCAbsorptionSupply_of_atoms H)

end

end GQ2.Dyadic.Instances.MpcGeneralTowerAtoms

section AxiomPins

open GQ2.Dyadic.Instances.MpcGeneralTowerAtoms

#print axioms mpcGeneralTowerAtom
#print axioms mpcGeneralTowerAtom_mem
#print axioms mpcGeneralHeadSingleCHom
#print axioms MpcGeneralTowerAtomAbsorptionSupply
#print axioms mpcGeneralTowerAtoms_prod
#print axioms mpcGeneralTowerCAbsorptionSupply_of_atoms
#print axioms mpcPivShiftH_of_generalTowerAtoms

end AxiomPins

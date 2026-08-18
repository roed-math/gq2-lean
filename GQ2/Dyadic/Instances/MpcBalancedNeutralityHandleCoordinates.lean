/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedNeutralityHandleZModFour
import GQ2.Dyadic.Instances.MpcBalancedNeutralityLinearSystem

/-!
# Handle-coordinate normal forms for the neutral quotient

W224 computes the ordinary one-handle relative source modulo exact row-neutral classes as
two copies of `ZMod 4`.  This module turns that equivalence into a working coordinate API.
It supplies a relative class with any prescribed digit pair, proves that the coordinate map
is surjective with exactly the neutral range as kernel, and gives a unique deep-handle normal
form modulo that range.

The final two theorems replace the abstract equality of relative `C` quotient classes in the
CABD range criterion by equality of the two explicit `ZMod 4` coordinates.  No solution of
the remaining central-layer CABD equation is asserted.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedNeutralityHandleCoordinates

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Dyadic.Instances.MpcBalancedFiniteCore
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcBalancedCoordinateSpan
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCokernel
open GQ2.Dyadic.Instances.MpcBalancedNeutralitySpan
open GQ2.Dyadic.Instances.MpcBalancedNeutralitySourceQuotient
open GQ2.Dyadic.Instances.MpcBalancedNeutralityHandleRange
open GQ2.Dyadic.Instances.MpcBalancedNeutralityHandleZModFour
open GQ2.Dyadic.Instances.MpcBalancedNeutralityInteraction
open GQ2.Dyadic.Instances.MpcBalancedNeutralityEquation
open GQ2.Dyadic.Instances.MpcBalancedNeutralityLinearSystem

/-- The two `ZMod 4` coordinates of an ordinary relative source class modulo exact
row-neutral representatives. -/
noncomputable def oneHandleRelativeCCoordinates
    (k : ℕ) (hk : 3 ≤ k) :
    oneHandleRelativeLambdaImage (k - 1) (k + 1) →*
      Multiplicative (ZMod 4) × Multiplicative (ZMod 4) :=
  (oneHandleRelativeCModuloNeutralEquivZModFourSq k hk).toMonoidHom.comp
    (oneHandleRelativeCModuloNeutralMk k hk)

/-- A chosen ordinary relative class realizing a prescribed pair of deep handle digits. -/
noncomputable def oneHandleDeepRelativeClass
    (k : ℕ) (hk : 3 ≤ k)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :
    oneHandleRelativeLambdaImage (k - 1) (k + 1) := by
  have hz : deepUVHom k hk z ∈ (oneHandleRelativeUVLevel k).range := by
    rw [oneHandleRelativeUVLevel_range_eq_deepUVHom_range k hk]
    exact ⟨z, rfl⟩
  exact Classical.choose hz

theorem oneHandleRelativeUVLevel_deepRelativeClass
    (k : ℕ) (hk : 3 ≤ k)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :
    oneHandleRelativeUVLevel k (oneHandleDeepRelativeClass k hk z) =
      deepUVHom k hk z :=
  Classical.choose_spec (show deepUVHom k hk z ∈
    (oneHandleRelativeUVLevel k).range by
      rw [oneHandleRelativeUVLevel_range_eq_deepUVHom_range k hk]
      exact ⟨z, rfl⟩)

private theorem equivUVRange_mk
    (k : ℕ) (hk : 3 ≤ k)
    (x : oneHandleRelativeLambdaImage (k - 1) (k + 1)) :
    ((oneHandleRelativeCModuloNeutralEquivUVRange k hk
      (oneHandleRelativeCModuloNeutralMk k hk x) :
        (oneHandleRelativeUVLevel k).range) :
      Multiplicative (ZMod (2 ^ k)) × Multiplicative (ZMod (2 ^ k))) =
        oneHandleRelativeUVLevel k x := by
  rfl

@[simp] theorem oneHandleRelativeCCoordinates_deepRelativeClass
    (k : ℕ) (hk : 3 ≤ k)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :
    oneHandleRelativeCCoordinates k hk (oneHandleDeepRelativeClass k hk z) = z := by
  change (deepUVEquivRelativeRange k hk).symm
      (oneHandleRelativeCModuloNeutralEquivUVRange k hk
        (oneHandleRelativeCModuloNeutralMk k hk
          (oneHandleDeepRelativeClass k hk z))) = z
  apply (deepUVEquivRelativeRange k hk).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [equivUVRange_mk]
  exact oneHandleRelativeUVLevel_deepRelativeClass k hk z

theorem oneHandleRelativeCCoordinates_surjective
    (k : ℕ) (hk : 3 ≤ k) :
    Function.Surjective (oneHandleRelativeCCoordinates k hk) := by
  intro z
  exact ⟨oneHandleDeepRelativeClass k hk z,
    oneHandleRelativeCCoordinates_deepRelativeClass k hk z⟩

/-- Two ordinary relative classes define the same neutral quotient class exactly when their
two `ZMod 4` coordinates agree. -/
theorem oneHandleRelativeCModuloNeutralMk_eq_iff_coordinates
    (k : ℕ) (hk : 3 ≤ k)
    (x y : oneHandleRelativeLambdaImage (k - 1) (k + 1)) :
    oneHandleRelativeCModuloNeutralMk k hk x =
        oneHandleRelativeCModuloNeutralMk k hk y ↔
      oneHandleRelativeCCoordinates k hk x =
        oneHandleRelativeCCoordinates k hk y := by
  constructor
  · exact fun h => congrArg
      (oneHandleRelativeCModuloNeutralEquivZModFourSq k hk) h
  · intro h
    exact (oneHandleRelativeCModuloNeutralEquivZModFourSq k hk).injective h

/-- Every relative class has the prescribed deep-handle representative modulo exact
row-neutral classes. -/
theorem oneHandleRelativeCModuloNeutralMk_deepCoordinates
    (k : ℕ) (hk : 3 ≤ k)
    (x : oneHandleRelativeLambdaImage (k - 1) (k + 1)) :
    oneHandleRelativeCModuloNeutralMk k hk x =
      oneHandleRelativeCModuloNeutralMk k hk
        (oneHandleDeepRelativeClass k hk
          (oneHandleRelativeCCoordinates k hk x)) := by
  rw [oneHandleRelativeCModuloNeutralMk_eq_iff_coordinates,
    oneHandleRelativeCCoordinates_deepRelativeClass]

/-- The coordinate map has exactly the genuine row-neutral kernel. -/
theorem oneHandleRelativeCCoordinates_ker_eq_neutralRange
    (k : ℕ) (hk : 3 ≤ k) :
    (oneHandleRelativeCCoordinates k hk).ker =
      (oneHandleNeutralRelativeInclusion
        (k - 1) (k + 1) (by omega)).range := by
  letI := oneHandleRelativeLambdaImageIsMulCommutative k hk
  ext x
  change oneHandleRelativeCCoordinates k hk x = 1 ↔ _
  constructor
  · intro hx
    apply (QuotientGroup.eq_one_iff _).mp
    change oneHandleRelativeCModuloNeutralMk k hk x = 1
    have h := (oneHandleRelativeCModuloNeutralMk_eq_iff_coordinates
      k hk x 1).mpr
    simpa using h (by simpa using hx)
  · intro hx
    have hmk : oneHandleRelativeCModuloNeutralMk k hk x = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      exact hx
    have h := (oneHandleRelativeCModuloNeutralMk_eq_iff_coordinates
      k hk x 1).mp
    simpa using h (by simpa using hmk)

/-- Exact normal form: after removing its chosen deep-handle representative, a relative
class is genuinely row-neutral. -/
theorem relative_mul_deepCoordinates_inv_mem_neutralRange
    (k : ℕ) (hk : 3 ≤ k)
    (x : oneHandleRelativeLambdaImage (k - 1) (k + 1)) :
    x * (oneHandleDeepRelativeClass k hk
      (oneHandleRelativeCCoordinates k hk x))⁻¹ ∈
        (oneHandleNeutralRelativeInclusion
          (k - 1) (k + 1) (by omega)).range := by
  letI := oneHandleRelativeLambdaImageIsMulCommutative k hk
  apply (QuotientGroup.eq_one_iff _).mp
  change oneHandleRelativeCModuloNeutralMk k hk
    (x * (oneHandleDeepRelativeClass k hk
      (oneHandleRelativeCCoordinates k hk x))⁻¹) = 1
  rw [map_mul, map_inv,
    oneHandleRelativeCModuloNeutralMk_deepCoordinates k hk x,
    mul_inv_cancel]

/-- The two digits are the unique deep-handle normal form modulo row-neutral classes. -/
theorem existsUnique_deepRelativeClass_mod_neutral
    (k : ℕ) (hk : 3 ≤ k)
    (x : oneHandleRelativeLambdaImage (k - 1) (k + 1)) :
    ∃! z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
      x * (oneHandleDeepRelativeClass k hk z)⁻¹ ∈
        (oneHandleNeutralRelativeInclusion
          (k - 1) (k + 1) (by omega)).range := by
  refine ⟨oneHandleRelativeCCoordinates k hk x,
    relative_mul_deepCoordinates_inv_mem_neutralRange k hk x, ?_⟩
  intro z hz
  have hker : x * (oneHandleDeepRelativeClass k hk z)⁻¹ ∈
      (oneHandleRelativeCCoordinates k hk).ker := by
    rw [oneHandleRelativeCCoordinates_ker_eq_neutralRange k hk]
    exact hz
  have hm := MonoidHom.mem_ker.mp hker
  rw [map_mul, map_inv,
    oneHandleRelativeCCoordinates_deepRelativeClass] at hm
  exact (mul_inv_eq_one.mp hm).symm

/-- The combined CABD range condition has two explicit `ZMod 4` class equations. -/
theorem mem_oneHandleBalancedCABDSystem_range_iff_coordinates
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (x : oneHandleRelativeLambdaImage (k - 1) (k + 1)) :
    (1, oneHandleRelativeCModuloNeutralMk k hk x) ∈
        (oneHandleBalancedCABDSystem p k hk).range ↔
      ∃ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
        oneHandleRelativeCCoordinates k hk y =
            oneHandleRelativeCCoordinates k hk x ∧
          oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
            oneHandleBalancedCoreRelativeShiftA p k hk a *
              oneHandleBalancedCoreRelativeShiftB p k hk b *
                oneHandleBalancedCoreRelativeShiftD p k hk d := by
  rw [mem_oneHandleBalancedCABDSystem_range_iff]
  constructor
  · rintro ⟨y, a, b, d, hclass, heq⟩
    exact ⟨y, a, b, d,
      (oneHandleRelativeCModuloNeutralMk_eq_iff_coordinates k hk y x).mp hclass, heq⟩
  · rintro ⟨y, a, b, d, hcoords, heq⟩
    exact ⟨y, a, b, d,
      (oneHandleRelativeCModuloNeutralMk_eq_iff_coordinates k hk y x).mpr hcoords, heq⟩

/-- The remaining neutrality obstruction is an explicit CABD equation with the two prescribed
`ZMod 4` coordinates. -/
theorem neutralityObstruction_eq_one_iff_CABD_coordinates
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk)
    (x : oneHandleRelativeLambdaImage (k - 1) (k + 1))
    (hx : oneHandleBalancedCoreNeutralityClassHom p k hk x =
      oneHandleBalancedCoreNeutralityObstruction p hk hp hrel) :
    oneHandleBalancedCoreNeutralityObstruction p hk hp hrel = 1 ↔
      ∃ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
        oneHandleRelativeCCoordinates k hk y =
            oneHandleRelativeCCoordinates k hk x ∧
          oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
            oneHandleBalancedCoreRelativeShiftA p k hk a *
              oneHandleBalancedCoreRelativeShiftB p k hk b *
                oneHandleBalancedCoreRelativeShiftD p k hk d := by
  rw [neutralityObstruction_eq_one_iff_CABD p hk hp hrel x hx]
  constructor
  · rintro ⟨y, a, b, d, hclass, heq⟩
    exact ⟨y, a, b, d,
      (oneHandleRelativeCModuloNeutralMk_eq_iff_coordinates k hk y x).mp hclass, heq⟩
  · rintro ⟨y, a, b, d, hcoords, heq⟩
    exact ⟨y, a, b, d,
      (oneHandleRelativeCModuloNeutralMk_eq_iff_coordinates k hk y x).mpr hcoords, heq⟩

#print axioms oneHandleRelativeCCoordinates
#print axioms oneHandleDeepRelativeClass
#print axioms oneHandleRelativeUVLevel_deepRelativeClass
#print axioms oneHandleRelativeCCoordinates_deepRelativeClass
#print axioms oneHandleRelativeCCoordinates_surjective
#print axioms oneHandleRelativeCModuloNeutralMk_eq_iff_coordinates
#print axioms oneHandleRelativeCModuloNeutralMk_deepCoordinates
#print axioms oneHandleRelativeCCoordinates_ker_eq_neutralRange
#print axioms relative_mul_deepCoordinates_inv_mem_neutralRange
#print axioms existsUnique_deepRelativeClass_mod_neutral
#print axioms mem_oneHandleBalancedCABDSystem_range_iff_coordinates
#print axioms neutralityObstruction_eq_one_iff_CABD_coordinates

end
end GQ2.Dyadic.Instances.MpcBalancedNeutralityHandleCoordinates

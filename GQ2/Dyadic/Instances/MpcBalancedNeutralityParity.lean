/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedNeutralityCoordinateGenerators

/-!
# The mod-two neutrality criterion

The residual one-handle neutrality interaction lives in two explicit `ZMod 4` coordinates.
This module reduces both coordinates modulo two and proves the finite Nakayama step directly:
a subgroup of `(ZMod 4)^2` is the whole group exactly when its parity image is all of
`(ZMod 2)^2`.  Indeed, lifts of the two parity basis vectors square to the two generators of
the reduction kernel.

Consequently the two exact `ZMod 4` CABD equations from the preceding module are equivalent
to two parity CABD equations.  This is an exact reduction, not an assertion that those
relations hold; their construction remains the graded interaction problem.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedNeutralityParity

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
open GQ2.Dyadic.Instances.MpcBalancedNeutralityInteraction
open GQ2.Dyadic.Instances.MpcBalancedNeutralityEquation
open GQ2.Dyadic.Instances.MpcBalancedNeutralityHandleCoordinates
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCoordinateCokernel
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCoordinateGenerators

def zmodFourParity : Multiplicative (ZMod 4) →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative
    (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)).toAddMonoidHom

def zmodFourParityAdd (a : ZMod 4) : ZMod 2 := (a.val : ZMod 2)

theorem zmodFourParityAdd_eq_castHom (a : ZMod 4) :
    zmodFourParityAdd a =
      ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) a := by
  rw [zmodFourParityAdd, ZMod.castHom_apply, ZMod.natCast_val]

def coordinateParity :
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) →*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
  MonoidHom.prodMap zmodFourParity zmodFourParity

def coordinateParityU :
    Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
  (ofAdd 1, 1)

def coordinateParityV :
    Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
  (1, ofAdd 1)

@[simp] theorem coordinateParity_U :
    coordinateParity oneHandleRelativeCoordinateU = coordinateParityU := by
  rfl

@[simp] theorem coordinateParity_V :
    coordinateParity oneHandleRelativeCoordinateV = coordinateParityV := by
  rfl

theorem zmodFourParity_eq_zero_iff (a : ZMod 4) :
    ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) a = 0 ↔
      a = 0 ∨ a = 2 := by
  rw [← zmodFourParityAdd_eq_castHom]
  revert a
  decide

theorem zmodFourParity_eq_one_iff (a : ZMod 4) :
    ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) a = 1 ↔
      a = 1 ∨ a = 3 := by
  rw [← zmodFourParityAdd_eq_castHom]
  revert a
  decide

theorem square_eq_U_sq_of_parity_U
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
    (hz : coordinateParity z = coordinateParityU) :
    z ^ 2 = oneHandleRelativeCoordinateU ^ 2 := by
  rcases z with ⟨u, v⟩
  change (u ^ 2, v ^ 2) = _
  apply Prod.ext
  · change u ^ 2 = (ofAdd (1 : ZMod 4)) ^ 2
    rw [← ofAdd_toAdd u, ← ofAdd_nsmul, ← ofAdd_nsmul]
    apply congrArg ofAdd
    have hu := congrArg (fun x => toAdd x.1) hz
    change ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) (toAdd u) = 1 at hu
    rcases (zmodFourParity_eq_one_iff (toAdd u)).mp hu with hu | hu
    · rw [hu]
    · rw [hu]
      decide
  · change v ^ 2 = (1 : Multiplicative (ZMod 4)) ^ 2
    rw [← ofAdd_toAdd v, ← ofAdd_nsmul]
    change ofAdd (2 • toAdd v) = ofAdd (0 : ZMod 4)
    apply congrArg ofAdd
    have hv := congrArg (fun x => toAdd x.2) hz
    change ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) (toAdd v) = 0 at hv
    rcases (zmodFourParity_eq_zero_iff (toAdd v)).mp hv with hv | hv
    · rw [hv]
      decide
    · rw [hv]
      decide

theorem square_eq_V_sq_of_parity_V
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
    (hz : coordinateParity z = coordinateParityV) :
    z ^ 2 = oneHandleRelativeCoordinateV ^ 2 := by
  rcases z with ⟨u, v⟩
  change (u ^ 2, v ^ 2) = _
  apply Prod.ext
  · change u ^ 2 = (1 : Multiplicative (ZMod 4)) ^ 2
    rw [← ofAdd_toAdd u, ← ofAdd_nsmul]
    change ofAdd (2 • toAdd u) = ofAdd (0 : ZMod 4)
    apply congrArg ofAdd
    have hu := congrArg (fun x => toAdd x.1) hz
    change ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) (toAdd u) = 0 at hu
    rcases (zmodFourParity_eq_zero_iff (toAdd u)).mp hu with hu | hu
    · rw [hu]
      decide
    · rw [hu]
      decide
  · change v ^ 2 = (ofAdd (1 : ZMod 4)) ^ 2
    rw [← ofAdd_toAdd v, ← ofAdd_nsmul, ← ofAdd_nsmul]
    apply congrArg ofAdd
    have hv := congrArg (fun x => toAdd x.2) hz
    change ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) (toAdd v) = 1 at hv
    rcases (zmodFourParity_eq_one_iff (toAdd v)).mp hv with hv | hv
    · rw [hv]
    · rw [hv]
      decide

theorem coordinate_mem_of_parity_one_of_squares
    (H : Subgroup (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
    (hU2 : oneHandleRelativeCoordinateU ^ 2 ∈ H)
    (hV2 : oneHandleRelativeCoordinateV ^ 2 ∈ H)
    {z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)}
    (hz : coordinateParity z = 1) : z ∈ H := by
  rcases z with ⟨u, v⟩
  have hu := congrArg (fun x => toAdd x.1) hz
  have hv := congrArg (fun x => toAdd x.2) hz
  change ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) (toAdd u) = 0 at hu
  change ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) (toAdd v) = 0 at hv
  rcases (zmodFourParity_eq_zero_iff (toAdd u)).mp hu with hu | hu <;>
    rcases (zmodFourParity_eq_zero_iff (toAdd v)).mp hv with hv | hv
  · have hz : (u, v) = 1 := by
      apply Prod.ext
      · rw [← ofAdd_toAdd u, hu]
        rfl
      · rw [← ofAdd_toAdd v, hv]
        rfl
    rw [hz]
    exact H.one_mem
  · have hz : (u, v) = oneHandleRelativeCoordinateV ^ 2 := by
      apply Prod.ext
      · rw [← ofAdd_toAdd u, hu]
        rfl
      · rw [← ofAdd_toAdd v, hv]
        rfl
    rw [hz]
    exact hV2
  · have hz : (u, v) = oneHandleRelativeCoordinateU ^ 2 := by
      apply Prod.ext
      · rw [← ofAdd_toAdd u, hu]
        rfl
      · rw [← ofAdd_toAdd v, hv]
        rfl
    rw [hz]
    exact hU2
  · have hz : (u, v) = oneHandleRelativeCoordinateU ^ 2 *
        oneHandleRelativeCoordinateV ^ 2 := by
      apply Prod.ext
      · rw [← ofAdd_toAdd u, hu]
        rfl
      · rw [← ofAdd_toAdd v, hv]
        rfl
    rw [hz]
    exact H.mul_mem hU2 hV2

theorem coordinateU_mem_of_parity
    (H : Subgroup (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
    {x y : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)}
    (hx : x ∈ H) (hy : y ∈ H)
    (hxp : coordinateParity x = coordinateParityU)
    (hyp : coordinateParity y = coordinateParityV) :
    oneHandleRelativeCoordinateU ∈ H := by
  have hU2 : oneHandleRelativeCoordinateU ^ 2 ∈ H := by
    rw [← square_eq_U_sq_of_parity_U x hxp]
    exact H.pow_mem hx 2
  have hV2 : oneHandleRelativeCoordinateV ^ 2 ∈ H := by
    rw [← square_eq_V_sq_of_parity_V y hyp]
    exact H.pow_mem hy 2
  have hzpar : coordinateParity (x * oneHandleRelativeCoordinateU⁻¹) = 1 := by
    rw [map_mul, map_inv, hxp, coordinateParity_U, mul_inv_cancel]
  have hzmem : x * oneHandleRelativeCoordinateU⁻¹ ∈ H :=
    coordinate_mem_of_parity_one_of_squares H hU2 hV2 hzpar
  have heq : x * (x * oneHandleRelativeCoordinateU⁻¹)⁻¹ =
      oneHandleRelativeCoordinateU := by
    simp [mul_inv_rev]
  rw [← heq]
  exact H.mul_mem hx (H.inv_mem hzmem)

theorem coordinateV_mem_of_parity
    (H : Subgroup (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
    {x y : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)}
    (hx : x ∈ H) (hy : y ∈ H)
    (hxp : coordinateParity x = coordinateParityU)
    (hyp : coordinateParity y = coordinateParityV) :
    oneHandleRelativeCoordinateV ∈ H := by
  have hU2 : oneHandleRelativeCoordinateU ^ 2 ∈ H := by
    rw [← square_eq_U_sq_of_parity_U x hxp]
    exact H.pow_mem hx 2
  have hV2 : oneHandleRelativeCoordinateV ^ 2 ∈ H := by
    rw [← square_eq_V_sq_of_parity_V y hyp]
    exact H.pow_mem hy 2
  have hzpar : coordinateParity (y * oneHandleRelativeCoordinateV⁻¹) = 1 := by
    rw [map_mul, map_inv, hyp, coordinateParity_V, mul_inv_cancel]
  have hzmem : y * oneHandleRelativeCoordinateV⁻¹ ∈ H :=
    coordinate_mem_of_parity_one_of_squares H hU2 hV2 hzpar
  have heq : y * (y * oneHandleRelativeCoordinateV⁻¹)⁻¹ =
      oneHandleRelativeCoordinateV := by
    simp [mul_inv_rev]
  rw [← heq]
  exact H.mul_mem hy (H.inv_mem hzmem)

theorem zmodFourParity_surjective : Function.Surjective zmodFourParity := by
  intro u
  refine ⟨ofAdd (((toAdd u).val : ℕ) : ZMod 4), ?_⟩
  apply congrArg ofAdd
  change ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)
      (((toAdd u).val : ℕ) : ZMod 4) = toAdd u
  rw [← zmodFourParityAdd_eq_castHom]
  generalize toAdd u = a
  revert a
  decide

theorem coordinateParity_surjective : Function.Surjective coordinateParity := by
  rintro ⟨u, v⟩
  obtain ⟨u', hu'⟩ := zmodFourParity_surjective u
  obtain ⟨v', hv'⟩ := zmodFourParity_surjective v
  exact ⟨(u', v'), Prod.ext hu' hv'⟩

theorem coordinateSubgroup_map_parity_eq_top_iff
    (H : Subgroup (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :
    Subgroup.map coordinateParity H = ⊤ ↔ H = ⊤ := by
  constructor
  · intro hmap
    have hUp : coordinateParityU ∈ Subgroup.map coordinateParity H := by
      rw [hmap]
      exact Subgroup.mem_top _
    have hVp : coordinateParityV ∈ Subgroup.map coordinateParity H := by
      rw [hmap]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_map] at hUp hVp
    obtain ⟨x, hx, hxp⟩ := hUp
    obtain ⟨y, hy, hyp⟩ := hVp
    exact (coordinateSubgroup_eq_top_iff_generators H).mpr
      ⟨coordinateU_mem_of_parity H hx hy hxp hyp,
        coordinateV_mem_of_parity H hx hy hxp hyp⟩
  · intro hH
    subst H
    exact Subgroup.map_top_of_surjective coordinateParity coordinateParity_surjective

theorem parityCoordinates_eq_generators
    (z : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    z = coordinateParityU ^ (toAdd z.1).val *
      coordinateParityV ^ (toAdd z.2).val := by
  rcases z with ⟨u, v⟩
  unfold coordinateParityU coordinateParityV
  apply Prod.ext
  · change u = ofAdd (1 : ZMod 2) ^ (toAdd u).val * 1 ^ (toAdd v).val
    rw [one_pow, mul_one, ← ofAdd_nsmul]
    rw [← ofAdd_toAdd u]
    apply congrArg ofAdd
    rw [nsmul_eq_mul, mul_one]
    exact (ZMod.natCast_zmod_val (toAdd u)).symm
  · change v = 1 ^ (toAdd u).val * ofAdd (1 : ZMod 2) ^ (toAdd v).val
    rw [one_pow, one_mul, ← ofAdd_nsmul]
    rw [← ofAdd_toAdd v]
    apply congrArg ofAdd
    rw [nsmul_eq_mul, mul_one]
    exact (ZMod.natCast_zmod_val (toAdd v)).symm

theorem parityCoordinateSubgroup_eq_top_iff_generators
    (H : Subgroup (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    H = ⊤ ↔ coordinateParityU ∈ H ∧ coordinateParityV ∈ H := by
  constructor
  · intro h
    rw [h]
    exact ⟨Subgroup.mem_top _, Subgroup.mem_top _⟩
  · rintro ⟨hU, hV⟩
    apply top_unique
    intro z _
    rw [parityCoordinates_eq_generators z]
    exact H.mul_mem (H.pow_mem hU _) (H.pow_mem hV _)

noncomputable def oneHandleBalancedCoreNeutralityParityRow
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    oneHandleBalancedCoreNeutralityInteractionSource p k hk →*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
  coordinateParity.comp
    (oneHandleBalancedCoreNeutralityCoordinateRow p k hk)

theorem oneHandleBalancedCoreNeutralityParityRow_range_eq_map
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    (oneHandleBalancedCoreNeutralityParityRow p k hk).range =
      Subgroup.map coordinateParity
        (oneHandleBalancedCoreNeutralityCoordinateRow p k hk).range := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rw [oneHandleBalancedCoreNeutralityParityRow, MonoidHom.comp_apply]
    exact ⟨oneHandleBalancedCoreNeutralityCoordinateRow p k hk x,
      ⟨x, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

theorem oneHandleBalancedCoreNeutralityParityRow_range_eq_top_iff
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    (oneHandleBalancedCoreNeutralityParityRow p k hk).range = ⊤ ↔
      (oneHandleBalancedCoreNeutralityCoordinateRow p k hk).range = ⊤ := by
  rw [oneHandleBalancedCoreNeutralityParityRow_range_eq_map,
    coordinateSubgroup_map_parity_eq_top_iff]

theorem mem_oneHandleBalancedCoreNeutralityParityRow_range_iff
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (z : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    z ∈ (oneHandleBalancedCoreNeutralityParityRow p k hk).range ↔
      ∃ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
        coordinateParity (oneHandleRelativeCCoordinates k hk y) = z ∧
          oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
            oneHandleBalancedCoreRelativeShiftA p k hk a *
              oneHandleBalancedCoreRelativeShiftB p k hk b *
                oneHandleBalancedCoreRelativeShiftD p k hk d := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨a, b, d, heq⟩ :=
      (mem_oneHandleBalancedCoreNeutralityInteractionSource_iff
        p k hk y.1).mp y.2
    exact ⟨y.1, a, b, d, hy, heq⟩
  · rintro ⟨y, a, b, d, hy, heq⟩
    have hymem : y ∈ oneHandleBalancedCoreNeutralityInteractionSource p k hk :=
      (mem_oneHandleBalancedCoreNeutralityInteractionSource_iff p k hk y).mpr
        ⟨a, b, d, heq⟩
    exact ⟨⟨y, hymem⟩, hy⟩

theorem oneHandleBalancedCoreNeutralityParityRow_range_eq_top_iff_basis
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    (oneHandleBalancedCoreNeutralityParityRow p k hk).range = ⊤ ↔
      (∃ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
        coordinateParity (oneHandleRelativeCCoordinates k hk y) =
            coordinateParityU ∧
          oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
            oneHandleBalancedCoreRelativeShiftA p k hk a *
              oneHandleBalancedCoreRelativeShiftB p k hk b *
                oneHandleBalancedCoreRelativeShiftD p k hk d) ∧
      (∃ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
        coordinateParity (oneHandleRelativeCCoordinates k hk y) =
            coordinateParityV ∧
          oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
            oneHandleBalancedCoreRelativeShiftA p k hk a *
              oneHandleBalancedCoreRelativeShiftB p k hk b *
                oneHandleBalancedCoreRelativeShiftD p k hk d) := by
  rw [parityCoordinateSubgroup_eq_top_iff_generators,
    mem_oneHandleBalancedCoreNeutralityParityRow_range_iff,
    mem_oneHandleBalancedCoreNeutralityParityRow_range_iff]

def OneHandleBalancedCoreNeutralityParitySupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (p : OneHandleBalancedPoint)
    (_hp : p ∈ oneHandleBalancedSet Psi0 k),
      (oneHandleBalancedCoreNeutralityParityRow p k hk).range = ⊤

theorem paritySupply_iff_coordinateGeneratorSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) :
    OneHandleBalancedCoreNeutralityParitySupply Psi0 ↔
      OneHandleBalancedCoreNeutralityCoordinateGeneratorSupply Psi0 := by
  rw [coordinateGeneratorSupply_iff_range_eq_top]
  exact forall_congr' fun k => forall_congr' fun hk => forall_congr' fun p =>
    forall_congr' fun _hp =>
      oneHandleBalancedCoreNeutralityParityRow_range_eq_top_iff p k hk

theorem mpcPivShiftH_two_one_of_balancedRelative_and_parity
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hchi0 : ∀ x, chiM 2 0 (Psi0 x) = chiM 2 0 x)
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0)))
    (Hrel : OneHandleBalancedCoreRelativeCoordinateSpanSupply Psi0)
    (Hpar : OneHandleBalancedCoreNeutralityParitySupply Psi0) :
    MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_balancedRelative_and_coordinateGenerators
    Psi0 hchi0 hrow Hrel
      ((paritySupply_iff_coordinateGeneratorSupply Psi0).mp Hpar)

#print axioms zmodFourParity
#print axioms zmodFourParityAdd
#print axioms zmodFourParityAdd_eq_castHom
#print axioms coordinateParity
#print axioms coordinateParityU
#print axioms coordinateParityV
#print axioms coordinateParity_U
#print axioms coordinateParity_V
#print axioms zmodFourParity_eq_zero_iff
#print axioms zmodFourParity_eq_one_iff
#print axioms square_eq_U_sq_of_parity_U
#print axioms square_eq_V_sq_of_parity_V
#print axioms coordinate_mem_of_parity_one_of_squares
#print axioms coordinateU_mem_of_parity
#print axioms coordinateV_mem_of_parity
#print axioms zmodFourParity_surjective
#print axioms coordinateParity_surjective
#print axioms coordinateSubgroup_map_parity_eq_top_iff
#print axioms parityCoordinates_eq_generators
#print axioms parityCoordinateSubgroup_eq_top_iff_generators
#print axioms oneHandleBalancedCoreNeutralityParityRow
#print axioms oneHandleBalancedCoreNeutralityParityRow_range_eq_map
#print axioms oneHandleBalancedCoreNeutralityParityRow_range_eq_top_iff
#print axioms mem_oneHandleBalancedCoreNeutralityParityRow_range_iff
#print axioms oneHandleBalancedCoreNeutralityParityRow_range_eq_top_iff_basis
#print axioms OneHandleBalancedCoreNeutralityParitySupply
#print axioms paritySupply_iff_coordinateGeneratorSupply
#print axioms mpcPivShiftH_two_one_of_balancedRelative_and_parity

end
end GQ2.Dyadic.Instances.MpcBalancedNeutralityParity

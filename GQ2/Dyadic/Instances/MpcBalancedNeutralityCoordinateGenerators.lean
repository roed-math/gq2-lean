import GQ2.Dyadic.Instances.MpcBalancedNeutralityCoordinateCokernel

namespace GQ2.Dyadic.Instances.MpcBalancedNeutralityCoordinateGenerators

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

/-- The first standard generator of the two deep handle digits. -/
def oneHandleRelativeCoordinateU :
    Multiplicative (ZMod 4) × Multiplicative (ZMod 4) :=
  (ofAdd 1, 1)

/-- The second standard generator of the two deep handle digits. -/
def oneHandleRelativeCoordinateV :
    Multiplicative (ZMod 4) × Multiplicative (ZMod 4) :=
  (1, ofAdd 1)

/-- Every digit pair is a product of powers of the two standard generators. -/
theorem oneHandleRelativeCoordinates_eq_generators
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :
  z = oneHandleRelativeCoordinateU ^ (toAdd z.1).val *
      oneHandleRelativeCoordinateV ^ (toAdd z.2).val := by
  rcases z with ⟨u, v⟩
  unfold oneHandleRelativeCoordinateU oneHandleRelativeCoordinateV
  apply Prod.ext
  · change u = ofAdd (1 : ZMod 4) ^ (toAdd u).val * 1 ^ (toAdd v).val
    rw [one_pow, mul_one, ← ofAdd_nsmul]
    rw [← ofAdd_toAdd u]
    apply congrArg ofAdd
    rw [nsmul_eq_mul, mul_one]
    exact (ZMod.natCast_zmod_val (toAdd u)).symm
  · change v = 1 ^ (toAdd u).val * ofAdd (1 : ZMod 4) ^ (toAdd v).val
    rw [one_pow, one_mul, ← ofAdd_nsmul]
    rw [← ofAdd_toAdd v]
    apply congrArg ofAdd
    rw [nsmul_eq_mul, mul_one]
    exact (ZMod.natCast_zmod_val (toAdd v)).symm

/-- A subgroup of the digit plane is all of it exactly when it contains the two standard
generators. -/
theorem coordinateSubgroup_eq_top_iff_generators
    (H : Subgroup
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :
    H = ⊤ ↔
      oneHandleRelativeCoordinateU ∈ H ∧
        oneHandleRelativeCoordinateV ∈ H := by
  constructor
  · intro h
    rw [h]
    exact ⟨Subgroup.mem_top _, Subgroup.mem_top _⟩
  · rintro ⟨hU, hV⟩
    apply top_unique
    intro z _
    rw [oneHandleRelativeCoordinates_eq_generators z]
    exact H.mul_mem (H.pow_mem hU _) (H.pow_mem hV _)

/-! ## The two-equation criterion -/

/-- The interaction range fills the digit plane exactly when the literal CABD equation has
solutions with the two standard digit pairs. -/
theorem oneHandleBalancedCoreNeutralityCoordinateRow_range_eq_top_iff
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    (oneHandleBalancedCoreNeutralityCoordinateRow p k hk).range = ⊤ ↔
      (∃ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
        oneHandleRelativeCCoordinates k hk y = oneHandleRelativeCoordinateU ∧
          oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
            oneHandleBalancedCoreRelativeShiftA p k hk a *
              oneHandleBalancedCoreRelativeShiftB p k hk b *
                oneHandleBalancedCoreRelativeShiftD p k hk d) ∧
      (∃ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
        oneHandleRelativeCCoordinates k hk y = oneHandleRelativeCoordinateV ∧
          oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
            oneHandleBalancedCoreRelativeShiftA p k hk a *
              oneHandleBalancedCoreRelativeShiftB p k hk b *
                oneHandleBalancedCoreRelativeShiftD p k hk d) := by
  rw [coordinateSubgroup_eq_top_iff_generators,
    mem_oneHandleBalancedCoreNeutralityCoordinateRow_range_iff,
    mem_oneHandleBalancedCoreNeutralityCoordinateRow_range_iff]

/-- Uniform solvability of the two standard coordinate equations. -/
def OneHandleBalancedCoreNeutralityCoordinateGeneratorSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (p : OneHandleBalancedPoint)
    (_hp : p ∈ oneHandleBalancedSet Psi0 k),
      oneHandleRelativeCoordinateU ∈
          (oneHandleBalancedCoreNeutralityCoordinateRow p k hk).range ∧
        oneHandleRelativeCoordinateV ∈
          (oneHandleBalancedCoreNeutralityCoordinateRow p k hk).range

/-- The two standard coordinate equations are equivalent to surjectivity of every
coordinate interaction row. -/
theorem coordinateGeneratorSupply_iff_range_eq_top
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) :
    OneHandleBalancedCoreNeutralityCoordinateGeneratorSupply Psi0 ↔
      ∀ (k : ℕ) (hk : 3 ≤ k) (p : OneHandleBalancedPoint)
        (_hp : p ∈ oneHandleBalancedSet Psi0 k),
          (oneHandleBalancedCoreNeutralityCoordinateRow p k hk).range = ⊤ := by
  constructor
  · intro H k hk p hp
    exact (coordinateSubgroup_eq_top_iff_generators _).mpr (H k hk p hp)
  · intro H k hk p hp
    exact (coordinateSubgroup_eq_top_iff_generators _).mp (H k hk p hp)

/-- Filling the two coordinate generators kills every target-specific neutrality
obstruction. -/
theorem neutralityObstructionVanishing_of_coordinateGeneratorSupply
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (H : OneHandleBalancedCoreNeutralityCoordinateGeneratorSupply Psi0) :
    OneHandleBalancedCoreNeutralityObstructionVanishing Psi0 := by
  intro k hk p hp hrel
  obtain ⟨x, hx⟩ := exists_relativeC_class_eq_neutralityObstruction p hk hp hrel
  apply (neutralityObstruction_eq_one_iff_coordinateInteraction
    p hk hp hrel x hx).mpr
  have htop := (coordinateGeneratorSupply_iff_range_eq_top Psi0).mp H k hk p hp
  rw [htop]
  exact Subgroup.mem_top _

/-- The ordinary-relative coverage problem together with only the two standard coordinate
equations implies the one-handle pivot. -/
theorem mpcPivShiftH_two_one_of_balancedRelative_and_coordinateGenerators
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hchi0 : ∀ x, chiM 2 0 (Psi0 x) = chiM 2 0 x)
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0)))
    (Hrel : OneHandleBalancedCoreRelativeCoordinateSpanSupply Psi0)
    (Hcoord : OneHandleBalancedCoreNeutralityCoordinateGeneratorSupply Psi0) :
    MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_balancedRelative_and_neutrality Psi0 hchi0 hrow Hrel
    (neutralityObstructionVanishing_of_coordinateGeneratorSupply Hcoord)

#print axioms oneHandleRelativeCoordinateU
#print axioms oneHandleRelativeCoordinateV
#print axioms oneHandleRelativeCoordinates_eq_generators
#print axioms coordinateSubgroup_eq_top_iff_generators
#print axioms oneHandleBalancedCoreNeutralityCoordinateRow_range_eq_top_iff
#print axioms OneHandleBalancedCoreNeutralityCoordinateGeneratorSupply
#print axioms coordinateGeneratorSupply_iff_range_eq_top
#print axioms neutralityObstructionVanishing_of_coordinateGeneratorSupply
#print axioms mpcPivShiftH_two_one_of_balancedRelative_and_coordinateGenerators

end
end GQ2.Dyadic.Instances.MpcBalancedNeutralityCoordinateGenerators

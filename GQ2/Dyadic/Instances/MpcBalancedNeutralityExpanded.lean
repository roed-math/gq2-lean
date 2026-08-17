/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedNeutralityEquation

/-!
# Expanded square-and-commutator form of the neutral-C boundary

W216 leaves one literal equality among four finite shift rows.  This file unfolds those rows
into the square and commutators appearing in the balanced relator derivative.  The resulting
statement is ready for a graded-Lie calculation and contains no span or cokernel membership.

No solution is asserted.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedNeutralityExpanded

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
open GQ2.Roe.Labute

/-! ## The expanded finite row equation -/

/-- The abstract `C = A * B * D` row equality is exactly the displayed square-and-four-
commutator identity in `Q_(k+1)`. -/
theorem balancedCABD_eq_iff_expanded
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1)) :
    oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
        oneHandleBalancedCoreRelativeShiftA p k hk a *
          oneHandleBalancedCoreRelativeShiftB p k hk b *
            oneHandleBalancedCoreRelativeShiftD p k hk d ↔
      commP y.1 (levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p 3)) =
        (a.1 ^ 2 *
          commP a.1 (levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p 0)) *
          commP a.1 (levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p 1))) *
        commP b.1 (levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p 0)) *
        commP d.1 (levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p 2)) := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    simpa only [oneHandleBalancedCoreRelativeShiftCRelaxed_apply,
      oneHandleBalancedCoreRelativeShiftA_apply,
      oneHandleBalancedCoreRelativeShiftB_apply,
      oneHandleBalancedCoreRelativeShiftD_apply, Subgroup.coe_mul] using hv
  · intro h
    apply Subtype.ext
    simpa only [oneHandleBalancedCoreRelativeShiftCRelaxed_apply,
      oneHandleBalancedCoreRelativeShiftA_apply,
      oneHandleBalancedCoreRelativeShiftB_apply,
      oneHandleBalancedCoreRelativeShiftD_apply, Subgroup.coe_mul] using h

/-- Target obstruction vanishing, with every finite shift row fully expanded. -/
theorem neutralityObstruction_eq_one_iff_expanded_CABD
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
        oneHandleRelativeCModuloNeutralMk k hk y =
          oneHandleRelativeCModuloNeutralMk k hk x ∧
        commP y.1 (levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p 3)) =
          (a.1 ^ 2 *
            commP a.1
              (levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p 0)) *
            commP a.1
              (levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p 1))) *
          commP b.1
            (levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p 0)) *
          commP d.1
            (levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p 2)) := by
  rw [neutralityObstruction_eq_one_iff_CABD p hk hp hrel x hx]
  constructor
  · rintro ⟨y, a, b, d, hy, heq⟩
    exact ⟨y, a, b, d, hy, (balancedCABD_eq_iff_expanded p k hk y a b d).mp heq⟩
  · rintro ⟨y, a, b, d, hy, heq⟩
    exact ⟨y, a, b, d, hy, (balancedCABD_eq_iff_expanded p k hk y a b d).mpr heq⟩

#print axioms balancedCABD_eq_iff_expanded
#print axioms neutralityObstruction_eq_one_iff_expanded_CABD

end
end GQ2.Dyadic.Instances.MpcBalancedNeutralityExpanded

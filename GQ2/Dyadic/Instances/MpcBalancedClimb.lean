/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcCupAdaptedSeed

/-!
# The exact balanced one-handle climb boundary

W202 supplies a balanced point through depth three.  The remaining climb cannot use either
of the fixed-`C`, one-slot bracket-surjectivity predicates: both have explicit counterexamples.
This module instead records the honest multi-slot correction interface.

A correction moves all five variables of a balanced point inside the handle-forgetting kernel
and at depth `k - 1`.  Its `C` move is exactly abelian-neutral, as required to preserve the fixed
universal row `C_std + 2 B_std`, and its only nonlinear clause is that the defect lies one rung
deeper.  The four prescribed fibres, the correction fibre, the universal row, and mod-two
independence are then automatic.  Thus a correction advances `oneHandleBalancedSet` by one.

Uniform availability of these corrections from depth three gives every finite balanced stage.
The existing compactness theorem then produces the exact absorber and `MpcPivShiftH 2 1`.
The module does not assert the correction supply: its nonlinear `nextDefect` field is precisely
the residual-specific, multi-slot graded reachability statement still to prove.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedClimb

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedRowLift
open GQ2.Dyadic.Instances.MpcCupAdaptedSeed
open GQ2.Roe.Labute

/-- Coordinatewise multiplication of the five variables in a balanced point. -/
def oneHandleBalancedModify (p e : OneHandleBalancedPoint) : OneHandleBalancedPoint :=
  (balancedA p * balancedA e,
    balancedB p * balancedB e,
    balancedC p * balancedC e,
    balancedD p * balancedD e,
    balancedZ p * balancedZ e)

@[simp] theorem balancedA_modify (p e : OneHandleBalancedPoint) :
    balancedA (oneHandleBalancedModify p e) = balancedA p * balancedA e := rfl

@[simp] theorem balancedB_modify (p e : OneHandleBalancedPoint) :
    balancedB (oneHandleBalancedModify p e) = balancedB p * balancedB e := rfl

@[simp] theorem balancedC_modify (p e : OneHandleBalancedPoint) :
    balancedC (oneHandleBalancedModify p e) = balancedC p * balancedC e := rfl

@[simp] theorem balancedD_modify (p e : OneHandleBalancedPoint) :
    balancedD (oneHandleBalancedModify p e) = balancedD p * balancedD e := rfl

@[simp] theorem balancedZ_modify (p e : OneHandleBalancedPoint) :
    balancedZ (oneHandleBalancedModify p e) = balancedZ p * balancedZ e := rfl

/-- A genuine depth-`k - 1`, five-slot balanced correction.  All linear invariants are stated
separately from the single nonlinear next-defect clause. -/
structure OneHandleBalancedCorrection (p : OneHandleBalancedPoint) (k : ℕ) where
  /-- The five coordinatewise correction factors. -/
  factors : OneHandleBalancedPoint
  /-- Every factor starts at the current two-central depth. -/
  depthA : balancedA factors ∈ twoCentralSeries (DM 2 1) (k - 1)
  depthB : balancedB factors ∈ twoCentralSeries (DM 2 1) (k - 1)
  depthC : balancedC factors ∈ twoCentralSeries (DM 2 1) (k - 1)
  depthD : balancedD factors ∈ twoCentralSeries (DM 2 1) (k - 1)
  depthZ : balancedZ factors ∈ twoCentralSeries (DM 2 1) (k - 1)
  /-- Every factor is invisible after forgetting the standard handle. -/
  forgetA : dmForgetHandles 2 1 (balancedA factors) = 1
  forgetB : dmForgetHandles 2 1 (balancedB factors) = 1
  forgetC : dmForgetHandles 2 1 (balancedC factors) = 1
  forgetD : dmForgetHandles 2 1 (balancedD factors) = 1
  forgetZ : dmForgetHandles 2 1 (balancedZ factors) = 1
  /-- The `C` correction is invisible to every `ℤ₂`-valued character, hence preserves the
  fixed universal `C_std + 2 B_std` row. -/
  row : ∀ f : ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]),
    toAdd (f (balancedC factors)) = 0
  /-- The corrected nonlinear defect vanishes one rung deeper. -/
  nextDefect :
    oneHandleDDefect
        (balancedA (oneHandleBalancedModify p factors))
        (balancedB (oneHandleBalancedModify p factors))
        (balancedC (oneHandleBalancedModify p factors))
        (balancedD (oneHandleBalancedModify p factors))
        (balancedZ (oneHandleBalancedModify p factors)) ∈
      twoCentralSeries (DM 2 1) (k + 1)

/-- The exact remaining all-rung boundary: every balanced point at depth at least three admits
a multi-slot correction to the next depth. -/
def OneHandleBalancedClimbSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ p ∈ oneHandleBalancedSet Psi0 k,
    Nonempty (OneHandleBalancedCorrection p k)

/-- A depth-`k - 1` balanced correction is invisible on the entire corrected marking modulo
`λ_(k-1)`.  This is the stage-compatibility check behind the successor interface. -/
theorem levelMk_balancedCorrectedMark_modify
    {p : OneHandleBalancedPoint} {k : ℕ}
    (E : OneHandleBalancedCorrection p k) (i : Fin (coreRank 1)) :
    levelMk (DM 2 1) (k - 1)
        (balancedCorrectedMark (oneHandleBalancedModify p E.factors) i) =
      levelMk (DM 2 1) (k - 1) (balancedCorrectedMark p i) := by
  have ha := E.depthA
  have hb := E.depthB
  have hc := E.depthC
  have hd := E.depthD
  have hz := E.depthZ
  rw [lim_mem_twoCentralSeries_iff_levelMk] at ha hb hc hd hz
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · simp only [balancedCorrectedMark, standardHandleMark_zero, balancedA_modify,
      map_mul, ha, mul_one]
  · simp only [balancedCorrectedMark, standardHandleMark_one, balancedB_modify,
      map_mul, hb, mul_one]
  · simp only [balancedCorrectedMark, standardHandleMark_two, balancedC_modify,
      map_mul, hc, mul_one]
  · simp only [balancedCorrectedMark, standardHandleMark_three, balancedZ_modify,
      balancedD_modify, map_mul, hz, hd, mul_one]
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simp only [balancedCorrectedMark, mHandleIdx_coordU,
        standardHandleMark_handleU]
    · simp only [balancedCorrectedMark, mHandleIdx_coordV,
        standardHandleMark_handleV]

/-- A multi-slot correction advances one balanced finite stage. -/
theorem oneHandleBalancedSet_succ_of_correction
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    {k : ℕ} {p : OneHandleBalancedPoint}
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (E : OneHandleBalancedCorrection p k) :
    oneHandleBalancedModify p E.factors ∈ oneHandleBalancedSet Psi0 (k + 1) := by
  rcases hp with ⟨ha, hb, hc, hd, hz, _, hrow, -⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, E.nextDefect⟩
  · rw [balancedA_modify, map_mul, E.forgetA, mul_one, ha]
  · rw [balancedB_modify, map_mul, E.forgetB, mul_one, hb]
  · rw [balancedC_modify, map_mul, E.forgetC, mul_one, hc]
  · rw [balancedD_modify, map_mul, E.forgetD, mul_one, hd]
  · rw [balancedZ_modify, map_mul, E.forgetZ, mul_one, hz]
  · apply oneHandleModTwoIndep_of_fibers Psi0
    · rw [balancedA_modify, map_mul, E.forgetA, mul_one, ha]
    · rw [balancedB_modify, map_mul, E.forgetB, mul_one, hb]
    · rw [balancedC_modify, map_mul, E.forgetC, mul_one, hc]
    · rw [balancedZ_modify, balancedD_modify, map_mul, map_mul, map_mul,
        E.forgetZ, E.forgetD, mul_one, hz, hd]
      simp
  · intro f
    rw [balancedC_modify, map_mul, toAdd_mul, hrow f, E.row f, add_zero]

/-- W202's depth-three seed and the exact climb supply give every finite balanced stage. -/
theorem oneHandleBalancedSet_nonempty_all
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0)))
    (Hclimb : OneHandleBalancedClimbSupply Psi0) (k : ℕ) :
    (oneHandleBalancedSet Psi0 k).Nonempty := by
  by_cases hk : k ≤ 3
  · exact ⟨Classical.choose (oneHandleBalancedSet_three_nonempty Psi0 hrow),
      oneHandleBalancedSet_antitone hk
        (Classical.choose_spec (oneHandleBalancedSet_three_nonempty Psi0 hrow))⟩
  · obtain ⟨d, rfl⟩ : ∃ d, k = 3 + d := ⟨k - 3, by omega⟩
    clear hk
    induction d with
    | zero => simpa using oneHandleBalancedSet_three_nonempty Psi0 hrow
    | succ d ih =>
      obtain ⟨p, hp⟩ := ih
      obtain ⟨E⟩ := Hclimb (3 + d) (by omega) p hp
      exact ⟨oneHandleBalancedModify p E.factors,
        by simpa only [Nat.add_assoc] using
          oneHandleBalancedSet_succ_of_correction Psi0 hp E⟩

/-- The honest W203 composition: the cup-adapted seed plus multi-slot reachability produces
the exact one-handle pivot shift. -/
theorem mpcPivShiftH_two_one_of_balancedClimb
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hchi0 : ∀ x, chiM 2 0 (Psi0 x) = chiM 2 0 x)
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0)))
    (Hclimb : OneHandleBalancedClimbSupply Psi0) :
    MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_balanced_forall_class Psi0 hchi0
    (oneHandleBalancedSet_nonempty_all Psi0 hrow Hclimb)

#print axioms oneHandleBalancedModify
#print axioms OneHandleBalancedCorrection
#print axioms OneHandleBalancedClimbSupply
#print axioms levelMk_balancedCorrectedMark_modify
#print axioms oneHandleBalancedSet_succ_of_correction
#print axioms oneHandleBalancedSet_nonempty_all
#print axioms mpcPivShiftH_two_one_of_balancedClimb

end
end GQ2.Dyadic.Instances.MpcBalancedClimb

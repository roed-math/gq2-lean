/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedCoordinateCokernel

/-!
# Separating the relative-row and neutral-C obstructions

W211 packages the remaining four-coordinate problem in one finite cokernel.  This file
splits that obstruction into two stages.  First all four core coordinates may range over the
ordinary relative layer.  The second quotient then measures only the extra requirement that
the `C` coordinate admit a character-neutral representative.

No spanning statement is asserted.  The point is to distinguish failure of ordinary
handle-relative row coverage from failure of the strictly smaller neutral-`C` condition.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedNeutralityCokernel

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Dyadic.Instances.MpcBalancedFiniteCore
open GQ2.Dyadic.Instances.MpcBalancedFiniteSpan
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcBalancedCoordinateSpan
open GQ2.Dyadic.Instances.MpcBalancedCoordinateCokernel
open GQ2.Roe.Labute

/-! ## The ordinary-relative C row -/

/-- Put an ordinary relative class in raw coordinate `C`. -/
noncomputable def oneHandleRelativeCoordCRaw (k : ℕ) :
    oneHandleRelativeLambdaImage (k - 1) (k + 1) →*
      EvenRawDepthCorrection (DM 2 1) 1 k where
  toFun x := evenRawDepthCoordinateCorrection 2 ⟨x.1, x.2.1⟩
  map_one' := by
    apply EvenRawDepthCorrection.ext
    funext i
    rw [evenRawDepthCoordinateCorrection_apply]
    by_cases hi : i = 2 <;> simp [hi]
  map_mul' x y := by
    apply EvenRawDepthCorrection.ext
    funext i
    rw [evenRawDepthCoordinateCorrection_apply,
      EvenRawDepthCorrection.mul_correction,
      evenRawDepthCoordinateCorrection_apply,
      evenRawDepthCoordinateCorrection_apply]
    by_cases hi : i = 2 <;> simp [hi]

/-- The ordinary-relative `C` shift, before corestricting its codomain. -/
noncomputable def oneHandleBalancedCoreRelativeShiftCPre
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    oneHandleRelativeLambdaImage (k - 1) (k + 1) →*
      zLayer (DM 2 1) k :=
  (evenRawDepthShiftHom
    (fun i ↦ levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p i)) hk).comp
      (oneHandleRelativeCoordCRaw k)

/-- An ordinary-relative `C` shift still vanishes after forgetting the handle. -/
theorem oneHandleForgetLevelMap_relativeShiftCPre
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (x : oneHandleRelativeLambdaImage (k - 1) (k + 1)) :
    oneHandleForgetLevelMap (k + 1)
      ((oneHandleBalancedCoreRelativeShiftCPre p k hk x).1) = 1 := by
  change oneHandleForgetLevelMap (k + 1)
    (((evenRawDepthShiftHom
      (fun i ↦ levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p i)) hk)
        (evenRawDepthCoordinateCorrection 2 ⟨x.1, x.2.1⟩)).1) = 1
  rw [evenRawDepthShiftHom_two_apply]
  have hx : oneHandleForgetLevelMap (k + 1) x.1 = 1 :=
    MonoidHom.mem_ker.mp x.2.2
  simp only [commP, map_mul, map_inv, hx, inv_one, one_mul]
  group

/-- The `C` shift with the neutral-character condition relaxed, valued in the same relative
central layer as the constrained four-coordinate shift. -/
noncomputable def oneHandleBalancedCoreRelativeShiftCRelaxed
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    oneHandleRelativeLambdaImage (k - 1) (k + 1) →*
      oneHandleRelativeZLayer k where
  toFun x := ⟨(oneHandleBalancedCoreRelativeShiftCPre p k hk x).1,
    ⟨(oneHandleBalancedCoreRelativeShiftCPre p k hk x).2,
      MonoidHom.mem_ker.mpr
        (oneHandleForgetLevelMap_relativeShiftCPre p k hk x)⟩⟩
  map_one' := by
    apply Subtype.ext
    change ((oneHandleBalancedCoreRelativeShiftCPre p k hk) 1).1 = 1
    exact congrArg Subtype.val
      (map_one (oneHandleBalancedCoreRelativeShiftCPre p k hk))
  map_mul' x y := by
    apply Subtype.ext
    change ((oneHandleBalancedCoreRelativeShiftCPre p k hk) (x * y)).1 =
      ((oneHandleBalancedCoreRelativeShiftCPre p k hk) x).1 *
        ((oneHandleBalancedCoreRelativeShiftCPre p k hk) y).1
    exact congrArg Subtype.val
      (map_mul (oneHandleBalancedCoreRelativeShiftCPre p k hk) x y)

/-- The relaxed `C` row has the same bracket formula as the constrained row. -/
theorem oneHandleBalancedCoreRelativeShiftCRelaxed_apply
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (x : oneHandleRelativeLambdaImage (k - 1) (k + 1)) :
    (oneHandleBalancedCoreRelativeShiftCRelaxed p k hk x).1 =
      commP x.1
        (levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p 3)) := by
  exact evenRawDepthShiftHom_two_apply _ hk ⟨x.1, x.2.1⟩

/-! ## The relaxed coordinate span -/

/-- The four-coordinate span with ordinary relative classes allowed in every coordinate. -/
def oneHandleBalancedCoreRelativeCoordinateSpan
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    Subgroup (oneHandleRelativeZLayer k) :=
  ((oneHandleBalancedCoreRelativeShiftA p k hk).range ⊔
    (oneHandleBalancedCoreRelativeShiftB p k hk).range) ⊔
  ((oneHandleBalancedCoreRelativeShiftCRelaxed p k hk).range ⊔
    (oneHandleBalancedCoreRelativeShiftD p k hk).range)

/-- Requiring a neutral `C` representative can only shrink the coordinate span. -/
theorem oneHandleBalancedCoreCoordinateSpan_le_relativeCoordinateSpan
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    oneHandleBalancedCoreCoordinateSpan p k hk ≤
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk := by
  change
    (((oneHandleBalancedCoreRelativeShiftA p k hk).range ⊔
        (oneHandleBalancedCoreRelativeShiftB p k hk).range) ⊔
      ((oneHandleBalancedCoreRelativeShiftC p k hk).range ⊔
        (oneHandleBalancedCoreRelativeShiftD p k hk).range)) ≤ _
  apply sup_le
  · exact le_sup_left
  · apply sup_le
    · rintro y ⟨x, rfl⟩
      refine (show (oneHandleBalancedCoreRelativeShiftCRelaxed p k hk).range ≤
          oneHandleBalancedCoreRelativeCoordinateSpan p k hk from
        le_trans le_sup_left le_sup_right) ?_
      let xr : oneHandleRelativeLambdaImage (k - 1) (k + 1) :=
        ⟨x.1, oneHandleNeutralRelativeLambdaImage_le_relative _ _ (by omega) x.2⟩
      refine ⟨xr, Subtype.ext ?_⟩
      rw [oneHandleBalancedCoreRelativeShiftCRelaxed_apply,
        oneHandleBalancedCoreRelativeShiftC_apply]
    · exact le_trans le_sup_right le_sup_right

/-! ## Two finite cokernels -/

/-- The first cokernel asks only whether ordinary relative rows cover the target. -/
abbrev OneHandleBalancedCoreRelativeCoordinateCokernel
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :=
  (oneHandleRelativeZLayer k) ⧸
    (oneHandleBalancedCoreRelativeCoordinateSpan p k hk)

noncomputable instance oneHandleBalancedCoreRelativeCoordinateCokernel_finite
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    Finite (OneHandleBalancedCoreRelativeCoordinateCokernel p k hk) := by
  dsimp [OneHandleBalancedCoreRelativeCoordinateCokernel]
  infer_instance

/-- The target class modulo the four ordinary-relative coordinate ranges. -/
def oneHandleBalancedCoreRelativeCoordinateObstruction
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k) :
    OneHandleBalancedCoreRelativeCoordinateCokernel p k hk :=
  QuotientGroup.mk' (oneHandleBalancedCoreRelativeCoordinateSpan p k hk)
    (oneHandleBalancedCoreRelativeTarget p hp)

/-- The first obstruction vanishes exactly when ordinary relative rows cover the target. -/
theorem oneHandleBalancedCoreRelativeCoordinateObstruction_eq_one_iff
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k) :
    oneHandleBalancedCoreRelativeCoordinateObstruction p hk hp = 1 ↔
      oneHandleBalancedCoreRelativeTarget p hp ∈
        oneHandleBalancedCoreRelativeCoordinateSpan p k hk := by
  exact QuotientGroup.eq_one_iff _

/-- Inside the relaxed span, the constrained span is exactly the neutral-`C` subgroup. -/
def oneHandleBalancedCoreNeutralitySubgroup
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    Subgroup (oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :=
  Subgroup.comap (oneHandleBalancedCoreRelativeCoordinateSpan p k hk).subtype
    (oneHandleBalancedCoreCoordinateSpan p k hk)

/-- The second finite cokernel measures only the loss caused by imposing neutral `C`. -/
abbrev OneHandleBalancedCoreNeutralityCokernel
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :=
  (oneHandleBalancedCoreRelativeCoordinateSpan p k hk) ⧸
    (oneHandleBalancedCoreNeutralitySubgroup p k hk)

noncomputable instance oneHandleBalancedCoreNeutralityCokernel_finite
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    Finite (OneHandleBalancedCoreNeutralityCokernel p k hk) := by
  dsimp [OneHandleBalancedCoreNeutralityCokernel]
  infer_instance

/-- Once ordinary relative coverage is known, reduce the target modulo the neutral-`C`
subgroup. -/
def oneHandleBalancedCoreNeutralityObstruction
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    OneHandleBalancedCoreNeutralityCokernel p k hk :=
  QuotientGroup.mk' (oneHandleBalancedCoreNeutralitySubgroup p k hk)
    ⟨oneHandleBalancedCoreRelativeTarget p hp, hrel⟩

/-- The second obstruction vanishes exactly when the already-relative target lies in the
original constrained coordinate span. -/
theorem oneHandleBalancedCoreNeutralityObstruction_eq_one_iff
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    oneHandleBalancedCoreNeutralityObstruction p hk hp hrel = 1 ↔
      oneHandleBalancedCoreRelativeTarget p hp ∈
        oneHandleBalancedCoreCoordinateSpan p k hk := by
  change QuotientGroup.mk' (oneHandleBalancedCoreNeutralitySubgroup p k hk)
      (⟨oneHandleBalancedCoreRelativeTarget p hp, hrel⟩ :
        oneHandleBalancedCoreRelativeCoordinateSpan p k hk) = 1 ↔ _
  constructor
  · intro h
    have hm := (QuotientGroup.eq_one_iff
      (⟨oneHandleBalancedCoreRelativeTarget p hp, hrel⟩ :
        oneHandleBalancedCoreRelativeCoordinateSpan p k hk)).mp h
    change oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreCoordinateSpan p k hk at hm
    exact hm
  · intro h
    apply (QuotientGroup.eq_one_iff
      (⟨oneHandleBalancedCoreRelativeTarget p hp, hrel⟩ :
        oneHandleBalancedCoreRelativeCoordinateSpan p k hk)).mpr
    change oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreCoordinateSpan p k hk
    exact h

/-! ## Uniform two-stage supply -/

/-- Uniform coverage by the four ordinary-relative rows. -/
def OneHandleBalancedCoreRelativeCoordinateSpanSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (p : OneHandleBalancedPoint)
    (hp : p ∈ oneHandleBalancedSet Psi0 k),
      oneHandleBalancedCoreRelativeTarget p hp ∈
        oneHandleBalancedCoreRelativeCoordinateSpan p k hk

/-- Uniform vanishing of the neutral-`C` obstruction whenever ordinary relative coverage is
available. -/
def OneHandleBalancedCoreNeutralityObstructionVanishing
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (p : OneHandleBalancedPoint)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk),
      oneHandleBalancedCoreNeutralityObstruction p hk hp hrel = 1

/-- The W210 supply is exactly ordinary-relative coverage plus neutral-`C` lifting. -/
theorem coordinateSpanSupply_iff_relative_and_neutrality
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) :
    OneHandleBalancedCoreCoordinateSpanSupply Psi0 ↔
      OneHandleBalancedCoreRelativeCoordinateSpanSupply Psi0 ∧
        OneHandleBalancedCoreNeutralityObstructionVanishing Psi0 := by
  constructor
  · intro H
    constructor
    · intro k hk p hp
      exact oneHandleBalancedCoreCoordinateSpan_le_relativeCoordinateSpan p k hk
        (H k hk p hp)
    · intro k hk p hp hrel
      exact (oneHandleBalancedCoreNeutralityObstruction_eq_one_iff
        p hk hp hrel).mpr (H k hk p hp)
  · rintro ⟨Hrel, Hneutral⟩ k hk p hp
    exact (oneHandleBalancedCoreNeutralityObstruction_eq_one_iff
      p hk hp (Hrel k hk p hp)).mp
        (Hneutral k hk p hp (Hrel k hk p hp))

/-- The two separated finite obstructions suffice for the one-handle pivot. -/
theorem mpcPivShiftH_two_one_of_balancedRelative_and_neutrality
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hchi0 : ∀ x, chiM 2 0 (Psi0 x) = chiM 2 0 x)
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0)))
    (Hrel : OneHandleBalancedCoreRelativeCoordinateSpanSupply Psi0)
    (Hneutral : OneHandleBalancedCoreNeutralityObstructionVanishing Psi0) :
    MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_balancedCoordinateSpan Psi0 hchi0 hrow
    ((coordinateSpanSupply_iff_relative_and_neutrality Psi0).mpr
      ⟨Hrel, Hneutral⟩)

#print axioms oneHandleRelativeCoordCRaw
#print axioms oneHandleBalancedCoreRelativeShiftCPre
#print axioms oneHandleForgetLevelMap_relativeShiftCPre
#print axioms oneHandleBalancedCoreRelativeShiftCRelaxed
#print axioms oneHandleBalancedCoreRelativeShiftCRelaxed_apply
#print axioms oneHandleBalancedCoreRelativeCoordinateSpan
#print axioms oneHandleBalancedCoreCoordinateSpan_le_relativeCoordinateSpan
#print axioms OneHandleBalancedCoreRelativeCoordinateCokernel
#print axioms oneHandleBalancedCoreRelativeCoordinateCokernel_finite
#print axioms oneHandleBalancedCoreRelativeCoordinateObstruction
#print axioms oneHandleBalancedCoreRelativeCoordinateObstruction_eq_one_iff
#print axioms oneHandleBalancedCoreNeutralitySubgroup
#print axioms OneHandleBalancedCoreNeutralityCokernel
#print axioms oneHandleBalancedCoreNeutralityCokernel_finite
#print axioms oneHandleBalancedCoreNeutralityObstruction
#print axioms oneHandleBalancedCoreNeutralityObstruction_eq_one_iff
#print axioms OneHandleBalancedCoreRelativeCoordinateSpanSupply
#print axioms OneHandleBalancedCoreNeutralityObstructionVanishing
#print axioms coordinateSpanSupply_iff_relative_and_neutrality
#print axioms mpcPivShiftH_two_one_of_balancedRelative_and_neutrality

end
end GQ2.Dyadic.Instances.MpcBalancedNeutralityCokernel

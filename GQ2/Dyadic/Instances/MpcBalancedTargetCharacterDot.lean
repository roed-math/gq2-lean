/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedTargetCharacterCoordinates

/-!
# Scalar form of the balanced target-character obstruction

W233 replaces an abstract character of the finite neutrality cokernel by a coefficient pair
`(a,b) ∈ (ZMod 4)²`. This file removes the remaining complex-valued character notation.

The character indexed by `(a,b)` takes the value one at a digit pair `(x,y)` exactly when
the scalar dot product `a*x + b*y` vanishes in `ZMod 4`. Consequently, a target is detected
exactly when some coefficient pair annihilates every CABD interaction row but has nonzero
dot product with that target.

This is a finite, purely algebraic obstruction: there are sixteen coefficient pairs and
sixteen possible target digit pairs. It remains pointwise; no detector is asserted to exist
uniformly.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedTargetCharacterDot

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcBalancedCoordinateSpan
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCokernel
open GQ2.Dyadic.Instances.MpcBalancedNeutralityInteraction
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCoordinateCokernel
open GQ2.Dyadic.Instances.MpcBalancedTargetCharacters
open GQ2.Dyadic.Instances.MpcBalancedTargetCharacterObstruction
open GQ2.Dyadic.Instances.MpcBalancedTargetCharacterCoordinates

open scoped IsMulCommutative

private theorem zmodAddEquiv_eval_comm (a x : ZMod 4) :
    AddChar.zmodAddEquiv a x = AddChar.zmodAddEquiv x a := by
  rw [AddChar.zmodAddEquiv_apply, AddChar.zmodAddEquiv_apply]
  change ((AddChar.zmod 4 a x : Circle) : ℂ) =
    ((AddChar.zmod 4 x a : Circle) : ℂ)
  simp [AddChar.zmod, mul_comm]

private theorem zmodAddEquiv_eval_mul (a x : ZMod 4) :
    AddChar.zmodAddEquiv a x = AddChar.zmodAddEquiv 1 (a * x) := by
  rw [AddChar.zmodAddEquiv_apply, AddChar.zmodAddEquiv_apply]
  change ((AddChar.zmod 4 a x : Circle) : ℂ) =
    ((AddChar.zmod 4 1 (a * x) : Circle) : ℂ)
  simp [AddChar.zmod]

theorem oneHandleZModFourPlaneCharacter_eq_zmod_dot
    (a b x y : ZMod 4) :
    oneHandleZModFourPlaneCharacter a b
        (Additive.ofMul (Multiplicative.ofAdd x, Multiplicative.ofAdd y)) =
      AddChar.zmodAddEquiv (1 : ZMod 4) (a * x + b * y) := by
  rw [oneHandleZModFourPlaneCharacter_apply]
  change AddChar.zmodAddEquiv a x * AddChar.zmodAddEquiv b y = _
  rw [zmodAddEquiv_eval_mul a x, zmodAddEquiv_eval_mul b y]
  exact (AddChar.map_add_eq_mul (AddChar.zmodAddEquiv (1 : ZMod 4))
    (a * x) (b * y)).symm

theorem zmodAddEquiv_one_eq_one_iff (t : ZMod 4) :
    AddChar.zmodAddEquiv (1 : ZMod 4) t = 1 ↔ t = 0 := by
  constructor
  · intro h
    have ht1 : AddChar.zmodAddEquiv t (1 : ZMod 4) = 1 := by
      rwa [zmodAddEquiv_eval_comm]
    have hchar : AddChar.zmodAddEquiv t = 1 := by
      by_contra hn
      exact (AddChar.zmod_char_ne_one_iff 4
        (AddChar.zmodAddEquiv t)).mp hn ht1
    apply AddChar.zmodAddEquiv.injective
    exact hchar.trans (map_zero AddChar.zmodAddEquiv).symm
  · rintro rfl
    exact AddChar.map_zero_eq_one _

def oneHandleZModFourDot (a b : ZMod 4)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) : ZMod 4 :=
  a * z.1.toAdd + b * z.2.toAdd

theorem oneHandleZModFourPlaneCharacter_eq_one_iff_dot_eq_zero
    (a b : ZMod 4)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :
    oneHandleZModFourPlaneCharacter a b (Additive.ofMul z) = 1 ↔
      oneHandleZModFourDot a b z = 0 := by
  change oneHandleZModFourPlaneCharacter a b
      (Additive.ofMul
        (Multiplicative.ofAdd z.1.toAdd, Multiplicative.ofAdd z.2.toAdd)) = 1 ↔ _
  rw [oneHandleZModFourPlaneCharacter_eq_zmod_dot,
    zmodAddEquiv_one_eq_one_iff]
  rfl

theorem oneHandleZModFourPlaneCharacter_ne_one_iff_dot_ne_zero
    (a b : ZMod 4)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :
    oneHandleZModFourPlaneCharacter a b (Additive.ofMul z) ≠ 1 ↔
      oneHandleZModFourDot a b z ≠ 0 :=
  not_congr (oneHandleZModFourPlaneCharacter_eq_one_iff_dot_eq_zero a b z)

def OneHandleBalancedCoreTargetDotDetected
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) : Prop :=
  ∃ z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
    oneHandleBalancedCoreNeutralityCoordinateFactor p k hk z =
        oneHandleBalancedCoreNeutralityObstruction p hk hp hrel ∧
      ∃ a b : ZMod 4,
        oneHandleZModFourDot a b z ≠ 0 ∧
          ∀ x : oneHandleBalancedCoreNeutralityInteractionSource p k hk,
            oneHandleZModFourDot a b
              (oneHandleBalancedCoreNeutralityCoordinateRow p k hk x) = 0

theorem targetDotDetected_iff_coefficientDetected
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    OneHandleBalancedCoreTargetDotDetected p hk hp hrel ↔
      OneHandleBalancedCoreTargetCoefficientDetected p hk hp hrel := by
  simp only [OneHandleBalancedCoreTargetDotDetected,
    OneHandleBalancedCoreTargetCoefficientDetected,
    oneHandleZModFourPlaneCharacter_eq_one_iff_dot_eq_zero,
    oneHandleZModFourPlaneCharacter_ne_one_iff_dot_ne_zero]

theorem targetDotDetected_iff_not_coordinateSpan
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    OneHandleBalancedCoreTargetDotDetected p hk hp hrel ↔
      oneHandleBalancedCoreRelativeTarget p hp ∉
        oneHandleBalancedCoreCoordinateSpan p k hk := by
  rw [targetDotDetected_iff_coefficientDetected,
    targetCoefficientDetected_iff_not_coordinateSpan]

theorem oneHandleBalancedSet_succ_empty_iff_pointwise_dotObstruction
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (k : ℕ) (hk : 3 ≤ k) :
    ¬(oneHandleBalancedSet Psi0 (k + 1)).Nonempty ↔
      ∀ p : OneHandleBalancedPoint,
        ∀ hp : p ∈ oneHandleBalancedSet Psi0 k,
          oneHandleBalancedCoreRelativeTarget p hp ∉
              oneHandleBalancedCoreRelativeCoordinateSpan p k hk ∨
            ∃ hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
              oneHandleBalancedCoreRelativeCoordinateSpan p k hk,
                OneHandleBalancedCoreTargetDotDetected p hk hp hrel := by
  simpa only [targetDotDetected_iff_coefficientDetected] using
    oneHandleBalancedSet_succ_empty_iff_pointwise_coefficientObstruction
      Psi0 k hk

#print axioms oneHandleZModFourPlaneCharacter_eq_zmod_dot
#print axioms zmodAddEquiv_one_eq_one_iff
#print axioms oneHandleZModFourDot
#print axioms oneHandleZModFourPlaneCharacter_eq_one_iff_dot_eq_zero
#print axioms oneHandleZModFourPlaneCharacter_ne_one_iff_dot_ne_zero
#print axioms OneHandleBalancedCoreTargetDotDetected
#print axioms targetDotDetected_iff_coefficientDetected
#print axioms targetDotDetected_iff_not_coordinateSpan
#print axioms oneHandleBalancedSet_succ_empty_iff_pointwise_dotObstruction

end
end GQ2.Dyadic.Instances.MpcBalancedTargetCharacterDot

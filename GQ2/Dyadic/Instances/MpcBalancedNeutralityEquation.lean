/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedNeutralityInteraction

/-!
# The literal C-versus-ABD equation

W215 reduces the neutral-`C` obstruction to the image of a `C`-versus-`ABD` relation source.
This file expands that subgroup membership into a literal finite row equation.  For any
chosen relaxed-`C` representative of the target obstruction, vanishing is equivalent to
changing it by a genuinely neutral class and solving that explicit equation.

No solution of the equation is asserted.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedNeutralityEquation

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

open scoped IsMulCommutative

/-! ## Expanding the interaction source -/

/-- Membership in the residual interaction source is exactly one literal relaxed-`C`
equals constrained-`A` times constrained-`B` times constrained-`D` equation. -/
theorem mem_oneHandleBalancedCoreNeutralityInteractionSource_iff
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (x : oneHandleRelativeLambdaImage (k - 1) (k + 1)) :
    x ∈ oneHandleBalancedCoreNeutralityInteractionSource p k hk ↔
      ∃ a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
        oneHandleBalancedCoreRelativeShiftCRelaxed p k hk x =
          oneHandleBalancedCoreRelativeShiftA p k hk a *
            oneHandleBalancedCoreRelativeShiftB p k hk b *
              oneHandleBalancedCoreRelativeShiftD p k hk d := by
  change oneHandleBalancedCoreRelativeShiftCRelaxed p k hk x ∈
      oneHandleBalancedCoreOtherCoordinateSpan p k hk ↔ _
  constructor
  · intro hx
    obtain ⟨ab, hab, dd, hdd, habd⟩ := Subgroup.mem_sup.mp hx
    obtain ⟨aa, haa, bb, hbb, hab'⟩ := Subgroup.mem_sup.mp hab
    obtain ⟨a, ha⟩ := haa
    obtain ⟨b, hb⟩ := hbb
    obtain ⟨d, hd⟩ := hdd
    refine ⟨a, b, d, ?_⟩
    rw [ha, hb, hd]
    rw [← hab'] at habd
    exact habd.symm
  · rintro ⟨a, b, d, heq⟩
    apply Subgroup.mem_sup.mpr
    refine ⟨oneHandleBalancedCoreRelativeShiftA p k hk a *
        oneHandleBalancedCoreRelativeShiftB p k hk b, ?_,
      oneHandleBalancedCoreRelativeShiftD p k hk d, ?_, ?_⟩
    · apply Subgroup.mem_sup.mpr
      exact ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
    · exact ⟨d, rfl⟩
    · exact heq.symm

/-! ## A target-specific exact criterion -/

/-- Fix any relaxed `C` representative of the target neutrality class.  The obstruction
vanishes exactly when the same class modulo genuinely neutral representatives contains a
solution of the literal `C = A * B * D` row equation. -/
theorem neutralityObstruction_eq_one_iff_CABD
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
        oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
          oneHandleBalancedCoreRelativeShiftA p k hk a *
            oneHandleBalancedCoreRelativeShiftB p k hk b *
              oneHandleBalancedCoreRelativeShiftD p k hk d := by
  constructor
  · intro hobs
    have hfactor : oneHandleBalancedCoreNeutralitySourceFactor p k hk
        (oneHandleRelativeCModuloNeutralMk k hk x) = 1 := by
      rw [oneHandleBalancedCoreNeutralitySourceFactor_mk, hx, hobs]
    have hker : oneHandleRelativeCModuloNeutralMk k hk x ∈
        oneHandleBalancedCoreNeutralityInteraction p k hk :=
      MonoidHom.mem_ker.mpr hfactor
    rw [← oneHandleBalancedCoreNeutralityInteraction_range_eq p k hk] at hker
    obtain ⟨y, hy⟩ := hker
    obtain ⟨a, b, d, heq⟩ :=
      (mem_oneHandleBalancedCoreNeutralityInteractionSource_iff
        p k hk y.1).mp y.2
    exact ⟨y.1, a, b, d, hy, heq⟩
  · rintro ⟨y, a, b, d, hy, heq⟩
    have hymem : y ∈ oneHandleBalancedCoreNeutralityInteractionSource p k hk :=
      (mem_oneHandleBalancedCoreNeutralityInteractionSource_iff p k hk y).mpr
        ⟨a, b, d, heq⟩
    have hyrange : oneHandleRelativeCModuloNeutralMk k hk y ∈
        (oneHandleBalancedCoreNeutralityInteractionToSource p k hk).range :=
      ⟨⟨y, hymem⟩, rfl⟩
    rw [oneHandleBalancedCoreNeutralityInteraction_range_eq p k hk] at hyrange
    have hyfactor : oneHandleBalancedCoreNeutralitySourceFactor p k hk
        (oneHandleRelativeCModuloNeutralMk k hk y) = 1 :=
      MonoidHom.mem_ker.mp hyrange
    have hxfactor : oneHandleBalancedCoreNeutralitySourceFactor p k hk
        (oneHandleRelativeCModuloNeutralMk k hk x) = 1 := by
      rw [← hy]
      exact hyfactor
    rw [oneHandleBalancedCoreNeutralitySourceFactor_mk, hx] at hxfactor
    exact hxfactor

#print axioms mem_oneHandleBalancedCoreNeutralityInteractionSource_iff
#print axioms neutralityObstruction_eq_one_iff_CABD

end
end GQ2.Dyadic.Instances.MpcBalancedNeutralityEquation

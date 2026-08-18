/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeRankJump

/-!
# The literal class-seven ordinary-relative equation

The zero-rank-jump condition of W272 is target membership in a join of four ranges.  This file
expands that join into four explicit source classes.  The target is ordinarily covered exactly
when it is a product of the standard `A`, `B`, relaxed `C`, and `D` rows, equivalently when one
literal square-and-bracket equation holds in the relative central layer.

The one-bit detector of W272 is exactly nonexistence of such a tuple.  No tuple is constructed
here, and the separate condition that the `C` class admit a character-neutral representative
is not imposed.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeEquation

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCorrection
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCoordinates
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeF2
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeRank
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeRankJump
open GQ2.Roe.Labute
open scoped IsMulCommutative

private abbrev H := DM 2 1

theorem standardRelativeTarget_mem_relaxed_iff_exists_rows
    (E : OneHandleC7RelativeLift) :
    oneHandleC7RelativeTarget E ∈
        oneHandleStandardRelativeRelaxedCoordinateSpan ↔
      ∃ a b c d : oneHandleRelativeLambdaImage 5 7,
        oneHandleC7RelativeTarget E =
          oneHandleStandardRelativeShiftA a *
            oneHandleStandardRelativeShiftB b *
              oneHandleStandardRelativeShiftCRelaxed c *
                oneHandleStandardRelativeShiftD d := by
  rw [oneHandleStandardRelativeRelaxedCoordinateSpan_eq_rows]
  constructor
  · intro htarget
    obtain ⟨ab, hab, cd, hcd, habcd⟩ := Subgroup.mem_sup.mp htarget
    obtain ⟨aa, haa, bb, hbb, hab'⟩ := Subgroup.mem_sup.mp hab
    obtain ⟨cc, hcc, dd, hdd, hcd'⟩ := Subgroup.mem_sup.mp hcd
    obtain ⟨a, ha⟩ := haa
    obtain ⟨b, hb⟩ := hbb
    obtain ⟨c, hc⟩ := hcc
    obtain ⟨d, hd⟩ := hdd
    refine ⟨a, b, c, d, ?_⟩
    rw [ha, hb, hc, hd]
    rw [← hab', ← hcd'] at habcd
    simpa only [mul_assoc] using habcd.symm
  · rintro ⟨a, b, c, d, htarget⟩
    apply Subgroup.mem_sup.mpr
    refine ⟨oneHandleStandardRelativeShiftA a *
        oneHandleStandardRelativeShiftB b, ?_,
      oneHandleStandardRelativeShiftCRelaxed c *
        oneHandleStandardRelativeShiftD d, ?_, ?_⟩
    · apply Subgroup.mem_sup.mpr
      exact ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
    · apply Subgroup.mem_sup.mpr
      exact ⟨_, ⟨c, rfl⟩, _, ⟨d, rfl⟩, rfl⟩
    · simpa only [mul_assoc] using htarget.symm

def OneHandleC7StandardRelativeRowEquation
    (E : OneHandleC7RelativeLift) : Prop :=
  ∃ a b c d : oneHandleRelativeLambdaImage 5 7,
    (oneHandleC7RelativeTarget E).1 =
      (a.1 ^ 2 * commP a.1 (levelMk H 7 (dmA 2 1)) *
          commP a.1 (levelMk H 7 (dmB 2 1))) *
        commP b.1 (levelMk H 7 (dmA 2 1)) *
          commP c.1 (levelMk H 7 (dmD 2 1)) *
            commP d.1 (levelMk H 7 (dmC 2 1))

theorem standardRelativeTarget_mem_relaxed_iff_rowEquation
    (E : OneHandleC7RelativeLift) :
    oneHandleC7RelativeTarget E ∈
        oneHandleStandardRelativeRelaxedCoordinateSpan ↔
      OneHandleC7StandardRelativeRowEquation E := by
  rw [standardRelativeTarget_mem_relaxed_iff_exists_rows]
  constructor
  · rintro ⟨a, b, c, d, h⟩
    refine ⟨a, b, c, d, ?_⟩
    have hv := congrArg Subtype.val h
    simpa only [Subgroup.coe_mul,
      oneHandleStandardRelativeShiftA_apply,
      oneHandleStandardRelativeShiftB_apply,
      oneHandleStandardRelativeShiftCRelaxed_apply,
      oneHandleStandardRelativeShiftD_apply, mul_assoc] using hv
  · rintro ⟨a, b, c, d, h⟩
    refine ⟨a, b, c, d, Subtype.ext ?_⟩
    simpa only [Subgroup.coe_mul,
      oneHandleStandardRelativeShiftA_apply,
      oneHandleStandardRelativeShiftB_apply,
      oneHandleStandardRelativeShiftCRelaxed_apply,
      oneHandleStandardRelativeShiftD_apply, mul_assoc] using h

theorem standardRelativeTargetDetected_iff_no_rowEquation
    (E : OneHandleC7RelativeLift) :
    OneHandleC7StandardRelativeTargetDetected E ↔
      ¬ OneHandleC7StandardRelativeRowEquation E := by
  rw [standardRelativeTargetDetected_iff_not_mem_relaxed]
  exact not_congr (standardRelativeTarget_mem_relaxed_iff_rowEquation E)

theorem standardRelativeRankJump_zero_iff_rowEquation
    (E : OneHandleC7RelativeLift) :
    oneHandleC7StandardRelativeAugmentedTransposeRank E -
        oneHandleC7StandardRelativeCoordinateTransposeRank = 0 ↔
      OneHandleC7StandardRelativeRowEquation E := by
  rw [← standardRelativeTarget_mem_relaxed_iff_rankJump_zero,
    standardRelativeTarget_mem_relaxed_iff_rowEquation]

theorem standardRelativeRankJump_one_iff_no_rowEquation
    (E : OneHandleC7RelativeLift) :
    oneHandleC7StandardRelativeAugmentedTransposeRank E -
        oneHandleC7StandardRelativeCoordinateTransposeRank = 1 ↔
      ¬ OneHandleC7StandardRelativeRowEquation E := by
  rw [← standardRelativeTargetDetected_iff_rankJump_one,
    standardRelativeTargetDetected_iff_no_rowEquation]

#print axioms standardRelativeTarget_mem_relaxed_iff_exists_rows
#print axioms OneHandleC7StandardRelativeRowEquation
#print axioms standardRelativeTarget_mem_relaxed_iff_rowEquation
#print axioms standardRelativeTargetDetected_iff_no_rowEquation
#print axioms standardRelativeRankJump_zero_iff_rowEquation
#print axioms standardRelativeRankJump_one_iff_no_rowEquation

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeEquation

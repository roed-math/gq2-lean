/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingRealization
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeF2

/-!
# Dual test for the compact connecting target

W282 reduced ordinary class-seven solvability to membership of one reference obstruction in
the compact connecting image.  This module dualizes that exact membership question over F2.
The connecting-image transpose evaluates each character of the ordinary relative cokernel on
all compact-kernel corrections.  The target evaluation appends the reference obstruction.

The obstruction belongs to the connecting image exactly when every character annihilating the
image also annihilates the obstruction.  Equivalently, adjoining target evaluation does not
shrink the transpose kernel.  Thus ordinary relative solvability has an exact finite kernel
test.  No value of that kernel is computed here.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingTarget

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeF2
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenFinitePacket
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingHom
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingCriterion
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingRealization
open GQ2.FoxH
open scoped IsMulCommutative

private abbrev ConnectingSource :=
  Additive OneHandleCompactKernelCorrection

private abbrev ConnectingTarget :=
  Additive OneHandleC7StandardRelativeCokernel

private abbrev ConnectingDual := ConnectingSource →+ ZMod 2

private def oneHandleCompactConnectingAdd :
    ConnectingSource →+ ConnectingTarget :=
  oneHandleCompactConnectingHom.toAdditive

noncomputable def oneHandleCompactConnectingImageTranspose :
    ElemDual ConnectingTarget →+ ConnectingDual where
  toFun ell := (ell : ConnectingTarget →+ ZMod 2).comp
    oneHandleCompactConnectingAdd
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable def oneHandleCompactConnectingTargetEvaluation
    (E : OneHandleC7RelativeLift) :
    ElemDual ConnectingTarget →+ ZMod 2 where
  toFun ell := ell
    (Additive.ofMul (oneHandleC7StandardRelativeObstruction E))
  map_zero' := rfl
  map_add' _ _ := rfl

def OneHandleCompactConnectingTargetTransposeVanishing
    (E : OneHandleC7RelativeLift) : Prop :=
  ∀ ell : ElemDual ConnectingTarget,
    oneHandleCompactConnectingImageTranspose ell = 0 →
      oneHandleCompactConnectingTargetEvaluation E ell = 0

private theorem connectingTargetQuotient_add_self
    (x : ConnectingTarget ⧸ oneHandleCompactConnectingAdd.range) :
    x + x = 0 := by
  obtain ⟨x, rfl⟩ :=
    QuotientAddGroup.mk'_surjective oneHandleCompactConnectingAdd.range x
  rw [← map_add, oneHandleC7StandardRelativeCokernel_add_self, map_zero]

theorem connectingTargetTransposeVanishing_iff_mem_range
    (E : OneHandleC7RelativeLift) :
    OneHandleCompactConnectingTargetTransposeVanishing E ↔
      Additive.ofMul (oneHandleC7StandardRelativeObstruction E) ∈
        oneHandleCompactConnectingAdd.range := by
  constructor
  · intro hvan
    by_contra hmem
    have hq : QuotientAddGroup.mk' oneHandleCompactConnectingAdd.range
        (Additive.ofMul (oneHandleC7StandardRelativeObstruction E)) ≠ 0 := by
      intro hzero
      exact hmem ((QuotientAddGroup.eq_zero_iff _).mp hzero)
    obtain ⟨qell, hqell⟩ := elemDual_separates
      connectingTargetQuotient_add_self hq
    let ell : ElemDual ConnectingTarget :=
      ((qell :
          (ConnectingTarget ⧸ oneHandleCompactConnectingAdd.range) →+
            ZMod 2).comp
        (QuotientAddGroup.mk' oneHandleCompactConnectingAdd.range) :
          ElemDual ConnectingTarget)
    have hell : oneHandleCompactConnectingImageTranspose ell = 0 := by
      apply AddMonoidHom.ext
      intro D
      change qell (QuotientAddGroup.mk'
        oneHandleCompactConnectingAdd.range
          (oneHandleCompactConnectingAdd D)) = 0
      have hz : QuotientAddGroup.mk'
          oneHandleCompactConnectingAdd.range
            (oneHandleCompactConnectingAdd D) = 0 :=
        (QuotientAddGroup.eq_zero_iff _).mpr ⟨D, rfl⟩
      rw [hz]
      exact map_zero qell
    exact hqell (hvan ell hell)
  · rintro ⟨D, hD⟩ ell hell
    have hz := congrArg (fun f : ConnectingDual ↦ f D) hell
    change ell
      (Additive.ofMul (oneHandleC7StandardRelativeObstruction E)) = 0
    rw [← hD]
    exact hz

theorem obstruction_mem_connectingValues_iff_transposeVanishing
    (E : OneHandleC7RelativeLift) :
    oneHandleC7StandardRelativeObstruction E ∈ compactConnectingValues ↔
      OneHandleCompactConnectingTargetTransposeVanishing E := by
  rw [connectingTargetTransposeVanishing_iff_mem_range,
    mem_compactConnectingValues_iff]
  constructor
  · rintro ⟨D, hD⟩
    exact ⟨Additive.ofMul D, congrArg Additive.ofMul hD⟩
  · rintro ⟨D, hD⟩
    exact ⟨D.toMul, Additive.ofMul.injective hD⟩

noncomputable def oneHandleCompactConnectingTargetAugmentedTranspose
    (E : OneHandleC7RelativeLift) :
    ElemDual ConnectingTarget →+ ConnectingDual × ZMod 2 where
  toFun ell :=
    (oneHandleCompactConnectingImageTranspose ell,
      oneHandleCompactConnectingTargetEvaluation E ell)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem connectingTargetAugmented_ker_le_imageTranspose_ker
    (E : OneHandleC7RelativeLift) :
    (oneHandleCompactConnectingTargetAugmentedTranspose E).ker ≤
      oneHandleCompactConnectingImageTranspose.ker := by
  intro ell hell
  exact AddMonoidHom.mem_ker.mpr
    (congrArg Prod.fst (AddMonoidHom.mem_ker.mp hell))

theorem connectingTargetTransposeVanishing_iff_ker_eq
    (E : OneHandleC7RelativeLift) :
    OneHandleCompactConnectingTargetTransposeVanishing E ↔
      (oneHandleCompactConnectingTargetAugmentedTranspose E).ker =
        oneHandleCompactConnectingImageTranspose.ker := by
  constructor
  · intro hvan
    apply le_antisymm
    · exact connectingTargetAugmented_ker_le_imageTranspose_ker E
    · intro ell hell
      have himage := AddMonoidHom.mem_ker.mp hell
      apply AddMonoidHom.mem_ker.mpr
      apply Prod.ext
      · exact himage
      · exact hvan ell himage
  · intro hker ell himage
    have hell : ell ∈ oneHandleCompactConnectingImageTranspose.ker :=
      AddMonoidHom.mem_ker.mpr himage
    rw [← hker] at hell
    exact congrArg Prod.snd (AddMonoidHom.mem_ker.mp hell)

theorem ordinaryRelativeSolvable_iff_connectingTarget_ker_eq
    (E : OneHandleC7RelativeLift) :
    OneHandleW6OrdinaryRelativeSolvable ↔
      (oneHandleCompactConnectingTargetAugmentedTranspose E).ker =
        oneHandleCompactConnectingImageTranspose.ker := by
  rw [ordinaryRelativeSolvable_iff_obstruction_mem_connectingValues,
    obstruction_mem_connectingValues_iff_transposeVanishing,
    connectingTargetTransposeVanishing_iff_ker_eq]

#print axioms oneHandleCompactConnectingImageTranspose
#print axioms oneHandleCompactConnectingTargetEvaluation
#print axioms OneHandleCompactConnectingTargetTransposeVanishing
#print axioms connectingTargetTransposeVanishing_iff_mem_range
#print axioms obstruction_mem_connectingValues_iff_transposeVanishing
#print axioms oneHandleCompactConnectingTargetAugmentedTranspose
#print axioms connectingTargetTransposeVanishing_iff_ker_eq
#print axioms ordinaryRelativeSolvable_iff_connectingTarget_ker_eq

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingTarget

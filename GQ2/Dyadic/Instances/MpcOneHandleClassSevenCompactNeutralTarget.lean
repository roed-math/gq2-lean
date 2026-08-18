/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralConnecting
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeF2

/-!
# Dual test for the class-seven neutral connecting target

The W287 neutral connecting image is elementary abelian. Its transpose evaluates every
character of the neutral-C cokernel on the compact connecting kernel, while the augmented
transpose also evaluates a chosen neutral obstruction.

The chosen obstruction lies in the neutral connecting image exactly when every character
annihilating that image also annihilates the obstruction. Equivalently, augmentation does not
shrink the transpose kernel. Applied to any ordinary correction, this is an exact finite dual
criterion for full W6 correctability. No kernel equality is asserted here.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralTarget

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeF2
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingHom
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingRealization
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactFullSolution
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralConnecting
open GQ2.FoxH GQ2.Roe.Labute
open scoped IsMulCommutative

private abbrev H := DM 2 1
private abbrev NeutralSource := Additive OneHandleCompactConnectingKernel
private abbrev NeutralTarget := Additive OneHandleC7StandardNeutralityCokernel
private abbrev NeutralDual := NeutralSource →+ ZMod 2

theorem oneHandleC7StandardNeutralityCokernel_sq
    (x : OneHandleC7StandardNeutralityCokernel) : x ^ 2 = 1 := by
  induction x using QuotientGroup.induction_on with
  | _ z =>
    have hz : z ^ 2 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact zLayer_sq H z.1.2.1
    change (QuotientGroup.mk' oneHandleC7StandardNeutralitySubgroup z) ^ 2 = 1
    rw [← map_pow, hz, map_one]

theorem oneHandleC7StandardNeutralityCokernel_add_self
    (x : NeutralTarget) : x + x = 0 := by
  apply Additive.toMul.injective
  simpa [pow_two] using oneHandleC7StandardNeutralityCokernel_sq x.toMul

private def oneHandleCompactNeutralConnectingAdd :
    NeutralSource →+ NeutralTarget :=
  oneHandleCompactNeutralConnectingHom.toAdditive

noncomputable def oneHandleCompactNeutralImageTranspose :
    ElemDual NeutralTarget →+ NeutralDual where
  toFun ell := (ell : NeutralTarget →+ ZMod 2).comp
    oneHandleCompactNeutralConnectingAdd
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable def oneHandleCompactNeutralTargetEvaluation
    (x : OneHandleC7StandardNeutralityCokernel) :
    ElemDual NeutralTarget →+ ZMod 2 where
  toFun ell := ell (Additive.ofMul x)
  map_zero' := rfl
  map_add' _ _ := rfl

def OneHandleCompactNeutralTargetTransposeVanishing
    (x : OneHandleC7StandardNeutralityCokernel) : Prop :=
  ∀ ell : ElemDual NeutralTarget,
    oneHandleCompactNeutralImageTranspose ell = 0 →
      oneHandleCompactNeutralTargetEvaluation x ell = 0

private theorem neutralTargetQuotient_add_self
    (x : NeutralTarget ⧸ oneHandleCompactNeutralConnectingAdd.range) :
    x + x = 0 := by
  obtain ⟨x, rfl⟩ :=
    QuotientAddGroup.mk'_surjective oneHandleCompactNeutralConnectingAdd.range x
  calc
    QuotientAddGroup.mk' oneHandleCompactNeutralConnectingAdd.range x +
        QuotientAddGroup.mk' oneHandleCompactNeutralConnectingAdd.range x =
      QuotientAddGroup.mk' oneHandleCompactNeutralConnectingAdd.range
        (x + x) := (map_add _ x x).symm
    _ = QuotientAddGroup.mk' oneHandleCompactNeutralConnectingAdd.range 0 := by
      have hx : x + x = 0 :=
        oneHandleC7StandardNeutralityCokernel_add_self x
      exact congrArg
        (QuotientAddGroup.mk' oneHandleCompactNeutralConnectingAdd.range) hx
    _ = 0 := map_zero _

theorem neutralTargetTransposeVanishing_iff_mem_range
    (x : OneHandleC7StandardNeutralityCokernel) :
    OneHandleCompactNeutralTargetTransposeVanishing x ↔
      Additive.ofMul x ∈ oneHandleCompactNeutralConnectingAdd.range := by
  constructor
  · intro hvan
    by_contra hmem
    have hq : QuotientAddGroup.mk' oneHandleCompactNeutralConnectingAdd.range
        (Additive.ofMul x) ≠ 0 := by
      intro hzero
      exact hmem ((QuotientAddGroup.eq_zero_iff _).mp hzero)
    obtain ⟨qell, hqell⟩ := elemDual_separates
      neutralTargetQuotient_add_self hq
    let ell : ElemDual NeutralTarget :=
      ((qell :
          (NeutralTarget ⧸ oneHandleCompactNeutralConnectingAdd.range) →+
            ZMod 2).comp
        (QuotientAddGroup.mk' oneHandleCompactNeutralConnectingAdd.range) :
          ElemDual NeutralTarget)
    have hell : oneHandleCompactNeutralImageTranspose ell = 0 := by
      apply AddMonoidHom.ext
      intro K
      change qell (QuotientAddGroup.mk'
        oneHandleCompactNeutralConnectingAdd.range
          (oneHandleCompactNeutralConnectingAdd K)) = 0
      have hz : QuotientAddGroup.mk'
          oneHandleCompactNeutralConnectingAdd.range
            (oneHandleCompactNeutralConnectingAdd K) = 0 :=
        (QuotientAddGroup.eq_zero_iff _).mpr ⟨K, rfl⟩
      rw [hz]
      exact map_zero qell
    exact hqell (hvan ell hell)
  · rintro ⟨K, hK⟩ ell hell
    have hz := congrArg (fun f : NeutralDual ↦ f K) hell
    change ell (Additive.ofMul x) = 0
    rw [← hK]
    exact hz

theorem mem_compactNeutralConnectingValues_iff_transposeVanishing
    (x : OneHandleC7StandardNeutralityCokernel) :
    x ∈ compactNeutralConnectingValues ↔
      OneHandleCompactNeutralTargetTransposeVanishing x := by
  rw [neutralTargetTransposeVanishing_iff_mem_range,
    mem_compactNeutralConnectingValues_iff]
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨Additive.ofMul K, congrArg Additive.ofMul hK⟩
  · rintro ⟨K, hK⟩
    exact ⟨K.toMul, Additive.ofMul.injective hK⟩

noncomputable def oneHandleCompactNeutralTargetAugmentedTranspose
    (x : OneHandleC7StandardNeutralityCokernel) :
    ElemDual NeutralTarget →+ NeutralDual × ZMod 2 where
  toFun ell :=
    (oneHandleCompactNeutralImageTranspose ell,
      oneHandleCompactNeutralTargetEvaluation x ell)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem neutralTargetAugmented_ker_le_imageTranspose_ker
    (x : OneHandleC7StandardNeutralityCokernel) :
    (oneHandleCompactNeutralTargetAugmentedTranspose x).ker ≤
      oneHandleCompactNeutralImageTranspose.ker := by
  intro ell hell
  exact AddMonoidHom.mem_ker.mpr
    (congrArg Prod.fst (AddMonoidHom.mem_ker.mp hell))

theorem neutralTargetTransposeVanishing_iff_ker_eq
    (x : OneHandleC7StandardNeutralityCokernel) :
    OneHandleCompactNeutralTargetTransposeVanishing x ↔
      (oneHandleCompactNeutralTargetAugmentedTranspose x).ker =
        oneHandleCompactNeutralImageTranspose.ker := by
  constructor
  · intro hvan
    apply le_antisymm
    · exact neutralTargetAugmented_ker_le_imageTranspose_ker x
    · intro ell hell
      have himage := AddMonoidHom.mem_ker.mp hell
      apply AddMonoidHom.mem_ker.mpr
      apply Prod.ext
      · exact himage
      · exact hvan ell himage
  · intro hker ell himage
    have hell : ell ∈ oneHandleCompactNeutralImageTranspose.ker :=
      AddMonoidHom.mem_ker.mpr himage
    rw [← hker] at hell
    exact congrArg Prod.snd (AddMonoidHom.mem_ker.mp hell)

theorem oneHandleW6Correctable_iff_neutralTarget_ker_eq
    (E : OneHandleC7RelativeLift)
    (D : OneHandleCompactKernelCorrection)
    (hD : oneHandleCompactConnectingHom D =
      oneHandleC7StandardRelativeObstruction E) :
    OneHandleW6Correctable ↔
      (oneHandleCompactNeutralTargetAugmentedTranspose
          (oneHandleC7StandardNeutralityObstruction
            (compactKernelCorrectionLift E D)
            (compactKernelCorrectionLift_relaxed E D hD))).ker =
        oneHandleCompactNeutralImageTranspose.ker := by
  rw [oneHandleW6Correctable_iff_neutrality_mem_connectingValues E D hD,
    mem_compactNeutralConnectingValues_iff_transposeVanishing,
    neutralTargetTransposeVanishing_iff_ker_eq]

private theorem zmodTwo_add_self (x : ZMod 2) : x + x = 0 := by
  rw [← two_smul (R := ZMod 2), show (2 : ZMod 2) = 0 by decide,
    zero_smul]

private theorem neutralDual_add_self (v : NeutralDual) : v + v = 0 := by
  ext K
  exact zmodTwo_add_self _

private theorem neutralAugmentedTarget_add_self
    (v : NeutralDual × ZMod 2) : v + v = 0 := by
  apply Prod.ext
  · exact neutralDual_add_self v.1
  · exact zmodTwo_add_self v.2

noncomputable def oneHandleCompactNeutralImageTransposeRank : ℕ := by
  letI : Module (ZMod 2) NeutralDual :=
    AddCommGroup.zmodModule (fun v ↦ by
      rw [two_nsmul]
      exact neutralDual_add_self v)
  exact Module.finrank (ZMod 2)
    (AddSubgroup.toZModSubmodule 2
      oneHandleCompactNeutralImageTranspose.range)

noncomputable def oneHandleCompactNeutralTargetAugmentedTransposeRank
    (x : OneHandleC7StandardNeutralityCokernel) : ℕ := by
  letI : Module (ZMod 2) (NeutralDual × ZMod 2) :=
    AddCommGroup.zmodModule (fun v ↦ by
      rw [two_nsmul]
      exact neutralAugmentedTarget_add_self v)
  exact Module.finrank (ZMod 2)
    (AddSubgroup.toZModSubmodule 2
      (oneHandleCompactNeutralTargetAugmentedTranspose x).range)

#print axioms oneHandleC7StandardNeutralityCokernel_sq
#print axioms oneHandleC7StandardNeutralityCokernel_add_self
#print axioms oneHandleCompactNeutralImageTranspose
#print axioms oneHandleCompactNeutralTargetEvaluation
#print axioms OneHandleCompactNeutralTargetTransposeVanishing
#print axioms neutralTargetTransposeVanishing_iff_mem_range
#print axioms mem_compactNeutralConnectingValues_iff_transposeVanishing
#print axioms oneHandleCompactNeutralTargetAugmentedTranspose
#print axioms neutralTargetTransposeVanishing_iff_ker_eq
#print axioms oneHandleW6Correctable_iff_neutralTarget_ker_eq
#print axioms oneHandleCompactNeutralImageTransposeRank
#print axioms oneHandleCompactNeutralTargetAugmentedTransposeRank

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralTarget

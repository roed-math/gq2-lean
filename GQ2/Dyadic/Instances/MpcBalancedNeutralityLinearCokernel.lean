/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedNeutralityZModFour

/-!
# The finite linear CABD cokernel

W220 identifies the remaining CABD system as a finite `ZMod 4`-linear map.  This file takes
its linear cokernel and places the prescribed `C` class in it.  The resulting canonical
obstruction vanishes exactly when the original one-handle neutrality obstruction vanishes.

This is a packaging boundary for the forthcoming coordinate calculation.  No cokernel
vanishing, dimension, invariant-factor, or rank assertion is made.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedNeutralityLinearCokernel

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
open GQ2.Dyadic.Instances.MpcBalancedNeutralityAdditive
open GQ2.Dyadic.Instances.MpcBalancedNeutralityLinearSystem
open GQ2.Dyadic.Instances.MpcBalancedNeutralityZModFour

open scoped IsMulCommutative

abbrev OneHandleBalancedCABDZModFourCokernel
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :=
  letI : IsMulCommutative
      (oneHandleRelativeLambdaImage (k - 1) (k + 1)) :=
    oneHandleRelativeLambdaImageIsMulCommutative k hk
  letI : IsMulCommutative (OneHandleRelativeCModuloNeutral k hk) :=
    oneHandleRelativeCModuloNeutralIsMulCommutative k hk
  letI : Module (ZMod 4) (Additive (OneHandleBalancedCABDData k)) :=
    AddCommGroup.zmodModule (oneHandleBalancedCABDData_four_nsmul k hk)
  letI : Module (ZMod 4)
      (Additive (oneHandleRelativeZLayer k × OneHandleRelativeCModuloNeutral k hk)) :=
    AddCommGroup.zmodModule (oneHandleBalancedCABDTarget_four_nsmul k hk)
  Additive (oneHandleRelativeZLayer k × OneHandleRelativeCModuloNeutral k hk) ⧸
    LinearMap.range (oneHandleBalancedCABDZModFourSystem p k hk)

noncomputable def oneHandleBalancedCABDZModFourObstruction
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (x : oneHandleRelativeLambdaImage (k - 1) (k + 1)) :
    OneHandleBalancedCABDZModFourCokernel p k hk := by
  letI : IsMulCommutative
      (oneHandleRelativeLambdaImage (k - 1) (k + 1)) :=
    oneHandleRelativeLambdaImageIsMulCommutative k hk
  letI : IsMulCommutative (OneHandleRelativeCModuloNeutral k hk) :=
    oneHandleRelativeCModuloNeutralIsMulCommutative k hk
  letI : Module (ZMod 4) (Additive (OneHandleBalancedCABDData k)) :=
    AddCommGroup.zmodModule (oneHandleBalancedCABDData_four_nsmul k hk)
  letI : Module (ZMod 4)
      (Additive (oneHandleRelativeZLayer k × OneHandleRelativeCModuloNeutral k hk)) :=
    AddCommGroup.zmodModule (oneHandleBalancedCABDTarget_four_nsmul k hk)
  exact Submodule.Quotient.mk
    (Additive.ofMul (1, oneHandleRelativeCModuloNeutralMk k hk x))

theorem oneHandleBalancedCABDZModFourObstruction_eq_zero_iff
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (x : oneHandleRelativeLambdaImage (k - 1) (k + 1)) :
    letI : IsMulCommutative
        (oneHandleRelativeLambdaImage (k - 1) (k + 1)) :=
      oneHandleRelativeLambdaImageIsMulCommutative k hk
    letI : IsMulCommutative (OneHandleRelativeCModuloNeutral k hk) :=
      oneHandleRelativeCModuloNeutralIsMulCommutative k hk
    letI : Module (ZMod 4) (Additive (OneHandleBalancedCABDData k)) :=
      AddCommGroup.zmodModule (oneHandleBalancedCABDData_four_nsmul k hk)
    letI : Module (ZMod 4)
        (Additive
          (oneHandleRelativeZLayer k × OneHandleRelativeCModuloNeutral k hk)) :=
      AddCommGroup.zmodModule (oneHandleBalancedCABDTarget_four_nsmul k hk)
    oneHandleBalancedCABDZModFourObstruction p k hk x = 0 ↔
      Additive.ofMul (1, oneHandleRelativeCModuloNeutralMk k hk x) ∈
        LinearMap.range (oneHandleBalancedCABDZModFourSystem p k hk) := by
  letI : IsMulCommutative
      (oneHandleRelativeLambdaImage (k - 1) (k + 1)) :=
    oneHandleRelativeLambdaImageIsMulCommutative k hk
  letI : IsMulCommutative (OneHandleRelativeCModuloNeutral k hk) :=
    oneHandleRelativeCModuloNeutralIsMulCommutative k hk
  letI : Module (ZMod 4) (Additive (OneHandleBalancedCABDData k)) :=
    AddCommGroup.zmodModule (oneHandleBalancedCABDData_four_nsmul k hk)
  letI : Module (ZMod 4)
      (Additive (oneHandleRelativeZLayer k × OneHandleRelativeCModuloNeutral k hk)) :=
    AddCommGroup.zmodModule (oneHandleBalancedCABDTarget_four_nsmul k hk)
  change Submodule.Quotient.mk
      (Additive.ofMul (1, oneHandleRelativeCModuloNeutralMk k hk x)) = 0 ↔ _
  exact Submodule.Quotient.mk_eq_zero _

theorem oneHandleBalancedCABDZModFourCokernel_finite
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    Finite (OneHandleBalancedCABDZModFourCokernel p k hk) := by
  letI : IsMulCommutative
      (oneHandleRelativeLambdaImage (k - 1) (k + 1)) :=
    oneHandleRelativeLambdaImageIsMulCommutative k hk
  letI : IsMulCommutative (OneHandleRelativeCModuloNeutral k hk) :=
    oneHandleRelativeCModuloNeutralIsMulCommutative k hk
  letI : Module (ZMod 4) (Additive (OneHandleBalancedCABDData k)) :=
    AddCommGroup.zmodModule (oneHandleBalancedCABDData_four_nsmul k hk)
  letI : Module (ZMod 4)
      (Additive (oneHandleRelativeZLayer k × OneHandleRelativeCModuloNeutral k hk)) :=
    AddCommGroup.zmodModule (oneHandleBalancedCABDTarget_four_nsmul k hk)
  exact Finite.of_surjective
    (Submodule.mkQ (LinearMap.range (oneHandleBalancedCABDZModFourSystem p k hk)))
    (Submodule.mkQ_surjective _)

theorem neutralityObstruction_eq_one_iff_CABDZModFourObstruction_eq_zero
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk)
    (x : oneHandleRelativeLambdaImage (k - 1) (k + 1))
    (hx : oneHandleBalancedCoreNeutralityClassHom p k hk x =
      oneHandleBalancedCoreNeutralityObstruction p hk hp hrel) :
    letI : IsMulCommutative
        (oneHandleRelativeLambdaImage (k - 1) (k + 1)) :=
      oneHandleRelativeLambdaImageIsMulCommutative k hk
    letI : IsMulCommutative (OneHandleRelativeCModuloNeutral k hk) :=
      oneHandleRelativeCModuloNeutralIsMulCommutative k hk
    letI : Module (ZMod 4) (Additive (OneHandleBalancedCABDData k)) :=
      AddCommGroup.zmodModule (oneHandleBalancedCABDData_four_nsmul k hk)
    letI : Module (ZMod 4)
        (Additive
          (oneHandleRelativeZLayer k × OneHandleRelativeCModuloNeutral k hk)) :=
      AddCommGroup.zmodModule (oneHandleBalancedCABDTarget_four_nsmul k hk)
    oneHandleBalancedCoreNeutralityObstruction p hk hp hrel = 1 ↔
      oneHandleBalancedCABDZModFourObstruction p k hk x = 0 := by
  letI : IsMulCommutative
      (oneHandleRelativeLambdaImage (k - 1) (k + 1)) :=
    oneHandleRelativeLambdaImageIsMulCommutative k hk
  letI : IsMulCommutative (OneHandleRelativeCModuloNeutral k hk) :=
    oneHandleRelativeCModuloNeutralIsMulCommutative k hk
  letI : Module (ZMod 4) (Additive (OneHandleBalancedCABDData k)) :=
    AddCommGroup.zmodModule (oneHandleBalancedCABDData_four_nsmul k hk)
  letI : Module (ZMod 4)
      (Additive (oneHandleRelativeZLayer k × OneHandleRelativeCModuloNeutral k hk)) :=
    AddCommGroup.zmodModule (oneHandleBalancedCABDTarget_four_nsmul k hk)
  rw [oneHandleBalancedCABDZModFourObstruction_eq_zero_iff]
  exact neutralityObstruction_eq_one_iff_mem_CABDZModFourSystem_range
    p hk hp hrel x hx

#print axioms OneHandleBalancedCABDZModFourCokernel
#print axioms oneHandleBalancedCABDZModFourObstruction
#print axioms oneHandleBalancedCABDZModFourObstruction_eq_zero_iff
#print axioms oneHandleBalancedCABDZModFourCokernel_finite
#print axioms neutralityObstruction_eq_one_iff_CABDZModFourObstruction_eq_zero

end
end GQ2.Dyadic.Instances.MpcBalancedNeutralityLinearCokernel

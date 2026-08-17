/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedNeutralityLinearSystem

/-!
# The CABD system over `ZMod 4`

W219 packages the remaining one-handle neutrality problem as a finite additive system.  Its
ordinary relative source is two two-central layers thick, so it has exponent dividing four;
the central defect row has exponent two, while the relative `C` class modulo exact neutral
classes still has exponent dividing four.  Thus the honest scalar ring is `ZMod 4`, not
`ZMod 2`.

This file installs the canonical local module structures, reinterprets the combined CABD row
as a `ZMod 4`-linear map, and restates the neutrality obstruction as membership of one explicit
vector in its linear range.  No rank or surjectivity assertion is made.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedNeutralityZModFour

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
open GQ2.Roe.Labute

open scoped IsMulCommutative

/-! ## Exponent bounds -/

theorem oneHandleRelativeLambdaImage_pow_four
    (k : ℕ) (hk : 3 ≤ k)
    (x : oneHandleRelativeLambdaImage (k - 1) (k + 1)) :
    x ^ 4 = 1 := by
  apply Subtype.ext
  change x.1 ^ 4 = 1
  obtain ⟨e, he, hex⟩ := x.2.1
  rw [← hex, ← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  have he2 := sq_mem_twoCentralSeries_succ (DM 2 1) he
  have he4 := sq_mem_twoCentralSeries_succ (DM 2 1) he2
  rw [show e ^ 4 = (e ^ 2) ^ 2 by group]
  simpa [show k - 1 + 1 + 1 = k + 1 by omega] using he4

theorem oneHandleRelativeLambdaImage_four_nsmul
    (k : ℕ) (hk : 3 ≤ k)
    (x : Additive (oneHandleRelativeLambdaImage (k - 1) (k + 1))) :
    4 • x = 0 := by
  change x.toMul ^ 4 = 1
  exact oneHandleRelativeLambdaImage_pow_four k hk x.toMul

theorem oneHandleRelativeCModuloNeutral_pow_four
    (k : ℕ) (hk : 3 ≤ k) (x : OneHandleRelativeCModuloNeutral k hk) :
    x ^ 4 = 1 := by
  obtain ⟨y, rfl⟩ := oneHandleRelativeCModuloNeutralMk_surjective k hk x
  rw [← map_pow, oneHandleRelativeLambdaImage_pow_four k hk, map_one]

theorem oneHandleRelativeCModuloNeutral_four_nsmul
    (k : ℕ) (hk : 3 ≤ k)
    (x : Additive (OneHandleRelativeCModuloNeutral k hk)) :
    4 • x = 0 := by
  change x.toMul ^ 4 = 1
  exact oneHandleRelativeCModuloNeutral_pow_four k hk x.toMul

theorem oneHandleRelativeZLayer_sq
    (k : ℕ) (x : oneHandleRelativeZLayer k) :
    x ^ 2 = 1 := by
  apply Subtype.ext
  exact zLayer_sq (DM 2 1) x.2.1

theorem oneHandleRelativeZLayer_pow_four
    (k : ℕ) (x : oneHandleRelativeZLayer k) :
    x ^ 4 = 1 := by
  rw [show x ^ 4 = (x ^ 2) ^ 2 by group,
    oneHandleRelativeZLayer_sq k x, one_pow]

theorem oneHandleBalancedCABDData_four_nsmul
    (k : ℕ) (hk : 3 ≤ k)
    (x : Additive (OneHandleBalancedCABDData k)) :
    4 • x = 0 := by
  change x.toMul ^ 4 = 1
  rcases x.toMul with ⟨c, a, b, d⟩
  change (c ^ 4, a ^ 4, b ^ 4, d ^ 4) = (1, 1, 1, 1)
  rw [oneHandleRelativeLambdaImage_pow_four k hk c,
    oneHandleRelativeLambdaImage_pow_four k hk a,
    oneHandleRelativeLambdaImage_pow_four k hk b,
    oneHandleRelativeLambdaImage_pow_four k hk d]

theorem oneHandleBalancedCABDTarget_four_nsmul
    (k : ℕ) (hk : 3 ≤ k)
    (x : Additive
      (oneHandleRelativeZLayer k × OneHandleRelativeCModuloNeutral k hk)) :
    4 • x = 0 := by
  change x.toMul ^ 4 = 1
  rcases x.toMul with ⟨z, c⟩
  change (z ^ 4, c ^ 4) = (1, 1)
  rw [oneHandleRelativeZLayer_pow_four k z,
    oneHandleRelativeCModuloNeutral_pow_four k hk c]

/-! ## The linear system -/

noncomputable def oneHandleBalancedCABDZModFourSystem
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
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
    Additive (OneHandleBalancedCABDData k) →ₗ[ZMod 4]
      Additive (oneHandleRelativeZLayer k × OneHandleRelativeCModuloNeutral k hk) := by
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
  exact (oneHandleBalancedCABDAddSystem p k hk).toZModLinearMap 4

theorem mem_oneHandleBalancedCABDZModFourSystem_range_iff
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
        (Additive (oneHandleRelativeZLayer k × OneHandleRelativeCModuloNeutral k hk)) :=
      AddCommGroup.zmodModule (oneHandleBalancedCABDTarget_four_nsmul k hk)
    Additive.ofMul (1, oneHandleRelativeCModuloNeutralMk k hk x) ∈
        LinearMap.range (oneHandleBalancedCABDZModFourSystem p k hk) ↔
      Additive.ofMul (1, oneHandleRelativeCModuloNeutralMk k hk x) ∈
        (oneHandleBalancedCABDAddSystem p k hk).range := by
  rfl

theorem neutralityObstruction_eq_one_iff_mem_CABDZModFourSystem_range
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
        (Additive (oneHandleRelativeZLayer k × OneHandleRelativeCModuloNeutral k hk)) :=
      AddCommGroup.zmodModule (oneHandleBalancedCABDTarget_four_nsmul k hk)
    oneHandleBalancedCoreNeutralityObstruction p hk hp hrel = 1 ↔
      Additive.ofMul (1, oneHandleRelativeCModuloNeutralMk k hk x) ∈
        LinearMap.range (oneHandleBalancedCABDZModFourSystem p k hk) := by
  rw [mem_oneHandleBalancedCABDZModFourSystem_range_iff]
  exact neutralityObstruction_eq_one_iff_mem_CABDAddSystem_range
    p hk hp hrel x hx

#print axioms oneHandleRelativeLambdaImage_pow_four
#print axioms oneHandleRelativeLambdaImage_four_nsmul
#print axioms oneHandleRelativeCModuloNeutral_pow_four
#print axioms oneHandleRelativeCModuloNeutral_four_nsmul
#print axioms oneHandleRelativeZLayer_sq
#print axioms oneHandleRelativeZLayer_pow_four
#print axioms oneHandleBalancedCABDData_four_nsmul
#print axioms oneHandleBalancedCABDTarget_four_nsmul
#print axioms oneHandleBalancedCABDZModFourSystem
#print axioms mem_oneHandleBalancedCABDZModFourSystem_range_iff
#print axioms neutralityObstruction_eq_one_iff_mem_CABDZModFourSystem_range

end
end GQ2.Dyadic.Instances.MpcBalancedNeutralityZModFour

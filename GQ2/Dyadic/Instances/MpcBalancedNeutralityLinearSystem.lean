/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedNeutralityAdditive

/-!
# The finite CABD system

W218 isolates the homogeneous CABD defect row.  The target-specific problem also remembers
the class of the `C` correction modulo genuinely neutral corrections.  This file combines
those two rows into one finite homomorphism.  Its additive range condition is exactly the
remaining neutrality obstruction.

No range or rank assertion is made.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedNeutralityLinearSystem

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
open GQ2.Dyadic.Instances.MpcBalancedNeutralityAdditive

/-! ## The class row and the combined system -/

/-- Project the `C` coordinate of CABD data to its class modulo neutral corrections. -/
noncomputable def oneHandleBalancedCABDClassRow
    (k : ℕ) (hk : 3 ≤ k) :
    OneHandleBalancedCABDData k →* OneHandleRelativeCModuloNeutral k hk where
  toFun t := oneHandleRelativeCModuloNeutralMk k hk t.1
  map_one' := map_one (oneHandleRelativeCModuloNeutralMk k hk)
  map_mul' x y := map_mul (oneHandleRelativeCModuloNeutralMk k hk) x.1 y.1

/-- The homogeneous CABD defect together with the inhomogeneous `C`-class row. -/
noncomputable def oneHandleBalancedCABDSystem
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    OneHandleBalancedCABDData k →*
      oneHandleRelativeZLayer k × OneHandleRelativeCModuloNeutral k hk :=
  (oneHandleBalancedCABDDefect p k hk).prod
    (oneHandleBalancedCABDClassRow k hk)

@[simp] theorem oneHandleBalancedCABDSystem_apply
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1)) :
    oneHandleBalancedCABDSystem p k hk (y, a, b, d) =
      (oneHandleBalancedCABDDefect p k hk (y, a, b, d),
        oneHandleRelativeCModuloNeutralMk k hk y) :=
  rfl

/-- Membership of the finite system target is the literal CABD equation with the prescribed
`C` class. -/
theorem mem_oneHandleBalancedCABDSystem_range_iff
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (x : oneHandleRelativeLambdaImage (k - 1) (k + 1)) :
    (1, oneHandleRelativeCModuloNeutralMk k hk x) ∈
        (oneHandleBalancedCABDSystem p k hk).range ↔
      ∃ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
        oneHandleRelativeCModuloNeutralMk k hk y =
            oneHandleRelativeCModuloNeutralMk k hk x ∧
          oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
            oneHandleBalancedCoreRelativeShiftA p k hk a *
              oneHandleBalancedCoreRelativeShiftB p k hk b *
                oneHandleBalancedCoreRelativeShiftD p k hk d := by
  constructor
  · rintro ⟨⟨y, a, b, d⟩, h⟩
    have hdef : oneHandleBalancedCABDDefect p k hk (y, a, b, d) = 1 := by
      simpa using congrArg Prod.fst h
    have hclass : oneHandleRelativeCModuloNeutralMk k hk y =
        oneHandleRelativeCModuloNeutralMk k hk x := by
      simpa using congrArg Prod.snd h
    exact ⟨y, a, b, d, hclass,
      (balancedCABD_eq_iff_defect_eq_one p k hk y a b d).mpr hdef⟩
  · rintro ⟨y, a, b, d, hclass, heq⟩
    refine ⟨(y, a, b, d), ?_⟩
    apply Prod.ext
    · simpa using (balancedCABD_eq_iff_defect_eq_one p k hk y a b d).mp heq
    · exact hclass

/-! ## Additive packaging -/

/-- The combined finite system under the multiplicative-to-additive type tag. -/
noncomputable def oneHandleBalancedCABDAddSystem
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    Additive (OneHandleBalancedCABDData k) →+
      Additive (oneHandleRelativeZLayer k × OneHandleRelativeCModuloNeutral k hk) :=
  (oneHandleBalancedCABDSystem p k hk).toAdditive

/-- The additive and multiplicative range formulations of the combined system agree. -/
theorem mem_oneHandleBalancedCABDAddSystem_range_iff
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (x : oneHandleRelativeLambdaImage (k - 1) (k + 1)) :
    Additive.ofMul (1, oneHandleRelativeCModuloNeutralMk k hk x) ∈
        (oneHandleBalancedCABDAddSystem p k hk).range ↔
      (1, oneHandleRelativeCModuloNeutralMk k hk x) ∈
        (oneHandleBalancedCABDSystem p k hk).range := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t.toMul, Additive.ofMul.injective ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨Additive.ofMul t, ht⟩

/-- The remaining neutrality obstruction is exactly membership of one explicit target in
the range of the finite additive CABD system. -/
theorem neutralityObstruction_eq_one_iff_mem_CABDAddSystem_range
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk)
    (x : oneHandleRelativeLambdaImage (k - 1) (k + 1))
    (hx : oneHandleBalancedCoreNeutralityClassHom p k hk x =
      oneHandleBalancedCoreNeutralityObstruction p hk hp hrel) :
    oneHandleBalancedCoreNeutralityObstruction p hk hp hrel = 1 ↔
      Additive.ofMul (1, oneHandleRelativeCModuloNeutralMk k hk x) ∈
        (oneHandleBalancedCABDAddSystem p k hk).range := by
  rw [mem_oneHandleBalancedCABDAddSystem_range_iff,
    mem_oneHandleBalancedCABDSystem_range_iff]
  exact neutralityObstruction_eq_one_iff_CABD p hk hp hrel x hx

#print axioms oneHandleBalancedCABDClassRow
#print axioms oneHandleBalancedCABDSystem
#print axioms oneHandleBalancedCABDSystem_apply
#print axioms mem_oneHandleBalancedCABDSystem_range_iff
#print axioms oneHandleBalancedCABDAddSystem
#print axioms mem_oneHandleBalancedCABDAddSystem_range_iff
#print axioms neutralityObstruction_eq_one_iff_mem_CABDAddSystem_range

end
end GQ2.Dyadic.Instances.MpcBalancedNeutralityLinearSystem

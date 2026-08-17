/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedNeutralityExpanded

/-!
# The additive CABD defect row

W217 exposes the remaining square-and-commutator equation.  This file packages the same
condition as the kernel of one homomorphism and then applies the multiplicative-to-additive
type tag.  It is the precise additive finite row for the next graded calculation.

No kernel-spanning result is asserted.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedNeutralityAdditive

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
open GQ2.Dyadic.Instances.MpcBalancedNeutralityExpanded

open scoped IsMulCommutative

/-- Four ordinary relative source rows, ordered `C,A,B,D`. -/
abbrev OneHandleBalancedCABDData (k : ℕ) :=
  oneHandleRelativeLambdaImage (k - 1) (k + 1) ×
  oneHandleRelativeLambdaImage (k - 1) (k + 1) ×
  oneHandleRelativeLambdaImage (k - 1) (k + 1) ×
  oneHandleRelativeLambdaImage (k - 1) (k + 1)

/-- The multiplicative defect `C * (A * B * D)⁻¹` of the four finite rows. -/
noncomputable def oneHandleBalancedCABDDefect
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    OneHandleBalancedCABDData k →* oneHandleRelativeZLayer k where
  toFun t := oneHandleBalancedCoreRelativeShiftCRelaxed p k hk t.1 *
    (oneHandleBalancedCoreRelativeShiftA p k hk t.2.1 *
      oneHandleBalancedCoreRelativeShiftB p k hk t.2.2.1 *
        oneHandleBalancedCoreRelativeShiftD p k hk t.2.2.2)⁻¹
  map_one' := by simp
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_inv_rev]
    ac_rfl

/-- The literal CABD equality is exactly vanishing of the multiplicative defect. -/
theorem balancedCABD_eq_iff_defect_eq_one
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1)) :
    oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
        oneHandleBalancedCoreRelativeShiftA p k hk a *
          oneHandleBalancedCoreRelativeShiftB p k hk b *
            oneHandleBalancedCoreRelativeShiftD p k hk d ↔
      oneHandleBalancedCABDDefect p k hk (y, a, b, d) = 1 := by
  change
    oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
        oneHandleBalancedCoreRelativeShiftA p k hk a *
          oneHandleBalancedCoreRelativeShiftB p k hk b *
            oneHandleBalancedCoreRelativeShiftD p k hk d ↔
      oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y *
          (oneHandleBalancedCoreRelativeShiftA p k hk a *
            oneHandleBalancedCoreRelativeShiftB p k hk b *
              oneHandleBalancedCoreRelativeShiftD p k hk d)⁻¹ = 1
  rw [mul_inv_eq_one]

/-- The same row as an additive homomorphism between additive type tags. -/
noncomputable def oneHandleBalancedCABDAddRow
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    Additive (OneHandleBalancedCABDData k) →+
      Additive (oneHandleRelativeZLayer k) :=
  (oneHandleBalancedCABDDefect p k hk).toAdditive

/-- The literal CABD equality is kernel membership for the additive finite row. -/
theorem balancedCABD_eq_iff_addRow_eq_zero
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1)) :
    oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
        oneHandleBalancedCoreRelativeShiftA p k hk a *
          oneHandleBalancedCoreRelativeShiftB p k hk b *
            oneHandleBalancedCoreRelativeShiftD p k hk d ↔
      oneHandleBalancedCABDAddRow p k hk (Additive.ofMul (y, a, b, d)) = 0 := by
  exact balancedCABD_eq_iff_defect_eq_one p k hk y a b d

/-- The exact additive subgroup of CABD solutions. -/
def oneHandleBalancedCABDAddKernel
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    AddSubgroup (Additive (OneHandleBalancedCABDData k)) :=
  (oneHandleBalancedCABDAddRow p k hk).ker

#print axioms OneHandleBalancedCABDData
#print axioms oneHandleBalancedCABDDefect
#print axioms balancedCABD_eq_iff_defect_eq_one
#print axioms oneHandleBalancedCABDAddRow
#print axioms balancedCABD_eq_iff_addRow_eq_zero
#print axioms oneHandleBalancedCABDAddKernel

end
end GQ2.Dyadic.Instances.MpcBalancedNeutralityAdditive

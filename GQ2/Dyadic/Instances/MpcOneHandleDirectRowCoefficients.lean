/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleDirectRowSpan

/-!
# Explicit coefficients for the direct one-handle target row

The abstract factor through the four-family coordinate target splits into four bidual
coefficients, one for each of the `A`, `B`, `C`, and `D` row families.  This file packages the
resulting pointwise scalar identity and proves that it is equivalent to row-span membership,
direct correction, and zero finrank jump.

All coefficient spaces are finite.  This is the direct scalar-search form of the remaining
one-handle problem; no coefficient tuple is constructed here.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleDirectRowCoefficients

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectTranspose
open GQ2.Dyadic.Instances.MpcOneHandleDirectAugmentedTranspose
open GQ2.Dyadic.Instances.MpcOneHandleDirectFinrank
open GQ2.Dyadic.Instances.MpcOneHandleDirectRowSpan
open GQ2.FoxH GQ2.Roe.Labute
open scoped IsMulCommutative

private abbrev H := DM 2 1

private abbrev DirectSource (k : ℕ) :=
  Additive (oneHandleDirectLambdaImage (k - 1) (k + 1))

private abbrev DirectNeutralSource (k : ℕ) :=
  Additive (oneHandleDirectNeutralLambdaImage (k - 1) (k + 1))

private abbrev DirectTransposeTarget (k : ℕ) :=
  (DirectSource k →+ ZMod 2) ×
    (DirectSource k →+ ZMod 2) ×
      (DirectNeutralSource k →+ ZMod 2) × (DirectSource k →+ ZMod 2)

private def rowCoefficientA {k : ℕ}
    (E : DirectTransposeTarget k →+ ZMod 2) :
    ((DirectSource k →+ ZMod 2) →+ ZMod 2) where
  toFun a := E (a, 0, 0, 0)
  map_zero' := E.map_zero
  map_add' a b := by
    simpa using E.map_add (a, 0, 0, 0) (b, 0, 0, 0)

private def rowCoefficientB {k : ℕ}
    (E : DirectTransposeTarget k →+ ZMod 2) :
    ((DirectSource k →+ ZMod 2) →+ ZMod 2) where
  toFun b := E (0, b, 0, 0)
  map_zero' := E.map_zero
  map_add' a b := by
    simpa using E.map_add (0, a, 0, 0) (0, b, 0, 0)

private def rowCoefficientC {k : ℕ}
    (E : DirectTransposeTarget k →+ ZMod 2) :
    ((DirectNeutralSource k →+ ZMod 2) →+ ZMod 2) where
  toFun c := E (0, 0, c, 0)
  map_zero' := E.map_zero
  map_add' a b := by
    simpa using E.map_add (0, 0, a, 0) (0, 0, b, 0)

private def rowCoefficientD {k : ℕ}
    (E : DirectTransposeTarget k →+ ZMod 2) :
    ((DirectSource k →+ ZMod 2) →+ ZMod 2) where
  toFun d := E (0, 0, 0, d)
  map_zero' := E.map_zero
  map_add' a b := by
    simpa using E.map_add (0, 0, 0, a) (0, 0, 0, b)

private theorem rowCoefficient_sum {k : ℕ}
    (E : DirectTransposeTarget k →+ ZMod 2)
    (x : DirectTransposeTarget k) :
    rowCoefficientA E x.1 + rowCoefficientB E x.2.1 +
        rowCoefficientC E x.2.2.1 + rowCoefficientD E x.2.2.2 = E x := by
  have hx : x = (x.1, 0, 0, 0) + (0, x.2.1, 0, 0) +
      (0, 0, x.2.2.1, 0) + (0, 0, 0, x.2.2.2) := by
    ext <;> simp
  calc
    _ = E (x.1, 0, 0, 0) + E (0, x.2.1, 0, 0) +
          E (0, 0, x.2.2.1, 0) + E (0, 0, 0, x.2.2.2) := rfl
    _ = E ((x.1, 0, 0, 0) + (0, x.2.1, 0, 0) +
          (0, 0, x.2.2.1, 0) + (0, 0, 0, x.2.2.2)) := by
      simp only [map_add]
    _ = E x := by rw [← hx]

private def rowCombination {k : ℕ}
    (eA eB eD : (DirectSource k →+ ZMod 2) →+ ZMod 2)
    (eC : (DirectNeutralSource k →+ ZMod 2) →+ ZMod 2) :
    DirectTransposeTarget k →+ ZMod 2 where
  toFun x := eA x.1 + eB x.2.1 + eC x.2.2.1 + eD x.2.2.2
  map_zero' := by simp
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel

def OneHandleDirectTargetRowCoefficients
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) : Prop :=
  ∃ eA eB eD : (DirectSource k →+ ZMod 2) →+ ZMod 2,
    ∃ eC : (DirectNeutralSource k →+ ZMod 2) →+ ZMod 2,
      ∀ ell : ElemDual (Additive (zLayer H k)),
        eA (oneHandleDirectCoordinateTranspose m k hk ell).1 +
            eB (oneHandleDirectCoordinateTranspose m k hk ell).2.1 +
            eC (oneHandleDirectCoordinateTranspose m k hk ell).2.2.1 +
            eD (oneHandleDirectCoordinateTranspose m k hk ell).2.2.2 =
          oneHandleDirectTargetEvaluation hm ell

theorem targetRowCoefficients_of_rowSpan
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k)
    (Hspan : OneHandleDirectTargetRowSpan hk hm) :
    OneHandleDirectTargetRowCoefficients hk hm := by
  obtain ⟨E, hE⟩ := Hspan
  refine ⟨rowCoefficientA E, rowCoefficientB E, rowCoefficientD E,
    rowCoefficientC E, fun ell => ?_⟩
  rw [rowCoefficient_sum]
  exact congrArg (fun f => f ell) hE

theorem targetRowSpan_of_rowCoefficients
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k)
    (Hcoeff : OneHandleDirectTargetRowCoefficients hk hm) :
    OneHandleDirectTargetRowSpan hk hm := by
  obtain ⟨eA, eB, eD, eC, hcoeff⟩ := Hcoeff
  refine ⟨rowCombination eA eB eD eC, ?_⟩
  ext ell
  exact hcoeff ell

theorem targetRowCoefficients_iff_rowSpan
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetRowCoefficients hk hm ↔
      OneHandleDirectTargetRowSpan hk hm :=
  ⟨targetRowSpan_of_rowCoefficients hk hm,
    targetRowCoefficients_of_rowSpan hk hm⟩

theorem targetRowCoefficients_iff_nonempty_directCorrection
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetRowCoefficients hk hm ↔
      Nonempty (OneHandleDirectCorrection m k) := by
  rw [targetRowCoefficients_iff_rowSpan hk hm,
    targetRowSpan_iff_nonempty_directCorrection hk hm]

theorem targetRowCoefficients_iff_no_finrank_jump
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetRowCoefficients hk hm ↔
      oneHandleDirectAugmentedTransposeRank hk hm =
        oneHandleDirectCoordinateTransposeRank m k hk := by
  rw [targetRowCoefficients_iff_rowSpan hk hm,
    targetRowSpan_iff_no_finrank_jump hk hm]

theorem directTargetTransposeDetected_iff_no_rowCoefficients
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetTransposeDetected hk hm ↔
      ¬ OneHandleDirectTargetRowCoefficients hk hm := by
  rw [directTargetTransposeDetected_iff_not_rowSpan hk hm,
    targetRowCoefficients_iff_rowSpan hk hm]

def OneHandleDirectTargetRowCoefficientSupply : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (m : Fin (coreRank 1) → H)
    (hm : m ∈ oneHandleDirectSet k),
      OneHandleDirectTargetRowCoefficients (by omega) hm

theorem targetRowCoefficientSupply_iff_correctionSupply :
    OneHandleDirectTargetRowCoefficientSupply ↔
      OneHandleDirectCorrectionSupply := by
  constructor <;> intro H k hk m hm
  · exact (targetRowCoefficients_iff_nonempty_directCorrection (by omega) hm).mp
      (H k hk m hm)
  · exact (targetRowCoefficients_iff_nonempty_directCorrection (by omega) hm).mpr
      (H k hk m hm)

theorem mpcPivShiftH_two_one_of_targetRowCoefficients
    (Hcoeff : OneHandleDirectTargetRowCoefficientSupply) : MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_direct_correctionSupply
    (targetRowCoefficientSupply_iff_correctionSupply.mp Hcoeff)

#print axioms OneHandleDirectTargetRowCoefficients
#print axioms targetRowCoefficients_of_rowSpan
#print axioms targetRowSpan_of_rowCoefficients
#print axioms targetRowCoefficients_iff_rowSpan
#print axioms targetRowCoefficients_iff_nonempty_directCorrection
#print axioms targetRowCoefficients_iff_no_finrank_jump
#print axioms directTargetTransposeDetected_iff_no_rowCoefficients
#print axioms OneHandleDirectTargetRowCoefficientSupply
#print axioms targetRowCoefficientSupply_iff_correctionSupply
#print axioms mpcPivShiftH_two_one_of_targetRowCoefficients

end
end GQ2.Dyadic.Instances.MpcOneHandleDirectRowCoefficients

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary
import GQ2.Dyadic.Instances.MpcFieldPivotFiltered
import GQ2.Dyadic.Instances.M0FamilyField

/-!
# The coordinate-free M-family pivot boundary

This module separates existence of an exact-level value in the cyclotomic kernel from its
placement on the distinguished `C` coordinate.  The former is intrinsic and holds for every
canonical selected M row.  The latter is exactly `MFieldCPivotAtLevel`, the sole M-family
condition left in the all-degree corrected-family dispatcher.

Consequently the outstanding M problem is not a list of nilpotency classes.  It is one
normal-form problem: move a mobile exact-level kernel value onto `C`, or replace the canonical
M normal form when that placement is impossible.  `MFieldPivotPlacementDefect` records the
precise failure of the present normal form.
-/

namespace GQ2.Dyadic.Instances.MFieldMobilePivotBoundary

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary
open GQ2.Dyadic.Instances.M0FamilyField
open GQ2.Dyadic.Instances.MpcFieldPivotFiltered
open GQ2.Dyadic.Instances.MpcGeneralHandleFamily

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-- The coordinate-free exact-level datum: the selected value occurs somewhere in the
cyclotomic kernel, without insisting that it occur on the distinguished `C` letter. -/
def MFieldMobilePivotAtLevel (B : MarkedRecip R K) (alpha r h : ℕ) : Prop :=
  ∃ e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)),
    ∃ x : (DM alpha h : Type), chiM alpha h x = 1 ∧
      ∃ gamma : ℤ_[2]ˣ,
        toAdd (nuUrKTwo B (e.1 x)) = (gamma : ℤ_[2]) * 2 ^ r

/-- Failure of the current canonical M normal form despite existence of an intrinsic exact
kernel value. -/
def MFieldPivotPlacementDefect (B : MarkedRecip R K) (alpha r h : ℕ) : Prop :=
  MFieldMobilePivotAtLevel B alpha r h ∧ ¬ MFieldCPivotAtLevel B alpha r h

omit [T2Space (GalK K)] in
theorem mFieldMobilePivotAtLevel_of_cPivot (B : MarkedRecip R K) {alpha r h : ℕ}
    (H : MFieldCPivotAtLevel B alpha r h) :
    MFieldMobilePivotAtLevel B alpha r h := by
  obtain ⟨e, gamma, hgamma⟩ := H
  exact ⟨e, dmC alpha h, chiM_dmC alpha h, gamma, hgamma⟩

omit [T2Space (GalK K)] in
theorem mFieldCPivotAtLevel_iff_not_placementDefect
    (B : MarkedRecip R K) {alpha r h : ℕ}
    (H : MFieldMobilePivotAtLevel B alpha r h) :
    MFieldCPivotAtLevel B alpha r h ↔
      ¬ MFieldPivotPlacementDefect B alpha r h := by
  constructor
  · intro hC hdefect
    exact hdefect.2 hC
  · intro hnot
    by_contra hC
    exact hnot ⟨H, hC⟩

omit [T2Space (GalK K)] in
theorem mFieldMobilePivotAtLevel_m0
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha) :
    MFieldMobilePivotAtLevel B alpha 0 (handleCount P (.M0 alpha)) := by
  obtain ⟨e⟩ := orientedEquivM_of_familySelection_of_matchesRange_m0
    B FF S hmatch hbranch
  have hr : B.r = 0 := by
    have hs := S.level_eq
    rw [hbranch] at hs
    exact hs.symm
  obtain ⟨x, hxchi, hxunit⟩ := mChiKerUnimodular_of_level_zero_general B hr e
  change IsUnit (toAdd (nuUrKTwo B (e.1 x))) at hxunit
  refine ⟨e, x, hxchi, hxunit.unit, ?_⟩
  rw [pow_zero, mul_one, hxunit.unit_spec]

omit [T2Space (GalK K)] in
theorem mFieldMobilePivotAtLevel_mpc
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta) :
    MFieldMobilePivotAtLevel B alpha r
      (handleCount P (.Mpc alpha r epsilon eta)) := by
  obtain ⟨e⟩ := orientedEquivM_of_familySelection_of_matchesRange_mpc
    B FF S hmatch hbranch
  have hr : B.r = r := by
    have hs := S.level_eq
    rw [hbranch] at hs
    exact hs.symm
  obtain ⟨x, hxchi, hx⟩ := exists_mpcExactKernelValue B hr e
  change toAdd (nuUrKTwo B (e.1 x)) = 2 ^ r at hx
  exact ⟨e, x, hxchi, 1, by simpa using hx⟩

/-- The coordinate-free M pivot exists on every canonical selected row. -/
def CanonicalMobilePivotBoundary (B : MarkedRecip R K)
    {P : FieldParameters} {FF : DyadicUnitFiltration K}
    {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W) : Prop :=
  match S.branch with
  | .M0 alpha => MFieldMobilePivotAtLevel B alpha 0 (handleCount P (.M0 alpha))
  | .Mpc alpha r epsilon eta =>
      MFieldMobilePivotAtLevel B alpha r (handleCount P (.Mpc alpha r epsilon eta))
  | _ => True

omit [T2Space (GalK K)] in
theorem canonicalMobilePivotBoundary_of_matchesRange
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange) :
    CanonicalMobilePivotBoundary B S := by
  generalize hbranch : S.branch = branch
  cases branch with
  | L =>
      rw [CanonicalMobilePivotBoundary, hbranch]
      trivial
  | N0 alpha =>
      rw [CanonicalMobilePivotBoundary, hbranch]
      trivial
  | Npc alpha r eta =>
      rw [CanonicalMobilePivotBoundary, hbranch]
      trivial
  | M0 alpha =>
      rw [CanonicalMobilePivotBoundary, hbranch]
      exact mFieldMobilePivotAtLevel_m0 B FF S hmatch hbranch
  | Mpc alpha r epsilon eta =>
      rw [CanonicalMobilePivotBoundary, hbranch]
      exact mFieldMobilePivotAtLevel_mpc B FF S hmatch hbranch

theorem canonicalMobilePivotBoundary_fieldSelectionFromRange
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K) :
    CanonicalMobilePivotBoundary B
      (selectFieldBranchFamilyFromRange B FF D RI) :=
  canonicalMobilePivotBoundary_of_matchesRange B FF
    (selectFieldBranchFamilyFromRange B FF D RI)
    (fieldFamilyWitnessFromRange_matchesCyclotomicRange B FF D RI)

#print axioms MFieldMobilePivotAtLevel
#print axioms MFieldPivotPlacementDefect
#print axioms mFieldMobilePivotAtLevel_of_cPivot
#print axioms mFieldCPivotAtLevel_iff_not_placementDefect
#print axioms mFieldMobilePivotAtLevel_m0
#print axioms mFieldMobilePivotAtLevel_mpc
#print axioms CanonicalMobilePivotBoundary
#print axioms canonicalMobilePivotBoundary_of_matchesRange
#print axioms canonicalMobilePivotBoundary_fieldSelectionFromRange

end

end GQ2.Dyadic.Instances.MFieldMobilePivotBoundary

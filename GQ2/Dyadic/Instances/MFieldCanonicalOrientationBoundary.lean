/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MFieldCanonicalMarkingTransitivity
import GQ2.Dyadic.Instances.MpcGeneralHandleRealization

/-!
# Characteristic orientation versus canonical M marking transitivity

This module tests W307's unrestricted marking-transitivity route against the expected
characteristic nature of the cyclotomic orientation.  Once one oriented field equivalence is
known, saying that every core automorphism preserves `chiM` is equivalent to saying that every
abstract field equivalence is oriented.  Under that rigidity, transitivity of all surjective
`Ztwo` markings is impossible whenever a handle is present.

The same rigidity also shows that W305's apparently weaker canonical-realization boundary
forces W303's exact distinguished-`C` pivot boundary, for compact M and procyclic M uniformly.
Thus the general campaign cannot consistently combine characteristic orientation with a
single unrestricted marking orbit.  It must instead prove the arithmetic pivot in its correct
invariant stratum or use an alternate M normal form centered on the mobile exact-level value.
-/

namespace GQ2.Dyadic.Instances.MFieldCanonicalOrientationBoundary

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.FieldBranchId
open GQ2.Dyadic.Instances.MFieldCanonicalMarkingTransitivity
open GQ2.Dyadic.Instances.MFieldCanonicalRealizationBoundary
open GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The canonical M orientation is characteristic under all core automorphisms. -/
def MCoreOrientationCharacteristic (alpha h : ℕ) : Prop :=
  ∀ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
    ∀ x, chiM alpha h (Psi x) = chiM alpha h x

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- Every abstract equivalence from the M core to the field pro-2 group preserves the
canonical cyclotomic orientation. -/
def MFieldOrientationRigidityAt (alpha h : ℕ) : Prop :=
  ∀ e : ContinuousMulEquiv (DM alpha h : Type)
      (maxProPQuotient 2 (GalK K)),
    OrientationMatches (chiM alpha h).toMonoidHom
      (chiCycKTwo (K := K)).toMonoidHom e

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- Once one oriented field equivalence exists, field orientation rigidity is equivalent to
the intrinsic statement that every core automorphism preserves `chiM`. -/
theorem mCoreOrientationCharacteristic_iff_fieldOrientationRigidityAt
    {alpha h : ℕ}
    (e0 : OrientedContinuousMulEquiv
      (chiM alpha h) (chiCycKTwo (K := K))) :
    MCoreOrientationCharacteristic alpha h ↔
      MFieldOrientationRigidityAt (K := K) alpha h := by
  constructor
  · intro H e x
    let Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type) :=
      e.trans e0.1.symm
    calc
      chiCycKTwo (K := K) (e x) =
          chiCycKTwo (K := K) (e0.1 (Psi x)) := by
            simp [Psi]
      _ = chiM alpha h (Psi x) := e0.2 (Psi x)
      _ = chiM alpha h x := H Psi x
  · intro H Psi x
    have hfield := H (Psi.trans e0.1) x
    calc
      chiM alpha h (Psi x) =
          chiCycKTwo (K := K) (e0.1 (Psi x)) := (e0.2 (Psi x)).symm
      _ = chiCycKTwo (K := K) ((Psi.trans e0.1) x) := rfl
      _ = chiM alpha h x := hfield

omit [T2Space (GalK K)] [CompactSpace AbsGalQ2]
  [TotallyDisconnectedSpace AbsGalQ2] in
/-- Characteristic orientation rules out transitivity of all surjective markings as soon as
a handle coordinate exists. -/
theorem not_mZtwoMarkingTransitivity_of_orientationCharacteristic
    {alpha h : ℕ} (halpha : 2 ≤ alpha) (j : Fin h)
    (Hchar : MCoreOrientationCharacteristic alpha h) :
    ¬ MZtwoMarkingTransitivity alpha h := by
  intro H
  apply not_mOrientedZtwoMarkingTransitivity halpha j
  intro nu1 nu2 hnu1 hnu2
  obtain ⟨Psi, hPsi⟩ := H nu1 nu2 hnu1 hnu2
  exact ⟨Psi, Hchar Psi, hPsi⟩

omit [T2Space (GalK K)] in
/-- Under field orientation rigidity, a canonical compact-M realization already forces the
old exact distinguished-`C` pivot. -/
theorem m0_cPivot_of_canonicalRealization_of_orientationRigidity
    (B : MarkedRecip R K) {alpha h : ℕ}
    (Hrigid : MFieldOrientationRigidityAt (K := K) alpha h)
    (H : M0CanonicalMarkedCoreRealization B alpha h) :
    MFieldCPivotAtLevel B alpha 0 h := by
  obtain ⟨halpha, ⟨M⟩⟩ := H
  let eM : OrientedContinuousMulEquiv
      (chiM alpha h) (chiCycKTwo (K := K)) :=
    ⟨M.equiv, Hrigid M.equiv⟩
  refine ⟨eM, 1, ?_⟩
  change toAdd (nuUrKTwo B (M.equiv (dmC alpha h))) = _
  have hm := M.nu_equiv (dmC alpha h)
  rw [fieldId_mNuZtwo_dmC, ztwoIota_ztwoOne] at hm
  rw [← hm, toAdd_ofAdd]
  norm_num

omit [T2Space (GalK K)] in
/-- The same rigidity turns a canonical procyclic-M realization into the exact level-`r`
distinguished-`C` pivot. -/
theorem mpc_cPivot_of_canonicalRealization_of_orientationRigidity
    (B : MarkedRecip R K) {alpha r h : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (Hrigid : MFieldOrientationRigidityAt (K := K) alpha h)
    (H : MpcCanonicalMarkedCoreRealization B alpha r h epsilon eta) :
    MFieldCPivotAtLevel B alpha r h := by
  obtain ⟨halpha, ⟨M⟩⟩ := H
  let eM : OrientedContinuousMulEquiv
      (chiM alpha h) (chiCycKTwo (K := K)) :=
    ⟨M.equiv, Hrigid M.equiv⟩
  refine ⟨eM, 1, ?_⟩
  change toAdd (nuUrKTwo B (M.equiv (dmC alpha h))) = _
  have hm := M.nu_equiv (dmC alpha h)
  change ztwoIota
      (ztwoIota.symm (mpcNuPadic alpha r (p epsilon r) h eta halpha
        (dmC alpha h))) = nuUrKTwo B (M.equiv (dmC alpha h)) at hm
  rw [ztwoIota.apply_symm_apply, dmC, mpcNuPadic_gen_two] at hm
  change toAdd (nuUrKTwo B (M.equiv (dmGen alpha h 2))) = _
  rw [← hm, toAdd_ofAdd]
  simp [s]

/-- Orientation rigidity only on the two unresolved selected M rows. -/
def EvenMFieldOrientationRigidityBoundary
    {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W) : Prop :=
  match S.branch with
  | .M0 alpha =>
      MFieldOrientationRigidityAt (K := K) alpha (handleCount P (.M0 alpha))
  | .Mpc alpha r false eta =>
      MFieldOrientationRigidityAt (K := K) alpha
        (handleCount P (.Mpc alpha r false eta))
  | _ => True

omit [T2Space (GalK K)] in
/-- Under the expected characteristic-orientation theorem, W305's realization boundary is no
weaker than W303's exact distinguished-`C` boundary. -/
theorem evenCanonicalMarkingBoundary_of_realization_of_orientationRigidity
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (Hrigid : EvenMFieldOrientationRigidityBoundary S)
    (Hreal : EvenCanonicalRealizationBoundary B S) :
    EvenCanonicalMarkingBoundary B S := by
  generalize hbranch : S.branch = branch
  cases branch with
  | L => rw [EvenCanonicalMarkingBoundary, hbranch]; trivial
  | N0 alpha => rw [EvenCanonicalMarkingBoundary, hbranch]; trivial
  | Npc alpha r eta => rw [EvenCanonicalMarkingBoundary, hbranch]; trivial
  | M0 alpha =>
      rw [EvenMFieldOrientationRigidityBoundary, hbranch] at Hrigid
      rw [EvenCanonicalRealizationBoundary, hbranch] at Hreal
      rw [EvenCanonicalMarkingBoundary, hbranch]
      exact m0_cPivot_of_canonicalRealization_of_orientationRigidity
        B Hrigid Hreal
  | Mpc alpha r epsilon eta =>
      cases epsilon with
      | false =>
          rw [EvenMFieldOrientationRigidityBoundary, hbranch] at Hrigid
          rw [EvenCanonicalRealizationBoundary, hbranch] at Hreal
          rw [EvenCanonicalMarkingBoundary, hbranch]
          exact mpc_cPivot_of_canonicalRealization_of_orientationRigidity
            B Hrigid Hreal
      | true => rw [EvenCanonicalMarkingBoundary, hbranch]; trivial

#print axioms MCoreOrientationCharacteristic
#print axioms MFieldOrientationRigidityAt
#print axioms mCoreOrientationCharacteristic_iff_fieldOrientationRigidityAt
#print axioms not_mZtwoMarkingTransitivity_of_orientationCharacteristic
#print axioms m0_cPivot_of_canonicalRealization_of_orientationRigidity
#print axioms mpc_cPivot_of_canonicalRealization_of_orientationRigidity
#print axioms EvenMFieldOrientationRigidityBoundary
#print axioms evenCanonicalMarkingBoundary_of_realization_of_orientationRigidity

end

end GQ2.Dyadic.Instances.MFieldCanonicalOrientationBoundary

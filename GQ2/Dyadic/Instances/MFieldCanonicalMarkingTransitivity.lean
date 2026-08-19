/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MFieldCanonicalMarkingOrbit
import GQ2.Dyadic.Instances.M0C0PivotAutomorphism

/-!
# A transitivity reduction for the canonical M marking orbit

W306 identifies the remaining even-family realization problem with an automorphism orbit of
the full `Ztwo` marking.  This module records the cleanest uniform sufficient condition: all
surjective `Ztwo` markings on `DM alpha h` lie in one automorphism orbit.  The field marking is
surjective, so this condition realizes both compact-M and procyclic-M canonical markings and
feeds the all-degree family dispatcher.

The stronger orientation-preserving formulation is false whenever `h > 0`.  A handle
coordinate is a surjective marking that vanishes on the distinguished `C` generator, whereas
the canonical compact-M marking is a unit there; the oriented `C`-pivot obstruction separates
their orbits.  Consequently a future proof cannot silently replace unrestricted transitivity
by oriented transitivity.  The honest next question is the invariant-stratified orbit problem
for unrestricted automorphisms, uniformly in `alpha` and `h`.
-/

namespace GQ2.Dyadic.Instances.MFieldCanonicalMarkingTransitivity

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.FieldBranchId
open GQ2.Dyadic.Instances.M0C0PivotAutomorphism
open GQ2.Dyadic.Instances.MFieldCanonicalMarkingOrbit
open GQ2.Dyadic.Instances.MFieldCanonicalRealizationBoundary
open GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The arithmetic unramified marking pulled back to an M core and written additively. -/
def mFieldTransportZ (B : MarkedRecip R K) {alpha h : ℕ}
    (e : ContinuousMulEquiv (DM alpha h : Type)
      (maxProPQuotient 2 (GalK K))) :
    ContinuousMonoidHom (DM alpha h : Type) Ztwo where
  toFun x := ztwoIota.symm (nuUrKTwo B (e x))
  map_one' := by simp
  map_mul' x y := by simp
  continuous_toFun := ztwoIota.symm.continuous_toFun.comp
    ((nuUrKTwo B).continuous_toFun.comp e.continuous_toFun)

omit [T2Space (GalK K)] [CompactSpace AbsGalQ2]
    [TotallyDisconnectedSpace AbsGalQ2] in
@[simp] theorem ztwoIota_mFieldTransportZ (B : MarkedRecip R K)
    {alpha h : ℕ}
    (e : ContinuousMulEquiv (DM alpha h : Type)
      (maxProPQuotient 2 (GalK K))) (x : DM alpha h) :
    ztwoIota (mFieldTransportZ B e x) = nuUrKTwo B (e x) :=
  ztwoIota.apply_symm_apply _

omit [T2Space (GalK K)] [CompactSpace AbsGalQ2]
    [TotallyDisconnectedSpace AbsGalQ2] in
/-- Pullback along a core equivalence preserves surjectivity of the field marking. -/
theorem mFieldTransportZ_surjective (B : MarkedRecip R K)
    (FF : DyadicUnitFiltration K) {alpha h : ℕ}
    (e : ContinuousMulEquiv (DM alpha h : Type)
      (maxProPQuotient 2 (GalK K))) :
    Function.Surjective (mFieldTransportZ B e) := by
  intro z
  obtain ⟨gbar, hgbar⟩ := B.nuUrSurjective FF (ztwoIota z)
  obtain ⟨g, rfl⟩ := surjective_toAbK K gbar
  refine ⟨e.symm (maxProPMk 2 (GalK K) g), ?_⟩
  apply ztwoIota.injective
  rw [ztwoIota_mFieldTransportZ, e.apply_symm_apply,
    nuUrKTwo_maxProPMk, hgbar]

/-- Transitivity of all surjective additive markings on one M core. -/
def MZtwoMarkingTransitivity (alpha h : ℕ) : Prop :=
  ∀ nu₁ nu₂ : ContinuousMonoidHom (DM alpha h : Type) Ztwo,
    Function.Surjective nu₁ → Function.Surjective nu₂ →
      ∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
        ∀ x, nu₁ (Psi x) = nu₂ x

omit [T2Space (GalK K)] [CompactSpace AbsGalQ2]
    [TotallyDisconnectedSpace AbsGalQ2] in
/-- Full marking transitivity implies the exact orbit needed by a realization. -/
theorem markedCoreMarkingOrbitAt_of_transitivity
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {alpha h : ℕ} (H : MZtwoMarkingTransitivity alpha h)
    (e : ContinuousMulEquiv (DM alpha h : Type)
      (maxProPQuotient 2 (GalK K)))
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hnuP : Function.Surjective nuP) :
    MarkedCoreMarkingOrbitAt B e nuP := by
  obtain ⟨Psi, hPsi⟩ := H (mFieldTransportZ B e) nuP
    (mFieldTransportZ_surjective B FF e) hnuP
  refine ⟨Psi, fun x => ?_⟩
  rw [← ztwoIota_mFieldTransportZ B e (Psi x), hPsi x]

omit [T2Space (GalK K)] in
/-- Full marking transitivity realizes every compact-M canonical marking. -/
theorem m0CanonicalMarkedCoreRealization_of_transitivity
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (H : MZtwoMarkingTransitivity alpha h)
    (e : ContinuousMulEquiv (DM alpha h : Type)
      (maxProPQuotient 2 (GalK K))) :
    M0CanonicalMarkedCoreRealization B alpha h := by
  refine (m0CanonicalMarkedCoreRealization_iff_markingOrbitAt
    B halpha e).2 ?_
  exact markedCoreMarkingOrbitAt_of_transitivity B FF H e
    (fieldId_mNuZtwo alpha h halpha)
    (fieldId_mNuZtwo_surjective alpha h halpha)

omit [T2Space (GalK K)] in
/-- Full marking transitivity realizes every procyclic-M canonical marking. -/
theorem mpcCanonicalMarkedCoreRealization_of_transitivity
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {alpha r h : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (halpha : 1 ≤ alpha) (H : MZtwoMarkingTransitivity alpha h)
    (e : ContinuousMulEquiv (DM alpha h : Type)
      (maxProPQuotient 2 (GalK K))) :
    MpcCanonicalMarkedCoreRealization B alpha r h epsilon eta := by
  refine (mpcCanonicalMarkedCoreRealization_iff_markingOrbitAt
    B halpha e).2 ?_
  exact markedCoreMarkingOrbitAt_of_transitivity B FF H e
    (mpcNu alpha r (p epsilon r) h eta halpha)
    (MpcGeneralHandleRealization.mpcNu_surjective
      alpha r (p epsilon r) h eta halpha)

/-- The general transitivity boundary, restricted to the two M rows not already closed by the
canonical family dispatcher. -/
def EvenMZtwoMarkingTransitivityBoundary
    {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W) : Prop :=
  match S.branch with
  | .M0 alpha => MZtwoMarkingTransitivity alpha (handleCount P (.M0 alpha))
  | .Mpc alpha r false eta =>
      MZtwoMarkingTransitivity alpha
        (handleCount P (.Mpc alpha r false eta))
  | _ => True

/-- The transitivity boundary implies W305's exact canonical-realization boundary. -/
theorem evenCanonicalRealizationBoundary_of_markingTransitivity
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    (H : EvenMZtwoMarkingTransitivityBoundary S) :
    EvenCanonicalRealizationBoundary B S := by
  generalize hbranch : S.branch = branch
  cases branch with
  | L => rw [EvenCanonicalRealizationBoundary, hbranch]; trivial
  | N0 alpha => rw [EvenCanonicalRealizationBoundary, hbranch]; trivial
  | Npc alpha r eta => rw [EvenCanonicalRealizationBoundary, hbranch]; trivial
  | M0 alpha =>
      rw [EvenMZtwoMarkingTransitivityBoundary, hbranch] at H
      rw [EvenCanonicalRealizationBoundary, hbranch]
      have halpha := S.valid
      rw [hbranch] at halpha
      obtain ⟨e⟩ := orientedEquivM_of_familySelection_of_matchesRange_m0
        B FF S hmatch hbranch
      exact m0CanonicalMarkedCoreRealization_of_transitivity
        B FF (le_trans (by omega) (BranchData.valid_M0_iff.mp halpha)) H e.1
  | Mpc alpha r epsilon eta =>
      cases epsilon with
      | false =>
          rw [EvenMZtwoMarkingTransitivityBoundary, hbranch] at H
          rw [EvenCanonicalRealizationBoundary, hbranch]
          have halpha := S.valid
          rw [hbranch] at halpha
          obtain ⟨e⟩ := orientedEquivM_of_familySelection_of_matchesRange_mpc
            B FF S hmatch hbranch
          exact mpcCanonicalMarkedCoreRealization_of_transitivity
            B FF (le_trans (by omega)
              (BranchData.valid_Mpc_iff.mp halpha).1) H e.1
      | true => rw [EvenCanonicalRealizationBoundary, hbranch]; trivial

/-- The all-degree corrected family dispatcher over the single general marking-transitivity
boundary. -/
theorem hasSelectedRowResidualRN_of_fieldSelectionFromRange_of_markingTransitivity
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (H : EvenMZtwoMarkingTransitivityBoundary
      (selectFieldBranchFamilyFromRange B FF D RI)) :
    HasSelectedRowResidualRN B FF
      (selectFieldBranchFamilyFromRange B FF D RI) := by
  let S := selectFieldBranchFamilyFromRange B FF D RI
  apply hasSelectedRowResidualRN_of_fieldSelectionFromRange_of_realizationBoundary
  exact evenCanonicalRealizationBoundary_of_markingTransitivity B FF S
    (fieldFamilyWitnessFromRange_matchesCyclotomicRange B FF D RI) H

/-- The stronger orientation-preserving version of marking transitivity. -/
def MOrientedZtwoMarkingTransitivity (alpha h : ℕ) : Prop :=
  ∀ nu₁ nu₂ : ContinuousMonoidHom (DM alpha h : Type) Ztwo,
    Function.Surjective nu₁ → Function.Surjective nu₂ →
      ∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
        (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
          ∀ x, nu₁ (Psi x) = nu₂ x

/-- A standard handle coordinate, as a multiplicative 2-adic character. -/
def mHandleCharacter (alpha : ℕ) {h : ℕ} (j : Fin h) :
    ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]) :=
  (mHHom alpha (mHandleCoordU j)).comp (mAbMkHom alpha h)

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
@[simp] theorem mHandleCharacter_gen (alpha : ℕ) {h : ℕ} (j : Fin h)
    (i : Fin (coreRank h)) :
    mHandleCharacter alpha j (dmGen alpha h i) =
      mHandleMark (mHandleCoordU j) (ofAdd (1 : ℤ_[2])) i := by
  change mHHom alpha (mHandleCoordU j)
    (mAbMkHom alpha h (dmGen alpha h i)) = _
  rw [mAbMkHom_apply, mHHom, mCoordHom_gen]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
@[simp] theorem mHandleCharacter_dmC (alpha : ℕ) {h : ℕ} (j : Fin h) :
    mHandleCharacter alpha j (dmC alpha h) = 1 := by
  rw [dmC, mHandleCharacter_gen, mHandleMark_core]
  rw [coreVal_two]
  omega

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
@[simp] theorem mHandleCharacter_handleU (alpha : ℕ) {h : ℕ} (j : Fin h) :
    mHandleCharacter alpha j (dmGen alpha h (handleIdxU j)) =
      ofAdd (1 : ℤ_[2]) := by
  rw [mHandleCharacter_gen, ← mHandleIdx_coordU, mHandleMark_self]

/-- The same handle coordinate with additive codomain. -/
def mHandleCharacterZ (alpha : ℕ) {h : ℕ} (j : Fin h) :
    ContinuousMonoidHom (DM alpha h : Type) Ztwo where
  toFun x := ztwoIota.symm (mHandleCharacter alpha j x)
  map_one' := by simp
  map_mul' x y := by simp
  continuous_toFun := ztwoIota.symm.continuous_toFun.comp
    (mHandleCharacter alpha j).continuous_toFun

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
@[simp] theorem ztwoIota_mHandleCharacterZ (alpha : ℕ) {h : ℕ}
    (j : Fin h) (x : DM alpha h) :
    ztwoIota (mHandleCharacterZ alpha j x) = mHandleCharacter alpha j x :=
  ztwoIota.apply_symm_apply _

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
theorem mHandleCharacterZ_surjective (alpha : ℕ) {h : ℕ} (j : Fin h) :
    Function.Surjective (mHandleCharacterZ alpha j) := by
  apply GQ2.Dyadic.Instances.NuWitness.surjective_of_ztwoOne_mem_range
  refine ⟨dmGen alpha h (handleIdxU j), ?_⟩
  apply ztwoIota.injective
  rw [ztwoIota_mHandleCharacterZ, mHandleCharacter_handleU,
    ztwoIota_ztwoOne]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- Already with one handle, orientation-preserving transitivity of all surjective markings is
false.  The handle marking vanishes at `C`, while the canonical compact-M marking is a unit
there, and oriented automorphisms preserve that parity. -/
theorem not_mOrientedZtwoMarkingTransitivity
    {alpha h : ℕ} (halpha : 2 ≤ alpha) (j : Fin h) :
    ¬ MOrientedZtwoMarkingTransitivity alpha h := by
  intro H
  obtain ⟨Psi, hchi, hmark⟩ := H
    (mHandleCharacterZ alpha j) (fieldId_mNuZtwo alpha h (by omega))
    (mHandleCharacterZ_surjective alpha j)
    (fieldId_mNuZtwo_surjective alpha h (by omega))
  have hunit : IsUnit (toAdd
      (mHandleCharacter alpha j (Psi (dmC alpha h)))) := by
    have hm := hmark (dmC alpha h)
    rw [fieldId_mNuZtwo_dmC] at hm
    have hm' := congrArg ztwoIota hm
    rw [ztwoIota_mHandleCharacterZ, ztwoIota_ztwoOne] at hm'
    rw [hm', toAdd_ofAdd]
    exact isUnit_one
  have hnot : ¬ IsUnit (toAdd (mHandleCharacter alpha j (dmC alpha h))) := by
    rw [mHandleCharacter_dmC, toAdd_one]
    exact not_isUnit_zero
  exact no_oriented_dmC_unitizer halpha (mHandleCharacter alpha j) hnot
    ⟨Psi, hchi, hunit⟩

#print axioms mFieldTransportZ
#print axioms mFieldTransportZ_surjective
#print axioms MZtwoMarkingTransitivity
#print axioms markedCoreMarkingOrbitAt_of_transitivity
#print axioms m0CanonicalMarkedCoreRealization_of_transitivity
#print axioms mpcCanonicalMarkedCoreRealization_of_transitivity
#print axioms EvenMZtwoMarkingTransitivityBoundary
#print axioms evenCanonicalRealizationBoundary_of_markingTransitivity
#print axioms
  hasSelectedRowResidualRN_of_fieldSelectionFromRange_of_markingTransitivity
#print axioms MOrientedZtwoMarkingTransitivity
#print axioms mHandleCharacterZ_surjective
#print axioms not_mOrientedZtwoMarkingTransitivity

end

end GQ2.Dyadic.Instances.MFieldCanonicalMarkingTransitivity

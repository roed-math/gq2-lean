/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.FieldFamilySelectionRangeFinal
import GQ2.Dyadic.Instances.M0FieldPivotInvariant
import GQ2.Dyadic.Instances.GammaLOddDegreeGrandAssembly
import GQ2.Dyadic.Instances.LRowCand
import GQ2.Dyadic.SqCore.GradedRowUniform

/-!
# The all-degree corrected family boundary

This module packages the corrected-RN campaign at its natural all-degree boundary.  It does
not enumerate nilpotency classes.  Starting with the family selection constructed from the
field's actual cyclotomic range, it realizes the selected displayed presentation and supplies
its corrected candidate certificate.

The odd L, N0, Npc, and epsilon-true Mpc rows close without another marking premise.  The two
remaining canonical M normal forms share one condition: the transported unramified character
must have exact selected level on the distinguished `C` coordinate.  At level zero this is
exactly `M0FieldPivotUnit`; at positive epsilon-false level it is the divided-C placement
problem.  `EvenCanonicalMarkingBoundary` records precisely these two cases and is `True` on
the other three even rows and on L.

Thus `hasSelectedRowResidualRN_of_fieldSelectionFromRange_of_boundary` is the uniform campaign
dispatcher.  Any future mobile-pivot or alternate-normal-form argument has a single interface
to discharge, simultaneously covering compact M and epsilon-false Mpc.
-/

namespace GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.M0FieldPivotInvariant
open GQ2.Dyadic.Instances.MpcGeneralHandleFamilyCanonical
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcGeneralTowerFinal
open GQ2.Dyadic.Instances.LRowCand

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The exact displayed presentation belonging to a family selection. -/
noncomputable def selectedPresentation
    {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W) :
    SelectedPresentation :=
  SelectedPresentation.ofBranch (handleCount P S.branch) S.branch S.display

/-- A family selection has been realized at its displayed presentation and carries the
corrected candidate certificate. -/
def HasSelectedRowResidualRN (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W) : Prop :=
  ∃ G : GenAsmBranch K B,
    G.pres = selectedPresentation S ∧
      Nonempty (GenAsmRowResidualRN (FF := FF) G)

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] [CompactSpace AbsGalQ2]
  [TotallyDisconnectedSpace AbsGalQ2] in
theorem selectedPresentation_eq_m0
    {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha) :
    selectedPresentation S = .M0 alpha (handleCount P (.M0 alpha)) := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      rfl

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] [CompactSpace AbsGalQ2]
  [TotallyDisconnectedSpace AbsGalQ2] in
theorem selectedPresentation_eq_mpc
    {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta) :
    let d : MpcDisplayFor eta :=
      Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
    selectedPresentation S = .Mpc alpha r epsilon d.display
      (handleCount P (.Mpc alpha r epsilon eta)) := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      rfl

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] [CompactSpace AbsGalQ2]
  [TotallyDisconnectedSpace AbsGalQ2] in
theorem selectedPresentation_eq_n0
    {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .N0 alpha) :
    selectedPresentation S = .N0 alpha (handleCount P (.N0 alpha)) := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      rfl

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] [CompactSpace AbsGalQ2]
  [TotallyDisconnectedSpace AbsGalQ2] in
theorem selectedPresentation_eq_npc
    {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Npc alpha r eta) :
    let d : NpcDisplayFor eta :=
      Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
    selectedPresentation S = .Npc alpha r
      (handleCount P (.Npc alpha r eta)) d.data := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      rfl

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] [CompactSpace AbsGalQ2]
  [TotallyDisconnectedSpace AbsGalQ2] in
theorem selectedPresentation_eq_l
    {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hbranch : S.branch = .L) :
    selectedPresentation S = .L (handleCount P .L) := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
      dsimp only at hbranch
      subst branch
      cases display
      rfl

/-- The common field-side condition behind the compact-M and procyclic-M canonical markings:
the distinguished `C` coordinate has exactly the selected `2`-adic level. -/
def MFieldCPivotAtLevel (B : MarkedRecip R K) (alpha r h : ℕ) : Prop :=
  ∃ e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)),
    ∃ gamma : ℤ_[2]ˣ,
      toAdd (nuUrKTwo B (e.1 (dmC alpha h))) = (gamma : ℤ_[2]) * 2 ^ r

/-- The only canonical-marking boundary left on the even selector.  N rows and epsilon-true
Mpc rows are already closed; compact M and epsilon-false Mpc retain the same exact-C condition
at levels zero and `r`, respectively. -/
def EvenCanonicalMarkingBoundary (B : MarkedRecip R K)
    {P : FieldParameters} {FF : DyadicUnitFiltration K}
    {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W) : Prop :=
  match S.branch with
  | .M0 alpha => MFieldCPivotAtLevel B alpha 0 (handleCount P (.M0 alpha))
  | .Mpc alpha r false eta =>
      MFieldCPivotAtLevel B alpha r (handleCount P (.Mpc alpha r false eta))
  | _ => True

omit [T2Space (GalK K)] [CompactSpace AbsGalQ2]
  [TotallyDisconnectedSpace AbsGalQ2] in
theorem mFieldCPivotAtLevel_zero_iff_m0FieldPivotUnit
    (B : MarkedRecip R K) {alpha h : ℕ} :
    MFieldCPivotAtLevel B alpha 0 h ↔ M0FieldPivotUnit B alpha h := by
  constructor
  · rintro ⟨e, gamma, hgamma⟩
    refine ⟨e, ?_⟩
    rw [pow_zero, mul_one] at hgamma
    rw [hgamma]
    exact gamma.isUnit
  · rintro ⟨e, he⟩
    refine ⟨e, he.unit, ?_⟩
    rw [pow_zero, mul_one, he.unit_spec]

omit [T2Space (GalK K)] in
theorem hasSelectedRowResidualRN_m0_of_cPivot
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha)
    (hpivot : MFieldCPivotAtLevel B alpha 0 (handleCount P (.M0 alpha))) :
    HasSelectedRowResidualRN B FF S := by
  obtain ⟨G, hG, hR⟩ := m0RowResidualRN_of_familySelection_of_fieldPivot
    B FF S hbranch
      ((mFieldCPivotAtLevel_zero_iff_m0FieldPivotUnit B).mp hpivot)
  refine ⟨G, ?_, hR⟩
  rw [selectedPresentation_eq_m0 S hbranch]
  exact hG

omit [T2Space (GalK K)] in
theorem hasSelectedRowResidualRN_mpc_of_cPivot
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta)
    (hpivot : MFieldCPivotAtLevel B alpha r
      (handleCount P (.Mpc alpha r epsilon eta))) :
    HasSelectedRowResidualRN B FF S := by
  obtain ⟨e, hpivot⟩ := hpivot
  obtain ⟨G, hG, hR⟩ := mpcRowResidualRN_of_familySelection_canonicalScaling
    B FF S hbranch e hpivot
  refine ⟨G, ?_, hR⟩
  rw [selectedPresentation_eq_mpc S hbranch]
  exact hG

theorem hasSelectedRowResidualRN_n0
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    {alpha : ℕ} (hbranch : S.branch = .N0 alpha) :
    HasSelectedRowResidualRN B FF S := by
  obtain ⟨G, hG, hR⟩ := n0RowResidualRN_of_familySelection_matchesRange
    B FF S hmatch hbranch
  refine ⟨G, ?_, hR⟩
  rw [selectedPresentation_eq_n0 S hbranch]
  exact hG

theorem hasSelectedRowResidualRN_npc
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Npc alpha r eta) :
    HasSelectedRowResidualRN B FF S := by
  obtain ⟨G, hG, hR⟩ := npcRowResidualRN_of_familySelection_matchesRange
    B FF S hmatch hbranch
  refine ⟨G, ?_, hR⟩
  rw [selectedPresentation_eq_npc S hbranch]
  exact hG

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
theorem mFieldCPivotAtLevel_mpc_true
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r true eta) :
    MFieldCPivotAtLevel B alpha r (handleCount P (.Mpc alpha r true eta)) := by
  obtain ⟨e⟩ := orientedEquivM_of_familySelection_of_matchesRange_mpc
    B FF S hmatch hbranch
  have halpha : 2 ≤ alpha := by
    have hv := S.valid
    rw [hbranch] at hv
    exact hv.1
  obtain ⟨_hr, _hrpos, e', hpivot⟩ :=
    mpc_familySelection_true_exists_exactPivot_of_shiftH B FF S hbranch e
      (mpcPivShiftH_all alpha (handleCount P (.Mpc alpha r true eta)) halpha)
  exact ⟨e', hpivot⟩

theorem hasSelectedRowResidualRN_l
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF)
    {W : FamilyFieldBranchWitness D.params (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K D.params (B.fieldMarkedPair FF) W)
    (hbranch : S.branch = .L) :
    HasSelectedRowResidualRN B FF S := by
  let h := handleCount D.params .L
  have hdeg : Module.finrank ℚ_[2] K = 2 * h + 1 := by
    have hd := S.degree_eq_field
    rw [hbranch] at hd
    exact hd.symm
  obtain ⟨f, horient, hsigma, hx0⟩ :=
    GQ2.Dyadic.SqCore.gUni_supply B FF hdeg
  let G : GenAsmBranch K B := lCandBranch h GQ2.Dyadic.SqCore.sqPivotExp hdeg
    ⟨f, horient⟩ (GQ2.Dyadic.SqCore.gOdd_pivotFix h) hsigma hx0
  have hfodd : Odd FF.f :=
    LSquare.odd_residueDegree_of_odd_finrank D (Nat.odd_iff.mpr (by omega))
  have hcert := LSquare.wordCertificateRN_lSq_qOf FF hfodd h
  refine ⟨G, ?_, ?_⟩
  · rw [selectedPresentation_eq_l S hbranch]
    rfl
  · exact ⟨⟨hcert⟩⟩

theorem hasSelectedRowResidualRN_of_evenBoundary
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange) (hnotL : S.branch ≠ .L)
    (hboundary : EvenCanonicalMarkingBoundary B S) :
    HasSelectedRowResidualRN B FF S := by
  generalize hbranch : S.branch = branch
  cases branch with
  | L => exact (hnotL hbranch).elim
  | N0 alpha => exact hasSelectedRowResidualRN_n0 B FF S hmatch hbranch
  | Npc alpha r eta => exact hasSelectedRowResidualRN_npc B FF S hmatch hbranch
  | M0 alpha =>
      rw [EvenCanonicalMarkingBoundary, hbranch] at hboundary
      exact hasSelectedRowResidualRN_m0_of_cPivot B FF S hbranch hboundary
  | Mpc alpha r epsilon eta =>
      cases epsilon with
      | false =>
          rw [EvenCanonicalMarkingBoundary, hbranch] at hboundary
          exact hasSelectedRowResidualRN_mpc_of_cPivot B FF S hbranch hboundary
      | true =>
          exact hasSelectedRowResidualRN_mpc_of_cPivot B FF S hbranch
            (mFieldCPivotAtLevel_mpc_true B FF S hmatch hbranch)

/-- The all-degree corrected-family dispatcher.  Its single premise is definitionally trivial
on L, N0, Npc, and epsilon-true Mpc.  It retains exactly the common distinguished-C placement
condition on compact M and epsilon-false Mpc. -/
theorem hasSelectedRowResidualRN_of_fieldSelectionFromRange_of_boundary
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (hboundary : EvenCanonicalMarkingBoundary B
      (selectFieldBranchFamilyFromRange B FF D RI)) :
    HasSelectedRowResidualRN B FF
      (selectFieldBranchFamilyFromRange B FF D RI) := by
  let S := selectFieldBranchFamilyFromRange B FF D RI
  have hmatch := fieldFamilyWitnessFromRange_matchesCyclotomicRange B FF D RI
  generalize hbranch : S.branch = branch
  cases branch with
  | L => exact hasSelectedRowResidualRN_l B FF D S hbranch
  | N0 alpha =>
      exact hasSelectedRowResidualRN_of_evenBoundary B FF S hmatch
        (by rw [hbranch]; intro h; cases h) hboundary
  | Npc alpha r eta =>
      exact hasSelectedRowResidualRN_of_evenBoundary B FF S hmatch
        (by rw [hbranch]; intro h; cases h) hboundary
  | M0 alpha =>
      exact hasSelectedRowResidualRN_of_evenBoundary B FF S hmatch
        (by rw [hbranch]; intro h; cases h) hboundary
  | Mpc alpha r epsilon eta =>
      exact hasSelectedRowResidualRN_of_evenBoundary B FF S hmatch
        (by rw [hbranch]; intro h; cases h) hboundary

#print axioms selectedPresentation
#print axioms HasSelectedRowResidualRN
#print axioms selectedPresentation_eq_m0
#print axioms selectedPresentation_eq_mpc
#print axioms selectedPresentation_eq_n0
#print axioms selectedPresentation_eq_npc
#print axioms selectedPresentation_eq_l
#print axioms MFieldCPivotAtLevel
#print axioms EvenCanonicalMarkingBoundary
#print axioms mFieldCPivotAtLevel_zero_iff_m0FieldPivotUnit
#print axioms hasSelectedRowResidualRN_m0_of_cPivot
#print axioms hasSelectedRowResidualRN_mpc_of_cPivot
#print axioms hasSelectedRowResidualRN_n0
#print axioms hasSelectedRowResidualRN_npc
#print axioms mFieldCPivotAtLevel_mpc_true
#print axioms hasSelectedRowResidualRN_of_evenBoundary
#print axioms hasSelectedRowResidualRN_l
#print axioms hasSelectedRowResidualRN_of_fieldSelectionFromRange_of_boundary

end

end GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary

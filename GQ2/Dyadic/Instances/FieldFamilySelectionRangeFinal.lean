/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.FieldFamilyWitnessFromRange

/-!
# Carrying the actual cyclotomic range through family selection

`FieldFamilyWitnessFromRange` eliminates the caller-supplied family witness.  This module keeps
the range identity as a proved invariant of that witness and feeds it directly to the general
oriented-presentation and corrected-RN consumers.

For N0, Npc, and epsilon-true Mpc, a branch equality for the canonical all-degree selection now
suffices: there is no separate `-1` exclusion, adjacent-depth test, oriented equivalence, pivot,
or determinant argument.  The M0 orientation is also automatic; its intrinsic field pivot is a
separate downstream arithmetic question.  No class or handle count is fixed here.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.EvenParity
open GQ2.Dyadic.Instances.N0FamilyFinal
open GQ2.Dyadic.Instances.NpcPlanePrimitiveField
open GQ2.Dyadic.Instances.MpcGeneralTowerFinal

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-- A corrected witness matches the actual cyclotomic range on its even family. -/
def FamilyFieldBranchWitness.MatchesCyclotomicRange
    {P : FieldParameters} {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}
    (W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)) : Prop :=
  match W with
  | .L .. => True
  | .M alpha .. =>
      MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha
  | .N alpha .. =>
      MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha

/-- The witness constructed from the actual range carries the corresponding range identity. -/
theorem fieldFamilyWitnessFromRange_matchesCyclotomicRange
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K) :
    (fieldFamilyWitnessFromRange B FF D RI).MatchesCyclotomicRange := by
  unfold fieldFamilyWitnessFromRange
  split
  · unfold evenDegreeFamilyFieldBranchWitness
    dsimp only
    split
    · rename_i hM
      exact hM
    · rename_i hM
      exact (Classical.choose_spec
        (EvenCyclotomicRange.evenRange_range_eq B RI.deltaI RI.sq_deltaI
          RI.ramified)).2.resolve_left hM
  · trivial

omit [T2Space (GalK K)] in
/-- An N selection over a range-matching witness carries the actual N range. -/
theorem range_eq_imChiN_of_familySelection_of_matchesRange
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    {alpha : ℕ} (hfamily : S.branch.labuteType = .N alpha) :
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha := by
  rw [S.family_eq] at hfamily
  cases W with
  | L => simp [FamilyFieldBranchWitness.family] at hfamily
  | M beta => simp [FamilyFieldBranchWitness.family] at hfamily
  | N beta hbeta heven marked =>
      simp [FamilyFieldBranchWitness.family] at hfamily
      subst beta
      exact hmatch

omit [T2Space (GalK K)] in
/-- An M selection over a range-matching witness carries the actual M range. -/
theorem range_eq_imChiM_of_familySelection_of_matchesRange
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    {alpha : ℕ} (hfamily : S.branch.labuteType = .M alpha) :
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha := by
  rw [S.family_eq] at hfamily
  cases W with
  | L => simp [FamilyFieldBranchWitness.family] at hfamily
  | N beta => simp [FamilyFieldBranchWitness.family] at hfamily
  | M beta hbeta heven marked =>
      simp [FamilyFieldBranchWitness.family] at hfamily
      subst beta
      exact hmatch

/-- The selected N0 orientation follows directly from its carried range. -/
theorem orientedEquivN_of_familySelection_of_matchesRange_n0
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    {alpha : ℕ} (hbranch : S.branch = .N0 alpha) :
    Nonempty (OrientedContinuousMulEquiv
      (chiN alpha (handleCount P (.N0 alpha))) (chiCycKTwo (K := K))) := by
  have hrange := range_eq_imChiN_of_familySelection_of_matchesRange B FF S hmatch
    (by rw [hbranch]; rfl)
  have halpha := S.valid
  rw [hbranch] at halpha
  have hdeg := S.degree_eq_field
  rw [hbranch] at hdeg
  exact parityFinal_orientedEquivN_of_range halpha hrange hdeg.symm

/-- The selected Npc orientation follows directly from its carried range. -/
theorem orientedEquivN_of_familySelection_of_matchesRange_npc
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ} (hbranch : S.branch = .Npc alpha r eta) :
    Nonempty (OrientedContinuousMulEquiv
      (chiN alpha (handleCount P (.Npc alpha r eta))) (chiCycKTwo (K := K))) := by
  have hrange := range_eq_imChiN_of_familySelection_of_matchesRange B FF S hmatch
    (by rw [hbranch]; rfl)
  have halpha := S.valid
  rw [hbranch] at halpha
  have hdeg := S.degree_eq_field
  rw [hbranch] at hdeg
  exact parityFinal_orientedEquivN_of_range halpha.1 hrange hdeg.symm

/-- The selected M0 orientation follows directly from its carried range. -/
theorem orientedEquivM_of_familySelection_of_matchesRange_m0
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha) :
    Nonempty (OrientedContinuousMulEquiv
      (chiM alpha (handleCount P (.M0 alpha))) (chiCycKTwo (K := K))) := by
  have hrange := range_eq_imChiM_of_familySelection_of_matchesRange B FF S hmatch
    (by rw [hbranch]; rfl)
  have halpha := S.valid
  rw [hbranch] at halpha
  have hdeg := S.degree_eq_field
  rw [hbranch] at hdeg
  exact parityFinal_orientedEquivM_of_range halpha hrange hdeg.symm

/-- The selected Mpc orientation follows directly from its carried range. -/
theorem orientedEquivM_of_familySelection_of_matchesRange_mpc
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta) :
    Nonempty (OrientedContinuousMulEquiv
      (chiM alpha (handleCount P (.Mpc alpha r epsilon eta)))
        (chiCycKTwo (K := K))) := by
  have hrange := range_eq_imChiM_of_familySelection_of_matchesRange B FF S hmatch
    (by rw [hbranch]; rfl)
  have halpha := S.valid
  rw [hbranch] at halpha
  have hdeg := S.degree_eq_field
  rw [hbranch] at hdeg
  exact parityFinal_orientedEquivM_of_range halpha.1 hrange hdeg.symm

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The N0 corrected residual over any range-matching selection. -/
theorem n0RowResidualRN_of_familySelection_matchesRange
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    {alpha : ℕ} (hbranch : S.branch = .N0 alpha) :
    ∃ G : GenAsmBranch K B,
      G.pres = .N0 alpha (handleCount P (.N0 alpha)) ∧
        Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  obtain ⟨e⟩ := orientedEquivN_of_familySelection_of_matchesRange_n0
    B FF S hmatch hbranch
  exact n0RowResidualRN_of_familySelection B FF S hbranch e

/-- The Npc corrected residual over any range-matching selection. -/
theorem npcRowResidualRN_of_familySelection_matchesRange
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ} (hbranch : S.branch = .Npc alpha r eta) :
    let d : NpcDisplayFor eta :=
      Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
    ∃ G : GenAsmBranch K B,
      G.pres = .Npc alpha r (handleCount P (.Npc alpha r eta)) d.data ∧
        Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  obtain ⟨e⟩ := orientedEquivN_of_familySelection_of_matchesRange_npc
    B FF S hmatch hbranch
  exact npcRowResidualRN_of_familySelection_exactLevel B FF S hbranch e

/-- The epsilon-true Mpc corrected residual over any range-matching selection. -/
theorem mpcRowResidualRN_of_familySelection_true_matchesRange
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r true eta) :
    let d : MpcDisplayFor eta :=
      Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
    ∃ G : GenAsmBranch K B,
      G.pres = .Mpc alpha r true d.display
        (handleCount P (.Mpc alpha r true eta)) ∧
      Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  exact mpcRowResidualRN_of_familySelection_true B FF S hbranch
    (orientedEquivM_of_familySelection_of_matchesRange_mpc B FF S hmatch hbranch)

/-- The canonical all-degree selection closes N0 from its branch equality alone. -/
theorem n0RowResidualRN_of_fieldSelectionFromRange
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    {alpha : ℕ}
    (hbranch : (selectFieldBranchFamilyFromRange B FF D RI).branch = .N0 alpha) :
    ∃ G : GenAsmBranch K B,
      G.pres = .N0 alpha (handleCount D.params (.N0 alpha)) ∧
        Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  exact n0RowResidualRN_of_familySelection_matchesRange B FF
    (selectFieldBranchFamilyFromRange B FF D RI)
    (fieldFamilyWitnessFromRange_matchesCyclotomicRange B FF D RI) hbranch

/-- The canonical all-degree selection closes Npc from its branch equality alone. -/
theorem npcRowResidualRN_of_fieldSelectionFromRange
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : (selectFieldBranchFamilyFromRange B FF D RI).branch =
      .Npc alpha r eta) :
    let S := selectFieldBranchFamilyFromRange B FF D RI
    let d : NpcDisplayFor eta :=
      Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
    ∃ G : GenAsmBranch K B,
      G.pres = .Npc alpha r (handleCount D.params (.Npc alpha r eta)) d.data ∧
        Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  exact npcRowResidualRN_of_familySelection_matchesRange B FF
    (selectFieldBranchFamilyFromRange B FF D RI)
    (fieldFamilyWitnessFromRange_matchesCyclotomicRange B FF D RI) hbranch

/-- The canonical all-degree selection closes epsilon-true Mpc from its branch equality alone. -/
theorem mpcRowResidualRN_of_fieldSelectionFromRange_true
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : (selectFieldBranchFamilyFromRange B FF D RI).branch =
      .Mpc alpha r true eta) :
    let S := selectFieldBranchFamilyFromRange B FF D RI
    let d : MpcDisplayFor eta :=
      Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
    ∃ G : GenAsmBranch K B,
      G.pres = .Mpc alpha r true d.display
        (handleCount D.params (.Mpc alpha r true eta)) ∧
      Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  exact mpcRowResidualRN_of_familySelection_true_matchesRange B FF
    (selectFieldBranchFamilyFromRange B FF D RI)
    (fieldFamilyWitnessFromRange_matchesCyclotomicRange B FF D RI) hbranch

#print axioms FamilyFieldBranchWitness.MatchesCyclotomicRange
#print axioms fieldFamilyWitnessFromRange_matchesCyclotomicRange
#print axioms range_eq_imChiN_of_familySelection_of_matchesRange
#print axioms range_eq_imChiM_of_familySelection_of_matchesRange
#print axioms orientedEquivN_of_familySelection_of_matchesRange_n0
#print axioms orientedEquivN_of_familySelection_of_matchesRange_npc
#print axioms orientedEquivM_of_familySelection_of_matchesRange_m0
#print axioms orientedEquivM_of_familySelection_of_matchesRange_mpc
#print axioms n0RowResidualRN_of_familySelection_matchesRange
#print axioms npcRowResidualRN_of_familySelection_matchesRange
#print axioms mpcRowResidualRN_of_familySelection_true_matchesRange
#print axioms n0RowResidualRN_of_fieldSelectionFromRange
#print axioms npcRowResidualRN_of_fieldSelectionFromRange
#print axioms mpcRowResidualRN_of_fieldSelectionFromRange_true

end

end GQ2.Dyadic

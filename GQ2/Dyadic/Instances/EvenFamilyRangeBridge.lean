/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.EvenParityModel
import GQ2.Dyadic.Instances.N0FamilyFinal
import GQ2.Dyadic.Instances.NpcPlanePrimitiveField
import GQ2.Dyadic.Instances.MpcGeneralTowerFinal

/-!
# From family selectors to the actual even cyclotomic range

The family selector records enough marked rows to choose the five presentation words, but its
family parameter is not definitionally tied to the actual cyclotomic image.  This module gives
the small, uniform bridge.

On the N side, membership of `nUnit alpha` and exclusion of `-1` force the actual range to be
`imChiN alpha`; depth rigidity does the rest.  On the M side, the marked rows force an actual
M depth no greater than the selected depth.  Depth two is automatically exact, and at larger
depth one additional test---absence of the immediately shallower `mUnit`---forces equality.

The resulting range identities feed the general even classification.  The final wrappers remove
the explicit oriented-equivalence premise from the selected N0, Npc, and epsilon-true Mpc
corrected-RN consumers.  No nilpotency class or fixed handle count occurs here.
-/

namespace GQ2.Dyadic.Instances.EvenFamilyRangeBridge

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.EvenCyclotomicRange
open GQ2.Dyadic.EvenParity
open GQ2.Dyadic.EvenRouteWitness
open GQ2.Dyadic.Instances.N0FamilyFinal
open GQ2.Dyadic.Instances.NpcCertificateLevel
open GQ2.Dyadic.Instances.NpcPlanePrimitiveField
open GQ2.Dyadic.Instances.MpcGeneralHandleFamily
open GQ2.Dyadic.Instances.MpcGeneralTowerFinal

local notation "Qbar2" => AlgebraicClosure ℚ_[2]

/-- The selected M depth is sharp when it is the first possible depth: at depth two this is
automatic, and afterwards it is detected by absence of the immediately shallower standard
orientation value. -/
def MFamilyDepthSharp {A : Type*} [CommGroup A] (Q : MarkedPair A) (alpha : ℕ) : Prop :=
  alpha = 2 ∨ mUnit (alpha - 1) ∉ Q.C

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] Qbar2} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

omit [T2Space (GalK K)] in
/-- A product-family marked row, together with one sharp-depth test, identifies the actual
cyclotomic range with the selected M range. -/
theorem range_eq_imChiM_of_marked_sharp
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) {alpha : ℕ}
    (halpha : 2 ≤ alpha)
    (hneg : (-1 : ℤ_[2]ˣ) ∈ (B.fieldMarkedPair FF).C)
    (hunit : mUnit alpha ∈ (B.fieldMarkedPair FF).C)
    (hsharp : MFamilyDepthSharp (B.fieldMarkedPair FF) alpha) :
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha := by
  have hC := GQ2.Dyadic.LSquare.range_chiCycKTwo_eq_fieldMarkedPairC K B FF
  have hneg' : (-1 : ℤ_[2]ˣ) ∈
      MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom := by
    rw [hC]
    exact hneg
  obtain ⟨beta, hbeta, hrange⟩ := evenRange_range_eq_imChiM B hneg'
  have hunit' : mUnit alpha ∈ imChiM beta := by
    rw [← hrange, hC]
    exact hunit
  have hle : beta ≤ alpha := by
    by_contra hnot
    exact GQ2.Dyadic.EvenRouteCarried.evenRouteCarried_mUnit_not_mem_imChiM
      halpha (by omega) hunit'
  have heq : beta = alpha := by
    rcases hsharp with rfl | hsharp
    · omega
    · by_contra hne
      have hmem : mUnit (alpha - 1) ∈ imChiM beta :=
        evenRouteWitness_mUnit_mem_imChiM hbeta (by omega)
      apply hsharp
      rw [← hC, hrange]
      exact hmem
  simpa [heq] using hrange

omit [T2Space (GalK K)] in
/-- The adjacent-depth test is exact: under the selected M rows, it is equivalent to the
selected depth being the actual cyclotomic depth. -/
theorem range_eq_imChiM_iff_marked_sharp
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) {alpha : ℕ}
    (halpha : 2 ≤ alpha)
    (hneg : (-1 : ℤ_[2]ˣ) ∈ (B.fieldMarkedPair FF).C)
    (hunit : mUnit alpha ∈ (B.fieldMarkedPair FF).C) :
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha ↔
      MFamilyDepthSharp (B.fieldMarkedPair FF) alpha := by
  constructor
  · intro hrange
    by_cases halpha2 : alpha = 2
    · exact Or.inl halpha2
    · right
      intro hmem
      have hdeep : mUnit (alpha - 1) ∈ imChiM alpha := by
        rw [← hrange,
          GQ2.Dyadic.LSquare.range_chiCycKTwo_eq_fieldMarkedPairC K B FF]
        exact hmem
      exact GQ2.Dyadic.EvenRouteCarried.evenRouteCarried_mUnit_not_mem_imChiM
        (alpha := alpha - 1) (beta := alpha) (by omega) (by omega) hdeep
  · exact range_eq_imChiM_of_marked_sharp B FF halpha hneg hunit

omit [T2Space (GalK K)] in
/-- A procyclic-family marked row identifies the actual N depth once the intrinsic branch
separator `-1 notin range(chi)` is known. -/
theorem range_eq_imChiN_of_marked
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) {alpha : ℕ}
    (halpha : 2 ≤ alpha)
    (hunit : nUnit alpha ∈ (B.fieldMarkedPair FF).C)
    (hneg : (-1 : ℤ_[2]ˣ) ∉ (B.fieldMarkedPair FF).C) :
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha := by
  have hC := GQ2.Dyadic.LSquare.range_chiCycKTwo_eq_fieldMarkedPairC K B FF
  have hneg' : (-1 : ℤ_[2]ˣ) ∉
      MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom := by
    rwa [hC]
  have hfour : ¬ ((2 : ℤ_[2]) ^ 2 ∣ ((nUnit alpha : ℤ_[2]ˣ) : ℤ_[2]) - 1) := by
    intro hdvd
    have hone := evenRange_toZModPow_eq_one_iff.mpr hdvd
    have hnegOne := MarkedGeneratorData.nUnit_toZModPow_two halpha
    rw [hnegOne] at hone
    exact (by decide : (-1 : ZMod (2 ^ 2)) ≠ 1) hone
  obtain ⟨beta, hbeta, hrange⟩ :=
    evenRange_eq_imChiN_of_neg_one_notMem
      (MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
      evenRange_isClosed_range (evenRange_prin_le_range B) hneg'
      ⟨nUnit alpha, by rwa [hC], hfour⟩
  have hunit' : nUnit alpha ∈ imChiN beta := by
    rw [← hrange, hC]
    exact hunit
  have heq : alpha = beta :=
    evenRouteWitness_nUnit_mem_imChiN halpha hbeta hunit'
  simpa [heq] using hrange

omit [T2Space (GalK K)] in
/-- Under the selected N row, exclusion of `-1` is exactly equivalent to the selected N depth
being the actual cyclotomic depth. -/
theorem range_eq_imChiN_iff_neg_one_notMem
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) {alpha : ℕ}
    (halpha : 2 ≤ alpha)
    (hunit : nUnit alpha ∈ (B.fieldMarkedPair FF).C) :
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha ↔
      (-1 : ℤ_[2]ˣ) ∉ (B.fieldMarkedPair FF).C := by
  constructor
  · intro hrange hneg
    apply GQ2.Dyadic.EvenNLab.neg_one_notMem_imChiN halpha
    rw [← hrange,
      GQ2.Dyadic.LSquare.range_chiCycKTwo_eq_fieldMarkedPairC K B FF]
    exact hneg
  · exact range_eq_imChiN_of_marked B FF halpha hunit

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
private theorem familyN0_unit_mem
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .N0 alpha) :
    nUnit alpha ∈ (B.fieldMarkedPair FF).C := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
    dsimp only at hbranch
    subst branch
    cases W with
    | L degree_odd level_zero =>
        simp [FamilyFieldBranchWitness.Matches] at arithmetic_matches
    | M beta hbeta heven marked =>
        simp [FamilyFieldBranchWitness.Matches] at arithmetic_matches
    | N beta hbeta heven marked =>
        simp only [FamilyFieldBranchWitness.Matches] at arithmetic_matches
        rcases arithmetic_matches with ⟨rfl, -⟩
        exact marked.unit_mem

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
private theorem familyM0_rows
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha) :
    (-1 : ℤ_[2]ˣ) ∈ (B.fieldMarkedPair FF).C ∧
      mUnit alpha ∈ (B.fieldMarkedPair FF).C := by
  cases S with
  | mk branch valid compatible level_eq family_eq arithmetic_matches display degree_params
      degree_field =>
    dsimp only at hbranch
    subst branch
    cases W with
    | L degree_odd level_zero =>
        simp [FamilyFieldBranchWitness.Matches] at arithmetic_matches
    | N beta hbeta heven marked =>
        simp [FamilyFieldBranchWitness.Matches] at arithmetic_matches
    | M beta hbeta heven marked =>
        simp only [FamilyFieldBranchWitness.Matches] at arithmetic_matches
        rcases arithmetic_matches with ⟨rfl, -⟩
        exact ⟨marked.negOne_mem, marked.unit_mem⟩

omit [T2Space (GalK K)] in
/-- The natural N branch separator constructs the oriented N presentation selected by N0. -/
theorem orientedEquivN_of_familySelection_n0
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .N0 alpha)
    (hneg : (-1 : ℤ_[2]ˣ) ∉ (B.fieldMarkedPair FF).C) :
    Nonempty (OrientedContinuousMulEquiv
      (chiN alpha (handleCount FP (.N0 alpha))) (chiCycKTwo (K := K))) := by
  have halpha := S.valid
  rw [hbranch] at halpha
  have hrange := range_eq_imChiN_of_marked B FF halpha
    (familyN0_unit_mem B FF S hbranch) hneg
  have hdeg := S.degree_eq_field
  rw [hbranch] at hdeg
  apply parityFinal_orientedEquivN_of_range halpha hrange
  exact hdeg.symm

omit [T2Space (GalK K)] in
/-- The natural N branch separator constructs the oriented N presentation selected by Npc. -/
theorem orientedEquivN_of_familySelection_npc
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ} (hbranch : S.branch = .Npc alpha r eta)
    (hneg : (-1 : ℤ_[2]ˣ) ∉ (B.fieldMarkedPair FF).C) :
    Nonempty (OrientedContinuousMulEquiv
      (chiN alpha (handleCount FP (.Npc alpha r eta))) (chiCycKTwo (K := K))) := by
  have halpha := S.valid
  rw [hbranch] at halpha
  obtain ⟨hunit, -⟩ := familyNpc_isEtaFor S hbranch
  have hrange := range_eq_imChiN_of_marked B FF halpha.1 hunit hneg
  have hdeg := S.degree_eq_field
  rw [hbranch] at hdeg
  apply parityFinal_orientedEquivN_of_range halpha.1 hrange
  exact hdeg.symm

omit [T2Space (GalK K)] in
/-- The sharp selected M depth constructs the oriented M presentation on an M0 branch. -/
theorem orientedEquivM_of_familySelection_m0
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha)
    (hsharp : MFamilyDepthSharp (B.fieldMarkedPair FF) alpha) :
    Nonempty (OrientedContinuousMulEquiv
      (chiM alpha (handleCount FP (.M0 alpha))) (chiCycKTwo (K := K))) := by
  have halpha := S.valid
  rw [hbranch] at halpha
  obtain ⟨hneg, hunit⟩ := familyM0_rows B FF S hbranch
  have hrange := range_eq_imChiM_of_marked_sharp B FF halpha hneg hunit hsharp
  have hdeg := S.degree_eq_field
  rw [hbranch] at hdeg
  apply parityFinal_orientedEquivM_of_range halpha hrange
  exact hdeg.symm

omit [T2Space (GalK K)] in
/-- The sharp selected M depth constructs the oriented M presentation on any Mpc branch. -/
theorem orientedEquivM_of_familySelection_mpc
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta)
    (hsharp : MFamilyDepthSharp (B.fieldMarkedPair FF) alpha) :
    Nonempty (OrientedContinuousMulEquiv
      (chiM alpha (handleCount FP (.Mpc alpha r epsilon eta)))
      (chiCycKTwo (K := K))) := by
  have halpha := S.valid
  rw [hbranch] at halpha
  obtain ⟨hneg, hunit, -, -⟩ := familyMpc_lambda_rows S hbranch
  have hrange := range_eq_imChiM_of_marked_sharp
    B FF halpha.1 hneg hunit hsharp
  have hdeg := S.degree_eq_field
  rw [hbranch] at hdeg
  apply parityFinal_orientedEquivM_of_range halpha.1 hrange
  exact hdeg.symm

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [T2Space (GalK K)] in
/-- The selected N0 corrected residual from the intrinsic N range separator. -/
theorem n0RowResidualRN_of_familySelection_range
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .N0 alpha)
    (hneg : (-1 : ℤ_[2]ˣ) ∉ (B.fieldMarkedPair FF).C) :
    ∃ G : GenAsmBranch K B,
      G.pres = .N0 alpha (handleCount FP (.N0 alpha)) ∧
        Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  obtain ⟨e⟩ := orientedEquivN_of_familySelection_n0
    B FF S hbranch hneg
  exact n0RowResidualRN_of_familySelection B FF S hbranch e

omit [T2Space (GalK K)] in
/-- The selected Npc corrected residual from the intrinsic N range separator. -/
theorem npcRowResidualRN_of_familySelection_range
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ} (hbranch : S.branch = .Npc alpha r eta)
    (hneg : (-1 : ℤ_[2]ˣ) ∉ (B.fieldMarkedPair FF).C) :
    let d : NpcDisplayFor eta :=
      Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
    ∃ G : GenAsmBranch K B,
      G.pres = .Npc alpha r (handleCount FP (.Npc alpha r eta)) d.data ∧
        Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  obtain ⟨e⟩ := orientedEquivN_of_familySelection_npc
    B FF S hbranch hneg
  exact npcRowResidualRN_of_familySelection_exactLevel B FF S hbranch e

omit [T2Space (GalK K)] in
/-- A selected epsilon-true Mpc branch has its corrected residual once the selector's M depth
passes the single sharpness test.  The general tower supplies the pivot at every handle count. -/
theorem mpcRowResidualRN_of_familySelection_true_range
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r true eta)
    (hsharp : MFamilyDepthSharp (B.fieldMarkedPair FF) alpha) :
    let d : MpcDisplayFor eta :=
      Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
    ∃ G : GenAsmBranch K B,
      G.pres = .Mpc alpha r true d.display
        (handleCount FP (.Mpc alpha r true eta)) ∧
      Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  exact mpcRowResidualRN_of_familySelection_true B FF S hbranch
    (orientedEquivM_of_familySelection_mpc B FF S hbranch hsharp)

#print axioms MFamilyDepthSharp
#print axioms range_eq_imChiM_of_marked_sharp
#print axioms range_eq_imChiM_iff_marked_sharp
#print axioms range_eq_imChiN_of_marked
#print axioms range_eq_imChiN_iff_neg_one_notMem
#print axioms orientedEquivN_of_familySelection_n0
#print axioms orientedEquivN_of_familySelection_npc
#print axioms orientedEquivM_of_familySelection_m0
#print axioms orientedEquivM_of_familySelection_mpc
#print axioms n0RowResidualRN_of_familySelection_range
#print axioms npcRowResidualRN_of_familySelection_range
#print axioms mpcRowResidualRN_of_familySelection_true_range

end
end GQ2.Dyadic.Instances.EvenFamilyRangeBridge

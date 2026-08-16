/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcGeneralHandleCertificate
import GQ2.Dyadic.CertificateSupplyFamilyRN

/-!
# Family-selected general-h procyclic-M realization

The corrected family selector supplies the level, the `B` residue through `lambda(-1)`, and the
`D` residue through its selected eta equation.  The transported `C` pivot is not a function of
the cyclotomic value and remains the sole field-coordinate premise.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralHandleFamily

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcGeneralHandleRealization
open GQ2.Dyadic.Instances.MpcGeneralHandleCertificate
open GQ2.Dyadic.SelectedCoreLeavesRN

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

noncomputable section

section Field

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The field level transported along a general-h oriented M equivalence. -/
theorem chiKerLevel_of_level (B : MarkedRecip Rec K) {alpha r h : ℕ}
    (hr : B.r = r)
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) :
    MpcChiKerLevelH alpha r h
      (transport (nuUrKTwo B).toMonoidHom e.1
        ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun)) := by
  intro x hx
  obtain ⟨g, hg⟩ := maxProPMk_surjective (p := 2) (G := GalK K) (e.1 x)
  have hchi : chiCycKAb K (toAbK K g) = 1 := by
    rw [chiCycKAb_toAbK, ← chiCycKTwo_maxProPMk, hg]
    exact (e.2 x).trans hx
  obtain ⟨y, hy⟩ := B.nu_ker_chi_le _ hchi
  refine ⟨y, ?_⟩
  change toAdd (nuUrKTwo B (e.1 x)) = 2 ^ r * y
  rw [← hg, nuUrKTwo_maxProPMk, ← hr]
  exact hy

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- A selected lambda value gives the residue of any transported core element with the same
cyclotomic value. -/
theorem residue_of_lambdaAt (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha r h : ℕ} (hr : B.r = r) {c : ℤ_[2]ˣ} (hc : c ∈ (B.fieldMarkedPair FF).C)
    (z : ℤ_[2])
    (hlambda : (B.fieldMarkedPair FF).lambdaAt c hc =
      PadicInt.toZModPow (B.fieldMarkedPair FF).r z)
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    {x : DM alpha h} (hx : chiM alpha h x = c) :
    ∃ w : ℤ_[2],
      toAdd (transport (nuUrKTwo B).toMonoidHom e.1
        ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun) x) =
          z + 2 ^ r * w := by
  let P := B.fieldMarkedPair FF
  obtain ⟨g, hg⟩ := maxProPMk_surjective (p := 2) (G := GalK K) (e.1 x)
  have hchi : P.chi (toAbK K g) = c := by
    change chiCycKAb K (toAbK K g) = c
    rw [chiCycKAb_toAbK, ← chiCycKTwo_maxProPMk, hg]
    exact (e.2 x).trans hx
  have hnuMod : PadicInt.toZModPow P.r (P.nu (toAbK K g)).toAdd =
      PadicInt.toZModPow P.r z := (P.lambdaAt_spec c hc _ hchi).symm.trans hlambda
  have hmod : PadicInt.toZModPow r
      (toAdd (nuUrKTwo B (e.1 x)) - z) = 0 := by
    rw [map_sub, ← hg, nuUrKTwo_maxProPMk]
    change PadicInt.toZModPow r (P.nu (toAbK K g)).toAdd -
      PadicInt.toZModPow r z = 0
    change PadicInt.toZModPow B.r (P.nu (toAbK K g)).toAdd =
      PadicInt.toZModPow B.r z at hnuMod
    rw [hr] at hnuMod
    exact sub_eq_zero.mpr hnuMod
  obtain ⟨w, hw⟩ := MarkedPair.exists_eq_two_pow_mul hmod
  exact ⟨w, by
    change toAdd (nuUrKTwo B (e.1 x)) = z + 2 ^ r * w
    linear_combination hw⟩

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- The Mpc selector exposes its two intrinsic lambda equations. -/
theorem familyMpc_lambda_rows
    {FP : FieldParameters} {Q : MarkedPair (GalKab K)}
    {W : FamilyFieldBranchWitness FP Q}
    (S : FamilyFieldBranchSelection K FP Q W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta) :
    ∃ (hneg : (-1 : ℤ_[2]ˣ) ∈ Q.C) (hunit : mUnit alpha ∈ Q.C),
      Q.lambdaAt (-1) hneg =
          PadicInt.toZModPow Q.r (p epsilon r : ℤ_[2]) ∧
        Q.lambdaAt (mUnit alpha) hunit =
          PadicInt.toZModPow Q.r (eta : ℤ_[2]) := by
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
        rcases arithmetic_matches with ⟨rfl, rfl, hneg, heta⟩
        change MarkedGeneratorData Q (mUnit alpha) at marked
        refine ⟨marked.negOne_mem, marked.unit_mem, ?_, ?_⟩
        · change Q.lambdaAt (-1) marked.negOne_mem =
            ((epsVal epsilon * 2 ^ (Q.r - 1) : ℕ) : ZMod (2 ^ Q.r)) at hneg
          simpa only [p, map_natCast] using hneg
        · exact (Q.isEtaFor_datum_iff (mUnit alpha) marked.unit_mem eta).mp heta

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- A selected Mpc branch closes the level and both rank-four residue rows. -/
theorem level_and_residues_of_familySelection
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta)
    (e : OrientedContinuousMulEquiv
      (chiM alpha (handleCount FP (.Mpc alpha r epsilon eta)))
      (chiCycKTwo (K := K))) :
    let h := handleCount FP (.Mpc alpha r epsilon eta)
    MpcChiKerLevelH alpha r h
      (transport (nuUrKTwo B).toMonoidHom e.1
        ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun)) ∧
      (∃ w : ℤ_[2], toAdd (transport (nuUrKTwo B).toMonoidHom e.1
        ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun) (dmD alpha h)) =
          (eta : ℤ_[2]) + 2 ^ r * w) ∧
        ∃ w : ℤ_[2], toAdd (transport (nuUrKTwo B).toMonoidHom e.1
          ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun) (dmB alpha h)) =
            (p epsilon r : ℤ_[2]) + 2 ^ r * w := by
  let h := handleCount FP (.Mpc alpha r epsilon eta)
  have hr : B.r = r := by
    have hs := S.level_eq
    rw [hbranch] at hs
    exact hs.symm
  obtain ⟨hneg, hunit, hnegrow, hunitrow⟩ := familyMpc_lambda_rows S hbranch
  refine ⟨chiKerLevel_of_level B hr e, ?_, ?_⟩
  · exact residue_of_lambdaAt B FF hr hunit (eta : ℤ_[2]) hunitrow e
      (chiM_dmD alpha h)
  · exact residue_of_lambdaAt B FF hr hneg (p epsilon r : ℤ_[2]) hnegrow e
      (chiM_dmB alpha h)

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The family-selected general-h certificate.  The selector discharges the level and the two
residues; only the transported kernel pivot and explicit scaling face remain as inputs. -/
theorem certificate_of_familySelection
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta)
    (e : OrientedContinuousMulEquiv
      (chiM alpha (handleCount FP (.Mpc alpha r epsilon eta)))
      (chiCycKTwo (K := K)))
    (hscale : MScalingHypothesis alpha
      (handleCount FP (.Mpc alpha r epsilon eta)))
    (hpivot : ∃ gamma : ℤ_[2]ˣ,
      toAdd (transport (nuUrKTwo B).toMonoidHom e.1
        ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun)
          (dmC alpha (handleCount FP (.Mpc alpha r epsilon eta)))) =
        (gamma : ℤ_[2]) * 2 ^ r) :
    Nonempty (Certificate alpha r (p epsilon r)
      (handleCount FP (.Mpc alpha r epsilon eta)) eta (by
        have hv := S.valid
        rw [hbranch] at hv
        exact le_trans (by decide) hv.1)
      (chiCycKTwo (K := K)).toMonoidHom (nuUrKTwo B).toMonoidHom) := by
  let h := handleCount FP (.Mpc alpha r epsilon eta)
  have halpha : 2 ≤ alpha := by
    have hv := S.valid
    rw [hbranch] at hv
    exact hv.1
  obtain ⟨hlev, hD, hB⟩ := level_and_residues_of_familySelection B FF S hbranch e
  apply certificate_of_oriented r (p epsilon r) h eta halpha (by omega) hscale
    (chiCycKTwo (K := K)).toMonoidHom (nuUrKTwo B).toMonoidHom e.1 e.2
    ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun)
  · exact hlev
  · exact ⟨hpivot, hD, hB⟩

/-- The family-selected corrected realization at the canonical arbitrary-unit marking. -/
theorem realization_of_familySelection
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta)
    (e : OrientedContinuousMulEquiv
      (chiM alpha (handleCount FP (.Mpc alpha r epsilon eta)))
      (chiCycKTwo (K := K)))
    (hscale : MScalingHypothesis alpha
      (handleCount FP (.Mpc alpha r epsilon eta)))
    (hpivot : ∃ gamma : ℤ_[2]ˣ,
      toAdd (transport (nuUrKTwo B).toMonoidHom e.1
        ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun)
          (dmC alpha (handleCount FP (.Mpc alpha r epsilon eta)))) =
        (gamma : ℤ_[2]) * 2 ^ r) :
    Nonempty (MarkedCoreRealization (K := K) (B := B)
      (DM alpha (handleCount FP (.Mpc alpha r epsilon eta)))
      (SelectedCoreLeavesRN.mpcNu alpha r (p epsilon r)
        (handleCount FP (.Mpc alpha r epsilon eta)) eta (by
          have hv := S.valid
          rw [hbranch] at hv
          exact le_trans (by decide) hv.1))) := by
  obtain ⟨C⟩ := certificate_of_familySelection B FF S hbranch e hscale hpivot
  exact ⟨MpcGeneralHandleRealization.realization C⟩

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- Convenience form using the repository's canonical scaling witness.  Its only additional
inherited constant is `peripheralCyclotomicAction`; the explicit-scaling theorem above stays
standard-three. -/
theorem certificate_of_familySelection_canonicalScaling
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta)
    (e : OrientedContinuousMulEquiv
      (chiM alpha (handleCount FP (.Mpc alpha r epsilon eta)))
      (chiCycKTwo (K := K)))
    (hpivot : ∃ gamma : ℤ_[2]ˣ,
      toAdd (transport (nuUrKTwo B).toMonoidHom e.1
        ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun)
          (dmC alpha (handleCount FP (.Mpc alpha r epsilon eta)))) =
        (gamma : ℤ_[2]) * 2 ^ r) :
    Nonempty (Certificate alpha r (p epsilon r)
      (handleCount FP (.Mpc alpha r epsilon eta)) eta (by
        have hv := S.valid
        rw [hbranch] at hv
        exact le_trans (by decide) hv.1)
      (chiCycKTwo (K := K)).toMonoidHom (nuUrKTwo B).toMonoidHom) :=
  certificate_of_familySelection B FF S hbranch e
    (mScalingHypothesis alpha (handleCount FP (.Mpc alpha r epsilon eta))) hpivot

#print axioms chiKerLevel_of_level
#print axioms residue_of_lambdaAt
#print axioms familyMpc_lambda_rows
#print axioms level_and_residues_of_familySelection
#print axioms certificate_of_familySelection
#print axioms realization_of_familySelection
#print axioms certificate_of_familySelection_canonicalScaling

end Field

end

end GQ2.Dyadic.Instances.MpcGeneralHandleFamily

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.GeneralCertificates
import GQ2.Dyadic.Instances.FieldSqrtFiveUnramified
import GQ2.Dyadic.Instances.MpcNormValues

/-!
# The canonical row records at the tied quadratic rows  (dyadic campaign, lane W83-RECORDS)

Placeholder docstring; filled in as the sections land.
-/

namespace GQ2.Dyadic.Instances.CanonicalRecords

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open TameSpec MarkedCore Multiplicative
open GQ2.Dyadic.Count GQ2.Dyadic.Words
open GQ2.Dyadic.FieldBranchId GQ2.Dyadic.FieldUnimod GQ2.Dyadic.Fields
open GQ2.Dyadic.Instances.MCompactCore GQ2.Dyadic.Instances.MProcyclicCore
open GQ2.Dyadic.Instances.NuWitness GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.Instances.MpcCert GQ2.Dyadic.Instances.MpcRow GQ2.Dyadic.Instances.MpcNorm
open GQ2.Dyadic.FieldSqrtFive

/-! ## §1 The two `M`-row markings are the same hom -/

section MMarking

/-- **The `M0` rows' two canonical markings agree.**

The general branch datum on an `M0` row is built at `fieldId_mNuZtwo α h hα`, which is
`ν_M` read backwards through the boundary seam `ztwoIota`; the row's committed word certificate
`MCompactCore.mWordCertificate` takes its marking with the two normalization clauses
`hnuSigma`/`hnuWild`, and the tree proves those only at `MCompactCore.mNu α h hα`, which is the
`dmNu` witness for the exponent vector `mNuExp`.

Nothing connected the two.  They are equal, and the proof is a generator check: both send
`μ₀ ↦ −m`, `μ₂ ↦ 1` and every other marked generator to `0`, once `mOf α = 2 ^ (α − 1)` is
pushed through the cast. -/
theorem canRec_mNu_eq_mNuZtwo (α h : ℕ) (hα : 1 ≤ α) :
    mNu α h hα = fieldId_mNuZtwo α h hα := by
  refine dm_hom_ext _ _ fun i => ?_
  refine ztwoIota.injective (Multiplicative.toAdd.injective ?_)
  have hL : toAdd (ztwoIota (mNu α h hα (dmGen α h i))) = ((mNuExp α h i : ℤ) : ℤ_[2]) := by
    rw [mNu, dmNu_dmGen, mpcCert_toAdd_ztwoIota_zpow]
  have hR : toAdd (ztwoIota (fieldId_mNuZtwo α h hα (dmGen α h i)))
      = toAdd (nuM α h hα (dmGen α h i)) := by
    rw [fieldId_ztwoIota_mNuZtwo]
  rw [hL, hR, nuM, mLiftHom_gen, coreMark_apply]
  by_cases h0 : (i : ℕ) = 0
  · rw [if_pos h0, mNuExp, if_pos h0, toAdd_ofAdd]
    simp only [mOf]
    push_cast
    ring
  by_cases h2 : (i : ℕ) = 2
  · rw [if_neg h0, if_neg (by omega : ¬ (i : ℕ) = 1), if_pos h2, mNuExp, if_neg h0, if_pos h2,
      toAdd_ofAdd]
    norm_num
  rw [mNuExp_eq_zero α h h0 h2, if_neg h0]
  by_cases h1 : (i : ℕ) = 1
  · rw [if_pos h1, toAdd_ofAdd, Int.cast_zero]
  rw [if_neg h1, if_neg h2]
  by_cases h3 : (i : ℕ) = 3
  · rw [if_pos h3, toAdd_ofAdd, Int.cast_zero]
  · rw [if_neg h3, Int.cast_zero, toAdd_one]

/-- `hnuSigma` for `mWordCertificate` at the *branch datum's* marking. -/
theorem canRec_mNuZtwo_sigma (α h : ℕ) (hα : 1 ≤ α) :
    fieldId_mNuZtwo α h hα ((mCorePresentation α h hα).mark .sigma) = ztwoOne := by
  rw [← canRec_mNu_eq_mNuZtwo]
  exact mNu_sigma α h hα

/-- `hnuWild` for `mWordCertificate` at the *branch datum's* marking. -/
theorem canRec_mNuZtwo_wild (α h : ℕ) (hα : 1 ≤ α) (j : Fin (2 + 2 * h + 1)) :
    fieldId_mNuZtwo α h hα ((mCorePresentation α h hα).mark (.wild j)) = 1 := by
  rw [← canRec_mNu_eq_mNuZtwo]
  exact mNu_wild α h hα j

end MMarking

/-! ## §2 The tied branch data at the four clause-free quadratic rows -/

section TiedBranches

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] {R : LocalReciprocity}

/-- **The `ℚ₂(√−2)` branch datum, tied to its marking.**  `fieldUni_genAsmBranch_sqrtNegTwo`
with the W83 conjunct kept. -/
theorem canRec_branch_sqrtNegTwo [T2Space (GalK KSqrtNegTwo)] (B : MarkedRecip R KSqrtNegTwo) :
    ∃ G : GenAsmBranch KSqrtNegTwo B, G.pres = .N0 2 0 ∧
      HEq G.nuP (SelectedCoreLeavesRN.nNuZtwo 2 0) :=
  fieldUni_genAsmBranch_of_orientedN_level_zero 2 (le_refl 2)
    (by rw [finrank_KSqrtNegTwo]; rfl) (fieldUni_level_sqrtNegTwo B)
    (fieldId_chosenEquivN_sqrtNegTwo B)

/-- **The `ℚ₂(√2)` branch datum, tied to its marking.** -/
theorem canRec_branch_sqrtTwo [T2Space (GalK KSqrtTwo)] (B : MarkedRecip R KSqrtTwo) :
    ∃ G : GenAsmBranch KSqrtTwo B, G.pres = .M0 3 0 ∧
      HEq G.nuP (fieldId_mNuZtwo 3 0 (by omega)) :=
  fieldUni_genAsmBranch_of_orientedM_level_zero 3 (by omega)
    (by rw [finrank_KSqrtTwo]; rfl) (fieldUni_level_sqrtTwo B)
    (fieldId_chosenEquivM_sqrtTwo B)

/-- **The `ℚ₂(√5)` branch datum, tied to its marking.**  Unconditional through
`fieldFive_twoIsUniformizer`. -/
theorem canRec_branch_sqrtFive [T2Space (GalK KSqrtFive)] (B : MarkedRecip R KSqrtFive) :
    ∃ G : GenAsmBranch KSqrtFive B, G.pres = .M0 2 0 ∧
      HEq G.nuP (fieldId_mNuZtwo 2 0 (by omega)) :=
  fieldUni_genAsmBranch_of_orientedM_level_zero 2 (le_refl 2)
    (by rw [finrank_KSqrtFive]; rfl)
    (fieldUni_level_eq_zero_of_twoUniformizer B fieldFive_twoIsUniformizer)
    (fieldId_chosenEquivM_sqrtFive B)

/-- **The `ℚ₂(√10)` branch datum, tied to its marking.**  Unconditional through
`mpcNorm_rowData_sqrtTen`. -/
theorem canRec_branch_sqrtTen [T2Space (GalK KSqrtTen)] (B : MarkedRecip R KSqrtTen) :
    ∃ G : GenAsmBranch KSqrtTen B, G.pres = .Mpc 2 1 false .one 0 ∧
      HEq G.nuP (mpcNu 2 1 (p false 1) (by omega)) :=
  mpcCert_genAsmBranch_of_orientedMpc 1 (p false 1) false .one (le_refl 2) (by omega)
    (by rw [finrank_KSqrtTen]; rfl) (fieldId_chosenEquivM_sqrtTen B)
    (mpcCert_chiKerLevel_of_level B (mpcNorm_rowData_sqrtTen B).1 _)
    (mpcNorm_rowData_sqrtTen B).2

end TiedBranches

end GQ2.Dyadic.Instances.CanonicalRecords

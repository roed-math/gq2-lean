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

`GeneralAssembly.GenAsmRowResidual` states all four of its blocks at the branch datum's own
marking `G.nuP`, and every committed `WordCertificate` producer in the campaign lives at a
*named* marking of its row's core.  Until wave 83 the branch producers concluded
`∃ G : GenAsmBranch K B, G.pres = S`, which forgets `G.nuP`, so no consumer could put the two
together: the record's `CAND` field was unreachable at every frozen row.  W82-CAND recorded this
and worked around it on the `L` row by rebuilding the datum as a definition
(`Instances.LRowCand.lCandBranch`).

Wave 83 ticket A strengthened five branch producers to carry `∧ HEq G.nuP <marking>`.  This
module is ticket B: with the marking in hand, the committed certificate producers are fed into
`GenAsmRowResidual.cand` at each of the four **clause-free** quadratic rows, and what remains of
the general theorem's hypotheses at each row is read off the resulting statements.

## What the module contains

* §1 **the `M0` rows' marking bridge**, `canRec_mNu_eq_mNuZtwo`.  This is the one piece of
  mathematics here rather than plumbing, and it closes a gap the tree carried silently: the
  branch datum on an `M0` row is built at `FieldBranchId.fieldId_mNuZtwo` (`ν_M` read backwards
  through `ztwoIota`) while `MCompactCore.mWordCertificate` normalises at `MCompactCore.mNu`
  (the `dmNu` witness for the exponent vector `mNuExp`), and **no lemma in the tree connected
  them**.  They are equal; §1 proves it on generators and transports the two normalization
  clauses.  Without it the `√2` and `√5` rows cannot reach `cand` even with ticket A.
* §2 the four tied branch data, each **unconditional** over the field's own bundle;
* §3 one `CAND` producer per branch shape, plus the pilot spelling at `√−2` and the `rfl`
  identification `SqrtNeg2.pilotNuP = SelectedCoreLeavesRN.nNuZtwo 2 0` that makes it land;
* §4 the transport `canRec_rowResidual_of_tied` and the three shape-level residuals;
* §5 the four rows.

## The per-row table

At every one of the four rows the branch datum and its marking are **free**, and the residual
record costs exactly three blocks.  Writing `q = q_K` and `Γ = Γ_R (deg) q (word)`:

| row | `K` | canonical marking | `CAND` producer | what remains |
| --- | --- | --- | --- | --- |
| `N0 2 0` | `ℚ₂(√−2)` | `nNuZtwo 2 0` | `genCertNWordCertificateCanonical` (or `sqrtNegTwoWordCertificate`) | 4 analytic clauses at `Γ`, `ASK` exactLifting, `ASK` stokes |
| `M0 3 0` | `ℚ₂(√2)` | `fieldId_mNuZtwo 3 0` | `mWordCertificate` (via §1) | the same |
| `M0 2 0` | `ℚ₂(√5)` | `fieldId_mNuZtwo 2 0` | `mWordCertificate` (via §1) | the same |
| `Mpc 2 1 false 1 0` | `ℚ₂(√10)` | `mpcNu 2 1 (p false 1)` | `mpcWordCertificate` | the same |

[W85-HOUSE, as of `76f21241`, on the `N0 2 0` row's two `CAND` producers: **use
`genCertNWordCertificateCanonical`, i.e. `canRec_candN` below, not `canRec_candPilot`.**  Wave
84 (`Instances/RowClauses.lean` §5) showed the pilot spelling is dominated: it carries
`PilotHsimp`, `PilotStageSep`, `PilotStageZ`, `PilotDet`, and its three recursion residues
together already imply `askCStageVanishing` at the same carrier
(`rowCl_pilot_stageVanishing`), which is all the `genCertN` spelling's `exactLifting` clause
asks for there (`rowCl_nCand_exactLifting_iff`); the `genCertN` spelling additionally gets its
`scalar` clause free (`rowCl_nCand_scalar`).  This module is already on the recommended
spelling: `canRec_analytic_sqrtNegTwo` runs through `canRec_rowResidual_N0_of_analytic` and
`canRec_candN`, and `canRec_candPilot` has no consumer in this file.  **The campaign assembly
is not**: `Main.lean`'s `ResidualSqrtNegTwo` still carries all four pilot residues as fields,
and `rowEquiv_sqrtNegTwo` feeds them to `ramifiedI_candidate_equiv_galK`, as does
`GeneralAssembly.genAsm_rowEquiv_sqrtNegTwo`.  So "nothing consumes the pilot spelling any
more" is true of the record lane and false of the assembly; retiring it is a statement-level
lane, not a housekeeping edit.]

Three readings worth keeping.

1. **`ASK` `determinant` is gone.**  It is not a binder of any statement in §4 or §5: the
   residual is assembled through `Instances.MpcRow.mpcRow_genAsmRowResidual_of_counting`, which
   derives it from `affineDeterminant_galK` and the field inputs' `ramifiedData`, with the two
   Gauss pins `rfl` at `standardNumerics`.  So the record costs **two** `ASK` blocks, not three.

   [W84-HOUSE, as of `45f9c42d`: verified by elaboration, and one precision note for a reader
   who greps rather than elaborates.  "Not a binder of any statement in §4 or §5" is about the
   `ASK` determinant, the one at the carrier `galKProfinite K`, and that is exactly right: the
   two `ASK` binders of both templates are `ExactLiftingSemantics` and `StokesDualityCertificate`
   at `galKProfinite K`, and there is no third.  But `AffineDeterminantCertificate` DOES occur as
   a binder in §5, in the analytic template `canRec_analytic_*`, at the carrier
   `GammaR deg q word`: it is one of the four Γ-side analytic clauses, not an `ASK` block.  Both
   templates measured: `canRec_rowResidual_<field>` carries `B`, `F`, `cand`, and the two `ASK`
   blocks; `canRec_analytic_<field>` carries `B`, `FF`, `F`, the four Γ-side clauses
   (`ExactLiftingSemantics`, `StokesDualityCertificate`, `ScalarHilbertCertificate`,
   `AffineDeterminantCertificate`), and the same two `ASK` blocks.  Identical across all four
   rows, which confirms reading 2 at the level of the binder LISTS.  See the W85-HOUSE note on
   reading 2 for what that measurement does not cover.]
2. **The residue is uniform.**  The four analytic clauses are the same four on every row, at
   the row's own candidate carrier; there is no per-row analytic obligation left.

   [W85-HOUSE, as of `76f21241`: **true of the clause SHAPES, and of nothing more.**  What is
   not uniform is the REDUCTION of those clauses, because each runs on its own branch's
   resolver package.  `Instances/RowClauses.lean` §2 and §4 (wave 84) turn the `exactLifting`
   clause into `askCStageVanishing` at the candidate carrier and discharge the `scalar` clause
   outright, at `M0 3 0`, `M0 2 0` and `N0 2 0`.  All three have an unconditional corrected
   bundle: `MCompact.exactLiftingRN_unconditional` (`Instances/EvenMRamifiedPairing.lean`) and
   `NCompact.exactLiftingRN_unconditional` (`Instances/N0M0CompactBranches.lean`), both at
   `2 ≤ α`, `q ≠ 0`, `Even q` and nothing else.  **`Mpc 2 1 false 1 0` has no such bundle**:
   `MProcyclicExact` offers only `exactLiftingRN_of_uniformPushed` (`Instances/MpcExact.lean`),
   which still binds a `Hsimp`-family hypothesis.  So the honest form of the uniformity claim
   at this tree is SUCCESS AT ONE ROW IS SUCCESS AT THREE, and W83-RECORDS' reading 2, which
   said four, is superseded here and in `docs/dyadic/w83-records-note.md`.  Bringing the fourth
   row in is the wave-85 ticket `MProcyclicExact.exactLiftingRN_unconditional`.]
3. **`ℚ₂(√−10)` is not here, and the reason is a statement.**  Its clause-free branch datum
   `Instances.MpcPivot.mpcPiv_genAsmBranch_sqrtNegTen` is built at the *transported* marking
   `mpcPiv_nuZtwo`, not at `mpcNu`, and no comparison of the two exists at this tree, so it
   cannot be tied.  The tied statement at that row is `mpcPiv_genAsmBranch_sqrtNegTen_of_shift`,
   conditional on `MpcPivShift 2`.

   ⚠⚠ **[W84-HOUSE, as of `45f9c42d`: the last sentence is FALSE at the statement level.**
   `mpcPiv_genAsmBranch_sqrtNegTen_of_shift` concludes
   `∃ G : GenAsmBranch KSqrtNegTen B, G.pres = .Mpc 2 1 true .one 0` and nothing more: it routes
   through the strengthened site 5, which does name `mpcNu 2 1 (p true 1)`, but then **drops the
   conjunct** with `Exists.imp (fun _ hG => hG.1)`.  So it is untied too, and it cannot be fed to
   `canRec_rowResidual_of_tied` below.  `ℚ₂(√−10)` has no tied statement at this tree; the two
   statements it does have differ in hypothesis, not in tie.  This does not change which four
   rows this module serves, only the reason the fifth is absent: it is not that the marking is
   wrong, it is that no `√−10` statement carries any marking at all.  The repair is one line at
   `Instances/MpcPivot.lean` and is an owner item, recorded there.]**

## Axioms

`#print axioms` runs on every declaration in §6, with the split recorded there.
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

/-! ## §3 The `CAND` field at the branch datum's own marking

One producer per branch shape, stated so that its conclusion is *literally* the type of
`GenAsmRowResidual.cand` over a branch datum sitting on that row at the canonical marking: the
degree, word, core and `IsProP` witness are written as the `SelectedPresentation` projections
rather than as the certificate layer's spellings, and the elaborator checks the two agree.

The four arguments are AS1's analytic clauses at the candidate carrier `Γ_R`.  They are the same
four on every row (this is W82-CAND's "uniform residue"), and they are the only thing left of
`cand` after this section. -/

section Cand

/-- **`CAND` on an `M0` row**, `MCompactCore.mWordCertificate` at `fieldId_mNuZtwo`.  The two
normalization clauses come from §1; before §1 this application did not typecheck. -/
noncomputable def canRec_candM (α h q : ℕ) (hα : 1 ≤ α) (hq0 : q ≠ 0) (hqe : Even q)
    (exactLifting : ExactLiftingSemantics (GammaR (2 + 2 * h) q (mCompactW α h))
      (2 + 2 * h) q (DM α h) (fieldId_mNuZtwo α h hα) (standardNumerics (2 + 2 * h)))
    (stokes : StokesDualityCertificate (GammaR (2 + 2 * h) q (mCompactW α h)) (2 + 2 * h) q
      (DM α h) (fieldId_mNuZtwo α h hα) (standardNumerics (2 + 2 * h)) (scalarActionZmodTwo _))
    (scalar : ScalarHilbertCertificate (GammaR (2 + 2 * h) q (mCompactW α h)) (2 + 2 * h)
      (standardNumerics (2 + 2 * h)) (scalarActionZmodTwo _))
    (determinant : AffineDeterminantCertificate (GammaR (2 + 2 * h) q (mCompactW α h))
      (2 + 2 * h) q (DM α h) (fieldId_mNuZtwo α h hα) (standardNumerics (2 + 2 * h))
      (tameOfSpec (2 + 2 * h) q (mCompactW α h) (mTameSpecializes α h q hq0 hqe))
      (mPro2 α h q hα hq0 hqe)
      (mCompat α h q hα hq0 hqe (mTameSpecializes α h q hq0 hqe) (fieldId_mNuZtwo α h hα)
        (canRec_mNuZtwo_sigma α h hα) (canRec_mNuZtwo_wild α h hα))
      (scalarActionZmodTwo _)) :
    WordCertificate (SelectedPresentation.M0 α h).degree q (SelectedPresentation.M0 α h).word
      (genAsmCore (.M0 α h)) (genAsmCoreIsProP (.M0 α h)) (fieldId_mNuZtwo α h hα)
      (standardNumerics (SelectedPresentation.M0 α h).degree) :=
  mWordCertificate α h q hα hq0 hqe (fieldId_mNuZtwo α h hα) (canRec_mNuZtwo_sigma α h hα)
    (canRec_mNuZtwo_wild α h hα) exactLifting stokes scalar determinant

/-- **`CAND` on an `N0` row**, `genCertNWordCertificateCanonical` at `nNuZtwo`.  This one needed
no bridge: the general `N` producer was already stated at the branch datum's marking. -/
noncomputable def canRec_candN (α h q : ℕ) (hq0 : q ≠ 0) (hqe : Even q)
    (exactLifting : ExactLiftingSemantics (GammaR (2 + 2 * h) q (nCompactW α h))
      (2 + 2 * h) q (DN α h) (SelectedCoreLeavesRN.nNuZtwo α h) (standardNumerics (2 + 2 * h)))
    (stokes : StokesDualityCertificate (GammaR (2 + 2 * h) q (nCompactW α h)) (2 + 2 * h) q
      (DN α h) (SelectedCoreLeavesRN.nNuZtwo α h) (standardNumerics (2 + 2 * h))
      (scalarActionZmodTwo _))
    (scalar : ScalarHilbertCertificate (GammaR (2 + 2 * h) q (nCompactW α h)) (2 + 2 * h)
      (standardNumerics (2 + 2 * h)) (scalarActionZmodTwo _))
    (determinant : AffineDeterminantCertificate (GammaR (2 + 2 * h) q (nCompactW α h))
      (2 + 2 * h) q (DN α h) (SelectedCoreLeavesRN.nNuZtwo α h) (standardNumerics (2 + 2 * h))
      (tameOfSpec (2 + 2 * h) q (nCompactW α h) (genCertNTameSpecializes α h q hq0 hqe))
      (genCertNPro2 α h q hq0 hqe)
      (genCertNCompat α h q hq0 hqe (genCertNTameSpecializes α h q hq0 hqe)
        (SelectedCoreLeavesRN.nNuZtwo α h) (SelectedCoreLeavesRN.nNuZtwo_sigma α h)
        (SelectedCoreLeavesRN.nNuZtwo_wild α h))
      (scalarActionZmodTwo _)) :
    WordCertificate (SelectedPresentation.N0 α h).degree q (SelectedPresentation.N0 α h).word
      (genAsmCore (.N0 α h)) (genAsmCoreIsProP (.N0 α h)) (SelectedCoreLeavesRN.nNuZtwo α h)
      (standardNumerics (SelectedPresentation.N0 α h).degree) :=
  genCertNWordCertificateCanonical α h q hq0 hqe exactLifting stokes scalar determinant

/-- **`CAND` on an `Mpc` row at the `η = 1` display**, `MProcyclicCore.mpcWordCertificate` at
`mpcNu`.  The row's `pp` is the table's `p ε r`, which is what the branch producer's marking
carries. -/
noncomputable def canRec_candMpc (α r q : ℕ) (epsilon : Bool) (hα : 1 ≤ α) (hq0 : q ≠ 0)
    (hqe : Even q)
    (exactLifting : ExactLiftingSemantics
      (GammaR (2 + 2 * 0) q (Words.Mpc.mpcW α r (p epsilon r) .one 0)) (2 + 2 * 0) q (DM α 0)
      (mpcNu α r (p epsilon r) hα) (standardNumerics (2 + 2 * 0)))
    (stokes : StokesDualityCertificate
      (GammaR (2 + 2 * 0) q (Words.Mpc.mpcW α r (p epsilon r) .one 0)) (2 + 2 * 0) q (DM α 0)
      (mpcNu α r (p epsilon r) hα) (standardNumerics (2 + 2 * 0)) (scalarActionZmodTwo _))
    (scalar : ScalarHilbertCertificate
      (GammaR (2 + 2 * 0) q (Words.Mpc.mpcW α r (p epsilon r) .one 0)) (2 + 2 * 0)
      (standardNumerics (2 + 2 * 0)) (scalarActionZmodTwo _))
    (determinant : AffineDeterminantCertificate
      (GammaR (2 + 2 * 0) q (Words.Mpc.mpcW α r (p epsilon r) .one 0)) (2 + 2 * 0) q (DM α 0)
      (mpcNu α r (p epsilon r) hα) (standardNumerics (2 + 2 * 0))
      (tameOfSpec (2 + 2 * 0) q (Words.Mpc.mpcW α r (p epsilon r) .one 0)
        (mpcTameSpecializes α r (p epsilon r) q hα hq0 hqe))
      (mpcPro2 α r (p epsilon r) q hα hq0 hqe)
      (mpcCompat α r (p epsilon r) q hα hq0 hqe (mpcTameSpecializes α r (p epsilon r) q hα hq0 hqe)
        (mpcNu α r (p epsilon r) hα) (mpcNu_sigma α r (p epsilon r) hα)
        (mpcNu_wild α r (p epsilon r) hα))
      (scalarActionZmodTwo _)) :
    WordCertificate (SelectedPresentation.Mpc α r epsilon .one 0).degree q
      (SelectedPresentation.Mpc α r epsilon .one 0).word
      (genAsmCore (.Mpc α r epsilon .one 0)) (genAsmCoreIsProP (.Mpc α r epsilon .one 0))
      (mpcNu α r (p epsilon r) hα)
      (standardNumerics (SelectedPresentation.Mpc α r epsilon .one 0).degree) :=
  mpcWordCertificate α r (p epsilon r) q hα hq0 hqe (mpcNu α r (p epsilon r) hα)
    (mpcNu_sigma α r (p epsilon r) hα) (mpcNu_wild α r (p epsilon r) hα)
    exactLifting stokes scalar determinant

/-- **The pilot row's committed marking IS the general `N` row's marking** at `(α, h) = (2, 0)`.
`rfl`, and never stated: `SqrtNeg2.pilotNuP` and `SelectedCoreLeavesRN.nNuZtwo 2 0` are the same
`ztwoIota.symm ∘ ν_N` written twice.  This is what lets the `√−2` row be served at *both*
committed spellings. -/
theorem canRec_pilotNuP_eq : SqrtNeg2.pilotNuP = SelectedCoreLeavesRN.nNuZtwo 2 0 := rfl

/-- **`CAND` at the `N0 2 0` row in the committed pilot spelling**, `sqrtNegTwoWordCertificate`.
Its four residuals are the pilot's own named `Prop`s rather than the generic clause types; the
conclusion is the same `GenAsmRowResidual.cand` slot as `canRec_candN 2 0`. -/
noncomputable def canRec_candPilot (q : ℕ) (hq0 : q ≠ 0) (hqe : Even q)
    (hsimp : SqrtNeg2.PilotHsimp q) (hsplit : SqrtNeg2.PilotStageSep q)
    (hZcount : SqrtNeg2.PilotStageZ q) (hdet : SqrtNeg2.PilotDet q hq0 hqe) :
    WordCertificate (SelectedPresentation.N0 2 0).degree q (SelectedPresentation.N0 2 0).word
      (genAsmCore (.N0 2 0)) (genAsmCoreIsProP (.N0 2 0)) (SelectedCoreLeavesRN.nNuZtwo 2 0)
      (standardNumerics (SelectedPresentation.N0 2 0).degree) :=
  SqrtNeg2.sqrtNegTwoWordCertificate hq0 hqe hsimp hsplit hZcount hdet

end Cand

/-! ## §4 The row residual records -/

section RowResidual

variable {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {R : LocalReciprocity} {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}

/-- **The transport, once.**  A branch datum that *names* its marking, plus the row's `CAND`
certificate at that marking, plus the two `ASK` counting clauses and the structural field
inputs, give the whole `GenAsmRowResidual`.

Three things happen here that could not happen before this lane.  The marking equation comes
out of the branch existential (W83 ticket A); it is turned from `HEq` into a substitution by
destructuring the datum, which is why the strengthened conjunct is usable rather than merely
true; and the `determinant` block is *derived* rather than carried, through
`Instances.MpcRow.mpcRow_genAsmRowResidual_of_counting`, whose Gauss pins are `rfl` at
`standardNumerics`.  So the record costs two `ASK` blocks and one `CAND` block, not four. -/
theorem canRec_rowResidual_of_tied {row : SelectedPresentation}
    {nu0 : ContinuousMonoidHom ((genAsmCore row : ProfiniteGrp) : Type) Ztwo}
    (H : ∃ G : GenAsmBranch K B, G.pres = row ∧ HEq G.nuP nu0)
    (F : GenAsmFieldInputs K B FF row.degree)
    (cand : WordCertificate row.degree (qOf K FF) row.word (genAsmCore row)
      (genAsmCoreIsProP row) nu0 (standardNumerics row.degree))
    (askExactLifting : ExactLiftingSemantics (galKProfinite K) row.degree (qOf K FF)
      (genAsmCore row) nu0 (standardNumerics row.degree))
    (askStokes : StokesDualityCertificate (galKProfinite K) row.degree (qOf K FF)
      (genAsmCore row) nu0 (standardNumerics row.degree) (smulZmod2GalK K)) :
    ∃ G : GenAsmBranch K B, G.pres = row ∧ Nonempty (GenAsmRowResidual G F.T) := by
  obtain ⟨G, hp, hnu⟩ := H
  refine ⟨G, hp, ?_⟩
  obtain ⟨pres, hdeg, nu, hnuP, realization⟩ := G
  subst hp
  obtain rfl : nu = nu0 := eq_of_heq hnu
  exact ⟨mpcRow_genAsmRowResidual_of_counting F.T askExactLifting askStokes cand F.params
    F.params_n F.params_qK F.ramifiedData⟩

/-- **The `M0` rows' residual over the analytic clauses alone.**  Free in `(α, h)`; each frozen
`M0` row is one instantiation, with `H` supplied by §2. -/
theorem canRec_rowResidual_M0_of_analytic (α h : ℕ) (hα : 1 ≤ α)
    (H : ∃ G : GenAsmBranch K B, G.pres = .M0 α h ∧ HEq G.nuP (fieldId_mNuZtwo α h hα))
    (F : GenAsmFieldInputs K B FF (SelectedPresentation.M0 α h).degree)
    (candExactLifting : ExactLiftingSemantics (GammaR (2 + 2 * h) (qOf K FF) (mCompactW α h))
      (2 + 2 * h) (qOf K FF) (DM α h) (fieldId_mNuZtwo α h hα) (standardNumerics (2 + 2 * h)))
    (candStokes : StokesDualityCertificate (GammaR (2 + 2 * h) (qOf K FF) (mCompactW α h))
      (2 + 2 * h) (qOf K FF) (DM α h) (fieldId_mNuZtwo α h hα) (standardNumerics (2 + 2 * h))
      (scalarActionZmodTwo _))
    (candScalar : ScalarHilbertCertificate (GammaR (2 + 2 * h) (qOf K FF) (mCompactW α h))
      (2 + 2 * h) (standardNumerics (2 + 2 * h)) (scalarActionZmodTwo _))
    (candDeterminant : AffineDeterminantCertificate
      (GammaR (2 + 2 * h) (qOf K FF) (mCompactW α h)) (2 + 2 * h) (qOf K FF) (DM α h)
      (fieldId_mNuZtwo α h hα) (standardNumerics (2 + 2 * h))
      (tameOfSpec (2 + 2 * h) (qOf K FF) (mCompactW α h)
        (mTameSpecializes α h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF)))
      (mPro2 α h (qOf K FF) hα (qOf_ne_zero K FF) (even_qOf K FF))
      (mCompat α h (qOf K FF) hα (qOf_ne_zero K FF) (even_qOf K FF)
        (mTameSpecializes α h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF))
        (fieldId_mNuZtwo α h hα) (canRec_mNuZtwo_sigma α h hα) (canRec_mNuZtwo_wild α h hα))
      (scalarActionZmodTwo _))
    (askExactLifting : ExactLiftingSemantics (galKProfinite K)
      (SelectedPresentation.M0 α h).degree (qOf K FF) (genAsmCore (.M0 α h))
      (fieldId_mNuZtwo α h hα) (standardNumerics (SelectedPresentation.M0 α h).degree))
    (askStokes : StokesDualityCertificate (galKProfinite K) (SelectedPresentation.M0 α h).degree
      (qOf K FF) (genAsmCore (.M0 α h)) (fieldId_mNuZtwo α h hα)
      (standardNumerics (SelectedPresentation.M0 α h).degree) (smulZmod2GalK K)) :
    ∃ G : GenAsmBranch K B, G.pres = .M0 α h ∧ Nonempty (GenAsmRowResidual G F.T) :=
  canRec_rowResidual_of_tied H F
    (canRec_candM α h (qOf K FF) hα (qOf_ne_zero K FF) (even_qOf K FF)
      candExactLifting candStokes candScalar candDeterminant)
    askExactLifting askStokes

/-- **The `N0` rows' residual over the analytic clauses alone.** -/
theorem canRec_rowResidual_N0_of_analytic (α h : ℕ)
    (H : ∃ G : GenAsmBranch K B, G.pres = .N0 α h ∧
      HEq G.nuP (SelectedCoreLeavesRN.nNuZtwo α h))
    (F : GenAsmFieldInputs K B FF (SelectedPresentation.N0 α h).degree)
    (candExactLifting : ExactLiftingSemantics (GammaR (2 + 2 * h) (qOf K FF) (nCompactW α h))
      (2 + 2 * h) (qOf K FF) (DN α h) (SelectedCoreLeavesRN.nNuZtwo α h)
      (standardNumerics (2 + 2 * h)))
    (candStokes : StokesDualityCertificate (GammaR (2 + 2 * h) (qOf K FF) (nCompactW α h))
      (2 + 2 * h) (qOf K FF) (DN α h) (SelectedCoreLeavesRN.nNuZtwo α h)
      (standardNumerics (2 + 2 * h)) (scalarActionZmodTwo _))
    (candScalar : ScalarHilbertCertificate (GammaR (2 + 2 * h) (qOf K FF) (nCompactW α h))
      (2 + 2 * h) (standardNumerics (2 + 2 * h)) (scalarActionZmodTwo _))
    (candDeterminant : AffineDeterminantCertificate
      (GammaR (2 + 2 * h) (qOf K FF) (nCompactW α h)) (2 + 2 * h) (qOf K FF) (DN α h)
      (SelectedCoreLeavesRN.nNuZtwo α h) (standardNumerics (2 + 2 * h))
      (tameOfSpec (2 + 2 * h) (qOf K FF) (nCompactW α h)
        (genCertNTameSpecializes α h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF)))
      (genCertNPro2 α h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF))
      (genCertNCompat α h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF)
        (genCertNTameSpecializes α h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF))
        (SelectedCoreLeavesRN.nNuZtwo α h) (SelectedCoreLeavesRN.nNuZtwo_sigma α h)
        (SelectedCoreLeavesRN.nNuZtwo_wild α h))
      (scalarActionZmodTwo _))
    (askExactLifting : ExactLiftingSemantics (galKProfinite K)
      (SelectedPresentation.N0 α h).degree (qOf K FF) (genAsmCore (.N0 α h))
      (SelectedCoreLeavesRN.nNuZtwo α h)
      (standardNumerics (SelectedPresentation.N0 α h).degree))
    (askStokes : StokesDualityCertificate (galKProfinite K) (SelectedPresentation.N0 α h).degree
      (qOf K FF) (genAsmCore (.N0 α h)) (SelectedCoreLeavesRN.nNuZtwo α h)
      (standardNumerics (SelectedPresentation.N0 α h).degree) (smulZmod2GalK K)) :
    ∃ G : GenAsmBranch K B, G.pres = .N0 α h ∧ Nonempty (GenAsmRowResidual G F.T) :=
  canRec_rowResidual_of_tied H F
    (canRec_candN α h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF)
      candExactLifting candStokes candScalar candDeterminant)
    askExactLifting askStokes

/-- **The `Mpc` rows' residual over the analytic clauses alone**, at the `η = 1` display and
`h = 0`, where the row's own certificate producer lives. -/
theorem canRec_rowResidual_Mpc_of_analytic (α r : ℕ) (epsilon : Bool) (hα : 1 ≤ α)
    (H : ∃ G : GenAsmBranch K B, G.pres = .Mpc α r epsilon .one 0 ∧
      HEq G.nuP (mpcNu α r (p epsilon r) hα))
    (F : GenAsmFieldInputs K B FF (SelectedPresentation.Mpc α r epsilon .one 0).degree)
    (candExactLifting : ExactLiftingSemantics
      (GammaR (2 + 2 * 0) (qOf K FF) (Words.Mpc.mpcW α r (p epsilon r) .one 0)) (2 + 2 * 0)
      (qOf K FF) (DM α 0) (mpcNu α r (p epsilon r) hα) (standardNumerics (2 + 2 * 0)))
    (candStokes : StokesDualityCertificate
      (GammaR (2 + 2 * 0) (qOf K FF) (Words.Mpc.mpcW α r (p epsilon r) .one 0)) (2 + 2 * 0)
      (qOf K FF) (DM α 0) (mpcNu α r (p epsilon r) hα) (standardNumerics (2 + 2 * 0))
      (scalarActionZmodTwo _))
    (candScalar : ScalarHilbertCertificate
      (GammaR (2 + 2 * 0) (qOf K FF) (Words.Mpc.mpcW α r (p epsilon r) .one 0)) (2 + 2 * 0)
      (standardNumerics (2 + 2 * 0)) (scalarActionZmodTwo _))
    (candDeterminant : AffineDeterminantCertificate
      (GammaR (2 + 2 * 0) (qOf K FF) (Words.Mpc.mpcW α r (p epsilon r) .one 0)) (2 + 2 * 0)
      (qOf K FF) (DM α 0) (mpcNu α r (p epsilon r) hα) (standardNumerics (2 + 2 * 0))
      (tameOfSpec (2 + 2 * 0) (qOf K FF) (Words.Mpc.mpcW α r (p epsilon r) .one 0)
        (mpcTameSpecializes α r (p epsilon r) (qOf K FF) hα (qOf_ne_zero K FF) (even_qOf K FF)))
      (mpcPro2 α r (p epsilon r) (qOf K FF) hα (qOf_ne_zero K FF) (even_qOf K FF))
      (mpcCompat α r (p epsilon r) (qOf K FF) hα (qOf_ne_zero K FF) (even_qOf K FF)
        (mpcTameSpecializes α r (p epsilon r) (qOf K FF) hα (qOf_ne_zero K FF) (even_qOf K FF))
        (mpcNu α r (p epsilon r) hα) (mpcNu_sigma α r (p epsilon r) hα)
        (mpcNu_wild α r (p epsilon r) hα))
      (scalarActionZmodTwo _))
    (askExactLifting : ExactLiftingSemantics (galKProfinite K)
      (SelectedPresentation.Mpc α r epsilon .one 0).degree (qOf K FF)
      (genAsmCore (.Mpc α r epsilon .one 0)) (mpcNu α r (p epsilon r) hα)
      (standardNumerics (SelectedPresentation.Mpc α r epsilon .one 0).degree))
    (askStokes : StokesDualityCertificate (galKProfinite K)
      (SelectedPresentation.Mpc α r epsilon .one 0).degree (qOf K FF)
      (genAsmCore (.Mpc α r epsilon .one 0)) (mpcNu α r (p epsilon r) hα)
      (standardNumerics (SelectedPresentation.Mpc α r epsilon .one 0).degree)
      (smulZmod2GalK K)) :
    ∃ G : GenAsmBranch K B, G.pres = .Mpc α r epsilon .one 0 ∧
      Nonempty (GenAsmRowResidual G F.T) :=
  canRec_rowResidual_of_tied H F
    (canRec_candMpc α r (qOf K FF) epsilon hα (qOf_ne_zero K FF) (even_qOf K FF)
      candExactLifting candStokes candScalar candDeterminant)
    askExactLifting askStokes

end RowResidual

/-! ## §5 The four rows

Each row gets two statements.  The named theorem carries `cand` as a single binder, so its
hypothesis list is the row's table entry: **the row's own `CAND` certificate, and the two `ASK`
counting blocks**, and nothing else.  The `_analytic` companion is §4's shape lemma already
instantiated at the row, so its (elaborated) type replaces `cand` by the four analytic clauses
at the row's candidate carrier; the instantiation is the acceptance check that §2's branch datum
and §3's producer agree on the marking. -/

section Rows

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] {R : LocalReciprocity}

/-- **`ℚ₂(√−2)`, the pilot row.**  `N0 2 0` at `nNuZtwo 2 0`. -/
theorem canRec_rowResidual_sqrtNegTwo [T2Space (GalK KSqrtNegTwo)]
    (B : MarkedRecip R KSqrtNegTwo) {FF : DyadicUnitFiltration KSqrtNegTwo}
    (F : GenAsmFieldInputs KSqrtNegTwo B FF (SelectedPresentation.N0 2 0).degree)
    (cand : WordCertificate (SelectedPresentation.N0 2 0).degree (qOf KSqrtNegTwo FF)
      (SelectedPresentation.N0 2 0).word (genAsmCore (.N0 2 0)) (genAsmCoreIsProP (.N0 2 0))
      (SelectedCoreLeavesRN.nNuZtwo 2 0)
      (standardNumerics (SelectedPresentation.N0 2 0).degree))
    (askExactLifting : ExactLiftingSemantics (galKProfinite KSqrtNegTwo)
      (SelectedPresentation.N0 2 0).degree (qOf KSqrtNegTwo FF) (genAsmCore (.N0 2 0))
      (SelectedCoreLeavesRN.nNuZtwo 2 0)
      (standardNumerics (SelectedPresentation.N0 2 0).degree))
    (askStokes : StokesDualityCertificate (galKProfinite KSqrtNegTwo)
      (SelectedPresentation.N0 2 0).degree (qOf KSqrtNegTwo FF) (genAsmCore (.N0 2 0))
      (SelectedCoreLeavesRN.nNuZtwo 2 0)
      (standardNumerics (SelectedPresentation.N0 2 0).degree) (smulZmod2GalK KSqrtNegTwo)) :
    ∃ G : GenAsmBranch KSqrtNegTwo B, G.pres = .N0 2 0 ∧ Nonempty (GenAsmRowResidual G F.T) :=
  canRec_rowResidual_of_tied (canRec_branch_sqrtNegTwo B) F cand askExactLifting askStokes

/-- **`ℚ₂(√2)`.**  `M0 3 0` at `fieldId_mNuZtwo 3 0`. -/
theorem canRec_rowResidual_sqrtTwo [T2Space (GalK KSqrtTwo)] (B : MarkedRecip R KSqrtTwo)
    {FF : DyadicUnitFiltration KSqrtTwo}
    (F : GenAsmFieldInputs KSqrtTwo B FF (SelectedPresentation.M0 3 0).degree)
    (cand : WordCertificate (SelectedPresentation.M0 3 0).degree (qOf KSqrtTwo FF)
      (SelectedPresentation.M0 3 0).word (genAsmCore (.M0 3 0)) (genAsmCoreIsProP (.M0 3 0))
      (fieldId_mNuZtwo 3 0 (by omega))
      (standardNumerics (SelectedPresentation.M0 3 0).degree))
    (askExactLifting : ExactLiftingSemantics (galKProfinite KSqrtTwo)
      (SelectedPresentation.M0 3 0).degree (qOf KSqrtTwo FF) (genAsmCore (.M0 3 0))
      (fieldId_mNuZtwo 3 0 (by omega))
      (standardNumerics (SelectedPresentation.M0 3 0).degree))
    (askStokes : StokesDualityCertificate (galKProfinite KSqrtTwo)
      (SelectedPresentation.M0 3 0).degree (qOf KSqrtTwo FF) (genAsmCore (.M0 3 0))
      (fieldId_mNuZtwo 3 0 (by omega))
      (standardNumerics (SelectedPresentation.M0 3 0).degree) (smulZmod2GalK KSqrtTwo)) :
    ∃ G : GenAsmBranch KSqrtTwo B, G.pres = .M0 3 0 ∧ Nonempty (GenAsmRowResidual G F.T) :=
  canRec_rowResidual_of_tied (canRec_branch_sqrtTwo B) F cand askExactLifting askStokes

/-- **`ℚ₂(√5)`.**  `M0 2 0` at `fieldId_mNuZtwo 2 0`. -/
theorem canRec_rowResidual_sqrtFive [T2Space (GalK KSqrtFive)] (B : MarkedRecip R KSqrtFive)
    {FF : DyadicUnitFiltration KSqrtFive}
    (F : GenAsmFieldInputs KSqrtFive B FF (SelectedPresentation.M0 2 0).degree)
    (cand : WordCertificate (SelectedPresentation.M0 2 0).degree (qOf KSqrtFive FF)
      (SelectedPresentation.M0 2 0).word (genAsmCore (.M0 2 0)) (genAsmCoreIsProP (.M0 2 0))
      (fieldId_mNuZtwo 2 0 (by omega))
      (standardNumerics (SelectedPresentation.M0 2 0).degree))
    (askExactLifting : ExactLiftingSemantics (galKProfinite KSqrtFive)
      (SelectedPresentation.M0 2 0).degree (qOf KSqrtFive FF) (genAsmCore (.M0 2 0))
      (fieldId_mNuZtwo 2 0 (by omega))
      (standardNumerics (SelectedPresentation.M0 2 0).degree))
    (askStokes : StokesDualityCertificate (galKProfinite KSqrtFive)
      (SelectedPresentation.M0 2 0).degree (qOf KSqrtFive FF) (genAsmCore (.M0 2 0))
      (fieldId_mNuZtwo 2 0 (by omega))
      (standardNumerics (SelectedPresentation.M0 2 0).degree) (smulZmod2GalK KSqrtFive)) :
    ∃ G : GenAsmBranch KSqrtFive B, G.pres = .M0 2 0 ∧ Nonempty (GenAsmRowResidual G F.T) :=
  canRec_rowResidual_of_tied (canRec_branch_sqrtFive B) F cand askExactLifting askStokes

/-- **`ℚ₂(√10)`.**  `Mpc 2 1 false 1 0` at `mpcNu 2 1 (p false 1)`. -/
theorem canRec_rowResidual_sqrtTen [T2Space (GalK KSqrtTen)] (B : MarkedRecip R KSqrtTen)
    {FF : DyadicUnitFiltration KSqrtTen}
    (F : GenAsmFieldInputs KSqrtTen B FF
      (SelectedPresentation.Mpc 2 1 false .one 0).degree)
    (cand : WordCertificate (SelectedPresentation.Mpc 2 1 false .one 0).degree
      (qOf KSqrtTen FF) (SelectedPresentation.Mpc 2 1 false .one 0).word
      (genAsmCore (.Mpc 2 1 false .one 0)) (genAsmCoreIsProP (.Mpc 2 1 false .one 0))
      (mpcNu 2 1 (p false 1) (by omega))
      (standardNumerics (SelectedPresentation.Mpc 2 1 false .one 0).degree))
    (askExactLifting : ExactLiftingSemantics (galKProfinite KSqrtTen)
      (SelectedPresentation.Mpc 2 1 false .one 0).degree (qOf KSqrtTen FF)
      (genAsmCore (.Mpc 2 1 false .one 0)) (mpcNu 2 1 (p false 1) (by omega))
      (standardNumerics (SelectedPresentation.Mpc 2 1 false .one 0).degree))
    (askStokes : StokesDualityCertificate (galKProfinite KSqrtTen)
      (SelectedPresentation.Mpc 2 1 false .one 0).degree (qOf KSqrtTen FF)
      (genAsmCore (.Mpc 2 1 false .one 0)) (mpcNu 2 1 (p false 1) (by omega))
      (standardNumerics (SelectedPresentation.Mpc 2 1 false .one 0).degree)
      (smulZmod2GalK KSqrtTen)) :
    ∃ G : GenAsmBranch KSqrtTen B, G.pres = .Mpc 2 1 false .one 0 ∧
      Nonempty (GenAsmRowResidual G F.T) :=
  canRec_rowResidual_of_tied (canRec_branch_sqrtTen B) F cand askExactLifting askStokes

/-- `ℚ₂(√−2)`'s row over the four analytic clauses; the elaborated type is the row's full
table entry. -/
def canRec_analytic_sqrtNegTwo [T2Space (GalK KSqrtNegTwo)]
    (B : MarkedRecip R KSqrtNegTwo) (FF : DyadicUnitFiltration KSqrtNegTwo) :=
  canRec_rowResidual_N0_of_analytic (K := KSqrtNegTwo) (B := B) (FF := FF) 2 0
    (canRec_branch_sqrtNegTwo B)

/-- `ℚ₂(√2)`'s row over the four analytic clauses. -/
def canRec_analytic_sqrtTwo [T2Space (GalK KSqrtTwo)] (B : MarkedRecip R KSqrtTwo)
    (FF : DyadicUnitFiltration KSqrtTwo) :=
  canRec_rowResidual_M0_of_analytic (K := KSqrtTwo) (B := B) (FF := FF) 3 0 (by omega)
    (canRec_branch_sqrtTwo B)

/-- `ℚ₂(√5)`'s row over the four analytic clauses. -/
def canRec_analytic_sqrtFive [T2Space (GalK KSqrtFive)] (B : MarkedRecip R KSqrtFive)
    (FF : DyadicUnitFiltration KSqrtFive) :=
  canRec_rowResidual_M0_of_analytic (K := KSqrtFive) (B := B) (FF := FF) 2 0 (by omega)
    (canRec_branch_sqrtFive B)

/-- `ℚ₂(√10)`'s row over the four analytic clauses. -/
def canRec_analytic_sqrtTen [T2Space (GalK KSqrtTen)] (B : MarkedRecip R KSqrtTen)
    (FF : DyadicUnitFiltration KSqrtTen) :=
  canRec_rowResidual_Mpc_of_analytic (K := KSqrtTen) (B := B) (FF := FF) 2 1 false (by omega)
    (canRec_branch_sqrtTen B)

end Rows

/-! ## §6 Axiom pins

One line per declaration, **24** in all, in declaration order, measured against the mirror.
Four sets occur, and the split says something about where the cost of this lane sits.

* **std-3** (`propext, Classical.choice, Quot.sound`) on **all of §1 and all of §3**: the `M0`
  marking bridge, the three `CAND` producers, the pilot identification and the pilot producer.
  So *placing the committed word certificate on the row's canonical marking costs no campaign
  axiom at any of the three branch shapes*, and neither does the bridge that makes the `M0`
  case possible.
* **The `GaussZ` set** (`hilbertSymbol_normCriterion_finiteDyadic`,
  `relativeStiefelWhitney_dyadic`, `tateDualityAt`,
  `Foundations.absGalQ2_localEulerCharacteristic`) on §4's four declarations.  This is exactly
  `affineDeterminant_galK`'s own set, inherited through
  `Instances.MpcRow.mpcRow_genAsmRowResidual_of_counting`, which is where the `determinant`
  block is discharged.  `absGalQ2_isTopologicallyFinitelyGenerated` is **not** in it.
* **The even route's endpoint set** (`hilbertSymbol_normCriterion_finiteDyadic`, `tateDualityAt`,
  `Foundations.absGalQ2_isTopologicallyFinitelyGenerated`,
  `Foundations.absGalQ2_localEulerCharacteristic`) on `canRec_branch_sqrtNegTwo`, and that set
  **plus `peripheralCyclotomicAction`** on the other three branch data.  These are inherited
  verbatim from `fieldUni_genAsmBranch_*` and `mpcCert_genAsmBranch_*`: tying the marking into
  the conclusion costs nothing.
* **The union of the previous two** on §5's eight per-row declarations, and nothing beyond it. -/

section AxiomPins

#print axioms canRec_mNu_eq_mNuZtwo
#print axioms canRec_mNuZtwo_sigma
#print axioms canRec_mNuZtwo_wild
#print axioms canRec_branch_sqrtNegTwo
#print axioms canRec_branch_sqrtTwo
#print axioms canRec_branch_sqrtFive
#print axioms canRec_branch_sqrtTen
#print axioms canRec_candM
#print axioms canRec_candN
#print axioms canRec_candMpc
#print axioms canRec_pilotNuP_eq
#print axioms canRec_candPilot
#print axioms canRec_rowResidual_of_tied
#print axioms canRec_rowResidual_M0_of_analytic
#print axioms canRec_rowResidual_N0_of_analytic
#print axioms canRec_rowResidual_Mpc_of_analytic
#print axioms canRec_rowResidual_sqrtNegTwo
#print axioms canRec_rowResidual_sqrtTwo
#print axioms canRec_rowResidual_sqrtFive
#print axioms canRec_rowResidual_sqrtTen
#print axioms canRec_analytic_sqrtNegTwo
#print axioms canRec_analytic_sqrtTwo
#print axioms canRec_analytic_sqrtFive
#print axioms canRec_analytic_sqrtTen

end AxiomPins

end GQ2.Dyadic.Instances.CanonicalRecords

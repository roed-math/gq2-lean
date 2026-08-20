/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.SourceBoundaryReplacementRN
import GQ2.Dyadic.Instances.EvenMChangedWordCertificate
import GQ2.Dyadic.Instances.FieldFlexibleEvenMFinal

/-!
# Boundary-independent mobile source models for the even M rows

The compact-M and displayed-Mpc exact-lifting, Stokes, and scalar theorems are already
polymorphic in the pro-2 core and its `Ztwo` marking.  They therefore apply directly to the
field's intrinsic mobile marking; no canonical-C placement and no marking-compatible core
transport is needed.

This module packages those landed theorems as `SourceAnalyticCoreRN` records.  The field-facing
endpoints then show that the only remaining corrected-source input is a
`SourceAnalyticBoundaryRN` on that core, together with the pro-2 wild-kernel property.  In
particular, neither a new exact-lifting argument nor a new Stokes/scalar calculation remains.

The adapted tame map is deliberately not required to equal the canonical `tameOfSpec` map.
That is the precise freedom required by W337's tame-compatible no-go.
-/

namespace GQ2.Dyadic.Instances.EvenMMobileSourceModel

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Instances.SourceBoundaryReplacementRN
open GQ2.Dyadic.Instances.FieldFamilyFlexibleModelAssembly
open GQ2.Dyadic.Instances.FieldFamilyFlexibleAssembly
open GQ2.Dyadic.Instances.FieldFamilyGeneralAssemblyExact
open GQ2.Dyadic.Instances.FieldFlexibleEvenMFinal
open GQ2.Dyadic.Instances.MpcCandidateScalar
open GQ2.Dyadic.Instances.MpcCandidateStokes
open GQ2.Dyadic.Words.MCompact GQ2.Dyadic.Words.Mpc

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## Analytic cores -/

/-- The compact-M boundary-independent corrected analytic core at an arbitrary marked pro-2
slot. -/
noncomputable def mCompactAnalyticCoreRN
    {alpha h q : ℕ} (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (P : ProfiniteGrp) (hP : IsProP 2 P) (nuP : ContinuousMonoidHom P Ztwo) :
    SourceAnalyticCoreRN (2 + 2 * h) q P hP nuP
      (standardNumerics (2 + 2 * h)) where
  Γ := GammaR (2 + 2 * h) q (mCompactW alpha h)
  smulZmod2 := scalarActionZmodTwo _
  contSMulZmod2 := scalarActionZmodTwo_continuousSMul _
  htriv := scalarActionZmodTwo_triv _
  tfg := Count.gammaR_topologicallyFinitelyGenerated _ _ _
  exactLifting := RowClauses.rowCl_mCand_exactLiftingRN halpha hq0 hqe nuP
  stokes := RecordBlocks.recBl_mCand_stokes halpha hq0 hqe
  scalar := RowClauses.rowCl_mCand_scalar halpha hq0 hqe

/-- The displayed-Mpc boundary-independent corrected analytic core at an arbitrary marked
pro-2 slot. -/
noncomputable def mpcAnalyticCoreRN
    {alpha r h q : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta)
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r) (hqe : Even q)
    (P : ProfiniteGrp) (hP : IsProP 2 P) (nuP : ContinuousMonoidHom P Ztwo) :
    SourceAnalyticCoreRN (2 + 2 * h) q P hP nuP
      (standardNumerics (2 + 2 * h)) := by
  let A : SourceAnalyticCoreRN (2 + 2 * h) q P hP nuP
      (standardNumerics (2 + 2 * h)) :=
    { Γ := GammaR (2 + 2 * h) q
        (mpcW alpha r (p epsilon r) d.display h)
      smulZmod2 := scalarActionZmodTwo _
      contSMulZmod2 := scalarActionZmodTwo_continuousSMul _
      htriv := scalarActionZmodTwo_triv _
      tfg := Count.gammaR_topologicallyFinitelyGenerated _ _ _
      exactLifting := by
        have H := RecordBlocks.recBl_mpc_exactLiftingRN
          (alpha := alpha) (r := r) (h := h) (q := q) (epsilon := epsilon)
          d halpha hr hqe nuP
        rw [MProcyclicExact.gamma_sign_eq_display alpha r h q epsilon d] at H
        exact NProcyclic.exactLiftingRN_standard_congr (by omega) H
      stokes := by
        apply RecordBlocks.recBl_stokes_standard_congr
          (n := 2 * h + 2) (m := 2 + 2 * h) (by omega)
        exact mpcCand_stokes_displayed
          (alpha := alpha) (r := r) (pp := p epsilon r) (h := h) (q := q)
          d halpha hr hqe (P := P) (nuP := nuP)
      scalar := mpcCandidate_scalar d halpha hr hqe }
  exact A

/-! ## Field-facing source models -/

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- A compact-M adapted boundary on the intrinsic field marking supplies the complete flexible
source model. -/
noncomputable def mCompactFieldModelSourceRN
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (D : SourceAnalyticBoundaryRN
      (mCompactAnalyticCoreRN (alpha := alpha) (h := h) (q := qOf K FF)
        halpha (qOf_ne_zero K FF) (even_qOf K FF)
        (maxProPQuotient 2 (GalK K)) isProP_maxProPQuotient (fieldCoreNuZtwo B)))
    (hwild : IsProP 2 D.tame.toMonoidHom.ker) :
    FlexibleModelSourceRN (2 + 2 * h) (qOf K FF) (mCompactW alpha h)
      (maxProPQuotient 2 (GalK K)) isProP_maxProPQuotient
      (fieldCoreNuZtwo B) (standardNumerics (2 + 2 * h)) :=
  FlexibleModelSourceRN.ofAnalyticBoundary _ D (ContinuousMulEquiv.refl _)
    (fieldCoreNuZtwo_surjective B FF) hwild

/-- General-K compact-M reconstruction from only the adapted mobile boundary and wild-kernel
property. -/
theorem mCompactField_candidate_equiv_galKRN_of_mobileBoundary
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (D : SourceAnalyticBoundaryRN
      (mCompactAnalyticCoreRN (alpha := alpha) (h := h) (q := qOf K FF)
        halpha (qOf_ne_zero K FF) (even_qOf K FF)
        (maxProPQuotient 2 (GalK K)) isProP_maxProPQuotient (fieldCoreNuZtwo B)))
    (hwild : IsProP 2 D.tame.toMonoidHom.ker)
    (F : GenAsmCompatibleFieldInputs B FF (2 + 2 * h)) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (2 + 2 * h) (qOf K FF) (mCompactW alpha h) : ProfiniteGrp) : Type)
      (GalK K)) :=
  genAsmFlexible_candidate_equiv_galKRN_compatible_ofModelSource
    (mCompactFieldFlexibleBranch B FF alpha h hdeg) F
    (mCompactFieldModelSourceRN B FF halpha D hwild)

/-- A displayed-Mpc adapted boundary on the intrinsic field marking supplies the complete
flexible source model. -/
noncomputable def mpcFieldModelSourceRN
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha r h : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta)
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r)
    (D : SourceAnalyticBoundaryRN
      (mpcAnalyticCoreRN (alpha := alpha) (r := r) (h := h) (q := qOf K FF)
        (epsilon := epsilon) d halpha hr (even_qOf K FF)
        (maxProPQuotient 2 (GalK K)) isProP_maxProPQuotient (fieldCoreNuZtwo B)))
    (hwild : IsProP 2 D.tame.toMonoidHom.ker) :
    FlexibleModelSourceRN (2 + 2 * h) (qOf K FF)
      (mpcW alpha r (p epsilon r) d.display h)
      (maxProPQuotient 2 (GalK K)) isProP_maxProPQuotient
      (fieldCoreNuZtwo B) (standardNumerics (2 + 2 * h)) :=
  FlexibleModelSourceRN.ofAnalyticBoundary _ D (ContinuousMulEquiv.refl _)
    (fieldCoreNuZtwo_surjective B FF) hwild

/-- General-K displayed-Mpc reconstruction from only the adapted mobile boundary and
wild-kernel property. -/
theorem mpcField_candidate_equiv_galKRN_of_mobileBoundary
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha r h : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta)
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (D : SourceAnalyticBoundaryRN
      (mpcAnalyticCoreRN (alpha := alpha) (r := r) (h := h) (q := qOf K FF)
        (epsilon := epsilon) d halpha hr (even_qOf K FF)
        (maxProPQuotient 2 (GalK K)) isProP_maxProPQuotient (fieldCoreNuZtwo B)))
    (hwild : IsProP 2 D.tame.toMonoidHom.ker)
    (F : GenAsmCompatibleFieldInputs B FF (2 + 2 * h)) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (2 + 2 * h) (qOf K FF)
        (mpcW alpha r (p epsilon r) d.display h) : ProfiniteGrp) : Type)
      (GalK K)) :=
  genAsmFlexible_candidate_equiv_galKRN_compatible_ofModelSource
    (mpcFieldFlexibleBranch B FF alpha r h epsilon d hdeg) F
    (mpcFieldModelSourceRN B FF d halpha hr D hwild)

#print axioms mCompactAnalyticCoreRN
#print axioms mpcAnalyticCoreRN
#print axioms mCompactFieldModelSourceRN
#print axioms mCompactField_candidate_equiv_galKRN_of_mobileBoundary
#print axioms mpcFieldModelSourceRN
#print axioms mpcField_candidate_equiv_galKRN_of_mobileBoundary

end

end GQ2.Dyadic.Instances.EvenMMobileSourceModel

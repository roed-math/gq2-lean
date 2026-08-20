/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMChangedWordCertificate
import GQ2.Dyadic.Instances.FieldFlexibleEvenMFinal

/-!
# Field assembly for changed even-M presentation words

This module states the remaining even-M normal-form task without a hidden canonical-pivot
condition.  The field core and its unramified marking are intrinsic.  A compact-M or displayed
Mpc data packet chooses an adapted word, presents the field core with normalized alphabet rows,
and identifies the resulting candidate group with the standard analytic word while preserving
the tame quotient.

The changed-word certificate theorem then supplies the corrected residual, and the general
assembler produces the final field equivalence.  These are conditional consumers: W337 proves
that existence of either packet already forces the corresponding canonical C pivot.  All
analytic and reconstruction clauses are closed, but changing the word does not remove the
underlying pivot-placement problem.
-/

namespace GQ2.Dyadic.Instances.EvenMChangedWordFieldFinal

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Instances.FieldFamilyFlexibleAssembly
open GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate
open GQ2.Dyadic.Instances.FieldFamilyGeneralAssemblyExact
open GQ2.Dyadic.Instances.FieldFlexibleEvenMFinal
open GQ2.Dyadic.Instances.EvenMChangedWordCertificate
open GQ2.Dyadic.MCompact
open GQ2.Dyadic.Words.MCompact GQ2.Dyadic.Words.Mpc
open TameSpec

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)

/-- A flexible branch for an arbitrary word, placed directly on the field pro-2 core. -/
def fieldChangedWordBranch (n : ℕ) (R : PWord (Generator n))
    (hdeg : Module.finrank ℚ_[2] K = n) : GenAsmFlexibleBranch K B where
  degree := n
  word := R
  core := maxProPQuotient 2 (GalK K)
  coreIsProP := isProP_maxProPQuotient
  hdeg := hdeg
  nuP := fieldCoreNuZtwo B
  hnuP := fieldCoreNuZtwo_surjective B FF
  realization := fieldCoreRealization B

/-- The exact presentation packet left for a changed compact-M normal form. -/
structure MCompactChangedWordFieldData (alpha h : ℕ) where
  word : PWord (Generator (2 + 2 * h))
  core : FlexibleCoreLeavesRN (2 + 2 * h) word
    (maxProPQuotient 2 (GalK K)) (fieldCoreNuZtwo B)
  tameSpecialization : TameSpecializes (2 + 2 * h) (qOf K FF) word
  equiv : ContinuousMulEquiv
    ((GammaR (2 + 2 * h) (qOf K FF) word) : Type)
    ((GammaR (2 + 2 * h) (qOf K FF) (mCompactW alpha h)) : Type)
  tame_eq : tameOfSpec (2 + 2 * h) (qOf K FF) word tameSpecialization =
    (tameOfSpec (2 + 2 * h) (qOf K FF) (mCompactW alpha h)
      (GQ2.Dyadic.Instances.MCompactCore.mTameSpecializes
        alpha h (qOf K FF) (qOf_ne_zero K FF)
        (even_qOf K FF))).comp
      (equiv : ContinuousMonoidHom _ _)

/-- A changed compact-M field presentation has the corrected flexible residual. -/
def mCompactChangedWordFieldRowResidualRN
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (D : MCompactChangedWordFieldData B FF alpha h) :
    GenAsmFlexibleRowResidualRN FF
      (fieldChangedWordBranch B FF (2 + 2 * h) D.word hdeg) where
  cand := mCompactWordCertificateRN_of_wordEquiv halpha
    (qOf_ne_zero K FF) (even_qOf K FF) isProP_maxProPQuotient
    D.core D.tameSpecialization D.equiv D.tame_eq

/-- End-to-end general-K compact-M assembly after changing the presentation word. -/
theorem mCompactChangedWordField_candidate_equiv_galKRN
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (D : MCompactChangedWordFieldData B FF alpha h)
    (F : GenAsmCompatibleFieldInputs B FF (2 + 2 * h)) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (2 + 2 * h) (qOf K FF) D.word : ProfiniteGrp) : Type)
      (GalK K)) :=
  genAsmFlexible_candidate_equiv_galKRN_compatible
    (fieldChangedWordBranch B FF (2 + 2 * h) D.word hdeg) F
    (mCompactChangedWordFieldRowResidualRN B FF halpha hdeg D)

/-- The exact presentation packet left for a changed displayed Mpc normal form. -/
structure MpcChangedWordFieldData (alpha r h : ℕ) (epsilon : Bool)
    {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta) where
  one_le_alpha : 1 ≤ alpha
  word : PWord (Generator (2 + 2 * h))
  core : FlexibleCoreLeavesRN (2 + 2 * h) word
    (maxProPQuotient 2 (GalK K)) (fieldCoreNuZtwo B)
  tameSpecialization : TameSpecializes (2 + 2 * h) (qOf K FF) word
  equiv : ContinuousMulEquiv
    ((GammaR (2 + 2 * h) (qOf K FF) word) : Type)
    ((GammaR (2 + 2 * h) (qOf K FF)
      (mpcW alpha r (p epsilon r) d.display h)) : Type)
  tame_eq : tameOfSpec (2 + 2 * h) (qOf K FF) word tameSpecialization =
    (tameOfSpec (2 + 2 * h) (qOf K FF)
      (mpcW alpha r (p epsilon r) d.display h)
      (Count.tameSpecializes_mpcW (qOf_ne_zero K FF) (even_qOf K FF)
        one_le_alpha r (p epsilon r) d.display h)).comp
      (equiv : ContinuousMonoidHom _ _)

/-- A changed displayed Mpc field presentation has the corrected flexible residual. -/
def mpcChangedWordFieldRowResidualRN
    {alpha r h : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta)
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (D : MpcChangedWordFieldData B FF alpha r h epsilon d) :
    GenAsmFlexibleRowResidualRN FF
      (fieldChangedWordBranch B FF (2 + 2 * h) D.word hdeg) where
  cand := mpcWordCertificateRN_of_wordEquiv d halpha hr
    (qOf_ne_zero K FF) (even_qOf K FF) isProP_maxProPQuotient
    D.core D.tameSpecialization D.equiv D.tame_eq

/-- End-to-end general-K displayed Mpc assembly after changing the presentation word. -/
theorem mpcChangedWordField_candidate_equiv_galKRN
    {alpha r h : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta)
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (D : MpcChangedWordFieldData B FF alpha r h epsilon d)
    (F : GenAsmCompatibleFieldInputs B FF (2 + 2 * h)) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (2 + 2 * h) (qOf K FF) D.word : ProfiniteGrp) : Type)
      (GalK K)) :=
  genAsmFlexible_candidate_equiv_galKRN_compatible
    (fieldChangedWordBranch B FF (2 + 2 * h) D.word hdeg) F
    (mpcChangedWordFieldRowResidualRN B FF d halpha hr hdeg D)

#print axioms MCompactChangedWordFieldData
#print axioms mCompactChangedWordFieldRowResidualRN
#print axioms mCompactChangedWordField_candidate_equiv_galKRN
#print axioms MpcChangedWordFieldData
#print axioms mpcChangedWordFieldRowResidualRN
#print axioms mpcChangedWordField_candidate_equiv_galKRN

end

end GQ2.Dyadic.Instances.EvenMChangedWordFieldFinal

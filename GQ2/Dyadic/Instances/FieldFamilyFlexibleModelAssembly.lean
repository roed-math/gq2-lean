/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.FieldFamilyFlexibleAssembly

/-!
# General assembly from a flexible corrected source model

The corrected reconstruction theorem compares `SourceDataRN` records.  A
`WordCertificateRN` is one important way to construct such a source, but it also fixes the
canonical tame specialization of its presentation word.  W337 shows that transporting the
old even-M certificate through a tame-compatible word equivalence still forces the false
canonical-C pivot in the obstructed compact-M family.

This module exposes the weaker and mathematically exact reconstruction input.  A
`FlexibleModelSourceRN` consists of a corrected source, an equivalence from the desired
candidate group to its carrier, and the two tame/wild hypotheses used by reconstruction.  Its
tame and pro-2 boundary maps need not be the canonical maps obtained from `tameOfSpec` and a
fixed `CorePresentation`.

Ordinary word certificates embed as a regression.  The new interface therefore changes no
landed branch, but it identifies the honest general even-M task: construct one corrected
mobile-pivot source model.  No nilpotency class, distinguished core coordinate, or five-row
selector table occurs in the interface.
-/

namespace GQ2.Dyadic.Instances.FieldFamilyFlexibleModelAssembly

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Instances.FieldFamilyFlexibleAssembly
open GQ2.Dyadic.Instances.FieldFamilyGeneralAssemblyExact

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## The presentation-independent corrected model -/

/-- A corrected source model for a candidate word.  The candidate group is only required to
be continuously isomorphic to the source carrier; its tame boundary may be adapted to a
mobile-pivot normal form. -/
structure FlexibleModelSourceRN (n q : ℕ) (R : PWord (Generator n))
    (P : ProfiniteGrp) (hP : IsProP 2 P) (nuP : ContinuousMonoidHom P Ztwo)
    (SN : SourceNumerics n) where
  source : SourceDataRN n q P hP nuP SN
  equivCandidate : ContinuousMulEquiv ((GammaR n q R) : Type) (source.Γ : Type)
  tame_surjective : Function.Surjective source.tame
  wild_isProP : IsProP 2 source.tame.toMonoidHom.ker

namespace FlexibleModelSourceRN

variable {n q : ℕ} {R : PWord (Generator n)} {P : ProfiniteGrp}
  {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}

/-- Every ordinary corrected word certificate gives a flexible source model. -/
noncomputable def ofWordCertificate
    (W : WordCertificateRN n q R P hP nuP SN) (hq2 : 2 ≤ q) (hqe : Even q) :
    FlexibleModelSourceRN n q R P hP nuP SN where
  source := W.toSourceRN hq2 hqe
  equivCandidate := ContinuousMulEquiv.refl _
  tame_surjective := W.htame
  wild_isProP := W.hwild

end FlexibleModelSourceRN

/-! ## Generic reconstruction from the model -/

/-- A flexible source model compares directly with any arithmetic corrected source over the
same boundary slot. -/
theorem candidate_equiv_galK_of_modelSourceRN
    {n q : ℕ} {R : PWord (Generator n)} {P : ProfiniteGrp}
    {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    (M : FlexibleModelSourceRN n q R P hP nuP SN)
    (A : GalKArithmeticSourceRN n q P hP nuP SN K)
    (hq0 : q ≠ 0) (hqe : Even q) (hnuP : Function.Surjective nuP) :
    Nonempty (ContinuousMulEquiv (GammaR n q R) (GalK K)) := by
  obtain ⟨e⟩ := nonempty_continuousMulEquiv_of_sourcesRN M.source A.source
    hq0 hqe hnuP M.tame_surjective M.wild_isProP
      A.tame_surjective A.wild_isProP
  exact ⟨M.equivCandidate.trans (e.trans A.equivGalK)⟩

/-! ## Field-family handoff -/

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
/-- Compatibility-aware general-K assembly from a flexible corrected source model. -/
theorem genAsmFlexible_candidate_equiv_galKRN_compatible_ofModelSource
    (G : GenAsmFlexibleBranch K B)
    (F : GenAsmCompatibleFieldInputs B FF G.degree)
    (M : FlexibleModelSourceRN G.degree (qOf K FF) G.word G.core
      G.coreIsProP G.nuP (standardNumerics G.degree)) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup G.degree (qOf K FF) G.word : ProfiniteGrp) : Type) (GalK K)) := by
  let KS : KExactSupplyRN F.T G.degree G.core G.coreIsProP G.nuP :=
    kExactSupplyRN_of_markedCore G.hdeg G.realization.pro2
      G.realization.pro2_surjective G.realization.ker_pro2 G.realization.nu_compat
  let source : SourceDataRN G.degree (qOf K FF) G.core G.coreIsProP G.nuP
      (standardNumerics G.degree) :=
    KS.toSourceRN_compatible F.params F.params_n F.params_qK F.ramifiedData
  let A : GalKArithmeticSourceRN G.degree (qOf K FF) G.core G.coreIsProP G.nuP
      (standardNumerics G.degree) K :=
    { source := source
      equivGalK := ContinuousMulEquiv.refl (GalK K)
      tame_surjective := F.T.tameFK_surjective
      wild_isProP := F.T.ker_tameFK ▸ F.T.isProP }
  exact candidate_equiv_galK_of_modelSourceRN M A
    (qOf_ne_zero K FF) (even_qOf K FF) G.hnuP

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
/-- Regression: the model-source assembler specializes to the existing flexible
word-certificate assembler. -/
theorem genAsmFlexible_candidate_equiv_galKRN_compatible_ofWordCertificate
    (G : GenAsmFlexibleBranch K B)
    (F : GenAsmCompatibleFieldInputs B FF G.degree)
    (W : WordCertificateRN G.degree (qOf K FF) G.word G.core
      G.coreIsProP G.nuP (standardNumerics G.degree)) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup G.degree (qOf K FF) G.word : ProfiniteGrp) : Type) (GalK K)) :=
  genAsmFlexible_candidate_equiv_galKRN_compatible_ofModelSource G F
    (FlexibleModelSourceRN.ofWordCertificate W (two_le_qOf K FF) (even_qOf K FF))

#print axioms FlexibleModelSourceRN
#print axioms FlexibleModelSourceRN.ofWordCertificate
#print axioms candidate_equiv_galK_of_modelSourceRN
#print axioms genAsmFlexible_candidate_equiv_galKRN_compatible_ofModelSource
#print axioms genAsmFlexible_candidate_equiv_galKRN_compatible_ofWordCertificate

end

end GQ2.Dyadic.Instances.FieldFamilyFlexibleModelAssembly

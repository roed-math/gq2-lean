/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.CertificateSupplyFamilyRN
import GQ2.Dyadic.Instances.FieldFamilyFlexibleAssembly

/-!
# Certificate supply for a flexible presentation

W324 removes the frozen five-row table from the final assembly, but its input is still a full
`WordCertificateRN`.  This module removes the corresponding table dependence from certificate
supply.  A `FlexibleCoreLeavesRN` is an arbitrary `CorePresentation` with the two normalized
`Ztwo` rows.  The generic pro-2 bridge then supplies the core map, its kernel and surjectivity,
and cyclotomic compatibility.

`FlexibleCertificateLeavesRN` retains only the genuinely word-dependent data: tame
specialization, exact lifting, and the Stokes, scalar, and determinant certificates.  The
constructor `wordCertificateRN_of_flexibleLeaves` fills every routine field uniformly.  Thus an
adapted mobile-pivot presentation does not need a new assembly argument, nor does it need to
reprove the maximal-pro-2 bridge.

The canonical semantic rows embed as a regression, but no declaration in the general
constructor mentions `SelectedPresentation`, `BranchData`, or the five-row table.  The next
mathematical task is correspondingly sharp: construct these leaves for a tame-compatible
Nielsen transform of a known word, transporting the five retained fields across the induced
source equivalence.
-/

namespace GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Count
open GQ2.Dyadic.Instances.FieldFamilyFlexibleAssembly
open GQ2.Dyadic.Instances.FieldFamilyGeneralAssemblyExact
open TameSpec

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## The table-free structural core -/

/-- An arbitrary presented pro-2 core with the two normalized cyclotomic rows. -/
structure FlexibleCoreLeavesRN (n : ℕ) (R : PWord (Generator n)) (P : ProfiniteGrp)
    (nuP : ContinuousMonoidHom P Ztwo) where
  presentation : CorePresentation n R P
  nu_sigma : nuP (presentation.mark .sigma) = ztwoOne
  nu_wild : ∀ j : Fin (n + 1), nuP (presentation.mark (.wild j)) = 1

namespace FlexibleCoreLeavesRN

variable {n q : ℕ} {R : PWord (Generator n)} {P : ProfiniteGrp}
  {nuP : ContinuousMonoidHom P Ztwo}

/-- The tautological evaluated pro-2 relation. -/
def coreRel (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking n G) : G :=
  t.eval (pro2 R)

theorem proTwoWord (_C : FlexibleCoreLeavesRN n R P nuP)
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking n G) :
    t.eval (pro2 R) = coreRel (R := R) G t := rfl

/-- The candidate map to its presented pro-2 core. -/
noncomputable def pro2 (C : FlexibleCoreLeavesRN n R P nuP)
    (hq0 : q ≠ 0) (hqe : Even q) :
    ContinuousMonoidHom ((GammaR n q R) : Type) P :=
  CorePresentation.coreHom C.presentation hq0 hqe

/-- The generic core map has exactly the maximal pro-2 kernel. -/
theorem ker_pro2 (C : FlexibleCoreLeavesRN n R P nuP)
    (hq0 : q ≠ 0) (hqe : Even q) :
    (C.pro2 hq0 hqe).toMonoidHom.ker = proPKernel 2 ((GammaR n q R) : Type) :=
  CorePresentation.ker_coreHom C.presentation hq0 hqe

/-- The generic core map is onto. -/
theorem hpro2 (C : FlexibleCoreLeavesRN n R P nuP)
    (hq0 : q ≠ 0) (hqe : Even q) : Function.Surjective (C.pro2 hq0 hqe) :=
  CorePresentation.coreHom_surjective C.presentation hq0 hqe

/-- Cyclotomic compatibility follows from the normalized sigma and wild rows. -/
theorem compat (C : FlexibleCoreLeavesRN n R P nuP)
    (hq0 : q ≠ 0) (hqe : Even q) (hspec : TameSpecializes n q R) :
    ∀ g : ((GammaR n q R) : Type),
      nuTq q (tameOfSpec n q R hspec g) = nuP (C.pro2 hq0 hqe g) :=
  CorePresentation.nu_compat_coreHom C.presentation hq0 hqe hspec nuP
    C.nu_sigma C.nu_wild

/-- Every canonical semantic core forgets to the table-free structural interface. -/
noncomputable def ofSemanticSelected
    {FP : FieldParameters} {S : SemanticSelectionView FP}
    (C : SemanticSelectedCoreLeavesRN S P nuP) :
    FlexibleCoreLeavesRN S.semantic.degree S.semantic.word P nuP where
  presentation := C.presentation
  nu_sigma := C.nu_sigma
  nu_wild := C.nu_wild

end FlexibleCoreLeavesRN

/-! ## The exact non-routine leaves -/

/-- The genuinely word-dependent inputs left after the generic core bridge and routine source
fields have been removed. -/
structure FlexibleCertificateLeavesRN (n q : ℕ) (R : PWord (Generator n))
    (P : ProfiniteGrp) (hP : IsProP 2 P) (nuP : ContinuousMonoidHom P Ztwo)
    (SN : SourceNumerics n) (hq0 : q ≠ 0) (hqe : Even q) where
  tameSpecialization : TameSpecializes n q R
  core : FlexibleCoreLeavesRN n R P nuP
  exactLifting : ExactLiftingSemanticsRN (GammaR n q R) n q P nuP SN
  stokes : StokesDualityCertificate (GammaR n q R) n q P nuP SN
    (scalarActionZmodTwo (GammaR n q R))
  scalar : ScalarHilbertCertificate (GammaR n q R) n SN
    (scalarActionZmodTwo (GammaR n q R))
  determinant : AffineDeterminantCertificate (GammaR n q R) n q P nuP SN
    (tameOfSpec n q R tameSpecialization) (core.pro2 hq0 hqe)
    (core.compat hq0 hqe tameSpecialization)
    (scalarActionZmodTwo (GammaR n q R))

/-- Assemble a corrected word certificate for an arbitrary presented word. -/
noncomputable def wordCertificateRN_of_flexibleLeaves
    {n q : ℕ} {R : PWord (Generator n)} {P : ProfiniteGrp}
    {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
    {hq0 : q ≠ 0} {hqe : Even q}
    (L : FlexibleCertificateLeavesRN n q R P hP nuP SN hq0 hqe) :
    WordCertificateRN n q R P hP nuP SN where
  tameSpecialization := L.tameSpecialization
  coreRel := FlexibleCoreLeavesRN.coreRel
  proTwoWord := L.core.proTwoWord
  pro2 := L.core.pro2 hq0 hqe
  ker_pro2 := L.core.ker_pro2 hq0 hqe
  hpro2 := L.core.hpro2 hq0 hqe
  compat := L.core.compat hq0 hqe L.tameSpecialization
  tfg := Count.gammaR_topologicallyFinitelyGenerated _ _ _
  smulZmod2 := scalarActionZmodTwo _
  contSMulZmod2 := scalarActionZmodTwo_continuousSMul _
  htriv := scalarActionZmodTwo_triv _
  exactLifting := L.exactLifting
  stokes := L.stokes
  scalar := L.scalar
  determinant := L.determinant
  htame := Count.htame_of_tameSpecializes L.tameSpecialization
  hwild := Count.hwild_of_tameSpecializes L.tameSpecialization

/-! ## Direct handoff to flexible general assembly -/

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}

/-- Flexible certificate leaves directly supply the row residual consumed by W324. -/
noncomputable def GenAsmFlexibleRowResidualRN.ofFlexibleLeaves
    (G : GenAsmFlexibleBranch K B)
    (L : FlexibleCertificateLeavesRN G.degree (qOf K FF) G.word G.core
      G.coreIsProP G.nuP (standardNumerics G.degree)
      (by have := two_le_qOf K FF; omega) (even_qOf K FF)) :
    GenAsmFlexibleRowResidualRN FF G where
  cand := wordCertificateRN_of_flexibleLeaves L

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
/-- End-to-end compatible assembly from the table-free certificate leaves. -/
theorem genAsmFlexible_candidate_equiv_galKRN_compatible_ofFlexibleLeaves
    (G : GenAsmFlexibleBranch K B)
    (F : GenAsmCompatibleFieldInputs B FF G.degree)
    (L : FlexibleCertificateLeavesRN G.degree (qOf K FF) G.word G.core
      G.coreIsProP G.nuP (standardNumerics G.degree)
      (by have := two_le_qOf K FF; omega) (even_qOf K FF)) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup G.degree (qOf K FF) G.word : ProfiniteGrp) : Type) (GalK K)) :=
  genAsmFlexible_candidate_equiv_galKRN_compatible G F
    (GenAsmFlexibleRowResidualRN.ofFlexibleLeaves G L)

#print axioms FlexibleCoreLeavesRN
#print axioms FlexibleCoreLeavesRN.pro2
#print axioms FlexibleCoreLeavesRN.ker_pro2
#print axioms FlexibleCoreLeavesRN.hpro2
#print axioms FlexibleCoreLeavesRN.compat
#print axioms FlexibleCoreLeavesRN.ofSemanticSelected
#print axioms FlexibleCertificateLeavesRN
#print axioms wordCertificateRN_of_flexibleLeaves
#print axioms GenAsmFlexibleRowResidualRN.ofFlexibleLeaves
#print axioms genAsmFlexible_candidate_equiv_galKRN_compatible_ofFlexibleLeaves

end

end GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate

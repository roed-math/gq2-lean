/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate
import GQ2.Dyadic.SourceTransportRN

/-!
# Transporting a flexible certificate from a reference word

W326 transports the complete corrected source record across a continuous group equivalence.
This module packages the exact compatibility required to apply that theorem to two candidate
words.

A `BoundaryCompatibleWordEquivRN` is an equivalence from the new candidate group to a certified
reference candidate, together with the two commuting boundary squares: one for the tame map and
one for the presented pro-2 core.  There is no analytic premise.  From this packet,
`FlexibleCertificateLeavesRN.ofTransport` transports exact lifting, Stokes duality, scalar
counts, and both determinant branches; W325 then rebuilds the full word certificate.

The final two declarations feed the transported certificate directly into the table-free W324
assembly.  Consequently the remaining mobile-pivot task is now one precise group-presentation
problem: construct a tame-compatible Nielsen equivalence and prove its two generator-level
boundary identities.
-/

namespace GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificateTransport

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Instances.FieldFamilyFlexibleAssembly
open GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate
open GQ2.Dyadic.Instances.FieldFamilyGeneralAssemblyExact
open TameSpec

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## The exact transport packet -/

/-- An equivalence of candidate words commuting with the tame and pro-2 boundary maps. -/
structure BoundaryCompatibleWordEquivRN
    {n q : ℕ} {R₀ R₁ : PWord (Generator n)} {P : ProfiniteGrp}
    {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
    (hq0 : q ≠ 0) (hqe : Even q)
    (W : WordCertificateRN n q R₀ P hP nuP SN)
    (C : FlexibleCoreLeavesRN n R₁ P nuP)
    (hspec : TameSpecializes n q R₁) where
  equiv : ContinuousMulEquiv ((GammaR n q R₁) : Type) ((GammaR n q R₀) : Type)
  tame_eq : tameOfSpec n q R₁ hspec =
    (tameOfSpec n q R₀ W.tameSpecialization).comp
      (equiv : ContinuousMonoidHom ((GammaR n q R₁) : Type) ((GammaR n q R₀) : Type))
  pro2_eq : C.pro2 hq0 hqe = W.pro2.comp
    (equiv : ContinuousMonoidHom ((GammaR n q R₁) : Type) ((GammaR n q R₀) : Type))

/-- Transport every non-routine flexible certificate leaf from the reference word. -/
noncomputable def FlexibleCertificateLeavesRN.ofTransport
    {n q : ℕ} {R₀ R₁ : PWord (Generator n)} {P : ProfiniteGrp}
    {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
    {hq0 : q ≠ 0} {hqe : Even q}
    (W : WordCertificateRN n q R₀ P hP nuP SN) (hq2 : 2 ≤ q)
    (C : FlexibleCoreLeavesRN n R₁ P nuP)
    (hspec : TameSpecializes n q R₁)
    (T : BoundaryCompatibleWordEquivRN hq0 hqe W C hspec) :
    FlexibleCertificateLeavesRN n q R₁ P hP nuP SN hq0 hqe := by
  let S := (W.toSourceRN hq2 hqe).transport T.equiv
    (scalarActionZmodTwo (GammaR n q R₁))
    (scalarActionZmodTwo_continuousSMul (GammaR n q R₁))
    (scalarActionZmodTwo_triv (GammaR n q R₁))
  refine
    { tameSpecialization := hspec
      core := C
      exactLifting := S.exactLifting
      stokes := S.stokes
      scalar := S.scalar
      determinant := ?_ }
  exact (affineDeterminantCertificate_congr
    (C.compat hq0 hqe hspec) S.compat _ T.tame_eq T.pro2_eq).mpr S.determinant

/-- A boundary-compatible word equivalence transports the complete corrected certificate. -/
noncomputable def wordCertificateRN_of_transport
    {n q : ℕ} {R₀ R₁ : PWord (Generator n)} {P : ProfiniteGrp}
    {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
    {hq0 : q ≠ 0} {hqe : Even q}
    (W : WordCertificateRN n q R₀ P hP nuP SN) (hq2 : 2 ≤ q)
    (C : FlexibleCoreLeavesRN n R₁ P nuP)
    (hspec : TameSpecializes n q R₁)
    (T : BoundaryCompatibleWordEquivRN hq0 hqe W C hspec) :
    WordCertificateRN n q R₁ P hP nuP SN :=
  wordCertificateRN_of_flexibleLeaves (FlexibleCertificateLeavesRN.ofTransport W hq2 C hspec T)

/-! ## Direct general-K consumers -/

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}

/-- A certified reference word and a compatible transport supply the flexible row residual. -/
noncomputable def GenAsmFlexibleRowResidualRN.ofTransport
    (G : GenAsmFlexibleBranch K B)
    {R₀ : PWord (Generator G.degree)}
    (W : WordCertificateRN G.degree (qOf K FF) R₀ G.core G.coreIsProP G.nuP
      (standardNumerics G.degree))
    (C : FlexibleCoreLeavesRN G.degree G.word G.core G.nuP)
    (hspec : TameSpecializes G.degree (qOf K FF) G.word)
    (T : BoundaryCompatibleWordEquivRN (by have := two_le_qOf K FF; omega)
      (even_qOf K FF) W C hspec) :
    GenAsmFlexibleRowResidualRN FF G where
  cand := wordCertificateRN_of_transport W (two_le_qOf K FF) C hspec T

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
/-- End-to-end compatible general-K assembly from a certified reference word and transport. -/
theorem genAsmFlexible_candidate_equiv_galKRN_compatible_ofTransport
    (G : GenAsmFlexibleBranch K B)
    (F : GenAsmCompatibleFieldInputs B FF G.degree)
    {R₀ : PWord (Generator G.degree)}
    (W : WordCertificateRN G.degree (qOf K FF) R₀ G.core G.coreIsProP G.nuP
      (standardNumerics G.degree))
    (C : FlexibleCoreLeavesRN G.degree G.word G.core G.nuP)
    (hspec : TameSpecializes G.degree (qOf K FF) G.word)
    (T : BoundaryCompatibleWordEquivRN (by have := two_le_qOf K FF; omega)
      (even_qOf K FF) W C hspec) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup G.degree (qOf K FF) G.word : ProfiniteGrp) : Type) (GalK K)) :=
  genAsmFlexible_candidate_equiv_galKRN_compatible G F
    (GenAsmFlexibleRowResidualRN.ofTransport G W C hspec T)

#print axioms BoundaryCompatibleWordEquivRN
#print axioms FlexibleCertificateLeavesRN.ofTransport
#print axioms wordCertificateRN_of_transport
#print axioms GenAsmFlexibleRowResidualRN.ofTransport
#print axioms genAsmFlexible_candidate_equiv_galKRN_compatible_ofTransport

end

end GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificateTransport

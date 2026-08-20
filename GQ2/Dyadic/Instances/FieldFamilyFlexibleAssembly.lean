/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.FieldFamilyGeneralAssemblyExact

/-!
# General assembly beyond the frozen five-row table

W323 shows that the unchanged canonical compact-M row is not a viable universal target.  This
module removes that accidental restriction from the assembly layer.  A
`GenAsmFlexibleBranch` carries an arbitrary word, pro-2 core, marking, and corrected field
realization.  Its sole row-dependent obligation is the same `WordCertificateRN` used by the
canonical campaign.

The compatibility-aware assembly is completely insensitive to the five-row constructor table,
so `genAsmFlexible_candidate_equiv_galKRN_compatible` reconstructs the candidate as `G_K` from
that one certificate and the W322 field packet.  Every old `GenAsmBranch` embeds
definitionally, providing regression coverage.  The remaining general M task can therefore be
stated honestly: construct a flexible word certificate adapted to the intrinsic mobile pivot.
It need not, and in the W323 arithmetic pattern cannot, pretend to be the frozen compact-M
marking.
-/

namespace GQ2.Dyadic.Instances.FieldFamilyFlexibleAssembly

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Instances.FieldFamilyGeneralAssemblyExact

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- A corrected general-assembly branch whose word and pro-2 core are not restricted to the
five canonical rows. -/
structure GenAsmFlexibleBranch (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] {R : LocalReciprocity} (B : MarkedRecip R K) where
  degree : ℕ
  word : PWord (Generator degree)
  core : ProfiniteGrp
  coreIsProP : IsProP 2 (core : Type)
  hdeg : Module.finrank ℚ_[2] K = degree
  nuP : ContinuousMonoidHom core Ztwo
  hnuP : Function.Surjective nuP
  realization : MarkedCoreRealization (K := K) (B := B) core nuP

namespace GenAsmFlexibleBranch

variable {B : MarkedRecip R K}

/-- Every canonical row is a flexible branch. -/
noncomputable def ofCanonical (G : GenAsmBranch K B) :
    GenAsmFlexibleBranch K B where
  degree := G.degree
  word := G.word
  core := G.core
  coreIsProP := G.coreIsProP
  hdeg := G.hdeg
  nuP := G.nuP
  hnuP := G.hnuP
  realization := G.realization

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
@[simp] theorem ofCanonical_degree (G : GenAsmBranch K B) :
    (ofCanonical G).degree = G.degree := rfl

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
@[simp] theorem ofCanonical_word (G : GenAsmBranch K B) :
    (ofCanonical G).word = G.word := rfl

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
@[simp] theorem ofCanonical_core (G : GenAsmBranch K B) :
    (ofCanonical G).core = G.core := rfl

end GenAsmFlexibleBranch

/-- The sole row-dependent obligation for a flexible corrected branch. -/
structure GenAsmFlexibleRowResidualRN {R : LocalReciprocity}
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {B : MarkedRecip R K} (FF : DyadicUnitFiltration K)
    (G : GenAsmFlexibleBranch K B) where
  cand : WordCertificateRN G.degree (qOf K FF) G.word G.core G.coreIsProP G.nuP
    (standardNumerics G.degree)

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
/-- Compatibility-aware corrected assembly for an arbitrary flexible word and marked core. -/
theorem genAsmFlexible_candidate_equiv_galKRN_compatible
    {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}
    (G : GenAsmFlexibleBranch K B)
    (F : GenAsmCompatibleFieldInputs B FF G.degree)
    (S : GenAsmFlexibleRowResidualRN FF G) :
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
  exact candidate_equiv_galK_of_supplyRN S.cand A
    (two_le_qOf K FF) (even_qOf K FF) G.hnuP

/-- A canonical corrected residual forgets to the flexible interface. -/
noncomputable def GenAsmFlexibleRowResidualRN.ofCanonical
    {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}
    (G : GenAsmBranch K B) (S : GenAsmRowResidualRN (FF := FF) G) :
    GenAsmFlexibleRowResidualRN FF (GenAsmFlexibleBranch.ofCanonical G) where
  cand := S.cand

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
/-- Regression: the flexible assembler specializes definitionally to every canonical row. -/
theorem genAsmFlexible_candidate_equiv_galKRN_compatible_ofCanonical
    {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}
    (G : GenAsmBranch K B)
    (F : GenAsmCompatibleFieldInputs B FF G.degree)
    (S : GenAsmRowResidualRN (FF := FF) G) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup G.degree (qOf K FF) G.word : ProfiniteGrp) : Type) (GalK K)) :=
  genAsmFlexible_candidate_equiv_galKRN_compatible
    (GenAsmFlexibleBranch.ofCanonical G) F
      (GenAsmFlexibleRowResidualRN.ofCanonical G S)

#print axioms GenAsmFlexibleBranch
#print axioms GenAsmFlexibleBranch.ofCanonical
#print axioms GenAsmFlexibleRowResidualRN
#print axioms genAsmFlexible_candidate_equiv_galKRN_compatible
#print axioms GenAsmFlexibleRowResidualRN.ofCanonical
#print axioms genAsmFlexible_candidate_equiv_galKRN_compatible_ofCanonical

end

end GQ2.Dyadic.Instances.FieldFamilyFlexibleAssembly

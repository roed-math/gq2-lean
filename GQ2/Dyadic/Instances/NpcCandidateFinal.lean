/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcCandidateRN
import GQ2.Dyadic.GeneralAssembly

/-!
# Corrected procyclic-N tied consumers

The arbitrary-unit, general-handle Npc word certificate is complete once its affine determinant
is supplied. This module transports that certificate through an already tied general-assembly
branch, first to `GenAsmRowResidualRN` and then to the corrected candidate/Galois equivalence.

There is deliberately no frozen field endpoint here. `Main.no_frozen_Npc` proves that the
canonical quadratic table contains no `.Npc` row. The corrected family selector can select an
Npc semantic word and its `NpcDisplayFor`, but it does not construct the field-side
`MarkedCoreRealization` needed by `GenAsmBranch`. A future binder-free field theorem must first
supply a tied selector of the shape
`exists G, G.pres = .Npc alpha r h d.data /\ HEq G.nuP (npcNu alpha r h eta)`.
-/

namespace GQ2.Dyadic.Instances.NpcCandidateFinal

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.Words GQ2.Dyadic.Words.Npc
open GQ2.Dyadic.Instances.NProcyclicCore
open GQ2.Dyadic.Instances.NpcCandidateRN
open GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.TameSpec

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {R : LocalReciprocity}

theorem npcRowResidualRN_of_tied_determinant
    {alpha r h : ℕ} {eta : ℤ_[2]ˣ}
    {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
    (B : MarkedRecip R K) {FF : DyadicUnitFiltration K} (G : GenAsmBranch K B)
    (d : NpcDisplayFor eta) (hα : 2 ≤ alpha)
    (hp : G.pres = .Npc alpha r h d.data)
    (hnu : HEq G.nuP (npcNu alpha r h eta))
    (determinant : AffineDeterminantCertificate
      (GammaR (2 + 2 * h) (qOf K FF) (npcWUnit alpha r h eta)) (2 + 2 * h)
      (qOf K FF) (DN alpha h) (npcNu alpha r h eta)
      (standardNumerics (2 + 2 * h))
      (tameOfSpec (2 + 2 * h) (qOf K FF) (npcWUnit alpha r h eta)
        (npcCandidate_tameSpecializes alpha r h (qOf K FF) d
          (qOf_ne_zero K FF) (even_qOf K FF)))
      (npcCandidate_pro2 alpha r h (qOf K FF) d
        (qOf_ne_zero K FF) (even_qOf K FF))
      (npcCandidate_compat alpha r h (qOf K FF) d
        (qOf_ne_zero K FF) (even_qOf K FF))
      (scalarActionZmodTwo _)) :
    Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  obtain ⟨pres, hdeg, nu, hnuP, realization⟩ := G
  subst hp
  obtain rfl : nu = npcNu alpha r h eta := eq_of_heq hnu
  refine ⟨⟨?_⟩⟩
  change WordCertificateRN (2 + 2 * h) (qOf K FF) (npcW alpha r h d.data)
    (DN alpha h) (isProP_DN alpha h) (npcNu alpha r h eta)
    (standardNumerics (2 + 2 * h))
  rw [← npcWUnit_eq_display alpha r h d]
  exact npcWordCertificateRN_of_determinant alpha r h (qOf K FF) d hα
    (qOf_ne_zero K FF) (even_qOf K FF) determinant

theorem npc_candidate_equiv_galKRN_of_tied_determinant
    {alpha r h : ℕ} {eta : ℤ_[2]ˣ}
    {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
    [T2Space (GalK K)] (B : MarkedRecip R K) {FF : DyadicUnitFiltration K}
    (G : GenAsmBranch K B) (d : NpcDisplayFor eta) (hα : 2 ≤ alpha)
    (hp : G.pres = .Npc alpha r h d.data)
    (hnu : HEq G.nuP (npcNu alpha r h eta))
    (F : GenAsmFieldInputs K B FF G.degree)
    (determinant : AffineDeterminantCertificate
      (GammaR (2 + 2 * h) (qOf K FF) (npcWUnit alpha r h eta)) (2 + 2 * h)
      (qOf K FF) (DN alpha h) (npcNu alpha r h eta)
      (standardNumerics (2 + 2 * h))
      (tameOfSpec (2 + 2 * h) (qOf K FF) (npcWUnit alpha r h eta)
        (npcCandidate_tameSpecializes alpha r h (qOf K FF) d
          (qOf_ne_zero K FF) (even_qOf K FF)))
      (npcCandidate_pro2 alpha r h (qOf K FF) d
        (qOf_ne_zero K FF) (even_qOf K FF))
      (npcCandidate_compat alpha r h (qOf K FF) d
        (qOf_ne_zero K FF) (even_qOf K FF))
      (scalarActionZmodTwo _)) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup G.degree (qOf K FF) G.word : ProfiniteGrp) : Type) (GalK K)) := by
  obtain ⟨S⟩ := npcRowResidualRN_of_tied_determinant B G d hα hp hnu determinant
  exact genAsm_candidate_equiv_galKRN G F S

#print axioms npcRowResidualRN_of_tied_determinant
#print axioms npc_candidate_equiv_galKRN_of_tied_determinant

end
end GQ2.Dyadic.Instances.NpcCandidateFinal

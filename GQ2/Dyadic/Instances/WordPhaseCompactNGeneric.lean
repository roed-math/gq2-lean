/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhaseCompactNFinal

/-!
# The general corrected compact-N endpoint

The compact-N determinant supply and corrected word certificate are already uniform in the
depth and handle count. This file connects that certificate to any general-assembly branch tied
to the canonical compact-N marking. The existing `sqrt(-2)` endpoint is the specialization at
`alpha = 2` and `h = 0`.
-/

namespace GQ2.Dyadic.Instances.WordPhaseCompactNGeneric

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words
open GQ2.Dyadic.Instances.WordPhaseCompactNFinal
open GQ2.Dyadic.SelectedCoreLeavesRN
open TameSpec MarkedCore

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {R : LocalReciprocity}

/-- A branch tied to a compact-N presentation and its canonical marking acquires the
corrected row residual with no additional analytic hypotheses. -/
theorem wPcN_rowResidualRN_of_tied
    {alpha h : Nat}
    {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
    (B : MarkedRecip R K) {FF : DyadicUnitFiltration K} (G : GenAsmBranch K B)
    (halpha : 2 ≤ alpha) (hp : G.pres = .N0 alpha h)
    (hnu : HEq G.nuP (nNuZtwo alpha h)) :
    Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  obtain ⟨pres, hdeg, nu, hnuP, realization⟩ := G
  subst hp
  obtain rfl : nu = nNuZtwo alpha h := eq_of_heq hnu
  exact ⟨⟨wPcNWordCertificateRN alpha h (qOf K FF) halpha
    (qOf_ne_zero K FF) (even_qOf K FF)⟩⟩

/-- Corrected general assembly consumes the canonical compact-N certificate at any tied
branch. -/
theorem wPcN_candidate_equiv_galKRN_of_tied
    {alpha h : Nat}
    {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
    [T2Space (GalK K)] (B : MarkedRecip R K) {FF : DyadicUnitFiltration K}
    (G : GenAsmBranch K B) (halpha : 2 ≤ alpha) (hp : G.pres = .N0 alpha h)
    (hnu : HEq G.nuP (nNuZtwo alpha h))
    (F : GenAsmFieldInputs K B FF G.degree) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup G.degree (qOf K FF) G.word : ProfiniteGrp) : Type) (GalK K)) := by
  obtain ⟨S⟩ := wPcN_rowResidualRN_of_tied B G halpha hp hnu
  exact genAsm_candidate_equiv_galKRN G F S

#print axioms wPcN_rowResidualRN_of_tied
#print axioms wPcN_candidate_equiv_galKRN_of_tied

end

end GQ2.Dyadic.Instances.WordPhaseCompactNGeneric

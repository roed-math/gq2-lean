/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLOddDegreeSingleResidual
import GQ2.Dyadic.SqCore.GradedOddClose

/-!
# The odd-L endpoint over its exact two-row marking residual

The general-h clearing packet is already closed by `SqCore.gOdd_nuClear`. Applying that theorem
to the existing two-rows-to-all-rows bridge shows that `SqNuForwardSupply` is equivalent to the
full marking supply consumed by the odd-L pro-2 block.

Consequently the general odd-degree endpoint needs no clearing, frame, cup, or relator premise.
Its remaining marking input is exactly the existence of an equivalence carrying the selected
`sigma` and `x0` rows. The packet-level oriented tame quotient and universal ramified
certificate supply remain explicit and are not addressed here.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Dyadic SqCore

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [T2Space (GalK K)] [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The closed odd clearing theorem upgrades the two selected rows to the full marking. -/
theorem sqFullNuForwardSupply_of_nuRows
    (B : MarkedRecip Rec K) {h : ℕ} (H : SqNuForwardSupply B h) :
    MarkingAudit.SqFullNuForwardSupply B h :=
  MarkingAudit.sqFullNuForwardSupply_of_clear (gOdd_nuClear h) H

omit [T2Space (GalK K)] [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The two selected rows are equivalent to the full-row supply. -/
theorem sqNuForwardSupply_iff_full
    (B : MarkedRecip Rec K) (h : ℕ) :
    SqNuForwardSupply B h ↔ MarkingAudit.SqFullNuForwardSupply B h :=
  ⟨sqFullNuForwardSupply_of_nuRows B, MarkingAudit.sqNuForwardSupply_of_full⟩

omit [T2Space (GalK K)] in
/-- The general odd-L endpoint over its genuine two-row arithmetic marking residual. -/
theorem gammaR_lSq_equiv_galK_oddDegree_of_nuRows_final
    (B : MarkedRecip Rec K) {FF : DyadicUnitFiltration K}
    (T : OrientedTameQuotientK B FF) (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (H : SqNuForwardSupply B h)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_oddDegree_of_fullNu B T D hdeg
    (sqFullNuForwardSupply_of_nuRows B H) ramifiedData

#print axioms sqFullNuForwardSupply_of_nuRows
#print axioms sqNuForwardSupply_iff_full
#print axioms gammaR_lSq_equiv_galK_oddDegree_of_nuRows_final

end
end GQ2.Dyadic.LSquare

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.GammaLSqCupAdaptedFrameGeneration
import GQ2.Dyadic.Instances.GammaLSylowPreimageMarkingAudit
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteCubicNeutral

/-!
# The odd-degree row carries **one** residual, and it is a `ν`-statement

`gammaR_lSq_equiv_galK_oddDegree` is proven over two binders,
`SqCore.SqNuClearHypothesis h` and `MarkedFrame.SqCupAdaptedFramePresentation K` (halved to
`SqCupAdaptedFrameRelator K` in `GammaLSqCupAdaptedFrameGeneration`).  This file replaces both
by the single hypothesis

  `MarkingAudit.SqFullNuForwardSupply B h` — *some* continuous isomorphism
  `f : D_sq(h) ≃ₜ* G_K(2)` carries the whole standard marking, `ν_ur ∘ f = ν_sq`.

Three facts make this the right endpoint, and all three are proved here or imported:

1. **It suffices** (§2).  The grand assembly consumes the two binders *only* to build the
   pro-2 block `MarkedCoreRealization (DSq h) (lNu h)`, and by
   `MarkingAudit.sqFullNuForwardSupply_iff_realization` that block **is** the full-row supply.
   So `gammaR_lSq_equiv_galK_oddDegree_of_fullNu` and its two corollaries carry no other input
   than the packet's structural pair `T`, `ramifiedData`.
2. **It is implied by the current pair** (§3, `sqFullNuForwardSupply_of_binders`): the frame
   chain plus the clearing binder produce it, so nothing is lost — the old endpoint factors
   through the new one (`gammaR_lSq_equiv_galK_oddDegree_of_binders`, a regression against the
   committed statement).
3. **It cannot be weakened** (§4): the converse `sqFullNuForwardSupply_of_realization` says the
   block *produces* it, so the residual is exactly the block, not a strengthening of it.

## Why the frame binder is genuinely retired, not merely repackaged

The frame lane exists to *produce an equivalence*.  But an equivalence is now free: the forward
presentation theorem `nonempty_orientedEquiv_oddDegree`
(`GammaLSylowPreimageFieldLabuteCubicNeutral`) is unconditional at every odd-degree `K`, and it
even carries the orientation clause.  What it does not carry is `ν`.  Meanwhile the *consumer*
of the frame lane discards orientation at the very first step
(`sqNuForwardSupply_of_marked`, the underscore in `markedCoreRealization_of_supply`), so what
`SqCupAdaptedFrameRelator K` actually buys the composite is: an equivalence, together with two
`ν`-rows.  The equivalence half is now redundant.  §5 makes this literal
(`sqNuForwardSupply_iff_exists_nuRows_equiv`, `orientedEquiv_of_oddDegree`): after this file the
frame lane contributes exactly its `ν`-rows and nothing else, so the honest residual is a
statement about `ν` alone.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Dyadic SqCore

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

section SingleResidual

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-! ### §1 The grand assembly, taken over the pro-2 block itself

`gammaR_lSq_equiv_galK_oddDegree` consumes its two binders in one step, to obtain `M`.  Cutting
the statement there is what exposes the true residual. -/

omit [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- **The grand assembly over the block.**  Everything after the pro-2 block is unconditional:
the word certificate is `wordCertificateRN_lSq_pow` at odd residue degree, and the corrected
arithmetic input is `kExactSupplyRN_of_markedCore`. -/
theorem gammaR_lSq_equiv_galK_of_realization (B : MarkedRecip Rec K)
    {FF : DyadicUnitFiltration K} (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (M : MarkedCoreRealization (K := K) (B := B) (DSq h) (Instances.LSquareCore.lNu h))
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FF) : Type) (GalK K)) :=
  lSq_candidate_equiv_galK_of_supplyRN
    (wordCertificateRN_lSq_qOf FF (odd_residueDegree_of_odd_finrank D
      (Nat.odd_iff.mpr (by omega))) h)
    (gammaLCorrectedArithmeticInput_of_markedCore T D hdeg M ramifiedData)
    (two_le_qOf K FF) (even_qOf K FF)

/-! ### §2 The single residual suffices -/

omit [T2Space (GalK K)] in
/-- **THE ODD-DEGREE ROW OVER ONE RESIDUAL.**  For every odd-degree ramified `K`, the improved
square presentation is `G_K` as soon as *some* continuous isomorphism `D_sq(h) ≃ₜ* G_K(2)`
carries the standard marking.  No frame, no relator, no cup datum, no orientation clause. -/
theorem gammaR_lSq_equiv_galK_oddDegree_of_fullNu (B : MarkedRecip Rec K)
    {FF : DyadicUnitFiltration K} (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hnu : MarkingAudit.SqFullNuForwardSupply B h)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FF) : Type) (GalK K)) := by
  obtain ⟨M⟩ := MarkingAudit.markedCoreRealization_of_fullSupply hnu
  exact gammaR_lSq_equiv_galK_of_realization B T D hdeg M ramifiedData

omit [T2Space (GalK K)] in
/-- **Free corollary 1 over the single residual**: the Krull open-subgroup field
identifications. -/
theorem gammaLOddIndexOpenSubgroupFieldIdentificationSupply_of_fullNu (B : MarkedRecip Rec K)
    {FF : DyadicUnitFiltration K} (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hnu : MarkingAudit.SqFullNuForwardSupply B h)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    GammaLOddIndexOpenSubgroupFieldIdentificationSupply h (qOf K FF) := by
  obtain ⟨M⟩ := MarkingAudit.markedCoreRealization_of_fullSupply hnu
  exact gammaLOddIndexOpenSubgroupFieldIdentificationSupply_of_fieldRealization
    (gammaLFieldRealization_oddDegree T D hdeg M ramifiedData)

/-- **Free corollary 2 over the single residual**: the full Tate bundle. -/
def tateDualityG_gamma_of_fullNu (B : MarkedRecip Rec K)
    {FF : DyadicUnitFiltration K} (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hnu : MarkingAudit.SqFullNuForwardSupply B h)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho))
    [DistribMulAction (gamma h (qOf K FF) : Type) (MuN 2)]
    [ContinuousSMul (gamma h (qOf K FF) : Type) (MuN 2)] :
    TateDualityG (gamma h (qOf K FF) : Type) 2 :=
  tateDualityG_of_fieldRealizationIdentification (even_qOf K FF)
    (gammaLFieldRealization_oddDegree T D hdeg
      (MarkingAudit.markedCoreRealization_of_fullSupply hnu).some ramifiedData)

/-! ### §3 The current pair implies the single residual -/

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **Nothing is lost.**  The two committed binders produce the full-row supply: the frame chain
gives the marked forward supply (orientation clause and all), forgetting the orientation gives
the two `ν`-rows, and the clearing binder upgrades two rows to all rows. -/
theorem sqFullNuForwardSupply_of_binders (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hclear : SqCore.SqNuClearHypothesis h)
    (hpres : MarkedFrame.SqCupAdaptedFramePresentation K) :
    MarkingAudit.SqFullNuForwardSupply B h := by
  have hh : (Module.finrank ℚ_[2] K - 1) / 2 = h := by omega
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  have hmarked := sqMarkedForwardSupply_oddDegree B FF hodd hpres
  rw [hh] at hmarked
  exact MarkingAudit.sqFullNuForwardSupply_of_clear hclear (sqNuForwardSupply_of_marked hmarked)

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The same over the halved frame residual `SqCupAdaptedFrameRelator`. -/
theorem sqFullNuForwardSupply_of_relator (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hclear : SqCore.SqNuClearHypothesis h) (hrel : SqCupAdaptedFrameRelator K) :
    MarkingAudit.SqFullNuForwardSupply B h :=
  sqFullNuForwardSupply_of_binders B FF hdeg hclear
    (sqCupAdaptedFramePresentation_of_relator hrel)

/-- **The regression.**  The committed endpoint `gammaR_lSq_equiv_galK_oddDegree` factors
through the single-residual endpoint: same statement, same hypotheses, new proof. -/
theorem gammaR_lSq_equiv_galK_oddDegree_of_binders (B : MarkedRecip Rec K)
    {FF : DyadicUnitFiltration K} (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (hclear : SqCore.SqNuClearHypothesis h)
    (hpres : MarkedFrame.SqCupAdaptedFramePresentation K)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_oddDegree_of_fullNu B T D hdeg
    (sqFullNuForwardSupply_of_binders B FF hdeg hclear hpres) ramifiedData

omit [T2Space (GalK K)] in
/-- The `h = 0` full circle over the single residual: at `[K : ℚ₂] = 1` the clearing binder is a
theorem, so only the frame lane's `ν`-rows survive. -/
theorem gammaR_lSq_equiv_galK_degreeOne_of_fullNu (B : MarkedRecip Rec K)
    {FF : DyadicUnitFiltration K} (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) (hdeg : Module.finrank ℚ_[2] K = 1)
    (hnu : MarkingAudit.SqFullNuForwardSupply B 0)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma 0 (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_oddDegree_of_fullNu B T D (by omega) hnu ramifiedData

/-! ### §4 The residual cannot be weakened

`MarkingAudit.sqFullNuForwardSupply_iff_realization` is an iff, so the hypothesis of §2 is
*equivalent* to the object the assembly consumes.  Any interface strictly weaker than the
full-row supply therefore cannot reach the grand assembly through this route. -/

omit [T2Space (GalK K)] in
/-- The single residual is exactly the pro-2 block. -/
theorem sqFullNuForwardSupply_iff_block (B : MarkedRecip Rec K) (h : ℕ) :
    MarkingAudit.SqFullNuForwardSupply B h ↔
      Nonempty (MarkedCoreRealization (K := K) (B := B) (DSq h)
        (Instances.LSquareCore.lNu h)) :=
  MarkingAudit.sqFullNuForwardSupply_iff_realization

end SingleResidual

/-! ### §5 What the frame lane still contributes: `ν`, and only `ν`

An equivalence is unconditional in odd degree, so the frame binder's whole contribution to the
composite is the pair of `ν`-rows. -/

section FrameContribution

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **An equivalence is free at odd degree, over the caller's bundle.**  This is
`nonempty_orientedEquiv_oddDegree` with the orientation clause spelled out and the handle count
normalized to `h`.  The marked bundle `B` is a binder the callers already carry; it replaces
what used to be an application of the axiom `markedRecipAt` (B5-K) deep in the frame supply. -/
theorem orientedEquiv_of_oddDegree (B : MarkedRecip Rec K) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) :
    ∃ f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)),
      ∀ x, chiCycKTwo (K := K) (f x) = chiSq h x := by
  have hh : (Module.finrank ℚ_[2] K - 1) / 2 = h := by omega
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  have hne := nonempty_orientedEquiv_oddDegree (K := K) B hodd
  rw [hh] at hne
  obtain ⟨e⟩ := hne
  exact ⟨e.1, e.2⟩

omit [T2Space (GalK K)] [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **The frame lane's whole contribution, isolated.**  `SqNuForwardSupply` is the two selected
`ν`-rows on *some* isomorphism; the isomorphism itself is not a residual at odd degree, since
`orientedEquiv_of_oddDegree` supplies one (oriented, even) with no hypothesis. -/
theorem sqNuForwardSupply_iff_exists_nuRows_equiv (B : MarkedRecip Rec K) (h : ℕ) :
    SqNuForwardSupply B h ↔
      ∃ f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)),
        nuUrKTwo B (f (dsqSigma h)) = Multiplicative.ofAdd (1 : ℤ_[2]) ∧
          nuUrKTwo B (f (dsqX0 h)) = Multiplicative.ofAdd (0 : ℤ_[2]) :=
  Iff.rfl

omit [T2Space (GalK K)] in
/-- **The composite over the two `ν`-statements alone.**  Neither the frame, nor the relator,
nor the orientation clause appears: `SqNuForwardSupply` (two rows on some isomorphism) and the
clearing binder (two rows to all rows) are the entire residual surface of the odd-degree row. -/
theorem gammaR_lSq_equiv_galK_oddDegree_of_nuRows (B : MarkedRecip Rec K)
    {FF : DyadicUnitFiltration K} (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (hclear : SqCore.SqNuClearHypothesis h)
    (hrows : SqNuForwardSupply B h)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_oddDegree_of_fullNu B T D hdeg
    (MarkingAudit.sqFullNuForwardSupply_of_clear hclear hrows) ramifiedData

end FrameContribution

end

#print axioms GQ2.Dyadic.LSquare.gammaR_lSq_equiv_galK_of_realization
#print axioms GQ2.Dyadic.LSquare.gammaR_lSq_equiv_galK_oddDegree_of_fullNu
#print axioms GQ2.Dyadic.LSquare.gammaLOddIndexOpenSubgroupFieldIdentificationSupply_of_fullNu
#print axioms GQ2.Dyadic.LSquare.tateDualityG_gamma_of_fullNu
#print axioms GQ2.Dyadic.LSquare.sqFullNuForwardSupply_of_binders
#print axioms GQ2.Dyadic.LSquare.sqFullNuForwardSupply_of_relator
#print axioms GQ2.Dyadic.LSquare.gammaR_lSq_equiv_galK_oddDegree_of_binders
#print axioms GQ2.Dyadic.LSquare.gammaR_lSq_equiv_galK_degreeOne_of_fullNu
#print axioms GQ2.Dyadic.LSquare.sqFullNuForwardSupply_iff_block
#print axioms GQ2.Dyadic.LSquare.orientedEquiv_of_oddDegree
#print axioms GQ2.Dyadic.LSquare.sqNuForwardSupply_iff_exists_nuRows_equiv
#print axioms GQ2.Dyadic.LSquare.gammaR_lSq_equiv_galK_oddDegree_of_nuRows

end GQ2.Dyadic.LSquare

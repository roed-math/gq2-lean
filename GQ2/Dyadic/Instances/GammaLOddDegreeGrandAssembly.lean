/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.GammaLOddDegreeRealization
import GQ2.Dyadic.Instances.KExactLiftingGalK
import GQ2.Dyadic.Instances.GammaLSourceArfGeneral
import GQ2.Dyadic.Instances.CandidateEquivGalKRN
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldKernelDescent

/-!
# `Γ_{R_K} ≅ G_K` for every odd-degree ramified `K` — the grand assembly

Every stage of the corrected `L`-row reconstruction is now a theorem at general `K`, so this
file composes them once, end to end.  Reading the chain in the order the pieces are consumed:

1. **The pro-2 block.**  `markedCoreRealization_oddDegree`
   (`GammaLOddDegreeRealization`) supplies `MarkedCoreRealization (DSq h) (lNu h)` over the
   χ-free clearing binder and the stage lane's frame residual, nothing else.
2. **The arithmetic source.**  `kExactSupplyRN_of_markedCore` (`KExactLiftingGalK`) turns the
   block's four exported theorems `pro2`/`hpro2`/`ker_pro2`/`nu_compat` into `KExactSupplyRN`
   at `G_K` — the corrected exact-lifting semantics is *not* an input, it is a theorem at every
   finite-dimensional `K` — and `GammaLCorrectedArithmeticInput.ofKExactSupplyRN` packages it
   with the numerical parameter record and the row-independent `ramifiedData` binder.
3. **The candidate side.**  `wordCertificateRN_lSq_pow` (`GammaLSourceArfGeneral`) is
   unconditional at `q = 2 ^ f` with `f` odd, and odd degree gives odd `f` for free: the
   parameter package carries `f ∣ n` (`FieldParameters.f_dvd_n`) and a divisor of an odd number
   is odd (`odd_residueDegree_of_odd_finrank`).  Since `q_K = 2 ^ f` by definition, the
   certificate lands at the field's own residue cardinality with no arithmetic binder at all.
4. **Reconstruction.**  `gammaLFieldRealization_of_wordCertificateRN_reconstruction` compares
   the two sources; `lSq_candidate_equiv_galK_of_supplyRN` (`CandidateEquivGalKRN`) reads off
   the equivalence `Γ_{R_K} ≅ G_K` through the row-generic wrapper.

The corollaries recorded here are free once the realization exists: the Krull open-subgroup
field identifications (`gammaLOddIndexOpenSubgroupFieldIdentificationSupply`) and the full Tate
bundle `TateDualityG (gamma h q) 2`.

## The residual surface

Two hypotheses remain on the composite, and they are exactly the two the `L` row has been
carrying:

| input | owner |
|---|---|
| `SqNuClearHypothesis h` | the χ-free seed search; a theorem at `h = 0` |
| `SqCupAdaptedFramePresentation K` | the stage lane's frame-tracking residual |

plus the two structural binders every row of the packet carries — an `OrientedTameQuotientK`
and the `ramifiedData` certificate supply.  In particular no `ν`-row, no cup datum, no level
equation, no handle stratum, and no analytic leaf survives on the odd-degree row.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Dyadic SqCore

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

section Assembly

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-! ### §1 The pro-2 block at an explicit handle count -/

/-- The odd-degree L-row pro-2 block, stated at an explicit handle count rather than at
`([K : ℚ₂] − 1) / 2`.  Every consumer downstream indexes by `h`, so this is the shape the
assembly wants. -/
theorem markedCoreRealization_of_finrank (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (hclear : SqNuClearHypothesis h)
    (hpres : MarkedFrame.SqCupAdaptedFramePresentation K) :
    Nonempty (MarkedCoreRealization (K := K) (B := B) (DSq h)
      (Instances.LSquareCore.lNu h)) := by
  have hh : (Module.finrank ℚ_[2] K - 1) / 2 = h := by omega
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  have hblock := markedCoreRealization_oddDegree B FF hodd (by rw [hh]; exact hclear) hpres
  rwa [hh] at hblock

/-! ### §2 Odd degree forces odd residue degree -/

omit [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **Odd degree gives odd residue degree.**  The parameter package carries `f ∣ n` and
`n = [K : ℚ₂]`, and a divisor of an odd natural number is odd.  This is the bridge that lets
the unconditional two-power word certificate `wordCertificateRN_lSq_pow` be used at the
field's own residue cardinality `q_K = 2 ^ f`. -/
theorem odd_residueDegree_of_odd_finrank {FF : DyadicUnitFiltration K}
    (D : FiniteDyadicParameters K FF) (hodd : Odd (Module.finrank ℚ_[2] K)) : Odd FF.f := by
  obtain ⟨c, hc⟩ := D.params.f_dvd_n
  rw [D.degree_eq, D.residueDegree_eq] at hc
  rw [hc] at hodd
  exact (Nat.odd_mul.mp hodd).1

/-! ### §3 The corrected arithmetic source -/

/-- **The corrected arithmetic input from the pro-2 block.**  `exactLifting` is a theorem at
`G_K` (`exactLiftingSemanticsRN_galK`), so the only data consumed here are the block, the
degree equation, the numerical parameter package, and the row-independent ramified certificate
supply. -/
def gammaLCorrectedArithmeticInput_of_markedCore {B : MarkedRecip Rec K}
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
    GammaLCorrectedArithmeticInput h (qOf K FF) K :=
  GammaLCorrectedArithmeticInput.ofKExactSupplyRN
    (kExactSupplyRN_of_markedCore (T := T) hdeg M.pro2 M.pro2_surjective M.ker_pro2 M.nu_compat)
    D.params (by rw [D.degree_eq]; exact hdeg) D.qK_eq_qOf ramifiedData

/-! ### §4 The candidate certificate at the field's own residue cardinality -/

/-- **The L word certificate at `q_K`, with no arithmetic binder.**  `q_K = 2 ^ f` is a
definitional unfolding, so `wordCertificateRN_lSq_pow` applies verbatim once `f` is odd. -/
def wordCertificateRN_lSq_qOf (FF : DyadicUnitFiltration K) (hfodd : Odd FF.f) (h : ℕ) :
    WordCertificateRN (2 * h + 1) (qOf K FF) (Words.LSq.lSqW h) (DSq h)
      (SqCore.isProP_DSq h) (Instances.LSquareCore.lNu h) (standardNumerics (2 * h + 1)) :=
  wordCertificateRN_lSq_pow hfodd

/-! ### §5 The field realization and the grand assembly -/

/-- **The odd-degree field realization.**  Corrected reconstruction against the arithmetic
source built from the pro-2 block: `gamma h q_K` is an open subgroup of `G_{ℚ₂}` of index
`2h + 1 = [K : ℚ₂]`. -/
def gammaLFieldRealization_oddDegree {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}
    (T : OrientedTameQuotientK B FF) (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (M : MarkedCoreRealization (K := K) (B := B) (DSq h) (Instances.LSquareCore.lNu h))
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    GammaLFieldRealization h (qOf K FF) :=
  gammaLFieldRealization_of_wordCertificateRN_reconstruction
    (wordCertificateRN_lSq_qOf FF (odd_residueDegree_of_odd_finrank D
      (Nat.odd_iff.mpr (by omega))) h)
    (gammaLCorrectedArithmeticInput_of_markedCore T D hdeg M ramifiedData)
    (two_le_qOf K FF) (even_qOf K FF)

/-- **THE GRAND ASSEMBLY.**  For every odd-degree ramified `K/ℚ₂`, the improved square
presentation is `G_K`:
`Γ_{R_K} = ⟨σ, τ, x₀, x₁, u_j, v_j ∣ τ^σ = τ^{q_K}, L_sq, …⟩_prof ≅ G_K`,
over the χ-free clearing binder and the stage lane's frame residual alone (plus the packet's
two structural binders `T` and `ramifiedData`, which every row carries). -/
theorem gammaR_lSq_equiv_galK_oddDegree (B : MarkedRecip Rec K) {FF : DyadicUnitFiltration K}
    (T : OrientedTameQuotientK B FF) (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (hclear : SqNuClearHypothesis h)
    (hpres : MarkedFrame.SqCupAdaptedFramePresentation K)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FF) : Type) (GalK K)) := by
  obtain ⟨M⟩ := markedCoreRealization_of_finrank B FF hdeg hclear hpres
  exact lSq_candidate_equiv_galK_of_supplyRN
    (wordCertificateRN_lSq_qOf FF (odd_residueDegree_of_odd_finrank D
      (Nat.odd_iff.mpr (by omega))) h)
    (gammaLCorrectedArithmeticInput_of_markedCore T D hdeg M ramifiedData)
    (two_le_qOf K FF) (even_qOf K FF)

/-! ### §6 The free corollaries -/

/-- **Free corollary 1**: the Krull open-subgroup field identifications. -/
theorem gammaLOddIndexOpenSubgroupFieldIdentificationSupply_oddDegree
    (B : MarkedRecip Rec K) {FF : DyadicUnitFiltration K} (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (hclear : SqNuClearHypothesis h)
    (hpres : MarkedFrame.SqCupAdaptedFramePresentation K)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    GammaLOddIndexOpenSubgroupFieldIdentificationSupply h (qOf K FF) := by
  obtain ⟨M⟩ := markedCoreRealization_of_finrank B FF hdeg hclear hpres
  exact gammaLOddIndexOpenSubgroupFieldIdentificationSupply_of_fieldRealization
    (gammaLFieldRealization_oddDegree T D hdeg M ramifiedData)

/-- **Free corollary 2**: the full Tate bundle on the candidate presentation. -/
def tateDualityG_gamma_oddDegree (B : MarkedRecip Rec K) {FF : DyadicUnitFiltration K}
    (T : OrientedTameQuotientK B FF) (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (hclear : SqNuClearHypothesis h)
    (hpres : MarkedFrame.SqCupAdaptedFramePresentation K)
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
      (markedCoreRealization_of_finrank B FF hdeg hclear hpres).some ramifiedData)

/-! ### §7 The `h = 0` instance -/

/-- **The `h = 0` full circle.**  At `[K : ℚ₂] = 1` the χ-free clearing binder is the theorem
`sqNuClearHypothesis_zero`, so the entire new machine reproduces `Γ_{R,q_K} ≅ G_K` over the
frame residual alone.

⚠ **Two declarations carry this name; this is the conditional one.**  It binds
`MarkedFrame.SqCupAdaptedFramePresentation K`, the stage lane's frame-tracking residual, which is
what makes it a full-circle *regression* for this assembly rather than the endpoint to cite.
(Its `_oddDegree` sibling `gammaR_lSq_equiv_galK_oddDegree` binds `SqNuClearHypothesis h` on top
of that; at `h = 0` that one is discharged here by `sqNuClearHypothesis_zero`.)

The **unconditional** degree-one endpoint is
`GQ2.Dyadic.LSquare.NuAdapted.gammaR_lSq_equiv_galK_degreeOne`
(`GQ2/Dyadic/SqCore/PivotSeedD0.lean` §6): no frame residual, no clearing binder, and a verified
root-level print of std-3 + `{B1, B3c, B6, B7, B8, B9, B11a}` — a strict subset of the frozen
`ℚ₂` capstone's nine.  **That** is the one the paper should quote at degree one. -/
theorem gammaR_lSq_equiv_galK_degreeOne (B : MarkedRecip Rec K)
    {FF : DyadicUnitFiltration K} (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) (hdeg : Module.finrank ℚ_[2] K = 1)
    (hpres : MarkedFrame.SqCupAdaptedFramePresentation K)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma 0 (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_oddDegree B T D (by omega) sqNuClearHypothesis_zero hpres ramifiedData

end Assembly

end

#print axioms GQ2.Dyadic.LSquare.markedCoreRealization_of_finrank
#print axioms GQ2.Dyadic.LSquare.odd_residueDegree_of_odd_finrank
#print axioms GQ2.Dyadic.LSquare.gammaLCorrectedArithmeticInput_of_markedCore
#print axioms GQ2.Dyadic.LSquare.wordCertificateRN_lSq_qOf
#print axioms GQ2.Dyadic.LSquare.gammaLFieldRealization_oddDegree
#print axioms GQ2.Dyadic.LSquare.gammaR_lSq_equiv_galK_oddDegree
#print axioms GQ2.Dyadic.LSquare.gammaLOddIndexOpenSubgroupFieldIdentificationSupply_oddDegree
#print axioms GQ2.Dyadic.LSquare.tateDualityG_gamma_oddDegree
#print axioms GQ2.Dyadic.LSquare.gammaR_lSq_equiv_galK_degreeOne

end GQ2.Dyadic.LSquare

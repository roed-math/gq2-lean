/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.KExactLiftingVar

/-!
# `ExactLiftingSemantics` at `G_K`  (package P5, assembly)

The two generic clauses of `KExactLifting.lean` and `KExactLiftingVar.lean`, instantiated at
`Γ = G_K`, joined to the already-landed corrected R-stage identity
(`KAnalytic.correctedRStageSemantics_galK`), and packaged as the constructors
`KExactSupplyRN`/`KExactSupply` were missing.

## What this closes

`KSupply.lean` §6 item 2 lists `exactLifting` as one of the eleven carried leaves, with three
sub-obligations:

| conjunct | `ℚ₂` ancestor | supplier here |
|---|---|---|
| `liftsOver_card` | `MStageCount.liftsOver_card_local` | `Count.liftsOver_card_*_tateDualityG` |
| `lem86` | `SectionEight.lemma_8_6_local` | `Count.lem86_of_tateDualityG` |
| `stageR136` (RN) | `RStageLocal.stageR136_local` | `correctedRStageSemantics_galK` (landed) |

so `ExactLiftingSemanticsRN` at `G_K` is now a theorem at **every** finite-dimensional `K`, and
`KExactSupplyRN` reduces to the marked-core pro-`2` block alone — the per-branch data of AS2–AS5.

## The frozen `ExactLiftingSemantics` is degree-one only, and that is not an omission

The legacy third conjunct pins the coefficient `RecursionFrame.zR = #R² · #D_R`, whereas the
R-cocycle count at `G_K` is `zRN RF (standardNumerics n) = #R^{n+1} · #D_R`
(`correctedRStage_hZcount_galK`).  The two agree exactly at `n = 1` (`zRN_standard_one`, `rfl`).
So `exactLiftingSemantics_galK` below is stated at `[K : ℚ₂] = 1`, and the general-`K` row is the
`RN` one — which is what `SourceDataRN`/`KExactSupplyRN`, i.e. every live branch row, consumes.
`exactLiftingSemantics_galK_of_stageR136` keeps the frozen API available for a caller who carries
its own stage clause.

Axioms (measured, per headline):

* `liftsOver_card_galK` — std-3 + **B6** (`tateDualityAt`) + **B7**
  (`absGalQ2_localEulerCharacteristic`, through LG2a's derived `localEulerCharacteristic_open`);
* `lem86_galK_of_noDescent` — std-3 + **B6** + **B1**
  (`absGalQ2_isTopologicallyFinitelyGenerated`, through `tfg_galK`; the `ℚ₂` ancestor
  `half_torsor_local` takes the same input as its `hfg` hypothesis).  **No B7**: the half-torsor
  clause is degree-free;
* `exactLiftingSemanticsRN_galK`, `exactLiftingSemantics_galK`, `kExactSupplyRN_of_markedCore`
  — the union, std-3 + {B6, B7, B1}.

`sourceRN_of_markedCore` additionally inherits B9/B11a from the already-landed
`affineDeterminant_galK` it routes through.  No new axiom, no `sorry`; the census is unchanged.

⚠ Spelling: the bundle must be `LiftingDualityG.tateDualityGalK`, at `GalK K`, **not**
`FieldData.tateDualityGalK`, which is typed at `↥K.fixingSubgroup`.  They are the same type
through two instance paths (`MarkedRecipBundle`'s R6 trap) and only the first one lets
`CompactSpace (GalK K)` synthesize afterwards.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open LiftingDualityG

section GalKClauses

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [FiniteDimensional ℚ_[2] K] [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The `μ₂`-action of `G_K` is continuous.  Spelled out rather than inferred: the subtype path
is the one `stokesDualityCertificate_galK` pins, and letting typeclass search find it through the
bundled profinite topology is the instance-path blow-up recorded in
`docs/dyadic/followup/stokes-galk-status.md`. -/
theorem contSMulMuTwoGalK : ContinuousSMul (GalK K) (MuN 2) :=
  ⟨Continuous.comp (continuous_smul (M := AbsGalQ2) (X := MuN 2))
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)⟩

/-- **The `liftsOver_card` conjunct at `G_K`** — `#LiftsOverK(ρ) = #M_B^{[K:ℚ₂]+1}`.

B6 (`LiftingDualityG.tateDualityGalK`) plus the degree-`n` local Euler characteristic.
⚠ The exponent is `n + 1`; the frozen `ℚ₂` value `#M_B²` is the `n = 1` case. -/
theorem liftsOver_card_galK {n q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (hdeg : Module.finrank ℚ_[2] K = n)
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom (galKProfinite K) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (ρ : BoundaryLiftsK b F RF.TC) :
    Nat.card (LiftsOverK RF b F ρ) = (standardNumerics n).mMult (Nat.card ↥RF.MB) := by
  letI dmMu : DistribMulAction (GalK K) (MuN 2) := inferInstance
  haveI csMu : ContinuousSMul (GalK K) (MuN 2) := contSMulMuTwoGalK K
  exact Count.liftsOver_card_standard_of_tateDualityG (LiftingDualityG.tateDualityGalK K)
    (localEulerChar_galK_of_finrank K hdeg) RF b F ρ

/-- **The `lem86` conjunct at `G_K`** — the half-torsor count.

B6 alone: the variation witness comes from Tate `(1,1)` separation, which carries no degree, and
the count is `Count.lem86N` against `tfg_galK` and `card_H2_zmodTwo_galK`.  This is the `K`-clone
of `SectionEight.lemma_8_6_local`, and the existential `KSupply.lem86_galK` left open. -/
theorem lem86_galK_of_noDescent {Bg : Type} [Group Bg] [TopologicalSpace Bg]
    [DiscreteTopology Bg] [Finite Bg] (D : RadicalCoverData Bg) (hedge : D.NoDescent)
    (ρ : ContinuousMonoidHom (GalK K) (Bg ⧸ D.M)) (hρ : Function.Surjective ρ) :
    2 * Nat.card {f : MLifts D ρ // f.Central} = Nat.card (MLifts D ρ) := by
  letI dmMu : DistribMulAction (GalK K) (MuN 2) := inferInstance
  haveI csMu : ContinuousSMul (GalK K) (MuN 2) := contSMulMuTwoGalK K
  exact Count.lem86_of_tateDualityG (LiftingDualityG.tateDualityGalK K) (tfg_galK K)
    (card_H2_zmodTwo_galK K) D hedge ρ hρ

end GalKClauses

/-! ## The assembled packets -/

section GalKPackets

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **The corrected exact-lifting semantics at `G_K`, for every finite-dimensional `K`.**

All three conjuncts are theorems: the lift count and the half-torsor count are this package's,
the corrected equation (136) is `correctedRStageSemantics_galK`.  Nothing is carried. -/
theorem exactLiftingSemanticsRN_galK {n q : ℕ} {P : ProfiniteGrp}
    {nuP : ContinuousMonoidHom P Ztwo} (hdeg : Module.finrank ℚ_[2] K = n) :
    ExactLiftingSemanticsRN (galKProfinite K) n q P nuP (standardNumerics n) :=
  ⟨fun RF b F ρ => liftsOver_card_galK K hdeg RF b F ρ,
   fun D hedge ρ hρ => lem86_galK_of_noDescent K D hedge ρ hρ,
   fun hE2 hRK hR2 b F => correctedRStageSemantics_galK hdeg hE2 hRK hR2 b F⟩

/-- The frozen exact-lifting semantics at `G_K`, with the legacy `zR`-coefficient stage clause
supplied by the caller.  Only the third conjunct is a hypothesis; the first two are theorems. -/
theorem exactLiftingSemantics_galK_of_stageR136 {n q : ℕ} {P : ProfiniteGrp}
    {nuP : ContinuousMonoidHom P Ztwo} (hdeg : Module.finrank ℚ_[2] K = n)
    (stage : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
      [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
      {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
      (hE2 : ∀ e : E, e ^ 2 = 1)
      (_hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
      (_hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
      (b : ContinuousMonoidHom (galKProfinite K) ↥(boundarySubgroupQ q nuP))
      (F : BoundaryFrameK q P H E),
      (Nat.card (blockFrameImpl T Blk hE2).DR : ℤ) * exactImageCountK b F T
        = (blockFrameImpl T Blk hE2).zR * ∑ᶠ l : (blockFrameImpl T Blk hE2).DR,
            (2 * (mBK (blockFrameImpl T Blk hE2) b F l : ℤ)
              - exactImageCountK b F (blockFrameImpl T Blk hE2).TB)) :
    ExactLiftingSemantics (galKProfinite K) n q P nuP (standardNumerics n) :=
  ⟨fun RF b F ρ => liftsOver_card_galK K hdeg RF b F ρ,
   fun D hedge ρ hρ => lem86_galK_of_noDescent K D hedge ρ hρ,
   fun hE2 hRK hR2 b F => stage hE2 hRK hR2 b F⟩

/-- **The frozen exact-lifting semantics at `G_K` for `[K : ℚ₂] = 1`.**

At degree one the corrected and frozen APIs are definitionally equal
(`exactLiftingSemanticsRN_standard_one_iff`), so the `RN` packet transfers.  For `[K : ℚ₂] > 1`
the frozen third conjunct pins the coefficient `#R²` while the R-cocycle count at `G_K` is
`#R^{n+1}` (`correctedRStage_hZcount_galK`), so the frozen identity is not the one the arithmetic
supports and there is no general-`n` companion. -/
theorem exactLiftingSemantics_galK {q : ℕ} {P : ProfiniteGrp}
    {nuP : ContinuousMonoidHom P Ztwo} (hdeg : Module.finrank ℚ_[2] K = 1) :
    ExactLiftingSemantics (galKProfinite K) 1 q P nuP (standardNumerics 1) :=
  (exactLiftingSemanticsRN_standard_one_iff _ _ _ _).mp (exactLiftingSemanticsRN_galK hdeg)

variable {R : LocalReciprocity} {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}

/-- **`KExactSupplyRN` from the marked-core block alone.**

The record's one analytic field is now a theorem, so the constructor's remaining arguments are
exactly the four pro-`2` data of AS2–AS5's marked-core certificate.  This is the shape the five
branch rows want. -/
noncomputable def kExactSupplyRN_of_markedCore {T : OrientedTameQuotientK B FF} {n : ℕ}
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (hdeg : Module.finrank ℚ_[2] K = n)
    (pro2 : ContinuousMonoidHom (GalK K) P) (hpro2 : Function.Surjective pro2)
    (ker_pro2 : pro2.toMonoidHom.ker = proPKernel 2 (GalK K))
    (nu_compat : ∀ g : GalK K, ztwoIota (nuP (pro2 g)) = B.nu_ur (toAbK K g)) :
    KExactSupplyRN T n P hP nuP where
  hdeg := hdeg
  pro2 := pro2
  hpro2 := hpro2
  ker_pro2 := ker_pro2
  nu_compat := nu_compat
  exactLifting := exactLiftingSemanticsRN_galK hdeg

/-- **`KExactSupply` from the marked-core block alone, at `[K : ℚ₂] = 1`.**  The frozen record's
degree restriction is the one recorded above. -/
noncomputable def kExactSupply_of_markedCore_degreeOne {T : OrientedTameQuotientK B FF}
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (hdeg : Module.finrank ℚ_[2] K = 1)
    (pro2 : ContinuousMonoidHom (GalK K) P) (hpro2 : Function.Surjective pro2)
    (ker_pro2 : pro2.toMonoidHom.ker = proPKernel 2 (GalK K))
    (nu_compat : ∀ g : GalK K, ztwoIota (nuP (pro2 g)) = B.nu_ur (toAbK K g)) :
    KExactSupply T 1 P hP nuP where
  hdeg := hdeg
  pro2 := pro2
  hpro2 := hpro2
  ker_pro2 := ker_pro2
  nu_compat := nu_compat
  exactLifting := exactLiftingSemantics_galK hdeg

/-- **The corrected arithmetic source at `G_K` from the marked-core block.**  The end of the
chain: with `exactLifting` discharged, `SourceDataRN` at `G_K` costs the four pro-`2` data, the
degree pin, the two `params` pins, and the packet's `ramifiedData` input. -/
noncomputable def sourceRN_of_markedCore (T : OrientedTameQuotientK B FF) {n : ℕ}
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    (hdeg : Module.finrank ℚ_[2] K = n)
    (pro2 : ContinuousMonoidHom (GalK K) P) (hpro2 : Function.Surjective pro2)
    (ker_pro2 : pro2.toMonoidHom.ker = proPKernel 2 (GalK K))
    (nu_compat : ∀ g : GalK K, ztwoIota (nuP (pro2 g)) = B.nu_ur (toAbK K g))
    (params : FieldParameters) (params_n : params.n = n) (params_qK : params.qK = qOf K FF)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) W cc rho)) :
    SourceDataRN n (qOf K FF) P hP nuP (standardNumerics n) :=
  (kExactSupplyRN_of_markedCore (T := T) hdeg pro2 hpro2 ker_pro2 nu_compat).toSourceRN
    params params_n params_qK ramifiedData

end GalKPackets

end GQ2.Dyadic

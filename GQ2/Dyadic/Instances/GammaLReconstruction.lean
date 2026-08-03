/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.CertificateSupplyRN
import GQ2.Dyadic.Instances.GammaLAnalyticLeaves
import GQ2.Dyadic.Instances.GammaLEulerH2Surjectivity
import GQ2.Dyadic.Instances.GammaLRealizationRoute
import GQ2.Dyadic.Instances.KAnalytic

/-!
# Corrected reconstruction for the improved L presentation

This file composes the completed word-level action-image argument with the corrected (`RN`)
finite-quotient reconstruction theorem.  It deliberately keeps the two genuinely separate
remaining inputs visible.

* `LSquareAnalyticLeavesRN` contains only the affine determinant not produced by the direct
  action-image argument.  The complete Stokes and scalar Hilbert certificates are theorems.
* `GammaLCorrectedArithmeticInput` is an arithmetic `SourceDataRN` over the same canonical
  square core, together with its identification with `G_K`, its tame/wild reconstruction
  hypotheses, and the expected degree.

The action-image theorem now proves `UniformPushedHsimp h q` from `Even q`; consequently the
corrected exact-lifting field is no longer an input.  The canonical `DSq` core, its orientation,
the maximal-pro-2 map, and tame/wild structural fields are also all constructed here.

The arithmetic record is necessary because the existing `DyadicLocalInput` supplies a frozen
`SourceDataN`.  Away from degree one there is no conversion from that frozen source to the
degree-corrected `SourceDataRN`: their R-stage coefficients differ.  Asking directly for the
corrected arithmetic source records this API gap without postulating an equivalence from the
candidate presentation to `G_K`; that equivalence is the output of reconstruction below.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.TameSpec

local notation "LCore" => SqCore.DSq
local notation "LNu" => Instances.LSquareCore.lNu
local notation "LSN" => standardNumerics

/-! ## Canonical structural data -/

/-- The nonzero hypothesis used by tame specialization, derived from the actual reconstruction
hypothesis `2 ≤ q`. -/
theorem q_ne_zero_of_two_le {q : ℕ} (hq2 : 2 ≤ q) : q ≠ 0 := by omega

/-- The canonical tame specialization of the improved L word. -/
def lCanonicalTameSpecialization (h q : ℕ) (hq2 : 2 ≤ q) (hqe : Even q) :
    TameSpecializes (2 * h + 1) q (Words.LSq.lSqW h) :=
  Count.tameSpecializes_lSq (q_ne_zero_of_two_le hq2) hqe h

/-- The canonical map from the improved L presentation to its square pro-2 core. -/
noncomputable def lCanonicalPro2 (h q : ℕ) (hq2 : 2 ≤ q) (hqe : Even q) :
    ContinuousMonoidHom (gamma h q : Type) (LCore h) :=
  Count.CorePresentation.coreHom (Instances.LSquareCore.lCorePresentation h)
    (q_ne_zero_of_two_le hq2) hqe

/-- The canonical tame and pro-2 maps have the same `Ztwo` orientation. -/
theorem lCanonicalCompat (h q : ℕ) (hq2 : 2 ≤ q) (hqe : Even q) :
    ∀ g : (gamma h q : Type),
      nuTq q (tameOfSpec (2 * h + 1) q (Words.LSq.lSqW h)
        (lCanonicalTameSpecialization h q hq2 hqe) g) =
        LNu h (lCanonicalPro2 h q hq2 hqe g) :=
  Count.CorePresentation.nu_compat_coreHom
    (Instances.LSquareCore.lCorePresentation h) (q_ne_zero_of_two_le hq2) hqe
    (lCanonicalTameSpecialization h q hq2 hqe) (LNu h)
    (Instances.LSquareCore.lNu_sigma h) (Instances.LSquareCore.lNu_wild h)

/-- The canonical L orientation is onto: its image contains the topological generator
`ztwoOne`. -/
theorem lNu_surjective (h : ℕ) : Function.Surjective (LNu h) :=
  Instances.NuWitness.surjective_of_ztwoOne_mem_range (LNu h)
    ⟨(Instances.LSquareCore.lCorePresentation h).mark .sigma, by
      exact Instances.LSquareCore.lNu_sigma h⟩

/-! ## The exact remaining candidate-side analytic leaves -/

/-- The exact candidate-side analytic residue after the direct action-image consequences are
used: the affine determinant alone.  `GammaLAnalyticLeaves` constructs the complete Stokes and
scalar certificates from the same action-image theorem used for exact lifting. -/
structure LSquareAnalyticLeavesRN (h q : ℕ) (hq2 : 2 ≤ q) (hqe : Even q) where
  determinant : DeterminantResidue (LNu h)
    (tameOfSpec (2 * h + 1) q (Words.LSq.lSqW h)
      (lCanonicalTameSpecialization h q hq2 hqe))
    (lCanonicalPro2 h q hq2 hqe) (lCanonicalCompat h q hq2 hqe)

/-- The completed action-image theorem, composed with the canonical L structural data, builds a
corrected word certificate.  In particular, corrected exact lifting is no longer a hypothesis. -/
noncomputable def wordCertificateRN_lSq_of_actionImage
    {h q : ℕ} (hq2 : 2 ≤ q) (hqe : Even q)
    (A : LSquareAnalyticLeavesRN h q hq2 hqe) :
    WordCertificateRN (2 * h + 1) q (Words.LSq.lSqW h) (LCore h)
      (SqCore.isProP_DSq h) (LNu h) (LSN (2 * h + 1)) where
  tameSpecialization := lCanonicalTameSpecialization h q hq2 hqe
  coreRel := fun G _ _ _ _ _ t => t.eval (pro2 (Words.LSq.lSqW h))
  proTwoWord := by
    intro G _ _ _ _ _ t
    rfl
  pro2 := lCanonicalPro2 h q hq2 hqe
  ker_pro2 := Count.CorePresentation.ker_coreHom
    (Instances.LSquareCore.lCorePresentation h) (q_ne_zero_of_two_le hq2) hqe
  hpro2 := Count.CorePresentation.coreHom_surjective
    (Instances.LSquareCore.lCorePresentation h) (q_ne_zero_of_two_le hq2) hqe
  compat := lCanonicalCompat h q hq2 hqe
  tfg := Count.gammaR_topologicallyFinitelyGenerated _ _ _
  smulZmod2 := scalarActionZmodTwo _
  contSMulZmod2 := scalarActionZmodTwo_continuousSMul _
  htriv := scalarActionZmodTwo_triv _
  exactLifting := exactLiftingRN_of_uniformPushed (uniformPushedHsimp_of_actionImage hqe)
    hqe (LNu h)
  stokes := stokesDualityCertificate_of_actionImage hqe
  scalar := scalarHilbertCertificate_of_actionImage hqe
  determinant := A.determinant
  htame := Count.htame_of_tameSpecializes (lCanonicalTameSpecialization h q hq2 hqe)
  hwild := Count.hwild_of_tameSpecializes (lCanonicalTameSpecialization h q hq2 hqe)

/-- Regression pin: the certificate's corrected lifting field is definitionally the action-image
constructor followed by `exactLiftingRN_of_uniformPushed`. -/
theorem wordCertificateRN_lSq_of_actionImage_exactLifting
    {h q : ℕ} (hq2 : 2 ≤ q) (hqe : Even q)
    (A : LSquareAnalyticLeavesRN h q hq2 hqe) :
    (wordCertificateRN_lSq_of_actionImage hq2 hqe A).exactLifting =
      exactLiftingRN_of_uniformPushed (uniformPushedHsimp_of_actionImage hqe)
        hqe (LNu h) := rfl

/-! ## Corrected arithmetic source and reconstruction -/

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The exact arithmetic-side data still required by corrected reconstruction.

Crucially, `equivGalK` identifies the arithmetic source's own carrier with `G_K`; it does not
identify the candidate presentation with `G_K`. -/
structure GammaLCorrectedArithmeticInput (h q : ℕ)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K] where
  source : SourceDataRN (2 * h + 1) q (LCore h) (SqCore.isProP_DSq h) (LNu h)
    (LSN (2 * h + 1))
  equivGalK : ContinuousMulEquiv source.Γ (GalK K)
  tame_surjective : Function.Surjective source.tame
  wild_isProP : IsProP 2 source.tame.toMonoidHom.ker
  degree_eq : Module.finrank ℚ_[2] K = 2 * h + 1

namespace GammaLCorrectedArithmeticInput

/-- Build the corrected reconstruction input from the corrected arithmetic supply.  The source
carrier is `G_K` definitionally, so the carrier equivalence is the identity; tame surjectivity,
wild pro-2-ness, and the degree are also projected from the existing arithmetic packets. -/
noncomputable def ofKExactSupplyRN
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    {Rec : LocalReciprocity} {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}
    {T : OrientedTameQuotientK B FF} {h : ℕ}
    (S : KExactSupplyRN T (2 * h + 1) (LCore h) (SqCore.isProP_DSq h) (LNu h))
    (params : FieldParameters) (params_n : params.n = 2 * h + 1)
    (params_qK : params.qK = qOf K FF)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) W cc rho)) :
    GammaLCorrectedArithmeticInput h (qOf K FF) K where
  source := S.toSourceRN params params_n params_qK ramifiedData
  equivGalK := ContinuousMulEquiv.refl (GalK K)
  tame_surjective := T.tameFK_surjective
  wild_isProP := T.ker_tameFK ▸ T.isProP
  degree_eq := S.hdeg

/-- Existing legacy arithmetic data upgrades to the corrected reconstruction input after
supplying only the corrected equation-(136) clause.  This is the exact API-level difference
between `KExactSupply` and the `RN` reconstruction. -/
noncomputable def ofKExactSupply_and_correctedRStage
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    {Rec : LocalReciprocity} {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}
    {T : OrientedTameQuotientK B FF} {h : ℕ}
    (S : KExactSupply T (2 * h + 1) (LCore h) (SqCore.isProP_DSq h) (LNu h))
    (stageRN : CorrectedRStageSemantics (galKProfinite K) (2 * h + 1) (qOf K FF)
      (LCore h) (LNu h) (LSN (2 * h + 1)))
    (params : FieldParameters) (params_n : params.n = 2 * h + 1)
    (params_qK : params.qK = qOf K FF)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) W cc rho)) :
    GammaLCorrectedArithmeticInput h (qOf K FF) K :=
  ofKExactSupplyRN (KExactSupplyRN.ofKExactSupply S stageRN)
    params params_n params_qK ramifiedData

/-- More granular form of `ofKExactSupply_and_correctedRStage`: `blockStageR136NK` is applied
internally, leaving precisely radical-obstruction separation and the corrected R-cocycle count. -/
noncomputable def ofKExactSupply_and_RStageResidues
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    {Rec : LocalReciprocity} {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}
    {T : OrientedTameQuotientK B FF} {h : ℕ}
    (S : KExactSupply T (2 * h + 1) (LCore h) (SqCore.isProP_DSq h) (LNu h))
    (Rstage : CorrectedRStageResiduesGalK K (2 * h + 1) (qOf K FF)
      (LCore h) (LNu h) (LSN (2 * h + 1)))
    (params : FieldParameters) (params_n : params.n = 2 * h + 1)
    (params_qK : params.qK = qOf K FF)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) W cc rho)) :
    GammaLCorrectedArithmeticInput h (qOf K FF) K :=
  ofKExactSupplyRN (KExactSupplyRN.ofKExactSupplyAndRStageResidues S Rstage)
    params params_n params_qK ramifiedData

/-- Compatibility reconstruction from legacy arithmetic data and an explicit GalK separation
record.  The canonical constructor below discharges this record from Tate duality. -/
noncomputable def ofKExactSupply_and_RStageSeparation
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    {Rec : LocalReciprocity} {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}
    {T : OrientedTameQuotientK B FF} {h : ℕ}
    (S : KExactSupply T (2 * h + 1) (LCore h) (SqCore.isProP_DSq h) (LNu h))
    (Sep : CorrectedRStageSeparationGalK K (qOf K FF) (LCore h) (LNu h))
    (params : FieldParameters) (params_n : params.n = 2 * h + 1)
    (params_qK : params.qK = qOf K FF)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) W cc rho)) :
    GammaLCorrectedArithmeticInput h (qOf K FF) K :=
  ofKExactSupplyRN (KExactSupplyRN.ofKExactSupplyAndRStageSeparation S Sep)
    params params_n params_qK ramifiedData

/-- Corrected reconstruction from the legacy arithmetic supply with the entire corrected
R-stage discharged by local Euler counting and Tate `(2,0)` separation. -/
noncomputable def ofKExactSupply_canonical
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    {Rec : LocalReciprocity} {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}
    {T : OrientedTameQuotientK B FF} {h : ℕ}
    (S : KExactSupply T (2 * h + 1) (LCore h) (SqCore.isProP_DSq h) (LNu h))
    (params : FieldParameters) (params_n : params.n = 2 * h + 1)
    (params_qK : params.qK = qOf K FF)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) W cc rho)) :
    GammaLCorrectedArithmeticInput h (qOf K FF) K :=
  ofKExactSupplyRN (KExactSupplyRN.ofKExactSupplyCanonical S)
    params params_n params_qK ramifiedData

/-- Degree-one specialization of the corrected arithmetic constructor.  Unlike the general
odd-degree constructor, this needs no extra equation-(136) input because the corrected and
legacy coefficients coincide at `n = 1`. -/
noncomputable def ofKExactSupplyDegreeOne
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    {Rec : LocalReciprocity} {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}
    {T : OrientedTameQuotientK B FF}
    (S : KExactSupply T 1 (LCore 0) (SqCore.isProP_DSq 0) (LNu 0))
    (params : FieldParameters) (params_n : params.n = 1)
    (params_qK : params.qK = qOf K FF)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) W cc rho)) :
    GammaLCorrectedArithmeticInput 0 (qOf K FF) K :=
  ofKExactSupplyRN (KExactSupplyRN.ofKExactSupplyStandardOne S)
    params params_n params_qK ramifiedData

end GammaLCorrectedArithmeticInput

/-- Corrected finite-quotient reconstruction compares a certified L word source with an
arithmetic corrected source.  This is the carrier-noncircular core of the realization route. -/
noncomputable def gammaLFieldRealization_of_wordCertificateRN_reconstruction
    {h q : ℕ} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    (W : WordCertificateRN (2 * h + 1) q (Words.LSq.lSqW h) (LCore h)
      (SqCore.isProP_DSq h) (LNu h) (LSN (2 * h + 1)))
    (AK : GammaLCorrectedArithmeticInput h q K)
    (hq2 : 2 ≤ q) (hqe : Even q) : GammaLFieldRealization h q where
  subgroup := GalKsub K
  isOpen_subgroup := isOpen_fixingSubgroup K
  equiv := (nonempty_continuousMulEquiv_of_sourcesRN (W.toSourceRN hq2 hqe) AK.source
    (q_ne_zero_of_two_le hq2) hqe (lNu_surjective h)
    W.htame W.hwild AK.tame_surjective AK.wild_isProP).some.trans AK.equivGalK
  index_eq := (IntermediateField.finrank_eq_fixingSubgroup_index K).symm.trans AK.degree_eq

/-- End-to-end realization from the proved action-image Stokes theorem, the three remaining
candidate analytic bundles, and a corrected arithmetic source. -/
noncomputable def gammaLFieldRealization_of_actionImage_reconstruction
    {h q : ℕ} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    (hq2 : 2 ≤ q) (hqe : Even q) (A : LSquareAnalyticLeavesRN h q hq2 hqe)
    (AK : GammaLCorrectedArithmeticInput h q K) : GammaLFieldRealization h q :=
  gammaLFieldRealization_of_wordCertificateRN_reconstruction
    (wordCertificateRN_lSq_of_actionImage hq2 hqe A) AK hq2 hqe

/-! ## The two requested downstream statements -/

/-- The corrected reconstruction route supplies full Tate duality (through the existing B6
field theorem). -/
noncomputable def gammaL_tateDualityG_of_actionImage_reconstruction
    {h q : ℕ} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    (hq2 : 2 ≤ q) (hqe : Even q) (A : LSquareAnalyticLeavesRN h q hq2 hqe)
    (AK : GammaLCorrectedArithmeticInput h q K)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)] :
    TateDualityG (gamma h q : Type) 2 :=
  gammaL_tateDualityG (gammaLFieldRealization_of_actionImage_reconstruction hq2 hqe A AK)

/-- The same realization supplies the one-map uniform simple `H²`-surjectivity interface via
the field Euler characteristic. -/
theorem uniformSimpleH2SurjectiveSingleSupply_of_actionImage_reconstruction
    {h q : ℕ} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    (hq2 : 2 ≤ q) (hqe : Even q) (A : LSquareAnalyticLeavesRN h q hq2 hqe)
    (AK : GammaLCorrectedArithmeticInput h q K) :
    UniformSimpleH2SurjectiveSingleSupply (h := h) (q := q) :=
  uniformSimpleH2SurjectiveSingleSupply_of_fieldRealization
    (gammaLFieldRealization_of_actionImage_reconstruction hq2 hqe A AK)

/-- The same realization supplies the paired primal/dual uniform simple `H²`-surjectivity
interface. -/
theorem uniformSimpleH2SurjectiveSupply_of_actionImage_reconstruction
    {h q : ℕ} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    (hq2 : 2 ≤ q) (hqe : Even q) (A : LSquareAnalyticLeavesRN h q hq2 hqe)
    (AK : GammaLCorrectedArithmeticInput h q K) :
    UniformSimpleH2SurjectiveSupply (h := h) (q := q) :=
  uniformSimpleH2SurjectiveSupply_of_fieldRealization
    (gammaLFieldRealization_of_actionImage_reconstruction hq2 hqe A AK)

end

end GQ2.Dyadic.LSquare

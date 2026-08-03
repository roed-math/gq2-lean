/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.CertificateSupplyRN
import GQ2.Dyadic.Instances.GammaLAnalyticLeaves
import GQ2.Dyadic.Instances.GammaLEulerH2Surjectivity
import GQ2.Dyadic.Instances.GammaLRealizationRoute

/-!
# Corrected reconstruction for the improved L presentation

This file composes the completed word-level action-image argument with the corrected (`RN`)
finite-quotient reconstruction theorem.  It deliberately keeps the two genuinely separate
remaining inputs visible.

* `LSquareAnalyticLeavesRN` contains the two Stokes tail clauses and affine determinant not yet
  produced by the direct action-image argument.  Scalar Hilbert and the first two Stokes clauses
  are theorems.
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

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count
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

/-- The exact analytic residue after the direct action-image consequences are used: character
nondegeneracy, the `V`-cocycle count, and the affine determinant.

The scalar certificate and the first two Stokes clauses (`tcocycle` and `hsep`) are deliberately
absent: `GammaLAnalyticLeaves` constructs them from the same action-image theorem used for exact
lifting. -/
structure LSquareAnalyticLeavesRN (h q : ℕ) (hq2 : 2 ≤ q) (hqe : Even q) where
  hpartial : letI := scalarActionZmodTwo (gamma h q : Type)
    ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
      [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
      {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
      (b : ContinuousMonoidHom (gamma h q) ↥(boundarySubgroupQ q (LNu h)))
      (F : BoundaryFrameK q (LCore h) H E)
      (En : RF.Enrichment) (l : RF.DR) (hl : l ≠ RF.zeroDR)
      (Dsc : Descent (En.radData l hl)) (ρ : BoundaryLiftsK b F RF.TC)
      (χ : ↥(TCharC (En.radData l hl))), χ ≠ 0 →
      ∃ c : VCocycle (En.descData l hl) (rhoPrimeK RF b F (En.radData l hl) rfl ρ),
        betaChi (descSections En l hl Dsc) (descSigma_spec En l hl Dsc) χ c ≠
          betaChi (descSections En l hl Dsc) (descSigma_spec En l hl Dsc) χ
            (0 : VCocycle (En.descData l hl)
              (rhoPrimeK RF b F (En.radData l hl) rfl ρ))
  hZcard : letI := scalarActionZmodTwo (gamma h q : Type)
    ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
      [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
      {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
      (b : ContinuousMonoidHom (gamma h q) ↥(boundarySubgroupQ q (LNu h)))
      (F : BoundaryFrameK q (LCore h) H E)
      (En : RF.Enrichment) (l : RF.DR) (hl : l ≠ RF.zeroDR),
      (∀ W : AddSubgroup En.Vmod, (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤) →
      (∃ v : En.Vmod, v ≠ 0) →
      (∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v) →
      ∀ ρ : BoundaryLiftsK b F RF.TC,
        Nat.card (VCocycle (En.descData l hl)
          (rhoPrimeK RF b F (En.radData l hl) rfl ρ)) =
          Nat.card En.Vmod * (LSN (2 * h + 1)).h1Mult (Nat.card En.Vmod)
  determinant : AffineDeterminantCertificate (gamma h q) (2 * h + 1) q
    (LCore h) (LNu h) (LSN (2 * h + 1))
    (tameOfSpec (2 * h + 1) q (Words.LSq.lSqW h)
      (lCanonicalTameSpecialization h q hq2 hqe))
    (lCanonicalPro2 h q hq2 hqe) (lCanonicalCompat h q hq2 hqe)
    (scalarActionZmodTwo (gamma h q : Type))

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
  stokes := ⟨tcocycle_of_uniformPushed (uniformPushedHsimp_of_actionImage hqe) hqe,
    hsep_of_uniformPushed (uniformPushedHsimp_of_actionImage hqe) hqe,
    A.hpartial, A.hZcard⟩
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

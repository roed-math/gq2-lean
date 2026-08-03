/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLActionImageDevissage
import GQ2.Dyadic.Count.Marking
import GQ2.Dyadic.Count.LocalDuality
import GQ2.Dyadic.CertificateSupplyFamilyRN

/-!
# Analytic certificate leaves for the improved odd/L presentation

The direct action-image theorem supplies substantially more than exact lifting.  At the fixed
uniform L resolver it also supplies every word-duality payload used by the count comparison:
the scalar character count, scalar `H^2`, the two cocycle counts, marking separation, and right
separation.  Thus `StokesDualityCertificate` and `ScalarHilbertCertificate` are theorems for the
improved `lSqW` presentation, without Tate duality, a local Euler characteristic, or an
identification with a field Galois group.

The only analytic leaf not constructed here is `AffineDeterminantCertificate`.  Its two
`GaussZResidueK` conclusions are the genuinely arithmetic/affine-phase residue: the existing
L-word Hessian computation determines the quadratic form but does not determine those two Gauss
values.  The final constructor therefore exposes exactly that certificate, and nothing from the
Stokes or scalar blocks, as its remaining hypothesis.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.LSq
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes
open GQ2.Dyadic.Count GQ2.Dyadic.Count.PilotN
open GQ2.CardH2GammaA
open TameSpec

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-! ## Scalar certificate -/

/-- The scalar continuous-character count from the direct uniform Stokes theorem. -/
theorem homCard_of_uniformPushed {h q : ℕ} (hsimp : UniformPushedHsimp h q)
    (hqe : Even q) :
    Nat.card (ContinuousMonoidHom ((gamma h q : Type)) (Multiplicative (ZMod 2))) =
      (standardNumerics (2 * h + 1)).homScalar := by
  letI : TopologicalSpace Base := ⊥
  letI : DiscreteTopology Base := ⟨rfl⟩
  letI : DiscreteTopology (Base ⧸ datum.M) :=
    CentralObstruction.discreteTopology_quotient datum
  letI := scalarActionZmodTwo (Base ⧸ datum.M)
  let rho := datumRho h q
  have hb := resolvesAt_and_endpoint_lSqFam_uniformHeis
    (C := Base ⧸ datum.M) (A := ZMod 2)
    (by decide : ∀ a : ZMod 2, a + a = 0) (h := h) (q := q) hqe
  have hres : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q (omega2Exp (4 * Monoid.exponent (Base ⧸ datum.M))))
      (WordLift (ZMod 2) (Base ⧸ datum.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (ZMod 2) (Base ⧸ datum.M))
        (HeisLift (ZMod 2) (Base ⧸ datum.M)) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisPrim_injective
  exact homCard_field_goal rho (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h)) hres
    (isWildTwo_of_gammaGen rho (datumRho_surjective h q) (fun _ => rfl))
    (degree h)
    (hsimp (Base ⧸ datum.M) rho (ZMod 2)
      (by decide : ∀ a : ZMod 2, a + a = 0)) hb.2

/-- The complete scalar Hilbert certificate for the improved L presentation. -/
theorem scalarHilbertCertificate_of_uniformPushed {h q : ℕ}
    (hsimp : UniformPushedHsimp h q) (hqe : Even q) :
    ScalarHilbertCertificate (gamma h q) (2 * h + 1)
      (standardNumerics (2 * h + 1))
      (scalarActionZmodTwo ((gamma h q : Type))) :=
  ⟨homCard_of_uniformPushed hsimp hqe, cardH2_of_uniformPushed hsimp hqe⟩

/-- The action-image proof discharges the scalar certificate directly. -/
theorem scalarHilbertCertificate_of_actionImage {h q : ℕ} (hqe : Even q) :
    ScalarHilbertCertificate (gamma h q) (2 * h + 1)
      (standardNumerics (2 * h + 1))
      (scalarActionZmodTwo ((gamma h q : Type))) :=
  scalarHilbertCertificate_of_uniformPushed (uniformPushedHsimp_of_actionImage hqe) hqe

/-! ## Stokes certificate: the `T`-side clauses -/

set_option maxHeartbeats 1200000 in
/-- The `T`-cocycle count at every recursion frame, from the direct uniform word duality. -/
theorem tcocycle_of_uniformPushed {h q : ℕ} (hsimp : UniformPushedHsimp h q)
    (hqe : Even q) {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((gamma h q : Type)) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR)
    (hl : l ≠ RF.zeroDR) (ρ : BoundaryLiftsK b F RF.TC) :
    Nat.card (TCocycle (En.radData l hl) (rhoPrimeK RF b F (En.radData l hl) rfl ρ)) =
      (standardNumerics (2 * h + 1)).tMult
          (Nat.card (Additive ↥(En.radData l hl).T)) *
        Nat.card (fixedPts (RF.YB ⧸ (En.radData l hl).M)
          (ElemDual (Additive ↥(En.radData l hl).T))) := by
  let D := En.radData l hl
  let rho := rhoPrimeK RF b F D rfl ρ
  letI : TopologicalSpace (Additive ↥D.T) := ⊥
  haveI : DiscreteTopology (Additive ↥D.T) := ⟨rfl⟩
  letI : DistribMulAction ((gamma h q : Type)) (Additive ↥D.T) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  haveI : ContinuousSMul ((gamma h q : Type)) (Additive ↥D.T) := by
    constructor
    have hfac :
        (fun p : ((gamma h q : Type)) × Additive ↥D.T => p.1 • p.2) =
          (fun p : (RF.YB ⧸ D.M) × Additive ↥D.T => p.1 • p.2) ∘
            (fun p : ((gamma h q : Type)) × Additive ↥D.T => (rho p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  letI := scalarActionZmodTwo (RF.YB ⧸ D.M)
  have hb := resolvesAt_and_endpoint_lSqFam_uniformHeis
    (C := RF.YB ⧸ D.M) (A := Additive ↥D.T) (radT_add_self D)
    (h := h) (q := q) hqe
  have hres : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q (omega2Exp (4 * Monoid.exponent (RF.YB ⧸ D.M))))
      (WordLift (Additive ↥D.T) (RF.YB ⧸ D.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (Additive ↥D.T) (RF.YB ⧸ D.M))
        (HeisLift (Additive ↥D.T) (RF.YB ⧸ D.M)) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisPrim_injective
  exact tcocycle_cardN rho (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h)) hres
    (radT_add_self D)
    (isWildTwo_of_gammaGen rho (rhoPrimeK_surjective RF b F D rfl ρ) (fun _ => rfl))
    (rhoPrimeK_surjective RF b F D rfl ρ) (degree h)
    (hsimp (RF.YB ⧸ D.M) rho (Additive ↥D.T) (radT_add_self D)) hb.2

set_option maxHeartbeats 1200000 in
/-- The `(T^∨)^C` separation clause via the word-side marking route. -/
theorem hsep_of_uniformPushed {h q : ℕ} (hsimp : UniformPushedHsimp h q)
    (hqe : Even q) {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((gamma h q : Type)) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR)
    (hl : l ≠ RF.zeroDR) (Dsc : Descent (En.radData l hl))
    (ρ : BoundaryLiftsK b F RF.TC)
    (c : VCocycle (En.descData l hl) (rhoPrimeK RF b F (En.radData l hl) rfl ρ))
    (hvan : letI := scalarActionZmodTwo ((gamma h q : Type))
      ∀ chi : ↥(TCharC (En.radData l hl)),
        betaChi (descSections En l hl Dsc) (descSigma_spec En l hl Dsc) chi c = 0) :
    TLiftable (descSigma_spec En l hl Dsc) c := by
  let D := En.radData l hl
  let rho := rhoPrimeK RF b F D rfl ρ
  letI := scalarActionZmodTwo ((gamma h q : Type))
  letI := scalarActionZmodTwo (RF.YB ⧸ D.M)
  have hb := resolvesAt_and_endpoint_lSqFam_uniformHeis
    (C := RF.YB ⧸ D.M) (A := Additive ↥D.T) (radT_add_self D)
    (h := h) (q := q) hqe
  have hres2 : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q (omega2Exp (4 * Monoid.exponent (RF.YB ⧸ D.M))))
      (WordLift (ZMod 2) (RF.YB ⧸ D.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (ZMod 2) (RF.YB ⧸ D.M))
        (HeisLift (Additive ↥D.T) (RF.YB ⧸ D.M)) :=
      ⟨Count.heisScal, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisScal_injective
  have hresT : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q (omega2Exp (4 * Monoid.exponent (RF.YB ⧸ D.M))))
      (WordLift (Additive ↥D.T) (RF.YB ⧸ D.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (Additive ↥D.T) (RF.YB ⧸ D.M))
        (HeisLift (Additive ↥D.T) (RF.YB ⧸ D.M)) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisPrim_injective
  exact hsep_field_goal_marking b F En l hl Dsc ρ (scalarActionZmodTwo _)
    (scalarActionZmodTwo_triv _) (scalarActionZmodTwo _) (scalarActionZmodTwo_triv _)
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h)) (fun _ => rfl)
    (isWildTwo_of_gammaGen rho (rhoPrimeK_surjective RF b F D rfl ρ) (fun _ => rfl))
    hres2 hresT (hsimp (RF.YB ⧸ D.M) rho (Additive ↥D.T) (radT_add_self D))
    hb.2 c hvan

/-! ## Stokes certificate: the `V`-side clauses -/

/-- Surjectivity of the continuous descent lower map. -/
theorem rho0Continuous_surjective
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    {D : RadicalCoverData Bg} (DD : DescData D)
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    {G : Type} [Group G] [TopologicalSpace G]
    (rho : ContinuousMonoidHom G (Bg ⧸ D.M)) (hrho : Function.Surjective rho) :
    Function.Surjective (Count.rho0Continuous DD rho) := by
  intro c0
  obtain ⟨bb, hbb⟩ := DD.hpiC0 c0
  obtain ⟨g, hg⟩ := hrho (QuotientGroup.mk bb)
  exact ⟨g, (rho0_apply_of_rep DD rho g bb hg.symm).trans hbb⟩

set_option maxHeartbeats 1600000 in
/-- Right separation for the descent module, obtained entirely from uniform word Stokes
duality and the comparison theorem `isRightSeparating_of_selfDualN`. -/
theorem hrsep_of_uniformPushed {h q : ℕ} (hsimp : UniformPushedHsimp h q)
    (hqe : Even q) {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((gamma h q : Type)) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR)
    (hl : l ≠ RF.zeroDR) (ρ : BoundaryLiftsK b F RF.TC) :
    letI := scalarActionZmodTwo ((gamma h q : Type))
    letI : TopologicalSpace (En.descData l hl).Vmod := ⊥
    haveI : DiscreteTopology (En.descData l hl).Vmod := ⟨rfl⟩
    letI : DistribMulAction ((gamma h q : Type)) (En.descData l hl).Vmod :=
      DistribMulAction.compHom (En.descData l hl).Vmod
        (rho0 (En.descData l hl) (rhoPrimeK RF b F (En.radData l hl) rfl ρ))
    letI : TopologicalSpace (ElemDual (En.descData l hl).Vmod) := ⊥
    haveI : DiscreteTopology (ElemDual (En.descData l hl).Vmod) := ⟨rfl⟩
    IsRightSeparating ((gamma h q : Type)) (En.descData l hl).Vmod := by
  let D := En.radData l hl
  let DD := En.descData l hl
  let rho := rhoPrimeK RF b F D rfl ρ
  letI := scalarActionZmodTwo ((gamma h q : Type))
  haveI := scalarActionZmodTwo_continuousSMul ((gamma h q : Type))
  letI : TopologicalSpace DD.Vmod := ⊥
  haveI : DiscreteTopology DD.Vmod := ⟨rfl⟩
  letI : DistribMulAction ((gamma h q : Type)) DD.Vmod :=
    DistribMulAction.compHom DD.Vmod (rho0 DD rho)
  letI : TopologicalSpace (ElemDual DD.Vmod) := ⊥
  haveI : DiscreteTopology (ElemDual DD.Vmod) := ⟨rfl⟩
  letI : TopologicalSpace DD.C0 := ⊥
  haveI : DiscreteTopology DD.C0 := ⟨rfl⟩
  letI := scalarActionZmodTwo DD.C0
  let theta := Count.rho0Continuous DD rho
  have hcompat : ∀ (g : ((gamma h q : Type))) (a : DD.Vmod), g • a = theta g • a :=
    fun _ _ => rfl
  haveI : ContinuousSMul ((gamma h q : Type)) (ElemDual DD.Vmod) := by
    constructor
    have hfac :
        (fun p : ((gamma h q : Type)) × ElemDual DD.Vmod => p.1 • p.2) =
          (fun p : DD.C0 × ElemDual DD.Vmod => p.1 • p.2) ∘
            (fun p : ((gamma h q : Type)) × ElemDual DD.Vmod => (theta p.1, p.2)) := by
      funext p
      exact elemDual_compat theta hcompat p.1 p.2
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((theta.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hb := resolvesAt_and_endpoint_lSqFam_uniformHeis
    (C := DD.C0) (A := DD.Vmod) (Vmod_exp2 DD) (h := h) (q := q) hqe
  have hresS : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q (omega2Exp (4 * Monoid.exponent DD.C0)))
      (WordLift (ZMod 2) DD.C0) := by
    let incl : ContinuousMonoidHom (WordLift (ZMod 2) DD.C0) (HeisLift DD.Vmod DD.C0) :=
      ⟨Count.heisScal, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisScal_injective
  have hresP : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q (omega2Exp (4 * Monoid.exponent DD.C0)))
      (WordLift DD.Vmod DD.C0) := by
    let incl : ContinuousMonoidHom (WordLift DD.Vmod DD.C0) (HeisLift DD.Vmod DD.C0) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisPrim_injective
  have hresD : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q (omega2Exp (4 * Monoid.exponent DD.C0)))
      (WordLift (ElemDual DD.Vmod) DD.C0) := by
    let incl : ContinuousMonoidHom
        (WordLift (ElemDual DD.Vmod) DD.C0) (HeisLift DD.Vmod DD.C0) :=
      ⟨Count.heisDual, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisDual_injective
  have hsurj : Function.Surjective theta :=
    rho0Continuous_surjective DD rho (rhoPrimeK_surjective RF b F D rfl ρ)
  have hwild := isWildTwo_of_gammaGen theta hsurj (fun _ => rfl)
  have hd := hsimp DD.C0 theta DD.Vmod (Vmod_exp2 DD)
  have hsd : IsSelfDualN (2 * h + 1)
      (fun g => theta (gammaGen (2 * h + 1) q (lSqW h) g))
      (lSqFam h q (omega2Exp (4 * Monoid.exponent DD.C0))) DD.Vmod :=
    isSelfDualN_of_stokesDuality (degree h) hd
      (lower_rel theta (fun _ => rfl)
        (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h)) hresP) hb.2
  exact isRightSeparating_of_selfDualN theta hcompat (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h)) hwild
    hresS hresP hresD hb.1 hsd hb.2 (Vmod_exp2 DD)

set_option maxHeartbeats 1600000 in
/-- The nonzero-character obstruction clause from word-side right separation and the direct
scalar `H^2` count. -/
theorem hpartial_of_uniformPushed {h q : ℕ} (hsimp : UniformPushedHsimp h q)
    (hqe : Even q) {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((gamma h q : Type)) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR)
    (hl : l ≠ RF.zeroDR) (Dsc : Descent (En.radData l hl))
    (ρ : BoundaryLiftsK b F RF.TC) (chi : ↥(TCharC (En.radData l hl)))
    (hchi : chi ≠ 0) :
    letI := scalarActionZmodTwo ((gamma h q : Type))
    ∃ c : VCocycle (En.descData l hl) (rhoPrimeK RF b F (En.radData l hl) rfl ρ),
      betaChi (descSections En l hl Dsc) (descSigma_spec En l hl Dsc) chi c ≠
        betaChi (descSections En l hl Dsc) (descSigma_spec En l hl Dsc) chi
          (0 : VCocycle (En.descData l hl)
            (rhoPrimeK RF b F (En.radData l hl) rfl ρ)) :=
  hpartial_field_goal b F En l hl Dsc ρ (scalarActionZmodTwo _)
    (scalarActionZmodTwo_triv _) (cardH2_of_uniformPushed hsimp hqe)
    (hrsep_of_uniformPushed hsimp hqe b F En l hl ρ) chi hchi

set_option maxHeartbeats 1200000 in
/-- The simple nontrivial `V`-cocycle count at every recursion frame. -/
theorem hZcard_of_uniformPushed {h q : ℕ} (hsimp : UniformPushedHsimp h q)
    (hqe : Even q) {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((gamma h q : Type)) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR)
    (hl : l ≠ RF.zeroDR)
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v)
    (ρ : BoundaryLiftsK b F RF.TC) :
    Nat.card (VCocycle (En.descData l hl)
        (rhoPrimeK RF b F (En.radData l hl) rfl ρ)) =
      Nat.card En.Vmod *
        (standardNumerics (2 * h + 1)).h1Mult (Nat.card En.Vmod) := by
  let D := En.radData l hl
  let DD := En.descData l hl
  letI : TopologicalSpace DD.Vmod := ⊥
  haveI : DiscreteTopology DD.Vmod := ⟨rfl⟩
  letI : DistribMulAction RF.YC DD.Vmod :=
    (inferInstance : DistribMulAction RF.YC En.Vmod)
  letI : DistribMulAction ((gamma h q : Type)) DD.Vmod :=
    DistribMulAction.compHom _ ρ.1.1.toMonoidHom
  haveI : ContinuousSMul ((gamma h q : Type)) DD.Vmod := by
    constructor
    have hfac :
        (fun p : ((gamma h q : Type)) × DD.Vmod => p.1 • p.2) =
          (fun p : RF.YC × DD.Vmod => p.1 • p.2) ∘
            (fun p : ((gamma h q : Type)) × DD.Vmod => (ρ.1.1 p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((ρ.1.1.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  letI := scalarActionZmodTwo RF.YC
  have hb := resolvesAt_and_endpoint_lSqFam_uniformHeis
    (C := RF.YC) (A := DD.Vmod) (Vmod_exp2 DD) (h := h) (q := q) hqe
  have hres : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q (omega2Exp (4 * Monoid.exponent RF.YC)))
      (WordLift DD.Vmod RF.YC) := by
    let incl : ContinuousMonoidHom (WordLift DD.Vmod RF.YC) (HeisLift DD.Vmod RF.YC) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisPrim_injective
  have hsimple' : IsSimpleModTwo RF.YC DD.Vmod := by
    obtain ⟨v, hv⟩ := hVne
    exact ⟨nontrivial_of_ne v 0 hv, hsimple⟩
  exact hZcardN ρ.1.1
    (fun g v => congrArg (fun c : RF.YC => c • v)
      (rho0_descData_rhoPrimeK b F En l hl ρ g))
    (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h)) hres
    (Vmod_exp2 DD) (isWildTwo_of_gammaGen ρ.1.1 ρ.1.2 (fun _ => rfl)) ρ.1.2
    (degree h) (hsimp RF.YC ρ.1.1 DD.Vmod (Vmod_exp2 DD)) hb.2 hsimple' hnt

/-! ## Packed certificates and the exact residual interface -/

/-- The complete Stokes certificate for the improved L presentation. -/
theorem stokesDualityCertificate_of_uniformPushed {h q : ℕ}
    (hsimp : UniformPushedHsimp h q) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo} :
    StokesDualityCertificate (gamma h q) (2 * h + 1) q P nuP
      (standardNumerics (2 * h + 1))
      (scalarActionZmodTwo ((gamma h q : Type))) :=
  ⟨fun b F En l hl ρ => tcocycle_of_uniformPushed hsimp hqe b F En l hl ρ,
   fun b F En l hl Dsc ρ c hvan =>
    hsep_of_uniformPushed hsimp hqe b F En l hl Dsc ρ c hvan,
   fun b F En l hl Dsc ρ chi hchi =>
    hpartial_of_uniformPushed hsimp hqe b F En l hl Dsc ρ chi hchi,
   fun b F En l hl hsimple hVne hnt ρ =>
    hZcard_of_uniformPushed hsimp hqe b F En l hl hsimple hVne hnt ρ⟩

/-- The action-image proof discharges the complete Stokes certificate directly. -/
theorem stokesDualityCertificate_of_actionImage {h q : ℕ} (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo} :
    StokesDualityCertificate (gamma h q) (2 * h + 1) q P nuP
      (standardNumerics (2 * h + 1))
      (scalarActionZmodTwo ((gamma h q : Type))) :=
  stokesDualityCertificate_of_uniformPushed (uniformPushedHsimp_of_actionImage hqe) hqe

/-- Exact remaining analytic input after direct action-image Stokes and scalar counts. -/
def DeterminantResidue {h q : ℕ} {P : ProfiniteGrp}
    (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (gamma h q) (Tq q))
    (pro2 : ContinuousMonoidHom (gamma h q) P)
    (compat : ∀ g : (gamma h q : Type), nuTq q (tame g) = nuP (pro2 g)) : Prop :=
  AffineDeterminantCertificate (gamma h q) (2 * h + 1) q P nuP
    (standardNumerics (2 * h + 1)) tame pro2 compat
    (scalarActionZmodTwo ((gamma h q : Type)))

/-- Constructor regression: for the improved L presentation, the direct action-image theorem
reduces all three analytic leaves to the determinant residue alone. -/
def analyticLeaves_of_actionImage {h q : ℕ} (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (gamma h q) (Tq q))
    (pro2 : ContinuousMonoidHom (gamma h q) P)
    (compat : ∀ g : (gamma h q : Type), nuTq q (tame g) = nuP (pro2 g))
    (determinant : DeterminantResidue nuP tame pro2 compat) :
    StokesDualityCertificate (gamma h q) (2 * h + 1) q P nuP
        (standardNumerics (2 * h + 1))
        (scalarActionZmodTwo ((gamma h q : Type))) ∧
      ScalarHilbertCertificate (gamma h q) (2 * h + 1)
        (standardNumerics (2 * h + 1))
        (scalarActionZmodTwo ((gamma h q : Type))) ∧
      AffineDeterminantCertificate (gamma h q) (2 * h + 1) q P nuP
        (standardNumerics (2 * h + 1)) tame pro2 compat
        (scalarActionZmodTwo ((gamma h q : Type))) :=
  ⟨stokesDualityCertificate_of_actionImage hqe,
   scalarHilbertCertificate_of_actionImage hqe, determinant⟩

/-- Selector-level constructor for the corrected certificate pipeline.  On an L row, the
`SemanticSelectedAnalyticLeavesRN` input is reduced definitionally to its determinant field. -/
noncomputable def semanticSelectedAnalyticLeavesRN_of_actionImage
    {FP : FieldParameters} (S : SemanticSelectionView FP) {q : ℕ}
    (hbranch : S.branch = .L) {P : ProfiniteGrp} (hP : IsProP 2 P)
    (nuP : ContinuousMonoidHom P Ztwo) (hq0 : q ≠ 0) (hqe : Even q)
    (C : SemanticSelectedCoreLeavesRN S P nuP)
    (determinant : AffineDeterminantCertificate
      (GammaR S.semantic.degree q S.semantic.word) S.semantic.degree q P nuP
      (standardNumerics S.semantic.degree)
      (tameOfSpec S.semantic.degree q S.semantic.word
        (tameSpecialization_of_semanticSelection S hq0 hqe))
      (C.pro2 hq0 hqe) (C.compat hq0 hqe)
      (scalarActionZmodTwo (GammaR S.semantic.degree q S.semantic.word))) :
    SemanticSelectedAnalyticLeavesRN S q P hP nuP hq0 hqe C := by
  cases S with
  | mk branch valid display =>
      dsimp only at hbranch
      subst branch
      exact
        { stokes := stokesDualityCertificate_of_actionImage hqe
          scalar := scalarHilbertCertificate_of_actionImage hqe
          determinant := determinant }

/-- Regression theorem exposing the exact post-action-image analytic obligation: on the
improved L row, a determinant certificate alone constructs all selected analytic leaves. -/
theorem exists_semanticSelectedAnalyticLeavesRN_of_actionImage
    {FP : FieldParameters} (S : SemanticSelectionView FP) {q : ℕ}
    (hbranch : S.branch = .L) {P : ProfiniteGrp} (hP : IsProP 2 P)
    (nuP : ContinuousMonoidHom P Ztwo) (hq0 : q ≠ 0) (hqe : Even q)
    (C : SemanticSelectedCoreLeavesRN S P nuP)
    (determinant : AffineDeterminantCertificate
      (GammaR S.semantic.degree q S.semantic.word) S.semantic.degree q P nuP
      (standardNumerics S.semantic.degree)
      (tameOfSpec S.semantic.degree q S.semantic.word
        (tameSpecialization_of_semanticSelection S hq0 hqe))
      (C.pro2 hq0 hqe) (C.compat hq0 hqe)
      (scalarActionZmodTwo (GammaR S.semantic.degree q S.semantic.word))) :
    Nonempty (SemanticSelectedAnalyticLeavesRN S q P hP nuP hq0 hqe C) :=
  ⟨semanticSelectedAnalyticLeavesRN_of_actionImage S hbranch hP nuP hq0 hqe C determinant⟩

end

end GQ2.Dyadic.LSquare

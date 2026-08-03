/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLActionImageDevissage
import GQ2.Dyadic.Count.Marking
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

end

end GQ2.Dyadic.LSquare

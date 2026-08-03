/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLAnalyticLeaves
import GQ2.Dyadic.Instances.LRamifiedHessian
import GQ2.Dyadic.GaussZ.FinalDK

/-!
# The exact word-phase seam for the L determinant residue

`AffineDeterminantCertificate` does not consume a word Hessian directly.  It consumes
`GaussZResidueK`, a signed sum of the continuous source form `QZero` over `VCocycle`.  The
generic reduction already descends that sum to `QZeroBar` on `Z¹/B¹`.  The missing comparison
is therefore an equivalence from this source quotient to the word endpoint, preserving the
quadratic value.

This file isolates precisely that seam.  Once a `SourceWordPhaseComparison` is supplied,
`gaussZResidueK_of_wordPhase` converts any proved word Gauss sum into the source residue.
`gaussZResidueK_of_hessian` and `gaussZResidueK_of_phaseCover` specialize the result to the two
existing word certificate APIs.  No Tate duality, local Euler characteristic, field
equivalence, or new axiom is used.

For the improved L presentation, the final section packages the exact unramified and ramified
comparison obligations and reconstructs `AffineDeterminantCertificate`.  The polar ramified
Hessian alone does not choose an Arf sign, but `Certificates.L.hessRelZ_lSq` separately computes
the actual quadratic diagonal as the Wall double `qDouble`, plus hyperbolic handles.  The finite
ramified Arf/Gauss calculation for that explicit diagonal is closed in
`GammaLRamifiedPhase`; the genuine remaining input is its pointwise identification with the
descended continuous source form `QZeroBar`.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.LSq
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes
open GQ2.Dyadic.Count
open GQ2.QuadraticFp2

/-- The two pre-existing spellings of the nontrivial `ZMod 2` sign character agree. -/
theorem sectionEight_sign_eq_quadraticSign (a : ZMod 2) :
    SectionEight.sign a = QuadraticFp2.sign a := by
  revert a
  decide

/-! ## Generic source-to-word phase comparison -/

/-- The missing comparison datum between the descended continuous source phase and a word
endpoint.  No additivity is required of the equivalence: the Gauss sum only needs a bijective
change of variables and pointwise preservation of the quadratic value. -/
structure SourceWordPhaseComparison
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} (DD : DescData D)
    {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
    (rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M))
    [DistribMulAction Gamma (ZMod 2)]
    (htriv : ∀ (g : Gamma) (a : ZMod 2), g • a = a)
    (W : Type) [Fintype W] (Q : W → ZMod 2) where
  phaseEquiv : (VCocycle DD rho ⧸ vCobRange DD rho) ≃ W
  phase_eq : ∀ x, QZeroBar DD rho htriv x = Q (phaseEquiv x)

/-- Reindex the descended source Gauss sum along a source-to-word phase comparison. -/
theorem SourceWordPhaseComparison.finsum_eq_gaussSum
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
    {rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M)}
    [DistribMulAction Gamma (ZMod 2)]
    {htriv : ∀ (g : Gamma) (a : ZMod 2), g • a = a}
    {W : Type} [Fintype W] {Q : W → ZMod 2}
    [Finite (VCocycle DD rho)]
    (C : SourceWordPhaseComparison DD rho htriv W Q) :
    ∑ᶠ x : (VCocycle DD rho ⧸ vCobRange DD rho),
        SectionEight.sign (QZeroBar DD rho htriv x) = QuadraticFp2.gaussSum Q := by
  classical
  letI : Fintype (VCocycle DD rho ⧸ vCobRange DD rho) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  simp_rw [C.phase_eq, sectionEight_sign_eq_quadraticSign]
  change (∑ x, QuadraticFp2.sign (Q (C.phaseEquiv x))) = QuadraticFp2.gaussSum Q
  exact gaussSum_comp_equiv Q C.phaseEquiv

/-- A word-phase model for every boundary lift at one recursion frame. -/
def WordPhaseResidueK
    {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
    [DistribMulAction Gamma (ZMod 2)]
    {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom Gamma ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR)
    (hl : l ≠ RF.zeroDR)
    (htriv : ∀ (g : Gamma) (a : ZMod 2), g • a = a) (G0 : ℤ) : Prop :=
  ∀ rho : BoundaryLiftsK b F RF.TC,
    ∃ (W : Type) (_ : Fintype W) (Q : W → ZMod 2),
      Nonempty (SourceWordPhaseComparison (En.descData l hl)
        (rhoPrimeK RF b F (En.radData l hl) rfl rho) htriv W Q) ∧
      QuadraticFp2.gaussSum Q = G0

/-- The reusable Hessian/word-phase to `GaussZResidueK` bridge at one boundary lift. -/
theorem sourceGauss_eq_of_wordPhase
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma] [IsTopologicalGroup Gamma]
    {rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M)}
    [DistribMulAction Gamma (ZMod 2)] [ContinuousSMul Gamma (ZMod 2)]
    {htriv : ∀ (g : Gamma) (a : ZMod 2), g • a = a}
    {W : Type} [Fintype W] {Q : W → ZMod 2}
    [Finite (VCocycle DD rho)]
    (hfix : ∀ v : DD.Vmod, (∀ g : Gamma, rho0 DD rho g • v = v) → v = 0)
    (C : SourceWordPhaseComparison DD rho htriv W Q)
    {G0 : ℤ} (hgauss : QuadraticFp2.gaussSum Q = G0) :
    ∑ᶠ c : VCocycle DD rho, SectionEight.sign (QZero DD rho c) =
      (Nat.card DD.Vmod : ℤ) * G0 := by
  rw [gaussZ_reduction htriv hfix, C.finsum_eq_gaussSum, hgauss]

/-- A per-boundary-lift word phase supplies the full source `GaussZResidueK`. -/
theorem gaussZResidueK_of_wordPhase
    {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma] [IsTopologicalGroup Gamma]
    [CompactSpace Gamma] [TotallyDisconnectedSpace Gamma]
    [DistribMulAction Gamma (ZMod 2)] [ContinuousSMul Gamma (ZMod 2)]
    {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom Gamma ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR)
    (hl : l ≠ RF.zeroDR)
    (htriv : ∀ (g : Gamma) (a : ZMod 2), g • a = a)
    (hfinite : ∀ rho : BoundaryLiftsK b F RF.TC,
      Finite (VCocycle (En.descData l hl)
        (rhoPrimeK RF b F (En.radData l hl) rfl rho)))
    (hfix : ∀ (rho : BoundaryLiftsK b F RF.TC)
      (v : (En.descData l hl).Vmod),
      (∀ g : Gamma,
        rho0 (En.descData l hl)
          (rhoPrimeK RF b F (En.radData l hl) rfl rho) g • v = v) → v = 0)
    {G0 : ℤ}
    (hphase : WordPhaseResidueK b F En l hl htriv G0) :
    GaussZResidueK b F En l hl G0 := by
  intro rho
  letI : Finite (VCocycle (En.descData l hl)
      (rhoPrimeK RF b F (En.radData l hl) rfl rho)) := hfinite rho
  obtain ⟨W, fW, Q, ⟨C⟩, hgauss⟩ := hphase rho
  letI : Fintype W := fW
  exact sourceGauss_eq_of_wordPhase (hfix rho) C hgauss

/-! ## Existing word certificate APIs feed the bridge -/

/-- A full Hessian certificate feeds the source residue once its endpoint is identified with
`QZeroBar`. -/
theorem gaussZResidueK_of_hessian
    {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma] [IsTopologicalGroup Gamma]
    [CompactSpace Gamma] [TotallyDisconnectedSpace Gamma]
    [DistribMulAction Gamma (ZMod 2)] [ContinuousSMul Gamma (ZMod 2)]
    {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom Gamma ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR)
    (hl : l ≠ RF.zeroDR)
    (htriv : ∀ (g : Gamma) (a : ZMod 2), g • a = a)
    (hfinite : ∀ rho : BoundaryLiftsK b F RF.TC,
      Finite (VCocycle (En.descData l hl)
        (rhoPrimeK RF b F (En.radData l hl) rfl rho)))
    (hfix : ∀ (rho : BoundaryLiftsK b F RF.TC)
      (v : (En.descData l hl).Vmod),
      (∀ g : Gamma, rho0 (En.descData l hl)
        (rhoPrimeK RF b F (En.radData l hl) rfl rho) g • v = v) → v = 0)
    {C V W W' : Type} [AddCommGroup V]
    [AddCommGroup W] [Module (ZMod 2) W] [Fintype W]
    [AddCommGroup W'] [Module (ZMod 2) W'] [Fintype W']
    {dat : FactorSet C V} {diag : V → ZMod 2}
    {Q : W → ZMod 2} {Qnf : W' → ZMod 2} {j0 j1 : V →+ W'}
    (HC : HessianCertificate dat diag Q Qnf j0 j1)
    (hcomparison : ∀ rho : BoundaryLiftsK b F RF.TC,
      Nonempty (SourceWordPhaseComparison (En.descData l hl)
        (rhoPrimeK RF b F (En.radData l hl) rfl rho) htriv W Q)) :
    GaussZResidueK b F En l hl HC.affinePhase.G0 :=
  gaussZResidueK_of_wordPhase b F En l hl htriv hfinite hfix
    (fun rho ↦ ⟨W, inferInstance, Q, hcomparison rho, HC.endpoint_gaussSum⟩)

/-- A `PhaseCoverCertificate` feeds the source residue directly at its normal form. -/
theorem gaussZResidueK_of_phaseCover
    {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma] [IsTopologicalGroup Gamma]
    [CompactSpace Gamma] [TotallyDisconnectedSpace Gamma]
    [DistribMulAction Gamma (ZMod 2)] [ContinuousSMul Gamma (ZMod 2)]
    {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom Gamma ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR)
    (hl : l ≠ RF.zeroDR)
    (htriv : ∀ (g : Gamma) (a : ZMod 2), g • a = a)
    (hfinite : ∀ rho : BoundaryLiftsK b F RF.TC,
      Finite (VCocycle (En.descData l hl)
        (rhoPrimeK RF b F (En.radData l hl) rfl rho)))
    (hfix : ∀ (rho : BoundaryLiftsK b F RF.TC)
      (v : (En.descData l hl).Vmod),
      (∀ g : Gamma, rho0 (En.descData l hl)
        (rhoPrimeK RF b F (En.radData l hl) rfl rho) g • v = v) → v = 0)
    {C V W : Type} [AddCommGroup V] [AddCommGroup W] [Fintype W]
    {dat : FactorSet C V} {diag : V → ZMod 2}
    {Q : W → ZMod 2} {j0 j1 : V →+ W}
    (PC : PhaseCoverCertificate dat diag Q j0 j1)
    (hcomparison : ∀ rho : BoundaryLiftsK b F RF.TC,
      Nonempty (SourceWordPhaseComparison (En.descData l hl)
        (rhoPrimeK RF b F (En.radData l hl) rfl rho) htriv W Q)) :
    GaussZResidueK b F En l hl PC.G0 :=
  gaussZResidueK_of_wordPhase b F En l hl htriv hfinite hfix
    (fun rho ↦ ⟨W, inferInstance, Q, hcomparison rho, PC.gaussSum_eq_G0⟩)

/-! ## Exact L determinant phase interfaces -/

set_option linter.unusedVariables false in
/-- The exact source-to-word phase obligations remaining for the improved L presentation.

The hypotheses of the two fields are verbatim those of `AffineDeterminantCertificate`; only
the conclusion is changed from the already-summed `GaussZResidueK` to a word phase model whose
Gauss sum has the required sign. -/
structure DeterminantWordPhaseSupply {h q : ℕ} {P : ProfiniteGrp}
    (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (gamma h q) (Tq q))
    (pro2 : ContinuousMonoidHom (gamma h q) P)
    (compat : ∀ g : (gamma h q : Type), nuTq q (tame g) = nuP (pro2 g)) where
  unramified :
    letI := scalarActionZmodTwo ((gamma h q : Type))
    ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
      [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
      (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
      [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
      (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
      (F : BoundaryFrameK q P H E)
      (hsimple : ∀ W : AddSubgroup (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod,
        (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) →
          W = ⊥ ∨ W = ⊤)
      (hVne : ∃ v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod, v ≠ 0)
      (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
        (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g • v ≠ v)
      (m : ℕ) (hm : 1 ≤ m)
      (hcard : Nat.card (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod = 2 ^ (2 * m))
      (l : (SectionNine.blockFrame T Blk hE2).DR)
      (hl : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
      (hunram :
        letI := blockPS_commGroup Blk
        letI := SectionNine.headAct T Blk
        ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha (tqTau q) • v = v),
      WordPhaseResidueK (sourceBoundaryMapK tame pro2 compat) F
        (blockEnrichmentDK T Blk hE2 hq0 hqe F) l hl
        (scalarActionZmodTwo_triv _)
        ((standardNumerics (2 * h + 1)).gaussUnram m)
  ramified :
    letI := scalarActionZmodTwo ((gamma h q : Type))
    ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
      [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
      (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
      [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
      (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
      (F : BoundaryFrameK q P H E)
      (hsimple : ∀ W : AddSubgroup (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod,
        (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) →
          W = ⊥ ∨ W = ⊤)
      (hVne : ∃ v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod, v ≠ 0)
      (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
        (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g • v ≠ v)
      (m : ℕ) (hm : 1 ≤ m)
      (hcard : Nat.card (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod = 2 ^ (2 * m))
      (l : (SectionNine.blockFrame T Blk hE2).DR)
      (hl : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
      (hram :
        letI := blockPS_commGroup Blk
        letI := SectionNine.headAct T Blk
        ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha (tqTau q) • v ≠ v),
      WordPhaseResidueK (sourceBoundaryMapK tame pro2 compat) F
        (blockEnrichmentDK T Blk hE2 hq0 hqe F) l hl
        (scalarActionZmodTwo_triv _)
        ((standardNumerics (2 * h + 1)).gaussRam m)

set_option maxHeartbeats 1200000 in
/-- The exact determinant constructor for the improved L presentation.  The action-image
theorem supplies finiteness of `Z¹`, while simplicity and nontriviality kill fixed vectors;
the only additional input is the source-to-word phase comparison packaged above. -/
theorem affineDeterminantCertificate_of_wordPhaseSupply
    {h q : ℕ} {P : ProfiniteGrp}
    (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (gamma h q) (Tq q))
    (pro2 : ContinuousMonoidHom (gamma h q) P)
    (compat : ∀ g : (gamma h q : Type), nuTq q (tame g) = nuP (pro2 g))
    (S : DeterminantWordPhaseSupply nuP tame pro2 compat) :
    AffineDeterminantCertificate (gamma h q) (2 * h + 1) q P nuP
      (standardNumerics (2 * h + 1)) tame pro2 compat
      (scalarActionZmodTwo ((gamma h q : Type))) := by
  letI := scalarActionZmodTwo ((gamma h q : Type))
  haveI := scalarActionZmodTwo_continuousSMul ((gamma h q : Type))
  constructor
  · exact fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl hunram ↦ by
      let En := blockEnrichmentDK T Blk hE2 hq0 hqe F
      apply gaussZResidueK_of_wordPhase
        (sourceBoundaryMapK tame pro2 compat) F En l hl (scalarActionZmodTwo_triv _)
      · intro rho
        apply (Nat.card_ne_zero.mp ?_).2
        rw [hZcard_of_uniformPushed (uniformPushedHsimp_of_actionImage hqe) hqe
          (sourceBoundaryMapK tame pro2 compat) F En l hl hsimple hVne hnt rho]
        exact Nat.mul_ne_zero Nat.card_pos.ne' (Nat.pow_pos Nat.card_pos).ne'
      · intro rho v hfixed
        apply hfix_of_simple_nt (hsimple := hsimple) (hnt := hnt) ?_ v hfixed
        intro c0
        obtain ⟨g, hg⟩ := rho.1.2 c0
        exact ⟨g, (rho0_descData_rhoPrimeK
          (sourceBoundaryMapK tame pro2 compat) F En l hl rho g).trans hg⟩
      · exact S.unramified T Blk hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl hunram
  · exact fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl hram ↦ by
      let En := blockEnrichmentDK T Blk hE2 hq0 hqe F
      apply gaussZResidueK_of_wordPhase
        (sourceBoundaryMapK tame pro2 compat) F En l hl (scalarActionZmodTwo_triv _)
      · intro rho
        apply (Nat.card_ne_zero.mp ?_).2
        rw [hZcard_of_uniformPushed (uniformPushedHsimp_of_actionImage hqe) hqe
          (sourceBoundaryMapK tame pro2 compat) F En l hl hsimple hVne hnt rho]
        exact Nat.mul_ne_zero Nat.card_pos.ne' (Nat.pow_pos Nat.card_pos).ne'
      · intro rho v hfixed
        apply hfix_of_simple_nt (hsimple := hsimple) (hnt := hnt) ?_ v hfixed
        intro c0
        obtain ⟨g, hg⟩ := rho.1.2 c0
        exact ⟨g, (rho0_descData_rhoPrimeK
          (sourceBoundaryMapK tame pro2 compat) F En l hl rho g).trans hg⟩
      · exact S.ramified T Blk hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl hram

/-- End-to-end regression for the analytic layer: a word-phase supply now closes the
determinant residue and hence, together with action-image Stokes, all three L analytic leaves. -/
def analyticLeaves_of_wordPhaseSupply
    {h q : ℕ} (hqe : Even q) {P : ProfiniteGrp}
    (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (gamma h q) (Tq q))
    (pro2 : ContinuousMonoidHom (gamma h q) P)
    (compat : ∀ g : (gamma h q : Type), nuTq q (tame g) = nuP (pro2 g))
    (S : DeterminantWordPhaseSupply nuP tame pro2 compat) :
    StokesDualityCertificate (gamma h q) (2 * h + 1) q P nuP
        (standardNumerics (2 * h + 1))
        (scalarActionZmodTwo ((gamma h q : Type))) ∧
      ScalarHilbertCertificate (gamma h q) (2 * h + 1)
        (standardNumerics (2 * h + 1))
        (scalarActionZmodTwo ((gamma h q : Type))) ∧
      AffineDeterminantCertificate (gamma h q) (2 * h + 1) q P nuP
        (standardNumerics (2 * h + 1)) tame pro2 compat
        (scalarActionZmodTwo ((gamma h q : Type))) :=
  analyticLeaves_of_actionImage hqe nuP tame pro2 compat
    (affineDeterminantCertificate_of_wordPhaseSupply nuP tame pro2 compat S)

end

end GQ2.Dyadic.LSquare

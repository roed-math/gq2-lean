/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.SourceDataRN
import GQ2.Dyadic.Recursion.Prop89Close
import GQ2.Dyadic.Recursion.Induction

/-!
# Closed recursion with the degree-indexed R-stage coefficient

The frozen `ClosedRecursionK` and its consumers retain `RF.zR`.  This file supplies the
parallel corrected path whose sole type-level change is
`ClosedRecursionRN.eq136 : ... = zRN RF SN * ...`.  Equations (137)--(140) are unchanged.

At degree one, explicit mutually inverse conversions recover the frozen boxed system.  At
general degree, `prop_8_9_auxRN` consumes `RecursionInputsRN` directly and the comparison
solver cancels the common `zRN` coefficient without assuming it equals `RF.zR`.

This file stops at the first comparison consumer.  The next capstone step,
`ThmFourTwoN.rStage_laneN`, is private and is stated over `SourceDataN`; its Prop. 8.9 result
has type `ClosedRecursionK ...`, whereas `prop_8_9_of_sourcesRN` returns
`ClosedRecursionRN ... SN ...`.  Continuing to the public capstone therefore requires a
parallel strong-induction lane over `SourceDataRN`, not a coefficient cast.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight GQ2.SectionNine
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

variable {q n : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
  {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}

open scoped Classical in
/-- The corrected boxed system.  Only (136) differs from `ClosedRecursionK`. -/
structure ClosedRecursionRN {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
    {q n : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (SN : SourceNumerics n)
    (b : ContinuousMonoidHom Gamma ↑(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (mu : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT]
    (phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC)
    (cS mM vH : ℕ) : Prop where
  eq136 : (Nat.card RF.DR : ℤ) * exactImageCountK b F T
    = zRN RF SN * ∑ᶠ l : RF.DR,
        (2 * (mBK RF b F l : ℤ) - exactImageCountK b F RF.TB)
  eq137 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (zBCK RF b F l h : ℤ) = mBK RF b F l
      + ∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤},
          (mJOnK RF b F l h J : ℤ)
  eq138 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (J : Subgroup RF.YB)
      (hJ : Function.Surjective (RF.TB.piY.comp J.subtype)),
    cS * mJK RF b F l h J hJ
      = ∑ᶠ J' ∈ {J' : Subgroup (RF.scalarCover l h).cover |
          J'.map (RF.scalarCover l h).p = J},
          exactImageCountOnK b F ((RF.scalarCover l h).pullTarget RF.TB) J'
  eq139 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (¬∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
        N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N) →
      2 * zBCK RF b F l h = mM * exactImageCountK b F RF.TC
  eq140 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
        N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N) →
      2 * (Nat.card DT : ℤ) * zBCK RF b F l h
        = mu * ((vH : ℕ) * exactImageCountK b F RF.TC
            + G0 * ∑ᶠ zeta : DT,
                (2 * (nPhaseK RF b F (phase l h zeta) : ℤ)
                  - exactImageCountK b F RF.TC))

namespace ClosedRecursionRN

/-- Degree one forgets to the frozen boxed system definitionally at (136). -/
def toClosedRecursionKStandardOne {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
    {b : ContinuousMonoidHom Gamma ↑(boundarySubgroupQ q nuP)}
    {F : BoundaryFrameK q P H E} {mu : ℕ} {G0 : ℤ} {DT : Type} [Fintype DT]
    {phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC}
    {cS mM vH : ℕ}
    (C : ClosedRecursionRN RF (standardNumerics 1) b F mu G0 DT phase cS mM vH) :
    ClosedRecursionK RF b F mu G0 DT phase cS mM vH where
  eq136 := by simpa only [zRN_standard_one] using C.eq136
  eq137 := C.eq137
  eq138 := C.eq138
  eq139 := C.eq139
  eq140 := C.eq140

/-- Every frozen boxed system has its corrected degree-one companion. -/
def ofClosedRecursionKStandardOne {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
    {b : ContinuousMonoidHom Gamma ↑(boundarySubgroupQ q nuP)}
    {F : BoundaryFrameK q P H E} {mu : ℕ} {G0 : ℤ} {DT : Type} [Fintype DT]
    {phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC}
    {cS mM vH : ℕ}
    (C : ClosedRecursionK RF b F mu G0 DT phase cS mM vH) :
    ClosedRecursionRN RF (standardNumerics 1) b F mu G0 DT phase cS mM vH where
  eq136 := by simpa only [zRN_standard_one] using C.eq136
  eq137 := C.eq137
  eq138 := C.eq138
  eq139 := C.eq139
  eq140 := C.eq140

@[simp] theorem toClosedRecursionKStandardOne_ofClosedRecursionKStandardOne
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    {RF : RecursionFrame T Blk} {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
    {b : ContinuousMonoidHom Gamma ↑(boundarySubgroupQ q nuP)}
    {F : BoundaryFrameK q P H E} {mu : ℕ} {G0 : ℤ} {DT : Type} [Fintype DT]
    {phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC}
    {cS mM vH : ℕ} (C : ClosedRecursionK RF b F mu G0 DT phase cS mM vH) :
    (ofClosedRecursionKStandardOne C).toClosedRecursionKStandardOne = C := by
  cases C
  rfl

@[simp] theorem ofClosedRecursionKStandardOne_toClosedRecursionKStandardOne
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    {RF : RecursionFrame T Blk} {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
    {b : ContinuousMonoidHom Gamma ↑(boundarySubgroupQ q nuP)}
    {F : BoundaryFrameK q P H E} {mu : ℕ} {G0 : ℤ} {DT : Type} [Fintype DT]
    {phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC}
    {cS mM vH : ℕ}
    (C : ClosedRecursionRN RF (standardNumerics 1) b F mu G0 DT phase cS mM vH) :
    ofClosedRecursionKStandardOne C.toClosedRecursionKStandardOne = C := by
  cases C
  rfl

end ClosedRecursionRN

open scoped Classical in
/-- Corrected Prop. 8.9 assembly: no coefficient conversion is required. -/
theorem prop_8_9_auxRN {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
    [IsTopologicalGroup Gamma] [CompactSpace Gamma] [TotallyDisconnectedSpace Gamma]
    (hfg : ∃ s : Finset Gamma, (Subgroup.closure (s : Set Gamma)).topologicalClosure = ⊤)
    (SN : SourceNumerics n)
    (b : ContinuousMonoidHom Gamma ↑(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E)
    (cS : ℕ) (hscalar : Nat.card (ContinuousMonoidHom Gamma (Multiplicative (ZMod 2))) = cS)
    (hhead : Function.Surjective (fun gamma : Gamma => (F.frameMap (b gamma)).1))
    (mu : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT]
    (phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC)
    (mM vH : ℕ)
    (inp : RecursionInputsRN RF SN b F mu G0 DT phase mM vH) :
    ClosedRecursionRN RF SN b F mu G0 DT phase cS mM vH where
  eq136 := inp.stageR136
  eq137 := partition137_ofK RF hfg b F hhead
  eq138 := fun l h => lemma_8_3K hfg b F RF.TB (RF.scalarCover l h) cS hscalar
  eq139 := inp.half139
  eq140 := inp.phase140

/-! ## One-sided producer -/

section Producer

variable {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma] [IsTopologicalGroup Gamma]
  [CompactSpace Gamma] [TotallyDisconnectedSpace Gamma]
  [DistribMulAction Gamma (ZMod 2)] [ContinuousSMul Gamma (ZMod 2)]

open scoped Classical in
/-- The one-sided Prop. 8.9 producer with the corrected (136) coefficient. -/
theorem closedRecursionRN_of_source {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (SN : SourceNumerics n) (En : RF.Enrichment)
    (b : ContinuousMonoidHom Gamma ↑(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E)
    (l0 : RF.DR) (hl0 : l0 ≠ RF.zeroDR) [Fintype ↑(TCharC (En.radData l0 hl0))]
    (cS mM vH : ℕ) (tMult : ℕ → ℕ) (G0 : ℤ)
    (htriv : ∀ (gamma : Gamma) (m : ZMod 2), gamma • m = m)
    (hfg : ∃ s : Finset Gamma, (Subgroup.closure (s : Set Gamma)).topologicalClosure = ⊤)
    (hscalar : Nat.card (ContinuousMonoidHom Gamma (Multiplicative (ZMod 2))) = cS)
    (hH2 : Nat.card (H2 Gamma (ZMod 2)) = 2)
    (hhead : Function.Surjective (fun gamma : Gamma => (F.frameMap (b gamma)).1))
    (hstage : (Nat.card RF.DR : ℤ) * exactImageCountK b F T
      = zRN RF SN * ∑ᶠ l : RF.DR,
          (2 * (mBK RF b F l : ℤ) - exactImageCountK b F RF.TB))
    (hlem86 : ∀ {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
      (D : RadicalCoverData Bg), D.NoDescent →
      ∀ (rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M)), Function.Surjective rho →
        2 * Nat.card {f : MLifts D rho // f.Central} = Nat.card (MLifts D rho))
    (hMcount : ∀ rho : BoundaryLiftsK b F RF.TC, Nat.card (LiftsOverK RF b F rho) = mM)
    (htcoc : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (rho : BoundaryLiftsK b F RF.TC),
      Nat.card (TCocycle (En.radData l h) (rhoPrimeK RF b F (En.radData l h) rfl rho))
        = tMult (Nat.card (Additive ↑(En.radData l h).T))
          * Nat.card (fixedPts (RF.YB ⧸ (En.radData l h).M)
              (ElemDual (Additive ↑(En.radData l h).T))))
    (hsep : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (Dsc : Descent (En.radData l h))
      (rho : BoundaryLiftsK b F RF.TC)
      (c : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl rho)),
      (∀ chi : ↑(TCharC (En.radData l h)),
        betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) chi c = 0) →
        TLiftable (descSigma_spec En l h Dsc) c)
    (hpartial : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (Dsc : Descent (En.radData l h))
      (rho : BoundaryLiftsK b F RF.TC) (chi : ↑(TCharC (En.radData l h))), chi ≠ 0 →
      ∃ c : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl rho),
        betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) chi c
          ≠ betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) chi
              (0 : VCocycle (En.descData l h)
                (rhoPrimeK RF b F (En.radData l h) rfl rho)))
    (hZcard : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (rho : BoundaryLiftsK b F RF.TC),
      Nat.card (VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl rho))
        = Nat.card En.Vmod * vH)
    (hGaussZ : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR), GaussZResidueK b F En l h G0) :
    ClosedRecursionRN RF SN b F (Nat.card En.Vmod * muZeroN tMult En l0 hl0) G0
      ↑(TCharC (En.radData l0 hl0)) (phaseFamily En l0 hl0) cS mM vH := by
  classical
  refine prop_8_9_auxRN RF hfg SN b F cS hscalar hhead _ _ _ _ _ _ ?_
  refine ⟨hstage, fun l h hedge => ?_, fun l h hN => ?_⟩
  · exact half139_of_leavesK RF b F En mM hfg hlem86 hMcount l h hedge
  · have h140 := phase140_from_residuesK b F En l h (descentOf En l h hN)
      htriv hfg hH2 (muZeroN tMult En l0 hl0) vH G0
      (fun rho => (tcocycle_cardK_l_indep RF b F En l h l0 hl0 rho).trans (htcoc l0 hl0 rho))
      (fun rho => hsep l h (descentOf En l h hN) rho)
      (fun rho => hpartial l h (descentOf En l h hN) rho)
      (fun rho => hZcard l h rho)
      (hGaussZ l h)
    simp only [phaseFamily_pos En l0 hl0 l h hN]
    exact h140

open scoped Classical in
omit [DistribMulAction Gamma (ZMod 2)] [ContinuousSMul Gamma (ZMod 2)] in
/-- Degenerate corrected producer: with no nonzero scalar character only (136) is live. -/
theorem closedRecursionRN_of_source_degenerate {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (SN : SourceNumerics n)
    (b : ContinuousMonoidHom Gamma ↑(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (cS mM vH mu : ℕ) (G0 : ℤ)
    (DT : Type) [Fintype DT]
    (phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC)
    (hfg : ∃ s : Finset Gamma, (Subgroup.closure (s : Set Gamma)).topologicalClosure = ⊤)
    (hscalar : Nat.card (ContinuousMonoidHom Gamma (Multiplicative (ZMod 2))) = cS)
    (hhead : Function.Surjective (fun gamma : Gamma => (F.frameMap (b gamma)).1))
    (hex : ¬∃ l : RF.DR, l ≠ RF.zeroDR)
    (hstage : (Nat.card RF.DR : ℤ) * exactImageCountK b F T
      = zRN RF SN * ∑ᶠ l : RF.DR,
          (2 * (mBK RF b F l : ℤ) - exactImageCountK b F RF.TB)) :
    ClosedRecursionRN RF SN b F mu G0 DT phase cS mM vH :=
  prop_8_9_auxRN RF hfg SN b F cS hscalar hhead _ _ _ _ _ _
    ⟨hstage, fun l h => absurd ⟨l, h⟩ hex, fun l h => absurd ⟨l, h⟩ hex⟩

end Producer

/-! ## Two corrected sources at shared closed data -/

section SourcePackaging

variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]

/-- Package two `SourceDataRN` records into corrected closed recursions over the same reference
edge and the same numerical data. -/
theorem prop_8_9_of_sourcesRN (S1 S2 : SourceDataRN n q P hP nuP SN)
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    (hE2 : ∀ e : E, e ^ 2 = 1) (En : (blockFrameImpl T Blk hE2).Enrichment)
    (F : BoundaryFrameK q P H E)
    (hhead1 : Function.Surjective (fun gamma : S1.Γ => (F.frameMap (S1.b gamma)).1))
    (hhead2 : Function.Surjective (fun gamma : S2.Γ => (F.frameMap (S2.b gamma)).1))
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : (blockFrameImpl T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : (blockFrameImpl T Blk hE2).YC) (v : En.Vmod), g • v ≠ v)
    (G0 : ℤ)
    (hGaussZ1 : letI := S1.smulZmod2
      ∀ (l : (blockFrameImpl T Blk hE2).DR) (h : l ≠ (blockFrameImpl T Blk hE2).zeroDR),
        GaussZResidueK S1.b F En l h G0)
    (hGaussZ2 : letI := S2.smulZmod2
      ∀ (l : (blockFrameImpl T Blk hE2).DR) (h : l ≠ (blockFrameImpl T Blk hE2).zeroDR),
        GaussZResidueK S2.b F En l h G0) :
    ∃ (mu : ℕ) (G0' : ℤ) (DT : Type) (_ : Fintype DT)
      (phase : (l : (blockFrameImpl T Blk hE2).DR) →
        l ≠ (blockFrameImpl T Blk hE2).zeroDR → DT →
          CentralCover (blockFrameImpl T Blk hE2).YC),
      0 < Nat.card DT ∧
        ClosedRecursionRN (blockFrameImpl T Blk hE2) SN S1.b F mu G0' DT phase
            SN.homScalar (SN.mMult (Nat.card ↑(blockFrameImpl T Blk hE2).MB))
            (SN.h1Mult (Nat.card En.Vmod)) ∧
        ClosedRecursionRN (blockFrameImpl T Blk hE2) SN S2.b F mu G0' DT phase
            SN.homScalar (SN.mMult (Nat.card ↑(blockFrameImpl T Blk hE2).MB))
            (SN.h1Mult (Nat.card En.Vmod)) := by
  classical
  by_cases hex : ∃ l : (blockFrameImpl T Blk hE2).DR,
      l ≠ (blockFrameImpl T Blk hE2).zeroDR
  · obtain ⟨l0, hl0⟩ := hex
    haveI : Fintype ↑(TCharC (En.radData l0 hl0)) := Fintype.ofFinite _
    have hcr1 : ClosedRecursionRN (blockFrameImpl T Blk hE2) SN S1.b F
        (Nat.card En.Vmod * muZeroN SN.tMult En l0 hl0) G0
        ↑(TCharC (En.radData l0 hl0)) (phaseFamily En l0 hl0) SN.homScalar
        (SN.mMult (Nat.card ↑(blockFrameImpl T Blk hE2).MB))
        (SN.h1Mult (Nat.card En.Vmod)) := by
      letI := S1.smulZmod2
      letI := S1.contSMulZmod2
      exact closedRecursionRN_of_source (blockFrameImpl T Blk hE2) SN En S1.b F l0 hl0
        _ _ _ _ G0 S1.htriv S1.tfg S1.homCard S1.cardH2 hhead1
        (S1.stageR136 hE2 hRK hR2 S1.b F)
        (fun D hedge rho hrho => S1.lem86 D hedge rho hrho)
        (S1.liftsOver_card _ S1.b F)
        (fun l h rho => S1.tcocycle_card S1.b F En l h rho)
        (fun l h Dsc rho c hc => S1.hsep S1.b F En l h Dsc rho c hc)
        (fun l h Dsc rho chi hchi => S1.hpartial S1.b F En l h Dsc rho chi hchi)
        (fun l h rho => S1.hZcard S1.b F En l h hsimple hVne hnt rho)
        hGaussZ1
    have hcr2 : ClosedRecursionRN (blockFrameImpl T Blk hE2) SN S2.b F
        (Nat.card En.Vmod * muZeroN SN.tMult En l0 hl0) G0
        ↑(TCharC (En.radData l0 hl0)) (phaseFamily En l0 hl0) SN.homScalar
        (SN.mMult (Nat.card ↑(blockFrameImpl T Blk hE2).MB))
        (SN.h1Mult (Nat.card En.Vmod)) := by
      letI := S2.smulZmod2
      letI := S2.contSMulZmod2
      exact closedRecursionRN_of_source (blockFrameImpl T Blk hE2) SN En S2.b F l0 hl0
        _ _ _ _ G0 S2.htriv S2.tfg S2.homCard S2.cardH2 hhead2
        (S2.stageR136 hE2 hRK hR2 S2.b F)
        (fun D hedge rho hrho => S2.lem86 D hedge rho hrho)
        (S2.liftsOver_card _ S2.b F)
        (fun l h rho => S2.tcocycle_card S2.b F En l h rho)
        (fun l h Dsc rho c hc => S2.hsep S2.b F En l h Dsc rho c hc)
        (fun l h Dsc rho chi hchi => S2.hpartial S2.b F En l h Dsc rho chi hchi)
        (fun l h rho => S2.hZcard S2.b F En l h hsimple hVne hnt rho)
        hGaussZ2
    exact ⟨_, G0, _, inferInstance, phaseFamily En l0 hl0, card_TCharC_pos En l0 hl0,
      hcr1, hcr2⟩
  · exact ⟨1, G0, PUnit, inferInstance, fun l h _ => absurd ⟨l, h⟩ hex, by simp,
      closedRecursionRN_of_source_degenerate (blockFrameImpl T Blk hE2) SN S1.b F
        _ _ _ _ G0 _ _ S1.tfg S1.homCard hhead1 hex
        (S1.stageR136 hE2 hRK hR2 S1.b F),
      closedRecursionRN_of_source_degenerate (blockFrameImpl T Blk hE2) SN S2.b F
        _ _ _ _ G0 _ _ S2.tfg S2.homCard hhead2 hex
        (S2.stageR136 hE2 hRK hR2 S2.b F)⟩

end SourcePackaging

/-! ## First comparison consumer -/

/-- The closed-recursion solver with the corrected coefficient.  The proof is the frozen
solver until its final line: there the common factor is `zRN RF SN`, and equality of the two
right-hand sides follows from the already-proved equality of the `mB` summands.  No
coefficient nonvanishing or equality with `RF.zR` is used. -/
theorem count_eq_of_closedRecursionRN {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    {Gamma1 : Type} [Group Gamma1] [TopologicalSpace Gamma1]
    {Gamma2 : Type} [Group Gamma2] [TopologicalSpace Gamma2]
    (SN : SourceNumerics n)
    (b1 : ContinuousMonoidHom Gamma1 ↑(boundarySubgroupQ q nuP))
    (b2 : ContinuousMonoidHom Gamma2 ↑(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (mu : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT]
    (phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC)
    (cS mM vH : ℕ) (hcS : 0 < cS)
    (h1 : ClosedRecursionRN RF SN b1 F mu G0 DT phase cS mM vH)
    (h2 : ClosedRecursionRN RF SN b2 F mu G0 DT phase cS mM vH)
    (hDT : Nat.card DT ≠ 0)
    (hTB : exactImageCountK b1 F RF.TB = exactImageCountK b2 F RF.TB)
    (hTC : exactImageCountK b1 F RF.TC = exactImageCountK b2 F RF.TC)
    (hpull : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (J' : Subgroup (RF.scalarCover l h).cover),
      J'.map (RF.scalarCover l h).p ≠ ⊤ → (J'.map (RF.scalarCover l h).p).map RF.piBC = ⊤ →
      exactImageCountOnK b1 F ((RF.scalarCover l h).pullTarget RF.TB) J'
        = exactImageCountOnK b2 F ((RF.scalarCover l h).pullTarget RF.TB) J')
    (hphase : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (zeta : DT),
      nPhaseK RF b1 F (phase l h zeta) = nPhaseK RF b2 F (phase l h zeta)) :
    exactImageCountK b1 F T = exactImageCountK b2 F T := by
  classical
  have hmJOn : ∀ (l : RF.DR) (hl : l ≠ RF.zeroDR) (J : Subgroup RF.YB),
      J ≠ ⊤ → J.map RF.piBC = ⊤ →
      mJOnK RF b1 F l hl J = mJOnK RF b2 F l hl J := by
    intro l hl J hJne hJC
    simp only [mJOnK]
    by_cases hJ : Function.Surjective (RF.TB.piY.comp J.subtype)
    · rw [dif_pos hJ, dif_pos hJ]
      have hcs : cS * mJK RF b1 F l hl J hJ = cS * mJK RF b2 F l hl J hJ := by
        rw [h1.eq138 l hl J hJ, h2.eq138 l hl J hJ]
        refine finsum_mem_congr rfl (fun J' hJ' => ?_)
        have hJ'' : J'.map (RF.scalarCover l hl).p = J := hJ'
        exact hpull l hl J' (by rw [hJ'']; exact hJne) (by rw [hJ'']; exact hJC)
      exact Nat.eq_of_mul_eq_mul_left hcS hcs
    · rw [dif_neg hJ, dif_neg hJ]
  have hzBC : ∀ (l : RF.DR) (hl : l ≠ RF.zeroDR),
      zBCK RF b1 F l hl = zBCK RF b2 F l hl := by
    intro l hl
    by_cases hdesc : ∃ N : Subgroup (RF.scalarCover l hl).cover, N.Normal ∧
        N.map (RF.scalarCover l hl).p = RF.TBsub ∧ (RF.scalarCover l hl).z ∉ N
    · have hns : (∑ᶠ zeta : DT,
            (2 * (nPhaseK RF b1 F (phase l hl zeta) : ℤ)
              - (exactImageCountK b1 F RF.TC : ℤ)))
          = ∑ᶠ zeta : DT,
            (2 * (nPhaseK RF b2 F (phase l hl zeta) : ℤ)
              - (exactImageCountK b2 F RF.TC : ℤ)) :=
        finsum_congr (fun zeta => by rw [hphase l hl zeta, hTC])
      have hcancel : 2 * (Nat.card DT : ℤ) * (zBCK RF b1 F l hl : ℤ)
          = 2 * (Nat.card DT : ℤ) * (zBCK RF b2 F l hl : ℤ) := by
        rw [h1.eq140 l hl hdesc, h2.eq140 l hl hdesc, hns, hTC]
      have hne : (2 : ℤ) * (Nat.card DT : ℤ) ≠ 0 :=
        mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr hDT)
      exact_mod_cast mul_left_cancel₀ hne hcancel
    · have hcancel : 2 * zBCK RF b1 F l hl = 2 * zBCK RF b2 F l hl := by
        rw [h1.eq139 l hl hdesc, h2.eq139 l hl hdesc, hTC]
      omega
  have hmB : ∀ l : RF.DR, mBK RF b1 F l = mBK RF b2 F l := by
    intro l
    by_cases hl : l = RF.zeroDR
    · subst hl
      simp only [mBK]
      exact hTB
    · have hsum : (∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤},
            (mJOnK RF b1 F l hl J : ℤ))
          = ∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤},
            (mJOnK RF b2 F l hl J : ℤ) :=
        finsum_mem_congr rfl (fun J hJmem => by
          obtain ⟨hJne, hJC⟩ := hJmem
          rw [hmJOn l hl J hJne hJC])
      have hz : (zBCK RF b1 F l hl : ℤ) = (zBCK RF b2 F l hl : ℤ) := by
        rw [hzBC l hl]
      have hcast : (mBK RF b1 F l : ℤ) = (mBK RF b2 F l : ℤ) := by
        have h137 : (mBK RF b1 F l : ℤ)
            + ∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤},
                (mJOnK RF b1 F l hl J : ℤ)
            = (mBK RF b2 F l : ℤ)
            + ∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤},
                (mJOnK RF b2 F l hl J : ℤ) := by
          rw [← h1.eq137 l hl, ← h2.eq137 l hl, hz]
        rw [hsum] at h137
        exact add_right_cancel h137
      exact_mod_cast hcast
  have hDRne : (Nat.card RF.DR : ℤ) ≠ 0 := by
    have h : Nat.card RF.DR ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨RF.zeroDR⟩, inferInstance⟩
    exact_mod_cast h
  have hrhs : (zRN RF SN : ℤ) * ∑ᶠ l : RF.DR,
        (2 * (mBK RF b1 F l : ℤ) - exactImageCountK b1 F RF.TB)
      = (zRN RF SN : ℤ) * ∑ᶠ l : RF.DR,
        (2 * (mBK RF b2 F l : ℤ) - exactImageCountK b2 F RF.TB) := by
    congr 1
    exact finsum_congr (fun l => by rw [hmB l, hTB])
  have hcast : (exactImageCountK b1 F T : ℤ) = (exactImageCountK b2 F T : ℤ) := by
    refine mul_left_cancel₀ hDRne ?_
    rw [h1.eq136, h2.eq136, hrhs]
  exact_mod_cast hcast

/-- At degree one the corrected comparison theorem is obtained through the frozen solver after
the exact boxed-system conversion.  This pins the parallel path to the historical API. -/
theorem count_eq_of_closedRecursionRN_standard_one {Y : Type} [Group Y]
    [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    {Gamma1 : Type} [Group Gamma1] [TopologicalSpace Gamma1]
    {Gamma2 : Type} [Group Gamma2] [TopologicalSpace Gamma2]
    (b1 : ContinuousMonoidHom Gamma1 ↑(boundarySubgroupQ q nuP))
    (b2 : ContinuousMonoidHom Gamma2 ↑(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (mu : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT]
    (phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC)
    (cS mM vH : ℕ) (hcS : 0 < cS)
    (h1 : ClosedRecursionRN RF (standardNumerics 1) b1 F mu G0 DT phase cS mM vH)
    (h2 : ClosedRecursionRN RF (standardNumerics 1) b2 F mu G0 DT phase cS mM vH)
    (hDT : Nat.card DT ≠ 0)
    (hTB : exactImageCountK b1 F RF.TB = exactImageCountK b2 F RF.TB)
    (hTC : exactImageCountK b1 F RF.TC = exactImageCountK b2 F RF.TC)
    (hpull : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (J' : Subgroup (RF.scalarCover l h).cover),
      J'.map (RF.scalarCover l h).p ≠ ⊤ → (J'.map (RF.scalarCover l h).p).map RF.piBC = ⊤ →
      exactImageCountOnK b1 F ((RF.scalarCover l h).pullTarget RF.TB) J'
        = exactImageCountOnK b2 F ((RF.scalarCover l h).pullTarget RF.TB) J')
    (hphase : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (zeta : DT),
      nPhaseK RF b1 F (phase l h zeta) = nPhaseK RF b2 F (phase l h zeta)) :
    exactImageCountK b1 F T = exactImageCountK b2 F T :=
  count_eq_of_closedRecursionK RF b1 b2 F mu G0 DT phase cS mM vH hcS
    h1.toClosedRecursionKStandardOne h2.toClosedRecursionKStandardOne hDT hTB hTC hpull hphase

end GQ2.Dyadic

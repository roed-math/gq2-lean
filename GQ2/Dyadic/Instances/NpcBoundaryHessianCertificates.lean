/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcHessianCertificates
import GQ2.Dyadic.Instances.NpcBoundaryFinal
import GQ2.Dyadic.Instances.WordPhaseHeadProfiles

/-!
# Branch-free original Npc Hessian records at actual boundary lifts

The actual source is the same displayed Npc word and the records retain its full
offset phase, including the head-dependent diagonal. All projected-head and
resolved sigma-power hypotheses are discharged from the existing boundary data.
No ramification-sector input, inverse-Lc premise, x2-zero restriction, or assumed
phase comparison survives. The finite dimension and cardinality are derived.

Public word-independent projected-head/profile lemmas avoid duplicating the old
two boundary branches. The only copied private proof is the exact resolved-power
fixed-point-free helper; it is kept private and uses the same action-image argument.
No old API is altered. The existential diagonal is deliberate: the genuine
unramified and ramified diagonals are not identified with each other or with qbar.
-/

namespace GQ2.Dyadic.Instances.NpcBoundaryHessianCertificates
noncomputable section
open GQ2 GQ2.SectionEight GQ2.SectionSix
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic Count Certificates Words Words.Npc NProcyclic NProcyclicUnram
open RowActionImage LSquare
open Instances.WordPhase Instances.WordPhaseModel Instances.NpcWordPhaseModel
open Instances.NpcHessianCertificates Instances.WordPhaseWallHandleCertificates
open Instances.WordPhaseBoundaryMarking Instances.WordPhaseHeadProfiles

private theorem unramified_concreteHead_powers_fixedPointFree
    {alpha r h q : ℕ} {d : EtaData}
    {C V : Type} [Group C] [Finite C] [TopologicalSpace C] [DiscreteTopology C]
    [AddCommGroup V] [Finite V] [TopologicalSpace V] [DiscreteTopology V]
    [DistribMulAction C V]
    [DistribMulAction
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) V]
    [ContinuousSMul
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) V]
    (phi : ContinuousMonoidHom
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) C)
    (hcompat : ∀
      (gamma : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type))
      (v : V), gamma • v = phi gamma • v)
    (hV2 : ∀ v : V, v + v = 0)
    (hsimple : IsSimpleModTwo
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) V)
    (htau : ∀ v : V,
      gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau • v = v)
    (hsigmaFpf : ∀ v : V,
      gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma • v = v → v = 0) :
    let L := SectionSix.SemiProd C V
    let E := npcResolver (4 * Monoid.exponent L) d
    let s := phi (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)
    (∀ v : V, ((s ^ E d.toZhat)⁻¹ : C) • v = v → v = 0) ∧
      (∀ v : V, ((s ^ ((2 : ℤ) ^ r))⁻¹ : C) • v = v → v = 0) := by
  letI : ContinuousSMul C V := ⟨continuous_of_discreteTopology⟩
  let L := SectionSix.SemiProd C V
  letI : Finite L := inferInstanceAs (Finite (V × C))
  let N := 4 * Monoid.exponent L
  let E := npcResolver N d
  let gammaSigma := gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma
  let s := phi gammaSigma
  dsimp only
  let t := actionImageMarking (2 + 2 * h) q (npcW alpha r h d) V
  have hsigmaImageFpf : ∀ v : V, t.σ • v = v → v = 0 := by
    intro v hv
    apply hsigmaFpf v
    change actionImageHom (2 + 2 * h) q (npcW alpha r h d) V gammaSigma • v = v at hv
    exact hv
  have hsd : Function.Surjective (sdSnd : L →* C) := by
    intro x
    exact ⟨((0, x) : L), rfl⟩
  have hN : N ≠ 0 := fourMulExponent_ne_zero_and_even L |>.1
  have hunder : ((t.σ : ActionImage (2 + 2 * h) q
      (npcW alpha r h d) V) : Multiplicative (AddAut V)) =
      finiteActionHom (G := C) (M := V) s := by
    ext v
    exact hcompat gammaSigma v
  have hord : orderOf t.σ ∣ N := by
    rw [← orderOf_submonoid t.σ, hunder]
    exact (orderOf_map_dvd
      (finiteActionHom (G := C) (M := V)).toMonoidHom s).trans
      ((Monoid.order_dvd_exponent s).trans
        ((MonoidHom.exponent_dvd hsd).trans ⟨4, by ring⟩))
  have hAeq : t.σ ^ E d.toZhat = t.σ :=
    actionImage_unramified_sigma_etaPow hV2 hsimple htau d hN hord
  have hBfpf : ∀ v : V, (t.σ ^ ((2 : ℤ) ^ r)) • v = v → v = 0 :=
    actionImage_unramified_sigmaPow_fixedPointFree
      hV2 hsimple htau hsigmaImageFpf r
  have hsourceAction : ∀ (z : ℤ) (v : V),
      (s ^ z) • v = (t.σ ^ z) • v := by
    intro z v
    calc
      (s ^ z) • v = finiteActionHom (G := C) (M := V) (s ^ z) • v := rfl
      _ = (finiteActionHom (G := C) (M := V) s ^ z) • v := by rw [map_zpow]
      _ = ((t.σ : ActionImage (2 + 2 * h) q
          (npcW alpha r h d) V) : Multiplicative (AddAut V)) ^ z • v := by rw [hunder]
      _ = (t.σ ^ z) • v := rfl
  constructor
  · intro v hv
    apply hsigmaImageFpf v
    have hv' : (t.σ ^ E d.toZhat)⁻¹ • v = v := by
      calc
        (t.σ ^ E d.toZhat)⁻¹ • v = t.σ ^ (-E d.toZhat) • v := by rw [zpow_neg]
        _ = s ^ (-E d.toZhat) • v := (hsourceAction _ v).symm
        _ = (s ^ E d.toZhat)⁻¹ • v := by rw [zpow_neg]
        _ = v := hv
    rw [hAeq] at hv'
    exact (inv_smul_eq_iff.mp hv').symm
  · intro v hv
    apply hBfpf v
    have hv' : (t.σ ^ ((2 : ℤ) ^ r))⁻¹ • v = v := by
      calc
        (t.σ ^ ((2 : ℤ) ^ r))⁻¹ • v = t.σ ^ (-((2 : ℤ) ^ r)) • v := by
          rw [zpow_neg]
        _ = s ^ (-((2 : ℤ) ^ r)) • v := (hsourceAction _ v).symm
        _ = (s ^ ((2 : ℤ) ^ r))⁻¹ • v := by rw [zpow_neg]
        _ = v := hv
    exact (inv_smul_eq_iff.mp hv').symm


/-- Original full-offset Hessian records at every actual simple nontrivial
boundary lift, with no ramification-sector input or additional analytic premise.
The diagonal is retained existentially because the two genuine diagonals differ. -/
theorem npcBoundaryHessian
    {alpha r h q : ℕ} {d : EtaData}
    (hsimp : UniformHsimp alpha r h q d) (halpha : 2 ≤ alpha)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e^2=1) (hq0 : q≠0) (hqe : Even q)
    (F : BoundaryFrameK q P H E)
    (tame : ContinuousMonoidHom (displayedGamma alpha r h q d) (Tq q))
    (pro2 : ContinuousMonoidHom (displayedGamma alpha r h q d) P)
    (compat : ∀ g, nuTq q (tame g)=nuP (pro2 g))
    (htameSigma : tame (gammaGen (2+2*h) q (npcW alpha r h d) .sigma)=tqSigma q)
    (htameTau : tame (gammaGen (2+2*h) q (npcW alpha r h d) .tau)=tqTau q)
    (htameWild : ∀ i, tame (gammaGen (2+2*h) q (npcW alpha r h d) (.wild i))=1)
    (hsimple : ∀ W : AddSubgroup (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod,
      (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) →
        W=⊥ ∨ W=⊤)
    (hVne : ∃ v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod, v≠0)
    (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
      (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g•v≠v)
    (l : (SectionNine.blockFrame T Blk hE2).DR)
    (hl : l≠(SectionNine.blockFrame T Blk hE2).zeroDR)
    (rho : BoundaryLiftsK (sourceBoundaryMapK tame pro2 compat) F
      (SectionNine.blockFrame T Blk hE2).TC) :
    let DD := (blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl
    let rhoN := rhoPrimeK (SectionNine.blockFrame T Blk hE2)
      (sourceBoundaryMapK tame pro2 compat) F
      ((blockEnrichmentDK T Blk hE2 hq0 hqe F).radData l hl) rfl rho
    letI := scalarActionZmodTwo
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    ∃ d0 : DD.Vmod → ZMod 2,
      Nonempty (SourceWallHessian DD rhoN (scalarActionZmodTwo_triv _) d0 h) := by
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := SectionNine.headAct T Blk
  letI := SectionNine.hvAct T Blk
  classical
  let b := sourceBoundaryMapK tame pro2 compat
  let En := blockEnrichmentDK T Blk hE2 hq0 hqe F
  let DD := En.descData l hl
  have hl' : l.1≠Blk.frattiniK := fun heq ↦ hl (Subtype.ext heq)
  let rhoN := rhoPrimeK (SectionNine.blockFrame T Blk hE2) b F (En.radData l hl) rfl rho
  letI : TopologicalSpace DD.C0 :=
    (inferInstance : TopologicalSpace (SectionNine.blockFrame T Blk hE2).YC)
  letI : DiscreteTopology DD.C0 :=
    (inferInstance : DiscreteTopology (SectionNine.blockFrame T Blk hE2).YC)
  letI : TopologicalSpace DD.Vmod := ⊥
  letI : DiscreteTopology DD.Vmod := ⟨rfl⟩
  letI : DistribMulAction (SectionNine.blockFrame T Blk hE2).YC DD.Vmod := blockActV Blk
  letI : DistribMulAction (SectionNine.HVq T Blk) DD.Vmod := SectionNine.hvAct T Blk
  letI : DistribMulAction
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  letI : DistribMulAction
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod :=
    DistribMulAction.compHom DD.Vmod rho.1.1.toMonoidHom
  haveI : ContinuousSMul
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod := by
    constructor
    have hfac :
        (fun p : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) × DD.Vmod ↦
          p.1•p.2) =
        (fun p : (SectionNine.blockFrame T Blk hE2).YC × DD.Vmod ↦ p.1•p.2) ∘
          (fun p ↦ (rho.1.1 p.1,p.2)) := by funext p; rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((rho.1.1.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hround : ∀ g : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type),
      rho0 DD rhoN g=rho.1.1 g :=
    rho0_descData_rhoPrimeK b F En l hl rho
  have hcompat : ∀ (g : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type))
      (v : DD.Vmod), g•v=rho0 DD rhoN g•v := by
    intro g v
    exact congrArg (fun c : (SectionNine.blockFrame T Blk hE2).YC ↦ c•v) (hround g).symm
  have hsimpleGamma : IsSimpleModTwo
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod := by
    obtain ⟨v,hv⟩ := hVne
    refine ⟨nontrivial_of_ne v 0 hv, ?_⟩
    intro W hW
    apply hsimple W
    intro c w hw
    obtain ⟨gamma,rfl⟩ := rho.1.2 c
    exact hW gamma w hw
  have hmark := projectedHead_marking T Blk hE2 hq0 hqe F tame pro2 compat l hl rho
    (gammaGen (2+2*h) q (npcW alpha r h d)) htameSigma htameTau htameWild
  have hsigmaHead : SectionNine.blockProjF T Blk
      (rho0 DD rhoN (gammaGen (2+2*h) q (npcW alpha r h d) .sigma))=hvSigmaK T Blk F :=
    hmark.1
  have htauHead : SectionNine.blockProjF T Blk
      (rho0 DD rhoN (gammaGen (2+2*h) q (npcW alpha r h d) .tau))=hvTauK T Blk F :=
    hmark.2.1
  have hwildHead : ∀ i, SectionNine.blockProjF T Blk
      (rho0 DD rhoN (gammaGen (2+2*h) q (npcW alpha r h d) (.wild i)))=1 := hmark.2.2
  have hwildTwo : IsWildTwo (wildAlphabet (2+2*h))
      (fun i ↦ Count.rho0Continuous DD rhoN (gammaGen (2+2*h) q (npcW alpha r h d) i)) :=
    isWildTwo_of_gammaGen (Count.rho0Continuous DD rhoN)
      (rho0Continuous_surjective DD rhoN
        (rhoPrimeK_surjective (SectionNine.blockFrame T Blk hE2) b F
          (En.radData l hl) rfl rho)) (fun _ ↦ rfl)
  have hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc•v=SectionNine.blockProjF T Blk cc•v :=
    SectionNine.blockProjF_compat T Blk
  have hblockPiCH : Function.Surjective (SectionNine.blockPiCH T Blk) := by
    intro c
    obtain ⟨y,hy⟩ := T.piY_surjective c
    exact ⟨QuotientGroup.mk' Blk.K y,hy⟩
  have hblockProj : Function.Surjective (SectionNine.blockProjF T Blk) :=
    (QuotientGroup.mk'_surjective _).comp hblockPiCH
  have hsemi : Function.Surjective (semiProdProjHom (C' := DD.C0) (V := DD.Vmod)
      (SectionNine.blockProjF T Blk) hpi) := by
    intro z
    obtain ⟨c,hc⟩ := hblockProj z.2
    exact ⟨(z.1,c),Prod.ext rfl hc⟩
  have hcardH2 : Nat.card
      (H2 ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2))=2 :=
    cardH2_of_uniformPushed (alpha := alpha) (r := r) (h := h) (q := q) (d := d)
      hsimp (by omega) hqe
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  by_cases hunram : ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P),
      F.alpha (tqTau q)•v=v
  · have htauOne : SectionNine.blockProjF T Blk
        (rho0 DD rhoN (gammaGen (2+2*h) q (npcW alpha r h d) .tau))=1 :=
      htauHead.trans (head_cyclic_of_unramified T Blk F hunram).1
    have hsigmaFpf : ∀ v : DD.Vmod, SectionNine.blockProjF T Blk
        (rho0 DD rhoN (gammaGen (2+2*h) q (npcW alpha r h d) .sigma))•v=v → v=0 := by
      intro v hv
      apply head_sigma_fixedPointFree T Blk hE2 hq0 hqe F hnt hunram v
      rwa [hsigmaHead] at hv
    have htauAct : ∀ v : DD.Vmod,
        gammaGen (2+2*h) q (npcW alpha r h d) .tau • v=v := by
      intro v
      rw [hcompat, hpi, htauOne, one_smul]
    have hsigmaAct : ∀ v : DD.Vmod,
        gammaGen (2+2*h) q (npcW alpha r h d) .sigma • v=v → v=0 := by
      intro v hv
      apply hsigmaFpf v
      rwa [hcompat, hpi] at hv
    obtain ⟨hgfpf,hufpf⟩ := unramified_concreteHead_powers_fixedPointFree
      (Count.rho0Continuous DD rhoN) hcompat (Vmod_exp2 DD) hsimpleGamma htauAct hsigmaAct
    exact ⟨_, ⟨npcUnramifiedHeadHessian rhoN
      (blockDatHVK T Blk hq0 hqe F l hl') (blockDatHV_specK T Blk hq0 hqe F l hl')
      (SectionNine.blockProjF T Blk) hpi (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      hcompat (Vmod_exp2 DD) hwildTwo halpha hqe hcardH2 htauOne hwildHead
      hsigmaFpf hgfpf hufpf⟩⟩
  · have hram : ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P),
        F.alpha (tqTau q)•v≠v := by simpa only [not_forall] using hunram
    have hprof := head_tau_ramified_profile T Blk hq0 hqe F hram
    have htauOdd : Odd (orderOf (SectionNine.blockProjF T Blk
        (rho0 DD rhoN (gammaGen (2+2*h) q (npcW alpha r h d) .tau)))) := by
      rw [htauHead]
      exact hprof.1
    have htauFpf : ∀ v : DD.Vmod, SectionNine.blockProjF T Blk
        (rho0 DD rhoN (gammaGen (2+2*h) q (npcW alpha r h d) .tau))•v=v → v=0 := by
      intro v hv
      rw [htauHead] at hv
      exact hprof.2.2 v hv
    exact ⟨_, nonempty_npcRamifiedHeadHessian rhoN
      (blockDatHVK T Blk hq0 hqe F l hl') (blockDatHV_specK T Blk hq0 hqe F l hl')
      (SectionNine.blockProjF T Blk) hpi (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      hsemi hcompat (Vmod_exp2 DD) hwildTwo halpha hqe hcardH2 hwildHead htauOdd htauFpf⟩

#print axioms npcBoundaryHessian

end
end GQ2.Dyadic.Instances.NpcBoundaryHessianCertificates

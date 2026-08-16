/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcRamifiedComparison
import GQ2.Dyadic.Instances.NpcUnramifiedComparison
import GQ2.Dyadic.Instances.NpcUnramifiedDiagonal

/-!
# Final procyclic-N boundary supply

This file joins the faithful unramified and ramified projected-head comparisons at their
common twisted plus-form endpoint.  The simple, nontrivial boundary coefficient rules out the
separate scalar unramified branch, so the resulting supply is branch-free without strengthening
`wPnpcPhaseModel` beyond its intended comparison-only interface.

Every selected `NpcDisplayFor` can therefore supply the uniform row residue downstream.  No
quadratic, resolver, or Gauss premise survives in the public boundary supply.
-/

namespace GQ2.Dyadic.Instances.NpcBoundaryFinal

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.Words.Npc
open GQ2.Dyadic.Certificates GQ2.QuadraticFp2
open GQ2.Dyadic.NProcyclic GQ2.Dyadic.NProcyclicUnram
open GQ2.Dyadic.RowActionImage GQ2.Dyadic.LSquare
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.NpcWordPhaseModel
open GQ2.Dyadic.Instances.NpcUnramifiedComparison
open GQ2.Dyadic.Instances.NpcUnramifiedFullOffsetHessian
open GQ2.Dyadic.Instances.NpcUnramifiedDiagonal
open GQ2.Dyadic.Instances.NpcRamifiedComparison
open GQ2.Dyadic.Instances.NpcRamifiedDiagonal
open GQ2.Dyadic.Instances.NpcRamifiedFullOffsetHessian

/-- The unramified comparison of W136, together with quadraticity of its honest head diagonal. -/
private noncomputable def wPnpcComparison_unramifiedHead_quadratic
    {alpha r h q : ℕ} {d : EtaData}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod]
    [ContinuousSMul
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar)
    (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ (a b : DD.Vmod), DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hcompat : ∀
      (gamma : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type))
      (v : DD.Vmod), gamma • v = rho0 DD rho gamma • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) i)))
    (halpha : 2 ≤ alpha) (hqe : Even q)
    (hcardH2 :
      letI : TopologicalSpace (ZMod 2) := ⊥
      letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
      letI : DistribMulAction
          ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
        scalarActionZmodTwo _
      Nat.card
        (H2 ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2)) = 2)
    (htauHead : pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau)) = 1)
    (hwildHead : ∀ i : Fin (2 + 2 * h + 1), pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) (.wild i))) = 1)
    (hsigmaFpf : ∀ v : DD.Vmod,
      pi (rho0 DD rho
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)) • v = v → v = 0)
    (hgfpf : ∀ v : DD.Vmod,
      ((rho0 DD rho
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma) ^
          npcResolver
            (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) d d.toZhat)⁻¹ :
        DD.C0) • v = v → v = 0)
    (hufpf : ∀ v : DD.Vmod,
      ((rho0 DD rho
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma) ^
          ((2 : ℤ) ^ r))⁻¹ : DD.C0) • v = v → v = 0) :
    let L := SectionSix.SemiProd DD.C0 DD.Vmod
    let E := npcResolver (4 * Monoid.exponent L) d
    let s0 : DD.C0 := rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)
    let g : DD.C0 := (s0 ^ E d.toZhat)⁻¹
    let u : DD.C0 := (s0 ^ ((2 : ℤ) ^ r))⁻¹
    let Phi : DD.Vmod ≃+ DD.Vmod := AddEquiv.ofBijective
      (unramPhi (A := DD.Vmod) g hufpf)
      (by simpa [g, u, s0, E, L] using
        (unramPhi_bijective (A := DD.Vmod) hgfpf hufpf))
    let s := pi s0
    let d0 : DD.Vmod → ZMod 2 := fun a ↦
      npcUnramifiedDiagonal base hbase s E alpha r d
        Phi.toAddMonoidHom (Phi.symm a)
    letI := scalarActionZmodTwo
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    IsQuadraticFp2 d0 ∧ Nonempty (SourceWordPhaseComparison DD rho
      (scalarActionZmodTwo_triv _)
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (wPnpcWallHandlePhase d0 DD.qbar h)) := by
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  let N := 4 * Monoid.exponent L
  let E := npcResolver N d
  let s0 : DD.C0 := rho0 DD rho
    (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)
  let g : DD.C0 := (s0 ^ E d.toZhat)⁻¹
  let u : DD.C0 := (s0 ^ ((2 : ℤ) ^ r))⁻¹
  have hgfpf' : ∀ v : DD.Vmod, g • v = v → v = 0 := by
    simpa [g, s0, E, N, L] using hgfpf
  have hufpf' : ∀ v : DD.Vmod, u • v = v → v = 0 := by
    simpa [u, s0] using hufpf
  let Phi : DD.Vmod ≃+ DD.Vmod := AddEquiv.ofBijective
    (unramPhi (A := DD.Vmod) g hufpf') (unramPhi_bijective hgfpf' hufpf')
  let s := pi s0
  let d0 : DD.Vmod → ZMod 2 := fun a ↦
    npcUnramifiedDiagonal base hbase s E alpha r d
      Phi.toAddMonoidHom (Phi.symm a)
  letI : TopologicalSpace Cbar := ⊥
  letI : DiscreteTopology Cbar := ⟨rfl⟩
  letI := scalarActionZmodTwo
    ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  have hsd : Function.Surjective (sdSnd : L →* DD.C0) := by
    intro x
    exact ⟨((0, x) : L), rfl⟩
  have hord : orderOf s ∣ N := by
    exact (orderOf_map_dvd pi s0).trans
      ((Monoid.order_dvd_exponent s0).trans
        ((MonoidHom.exponent_dvd hsd).trans ⟨4, by ring⟩))
  have hN : N ≠ 0 := fourMulExponent_ne_zero_and_even L |>.1
  have hresolverEta : s ^ E d.toZhat = s ^ᶻ etaHatZ d.toPadic := by
    change s ^ npcResolver N d d.toZhat = s ^ᶻ etaHatZ d.toPadic
    rw [npcResolver_toZhat, zpow_natCast]
    exact (zpowHat_etaHatZ_zpow hN hord d.toPadic).symm
  have hPhiQuadratic : ∀ v : DD.Vmod,
      v + (s ^ E d.toZhat)⁻¹ • v =
        Phi.toAddMonoidHom v + (s ^ (2 ^ r : ℤ))⁻¹ • Phi.toAddMonoidHom v := by
    intro v
    have hs := unramPhi_spec (A := DD.Vmod) g hufpf' v
    change Phi v - u • Phi v = v - g • v at hs
    rw [sub_eq_add_neg, Certificates.neg_eq_self hA2,
      sub_eq_add_neg, Certificates.neg_eq_self hA2] at hs
    rw [hpi g, hpi u] at hs
    simpa [g, u, s, s0] using hs.symm
  refine ⟨?_, ?_⟩
  · exact isQuadratic_npcUnramifiedDiagonal_comp base hbase DD.hquad hA2
      s E d hresolverEta halpha Phi.toAddMonoidHom Phi.symm.toAddMonoidHom
      hPhiQuadratic
  · exact ⟨wPnpcComparison_unramifiedHead rho base hbase pi hpi hf hm hcompat
      hA2 hwildTwo halpha hqe hcardH2 htauHead hwildHead hsigmaFpf hgfpf hufpf⟩

/-- Action-image arithmetic gives both concrete unramified head powers at the source resolver. -/
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

/-- Consume the unramified projected-head facts at one boundary lift. -/
private theorem wPnpcBoundaryResidue_unramified_of_head
    {alpha r h q m : ℕ} {d : EtaData}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod]
    [ContinuousSMul
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar)
    (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ (a b : DD.Vmod), DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hcompat : ∀
      (gamma : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type))
      (v : DD.Vmod), gamma • v = rho0 DD rho gamma • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) i)))
    (halpha : 2 ≤ alpha) (hqe : Even q)
    (hcardH2 :
      letI := scalarActionZmodTwo
        ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
      Nat.card
        (H2 ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2)) = 2)
    (htauHead : pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau)) = 1)
    (hwildHead : ∀ i : Fin (2 + 2 * h + 1), pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) (.wild i))) = 1)
    (hsigmaFpf : ∀ v : DD.Vmod, pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)) • v = v → v = 0)
    (hgfpf : ∀ v : DD.Vmod,
      ((rho0 DD rho (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma) ^
        npcResolver (4 * Monoid.exponent
          (SectionSix.SemiProd DD.C0 DD.Vmod)) d d.toZhat)⁻¹ : DD.C0) • v = v → v = 0)
    (hufpf : ∀ v : DD.Vmod,
      ((rho0 DD rho (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma) ^
        ((2 : ℤ) ^ r))⁻¹ : DD.C0) • v = v → v = 0)
    (hcard : Nat.card DD.Vmod = 2 ^ (2 * m)) :
    letI := scalarActionZmodTwo
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
    ∃ (W : Type) (_ : Fintype W) (Q : W → ZMod 2),
      Nonempty (SourceWordPhaseComparison DD rho (scalarActionZmodTwo_triv _) W Q) ∧
      QuadraticFp2.gaussSum Q = (standardNumerics (2 * h + 2)).gaussRam m := by
  letI := scalarActionZmodTwo
    ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  let E0 := npcResolver (4 * Monoid.exponent L) d
  let s0 : DD.C0 := rho0 DD rho
    (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)
  let g : DD.C0 := (s0 ^ E0 d.toZhat)⁻¹
  let u : DD.C0 := (s0 ^ ((2 : ℤ) ^ r))⁻¹
  let Phi : DD.Vmod ≃+ DD.Vmod := AddEquiv.ofBijective
    (unramPhi (A := DD.Vmod) g hufpf) (unramPhi_bijective hgfpf hufpf)
  let s := pi s0
  let d0 : DD.Vmod → ZMod 2 := fun a ↦
    npcUnramifiedDiagonal base hbase s E0 alpha r d Phi.toAddMonoidHom (Phi.symm a)
  have C : IsQuadraticFp2 d0 ∧ Nonempty (SourceWordPhaseComparison DD rho
      (scalarActionZmodTwo_triv _)
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (wPnpcWallHandlePhase d0 DD.qbar h)) := by
    simpa only [L, E0, s0, g, u, Phi, s, d0] using
      (wPnpcComparison_unramifiedHead_quadratic rho base hbase pi hpi hf hm
        hcompat hA2 hwildTwo halpha hqe hcardH2 htauHead hwildHead
        hsigmaFpf hgfpf hufpf)
  refine ⟨(DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod), inferInstance,
    wPnpcWallHandlePhase d0 DD.qbar h, C.2, ?_⟩
  exact wPnpc_wallHandlePhase_gaussSum_standardRam C.1 DD.hquad DD.hns
    ((Nat.card_eq_fintype_card (α := DD.Vmod)).symm.trans hcard) h

/-- A cyclic projected head makes the source sigma action fixed-point-free. -/
private theorem boundary_sigma_fixedPointFree_of_tau_one
    {alpha r h q : ℕ} {d : EtaData}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    {Cbar : Type} [Group Cbar] [DistribMulAction Cbar DD.Vmod]
    (pi : DD.C0 →* Cbar) (sigmaBar : Cbar)
    (hpi : ∀ (cc : DD.C0) (v : DD.Vmod),
      cc • v = pi cc • v)
    (hsigmaHead : pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)) = sigmaBar)
    (hzp : ∀ x : Cbar, x ∈ Subgroup.zpowers sigmaBar)
    (hfix : ∀ v : DD.Vmod,
      (∀ gamma : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type),
        rho0 DD rho gamma • v = v) → v = 0) :
    ∀ v : DD.Vmod, rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma) • v = v → v = 0 := by
  intro v hv
  have hv' : sigmaBar • v = v := by
    have hstep := hpi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)) v
    rwa [hstep, hsigmaHead] at hv
  refine hfix v fun gamma ↦ ?_
  rw [hpi _ v]
  have hmem : sigmaBar ∈ MulAction.stabilizer Cbar v :=
    MulAction.mem_stabilizer_iff.mpr hv'
  exact (Subgroup.zpowers_le.mpr hmem)
    (hzp (pi (rho0 DD rho gamma)))

/-- Package the three fixed-point-free facts consumed by the unramified comparison. -/
private theorem boundary_unramified_headPowers
    {alpha r h q : ℕ} {d : EtaData}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod]
    [ContinuousSMul
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod]
    {Cbar : Type} [Group Cbar] [DistribMulAction Cbar DD.Vmod]
    (pi : DD.C0 →* Cbar) (sigmaBar : Cbar)
    (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hcompat : ∀
      (gamma : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type))
      (v : DD.Vmod), gamma • v = rho0 DD rho gamma • v)
    (hV2 : ∀ v : DD.Vmod, v + v = 0)
    (hsimple : IsSimpleModTwo
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod)
    (hfix : ∀ v : DD.Vmod,
      (∀ gamma : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type),
        rho0 DD rho gamma • v = v) → v = 0)
    (hsigmaHead : pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)) = sigmaBar)
    (htauHead : pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau)) = 1)
    (hzp : ∀ x : Cbar, x ∈ Subgroup.zpowers sigmaBar) :
    let L := SectionSix.SemiProd DD.C0 DD.Vmod
    let E := npcResolver (4 * Monoid.exponent L) d
    let s0 := rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)
    (∀ v : DD.Vmod, pi s0 • v = v → v = 0) ∧
      (∀ v : DD.Vmod, ((s0 ^ E d.toZhat)⁻¹ : DD.C0) • v = v → v = 0) ∧
      (∀ v : DD.Vmod, ((s0 ^ ((2 : ℤ) ^ r))⁻¹ : DD.C0) • v = v → v = 0) := by
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  let E := npcResolver (4 * Monoid.exponent L) d
  let s0 := rho0 DD rho
    (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)
  have htauAct : ∀ v : DD.Vmod, rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau) • v = v := by
    intro v
    exact (hpi _ v).trans (by rw [htauHead, one_smul])
  have hsigmaFpf : ∀ v : DD.Vmod, s0 • v = v → v = 0 :=
    boundary_sigma_fixedPointFree_of_tau_one
      (alpha := alpha) (r := r) (h := h) (q := q) (d := d)
      rho pi sigmaBar hpi hsigmaHead hzp hfix
  have hsigmaProjectedFpf : ∀ v : DD.Vmod, pi s0 • v = v → v = 0 := by
    intro v hv
    exact hsigmaFpf v ((hpi _ v).trans hv)
  have htauGamma : ∀ v : DD.Vmod,
      gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau • v = v := by
    intro v
    exact (hcompat _ v).trans (htauAct v)
  have hsigmaGammaFpf : ∀ v : DD.Vmod,
      gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma • v = v → v = 0 := by
    intro v hv
    exact hsigmaFpf v ((hcompat _ v).symm.trans hv)
  obtain ⟨hgfpf, hufpf⟩ := unramified_concreteHead_powers_fixedPointFree
    (alpha := alpha) (r := r) (h := h) (q := q) (d := d)
    (Count.rho0Continuous DD rho) hcompat hV2 hsimple htauGamma hsigmaGammaFpf
  exact ⟨hsigmaProjectedFpf, hgfpf, hufpf⟩

/-- Close an unramified residue once the cyclic projected-head data have been exposed. -/
private theorem wPnpcBoundaryResidue_unramified_of_cyclic_head
    {alpha r h q m : ℕ} {d : EtaData}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod]
    [ContinuousSMul
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar) (sigmaBar : Cbar)
    (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ (a b : DD.Vmod), DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hcompat : ∀
      (gamma : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type))
      (v : DD.Vmod), gamma • v = rho0 DD rho gamma • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hsimple : IsSimpleModTwo
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod)
    (hfix : ∀ v : DD.Vmod,
      (∀ gamma : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type),
        rho0 DD rho gamma • v = v) → v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) i)))
    (halpha : 2 ≤ alpha) (hqe : Even q)
    (hcardH2 :
      letI := scalarActionZmodTwo
        ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
      Nat.card
        (H2 ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2)) = 2)
    (hsigmaHead : pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)) = sigmaBar)
    (htauHeadOne : pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau)) = 1)
    (hwildHead : ∀ i : Fin (2 + 2 * h + 1), pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) (.wild i))) = 1)
    (hzp : ∀ x : Cbar, x ∈ Subgroup.zpowers sigmaBar)
    (hcard : Nat.card DD.Vmod = 2 ^ (2 * m)) :
    letI := scalarActionZmodTwo
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
    ∃ (W : Type) (_ : Fintype W) (Q : W → ZMod 2),
      Nonempty (SourceWordPhaseComparison DD rho (scalarActionZmodTwo_triv _) W Q) ∧
      QuadraticFp2.gaussSum Q = (standardNumerics (2 * h + 2)).gaussRam m := by
  obtain ⟨hsigmaFpf, hgfpf, hufpf⟩ :=
    boundary_unramified_headPowers (alpha := alpha) (r := r) (h := h) (q := q)
      (d := d) rho pi sigmaBar hpi hcompat hA2 hsimple hfix hsigmaHead
      htauHeadOne hzp
  exact wPnpcBoundaryResidue_unramified_of_head
    (alpha := alpha) (r := r) (h := h) (q := q) (m := m) (d := d)
    rho base hbase pi hpi hf hm hcompat hA2 hwildTwo halpha hqe hcardH2
    htauHeadOne hwildHead hsigmaFpf hgfpf hufpf hcard

/-- Consume the ramified projected-head facts at one boundary lift. -/
private theorem wPnpcBoundaryResidue_ramified_of_head
    {alpha r h q m : ℕ} {d : EtaData}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod]
    [ContinuousSMul
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar)
    (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ (a b : DD.Vmod), DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hphi : Function.Surjective (semiProdProjHom (V := DD.Vmod) pi hpi))
    (hcompat : ∀
      (gamma : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type))
      (v : DD.Vmod), gamma • v = rho0 DD rho gamma • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) i)))
    (halpha : 2 ≤ alpha) (hqe : Even q)
    (hcardH2 :
      letI := scalarActionZmodTwo
        ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
      Nat.card
        (H2 ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2)) = 2)
    (hwildHead : ∀ i : Fin (2 + 2 * h + 1), pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) (.wild i))) = 1)
    (htauHeadOdd : Odd (orderOf (pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau)))))
    (htauHeadFpf : ∀ v : DD.Vmod, pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau)) • v = v → v = 0)
    (hcard : Nat.card DD.Vmod = 2 ^ (2 * m)) :
    letI := scalarActionZmodTwo
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
    ∃ (W : Type) (_ : Fintype W) (Q : W → ZMod 2),
      Nonempty (SourceWordPhaseComparison DD rho (scalarActionZmodTwo_triv _) W Q) ∧
      QuadraticFp2.gaussSum Q = (standardNumerics (2 * h + 2)).gaussRam m := by
  letI := scalarActionZmodTwo
    ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  let E := npcResolver (4 * Monoid.exponent L) d
  let s := pi (rho0 DD rho
    (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma))
  let u := pi (rho0 DD rho
    (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau))
  let Phi := DistribMulAction.toAddEquiv DD.Vmod (s ^ E d.toZhat)⁻¹
  let d0 : DD.Vmod → ZMod 2 := fun a ↦
    npcRamifiedDiagonal base hbase s u E alpha r d (Phi.symm a)
  have C : IsQuadraticFp2 d0 ∧ Nonempty (SourceWordPhaseComparison DD rho
      (scalarActionZmodTwo_triv _)
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (wPnpcWallHandlePhase d0 DD.qbar h)) := by
    simpa only [L, E, s, u, Phi, d0] using
      (wPnpcComparison_ramifiedHead
        (alpha := alpha) (r := r) (h := h) (q := q) (d := d)
        rho base hbase pi hpi hf hm hphi hcompat hA2 hwildTwo halpha hqe
        hcardH2 hwildHead htauHeadOdd htauHeadFpf)
  refine ⟨(DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod), inferInstance,
    wPnpcWallHandlePhase d0 DD.qbar h, C.2, ?_⟩
  exact wPnpc_wallHandlePhase_gaussSum_standardRam C.1 DD.hquad DD.hns
    ((Nat.card_eq_fintype_card (α := DD.Vmod)).symm.trans hcard) h

/-- The unramified simple boundary residue. -/
private theorem wPnpcBoundary_unramified_at_lift
    {alpha r h q : ℕ} {d : EtaData}
    (hsimp : UniformHsimp alpha r h q d) (halpha : 2 ≤ alpha)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
    (F : BoundaryFrameK q P H E)
    (tame : ContinuousMonoidHom (displayedGamma alpha r h q d) (Tq q))
    (pro2 : ContinuousMonoidHom (displayedGamma alpha r h q d) P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma) = tqSigma q)
    (htameTau : tame
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau) = tqTau q)
    (htameWild : ∀ i : Fin (2 + 2 * h + 1),
      tame (gammaGen (2 + 2 * h) q (npcW alpha r h d) (.wild i)) = 1)
    (hsimple : ∀ W : AddSubgroup (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod,
      (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) →
        W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod, v ≠ 0)
    (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
      (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g • v ≠ v)
    (m : ℕ) (_hm : 1 ≤ m)
    (hcard : Nat.card (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod = 2 ^ (2 * m))
    (l : (SectionNine.blockFrame T Blk hE2).DR)
    (hl : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
    (hunram :
      letI := blockPS_commGroup Blk
      letI := SectionNine.headAct T Blk
      ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P),
        F.alpha (tqTau q) • v = v)
    (rho : BoundaryLiftsK (sourceBoundaryMapK tame pro2 compat) F
      (SectionNine.blockFrame T Blk hE2).TC) :
    let DD := (blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl
    let rhoN := rhoPrimeK (SectionNine.blockFrame T Blk hE2)
      (sourceBoundaryMapK tame pro2 compat) F
      ((blockEnrichmentDK T Blk hE2 hq0 hqe F).radData l hl) rfl rho
    letI := scalarActionZmodTwo
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
    ∃ (W : Type) (_ : Fintype W) (Q : W → ZMod 2),
      Nonempty (SourceWordPhaseComparison DD rhoN (scalarActionZmodTwo_triv _) W Q) ∧
      QuadraticFp2.gaussSum Q = (standardNumerics (2 * h + 2)).gaussRam m := by
  letI := scalarActionZmodTwo
    ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := SectionNine.headAct T Blk
  letI := SectionNine.hvAct T Blk
  classical
  let b := sourceBoundaryMapK tame pro2 compat
  set En := blockEnrichmentDK T Blk hE2 hq0 hqe F with hEn
  set DD := En.descData l hl with hDD
  have hl' : l.1 ≠ Blk.frattiniK := fun heq ↦ hl (Subtype.ext heq)
  let rhoN := rhoPrimeK (SectionNine.blockFrame T Blk hE2) b F
    (En.radData l hl) rfl rho
  letI : TopologicalSpace DD.C0 :=
    (inferInstance : TopologicalSpace (SectionNine.blockFrame T Blk hE2).YC)
  haveI : DiscreteTopology DD.C0 :=
    (inferInstance : DiscreteTopology (SectionNine.blockFrame T Blk hE2).YC)
  letI : TopologicalSpace DD.Vmod := ⊥
  haveI : DiscreteTopology DD.Vmod := ⟨rfl⟩
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI actYC : DistribMulAction
      (SectionNine.blockFrame T Blk hE2).YC DD.Vmod := blockActV Blk
  letI : DistribMulAction (SectionNine.HVq T Blk) DD.Vmod := SectionNine.hvAct T Blk
  letI : DistribMulAction
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
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
          p.1 • p.2) =
        (fun p : (SectionNine.blockFrame T Blk hE2).YC × DD.Vmod ↦ p.1 • p.2) ∘
          (fun p ↦ (rho.1.1 p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((rho.1.1.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hround : ∀ gamma : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type),
      rho0 DD rhoN gamma = rho.1.1 gamma :=
    rho0_descData_rhoPrimeK b F En l hl rho
  have hcompat : ∀
      (gamma : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type))
      (v : DD.Vmod), gamma • v = rho0 DD rhoN gamma • v := by
    intro gamma v
    exact congrArg (fun c : (SectionNine.blockFrame T Blk hE2).YC ↦ c • v)
      (hround gamma).symm
  have hsimpleGamma : IsSimpleModTwo
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) DD.Vmod := by
    obtain ⟨v, hv⟩ := hVne
    refine ⟨nontrivial_of_ne v 0 hv, ?_⟩
    intro W hW
    apply hsimple W
    intro c w hw
    obtain ⟨gamma, rfl⟩ := rho.1.2 c
    exact hW gamma w hw
  have hheadFac : ∀ gamma : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type),
      SectionNine.blockProjF T Blk (rho0 DD rhoN gamma) =
        headTameSurjK T Blk F (tame gamma) := by
    intro gamma
    rw [hround gamma]
    exact congrArg (⇑(QuotientGroup.mk' (SectionNine.headActKer T Blk)))
      (boundaryLift_headK T Blk hE2 b F rho gamma)
  have hsigmaHead : SectionNine.blockProjF T Blk (rho0 DD rhoN
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)) =
      hvSigmaK T Blk F := by
    rw [hheadFac, htameSigma]
    rfl
  have htauHead : SectionNine.blockProjF T Blk (rho0 DD rhoN
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau)) =
      hvTauK T Blk F := by
    rw [hheadFac, htameTau]
    rfl
  have hwildHead : ∀ i : Fin (2 + 2 * h + 1), SectionNine.blockProjF T Blk
      (rho0 DD rhoN
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) (.wild i))) = 1 := by
    intro i
    rw [hheadFac, htameWild i]
    show QuotientGroup.mk' (SectionNine.headActKer T Blk) (F.alpha 1) = 1
    rw [map_one, map_one]
  have hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rhoN
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) i)) :=
    isWildTwo_of_gammaGen (Count.rho0Continuous DD rhoN)
      (rho0Continuous_surjective DD rhoN
        (rhoPrimeK_surjective (SectionNine.blockFrame T Blk hE2) b F
          (En.radData l hl) rfl rho)) (fun _ ↦ rfl)
  have hsurjrho : Function.Surjective
      (fun gamma : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) ↦
        rho0 DD rhoN gamma) := fun y ↦ by
    obtain ⟨gamma, hgamma⟩ := rho.1.2 y
    exact ⟨gamma, (hround gamma).trans hgamma⟩
  have hfix : ∀ v : DD.Vmod,
      (∀ gamma : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type),
        rho0 DD rhoN gamma • v = v) → v = 0 :=
    hfix_of_simple_nt hsurjrho hsimple hnt
  have hpi : ∀ (cc : DD.C0) (v : DD.Vmod),
      cc • v = SectionNine.blockProjF T Blk cc • v :=
    fun cc v ↦ SectionNine.blockProjF_compat T Blk cc v
  have hcardH2 :
      Nat.card
        (H2 ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2)) = 2 :=
    cardH2_of_uniformPushed (alpha := alpha) (r := r) (h := h) (q := q) (d := d)
      hsimp (by omega) hqe
  refine ?_
  · have htauHeadOne : SectionNine.blockProjF T Blk (rho0 DD rhoN
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau)) = 1 := by
      rw [htauHead]
      show QuotientGroup.mk' (SectionNine.headActKer T Blk) (F.alpha (tqTau q)) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hunram
    have htauHVOne : hvTauK T Blk F = 1 := by
      show QuotientGroup.mk' (SectionNine.headActKer T Blk) (F.alpha (tqTau q)) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hunram
    have hzp : ∀ x : SectionNine.HVq T Blk,
        x ∈ Subgroup.zpowers (hvSigmaK T Blk F) := by
      have hle : Subgroup.closure {hvSigmaK T Blk F, hvTauK T Blk F} ≤
          Subgroup.zpowers (hvSigmaK T Blk F) := by
        rw [Subgroup.closure_le, Set.pair_subset_iff]
        refine ⟨Subgroup.mem_zpowers _, ?_⟩
        rw [htauHVOne]
        exact Subgroup.one_mem _
      rw [hv_genK T Blk F] at hle
      exact fun x ↦ hle (Subgroup.mem_top x)
    dsimp only at ⊢
    change ∃ (W : Type) (_ : Fintype W) (Q : W → ZMod 2),
      Nonempty (SourceWordPhaseComparison DD rhoN (scalarActionZmodTwo_triv _) W Q) ∧
      QuadraticFp2.gaussSum Q = (standardNumerics (2 * h + 2)).gaussRam m
    exact wPnpcBoundaryResidue_unramified_of_cyclic_head
      (alpha := alpha) (r := r) (h := h) (q := q) (m := m) (d := d) rhoN
      (blockDatHVK T Blk hq0 hqe F l hl')
      (blockDatHV_specK T Blk hq0 hqe F l hl')
      (SectionNine.blockProjF T Blk) (hvSigmaK T Blk F) hpi
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hcompat (Vmod_exp2 DD)
      hsimpleGamma hfix hwildTwo halpha hqe hcardH2 hsigmaHead
      htauHeadOne hwildHead hzp hcard

/-- The ramified simple boundary residue. -/
private theorem wPnpcBoundary_ramified_at_lift
    {alpha r h q : ℕ} {d : EtaData}
    (hsimp : UniformHsimp alpha r h q d) (halpha : 2 ≤ alpha)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
    (F : BoundaryFrameK q P H E)
    (tame : ContinuousMonoidHom (displayedGamma alpha r h q d) (Tq q))
    (pro2 : ContinuousMonoidHom (displayedGamma alpha r h q d) P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (htameTau : tame
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau) = tqTau q)
    (htameWild : ∀ i : Fin (2 + 2 * h + 1),
      tame (gammaGen (2 + 2 * h) q (npcW alpha r h d) (.wild i)) = 1)
    (m : ℕ)
    (hcard : Nat.card (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod = 2 ^ (2 * m))
    (l : (SectionNine.blockFrame T Blk hE2).DR)
    (hl : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
    (hram :
      letI := blockPS_commGroup Blk
      letI := SectionNine.headAct T Blk
      ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P),
        F.alpha (tqTau q) • v ≠ v)
    (rho : BoundaryLiftsK (sourceBoundaryMapK tame pro2 compat) F
      (SectionNine.blockFrame T Blk hE2).TC) :
    let DD := (blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl
    let rhoN := rhoPrimeK (SectionNine.blockFrame T Blk hE2)
      (sourceBoundaryMapK tame pro2 compat) F
      ((blockEnrichmentDK T Blk hE2 hq0 hqe F).radData l hl) rfl rho
    letI := scalarActionZmodTwo
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
    ∃ (W : Type) (_ : Fintype W) (Q : W → ZMod 2),
      Nonempty (SourceWordPhaseComparison DD rhoN (scalarActionZmodTwo_triv _) W Q) ∧
      QuadraticFp2.gaussSum Q = (standardNumerics (2 * h + 2)).gaussRam m := by
  letI := scalarActionZmodTwo
    ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := SectionNine.headAct T Blk
  letI := SectionNine.hvAct T Blk
  classical
  let b := sourceBoundaryMapK tame pro2 compat
  set En := blockEnrichmentDK T Blk hE2 hq0 hqe F with hEn
  set DD := En.descData l hl with hDD
  have hl' : l.1 ≠ Blk.frattiniK := fun heq ↦ hl (Subtype.ext heq)
  let rhoN := rhoPrimeK (SectionNine.blockFrame T Blk hE2) b F
    (En.radData l hl) rfl rho
  letI : TopologicalSpace DD.C0 :=
    (inferInstance : TopologicalSpace (SectionNine.blockFrame T Blk hE2).YC)
  haveI : DiscreteTopology DD.C0 :=
    (inferInstance : DiscreteTopology (SectionNine.blockFrame T Blk hE2).YC)
  letI : TopologicalSpace DD.Vmod := ⊥
  haveI : DiscreteTopology DD.Vmod := ⟨rfl⟩
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI actYC : DistribMulAction
      (SectionNine.blockFrame T Blk hE2).YC DD.Vmod := blockActV Blk
  letI : DistribMulAction (SectionNine.HVq T Blk) DD.Vmod := SectionNine.hvAct T Blk
  letI : DistribMulAction
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
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
          p.1 • p.2) =
        (fun p : (SectionNine.blockFrame T Blk hE2).YC × DD.Vmod ↦ p.1 • p.2) ∘
          (fun p ↦ (rho.1.1 p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((rho.1.1.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hround : ∀ gamma : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type),
      rho0 DD rhoN gamma = rho.1.1 gamma :=
    rho0_descData_rhoPrimeK b F En l hl rho
  have hcompat : ∀
      (gamma : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type))
      (v : DD.Vmod), gamma • v = rho0 DD rhoN gamma • v := by
    intro gamma v
    exact congrArg (fun c : (SectionNine.blockFrame T Blk hE2).YC ↦ c • v)
      (hround gamma).symm
  have hheadFac : ∀ gamma : ((displayedGamma alpha r h q d : ProfiniteGrp) : Type),
      SectionNine.blockProjF T Blk (rho0 DD rhoN gamma) =
        headTameSurjK T Blk F (tame gamma) := by
    intro gamma
    rw [hround gamma]
    exact congrArg (⇑(QuotientGroup.mk' (SectionNine.headActKer T Blk)))
      (boundaryLift_headK T Blk hE2 b F rho gamma)
  have htauHead : SectionNine.blockProjF T Blk (rho0 DD rhoN
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau)) =
      hvTauK T Blk F := by
    rw [hheadFac, htameTau]
    rfl
  have hwildHead : ∀ i : Fin (2 + 2 * h + 1), SectionNine.blockProjF T Blk
      (rho0 DD rhoN
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) (.wild i))) = 1 := by
    intro i
    rw [hheadFac, htameWild i]
    show QuotientGroup.mk' (SectionNine.headActKer T Blk) (F.alpha 1) = 1
    rw [map_one, map_one]
  have hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rhoN
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) i)) :=
    isWildTwo_of_gammaGen (Count.rho0Continuous DD rhoN)
      (rho0Continuous_surjective DD rhoN
        (rhoPrimeK_surjective (SectionNine.blockFrame T Blk hE2) b F
          (En.radData l hl) rfl rho)) (fun _ ↦ rfl)
  have hpi : ∀ (cc : DD.C0) (v : DD.Vmod),
      cc • v = SectionNine.blockProjF T Blk cc • v :=
    fun cc v ↦ SectionNine.blockProjF_compat T Blk cc v
  have hblockPiCH : Function.Surjective (SectionNine.blockPiCH T Blk) := by
    intro c
    obtain ⟨y, hy⟩ := T.piY_surjective c
    refine ⟨QuotientGroup.mk' Blk.K y, ?_⟩
    change T.piY y = c
    exact hy
  have hblockProj : Function.Surjective (SectionNine.blockProjF T Blk) :=
    (QuotientGroup.mk'_surjective _).comp hblockPiCH
  have hsemi : Function.Surjective
      (semiProdProjHom (C' := DD.C0) (V := DD.Vmod)
        (SectionNine.blockProjF T Blk) hpi) := by
    intro z
    obtain ⟨c, hc⟩ := hblockProj z.2
    exact ⟨(z.1, c), Prod.ext rfl hc⟩
  have hrelHV : (hvSigmaK T Blk F)⁻¹ * hvTauK T Blk F * hvSigmaK T Blk F =
      hvTauK T Blk F ^ q := hv_relK T Blk F
  haveI hnormHV : (Subgroup.zpowers (hvTauK T Blk F)).Normal :=
    tame_zpowers_normal_pow (hv_genK T Blk F) hrelHV
  have hoddHV : Odd (orderOf (hvTauK T Blk F)) :=
    tame_odd_order_pow (orderOf_pos (hvSigmaK T Blk F)).ne' hq0 hqe hrelHV
  have htauHeadFpf : ∀ v : DD.Vmod, hvTauK T Blk F • v = v → v = 0 := by
    intro v hv
    exact tau_fixed_eq_zero_of_zpowers_normal (hvTauK T Blk F) hnormHV
      (SectionNine.hv_simple T Blk) hram v hv
  have hoddProjected : Odd (orderOf (SectionNine.blockProjF T Blk (rho0 DD rhoN
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau)))) := by
    rw [htauHead]
    exact hoddHV
  have htauProjectedFpf : ∀ v : DD.Vmod, SectionNine.blockProjF T Blk
      (rho0 DD rhoN
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau)) • v = v → v = 0 := by
    intro v hv
    apply htauHeadFpf v
    rwa [htauHead] at hv
  have hcardH2 :
      Nat.card
        (H2 ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2)) = 2 :=
    cardH2_of_uniformPushed (alpha := alpha) (r := r) (h := h) (q := q) (d := d)
      hsimp (by omega) hqe
  dsimp only at ⊢
  change ∃ (W : Type) (_ : Fintype W) (Q : W → ZMod 2),
    Nonempty (SourceWordPhaseComparison DD rhoN (scalarActionZmodTwo_triv _) W Q) ∧
    QuadraticFp2.gaussSum Q = (standardNumerics (2 * h + 2)).gaussRam m
  exact wPnpcBoundaryResidue_ramified_of_head
    (alpha := alpha) (r := r) (h := h) (q := q) (m := m) (d := d) rhoN
    (blockDatHVK T Blk hq0 hqe F l hl')
    (blockDatHV_specK T Blk hq0 hqe F l hl')
    (SectionNine.blockProjF T Blk) hpi (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    hsemi hcompat (Vmod_exp2 DD) hwildTwo halpha hqe hcardH2 hwildHead
    hoddProjected htauProjectedFpf hcard

/-- The faithful Npc boundary supplies a single even Gauss endpoint in both head branches. -/
theorem wPnpc_branchFreeSupply
    {alpha r h q : ℕ} {d : EtaData}
    (hsimp : UniformHsimp alpha r h q d) (halpha : 2 ≤ alpha)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (displayedGamma alpha r h q d) (Tq q))
    (pro2 : ContinuousMonoidHom (displayedGamma alpha r h q d) P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma) = tqSigma q)
    (htameTau : tame
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau) = tqTau q)
    (htameWild : ∀ i : Fin (2 + 2 * h + 1),
      tame (gammaGen (2 + 2 * h) q (npcW alpha r h d) (.wild i)) = 1) :
    wPhBranchFreeSupply (2 * h + 2) nuP tame pro2 compat := by
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk _ _ _ hE2 hq0 hqe F
    hsimple hVne hnt m hm hcard l hl rho
  letI := blockPS_commGroup Blk
  letI := SectionNine.headAct T Blk
  classical
  by_cases hunram : ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P),
      F.alpha (tqTau q) • v = v
  · exact wPnpcBoundary_unramified_at_lift
      (alpha := alpha) (r := r) (h := h) (q := q) (d := d)
      hsimp halpha T Blk hE2 hq0 hqe F tame pro2 compat htameSigma htameTau
      htameWild hsimple hVne hnt m hm hcard l hl hunram rho
  · have hram : ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P),
        F.alpha (tqTau q) • v ≠ v := by
      simpa only [not_forall] using hunram
    exact wPnpcBoundary_ramified_at_lift
      (alpha := alpha) (r := r) (h := h) (q := q) (d := d)
      hsimp halpha T Blk hE2 hq0 hqe F tame pro2 compat htameTau htameWild
      m hcard l hl hram rho

#print axioms wPnpc_branchFreeSupply

end
end GQ2.Dyadic.Instances.NpcBoundaryFinal

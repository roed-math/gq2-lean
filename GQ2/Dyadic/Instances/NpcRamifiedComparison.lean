/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcRamifiedDiagonal
import GQ2.Dyadic.Instances.NpcRamifiedComparisonBase
import GQ2.Dyadic.Instances.NpcWordPhaseSeam
import GQ2.Dyadic.Instances.KappaResolverTransport

/-!
# Ramified procyclic-N source/word comparison

This module combines the full-offset ramified Hessian with the quadratic diagonal calculation.
At a faithful projected cyclic head it identifies `QZero` with the twisted plus-form head and
standard handle tail, then assembles the corrected source/word phase comparison.
-/

namespace GQ2.Dyadic.Instances.NpcRamifiedComparison

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.Words.Npc
open GQ2.Dyadic.Certificates GQ2.QuadraticFp2
open GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.NProcyclic
open GQ2.Dyadic.LSquare
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.WordPhaseSeam
open GQ2.Dyadic.Instances.NpcWordPhaseModel
open GQ2.Dyadic.Instances.NpcWordPhaseSeam
open GQ2.Dyadic.Instances.NpcRamifiedComparisonBase
open GQ2.Dyadic.Instances.NpcRamifiedFullOffsetHessian
open GQ2.Dyadic.Instances.NpcRamifiedDiagonal

private theorem isTwoEntryRamifiedRow_npc_at
    {alpha r h q N : ℕ} {d : EtaData}
    {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (hA2 : ∀ a : A, a + a = 0)
    (ht : t.TameRelAt q)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (htauFpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a) (halpha : 1 ≤ alpha)
    (hresolver : MProcyclic.ResolverLifts (npcResolver N d) (WordLift A C)) :
    IsTwoEntryRamifiedRow t (resolvedFamily alpha r h q d N) q
      ((t.σ ^ (npcResolver N d) d.toZhat)⁻¹)
      ((t.σ ^ ((2 : ℤ) ^ r))⁻¹) A := by
  intro x
  funext k
  fin_cases k
  · change
      (FreeGroup.lift (heisGen (⇑t) x 0)
        (heisToFree (npcResolver N d) (fun _ ↦ (0 : ℤ))
          (tameRelW (2 + 2 * h) q))).a =
        t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
          - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau
    rw [← heisEvalZ_eq_lift, heisEvalZ_a_eq_foxD hresolver,
      Certificates.foxD_tameRelW_of_tameRel t _ _ ht]
  · change
      (FreeGroup.lift (heisGen (⇑t) x 0)
        (heisToFree (npcResolver N d) (fun _ ↦ (0 : ℤ))
          (Words.Npc.npcW alpha r h d))).a =
        ((t.σ ^ (npcResolver N d) d.toZhat)⁻¹ • x (coreLetter h 0)
            - x (coreLetter h 0))
          - (t.σ ^ ((2 : ℤ) ^ r))⁻¹ • x (coreLetter h 2)
    rw [← heisEvalZ_eq_lift, heisEvalZ_a_eq_foxD hresolver,
      Certificates.Npc.foxD_npc_ram t _ _ hA2 hwild htauFpf hTodd halpha d]

theorem wPnpc_QZero_eq_ramifiedWallHandlePhase_of_projectedTwistedMark
    {alpha r h q : ℕ} {d : EtaData}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar)
    (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ (a b : DD.Vmod), DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hphi : Function.Surjective (semiProdProjHom (V := DD.Vmod) pi hpi))
    (halpha : 2 ≤ alpha) (hqe : Even q)
    (hcardH2 :
      letI : TopologicalSpace (ZMod 2) := ⊥
      letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
      letI : DistribMulAction
          ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
        scalarActionZmodTwo _
      Nat.card
        (H2 ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2)) = 2)
    (c : VCocycle DD rho)
    (hwildHead : ∀ i : Fin (2 + 2 * h + 1), pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) (.wild i))) = 1)
    (htauHeadOdd : Odd (orderOf (pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau)))))
    (htauHeadFpf : ∀ v : DD.Vmod, pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau)) • v = v → v = 0)
    (p : (DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
    (hc : (fun i ↦ c.c (gammaGen (2 + 2 * h) q (npcW alpha r h d) i)) =
      wPnpcTwistedPhaseNormal h
        ((rho0 DD rho (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma) ^
          npcResolver
            (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) d d.toZhat)⁻¹)
        ((rho0 DD rho (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma) ^
          ((2 : ℤ) ^ r))⁻¹)
        (DistribMulAction.toAddEquiv DD.Vmod
          ((pi (rho0 DD rho
            (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)) ^
              npcResolver
                (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) d d.toZhat)⁻¹)) p) :
    let L := SectionSix.SemiProd DD.C0 DD.Vmod
    let E := npcResolver (4 * Monoid.exponent L) d
    let s := pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma))
    let u := pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau))
    let Phi := DistribMulAction.toAddEquiv DD.Vmod (s ^ E d.toZhat)⁻¹
    let d0 : DD.Vmod → ZMod 2 := fun a ↦
      npcRamifiedDiagonal base hbase s u E alpha r d (Phi.symm a)
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction
        ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo _
    letI : ContinuousSMul
        ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    QZero DD rho c = wPnpcWallHandlePhase d0 DD.qbar h p := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  let N := 4 * Monoid.exponent L
  let E := npcResolver N d
  let E2 : ℤ_[2] → ℤ := fun _ ↦ 0
  let s0 := rho0 DD rho
    (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)
  let tau0 := rho0 DD rho
    (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau)
  let s := pi s0
  let u := pi tau0
  let g0 : DD.C0 := (s0 ^ E d.toZhat)⁻¹
  let b0 : DD.C0 := (s0 ^ ((2 : ℤ) ^ r))⁻¹
  let Phi := DistribMulAction.toAddEquiv DD.Vmod (s ^ E d.toZhat)⁻¹
  let d0 : DD.Vmod → ZMod 2 := fun a ↦
    npcRamifiedDiagonal base hbase s u E alpha r d (Phi.symm a)
  letI : TopologicalSpace Cbar := ⊥
  letI : DiscreteTopology Cbar := ⟨rfl⟩
  let K := WordCoh.CentExt (kappa0Cocycle DD.dat DD.hdat)
  letI : Finite K := inferInstance
  letI : TopologicalSpace K := ⊥
  letI : DiscreteTopology K := ⟨rfl⟩
  have hN : N ≠ 0 := fourMulExponent_ne_zero_and_even L |>.1
  have hordK : ∀ y : K, orderOf y ∣ N := by
    intro y
    have hbasePow : y.base ^ Monoid.exponent L = 1 := Monoid.pow_exponent_eq_one y.base
    exact (nc3_orderOf_dvd_two_mul DD.dat DD.hdat hbasePow).trans ⟨2, by ring⟩
  have homega : ∀ y : K, y ^ᶻ omega2 = y ^ E omega2 := by
    intro y
    change y ^ᶻ omega2 = y ^ npcResolver N d omega2
    rw [npcResolver_omega2, PWord.zpowHat_omega2_zpow hN (hordK y), zpow_natCast]
  have heta : ∀ y : K, y ^ᶻ d.toZhat = y ^ E d.toZhat := by
    intro y
    change y ^ᶻ d.toZhat = y ^ npcResolver N d d.toZhat
    rw [npcResolver_toZhat, EtaData.toZhat,
      zpowHat_etaHatZ_zpow hN (hordK y), zpow_natCast]
  have hresolved : ∀ k, PWord.ResolvedAt
      (WordCoh.lift
        (fun i ↦ graphSemiProdHom c
          (gammaGen (2 + 2 * h) q (npcW alpha r h d) i))
        (kappa0Cocycle DD.dat DD.hdat)) E E2
      (gammaFam (2 + 2 * h) q (npcW alpha r h d) k) := by
    intro k
    fin_cases k
    · exact PWord.resolvedAt_of_isOmega2Only _ E E2 homega _
        (isOmega2Only_tameRelW (2 + 2 * h) q)
    · exact Count.resolvedAt_npcW _ homega heta alpha r
  let phi := semiProdProjHom (V := DD.Vmod) pi hpi
  have hcval : ∀ i, c.c (gammaGen (2 + 2 * h) q (npcW alpha r h d) i) =
      wPnpcTwistedPhaseNormal h g0 b0 Phi p i := by
    intro i
    simpa only [g0, b0, Phi, s, s0, E, N, L] using congrFun hc i
  have hmark :
      (fun i ↦ phi (graphSemiProdHom c
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) i))) =
        Certificates.hessMark s u
          (fun i ↦ wPnpcTwistedPhaseNormal h g0 b0 Phi p (.wild i)) := by
    funext i
    cases i with
    | sigma => exact Prod.ext ((hcval _).trans
        (wPnpcTwistedPhaseNormal_sigma h g0 b0 Phi p)) rfl
    | tau => exact Prod.ext ((hcval _).trans
        (wPnpcTwistedPhaseNormal_tau h g0 b0 Phi p)) rfl
    | wild i => exact Prod.ext (hcval _) (hwildHead i)
  let raw := (wPnpcRamifiedCoordsEquiv h DD.Vmod Phi).symm p
  have hraw := (wPnpcRamifiedCoordsEquiv h DD.Vmod Phi).apply_symm_apply p
  have hraw0 : raw.1 = Phi.symm p.1.1 := by
    apply Phi.injective
    have hh := congrArg (fun x ↦ x.1.1) hraw
    change Phi raw.1 = p.1.1 at hh
    exact hh.trans (Phi.apply_symm_apply p.1.1).symm
  have hraw1 : raw.2.1 = p.1.2 := congrArg (fun x ↦ x.1.2) hraw
  have hrawU : ∀ j, raw.2.2 (j, 0) = (p.2 j).1 := by
    intro j
    exact congrArg (fun x ↦ (x.2 j).1) hraw
  have hrawV : ∀ j, raw.2.2 (j, 1) = (p.2 j).2 := by
    intro j
    exact congrArg (fun x ↦ (x.2 j).2) hraw
  have hoffsets :
      (fun i ↦ wPnpcTwistedPhaseNormal h g0 b0 Phi p (.wild i)) =
        npcTwistedOffsets h (s ^ E d.toZhat)⁻¹ (s ^ ((2 : ℤ) ^ r))⁻¹
          raw.1 raw.2.1 raw.2.2 := by
    have hgact : ∀ v : DD.Vmod, g0 • v = (s ^ E d.toZhat)⁻¹ • v := by
      intro v
      rw [hpi]
      simp [g0, s, s0, map_zpow]
    have hbInvact : ∀ v : DD.Vmod,
        b0⁻¹ • v = ((s ^ ((2 : ℤ) ^ r))⁻¹)⁻¹ • v := by
      intro v
      rw [hpi]
      simp [b0, s, s0, map_zpow]
    have heven : evenTwistedNormal h g0 b0 raw.1 raw.2.1 raw.2.2 =
        evenTwistedNormal h (s ^ E d.toZhat)⁻¹ (s ^ ((2 : ℤ) ^ r))⁻¹
          raw.1 raw.2.1 raw.2.2 := by
      unfold evenTwistedNormal
      apply congrArg (EvenCore.coreHandleAddEquiv h DD.Vmod).symm
      apply Prod.ext
      · funext j
        cases j with
        | sigma => rfl
        | tau => rfl
        | wild i =>
          fin_cases i
          · rfl
          · rfl
          · rw [hgact, hbInvact]
      · rfl
    funext i
    calc
      _ = wPnpcTwistedPhaseNormal h g0 b0 Phi
          (wPnpcRamifiedCoordsEquiv h DD.Vmod Phi raw) (.wild i) := by rw [hraw]
      _ = evenTwistedNormal h g0 b0 raw.1 raw.2.1 raw.2.2 (.wild i) :=
        congrFun (wPnpcTwistedPhaseNormal_coordsEquiv h g0 b0 Phi raw) (.wild i)
      _ = evenTwistedNormal h (s ^ E d.toZhat)⁻¹ (s ^ ((2 : ℤ) ^ r))⁻¹
          raw.1 raw.2.1 raw.2.2 (.wild i) := congrFun heven (.wild i)
      _ = _ := rfl
  have hresTarget : MProcyclic.ResolverLifts E
      (WordCoh.CentExt (kappa0Cocycle base hbase)) := by
    intro y
    have hbasePow : y.base ^ Monoid.exponent L = 1 := by
      obtain ⟨x, hx⟩ := hphi y.base
      rw [← hx, ← map_pow, Monoid.pow_exponent_eq_one, map_one]
    have hord : orderOf y ∣ N :=
      (nc3_orderOf_dvd_two_mul base hbase hbasePow).trans ⟨2, by ring⟩
    change y ^ npcResolver N d omega2 = powOmega2 y
    rw [npcResolver_omega2, zpow_natCast]
    exact powOmega2_pow_eq y hord hN
  rw [wPnpc_QZero_eq_graphHessianTrace rho DD.hdat (by omega) hqe hcardH2
      c E E2 hresolved,
    kappa0Cocycle_comap_semiProdProjHom base hbase DD.dat DD.hdat pi hpi hf hm]
  rw [← hessRelZ_comap (kappa0Cocycle base hbase) E E2
      (fun i ↦ graphSemiProdHom c
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) i)) phi
      (tameRelW (2 + 2 * h) q),
    ← hessRelZ_comap (kappa0Cocycle base hbase) E E2
      (fun i ↦ graphSemiProdHom c
        (gammaGen (2 + 2 * h) q (npcW alpha r h d) i)) phi
      (npcW alpha r h d),
    hmark, hoffsets,
    wPs_hessRelZ_tameRelW_hessMark_eq_zero base hbase _ _ _ E E2,
    zero_add,
    hessRelZ_npcW_evenTwistedNormal base hbase DD.hquad
      (Vmod_exp2 DD) h s u htauHeadOdd htauHeadFpf E E2 alpha r d
      raw.1 raw.2.1 raw.2.2 hresTarget]
  rw [hraw0, hraw1]
  simp_rw [hrawU, hrawV]
  dsimp only [d0, wPnpcWallHandlePhase, plusFormD]
  have hPhiInv : Phi (Phi.symm p.1.1) = p.1.1 := Phi.apply_symm_apply p.1.1
  rw [show (s ^ E d.toZhat)⁻¹ • Phi.symm p.1.1 = Phi (Phi.symm p.1.1) by rfl]
  rw [hPhiInv, polar_comm]

/-- The concrete ramified Npc source/word comparison at a faithful projected head. -/
noncomputable def wPnpcComparison_ramifiedHead
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
      letI : TopologicalSpace (ZMod 2) := ⊥
      letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
      letI : DistribMulAction
          ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
        scalarActionZmodTwo _
      Nat.card
        (H2 ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2)) = 2)
    (hwildHead : ∀ i : Fin (2 + 2 * h + 1), pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) (.wild i))) = 1)
    (htauHeadOdd : Odd (orderOf (pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau)))))
    (htauHeadFpf : ∀ v : DD.Vmod, pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau)) • v = v → v = 0) :
    let L := SectionSix.SemiProd DD.C0 DD.Vmod
    let E := npcResolver (4 * Monoid.exponent L) d
    let s := pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma))
    let u := pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau))
    let Phi := DistribMulAction.toAddEquiv DD.Vmod (s ^ E d.toZhat)⁻¹
    let d0 : DD.Vmod → ZMod 2 := fun a ↦
      npcRamifiedDiagonal base hbase s u E alpha r d (Phi.symm a)
    letI := scalarActionZmodTwo
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type)
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    IsQuadraticFp2 d0 ∧ Nonempty (SourceWordPhaseComparison DD rho
      (scalarActionZmodTwo_triv _)
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (wPnpcWallHandlePhase d0 DD.qbar h)) := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((displayedGamma alpha r h q d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  let N := 4 * Monoid.exponent L
  let E := npcResolver N d
  let s0 : DD.C0 := rho0 DD rho
    (gammaGen (2 + 2 * h) q (npcW alpha r h d) .sigma)
  let tau0 : DD.C0 := rho0 DD rho
    (gammaGen (2 + 2 * h) q (npcW alpha r h d) .tau)
  let t : Marking (2 + 2 * h) DD.C0 :=
    Marking.mk (fun i ↦ Count.rho0Continuous DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) i))
  let s := pi s0
  let u := pi tau0
  let g : DD.C0 := (s0 ^ E d.toZhat)⁻¹
  let b : DD.C0 := (s0 ^ ((2 : ℤ) ^ r))⁻¹
  let Phi := DistribMulAction.toAddEquiv DD.Vmod (s ^ E d.toZhat)⁻¹
  let d0 : DD.Vmod → ZMod 2 := fun a ↦
    npcRamifiedDiagonal base hbase s u E alpha r d (Phi.symm a)
  have ht : t.TameRelAt q := by
    let theta := Count.rho0Continuous DD rho
    have hrel := (isAdmissibleMarkedPresentation_gammaR
      (2 + 2 * h) q (npcW alpha r h d)).rel theta (0 : Fin 2)
    change PWord.eval ⇑t (tameRelW (2 + 2 * h) q) = 1 at hrel
    rw [← Marking.eval_def, Certificates.eval_tameRelW] at hrel
    exact mul_inv_eq_one.mp hrel
  have hbaseOrd : ∀ cc : DD.C0, orderOf cc ∣ Monoid.exponent L := by
    intro cc
    have hsd : Function.Surjective (sdSnd : L →* DD.C0) := by
      intro x
      exact ⟨((0, x) : L), rfl⟩
    exact (Monoid.order_dvd_exponent cc).trans (MonoidHom.exponent_dvd hsd)
  have horder : ∀ x : WordLift DD.Vmod DD.C0, orderOf x ∣ N := by
    intro x
    exact (WordLift.orderOf_dvd_two_mul hA2 hbaseOrd x).trans ⟨2, by ring⟩
  have hN : N ≠ 0 := fourMulExponent_ne_zero_and_even L |>.1
  have hres : ResolvesAt
      (gammaFam (2 + 2 * h) q (npcW alpha r h d))
      (resolvedFamily alpha r h q d N) (WordLift DD.Vmod DD.C0) :=
    resolvesAt_npcFamOf hN horder alpha r h q d (fun _ ↦ 0)
  have hresolver : MProcyclic.ResolverLifts E (WordLift DD.Vmod DD.C0) := by
    intro x
    simpa only [E, npcResolver_omega2, zpow_natCast] using
      (powOmega2_pow_eq x (horder x) hN)
  have hwildAct : ∀ (i : Fin (2 + 2 * h + 1)) (v : DD.Vmod), t.x i • v = v := by
    intro i v
    change rho0 DD rho
      (gammaGen (2 + 2 * h) q (npcW alpha r h d) (.wild i)) • v = v
    rw [hpi, hwildHead i, one_smul]
  have htauFpf : ∀ v : DD.Vmod, t.τ • v = v → v = 0 := by
    intro v hv
    apply htauHeadFpf v
    rw [← hpi]
    exact hv
  have hTodd : ∀ v : DD.Vmod, powOmega2 t.τ • v = v := by
    intro v
    change powOmega2 tau0 • v = v
    rw [hpi, powOmega2_map pi, powOmega2_eq_one_of_odd htauHeadOdd, one_smul]
  have hrow : IsTwoEntryRamifiedRow t (resolvedFamily alpha r h q d N) q g b DD.Vmod :=
    isTwoEntryRamifiedRow_npc_at t hA2 ht hwildAct htauFpf hTodd (by omega) hresolver
  have hr : ∀ k, FreeGroup.lift ⇑t
      (resolvedFamily alpha r h q d N k) = 1 := by
    let theta := Count.rho0Continuous DD rho
    intro k
    exact lower_rel (A := DD.Vmod) theta (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR
        (2 + 2 * h) q (npcW alpha r h d)) hres k
  have hd : IsQuadraticFp2 (npcRamifiedDiagonal base hbase s u E alpha r d) :=
    isQuadratic_npcRamifiedDiagonal base hbase DD.hquad hA2 s u E halpha d
      htauHeadOdd htauHeadFpf
  have hd0 : IsQuadraticFp2 d0 :=
    isQuadraticFp2_comp (npcRamifiedDiagonal base hbase s u E alpha r d) hd
      (⇑Phi.symm) (fun a b ↦ map_add Phi.symm a b) (map_zero Phi.symm)
  exact wPnpcPhaseComparison_of_twistedHeadPhase rho hcompat hres hA2 hwildTwo
    g b Phi hrow hwildAct htauFpf hr (scalarActionZmodTwo_triv _) d0 hd0
    (fun p c hc ↦
      wPnpc_QZero_eq_ramifiedWallHandlePhase_of_projectedTwistedMark
        rho base hbase pi hpi hf hm hphi halpha hqe hcardH2 c hwildHead
        htauHeadOdd htauHeadFpf p hc)

#print axioms wPnpc_QZero_eq_ramifiedWallHandlePhase_of_projectedTwistedMark
#print axioms wPnpcComparison_ramifiedHead

end
end GQ2.Dyadic.Instances.NpcRamifiedComparison

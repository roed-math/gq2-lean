/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcWordPhaseData
import GQ2.Dyadic.Instances.PlusFormLinearShift

/-!
# Procyclic-M word-phase data for the pp-one row

The unramified pp-one Hessian differs from the split plus form by one factor-set charge.
This module exposes that projected-head formula and a normal-form comparison carrying the
charge. The ramified branch is charge-free and reaches the common split plus form directly.
-/

namespace GQ2.Dyadic.Instances.MpcSqrtNegTenWordPhaseData

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Certificates GQ2.QuadraticFp2
open GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.MpcWordPhaseData
open GQ2.Dyadic.Instances.PlusFormLinearShift
open GQ2.Dyadic.MProcyclicExact
open GQ2.Dyadic.MProcyclicUnram
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.TameSpec
open GQ2.Dyadic.LSquare

theorem wPmpc_sqrtNegTen_cardH2 (q : ℕ) (hqe : Even q) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction
        ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo _
    Nat.card
      (H2 ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (ZMod 2)) = 2 := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  have hsimp : UniformHsimp 2 1 1 0 q .one :=
    RecordBlocks.recBl_mpc_uniformPushedHsimp
      (alpha := 2) (r := 1) (pp := 1) (h := 0) (q := q)
      (by omega) hqe MpcDisplayFor.one
  exact cardH2_of_uniformPushed
    (alpha := 2) (r := 1) (pp := 1) (h := 0) (q := q) (d := EtaDisplay.one)
    hsimp (by omega) (by omega) hqe

theorem wPmpc_QZero_eq_plusFormD_charge_of_projectedHeadMark
    {q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hqe : Even q)
    (hcardH2 :
      letI : TopologicalSpace (ZMod 2) := ⊥
      letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
      letI : DistribMulAction
          ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
        scalarActionZmodTwo _
      Nat.card
        (H2 ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (ZMod 2)) = 2)
    (c : VCocycle DD rho)
    (htauHead : pi (rho0 DD rho
      (gammaGen 2 q (mpcW 2 1 1 .one 0) .tau)) = 1)
    (hwildHead : ∀ i : Fin 3, pi (rho0 DD rho
      (gammaGen 2 q (mpcW 2 1 1 .one 0) (.wild i))) = 1)
    (hsigma2Head : ∀ v : DD.Vmod,
      (pi (rho0 DD rho (gammaGen 2 q (mpcW 2 1 1 .one 0) .sigma)) ^
        (omega2Exp
          (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : ℤ)) • v = v)
    (p : (DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod))
    (hc : (fun i ↦ c.c (gammaGen 2 q (mpcW 2 1 1 .one 0) i)) =
      wPmCompactPhaseNormal 0 p) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction
        ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo _
    letI : ContinuousSMul
        ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    QZero DD rho c = plusFormD DD.qbar DD.qbar p.1 +
      base.m
        (pi (rho0 DD rho (gammaGen 2 q (mpcW 2 1 1 .one 0) .sigma)) ^
          (omega2Exp
            (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : ℤ)) p.1.1 := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  let E : Zhat → ℤ := fun _ ↦ (omega2Exp (4 * Monoid.exponent L) : ℤ)
  let E₂ : ℤ_[2] → ℤ := fun _ ↦ (omega2Exp (4 * Monoid.exponent L) : ℤ)
  let phi := semiProdProjHom (V := DD.Vmod) pi hpi
  have hcval : ∀ i, c.c (gammaGen 2 q (mpcW 2 1 1 .one 0) i) =
      wPmCompactPhaseNormal 0 p i := fun i ↦ congrFun hc i
  have hmark :
      (fun i ↦ phi (graphSemiProdHom c (gammaGen 2 q (mpcW 2 1 1 .one 0) i))) =
        Certificates.hessMark (h := 0)
          (pi (rho0 DD rho (gammaGen 2 q (mpcW 2 1 1 .one 0) .sigma)))
          (1 : Cbar)
          (fun i : Fin 3 ↦ wPmCompactPhaseNormal 0 p (Generator.wild i)) := by
    funext i
    cases i with
    | sigma => exact Prod.ext ((hcval _).trans (wPmCompactPhaseNormal_sigma 0 p)) rfl
    | tau => exact Prod.ext ((hcval _).trans (wPmCompactPhaseNormal_tau 0 p)) htauHead
    | wild i => exact Prod.ext (hcval _) (hwildHead i)
  have hoffsets :
      (fun i : Fin 3 ↦ wPmCompactPhaseNormal 0 p (Generator.wild i)) =
        ![p.1.1, p.1.2, 0] := by
    funext i
    fin_cases i
    · change wPmCompactPhaseNormal 0 p (coreLetter 0 0) = p.1.1
      rw [wPmCompactPhaseNormal_coreLetter]
      rfl
    · change wPmCompactPhaseNormal 0 p (coreLetter 0 1) = p.1.2
      rw [wPmCompactPhaseNormal_coreLetter]
      rfl
    · change wPmCompactPhaseNormal 0 p (coreLetter 0 2) = 0
      rw [wPmCompactPhaseNormal_coreLetter]
      rfl
  have hresolved := wPmpc_resolvedAt_graph_one
    (alpha := 2) (r := 1) (pp := 1) (q := q)
    DD.dat DD.hdat (Vmod_exp2 DD)
    (fun i ↦ graphSemiProdHom c (gammaGen 2 q (mpcW 2 1 1 .one 0) i))
  rw [MpcWordPhaseSeam.wPmpc_QZero_eq_graphHessianTrace
      rho DD.hdat (by omega) hqe hcardH2 c E E₂ hresolved,
    kappa0Cocycle_comap_semiProdProjHom base hbase DD.dat DD.hdat pi hpi hf hm]
  rw [← hessRelZ_comap (kappa0Cocycle base hbase) E E₂
      (fun i ↦ graphSemiProdHom c (gammaGen 2 q (mpcW 2 1 1 .one 0) i)) phi
      (tameRelW 2 q),
    ← hessRelZ_comap (kappa0Cocycle base hbase) E E₂
      (fun i ↦ graphSemiProdHom c (gammaGen 2 q (mpcW 2 1 1 .one 0) i)) phi
      (mpcW 2 1 1 .one 0),
    hmark, hoffsets, WordPhaseSeam.wPs_hessRelZ_tameRelW_hessMark_eq_zero
      base hbase _ _ _ E E₂, zero_add,
    MpcUnramifiedHessian.hessRelZ_mpcW_unramified_zero
      base hbase (Vmod_exp2 DD) (by omega) 1 1 _ p.1.1 p.1.2 E E₂
      (by simpa [E] using hsigma2Head) rfl
      (omega2Exp_fourMulExponent_mod_four L), pow_one, plusFormD_apply]

noncomputable def wPmpcComparison_unramified_of_headPhase_charge
    {alpha r pp q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r pp 0 q .one : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((displayedGamma alpha r pp 0 q .one : ProfiniteGrp) : Type) DD.Vmod]
    [ContinuousSMul
      ((displayedGamma alpha r pp 0 q .one : ProfiniteGrp) : Type) DD.Vmod]
    [DistribMulAction
      ((displayedGamma alpha r pp 0 q .one : ProfiniteGrp) : Type) (ZMod 2)]
    [ContinuousSMul
      ((displayedGamma alpha r pp 0 q .one : ProfiniteGrp) : Type) (ZMod 2)]
    {Cbar : Type} [Group Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (g : Cbar)
    (htriv : ∀
      (gamma : ((displayedGamma alpha r pp 0 q .one : ProfiniteGrp) : Type))
      (a : ZMod 2), gamma • a = a)
    (hcompat : ∀
      (gamma : ((displayedGamma alpha r pp 0 q .one : ProfiniteGrp) : Type))
      (v : DD.Vmod), gamma • v = rho0 DD rho gamma • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet 2)
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen 2 q (mpcW alpha r pp .one 0) i)))
    (hα : 1 ≤ alpha) (hqe : Even q)
    (htauAct : ∀ v : DD.Vmod,
      rho0 DD rho (gammaGen 2 q (mpcW alpha r pp .one 0) .tau) • v = v)
    (hwildAct : ∀ (i : Fin 3) (v : DD.Vmod),
      rho0 DD rho (gammaGen 2 q (mpcW alpha r pp .one 0) (.wild i)) • v = v)
    (hsigmaFpf : ∀ v : DD.Vmod,
      rho0 DD rho (gammaGen 2 q (mpcW alpha r pp .one 0) .sigma) • v = v → v = 0)
    (hsigma2 : ∀ v : DD.Vmod,
      powOmega2 (rho0 DD rho
        (gammaGen 2 q (mpcW alpha r pp .one 0) .sigma)) • v = v)
    (hphase : ∀
      (p : (DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod))
      (c : VCocycle DD rho),
      (fun i ↦ c.c (gammaGen 2 q (mpcW alpha r pp .one 0) i)) =
          wPmCompactPhaseNormal 0 p →
      QZero DD rho c = plusFormD DD.qbar DD.qbar p.1 + base.m g p.1.1) :
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod)) :=
      inferInstance
    SourceWordPhaseComparison DD rho htriv
      ((DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod))
      (fun p ↦ plusFormD DD.qbar DD.qbar p.1 + base.m g p.1.1) := by
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod)) :=
    inferInstance
  let theta := Count.rho0Continuous DD rho
  let t : Marking 2 DD.C0 :=
    ⟨fun i ↦ theta (gammaGen 2 q (mpcW alpha r pp .one 0) i)⟩
  have hres : ResolvesAt (gammaFam 2 q (mpcW alpha r pp .one 0))
      (resolvedFamily alpha r pp 0 q .one (4 * Monoid.exponent DD.C0))
      (WordLift DD.Vmod DD.C0) := by
    exact wPmpc_resolvedFamily_resolves_wordLift hA2 hα hqe
  have hr : ∀ k, FreeGroup.lift ⇑t
      (resolvedFamily alpha r pp 0 q .one (4 * Monoid.exponent DD.C0) k) = 1 :=
    fun k ↦ Count.lower_rel (A := DD.Vmod) theta (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR 2 q (mpcW alpha r pp .one 0)) hres k
  exact wPmPhaseComparison_of_normalForm rho hcompat hres hA2 hwildTwo
    (wPmCompactPhaseNormal 0)
    (wPmpc_unramified_normal_closed t hA2 hα hqe hwildAct htauAct hsigma2)
    (wPmpc_unramified_normal_form t hA2 hα hqe hwildAct htauAct
      hsigmaFpf hsigma2 hr)
    htriv (fun p ↦ plusFormD DD.qbar DD.qbar p.1 + base.m g p.1.1) hphase

theorem hessRelZ_mpcW_ramified_zero_pp_one
    {C V : Type} [Group C] [Finite C] [AddCommGroup V] [Finite V]
    [DistribMulAction C V]
    {q0 : V → ZMod 2} (dat : FactorSet C V)
    (hdat : IsEquivariantFactorSet q0 dat)
    (hV2 : ∀ v : V, v + v = 0) (s u : C)
    (hu : Odd (orderOf u)) (hufpf : ∀ v : V, u • v = v → v = 0)
    (c0 c1 : V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hres : ResolverLifts E (WordCoh.CentExt (kappa0Cocycle dat hdat))) :
    hessRelZ (Certificates.hessMark (h := 0) s u ![c0, c1, 0])
        (kappa0Cocycle dat hdat) E E₂ (mpcW 2 1 1 .one 0) =
      plusFormD q0 q0 (c0, c1) := by
  have hv0 : ![c0, c1, 0] (Certificates.x0Idx 0) = c0 := rfl
  have hv1 : ![c0, c1, 0] (Certificates.x1Idx 0) = c1 := rfl
  have hmain :=
    GQ2.Dyadic.Certificates.MpcJet.hessRelZ_mpcW_handles_plusForm
      (h := 0) dat hdat s u ![c0, c1, 0] E E₂ hV2 hu hufpf rfl
      (α := 2) (by omega) 1 1 (η := EtaDisplay.one) (nη := 1)
      (MProcyclic.actsAsPow_etaOne_general E E₂ _) hres
  simpa only [Fin.sum_univ_zero, add_zero, hv0, hv1] using hmain

theorem hessRelZ_mpcW_ramified_zero_pp_one_of_surjective
    {L0 C V : Type} [Group L0] [Finite L0]
    [Group C] [Finite C] [AddCommGroup V] [Finite V] [DistribMulAction C V]
    {q0 : V → ZMod 2} (dat : FactorSet C V)
    (hdat : IsEquivariantFactorSet q0 dat)
    (phi : L0 →* SectionSix.SemiProd C V) (hphi : Function.Surjective phi)
    (hV2 : ∀ v : V, v + v = 0) (s u : C)
    (hu : Odd (orderOf u)) (hufpf : ∀ v : V, u • v = v → v = 0)
    (c0 c1 : V) :
    hessRelZ (Certificates.hessMark (h := 0) s u ![c0, c1, 0])
        (kappa0Cocycle dat hdat)
        (fun _ ↦ ((omega2Exp (4 * Monoid.exponent L0) : ℕ) : ℤ))
        (fun _ ↦ ((omega2Exp (4 * Monoid.exponent L0) : ℕ) : ℤ))
        (mpcW 2 1 1 .one 0) =
      plusFormD q0 q0 (c0, c1) := by
  have hkappa : ResolverLifts
      (fun _ ↦ ((omega2Exp (4 * Monoid.exponent L0) : ℕ) : ℤ))
      (WordCoh.CentExt (kappa0Cocycle dat hdat)) :=
    kappaResolverLifts_of_surjective dat hdat phi hphi
  exact hessRelZ_mpcW_ramified_zero_pp_one
    dat hdat hV2 s u hu hufpf c0 c1 _ _ hkappa

theorem wPmpc_QZero_eq_plusFormD_pp_one_of_ramifiedProjectedHeadMark
    {q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hphi : Function.Surjective (semiProdProjHom (V := DD.Vmod) pi hpi))
    (hqe : Even q)
    (hcardH2 :
      letI : TopologicalSpace (ZMod 2) := ⊥
      letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
      letI : DistribMulAction
          ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
        scalarActionZmodTwo _
      Nat.card
        (H2 ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (ZMod 2)) = 2)
    (c : VCocycle DD rho)
    (hwildHead : ∀ i : Fin 3, pi (rho0 DD rho
      (gammaGen 2 q (mpcW 2 1 1 .one 0) (.wild i))) = 1)
    (htauHeadOdd : Odd (orderOf (pi (rho0 DD rho
      (gammaGen 2 q (mpcW 2 1 1 .one 0) .tau)))))
    (htauHeadFpf : ∀ v : DD.Vmod, pi (rho0 DD rho
      (gammaGen 2 q (mpcW 2 1 1 .one 0) .tau)) • v = v → v = 0)
    (p : (DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod))
    (hc : (fun i ↦ c.c (gammaGen 2 q (mpcW 2 1 1 .one 0) i)) =
      wPmCompactPhaseNormal 0 p) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction
        ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo _
    letI : ContinuousSMul
        ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    QZero DD rho c = plusFormD DD.qbar DD.qbar p.1 := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  let E : Zhat → ℤ := fun _ ↦ (omega2Exp (4 * Monoid.exponent L) : ℤ)
  let E₂ : ℤ_[2] → ℤ := fun _ ↦ (omega2Exp (4 * Monoid.exponent L) : ℤ)
  let phi := semiProdProjHom (V := DD.Vmod) pi hpi
  have hcval : ∀ i, c.c (gammaGen 2 q (mpcW 2 1 1 .one 0) i) =
      wPmCompactPhaseNormal 0 p i := fun i ↦ congrFun hc i
  have hoffsets :
      (fun i : Fin 3 ↦ wPmCompactPhaseNormal 0 p (Generator.wild i)) =
        ![p.1.1, p.1.2, 0] := by
    funext i
    fin_cases i
    · change wPmCompactPhaseNormal 0 p (coreLetter 0 0) = p.1.1
      rw [wPmCompactPhaseNormal_coreLetter]
      rfl
    · change wPmCompactPhaseNormal 0 p (coreLetter 0 1) = p.1.2
      rw [wPmCompactPhaseNormal_coreLetter]
      rfl
    · change wPmCompactPhaseNormal 0 p (coreLetter 0 2) = 0
      rw [wPmCompactPhaseNormal_coreLetter]
      rfl
  have hmark :
      (fun i ↦ phi (graphSemiProdHom c (gammaGen 2 q (mpcW 2 1 1 .one 0) i))) =
        Certificates.hessMark (h := 0)
          (pi (rho0 DD rho (gammaGen 2 q (mpcW 2 1 1 .one 0) .sigma)))
          (pi (rho0 DD rho (gammaGen 2 q (mpcW 2 1 1 .one 0) .tau)))
          ![p.1.1, p.1.2, 0] := by
    rw [← hoffsets]
    funext i
    cases i with
    | sigma => exact Prod.ext ((hcval _).trans (wPmCompactPhaseNormal_sigma 0 p)) rfl
    | tau => exact Prod.ext ((hcval _).trans (wPmCompactPhaseNormal_tau 0 p)) rfl
    | wild i => exact Prod.ext (hcval _) (hwildHead i)
  have hresolved := wPmpc_resolvedAt_graph_one
    (alpha := 2) (r := 1) (pp := 1) (q := q)
    DD.dat DD.hdat (Vmod_exp2 DD)
    (fun i ↦ graphSemiProdHom c (gammaGen 2 q (mpcW 2 1 1 .one 0) i))
  rw [MpcWordPhaseSeam.wPmpc_QZero_eq_graphHessianTrace
      rho DD.hdat (by omega) hqe hcardH2 c E E₂ hresolved,
    kappa0Cocycle_comap_semiProdProjHom base hbase DD.dat DD.hdat pi hpi hf hm]
  rw [← hessRelZ_comap (kappa0Cocycle base hbase) E E₂
      (fun i ↦ graphSemiProdHom c (gammaGen 2 q (mpcW 2 1 1 .one 0) i)) phi
      (tameRelW 2 q),
    ← hessRelZ_comap (kappa0Cocycle base hbase) E E₂
      (fun i ↦ graphSemiProdHom c (gammaGen 2 q (mpcW 2 1 1 .one 0) i)) phi
      (mpcW 2 1 1 .one 0),
    hmark, WordPhaseSeam.wPs_hessRelZ_tameRelW_hessMark_eq_zero
      base hbase _ _ _ E E₂, zero_add]
  exact hessRelZ_mpcW_ramified_zero_pp_one_of_surjective base hbase phi hphi
    (Vmod_exp2 DD)
    (pi (rho0 DD rho (gammaGen 2 q (mpcW 2 1 1 .one 0) .sigma)))
    (pi (rho0 DD rho (gammaGen 2 q (mpcW 2 1 1 .one 0) .tau)))
    htauHeadOdd htauHeadFpf p.1.1 p.1.2

theorem wPmpc_resolvedFamily_ramified_row_pp_one
    {q : ℕ} {C V : Type} [Group C] [Finite C]
    [AddCommGroup V] [Finite V] [DistribMulAction C V]
    (t : Marking 2 C) (hV2 : ∀ v : V, v + v = 0)
    (htame : t.TameRelAt q)
    (hwild : ∀ (i : Fin 3) (v : V), t.x i • v = v)
    (htauFpf : ∀ v : V, t.τ • v = v → v = 0)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    ∀ x : Generator 2 → V,
      heisD1 ⇑t (resolvedFamily 2 1 1 0 q .one
        (4 * Monoid.exponent C)) x =
        ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
            - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
          ((powOmega2 t.σ) ^ (-(s 1 : ℤ)) * t.σ ^ (-(1 : ℤ))) •
            x (coreLetter 0 2)] := by
  let e := omega2Exp (4 * Monoid.exponent C)
  let E : Zhat → ℤ := fun _ ↦ (e : ℤ)
  let E₂ : ℤ_[2] → ℤ := fun _ ↦ (e : ℤ)
  have hfam : resolvedFamily 2 1 1 0 q .one (4 * Monoid.exponent C) =
      mpcFamOf 2 1 1 0 q .one E E₂ := by
    exact (mpcFamOf_const 2 1 1 0 q e .one).symm
  have hlift : ResolverLifts E (WordLift V C) := by
    exact resolverLifts_uniformWordLift_ramified hV2
  have heta : PWord.evalFin ⇑t E E₂
      (EtaDisplay.one.toPWord (n := 2)) = t.σ ^ (1 : ℤ) := by
    rw [zpow_one]
    rfl
  rw [hfam]
  intro x
  exact heisD1_mpcFamOf_ramified_apply
    (alpha := 2) (r := 1) (pp := 1) (h := 0) (q := q)
    (η := EtaDisplay.one) (nη := 1) t E E₂ hlift hV2 (by omega)
    htame hwild htauFpf hTodd heta x

theorem wPmpc_marking_tameRel_pp_one
    {q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0] :
    let t : Marking 2 DD.C0 :=
      ⟨fun i ↦ Count.rho0Continuous DD rho
        (gammaGen 2 q (mpcW 2 1 1 .one 0) i)⟩
    t.TameRelAt q := by
  let theta := Count.rho0Continuous DD rho
  let t : Marking 2 DD.C0 :=
    ⟨fun i ↦ theta (gammaGen 2 q (mpcW 2 1 1 .one 0) i)⟩
  have hrel := (isAdmissibleMarkedPresentation_gammaR
    2 q (mpcW 2 1 1 .one 0)).rel theta (0 : Fin 2)
  change PWord.eval ⇑t (tameRelW 2 q) = 1 at hrel
  rw [← Marking.eval_def, Certificates.eval_tameRelW] at hrel
  exact mul_inv_eq_one.mp hrel

noncomputable def wPmpcComparison_ramified_pp_one_of_headPhase
    {q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) DD.Vmod]
    [ContinuousSMul
      ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) DD.Vmod]
    [DistribMulAction
      ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (ZMod 2)]
    [ContinuousSMul
      ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (ZMod 2)]
    (htriv : ∀
      (g : ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type))
      (a : ZMod 2), g • a = a)
    (hcompat : ∀
      (g : ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type))
      (v : DD.Vmod), g • v = rho0 DD rho g • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet 2)
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen 2 q (mpcW 2 1 1 .one 0) i)))
    (hqe : Even q)
    (hwildAct : ∀ (i : Fin 3) (v : DD.Vmod),
      rho0 DD rho (gammaGen 2 q (mpcW 2 1 1 .one 0) (.wild i)) • v = v)
    (htauFpf : ∀ v : DD.Vmod,
      rho0 DD rho (gammaGen 2 q (mpcW 2 1 1 .one 0) .tau) • v = v → v = 0)
    (hTodd : ∀ v : DD.Vmod, powOmega2 (rho0 DD rho
      (gammaGen 2 q (mpcW 2 1 1 .one 0) .tau)) • v = v)
    (hphase : ∀
      (p : (DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod))
      (c : VCocycle DD rho),
      (fun i ↦ c.c (gammaGen 2 q (mpcW 2 1 1 .one 0) i)) =
          wPmCompactPhaseNormal 0 p →
      QZero DD rho c = plusFormD DD.qbar DD.qbar p.1) :
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod)) :=
      inferInstance
    SourceWordPhaseComparison DD rho htriv
      ((DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod))
      (fun p ↦ plusFormD DD.qbar DD.qbar p.1) := by
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod)) :=
    inferInstance
  let theta := Count.rho0Continuous DD rho
  let t : Marking 2 DD.C0 :=
    ⟨fun i ↦ theta (gammaGen 2 q (mpcW 2 1 1 .one 0) i)⟩
  have hres : ResolvesAt (gammaFam 2 q (mpcW 2 1 1 .one 0))
      (resolvedFamily 2 1 1 0 q .one (4 * Monoid.exponent DD.C0))
      (WordLift DD.Vmod DD.C0) :=
    wPmpc_resolvedFamily_resolves_wordLift hA2 (by omega) hqe
  have htame : t.TameRelAt q := wPmpc_marking_tameRel_pp_one rho
  let u : DD.C0 := (powOmega2 t.σ) ^ (-(s 1 : ℤ)) * t.σ ^ (-(1 : ℤ))
  have hrow : ∀ x : Generator 2 → DD.Vmod,
      heisD1 ⇑t (resolvedFamily 2 1 1 0 q .one
        (4 * Monoid.exponent DD.C0)) x =
        ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
            - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
          u • x (coreLetter 0 2)] :=
    wPmpc_resolvedFamily_ramified_row_pp_one t hA2 htame hwildAct htauFpf hTodd
  have hr : ∀ k, FreeGroup.lift ⇑t
      (resolvedFamily 2 1 1 0 q .one (4 * Monoid.exponent DD.C0) k) = 1 :=
    fun k ↦ Count.lower_rel (A := DD.Vmod) theta (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR 2 q (mpcW 2 1 1 .one 0)) hres k
  exact wPmPhaseComparison_of_normalForm rho hcompat hres hA2 hwildTwo
    (wPmCompactPhaseNormal 0)
    (wPmpc_compactNormal_closed_of_smul_row t _ u hrow)
    (wPmpc_compactNormalForm_of_smul_row t _ u hrow hwildAct htauFpf hr)
    htriv (fun p ↦ plusFormD DD.qbar DD.qbar p.1) hphase

/-! ## Axiom audit -/

#print axioms wPmpc_sqrtNegTen_cardH2
#print axioms wPmpc_QZero_eq_plusFormD_charge_of_projectedHeadMark
#print axioms wPmpcComparison_unramified_of_headPhase_charge
#print axioms hessRelZ_mpcW_ramified_zero_pp_one
#print axioms hessRelZ_mpcW_ramified_zero_pp_one_of_surjective
#print axioms wPmpc_QZero_eq_plusFormD_pp_one_of_ramifiedProjectedHeadMark
#print axioms wPmpc_resolvedFamily_ramified_row_pp_one
#print axioms wPmpc_marking_tameRel_pp_one
#print axioms wPmpcComparison_ramified_pp_one_of_headPhase

end

end GQ2.Dyadic.Instances.MpcSqrtNegTenWordPhaseData

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcUnramifiedProjectedData
import GQ2.Dyadic.Instances.MpcUnramifiedHandleComparison

/-!
# Projected unramified procyclic-M comparison

The display-dependent graph resolver descends through the projected semidirect product, while
the exact source resolved-family pivot projects to the odd fixed-point-free head sigma. Hence the
arbitrary-display unramified branch reaches the common uncharged compact wall-handle phase with
no exposed resolver, pivot, or factor-set-charge premise.
-/

namespace GQ2.Dyadic.Instances.MpcUnramifiedProjectedComparison

noncomputable section

open GQ2 GQ2.SectionSix GQ2.FoxH GQ2.QuadraticFp2
open GQ2.SectionEight SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Count GQ2.Dyadic.LSquare
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.MProcyclicExact
open GQ2.Dyadic.Instances.MpcWordPhaseSeam
open GQ2.Dyadic.Instances.MpcUnramifiedHandleHessian
open GQ2.Dyadic.Instances.MpcUnramifiedHandleComparison
open GQ2.Dyadic.Instances.MpcUnramifiedProjectedData
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseModel

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-- The projected graph trace is the uncharged compact wall-handle phase on an odd head. -/
theorem wPmpc_QZero_eq_unramifiedCompactPhase_of_projectedHeadMark
    {alpha r pp h qrel : ℕ} {d : EtaDisplay}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [TopologicalSpace Cbar]
    [DiscreteTopology Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar)
    (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hphi : Function.Surjective (semiProdProjHom (V := DD.Vmod) pi hpi))
    (halpha : 2 ≤ alpha) (hqrel : Even qrel)
    (hcardH2 :
      letI : TopologicalSpace (ZMod 2) := ⊥
      letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
      letI : DistribMulAction
          ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (ZMod 2) :=
        scalarActionZmodTwo _
      Nat.card
        (H2 ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (ZMod 2)) = 2)
    (c : VCocycle DD rho)
    (htauHead : pi (rho0 DD rho
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) .tau)) = 1)
    (hwildHead : ∀ i : Fin (2 + 2 * h + 1), pi (rho0 DD rho
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) (.wild i))) = 1)
    (hsigmaHeadOdd : Odd (orderOf (pi (rho0 DD rho
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) .sigma)))))
    (p : (DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
    (hc : (fun i ↦ c.c
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) i)) =
        wPmCompactPhaseNormal h p) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction
        ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo _
    letI : ContinuousSMul
        ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    QZero DD rho c = wPhCompactWallHandlePhase DD.qbar h p := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  let N := 4 * Monoid.exponent L
  let E := resolvedE N d
  let E2 := resolvedE2 N d
  let phi := semiProdProjHom (V := DD.Vmod) pi hpi
  let K := WordCoh.CentExt (kappa0Cocycle DD.dat DD.hdat)
  letI : Finite K := inferInstance
  letI : TopologicalSpace K := ⊥
  letI : DiscreteTopology K := ⟨rfl⟩
  have hN : N ≠ 0 := (fourMulExponent_ne_zero_and_even L).1
  have hordK : ∀ y : K, orderOf y ∣ N := by
    intro y
    have hbasePow : y.base ^ Monoid.exponent L = 1 :=
      Monoid.pow_exponent_eq_one y.base
    exact (nc3_orderOf_dvd_two_mul DD.dat DD.hdat hbasePow).trans ⟨2, by ring⟩
  have homega : ∀ y : K, y ^ᶻ omega2 = y ^ E omega2 := by
    intro y
    cases d with
    | one => exact PWord.zpowHat_omega2_zpow hN (hordK y)
    | lit k => exact PWord.zpowHat_omega2_zpow hN (hordK y)
    | hat num den =>
        rw [show E = npcResolver N ⟨num, den⟩ from rfl, npcResolver_omega2,
          PWord.zpowHat_omega2_zpow hN (hordK y), zpow_natCast]
  have hresolved : ∀ k, PWord.ResolvedAt
      (WordCoh.lift
        (fun i ↦ graphSemiProdHom c
          (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) i))
        (kappa0Cocycle DD.dat DD.hdat)) E E2
      (gammaFam (2 + 2 * h) qrel (mpcW alpha r pp d h) k) := by
    intro k
    fin_cases k
    · exact PWord.resolvedAt_of_isOmega2Only _ E E2 homega _
        (isOmega2Only_tameRelW (2 + 2 * h) qrel)
    · cases d with
      | one =>
          exact PWord.resolvedAt_of_isOmega2Only _ E E2 homega _
            (isOmega2Only_mpcW alpha r pp
              (show EtaDisplay.IsOmega2Only .one from trivial) h)
      | lit z =>
          exact PWord.resolvedAt_of_isOmega2Only _ E E2 homega _
            (isOmega2Only_mpcW alpha r pp
              (show EtaDisplay.IsOmega2Only (.lit z) from trivial) h)
      | hat num den =>
          have heta : ∀ y : K,
              y ^ᶻ (EtaDisplay.hat num den).zhat =
                y ^ E (EtaDisplay.hat num den).zhat := by
            intro y
            rw [show (EtaDisplay.hat num den).zhat =
                EtaData.toZhat ⟨num, den⟩ from rfl,
              show E = npcResolver N ⟨num, den⟩ from rfl,
              npcResolver_toZhat, EtaData.toZhat,
              Count.zpowHat_etaHatZ_zpow hN (hordK y), zpow_natCast]
          exact Count.resolvedAt_mpcW _ homega heta alpha r pp
  have hresSource : ResolverLifts E (WordCoh.CentExt
      (kappa0Cocycle DD.dat DD.hdat)) := by
    intro y
    cases d with
    | one =>
        change y ^ (omega2Exp N : ℤ) = powOmega2 y
        rw [zpow_natCast]
        exact powOmega2_pow_eq y (hordK y) hN
    | lit z =>
        change y ^ (omega2Exp N : ℤ) = powOmega2 y
        rw [zpow_natCast]
        exact powOmega2_pow_eq y (hordK y) hN
    | hat num den =>
        rw [show E = npcResolver N ⟨num, den⟩ from rfl,
          npcResolver_omega2, zpow_natCast]
        exact powOmega2_pow_eq y (hordK y) hN
  have hcoc : (kappa0Cocycle base hbase).comap phi =
      kappa0Cocycle DD.dat DD.hdat :=
    (kappa0Cocycle_comap_semiProdProjHom
      base hbase DD.dat DD.hdat pi hpi hf hm).symm
  have hresComap : ResolverLifts E
      (WordCoh.CentExt ((kappa0Cocycle base hbase).comap phi)) := by
    rw [hcoc]
    exact hresSource
  have hresTarget : ResolverLifts E
      (WordCoh.CentExt (kappa0Cocycle base hbase)) :=
    resolverLifts_comap_target_of_surjective
      (kappa0Cocycle base hbase) phi hphi E hresComap
  have hcval : ∀ i, c.c
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) i) =
        wPmCompactPhaseNormal h p i := fun i ↦ congrFun hc i
  let s := pi (rho0 DD rho
    (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) .sigma))
  have hmark :
      (fun i ↦ phi (graphSemiProdHom c
        (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) i))) =
        Certificates.hessMark (h := h) s 1
          (fun i : Fin (2 + 2 * h + 1) ↦
            wPmCompactPhaseNormal h p (Generator.wild i)) := by
    funext i
    cases i with
    | sigma => exact Prod.ext ((hcval _).trans (wPmCompactPhaseNormal_sigma h p)) rfl
    | tau => exact Prod.ext ((hcval _).trans (wPmCompactPhaseNormal_tau h p)) htauHead
    | wild i => exact Prod.ext (hcval _) (hwildHead i)
  have hsodd : Odd (orderOf s) := hsigmaHeadOdd
  let e := omega2Exp N
  have hE : E omega2 = (e : ℤ) := by
    cases d with
    | one => rfl
    | lit z => rfl
    | hat num den => exact npcResolver_omega2 N ⟨num, den⟩
  have he : e % 4 = 1 := omega2Exp_fourMulExponent_mod_four L
  have hordS : orderOf s ∣ N := by
    obtain ⟨x, hx⟩ := hphi ((0, s) : SectionSix.SemiProd Cbar DD.Vmod)
    have hsnd : (phi x).2 = s := congrArg Prod.snd hx
    rw [← hsnd]
    exact (orderOf_map_dvd
      (sdSnd : SectionSix.SemiProd Cbar DD.Vmod →* Cbar) (phi x)).trans
        ((orderOf_map_dvd phi x).trans
          ((Monoid.order_dvd_exponent x).trans ⟨4, by simp [N, L, mul_comm]⟩))
  have hS2 : ∀ v : DD.Vmod, (s ^ E omega2) • v = v := by
    intro v
    rw [hE, zpow_natCast, powOmega2_pow_eq s hordS hN,
      powOmega2_eq_one_of_odd hsodd, one_smul]
  rw [wPmpc_QZero_eq_graphHessianTrace rho DD.hdat (by omega) hqrel
      hcardH2 c E E2 hresolved,
    kappa0Cocycle_comap_semiProdProjHom base hbase DD.dat DD.hdat pi hpi hf hm]
  rw [← hessRelZ_comap (kappa0Cocycle base hbase) E E2
      (fun i ↦ graphSemiProdHom c
        (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) i)) phi
      (tameRelW (2 + 2 * h) qrel),
    ← hessRelZ_comap (kappa0Cocycle base hbase) E E2
      (fun i ↦ graphSemiProdHom c
        (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) i)) phi
      (mpcW alpha r pp d h),
    hmark,
    GQ2.Dyadic.Instances.WordPhaseSeam.wPs_hessRelZ_tameRelW_hessMark_eq_zero
      base hbase s 1 _ E E2,
    zero_add,
    hessRelZ_mpcW_unramified_compactPhase base hbase s E E2
      (Vmod_exp2 DD) halpha r pp d p hS2 hE he]
  rw [hE, zpow_natCast, powOmega2_pow_eq s hordS hN,
    powOmega2_eq_one_of_odd hsodd, one_pow, hbase.m_one, add_zero]

/-- The honest projected unramified head supplies the common compact wall-handle comparison. -/
theorem exists_comparison_unramified_of_projectedHead_handles
    {alpha r pp h qrel : ℕ} {d : EtaDisplay} {eta : ℤ_[2]ˣ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod]
    [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) DD.Vmod]
    [ContinuousSMul
      ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) DD.Vmod]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [TopologicalSpace Cbar]
    [DiscreteTopology Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar)
    (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hphi : Function.Surjective (semiProdProjHom (V := DD.Vmod) pi hpi))
    (hcompat : ∀
      (x : ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type))
      (v : DD.Vmod), x • v = rho0 DD rho x • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) i)))
    (hd : d.RepresentsUnit eta) (halpha : 2 ≤ alpha) (hqrel : Even qrel)
    (hcardH2 :
      letI : TopologicalSpace (ZMod 2) := ⊥
      letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
      letI : DistribMulAction
          ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (ZMod 2) :=
        scalarActionZmodTwo _
      Nat.card
        (H2 ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (ZMod 2)) = 2)
    (htauHead : pi (rho0 DD rho
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) .tau)) = 1)
    (hwildHead : ∀ i : Fin (2 + 2 * h + 1), pi (rho0 DD rho
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) (.wild i))) = 1)
    (hsigmaHeadOdd : Odd (orderOf (pi (rho0 DD rho
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) .sigma)))))
    (hsigmaHeadFpf : ∀ v : DD.Vmod, pi (rho0 DD rho
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) .sigma)) • v = v → v = 0)
    (hquad : IsQuadraticFp2 DD.qbar) (hns : Nonsingular DD.qbar) :
    letI := scalarActionZmodTwo
      ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type)
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    Nonempty (SourceWordPhaseComparison DD rho (scalarActionZmodTwo_triv _)
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (wPhCompactWallHandlePhase DD.qbar h)) := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  let t : Marking (2 + 2 * h) DD.C0 :=
    ⟨fun i ↦ Count.rho0Continuous DD rho
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) i)⟩
  have htauAct : ∀ v : DD.Vmod, t.τ • v = v := by
    intro v
    change rho0 DD rho
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) .tau) • v = v
    rw [hpi, htauHead, one_smul]
  have hwildAct : ∀ (i : Fin (2 + 2 * h + 1)) (v : DD.Vmod),
      t.x i • v = v := by
    intro i v
    change rho0 DD rho
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) (.wild i)) • v = v
    rw [hpi, hwildHead i, one_smul]
  have hsigmaFpf : ∀ v : DD.Vmod, t.σ • v = v → v = 0 := by
    intro v hv
    apply hsigmaHeadFpf v
    rw [← hpi]
    change rho0 DD rho
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) .sigma) • v = v
      at hv
    exact hv
  have hsigma2 : ∀ v : DD.Vmod, powOmega2 t.σ • v = v := by
    intro v
    change powOmega2 (rho0 DD rho
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) .sigma)) • v = v
    rw [hpi, powOmega2_map pi, powOmega2_eq_one_of_odd hsigmaHeadOdd, one_smul]
  have hsigmaOdd' : Odd (orderOf (pi t.σ)) := by
    change Odd (orderOf (pi (rho0 DD rho
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) .sigma))))
    exact hsigmaHeadOdd
  have hsigmaFpf' : ∀ v : DD.Vmod, pi t.σ • v = v → v = 0 := by
    change ∀ v : DD.Vmod, pi (rho0 DD rho
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) .sigma)) • v = v → v = 0
    exact hsigmaHeadFpf
  have halpha1 : 1 ≤ alpha := le_trans (by omega : 1 ≤ 2) halpha
  obtain ⟨u, hrow, huFpf⟩ :=
    exists_resolvedFamily_unramified_smul_row_fpf_of_projected
      t pi hpi hd hA2 halpha1 hqrel hwildAct htauAct hsigma2
        hsigmaOdd' hsigmaFpf'
  exact exists_comparison_unramified_of_headPhase_handles rho
    (scalarActionZmodTwo_triv _) hcompat hA2 hwildTwo (by omega) hqrel
    hwildAct htauAct hsigmaFpf u hrow huFpf 1 (fun v ↦ one_smul _ v)
    hquad hns (fun p c hc ↦ by
      rw [wPmpc_QZero_eq_unramifiedCompactPhase_of_projectedHeadMark
        rho base hbase pi hpi hf hm hphi halpha hqrel hcardH2
        c htauHead hwildHead hsigmaHeadOdd p hc,
        DD.hdat.m_one, add_zero])

#print axioms wPmpc_QZero_eq_unramifiedCompactPhase_of_projectedHeadMark
#print axioms exists_comparison_unramified_of_projectedHead_handles

end
end GQ2.Dyadic.Instances.MpcUnramifiedProjectedComparison

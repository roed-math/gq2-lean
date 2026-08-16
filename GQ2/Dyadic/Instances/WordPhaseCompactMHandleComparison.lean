/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhaseCompactMHandleData
import GQ2.Dyadic.Instances.WordPhaseCompactMData

/-!
# Compact-M comparisons with handles

This file transports the arbitrary-h compact-M phase calculations through projected head
quotients and assembles the unramified and honest ramified Fox normal forms.  Both exported
comparisons use the common wall-handle endpoint; the ramified branch reaches it by swapping
only the two head coordinates.
-/

namespace GQ2.Dyadic.Instances.WordPhaseCompactMHandleComparison

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words
open GQ2.Dyadic.Certificates GQ2.QuadraticFp2
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.WordPhaseSeam
open GQ2.Dyadic.Instances.WordPhaseCompactMData
open GQ2.Dyadic.Instances.WordPhaseCompactMHandleData
open GQ2.Dyadic.Instances.WordPhaseCompactNData
open GQ2.Dyadic.LSquare

/-- The arbitrary-h ramified graph trace after transport through a projected head. -/
theorem wPcM_QZero_eq_ramifiedHandlePhase_of_projectedHeadMark
    {alpha h q : Nat}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hq : Even q) (hq0 : q ≠ 0) (halpha : 2 ≤ alpha) (c : VCocycle DD rho)
    (hwildHead : ∀ i : Fin (2 + 2 * h + 1), pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) (.wild i))) = 1)
    (htauOdd : Odd (orderOf (pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .tau)))))
    (htauFpf : ∀ v : DD.Vmod, pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .tau)) • v = v → v = 0)
    (hres : MProcyclic.ResolverLifts
      (fun _ ↦ (omega2Exp
        (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : Int))
      (WordCoh.CentExt (kappa0Cocycle base hbase)))
    (p : (DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
    (hc : (fun i ↦ c.c
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) i)) =
        wPmCompactPhaseNormal h p) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction
        ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
        (ZMod 2) := scalarActionZmodTwo _
    letI : ContinuousSMul
        ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
        (ZMod 2) := scalarActionZmodTwo_continuousSMul _
    QZero DD rho c = wPcMRamifiedHandlePhase DD.qbar h p := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      (ZMod 2) := scalarActionZmodTwo_continuousSMul _
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  set E : Zhat → Int := fun _ ↦ (omega2Exp (4 * Monoid.exponent L) : Int)
  set E2 : ℤ_[2] → Int := fun _ ↦ (omega2Exp (4 * Monoid.exponent L) : Int)
  set phi := semiProdProjHom (V := DD.Vmod) pi hpi
  have hcval : ∀ i, c.c
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) i) =
        wPmCompactPhaseNormal h p i := fun i ↦ congrFun hc i
  have hmark :
      (fun i ↦ phi (graphSemiProdHom c
        (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) i))) =
        Certificates.hessMark (h := h)
          (pi (rho0 DD rho
            (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .sigma)))
          (pi (rho0 DD rho
            (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .tau)))
          (fun i : Fin (2 + 2 * h + 1) ↦
            wPmCompactPhaseNormal h p (Generator.wild i)) := by
    funext i
    cases i with
    | sigma => exact Prod.ext ((hcval _).trans (wPmCompactPhaseNormal_sigma h p)) rfl
    | tau => exact Prod.ext ((hcval _).trans (wPmCompactPhaseNormal_tau h p)) rfl
    | wild i => exact Prod.ext (hcval _) (hwildHead i)
  rw [wPs_QZero_eq_mCompact_graphHessianTrace
      (α := alpha) (h := h) (q := q) rho DD.hdat hq hq0 halpha c,
    kappa0Cocycle_comap_semiProdProjHom base hbase DD.dat DD.hdat pi hpi hf hm]
  rw [show (fun _ : Zhat ↦
      (omega2Exp (4 * Monoid.exponent L) : Int)) = E from rfl,
    show (fun _ : ℤ_[2] ↦
      (omega2Exp (4 * Monoid.exponent L) : Int)) = E2 from rfl,
    ← hessRelZ_comap (kappa0Cocycle base hbase) E E2
      (fun i ↦ graphSemiProdHom c
        (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) i)) phi
      (tameRelW (2 + 2 * h) q),
    ← hessRelZ_comap (kappa0Cocycle base hbase) E E2
      (fun i ↦ graphSemiProdHom c
        (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) i)) phi
      (MCompact.mCompactW alpha h),
    hmark, wPs_hessRelZ_tameRelW_hessMark_eq_zero base hbase _ _ _ E E2,
    zero_add,
    wPcM_hessRelZ_eq_ramifiedHandlePhase base hbase (Vmod_exp2 DD)
      (s := pi (rho0 DD rho
        (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .sigma)))
      (u := pi (rho0 DD rho
        (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .tau)))
      htauOdd htauFpf p E E2 (by simpa only [E, L] using hres)]

/-- The projected ramified graph trace with resolver transport supplied by surjectivity. -/
theorem wPcM_QZero_eq_ramifiedHandlePhase_of_surjectiveHeadMark
    {alpha h q : Nat}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hphi : Function.Surjective (semiProdProjHom (V := DD.Vmod) pi hpi))
    (hq : Even q) (hq0 : q ≠ 0) (halpha : 2 ≤ alpha) (c : VCocycle DD rho)
    (hwildHead : ∀ i : Fin (2 + 2 * h + 1), pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) (.wild i))) = 1)
    (htauOdd : Odd (orderOf (pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .tau)))))
    (htauFpf : ∀ v : DD.Vmod, pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .tau)) • v = v → v = 0)
    (p : (DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
    (hc : (fun i ↦ c.c
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) i)) =
        wPmCompactPhaseNormal h p) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction
        ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
        (ZMod 2) := scalarActionZmodTwo _
    letI : ContinuousSMul
        ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
        (ZMod 2) := scalarActionZmodTwo_continuousSMul _
    QZero DD rho c = wPcMRamifiedHandlePhase DD.qbar h p :=
  wPcM_QZero_eq_ramifiedHandlePhase_of_projectedHeadMark rho base hbase pi hpi
    hf hm hq hq0 halpha c hwildHead htauOdd htauFpf
      (kappaResolverLifts_of_surjective base hbase
        (semiProdProjHom (V := DD.Vmod) pi hpi) hphi) p hc

/-- The arbitrary-h unramified projected-head graph trace. -/
theorem wPcM_QZero_eq_compactWallPhase_P1_handles_of_headMark
    {alpha h q : Nat}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    {Cbar : Type} [Group Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hq : Even q) (hq0 : q ≠ 0) (halpha : 2 ≤ alpha) (c : VCocycle DD rho)
    (htauHead : pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .tau)) = 1)
    (hwildHead : ∀ i : Fin (2 + 2 * h + 1), pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) (.wild i))) = 1)
    (hsigma2Head : ∀ v : DD.Vmod,
      (pi (rho0 DD rho
        (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .sigma)) ^
          (omega2Exp
            (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : Int)) • v = v)
    (p : (DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
    (hc : (fun i ↦ c.c
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) i)) =
        wPmCompactPhaseNormal h p) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction
        ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
        (ZMod 2) := scalarActionZmodTwo _
    letI : ContinuousSMul
        ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
        (ZMod 2) := scalarActionZmodTwo_continuousSMul _
    QZero DD rho c = wPhCompactWallHandlePhase DD.qbar h p := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      (ZMod 2) := scalarActionZmodTwo_continuousSMul _
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  set E : Zhat → Int := fun _ ↦ (omega2Exp (4 * Monoid.exponent L) : Int)
  set E2 : ℤ_[2] → Int := fun _ ↦ (omega2Exp (4 * Monoid.exponent L) : Int)
  set phi := semiProdProjHom (V := DD.Vmod) pi hpi
  have hcval : ∀ i, c.c
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) i) =
        wPmCompactPhaseNormal h p i := fun i ↦ congrFun hc i
  have hmark :
      (fun i ↦ phi (graphSemiProdHom c
        (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) i))) =
        Certificates.hessMark (h := h)
          (pi (rho0 DD rho
            (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .sigma)))
          (1 : Cbar)
          (fun i : Fin (2 + 2 * h + 1) ↦
            wPmCompactPhaseNormal h p (Generator.wild i)) := by
    funext i
    cases i with
    | sigma => exact Prod.ext ((hcval _).trans (wPmCompactPhaseNormal_sigma h p)) rfl
    | tau => exact Prod.ext ((hcval _).trans (wPmCompactPhaseNormal_tau h p)) htauHead
    | wild i => exact Prod.ext (hcval _) (hwildHead i)
  rw [wPs_QZero_eq_mCompact_graphHessianTrace
      (α := alpha) (h := h) (q := q) rho DD.hdat hq hq0 halpha c,
    kappa0Cocycle_comap_semiProdProjHom base hbase DD.dat DD.hdat pi hpi hf hm]
  rw [show (fun _ : Zhat ↦
      (omega2Exp (4 * Monoid.exponent L) : Int)) = E from rfl,
    show (fun _ : ℤ_[2] ↦
      (omega2Exp (4 * Monoid.exponent L) : Int)) = E2 from rfl,
    ← hessRelZ_comap (kappa0Cocycle base hbase) E E2
      (fun i ↦ graphSemiProdHom c
        (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) i)) phi
      (tameRelW (2 + 2 * h) q),
    ← hessRelZ_comap (kappa0Cocycle base hbase) E E2
      (fun i ↦ graphSemiProdHom c
        (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) i)) phi
      (MCompact.mCompactW alpha h),
    hmark, wPs_hessRelZ_tameRelW_hessMark_eq_zero base hbase _ _ _ E E2,
    zero_add,
    wPcM_hessRelZ_eq_compactWallPhase_P1_handles base hbase (Vmod_exp2 DD)
      halpha _ p E E2 (by simpa only [E, L] using hsigma2Head)
      rfl (omega2Exp_fourMulExponent_mod_four L)]

/-- Transport source `powOmega2`-triviality to the compact trace exponent. -/
theorem wPcM_resolver_smul_of_powOmega2_handles
    {C Cbar V : Type} [Group C] [Finite C] [Group Cbar] [AddCommGroup V] [Finite V]
    [DistribMulAction C V] [DistribMulAction Cbar V]
    (pi : C →* Cbar) (hpi : ∀ (c : C) (v : V), c • v = pi c • v) (s : C)
    (hsigma2 : ∀ v : V, powOmega2 s • v = v) :
    ∀ v : V,
      (pi s ^ (omega2Exp
        (4 * Monoid.exponent (SectionSix.SemiProd C V)) : Int)) • v = v := by
  let L := SectionSix.SemiProd C V
  letI : Finite L := inferInstanceAs (Finite (V × C))
  let N := 4 * Monoid.exponent L
  have hN : N ≠ 0 := (fourMulExponent_ne_zero_and_even L).1
  have hsExp : s ^ Monoid.exponent L = 1 := by
    let p : L := (0, s)
    have hp : p ^ Monoid.exponent L = 1 := Monoid.pow_exponent_eq_one p
    calc
      s ^ Monoid.exponent L = sdSnd (p ^ Monoid.exponent L) :=
        (map_pow (sdSnd : L →* C) p _).symm
      _ = 1 := by rw [hp]; exact map_one _
  have hsN : s ^ N = 1 := by
    rw [show N = Monoid.exponent L * 4 by simp [N, Nat.mul_comm],
      pow_mul, hsExp, one_pow]
  have hresolved : s ^ omega2Exp N = powOmega2 s :=
    powOmega2_pow_eq _ (orderOf_dvd_of_pow_eq_one hsN) hN
  intro v
  calc
    (pi s ^ (omega2Exp N : Int)) • v = pi (s ^ (omega2Exp N : Int)) • v := by
      rw [map_zpow]
    _ = (s ^ (omega2Exp N : Int)) • v := (hpi _ _).symm
    _ = powOmega2 s • v := by rw [zpow_natCast, hresolved]
    _ = v := hsigma2 v

/-- The arbitrary-h unramified comparison in the common compact endpoint coordinates. -/
noncomputable def wPcMComparison_unramifiedHead_handles
    {alpha h q : Nat}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      DD.Vmod]
    [ContinuousSMul
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      DD.Vmod]
    {Cbar : Type} [Group Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hcompat : ∀
      (g : ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type))
      (v : DD.Vmod), g • v = rho0 DD rho g • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) i)))
    (hqe : Even q) (hq0 : q ≠ 0) (halpha : 2 ≤ alpha)
    (htauHead : pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .tau)) = 1)
    (hwildHead : ∀ i : Fin (2 + 2 * h + 1), pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) (.wild i))) = 1)
    (hsigmaFpf : ∀ v : DD.Vmod, rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .sigma) • v = v → v = 0)
    (hsigma2 : ∀ v : DD.Vmod, powOmega2 (rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .sigma)) • v = v) :
    letI := scalarActionZmodTwo
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) :=
      inferInstance
    SourceWordPhaseComparison DD rho (scalarActionZmodTwo_triv _)
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (wPhCompactWallHandlePhase DD.qbar h) := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      (ZMod 2) := scalarActionZmodTwo_continuousSMul _
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) :=
    inferInstance
  have htauAct : ∀ v : DD.Vmod, rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .tau) • v = v := by
    intro v
    rw [hpi, htauHead, one_smul]
  have hwildAct : ∀ (i : Fin (2 + 2 * h + 1)) (v : DD.Vmod), rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) (.wild i)) • v = v := by
    intro i v
    rw [hpi, hwildHead i, one_smul]
  have hsigma2Head : ∀ v : DD.Vmod,
      (pi (rho0 DD rho
        (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .sigma)) ^
          (omega2Exp
            (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : Int)) • v = v :=
    wPcM_resolver_smul_of_powOmega2_handles pi hpi _ hsigma2
  have hphase : ∀
      (p : (DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (c : VCocycle DD rho),
      (fun i ↦ c.c
        (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) i)) =
          wPmCompactPhaseNormal h p →
      QZero DD rho c = wPhCompactWallHandlePhase DD.qbar h p := by
    intro p c hc
    exact wPcM_QZero_eq_compactWallPhase_P1_handles_of_headMark rho base hbase
      pi hpi hf hm hqe hq0 halpha c htauHead hwildHead hsigma2Head p hc
  exact wPcMComparison_unramifiedP1_of_headPhase rho (scalarActionZmodTwo_triv _)
    hcompat hA2 hwildTwo hqe htauAct hwildAct hsigmaFpf hsigma2 hphase

/-- The arbitrary-h ramified comparison in its natural block-swapped coordinates. -/
noncomputable def wPcMComparison_ramifiedNatural_handles
    {alpha h q : Nat}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      DD.Vmod]
    [ContinuousSMul
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      DD.Vmod]
    [DistribMulAction
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      (ZMod 2)]
    [ContinuousSMul
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      (ZMod 2)]
    (htriv : ∀
      (g : ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type))
      (a : ZMod 2), g • a = a)
    (hcompat : ∀
      (g : ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type))
      (v : DD.Vmod), g • v = rho0 DD rho g • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) i)))
    (hwildAct : ∀ (i : Fin (2 + 2 * h + 1)) (v : DD.Vmod), rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) (.wild i)) • v = v)
    (htauFpf : ∀ v : DD.Vmod, rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .tau) • v = v → v = 0)
    (hTodd : ∀ v : DD.Vmod, powOmega2 (rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .tau)) • v = v)
    (hphase : ∀
      (p : (DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (c : VCocycle DD rho),
      (fun i ↦ c.c
        (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) i)) =
          wPmCompactPhaseNormal h p →
      QZero DD rho c = wPcMRamifiedHandlePhase DD.qbar h p) :
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) :=
      inferInstance
    SourceWordPhaseComparison DD rho htriv
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (wPcMRamifiedHandlePhase DD.qbar h) := by
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) :=
    inferInstance
  let e := omega2Exp (4 * Monoid.exponent DD.C0)
  let theta := Count.rho0Continuous DD rho
  let t : Marking (2 + 2 * h) DD.C0 :=
    ⟨fun i ↦ theta (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) i)⟩
  have hbaseOrd : ∀ g : DD.C0, orderOf g ∣ Monoid.exponent DD.C0 :=
    fun g ↦ Monoid.order_dvd_exponent g
  have horder : ∀ p : WordLift DD.Vmod DD.C0,
      orderOf p ∣ 4 * Monoid.exponent DD.C0 := fun p ↦
    (WordLift.orderOf_dvd_two_mul hA2 hbaseOrd p).trans ⟨2, by ring⟩
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (MCompact.mCompactW alpha h))
      (MCompact.mCompactFam alpha h q e) (WordLift DD.Vmod DD.C0) :=
    Count.resolvesAt_mCompactFam (Count.fourMulExponent_ne_zero_and_even DD.C0).1
      horder alpha h q
  have htame : t.TameRelAt q := by
    have hrel := (isAdmissibleMarkedPresentation_gammaR
      (2 + 2 * h) q (MCompact.mCompactW alpha h)).rel theta (0 : Fin 2)
    change PWord.eval ⇑t (tameRelW (2 + 2 * h) q) = 1 at hrel
    rw [← Marking.eval_def, Certificates.eval_tameRelW] at hrel
    exact mul_inv_eq_one.mp hrel
  have hrow : ∀ x : Generator (2 + 2 * h) → DD.Vmod,
      heisD1 ⇑t (MCompact.mCompactFam alpha h q e) x =
        ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma) -
            ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
          -(t.σ⁻¹ • x (coreLetter h 2))] :=
    heisD1_mCompactFam_ramified_apply t hA2 htame hwildAct htauFpf hTodd
  have hr : ∀ k, FreeGroup.lift ⇑t (MCompact.mCompactFam alpha h q e k) = 1 :=
    fun k ↦ Count.lower_rel (A := DD.Vmod) theta (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR
        (2 + 2 * h) q (MCompact.mCompactW alpha h)) hres k
  exact wPmPhaseComparison_of_normalForm rho hcompat hres hA2 hwildTwo
    (wPmCompactPhaseNormal h)
    (wPcN_compactNormal_closed_ramified t (MCompact.mCompactFam alpha h q e) hrow)
    (wPcN_compactNormalForm_ramified t (MCompact.mCompactFam alpha h q e) hrow
      hwildAct htauFpf hr)
    htriv (wPcMRamifiedHandlePhase DD.qbar h) hphase

/-- The arbitrary-h projected ramified comparison in the common compact coordinates. -/
noncomputable def wPcMComparison_ramifiedHead_handles
    {alpha h q : Nat}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      DD.Vmod]
    [ContinuousSMul
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      DD.Vmod]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hphi : Function.Surjective (semiProdProjHom (V := DD.Vmod) pi hpi))
    (hcompat : ∀
      (g : ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type))
      (v : DD.Vmod), g • v = rho0 DD rho g • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) i)))
    (hq0 : q ≠ 0) (hqe : Even q) (halpha : 2 ≤ alpha)
    (hwildHead : ∀ i : Fin (2 + 2 * h + 1), pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) (.wild i))) = 1)
    (htauHeadOdd : Odd (orderOf (pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .tau)))))
    (htauHeadFpf : ∀ v : DD.Vmod, pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .tau)) • v = v → v = 0)
    (hTodd : ∀ v : DD.Vmod, powOmega2 (rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .tau)) • v = v) :
    letI := scalarActionZmodTwo
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) :=
      inferInstance
    SourceWordPhaseComparison DD rho (scalarActionZmodTwo_triv _)
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (wPhCompactWallHandlePhase DD.qbar h) := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      (ZMod 2) := scalarActionZmodTwo_continuousSMul _
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) :=
    inferInstance
  have hwildAct : ∀ (i : Fin (2 + 2 * h + 1)) (v : DD.Vmod), rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) (.wild i)) • v = v := by
    intro i v
    rw [hpi, hwildHead i, one_smul]
  have htauFpf : ∀ v : DD.Vmod, rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .tau) • v = v → v = 0 := by
    intro v hv
    apply htauHeadFpf v
    rw [← hpi]
    exact hv
  have hphase : ∀
      (p : (DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (c : VCocycle DD rho),
      (fun i ↦ c.c
        (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) i)) =
          wPmCompactPhaseNormal h p →
      QZero DD rho c = wPcMRamifiedHandlePhase DD.qbar h p :=
    fun p c hc ↦
      wPcM_QZero_eq_ramifiedHandlePhase_of_surjectiveHeadMark rho base hbase
        pi hpi hf hm hphi hqe hq0 halpha c hwildHead htauHeadOdd htauHeadFpf p hc
  let C := wPcMComparison_ramifiedNatural_handles rho (scalarActionZmodTwo_triv _)
    hcompat hA2 hwildTwo hwildAct htauFpf hTodd hphase
  refine {
    phaseEquiv := C.phaseEquiv.trans (wPcMRamifiedHandleSwap DD.Vmod h)
    phase_eq := fun x ↦ ?_ }
  rw [C.phase_eq]
  exact wPcMRamifiedHandlePhase_eq_compactWall_swap DD.qbar h _

/-! ## Axiom audit -/

#print axioms wPcM_QZero_eq_ramifiedHandlePhase_of_projectedHeadMark
#print axioms wPcM_QZero_eq_ramifiedHandlePhase_of_surjectiveHeadMark
#print axioms wPcM_QZero_eq_compactWallPhase_P1_handles_of_headMark
#print axioms wPcM_resolver_smul_of_powOmega2_handles
#print axioms wPcMComparison_unramifiedHead_handles
#print axioms wPcMComparison_ramifiedNatural_handles
#print axioms wPcMComparison_ramifiedHead_handles

end

end GQ2.Dyadic.Instances.WordPhaseCompactMHandleComparison


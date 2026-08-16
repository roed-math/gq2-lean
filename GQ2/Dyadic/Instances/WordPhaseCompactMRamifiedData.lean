/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Certificates.M0Ramified
import GQ2.Dyadic.Instances.KappaResolverTransport
import GQ2.Dyadic.Instances.WordPhaseCompactNData
import GQ2.Dyadic.Instances.M0RamifiedStokes

/-!
# Honest ramified compact-M graph data

This file identifies the handle-free compact-M graph-Hessian phase under the honest
ramified head hypotheses.  It retains projected wild-head triviality and transports the
source trace resolver through a surjective semidirect-product projection; it does not use
the false per-letter projector or square-power hypotheses.
-/

namespace GQ2.Dyadic.Instances.WordPhaseCompactMRamifiedData

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words
open GQ2.Dyadic.Certificates GQ2.QuadraticFp2
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.WordPhaseSeam
open GQ2.Dyadic.Instances.WordPhaseCompactNData
open GQ2.Dyadic.LSquare

/-- The block-swapped compact-M head phase in ramified normal coordinates. -/
def wPcMRamifiedPhase {V : Type} [AddCommGroup V] (q0 : V → ZMod 2) :
    (V × V) × (Fin 0 → V × V) → ZMod 2 :=
  fun p ↦ q0 p.1.2 + polar q0 p.1.1 p.1.2

/-- The compact trace exponent resolves the full κ⁰-extension, not only its base. -/
theorem wPcM_resolverLifts_graphTrace
    {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
    [Finite C] [Finite V]
    {q0 : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat)
    (hV2 : ∀ v : V, v + v = 0) :
    MProcyclic.ResolverLifts
      (fun _ ↦ (omega2Exp
        (4 * Monoid.exponent (SectionSix.SemiProd C V)) : Int))
      (WordCoh.CentExt (kappa0Cocycle dat hdat)) := by
  let L := SectionSix.SemiProd C V
  let N := 4 * Monoid.exponent L
  have hN : N ≠ 0 := (fourMulExponent_ne_zero_and_even L).1
  have hord : ∀ p : WordCoh.CentExt (kappa0Cocycle dat hdat), orderOf p ∣ N := by
    intro p
    rw [orderOf_dvd_iff_pow_eq_one]
    apply kappa0_pow_eq_one_of_snd_pow dat hdat hV2
    have hb : p.base ^ Monoid.exponent L = 1 := Monoid.pow_exponent_eq_one p.base
    calc
      p.base.2 ^ Monoid.exponent L = sdSnd (p.base ^ Monoid.exponent L) :=
        (map_pow (sdSnd : L →* C) p.base _).symm
      _ = 1 := by rw [hb]; exact map_one _
  intro p
  rw [zpow_natCast]
  exact powOmega2_pow_eq p (hord p) hN

/-- The honest ramified compact-M Hessian at the handle-free compact normal cochain. -/
theorem wPcM_hessRelZ_eq_ramifiedPhase
    {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
    [Finite C] [Finite V]
    {q0 : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat)
    (hV2 : ∀ v : V, v + v = 0) (alpha : Nat) (s u : C)
    (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (p : (V × V) × (Fin 0 → V × V)) (E : Zhat → Int) (E2 : ℤ_[2] → Int)
    (hres : MProcyclic.ResolverLifts E
      (WordCoh.CentExt (kappa0Cocycle dat hdat))) :
    hessRelZ
        (Certificates.hessMark (h := 0) s u
          (fun i : Fin 3 ↦ wPmCompactPhaseNormal 0 p (Generator.wild i)))
        (kappa0Cocycle dat hdat) E E2 (MCompact.mCompactW alpha 0)
      = wPcMRamifiedPhase q0 p := by
  have hoffsets : (fun i : Fin 3 ↦ wPmCompactPhaseNormal 0 p (Generator.wild i))
      = ![p.1.1, p.1.2, 0] := by
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
  rw [hoffsets, MCompactRamified.hessRelZ_mCompact_ramified_zero dat hdat hV2
    alpha s u hu hVu p.1.1 p.1.2 E E2 hres]
  rfl

/-- The graph-Hessian trace reaches the swapped compact-M phase on the honest ramified head. -/
theorem wPcM_QZero_eq_ramifiedPhase_of_headMark
    {alpha q : Nat}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    (hdat : IsEquivariantFactorSet DD.qbar DD.dat)
    (hq : Even q) (hq0 : q ≠ 0) (halpha : 2 ≤ alpha) (c : VCocycle DD rho)
    (hwildHead : ∀ i : Fin 3, rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) (.wild i)) = 1)
    (htauOdd : Odd (orderOf (rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau))))
    (htauFpf : ∀ v : DD.Vmod, rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau) • v = v → v = 0)
    (p : (DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod))
    (hc : (fun i ↦ c.c (gammaGen 2 q (MCompact.mCompactW alpha 0) i))
      = wPmCompactPhaseNormal 0 p) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction
        ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo _
    letI : ContinuousSMul
        ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    QZero DD rho c = wPcMRamifiedPhase DD.qbar p := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  set E : Zhat → Int := fun _ ↦ (omega2Exp (4 * Monoid.exponent L) : Int) with hE
  set E2 : ℤ_[2] → Int := fun _ ↦ (omega2Exp (4 * Monoid.exponent L) : Int) with hE2
  have hcval : ∀ i, c.c (gammaGen 2 q (MCompact.mCompactW alpha 0) i)
      = wPmCompactPhaseNormal 0 p i := fun i ↦ congrFun hc i
  have hmark :
      (fun i ↦ graphSemiProdHom c (gammaGen 2 q (MCompact.mCompactW alpha 0) i))
        = Certificates.hessMark (h := 0)
            (rho0 DD rho (gammaGen 2 q (MCompact.mCompactW alpha 0) .sigma))
            (rho0 DD rho (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau))
            (fun i : Fin 3 ↦ wPmCompactPhaseNormal 0 p (Generator.wild i)) := by
    funext i
    cases i with
    | sigma => exact Prod.ext ((hcval _).trans (wPmCompactPhaseNormal_sigma 0 p)) rfl
    | tau => exact Prod.ext ((hcval _).trans (wPmCompactPhaseNormal_tau 0 p)) rfl
    | wild i => exact Prod.ext (hcval _) (hwildHead i)
  have hres : MProcyclic.ResolverLifts E
      (WordCoh.CentExt (kappa0Cocycle DD.dat hdat)) := by
    simpa only [E, L] using
      wPcM_resolverLifts_graphTrace DD.dat hdat (Vmod_exp2 DD)
  rw [wPs_QZero_eq_mCompact_graphHessianTrace (α := alpha) (h := 0) (q := q)
      rho hdat hq hq0 halpha c]
  rw [show (fun _ : Zhat ↦ (omega2Exp (4 * Monoid.exponent L) : Int)) = E from rfl,
    show (fun _ : ℤ_[2] ↦ (omega2Exp (4 * Monoid.exponent L) : Int)) = E2 from rfl,
    hmark, wPs_hessRelZ_tameRelW_hessMark_eq_zero DD.dat hdat _ _ _ E E2, zero_add,
    wPcM_hessRelZ_eq_ramifiedPhase DD.dat hdat (Vmod_exp2 DD) alpha _ _ htauOdd
      htauFpf p E E2 hres]

/-- The projected-head graph trace, with resolver transport stated at its exact boundary. -/
theorem wPcM_QZero_eq_ramifiedPhase_of_projectedHeadMark
    {alpha q : Nat}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hq : Even q) (hq0 : q ≠ 0) (halpha : 2 ≤ alpha) (c : VCocycle DD rho)
    (hwildHead : ∀ i : Fin 3, pi (rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) (.wild i))) = 1)
    (htauOdd : Odd (orderOf (pi (rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau)))))
    (htauFpf : ∀ v : DD.Vmod, pi (rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau)) • v = v → v = 0)
    (hres : MProcyclic.ResolverLifts
      (fun _ ↦ (omega2Exp
        (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : Int))
      (WordCoh.CentExt (kappa0Cocycle base hbase)))
    (p : (DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod))
    (hc : (fun i ↦ c.c (gammaGen 2 q (MCompact.mCompactW alpha 0) i))
      = wPmCompactPhaseNormal 0 p) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction
        ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo _
    letI : ContinuousSMul
        ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    QZero DD rho c = wPcMRamifiedPhase DD.qbar p := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  set E : Zhat → Int := fun _ ↦ (omega2Exp (4 * Monoid.exponent L) : Int) with hE
  set E2 : ℤ_[2] → Int := fun _ ↦ (omega2Exp (4 * Monoid.exponent L) : Int) with hE2
  set phi := semiProdProjHom (V := DD.Vmod) pi hpi with hphi
  have hcval : ∀ i, c.c (gammaGen 2 q (MCompact.mCompactW alpha 0) i)
      = wPmCompactPhaseNormal 0 p i := fun i ↦ congrFun hc i
  have hmark :
      (fun i ↦ phi (graphSemiProdHom c
        (gammaGen 2 q (MCompact.mCompactW alpha 0) i)))
        = Certificates.hessMark (h := 0)
            (pi (rho0 DD rho (gammaGen 2 q (MCompact.mCompactW alpha 0) .sigma)))
            (pi (rho0 DD rho (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau)))
            (fun i : Fin 3 ↦ wPmCompactPhaseNormal 0 p (Generator.wild i)) := by
    funext i
    cases i with
    | sigma => exact Prod.ext ((hcval _).trans (wPmCompactPhaseNormal_sigma 0 p)) rfl
    | tau => exact Prod.ext ((hcval _).trans (wPmCompactPhaseNormal_tau 0 p)) rfl
    | wild i => exact Prod.ext (hcval _) (hwildHead i)
  rw [wPs_QZero_eq_mCompact_graphHessianTrace (α := alpha) (h := 0) (q := q)
      rho DD.hdat hq hq0 halpha c,
    kappa0Cocycle_comap_semiProdProjHom base hbase DD.dat DD.hdat pi hpi hf hm]
  rw [show (fun _ : Zhat ↦ (omega2Exp (4 * Monoid.exponent L) : Int)) = E from rfl,
    show (fun _ : ℤ_[2] ↦ (omega2Exp (4 * Monoid.exponent L) : Int)) = E2 from rfl,
    ← hessRelZ_comap (kappa0Cocycle base hbase) E E2
      (fun i ↦ graphSemiProdHom c (gammaGen 2 q (MCompact.mCompactW alpha 0) i)) phi
      (tameRelW 2 q),
    ← hessRelZ_comap (kappa0Cocycle base hbase) E E2
      (fun i ↦ graphSemiProdHom c (gammaGen 2 q (MCompact.mCompactW alpha 0) i)) phi
      (MCompact.mCompactW alpha 0),
    hmark, wPs_hessRelZ_tameRelW_hessMark_eq_zero base hbase _ _ _ E E2, zero_add,
    wPcM_hessRelZ_eq_ramifiedPhase base hbase (Vmod_exp2 DD) alpha _ _ htauOdd htauFpf
      p E E2 (by simpa only [E, L] using hres)]

/-- The projected-head graph trace with its resolver obtained from a surjective
projection of the source semidirect product. -/
theorem wPcM_QZero_eq_ramifiedPhase_of_surjectiveHeadMark
    {alpha q : Nat}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hphi : Function.Surjective (semiProdProjHom (V := DD.Vmod) pi hpi))
    (hq : Even q) (hq0 : q ≠ 0) (halpha : 2 ≤ alpha) (c : VCocycle DD rho)
    (hwildHead : ∀ i : Fin 3, pi (rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) (.wild i))) = 1)
    (htauOdd : Odd (orderOf (pi (rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau)))))
    (htauFpf : ∀ v : DD.Vmod, pi (rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau)) • v = v → v = 0)
    (p : (DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod))
    (hc : (fun i ↦ c.c (gammaGen 2 q (MCompact.mCompactW alpha 0) i))
      = wPmCompactPhaseNormal 0 p) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction
        ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo _
    letI : ContinuousSMul
        ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    QZero DD rho c = wPcMRamifiedPhase DD.qbar p := by
  exact wPcM_QZero_eq_ramifiedPhase_of_projectedHeadMark rho base hbase pi hpi
    hf hm hq hq0 halpha c hwildHead htauOdd htauFpf
      (kappaResolverLifts_of_surjective base hbase
        (semiProdProjHom (V := DD.Vmod) pi hpi) hphi) p hc

/-- Closedness of the handle-free compact normal cochain for the shared ramified row. -/
theorem wPcMRamifiedNormal_closed
    {q : Nat} {C A : Type} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking 2 C) (w : Fin 2 → FreeGroup (Generator 2))
    (hrow : ∀ x : Generator 2 → A, heisD1 ⇑t w x =
      ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
          - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
        -(t.σ⁻¹ • x (coreLetter 0 2))])
    (p : (A × A) × (Fin 0 → A × A)) :
    heisD1 ⇑t w (wPmCompactPhaseNormal 0 p) = 0 :=
  wPcN_compactNormal_closed_ramified (h := 0) (q := q) t w hrow p

/-- The handle-free ramified normal form in compact endpoint coordinates. -/
theorem wPcMRamifiedNormal_form
    {q : Nat} {C A : Type} [Group C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking 2 C) (w : Fin 2 → FreeGroup (Generator 2))
    (hrow : ∀ x : Generator 2 → A, heisD1 ⇑t w x =
      ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
          - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
        -(t.σ⁻¹ • x (coreLetter 0 2))])
    (hwild : ∀ (i : Fin 3) (a : A), t.x i • a = a)
    (htauFpf : ∀ a : A, t.τ • a = a → a = 0)
    (hr : ∀ k, FreeGroup.lift ⇑t (w k) = 1) :
    ∀ x, heisD1 (A := A) ⇑t w x = 0 →
      ∃! p : (A × A) × (Fin 0 → A × A),
        x - wPmCompactPhaseNormal 0 p ∈ Set.range (heisD0 ⇑t) :=
  wPcN_compactNormalForm_ramified (h := 0) (q := q) t w hrow hwild htauFpf hr

/-! ## Axiom audit -/

#print axioms wPcMRamifiedPhase
#print axioms wPcM_resolverLifts_graphTrace
#print axioms wPcM_hessRelZ_eq_ramifiedPhase
#print axioms wPcM_QZero_eq_ramifiedPhase_of_headMark
#print axioms wPcM_QZero_eq_ramifiedPhase_of_projectedHeadMark
#print axioms wPcM_QZero_eq_ramifiedPhase_of_surjectiveHeadMark
#print axioms wPcMRamifiedNormal_closed
#print axioms wPcMRamifiedNormal_form

end

end GQ2.Dyadic.Instances.WordPhaseCompactMRamifiedData

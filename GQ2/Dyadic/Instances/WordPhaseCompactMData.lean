/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhaseSeam
import GQ2.Dyadic.Certificates.M0Assembly

/-!
# Compact-M determinant data

This file supplies the unramified `P = 1` source-to-word phase comparison for the compact `M`
word at handle count zero.  The trace seam is word-generic; the second-order input is the
honest-resolver endpoint `MCompact.hessRelZ_mCompact_P1_plusForm`, while the first-order input
is the shared compact unramified Fox row.

The projected `sigma` two-primary action is stated explicitly at the trace resolver.  This is
the precise additional datum required by the compact-`M` correction block and is separate from
the uniform first-order `powOmega2` hypothesis.
-/

namespace GQ2.Dyadic.Instances.WordPhaseCompactMData

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words
open GQ2.Dyadic.Certificates GQ2.QuadraticFp2
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.WordPhaseSeam
open GQ2.Dyadic.LSquare

/-! ## The unramified P1 head phase -/

/-- The `h = 0` `P = 1` Hessian endpoint in the compact phase coordinates. -/
theorem wPcM_hessRelZ_eq_compactWallPhase_P1
    {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
    {q0 : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat)
    (hV2 : ∀ v : V, v + v = 0) {alpha : Nat} (halpha : 2 ≤ alpha) (s : C)
    (p : (V × V) × (Fin 0 → V × V)) (E : Zhat → Int) (E2 : ℤ_[2] → Int)
    (hsigma2 : ∀ v : V, (s ^ E omega2) • v = v)
    {e : Nat} (hE : E omega2 = (e : Int)) (he : e % 4 = 1) :
    hessRelZ
        (Certificates.hessMark (h := 0) s 1
          (fun i : Fin 3 ↦ wPmCompactPhaseNormal 0 p (Generator.wild i)))
        (kappa0Cocycle dat hdat) E E2 (MCompact.mCompactW alpha 0)
      = wPhCompactWallHandlePhase q0 0 p := by
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
  rw [hoffsets, Certificates.MCompact.hessRelZ_mCompact_P1_plusForm dat hdat hV2
    halpha s p.1.1 p.1.2 E E2 hsigma2 hE he]
  simp [wPhCompactWallHandlePhase]

/-- At `h = 0`, the compact-`M` Hessian in the unramified `P = 1` branch is the compact
wall-head phase.  The projected `sigma` hypothesis is exactly the `S2`-collapse required by
the `M` correction block at the trace resolver. -/
theorem wPcM_QZero_eq_compactWallPhase_P1_of_headMark
    {alpha q : Nat}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    {Cbar : Type} [Group Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hq : Even q) (hq0 : q ≠ 0) (halpha : 2 ≤ alpha) (c : VCocycle DD rho)
    (htauHead : pi (rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau)) = 1)
    (hwildHead : ∀ i : Fin 3, pi (rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) (.wild i))) = 1)
    (hsigma2Head : ∀ v : DD.Vmod,
      (pi (rho0 DD rho (gammaGen 2 q (MCompact.mCompactW alpha 0) .sigma)) ^
        (omega2Exp
          (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : Int)) • v = v)
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
    QZero DD rho c = wPhCompactWallHandlePhase DD.qbar 0 p := by
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
      (fun i ↦ phi (graphSemiProdHom c (gammaGen 2 q (MCompact.mCompactW alpha 0) i)))
        = Certificates.hessMark (h := 0)
            (pi (rho0 DD rho (gammaGen 2 q (MCompact.mCompactW alpha 0) .sigma)))
            (1 : Cbar)
            (fun i : Fin 3 ↦ wPmCompactPhaseNormal 0 p (Generator.wild i)) := by
    funext i
    cases i with
    | sigma => exact Prod.ext ((hcval _).trans (wPmCompactPhaseNormal_sigma 0 p)) rfl
    | tau => exact Prod.ext ((hcval _).trans (wPmCompactPhaseNormal_tau 0 p)) htauHead
    | wild i => exact Prod.ext (hcval _) (hwildHead i)
  rw [wPs_QZero_eq_mCompact_graphHessianTrace (α := alpha) (h := 0) (q := q)
      rho DD.hdat hq hq0 halpha c,
    kappa0Cocycle_comap_semiProdProjHom base hbase DD.dat DD.hdat pi hpi hf hm]
  rw [show (fun _ : Zhat ↦ (omega2Exp (4 * Monoid.exponent L) : Int)) = E from rfl,
    show (fun _ : ℤ_[2] ↦ (omega2Exp (4 * Monoid.exponent L) : Int)) = E2 from rfl,
    ← hessRelZ_comap (GQ2.Dyadic.kappa0Cocycle base hbase) E E2
      (fun i ↦ graphSemiProdHom c (gammaGen 2 q (MCompact.mCompactW alpha 0) i)) phi
      (tameRelW 2 q),
    ← hessRelZ_comap (GQ2.Dyadic.kappa0Cocycle base hbase) E E2
      (fun i ↦ graphSemiProdHom c (gammaGen 2 q (MCompact.mCompactW alpha 0) i)) phi
      (MCompact.mCompactW alpha 0),
    hmark, wPs_hessRelZ_tameRelW_hessMark_eq_zero base hbase _ _ _ E E2, zero_add,
    wPcM_hessRelZ_eq_compactWallPhase_P1 base hbase (Vmod_exp2 DD) halpha _ p E E2
      (by simpa [E] using hsigma2Head) rfl (omega2Exp_fourMulExponent_mod_four L)]

/-! ## Source-to-word comparison -/

/-- The handle-free compact normal cochain, with no vacuous `Fin 0` coordinate in its type. -/
def wPcMPhaseNormal0 {V : Type} [AddCommGroup V] (p : V × V) : Generator 2 → V :=
  wPmCompactPhaseNormal 0 (p, fun i ↦ Fin.elim0 i)

/-- The handle-free compact endpoint phase. -/
def wPcMPhase0 {V : Type} [AddCommGroup V] (q0 : V → ZMod 2) : V × V → ZMod 2 :=
  plusFormD q0 q0

/-- Closedness of the handle-free compact normal cochain. -/
theorem wPcMPhaseNormal0_closed
    {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
    (t : Marking 2 C) (w : Fin 2 → FreeGroup (Generator 2))
    (hrow : ∀ x : Generator 2 → V, heisD1 ⇑t w x
      = ![t.σ⁻¹ • x .tau, x .tau + (x (coreLetter 0 2) - t.σ⁻¹ • x (coreLetter 0 2))])
    (p : V × V) : heisD1 ⇑t w (wPcMPhaseNormal0 p) = 0 :=
  wPm_heisD1_compactPhaseNormal_eq_zero t w hrow (p, fun i ↦ Fin.elim0 i)

/-- Uniqueness of the handle-free compact normal representative. -/
theorem wPcMPhaseNormal0_form
    {C V : Type} [Group C] [AddCommGroup V] [Finite V] [DistribMulAction C V]
    (t : Marking 2 C) (w : Fin 2 → FreeGroup (Generator 2))
    (hrow : ∀ x : Generator 2 → V, heisD1 ⇑t w x
      = ![t.σ⁻¹ • x .tau, x .tau + (x (coreLetter 0 2) - t.σ⁻¹ • x (coreLetter 0 2))])
    (hwild : ∀ (i : Fin 3) (v : V), t.x i • v = v)
    (htau : ∀ v : V, t.τ • v = v) (hsigmaFpf : ∀ v : V, t.σ • v = v → v = 0)
    (hr : ∀ k, FreeGroup.lift ⇑t (w k) = 1) :
    ∀ x, heisD1 ⇑t w x = 0 →
      ∃! p : V × V, x - wPcMPhaseNormal0 p ∈ Set.range (heisD0 ⇑t) := by
  intro x hx
  obtain ⟨r, hr0, hu⟩ := wPm_compactPhaseNormalForm (h := 0) (C := C) (A := V)
    t w hrow hwild htau hsigmaFpf hr x hx
  refine ⟨r.1, ?_, ?_⟩
  · have her : (r.1, fun i : Fin 0 ↦ Fin.elim0 i) = r :=
      Prod.ext rfl (Subsingleton.elim _ _)
    simpa only [wPcMPhaseNormal0, her] using hr0
  · intro p hp
    have hep : (p, fun i : Fin 0 ↦ Fin.elim0 i) = r := by
      apply hu
      exact hp
    exact congrArg Prod.fst hep

/-- The compact-`M` unramified source-to-word comparison from a compact head phase.  It is
stated at general handle count so the generic normal-form assembler remains syntactically
uniform; the `P = 1` head theorem above supplies its `h = 0` specialization. -/
noncomputable def wPcMComparison_unramifiedP1_of_headPhase
    {alpha h q : Nat}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type) DD.Vmod]
    [ContinuousSMul
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type) DD.Vmod]
    [DistribMulAction
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type) (ZMod 2)]
    [ContinuousSMul
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type) (ZMod 2)]
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
    (hqe : Even q)
    (htauAct : ∀ v : DD.Vmod,
      rho0 DD rho (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .tau) • v = v)
    (hwildAct : ∀ (i : Fin (2 + 2 * h + 1)) (v : DD.Vmod),
      rho0 DD rho (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) (.wild i)) • v = v)
    (hsigmaFpf : ∀ v : DD.Vmod,
      rho0 DD rho (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .sigma) • v = v →
        v = 0)
    (hsigma2 : ∀ v : DD.Vmod,
      powOmega2 (rho0 DD rho
        (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .sigma)) • v = v)
    (hphase : ∀
      (p : (DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) (c : VCocycle DD rho),
      (fun i ↦ c.c (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) i))
        = wPmCompactPhaseNormal h p →
      QZero DD rho c = wPhCompactWallHandlePhase DD.qbar h p) :
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) := inferInstance
    SourceWordPhaseComparison DD rho htriv
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (wPhCompactWallHandlePhase DD.qbar h) := by
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) := inferInstance
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
  have hrow : ∀ x : Generator (2 + 2 * h) → DD.Vmod,
      heisD1 ⇑t (MCompact.mCompactFam alpha h q e) x
        = ![t.σ⁻¹ • x .tau,
            x .tau + (x (coreLetter h 2) - t.σ⁻¹ • x (coreLetter h 2))] :=
    heisD1_mCompactFam_unramified_apply t hA2 hwildAct htauAct hsigma2 hqe
  have hr : ∀ k, FreeGroup.lift ⇑t (MCompact.mCompactFam alpha h q e k) = 1 := fun k ↦
    Count.lower_rel (A := DD.Vmod) theta (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
        (MCompact.mCompactW alpha h)) hres k
  exact wPmPhaseComparison_of_normalForm rho hcompat hres hA2 hwildTwo
    (wPmCompactPhaseNormal h)
    (wPm_heisD1_compactPhaseNormal_eq_zero t (MCompact.mCompactFam alpha h q e) hrow)
    (wPm_compactPhaseNormalForm t (MCompact.mCompactFam alpha h q e) hrow hwildAct
      htauAct hsigmaFpf hr)
    htriv (wPhCompactWallHandlePhase DD.qbar h) hphase

/-! ## Axiom audit -/

#print axioms wPcM_QZero_eq_compactWallPhase_P1_of_headMark
#print axioms wPcM_hessRelZ_eq_compactWallPhase_P1
#print axioms wPcMPhaseNormal0
#print axioms wPcMPhase0
#print axioms wPcMPhaseNormal0_closed
#print axioms wPcMPhaseNormal0_form
#print axioms wPcMComparison_unramifiedP1_of_headPhase

end

end GQ2.Dyadic.Instances.WordPhaseCompactMData

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLUnramifiedPhase

/-!
# The graph-pullback Hessian formula for the improved L presentation

This file closes the representative-level comparison between the continuous scalar obstruction
`QZero` and the evaluated word Hessian of the improved L presentation.  The scalar orientation
is supplied by the direct action-image `H²` theorem, so no Tate duality, Euler characteristic,
or field-realization axiom enters.

The exact answer is the sum of two coordinates: the tame-relator Hessian and the improved
`L_sq` Hessian.  The tame term vanishes once the unramified graph normal form sends `tau` to the
identity.  At the `x₁`-supported graph marking, the remaining term is exactly the Wall head plus
the hyperbolic handle planes computed in `GammaLUnramifiedPhase`.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.LSq
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes
open GQ2.Dyadic.Count

/-- A central cocycle regarded as a module cocycle under a trivial action. -/
def centralModuleCocycle {L : Type*} [Group L] [DistribMulAction L (ZMod 2)]
    (htriv : ∀ (g : L) (a : ZMod 2), g • a = a)
    (c : WordCoh.TwoCocycle L) : ModuleTwoCocycle L (ZMod 2) where
  κ := c.κ
  norm := c.norm
  cocyc g h k := by
    rw [htriv]
    simpa only [add_comm] using (c.cocyc g h k).symm

/-- The module extension of a central cocycle is its central extension, with coordinates
reordered. -/
def moduleExtToCentExt {L : Type*} [Group L] [DistribMulAction L (ZMod 2)]
    (htriv : ∀ (g : L) (a : ZMod 2), g • a = a)
    (c : WordCoh.TwoCocycle L) :
    ModuleExt (centralModuleCocycle htriv c) →* WordCoh.CentExt c where
  toFun p := (p.g, p.u)
  map_one' := rfl
  map_mul' p q := by
    apply WordCoh.CentExt.ext
    · rfl
    · show p.u + p.g • q.u + c.κ p.g q.g = p.u + q.u + c.κ p.g q.g
      rw [htriv]

@[simp] theorem moduleExtToCentExt_u {L : Type*} [Group L]
    [DistribMulAction L (ZMod 2)]
    (htriv : ∀ (g : L) (a : ZMod 2), g • a = a)
    (c : WordCoh.TwoCocycle L) (p : ModuleExt (centralModuleCocycle htriv c)) :
    (moduleExtToCentExt htriv c p).fib = p.u := rfl

@[simp] theorem moduleExtToCentExt_lift {X : Type*} {L : Type} [Group L]
    [DistribMulAction L (ZMod 2)]
    (htriv : ∀ (g : L) (a : ZMod 2), g • a = a)
    (c : WordCoh.TwoCocycle L) (m : X → L) (x : X) :
    moduleExtToCentExt htriv c (ModuleExt.lift (centralModuleCocycle htriv c) m x) =
      WordCoh.lift m c x := rfl

/-- Under trivial coefficients, an intrinsic module-relator fibre is the evaluated Hessian
whenever the chosen integer exponents resolve the profinite word in the central extension. -/
theorem moduleRel_eq_hessRelZ {X : Type*} {L : Type} [Group L] [Finite L]
    [TopologicalSpace L] [DiscreteTopology L] [DistribMulAction L (ZMod 2)]
    (htriv : ∀ (g : L) (a : ZMod 2), g • a = a)
    (c : WordCoh.TwoCocycle L) (m : X → L) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (w : PWord X) (hres : PWord.ResolvedAt (WordCoh.lift m c) E E₂ w) :
    moduleRel w m (centralModuleCocycle htriv c) = hessRelZ m c E E₂ w := by
  have hmap := PWord.map_eval
    ⟨moduleExtToCentExt htriv c, continuous_of_discreteTopology⟩
    (ModuleExt.lift (centralModuleCocycle htriv c) m) w
  have hfib := congrArg WordCoh.CentExt.fib hmap
  change moduleRel w m (centralModuleCocycle htriv c) =
    (PWord.eval (WordCoh.lift m c) w).fib at hfib
  rw [PWord.eval_eq_evalZ _ E E₂ w hres] at hfib
  exact hfib

/-- A global module obstruction whose normalized cocycle is an explicit central pullback is
the evaluated Hessian at the pushed generator marking. -/
theorem moduleObsFun_eq_hessRelZ_of_normalized_pullback
    {iota rel : Type*} {G L : Type}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    [Group L] [TopologicalSpace L] [DiscreteTopology L] [Finite L]
    [TopologicalSpace (ZMod 2)] [IsTopologicalAddGroup (ZMod 2)]
    [DiscreteTopology (ZMod 2)] [DistribMulAction G (ZMod 2)]
    [ContinuousSMul G (ZMod 2)] [DistribMulAction L (ZMod 2)]
    (htrivG : ∀ (g : G) (a : ZMod 2), g • a = a)
    (htrivL : ∀ (g : L) (a : ZMod 2), g • a = a)
    (W : rel → PWord iota) (gen : iota → G) (rho : ContinuousMonoidHom G L)
    (f : Z2 G (ZMod 2)) (c : WordCoh.TwoCocycle L)
    (hpull : ∀ x y : G, moduleNormalize f.1 (x, y) = c.κ (rho x) (rho y))
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (k : rel)
    (hres : PWord.ResolvedAt (WordCoh.lift (fun i ↦ rho (gen i)) c) E E₂ (W k)) :
    moduleObsFun W gen rho (fun g a ↦ (htrivG g a).trans (htrivL (rho g) a).symm) f k =
      hessRelZ (fun i ↦ rho (gen i)) c E E₂ (W k) := by
  let U : OpenNormalSubgroup G := moduleActionKerON rho
  have hU : U.toSubgroup ≤ rho.toMonoidHom.ker := le_rfl
  let phi : (G ⧸ U.toSubgroup) →* L := quotientActionHom rho U hU
  letI : DistribMulAction (G ⧸ U.toSubgroup) (ZMod 2) :=
    DistribMulAction.compHom (ZMod 2) phi
  have hphi : ∀ (g : G ⧸ U.toSubgroup) (a : ZMod 2), g • a = phi g • a :=
    fun _ _ ↦ rfl
  let F : ModuleLevelFactor rho (moduleNormalize f.1) :=
    { V := U
      hV := hU
      z := (centralModuleCocycle htrivL c).comap phi hphi
      hfact := by
        intro x y
        rw [hpull]
        rfl }
  rw [moduleObsFun_eq W gen rho _ f F]
  change moduleRel (W k) (fun i ↦ QuotientGroup.mk' U.toSubgroup (gen i)) F.z = _
  rw [← moduleRel_comap (W k)
    (fun i ↦ QuotientGroup.mk' U.toSubgroup (gen i))
    (centralModuleCocycle htrivL c) phi hphi]
  change moduleRel (W k) (fun i ↦ rho (gen i)) (centralModuleCocycle htrivL c) = _
  exact moduleRel_eq_hessRelZ htrivL c _ E E₂ (W k) hres

/-! ## Graph pullbacks -/

/-- The crossed-cocycle graph as a homomorphism into the module-side semidirect product. -/
noncomputable def graphSemiProdHom
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    {G : Type} [Group G] [TopologicalSpace G]
    {rho : ContinuousMonoidHom G (Bg ⧸ D.M)}
    (c : VCocycle DD rho) : G →* SectionSix.SemiProd DD.C0 DD.Vmod where
  toFun g := (c.c g, rho0 DD rho g)
  map_one' := Prod.ext c.c_one (map_one (rho0 DD rho))
  map_mul' g h := Prod.ext (c.crossed g h) (map_mul (rho0 DD rho) g h)

@[simp] theorem graphSemiProdHom_apply
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    {G : Type} [Group G] [TopologicalSpace G]
    {rho : ContinuousMonoidHom G (Bg ⧸ D.M)}
    (c : VCocycle DD rho) (g : G) :
    graphSemiProdHom c g = (c.c g, rho0 DD rho g) := rfl

/-- A `VCocycle` is continuous as a map to the discrete module whenever that topology is
installed. -/
theorem continuous_vcocycle_c_generic
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    {G : Type} [Group G] [TopologicalSpace G]
    {rho : ContinuousMonoidHom G (Bg ⧸ D.M)}
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    (c : VCocycle DD rho) : Continuous c.c := by
  have hlc : IsLocallyConstant c.c := by
    intro s
    have hpre : c.c ⁻¹' s
        = (fun g => iV DD (Multiplicative.ofAdd (c.c g))) ⁻¹'
            ((fun v => iV DD (Multiplicative.ofAdd v)) '' s) := by
      ext g
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro h
        exact ⟨c.c g, h, rfl⟩
      · rintro ⟨v, hv, heq⟩
        rwa [← iV_ofAdd_inj DD heq]
    rw [hpre]
    exact IsOpen.preimage c.cont (isOpen_discrete _)
  exact hlc.continuous

/-- The graph homomorphism is continuous into the finite discrete semidirect target. -/
theorem continuous_graphSemiProdHom
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    {G : Type} [Group G] [TopologicalSpace G]
    {rho : ContinuousMonoidHom G (Bg ⧸ D.M)}
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    (c : VCocycle DD rho) : Continuous (graphSemiProdHom c) := by
  haveI : DiscreteTopology (Bg ⧸ D.M) := CentralObstruction.discreteTopology_quotient D
  have hp : Continuous fun g => ((c.c g, rho0 DD rho g) : DD.Vmod × DD.C0) :=
    (continuous_vcocycle_c_generic c).prodMk
    ((continuous_of_discreteTopology (f := fun x : Bg ⧸ D.M => liftC0 DD x)).comp
      rho.continuous)
  have hlc : IsLocallyConstant fun g => ((c.c g, rho0 DD rho g) : DD.Vmod × DD.C0) :=
    fun s => IsOpen.preimage hp (isOpen_discrete s)
  change IsLocallyConstant (graphSemiProdHom c) at hlc
  exact hlc.continuous

/-- The graph pullback is the module-side `κ⁰` cocycle pulled back along the graph
homomorphism, on the nose. -/
theorem graphPullback_eq_dyadicKappa0_graph
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    {G : Type} [Group G] [TopologicalSpace G]
    {rho : ContinuousMonoidHom G (Bg ⧸ D.M)}
    {q0 : DD.Vmod → ZMod 2} (hdat : IsEquivariantFactorSet q0 DD.dat)
    (c : VCocycle DD rho) (g h : G) :
    graphPullback DD.dat (fun x ↦ rho0 DD rho x) c.c (g, h) =
      (GQ2.Dyadic.kappa0Cocycle DD.dat hdat).κ
        (graphSemiProdHom c g) (graphSemiProdHom c h) := rfl

/-- The coefficient-independent L exponent resolves every `ω₂`-only word in the concrete
`κ⁰` central extension.  The factor `4` is the sharp extraspecial lift-level constant. -/
theorem kappa0_resolvedAt_uniform
    {C V X : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
    [Finite C] [Finite V] [Finite (SectionSix.SemiProd C V)] {q0 : V → ZMod 2}
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat)
    (hV2 : ∀ v : V, v + v = 0)
    (m : X → SectionSix.SemiProd C V) (w : PWord X) (hw : w.IsOmega2Only) :
    PWord.ResolvedAt (WordCoh.lift m (GQ2.Dyadic.kappa0Cocycle dat hdat))
      (fun _ ↦ (omega2Exp
        (4 * Monoid.exponent (SectionSix.SemiProd C V)) : ℤ))
      (fun _ ↦ (omega2Exp
        (4 * Monoid.exponent (SectionSix.SemiProd C V)) : ℤ)) w := by
  let L := SectionSix.SemiProd C V
  let N := 4 * Monoid.exponent L
  have hN : N ≠ 0 := (fourMulExponent_ne_zero_and_even L).1
  have hord : ∀ p : WordCoh.CentExt (GQ2.Dyadic.kappa0Cocycle dat hdat),
      orderOf p ∣ N := by
    intro p
    rw [orderOf_dvd_iff_pow_eq_one]
    apply kappa0_pow_eq_one_of_snd_pow dat hdat hV2
    have hb : p.base ^ Monoid.exponent L = 1 := Monoid.pow_exponent_eq_one p.base
    calc
      p.base.2 ^ Monoid.exponent L = sdSnd (p.base ^ Monoid.exponent L) :=
        (map_pow (sdSnd : L →* C) p.base _).symm
      _ = 1 := by rw [hb]; exact map_one _
  apply PWord.resolvedAt_of_isOmega2Only _ _ _ _ w hw
  intro p
  simpa only [N, L] using PWord.zpowHat_omega2_zpow hN (hord p)

/-! ## The exact improved-L representative formula -/

/-- The source scalar phase of a crossed cocycle is exactly the sum of the evaluated `κ⁰`
Hessians of the tame relator and the improved `L_sq` relator at its graph marking.

This is the representative-level seam between `QZero`/`moduleObsFun` and the word Hessian.
The tame coordinate is intentionally explicit: removing it requires a separate normal-form
vanishing theorem. -/
theorem QZero_eq_lUniform_graphHessianTrace
    {h q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [Finite DD.Vmod] [Finite DD.C0]
    {q0 : DD.Vmod → ZMod 2} (hdat : IsEquivariantFactorSet q0 DD.dat)
    (hq : Even q) (c : VCocycle DD rho) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
      scalarActionZmodTwo ((gamma h q : Type))
    letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul ((gamma h q : Type))
    QZero DD rho c =
      hessRelZ
          (fun i ↦ graphSemiProdHom c
            (gammaGen (2 * h + 1) q (lSqW h) i))
          (GQ2.Dyadic.kappa0Cocycle DD.dat hdat)
          (fun _ ↦ (omega2Exp
            (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : ℤ))
          (fun _ ↦ (omega2Exp
            (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : ℤ))
          (tameRelW (2 * h + 1) q) +
        hessRelZ
          (fun i ↦ graphSemiProdHom c
            (gammaGen (2 * h + 1) q (lSqW h) i))
          (GQ2.Dyadic.kappa0Cocycle DD.dat hdat)
          (fun _ ↦ (omega2Exp
            (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : ℤ))
          (fun _ ↦ (omega2Exp
            (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : ℤ))
          (lSqW h) := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo ((gamma h q : Type))
  letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul ((gamma h q : Type))
  letI : DistribMulAction ((gamma h q : Type)) (MuN 2) :=
    { smul := fun _ a ↦ a
      one_smul := fun _ ↦ rfl
      mul_smul := fun _ _ _ ↦ rfl
      smul_zero := fun _ ↦ rfl
      smul_add := fun _ _ _ ↦ rfl }
  letI : ContinuousSMul ((gamma h q : Type)) (MuN 2) := ⟨continuous_snd⟩
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  let N := 4 * Monoid.exponent L
  let e := omega2Exp N
  let W : Fin 2 → PWord (Generator (2 * h + 1)) :=
    gammaFam (2 * h + 1) q (lSqW h)
  let gen : Generator (2 * h + 1) → (gamma h q : Type) :=
    gammaGen (2 * h + 1) q (lSqW h)
  let graph : ContinuousMonoidHom ((gamma h q : Type)) L :=
    ⟨graphSemiProdHom c, continuous_graphSemiProdHom c⟩
  let kappa := GQ2.Dyadic.kappa0Cocycle DD.dat hdat
  let f : Z2 ((gamma h q : Type)) (ZMod 2) :=
    ⟨graphPullback DD.dat (fun g ↦ rho0 DD rho g) c.c,
      graphPullback_mem_Z2_of_cocycle (fun _ _ ↦ rfl) c⟩
  have he : Odd e := by
    exact odd_omega2Exp (fourMulExponent_ne_zero_and_even L).1
      (fourMulExponent_ne_zero_and_even L).2
  have hresolve : ResolvesAt W (lSqFam h q e) (WordLift (ZMod 2) L) := by
    simpa only [W, e, N, L] using
      (lUniform_wordLift_resolver (C := L) (h := h) (q := q)
        (by decide : ∀ a : ZMod 2, a + a = 0))
  have hr : ∀ k, FreeGroup.lift (fun i ↦ graph (gen i)) (lSqFam h q e k) = 1 :=
    lower_rel (A := ZMod 2) graph (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h)) hresolve
  have hsurj : Function.Surjective
      (lScalarH2WordFlexible graph (fun _ _ ↦ rfl) he) := by
    simpa only [e, N, L] using
      (lUniform_scalarH2WordFlexible_surjective_of_actionImage graph hq)
  let orient : H2 ((gamma h q : Type)) (ZMod 2) ≃+ ZMod 2 :=
    lScalarH2TraceEquiv_of_surjective graph (fun _ _ ↦ rfl) hq he hr hsurj
  have htrace : QZero DD rho c =
      ∑ k, moduleObsFun W gen graph (fun _ _ ↦ rfl) f k := by
    rw [QZero]
    change iotaB f.1 = _
    rw [iotaB_eq_h2Equiv orient f]
    exact lScalarH2TraceEquiv_of_surjective_mk graph (fun _ _ ↦ rfl)
      hq he hr hsurj f
  have hnorm : ∀ x y : (gamma h q : Type),
      moduleNormalize f.1 (x, y) = kappa.κ (graph x) (graph y) := by
    intro x y
    have h11 : f.1 (1, 1) = 0 := by
      change DD.dat.f (c.c 1) (rho0 DD rho 1 • c.c 1) +
        DD.dat.m (rho0 DD rho 1) (c.c 1) = 0
      rw [c.c_one, smul_zero, hdat.f_zero_left, map_one, hdat.m_one, add_zero]
    rw [moduleNormalize, h11, smul_zero, sub_zero]
    exact graphPullback_eq_dyadicKappa0_graph hdat c x y
  have hresolved : ∀ k, PWord.ResolvedAt
      (WordCoh.lift (fun i ↦ graph (gen i)) kappa)
        (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ)) (W k) := by
    intro k
    fin_cases k
    · exact kappa0_resolvedAt_uniform DD.dat hdat (Vmod_exp2 DD) _ _
        (isOmega2Only_tameRelW (2 * h + 1) q)
    · exact kappa0_resolvedAt_uniform DD.dat hdat (Vmod_exp2 DD) _ _
        (isOmega2Only_lSq h)
  have hcoord : ∀ k, moduleObsFun W gen graph (fun _ _ ↦ rfl) f k =
      hessRelZ (fun i ↦ graph (gen i)) kappa
        (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ)) (W k) := by
    intro k
    exact moduleObsFun_eq_hessRelZ_of_normalized_pullback
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) W gen graph f kappa hnorm _ _ k (hresolved k)
  rw [htrace, Fin.sum_univ_two, hcoord, hcoord]
  rfl

/-- The tame Hessian vanishes as soon as the graph's `tau` generator is the identity.  This is
the exact final simplification used by an unramified normal form after its tame row kills the
`tau` coordinate. -/
theorem hessRelZ_tameRelW_eq_zero_of_tau_eq_one
    {n q : ℕ} {L : Type} [Group L]
    (m : Generator n → L) (c : WordCoh.TwoCocycle L)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (hTau : m .tau = 1) :
    hessRelZ m c E E₂ (tameRelW n q) = 0 := by
  have hLift : WordCoh.lift m c (.tau : Generator n) = 1 := by
    apply WordCoh.CentExt.ext
    · exact hTau
    · rfl
  rw [hessRelZ, hessEvalZ, tameRelW, PWord.evalZ_mul, PWord.evalZ_conj,
    PWord.evalZ_gen, PWord.evalZ_gen, PWord.evalZ_inv, PWord.evalZ_zpow,
    PWord.evalZ_gen, hLift]
  simp [conjR]

/-- Under the exact unramified graph normal form (`tau` maps to the identity), the source
phase is the improved `L_sq` Hessian alone. -/
theorem QZero_eq_lUniform_lSqHessian_of_graph_tau_eq_one
    {h q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [Finite DD.Vmod] [Finite DD.C0]
    {q0 : DD.Vmod → ZMod 2} (hdat : IsEquivariantFactorSet q0 DD.dat)
    (hq : Even q) (c : VCocycle DD rho)
    (hTau : graphSemiProdHom c
      (gammaGen (2 * h + 1) q (lSqW h) .tau) = 1) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
      scalarActionZmodTwo ((gamma h q : Type))
    letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul ((gamma h q : Type))
    QZero DD rho c =
      hessRelZ
        (fun i ↦ graphSemiProdHom c (gammaGen (2 * h + 1) q (lSqW h) i))
        (GQ2.Dyadic.kappa0Cocycle DD.dat hdat)
        (fun _ ↦ (omega2Exp
          (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : ℤ))
        (fun _ ↦ (omega2Exp
          (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : ℤ))
        (lSqW h) := by
  rw [QZero_eq_lUniform_graphHessianTrace rho hdat hq c,
    hessRelZ_tameRelW_eq_zero_of_tau_eq_one _ _ _ _ hTau, zero_add]

/-- Once a cocycle representative has the improved graph normal form, its source phase is the
Wall head plus the `h` hyperbolic handle planes.  Thus the only remaining quotient-level input
is the existence and uniqueness of these normal-form representatives. -/
theorem QZero_eq_lSqWallHandlePhase_of_graph_normalForm
    {h q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [Finite DD.Vmod] [Finite DD.C0]
    {q0 : DD.Vmod → ZMod 2} (hdat : IsEquivariantFactorSet q0 DD.dat)
    (hq : Even q) (c : VCocycle DD rho) (s u : DD.C0)
    (v : Fin (2 * h + 1 + 1) → DD.Vmod)
    (hmark : (fun i ↦ graphSemiProdHom c
      (gammaGen (2 * h + 1) q (lSqW h) i)) = lSqHessMark s u v)
    (hTau : graphSemiProdHom c
      (gammaGen (2 * h + 1) q (lSqW h) .tau) = 1)
    (hv0 : v (lSqIdx0 h) = 0) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
      scalarActionZmodTwo ((gamma h q : Type))
    letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul ((gamma h q : Type))
    QZero DD rho c =
      lSqWallHandlePhase q0
        (smulAddEquiv
          ((s ^ (omega2Exp
            (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : ℤ))⁻¹)) h
        (v (lSqIdx1 h), fun j ↦ (v (lSqIdxU j), v (lSqIdxV j))) := by
  rw [QZero_eq_lUniform_lSqHessian_of_graph_tau_eq_one rho hdat hq c hTau, hmark,
    hessRelZ_lSq DD.dat hdat (Vmod_exp2 DD) s u v hv0]
  rfl

end

end GQ2.Dyadic.LSquare

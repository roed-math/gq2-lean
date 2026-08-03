/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLGraphHessian
import GQ2.Dyadic.Instances.GammaLRamifiedPhase

/-!
# Ramified graph normal forms for the improved L phase

The graph-Hessian trace has two coordinates, coming from the tame relator and the improved
`L_sq` relator.  In ramified normal coordinates the scalar cocycle vanishes on `sigma` and
`tau`, but the lower tame marking itself does not.  The tame graph therefore lies on the
`kappa0`-free `C`-line rather than at the identity.  This file proves that this is already
enough to kill the tame Hessian, and evaluates the remaining coordinate as the Wall double
with its hyperbolic handle planes.

No Tate duality, Euler characteristic, or field realization is used.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.LSq
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes
open GQ2.Dyadic.Count
open GQ2.QuadraticFp2

/-! ## The fixed lower line target -/

/-- The pure `C`-line in the semidirect product. -/
def semiProdLineHom {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V] :
    C →* SectionSix.SemiProd C V where
  toFun c := (0, c)
  map_one' := Prod.ext (by simp) (by simp)
  map_mul' c d := Prod.ext (by simp [SectionSix.SemiProd.mul_def]) (by simp)

@[simp] theorem semiProdLineHom_apply
    {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V] (c : C) :
    semiProdLineHom (C := C) (V := V) c = (0, c) := rfl

/-- The lower action map embedded in the pure line of its semidirect product.  Unlike
`graphSemiProdHom`, this map is fixed independently of a crossed cocycle. -/
noncomputable def lGraphLineHom
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} (DD : DescData D)
    {G : Type} [Group G] [TopologicalSpace G]
    (rho : ContinuousMonoidHom G (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0] :
    ContinuousMonoidHom G (SectionSix.SemiProd DD.C0 DD.Vmod) where
  toMonoidHom := graphSemiProdHom (0 : VCocycle DD rho)
  continuous_toFun := continuous_graphSemiProdHom (0 : VCocycle DD rho)

@[simp] theorem lGraphLineHom_apply
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} (DD : DescData D)
    {G : Type} [Group G] [TopologicalSpace G]
    (rho : ContinuousMonoidHom G (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0] (g : G) :
    lGraphLineHom DD rho g = (0, rho0 DD rho g) := by
  rfl

/-- The source `H¹` equivalence in ramified graph coordinates, built at the fixed pure-line
target.  Taking the semidirect product as the finite target synchronizes the uniform resolver
exponent with the graph-Hessian calculation.  All tame and improved relator-death conditions
are derived from the improved L presentation; the only action hypotheses are the ramified
fixed-point conditions and death of the wild lower image. -/
noncomputable def lSqRamifiedGraphSourceH1Equiv
    {h q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod]
    [DiscreteTopology DD.Vmod] [Finite DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0] [Finite DD.C0]
    [DistribMulAction ((gamma h q : Type)) DD.Vmod]
    [ContinuousSMul ((gamma h q : Type)) DD.Vmod]
    (hcomp : ∀ (g : (gamma h q : Type)) (v : DD.Vmod),
      g • v = rho0 DD rho g • v)
    (hwildBase : ∀ i : Fin (2 * h + 1 + 1),
      rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) = 1)
    (hτfpf : ∀ v : DD.Vmod,
      rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .tau) • v = v → v = 0)
    (hTodd : ∀ v : DD.Vmod,
      powOmega2 (rho0 DD rho
        (gammaGen (2 * h + 1) q (lSqW h) .tau)) • v = v) :
    H1 (gamma h q : Type) DD.Vmod ≃
      DD.Vmod × (Fin h → DD.Vmod × DD.Vmod) := by
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  letI : DistribMulAction L DD.Vmod :=
    DistribMulAction.compHom DD.Vmod (sdSnd : L →* DD.C0)
  letI : TopologicalSpace (WordLift DD.Vmod L) := ⊥
  letI : DiscreteTopology (WordLift DD.Vmod L) := ⟨rfl⟩
  let rhoL : ContinuousMonoidHom ((gamma h q : Type)) L := lGraphLineHom DD rho
  let t := lTargetMarking (h := h) (q := q) rhoL
  let N := 4 * Monoid.exponent L
  let e := omega2Exp N
  have hcompatL : ∀ (g : (gamma h q : Type)) (v : DD.Vmod),
      g • v = rhoL g • v := by
    intro g v
    exact hcomp g v
  have hV₂ : ∀ v : DD.Vmod, v + v = 0 := Vmod_exp2 DD
  have hres : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q e) (WordLift DD.Vmod L) := by
    simpa only [e, N, L] using
      (lUniform_wordLift_resolver (C := L) (h := h) (q := q) hV₂)
  have ht : t.TameRelAt q := by
    have hrel := (isAdmissibleMarkedPresentation_gammaR
      (2 * h + 1) q (lSqW h)).rel rhoL (0 : Fin 2)
    change PWord.eval ⇑t (tameRelW (2 * h + 1) q) = 1 at hrel
    rw [← Marking.eval_def, Certificates.eval_tameRelW] at hrel
    exact mul_inv_eq_one.mp hrel
  have hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : DD.Vmod), t.x i • v = v := by
    intro i v
    change (rho0 DD rho
      (gammaGen (2 * h + 1) q (lSqW h) (.wild i))) • v = v
    rw [hwildBase i, one_smul]
  have hτfpfL : ∀ v : DD.Vmod, t.τ • v = v → v = 0 := by
    intro v hv
    exact hτfpf v hv
  have hToddL : ∀ v : DD.Vmod, powOmega2 t.τ • v = v := by
    intro v
    change sdSnd (powOmega2 (rhoL
      (gammaGen (2 * h + 1) q (lSqW h) .tau))) • v = v
    rw [powOmega2_map (sdSnd : L →* DD.C0), lGraphLineHom_apply]
    exact hTodd v
  have hL : PWord.evalZ ⇑t
      (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ)) (lSqW h) = 1 := by
    have hrel := (isAdmissibleMarkedPresentation_gammaR
      (2 * h + 1) q (lSqW h)).rel rhoL (1 : Fin 2)
    change PWord.eval ⇑t (lSqW h) = 1 at hrel
    have hN : N ≠ 0 := (fourMulExponent_ne_zero_and_even L).1
    have hord : ∀ c : L, orderOf c ∣ N := by
      intro c
      exact (Monoid.order_dvd_exponent c).trans (by
        simpa [N, mul_comm] using dvd_mul_right (Monoid.exponent L) 4)
    have hresolved : PWord.ResolvedAt ⇑t (fun _ ↦ (e : ℤ))
        (fun _ ↦ (e : ℤ)) (lSqW h) :=
      PWord.resolvedAt_of_isOmega2Only _ _ _
        (fun c ↦ PWord.zpowHat_omega2_zpow hN (hord c)) _ (isOmega2Only_lSq h)
    rw [PWord.eval_eq_evalZ _ _ _ _ hresolved] at hrel
    exact hrel
  exact lSqRamifiedSourceH1Equiv rhoL hcompatL hV₂ hres ht hwild hτfpfL hToddL hL

/-! ## The tame coordinate on the pure `C`-line -/

/-- The tame Hessian is zero at every `L_sq` Hessian marking.  Its `sigma` and `tau` lifts lie
on the `kappa0`-free `C`-line, and this line is the image of the homomorphism `hessLineHom`.
Unlike the earlier unramified lemma, neither lower tame generator is required to be the
identity. -/
theorem hessRelZ_tameRelW_lSqHessMark_eq_zero
    {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
    {q0 : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat)
    {h q : ℕ} (s u : C) (v : Fin (2 * h + 1 + 1) → V)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    hessRelZ (lSqHessMark s u v) (kappa0Cocycle dat hdat) E E₂
      (tameRelW (2 * h + 1) q) = 0 := by
  rw [hessRelZ, hessEvalZ, tameRelW, PWord.evalZ_mul, PWord.evalZ_conj,
    PWord.evalZ_gen, PWord.evalZ_gen, PWord.evalZ_inv, PWord.evalZ_zpow,
    PWord.evalZ_gen]
  change WordCoh.CentExt.fib
    (conjR (hessLine dat hdat u) (hessLine dat hdat s) *
      (hessLine dat hdat u ^ (q : ℤ))⁻¹) = 0
  rw [show hessLine dat hdat u = hessLineHom dat hdat u from rfl,
    show hessLine dat hdat s = hessLineHom dat hdat s from rfl,
    ← map_conjR, ← map_zpow, ← map_inv, ← map_mul]
  exact hessLine_fib dat hdat _

/-! ## Representative-level ramified normal form -/

/-- A crossed cocycle whose generator values are in the proved ramified normal form has source
phase equal to the explicit Wall head plus the `h` handle planes.  The only lower-marking
condition is that the wild generators die in `C0`; the tame generators may remain nontrivial.

This is the ramified counterpart of
`QZero_eq_lSqWallHandlePhase_of_graph_normalForm`, with the overly strong `graph(tau)=1`
hypothesis removed. -/
theorem QZero_eq_lSqWallHandlePhase_of_ramifiedNormal
    {h q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [Finite DD.Vmod] [Finite DD.C0]
    {q0 : DD.Vmod → ZMod 2} (hdat : IsEquivariantFactorSet q0 DD.dat)
    (hq : Even q) (c : VCocycle DD rho)
    (hwildBase : ∀ i : Fin (2 * h + 1 + 1),
      rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) = 1)
    (d : DD.Vmod) (z : Fin h × Fin 2 → DD.Vmod)
    (hnormal : ∀ i : Generator (2 * h + 1),
      c.c (gammaGen (2 * h + 1) q (lSqW h) i) = lSqRamifiedNormal h d z i) :
    let s := rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .sigma)
    let N := 4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)
    let U : DD.Vmod ≃+ DD.Vmod :=
      smulAddEquiv (V := DD.Vmod) ((s ^ (omega2Exp N : ℤ))⁻¹)
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
      scalarActionZmodTwo ((gamma h q : Type))
    letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul ((gamma h q : Type))
    QZero DD rho c =
      lSqWallHandlePhase q0 U h (d, fun j ↦ (z (j, 0), z (j, 1))) := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo ((gamma h q : Type))
  letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul ((gamma h q : Type))
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  let N := 4 * Monoid.exponent L
  let E : Zhat → ℤ := fun _ ↦ (omega2Exp N : ℤ)
  let E₂ : ℤ_[2] → ℤ := fun _ ↦ (omega2Exp N : ℤ)
  let s := rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .sigma)
  let u := rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .tau)
  let v : Fin (2 * h + 1 + 1) → DD.Vmod :=
    fun i ↦ lSqRamifiedNormal h d z (.wild i)
  have hmark : (fun i ↦ graphSemiProdHom c
      (gammaGen (2 * h + 1) q (lSqW h) i)) = lSqHessMark s u v := by
    funext i
    cases i with
    | sigma =>
        apply Prod.ext
        · change c.c (gammaGen (2 * h + 1) q (lSqW h) .sigma) = 0
          simpa using hnormal (.sigma : Generator (2 * h + 1))
        · rfl
    | tau =>
        apply Prod.ext
        · change c.c (gammaGen (2 * h + 1) q (lSqW h) .tau) = 0
          simpa using hnormal (.tau : Generator (2 * h + 1))
        · rfl
    | wild i =>
        apply Prod.ext
        · exact hnormal (.wild i)
        · exact hwildBase i
  have hv0 : v (lSqIdx0 h) = 0 := by
    change lSqRamifiedNormal h d z (coreLetter h 0) = 0
    exact lSqRamifiedNormal_core_zero h d z
  rw [QZero_eq_lUniform_graphHessianTrace rho hdat hq c, hmark,
    hessRelZ_tameRelW_lSqHessMark_eq_zero DD.dat hdat s u v E E₂, zero_add,
    hessRelZ_lSq_eq_wallHandlePhase DD.dat hdat (Vmod_exp2 DD) s u v hv0 E E₂]
  change lSqWallHandlePhase q0 (smulAddEquiv ((s ^ E omega2)⁻¹)) h
      (v (lSqIdx1 h), fun j ↦ (v (lSqIdxU j), v (lSqIdxV j))) =
    lSqWallHandlePhase q0
      (smulAddEquiv ((s ^ (omega2Exp N : ℤ))⁻¹)) h
      (d, fun j ↦ (z (j, 0), z (j, 1)))
  congr 1
  apply Prod.ext
  · change lSqRamifiedNormal h d z (coreLetter h 1) = d
    exact lSqRamifiedNormal_core_one h d z
  · funext j
    apply Prod.ext
    · change lSqRamifiedNormal h d z (LSq.handleU j) = z (j, 0)
      exact lSqRamifiedNormal_handleU d z j
    · change lSqRamifiedNormal h d z (LSq.handleV j) = z (j, 1)
      exact lSqRamifiedNormal_handleV d z j

/-! ## Quotient-level phase identity -/

/-- The full pointwise ramified phase identity for the canonical graph normal coordinates.

Every quotient class is represented by a crossed cocycle.  The proved L degree-one normal form
finds a principal-coboundary translate whose generator values are exactly
`lSqRamifiedNormal`.  The representative theorem above evaluates that translate, while
`QZeroBar` and `h1OfVQuot` identify the translated and original quotient classes.  Thus the
former opaque pointwise phase premise is discharged from:

* the improved L presentation and its direct scalar orientation;
* wild death in the lower `C0` marking; and
* the two standard ramified fixed-point hypotheses on `tau`.
-/
theorem lRamifiedPointwisePhaseIdentity_of_graphNormalForm
    {h q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod]
    [DiscreteTopology DD.Vmod] [Finite DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0] [Finite DD.C0]
    [DistribMulAction ((gamma h q : Type)) DD.Vmod]
    [ContinuousSMul ((gamma h q : Type)) DD.Vmod]
    {q0 : DD.Vmod → ZMod 2} (hdat : IsEquivariantFactorSet q0 DD.dat)
    (hq : Even q)
    (hcomp : ∀ (g : (gamma h q : Type)) (v : DD.Vmod),
      g • v = rho0 DD rho g • v)
    (hwildBase : ∀ i : Fin (2 * h + 1 + 1),
      rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) = 1)
    (hτfpf : ∀ v : DD.Vmod,
      rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .tau) • v = v → v = 0)
    (hTodd : ∀ v : DD.Vmod,
      powOmega2 (rho0 DD rho
        (gammaGen (2 * h + 1) q (lSqW h) .tau)) • v = v) :
    let L := SectionSix.SemiProd DD.C0 DD.Vmod
    let N := 4 * Monoid.exponent L
    let s := rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .sigma)
    let U := smulAddEquiv ((s ^ (omega2Exp N : ℤ))⁻¹)
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
      scalarActionZmodTwo ((gamma h q : Type))
    letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul ((gamma h q : Type))
    LRamifiedPointwisePhaseIdentity
      (scalarActionZmodTwo_triv ((gamma h q : Type))) hcomp q0 U h
      (lSqRamifiedGraphSourceH1Equiv rho hcomp hwildBase hτfpf hTodd) := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo ((gamma h q : Type))
  letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul ((gamma h q : Type))
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  letI : DistribMulAction L DD.Vmod :=
    DistribMulAction.compHom DD.Vmod (sdSnd : L →* DD.C0)
  letI : TopologicalSpace (WordLift DD.Vmod L) := ⊥
  letI : DiscreteTopology (WordLift DD.Vmod L) := ⟨rfl⟩
  let rhoL : ContinuousMonoidHom ((gamma h q : Type)) L := lGraphLineHom DD rho
  let t := lTargetMarking (h := h) (q := q) rhoL
  let N := 4 * Monoid.exponent L
  let eN := omega2Exp N
  let s := rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .sigma)
  let U : DD.Vmod ≃+ DD.Vmod :=
    smulAddEquiv (V := DD.Vmod) ((s ^ (eN : ℤ))⁻¹)
  have hcompatL : ∀ (g : (gamma h q : Type)) (v : DD.Vmod),
      g • v = rhoL g • v := by
    intro g v
    exact hcomp g v
  have hV₂ : ∀ v : DD.Vmod, v + v = 0 := Vmod_exp2 DD
  have hres : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q eN) (WordLift DD.Vmod L) := by
    simpa only [eN, N, L] using
      (lUniform_wordLift_resolver (C := L) (h := h) (q := q) hV₂)
  have ht : t.TameRelAt q := by
    have hrel := (isAdmissibleMarkedPresentation_gammaR
      (2 * h + 1) q (lSqW h)).rel rhoL (0 : Fin 2)
    change PWord.eval ⇑t (tameRelW (2 * h + 1) q) = 1 at hrel
    rw [← Marking.eval_def, Certificates.eval_tameRelW] at hrel
    exact mul_inv_eq_one.mp hrel
  have hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : DD.Vmod), t.x i • v = v := by
    intro i v
    change (rho0 DD rho
      (gammaGen (2 * h + 1) q (lSqW h) (.wild i))) • v = v
    rw [hwildBase i, one_smul]
  have hτfpfL : ∀ v : DD.Vmod, t.τ • v = v → v = 0 := by
    intro v hv
    exact hτfpf v hv
  have hToddL : ∀ v : DD.Vmod, powOmega2 t.τ • v = v := by
    intro v
    change sdSnd (powOmega2 (rhoL
      (gammaGen (2 * h + 1) q (lSqW h) .tau))) • v = v
    rw [powOmega2_map (sdSnd : L →* DD.C0), lGraphLineHom_apply]
    exact hTodd v
  have hL : PWord.evalZ ⇑t
      (fun _ ↦ (eN : ℤ)) (fun _ ↦ (eN : ℤ)) (lSqW h) = 1 := by
    have hrel := (isAdmissibleMarkedPresentation_gammaR
      (2 * h + 1) q (lSqW h)).rel rhoL (1 : Fin 2)
    change PWord.eval ⇑t (lSqW h) = 1 at hrel
    have hN : N ≠ 0 := (fourMulExponent_ne_zero_and_even L).1
    have hord : ∀ c : L, orderOf c ∣ N := by
      intro c
      exact (Monoid.order_dvd_exponent c).trans (by
        simpa [N, mul_comm] using dvd_mul_right (Monoid.exponent L) 4)
    have hresolved : PWord.ResolvedAt ⇑t (fun _ ↦ (eN : ℤ))
        (fun _ ↦ (eN : ℤ)) (lSqW h) :=
      PWord.resolvedAt_of_isOmega2Only _ _ _
        (fun c ↦ PWord.zpowHat_omega2_zpow hN (hord c)) _ (isOmega2Only_lSq h)
    rw [PWord.eval_eq_evalZ _ _ _ _ hresolved] at hrel
    exact hrel
  change LRamifiedPointwisePhaseIdentity
    (scalarActionZmodTwo_triv ((gamma h q : Type))) hcomp q0 U h
    (lSqRamifiedGraphSourceH1Equiv rho hcomp hwildBase hτfpf hTodd)
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    let zc : ↥(heisD1 (A := DD.Vmod) ⇑t (lSqFam h q eN)).ker :=
      lSourceZ1Map rhoL hcompatL hres (toZ1 hcomp c)
    obtain ⟨p, hp, _⟩ := lSqFam_ramified_normalForm t hV₂ ht hwild hτfpfL hToddL hL
      zc.1 (AddMonoidHom.mem_ker.mp zc.2)
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp hp
    let cN : VCocycle DD rho := c + vCob DD rho (-a)
    have hnormal : ∀ i : Generator (2 * h + 1),
        cN.c (gammaGen (2 * h + 1) q (lSqW h) i) =
          lSqRamifiedNormal h p.1 p.2 i := by
      intro i
      have hai := congrFun ha i
      change (rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) i)) • a - a =
        c.c (gammaGen (2 * h + 1) q (lSqW h) i) -
          lSqRamifiedNormal h p.1 p.2 i at hai
      change c.c (gammaGen (2 * h + 1) q (lSqW h) i) +
          ((rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) i)) • (-a) - (-a)) =
        lSqRamifiedNormal h p.1 p.2 i
      rw [smul_neg, show
        -((rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) i)) • a) - (-a) =
          -((rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) i)) • a - a) by abel,
        hai]
      abel
    have hquot : (QuotientAddGroup.mk c : VCocycle DD rho ⧸ vCobRange DD rho) =
        QuotientAddGroup.mk cN := by
      rw [QuotientAddGroup.eq_iff_sub_mem]
      refine AddMonoidHom.mem_range.mpr ⟨a, ?_⟩
      rw [vCobHom_apply]
      dsimp [cN]
      have hneg : vCob DD rho (-a) = -vCob DD rho a := by
        simpa only [vCobHom_apply] using (vCobHom DD rho).map_neg a
      rw [hneg]
      abel
    let normalZ : ↥(heisD1 (A := DD.Vmod) ⇑t (lSqFam h q eN)).ker :=
      ⟨lSqRamifiedNormal h p.1 p.2,
        AddMonoidHom.mem_ker.mpr
          (heisD1_lSqRamifiedNormal_eq_zero t hV₂ ht hwild hτfpfL hToddL p.1 p.2)⟩
    have hsourceMap : lSourceZ1Map rhoL hcompatL hres (toZ1 hcomp cN) = normalZ := by
      apply Subtype.ext
      funext i
      exact hnormal i
    have hcoord :
        lSqRamifiedGraphSourceH1Equiv rho hcomp hwildBase hτfpf hTodd
            (H1mk (gamma h q : Type) DD.Vmod (toZ1 hcomp cN)) =
          (p.1, fun j ↦ (p.2 (j, 0), p.2 (j, 1))) := by
      change lSqRamifiedWordH1Equiv t hV₂ ht hwild hτfpfL hToddL hL
          (lSourceH1Equiv rhoL hcompatL hV₂ hres
            (H1mk (gamma h q : Type) DD.Vmod (toZ1 hcomp cN))) = _
      rw [lSourceH1Equiv_mk, hsourceMap]
      exact lSqRamifiedWordH1Equiv_normalClass
        t hV₂ ht hwild hτfpfL hToddL hL p.1 p.2
    rw [hquot, QZeroBar_mk]
    change QZero DD rho cN = lSqWallHandlePhase q0 U h
      (lSqRamifiedGraphSourceH1Equiv rho hcomp hwildBase hτfpf hTodd
        (H1mk (gamma h q : Type) DD.Vmod (toZ1 hcomp cN)))
    rw [hcoord]
    exact QZero_eq_lSqWallHandlePhase_of_ramifiedNormal
      rho hdat hq cN hwildBase p.1 p.2 hnormal

/-- The canonical source/word phase comparison supplied by the ramified graph normal form.
Unlike `sourceWordPhaseComparison_of_lRamifiedPointwise`, this constructor has no pointwise
phase hypothesis: the preceding theorem proves it from the improved presentation and the
ramified action conditions. -/
noncomputable def sourceWordPhaseComparison_lRamifiedGraphNormalForm
    {h q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod]
    [DiscreteTopology DD.Vmod] [Fintype DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0] [Finite DD.C0]
    [DistribMulAction ((gamma h q : Type)) DD.Vmod]
    [ContinuousSMul ((gamma h q : Type)) DD.Vmod]
    {q0 : DD.Vmod → ZMod 2} (hdat : IsEquivariantFactorSet q0 DD.dat)
    (hq : Even q)
    (hcomp : ∀ (g : (gamma h q : Type)) (v : DD.Vmod),
      g • v = rho0 DD rho g • v)
    (hwildBase : ∀ i : Fin (2 * h + 1 + 1),
      rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) = 1)
    (hτfpf : ∀ v : DD.Vmod,
      rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .tau) • v = v → v = 0)
    (hTodd : ∀ v : DD.Vmod,
      powOmega2 (rho0 DD rho
        (gammaGen (2 * h + 1) q (lSqW h) .tau)) • v = v) :
    let L := SectionSix.SemiProd DD.C0 DD.Vmod
    let N := 4 * Monoid.exponent L
    let s := rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .sigma)
    let U := smulAddEquiv ((s ^ (omega2Exp N : ℤ))⁻¹)
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
      scalarActionZmodTwo ((gamma h q : Type))
    letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul ((gamma h q : Type))
    SourceWordPhaseComparison DD rho
      (scalarActionZmodTwo_triv ((gamma h q : Type)))
      (DD.Vmod × (Fin h → DD.Vmod × DD.Vmod))
      (lSqWallHandlePhase q0 U h) := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo ((gamma h q : Type))
  letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul ((gamma h q : Type))
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  let N := 4 * Monoid.exponent L
  let s := rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .sigma)
  let U : DD.Vmod ≃+ DD.Vmod :=
    smulAddEquiv (V := DD.Vmod) ((s ^ (omega2Exp N : ℤ))⁻¹)
  change SourceWordPhaseComparison DD rho
    (scalarActionZmodTwo_triv ((gamma h q : Type)))
    (DD.Vmod × (Fin h → DD.Vmod × DD.Vmod))
    (lSqWallHandlePhase q0 U h)
  exact sourceWordPhaseComparison_of_lRamifiedPointwise
    (scalarActionZmodTwo_triv ((gamma h q : Type))) hcomp q0 U h
    (lSqRamifiedGraphSourceH1Equiv rho hcomp hwildBase hτfpf hTodd)
    (lRamifiedPointwisePhaseIdentity_of_graphNormalForm
      rho hdat hq hcomp hwildBase hτfpf hTodd)

end

end GQ2.Dyadic.LSquare

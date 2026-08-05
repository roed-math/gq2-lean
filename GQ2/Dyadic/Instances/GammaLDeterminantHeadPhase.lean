/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.GammaLDeterminantUnramified
import GQ2.Dyadic.Instances.GammaLDeterminantRamified

/-!
# Head-factored graph marking for the improved L determinant phase

`GammaLGraphNormalForm` and `GammaLRamifiedGraphPhase` compute the source phase from a graph
marking whose lower coordinates are literally trivial in `DD.C0`: `rho0 DD rho (x_i) = 1` (and,
in the unramified file, `rho0 DD rho tau = 1` as well).  At the block enrichment consumed by
`AffineDeterminantCertificate` those equations are **not available**: there `DD.C0` is the
recursion frame's `Y ⧸ K`, `rho0` is the boundary lift itself, and a boundary lift is only
constrained at the *head* `T.piY`.  The wild letters die after `blockProjF : Y ⧸ K →* H_V`, not
before it; this is exactly how the closed `ℚ₂` twins
(`GQ2.SectionNine.gaussZResidueD_gammaR_unramified`) state the same facts.

This file removes that gap once and for all, at the level where the phase is computed.  The
module-side `κ⁰` cocycle of a reindexed factor set is the pullback of the base cocycle along the
semidirect projection (`kappa0Cocycle_comap_semiProdProjHom`), so the evaluated Hessian may be
computed after pushing the graph marking down to `V ⋊ C̄`.  Both branch words then see a genuine
`lSqHessMark`, and the source phase formula
`QZero_eq_lSqWallHandlePhase_of_headMark` holds with the wild letters required trivial only in
`C̄`.

No new interface is introduced: the conclusion is the same `lSqWallHandlePhase` value used by
`GammaLDeterminantUnramified`/`GammaLDeterminantRamified`, with the Wall head operator taken at
the pushed `sigma`.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.LSq
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes
open GQ2.Dyadic.Count
open GQ2.QuadraticFp2

/-! ## Level change for the module-side `κ⁰` -/

/-- The semidirect projection `V ⋊ C' →* V ⋊ C` along a group map `π` whose pullback is the
`C'`-action.  Module-side twin of `GQ2.SectionNine.sdProjHom`. -/
def semiProdProjHom {C C' V : Type} [Group C] [Group C'] [AddCommGroup V]
    [DistribMulAction C V] [DistribMulAction C' V] (π : C' →* C)
    (hpi : ∀ (c : C') (v : V), c • v = π c • v) :
    SectionSix.SemiProd C' V →* SectionSix.SemiProd C V where
  toFun p := (p.1, π p.2)
  map_one' := Prod.ext rfl (map_one π)
  map_mul' p r := Prod.ext (by simpa using hpi p.2 r.1) (map_mul π p.2 r.2)

@[simp] theorem semiProdProjHom_apply {C C' V : Type} [Group C] [Group C'] [AddCommGroup V]
    [DistribMulAction C V] [DistribMulAction C' V] (π : C' →* C)
    (hpi : ∀ (c : C') (v : V), c • v = π c • v) (p : SectionSix.SemiProd C' V) :
    semiProdProjHom π hpi p = (p.1, π p.2) := rfl

/-- Two 2-cocycles with the same cochain agree (the remaining fields are proofs). -/
private theorem twoCocycle_ext' {L : Type} [Group L] {c₁ c₂ : WordCoh.TwoCocycle L}
    (hk : c₁.κ = c₂.κ) : c₁ = c₂ := by
  cases c₁
  cases c₂
  cases hk
  rfl

/-- **`κ⁰` at a reindexed factor set is the pulled-back base `κ⁰`.**  The cochain sees the
acting group only through `dat.m`, so pre-composing `m` with `π` is exactly pulling back along
`semiProdProjHom π`.  Module-side twin of `GQ2.SectionNine.kappa0Cocycle_reindexHom`. -/
theorem kappa0Cocycle_comap_semiProdProjHom
    {C C' V : Type} [Group C] [Group C'] [AddCommGroup V]
    [DistribMulAction C V] [DistribMulAction C' V]
    {q0 q1 : V → ZMod 2}
    (base : FactorSet C V) (hbase : IsEquivariantFactorSet q0 base)
    (dat : FactorSet C' V) (hdat : IsEquivariantFactorSet q1 dat)
    (π : C' →* C) (hpi : ∀ (c : C') (v : V), c • v = π c • v)
    (hf : ∀ a b : V, dat.f a b = base.f a b)
    (hm : ∀ (c : C') (v : V), dat.m c v = base.m (π c) v) :
    GQ2.Dyadic.kappa0Cocycle dat hdat =
      (GQ2.Dyadic.kappa0Cocycle base hbase).comap (semiProdProjHom π hpi) := by
  refine twoCocycle_ext' (funext fun p ↦ funext fun r ↦ ?_)
  show dat.f p.1 (p.2 • r.1) + dat.m p.2 r.1
    = base.f p.1 (π p.2 • r.1) + base.m (π p.2) r.1
  rw [hf, hm, hpi]

/-! ## The head-factored source phase formula -/

set_option maxHeartbeats 1600000 in
/-- **The improved-L source phase from a head-level graph normal form.**

The cocycle `c` is assumed to be in `L_sq` normal coordinates (vanishing on `sigma` and `tau`,
offsets `v` on the wild letters, with the `x₀` offset zero), and the wild letters are assumed
trivial *after* `π`.  Neither `tau` nor the wild letters need to be trivial in `DD.C0`.

This is the replacement for `QZero_eq_lSqWallHandlePhase_of_graph_normalForm` and
`QZero_eq_lSqWallHandlePhase_of_ramifiedNormal` at a boundary lift, where only the head
factorization is available. -/
theorem QZero_eq_lSqWallHandlePhase_of_headMark
    {h q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    {Cbar : Type} [Group Cbar] [DistribMulAction Cbar DD.Vmod]
    {q0 : DD.Vmod → ZMod 2} (hdat : IsEquivariantFactorSet q0 DD.dat)
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet q0 base)
    (π : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = π cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (π cc) v)
    (hq : Even q) (c : VCocycle DD rho)
    (hwildHead : ∀ i : Fin (2 * h + 1 + 1),
      π (rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) (.wild i))) = 1)
    (v : Fin (2 * h + 1 + 1) → DD.Vmod)
    (hcsigma : c.c (gammaGen (2 * h + 1) q (lSqW h) .sigma) = 0)
    (hctau : c.c (gammaGen (2 * h + 1) q (lSqW h) .tau) = 0)
    (hcwild : ∀ i : Fin (2 * h + 1 + 1),
      c.c (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) = v i)
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
          ((π (rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .sigma)) ^
            (omega2Exp
              (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : ℤ))⁻¹)) h
        (v (lSqIdx1 h), fun j ↦ (v (lSqIdxU j), v (lSqIdxV j))) := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo ((gamma h q : Type))
  letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul ((gamma h q : Type))
  set N := 4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod) with hN
  set E : Zhat → ℤ := fun _ ↦ (omega2Exp N : ℤ) with hE
  set E₂ : ℤ_[2] → ℤ := fun _ ↦ (omega2Exp N : ℤ) with hE₂
  set φ := semiProdProjHom (V := DD.Vmod) π hpi with hφ
  set s := π (rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .sigma)) with hs
  set u := π (rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .tau)) with hu
  have hmark : (fun i ↦ φ (graphSemiProdHom c (gammaGen (2 * h + 1) q (lSqW h) i)))
      = lSqHessMark s u v := by
    funext i
    cases i with
    | sigma => exact Prod.ext hcsigma rfl
    | tau => exact Prod.ext hctau rfl
    | wild i => exact Prod.ext (hcwild i) (hwildHead i)
  rw [QZero_eq_lUniform_graphHessianTrace rho hdat hq c,
    kappa0Cocycle_comap_semiProdProjHom base hbase DD.dat hdat π hpi hf hm]
  rw [show (fun _ : Zhat ↦ (omega2Exp
        (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : ℤ)) = E from rfl,
    show (fun _ : ℤ_[2] ↦ (omega2Exp
        (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : ℤ)) = E₂ from rfl,
    ← hessRelZ_comap (GQ2.Dyadic.kappa0Cocycle base hbase) E E₂
      (fun i ↦ graphSemiProdHom c (gammaGen (2 * h + 1) q (lSqW h) i)) φ
      (tameRelW (2 * h + 1) q),
    ← hessRelZ_comap (GQ2.Dyadic.kappa0Cocycle base hbase) E E₂
      (fun i ↦ graphSemiProdHom c (gammaGen (2 * h + 1) q (lSqW h) i)) φ (lSqW h),
    hmark, hessRelZ_tameRelW_lSqHessMark_eq_zero base hbase s u v E E₂, zero_add,
    hessRelZ_lSq_eq_wallHandlePhase base hbase (Vmod_exp2 DD) s u v hv0 E E₂]

/-! ## The head-factored source/word phase comparison -/

set_option maxHeartbeats 1600000 in
/-- **The head-factored replacement for `sourceWordPhaseComparison_of_lSqGraphNormalForm`.**

Identical to that theorem except that the lower marking conditions are moved past `π`: only
`π (rho0 (x_i)) = 1` is required, and no condition at all is placed on `rho0 tau`.  The word-side
normal form inputs `hmem`/`hnf` are unchanged (they are first-order statements about
`heisD0`/`heisD1` and see only the action). -/
noncomputable def sourceWordPhaseComparison_of_lSqHeadNormalForm
    {h q e : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod]
    [DiscreteTopology DD.Vmod] [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction ((gamma h q : Type)) DD.Vmod]
    [ContinuousSMul ((gamma h q : Type)) DD.Vmod]
    {Cbar : Type} [Group Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (π : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = π cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (π cc) v)
    (hcompat : ∀ (g : (gamma h q : Type)) (v : DD.Vmod),
      g • v = rho0 DD rho g • v)
    (hres : ResolvesAt
      (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q e) (WordLift DD.Vmod DD.C0))
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet (2 * h + 1))
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 * h + 1) q (lSqW h) i)))
    (hq : Even q)
    (hwildHead : ∀ i : Fin (2 * h + 1 + 1),
      π (rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) (.wild i))) = 1)
    (hmem : ∀ p : DD.Vmod × (Fin h → DD.Vmod × DD.Vmod),
      heisD1
        (fun i ↦ Count.rho0Continuous DD rho
          (gammaGen (2 * h + 1) q (lSqW h) i))
        (lSqFam h q e) (lSqPhaseNormal h p) = 0)
    (hnf : ∀ x,
      heisD1
        (fun i ↦ Count.rho0Continuous DD rho
          (gammaGen (2 * h + 1) q (lSqW h) i))
        (lSqFam h q e) x = 0 →
      ∃! p : DD.Vmod × (Fin h → DD.Vmod × DD.Vmod),
        x - lSqPhaseNormal h p ∈ Set.range
          (heisD0 (A := DD.Vmod)
            (fun i ↦ Count.rho0Continuous DD rho
              (gammaGen (2 * h + 1) q (lSqW h) i)))) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
      scalarActionZmodTwo ((gamma h q : Type))
    letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul ((gamma h q : Type))
    letI : Fintype DD.Vmod := Fintype.ofFinite DD.Vmod
    SourceWordPhaseComparison DD rho (scalarActionZmodTwo_triv _)
      (DD.Vmod × (Fin h → DD.Vmod × DD.Vmod))
      (lSqWallHandlePhase DD.qbar
        (smulAddEquiv
          ((π (rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .sigma)) ^
            (omega2Exp
              (4 * Monoid.exponent
                (SectionSix.SemiProd DD.C0 DD.Vmod)) : ℤ))⁻¹)) h) := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo ((gamma h q : Type))
  letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul ((gamma h q : Type))
  letI : Fintype DD.Vmod := Fintype.ofFinite DD.Vmod
  let theta := Count.rho0Continuous DD rho
  let d0 := heisD0 (A := DD.Vmod)
    (fun i ↦ theta (gammaGen (2 * h + 1) q (lSqW h) i))
  let d1 := heisD1 (A := DD.Vmod)
    (fun i ↦ theta (gammaGen (2 * h + 1) q (lSqW h) i)) (lSqFam h q e)
  let normal := lSqPhaseNormal h (A := DD.Vmod)
  let wordEquiv : StokesH1 d0 d1 ≃
      DD.Vmod × (Fin h → DD.Vmod × DD.Vmod) :=
    stokesNormalEquiv d0 d1 normal hmem hnf
  let h1Equiv : H1 (gamma h q : Type) DD.Vmod ≃
      DD.Vmod × (Fin h → DD.Vmod × DD.Vmod) :=
    (lSourceH1Equiv theta hcompat hA2 hres).toEquiv.trans wordEquiv
  let phaseEquiv : (VCocycle DD rho ⧸ vCobRange DD rho) ≃
      DD.Vmod × (Fin h → DD.Vmod × DD.Vmod) :=
    (sourceQuotientH1Equiv hcompat).trans h1Equiv
  have hZ1surj : Function.Surjective (lSourceZ1Map theta hcompat hres) := by
    exact Count.toZ1w_surjective theta hcompat (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h))
      hres hA2 hwildTwo
  let normalZ1 (p : DD.Vmod × (Fin h → DD.Vmod × DD.Vmod)) :
      Z1 (gamma h q : Type) DD.Vmod :=
    Function.surjInv hZ1surj
      ⟨normal p, AddMonoidHom.mem_ker.mpr (hmem p)⟩
  let normalSource (p : DD.Vmod × (Fin h → DD.Vmod × DD.Vmod)) :
      VCocycle DD rho := ofZ1 hcompat (normalZ1 p)
  have hnormalOffsets (p : DD.Vmod × (Fin h → DD.Vmod × DD.Vmod)) :
      (fun i ↦ (normalSource p).c
        (gammaGen (2 * h + 1) q (lSqW h) i)) = normal p := by
    have hs := Function.surjInv_eq hZ1surj
      ⟨normal p, AddMonoidHom.mem_ker.mpr (hmem p)⟩
    have hsv := congrArg Subtype.val hs
    change (fun i ↦ (normalZ1 p).1
      (gammaGen (2 * h + 1) q (lSqW h) i)) = normal p
    simpa [normalZ1, normal, theta] using hsv
  have hnormalClass (p : DD.Vmod × (Fin h → DD.Vmod × DD.Vmod)) :
      phaseEquiv (QuotientAddGroup.mk (normalSource p)) = p := by
    change wordEquiv
      (lSourceH1Equiv theta hcompat hA2 hres
        (H1mk (gamma h q : Type) DD.Vmod (normalZ1 p))) = p
    rw [lSourceH1Equiv_mk]
    have hs := Function.surjInv_eq hZ1surj
      ⟨normal p, AddMonoidHom.mem_ker.mpr (hmem p)⟩
    rw [show lSourceZ1Map theta hcompat hres (normalZ1 p) =
        ⟨normal p, AddMonoidHom.mem_ker.mpr (hmem p)⟩ from hs]
    exact stokesNormalEquiv_normalClass d0 d1 normal hmem hnf p
  refine
    { phaseEquiv := phaseEquiv
      phase_eq := fun x ↦ ?_ }
  let p := phaseEquiv x
  let c := normalSource p
  have hcx : QuotientAddGroup.mk c = x := by
    apply phaseEquiv.injective
    simpa [c, p] using hnormalClass p
  rw [← hcx, QZeroBar_mk]
  let v : Fin (2 * h + 1 + 1) → DD.Vmod := fun i ↦ normal p (.wild i)
  have hcsigma : c.c (gammaGen (2 * h + 1) q (lSqW h) .sigma) = 0 := by
    simpa [c, normal] using congrFun (hnormalOffsets p) (.sigma)
  have hctau : c.c (gammaGen (2 * h + 1) q (lSqW h) .tau) = 0 := by
    simpa [c, normal] using congrFun (hnormalOffsets p) (.tau)
  have hcwild : ∀ i : Fin (2 * h + 1 + 1),
      c.c (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) = v i := by
    intro i
    simpa [c, v] using congrFun (hnormalOffsets p) (.wild i)
  have hv0 : v (lSqIdx0 h) = 0 := by
    change normal p (.wild (lSqIdx0 h)) = 0
    rw [show (.wild (lSqIdx0 h) : Generator (2 * h + 1)) =
        GQ2.Dyadic.Words.LSq.coreLetter h 0 by
      congr 1]
    exact lSqPhaseNormal_core_zero h p
  have hphase := QZero_eq_lSqWallHandlePhase_of_headMark rho DD.hdat base hbase π hpi hf hm
    hq c hwildHead v hcsigma hctau hcwild hv0
  have hpcoords :
      (v (lSqIdx1 h), fun j ↦ (v (lSqIdxU j), v (lSqIdxV j))) = p := by
    apply Prod.ext
    · change normal p (.wild (lSqIdx1 h)) = p.1
      rw [show (.wild (lSqIdx1 h) : Generator (2 * h + 1)) =
          GQ2.Dyadic.Words.LSq.coreLetter h 1 by
        congr 1]
      exact lSqPhaseNormal_core_one h p
    · funext j
      apply Prod.ext
      · simpa only [v, normal, lSqIdxU, GQ2.Dyadic.Words.LSq.handleU] using
          lSqPhaseNormal_handleU p j
      · simpa only [v, normal, lSqIdxV, GQ2.Dyadic.Words.LSq.handleV] using
          lSqPhaseNormal_handleV p j
  rw [hpcoords] at hphase
  have hpc : phaseEquiv (QuotientAddGroup.mk c) = p := by
    simpa [c] using hnormalClass p
  rw [hpc]
  exact hphase

end

end GQ2.Dyadic.LSquare

#print axioms GQ2.Dyadic.LSquare.QZero_eq_lSqWallHandlePhase_of_headMark
#print axioms GQ2.Dyadic.LSquare.sourceWordPhaseComparison_of_lSqHeadNormalForm

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLGraphHessian
import GQ2.Dyadic.Instances.LHeisenbergResolver
import GQ2.Dyadic.Instances.LRamifiedStokes

/-!
# Quotient normal coordinates for the improved L presentation

This file closes the quotient-level seam left by `GammaLGraphHessian`.  Its input is the
first-order, word-complex normal-form statement: every cocycle is uniquely congruent modulo
`heisD0` to an `x1`-supported core together with arbitrary handle coordinates.  From that datum
we construct an actual equivalence from middle word cohomology to the normal coordinates.

The source comparison is representative-level, not only a cardinality comparison.  We use its
surjectivity to lift every normal word cocycle to a continuous source cocycle.  Literal lower
marking identities (`tau = 1` and every wild generator equal to `1`) then turn that lift into the
graph normal form consumed by `QZero_eq_lSqWallHandlePhase_of_graph_normalForm`.

There is no phase or Gauss-sum hypothesis in the construction.  Thus the final
`SourceWordPhaseComparison` is noncircular: uniqueness is purely first-order, while its phase
identity is supplied only afterwards by the graph Hessian theorem.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.LSq
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes
open GQ2.Dyadic.Count

/-! ## Normal coordinates and the abstract quotient equivalence -/

/-- The improved-L normal cochain in the endpoint coordinates used by
`lSqWallHandlePhase`: one `x1` coordinate and `h` ordered handle pairs. -/
def lSqPhaseNormal (h : ℕ) {A : Type*} [AddCommGroup A]
    (p : A × (Fin h → A × A)) : Generator (2 * h + 1) → A :=
  lSqRamifiedNormal h p.1 (fun jk ↦ (finTwoProdAddEquiv.symm (p.2 jk.1)) jk.2)

/-- Rebracket the old handle coordinates into the endpoint pairs used by the improved phase. -/
def lSqPhaseCoordsEquiv (h : ℕ) (A : Type*) [AddCommGroup A] :
    (A × (Fin h × Fin 2 → A)) ≃ (A × (Fin h → A × A)) where
  toFun p := (p.1, fun j ↦ finTwoProdAddEquiv (fun k ↦ p.2 (j, k)))
  invFun p := (p.1, fun jk ↦ (finTwoProdAddEquiv.symm (p.2 jk.1)) jk.2)
  left_inv p := by
    apply Prod.ext
    · rfl
    · funext jk
      rcases jk with ⟨j, k⟩
      fin_cases k <;> rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    · funext j
      apply Prod.ext <;> rfl

@[simp] theorem lSqPhaseNormal_coordsEquiv
    (h : ℕ) {A : Type*} [AddCommGroup A] (p : A × (Fin h × Fin 2 → A)) :
    lSqPhaseNormal h (lSqPhaseCoordsEquiv h A p) =
      lSqRamifiedNormal h p.1 p.2 := by
  unfold lSqPhaseNormal
  congr 1
  funext jk
  rcases jk with ⟨j, k⟩
  fin_cases k <;> rfl

theorem lSqPhaseNormal_eq_coordsSymm
    (h : ℕ) {A : Type*} [AddCommGroup A] (p : A × (Fin h → A × A)) :
    lSqPhaseNormal h p =
      lSqRamifiedNormal h ((lSqPhaseCoordsEquiv h A).symm p).1
        ((lSqPhaseCoordsEquiv h A).symm p).2 := by
  rw [← lSqPhaseNormal_coordsEquiv h ((lSqPhaseCoordsEquiv h A).symm p),
    Equiv.apply_symm_apply]

@[simp] theorem lSqPhaseNormal_sigma
    (h : ℕ) {A : Type*} [AddCommGroup A] (p : A × (Fin h → A × A)) :
    lSqPhaseNormal h p .sigma = 0 := by
  simp [lSqPhaseNormal]

@[simp] theorem lSqPhaseNormal_tau
    (h : ℕ) {A : Type*} [AddCommGroup A] (p : A × (Fin h → A × A)) :
    lSqPhaseNormal h p .tau = 0 := by
  simp [lSqPhaseNormal]

@[simp] theorem lSqPhaseNormal_core_zero
    (h : ℕ) {A : Type*} [AddCommGroup A] (p : A × (Fin h → A × A)) :
    lSqPhaseNormal h p (coreLetter h 0) = 0 := by
  simp [lSqPhaseNormal]

@[simp] theorem lSqPhaseNormal_core_one
    (h : ℕ) {A : Type*} [AddCommGroup A] (p : A × (Fin h → A × A)) :
    lSqPhaseNormal h p (coreLetter h 1) = p.1 := by
  simp [lSqPhaseNormal]

@[simp] theorem lSqPhaseNormal_handleU
    {h : ℕ} {A : Type*} [AddCommGroup A] (p : A × (Fin h → A × A)) (j : Fin h) :
    lSqPhaseNormal h p (handleU j) = (p.2 j).1 := by
  simp [lSqPhaseNormal, finTwoProdAddEquiv]

@[simp] theorem lSqPhaseNormal_handleV
    {h : ℕ} {A : Type*} [AddCommGroup A] (p : A × (Fin h → A × A)) (j : Fin h) :
    lSqPhaseNormal h p (handleV j) = (p.2 j).2 := by
  simp [lSqPhaseNormal, finTwoProdAddEquiv]

/-- The class of a prescribed normal representative in a three-term complex. -/
def stokesNormalClass
    {K0 K1 K2 P : Type*} [AddCommGroup K0] [AddCommGroup K1] [AddCommGroup K2]
    (d0 : K0 →+ K1) (d1 : K1 →+ K2) (normal : P → K1)
    (hmem : ∀ p, d1 (normal p) = 0) (p : P) : StokesH1 d0 d1 :=
  stokesH1Mk d0 d1 ⟨normal p, AddMonoidHom.mem_ker.mpr (hmem p)⟩

/-- Unique normal representatives give a genuine quotient-level bijection, not merely the
cardinality identity recorded by `card_stokesH1_of_normalForm`. -/
theorem stokesNormalClass_bijective
    {K0 K1 K2 P : Type*} [AddCommGroup K0] [AddCommGroup K1] [AddCommGroup K2]
    (d0 : K0 →+ K1) (d1 : K1 →+ K2) (normal : P → K1)
    (hmem : ∀ p, d1 (normal p) = 0)
    (hnf : ∀ x, d1 x = 0 → ∃! p, x - normal p ∈ Set.range d0) :
    Function.Bijective (stokesNormalClass d0 d1 normal hmem) := by
  have key : ∀ (a b : ↥d1.ker),
      stokesH1Mk d0 d1 a = stokesH1Mk d0 d1 b ↔
        b.val - a.val ∈ Set.range d0 := by
    intro a b
    show QuotientAddGroup.mk a = QuotientAddGroup.mk b ↔ _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    show -a.val + b.val ∈ d0.range ↔ b.val - a.val ∈ Set.range d0
    rw [show -a.val + b.val = b.val - a.val from by abel]
    exact AddMonoidHom.mem_range
  constructor
  · intro p p' hpp
    rw [stokesNormalClass, stokesNormalClass, key] at hpp
    obtain ⟨p0, -, huniq⟩ := hnf (normal p) (hmem p)
    have hp : p = p0 := huniq p ⟨0, by simp⟩
    have hp' : p' = p0 := huniq p' (by
      obtain ⟨v, hv⟩ := hpp
      exact ⟨-v, by rw [map_neg, hv]; abel⟩)
    exact hp.trans hp'.symm
  · intro H
    obtain ⟨x, rfl⟩ := stokesH1Mk_surjective d0 d1 H
    obtain ⟨p, hp, -⟩ := hnf x.val (AddMonoidHom.mem_ker.mp x.2)
    exact ⟨p, (key ⟨normal p, AddMonoidHom.mem_ker.mpr (hmem p)⟩ x).mpr hp⟩

/-- The quotient equivalence determined by unique normal representatives. -/
noncomputable def stokesNormalEquiv
    {K0 K1 K2 P : Type*} [AddCommGroup K0] [AddCommGroup K1] [AddCommGroup K2]
    (d0 : K0 →+ K1) (d1 : K1 →+ K2) (normal : P → K1)
    (hmem : ∀ p, d1 (normal p) = 0)
    (hnf : ∀ x, d1 x = 0 → ∃! p, x - normal p ∈ Set.range d0) :
    StokesH1 d0 d1 ≃ P :=
  (Equiv.ofBijective (stokesNormalClass d0 d1 normal hmem)
    (stokesNormalClass_bijective d0 d1 normal hmem hnf)).symm

@[simp] theorem stokesNormalEquiv_normalClass
    {K0 K1 K2 P : Type*} [AddCommGroup K0] [AddCommGroup K1] [AddCommGroup K2]
    (d0 : K0 →+ K1) (d1 : K1 →+ K2) (normal : P → K1)
    (hmem : ∀ p, d1 (normal p) = 0)
    (hnf : ∀ x, d1 x = 0 → ∃! p, x - normal p ∈ Set.range d0) (p : P) :
    stokesNormalEquiv d0 d1 normal hmem hnf
        (stokesNormalClass d0 d1 normal hmem p) = p := by
  exact (Equiv.ofBijective (stokesNormalClass d0 d1 normal hmem)
    (stokesNormalClass_bijective d0 d1 normal hmem hnf)).symm_apply_apply p

/-! ## Source quotient and phase comparison -/

set_option maxHeartbeats 1600000 in
/-- A word-level unique normal form plus literal lower graph coordinates produces the desired
source quotient equivalence and phase comparison.  The hypotheses `hmem` and `hnf` are purely
first-order statements about `heisD0/heisD1`; `hwildTwo` is used only to lift a normal word
cocycle back to a continuous source cocycle. -/
noncomputable def sourceWordPhaseComparison_of_lSqGraphNormalForm
    {h q e : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod]
    [DiscreteTopology DD.Vmod] [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction ((gamma h q : Type)) DD.Vmod]
    [ContinuousSMul ((gamma h q : Type)) DD.Vmod]
    (hcompat : ∀ (g : (gamma h q : Type)) (v : DD.Vmod),
      g • v = rho0 DD rho g • v)
    (hres : ResolvesAt
      (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q e) (WordLift DD.Vmod DD.C0))
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet (2 * h + 1))
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 * h + 1) q (lSqW h) i)))
    (hq : Even q) (s : DD.C0)
    (hsigma : rho0 DD rho
      (gammaGen (2 * h + 1) q (lSqW h) .sigma) = s)
    (htau : rho0 DD rho
      (gammaGen (2 * h + 1) q (lSqW h) .tau) = 1)
    (hwild : ∀ i : Fin (2 * h + 1 + 1), rho0 DD rho
      (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) = 1)
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
          ((s ^ (omega2Exp
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
  have hmark : (fun i ↦ graphSemiProdHom c
      (gammaGen (2 * h + 1) q (lSqW h) i)) = lSqHessMark s 1 v := by
    funext i
    cases i with
    | sigma =>
        apply Prod.ext
        · change c.c (gammaGen (2 * h + 1) q (lSqW h) .sigma) = 0
          simpa [c, normal] using congrFun (hnormalOffsets p) (.sigma)
        · change rho0 DD rho
            (gammaGen (2 * h + 1) q (lSqW h) .sigma) = s
          exact hsigma
    | tau =>
        apply Prod.ext
        · change c.c (gammaGen (2 * h + 1) q (lSqW h) .tau) = 0
          simpa [c, normal] using congrFun (hnormalOffsets p) (.tau)
        · change rho0 DD rho
            (gammaGen (2 * h + 1) q (lSqW h) .tau) = 1
          exact htau
    | wild i =>
        apply Prod.ext
        · change c.c (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) = v i
          simpa [c, v] using congrFun (hnormalOffsets p) (.wild i)
        · change rho0 DD rho
            (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) = 1
          exact hwild i
  have hTau : graphSemiProdHom c
      (gammaGen (2 * h + 1) q (lSqW h) .tau) = 1 := by
    have hm := congrFun hmark (.tau)
    simpa [lSqHessMark] using hm
  have hv0 : v (lSqIdx0 h) = 0 := by
    change normal p (.wild (lSqIdx0 h)) = 0
    rw [show (.wild (lSqIdx0 h) : Generator (2 * h + 1)) =
        GQ2.Dyadic.Words.LSq.coreLetter h 0 by
      congr 1]
    exact lSqPhaseNormal_core_zero h p
  have hphase := QZero_eq_lSqWallHandlePhase_of_graph_normalForm
    rho DD.hdat hq c s 1 v hmark hTau hv0
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

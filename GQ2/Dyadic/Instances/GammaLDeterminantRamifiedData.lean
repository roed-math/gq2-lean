/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.GammaLDeterminantHeadPhase

/-!
# The ramified head graph datum and its phase model

The ramified twin of `GammaLDeterminantUnramifiedData`.  `LRamifiedGraphData` asks for
`rho0 DD rho (x_i) = 1` in `DD.C0`; at the block enrichment only the head-quotient statement
`blockProjF (rho0 (x_i)) = 1` is available, and that is what the closed `ℚ₂` twin
`GQ2.SectionNine.gaussZResidueD_gammaR_ramified` proves.  `LRamifiedHeadData` records the
correct level.

The remaining input in this branch is unchanged: `LRamifiedSourceArfData`, the
presentation-independent statement that the descended continuous source form is a form of Arf
invariant zero.  That record mentions no `C0` datum at all, so it is reused verbatim.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.LSq
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes
open GQ2.Dyadic.Count
open GQ2.QuadraticFp2

local instance finiteSemiProdRamHead {C V : Type} [Group C] [AddCommGroup V]
    [DistribMulAction C V] [Finite V] [Finite C] :
    Finite (SectionSix.SemiProd C V) := inferInstanceAs (Finite (V × C))

/-! ## The ramified source `H¹` equivalence from action-level data -/

set_option maxHeartbeats 1600000 in
/-- `lSqRamifiedGraphSourceH1Equiv` with the wild condition weakened from death in `DD.C0` to
trivial action on `DD.Vmod` — the only way it was used. -/
noncomputable def lSqRamifiedActionSourceH1Equiv
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
    (hwildAct : ∀ (i : Fin (2 * h + 1 + 1)) (v : DD.Vmod),
      rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) • v = v)
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
    exact hwildAct i v
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
      exact (Monoid.order_dvd_exponent c).trans (by simp [N])
    have hresolved : PWord.ResolvedAt ⇑t (fun _ ↦ (e : ℤ))
        (fun _ ↦ (e : ℤ)) (lSqW h) :=
      PWord.resolvedAt_of_isOmega2Only _ _ _
        (fun c ↦ PWord.zpowHat_omega2_zpow hN (hord c)) _ (isOmega2Only_lSq h)
    rw [PWord.eval_eq_evalZ _ _ _ _ hresolved] at hrel
    exact hrel
  exact lSqRamifiedSourceH1Equiv rhoL hcompatL hV₂ hres ht hwild hτfpfL hToddL hL

/-! ## The head-factored pointwise ramified phase identity -/

set_option maxHeartbeats 2400000 in
/-- `lRamifiedPointwisePhaseIdentity_of_graphNormalForm` with every lower marking condition
taken after `π`.  The Wall head operator is the pushed `sigma` at the *upper* uniform
exponent, exactly as in `QZero_eq_lSqWallHandlePhase_of_headMark`. -/
theorem lRamifiedPointwisePhaseIdentity_of_headNormalForm
    {h q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod]
    [DiscreteTopology DD.Vmod] [Finite DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0] [Finite DD.C0]
    [DistribMulAction ((gamma h q : Type)) DD.Vmod]
    [ContinuousSMul ((gamma h q : Type)) DD.Vmod]
    {Cbar : Type} [Group Cbar] [DistribMulAction Cbar DD.Vmod]
    {q0 : DD.Vmod → ZMod 2} (hdat : IsEquivariantFactorSet q0 DD.dat)
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet q0 base)
    (π : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = π cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (π cc) v)
    (hq : Even q)
    (hcomp : ∀ (g : (gamma h q : Type)) (v : DD.Vmod),
      g • v = rho0 DD rho g • v)
    (hwildHead : ∀ i : Fin (2 * h + 1 + 1),
      π (rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) (.wild i))) = 1)
    (hwildAct : ∀ (i : Fin (2 * h + 1 + 1)) (v : DD.Vmod),
      rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) • v = v)
    (hτfpf : ∀ v : DD.Vmod,
      rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .tau) • v = v → v = 0)
    (hTodd : ∀ v : DD.Vmod,
      powOmega2 (rho0 DD rho
        (gammaGen (2 * h + 1) q (lSqW h) .tau)) • v = v) :
    let N := 4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)
    let s := π (rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .sigma))
    let U := smulAddEquiv (V := DD.Vmod) ((s ^ (omega2Exp N : ℤ))⁻¹)
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
      scalarActionZmodTwo ((gamma h q : Type))
    letI : ContinuousSMul ((gamma h q : Type)) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul ((gamma h q : Type))
    LRamifiedPointwisePhaseIdentity
      (scalarActionZmodTwo_triv ((gamma h q : Type))) hcomp q0 U h
      (lSqRamifiedActionSourceH1Equiv rho hcomp hwildAct hτfpf hTodd) := by
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
  let s := π (rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .sigma))
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
    exact hwildAct i v
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
      exact (Monoid.order_dvd_exponent c).trans (by simp [N])
    have hresolved : PWord.ResolvedAt ⇑t (fun _ ↦ (eN : ℤ))
        (fun _ ↦ (eN : ℤ)) (lSqW h) :=
      PWord.resolvedAt_of_isOmega2Only _ _ _
        (fun c ↦ PWord.zpowHat_omega2_zpow hN (hord c)) _ (isOmega2Only_lSq h)
    rw [PWord.eval_eq_evalZ _ _ _ _ hresolved] at hrel
    exact hrel
  change LRamifiedPointwisePhaseIdentity
    (scalarActionZmodTwo_triv ((gamma h q : Type))) hcomp q0 U h
    (lSqRamifiedActionSourceH1Equiv rho hcomp hwildAct hτfpf hTodd)
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
        lSqRamifiedActionSourceH1Equiv rho hcomp hwildAct hτfpf hTodd
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
      (lSqRamifiedActionSourceH1Equiv rho hcomp hwildAct hτfpf hTodd
        (H1mk (gamma h q : Type) DD.Vmod (toZ1 hcomp cN)))
    rw [hcoord]
    let v : Fin (2 * h + 1 + 1) → DD.Vmod :=
      fun i ↦ lSqRamifiedNormal h p.1 p.2 (.wild i)
    have hcsigma : cN.c (gammaGen (2 * h + 1) q (lSqW h) .sigma) = 0 := by
      have := hnormal (.sigma : Generator (2 * h + 1))
      simpa using this
    have hctau : cN.c (gammaGen (2 * h + 1) q (lSqW h) .tau) = 0 := by
      have := hnormal (.tau : Generator (2 * h + 1))
      simpa using this
    have hcwild : ∀ i : Fin (2 * h + 1 + 1),
        cN.c (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) = v i :=
      fun i ↦ hnormal (.wild i)
    have hv0 : v (lSqIdx0 h) = 0 := by
      change lSqRamifiedNormal h p.1 p.2 (coreLetter h 0) = 0
      exact lSqRamifiedNormal_core_zero h p.1 p.2
    have hphase := QZero_eq_lSqWallHandlePhase_of_headMark rho hdat base hbase π hpi hf hm
      hq cN hwildHead v hcsigma hctau hcwild hv0
    have hpcoords :
        (v (lSqIdx1 h), fun j ↦ (v (lSqIdxU j), v (lSqIdxV j))) =
          ((p.1, fun j ↦ (p.2 (j, 0), p.2 (j, 1))) :
            DD.Vmod × (Fin h → DD.Vmod × DD.Vmod)) := by
      apply Prod.ext
      · change lSqRamifiedNormal h p.1 p.2 (coreLetter h 1) = p.1
        exact lSqRamifiedNormal_core_one h p.1 p.2
      · funext j
        apply Prod.ext
        · change lSqRamifiedNormal h p.1 p.2 (LSq.handleU j) = p.2 (j, 0)
          exact lSqRamifiedNormal_handleU p.1 p.2 j
        · change lSqRamifiedNormal h p.1 p.2 (LSq.handleV j) = p.2 (j, 1)
          exact lSqRamifiedNormal_handleV p.1 p.2 j
    rw [hpcoords] at hphase
    exact hphase

/-! ## The ramified head datum and its phase model -/

/-- The concrete lower-action facts needed by the ramified phase model, at the faithful head
quotient.  This is `LRamifiedGraphData` with the wild condition moved past `π`; the two `tau`
conditions are already action-level and unchanged. -/
structure LRamifiedHeadData
    {h q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M))
    {Cbar : Type} [Group Cbar] [DistribMulAction Cbar DD.Vmod]
    (π : DD.C0 →* Cbar) where
  wild_head : ∀ i : Fin (2 * h + 1 + 1),
    π (rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) (.wild i))) = 1
  tau_fixedPointFree : ∀ v : DD.Vmod,
    rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .tau) • v = v → v = 0
  tau_oddPart_fixed : ∀ v : DD.Vmod,
    powOmega2 (rho0 DD rho
      (gammaGen (2 * h + 1) q (lSqW h) .tau)) • v = v

set_option maxHeartbeats 2400000 in
/-- The complete ramified phase model at one finite descended representation, from head-level
data.  Verbatim analogue of `lSqRamifiedPhaseModel_of_graphData`: transport of the source
Arf-zero theorem fixes the Wall-head sign, and the Wall operator's quadratic invariance and
two-power order are proved internally at the head. -/
theorem lSqRamifiedPhaseModel_of_headData
    {h q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod]
    [DiscreteTopology DD.Vmod] [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction ((gamma h q : Type)) DD.Vmod]
    [ContinuousSMul ((gamma h q : Type)) DD.Vmod]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (π : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = π cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (π cc) v)
    (hcompat : ∀ (g : (gamma h q : Type)) (v : DD.Vmod),
      g • v = rho0 DD rho g • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hqe : Even q) (m : ℕ)
    (hcard : Nat.card DD.Vmod = 2 ^ (2 * m))
    (G : LRamifiedHeadData (DD := DD) rho π)
    (S : letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
        scalarActionZmodTwo ((gamma h q : Type))
      LRamifiedSourceArfData rho (scalarActionZmodTwo_triv _) hcompat) :
    letI : Fintype DD.Vmod := Fintype.ofFinite DD.Vmod
    letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
      scalarActionZmodTwo ((gamma h q : Type))
    ∃ (W : Type) (_ : Fintype W) (Q : W → ZMod 2),
      Nonempty (SourceWordPhaseComparison DD rho (scalarActionZmodTwo_triv _) W Q) ∧
      QuadraticFp2.gaussSum Q = (standardNumerics (2 * h + 1)).gaussRam m := by
  letI : Fintype DD.Vmod := Fintype.ofFinite DD.Vmod
  letI : Module (ZMod 2) DD.Vmod :=
    AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact hA2 v)
  letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo ((gamma h q : Type))
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  let N := 4 * Monoid.exponent L
  let c0 := rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .sigma)
  let s := π c0
  let U : DD.Vmod ≃+ DD.Vmod :=
    smulAddEquiv (V := DD.Vmod) ((s ^ (omega2Exp N : ℤ))⁻¹)
  have hwildAct : ∀ (i : Fin (2 * h + 1 + 1)) (v : DD.Vmod),
      rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) • v = v := by
    intro i v
    rw [hpi, G.wild_head i, one_smul]
  let e : H1 (gamma h q : Type) DD.Vmod ≃
      DD.Vmod × (Fin h → DD.Vmod × DD.Vmod) :=
    lSqRamifiedActionSourceH1Equiv rho hcompat hwildAct
      G.tau_fixedPointFree G.tau_oddPart_fixed
  have hUq : ∀ v, DD.qbar (U v) = DD.qbar v := by
    intro v
    change DD.qbar (((s ^ (omega2Exp N : ℤ))⁻¹) • v) = DD.qbar v
    exact factorSet_q_invariant base hbase hA2 _ v
  have hc0Exp : c0 ^ Monoid.exponent L = 1 := by
    let p : L := (0, c0)
    have hp : p ^ Monoid.exponent L = 1 := Monoid.pow_exponent_eq_one p
    calc
      c0 ^ Monoid.exponent L = sdSnd (p ^ Monoid.exponent L) :=
        (map_pow sdSnd p _).symm
      _ = 1 := by rw [hp]; exact map_one sdSnd
  have hsExp : s ^ Monoid.exponent L = 1 := by
    change π c0 ^ Monoid.exponent L = 1
    rw [← map_pow, hc0Exp, map_one]
  have hsN : s ^ N = 1 := by
    rw [show N = Monoid.exponent L * 4 by simp [N, Nat.mul_comm], pow_mul, hsExp, one_pow]
  have hord : orderOf s ∣ N := orderOf_dvd_of_pow_eq_one hsN
  have hN : N ≠ 0 := (fourMulExponent_ne_zero_and_even L).1
  have hresolved : s ^ omega2Exp N = powOmega2 s := powOmega2_pow_eq s hord hN
  have hU2 : ∃ n, (⇑U)^[2 ^ n] = id := by
    refine ⟨(orderOf s).factorization 2, ?_⟩
    have hp : powOmega2 s ^ 2 ^ (orderOf s).factorization 2 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (orderOf_powOmega2_dvd_two_pow s)
    have hinv : (s ^ omega2Exp N)⁻¹ ^ 2 ^ (orderOf s).factorization 2 = 1 := by
      rw [hresolved, inv_pow, hp, inv_one]
    funext v
    dsimp [U]
    show (((s ^ (omega2Exp N : ℤ))⁻¹ • ·)^[2 ^ (orderOf s).factorization 2]) v = v
    rw [zpow_natCast, smul_iterate_apply, hinv, one_smul]
  have hphase : LRamifiedPointwisePhaseIdentity
      (scalarActionZmodTwo_triv ((gamma h q : Type))) hcompat DD.qbar U h e :=
    lRamifiedPointwisePhaseIdentity_of_headNormalForm rho DD.hdat base hbase π hpi hf hm
      hqe hcompat G.wild_head hwildAct G.tau_fixedPointFree G.tau_oddPart_fixed
  have pkg := lRamifiedPhasePackage_standardRam_of_sourceArf_zero
    (scalarActionZmodTwo_triv ((gamma h q : Type))) hcompat
    S.qSource S.source_eq S.arf_zero DD.qbar DD.hquad DD.hns hA2 m
    (by simpa only [Nat.card_eq_fintype_card] using hcard) U hUq hU2 h e hphase
  exact ⟨DD.Vmod × (Fin h → DD.Vmod × DD.Vmod), inferInstance,
    lSqWallHandlePhase DD.qbar U h, pkg.1, pkg.2.2⟩

/-! ## Boundary-lift packaging -/

/-- The general-`q` form of `GQ2.SectionNine.tau_fixed_eq_zero_of_gen`: normality of `⟨t⟩` is
taken as the hypothesis rather than re-derived from the `q = 2` tame relation, so the tame
relation may be `t ↦ t ^ q` for any `q`.  Its producer is `tame_zpowers_normal_pow`. -/
theorem tau_fixed_eq_zero_of_zpowers_normal {C V : Type} [Group C] [AddCommGroup V]
    [DistribMulAction C V] (t : C) (hnorm : (Subgroup.zpowers t).Normal)
    (hsimple : ∀ W : AddSubgroup V,
      (∀ g : C, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hmoved : ∃ v : V, t • v ≠ v) :
    ∀ v : V, t • v = v → v = 0 := by
  set W : AddSubgroup V :=
    { carrier := {v : V | t • v = v}
      zero_mem' := smul_zero t
      add_mem' := fun {a b} ha hb => by
        show t • (a + b) = a + b
        rw [smul_add]
        exact congrArg₂ (· + ·) ha hb
      neg_mem' := fun {a} ha => by
        show t • (-a) = -a
        rw [smul_neg]
        exact congrArg Neg.neg ha } with hW
  have hstab : ∀ g : C, ∀ w ∈ W, g • w ∈ W := fun g w hw => by
    show t • (g • w) = g • w
    have hmem : g⁻¹ * t * g ∈ Subgroup.zpowers t := by
      simpa using hnorm.conj_mem t (Subgroup.mem_zpowers t) g⁻¹
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hfix : (g⁻¹ * t * g) • w = w := by
      rw [← hk]
      exact Subgroup.zpow_mem (MulAction.stabilizer C w)
        (hw : t ∈ MulAction.stabilizer C w) k
    calc t • (g • w) = (t * g) • w := (mul_smul t g w).symm
      _ = (g * (g⁻¹ * t * g)) • w := by rw [show t * g = g * (g⁻¹ * t * g) from by group]
      _ = g • ((g⁻¹ * t * g) • w) := mul_smul _ _ _
      _ = g • w := by rw [hfix]
  rcases hsimple W hstab with hbot | htop
  · exact fun v hv => AddSubgroup.mem_bot.mp (hbot ▸ (hv : v ∈ W))
  · exact absurd (htop.ge (AddSubgroup.mem_top hmoved.choose)) hmoved.choose_spec

set_option linter.unusedVariables false in
set_option maxHeartbeats 2400000 in
/-- **The ramified word phase for the improved L presentation, reduced to the source-Arf datum
alone.**

Every `LRamifiedHeadData` field is a theorem at the head-inflated block enrichment:

* wild death in `H_V` is the tame specialization plus `boundaryLift_headK`;
* `⟨τ_{H_V}⟩` is normal (`tame_zpowers_normal_pow` at the general-`q` relation `hv_relK`), so
  the `τ`-fixed space is `H_V`-stable and `hv_simple` plus `hram` force it to `⊥`;
* `τ_{H_V}` has odd order (`tame_odd_order_pow`), so its `ω₂`-part is trivial.

The only remaining per-lift input is `LRamifiedSourceArfData`, the presentation-independent
arithmetic statement that the descended continuous source form has Arf invariant zero.  This is
the exact ramified analogue of the field side's `RamifiedCertificate` binder in
`GQ2.Dyadic.gaussZResidueDK_ramified`. -/
theorem wordPhaseResidueK_ramified_lSq
    {h q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
    (F : BoundaryFrameK q P H E)
    (tame : ContinuousMonoidHom (gamma h q) (Tq q))
    (pro2 : ContinuousMonoidHom (gamma h q) P)
    (compat : ∀ g : (gamma h q : Type), nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame (gammaGen (2 * h + 1) q (lSqW h) .sigma) = tqSigma q)
    (htameTau : tame (gammaGen (2 * h + 1) q (lSqW h) .tau) = tqTau q)
    (htameWild : ∀ i : Fin (2 * h + 1 + 1),
      tame (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) = 1)
    (m : ℕ)
    (hcard : Nat.card (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod = 2 ^ (2 * m))
    (l : (SectionNine.blockFrame T Blk hE2).DR)
    (hl : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
    (hram :
      letI := blockPS_commGroup Blk
      letI := SectionNine.headAct T Blk
      ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha (tqTau q) • v ≠ v)
    (hsource :
      let En := blockEnrichmentDK T Blk hE2 hq0 hqe F
      let DD := En.descData l hl
      letI : TopologicalSpace DD.Vmod := ⊥
      letI : DiscreteTopology DD.Vmod := ⟨rfl⟩
      letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
        scalarActionZmodTwo ((gamma h q : Type))
      ∀ rho : BoundaryLiftsK (sourceBoundaryMapK tame pro2 compat) F
          (SectionNine.blockFrame T Blk hE2).TC,
        let rhoM := rhoPrimeK (SectionNine.blockFrame T Blk hE2)
          (sourceBoundaryMapK tame pro2 compat) F (En.radData l hl) rfl rho
        letI : DistribMulAction ((gamma h q : Type)) DD.Vmod :=
          DistribMulAction.compHom DD.Vmod (rho0 DD rhoM)
        let hcomp : ∀ (g : (gamma h q : Type)) (v : DD.Vmod),
            g • v = rho0 DD rhoM g • v := fun _ _ ↦ rfl
        LRamifiedSourceArfData rhoM (scalarActionZmodTwo_triv _) hcomp) :
    letI := scalarActionZmodTwo ((gamma h q : Type))
    WordPhaseResidueK (sourceBoundaryMapK tame pro2 compat) F
      (blockEnrichmentDK T Blk hE2 hq0 hqe F) l hl
      (scalarActionZmodTwo_triv _)
      ((standardNumerics (2 * h + 1)).gaussRam m) := by
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := SectionNine.headAct T Blk
  letI := SectionNine.hvAct T Blk
  set b := sourceBoundaryMapK tame pro2 compat with hb
  set En := blockEnrichmentDK T Blk hE2 hq0 hqe F with hEn
  set DD := En.descData l hl with hDD
  have hl' : l.1 ≠ Blk.frattiniK := fun heq => hl (Subtype.ext heq)
  intro rho
  set rhoM := rhoPrimeK (SectionNine.blockFrame T Blk hE2) b F (En.radData l hl) rfl rho
    with hrhoM
  letI : TopologicalSpace DD.C0 :=
    (inferInstance : TopologicalSpace (SectionNine.blockFrame T Blk hE2).YC)
  haveI : DiscreteTopology DD.C0 :=
    (inferInstance : DiscreteTopology (SectionNine.blockFrame T Blk hE2).YC)
  letI : TopologicalSpace DD.Vmod := ⊥
  haveI : DiscreteTopology DD.Vmod := ⟨rfl⟩
  letI : DistribMulAction (SectionNine.blockFrame T Blk hE2).YC DD.Vmod := blockActV Blk
  letI : DistribMulAction (SectionNine.HVq T Blk) DD.Vmod := SectionNine.hvAct T Blk
  set theta := Count.rho0Continuous DD rhoM with htheta
  letI : DistribMulAction ((gamma h q : Type)) DD.Vmod :=
    DistribMulAction.compHom DD.Vmod theta.toMonoidHom
  haveI : ContinuousSMul ((gamma h q : Type)) DD.Vmod := by
    constructor
    have hfac :
        (fun p : ((gamma h q : Type)) × DD.Vmod ↦ p.1 • p.2) =
          (fun p : DD.C0 × DD.Vmod ↦ p.1 • p.2) ∘
            (fun p : ((gamma h q : Type)) × DD.Vmod ↦ (theta p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((theta.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo ((gamma h q : Type))
  have hcompat : ∀ (g : (gamma h q : Type)) (v : DD.Vmod),
      g • v = rho0 DD rhoM g • v := fun _ _ ↦ rfl
  have hround : ∀ γ : (gamma h q : Type), rho0 DD rhoM γ = rho.1.1 γ :=
    rho0_descData_rhoPrimeK b F En l hl rho
  have hheadFac : ∀ γ : (gamma h q : Type),
      SectionNine.blockProjF T Blk (rho0 DD rhoM γ) = headTameSurjK T Blk F (tame γ) := by
    intro γ
    rw [hround γ]
    exact congrArg (⇑(QuotientGroup.mk' (SectionNine.headActKer T Blk)))
      (boundaryLift_headK T Blk hE2 b F rho γ)
  have hwildHead : ∀ i : Fin (2 * h + 1 + 1),
      SectionNine.blockProjF T Blk
        (rho0 DD rhoM (gammaGen (2 * h + 1) q (lSqW h) (.wild i))) = 1 := by
    intro i
    rw [hheadFac, htameWild i]
    show QuotientGroup.mk' (SectionNine.headActKer T Blk) (F.alpha 1) = 1
    rw [map_one, map_one]
  have htauHead :
      SectionNine.blockProjF T Blk
        (rho0 DD rhoM (gammaGen (2 * h + 1) q (lSqW h) .tau)) = hvTauK T Blk F := by
    rw [hheadFac, htameTau]
    rfl
  -- the two ramified tame facts at the faithful head quotient
  have hrelHV : (hvSigmaK T Blk F)⁻¹ * hvTauK T Blk F * hvSigmaK T Blk F
      = hvTauK T Blk F ^ q := hv_relK T Blk F
  haveI hnormHV : (Subgroup.zpowers (hvTauK T Blk F)).Normal :=
    tame_zpowers_normal_pow (hv_genK T Blk F) hrelHV
  have hoddHV : Odd (orderOf (hvTauK T Blk F)) :=
    tame_odd_order_pow (orderOf_pos (hvSigmaK T Blk F)).ne' hq0 hqe hrelHV
  have hramF : ∃ v : DD.Vmod, hvTauK T Blk F • v ≠ v := hram
  have htauFPF : ∀ v : DD.Vmod, hvTauK T Blk F • v = v → v = 0 :=
    tau_fixed_eq_zero_of_zpowers_normal (hvTauK T Blk F) hnormHV
      (SectionNine.hv_simple T Blk) hramF
  have hτfpf : ∀ v : DD.Vmod,
      rho0 DD rhoM (gammaGen (2 * h + 1) q (lSqW h) .tau) • v = v → v = 0 := by
    intro v hv
    apply htauFPF v
    have hstep : rho0 DD rhoM (gammaGen (2 * h + 1) q (lSqW h) .tau) • v
        = SectionNine.blockProjF T Blk
            (rho0 DD rhoM (gammaGen (2 * h + 1) q (lSqW h) .tau)) • v :=
      SectionNine.blockProjF_compat T Blk _ v
    rwa [hstep, htauHead] at hv
  have hTodd : ∀ v : DD.Vmod,
      powOmega2 (rho0 DD rhoM (gammaGen (2 * h + 1) q (lSqW h) .tau)) • v = v := by
    intro v
    have hstep : powOmega2 (rho0 DD rhoM (gammaGen (2 * h + 1) q (lSqW h) .tau)) • v
        = SectionNine.blockProjF T Blk
            (powOmega2 (rho0 DD rhoM (gammaGen (2 * h + 1) q (lSqW h) .tau))) • v :=
      SectionNine.blockProjF_compat T Blk _ v
    rw [hstep, powOmega2_map (SectionNine.blockProjF T Blk), htauHead,
      powOmega2_eq_one_of_odd hoddHV, one_smul]
  exact lSqRamifiedPhaseModel_of_headData rhoM
    (blockDatHVK T Blk hq0 hqe F l hl') (blockDatHV_specK T Blk hq0 hqe F l hl')
    (SectionNine.blockProjF T Blk) (SectionNine.blockProjF_compat T Blk)
    (fun _ _ => rfl) (fun _ _ => rfl) hcompat (Vmod_exp2 DD) hqe m hcard
    { wild_head := hwildHead
      tau_fixedPointFree := hτfpf
      tau_oddPart_fixed := hTodd }
    (hsource rho)

end

end GQ2.Dyadic.LSquare

#print axioms GQ2.Dyadic.LSquare.lSqRamifiedActionSourceH1Equiv
#print axioms GQ2.Dyadic.LSquare.lRamifiedPointwisePhaseIdentity_of_headNormalForm
#print axioms GQ2.Dyadic.LSquare.lSqRamifiedPhaseModel_of_headData
#print axioms GQ2.Dyadic.LSquare.wordPhaseResidueK_ramified_lSq

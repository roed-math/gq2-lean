/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhaseSeam
import GQ2.Dyadic.Instances.GammaLDeterminantRamifiedData

/-!
# Compact-N determinant data

The compact phase seam reduces the determinant clause to a source-to-word phase comparison at
each boundary lift.  This file supplies that comparison for the compact `N` word in both action
branches and packages the result as the branch-free supply used by the frozen `sqrt(-2)` row.

The endpoint form is the same in both branches.  Only the first-order normal-form argument
splits: the unramified branch kills `tau` and pivots on `sigma`, while the ramified branch pivots
on `tau`.  The head factorization and the compact Hessian trace are shared.
-/

namespace GQ2.Dyadic.Instances.WordPhaseCompactNData

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words
open GQ2.Dyadic.Certificates GQ2.QuadraticFp2
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.WordPhaseSeam
open GQ2.Dyadic.LSquare

/-! ## The two compact-N comparisons -/

/-- The compact `N` comparison in the unramified action branch, with all lower marking
conditions stated after the faithful head quotient. -/
noncomputable def wPcNComparison_unramifiedHead
    {alpha h q : Nat}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((GammaR (2 + 2 * h) q (nCompactW alpha h) : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((GammaR (2 + 2 * h) q (nCompactW alpha h) : ProfiniteGrp) : Type) DD.Vmod]
    [ContinuousSMul
      ((GammaR (2 + 2 * h) q (nCompactW alpha h) : ProfiniteGrp) : Type) DD.Vmod]
    {Cbar : Type} [Group Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hcompat : ∀
      (g : ((GammaR (2 + 2 * h) q (nCompactW alpha h) : ProfiniteGrp) : Type))
      (v : DD.Vmod), g • v = rho0 DD rho g • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 + 2 * h) q (nCompactW alpha h) i)))
    (hq0 : q ≠ 0) (hqe : Even q) (halpha : 2 ≤ alpha)
    (htauHead : pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (nCompactW alpha h) .tau)) = 1)
    (hwildHead : ∀ i : Fin (2 + 2 * h + 1), pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (nCompactW alpha h) (.wild i))) = 1)
    (hsigmaFpf : ∀ v : DD.Vmod, pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (nCompactW alpha h) .sigma)) • v = v → v = 0) :
    letI := scalarActionZmodTwo
      ((GammaR (2 + 2 * h) q (nCompactW alpha h) : ProfiniteGrp) : Type)
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) :=
      inferInstance
    SourceWordPhaseComparison DD rho (scalarActionZmodTwo_triv _)
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (wPhCompactWallHandlePhase DD.qbar h) := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((GammaR (2 + 2 * h) q (nCompactW alpha h) : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((GammaR (2 + 2 * h) q (nCompactW alpha h) : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) :=
    inferInstance
  have htauAct : ∀ v : DD.Vmod,
      rho0 DD rho (gammaGen (2 + 2 * h) q (nCompactW alpha h) .tau) • v = v := by
    intro v
    rw [hpi, htauHead, one_smul]
  have hwildAct : ∀ (i : Fin (2 + 2 * h + 1)) (v : DD.Vmod),
      rho0 DD rho (gammaGen (2 + 2 * h) q (nCompactW alpha h) (.wild i)) • v = v := by
    intro i v
    rw [hpi, hwildHead i, one_smul]
  have hsigmaFpf' : ∀ v : DD.Vmod,
      rho0 DD rho (gammaGen (2 + 2 * h) q (nCompactW alpha h) .sigma) • v = v → v = 0 := by
    intro v hv
    apply hsigmaFpf v
    rw [← hpi]
    exact hv
  have hphase : wPmCompactHeadPhase DD rho :=
    wPs_wPmCompactHeadPhase_of_headFactorization rho base hbase pi hpi hf hm
      hqe hq0 halpha hwildHead
  let C := wPmCompactPhaseComparison_of_headPhase rho hcompat hA2 hwildTwo hqe
    (by omega) htauAct hwildAct hsigmaFpf' (scalarActionZmodTwo_triv _) hphase
  rcases C with ⟨phaseEquiv, phase_eq⟩
  exact ⟨phaseEquiv, phase_eq⟩

/-- The compact normal cochain is closed for the shared ramified Fox row. -/
theorem wPcN_compactNormal_closed_ramified
    {h q : Nat} {C A : Type} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (hrow : ∀ x : Generator (2 + 2 * h) → A, heisD1 ⇑t w x =
      ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
          - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
        -(t.σ⁻¹ • x (coreLetter h 2))])
    (p : (A × A) × (Fin h → A × A)) :
    heisD1 ⇑t w (wPmCompactPhaseNormal h p) = 0 := by
  rw [wPmCompactPhaseNormal]
  exact heisD1_evenNormal_eq_zero_of_ramified_row t w hrow _ _ _

/-- The ramified normal-form theorem in endpoint bracketing. -/
theorem wPcN_compactNormalForm_ramified
    {h q : Nat} {C A : Type} [Group C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (hrow : ∀ x : Generator (2 + 2 * h) → A, heisD1 ⇑t w x =
      ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
          - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
        -(t.σ⁻¹ • x (coreLetter h 2))])
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (htauFpf : ∀ a : A, t.τ • a = a → a = 0)
    (hr : ∀ k, FreeGroup.lift ⇑t (w k) = 1) :
    ∀ x, heisD1 (A := A) ⇑t w x = 0 →
      ∃! p : (A × A) × (Fin h → A × A),
        x - wPmCompactPhaseNormal h p ∈ Set.range (heisD0 ⇑t) := by
  intro x hx
  obtain ⟨r, hr0, hu⟩ := evenNormalForm_of_ramified_row t w hrow hwild htauFpf hr x hx
  refine ⟨wPmCompactCoordsEquiv h A r, ?_, ?_⟩
  · show x - wPmCompactPhaseNormal h (wPmCompactCoordsEquiv h A r) ∈ _
    rw [wPmCompactPhaseNormal_coordsEquiv]
    exact hr0
  · intro p hp
    have hpr : (wPmCompactCoordsEquiv h A).symm p = r := by
      refine hu _ ?_
      show x - evenNormal h ((wPmCompactCoordsEquiv h A).symm p).1
        ((wPmCompactCoordsEquiv h A).symm p).2.1
        ((wPmCompactCoordsEquiv h A).symm p).2.2 ∈ _
      exact hp
    rw [← hpr, Equiv.apply_symm_apply]

/-- The compact `N` comparison in the ramified action branch. -/
noncomputable def wPcNComparison_ramifiedHead
    {alpha h q : Nat}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((GammaR (2 + 2 * h) q (nCompactW alpha h) : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((GammaR (2 + 2 * h) q (nCompactW alpha h) : ProfiniteGrp) : Type) DD.Vmod]
    [ContinuousSMul
      ((GammaR (2 + 2 * h) q (nCompactW alpha h) : ProfiniteGrp) : Type) DD.Vmod]
    {Cbar : Type} [Group Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hcompat : ∀
      (g : ((GammaR (2 + 2 * h) q (nCompactW alpha h) : ProfiniteGrp) : Type))
      (v : DD.Vmod), g • v = rho0 DD rho g • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 + 2 * h) q (nCompactW alpha h) i)))
    (hq0 : q ≠ 0) (hqe : Even q) (halpha : 2 ≤ alpha)
    (hwildHead : ∀ i : Fin (2 + 2 * h + 1), pi (rho0 DD rho
      (gammaGen (2 + 2 * h) q (nCompactW alpha h) (.wild i))) = 1)
    (htauFpf : ∀ v : DD.Vmod,
      rho0 DD rho (gammaGen (2 + 2 * h) q (nCompactW alpha h) .tau) • v = v → v = 0)
    (htauOdd : ∀ v : DD.Vmod, powOmega2 (rho0 DD rho
      (gammaGen (2 + 2 * h) q (nCompactW alpha h) .tau)) • v = v) :
    letI := scalarActionZmodTwo
      ((GammaR (2 + 2 * h) q (nCompactW alpha h) : ProfiniteGrp) : Type)
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) :=
      inferInstance
    SourceWordPhaseComparison DD rho (scalarActionZmodTwo_triv _)
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (wPhCompactWallHandlePhase DD.qbar h) := by
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) :=
    inferInstance
  let e := omega2Exp (4 * Monoid.exponent DD.C0)
  let theta := Count.rho0Continuous DD rho
  let t : Marking (2 + 2 * h) DD.C0 :=
    ⟨fun i ↦ theta (gammaGen (2 + 2 * h) q (nCompactW alpha h) i)⟩
  have hbaseOrd : ∀ g : DD.C0, orderOf g ∣ Monoid.exponent DD.C0 :=
    fun g ↦ Monoid.order_dvd_exponent g
  have horder : ∀ p : WordLift DD.Vmod DD.C0,
      orderOf p ∣ 4 * Monoid.exponent DD.C0 := fun p ↦
    (WordLift.orderOf_dvd_two_mul hA2 hbaseOrd p).trans ⟨2, by ring⟩
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW alpha h))
      (nCompactFam alpha h q e) (WordLift DD.Vmod DD.C0) :=
    Count.resolvesAt_nCompactFam (Count.fourMulExponent_ne_zero_and_even DD.C0).1
      horder alpha h q
  have ht : t.TameRelAt q := by
    have hrel := (isAdmissibleMarkedPresentation_gammaR
      (2 + 2 * h) q (nCompactW alpha h)).rel (Count.rho0Continuous DD rho) (0 : Fin 2)
    change PWord.eval ⇑t (tameRelW (2 + 2 * h) q) = 1 at hrel
    rw [← Marking.eval_def, Certificates.eval_tameRelW] at hrel
    exact mul_inv_eq_one.mp hrel
  have hwildAct : ∀ (i : Fin (2 + 2 * h + 1)) (v : DD.Vmod), t.x i • v = v := by
    intro i v
    change rho0 DD rho (gammaGen (2 + 2 * h) q (nCompactW alpha h) (.wild i)) • v = v
    rw [hpi, hwildHead i, one_smul]
  have hrow : ∀ x : Generator (2 + 2 * h) → DD.Vmod, heisD1 ⇑t
      (nCompactFam alpha h q e) x =
        ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
            - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
          -(t.σ⁻¹ • x (coreLetter h 2))] :=
    heisD1_nCompactFam_ramified_apply t hA2 ht hwildAct htauFpf htauOdd (by omega)
  have hr : ∀ k, FreeGroup.lift ⇑t (nCompactFam alpha h q e k) = 1 := fun k ↦
    Count.lower_rel (A := DD.Vmod) theta (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (nCompactW alpha h)) hres k
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((GammaR (2 + 2 * h) q (nCompactW alpha h) : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((GammaR (2 + 2 * h) q (nCompactW alpha h) : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  have hphase : wPmCompactHeadPhase DD rho :=
    wPs_wPmCompactHeadPhase_of_headFactorization rho base hbase pi hpi hf hm
      hqe hq0 halpha hwildHead
  exact wPmPhaseComparison_of_normalForm rho hcompat hres hA2 hwildTwo
    (wPmCompactPhaseNormal h)
    (wPcN_compactNormal_closed_ramified t (nCompactFam alpha h q e) hrow)
    (wPcN_compactNormalForm_ramified t (nCompactFam alpha h q e) hrow hwildAct htauFpf hr)
    (scalarActionZmodTwo_triv _) (wPhCompactWallHandlePhase DD.qbar h) hphase

/-! ## Boundary-lift packaging -/

/-- At a compact `N` boundary lift, the branch data are theorems.  The proof splits on the
action of tame inertia at the faithful head quotient and returns the common even endpoint
comparison. -/
theorem wPcNComparison_boundary
    {alpha h q : Nat} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
    (F : BoundaryFrameK q P H E)
    (tame : ContinuousMonoidHom (NCompact.gamma alpha h q) (Tq q))
    (pro2 : ContinuousMonoidHom (NCompact.gamma alpha h q) P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame (gammaGen (2 + 2 * h) q (nCompactW alpha h) .sigma) = tqSigma q)
    (htameTau : tame (gammaGen (2 + 2 * h) q (nCompactW alpha h) .tau) = tqTau q)
    (htameWild : ∀ i : Fin (2 + 2 * h + 1),
      tame (gammaGen (2 + 2 * h) q (nCompactW alpha h) (.wild i)) = 1)
    (halpha : 2 ≤ alpha)
    (hsimple : ∀ W : AddSubgroup (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod,
      (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) →
        W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod, v ≠ 0)
    (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
      (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g • v ≠ v)
    (l : (SectionNine.blockFrame T Blk hE2).DR)
    (hl : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR) :
    ∀ rho : BoundaryLiftsK (sourceBoundaryMapK tame pro2 compat) F
        (SectionNine.blockFrame T Blk hE2).TC,
      let DD := (blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl
      let rhoM := rhoPrimeK (SectionNine.blockFrame T Blk hE2)
        (sourceBoundaryMapK tame pro2 compat) F
        ((blockEnrichmentDK T Blk hE2 hq0 hqe F).radData l hl) rfl rho
      letI := scalarActionZmodTwo ((NCompact.gamma alpha h q : ProfiniteGrp) : Type)
      letI : Fintype DD.Vmod := Fintype.ofFinite _
      letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) :=
        inferInstance
      Nonempty (SourceWordPhaseComparison DD rhoM (scalarActionZmodTwo_triv _)
        ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
        (wPhCompactWallHandlePhase DD.qbar h)) := by
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := SectionNine.headAct T Blk
  letI := SectionNine.hvAct T Blk
  set b := sourceBoundaryMapK tame pro2 compat with hb
  set En := blockEnrichmentDK T Blk hE2 hq0 hqe F with hEn
  intro rho
  set DD := En.descData l hl with hDD
  have hl' : l.1 ≠ Blk.frattiniK := fun heq ↦ hl (Subtype.ext heq)
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
  letI : DistribMulAction
      ((NCompact.gamma alpha h q : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((NCompact.gamma alpha h q : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  letI : DistribMulAction ((NCompact.gamma alpha h q : ProfiniteGrp) : Type) DD.Vmod :=
    DistribMulAction.compHom DD.Vmod rho.1.1.toMonoidHom
  haveI : ContinuousSMul ((NCompact.gamma alpha h q : ProfiniteGrp) : Type) DD.Vmod := by
    constructor
    have hfac :
        (fun p : ((NCompact.gamma alpha h q : ProfiniteGrp) : Type) × DD.Vmod ↦ p.1 • p.2) =
          (fun p : (SectionNine.blockFrame T Blk hE2).YC × DD.Vmod ↦ p.1 • p.2) ∘
            (fun p ↦ (rho.1.1 p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((rho.1.1.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hround : ∀ gamma : ((NCompact.gamma alpha h q : ProfiniteGrp) : Type),
      rho0 DD rhoM gamma = rho.1.1 gamma :=
    rho0_descData_rhoPrimeK b F En l hl rho
  have hcompat : ∀ (g : ((NCompact.gamma alpha h q : ProfiniteGrp) : Type)) (v : DD.Vmod),
      g • v = rho0 DD rhoM g • v := by
    intro g v
    exact congrArg (fun c : (SectionNine.blockFrame T Blk hE2).YC ↦ c • v) (hround g).symm
  have hsimpleGamma : IsSimpleModTwo
      ((NCompact.gamma alpha h q : ProfiniteGrp) : Type) DD.Vmod := by
    obtain ⟨v, hv⟩ := hVne
    refine ⟨nontrivial_of_ne v 0 hv, ?_⟩
    intro W hW
    apply hsimple W
    intro c w hw
    obtain ⟨g, rfl⟩ := rho.1.2 c
    exact hW g w hw
  have hheadFac : ∀ gamma : ((NCompact.gamma alpha h q : ProfiniteGrp) : Type),
      SectionNine.blockProjF T Blk (rho0 DD rhoM gamma) = headTameSurjK T Blk F (tame gamma) := by
    intro gamma
    rw [hround gamma]
    exact congrArg (⇑(QuotientGroup.mk' (SectionNine.headActKer T Blk)))
      (boundaryLift_headK T Blk hE2 b F rho gamma)
  have hsigmaHead : SectionNine.blockProjF T Blk (rho0 DD rhoM
      (gammaGen (2 + 2 * h) q (nCompactW alpha h) .sigma)) = hvSigmaK T Blk F := by
    rw [hheadFac, htameSigma]
    rfl
  have htauHead : SectionNine.blockProjF T Blk (rho0 DD rhoM
      (gammaGen (2 + 2 * h) q (nCompactW alpha h) .tau)) = hvTauK T Blk F := by
    rw [hheadFac, htameTau]
    rfl
  have hwildHead : ∀ i : Fin (2 + 2 * h + 1), SectionNine.blockProjF T Blk
      (rho0 DD rhoM (gammaGen (2 + 2 * h) q (nCompactW alpha h) (.wild i))) = 1 := by
    intro i
    rw [hheadFac, htameWild i]
    show QuotientGroup.mk' (SectionNine.headActKer T Blk) (F.alpha 1) = 1
    rw [map_one, map_one]
  have hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rhoM
        (gammaGen (2 + 2 * h) q (nCompactW alpha h) i)) :=
    isWildTwo_of_gammaGen (Count.rho0Continuous DD rhoM)
      (rho0Continuous_surjective DD rhoM
        (rhoPrimeK_surjective (SectionNine.blockFrame T Blk hE2) b F
          (En.radData l hl) rfl rho)) (fun _ ↦ rfl)
  have hsurjrho : Function.Surjective
      (fun gamma : ((NCompact.gamma alpha h q : ProfiniteGrp) : Type) ↦ rho0 DD rhoM gamma) :=
    fun y ↦ by
    obtain ⟨gamma, hgamma⟩ := rho.1.2 y
    exact ⟨gamma, (hround gamma).trans hgamma⟩
  have hfix : ∀ v : DD.Vmod,
      (∀ gamma : ((NCompact.gamma alpha h q : ProfiniteGrp) : Type),
        rho0 DD rhoM gamma • v = v) → v = 0 :=
    hfix_of_simple_nt hsurjrho hsimple hnt
  classical
  by_cases hunram : ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P),
      F.alpha (tqTau q) • v = v
  · have htauHeadOne : SectionNine.blockProjF T Blk (rho0 DD rhoM
        (gammaGen (2 + 2 * h) q (nCompactW alpha h) .tau)) = 1 := by
      rw [hheadFac, htameTau]
      show QuotientGroup.mk' (SectionNine.headActKer T Blk) (F.alpha (tqTau q)) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hunram
    have hzp : ∀ x : SectionNine.HVq T Blk, x ∈ Subgroup.zpowers (hvSigmaK T Blk F) := by
      have hle : Subgroup.closure {hvSigmaK T Blk F, hvTauK T Blk F} ≤
          Subgroup.zpowers (hvSigmaK T Blk F) := by
        rw [Subgroup.closure_le, Set.pair_subset_iff]
        refine ⟨Subgroup.mem_zpowers _, ?_⟩
        have htauOne : hvTauK T Blk F = 1 := by
          show QuotientGroup.mk' (SectionNine.headActKer T Blk) (F.alpha (tqTau q)) = 1
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact hunram
        rw [htauOne]
        exact Subgroup.one_mem _
      rw [hv_genK T Blk F] at hle
      exact fun x ↦ hle (Subgroup.mem_top x)
    have hsigmaFpf : ∀ v : DD.Vmod, SectionNine.blockProjF T Blk (rho0 DD rhoM
        (gammaGen (2 + 2 * h) q (nCompactW alpha h) .sigma)) • v = v → v = 0 := by
      intro v hv
      rw [hsigmaHead] at hv
      refine hfix v fun gamma ↦ ?_
      have hstep : rho0 DD rhoM gamma • v =
          SectionNine.blockProjF T Blk (rho0 DD rhoM gamma) • v :=
        SectionNine.blockProjF_compat T Blk _ v
      rw [hstep]
      have hmem : hvSigmaK T Blk F ∈ MulAction.stabilizer (SectionNine.HVq T Blk) v :=
        MulAction.mem_stabilizer_iff.mpr hv
      exact (Subgroup.zpowers_le.mpr hmem)
        (hzp (SectionNine.blockProjF T Blk (rho0 DD rhoM gamma)))
    refine ⟨?_⟩
    simpa only [rhoM, b, En] using
      (wPcNComparison_unramifiedHead rhoM
        (blockDatHVK T Blk hq0 hqe F l hl') (blockDatHV_specK T Blk hq0 hqe F l hl')
        (SectionNine.blockProjF T Blk) (SectionNine.blockProjF_compat T Blk)
        (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hcompat (Vmod_exp2 DD) hwildTwo
        hq0 hqe halpha htauHeadOne hwildHead hsigmaFpf)
  · have hram : ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P),
        F.alpha (tqTau q) • v ≠ v := by
      simpa only [not_forall] using hunram
    have hrelHV : (hvSigmaK T Blk F)⁻¹ * hvTauK T Blk F * hvSigmaK T Blk F =
        hvTauK T Blk F ^ q := hv_relK T Blk F
    haveI hnormHV : (Subgroup.zpowers (hvTauK T Blk F)).Normal :=
      tame_zpowers_normal_pow (hv_genK T Blk F) hrelHV
    have hoddHV : Odd (orderOf (hvTauK T Blk F)) :=
      tame_odd_order_pow (orderOf_pos (hvSigmaK T Blk F)).ne' hq0 hqe hrelHV
    have htauFpf : ∀ v : DD.Vmod, rho0 DD rhoM
        (gammaGen (2 + 2 * h) q (nCompactW alpha h) .tau) • v = v → v = 0 := by
      intro v hv
      apply tau_fixed_eq_zero_of_zpowers_normal (hvTauK T Blk F) hnormHV
        (SectionNine.hv_simple T Blk) hram v
      have hstep : rho0 DD rhoM
          (gammaGen (2 + 2 * h) q (nCompactW alpha h) .tau) • v =
          SectionNine.blockProjF T Blk (rho0 DD rhoM
            (gammaGen (2 + 2 * h) q (nCompactW alpha h) .tau)) • v :=
        SectionNine.blockProjF_compat T Blk _ v
      rwa [hstep, htauHead] at hv
    have htauOdd : ∀ v : DD.Vmod, powOmega2 (rho0 DD rhoM
        (gammaGen (2 + 2 * h) q (nCompactW alpha h) .tau)) • v = v := by
      intro v
      have hstep : powOmega2 (rho0 DD rhoM
          (gammaGen (2 + 2 * h) q (nCompactW alpha h) .tau)) • v =
          SectionNine.blockProjF T Blk (powOmega2 (rho0 DD rhoM
            (gammaGen (2 + 2 * h) q (nCompactW alpha h) .tau))) • v :=
        SectionNine.blockProjF_compat T Blk _ v
      rw [hstep, powOmega2_map (SectionNine.blockProjF T Blk) (rho0 DD rhoM
          (gammaGen (2 + 2 * h) q (nCompactW alpha h) .tau)), htauHead,
        powOmega2_eq_one_of_odd hoddHV, one_smul]
    refine ⟨?_⟩
    simpa only [rhoM, b, En] using
      (wPcNComparison_ramifiedHead rhoM
        (blockDatHVK T Blk hq0 hqe F l hl') (blockDatHV_specK T Blk hq0 hqe F l hl')
        (SectionNine.blockProjF T Blk) (SectionNine.blockProjF_compat T Blk)
        (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hcompat (Vmod_exp2 DD) hwildTwo
        hq0 hqe halpha hwildHead htauFpf htauOdd)

/-! ## The branch-free supply and the frozen row -/

/-- The branch-free determinant supply for the compact `N` word. -/
theorem wPcN_branchFreeSupply
    {alpha h q : Nat} {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (NCompact.gamma alpha h q) (Tq q))
    (pro2 : ContinuousMonoidHom (NCompact.gamma alpha h q) P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame (gammaGen (2 + 2 * h) q (nCompactW alpha h) .sigma) = tqSigma q)
    (htameTau : tame (gammaGen (2 + 2 * h) q (nCompactW alpha h) .tau) = tqTau q)
    (htameWild : ∀ i : Fin (2 + 2 * h + 1),
      tame (gammaGen (2 + 2 * h) q (nCompactW alpha h) (.wild i)) = 1)
    (halpha : 2 ≤ alpha) :
    wPhBranchFreeSupply (2 * h + 2) nuP tame pro2 compat := by
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk _ _ _ hE2 hq0 hqe F
    hsimple hVne hnt m hm hcard l hl rho
  set DD := (blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl with hDD
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) :=
    inferInstance
  refine ⟨(DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod), inferInstance,
    wPhCompactWallHandlePhase DD.qbar h, ?_, ?_⟩
  · simpa only [DD] using
      (wPcNComparison_boundary T Blk hE2 hq0 hqe F tame pro2 compat
        htameSigma htameTau htameWild halpha hsimple hVne hnt l hl rho)
  · exact wPh_compactWallHandlePhase_gaussSum_standardRam DD.hquad DD.hns
      ((Nat.card_eq_fintype_card (α := DD.Vmod)).symm.trans hcard) h

open GQ2.Dyadic.Instances.CanonicalRecords GQ2.Dyadic.Fields
open GQ2.Dyadic.Words TameSpec MarkedCore
open GQ2.Dyadic.SelectedCoreLeavesRN

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] {R : LocalReciprocity}

/-- The frozen `sqrt(-2)` row with its determinant supply discharged.  Only the two existing
coefficient-stage vanishing statements remain. -/
theorem wPcN_candidate_equiv_galK_sqrtNegTwo [T2Space (GalK KSqrtNegTwo)]
    (B : MarkedRecip R KSqrtNegTwo) {FF : DyadicUnitFiltration KSqrtNegTwo}
    (F : GenAsmFieldInputs KSqrtNegTwo B FF (SelectedPresentation.N0 2 0).degree)
    (hvanCand : askCStageVanishing
      (GammaR 2 (qOf KSqrtNegTwo FF) (nCompactW 2 0))
      (qOf KSqrtNegTwo FF) (DN 2 0) (nNuZtwo 2 0))
    (hvanK : askCStageVanishing (galKProfinite KSqrtNegTwo) (qOf KSqrtNegTwo FF)
      (genAsmCore (.N0 2 0)) (nNuZtwo 2 0)) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (SelectedPresentation.N0 2 0).degree (qOf KSqrtNegTwo FF)
        (SelectedPresentation.N0 2 0).word : ProfiniteGrp) : Type) (GalK KSqrtNegTwo)) := by
  apply wPh_candidate_equiv_galK_sqrtNegTwo_branchFree B F ?_ hvanCand hvanK
  apply wPcN_branchFreeSupply
  · simp
  · simp
  · intro i
    simp
  · omega

/-! ## Axiom audit -/

#print axioms wPcNComparison_unramifiedHead
#print axioms wPcN_compactNormal_closed_ramified
#print axioms wPcN_compactNormalForm_ramified
#print axioms wPcNComparison_ramifiedHead
#print axioms wPcNComparison_boundary
#print axioms wPcN_branchFreeSupply
#print axioms wPcN_candidate_equiv_galK_sqrtNegTwo

end

end GQ2.Dyadic.Instances.WordPhaseCompactNData

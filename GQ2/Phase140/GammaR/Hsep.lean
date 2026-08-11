/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Phase140.GammaR.Foundation

/-!
# The `Γ_R` separation and partial-count assembly

The Roe-candidate twin of `GQ2/Phase140/GammaA/Hsep.lean`: the word-side right-slot separator,
the private assembly helpers, and the final `hsep`/`hpartial` calculations.

See `GQ2.Phase140.GammaR` for the paper-facing overview and architectural notes.
-/

namespace GQ2

namespace Phase140GammaR

open SectionEight AffineTLift CentralObstruction ContCoh WordCohBridgeR GQ2.FoxH RStageGammaR
  RStageGammaA RadicalEdgeGammaA WordCoh2 WordCoh2R MixedBObs MixedBObsR

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
variable {RF : RecursionFrame T Blk}
variable (b : ContinuousMonoidHom GammaR ↥boundarySubgroup) (F : BoundaryFrame H E)
  (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)

/-! ## The word-side right-slot separator  (the `hpartial_gammaR` stage-6 engine)

The `Γ_R` replacement for the local `cup11_dualEval_right_separating` (which runs on B6 Tate
duality), and the exact twin of `Phase140GammaA.b1_of_pair_cochain_B2` on the Roe spine: a
continuous dual 1-cocycle `ξ` whose pair cochain `(a,b) ↦ ξ(a)(a • z(b))` is a continuous
coboundary against EVERY `A`-cocycle `z` is itself a coboundary.  Route: the pair cochain is the
`kappaHeis`-inflation of the paired `wordHomR` (`MixedBObsR.obs_inflation_R`), so its
`WordCoh2R.obs_R` equals the traced mixed pairing `mixedB_R (markC_R θ) (evalR z) (evalR ξ)`
(`mixedB_eq_relZPairR`); `obs_R` kills `B²` (`obs_B2_eq_zero_R`), so all word pairings vanish, and
`prop_5_15_R`'s clause-3 RIGHT-slot nondegeneracy forces `[evalR ξ]_w = 0`; `eval_dZeroR` +
`z1EquivR`-injectivity pull the word coboundary back to a continuous one.  No B-axioms. -/

section WordSeparatorR

variable {Cf : Type} [Group Cf] [TopologicalSpace Cf] [DiscreteTopology Cf] [Finite Cf]
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction Cf A]
  [DistribMulAction GR A] [ContinuousSMul GR A]
  [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
  [DistribMulAction GR (ElemDual A)] [ContinuousSMul GR (ElemDual A)]
  [DistribMulAction GR (ZMod 2)] [ContinuousSMul GR (ZMod 2)]
variable (θ : ContinuousMonoidHom GR Cf)

omit [ContinuousSMul GR A] in
private theorem b1_of_pair_cochain_B2_R
    (hcompat : ∀ (γ : GR) (a : A), γ • a = θ γ • a)
    (hcompatD : ∀ (γ : GR) (lam : ElemDual A), γ • lam = θ γ • lam)
    (htriv : ∀ (x : GR) (m : ZMod 2), x • m = m)
    (hθs : Function.Surjective ⇑θ)
    (hA₂ : ∀ a : A, a + a = 0)
    (ξ : ↥(Z1 GR (ElemDual A)))
    (hvan : ∀ zc : ↥(Z1 GR A),
      (fun p : GR × GR => (ξ.1 p.1) (p.1 • zc.1 p.2)) ∈ B2 GR (ZMod 2)) :
    ∃ n : ElemDual A, dZero GR (ElemDual A) n = ξ.1 := by
  classical
  have hA₂D : ∀ lam : ElemDual A, lam + lam = 0 := fun lam => by
    ext a; exact CharTwo.add_self_eq_zero (lam a)
  have adm := markC_admissible_R θ hθs
  obtain ⟨P, hPmix, _hPleft, hPright⟩ :=
    (GQ2.FoxH.prop_5_15_R (markC_R θ) adm.2.1 adm.2.2.1 adm.1 hA₂ adm.2.2.2).2.2
  -- every word pairing of `evalR ξ` against a primal word class vanishes
  have hmix0 : ∀ xw : ↥(Z1wR (A := A) (markC_R θ)),
      mixedB_R (markC_R θ) xw.1 (toZ1wRHom θ hcompatD ξ).1 = 0 := by
    intro xw
    obtain ⟨zc, rfl⟩ := (z1EquivR θ hcompat hθs hA₂).surjective xw
    -- the paired `WordLift`-hom of `(zc, ξ)`
    have hcompatP : ∀ (γ : GR) (p : A × ElemDual A), γ • p = θ γ • p := fun γ p =>
      Prod.ext (hcompat γ p.1) (hcompatD γ p.2)
    set Hw : ContinuousMonoidHom GR (WordLift (A × ElemDual A) Cf) :=
      wordHomR θ hcompatP
        ⟨fun γ => (zc.1 γ, ξ.1 γ),
          mem_Z1_iff.mpr ⟨((mem_Z1_iff.mp zc.2).1).prodMk ((mem_Z1_iff.mp ξ.2).1),
            fun γ δ => by
              rw [Prod.ext_iff]
              exact ⟨(mem_Z1_iff.mp zc.2).2 γ δ, (mem_Z1_iff.mp ξ.2).2 γ δ⟩⟩⟩ with hHw
    -- the pair cochain is a `Z²` element (it is even a coboundary, `hvan`)
    have hmem : (fun p : GR × GR => (ξ.1 p.1) (p.1 • zc.1 p.2)) ∈ Z2 GR (ZMod 2) :=
      B2_le_Z2 (hvan zc)
    -- it is the `kappaHeis`-inflation along `Hw`
    have hunfold : ∀ a b : GR,
        (fun p : GR × GR => (ξ.1 p.1) (p.1 • zc.1 p.2)) (a, b)
          = kappaHeis.κ (Hw a) (Hw b) := by
      intro a b
      show (ξ.1 a) (a • zc.1 b) = (Hw a).u.2 ((Hw a).g • (Hw b).u.1)
      show (ξ.1 a) (a • zc.1 b) = (ξ.1 a) (θ a • zc.1 b)
      exact congrArg (ξ.1 a) (hcompat a (zc.1 b))
    -- its obstruction vanishes (`obs_R` kills `B²`)
    have hobs0 : obs_R htriv ⟨_, hmem⟩ = 0 :=
      AddMonoidHom.mem_ker.mp
        (obs_B2_eq_zero_R htriv (AddSubgroup.mem_addSubgroupOf.mpr (hvan zc)))
    -- ... and equals the traced mixed pairing
    have hinfl := obs_inflation_R htriv Hw kappaHeis ⟨_, hmem⟩ hunfold
    have hmark : gammaGenR.map Hw.toMonoidHom
        = mBaseMarking (markC_R θ) (evalR zc) (evalR ξ) := by
      rw [markC_R_map]; rfl
    rw [hmark] at hinfl
    show mixedB_R (markC_R θ) (evalR zc) (evalR ξ) = 0
    rw [mixedB_eq_relZPairR, ← hinfl]
    exact hobs0
  -- right-slot nondegeneracy kills the `ξ`-class
  have hcls0 : h1wMkR (markC_R θ) (toZ1wRHom θ hcompatD ξ) = 0 := by
    by_contra hne
    obtain ⟨hcl, hPne⟩ := hPright _ hne
    obtain ⟨xw, hxw⟩ := QuotientAddGroup.mk_surjective hcl
    exact hPne (hxw ▸ (hPmix xw (toZ1wRHom θ hcompatD ξ)).trans (hmix0 xw))
  -- `B¹w`-extraction and pullback through the bridge
  have hmemB1w :
      ((toZ1wRHom θ hcompatD ξ : ↥(Z1wR (A := ElemDual A) (markC_R θ))) : Fin 4 → ElemDual A)
      ∈ B1wR (A := ElemDual A) (markC_R θ) :=
    AddSubgroup.mem_addSubgroupOf.mp
      ((QuotientAddGroup.eq_zero_iff (toZ1wRHom θ hcompatD ξ)).mp hcls0)
  obtain ⟨m, hm⟩ := AddMonoidHom.mem_range.mp hmemB1w
  refine ⟨m, ?_⟩
  have hbundle :
      (⟨dZero GR (ElemDual A) m, B1_le_Z1 ⟨m, rfl⟩⟩ : ↥(Z1 GR (ElemDual A))) = ξ := by
    apply (z1EquivR θ hcompatD hθs hA₂D).injective
    apply Subtype.ext
    show evalR (⟨dZero GR (ElemDual A) m, B1_le_Z1 ⟨m, rfl⟩⟩ : ↥(Z1 GR (ElemDual A))) = evalR ξ
    rwa [eval_dZeroR θ hcompatD m]
  exact congrArg Subtype.val hbundle

end WordSeparatorR

/-! ## Generic helpers for the `hsep_gammaR`/`hpartial_gammaR` decompositions

These are the `Γ`-free (or retype-only) private helpers of `Phase140GammaA.Hsep`; they are
`private` there, hence restated here rather than imported.  Statements are binder-for-binder the
`Γ_A` ones, with `GA → GR`, `GammaA → GammaR`, and `Marking.push → Marking.pushR` /
`wildValue → wildValueR` where a relator is read. -/

section GammaRHelpers

/-- Set-lift a marking through a surjective homomorphism, field by field. -/
private theorem exists_marking_map_eq {G G' : Type*} [Group G] [Group G'] {π : G →* G'}
    (hπ : Function.Surjective π) (t : Marking G') : ∃ s : Marking G, s.map π = t := by
  obtain ⟨yσ, hyσ⟩ := hπ t.σ
  obtain ⟨yτ, hyτ⟩ := hπ t.τ
  obtain ⟨yx₀, hyx₀⟩ := hπ t.x₀
  obtain ⟨yx₁, hyx₁⟩ := hπ t.x₁
  exact ⟨⟨yσ, yτ, yx₀, yx₁⟩, marking_ext hyσ hyτ hyx₀ hyx₁⟩

/-- Instance pack (`hpartial_gammaR` stage 0): a `Γ_R`-smul that factors pointwise through a
continuous hom to a discrete group is continuous on a discrete space. -/
private theorem continuousSMul_of_smul_factor {Cf X : Type} [Group Cf] [TopologicalSpace Cf]
    [DiscreteTopology Cf] [TopologicalSpace X] [DiscreteTopology X] [SMul Cf X] [SMul GR X]
    (θ : ContinuousMonoidHom GR Cf) (hcomp : ∀ (γ : GR) (x : X), γ • x = θ γ • x) :
    ContinuousSMul GR X := by
  constructor
  have hfac : (fun p : GR × X => p.1 • p.2)
      = (fun q : Cf × X => q.1 • q.2) ∘ fun p : GR × X => (θ p.1, p.2) := by
    funext p
    exact hcomp p.1 p.2
  rw [hfac]
  exact continuous_of_discreteTopology.comp
    ((θ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)

/-- The `θ`-compatibility of a pulled-back action passes to the contragredient duals. -/
private theorem elemDual_smul_eq_of_smul_eq {Cf A : Type} [Group Cf] [TopologicalSpace Cf]
    [AddCommGroup A] [DistribMulAction Cf A] [DistribMulAction GR A]
    (θ : ContinuousMonoidHom GR Cf)
    (hcomp : ∀ (γ : GR) (a : A), γ • a = θ γ • a) (γ : GR) (lam : ElemDual A) :
    γ • lam = θ γ • lam := by
  ext a
  rw [ElemDual.smul_apply, ElemDual.smul_apply]
  congr 1
  rw [hcomp, map_inv]

/-- `iotaB` is unchanged by a `B²`-shift (`hpartial_gammaR` stage 2). -/
private theorem iotaB_add_right_of_mem_B2 (φ β : GammaR × GammaR → ZMod 2)
    (hβ : β ∈ B2 GammaR (ZMod 2)) : iotaB (φ + β) = iotaB φ := by
  unfold iotaB
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ((AddSubgroup.add_mem_cancel_right _ hβ).mp h1) h2
  · exact absurd ((AddSubgroup.add_mem_cancel_right _ hβ).mpr h2) h1
  · rfl

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg}

/-- The relator values of a set-lift marking of a `Γ_R`-hom into `B/T` lie in `T` (both **Roe**
relator words die along `g_Q`, so their `tB`-values die in `B/T`). -/
private theorem relatorValues_mem_of_map_eq_pushR (gQ : ContinuousMonoidHom GR (Bg ⧸ D.T))
    {tB : Marking Bg} (hproj : tB.map (QuotientGroup.mk' D.T) = Marking.pushR gQ) :
    tB.tameValue ∈ D.T ∧ tB.wildValueR ∈ D.T := by
  constructor
  · have hmt := Marking.map_tameValue (QuotientGroup.mk' D.T) tB
    rw [hproj, (Marking.tameValue_eq_one_iff _).mpr (push_tameRelR _)] at hmt
    exact (QuotientGroup.eq_one_iff _).mp hmt.symm
  · have hmw := Marking.map_wildValueR (QuotientGroup.mk' D.T) tB
    rw [hproj, (Marking.wildValueR_eq_one_iff _).mpr (push_wildRelR _)] at hmw
    exact (QuotientGroup.eq_one_iff _).mp hmw.symm

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {DD : DescData D}
  {ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)}

omit [DiscreteTopology Bg] in
/-- A `π_T`-lift datum determines the `B/M`-value (`hsep_gammaR` §3): `liftC0` is injective by
`hkerC0`, and both sides land on the same `C₀`-value through `piQbar`. -/
private theorem mk_eq_of_mkT_eq (gQ : QLiftsOver DD ρ) (y : Bg) (γ : Γ)
    (hy : QuotientGroup.mk' D.T y = gQ.1 γ) : QuotientGroup.mk y = ρ γ := by
  have hinj : Function.Injective ⇑(liftC0 DD) := by
    intro a a' haa'
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective a'
    rw [liftC0_mk, liftC0_mk] at haa'
    rw [QuotientGroup.eq]
    have hker : x⁻¹ * x' ∈ DD.piC0.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, haa', inv_mul_cancel]
    rwa [DD.hkerC0] at hker
  refine hinj ?_
  have h1 : liftC0 DD (QuotientGroup.mk y) = DD.piC0 y := liftC0_mk DD y
  have h2 : DD.piC0 y = piQbar DD (QuotientGroup.mk' D.T y) := (piQbar_mk DD y).symm
  rw [h1, h2, hy]
  exact gQ.2 γ

end GammaRHelpers

section CharKernelPrivateR

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg}

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
private theorem mem_charKer_iff (χ : ↥(TCharC D)) (t : ↥D.T) :
    (t : Bg) ∈ Phase140GammaA.charKer χ ↔ χ.1 t = 0 :=
  Subgroup.mem_map_iff_mem Subtype.coe_injective

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
private theorem charKer_normal (χ : ↥(TCharC D)) : (Phase140GammaA.charKer χ).Normal := by
  constructor
  intro n hn g
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hn
  refine Subgroup.mem_map.mpr
    ⟨⟨g * (t : Bg) * g⁻¹, D.hT.conj_mem (t : Bg) t.2 g⟩, ?_, rfl⟩
  show χ.1 ⟨g * (t : Bg) * g⁻¹, _⟩ = 0
  rwa [TCharC.conj_invariant χ g t]

end CharKernelPrivateR

/-! ## `hsep` for `Γ_R`: the `(T^∨)^C`-separation via the marking route -/

section HsepGammaR

variable (Dsc : Descent (En.radData l h))

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- A `C`-fixed elementary dual of `Additive T` is conjugation-invariant: its values depend on the
`T`-element only up to `Y_B`-conjugacy (`hsep_gammaR` L4, invariance step).  Frame-level and
source-free; the `Γ_A` twin is `private`, hence restated. -/
private theorem fixed_elemDual_conj_apply (lam : ElemDual (Additive ↥(En.radData l h).T))
    (hfixmem : lam ∈ fixedPts (RF.YB ⧸ (En.radData l h).M)
      (ElemDual (Additive ↥(En.radData l h).T)))
    (bb : RF.YB) (t : ↥(En.radData l h).T) :
    lam (Additive.ofMul ⟨bb * (t : RF.YB) * bb⁻¹,
      (En.radData l h).hT.conj_mem (t : RF.YB) t.2 bb⟩) = lam (Additive.ofMul t) := by
  have hfix := hfixmem (QuotientGroup.mk bb : RF.YB ⧸ (En.radData l h).M)
  have h1 := congrArg (fun mu : ElemDual (Additive ↥(En.radData l h).T) =>
    mu (Additive.ofMul ⟨bb * (t : RF.YB) * bb⁻¹,
      (En.radData l h).hT.conj_mem (t : RF.YB) t.2 bb⟩)) hfix
  have h3 : (QuotientGroup.mk bb : RF.YB ⧸ (En.radData l h).M)⁻¹
      • Additive.ofMul (⟨bb * (t : RF.YB) * bb⁻¹,
        (En.radData l h).hT.conj_mem (t : RF.YB) t.2 bb⟩ : ↥(En.radData l h).T)
      = Additive.ofMul t := by
    apply Additive.toMul.injective
    rw [cActT_toMul]
    apply Subtype.ext
    rw [cactFun_eq (En.radData l h) ((QuotientGroup.mk bb : RF.YB ⧸ (En.radData l h).M)⁻¹)
      (b := bb⁻¹) rfl]
    show bb⁻¹ * (bb * (t : RF.YB) * bb⁻¹) * bb⁻¹⁻¹ = (t : RF.YB)
    group
  have h2 : ((QuotientGroup.mk bb : RF.YB ⧸ (En.radData l h).M) • lam)
      (Additive.ofMul ⟨bb * (t : RF.YB) * bb⁻¹,
        (En.radData l h).hT.conj_mem (t : RF.YB) t.2 bb⟩)
      = lam (Additive.ofMul t) := by
    rw [ElemDual.smul_apply, h3]
  rw [h2] at h1
  exact h1.symm

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **`hsep_gammaR` L4 at one character**: a nonzero invariant character whose `β_χ(c)`
obstruction is a coboundary takes equal values on the tame and **Roe**-wild relator values of a
set-lift marking of `g_c` — the `χ`-cover lift (the abstract-`Γ`
`Phase140GammaA.exists_lift_charCover`, applied at `Γ_R` with `htriv_gammaR`) forces reduced-value
agreement (`RStageGammaR.redValues_eq_of_coverLift_R`), putting the discrepancy in `ker χ`. -/
private theorem tCharC_relatorSum_eq_zero_R (ρ : BoundaryLifts b F RF.TC)
    (c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
    (χ : ↥(TCharC (En.radData l h))) (hz : χ ≠ 0)
    (hB2 : chiDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c
      ∈ B2 GammaR (ZMod 2))
    {tB : Marking RF.YB}
    (hproj : tB.map (QuotientGroup.mk' (En.radData l h).T)
      = Marking.pushR (qOfCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)
          (descSigma En l h Dsc) (descSigma_spec En l h Dsc) c).1)
    (hv₁mem : tB.tameValue ∈ (En.radData l h).T)
    (hv₂mem : tB.wildValueR ∈ (En.radData l h).T) :
    χ.1 ⟨tB.tameValue, hv₁mem⟩ + χ.1 ⟨tB.wildValueR, hv₂mem⟩ = 0 := by
  obtain ⟨gc, hgc⟩ := Phase140GammaA.exists_lift_charCover htriv_gammaR
    (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ hz c hB2
  have hkey := redValues_eq_of_coverLift_R (Phase140GammaA.charCover χ hz)
    (QuotientGroup.mk' (En.radData l h).T) (Phase140GammaA.charCoverMap χ hz)
    (Phase140GammaA.charCover_p_comp χ hz) _ gc hgc tB hproj
  have hmemK : ((⟨tB.tameValue, hv₁mem⟩ * (⟨tB.wildValueR, hv₂mem⟩)⁻¹ :
      ↥(En.radData l h).T) : RF.YB) ∈ Phase140GammaA.charKer χ := by
    have h1 : Phase140GammaA.charCoverMap χ hz (tB.tameValue * tB.wildValueR⁻¹) = 1 := by
      rw [map_mul, map_inv, hkey, mul_inv_cancel]
    have h2 : ((⟨tB.tameValue, hv₁mem⟩ * (⟨tB.wildValueR, hv₂mem⟩)⁻¹ :
        ↥(En.radData l h).T) : RF.YB) ∈ (Phase140GammaA.charCoverMap χ hz).ker :=
      MonoidHom.mem_ker.mpr h1
    haveI : (Phase140GammaA.charKer χ).Normal := charKer_normal χ
    rwa [show (Phase140GammaA.charCoverMap χ hz).ker = Phase140GammaA.charKer χ from
      QuotientGroup.ker_mk' (Phase140GammaA.charKer χ)] at h2
  have hchival :=
    (mem_charKer_iff χ (⟨tB.tameValue, hv₁mem⟩ * (⟨tB.wildValueR, hv₂mem⟩)⁻¹)).mp hmemK
  rw [TCharC.map_mul χ, TCharC.map_inv χ] at hchival
  exact hchival

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **`hsep_gammaR` L4**: when all `χ`-obstructions of `c` vanish, every `d⁰`-invariant elementary
dual kills the relator-value sum of a set-lift marking of `g_c` — zero characters kill both values
outright, nonzero ones agree on them by `tCharC_relatorSum_eq_zero_R`. -/
private theorem invariant_dual_relatorSum_eq_zero_R
    [DiscreteTopology (RF.YB ⧸ (En.radData l h).M)] (ρ : BoundaryLifts b F RF.TC)
    (c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
    (hc : ∀ χ : ↥(TCharC (En.radData l h)),
      betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c = 0)
    {tB : Marking RF.YB}
    (hproj : tB.map (QuotientGroup.mk' (En.radData l h).T)
      = Marking.pushR (qOfCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)
          (descSigma En l h Dsc) (descSigma_spec En l h Dsc) c).1)
    (hv₁mem : tB.tameValue ∈ (En.radData l h).T)
    (hv₂mem : tB.wildValueR ∈ (En.radData l h).T) :
    ∀ lam : ElemDual (Additive ↥(En.radData l h).T),
      (d0 (A := ElemDual (Additive ↥(En.radData l h).T))
        (markC_R (RF.rhoPrime b F (En.radData l h) rfl ρ))) lam = 0 →
      lam (Additive.ofMul ⟨tB.tameValue, hv₁mem⟩ + Additive.ofMul ⟨tB.wildValueR, hv₂mem⟩)
        = 0 := by
  intro lam hlam
  have adm := markC_admissible_R (RF.rhoPrime b F (En.radData l h) rfl ρ)
    (rhoPrime_surjective RF b F (En.radData l h) rfl ρ)
  have hfixmem : lam ∈ fixedPts (RF.YB ⧸ (En.radData l h).M)
      (ElemDual (Additive ↥(En.radData l h).T)) := by
    have hmem : lam ∈ H0w (A := ElemDual (Additive ↥(En.radData l h).T))
        (markC_R (RF.rhoPrime b F (En.radData l h) rfl ρ)) :=
      AddMonoidHom.mem_ker.mpr hlam
    rw [← H0w_eq_fixedPts (markC_R (RF.rhoPrime b F (En.radData l h) rfl ρ)) adm.1]
    exact hmem
  set chiLam : ↥(TCharC (En.radData l h)) := ⟨fun t => lam (Additive.ofMul t),
    ⟨fun t t' => by
      show lam (Additive.ofMul (t * t')) = lam (Additive.ofMul t) + lam (Additive.ofMul t')
      rw [show Additive.ofMul (t * t') = Additive.ofMul t + Additive.ofMul t' from rfl,
        map_add],
     fun bb t => fixed_elemDual_conj_apply En l h lam hfixmem bb t⟩⟩ with hchiLam
  rw [map_add]
  by_cases hz : chiLam = 0
  · have hlam0 : ∀ t : ↥(En.radData l h).T, lam (Additive.ofMul t) = 0 := by
      intro t
      have h0 := congrArg (fun ξ : ↥(TCharC (En.radData l h)) => ξ.1 t) hz
      simpa using h0
    rw [hlam0 ⟨tB.tameValue, hv₁mem⟩, hlam0 ⟨tB.wildValueR, hv₂mem⟩, add_zero]
  · have hB2 : chiDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) chiLam c
        ∈ B2 GammaR (ZMod 2) := iotaB_eq_zero_iff.mp (hc chiLam)
    exact tCharC_relatorSum_eq_zero_R b F En l h Dsc ρ c chiLam hz hB2 hproj hv₁mem hv₂mem

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- `cActT` through the `M`-quotient map is `Y_B`-conjugation on `T`-realizations (`hsep_gammaR`
L5, the `hjconj` field of the correction calculus). -/
private theorem coe_toMul_mkM_smul (y : RF.YB) (a : Additive ↥(En.radData l h).T) :
    ((Additive.toMul (QuotientGroup.mk' (En.radData l h).M y • a) :
        ↥(En.radData l h).T) : RF.YB)
      = y * ((Additive.toMul a : ↥(En.radData l h).T) : RF.YB) * y⁻¹ := by
  have h2 := congrArg Subtype.val
    (cActT_toMul (En.radData l h) (QuotientGroup.mk' (En.radData l h).M y) a)
  rw [h2]
  exact cactFun_eq (En.radData l h) (QuotientGroup.mk' (En.radData l h).M y) rfl
    (Additive.toMul a)

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **`hsep_gammaR` L5, correction step**: a word-level correction `x` with `d¹_R x = (v₁, v₂)` (at
the pushed `B/M`-base) turns a set-lift marking `tB` into one that kills both `Γ_R` relators
(`corrected_tameValue` — the tame row is **shared** with `Γ_A` — and `corrected_wildValueR`, plus
`T`-elementarity) and still covers `g_Q` (the correction lies in `T`). -/
private theorem exists_relatorFree_markingR (ρ : BoundaryLifts b F RF.TC)
    (gQ : QLiftsOver (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
    {tB : Marking RF.YB}
    (hproj : tB.map (QuotientGroup.mk' (En.radData l h).T) = Marking.pushR gQ.1)
    (hv₁mem : tB.tameValue ∈ (En.radData l h).T)
    (hv₂mem : tB.wildValueR ∈ (En.radData l h).T)
    (x : Fin 4 → Additive ↥(En.radData l h).T)
    (hx : d1FunR (tB.map (QuotientGroup.mk' (En.radData l h).M)) x
      = (Additive.ofMul ⟨tB.tameValue, hv₁mem⟩, Additive.ofMul ⟨tB.wildValueR, hv₂mem⟩)) :
    ∃ tHat : Marking RF.YB, tHat.TameRel ∧ tHat.WildRelR ∧
      tHat.map (QuotientGroup.mk' (En.radData l h).T) = Marking.pushR gQ.1 := by
  classical
  have htelem : ∀ t ∈ (En.radData l h).T, t * t = 1 :=
    fun t ht => (En.radData l h).helem t ((En.radData l h).hTM ht)
  letI actYB : DistribMulAction RF.YB (Additive ↥(En.radData l h).T) :=
    DistribMulAction.compHom (Additive ↥(En.radData l h).T)
      (QuotientGroup.mk' (En.radData l h).M)
  have hjmul : ∀ a b' : Additive ↥(En.radData l h).T,
      ((Additive.toMul (a + b') : ↥(En.radData l h).T) : RF.YB)
        = ((Additive.toMul a : ↥(En.radData l h).T) : RF.YB)
          * ((Additive.toMul b' : ↥(En.radData l h).T) : RF.YB) :=
    fun _ _ => rfl
  have hjconj : ∀ (y : RF.YB) (a : Additive ↥(En.radData l h).T),
      ((Additive.toMul (y • a) : ↥(En.radData l h).T) : RF.YB)
        = y * ((Additive.toMul a : ↥(En.radData l h).T) : RF.YB) * y⁻¹ :=
    fun y a => coe_toMul_mkM_smul En l h y a
  have hd1 : d1FunR tB x
      = (Additive.ofMul ⟨tB.tameValue, hv₁mem⟩, Additive.ofMul ⟨tB.wildValueR, hv₂mem⟩) := by
    rw [← d1FunR_base_change (QuotientGroup.mk' (En.radData l h).M) (fun _ _ => rfl) tB x]
    exact hx
  set tHat : Marking RF.YB :=
    ⟨((Additive.toMul (x 0) : ↥(En.radData l h).T) : RF.YB) * tB.σ,
      ((Additive.toMul (x 1) : ↥(En.radData l h).T) : RF.YB) * tB.τ,
      ((Additive.toMul (x 2) : ↥(En.radData l h).T) : RF.YB) * tB.x₀,
      ((Additive.toMul (x 3) : ↥(En.radData l h).T) : RF.YB) * tB.x₁⟩ with htHat
  refine ⟨tHat, ?_, ?_, ?_⟩
  · rw [← Marking.tameValue_eq_one_iff]
    rw [show tHat.tameValue
        = ((Additive.toMul ((d1FunR tB x).1) : ↥(En.radData l h).T) : RF.YB) * tB.tameValue from
      corrected_tameValue (fun a => ((Additive.toMul a : ↥(En.radData l h).T) : RF.YB))
        hjmul hjconj tB x, hd1]
    show ((⟨tB.tameValue, hv₁mem⟩ : ↥(En.radData l h).T) : RF.YB) * tB.tameValue = 1
    exact htelem _ hv₁mem
  · rw [← Marking.wildValueR_eq_one_iff]
    rw [show tHat.wildValueR
        = ((Additive.toMul ((d1FunR tB x).2) : ↥(En.radData l h).T) : RF.YB) * tB.wildValueR from
      corrected_wildValueR (fun a => ((Additive.toMul a : ↥(En.radData l h).T) : RF.YB))
        hjmul hjconj tB x, hd1]
    show ((⟨tB.wildValueR, hv₂mem⟩ : ↥(En.radData l h).T) : RF.YB) * tB.wildValueR = 1
    exact htelem _ hv₂mem
  · have hker : ∀ a : Additive ↥(En.radData l h).T,
        QuotientGroup.mk' (En.radData l h).T
          ((Additive.toMul a : ↥(En.radData l h).T) : RF.YB) = 1 := by
      intro a
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact (Additive.toMul a).2
    refine marking_ext ?_ ?_ ?_ ?_
    · show QuotientGroup.mk' (En.radData l h).T
        (((Additive.toMul (x 0) : ↥(En.radData l h).T) : RF.YB) * tB.σ) = _
      rw [map_mul, hker, one_mul]
      exact congrArg Marking.σ hproj
    · show QuotientGroup.mk' (En.radData l h).T
        (((Additive.toMul (x 1) : ↥(En.radData l h).T) : RF.YB) * tB.τ) = _
      rw [map_mul, hker, one_mul]
      exact congrArg Marking.τ hproj
    · show QuotientGroup.mk' (En.radData l h).T
        (((Additive.toMul (x 2) : ↥(En.radData l h).T) : RF.YB) * tB.x₀) = _
      rw [map_mul, hker, one_mul]
      exact congrArg Marking.x₀ hproj
    · show QuotientGroup.mk' (En.radData l h).T
        (((Additive.toMul (x 3) : ↥(En.radData l h).T) : RF.YB) * tB.x₁) = _
      rw [map_mul, hker, one_mul]
      exact congrArg Marking.x₁ hproj

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **`hsep` for `Γ_R`** — the `(T^∨)^C`-separation at the Roe candidate source: a `V`-coordinate
whose `χ`-obstructions all vanish is `T`-liftable.  The `Γ_R` twin of
`Phase140GammaA.hsep_gammaA`, by the same **marking route**: each nonzero invariant character's
vanishing obstruction produces a lift through its `𝔽₂`-cover (the abstract-`Γ`
`exists_lift_charCover`, reused), which forces `χ`-agreement of the tame and Roe-wild relator
values of a set-lift marking (`redValues_eq_of_coverLift_R`); `sep_word_R` (the `prop_5_15_R`
trace-span) converts total agreement into word-level corrections; the corrected marking kills both
`Γ_R` relators (`corrected_tameValue`/`corrected_wildValueR` + `T`-elementarity) and descends
(`mlift_of_relatorFree_markingR`) to the direct `M`-lift. -/
theorem hsep_gammaR
    (ρ : BoundaryLifts b F RF.TC)
    (c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
    (hc : ∀ χ : ↥(TCharC (En.radData l h)),
      betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c = 0) :
    TLiftable (descSigma_spec En l h Dsc) c := by
  classical
  haveI : (En.radData l h).M.Normal := (En.radData l h).hM
  haveI : DiscreteTopology (RF.YB ⧸ (En.radData l h).M) :=
    discreteTopology_quotient (En.radData l h)
  have hσ := descSigma_spec En l h Dsc
  have hρ's : Function.Surjective ⇑(RF.rhoPrime b F (En.radData l h) rfl ρ) :=
    rhoPrime_surjective RF b F (En.radData l h) rfl ρ
  have hA₂ : ∀ a : Additive ↥(En.radData l h).T, a + a = 0 := fun a =>
    Additive.toMul.injective (Subtype.ext
      ((En.radData l h).helem _ ((En.radData l h).hTM (Additive.toMul a).2)))
  set gq0 := qOfCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)
    (descSigma En l h Dsc) hσ c with hgq0
  -- §1: a set-lift marking of `g_Q` through `π_T`
  obtain ⟨tB, hproj⟩ := exists_marking_map_eq
    (QuotientGroup.mk'_surjective (En.radData l h).T) (Marking.pushR gq0.1)
  -- §2: the relator values live in `T` (both Roe relators die in `B/T` — `g_Q` is a hom)
  obtain ⟨hv₁mem, hv₂mem⟩ := relatorValues_mem_of_map_eq_pushR gq0.1 hproj
  -- §3+§4 (L4): every invariant character kills the relator-value sum
  have adm := markC_admissible_R (RF.rhoPrime b F (En.radData l h) rfl ρ) hρ's
  have hsd := GQ2.FoxH.prop_5_15_R (markC_R (RF.rhoPrime b F (En.radData l h) rfl ρ))
    adm.2.1 adm.2.2.1 adm.1 hA₂ adm.2.2.2
  have hv := invariant_dual_relatorSum_eq_zero_R b F En l h Dsc ρ c hc hproj hv₁mem hv₂mem
  -- §5: the separation delivers word-level corrections
  have hsep := sep_word_R (markC_R (RF.rhoPrime b F (En.radData l h) rfl ρ))
    adm.2.1 adm.2.2.1 adm.1 hsd hA₂
    (Additive.ofMul ⟨tB.tameValue, hv₁mem⟩, Additive.ofMul ⟨tB.wildValueR, hv₂mem⟩) hv
  obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp hsep
  -- §6 (L5): the corrected marking kills both relators and still covers `g_Q`
  have hfield : ∀ (y : RF.YB) (γ : GR),
      QuotientGroup.mk' (En.radData l h).T y = gq0.1 γ →
      QuotientGroup.mk (y : RF.YB) = RF.rhoPrime b F (En.radData l h) rfl ρ γ :=
    fun y γ hy => mk_eq_of_mkT_eq gq0 y γ hy
  have hmarkC : markC_R (RF.rhoPrime b F (En.radData l h) rfl ρ)
      = tB.map (QuotientGroup.mk' (En.radData l h).M) := by
    refine marking_ext ?_ ?_ ?_ ?_
    · exact (hfield tB.σ gammaGenR.σ (congrArg Marking.σ hproj)).symm
    · exact (hfield tB.τ gammaGenR.τ (congrArg Marking.τ hproj)).symm
    · exact (hfield tB.x₀ gammaGenR.x₀ (congrArg Marking.x₀ hproj)).symm
    · exact (hfield tB.x₁ gammaGenR.x₁ (congrArg Marking.x₁ hproj)).symm
  have hxB : d1FunR (tB.map (QuotientGroup.mk' (En.radData l h).M)) x
      = (Additive.ofMul ⟨tB.tameValue, hv₁mem⟩, Additive.ofMul ⟨tB.wildValueR, hv₂mem⟩) := by
    rw [← hmarkC]
    exact hx
  obtain ⟨tHat, htameHat, hwildHat, hprojHat⟩ :=
    exists_relatorFree_markingR b F En l h ρ gq0 hproj hv₁mem hv₂mem x hxB
  -- §7: descend and package as the `M`-lift
  obtain ⟨f₀, hf₀⟩ := mlift_of_relatorFree_markingR gq0.1 tHat hprojHat htameHat hwildHat
  refine ⟨⟨f₀, fun γ => hfield (f₀ γ) γ (hf₀ γ)⟩, ?_⟩
  refine Subtype.ext (DFunLike.ext _ _ fun γ => ?_)
  rw [redTLift_apply]
  exact hf₀ γ

/-! ## `hpartial` for `Γ_R`: nondegeneracy of the obstruction pairing in the character -/

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- The `T`-realization of an `M`-element (`hpartial_gammaR` stage 8): `m · mV(v_m)⁻¹ ∈ T`, where
`v_m = toAdd(descend m)` is the `V`-coordinate; its `descend` is trivial, so it lands in
`T = ker(descend)|_M`.  Frame-level and source-free; the `Γ_A` twin is `private`. -/
private theorem descend_tPart_mem (m : ↥(En.radData l h).M) :
    ((m * ((descSections En l h Dsc).mV (Multiplicative.toAdd
      ((En.descData l h).descend m)))⁻¹ : ↥(En.radData l h).M) : RF.YB)
      ∈ (En.radData l h).T := by
  refine ((En.descData l h).hdesc_ker _).mp ?_
  rw [map_mul, map_inv, (descSections En l h Dsc).descend_mV, ofAdd_toAdd, mul_inv_cancel]

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **T-part product law** (`hpartial_gammaR` stage 8): `tpart(mm') = tpart m · tpart m' ·
mDef(v_m, v_{m'})` — the section 2-cocycle `mDef` corrects the product (`M` abelian). -/
private theorem descend_tPart_mul (m m' : ↥(En.radData l h).M) :
    (⟨_, descend_tPart_mem En l h Dsc (m * m')⟩ : ↥(En.radData l h).T)
      = ⟨_, descend_tPart_mem En l h Dsc m⟩ * ⟨_, descend_tPart_mem En l h Dsc m'⟩
        * mDef (En.descData l h) (descSections En l h Dsc)
            (Multiplicative.toAdd ((En.descData l h).descend m))
            (Multiplicative.toAdd ((En.descData l h).descend m')) := by
  apply Subtype.ext
  have hvco : Multiplicative.toAdd ((En.descData l h).descend (m * m'))
      = Multiplicative.toAdd ((En.descData l h).descend m)
        + Multiplicative.toAdd ((En.descData l h).descend m') := by rw [map_mul]; rfl
  show (↑m * ↑m' : RF.YB)
      * (↑((descSections En l h Dsc).mV
          (Multiplicative.toAdd ((En.descData l h).descend (m * m')))))⁻¹
    = ↑m * (↑((descSections En l h Dsc).mV
          (Multiplicative.toAdd ((En.descData l h).descend m))))⁻¹
      * (↑m' * (↑((descSections En l h Dsc).mV
          (Multiplicative.toAdd ((En.descData l h).descend m'))))⁻¹)
      * (↑((descSections En l h Dsc).mV
          (Multiplicative.toAdd ((En.descData l h).descend m)))
        * ↑((descSections En l h Dsc).mV
          (Multiplicative.toAdd ((En.descData l h).descend m')))
        * (↑((descSections En l h Dsc).mV
          (Multiplicative.toAdd ((En.descData l h).descend m)
            + Multiplicative.toAdd ((En.descData l h).descend m'))))⁻¹)
  rw [hvco]
  set a : RF.YB := (↑m : RF.YB) with ha
  set bb : RF.YB := (↑m' : RF.YB) with hbb
  set p : RF.YB := (↑((descSections En l h Dsc).mV
      (Multiplicative.toAdd ((En.descData l h).descend m))) : RF.YB) with hp
  set q : RF.YB := (↑((descSections En l h Dsc).mV
      (Multiplicative.toAdd ((En.descData l h).descend m'))) : RF.YB) with hq
  set r : RF.YB := (↑((descSections En l h Dsc).mV
      (Multiplicative.toAdd ((En.descData l h).descend m)
        + Multiplicative.toAdd ((En.descData l h).descend m'))) : RF.YB) with hr
  have hpM : p ∈ (En.radData l h).M := ((descSections En l h Dsc).mV _).2
  have hqM : q ∈ (En.radData l h).M := ((descSections En l h Dsc).mV _).2
  have hbM : bb ∈ (En.radData l h).M := m'.2
  have c1 : p⁻¹ * bb = bb * p⁻¹ := (En.radData l h).hcomm _ (inv_mem hpM) _ hbM
  have c2 : q⁻¹ * p = p * q⁻¹ := (En.radData l h).hcomm _ (inv_mem hqM) _ hpM
  symm
  calc a * p⁻¹ * (bb * q⁻¹) * (p * q * r⁻¹)
      = a * (p⁻¹ * bb) * q⁻¹ * p * q * r⁻¹ := by group
    _ = a * (bb * p⁻¹) * q⁻¹ * p * q * r⁻¹ := by rw [c1]
    _ = a * bb * (p⁻¹ * (q⁻¹ * p)) * q * r⁻¹ := by group
    _ = a * bb * (p⁻¹ * (p * q⁻¹)) * q * r⁻¹ := by rw [c2]
    _ = a * bb * r⁻¹ := by group

/-- The invariant `M`-character `ψ` of `hpartial_gammaR` stage 8: the `V`-coordinatization
`ψ m = χ(tpart m) + gχ(v_m) + n(v_m)`, built from the character `χ`, the quadratic splitting `gχ`
and the `B¹`-witness `n`. -/
private noncomputable def psiVCoord (χ : ↥(TCharC (En.radData l h)))
    (gχ : En.Vmod → ZMod 2) (n : ElemDual En.Vmod) (m : ↥(En.radData l h).M) : ZMod 2 :=
  χ.1 ⟨_, descend_tPart_mem En l h Dsc m⟩
    + gχ (Multiplicative.toAdd ((En.descData l h).descend m))
    + n (Multiplicative.toAdd ((En.descData l h).descend m))

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- `ψ = psiVCoord …` is additive (`hpartial_gammaR` stage 8): the `mDef` term of the T-part
product law (`descend_tPart_mul`) is exactly `gχ`'s splitting defect of `χ`, cancelling in
characteristic two. -/
private theorem psiVCoord_add (χ : ↥(TCharC (En.radData l h)))
    (gχ : En.Vmod → ZMod 2)
    (hg : ∀ v w : En.Vmod, χ.1 (mDef (En.descData l h) (descSections En l h Dsc) v w)
      = gχ (v + w) + gχ v + gχ w)
    (n : ElemDual En.Vmod) (m m' : ↥(En.radData l h).M) :
    psiVCoord En l h Dsc χ gχ n (m * m')
      = psiVCoord En l h Dsc χ gχ n m + psiVCoord En l h Dsc χ gχ n m' := by
  have hvco : Multiplicative.toAdd ((En.descData l h).descend (m * m'))
      = Multiplicative.toAdd ((En.descData l h).descend m)
        + Multiplicative.toAdd ((En.descData l h).descend m') := by rw [map_mul]; rfl
  have hmD : χ.1 (mDef (En.descData l h) (descSections En l h Dsc)
        (Multiplicative.toAdd ((En.descData l h).descend m))
        (Multiplicative.toAdd ((En.descData l h).descend m')))
      = gχ (Multiplicative.toAdd ((En.descData l h).descend m)
          + Multiplicative.toAdd ((En.descData l h).descend m'))
        + gχ (Multiplicative.toAdd ((En.descData l h).descend m))
        + gχ (Multiplicative.toAdd ((En.descData l h).descend m')) := hg _ _
  have hnv : n (Multiplicative.toAdd ((En.descData l h).descend (m * m')))
      = n (Multiplicative.toAdd ((En.descData l h).descend m))
        + n (Multiplicative.toAdd ((En.descData l h).descend m')) :=
    (congrArg n hvco).trans (n.map_add _ _)
  have hgv : gχ (Multiplicative.toAdd ((En.descData l h).descend (m * m')))
      = gχ (Multiplicative.toAdd ((En.descData l h).descend m)
          + Multiplicative.toAdd ((En.descData l h).descend m')) :=
    congrArg gχ hvco
  show χ.1 ⟨_, descend_tPart_mem En l h Dsc (m * m')⟩
      + gχ (Multiplicative.toAdd ((En.descData l h).descend (m * m')))
      + n (Multiplicative.toAdd ((En.descData l h).descend (m * m'))) = _
  rw [descend_tPart_mul, TCharC.map_mul, TCharC.map_mul, hmD, hnv, hgv]
  have hchar : ∀ A B P Q R S FF : ZMod 2,
      A + B + (FF + P + Q) + FF + (R + S) = (A + P + R) + (B + Q + S) := by decide
  exact hchar _ _ _ _ _ _ _

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- `ψ = psiVCoord …` is `Y_B`-conjugation invariant (`hpartial_gammaR` stage 8): conjugating `m`
by `bb` shifts its T-part by `conjDef(cc, v_m)` and its V-coordinate by `cc • v_m`
(`cc = π_{C₀}(bb)`, `bb = uσ(cc)·k` with `k ∈ M` central in `M`); the `∂n`-relation `hkey`
cancels the shift. -/
private theorem psiVCoord_conj (χ : ↥(TCharC (En.radData l h)))
    (gχ : En.Vmod → ZMod 2) (n : ElemDual En.Vmod)
    (hkey : ∀ (cc : RF.YC) (v : En.Vmod),
      χ.1 (conjDef (En.descData l h) (descSections En l h Dsc)
          (descSigma_spec En l h Dsc) cc v) + gχ (cc • v) + gχ v
        = n v + n (cc • v))
    (bb : RF.YB) (m : ↥(En.radData l h).M)
    (hm : bb * (m : RF.YB) * bb⁻¹ ∈ (En.radData l h).M) :
    psiVCoord En l h Dsc χ gχ n ⟨bb * (m : RF.YB) * bb⁻¹, hm⟩
      = psiVCoord En l h Dsc χ gχ n m := by
  set cc : RF.YC := (En.descData l h).piC0 bb with hcc
  set v : En.Vmod := Multiplicative.toAdd ((En.descData l h).descend m) with hvdef
  have hvc : Multiplicative.toAdd ((En.descData l h).descend ⟨bb * (m : RF.YB) * bb⁻¹, hm⟩)
      = cc • v := by
    rw [(En.descData l h).hdesc_conj bb m hm]; rfl
  have hpiC0uσ : (En.descData l h).piC0 ((descSections En l h Dsc).uσ cc) = cc := by
    have h1 := piQbar_mk (En.descData l h) ((descSections En l h Dsc).uσ cc)
    rw [(descSections En l h Dsc).piT_uσ] at h1
    rw [← h1, descSigma_spec En l h Dsc]
  have hkM : ((descSections En l h Dsc).uσ cc)⁻¹ * bb ∈ (En.radData l h).M := by
    rw [← (En.descData l h).hkerC0, MonoidHom.mem_ker, map_mul, map_inv, hpiC0uσ, hcc,
      inv_mul_cancel]
  have hbbdecomp : bb = (descSections En l h Dsc).uσ cc
      * (((descSections En l h Dsc).uσ cc)⁻¹ * bb) := by group
  have hsecconj : bb * (↑((descSections En l h Dsc).mV v) : RF.YB) * bb⁻¹
      = (descSections En l h Dsc).uσ cc * (↑((descSections En l h Dsc).mV v) : RF.YB)
        * ((descSections En l h Dsc).uσ cc)⁻¹ := by
    conv_lhs => rw [hbbdecomp]
    set k : RF.YB := ((descSections En l h Dsc).uσ cc)⁻¹ * bb with hkdef
    have hcomm_k : k * (↑((descSections En l h Dsc).mV v) : RF.YB)
        = (↑((descSections En l h Dsc).mV v) : RF.YB) * k :=
      (En.radData l h).hcomm _ hkM _ ((descSections En l h Dsc).mV v).2
    calc (descSections En l h Dsc).uσ cc * k * (↑((descSections En l h Dsc).mV v) : RF.YB)
          * ((descSections En l h Dsc).uσ cc * k)⁻¹
        = (descSections En l h Dsc).uσ cc * (k * (↑((descSections En l h Dsc).mV v) : RF.YB))
            * k⁻¹ * ((descSections En l h Dsc).uσ cc)⁻¹ := by group
      _ = (descSections En l h Dsc).uσ cc
            * ((↑((descSections En l h Dsc).mV v) : RF.YB) * k) * k⁻¹
            * ((descSections En l h Dsc).uσ cc)⁻¹ := by rw [hcomm_k]
      _ = _ := by group
  have htsplit : (⟨_, descend_tPart_mem En l h Dsc ⟨bb * (m : RF.YB) * bb⁻¹, hm⟩⟩ :
        ↥(En.radData l h).T)
      = ⟨bb * (⟨_, descend_tPart_mem En l h Dsc m⟩ : ↥(En.radData l h).T).1 * bb⁻¹,
          (En.radData l h).hT.conj_mem _
            (⟨_, descend_tPart_mem En l h Dsc m⟩ : ↥(En.radData l h).T).2 _⟩
        * conjDef (En.descData l h) (descSections En l h Dsc)
            (descSigma_spec En l h Dsc) cc v := by
    apply Subtype.ext
    show (bb * (m : RF.YB) * bb⁻¹)
        * (↑((descSections En l h Dsc).mV
            (Multiplicative.toAdd ((En.descData l h).descend
              ⟨bb * (m : RF.YB) * bb⁻¹, hm⟩))))⁻¹
      = bb * ((m : RF.YB) * (↑((descSections En l h Dsc).mV v))⁻¹) * bb⁻¹
        * ((descSections En l h Dsc).uσ cc * (↑((descSections En l h Dsc).mV v) : RF.YB)
            * ((descSections En l h Dsc).uσ cc)⁻¹
            * (↑((descSections En l h Dsc).mV (cc • v)))⁻¹)
    rw [hvc, ← hsecconj]
    group
  have hlhs : psiVCoord En l h Dsc χ gχ n ⟨bb * (m : RF.YB) * bb⁻¹, hm⟩
      = χ.1 (⟨_, descend_tPart_mem En l h Dsc m⟩ : ↥(En.radData l h).T)
        + χ.1 (conjDef (En.descData l h) (descSections En l h Dsc)
            (descSigma_spec En l h Dsc) cc v)
        + gχ (cc • v) + n (cc • v) := by
    show χ.1 ⟨_, descend_tPart_mem En l h Dsc ⟨bb * (m : RF.YB) * bb⁻¹, hm⟩⟩
        + gχ (Multiplicative.toAdd ((En.descData l h).descend
            ⟨bb * (m : RF.YB) * bb⁻¹, hm⟩))
        + n (Multiplicative.toAdd ((En.descData l h).descend
            ⟨bb * (m : RF.YB) * bb⁻¹, hm⟩))
      = χ.1 (⟨_, descend_tPart_mem En l h Dsc m⟩ : ↥(En.radData l h).T)
        + χ.1 (conjDef (En.descData l h) (descSections En l h Dsc)
            (descSigma_spec En l h Dsc) cc v)
        + gχ (cc • v) + n (cc • v)
    rw [htsplit, TCharC.map_mul,
      TCharC.conj_invariant χ bb (⟨_, descend_tPart_mem En l h Dsc m⟩ : ↥(En.radData l h).T)]
    exact congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl (congrArg gχ hvc)) (congrArg n hvc)
  have hrhs : psiVCoord En l h Dsc χ gχ n m
      = χ.1 (⟨_, descend_tPart_mem En l h Dsc m⟩ : ↥(En.radData l h).T) + gχ v + n v := rfl
  rw [hlhs, hrhs]
  have hk := hkey cc v
  have hfin : ∀ (TP CJ GCV NCV GV NV : ZMod 2),
      CJ + GCV + GV = NV + NCV → TP + CJ + GCV + NCV = TP + GV + NV := by decide
  exact hfin _ _ _ _ _ _ hk

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **Stage 2 of `hpartial_gammaR`**: the cup part of every `χ`-difference vanishes in `H²`.  The
`betaChi`-collapse `hall` forces `iotaB` of the `χ`-difference to be `0`; peeling off the `B²`
`g`-parts (`gPart_mem_B2`) leaves exactly the cup cochain.  The additivity of `iotaB` is the
unconditional `Γ_R` leaf `LedgerGammaR.card_H2_gammaR` (`#H²(Γ_R, 𝔽₂) = 2`), where the `Γ_A` twin
threads `CardH2GammaA.card_H2_gammaA`. -/
private theorem cupChi_iotaB_eq_zero_R (ρ : BoundaryLifts b F RF.TC)
    (χ : ↥(TCharC (En.radData l h))) (gχ : En.Vmod → ZMod 2) (hg0 : gχ 0 = 0)
    (hg : ∀ v w : En.Vmod, χ.1 (mDef (En.descData l h) (descSections En l h Dsc) v w)
      = gχ (v + w) + gχ v + gχ w)
    (hall : ∀ c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ),
      betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c
        = betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ
            (0 : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)))
    (c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)) :
    iotaB (cupChi (En.descData l h) (descSections En l h Dsc)
      (RF.rhoPrime b F (En.radData l h) rfl ρ) (descSigma_spec En l h Dsc) gχ χ c) = 0 := by
  have htrivR : ∀ (γ : GammaR) (m : ZMod 2), γ • m = m := htriv_gammaR
  set c0 : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) := 0 with hc0
  have hB : ((fun p : GammaR × GammaR =>
        gχ (c.c (p.1 * p.2)) + gχ (c.c p.1) + gχ (c.c p.2))
      + (fun p : GammaR × GammaR =>
        gχ (c0.c (p.1 * p.2)) + gχ (c0.c p.1) + gχ (c0.c p.2)))
      ∈ B2 GammaR (ZMod 2) :=
    AddSubgroup.add_mem _
      (gPart_mem_B2 (descSigma_spec En l h Dsc) htrivR gχ c)
      (gPart_mem_B2 (descSigma_spec En l h Dsc) htrivR gχ c0)
  have hdecomp : chiDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c
      + chiDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c0
      = cupChi (En.descData l h) (descSections En l h Dsc)
          (RF.rhoPrime b F (En.radData l h) rfl ρ) (descSigma_spec En l h Dsc) gχ χ c
        + ((fun p : GammaR × GammaR =>
            gχ (c.c (p.1 * p.2)) + gχ (c.c p.1) + gχ (c.c p.2))
          + (fun p : GammaR × GammaR =>
            gχ (c0.c (p.1 * p.2)) + gχ (c0.c p.1) + gχ (c0.c p.2))) := by
    funext p
    have h1 := chiDef_decomp (descSections En l h Dsc) (descSigma_spec En l h Dsc)
      χ gχ hg c p
    have h2 := chiDef_decomp (descSections En l h Dsc) (descSigma_spec En l h Dsc)
      χ gχ hg c0 p
    have h3 := cupChi_zero (ρ := RF.rhoPrime b F (En.radData l h) rfl ρ)
      (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ gχ hg0 p
    rw [← hc0] at h3
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]; try ring_nf))
      h1 + h2 + h3
  have hiota : iotaB (chiDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c
      + chiDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c0) = 0 := by
    rw [iotaB_add LedgerGammaR.card_H2_gammaR
      (chiDef_mem_Z2 (descSections En l h Dsc) (descSigma_spec En l h Dsc) htrivR χ c)
      (chiDef_mem_Z2 (descSections En l h Dsc) (descSigma_spec En l h Dsc) htrivR χ c0)]
    have hbc : iotaB (chiDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c)
        = iotaB (chiDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c0) :=
      hall c
    rw [hbc, CharTwo.add_self_eq_zero]
  rw [hdecomp, iotaB_add_right_of_mem_B2 _ _ hB] at hiota
  exact hiota

set_option synthInstance.maxHeartbeats 800000 in
omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **`hpartial` for `Γ_R`** — nondegeneracy of the obstruction pairing in the character: every
nonzero `χ ∈ (T^∨)^C` is detected by some `V`-coordinate.  The `Γ_R` twin of
`Phase140GammaA.hpartial_gammaA`, stages 1, 3–5 and 8–9 mirrored verbatim (they are frame-level or
`Γ`-generic); the two source-specific stages are stage 2 (`cupChi_iotaB_eq_zero_R`, on the
unconditional `Γ_R` leaf `card_H2_gammaR`) and stages 6–7, the word-side right-slot separation
`b1_of_pair_cochain_B2_R` (`prop_5_15_R` clause-3 right-nondegeneracy through the
`obs_R`/`mixedB_R` ledger).  All std-3, no B-axioms. -/
theorem hpartial_gammaR
    (ρ : BoundaryLifts b F RF.TC)
    (χ : ↥(TCharC (En.radData l h))) (hχ : χ ≠ 0) :
    ∃ c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ),
      betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c
        ≠ betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ
            (0 : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)) := by
  classical
  by_contra! hall
  -- ### Stage 0: module instances over the raw quotient `GR` (the `hZcard_gammaR` block)
  let θ : ContinuousMonoidHom GR RF.YC := ρ.1.1
  have hθs : Function.Surjective ⇑θ := ρ.1.2
  have hroundtrip : ∀ γ : GR,
      rho0 (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) γ = θ γ :=
    fun γ => rho0_descData_rhoPrime b F En l h ρ γ
  haveI : IsTopologicalGroup GR := inferInstanceAs (IsTopologicalGroup (GammaR : Type))
  letI : DistribMulAction GR (ZMod 2) := instDistribMulActionGammaR
  letI : ContinuousSMul GR (ZMod 2) := ⟨continuous_snd⟩
  have htriv : ∀ (x : GR) (m : ZMod 2), x • m = m := fun _ _ => rfl
  letI : TopologicalSpace En.Vmod := ⊥
  haveI : DiscreteTopology En.Vmod := ⟨rfl⟩
  letI actG : DistribMulAction GR En.Vmod :=
    DistribMulAction.compHom En.Vmod θ.toMonoidHom
  have hcomp : ∀ (γ : GR) (v : En.Vmod), γ • v = θ γ • v := fun _ _ => rfl
  haveI : ContinuousSMul GR En.Vmod := continuousSMul_of_smul_factor θ hcomp
  have hA₂ : ∀ v : En.Vmod, v + v = 0 := fun v => Vmod_exp2 (En.descData l h) v
  letI : TopologicalSpace (ElemDual En.Vmod) := ⊥
  haveI : DiscreteTopology (ElemDual En.Vmod) := ⟨rfl⟩
  have hcompD : ∀ (γ : GR) (lam : ElemDual En.Vmod), γ • lam = θ γ • lam :=
    fun γ lam => elemDual_smul_eq_of_smul_eq θ hcomp γ lam
  haveI : ContinuousSMul GR (ElemDual En.Vmod) := continuousSMul_of_smul_factor θ hcompD
  -- ### Stage 1: split `χ∘mDef` (the `betaChi_affine` splitting; frame-level)
  obtain ⟨gχ, hg0, hg⟩ := exists_splitting_of_symm_zero_diag (Vmod_exp2 (En.descData l h))
    (fun v w => χ.1 (mDef (En.descData l h) (descSections En l h Dsc) v w))
    (fun v w x => (isEquivariantFactorSet_datChi (descSections En l h Dsc)
      (descSigma_spec En l h Dsc) χ).f_cocycle v w x)
    (fun v w => by rw [mDef_symm])
    (fun v => by rw [mDef_self, TCharC.map_one])
    (fun v => by rw [mDef_zero_left, TCharC.map_one])
  -- ### Stage 2: the cup part of every `χ`-difference vanishes in `H²`
  have hcup := cupChi_iotaB_eq_zero_R b F En l h Dsc ρ χ gχ hg0 hg hall
  -- ### Stage 3: the dual-connecting cochain ξ (factored through `RF.YC`; frame-level)
  have hξadd : ∀ (y : RF.YC) (w w' : En.Vmod),
      (χ.1 (conjDef (En.descData l h) (descSections En l h Dsc) (descSigma_spec En l h Dsc)
          y (y⁻¹ • (w + w')))
        + gχ (w + w') + gχ (y⁻¹ • (w + w')))
      = (χ.1 (conjDef (En.descData l h) (descSections En l h Dsc) (descSigma_spec En l h Dsc)
          y (y⁻¹ • w)) + gχ w + gχ (y⁻¹ • w))
        + (χ.1 (conjDef (En.descData l h) (descSections En l h Dsc)
            (descSigma_spec En l h Dsc) y (y⁻¹ • w'))
          + gχ w' + gχ (y⁻¹ • w')) := by
    intro y w w'
    have hq : χ.1 (conjDef (En.descData l h) (descSections En l h Dsc)
          (descSigma_spec En l h Dsc) y (y⁻¹ • w + y⁻¹ • w'))
        + χ.1 (conjDef (En.descData l h) (descSections En l h Dsc)
          (descSigma_spec En l h Dsc) y (y⁻¹ • w))
        + χ.1 (conjDef (En.descData l h) (descSections En l h Dsc)
          (descSigma_spec En l h Dsc) y (y⁻¹ • w'))
        = χ.1 (mDef (En.descData l h) (descSections En l h Dsc)
            (y • (y⁻¹ • w)) (y • (y⁻¹ • w')))
          + χ.1 (mDef (En.descData l h) (descSections En l h Dsc)
            (y⁻¹ • w) (y⁻¹ • w')) :=
      (isEquivariantFactorSet_datChi (descSections En l h Dsc)
        (descSigma_spec En l h Dsc) χ).m_quad y (y⁻¹ • w) (y⁻¹ • w')
    rw [smul_inv_smul, smul_inv_smul] at hq
    rw [show y⁻¹ • (w + w') = y⁻¹ • w + y⁻¹ • w' from smul_add _ _ _]
    have hchar : ∀ A B C F G P Q R S U V : ZMod 2,
        A + B + C = F + G → F = P + Q + R → G = S + U + V →
        A + P + S = (B + Q + U) + (C + R + V) := by decide
    exact hchar _ _ _ _ _ _ _ _ _ _ _ hq (hg w w') (hg (y⁻¹ • w) (y⁻¹ • w'))
  set Fξ : RF.YC → ElemDual En.Vmod := fun y =>
    AddMonoidHom.mk' (fun w =>
      χ.1 (conjDef (En.descData l h) (descSections En l h Dsc) (descSigma_spec En l h Dsc)
          y (y⁻¹ • w))
        + gχ w + gχ (y⁻¹ • w))
      (fun w w' => hξadd y w w') with hFdef
  have hFval : ∀ (y : RF.YC) (w : En.Vmod),
      Fξ y w = χ.1 (conjDef (En.descData l h) (descSections En l h Dsc)
          (descSigma_spec En l h Dsc) y (y⁻¹ • w))
        + gχ w + gχ (y⁻¹ • w) := fun _ _ => rfl
  set ξfun : GR → ElemDual En.Vmod := fun γ => Fξ (θ γ) with hξdef
  -- ### Stage 4: ξ is a continuous 1-cocycle for the contragredient action (over `GR`)
  have hξZ1 : ξfun ∈ Z1 GR (ElemDual En.Vmod) := by
    refine mem_Z1_iff.mpr ⟨?_, ?_⟩
    · exact (continuous_of_discreteTopology (f := Fξ)).comp θ.continuous_toFun
    · intro γ δ
      refine DFunLike.ext _ _ fun w => ?_
      rw [show ξfun (γ * δ) = Fξ (θ (γ * δ)) from rfl,
        show (ξfun γ + γ • ξfun δ) w = ξfun γ w + (γ • ξfun δ) w from rfl,
        ElemDual.smul_apply]
      have hγinv : γ⁻¹ • w = (θ γ)⁻¹ • w := by rw [hcomp, map_inv]
      rw [hγinv, show ξfun γ = Fξ (θ γ) from rfl, show ξfun δ = Fξ (θ δ) from rfl,
        hFval, hFval, hFval, map_mul, mul_inv_rev, mul_smul]
      have hmul : χ.1 (conjDef (En.descData l h) (descSections En l h Dsc)
            (descSigma_spec En l h Dsc) (θ γ * θ δ)
            ((θ δ)⁻¹ • ((θ γ)⁻¹ • w)))
          = χ.1 (conjDef (En.descData l h) (descSections En l h Dsc)
              (descSigma_spec En l h Dsc) (θ γ)
              (θ δ • ((θ δ)⁻¹ • ((θ γ)⁻¹ • w))))
            + χ.1 (conjDef (En.descData l h) (descSections En l h Dsc)
              (descSigma_spec En l h Dsc) (θ δ)
              ((θ δ)⁻¹ • ((θ γ)⁻¹ • w))) :=
        (isEquivariantFactorSet_datChi (descSections En l h Dsc)
          (descSigma_spec En l h Dsc) χ).m_mul (θ γ) (θ δ)
          ((θ δ)⁻¹ • ((θ γ)⁻¹ • w))
      rw [smul_inv_smul] at hmul
      rw [hmul]
      have hchar : ∀ X Y P Q R : ZMod 2,
          (X + Y) + P + R = (X + P + Q) + (Y + Q + R) := by decide
      exact hchar _ _ _ _ _
  -- ### Stage 5: the pair cochain against every `V`-cocycle is a coboundary
  have hvan : ∀ zc : ↥(Z1 GR En.Vmod),
      (fun p : GR × GR => (ξfun p.1) (p.1 • zc.1 p.2)) ∈ B2 GR (ZMod 2) := by
    intro zc
    -- the bridged `VCocycle` (the `hZcard_gammaR` construction)
    set c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) :=
      { c := fun γ => (zc.1 γ : (En.descData l h).Vmod)
        cont := (continuous_of_discreteTopology (f := fun v : En.Vmod =>
          iV (En.descData l h) (Multiplicative.ofAdd v))).comp (mem_Z1_iff.mp zc.2).1
        crossed := fun γ δ => by
          rw [hroundtrip γ]; exact (mem_Z1_iff.mp zc.2).2 γ δ } with hcdef
    have hident : (fun p : GR × GR => (ξfun p.1) (p.1 • zc.1 p.2))
        = cupChi (En.descData l h) (descSections En l h Dsc)
            (RF.rhoPrime b F (En.radData l h) rfl ρ) (descSigma_spec En l h Dsc) gχ χ c := by
      funext p
      rw [show ξfun p.1 = Fξ (θ p.1) from rfl, hFval]
      show χ.1 (conjDef (En.descData l h) (descSections En l h Dsc)
            (descSigma_spec En l h Dsc) (θ p.1) ((θ p.1)⁻¹ • (p.1 • zc.1 p.2)))
          + gχ (p.1 • zc.1 p.2) + gχ ((θ p.1)⁻¹ • (p.1 • zc.1 p.2))
        = χ.1 (conjDef (En.descData l h) (descSections En l h Dsc)
            (descSigma_spec En l h Dsc)
            (rho0 (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) p.1) (c.c p.2))
          + gχ (rho0 (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) p.1 • c.c p.2)
          + gχ (c.c p.2)
      rw [hroundtrip p.1, hcomp p.1, inv_smul_smul]
      rfl
    rw [hident]
    exact iotaB_eq_zero_iff.mp (hcup c)
  -- ### Stage 6+7: the ξ-class dies (word-side right-slot separation) and B¹-extracts
  obtain ⟨n, hn'⟩ := b1_of_pair_cochain_B2_R θ hcomp hcompD htriv hθs hA₂ ⟨ξfun, hξZ1⟩ hvan
  have hn : dZero GR (ElemDual En.Vmod) n = ξfun := hn'
  -- ### Stage 8: the invariant M-character ψ and its vanishing (frame-level)
  have hψ : ∀ t : ↥(En.radData l h).T, χ.1 t = 0 := by
    -- the ∂n-relation in `(cc, v)`-coordinates (via `θ`-surjectivity)
    have hkey : ∀ (cc : RF.YC) (v : En.Vmod),
        χ.1 (conjDef (En.descData l h) (descSections En l h Dsc)
            (descSigma_spec En l h Dsc) cc v) + gχ (cc • v) + gχ v
          = n v + n (cc • v) := by
      intro cc v
      obtain ⟨γ, hγ⟩ := hθs cc
      have h2 : γ • n = ξfun γ + n := sub_eq_iff_eq_add.mp (congrFun hn γ)
      have h4 : (γ • n) (cc • v) = n v := by
        rw [ElemDual.smul_apply]
        congr 1
        rw [hcomp, map_inv, hγ, inv_smul_smul]
      have h5 : ξfun γ (cc • v)
          = χ.1 (conjDef (En.descData l h) (descSections En l h Dsc)
              (descSigma_spec En l h Dsc) cc v) + gχ (cc • v) + gχ v := by
        rw [show ξfun γ = Fξ (θ γ) from rfl, hFval]
        rw [hγ, inv_smul_smul]
      have h3 : (γ • n) (cc • v) = ξfun γ (cc • v) + n (cc • v) :=
        DFunLike.congr_fun h2 (cc • v)
      rw [← h5, ← h4, h3]
      have hchar : ∀ X Y : ZMod 2, X = X + Y + Y := by decide
      exact hchar _ _
    -- conclude: `ψ = psiVCoord …` vanishes on `M` (additive + `Y_B`-conjugation-invariant),
    -- so `χ` vanishes on `T` (where the `V`-coordinate is trivial)
    intro t₀
    have h0 := mchar_conj_invariant_eq_zero RF En l h (psiVCoord En l h Dsc χ gχ n)
      (psiVCoord_add En l h Dsc χ gχ hg n) (psiVCoord_conj En l h Dsc χ gχ n hkey)
      ⟨t₀.1, (En.radData l h).hTM t₀.2⟩
    have hdesc1 : (En.descData l h).descend ⟨t₀.1, (En.radData l h).hTM t₀.2⟩ = 1 :=
      ((En.descData l h).hdesc_ker _).mpr t₀.2
    have harg : (⟨_, descend_tPart_mem En l h Dsc ⟨t₀.1, (En.radData l h).hTM t₀.2⟩⟩ :
        ↥(En.radData l h).T) = t₀ := by
      apply Subtype.ext
      show ((t₀ : RF.YB)) * (↑((descSections En l h Dsc).mV (Multiplicative.toAdd
          ((En.descData l h).descend ⟨t₀.1, (En.radData l h).hTM t₀.2⟩))))⁻¹
        = (t₀ : RF.YB)
      rw [hdesc1,
        show Multiplicative.toAdd (1 : Multiplicative (En.descData l h).Vmod)
          = (0 : (En.descData l h).Vmod) from toAdd_one, (descSections En l h Dsc).mV_zero]
      simp
    have hval : psiVCoord En l h Dsc χ gχ n ⟨t₀.1, (En.radData l h).hTM t₀.2⟩ = χ.1 t₀ := by
      show χ.1 ⟨_, descend_tPart_mem En l h Dsc ⟨t₀.1, (En.radData l h).hTM t₀.2⟩⟩
          + gχ (Multiplicative.toAdd ((En.descData l h).descend
              ⟨t₀.1, (En.radData l h).hTM t₀.2⟩))
          + n (Multiplicative.toAdd ((En.descData l h).descend
              ⟨t₀.1, (En.radData l h).hTM t₀.2⟩)) = χ.1 t₀
      have hg0' : gχ (Multiplicative.toAdd ((En.descData l h).descend
          ⟨t₀.1, (En.radData l h).hTM t₀.2⟩)) = 0 := by rw [hdesc1, toAdd_one]; exact hg0
      have hn0' : n (Multiplicative.toAdd ((En.descData l h).descend
          ⟨t₀.1, (En.radData l h).hTM t₀.2⟩)) = 0 := by
        rw [hdesc1]; exact map_zero n
      rw [harg, hg0', hn0', add_zero, add_zero]
    exact hval.symm.trans h0
  -- ### Stage 9: contradiction with `hχ`
  exact hχ (Subtype.ext (funext hψ))

/-! ### `SourceData` field-type smoke tests (R31 spelling discipline) -/

/-- Smoke test for the `SourceData.hsep` field at `Γ := GammaR`. -/
example : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom GammaR ↥boundarySubgroup) (F : BoundaryFrame H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
    (Dsc : Descent (En.radData l h)) (ρ : BoundaryLifts b F RF.TC)
    (c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)),
    (∀ χ : ↥(TCharC (En.radData l h)),
      betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c = 0) →
      TLiftable (descSigma_spec En l h Dsc) c :=
  fun b F En l h Dsc ρ c hc => hsep_gammaR b F En l h Dsc ρ c hc

/-- Smoke test for the `SourceData.hpartial` field at `Γ := GammaR`. -/
example : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom GammaR ↥boundarySubgroup) (F : BoundaryFrame H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
    (Dsc : Descent (En.radData l h)) (ρ : BoundaryLifts b F RF.TC)
    (χ : ↥(TCharC (En.radData l h))), χ ≠ 0 →
    ∃ c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ),
      betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c
        ≠ betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ
            (0 : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)) :=
  fun b F En l h Dsc ρ χ hχ => hpartial_gammaR b F En l h Dsc ρ χ hχ

end HsepGammaR

end Phase140GammaR

end GQ2

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Phase140.GammaA.Foundation

/-!
# The `Γ_A` separation and partial-count assembly

The word-side separator, private assembly helpers, and the final `hsep` calculation.

See `GQ2.Phase140.GammaA` for the paper-facing overview and architectural notes.
-/

namespace GQ2

namespace Phase140GammaA

open SectionEight AffineTLift CentralObstruction ContCoh WordCohBridge GQ2.FoxH RStageGammaA
  RadicalEdgeGammaA WordCoh2 MixedBObs

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
variable {RF : RecursionFrame T Blk}
variable (b : ContinuousMonoidHom GammaA ↥boundarySubgroup) (F : BoundaryFrame H E)
  (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)

/-! ## The word-side right-slot separator  (the `hpartial_A` stage-6 engine)

The `Γ_A` replacement for the local `cup11_dualEval_right_separating` (which runs on B6
Tate duality): a continuous dual 1-cocycle `ξ` whose pair cochain `(a,b) ↦ ξ(a)(a • z(b))`
is a continuous coboundary against EVERY `A`-cocycle `z` is itself a coboundary.  Route:
the pair cochain is the `kappaHeis`-inflation of the paired `wordHom`
(`MixedBObs.obs_inflation`), so its `WordCoh2.obs` equals the traced mixed pairing
`mixedB (markC θ) (eval z) (eval ξ)` (`mixedB_eq_relZPair`); `obs` kills `B²`
(`obs_B2_eq_zero`), so all word pairings vanish, and `prop_5_15`'s clause-3 RIGHT-slot
nondegeneracy forces `[eval ξ]_w = 0`; `eval_dZero` + `z1Equiv`-injectivity pull the word
coboundary back to a continuous one.  No B-axioms. -/

section WordSeparator

variable {Cf : Type} [Group Cf] [TopologicalSpace Cf] [DiscreteTopology Cf] [Finite Cf]
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction Cf A]
  [DistribMulAction GA A] [ContinuousSMul GA A]
  [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
  [DistribMulAction GA (ElemDual A)] [ContinuousSMul GA (ElemDual A)]
  [DistribMulAction GA (ZMod 2)] [ContinuousSMul GA (ZMod 2)]
variable (θ : ContinuousMonoidHom GA Cf)

omit [ContinuousSMul GA A] in
private theorem b1_of_pair_cochain_B2
    (hcompat : ∀ (γ : GA) (a : A), γ • a = θ γ • a)
    (hcompatD : ∀ (γ : GA) (lam : ElemDual A), γ • lam = θ γ • lam)
    (htriv : ∀ (x : GA) (m : ZMod 2), x • m = m)
    (hθs : Function.Surjective ⇑θ)
    (hA₂ : ∀ a : A, a + a = 0)
    (ξ : ↥(Z1 GA (ElemDual A)))
    (hvan : ∀ zc : ↥(Z1 GA A),
      (fun p : GA × GA => (ξ.1 p.1) (p.1 • zc.1 p.2)) ∈ B2 GA (ZMod 2)) :
    ∃ n : ElemDual A, dZero GA (ElemDual A) n = ξ.1 := by
  classical
  have hA₂D : ∀ lam : ElemDual A, lam + lam = 0 := fun lam => by
    ext a; exact CharTwo.add_self_eq_zero (lam a)
  have adm := markC_admissible θ hθs
  obtain ⟨P, hPmix, _hPleft, hPright⟩ :=
    (GQ2.FoxH.prop_5_15 (markC θ) adm.2.1 adm.2.2.1 adm.1 hA₂ adm.2.2.2).2.2
  -- every word pairing of `eval ξ` against a primal word class vanishes
  have hmix0 : ∀ xw : ↥(Z1w (A := A) (markC θ)),
      mixedB (markC θ) xw.1 (toZ1wHom θ hcompatD ξ).1 = 0 := by
    intro xw
    obtain ⟨zc, rfl⟩ := (z1Equiv θ hcompat hθs hA₂).surjective xw
    -- the paired `WordLift`-hom of `(zc, ξ)`
    have hcompatP : ∀ (γ : GA) (p : A × ElemDual A), γ • p = θ γ • p := fun γ p =>
      Prod.ext (hcompat γ p.1) (hcompatD γ p.2)
    set H : ContinuousMonoidHom GA (WordLift (A × ElemDual A) Cf) :=
      wordHom θ hcompatP
        ⟨fun γ => (zc.1 γ, ξ.1 γ),
          mem_Z1_iff.mpr ⟨((mem_Z1_iff.mp zc.2).1).prodMk ((mem_Z1_iff.mp ξ.2).1),
            fun γ δ => by
              rw [Prod.ext_iff]
              exact ⟨(mem_Z1_iff.mp zc.2).2 γ δ, (mem_Z1_iff.mp ξ.2).2 γ δ⟩⟩⟩ with hH
    -- the pair cochain is a `Z²` element (it is even a coboundary, `hvan`)
    have hmem : (fun p : GA × GA => (ξ.1 p.1) (p.1 • zc.1 p.2)) ∈ Z2 GA (ZMod 2) :=
      B2_le_Z2 (hvan zc)
    -- it is the `kappaHeis`-inflation along `H`
    have hunfold : ∀ a b : GA,
        (fun p : GA × GA => (ξ.1 p.1) (p.1 • zc.1 p.2)) (a, b)
          = kappaHeis.κ (H a) (H b) := by
      intro a b
      show (ξ.1 a) (a • zc.1 b) = (H a).u.2 ((H a).g • (H b).u.1)
      show (ξ.1 a) (a • zc.1 b) = (ξ.1 a) (θ a • zc.1 b)
      exact congrArg (ξ.1 a) (hcompat a (zc.1 b))
    -- its obstruction vanishes (`obs` kills `B²`)
    have hobs0 : obs htriv ⟨_, hmem⟩ = 0 :=
      AddMonoidHom.mem_ker.mp
        (obs_B2_eq_zero htriv (AddSubgroup.mem_addSubgroupOf.mpr (hvan zc)))
    -- ... and equals the traced mixed pairing
    have hinfl := obs_inflation htriv H kappaHeis ⟨_, hmem⟩ hunfold
    have hmark : gammaGen.map H.toMonoidHom
        = mBaseMarking (markC θ) (eval zc) (eval ξ) := by
      rw [markC_map]; rfl
    rw [hmark] at hinfl
    show mixedB (markC θ) (eval zc) (eval ξ) = 0
    rw [mixedB_eq_relZPair, ← hinfl]
    exact hobs0
  -- right-slot nondegeneracy kills the `ξ`-class
  have hcls0 : h1wMk (markC θ) (toZ1wHom θ hcompatD ξ) = 0 := by
    by_contra hne
    obtain ⟨hcl, hPne⟩ := hPright _ hne
    obtain ⟨xw, hxw⟩ := QuotientAddGroup.mk_surjective hcl
    exact hPne (hxw ▸ (hPmix xw (toZ1wHom θ hcompatD ξ)).trans (hmix0 xw))
  -- `B¹w`-extraction and pullback through the bridge
  have hmemB1w : ((toZ1wHom θ hcompatD ξ : ↥(Z1w (A := ElemDual A) (markC θ))) : Fin 4 → ElemDual A)
      ∈ B1w (A := ElemDual A) (markC θ) :=
    AddSubgroup.mem_addSubgroupOf.mp
      ((QuotientAddGroup.eq_zero_iff (toZ1wHom θ hcompatD ξ)).mp hcls0)
  obtain ⟨m, hm⟩ := AddMonoidHom.mem_range.mp hmemB1w
  refine ⟨m, ?_⟩
  have hbundle : (⟨dZero GA (ElemDual A) m, B1_le_Z1 ⟨m, rfl⟩⟩ : ↥(Z1 GA (ElemDual A))) = ξ := by
    apply (z1Equiv θ hcompatD hθs hA₂D).injective
    apply Subtype.ext
    show eval (⟨dZero GA (ElemDual A) m, B1_le_Z1 ⟨m, rfl⟩⟩ : ↥(Z1 GA (ElemDual A))) = eval ξ
    rwa [eval_dZero θ hcompatD m]
  exact congrArg Subtype.val hbundle

end WordSeparator

/-! ## Generic helpers for the `hsep_gammaA`/`hpartial_gammaA` decompositions -/

section GammaAHelpers

/-- Set-lift a marking through a surjective homomorphism, field by field. -/
private theorem exists_marking_map_eq {G G' : Type*} [Group G] [Group G'] {π : G →* G'}
    (hπ : Function.Surjective π) (t : Marking G') : ∃ s : Marking G, s.map π = t := by
  obtain ⟨yσ, hyσ⟩ := hπ t.σ
  obtain ⟨yτ, hyτ⟩ := hπ t.τ
  obtain ⟨yx₀, hyx₀⟩ := hπ t.x₀
  obtain ⟨yx₁, hyx₁⟩ := hπ t.x₁
  exact ⟨⟨yσ, yτ, yx₀, yx₁⟩, marking_ext hyσ hyτ hyx₀ hyx₁⟩

/-- Instance pack (`hpartial_gammaA` stage 0): a `Γ_A`-smul that factors pointwise through a
continuous hom to a discrete group is continuous on a discrete space. -/
private theorem continuousSMul_of_smul_factor {Cf X : Type} [Group Cf] [TopologicalSpace Cf]
    [DiscreteTopology Cf] [TopologicalSpace X] [DiscreteTopology X] [SMul Cf X] [SMul GA X]
    (θ : ContinuousMonoidHom GA Cf) (hcomp : ∀ (γ : GA) (x : X), γ • x = θ γ • x) :
    ContinuousSMul GA X := by
  constructor
  have hfac : (fun p : GA × X => p.1 • p.2)
      = (fun q : Cf × X => q.1 • q.2) ∘ fun p : GA × X => (θ p.1, p.2) := by
    funext p
    exact hcomp p.1 p.2
  rw [hfac]
  exact continuous_of_discreteTopology.comp
    ((θ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)

/-- The `θ`-compatibility of a pulled-back action passes to the contragredient duals. -/
private theorem elemDual_smul_eq_of_smul_eq {Cf A : Type} [Group Cf] [TopologicalSpace Cf]
    [AddCommGroup A] [DistribMulAction Cf A] [DistribMulAction GA A]
    (θ : ContinuousMonoidHom GA Cf)
    (hcomp : ∀ (γ : GA) (a : A), γ • a = θ γ • a) (γ : GA) (lam : ElemDual A) :
    γ • lam = θ γ • lam := by
  ext a
  rw [ElemDual.smul_apply, ElemDual.smul_apply]
  congr 1
  rw [hcomp, map_inv]

/-- `iotaB` is unchanged by a `B²`-shift (`hpartial_gammaA` stage 2). -/
private theorem iotaB_add_right_of_mem_B2 (φ β : GammaA × GammaA → ZMod 2)
    (hβ : β ∈ B2 GammaA (ZMod 2)) : iotaB (φ + β) = iotaB φ := by
  unfold iotaB
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ((AddSubgroup.add_mem_cancel_right _ hβ).mp h1) h2
  · exact absurd ((AddSubgroup.add_mem_cancel_right _ hβ).mpr h2) h1
  · rfl

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg}

/-- The relator values of a set-lift marking of a `Γ_A`-hom into `B/T` lie in `T` (the relator
words die along `g_Q`, so their `tB`-values die in `B/T`). -/
private theorem relatorValues_mem_of_map_eq_push (gQ : ContinuousMonoidHom GA (Bg ⧸ D.T))
    {tB : Marking Bg} (hproj : tB.map (QuotientGroup.mk' D.T) = Marking.push gQ) :
    tB.tameValue ∈ D.T ∧ tB.wildValue ∈ D.T := by
  constructor
  · have hmt := Marking.map_tameValue (QuotientGroup.mk' D.T) tB
    rw [hproj, (Marking.tameValue_eq_one_iff _).mpr (push_tameRel _)] at hmt
    exact (QuotientGroup.eq_one_iff _).mp hmt.symm
  · have hmw := Marking.map_wildValue (QuotientGroup.mk' D.T) tB
    rw [hproj, (Marking.wildValue_eq_one_iff _).mpr (push_wildRel _)] at hmw
    exact (QuotientGroup.eq_one_iff _).mp hmw.symm

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {DD : DescData D}
  {ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)}

omit [DiscreteTopology Bg] in
/-- A `π_T`-lift datum determines the `B/M`-value (`hsep_gammaA` §3): `liftC0` is injective
by `hkerC0`, and both sides land on the same `C₀`-value through `piQbar`. -/
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

end GammaAHelpers

section CharKernelPrivate

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg}

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
private theorem mem_charKer_iff (χ : ↥(TCharC D)) (t : ↥D.T) :
    (t : Bg) ∈ charKer χ ↔ χ.1 t = 0 :=
  Subgroup.mem_map_iff_mem Subtype.coe_injective

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
private theorem charKer_normal (χ : ↥(TCharC D)) : (charKer χ).Normal := by
  constructor
  intro n hn g
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hn
  refine Subgroup.mem_map.mpr
    ⟨⟨g * (t : Bg) * g⁻¹, D.hT.conj_mem (t : Bg) t.2 g⟩, ?_, rfl⟩
  show χ.1 ⟨g * (t : Bg) * g⁻¹, _⟩ = 0
  rwa [TCharC.conj_invariant χ g t]

end CharKernelPrivate

/-! ## `hsep` for `Γ_A`: the `(T^∨)^C`-separation via the marking route -/

section HsepGammaA

variable (Dsc : Descent (En.radData l h))

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- A `C`-fixed elementary dual of `Additive T` is conjugation-invariant: its values depend on
the `T`-element only up to `Y_B`-conjugacy (`hsep_gammaA` L4, invariance step). -/
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
/-- **`hsep_gammaA` L4 at one character**: a nonzero invariant character whose `β_χ(c)`
obstruction is a coboundary takes equal values on the tame and wild relator values of a
set-lift marking of `g_c` — the `χ`-cover lift (`exists_lift_charCover`) forces reduced-value
agreement (`redValues_eq_of_coverLift`), putting the discrepancy in `ker χ`. -/
private theorem tCharC_relatorSum_eq_zero (ρ : BoundaryLifts b F RF.TC)
    (c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
    (χ : ↥(TCharC (En.radData l h))) (hz : χ ≠ 0)
    (hB2 : chiDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c
      ∈ B2 GammaA (ZMod 2))
    {tB : Marking RF.YB}
    (hproj : tB.map (QuotientGroup.mk' (En.radData l h).T)
      = Marking.push (qOfCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)
          (descSigma En l h Dsc) (descSigma_spec En l h Dsc) c).1)
    (hv₁mem : tB.tameValue ∈ (En.radData l h).T)
    (hv₂mem : tB.wildValue ∈ (En.radData l h).T) :
    χ.1 ⟨tB.tameValue, hv₁mem⟩ + χ.1 ⟨tB.wildValue, hv₂mem⟩ = 0 := by
  obtain ⟨gc, hgc⟩ := exists_lift_charCover htriv_gammaA (descSections En l h Dsc)
    (descSigma_spec En l h Dsc) χ hz c hB2
  have hkey := redValues_eq_of_coverLift (charCover χ hz)
    (QuotientGroup.mk' (En.radData l h).T) (charCoverMap χ hz)
    (charCover_p_comp χ hz) _ gc hgc tB hproj
  have hmemK : ((⟨tB.tameValue, hv₁mem⟩ * (⟨tB.wildValue, hv₂mem⟩)⁻¹ :
      ↥(En.radData l h).T) : RF.YB) ∈ charKer χ := by
    have h1 : charCoverMap χ hz (tB.tameValue * tB.wildValue⁻¹) = 1 := by
      rw [map_mul, map_inv, hkey, mul_inv_cancel]
    have h2 : ((⟨tB.tameValue, hv₁mem⟩ * (⟨tB.wildValue, hv₂mem⟩)⁻¹ :
        ↥(En.radData l h).T) : RF.YB) ∈ (charCoverMap χ hz).ker := MonoidHom.mem_ker.mpr h1
    haveI : (charKer χ).Normal := charKer_normal χ
    rwa [show (charCoverMap χ hz).ker = charKer χ from
      QuotientGroup.ker_mk' (charKer χ)] at h2
  have hchival :=
    (mem_charKer_iff χ (⟨tB.tameValue, hv₁mem⟩ * (⟨tB.wildValue, hv₂mem⟩)⁻¹)).mp hmemK
  rw [TCharC.map_mul χ, TCharC.map_inv χ] at hchival
  exact hchival

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **`hsep_gammaA` L4**: when all `χ`-obstructions of `c` vanish, every `d⁰`-invariant
elementary dual kills the relator-value sum of a set-lift marking of `g_c` — zero characters
kill both values outright, nonzero ones agree on them by `tCharC_relatorSum_eq_zero`. -/
private theorem invariant_dual_relatorSum_eq_zero
    [DiscreteTopology (RF.YB ⧸ (En.radData l h).M)] (ρ : BoundaryLifts b F RF.TC)
    (c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
    (hc : ∀ χ : ↥(TCharC (En.radData l h)),
      betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c = 0)
    {tB : Marking RF.YB}
    (hproj : tB.map (QuotientGroup.mk' (En.radData l h).T)
      = Marking.push (qOfCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)
          (descSigma En l h Dsc) (descSigma_spec En l h Dsc) c).1)
    (hv₁mem : tB.tameValue ∈ (En.radData l h).T)
    (hv₂mem : tB.wildValue ∈ (En.radData l h).T) :
    ∀ lam : ElemDual (Additive ↥(En.radData l h).T),
      (d0 (A := ElemDual (Additive ↥(En.radData l h).T))
        (markC (RF.rhoPrime b F (En.radData l h) rfl ρ))) lam = 0 →
      lam (Additive.ofMul ⟨tB.tameValue, hv₁mem⟩ + Additive.ofMul ⟨tB.wildValue, hv₂mem⟩)
        = 0 := by
  intro lam hlam
  have adm := markC_admissible (RF.rhoPrime b F (En.radData l h) rfl ρ)
    (rhoPrime_surjective RF b F (En.radData l h) rfl ρ)
  have hfixmem : lam ∈ fixedPts (RF.YB ⧸ (En.radData l h).M)
      (ElemDual (Additive ↥(En.radData l h).T)) := by
    have hmem : lam ∈ H0w (A := ElemDual (Additive ↥(En.radData l h).T))
        (markC (RF.rhoPrime b F (En.radData l h) rfl ρ)) :=
      AddMonoidHom.mem_ker.mpr hlam
    rw [← H0w_eq_fixedPts (markC (RF.rhoPrime b F (En.radData l h) rfl ρ)) adm.1]
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
    rw [hlam0 ⟨tB.tameValue, hv₁mem⟩, hlam0 ⟨tB.wildValue, hv₂mem⟩, add_zero]
  · have hB2 : chiDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) chiLam c
        ∈ B2 GammaA (ZMod 2) := iotaB_eq_zero_iff.mp (hc chiLam)
    exact tCharC_relatorSum_eq_zero b F En l h Dsc ρ c chiLam hz hB2 hproj hv₁mem hv₂mem

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- `cActT` through the `M`-quotient map is `Y_B`-conjugation on `T`-realizations
(`hsep_gammaA` L5, the `hjconj` field of the correction calculus). -/
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
/-- **`hsep_gammaA` L5, correction step**: a word-level correction `x` with
`d¹x = (v₁, v₂)` (at the pushed `B/M`-base) turns a set-lift marking `tB` into one that kills
both relators (`corrected_tameValue`/`corrected_wildValue` + `T`-elementarity) and still
covers `g_Q` (the correction lies in `T`). -/
private theorem exists_relatorFree_marking (ρ : BoundaryLifts b F RF.TC)
    (gQ : QLiftsOver (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
    {tB : Marking RF.YB}
    (hproj : tB.map (QuotientGroup.mk' (En.radData l h).T) = Marking.push gQ.1)
    (hv₁mem : tB.tameValue ∈ (En.radData l h).T)
    (hv₂mem : tB.wildValue ∈ (En.radData l h).T)
    (x : Fin 4 → Additive ↥(En.radData l h).T)
    (hx : d1Fun (tB.map (QuotientGroup.mk' (En.radData l h).M)) x
      = (Additive.ofMul ⟨tB.tameValue, hv₁mem⟩, Additive.ofMul ⟨tB.wildValue, hv₂mem⟩)) :
    ∃ tHat : Marking RF.YB, tHat.TameRel ∧ tHat.WildRel ∧
      tHat.map (QuotientGroup.mk' (En.radData l h).T) = Marking.push gQ.1 := by
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
  have hd1 : d1Fun tB x
      = (Additive.ofMul ⟨tB.tameValue, hv₁mem⟩, Additive.ofMul ⟨tB.wildValue, hv₂mem⟩) := by
    rw [← d1Fun_base_change (QuotientGroup.mk' (En.radData l h).M) (fun _ _ => rfl) tB x]
    exact hx
  set tHat : Marking RF.YB :=
    ⟨((Additive.toMul (x 0) : ↥(En.radData l h).T) : RF.YB) * tB.σ,
      ((Additive.toMul (x 1) : ↥(En.radData l h).T) : RF.YB) * tB.τ,
      ((Additive.toMul (x 2) : ↥(En.radData l h).T) : RF.YB) * tB.x₀,
      ((Additive.toMul (x 3) : ↥(En.radData l h).T) : RF.YB) * tB.x₁⟩ with htHat
  refine ⟨tHat, ?_, ?_, ?_⟩
  · rw [← Marking.tameValue_eq_one_iff]
    rw [show tHat.tameValue
        = ((Additive.toMul ((d1Fun tB x).1) : ↥(En.radData l h).T) : RF.YB) * tB.tameValue from
      corrected_tameValue (fun a => ((Additive.toMul a : ↥(En.radData l h).T) : RF.YB))
        hjmul hjconj tB x, hd1]
    show ((⟨tB.tameValue, hv₁mem⟩ : ↥(En.radData l h).T) : RF.YB) * tB.tameValue = 1
    exact htelem _ hv₁mem
  · rw [← Marking.wildValue_eq_one_iff]
    rw [show tHat.wildValue
        = ((Additive.toMul ((d1Fun tB x).2) : ↥(En.radData l h).T) : RF.YB) * tB.wildValue from
      corrected_wildValue (fun a => ((Additive.toMul a : ↥(En.radData l h).T) : RF.YB))
        hjmul hjconj tB x, hd1]
    show ((⟨tB.wildValue, hv₂mem⟩ : ↥(En.radData l h).T) : RF.YB) * tB.wildValue = 1
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
/-- **`hsep` for `Γ_A`** — the `(T^∨)^C`-separation at the candidate source: a `V`-coordinate
whose `χ`-obstructions all vanish is `T`-liftable.  The `Γ_A` twin of
`Phase140Local.hsep_local`, by the **marking route** (the local `prop_5_16` `cup20` route has
no `Γ_A` analog): each nonzero invariant character's vanishing obstruction produces a lift
through its `𝔽₂`-cover (`exists_lift_charCover`), which forces `χ`-agreement of the relator
values of a set-lift marking (`redValues_eq_of_coverLift`); `sep_word` (the `prop_5_15`
trace-span) converts total agreement into word-level corrections; the corrected marking kills
both relators (`corrected_tameValue`/`corrected_wildValue` + `T`-elementarity) and descends
(`mlift_of_relatorFree_marking`) to the direct `M`-lift. -/
theorem hsep_gammaA
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
    (QuotientGroup.mk'_surjective (En.radData l h).T) (Marking.push gq0.1)
  -- §2: the relator values live in `T` (the relators die in `B/T` — `g_Q` is a hom)
  obtain ⟨hv₁mem, hv₂mem⟩ := relatorValues_mem_of_map_eq_push gq0.1 hproj
  -- §3+§4 (L4): every invariant character kills the relator-value sum
  have adm := markC_admissible (RF.rhoPrime b F (En.radData l h) rfl ρ) hρ's
  have hsd := GQ2.FoxH.prop_5_15 (markC (RF.rhoPrime b F (En.radData l h) rfl ρ))
    adm.2.1 adm.2.2.1 adm.1 hA₂ adm.2.2.2
  have hv := invariant_dual_relatorSum_eq_zero b F En l h Dsc ρ c hc hproj hv₁mem hv₂mem
  -- §5: the separation delivers word-level corrections
  have hsep := sep_word (markC (RF.rhoPrime b F (En.radData l h) rfl ρ))
    adm.2.1 adm.2.2.1 adm.1 hsd hA₂
    (Additive.ofMul ⟨tB.tameValue, hv₁mem⟩, Additive.ofMul ⟨tB.wildValue, hv₂mem⟩) hv
  obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp hsep
  -- §6 (L5): the corrected marking kills both relators and still covers `g_Q`
  have hfield : ∀ (y : RF.YB) (γ : GA),
      QuotientGroup.mk' (En.radData l h).T y = gq0.1 γ →
      QuotientGroup.mk (y : RF.YB) = RF.rhoPrime b F (En.radData l h) rfl ρ γ :=
    fun y γ hy => mk_eq_of_mkT_eq gq0 y γ hy
  have hmarkC : markC (RF.rhoPrime b F (En.radData l h) rfl ρ)
      = tB.map (QuotientGroup.mk' (En.radData l h).M) := by
    refine marking_ext ?_ ?_ ?_ ?_
    · exact (hfield tB.σ gammaGen.σ (congrArg Marking.σ hproj)).symm
    · exact (hfield tB.τ gammaGen.τ (congrArg Marking.τ hproj)).symm
    · exact (hfield tB.x₀ gammaGen.x₀ (congrArg Marking.x₀ hproj)).symm
    · exact (hfield tB.x₁ gammaGen.x₁ (congrArg Marking.x₁ hproj)).symm
  have hxB : d1Fun (tB.map (QuotientGroup.mk' (En.radData l h).M)) x
      = (Additive.ofMul ⟨tB.tameValue, hv₁mem⟩, Additive.ofMul ⟨tB.wildValue, hv₂mem⟩) := by
    rw [← hmarkC]
    exact hx
  obtain ⟨tHat, htameHat, hwildHat, hprojHat⟩ :=
    exists_relatorFree_marking b F En l h ρ gq0 hproj hv₁mem hv₂mem x hxB
  -- §7: descend and package as the `M`-lift
  obtain ⟨f₀, hf₀⟩ := mlift_of_relatorFree_marking gq0.1 tHat hprojHat htameHat hwildHat
  refine ⟨⟨f₀, fun γ => hfield (f₀ γ) γ (hf₀ γ)⟩, ?_⟩
  refine Subtype.ext (DFunLike.ext _ _ fun γ => ?_)
  rw [redTLift_apply]
  exact hf₀ γ

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- The `T`-realization of an `M`-element (`hpartial_gammaA` stage 8): `m · mV(v_m)⁻¹ ∈ T`,
where `v_m = toAdd(descend m)` is the `V`-coordinate; its `descend` is trivial, so it lands in
`T = ker(descend)|_M`. -/
private theorem descend_tPart_mem (m : ↥(En.radData l h).M) :
    ((m * ((descSections En l h Dsc).mV (Multiplicative.toAdd
      ((En.descData l h).descend m)))⁻¹ : ↥(En.radData l h).M) : RF.YB)
      ∈ (En.radData l h).T := by
  refine ((En.descData l h).hdesc_ker _).mp ?_
  rw [map_mul, map_inv, (descSections En l h Dsc).descend_mV, ofAdd_toAdd, mul_inv_cancel]

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **T-part product law** (`hpartial_gammaA` stage 8): `tpart(mm') = tpart m · tpart m' ·
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

/-- The invariant `M`-character `ψ` of `hpartial_gammaA` stage 8: the `V`-coordinatization
`ψ m = χ(tpart m) + gχ(v_m) + n(v_m)`, built from the character `χ`, the quadratic splitting
`gχ` and the `B¹`-witness `n`. -/
private noncomputable def psiVCoord (χ : ↥(TCharC (En.radData l h)))
    (gχ : En.Vmod → ZMod 2) (n : ElemDual En.Vmod) (m : ↥(En.radData l h).M) : ZMod 2 :=
  χ.1 ⟨_, descend_tPart_mem En l h Dsc m⟩
    + gχ (Multiplicative.toAdd ((En.descData l h).descend m))
    + n (Multiplicative.toAdd ((En.descData l h).descend m))

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- `ψ = psiVCoord …` is additive (`hpartial_gammaA` stage 8): the `mDef` term of the T-part
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
/-- `ψ = psiVCoord …` is `Y_B`-conjugation invariant (`hpartial_gammaA` stage 8): conjugating
`m` by `bb` shifts its T-part by `conjDef(cc, v_m)` and its V-coordinate by `cc • v_m`
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
/-- **Stage 2 of `hpartial_gammaA`**: the cup part of every `χ`-difference vanishes in `H²`.
The `betaChi`-collapse `hall` forces `iotaB` of the `χ`-difference to be `0`; peeling off the
`B²` `g`-parts (`gPart_mem_B2`) leaves exactly the cup cochain. -/
private theorem cupChi_iotaB_eq_zero (ρ : BoundaryLifts b F RF.TC)
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
  have htrivA : ∀ (γ : GammaA) (m : ZMod 2), γ • m = m := htriv_gammaA
  set c0 : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) := 0 with hc0
  have hB : ((fun p : GammaA × GammaA =>
        gχ (c.c (p.1 * p.2)) + gχ (c.c p.1) + gχ (c.c p.2))
      + (fun p : GammaA × GammaA =>
        gχ (c0.c (p.1 * p.2)) + gχ (c0.c p.1) + gχ (c0.c p.2)))
      ∈ B2 GammaA (ZMod 2) :=
    AddSubgroup.add_mem _
      (gPart_mem_B2 (descSigma_spec En l h Dsc) htrivA gχ c)
      (gPart_mem_B2 (descSigma_spec En l h Dsc) htrivA gχ c0)
  have hdecomp : chiDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c
      + chiDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c0
      = cupChi (En.descData l h) (descSections En l h Dsc)
          (RF.rhoPrime b F (En.radData l h) rfl ρ) (descSigma_spec En l h Dsc) gχ χ c
        + ((fun p : GammaA × GammaA =>
            gχ (c.c (p.1 * p.2)) + gχ (c.c p.1) + gχ (c.c p.2))
          + (fun p : GammaA × GammaA =>
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
    rw [iotaB_add CardH2GammaA.card_H2_gammaA
      (chiDef_mem_Z2 (descSections En l h Dsc) (descSigma_spec En l h Dsc) htrivA χ c)
      (chiDef_mem_Z2 (descSections En l h Dsc) (descSigma_spec En l h Dsc) htrivA χ c0)]
    have hbc : iotaB (chiDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c)
        = iotaB (chiDef (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c0) :=
      hall c
    rw [hbc, CharTwo.add_self_eq_zero]
  rw [hdecomp, iotaB_add_right_of_mem_B2 _ _ hB] at hiota
  exact hiota

set_option synthInstance.maxHeartbeats 800000 in
omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **`hpartial` for `Γ_A`** — nondegeneracy of the obstruction pairing in the character:
every nonzero `χ ∈ (T^∨)^C` is detected by some `V`-coordinate.  The `Γ_A` twin of
`Phase140Local.hpartial_local`, stages 1–5 and 7–9 mirrored verbatim (they are frame-level
or `Γ`-generic); the ONE divergent stage is the right-slot separation (local stage 6, B6
Tate duality), replaced by the word-side `b1_of_pair_cochain_B2` (`prop_5_15` clause-3
right-nondegeneracy through the `obs`/`mixedB` ledger).  All std-3, no B-axioms. -/
theorem hpartial_gammaA
    (ρ : BoundaryLifts b F RF.TC)
    (χ : ↥(TCharC (En.radData l h))) (hχ : χ ≠ 0) :
    ∃ c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ),
      betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c
        ≠ betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ
            (0 : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)) := by
  classical
  by_contra! hall
  -- ### Stage 0: module instances over the raw quotient `GA` (the `hZcard_gammaA` block)
  let θ : ContinuousMonoidHom GA RF.YC := ρ.1.1
  have hθs : Function.Surjective ⇑θ := ρ.1.2
  have hroundtrip : ∀ γ : GA,
      rho0 (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) γ = θ γ :=
    fun γ => rho0_descData_rhoPrime b F En l h ρ γ
  haveI : IsTopologicalGroup GA := inferInstanceAs (IsTopologicalGroup (GammaA : Type))
  letI : DistribMulAction GA (ZMod 2) := instDistribMulActionGammaA
  letI : ContinuousSMul GA (ZMod 2) := ⟨continuous_snd⟩
  have htriv : ∀ (x : GA) (m : ZMod 2), x • m = m := fun _ _ => rfl
  letI : TopologicalSpace En.Vmod := ⊥
  haveI : DiscreteTopology En.Vmod := ⟨rfl⟩
  letI actG : DistribMulAction GA En.Vmod :=
    DistribMulAction.compHom En.Vmod θ.toMonoidHom
  have hcomp : ∀ (γ : GA) (v : En.Vmod), γ • v = θ γ • v := fun _ _ => rfl
  haveI : ContinuousSMul GA En.Vmod := continuousSMul_of_smul_factor θ hcomp
  have hA₂ : ∀ v : En.Vmod, v + v = 0 := fun v => Vmod_exp2 (En.descData l h) v
  letI : TopologicalSpace (ElemDual En.Vmod) := ⊥
  haveI : DiscreteTopology (ElemDual En.Vmod) := ⟨rfl⟩
  have hcompD : ∀ (γ : GA) (lam : ElemDual En.Vmod), γ • lam = θ γ • lam :=
    fun γ lam => elemDual_smul_eq_of_smul_eq θ hcomp γ lam
  haveI : ContinuousSMul GA (ElemDual En.Vmod) := continuousSMul_of_smul_factor θ hcompD
  -- ### Stage 1: split `χ∘mDef` (the `betaChi_affine` splitting; frame-level)
  obtain ⟨gχ, hg0, hg⟩ := exists_splitting_of_symm_zero_diag (Vmod_exp2 (En.descData l h))
    (fun v w => χ.1 (mDef (En.descData l h) (descSections En l h Dsc) v w))
    (fun v w x => (isEquivariantFactorSet_datChi (descSections En l h Dsc)
      (descSigma_spec En l h Dsc) χ).f_cocycle v w x)
    (fun v w => by rw [mDef_symm])
    (fun v => by rw [mDef_self, TCharC.map_one])
    (fun v => by rw [mDef_zero_left, TCharC.map_one])
  -- ### Stage 2: the cup part of every `χ`-difference vanishes in `H²`
  -- (`cupChi_iotaB_eq_zero`: the `betaChi`-collapse minus the `B²` `g`-parts)
  have hcup := cupChi_iotaB_eq_zero b F En l h Dsc ρ χ gχ hg0 hg hall
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
  set ξfun : GA → ElemDual En.Vmod := fun γ => Fξ (θ γ) with hξdef
  -- ### Stage 4: ξ is a continuous 1-cocycle for the contragredient action (over `GA`)
  have hξZ1 : ξfun ∈ Z1 GA (ElemDual En.Vmod) := by
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
  have hvan : ∀ zc : ↥(Z1 GA En.Vmod),
      (fun p : GA × GA => (ξfun p.1) (p.1 • zc.1 p.2)) ∈ B2 GA (ZMod 2) := by
    intro zc
    -- the bridged `VCocycle` (the `hZcard_gammaA` construction)
    set c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) :=
      { c := fun γ => (zc.1 γ : (En.descData l h).Vmod)
        cont := (continuous_of_discreteTopology (f := fun v : En.Vmod =>
          iV (En.descData l h) (Multiplicative.ofAdd v))).comp (mem_Z1_iff.mp zc.2).1
        crossed := fun γ δ => by
          rw [hroundtrip γ]; exact (mem_Z1_iff.mp zc.2).2 γ δ } with hcdef
    have hident : (fun p : GA × GA => (ξfun p.1) (p.1 • zc.1 p.2))
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
  obtain ⟨n, hn'⟩ := b1_of_pair_cochain_B2 θ hcomp hcompD htriv hθs hA₂ ⟨ξfun, hξZ1⟩ hvan
  have hn : dZero GA (ElemDual En.Vmod) n = ξfun := hn'
  -- ### Stage 8: the invariant M-character ψ and its vanishing (frame-level, verbatim local)
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


end HsepGammaA

end Phase140GammaA

end GQ2

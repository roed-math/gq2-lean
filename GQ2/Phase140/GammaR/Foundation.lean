/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Phase140.GammaA.Foundation
import GQ2.WordCohBridgeR
import GQ2.Roe.DualityAssembly
import GQ2.HalfTorsorGammaR
import GQ2.RStage.GammaR
import GQ2.MixedBObsR
import GQ2.IotaGammaR

/-!
# Foundations for the `Γ_R` phase-140 residues

The Roe-candidate twin of `GQ2/Phase140/GammaA/Foundation.lean`: the candidate-side counts and
the `T`-stage descent of covering markings.

See `GQ2.Phase140.GammaR` for the paper-facing overview and architectural notes.

**What is reused, never cloned.**  The per-character `𝔽₂`-cover layer of `Γ_A`'s Foundation
(`Phase140GammaA.charKer`/`charCover`/`charCoverMap`/`charCover_p_comp`/`charCoverMap_coe_eq_zpow`/
`exists_lift_charCover`, `Foundation.lean:181–441`) is **abstract in `Γ`** — it takes the source as
a section variable with `[DistribMulAction Γ (ZMod 2)]` plus `htriv` — so `Γ_R` imports and applies
it at `GR` rather than re-deriving it.  Likewise the L5 kernel is the shared
`RStageGammaR.lift_of_relatorFree_markingR` (`GQ2/Roe/CoverLiftR.lean`), which is *more* general
than the `Γ_A` original precisely so that this file's non-surjective `T`-stage can feed it a
corestricted `Pro2Core` certificate instead of cloning the descent.
-/

namespace GQ2

namespace Phase140GammaR

-- `RStageGammaA` is opened for the **word-free** marking calculus it hosts (`marking_ext`,
-- `corrMark`, `tameValue_correction`) — the same reuse discipline `GQ2/Roe/CoverLiftR.lean` and
-- `GQ2/RStage/GammaR.lean` follow; nothing `Γ_A`-specific is consumed from it.
open SectionEight AffineTLift CentralObstruction ContCoh WordCohBridgeR GQ2.FoxH RStageGammaR
  RStageGammaA RadicalEdgeGammaA WordCoh2R MixedBObsR

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
variable {RF : RecursionFrame T Blk}
variable (b : ContinuousMonoidHom GammaR ↥boundarySubgroup) (F : BoundaryFrame H E)
  (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **`hZcard` for `Γ_R`** — `#Z¹_{Γ_R,ρ'}(V) = #V²`.  Mirror of `Phase140GammaA.hZcard_gammaA`
with the Roe word complex: the `VCocycle ≃ Z¹_cont(Γ_R, V)` bridge (structurally `Γ`-generic),
then `z1EquivR` + `prop_5_15_R` clause 2 (`#Z1wR = #V²·#fixedPts`) instead of `card_Z1_eq`, and
the `#fixedPts = 1` factor from the simple nontrivial `Y_C`-action
(`card_fixedPts_elemDual_eq_one_of_nontrivial`).

`hnt` (the nontrivial `Y_C`-action) is REQUIRED — in the `#V = 2 ∧ Y_C = 1` corner
`#(V^∨)^{Y_C} = 2 ≠ 1` and the identity is false; it is discharged at the capstone from the
block's chief-factor structure (same amendment as on the `Γ_A` and local sides). -/
theorem hZcard_gammaR
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v)
    (ρ : BoundaryLifts b F RF.TC) :
    Nat.card (VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
      = Nat.card En.Vmod * Nat.card En.Vmod := by
  classical
  -- the lower map `θ = ρ.1.1 : Γ_R ↠ Y_C`, retyped against the raw quotient `GR`
  let θ : ContinuousMonoidHom GR RF.YC := ρ.1.1
  have hθs : Function.Surjective ⇑θ := ρ.1.2
  have hroundtrip : ∀ γ : GR,
      rho0 (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) γ = θ γ :=
    fun γ => rho0_descData_rhoPrime b F En l h ρ γ
  -- `En.Vmod` (with its `Y_C`-action) as a `GR`-module through `θ`
  letI : TopologicalSpace En.Vmod := ⊥
  haveI : DiscreteTopology En.Vmod := ⟨rfl⟩
  letI actG : DistribMulAction GR En.Vmod := DistribMulAction.compHom En.Vmod θ.toMonoidHom
  have hcomp : ∀ (γ : GR) (v : En.Vmod), γ • v = θ γ • v := fun _ _ => rfl
  haveI : ContinuousSMul GR En.Vmod :=
    ⟨show Continuous ((fun q : RF.YC × En.Vmod => q.1 • q.2)
          ∘ fun p : GR × En.Vmod => (θ p.1, p.2)) from
      continuous_of_discreteTopology.comp
        ((θ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)⟩
  have hA₂ : ∀ v : En.Vmod, v + v = 0 := fun v => Vmod_exp2 (En.descData l h) v
  -- the `VCocycle ≃ Z¹_cont(GR, En.Vmod)` bridge (continuity through the `iV ∘ ofAdd` injection)
  have hequiv : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)
      ≃ ↥(Z1 GR En.Vmod) :=
    { toFun := fun c =>
        ⟨fun γ => (c.c γ : En.Vmod), by
          refine mem_Z1_iff.mpr ⟨?_, ?_⟩
          · exact (IsLocallyConstant.desc (α := En.Vmod) (fun γ => (c.c γ : En.Vmod))
              (fun v : En.Vmod => iV (En.descData l h) (Multiplicative.ofAdd v))
              ((IsLocallyConstant.iff_continuous _).mpr c.cont)
              fun a a' haa' => iV_ofAdd_inj (En.descData l h) haa').continuous
          · intro γ δ
            have H := c.crossed γ δ
            rwa [hroundtrip γ] at H⟩
      invFun := fun z =>
        { c := fun γ => (z.1 γ : (En.descData l h).Vmod)
          cont := (continuous_of_discreteTopology (f := fun v : En.Vmod =>
            iV (En.descData l h) (Multiplicative.ofAdd v))).comp (mem_Z1_iff.mp z.2).1
          crossed := fun γ δ => by
            rw [hroundtrip γ]; exact (mem_Z1_iff.mp z.2).2 γ δ }
      left_inv := fun c => rfl
      right_inv := fun z => rfl }
  -- the count: `#Z¹(GR, V) = #Z1wR(markC_R θ) = #V² · #fixedPts Y_C (V^∨)` (Roe duality)
  have adm := markC_admissible_R θ hθs
  rw [Nat.card_congr hequiv, Nat.card_congr (z1EquivR θ hcomp hθs hA₂).toEquiv,
    (GQ2.FoxH.prop_5_15_R (markC_R θ) adm.2.1 adm.2.2.1 adm.1 hA₂ adm.2.2.2).2.1]
  -- `#fixedPts Y_C (V^∨) = 1` (simple module, nontrivial action)
  obtain ⟨v, hv⟩ := hVne
  have hsimpleMod : IsSimpleModTwo RF.YC En.Vmod :=
    ⟨nontrivial_of_ne (0 : En.Vmod) v hv.symm, fun W hW => hsimple W hW⟩
  rw [card_fixedPts_elemDual_eq_one_of_nontrivial hsimpleMod hnt, mul_one, pow_two]

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **`hμ` for `Γ_R`** — the `T`-cocycle count `#Z¹_{Γ_R,ρ'}(T) = #T²·#(T^∨)^{Y_B/M}` in the
`muZero` closed form (`Phase140GammaA.tcocycle_card_gammaA`'s twin).  Same module setup (the
global `RadicalEdgeGammaA.cActT` conjugation action, which is `Γ`-free over `RadicalCoverData`)
and the same `TCocycle ≃ Z¹_cont(GR, Additive T)` bridge; the count is `z1EquivR` + `prop_5_15_R`
clause 2.  The `#fixedPts` factor is NOT reduced: it is part of the shared `μ₀` value (the twin
dualities produce the same closed form, which is the source-independence `prop_8_9` needs). -/
theorem tcocycle_card_gammaR (ρ : BoundaryLifts b F RF.TC) :
    Nat.card (TCocycle (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
      = Nat.card (Additive ↥(En.radData l h).T) ^ 2
        * Nat.card (fixedPts (RF.YB ⧸ (En.radData l h).M)
            (ElemDual (Additive ↥(En.radData l h).T))) := by
  classical
  haveI : (En.radData l h).M.Normal := (En.radData l h).hM
  haveI : DiscreteTopology (RF.YB ⧸ (En.radData l h).M) :=
    discreteTopology_quotient (En.radData l h)
  -- the lower map, retyped against the raw quotient `GR`
  let θ : ContinuousMonoidHom GR (RF.YB ⧸ (En.radData l h).M) :=
    RF.rhoPrime b F (En.radData l h) rfl ρ
  have hθs : Function.Surjective ⇑θ := fun y =>
    rhoPrime_surjective RF b F (En.radData l h) rfl ρ y
  -- `Additive ↥T` as a finite discrete `GR`-module through `θ` (the `C`-action is the
  -- global `cActT`)
  letI : TopologicalSpace (Additive ↥(En.radData l h).T) :=
    (inferInstance : TopologicalSpace ↥(En.radData l h).T)
  haveI : DiscreteTopology (Additive ↥(En.radData l h).T) :=
    ⟨(inferInstance : DiscreteTopology ↥(En.radData l h).T).eq_bot⟩
  haveI : Finite (Additive ↥(En.radData l h).T) :=
    (inferInstance : Finite ↥(En.radData l h).T)
  letI actG : DistribMulAction GR (Additive ↥(En.radData l h).T) :=
    DistribMulAction.compHom _ θ.toMonoidHom
  have hcomp : ∀ (γ : GR) (a : Additive ↥(En.radData l h).T), γ • a = θ γ • a :=
    fun _ _ => rfl
  -- the action at a representative `bb` of `θ γ`
  have hsmul : ∀ (γ : GR) (bb : RF.YB) (a : Additive ↥(En.radData l h).T),
      QuotientGroup.mk bb = θ γ →
      γ • a = Additive.ofMul (⟨bb * (Additive.toMul a).1 * bb⁻¹,
        (En.radData l h).hT.conj_mem _ (Additive.toMul a).2 _⟩ : ↥(En.radData l h).T) :=
    fun γ bb a hbb => Additive.toMul.injective
      (Subtype.ext (cactFun_eq (En.radData l h) (θ γ) hbb (Additive.toMul a)))
  haveI : ContinuousSMul GR (Additive ↥(En.radData l h).T) :=
    ⟨show Continuous
        ((fun q : (RF.YB ⧸ (En.radData l h).M) × Additive ↥(En.radData l h).T => q.1 • q.2)
          ∘ fun p : GR × Additive ↥(En.radData l h).T => (θ p.1, p.2)) from
      continuous_of_discreteTopology.comp
        ((θ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)⟩
  have hA₂ : ∀ a : Additive ↥(En.radData l h).T, a + a = 0 := fun a =>
    Additive.toMul.injective
      (Subtype.ext ((En.radData l h).helem _ ((En.radData l h).hTM (Additive.toMul a).2)))
  -- the direct `TCocycle ≃ Z¹_cont(GR, Additive T)` bridge
  have hequiv : TCocycle (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)
      ≃ ↥(Z1 GR (Additive ↥(En.radData l h).T)) :=
    { toFun := fun u =>
        ⟨fun γ => Additive.ofMul ⟨u.u γ, u.mem γ⟩, by
          refine mem_Z1_iff.mpr ⟨?_, ?_⟩
          · exact Continuous.subtype_mk u.cont _
          · intro γ δ
            rw [hsmul γ (Quotient.out (θ γ)) (Additive.ofMul ⟨u.u δ, u.mem δ⟩)
              (QuotientGroup.out_eq' _)]
            exact Additive.toMul.injective (Subtype.ext
              (u.crossed γ δ (Quotient.out (θ γ)) (QuotientGroup.out_eq' _)))⟩
      invFun := fun z =>
        { u := fun γ => ((Additive.toMul (z.1 γ) : ↥(En.radData l h).T)).1
          mem := fun γ => (Additive.toMul (z.1 γ)).2
          cont := continuous_subtype_val.comp (mem_Z1_iff.mp z.2).1
          crossed := fun γ δ bb hbb => by
            have hz := (mem_Z1_iff.mp z.2).2 γ δ
            rw [hsmul γ bb (z.1 δ) hbb] at hz
            exact congrArg (fun a => ((Additive.toMul a : ↥(En.radData l h).T)).1) hz }
      left_inv := fun u => rfl
      right_inv := fun z => rfl }
  -- the count: `#Z¹(GR, T) = #Z1wR(markC_R θ) = #T² · #fixedPts C (T^∨)` (Roe duality)
  have adm := markC_admissible_R θ hθs
  rw [Nat.card_congr hequiv, Nat.card_congr (z1EquivR θ hcomp hθs hA₂).toEquiv,
    (GQ2.FoxH.prop_5_15_R (markC_R θ) adm.2.1 adm.2.2.1 adm.1 hA₂ adm.2.2.2).2.1]

/-! ## L5 descent at the `T`-stage: a relator-free covering marking of `B` descends from `Γ_R`

The `T`-stage consumer of the shared `Γ_R` L5 kernel (`GQ2/Roe/CoverLiftR.lean`), with the one
twist the `Γ_A` side also had to absorb: the covered map `g_Q : Γ_R → B/T` is **not surjective**
(its image is the graph-like subgroup of a `V`-cocycle), so `Marking.pushR_admissible` does not
apply to it directly and no `Pro2Core` certificate is available downstairs.

The `Γ_A` file solved this by cloning the whole descent (`Phase140GammaA.mlift_of_relatorFree_marking`,
221 ln).  Here the kernel was deliberately generalised — `lift_of_relatorFree_markingR` takes an
**abstract** `π` and the `Pro2Core` input **directly** rather than through surjectivity of `g_B` —
so the fix is just a corestriction: the four `B/T`-generator images generate `J̄`, the `F₄`-hom
classified by the `J̄`-marking kills `N_R`, so it descends to a **surjective** `ḡ : Γ_R ↠ J̄`, whose
pushed marking is `R`-admissible and supplies `hcoreB`.  Nothing of the kernel is cloned. -/

section DescendT

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg}

/-- **The `T`-stage descent** (`hsep_gammaR` L5): a marking of `B` that covers `g_Q`'s marking
through `π_T` and kills both `Γ_R` relators descends to a continuous `f : Γ_R → B` with
`π_T ∘ f = g_Q`.  `Γ_R` twin of `Phase140GammaA.mlift_of_relatorFree_marking`, but assembled from
the shared kernel `RStageGammaR.lift_of_relatorFree_markingR` at the corestricted projection
`qJ' : J → J̄` instead of re-deriving the descent. -/
theorem mlift_of_relatorFree_markingR
    (gQ : ContinuousMonoidHom GR (Bg ⧸ D.T))
    (tHat : Marking Bg)
    (hproj : tHat.map (QuotientGroup.mk' D.T) = Marking.pushR gQ)
    (htame : tHat.TameRel) (hwild : tHat.WildRelR) :
    ∃ f : ContinuousMonoidHom GammaR Bg,
      ∀ γ, QuotientGroup.mk' D.T (f γ) = gQ γ := by
  classical
  have htelem : ∀ t ∈ D.T, t * t = 1 := fun t ht => D.helem t (D.hTM ht)
  -- §1: the generated subgroup of `B` and its marking
  set J : Subgroup Bg := Subgroup.closure {tHat.σ, tHat.τ, tHat.x₀, tHat.x₁} with hJ
  have hmemσ : tHat.σ ∈ J := Subgroup.subset_closure (by simp)
  have hmemτ : tHat.τ ∈ J := Subgroup.subset_closure (by simp)
  have hmemx₀ : tHat.x₀ ∈ J := Subgroup.subset_closure (by simp)
  have hmemx₁ : tHat.x₁ ∈ J := Subgroup.subset_closure (by simp)
  set tJ : Marking ↥J :=
    ⟨⟨tHat.σ, hmemσ⟩, ⟨tHat.τ, hmemτ⟩, ⟨tHat.x₀, hmemx₀⟩, ⟨tHat.x₁, hmemx₁⟩⟩ with htJ
  have hmapJ : tJ.map J.subtype = tHat := marking_ext rfl rfl rfl rfl
  have htameJ : tJ.TameRel := by
    rw [← Marking.tameValue_eq_one_iff]
    have hm := Marking.map_tameValue J.subtype tJ
    rw [hmapJ, (Marking.tameValue_eq_one_iff tHat).mpr htame] at hm
    exact Subtype.val_injective hm.symm
  have hwildJ : tJ.WildRelR := by
    rw [← Marking.wildValueR_eq_one_iff]
    have hm := Marking.map_wildValueR J.subtype tJ
    rw [hmapJ, (Marking.wildValueR_eq_one_iff tHat).mpr hwild] at hm
    exact Subtype.val_injective hm.symm
  -- §2: the corestriction `ḡ : Γ_R ↠ J̄ = ⟨g_Q-generator images⟩ ≤ B/T`
  set Jbar : Subgroup (Bg ⧸ D.T) := Subgroup.closure
    {(Marking.pushR gQ).σ, (Marking.pushR gQ).τ, (Marking.pushR gQ).x₀, (Marking.pushR gQ).x₁}
    with hJbar
  have hmemσ' : (Marking.pushR gQ).σ ∈ Jbar := Subgroup.subset_closure (by simp)
  have hmemτ' : (Marking.pushR gQ).τ ∈ Jbar := Subgroup.subset_closure (by simp)
  have hmemx₀' : (Marking.pushR gQ).x₀ ∈ Jbar := Subgroup.subset_closure (by simp)
  have hmemx₁' : (Marking.pushR gQ).x₁ ∈ Jbar := Subgroup.subset_closure (by simp)
  set tbar : Marking ↥Jbar :=
    ⟨⟨(Marking.pushR gQ).σ, hmemσ'⟩, ⟨(Marking.pushR gQ).τ, hmemτ'⟩,
      ⟨(Marking.pushR gQ).x₀, hmemx₀'⟩, ⟨(Marking.pushR gQ).x₁, hmemx₁'⟩⟩ with htbar
  have hclassbar : univMarking.map (Marking.classify tbar).toMonoidHom = tbar :=
    univMarking_map_toHom (P := ProfiniteGrp.of ↥Jbar) tbar
  -- the classified hom, compared with `g_Q ∘ quotientMk` through the subtype
  set cbar : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) (Bg ⧸ D.T) :=
    (⟨Jbar.subtype, continuous_subtype_val⟩ :
        ContinuousMonoidHom ↥Jbar (Bg ⧸ D.T)).comp (Marking.classify tbar) with hcbar
  have hcomp : cbar = gQ.comp (quotientMk NR) := by
    have h1 := Marking.toHom_hom_univMarking_map cbar
    have h2 := Marking.toHom_hom_univMarking_map (gQ.comp (quotientMk NR))
    have hpushc : univMarking.map cbar.toMonoidHom
        = univMarking.map (gQ.comp (quotientMk NR)).toMonoidHom := by
      refine marking_ext ?_ ?_ ?_ ?_
      · exact congrArg (fun t : Marking ↥Jbar => (t.σ : Bg ⧸ D.T)) hclassbar
      · exact congrArg (fun t : Marking ↥Jbar => (t.τ : Bg ⧸ D.T)) hclassbar
      · exact congrArg (fun t : Marking ↥Jbar => (t.x₀ : Bg ⧸ D.T)) hclassbar
      · exact congrArg (fun t : Marking ↥Jbar => (t.x₁ : Bg ⧸ D.T)) hclassbar
    rw [← h1, ← h2, hpushc]
  have hker : NR ≤ (Marking.classify tbar).toMonoidHom.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    refine Subtype.val_injective ?_
    have h1 : (((Marking.classify tbar).toMonoidHom x : ↥Jbar) : Bg ⧸ D.T) = cbar x := rfl
    rw [h1, hcomp]
    show gQ (quotientMk NR x) = ((1 : ↥Jbar) : Bg ⧸ D.T)
    rw [(quotientMk_eq_one_iff NR).mpr hx, map_one]
    rfl
  set gbar : ContinuousMonoidHom GR ↥Jbar :=
    quotientLift NR (Marking.classify tbar) hker with hgbar
  have hgbar_val : ∀ γ : GR, (gbar γ : Bg ⧸ D.T) = gQ γ := by
    intro γ
    obtain ⟨w, rfl⟩ := quotientMk_surjective NR γ
    show (Marking.classify tbar w : Bg ⧸ D.T) = gQ (quotientMk NR w)
    rw [show (Marking.classify tbar w : Bg ⧸ D.T) = cbar w from rfl, hcomp]
    rfl
  -- `ḡ` hits the four generators, hence is surjective; its pushed marking is `tbar`
  have hgbar_gen : ∀ i : Fin 4, gbar (quotientMk NR (FreeProfiniteGroup.of i)) =
      ![tbar.σ, tbar.τ, tbar.x₀, tbar.x₁] i := by
    intro i
    show Marking.classify tbar (FreeProfiniteGroup.of i) = _
    fin_cases i
    exacts [congrArg Marking.σ hclassbar, congrArg Marking.τ hclassbar,
      congrArg Marking.x₀ hclassbar, congrArg Marking.x₁ hclassbar]
  have hpushbar : Marking.pushR gbar = tbar := by
    refine marking_ext ?_ ?_ ?_ ?_
    · exact hgbar_gen 0
    · exact hgbar_gen 1
    · exact hgbar_gen 2
    · exact hgbar_gen 3
  have hgenbar : Subgroup.closure ({tbar.σ, tbar.τ, tbar.x₀, tbar.x₁} : Set ↥Jbar) = ⊤ := by
    have hpre : ({tbar.σ, tbar.τ, tbar.x₀, tbar.x₁} : Set ↥Jbar)
        = ((↑) : ↥Jbar → Bg ⧸ D.T) ⁻¹'
          {(Marking.pushR gQ).σ, (Marking.pushR gQ).τ, (Marking.pushR gQ).x₀,
            (Marking.pushR gQ).x₁} := by
      ext j
      simp [htbar, Subtype.ext_iff]
    rw [hpre]
    exact Subgroup.closure_closure_coe_preimage
  have hgbar_surj : Function.Surjective ⇑gbar := by
    intro y
    have hy : y ∈ Subgroup.closure ({tbar.σ, tbar.τ, tbar.x₀, tbar.x₁} : Set ↥Jbar) := by
      rw [hgenbar]
      exact Subgroup.mem_top y
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hy
    · rintro z (rfl | rfl | rfl | rfl)
      exacts [⟨_, hgbar_gen 0⟩, ⟨_, hgbar_gen 1⟩, ⟨_, hgbar_gen 2⟩, ⟨_, hgbar_gen 3⟩]
    · exact ⟨1, map_one gbar⟩
    · rintro a b - - ⟨γ, rfl⟩ ⟨δ, rfl⟩
      exact ⟨γ * δ, map_mul gbar γ δ⟩
    · rintro a - ⟨γ, rfl⟩
      exact ⟨γ⁻¹, map_inv gbar γ⟩
  -- §3: the corestricted comparison `qJ' : J → J̄`, and the kernel torsion `π_T`-elementarity
  have hmapJc : J.map (QuotientGroup.mk' D.T)
      = Subgroup.closure ((QuotientGroup.mk' D.T) '' {tHat.σ, tHat.τ, tHat.x₀, tHat.x₁}) := by
    rw [hJ, MonoidHom.map_closure]
  have hmemJbar : ∀ j : ↥J, QuotientGroup.mk' D.T (j : Bg) ∈ Jbar := by
    intro j
    have himg : QuotientGroup.mk' D.T (j : Bg)
        ∈ J.map (QuotientGroup.mk' D.T) := Subgroup.mem_map_of_mem _ j.2
    rw [hmapJc] at himg
    refine Subgroup.closure_mono ?_ himg
    rintro x ⟨y, (rfl | rfl | rfl | rfl), rfl⟩
    exacts [Or.inl (congrArg Marking.σ hproj), Or.inr (Or.inl (congrArg Marking.τ hproj)),
      Or.inr (Or.inr (Or.inl (congrArg Marking.x₀ hproj))),
      Or.inr (Or.inr (Or.inr (congrArg Marking.x₁ hproj)))]
  set qJ' : ↥J →* ↥Jbar :=
    ((QuotientGroup.mk' D.T).comp J.subtype).codRestrict Jbar (fun j => hmemJbar j) with hqJ'
  have hker2 : ∀ j ∈ qJ'.ker, j * j = 1 := by
    intro j hj
    rw [MonoidHom.mem_ker] at hj
    have hjT : (j : Bg) ∈ D.T := by
      have h1 : QuotientGroup.mk' D.T (j : Bg) = 1 := congrArg Subtype.val hj
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subtype.val_injective (by simpa using htelem _ hjT)
  have hprojJ : tJ.map qJ' = Marking.pushR gbar := by
    rw [hpushbar]
    refine marking_ext ?_ ?_ ?_ ?_
    exacts [Subtype.ext (congrArg Marking.σ hproj), Subtype.ext (congrArg Marking.τ hproj),
      Subtype.ext (congrArg Marking.x₀ hproj), Subtype.ext (congrArg Marking.x₁ hproj)]
  -- §4: descend through the shared `Γ_R` L5 kernel, then include `J ↪ B`
  obtain ⟨φ, hφ⟩ := lift_of_relatorFree_markingR qJ' hker2 gbar
    (Marking.pushR_admissible gbar hgbar_surj).2.2.2 tJ hprojJ htameJ hwildJ
  refine ⟨(⟨J.subtype, continuous_subtype_val⟩ : ContinuousMonoidHom ↥J Bg).comp φ, ?_⟩
  intro γ
  show QuotientGroup.mk' D.T ((φ γ : ↥J) : Bg) = gQ γ
  rw [show QuotientGroup.mk' D.T ((φ γ : ↥J) : Bg) = ((qJ' (φ γ) : ↥Jbar) : Bg ⧸ D.T) from rfl,
    hφ γ]
  exact hgbar_val γ

end DescendT

/-! ### `SourceData` field-type smoke tests (R31 spelling discipline)

Each residue is restated in the **verbatim** `GQ2.SourceData` field type at `Γ := GammaR` and
discharged by the plain lambda `BoundaryMaps.sourceA` uses for its `_gammaA` twin
(`GQ2/SourceData.lean:325–330`), so `sourceR` (R32) is a copy-paste. -/

/-- Smoke test for the `SourceData.hZcard` field at `Γ := GammaR`. -/
example : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom GammaR ↥boundarySubgroup) (F : BoundaryFrame H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR),
    (∀ W : AddSubgroup En.Vmod, (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∃ v : En.Vmod, v ≠ 0) →
    (∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v) →
    ∀ ρ : BoundaryLifts b F RF.TC,
      Nat.card (VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
        = Nat.card En.Vmod * Nat.card En.Vmod :=
  fun b F En l h hsimple hVne hnt ρ => hZcard_gammaR b F En l h hsimple hVne hnt ρ

/-- Smoke test for the `SourceData.tcocycle_card` field at `Γ := GammaR`. -/
example : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom GammaR ↥boundarySubgroup) (F : BoundaryFrame H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR) (ρ : BoundaryLifts b F RF.TC),
    Nat.card (TCocycle (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
      = Nat.card (Additive ↥(En.radData l h).T) ^ 2
        * Nat.card (fixedPts (RF.YB ⧸ (En.radData l h).M)
            (ElemDual (Additive ↥(En.radData l h).T))) :=
  fun b F En l h ρ => tcocycle_card_gammaR b F En l h ρ

end Phase140GammaR

end GQ2

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.RStage.GammaA
import GQ2.Roe.GammaR
import GQ2.Roe.CorrectionR
import GQ2.Roe.TrivialSelfDual
import GQ2.Roe.DualityAssembly
import GQ2.Roe.Devissage.EvalPairings

/-!
# The `(136)` R-stage for `Γ = Γ_R`

The **instance prerequisite** of the `Γ_R` source-data supply (ticket R31, discovered by the R30
`SourceData` recon): the `(136)`/`(140)`/Gauss-`Z` layers are all stated at an ambient
`DistribMulAction Γ (ZMod 2)`, and `GQ2.SourceData` carries that action as the three fields
`smulZmod2` / `contSMulZmod2` / `htriv`.  On the `Γ_A` side these are the *global* instances
registered in `GQ2/RStage/GammaA.lean:53-69`; this file registers their `Γ_R` mirrors so that
R32's `sourceR` can fill the three fields with `inferInstance`, `inferInstance`,
`RStageGammaR.htriv_gammaR` — exactly as `BoundaryMaps.sourceA` does
(`GQ2/SourceData.lean:316-318`).

On top of that instance layer this file carries the whole `Γ_R` `(136)` chain — the twin of
`GQ2/RStage/GammaA.lean`, name-for-name (ticket R31e, obligation ii.5):

* `hZcount_gammaR` — `#RCocycle = z_R`, via the *Roe* word bridge `z1EquivR`
  (`GQ2/WordCohBridgeR.lean`) + `prop_5_15_R` clause 2 + the frame-generic `blockRChar_card`;
* `wTrace_R` / `sep_word_R` — the `(2,0)`-trace-span package on `H²_{R,word}`, driven by
  `prop_5_8_right_R` and `IsSelfDual_R` clause 1 (**no** `H²(Γ_R, R)`);
* `hsep_hom_gammaR` — the `(R^∨)^C`-separation, on the shared L4/L5 cover-lift kernel
  `GQ2/Roe/CoverLiftR.lean`;
* `stageR136_gammaR_of_hcard` — the `(136)` identity, threading `hcard_R` hypothesis-side exactly
  as `stageR136_gammaA_of_hcard` threads `hcard_A` (so ii.5 is decoupled from the `card_H2`
  obligation, which is owned elsewhere).

Since `Aut(𝔽₂) = 1`, *every* action of any group on `ZMod 2` is the trivial one, so the content
here is nil: the instance is defined by `smul _ m := m` and `htriv_gammaR` is `rfl`.  What matters
is that the action is **registered globally at the `ProfiniteGrp`-bundled carrier `GammaR`**, the
carrier spelling the `SourceData` fields use (`↥Γ` at `Γ := GammaR`) — a `DistribMulAction`
registered at the raw quotient `F₄ ⧸ N_R` would *not* cross-resolve, exactly the `GammaA`/`GA`
instance-diamond documented in the `GQ2/RStage/GammaA.lean` standing plumbing note.

**Module-system note.**  Plain `import` (non-`module`), like its siblings `GQ2/Roe/Supply.lean`
and `GQ2/Roe/Prop23.lean`: it imports the non-`module` `GQ2.RStage.GammaA`, and `module`-style
files cannot import plain ones.  Importing the `module` file `GQ2.Roe.GammaR` from here is fine —
the restriction is one-directional.

Axioms: none introduced (`htriv_gammaR` is `rfl`; the instances are definitional).
-/

namespace GQ2

namespace RStageGammaR

open ContCoh SectionEight SectionSeven WordCohBridgeR GQ2.FoxH RStageGammaA

/-- `Γ_R`'s underlying type is the raw quotient `F₄ ⧸ N_R` against which the Roe marking
machinery (`markC_R`, `Z1wR`, `prop_5_15_R`) is stated — the `Γ_R` mirror of
`RStageGammaA.gammaA_eq_GA`, and the bridge every `Γ_R` word-machinery call transports across. -/
theorem gammaR_eq_quotient : (GammaR : Type) = (FreeProfiniteGroup (Fin 4) ⧸ NR) := rfl

/-! ## The canonical trivial `Γ_R`-action on `𝔽₂` -/

/-- The trivial `Γ_R`-action on `𝔽₂` (`Aut(𝔽₂) = 1`, so every action is this one).  Mirror of
`RStageGammaA.instDistribMulActionGammaA`. -/
instance instDistribMulActionGammaR : DistribMulAction GammaR (ZMod 2) where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

instance : ContinuousSMul GammaR (ZMod 2) := ⟨continuous_snd⟩

/-- **The `Γ_R`-action on `𝔽₂` is trivial** — the `htriv` field of `Γ_R`'s `SourceData`
(`GQ2/SourceData.lean:123`), mirror of `RStageGammaA.htriv_gammaA`.  Definitional, from the
registered trivial action. -/
theorem htriv_gammaR (γ : GammaR) (m : ZMod 2) : γ • m = m := rfl

/-! ### Sanity lemmas -/

/-- **Sanity 1.**  The registered action is the trivial one on the nose: scalar multiplication is
the second projection, so it is constant in the group argument. -/
theorem smul_eq_of_gammaR (γ δ : GammaR) (m : ZMod 2) : γ • m = δ • m := rfl

/-- **Sanity 2.**  The `Γ_R` action agrees with the `Γ_A` one under any map of underlying
elements — both are the unique (trivial) action, so the two sources present `𝔽₂` identically to
the `(136)`/`(140)` layers. -/
theorem htriv_gammaR_and_gammaA (γ : GammaR) (α : GammaA) (m : ZMod 2) :
    γ • m = m ∧ α • m = m :=
  ⟨htriv_gammaR γ m, RStageGammaA.htriv_gammaA α m⟩

/-- **Sanity 3.**  The action is by additive-group automorphisms and fixes everything, so the
fixed-point set is all of `𝔽₂` — the degenerate input the `(140)` layer's `fixedPts` factors
reduce through. -/
theorem gammaR_smul_add (γ : GammaR) (m n : ZMod 2) : γ • (m + n) = γ • m + γ • n := by
  rw [htriv_gammaR, htriv_gammaR, htriv_gammaR]

/-! ### `SourceData` field-type smoke tests (R31 spelling discipline)

Each `example` below is stated in the **verbatim field type** of `GQ2.SourceData`
(`GQ2/SourceData.lean:119-123`) specialised at `Γ := GammaR`, so that any future drift between
these declarations and the structure is caught here rather than in R32's `sourceR`.  (The fields
are mutually dependent — `contSMulZmod2`/`htriv` are stated under `letI := smulZmod2` — so the
`letI` is discharged here by the *registered global* instances, which is precisely the
`inferInstance` route `BoundaryMaps.sourceA` takes.) -/

/-- Smoke test for the `SourceData.smulZmod2` field at `Γ := GammaR`. -/
example : DistribMulAction (GammaR : Type) (ZMod 2) := inferInstance

/-- Smoke test for the `SourceData.contSMulZmod2` field at `Γ := GammaR`. -/
example : ContinuousSMul (GammaR : Type) (ZMod 2) := inferInstance

/-- Smoke test for the `SourceData.htriv` field at `Γ := GammaR`. -/
example : ∀ (γ : (GammaR : Type)) (m : ZMod 2), γ • m = m := htriv_gammaR

/-! ## Shared `C = Y/K`-module helpers (used by `hZcount` and `hsep_hom`)

Third copies of the `RStageLocal` pack (`GQ2/RStage/Local.lean:148/162/195`, already cloned once
in `GQ2/RStage/GammaA.lean:75/89/122`): all three are `private` at *both* sites, hence inaccessible
across modules.  The statements and proofs are entirely source-free — the marking word never
enters — so these are verbatim transcriptions, carrying the `R` suffix only to keep the `Γ_R`
namespace readable. -/

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- `R = Φ(K)` is elementary abelian: `Additive R` is 2-torsion. -/
private lemma frattiniK_add_selfR
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1) :
    letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
    ∀ a : Additive ↥Blk.frattiniK, a + a = 0 := by
  letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
  intro a
  refine Additive.toMul.injective (Subtype.ext ?_)
  exact hR2 _ (Additive.toMul a).2

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- A `C = Y/K`-invariant character of `R` takes equal values on `Y`-conjugates: the fixed-point
condition, evaluated through `conjC_smul_of_mk` at `y⁻¹`. -/
private lemma elemDual_fixed_apply_conjR
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r) :
    letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
    letI := RStageLocal.conjC Blk hRK
    ∀ lam : GQ2.FoxH.ElemDual (Additive ↥Blk.frattiniK),
      lam ∈ GQ2.FoxH.fixedPts (Y ⧸ Blk.K) (GQ2.FoxH.ElemDual (Additive ↥Blk.frattiniK)) →
      ∀ (y : Y) (r : ↥Blk.frattiniK),
        lam (Additive.ofMul ⟨y * (r : Y) * y⁻¹, RStageLocal.conj_mem_R y r⟩)
          = lam (Additive.ofMul r) := by
  letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
  letI := RStageLocal.conjC Blk hRK
  intro lam hfix y r
  have hfixy := hfix (QuotientGroup.mk' Blk.K y)
  have h1 := congrArg (fun mu : GQ2.FoxH.ElemDual (Additive ↥Blk.frattiniK) =>
    mu (Additive.ofMul ⟨y * (r : Y) * y⁻¹, RStageLocal.conj_mem_R y r⟩)) hfixy
  have h3 : (QuotientGroup.mk' Blk.K y : Y ⧸ Blk.K)⁻¹
      • Additive.ofMul (⟨y * (r : Y) * y⁻¹, RStageLocal.conj_mem_R y r⟩ : ↥Blk.frattiniK)
      = Additive.ofMul r := by
    rw [← map_inv,
      RStageLocal.conjC_smul_of_mk hRK y⁻¹ ⟨y * (r : Y) * y⁻¹, RStageLocal.conj_mem_R y r⟩]
    refine congrArg _ (Subtype.ext ?_)
    show y⁻¹ * (y * (r : Y) * y⁻¹) * y⁻¹⁻¹ = (r : Y)
    group
  have h2 : ((QuotientGroup.mk' Blk.K y : Y ⧸ Blk.K) • lam)
      (Additive.ofMul ⟨y * (r : Y) * y⁻¹, RStageLocal.conj_mem_R y r⟩)
      = lam (Additive.ofMul r) := by
    rw [GQ2.FoxH.ElemDual.smul_apply, h3]
  rw [h2] at h1
  exact h1.symm

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- The invariant-character bridge `(R^∨)^C ≃ D_Rmod`: `#fixedPts C (R^∨) = #RCharSub`. -/
private lemma card_fixedPts_eq_card_rCharSubR
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r) :
    letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
    letI := RStageLocal.conjC Blk hRK
    Nat.card
      (GQ2.FoxH.fixedPts (Y ⧸ Blk.K) (GQ2.FoxH.ElemDual (Additive ↥Blk.frattiniK)))
      = Nat.card ↥(RCharSub Blk) := by
  letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
  letI := RStageLocal.conjC Blk hRK
  refine Nat.card_congr
    { toFun := fun lam => ⟨lam.1, fun y r => elemDual_fixed_apply_conjR hRK lam.1 lam.2 y r⟩
      invFun := fun chi => ⟨chi.1, fun c => ?_⟩
      left_inv := fun lam => rfl
      right_inv := fun chi => rfl }
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Blk.K c
  refine GQ2.FoxH.ElemDual.ext fun a => ?_
  rw [GQ2.FoxH.ElemDual.smul_apply]
  have h3 : (QuotientGroup.mk' Blk.K y : Y ⧸ Blk.K)⁻¹ • a
      = Additive.ofMul (⟨y⁻¹ * ((Additive.toMul a : ↥Blk.frattiniK) : Y) * y⁻¹⁻¹,
          RStageLocal.conj_mem_R y⁻¹ (Additive.toMul a)⟩ : ↥Blk.frattiniK) := by
    rw [← map_inv]
    exact RStageLocal.conjC_smul_of_mk hRK y⁻¹ (Additive.toMul a)
  rw [h3]
  exact chi.2 y⁻¹ (Additive.toMul a)

/-- The Roe-source torsor count through the **Roe** word bridge: for a boundary lift `f₀`,
`#RCocycle(f₀) = #R² · #((R^∨)^C)` — `RCocycle ≃ Z¹(Γ_R, R_{f₀})` (multiplicative crossed ↔
additive cocycles, verbatim from `Γ_A`), then `z1EquivR` + `prop_5_15_R` clause 2.  The only
`Γ_R`-specific steps are the last two rewrites; everything above them is source-free plumbing. -/
private lemma card_rCocycle_eq_sq_mul_card_fixedPtsR
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (b : ContinuousMonoidHom GammaR ↥boundarySubgroup) (F : BoundaryFrame H E)
    (f₀ : BoundaryLifts b F T) :
    letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
    letI := RStageLocal.conjC Blk hRK
    Nat.card (RCocycle (blockFrameImpl T Blk hE2) f₀.1.1)
      = Nat.card (Additive ↥Blk.frattiniK) ^ 2
        * Nat.card
            (GQ2.FoxH.fixedPts (Y ⧸ Blk.K) (GQ2.FoxH.ElemDual (Additive ↥Blk.frattiniK))) := by
  classical
  letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
  letI actC : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) := RStageLocal.conjC Blk hRK
  -- the lower map through `C = Y/K`, surjective (over `GR`, against which `z1EquivR` is stated)
  set θ : ContinuousMonoidHom GR (Y ⧸ Blk.K) :=
    ⟨(QuotientGroup.mk' Blk.K).comp f₀.1.1.toMonoidHom, by
      show Continuous fun γ => QuotientGroup.mk' Blk.K (f₀.1.1 γ)
      exact Continuous.comp continuous_of_discreteTopology f₀.1.1.continuous_toFun⟩ with hθdef
  have hθs : Function.Surjective ⇑θ := by
    intro c
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective Blk.K c
    obtain ⟨γ, hγ⟩ := f₀.1.2 y
    exact ⟨γ, by show QuotientGroup.mk' Blk.K (f₀.1.1 γ) = c; rw [hγ, hy]⟩
  letI actG : DistribMulAction GR (Additive ↥Blk.frattiniK) :=
    DistribMulAction.compHom _ θ.toMonoidHom
  letI : TopologicalSpace (Additive ↥Blk.frattiniK) :=
    (inferInstance : TopologicalSpace ↥Blk.frattiniK)
  haveI : DiscreteTopology (Additive ↥Blk.frattiniK) :=
    ⟨(inferInstance : DiscreteTopology ↥Blk.frattiniK).eq_bot⟩
  haveI : Finite (Additive ↥Blk.frattiniK) := (inferInstance : Finite ↥Blk.frattiniK)
  haveI : ContinuousSMul GR (Additive ↥Blk.frattiniK) := ⟨by
    show Continuous ((fun q : (Y ⧸ Blk.K) × Additive ↥Blk.frattiniK => q.1 • q.2)
        ∘ (fun p : GR × Additive ↥Blk.frattiniK => (θ p.1, p.2)))
    exact continuous_of_discreteTopology.comp
      ((θ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)⟩
  have hcomp : ∀ (γ : GR) (a : Additive ↥Blk.frattiniK), γ • a = θ γ • a := fun _ _ => rfl
  have hA₂ : ∀ a : Additive ↥Blk.frattiniK, a + a = 0 := frattiniK_add_selfR hRK hR2
  -- the action at the `f₀`-representative (`f₀.1.1 γ` for `γ : GR` reads through `GammaR ≡ GR`)
  have hsmul : ∀ (γ : GR) (a : Additive ↥Blk.frattiniK),
      γ • a
        = Additive.ofMul (⟨f₀.1.1 γ * ((Additive.toMul a : ↥Blk.frattiniK) : Y) * (f₀.1.1 γ)⁻¹,
            RStageLocal.conj_mem_R (f₀.1.1 γ) (Additive.toMul a)⟩ : ↥Blk.frattiniK) := by
    intro γ a
    exact RStageLocal.conjC_smul_of_mk hRK (f₀.1.1 γ) (Additive.toMul a)
  -- the multiplicative↔additive crossed-cocycle bridge `RCocycle ≃ Z¹(Γ_R, R)`
  have hequiv : RCocycle (blockFrameImpl T Blk hE2) f₀.1.1
      ≃ ↥(Z1 GR (Additive ↥Blk.frattiniK)) :=
    { toFun := fun c =>
        ⟨fun γ => Additive.ofMul ⟨c.u γ, c.mem γ⟩, by
          refine mem_Z1_iff.mpr ⟨?_, ?_⟩
          · show Continuous fun γ => (⟨c.u γ, c.mem γ⟩ : ↥Blk.frattiniK)
            exact Continuous.subtype_mk c.cont _
          · intro γ δ
            rw [hsmul γ (Additive.ofMul ⟨c.u δ, c.mem δ⟩)]
            refine Additive.toMul.injective (Subtype.ext ?_)
            show c.u (γ * δ) = c.u γ * (f₀.1.1 γ * c.u δ * (f₀.1.1 γ)⁻¹)
            exact c.crossed γ δ⟩
      invFun := fun z =>
        { u := fun γ => ((Additive.toMul (z.1 γ) : ↥Blk.frattiniK) : Y)
          mem := fun γ => (Additive.toMul (z.1 γ)).2
          cont := by
            have hz := (mem_Z1_iff.mp z.2).1
            exact continuous_subtype_val.comp hz
          crossed := by
            intro γ δ
            have hz := (mem_Z1_iff.mp z.2).2 γ δ
            rw [hsmul γ (z.1 δ)] at hz
            exact congrArg (fun a => ((Additive.toMul a : ↥Blk.frattiniK) : Y)) hz }
      left_inv := fun c => RCocycle.ext rfl
      right_inv := fun z => Subtype.ext (funext fun γ => rfl) }
  rw [Nat.card_congr hequiv]
  -- the count: `#Z¹(Γ_R, R) = #Z1wR(markC_R θ) = #R²·#fixedPts C (R^∨)` (the Roe duality)
  have adm := markC_admissible_R θ hθs
  rw [Nat.card_congr (z1EquivR θ hcomp hθs hA₂).toEquiv,
    (GQ2.FoxH.prop_5_15_R (markC_R θ) adm.2.1 adm.2.2.1 adm.1 hA₂ adm.2.2.2).2.1]

/-! ## `hZcount`: the `z_R` torsor count at the Roe source

The `Γ_R` mirror of `hZcount_gammaA`: `RCocycle ≃ Z¹(Γ_R, R_{f₀})` (identical conjugation-action
setup, reusing `RStageLocal`'s `ConjAction` section), then the count via `z1EquivR` +
`prop_5_15_R` clause 2 (`#Z1wR = #R²·#fixedPts C (R^∨)`), and the same frame-generic
`fixedPts ≃ RCharSub` bridge + `blockRChar_card`. -/
theorem hZcount_gammaR
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (b : ContinuousMonoidHom GammaR ↥boundarySubgroup) (F : BoundaryFrame H E)
    (f₀ : BoundaryLifts b F T) :
    Nat.card (RCocycle (blockFrameImpl T Blk hE2) f₀.1.1)
      = (blockFrameImpl T Blk hE2).zR := by
  classical
  letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
  letI actC : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) := RStageLocal.conjC Blk hRK
  -- the count through the word bridge, then the invariant-character bridge `(R^∨)^C ≃ D_Rmod`
  rw [card_rCocycle_eq_sq_mul_card_fixedPtsR hE2 hRK hR2 b F f₀,
    card_fixedPts_eq_card_rCharSubR hRK, blockRChar_card T Blk hE2,
    Nat.card_congr (Additive.toMul (α := ↥Blk.frattiniK))]
  rfl

/-! ## L3 — the trace-span package: `(R^∨)^C` perfectly pairs `H2wR`

Statement-for-statement port of `RStageGammaA`'s `TraceSpan` section onto the Roe word complex
`H2wR t = (A × A) ⧸ (d1R t).range`.  Only three inputs change: `prop_5_8_right_R` (for
well-definedness), `IsSelfDual_R` clause 1 and `H2w_two_torsion_R` (for the count).  `H0w` and
`H0w_eq_fixedPts` are reused *verbatim* — the Roe `H0wR` is the very same object
(`H0wR_eq_H0w` is `rfl`, `GQ2/Roe/FoxBasic.lean:159`), since `d⁰` never sees the relator. -/

section TraceSpanR

open GQ2.FoxH

variable {C : Type} [Group C] [Finite C]
variable {A : Type} [AddCommGroup A] [Finite A] [DistribMulAction C A]

/-- **The trace functional for the Roe word** `Φ_λ : H2wR(A) →+ 𝔽₂`, `[v] ↦ λ(v.1 + v.2)` —
`Γ_R` twin of `RStageGammaA.wTrace`.  Well-defined on the quotient `H2wR = (A×A) ⧸ im d¹_R`
because for an invariant `λ` (`d⁰λ = 0`), `prop_5_8_right_R` gives
`λ((d¹_R x).1 + (d¹_R x).2) = mixedB_R t x (d⁰λ) = mixedB_R t x 0 = 0`.  This is the
`(2,0)`-pairing that `IsSelfDual_R` omits — supplied by Prop. 5.8 directly. -/
noncomputable def wTrace_R (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (lam : ElemDual A) (hlam : (d0 (A := ElemDual A) t) lam = 0) :
    H2wR (A := A) t →+ ZMod 2 :=
  QuotientAddGroup.lift _ (lam.comp (AddMonoidHom.fst A A + AddMonoidHom.snd A A)) (by
    rintro w ⟨x, rfl⟩
    have h58 := prop_5_8_right_R t ht hw x lam
    rw [hlam, mixedB_R_zero_right] at h58
    exact h58.symm)

@[simp] private theorem wTrace_R_mk (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (lam : ElemDual A) (hlam : (d0 (A := ElemDual A) t) lam = 0) (v : A × A) :
    wTrace_R t ht hw lam hlam (QuotientAddGroup.mk v) = lam (v.1 + v.2) := rfl

/-- **`λ ↦ Φ_λ` is injective** — `Φ_λ` at `[⟨a,0⟩]` is `λ a`, so the functional determines `λ`. -/
theorem wTrace_R_injective (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (lam lam' : ElemDual A) (hlam : (d0 (A := ElemDual A) t) lam = 0)
    (hlam' : (d0 (A := ElemDual A) t) lam' = 0)
    (h : wTrace_R t ht hw lam hlam = wTrace_R t ht hw lam' hlam') : lam = lam' := by
  ext a
  simpa only [wTrace_R_mk, add_zero] using congrArg (fun Ψ => Ψ (QuotientAddGroup.mk (a, 0))) h

/-- **`λ ↦ Φ_λ` is surjective** onto `H2wR →+ 𝔽₂` — the counting half of the perfect
`(2,0)`-pairing.  The invariant characters, `#H2wR`, and `#(H2wR →+ 𝔽₂)` are all equinumerous:
`#{λ : d⁰λ = 0} = #fixedPts C (A^∨) = #H2wR = #(H2wR →+ 𝔽₂)` — by `H0w_eq_fixedPts` (needs
`Generates`; `H0wR` *is* `H0w`), `IsSelfDual_R` clause 1, and `card_addHom_zmod2` at
`H2w_two_torsion_R`.  A finite injection (`wTrace_R_injective`) between equinumerous finite sets
is bijective, hence surjective. -/
theorem wTrace_R_surjective (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR) (hgen : t.Generates)
    (hsd : IsSelfDual_R t A) (hA₂ : ∀ a : A, a + a = 0) (Ψ : H2wR (A := A) t →+ ZMod 2) :
    ∃ (lam : ElemDual A) (hlam : (d0 (A := ElemDual A) t) lam = 0),
      wTrace_R t ht hw lam hlam = Ψ := by
  obtain ⟨hsd_card, -, -⟩ := hsd
  haveI : Finite (H2wR (A := A) t) := inferInstanceAs (Finite ((A × A) ⧸ _))
  haveI : Finite (H2wR (A := A) t →+ ZMod 2) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := H2wR (A := A) t →+ ZMod 2))
  haveI : Fintype ↥(H0w (A := ElemDual A) t) := Fintype.ofFinite _
  haveI : Fintype (H2wR (A := A) t →+ ZMod 2) := Fintype.ofFinite _
  -- `Θ : {invariant λ} → (H2wR →+ 𝔽₂)`, `λ ↦ Φ_λ`.
  let Θ : ↥(H0w (A := ElemDual A) t) → (H2wR (A := A) t →+ ZMod 2) :=
    fun x => wTrace_R t ht hw x.1 (AddMonoidHom.mem_ker.mp x.2)
  have hinj : Function.Injective Θ := fun x y hxy =>
    Subtype.ext (wTrace_R_injective t ht hw x.1 y.1
      (AddMonoidHom.mem_ker.mp x.2) (AddMonoidHom.mem_ker.mp y.2) hxy)
  have hcard : Fintype.card ↥(H0w (A := ElemDual A) t)
      = Fintype.card (H2wR (A := A) t →+ ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      LocalLiftingDuality.card_addHom_zmod2 (H2w_two_torsion_R t hA₂), hsd_card]
    exact Nat.card_congr (Equiv.setCongr (H0w_eq_fixedPts t hgen))
  obtain ⟨x, hx⟩ := ((Fintype.bijective_iff_injective_and_card Θ).mpr ⟨hinj, hcard⟩).2 Ψ
  exact ⟨x.1, AddMonoidHom.mem_ker.mp x.2, hx⟩

/-- **`sep_word_R` — the separation for the Roe word.**  If `v.1 + v.2` is killed by every
invariant character `λ` (`d⁰λ = 0`), then `v ∈ im d¹_R`.  Proof: if `[v] ≠ 0` in `H2wR`, then
`exists_addHom_ne_zero` (finite `𝔽₂`-space) produces a functional `Ψ` with `Ψ [v] ≠ 0`; by
`wTrace_R_surjective`, `Ψ = Φ_λ` for some invariant `λ`, and `Φ_λ [v] = λ(v.1 + v.2) = 0` by
hypothesis — contradiction.  `Γ_R` twin of `RStageGammaA.sep_word`. -/
theorem sep_word_R (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR) (hgen : t.Generates)
    (hsd : IsSelfDual_R t A) (hA₂ : ∀ a : A, a + a = 0) (v : A × A)
    (hv : ∀ lam : ElemDual A, (d0 (A := ElemDual A) t) lam = 0 → lam (v.1 + v.2) = 0) :
    v ∈ (d1R (A := A) t).range := by
  haveI : Finite (H2wR (A := A) t) := inferInstanceAs (Finite ((A × A) ⧸ _))
  rw [← QuotientAddGroup.eq_zero_iff]
  by_contra hne
  obtain ⟨Ψ, hΨ⟩ := LocalLiftingDuality.exists_addHom_ne_zero (H2w_two_torsion_R t hA₂) hne
  obtain ⟨lam, hlam, hΨeq⟩ := wTrace_R_surjective t ht hw hgen hsd hA₂ Ψ
  exact hΨ (by rw [← hΨeq, wTrace_R_mk]; exact hv lam hlam)

end TraceSpanR

end RStageGammaR

end GQ2

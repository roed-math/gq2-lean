/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.GaussZ.GammaAD
import GQ2.GaussZ.KappaR
import GQ2.GaussZ.RelatorGammaR
import GQ2.GaussZ.CoordGammaR
import GQ2.Roe.Gauss
import GQ2.SourceData

/-!
# The `Γ_R` `GaussZResidue` twins at the head-inflated enrichment

The `Γ_R` side of obligation ii.7 (the last supply seam): the two dichotomy twins
`gaussZResidueD_gammaR_{unramified,ramified}` — `GQ2/GaussZ/GammaAD.lean`'s
`gaussZResidueD_gammaA_*` replayed over the Roe candidate `Γ_R`, in the exact
`SourceData.gaussZ_{unramified,ramified}` field shapes (checked by the `example`s at the end
of this file), so R32's `sourceR` binds them exactly as `BoundaryMaps.sourceA` binds the
`Γ_A` twins (`fun T Blk => … (tame := …) …`).

The architecture is the `Γ_A` one stage-for-stage; what changes is word-shaped:

* the boundary interface is the abstract eq. (27) triple `(tame, pro2, compat)` with the
  four tame generator pinnings as hypotheses (at `Γ_A` these are the `BoundaryMaps` fields
  `B.tameA_*`; at `Γ_R` they will be `sourceR`'s fields, backed by `GQ2/Roe/Tame.lean`'s
  `phiR_gamma*` values), and the boundary map is `sourceBoundaryMap tame pro2 compat`;
* the **gauge swap**: `x₁`-supported sections (`x1SecC`/`x1SecClass`, slot 3) in place of
  `x₀`-supported ones (slot 2), through the Roe word bridge (`ofZ1wR`/`h1CoordGammaR`) at
  `markC_R θ`; the stage-6 slot facts read `congrFun (hevalx v) 3` for the value and
  `congrFun (hevalx v) 2` for the killed wild slot;
* the **value side** transports through the `Sd`-level reindexing exactly as for `Γ_A`
  (`sdProjHom`/`kappa0Cocycle_reindexHom` are imported generic; only the 8-line
  `relZPairR_kappa0_reindexHom` retype is new), and the wild peel is the *unconditional*
  Wall-shape evaluation `liftMark_kappa0_wildValueR_fib_ramified`
  (`GQ2/GaussZ/KappaR.lean`) — so **both** twins land stage 6 in the same
  `FoxH.QZeroR (blockQbar …) (powOmega2 (cF tameSigma))` shape (⟦eq:QR⟧), and stage 7 is
  R27's banked `QZeroR_finsum_sign_{unramified,ramified}` (`GQ2/Roe/Gauss.lean`), which
  performs the split collapse `Q_R⁰ = q̄` internally;
* stage-7 finiteness is `finite_vcocycle_gammaR` (σ-free from R31f's
  `Phase140GammaR.hZcard_gammaR`); the freeness `hfix_of_simple_nt` is imported generic.

The un/ramified dichotomy hypothesis is the same head-level `F.alpha tameTau`-action as on
the `Γ_A` side — ρ-free and source-free, so the P4e/`gaussZ_obtain_blockD_of_sources`
`by_cases` serves both sources at the shared external `G0 = ∓2^m`.

Axioms: std-3 throughout (no B-axioms, no sorries).
-/

namespace GQ2

namespace SectionNine

open ContCoh QuadraticFp2 SectionSix SectionSeven SectionEight SectionEight.AffineTLift
open WordCohBridge WordCohBridgeR WordCoh2 WordCoh2R FoxH RStageGammaR CentralObstruction

open scoped Classical

/-! ## The `Sd`-level reindexing transport at the Roe relator pair -/

section SdReindexR

variable {C C' : Type*} [Group C] [Group C']
variable {V : Type*} [AddCommGroup V] [DistribMulAction C V] [DistribMulAction C' V]

/-- **The `Sd`-level Roe relator transport** (the ii.7 value-side seam): the Roe relator
pair of the reindexed `κ⁰` at a marking is the Roe relator pair of the base `κ⁰` at the
`sdProjHom`-mapped marking — `relZPairR_comap` + the generic cocycle identification
`kappa0Cocycle_reindexHom` (imported from `GQ2/GaussZ/GammaAD.lean`). -/
theorem relZPairR_kappa0_reindexHom [Finite C] [Finite C'] [Finite V] {q q' : V → ZMod 2}
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (π : C' →* C) (hπ : ∀ (c' : C') (v : V), c' • v = π c' • v)
    (hdat' : IsEquivariantFactorSet q' (dat.reindexHom ⇑π)) (t : Marking (Sd C' V)) :
    relZPairR t (kappa0Cocycle (dat.reindexHom ⇑π) hdat')
      = relZPairR (t.map (sdProjHom π hπ)) (kappa0Cocycle dat hdat) := by
  rw [relZPairR_comap t (kappa0Cocycle dat hdat) (sdProjHom π hπ)]
  exact congrArg (relZPairR t) (kappa0Cocycle_reindexHom dat hdat π hπ hdat')

end SdReindexR

/-! ## The x₁-supported section classes (stages 4/5/6 of both twins)

The section cocycles `secC v := ofZ1 ∘ ofZ1wR` at the x₁-supported Roe word cocycles, their
classes `ψ v` in the Gauss domain, the `h1CoordGammaR`-coordinate computation, the `evalR`
roundtrip, and bijectivity given the section bijection.  Generic in the enrichment and in
the `Z¹_R`-membership pack (`hmem`), so the un/ramified twins differ only in how they
discharge `hmem`/`hsec` (the split vs ramified shape lemmas).  Instance context as in
`GQ2/GaussZ/CoordGammaR.lean` (the callers' letI-packs supply it). -/

section X1Sections

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : MinimalBlock T.LY} {RF : RecursionFrame T Blk}
variable (b : ContinuousMonoidHom GammaR ↥boundarySubgroup) (F : BoundaryFrame H E)
  (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR) (ρ : BoundaryLifts b F RF.TC)
variable [TopologicalSpace (En.descData l h).Vmod] [DiscreteTopology (En.descData l h).Vmod]
  [DistribMulAction GR (En.descData l h).Vmod] [ContinuousSMul GR (En.descData l h).Vmod]
  [DistribMulAction RF.YC (En.descData l h).Vmod]
  [Finite (En.descData l h).Vmod]
variable (hcomp : ∀ (γ : GR) (v : (En.descData l h).Vmod),
    γ • v = rho0 (En.descData l h) (rhoPrimeGR b F En l h ρ) γ • v)
  (hcompat : ∀ (γ : GR) (v : (En.descData l h).Vmod), γ • v = thetaGR b F ρ γ • v)
  (hA₂ : ∀ v : (En.descData l h).Vmod, v + v = 0)
  (hmem : ∀ v : (En.descData l h).Vmod,
    x1Supported v ∈ Z1wR (A := (En.descData l h).Vmod) (markC_R (thetaGR b F ρ)))

/-- The x₁-supported section cocycle at `v` (stage 4 of the twins). -/
noncomputable def x1SecC (v : (En.descData l h).Vmod) :
    VCocycle (En.descData l h) (rhoPrimeGR b F En l h ρ) :=
  ofZ1 hcomp (ofZ1wR (thetaGR b F ρ) hcompat (thetaGR_surjective b F ρ) hA₂
    ⟨x1Supported v, hmem v⟩)

/-- The class of `x1SecC v` in the Gauss domain `Z¹⧸B¹` (the twins' `ψ`). -/
noncomputable def x1SecClass (v : (En.descData l h).Vmod) :
    VCocycle (En.descData l h) (rhoPrimeGR b F En l h ρ)
      ⧸ vCobRange (En.descData l h) (rhoPrimeGR b F En l h ρ) :=
  QuotientAddGroup.mk (x1SecC b F En l h ρ hcomp hcompat hA₂ hmem v)

omit [TopologicalSpace Y] [DiscreteTopology Y] [ContinuousSMul GR (En.descData l h).Vmod] in
/-- `evalR` recovers the x₁-supported tuple from the section's Roe word cocycle (stage 6's
`hevalx`). -/
theorem evalR_ofZ1wR_x1Supported (v : (En.descData l h).Vmod) :
    evalR (ofZ1wR (thetaGR b F ρ) hcompat (thetaGR_surjective b F ρ) hA₂
      ⟨x1Supported v, hmem v⟩) = x1Supported v := by
  have h2 := congrArg Subtype.val
    (toZ1wRHom_ofZ1wR (thetaGR b F ρ) hcompat (thetaGR_surjective b F ρ) hA₂
      ⟨x1Supported v, hmem v⟩)
  rwa [toZ1wRHom_coe] at h2

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- The `h1CoordGammaR`-coordinate of `x1SecClass v` is the class of the x₁-supported Roe
word cocycle (stage 5's `hcoordψ`). -/
theorem h1CoordGammaR_x1SecClass (v : (En.descData l h).Vmod) :
    h1CoordGammaR b F En l h ρ hcomp hcompat hA₂
        (x1SecClass b F En l h ρ hcomp hcompat hA₂ hmem v)
      = h1wMkR (markC_R (thetaGR b F ρ)) ⟨x1Supported v, hmem v⟩ := by
  show h1wMkR (markC_R (thetaGR b F ρ))
      (toZ1wRHom (thetaGR b F ρ) hcompat
        (toZ1 hcomp (x1SecC b F En l h ρ hcomp hcompat hA₂ hmem v))) = _
  rw [show toZ1 hcomp (x1SecC b F En l h ρ hcomp hcompat hA₂ hmem v)
      = ofZ1wR (thetaGR b F ρ) hcompat (thetaGR_surjective b F ρ) hA₂
          ⟨x1Supported v, hmem v⟩ from toZ1_ofZ1 hcomp _]
  rw [toZ1wRHom_ofZ1wR]

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- Bijectivity of `v ↦ x1SecClass v`, given the section bijection (stage 5's `hψbij`). -/
theorem x1SecClass_bijective
    (hsec : Function.Bijective fun v : (En.descData l h).Vmod =>
      h1wMkR (markC_R (thetaGR b F ρ)) ⟨x1Supported v, hmem v⟩) :
    Function.Bijective (x1SecClass b F En l h ρ hcomp hcompat hA₂ hmem) := by
  constructor
  · intro v v' hvv'
    have h1 := congrArg (h1CoordGammaR b F En l h ρ hcomp hcompat hA₂) hvv'
    rw [h1CoordGammaR_x1SecClass b F En l h ρ hcomp hcompat hA₂ hmem v,
      h1CoordGammaR_x1SecClass b F En l h ρ hcomp hcompat hA₂ hmem v'] at h1
    exact hsec.1 h1
  · intro x
    obtain ⟨v, hv⟩ := hsec.2 (h1CoordGammaR b F En l h ρ hcomp hcompat hA₂ x)
    exact ⟨v, (h1CoordGammaR_bijective b F En l h ρ hcomp hcompat hA₂).1
      ((h1CoordGammaR_x1SecClass b F En l h ρ hcomp hcompat hA₂ hmem v).trans hv)⟩

end X1Sections

/-! ## The twins -/

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable (T : MarkedTarget H E Y) (Blk : MinimalBlock T.LY)
variable [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]

/-! ### The head-slot projections (stage 2/6 of both twins)

`blockProjF ∘ θ = cF ∘ tame` (`boundaryLift_head_gammaR` through `mk' (headActKer)`),
evaluated at the four `Γ_R`-generators: the tame slots project to the fixed
`headTameSurj`-values (through the pinning hypotheses `htσ`/`htτ` — at `sourceR` these are
the structure's `tame_sigma`/`tame_tau` fields), the wild slots to `1` (`htx0`/`htx1`).
Both twins consume these at `markC_R θ` (via `markC_R_map`) and at the mapped `Sd`-marking's
`cc`-slots (via the `rho0`-roundtrip). -/

section HeadSlotsR

variable (hE2 : ∀ e : E, e ^ 2 = 1)
variable (tame : ContinuousMonoidHom GammaR Ttame) (pro2 : ContinuousMonoidHom GammaR PiBd)
  (compat : ∀ g : GammaR, nuT (tame g) = nuTwo (pro2 g))
variable (F : BoundaryFrame H E)
  (ρ : BoundaryLifts (sourceBoundaryMap tame pro2 compat) F (blockFrame T Blk hE2).TC)

omit [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal] in
/-- `Γ_R` version of the boundary equation's head component: `TC.piY ∘ ρ = α ∘ tame`
(rfl-deep — the first component of `IsBoundaryLift` at `sourceBoundaryMap`). -/
theorem boundaryLift_head_gammaR (γ : GammaR) :
    (blockFrame T Blk hE2).TC.piY (ρ.1.1 γ) = F.alpha (tame γ) :=
  congrArg Prod.fst (ρ.2 γ)

omit [Blk.frattiniK.Normal] in
/-- The head factorization of the `Γ_R` boundary lift, through `mk' (headActKer)`. -/
theorem blockProjF_thetaGR (γ : GR) :
    blockProjF T Blk (thetaGR (sourceBoundaryMap tame pro2 compat) F ρ γ)
      = headTameSurj T Blk F (tame γ) :=
  congrArg (⇑(QuotientGroup.mk' (headActKer T Blk)))
    (boundaryLift_head_gammaR T Blk hE2 tame pro2 compat F ρ γ)

omit [Blk.frattiniK.Normal] in
/-- The `σ`-slot projects to the fixed tame `σ`-value. -/
theorem blockProjF_thetaGR_sigma (htσ : tame gammaSigmaR = tameSigma) :
    blockProjF T Blk (thetaGR (sourceBoundaryMap tame pro2 compat) F ρ gammaGenR.σ)
      = headTameSurj T Blk F tameSigma := by
  calc blockProjF T Blk (thetaGR (sourceBoundaryMap tame pro2 compat) F ρ gammaGenR.σ)
      = headTameSurj T Blk F (tame gammaSigmaR) :=
        blockProjF_thetaGR T Blk hE2 tame pro2 compat F ρ _
    _ = headTameSurj T Blk F tameSigma := by rw [htσ]

omit [Blk.frattiniK.Normal] in
/-- The `τ`-slot projects to the fixed tame `τ`-value. -/
theorem blockProjF_thetaGR_tau (htτ : tame gammaTauR = tameTau) :
    blockProjF T Blk (thetaGR (sourceBoundaryMap tame pro2 compat) F ρ gammaGenR.τ)
      = headTameSurj T Blk F tameTau := by
  calc blockProjF T Blk (thetaGR (sourceBoundaryMap tame pro2 compat) F ρ gammaGenR.τ)
      = headTameSurj T Blk F (tame gammaTauR) :=
        blockProjF_thetaGR T Blk hE2 tame pro2 compat F ρ _
    _ = headTameSurj T Blk F tameTau := by rw [htτ]

omit [Blk.frattiniK.Normal] in
/-- The `x₀`-slot projects to `1` (the wild generators die at the tame head). -/
theorem blockProjF_thetaGR_x0 (htx0 : tame gammaX0R = 1) :
    blockProjF T Blk (thetaGR (sourceBoundaryMap tame pro2 compat) F ρ gammaGenR.x₀) = 1 := by
  calc blockProjF T Blk (thetaGR (sourceBoundaryMap tame pro2 compat) F ρ gammaGenR.x₀)
      = headTameSurj T Blk F (tame gammaX0R) :=
        blockProjF_thetaGR T Blk hE2 tame pro2 compat F ρ _
    _ = 1 := by rw [htx0, map_one]

omit [Blk.frattiniK.Normal] in
/-- The `x₁`-slot projects to `1` (the wild generators die at the tame head). -/
theorem blockProjF_thetaGR_x1 (htx1 : tame gammaX1R = 1) :
    blockProjF T Blk (thetaGR (sourceBoundaryMap tame pro2 compat) F ρ gammaGenR.x₁) = 1 := by
  calc blockProjF T Blk (thetaGR (sourceBoundaryMap tame pro2 compat) F ρ gammaGenR.x₁)
      = headTameSurj T Blk F (tame gammaX1R) :=
        blockProjF_thetaGR T Blk hE2 tame pro2 compat F ρ _
    _ = 1 := by rw [htx1, map_one]

omit [Blk.frattiniK.Normal] in
/-- The head projection of the `markC_R θ` `σ`-slot is the fixed tame `σ`-value (stage 2 of
both twins, at `markC_R θ` via `markC_R_map`). -/
theorem blockProjF_markC_R_sigma (htσ : tame gammaSigmaR = tameSigma) :
    blockProjF T Blk ((markC_R (thetaGR (sourceBoundaryMap tame pro2 compat) F ρ)).σ)
      = headTameSurj T Blk F tameSigma := by
  rw [congrArg Marking.σ (markC_R_map (thetaGR (sourceBoundaryMap tame pro2 compat) F ρ))]
  exact blockProjF_thetaGR_sigma T Blk hE2 tame pro2 compat F ρ htσ

omit [Blk.frattiniK.Normal] in
/-- The head projection of the `markC_R θ` `τ`-slot is the fixed tame `τ`-value (stage 2 of
both twins, at `markC_R θ` via `markC_R_map`). -/
theorem blockProjF_markC_R_tau (htτ : tame gammaTauR = tameTau) :
    blockProjF T Blk ((markC_R (thetaGR (sourceBoundaryMap tame pro2 compat) F ρ)).τ)
      = headTameSurj T Blk F tameTau := by
  rw [congrArg Marking.τ (markC_R_map (thetaGR (sourceBoundaryMap tame pro2 compat) F ρ))]
  exact blockProjF_thetaGR_tau T Blk hE2 tame pro2 compat F ρ htτ

omit [Blk.frattiniK.Normal] in
/-- The head projection of the `markC_R θ` `x₀`-slot is `1` (the wild generators die at the
tame head). -/
theorem blockProjF_markC_R_x0 (htx0 : tame gammaX0R = 1) :
    blockProjF T Blk ((markC_R (thetaGR (sourceBoundaryMap tame pro2 compat) F ρ)).x₀)
      = 1 := by
  rw [congrArg Marking.x₀ (markC_R_map (thetaGR (sourceBoundaryMap tame pro2 compat) F ρ))]
  exact blockProjF_thetaGR_x0 T Blk hE2 tame pro2 compat F ρ htx0

omit [Blk.frattiniK.Normal] in
/-- The head projection of the `markC_R θ` `x₁`-slot is `1` (the wild generators die at the
tame head). -/
theorem blockProjF_markC_R_x1 (htx1 : tame gammaX1R = 1) :
    blockProjF T Blk ((markC_R (thetaGR (sourceBoundaryMap tame pro2 compat) F ρ)).x₁)
      = 1 := by
  rw [congrArg Marking.x₁ (markC_R_map (thetaGR (sourceBoundaryMap tame pro2 compat) F ρ))]
  exact blockProjF_thetaGR_x1 T Blk hE2 tame pro2 compat F ρ htx1

end HeadSlotsR

/-- **`hGaussZR` at the head-inflated enrichment, unramified case** (ii.7): for the block
enrichment `blockEnrichmentD`, `GaussZResidue (sourceBoundaryMap tame pro2 compat) F
(blockEnrichmentD …) l h (−2^m)` — the dichotomy hypothesis is the head-level
`F.alpha tameTau`-triviality, uniform in `ρ`, exactly as for `Γ_A`. -/
theorem gaussZResidueD_gammaR_unramified (hE2 : ∀ e : E, e ^ 2 = 1)
    (tame : ContinuousMonoidHom GammaR Ttame) (pro2 : ContinuousMonoidHom GammaR PiBd)
    (compat : ∀ g : GammaR, nuT (tame g) = nuTwo (pro2 g))
    (htσ : tame gammaSigmaR = tameSigma) (htτ : tame gammaTauR = tameTau)
    (htx0 : tame gammaX0R = 1) (htx1 : tame gammaX1R = 1)
    (F : BoundaryFrame H E)
    (hsimple : ∀ W : AddSubgroup (blockEnrichmentD T Blk hE2 F).Vmod,
      (∀ g : (blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : (blockEnrichmentD T Blk hE2 F).Vmod, v ≠ 0)
    (hnt : ∃ (g : (blockFrame T Blk hE2).YC) (v : (blockEnrichmentD T Blk hE2 F).Vmod),
      g • v ≠ v)
    (m : ℕ) (hm : 1 ≤ m)
    (hcard : Nat.card (blockEnrichmentD T Blk hE2 F).Vmod = 2 ^ (2 * m))
    (l : (blockFrame T Blk hE2).DR) (h : l ≠ (blockFrame T Blk hE2).zeroDR)
    (hunram :
      letI := blockPS_commGroup Blk
      letI := headAct T Blk
      ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha tameTau • v = v) :
    GaussZResidue (sourceBoundaryMap tame pro2 compat) F (blockEnrichmentD T Blk hE2 F) l h
      (-(2 ^ m : ℤ)) := by
  classical
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := headAct T Blk
  letI := hvAct T Blk
  letI : TopologicalSpace (HVq T Blk) := ⊥
  haveI : DiscreteTopology (HVq T Blk) := ⟨rfl⟩
  haveI : ContinuousMul (HVq T Blk) := ⟨continuous_of_discreteTopology⟩
  haveI : ContinuousInv (HVq T Blk) := ⟨continuous_of_discreteTopology⟩
  haveI : IsTopologicalGroup (HVq T Blk) := { }
  have hl' : l.1 ≠ Blk.frattiniK := fun heq => h (Subtype.ext heq)
  set bR := sourceBoundaryMap tame pro2 compat with hbRdef
  set EnD := blockEnrichmentD T Blk hE2 F with hEnDdef
  intro ρ
  set ρM := (blockFrame T Blk hE2).rhoPrime bR F (EnD.radData l h) rfl ρ with hρMdef
  -- ===== the fixed tame surjection into the faithful head quotient =====
  set cF : ContinuousMonoidHom Ttame (HVq T Blk) := headTameSurj T Blk F with hcFdef
  have hcF : Function.Surjective ⇑cF := headTameSurj_surjective T Blk F
  -- ===== stage 0: GR-instances and the letI pack =====
  letI : DistribMulAction GR (ZMod 2) :=
    inferInstanceAs (DistribMulAction GammaR (ZMod 2))
  haveI : ContinuousSMul GR (ZMod 2) := inferInstanceAs (ContinuousSMul GammaR (ZMod 2))
  haveI : IsTopologicalGroup GR := inferInstanceAs (IsTopologicalGroup (GammaR : Type))
  letI instT : TopologicalSpace EnD.Vmod := ⊥
  haveI instD : DiscreteTopology EnD.Vmod := ⟨rfl⟩
  letI instA : DistribMulAction GR EnD.Vmod :=
    DistribMulAction.compHom _ (thetaGR bR F ρ).toMonoidHom
  haveI instC : ContinuousSMul GR EnD.Vmod := ⟨by
    show Continuous fun p : GR × EnD.Vmod => (thetaGR bR F ρ) p.1 • p.2
    exact (continuous_of_discreteTopology
      (f := fun s : (blockFrame T Blk hE2).YC × EnD.Vmod => s.1 • s.2)).comp
      (((thetaGR bR F ρ).continuous.comp continuous_fst).prodMk continuous_snd)⟩
  letI : TopologicalSpace (EnD.descData l h).Vmod := instT
  haveI : DiscreteTopology (EnD.descData l h).Vmod := instD
  letI : DistribMulAction GR (EnD.descData l h).Vmod := instA
  haveI : ContinuousSMul GR (EnD.descData l h).Vmod := instC
  haveI : Finite (EnD.descData l h).Vmod := (inferInstance : Finite EnD.Vmod)
  letI : TopologicalSpace (EnD.descData l h).C0 :=
    (inferInstance : TopologicalSpace (blockFrame T Blk hE2).YC)
  haveI : DiscreteTopology (EnD.descData l h).C0 :=
    (inferInstance : DiscreteTopology (blockFrame T Blk hE2).YC)
  haveI : Finite (EnD.descData l h).C0 := (inferInstance : Finite (blockFrame T Blk hE2).YC)
  -- spelling covers: shadow the global quotient-topology at raw `Y ⧸ K`, pin the
  -- `YC`-action on both module spellings to `blockActV`, and key the `HVq`-action
  letI : TopologicalSpace (Y ⧸ Blk.K) :=
    (inferInstance : TopologicalSpace (blockFrame T Blk hE2).YC)
  haveI : DiscreteTopology (Y ⧸ Blk.K) :=
    (inferInstance : DiscreteTopology (blockFrame T Blk hE2).YC)
  haveI : Finite (Y ⧸ Blk.K) := (inferInstance : Finite (blockFrame T Blk hE2).YC)
  letI : DistribMulAction ((blockFrame T Blk hE2).YC)
      (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) := blockActV Blk
  letI : DistribMulAction ((blockFrame T Blk hE2).YC) (EnD.descData l h).Vmod :=
    blockActV Blk
  letI : DistribMulAction (HVq T Blk) EnD.Vmod := hvAct T Blk
  letI : DistribMulAction (HVq T Blk) (EnD.descData l h).Vmod := hvAct T Blk
  -- ===== stage 1: θ-facts and the bridge hypotheses =====
  have hθsurj : Function.Surjective ⇑(thetaGR bR F ρ) := thetaGR_surjective bR F ρ
  have hcompat : ∀ (γ : GR) (v : (EnD.descData l h).Vmod),
      γ • v = thetaGR bR F ρ γ • v := fun _ _ => rfl
  have hround : ∀ γ : GR,
      rho0 (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ) γ = thetaGR bR F ρ γ :=
    roundtripGR bR F EnD l h ρ
  have hcomp : ∀ (γ : GR) (v : (EnD.descData l h).Vmod),
      γ • v = rho0 (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ) γ • v := fun γ v =>
    (congrArg (fun cc : (EnD.descData l h).C0 => cc • v) (hround γ)).symm
  letI : DistribMulAction AbsGalQ2 EnD.Vmod :=
    DistribMulAction.compHom _ (1 : AbsGalQ2 →* (blockFrame T Blk hE2).YC)
  letI : DistribMulAction AbsGalQ2 (EnD.descData l h).Vmod :=
    (inferInstance : DistribMulAction AbsGalQ2 EnD.Vmod)
  haveI : ContinuousSMul AbsGalQ2 EnD.Vmod := ⟨by
    show Continuous fun p : AbsGalQ2 × EnD.Vmod =>
      ((1 : AbsGalQ2 →* (blockFrame T Blk hE2).YC) p.1) • p.2
    simpa only [MonoidHom.one_apply, one_smul] using continuous_snd⟩
  haveI : ContinuousSMul AbsGalQ2 (EnD.descData l h).Vmod :=
    (inferInstance : ContinuousSMul AbsGalQ2 EnD.Vmod)
  have hA₂ : ∀ v : (EnD.descData l h).Vmod, v + v = 0 :=
    DeepPart.exp_two_of_simple_of_card hsimple m hm hcard
  -- ===== stage HV: the head factorization and the `HVq`-level facts =====
  have hpc : ∀ (cc : Y ⧸ Blk.K) (w : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)),
      cc • w = blockProjF T Blk cc • w := fun cc w => blockProjF_compat T Blk cc w
  have hgenHV : Subgroup.closure ({cF tameSigma, cF tameTau} : Set (HVq T Blk)) = ⊤ :=
    SectionThree.gen_ttame_quotient cF.toMonoidHom cF.continuous_toFun hcF
  have hunramF : ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), cF tameTau • v = v :=
    hunram
  have hntHV : ∃ (g : HVq T Blk) (v : (EnD.descData l h).Vmod), g • v ≠ v := by
    obtain ⟨g, v, hgv⟩ := hnt
    exact ⟨blockProjF T Blk g, v, fun heq => hgv ((hpc g v).trans heq)⟩
  have hdvd : 2 ∣ Nat.card (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) := by
    rw [show Nat.card (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) = 2 ^ (2 * m) from hcard]
    exact dvd_pow_self 2 (by omega)
  -- ===== stage 2: the head-slot projections of `markC_R θ` =====
  have hσP : blockProjF T Blk ((markC_R (thetaGR bR F ρ)).σ) = cF tameSigma :=
    blockProjF_markC_R_sigma T Blk hE2 tame pro2 compat F ρ htσ
  have hτP : blockProjF T Blk ((markC_R (thetaGR bR F ρ)).τ) = cF tameTau :=
    blockProjF_markC_R_tau T Blk hE2 tame pro2 compat F ρ htτ
  have hadm := markC_admissible_R (thetaGR bR F ρ) hθsurj
  -- ===== stage 3: the split hypothesis pack at `markC_R θ`, through the head =====
  have hsimpleM : IsSimpleModTwo (blockFrame T Blk hE2).YC (EnD.descData l h).Vmod := by
    constructor
    · obtain ⟨v, hv⟩ := hVne
      exact ⟨v, 0, hv⟩
    · intro W hW
      exact hsimple W fun g w hw => hW g w hw
  have htauM : ∀ v : (EnD.descData l h).Vmod,
      (markC_R (thetaGR bR F ρ)).τ • v = v := fun v => by
    rw [show (markC_R (thetaGR bR F ρ)).τ • v
        = blockProjF T Blk ((markC_R (thetaGR bR F ρ)).τ) • v from hpc _ v, hτP]
    exact hunramF v
  have hVSM : ∀ v : (EnD.descData l h).Vmod,
      (markC_R (thetaGR bR F ρ)).σ • v = v → v = 0 := fun v hv =>
    sigma_fixed_eq_zero_of_gen (cF tameSigma) (cF tameTau) hgenHV hunramF
      (hv_simple T Blk) hntHV v (by
        rwa [show (markC_R (thetaGR bR F ρ)).σ • v
          = blockProjF T Blk ((markC_R (thetaGR bR F ρ)).σ) • v from hpc _ v, hσP] at hv)
  have hmem : ∀ v : (EnD.descData l h).Vmod,
      x1Supported v ∈ Z1wR (A := (EnD.descData l h).Vmod) (markC_R (thetaGR bR F ρ)) :=
    fun v => x1Supported_mem_Z1wR_split (markC_R (thetaGR bR F ρ)) hadm.2.1 hadm.2.2.1 hA₂
      hsimpleM hadm.2.2.2 htauM hVSM v
  have hsec := x1Section_bijective_split_R (markC_R (thetaGR bR F ρ)) hadm.2.1 hadm.2.2.1
    hA₂ hsimpleM hadm.2.2.2 htauM hVSM
  -- ===== stage 4/5: the section classes ψ, their coordinate, and bijectivity =====
  set secC : (EnD.descData l h).Vmod →
      VCocycle (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ) :=
    x1SecC bR F EnD l h ρ hcomp hcompat hA₂ hmem with hsecCdef
  set ψ : (EnD.descData l h).Vmod →
      (VCocycle (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ)
        ⧸ vCobRange (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ)) :=
    x1SecClass bR F EnD l h ρ hcomp hcompat hA₂ hmem with hψdef
  have hcoordψ : ∀ v, h1CoordGammaR bR F EnD l h ρ hcomp hcompat hA₂ (ψ v)
      = h1wMkR (markC_R (thetaGR bR F ρ)) ⟨x1Supported v, hmem v⟩ :=
    h1CoordGammaR_x1SecClass bR F EnD l h ρ hcomp hcompat hA₂ hmem
  have hψbij : Function.Bijective ψ :=
    x1SecClass_bijective bR F EnD l h ρ hcomp hcompat hA₂ hmem hsec
  -- ===== stage 6: the value on section classes is `Q_R⁰` at the head quotient =====
  have hdat : IsEquivariantFactorSet ((EnD.descData l h).qbar) (EnD.descData l h).dat :=
    EnD.hdat l h
  have hevalx : ∀ v : (EnD.descData l h).Vmod,
      evalR (ofZ1wR (thetaGR bR F ρ) hcompat hθsurj hA₂ ⟨x1Supported v, hmem v⟩)
        = x1Supported v :=
    evalR_ofZ1wR_x1Supported bR F EnD l h ρ hcompat hA₂ hmem
  have hval : ∀ v, QZeroBar (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ)
      htriv_gammaR (ψ v)
      = QZeroR (blockQbar T Blk F.alpha F.alpha_surjective l hl')
          (powOmega2 (cF tameSigma)) v := fun v => by
    show QZero (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ) (secC v)
      = QZeroR (blockQbar T Blk F.alpha F.alpha_surjective l hl')
          (powOmega2 (cF tameSigma)) v
    haveI : ContinuousSMul GR (ZMod 2) :=
      inferInstanceAs (ContinuousSMul GammaR (ZMod 2))
    -- slot facts at the `sdProjHom`-mapped marking (v-slots survive; cc-slots are cF-values)
    have hσv' : (((gammaGenR.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).σ).v = 0 := by
      show (secC v).c gammaGenR.σ = 0
      exact congrFun (hevalx v) 0
    have hτv' : (((gammaGenR.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).τ).v = 0 := by
      show (secC v).c gammaGenR.τ = 0
      exact congrFun (hevalx v) 1
    have hx0v' : (((gammaGenR.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).x₀).v = 0 := by
      show (secC v).c gammaGenR.x₀ = 0
      exact congrFun (hevalx v) 2
    have hx1v' : (((gammaGenR.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).x₁).v = v := by
      show (secC v).c gammaGenR.x₁ = v
      exact congrFun (hevalx v) 3
    have hccσ' : (((gammaGenR.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).σ).cc = cF tameSigma := by
      show blockProjF T Blk
        (rho0 (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ) gammaGenR.σ) = cF tameSigma
      rw [hround gammaGenR.σ]
      exact blockProjF_thetaGR_sigma T Blk hE2 tame pro2 compat F ρ htσ
    have hccτ' : (((gammaGenR.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).τ).cc = cF tameTau := by
      show blockProjF T Blk
        (rho0 (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ) gammaGenR.τ) = cF tameTau
      rw [hround gammaGenR.τ]
      exact blockProjF_thetaGR_tau T Blk hE2 tame pro2 compat F ρ htτ
    have hccx0' : (((gammaGenR.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).x₀).cc = 1 := by
      show blockProjF T Blk
        (rho0 (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ) gammaGenR.x₀) = 1
      rw [hround gammaGenR.x₀]
      exact blockProjF_thetaGR_x0 T Blk hE2 tame pro2 compat F ρ htx0
    have hccx1' : (((gammaGenR.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).x₁).cc = 1 := by
      show blockProjF T Blk
        (rho0 (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ) gammaGenR.x₁) = 1
      rw [hround gammaGenR.x₁]
      exact blockProjF_thetaGR_x1 T Blk hE2 tame pro2 compat F ρ htx1
    -- the Roe wild value at the mapped marking is `Q_R⁰(v)` (the unconditional Wall shape)
    have hτoddS : Odd (orderOf (((gammaGenR.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).τ).cc) := by
      rw [hccτ']
      exact LocalKummer.odd_orderOf_tameInertia cF
    have hwild : (liftMark ((gammaGenR.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc))
        (kappa0Cocycle (blockDatHV T Blk F l hl')
          (blockDatHV_spec T Blk F l hl'))).wildValueR.fib
        = QZeroR (blockQbar T Blk F.alpha F.alpha_surjective l hl')
            (powOmega2 (cF tameSigma)) v := by
      rw [liftMark_kappa0_wildValueR_fib_ramified (blockDatHV T Blk F l hl')
        (blockDatHV_spec T Blk F l hl') _ hσv' hτv' hx0v' hccx0' hccx1' hA₂ hτoddS,
        hx1v',
        show Marking.sigma2 (sdBaseMarking ((gammaGenR.map (graphSdHom (secC v))).map
          (sdProjHom (blockProjF T Blk) hpc))) = powOmega2 (cF tameSigma) from
          congrArg powOmega2 hccσ']
      rfl
    -- assemble: keystone → the `Sd`-reindex transport → fst-peel → wild peel
    rw [QZero_eq_relZPair_kappa0_R (fun x m => rfl) hdat (secC v)]
    have htrans : relZPairR (gammaGenR.map (graphSdHom (secC v)))
        (kappa0Cocycle (EnD.descData l h).dat hdat)
        = relZPairR ((gammaGenR.map (graphSdHom (secC v))).map
            (sdProjHom (blockProjF T Blk) hpc))
          (kappa0Cocycle (blockDatHV T Blk F l hl') (blockDatHV_spec T Blk F l hl')) :=
      relZPairR_kappa0_reindexHom (blockDatHV T Blk F l hl') (blockDatHV_spec T Blk F l hl')
        (blockProjF T Blk) hpc hdat (gammaGenR.map (graphSdHom (secC v)))
    rw [htrans, relZPairR_kappa0_fst_eq_zero (blockDatHV T Blk F l hl')
      (blockDatHV_spec T Blk F l hl') _ hσv' hτv', zero_add]
    exact hwild
  -- ===== stage 7: finiteness, freeness, reindex, count (at the `GammaR`-typed `ρM`) =====
  haveI hfinZ : Finite (VCocycle (EnD.descData l h) ρM) :=
    finite_vcocycle_gammaR bR F EnD l h ρ hsimple hVne hnt
  have hsurjρ' : Function.Surjective
      (fun γ : GammaR => rho0 (EnD.descData l h) ρM γ) := fun y => by
    obtain ⟨γ, hγ⟩ := ρ.1.2 y
    exact ⟨γ, (rho0_descData_rhoPrime bR F EnD l h ρ γ).trans hγ⟩
  have hfix : ∀ v : (EnD.descData l h).Vmod,
      (∀ γ : GammaR, rho0 (EnD.descData l h) ρM γ • v = v) → v = 0 :=
    fun v hv => hfix_of_simple_nt hsurjρ' hsimple hnt v hv
  have hUS : ∀ w : (EnD.descData l h).Vmod, powOmega2 (cF tameSigma) • w = w := fun w =>
    powOmega2_smul_eq_of_gen (cF tameSigma) (cF tameTau) hgenHV hunramF
      (hv_simple T Blk) hdvd w
  have hQbar : ∑ᶠ x : VCocycle (EnD.descData l h) ρM
      ⧸ vCobRange (EnD.descData l h) ρM,
      SectionEight.sign (QZeroBar (EnD.descData l h) ρM htriv_gammaR x)
      = -(2 ^ m : ℤ) := by
    show ∑ᶠ x : VCocycle (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ)
        ⧸ vCobRange (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ),
      SectionEight.sign (QZeroBar (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ)
        htriv_gammaR x) = -(2 ^ m : ℤ)
    calc ∑ᶠ x : VCocycle (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ)
        ⧸ vCobRange (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ),
        SectionEight.sign (QZeroBar (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ)
          htriv_gammaR x)
        = ∑ᶠ v : (EnD.descData l h).Vmod,
            SectionEight.sign (QZeroR (blockQbar T Blk F.alpha F.alpha_surjective l hl')
              (powOmega2 (cF tameSigma)) v) := by
          refine (finsum_eq_of_bijective ψ hψbij fun v => ?_).symm
          show SectionEight.sign (QZeroR (blockQbar T Blk F.alpha F.alpha_surjective l hl')
              (powOmega2 (cF tameSigma)) v)
            = SectionEight.sign (QZeroBar (EnD.descData l h)
                (rhoPrimeGR bR F EnD l h ρ) htriv_gammaR (ψ v))
          rw [hval v]
      _ = -(2 ^ m : ℤ) :=
          QZeroR_finsum_sign_unramified cF hcF (hv_simple T Blk) hVne hunramF
            (blockQbar T Blk F.alpha F.alpha_surjective l hl')
            (blockHquad T Blk F.alpha F.alpha_surjective l hl')
            (blockHns T Blk F.alpha F.alpha_surjective l hl')
            (hv_inv T Blk F l hl') hA₂ hUS m hm hcard
  calc ∑ᶠ cc : VCocycle (EnD.descData l h) ρM,
      SectionEight.sign (QZero (EnD.descData l h) ρM cc)
      = (Nat.card EnD.Vmod : ℤ) * ∑ᶠ x, SectionEight.sign
          (QZeroBar (EnD.descData l h) ρM htriv_gammaR x) :=
        gaussZ_reduction htriv_gammaR hfix
    _ = (Nat.card EnD.Vmod : ℤ) * (-(2 ^ m : ℤ)) := by rw [hQbar]

/-- **`hGaussZR` at the head-inflated enrichment, ramified case** (ii.7): inertia moves the
module at the head — `GaussZResidue (sourceBoundaryMap tame pro2 compat) F
(blockEnrichmentD …) l h (+2^m)`. -/
theorem gaussZResidueD_gammaR_ramified (hE2 : ∀ e : E, e ^ 2 = 1)
    (tame : ContinuousMonoidHom GammaR Ttame) (pro2 : ContinuousMonoidHom GammaR PiBd)
    (compat : ∀ g : GammaR, nuT (tame g) = nuTwo (pro2 g))
    (htσ : tame gammaSigmaR = tameSigma) (htτ : tame gammaTauR = tameTau)
    (htx0 : tame gammaX0R = 1) (htx1 : tame gammaX1R = 1)
    (F : BoundaryFrame H E)
    (hsimple : ∀ W : AddSubgroup (blockEnrichmentD T Blk hE2 F).Vmod,
      (∀ g : (blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : (blockEnrichmentD T Blk hE2 F).Vmod, v ≠ 0)
    (hnt : ∃ (g : (blockFrame T Blk hE2).YC) (v : (blockEnrichmentD T Blk hE2 F).Vmod),
      g • v ≠ v)
    (m : ℕ) (hm : 1 ≤ m)
    (hcard : Nat.card (blockEnrichmentD T Blk hE2 F).Vmod = 2 ^ (2 * m))
    (l : (blockFrame T Blk hE2).DR) (h : l ≠ (blockFrame T Blk hE2).zeroDR)
    (hram :
      letI := blockPS_commGroup Blk
      letI := headAct T Blk
      ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha tameTau • v ≠ v) :
    GaussZResidue (sourceBoundaryMap tame pro2 compat) F (blockEnrichmentD T Blk hE2 F) l h
      (2 ^ m : ℤ) := by
  classical
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := headAct T Blk
  letI := hvAct T Blk
  letI : TopologicalSpace (HVq T Blk) := ⊥
  haveI : DiscreteTopology (HVq T Blk) := ⟨rfl⟩
  haveI : ContinuousMul (HVq T Blk) := ⟨continuous_of_discreteTopology⟩
  haveI : ContinuousInv (HVq T Blk) := ⟨continuous_of_discreteTopology⟩
  haveI : IsTopologicalGroup (HVq T Blk) := { }
  have hl' : l.1 ≠ Blk.frattiniK := fun heq => h (Subtype.ext heq)
  set bR := sourceBoundaryMap tame pro2 compat with hbRdef
  set EnD := blockEnrichmentD T Blk hE2 F with hEnDdef
  intro ρ
  set ρM := (blockFrame T Blk hE2).rhoPrime bR F (EnD.radData l h) rfl ρ with hρMdef
  -- ===== the fixed tame surjection into the faithful head quotient =====
  set cF : ContinuousMonoidHom Ttame (HVq T Blk) := headTameSurj T Blk F with hcFdef
  have hcF : Function.Surjective ⇑cF := headTameSurj_surjective T Blk F
  -- ===== stage 0: GR-instances and the letI pack =====
  letI : DistribMulAction GR (ZMod 2) :=
    inferInstanceAs (DistribMulAction GammaR (ZMod 2))
  haveI : ContinuousSMul GR (ZMod 2) := inferInstanceAs (ContinuousSMul GammaR (ZMod 2))
  haveI : IsTopologicalGroup GR := inferInstanceAs (IsTopologicalGroup (GammaR : Type))
  letI instT : TopologicalSpace EnD.Vmod := ⊥
  haveI instD : DiscreteTopology EnD.Vmod := ⟨rfl⟩
  letI instA : DistribMulAction GR EnD.Vmod :=
    DistribMulAction.compHom _ (thetaGR bR F ρ).toMonoidHom
  haveI instC : ContinuousSMul GR EnD.Vmod := ⟨by
    show Continuous fun p : GR × EnD.Vmod => (thetaGR bR F ρ) p.1 • p.2
    exact (continuous_of_discreteTopology
      (f := fun s : (blockFrame T Blk hE2).YC × EnD.Vmod => s.1 • s.2)).comp
      (((thetaGR bR F ρ).continuous.comp continuous_fst).prodMk continuous_snd)⟩
  letI : TopologicalSpace (EnD.descData l h).Vmod := instT
  haveI : DiscreteTopology (EnD.descData l h).Vmod := instD
  letI : DistribMulAction GR (EnD.descData l h).Vmod := instA
  haveI : ContinuousSMul GR (EnD.descData l h).Vmod := instC
  haveI : Finite (EnD.descData l h).Vmod := (inferInstance : Finite EnD.Vmod)
  letI : TopologicalSpace (EnD.descData l h).C0 :=
    (inferInstance : TopologicalSpace (blockFrame T Blk hE2).YC)
  haveI : DiscreteTopology (EnD.descData l h).C0 :=
    (inferInstance : DiscreteTopology (blockFrame T Blk hE2).YC)
  haveI : Finite (EnD.descData l h).C0 := (inferInstance : Finite (blockFrame T Blk hE2).YC)
  letI : TopologicalSpace (Y ⧸ Blk.K) :=
    (inferInstance : TopologicalSpace (blockFrame T Blk hE2).YC)
  haveI : DiscreteTopology (Y ⧸ Blk.K) :=
    (inferInstance : DiscreteTopology (blockFrame T Blk hE2).YC)
  haveI : Finite (Y ⧸ Blk.K) := (inferInstance : Finite (blockFrame T Blk hE2).YC)
  letI : DistribMulAction ((blockFrame T Blk hE2).YC)
      (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) := blockActV Blk
  letI : DistribMulAction ((blockFrame T Blk hE2).YC) (EnD.descData l h).Vmod :=
    blockActV Blk
  letI : DistribMulAction (HVq T Blk) EnD.Vmod := hvAct T Blk
  letI : DistribMulAction (HVq T Blk) (EnD.descData l h).Vmod := hvAct T Blk
  -- ===== stage 1: θ-facts and the bridge hypotheses =====
  have hθsurj : Function.Surjective ⇑(thetaGR bR F ρ) := thetaGR_surjective bR F ρ
  have hcompat : ∀ (γ : GR) (v : (EnD.descData l h).Vmod),
      γ • v = thetaGR bR F ρ γ • v := fun _ _ => rfl
  have hround : ∀ γ : GR,
      rho0 (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ) γ = thetaGR bR F ρ γ :=
    roundtripGR bR F EnD l h ρ
  have hcomp : ∀ (γ : GR) (v : (EnD.descData l h).Vmod),
      γ • v = rho0 (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ) γ • v := fun γ v =>
    (congrArg (fun cc : (EnD.descData l h).C0 => cc • v) (hround γ)).symm
  letI : DistribMulAction AbsGalQ2 EnD.Vmod :=
    DistribMulAction.compHom _ (1 : AbsGalQ2 →* (blockFrame T Blk hE2).YC)
  letI : DistribMulAction AbsGalQ2 (EnD.descData l h).Vmod :=
    (inferInstance : DistribMulAction AbsGalQ2 EnD.Vmod)
  haveI : ContinuousSMul AbsGalQ2 EnD.Vmod := ⟨by
    show Continuous fun p : AbsGalQ2 × EnD.Vmod =>
      ((1 : AbsGalQ2 →* (blockFrame T Blk hE2).YC) p.1) • p.2
    simpa only [MonoidHom.one_apply, one_smul] using continuous_snd⟩
  haveI : ContinuousSMul AbsGalQ2 (EnD.descData l h).Vmod :=
    (inferInstance : ContinuousSMul AbsGalQ2 EnD.Vmod)
  have hA₂ : ∀ v : (EnD.descData l h).Vmod, v + v = 0 :=
    DeepPart.exp_two_of_simple_of_card hsimple m hm hcard
  -- ===== stage HV: the head factorization and the `HVq`-level facts =====
  have hpc : ∀ (cc : Y ⧸ Blk.K) (w : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)),
      cc • w = blockProjF T Blk cc • w := fun cc w => blockProjF_compat T Blk cc w
  have hgenHV : Subgroup.closure ({cF tameSigma, cF tameTau} : Set (HVq T Blk)) = ⊤ :=
    SectionThree.gen_ttame_quotient cF.toMonoidHom cF.continuous_toFun hcF
  have hramF : ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), cF tameTau • v ≠ v := hram
  have hoddHV : Odd (orderOf (cF tameTau)) := LocalKummer.odd_orderOf_tameInertia cF
  have hrelHV : (cF tameSigma)⁻¹ * cF tameTau * cF tameSigma = cF tameTau ^ 2 := by
    have hrel := congrArg (⇑cF) tame_relation
    simpa only [conjP, map_mul, map_inv, map_pow] using hrel
  -- ===== stage 2: the head-slot projections of `markC_R θ` =====
  have hσP : blockProjF T Blk ((markC_R (thetaGR bR F ρ)).σ) = cF tameSigma :=
    blockProjF_markC_R_sigma T Blk hE2 tame pro2 compat F ρ htσ
  have hτP : blockProjF T Blk ((markC_R (thetaGR bR F ρ)).τ) = cF tameTau :=
    blockProjF_markC_R_tau T Blk hE2 tame pro2 compat F ρ htτ
  have hx0P : blockProjF T Blk ((markC_R (thetaGR bR F ρ)).x₀) = 1 :=
    blockProjF_markC_R_x0 T Blk hE2 tame pro2 compat F ρ htx0
  have hx1P : blockProjF T Blk ((markC_R (thetaGR bR F ρ)).x₁) = 1 :=
    blockProjF_markC_R_x1 T Blk hE2 tame pro2 compat F ρ htx1
  have hadm := markC_admissible_R (thetaGR bR F ρ) hθsurj
  -- ===== stage 3: the ramified hypothesis pack at `markC_R θ`, through the head =====
  have hx0M : ∀ v : (EnD.descData l h).Vmod,
      (markC_R (thetaGR bR F ρ)).x₀ • v = v := fun v => by
    rw [show (markC_R (thetaGR bR F ρ)).x₀ • v
        = blockProjF T Blk ((markC_R (thetaGR bR F ρ)).x₀) • v from hpc _ v, hx0P, one_smul]
  have hx1M : ∀ v : (EnD.descData l h).Vmod,
      (markC_R (thetaGR bR F ρ)).x₁ • v = v := fun v => by
    rw [show (markC_R (thetaGR bR F ρ)).x₁ • v
        = blockProjF T Blk ((markC_R (thetaGR bR F ρ)).x₁) • v from hpc _ v, hx1P, one_smul]
  have htauM : ∀ v : (EnD.descData l h).Vmod,
      (markC_R (thetaGR bR F ρ)).τ • v = v → v = 0 := fun v hv =>
    tau_fixed_eq_zero_of_gen (cF tameSigma) (cF tameTau) hgenHV hrelHV hoddHV
      (hv_simple T Blk) hramF v (by
        rwa [show (markC_R (thetaGR bR F ρ)).τ • v
          = blockProjF T Blk ((markC_R (thetaGR bR F ρ)).τ) • v from hpc _ v, hτP] at hv)
  have hToddM : ∀ v : (EnD.descData l h).Vmod,
      powOmega2 (markC_R (thetaGR bR F ρ)).τ • v = v := fun v => by
    rw [show powOmega2 (markC_R (thetaGR bR F ρ)).τ • v
        = blockProjF T Blk (powOmega2 (markC_R (thetaGR bR F ρ)).τ) • v from hpc _ v,
      powOmega2_map (blockProjF T Blk) ((markC_R (thetaGR bR F ρ)).τ), hτP,
      powOmega2_eq_one_of_odd hoddHV, one_smul]
  have hmem : ∀ v : (EnD.descData l h).Vmod,
      x1Supported v ∈ Z1wR (A := (EnD.descData l h).Vmod) (markC_R (thetaGR bR F ρ)) :=
    fun v => x1Supported_mem_Z1wR_ramified (markC_R (thetaGR bR F ρ)) hadm.2.1 hA₂
      hx0M hx1M htauM hToddM v
  have hsec := x1Section_bijective_ramified_R (markC_R (thetaGR bR F ρ)) hadm.2.1
    hadm.2.2.1 hA₂ hx0M hx1M htauM hToddM
  -- ===== stage 4/5: the section classes ψ, their coordinate, and bijectivity =====
  set secC : (EnD.descData l h).Vmod →
      VCocycle (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ) :=
    x1SecC bR F EnD l h ρ hcomp hcompat hA₂ hmem with hsecCdef
  set ψ : (EnD.descData l h).Vmod →
      (VCocycle (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ)
        ⧸ vCobRange (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ)) :=
    x1SecClass bR F EnD l h ρ hcomp hcompat hA₂ hmem with hψdef
  have hcoordψ : ∀ v, h1CoordGammaR bR F EnD l h ρ hcomp hcompat hA₂ (ψ v)
      = h1wMkR (markC_R (thetaGR bR F ρ)) ⟨x1Supported v, hmem v⟩ :=
    h1CoordGammaR_x1SecClass bR F EnD l h ρ hcomp hcompat hA₂ hmem
  have hψbij : Function.Bijective ψ :=
    x1SecClass_bijective bR F EnD l h ρ hcomp hcompat hA₂ hmem hsec
  -- ===== stage 6: the value on section classes is `Q_R⁰` at the head quotient =====
  have hdat : IsEquivariantFactorSet ((EnD.descData l h).qbar) (EnD.descData l h).dat :=
    EnD.hdat l h
  have hevalx : ∀ v : (EnD.descData l h).Vmod,
      evalR (ofZ1wR (thetaGR bR F ρ) hcompat hθsurj hA₂ ⟨x1Supported v, hmem v⟩)
        = x1Supported v :=
    evalR_ofZ1wR_x1Supported bR F EnD l h ρ hcompat hA₂ hmem
  have hval : ∀ v, QZeroBar (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ)
      htriv_gammaR (ψ v)
      = QZeroR (blockQbar T Blk F.alpha F.alpha_surjective l hl')
          (powOmega2 (cF tameSigma)) v := fun v => by
    show QZero (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ) (secC v)
      = QZeroR (blockQbar T Blk F.alpha F.alpha_surjective l hl')
          (powOmega2 (cF tameSigma)) v
    haveI : ContinuousSMul GR (ZMod 2) :=
      inferInstanceAs (ContinuousSMul GammaR (ZMod 2))
    have hσv' : (((gammaGenR.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).σ).v = 0 := by
      show (secC v).c gammaGenR.σ = 0
      exact congrFun (hevalx v) 0
    have hτv' : (((gammaGenR.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).τ).v = 0 := by
      show (secC v).c gammaGenR.τ = 0
      exact congrFun (hevalx v) 1
    have hx0v' : (((gammaGenR.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).x₀).v = 0 := by
      show (secC v).c gammaGenR.x₀ = 0
      exact congrFun (hevalx v) 2
    have hx1v' : (((gammaGenR.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).x₁).v = v := by
      show (secC v).c gammaGenR.x₁ = v
      exact congrFun (hevalx v) 3
    have hccσ' : (((gammaGenR.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).σ).cc = cF tameSigma := by
      show blockProjF T Blk
        (rho0 (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ) gammaGenR.σ) = cF tameSigma
      rw [hround gammaGenR.σ]
      exact blockProjF_thetaGR_sigma T Blk hE2 tame pro2 compat F ρ htσ
    have hccτ' : (((gammaGenR.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).τ).cc = cF tameTau := by
      show blockProjF T Blk
        (rho0 (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ) gammaGenR.τ) = cF tameTau
      rw [hround gammaGenR.τ]
      exact blockProjF_thetaGR_tau T Blk hE2 tame pro2 compat F ρ htτ
    have hccx0' : (((gammaGenR.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).x₀).cc = 1 := by
      show blockProjF T Blk
        (rho0 (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ) gammaGenR.x₀) = 1
      rw [hround gammaGenR.x₀]
      exact blockProjF_thetaGR_x0 T Blk hE2 tame pro2 compat F ρ htx0
    have hccx1' : (((gammaGenR.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).x₁).cc = 1 := by
      show blockProjF T Blk
        (rho0 (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ) gammaGenR.x₁) = 1
      rw [hround gammaGenR.x₁]
      exact blockProjF_thetaGR_x1 T Blk hE2 tame pro2 compat F ρ htx1
    have hτoddS : Odd (orderOf (((gammaGenR.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).τ).cc) := by
      rw [hccτ']
      exact hoddHV
    have hwild : (liftMark ((gammaGenR.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc))
        (kappa0Cocycle (blockDatHV T Blk F l hl')
          (blockDatHV_spec T Blk F l hl'))).wildValueR.fib
        = QZeroR (blockQbar T Blk F.alpha F.alpha_surjective l hl')
            (powOmega2 (cF tameSigma)) v := by
      rw [liftMark_kappa0_wildValueR_fib_ramified (blockDatHV T Blk F l hl')
        (blockDatHV_spec T Blk F l hl') _ hσv' hτv' hx0v' hccx0' hccx1' hA₂ hτoddS,
        hx1v',
        show Marking.sigma2 (sdBaseMarking ((gammaGenR.map (graphSdHom (secC v))).map
          (sdProjHom (blockProjF T Blk) hpc))) = powOmega2 (cF tameSigma) from
          congrArg powOmega2 hccσ']
      rfl
    rw [QZero_eq_relZPair_kappa0_R (fun x m => rfl) hdat (secC v)]
    have htrans : relZPairR (gammaGenR.map (graphSdHom (secC v)))
        (kappa0Cocycle (EnD.descData l h).dat hdat)
        = relZPairR ((gammaGenR.map (graphSdHom (secC v))).map
            (sdProjHom (blockProjF T Blk) hpc))
          (kappa0Cocycle (blockDatHV T Blk F l hl') (blockDatHV_spec T Blk F l hl')) :=
      relZPairR_kappa0_reindexHom (blockDatHV T Blk F l hl') (blockDatHV_spec T Blk F l hl')
        (blockProjF T Blk) hpc hdat (gammaGenR.map (graphSdHom (secC v)))
    rw [htrans, relZPairR_kappa0_fst_eq_zero (blockDatHV T Blk F l hl')
      (blockDatHV_spec T Blk F l hl') _ hσv' hτv', zero_add]
    exact hwild
  -- ===== stage 7: finiteness, freeness, reindex, count (at the `GammaR`-typed `ρM`) =====
  haveI hfinZ : Finite (VCocycle (EnD.descData l h) ρM) :=
    finite_vcocycle_gammaR bR F EnD l h ρ hsimple hVne hnt
  have hsurjρ' : Function.Surjective
      (fun γ : GammaR => rho0 (EnD.descData l h) ρM γ) := fun y => by
    obtain ⟨γ, hγ⟩ := ρ.1.2 y
    exact ⟨γ, (rho0_descData_rhoPrime bR F EnD l h ρ γ).trans hγ⟩
  have hfix : ∀ v : (EnD.descData l h).Vmod,
      (∀ γ : GammaR, rho0 (EnD.descData l h) ρM γ • v = v) → v = 0 :=
    fun v hv => hfix_of_simple_nt hsurjρ' hsimple hnt v hv
  have hQbar : ∑ᶠ x : VCocycle (EnD.descData l h) ρM
      ⧸ vCobRange (EnD.descData l h) ρM,
      SectionEight.sign (QZeroBar (EnD.descData l h) ρM htriv_gammaR x)
      = (2 ^ m : ℤ) := by
    show ∑ᶠ x : VCocycle (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ)
        ⧸ vCobRange (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ),
      SectionEight.sign (QZeroBar (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ)
        htriv_gammaR x) = (2 ^ m : ℤ)
    calc ∑ᶠ x : VCocycle (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ)
        ⧸ vCobRange (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ),
        SectionEight.sign (QZeroBar (EnD.descData l h) (rhoPrimeGR bR F EnD l h ρ)
          htriv_gammaR x)
        = ∑ᶠ v : (EnD.descData l h).Vmod,
            SectionEight.sign (QZeroR (blockQbar T Blk F.alpha F.alpha_surjective l hl')
              (powOmega2 (cF tameSigma)) v) := by
          refine (finsum_eq_of_bijective ψ hψbij fun v => ?_).symm
          show SectionEight.sign (QZeroR (blockQbar T Blk F.alpha F.alpha_surjective l hl')
              (powOmega2 (cF tameSigma)) v)
            = SectionEight.sign (QZeroBar (EnD.descData l h)
                (rhoPrimeGR bR F EnD l h ρ) htriv_gammaR (ψ v))
          rw [hval v]
      _ = (2 ^ m : ℤ) :=
          QZeroR_finsum_sign_ramified cF hcF (hv_simple T Blk) hramF
            (blockQbar T Blk F.alpha F.alpha_surjective l hl')
            (blockHquad T Blk F.alpha F.alpha_surjective l hl')
            (blockHns T Blk F.alpha F.alpha_surjective l hl')
            (hv_inv T Blk F l hl') m hm hcard
  calc ∑ᶠ cc : VCocycle (EnD.descData l h) ρM,
      SectionEight.sign (QZero (EnD.descData l h) ρM cc)
      = (Nat.card EnD.Vmod : ℤ) * ∑ᶠ x, SectionEight.sign
          (QZeroBar (EnD.descData l h) ρM htriv_gammaR x) :=
        gaussZ_reduction htriv_gammaR hfix
    _ = (Nat.card EnD.Vmod : ℤ) * (2 ^ m : ℤ) := by rw [hQbar]

/-! ## Field-shape smoke tests

The two twins in the **exact** `SourceData.gaussZ_{unramified,ramified}` field types
(`GQ2/SourceData.lean`), bound exactly as R32's `sourceR` will bind them — the named-arg
partial application `fun T Blk => … (tame := …)` mirroring `BoundaryMaps.sourceA`'s
`fun T Blk => … (B := B)`.  The `letI := smulZmod2` prefix instantiates at the global
`RStageGammaR` scalar action (which is what `sourceR`'s `smulZmod2` field will be). -/

-- The named hypothesis binders in the two field-shape examples mirror the `SourceData`
-- obligation fields verbatim (interface documentation); the unused-variable linter would
-- flag them, so it is scoped off — the same idiom as `GQ2/SourceData.lean`'s structure.
set_option linter.unusedVariables false in
example (tame : ContinuousMonoidHom GammaR Ttame) (pro2 : ContinuousMonoidHom GammaR PiBd)
    (compat : ∀ g : GammaR, nuT (tame g) = nuTwo (pro2 g))
    (htσ : tame gammaSigmaR = tameSigma) (htτ : tame gammaTauR = tameTau)
    (htx0 : tame gammaX0R = 1) (htx1 : tame gammaX1R = 1) :
    ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
      [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
      (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
      [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
      (hE2 : ∀ e : E, e ^ 2 = 1) (F : BoundaryFrame H E)
      (hsimple : ∀ W : AddSubgroup (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod,
        (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
      (hVne : ∃ v : (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod, v ≠ 0)
      (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
        (v : (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod), g • v ≠ v)
      (m : ℕ) (hm : 1 ≤ m)
      (hcard : Nat.card (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod = 2 ^ (2 * m))
      (l : (SectionNine.blockFrame T Blk hE2).DR)
      (h : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
      (hunram :
        letI := blockPS_commGroup Blk
        letI := SectionNine.headAct T Blk
        ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha tameTau • v = v),
      letI := RStageGammaR.instDistribMulActionGammaR
      GaussZResidue (sourceBoundaryMap tame pro2 compat) F
        (SectionNine.blockEnrichmentD T Blk hE2 F) l h (-(2 ^ m : ℤ)) :=
  fun T Blk => gaussZResidueD_gammaR_unramified T Blk (tame := tame) (pro2 := pro2)
    (compat := compat) (htσ := htσ) (htτ := htτ) (htx0 := htx0) (htx1 := htx1)

set_option linter.unusedVariables false in
example (tame : ContinuousMonoidHom GammaR Ttame) (pro2 : ContinuousMonoidHom GammaR PiBd)
    (compat : ∀ g : GammaR, nuT (tame g) = nuTwo (pro2 g))
    (htσ : tame gammaSigmaR = tameSigma) (htτ : tame gammaTauR = tameTau)
    (htx0 : tame gammaX0R = 1) (htx1 : tame gammaX1R = 1) :
    ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
      [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
      (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
      [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
      (hE2 : ∀ e : E, e ^ 2 = 1) (F : BoundaryFrame H E)
      (hsimple : ∀ W : AddSubgroup (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod,
        (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
      (hVne : ∃ v : (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod, v ≠ 0)
      (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
        (v : (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod), g • v ≠ v)
      (m : ℕ) (hm : 1 ≤ m)
      (hcard : Nat.card (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod = 2 ^ (2 * m))
      (l : (SectionNine.blockFrame T Blk hE2).DR)
      (h : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
      (hram :
        letI := blockPS_commGroup Blk
        letI := SectionNine.headAct T Blk
        ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha tameTau • v ≠ v),
      letI := RStageGammaR.instDistribMulActionGammaR
      GaussZResidue (sourceBoundaryMap tame pro2 compat) F
        (SectionNine.blockEnrichmentD T Blk hE2 F) l h (2 ^ m : ℤ) :=
  fun T Blk => gaussZResidueD_gammaR_ramified T Blk (tame := tame) (pro2 := pro2)
    (compat := compat) (htσ := htσ) (htτ := htτ) (htx0 := htx0) (htx1 := htx1)

end SectionNine

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * Proposition 6.1/⟦prop:quadratic⟧, ⟦eq:QR⟧ — stage 6 lands both twins in the `QZeroR`
    two-term shape via `liftMark_kappa0_wildValueR_fib_ramified`.
  * Corollary 6.2/⟦cor:gauss⟧ — stage 7 is `QZeroR_finsum_sign_{unramified,ramified}`
    (`GQ2/Roe/Gauss.lean`), giving the `∓2^m` residues of
    `gaussZResidueD_gammaR_{unramified,ramified}`.
  * Lemma 4.2/⟦lem:normalforms⟧ — the `x₁`-supported gauge of stages 3–5.
-/

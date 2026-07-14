import GQ2.GaussZ.FinalGammaA
import GQ2.GaussZ.FinalD

/-!
# P-16d6e4aA-P4d — the `Γ_A` `GaussZResidue` twins at the head-inflated enrichment

The P4 reshape's `Γ_A` side (`docs/p16d6e4aA-p4-tame-package.md` §3,
`docs/p16d6e4aA-p4d-handoff.md`): the two `gaussZResidue_gammaA_*` twins of
`GQ2/GaussZFinalGammaA.lean` replayed at `En := blockEnrichmentD` — **without the refuted
per-lift `hpack`**.  For an arbitrary boundary lift `ρ` the tame factorization is recovered at
the faithful head quotient:

* the boundary equation's head component (`boundaryLift_head_gammaA`) identifies
  `blockProjF ∘ θ = cF ∘ B.tameA` with the **fixed** surjection `cF := mk' ∘ F.alpha` —
  tame-factored uniformly in `ρ` (`θ := ρ.1.1 = thetaGA`, rfl-deep);
* the **space side** (A-1/A-4.1: `x0Supported`/`x0Section`/`h1CoordGammaA`) runs at the
  `RF.YC`-marking `markC θ` verbatim; its action-level hypotheses discharge through
  `blockProjF_compat` + the head-slot projections + the banked `…_of_gen` lemmas at `HVq`;
* the **value side** transports through the NEW `Sd`-level reindexing:
  `blockEnrichmentD`'s datum is *definitionally* `(blockDatHV).reindexHom blockProjF`, and
  `relZPair_kappa0_reindexHom` (below: `κ⁰` of the reindexed datum = the
  `sdProjHom`-pullback of `κ⁰` of the datum, then `relZPair_comap`) moves the A-3 keystone's
  relator pair onto the `sdProjHom`-mapped marking over `Sd (HVq) V` — whose wild slots are
  literally `1` and whose tame slots are the `cF`-values;
* the **peels** (A-4.2/4.3c/4.4b) and **counts** (`finsum_sign_{unramified,ramified}_of_action`)
  then run at `C := HVq` with `dat := blockDatHV`, `hdat := blockDatHV_spec`, form
  `blockQbar`, where the generation is `gen_ttame_quotient cF` and inertia-oddness is
  `odd_orderOf_tameInertia cF`.

The un/ramified dichotomy hypothesis is taken at the **head** (`F.alpha tameTau`-action,
`headAct`) — ρ-free and source-free, matching the P4c local twins, so the P4e obtain can
`by_cases` on it once for both sources.

Axioms: the unramified twin is std-3; the ramified twin once inherited a transitive `sorryAx`
from `zeroCount_qDouble_ramified_of_faithful` (through `finsum_sign_ramified_of_action`), but
P3 landed and that count is proved — this file's trace is sorry-free.
-/

namespace GQ2

namespace SectionNine

open ContCoh QuadraticFp2 SectionSix SectionSeven SectionEight SectionEight.AffineTLift
open WordCohBridge WordCoh2 FoxH RStageGammaA CentralObstruction

open scoped Classical

/-! ## The `Sd`-level reindexing transport (the one new ingredient) -/

section SdReindex

variable {C C' : Type*} [Group C] [Group C']
variable {V : Type*} [AddCommGroup V] [DistribMulAction C V] [DistribMulAction C' V]

/-- Two `ZMod 2`-valued 2-cocycles with the same underlying cochain are equal (the `norm` and
`cocyc` fields are proofs). -/
private theorem twoCocycle_ext {L : Type*} [Group L] {c₁ c₂ : TwoCocycle L}
    (h : c₁.κ = c₂.κ) : c₁ = c₂ := by
  cases c₁
  cases c₂
  cases h
  rfl

/-- The `Sd`-level projection `V ⋊ C' →* V ⋊ C` along `π : C' →* C` (identity on `V`) — a
homomorphism exactly because the `C'`-action on `V` is the `π`-pullback of the `C`-action. -/
noncomputable def sdProjHom (π : C' →* C)
    (hπ : ∀ (c' : C') (v : V), c' • v = π c' • v) : Sd C' V →* Sd C V where
  toFun p := Sd.mk p.v (π p.cc)
  map_one' := by
    refine Sd.ext ?_ ?_
    · rfl
    · exact map_one π
  map_mul' p r := by
    refine Sd.ext ?_ ?_
    · show p.v + p.cc • r.v = p.v + π p.cc • r.v
      rw [hπ]
    · exact map_mul π _ _


/-- **`κ⁰` of the reindexed datum is the `sdProjHom`-pullback of `κ⁰` of the datum**: `f`
sees only `V`-arguments and `m` pre-composes with `π` — the `graphPullback_reindexHom`
computation at the cocycle level. -/
theorem kappa0Cocycle_reindexHom {q q' : V → ZMod 2}
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (π : C' →* C) (hπ : ∀ (c' : C') (v : V), c' • v = π c' • v)
    (hdat' : IsEquivariantFactorSet q' (dat.reindexHom ⇑π)) :
    kappa0Cocycle (dat.reindexHom ⇑π) hdat'
      = (kappa0Cocycle dat hdat).comap (sdProjHom π hπ) := by
  refine twoCocycle_ext (funext fun p => funext fun r => ?_)
  show dat.f p.v (p.cc • r.v) + dat.m (π p.cc) r.v
    = dat.f p.v (π p.cc • r.v) + dat.m (π p.cc) r.v
  rw [hπ]

/-- **The `Sd`-level relator transport** (the P4d value-side seam): the relator pair of the
reindexed `κ⁰` at a marking is the relator pair of the base `κ⁰` at the `sdProjHom`-mapped
marking (`relZPair_comap` + the cocycle identification above). -/
theorem relZPair_kappa0_reindexHom [Finite C] [Finite C'] [Finite V] {q q' : V → ZMod 2}
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (π : C' →* C) (hπ : ∀ (c' : C') (v : V), c' • v = π c' • v)
    (hdat' : IsEquivariantFactorSet q' (dat.reindexHom ⇑π)) (t : Marking (Sd C' V)) :
    relZPair t (kappa0Cocycle (dat.reindexHom ⇑π) hdat')
      = relZPair (t.map (sdProjHom π hπ)) (kappa0Cocycle dat hdat) := by
  rw [relZPair_comap t (kappa0Cocycle dat hdat) (sdProjHom π hπ)]
  exact congrArg (relZPair t) (kappa0Cocycle_reindexHom dat hdat π hπ hdat')

end SdReindex

/-! ## The x₀-supported section classes (stages 4/5/6 of both twins)

The section cocycles `secC v := ofZ1 ∘ ofZ1w` at the x₀-supported word cocycles, their
classes `ψ v` in the Gauss domain, the `h1CoordGammaA`-coordinate computation, the `eval`
roundtrip, and bijectivity given the A-4.1 section bijection.  Generic in the enrichment and
in the `Z¹_w`-membership pack (`hmem`), so the un/ramified twins differ only in how they
discharge `hmem`/`hsec` (the split vs ramified shape lemmas).  Instance context as in
`GQ2/GaussZ/CoordGammaA.lean` (the callers' letI-packs supply it). -/

section X0Sections

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : MinimalBlock T.LY} {RF : RecursionFrame T Blk}
variable (b : ContinuousMonoidHom GammaA ↥boundarySubgroup) (F : BoundaryFrame H E)
  (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR) (ρ : BoundaryLifts b F RF.TC)
variable [TopologicalSpace (En.descData l h).Vmod] [DiscreteTopology (En.descData l h).Vmod]
  [DistribMulAction GA (En.descData l h).Vmod] [ContinuousSMul GA (En.descData l h).Vmod]
  [DistribMulAction RF.YC (En.descData l h).Vmod]
  [Finite (En.descData l h).Vmod]
variable (hcomp : ∀ (γ : GA) (v : (En.descData l h).Vmod),
    γ • v = rho0 (En.descData l h) (rhoPrimeGA b F En l h ρ) γ • v)
  (hcompat : ∀ (γ : GA) (v : (En.descData l h).Vmod), γ • v = thetaGA b F ρ γ • v)
  (hA₂ : ∀ v : (En.descData l h).Vmod, v + v = 0)
  (hmem : ∀ v : (En.descData l h).Vmod,
    x0Supported v ∈ Z1w (A := (En.descData l h).Vmod) (markC (thetaGA b F ρ)))

/-- The x₀-supported section cocycle at `v` (stage 4 of the twins). -/
noncomputable def x0SecC (v : (En.descData l h).Vmod) :
    VCocycle (En.descData l h) (rhoPrimeGA b F En l h ρ) :=
  ofZ1 hcomp (ofZ1w (thetaGA b F ρ) hcompat (thetaGA_surjective b F ρ) hA₂
    ⟨x0Supported v, hmem v⟩)

/-- The class of `x0SecC v` in the Gauss domain `Z¹⧸B¹` (the twins' `ψ`). -/
noncomputable def x0SecClass (v : (En.descData l h).Vmod) :
    VCocycle (En.descData l h) (rhoPrimeGA b F En l h ρ)
      ⧸ vCobRange (En.descData l h) (rhoPrimeGA b F En l h ρ) :=
  QuotientAddGroup.mk (x0SecC b F En l h ρ hcomp hcompat hA₂ hmem v)

omit [TopologicalSpace Y] [DiscreteTopology Y] [ContinuousSMul GA (En.descData l h).Vmod] in
/-- `eval` recovers the x₀-supported tuple from the section's word cocycle (stage 6's
`hevalx`). -/
theorem eval_ofZ1w_x0Supported (v : (En.descData l h).Vmod) :
    eval (ofZ1w (thetaGA b F ρ) hcompat (thetaGA_surjective b F ρ) hA₂
      ⟨x0Supported v, hmem v⟩) = x0Supported v := by
  have h2 := congrArg Subtype.val
    (toZ1wHom_ofZ1w (thetaGA b F ρ) hcompat (thetaGA_surjective b F ρ) hA₂
      ⟨x0Supported v, hmem v⟩)
  rwa [toZ1wHom_coe] at h2

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- The `h1CoordGammaA`-coordinate of `x0SecClass v` is the class of the x₀-supported word
cocycle (stage 5's `hcoordψ`). -/
theorem h1CoordGammaA_x0SecClass (v : (En.descData l h).Vmod) :
    h1CoordGammaA b F En l h ρ hcomp hcompat hA₂
        (x0SecClass b F En l h ρ hcomp hcompat hA₂ hmem v)
      = h1wMk (markC (thetaGA b F ρ)) ⟨x0Supported v, hmem v⟩ := by
  show h1wMk (markC (thetaGA b F ρ))
      (toZ1wHom (thetaGA b F ρ) hcompat
        (toZ1 hcomp (x0SecC b F En l h ρ hcomp hcompat hA₂ hmem v))) = _
  rw [show toZ1 hcomp (x0SecC b F En l h ρ hcomp hcompat hA₂ hmem v)
      = ofZ1w (thetaGA b F ρ) hcompat (thetaGA_surjective b F ρ) hA₂
          ⟨x0Supported v, hmem v⟩ from toZ1_ofZ1 hcomp _]
  rw [toZ1wHom_ofZ1w]

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- Bijectivity of `v ↦ x0SecClass v`, given the A-4.1 section bijection (stage 5's
`hψbij`). -/
theorem x0SecClass_bijective
    (hsec : Function.Bijective fun v : (En.descData l h).Vmod =>
      h1wMk (markC (thetaGA b F ρ)) ⟨x0Supported v, hmem v⟩) :
    Function.Bijective (x0SecClass b F En l h ρ hcomp hcompat hA₂ hmem) := by
  constructor
  · intro v v' hvv'
    have h1 := congrArg (h1CoordGammaA b F En l h ρ hcomp hcompat hA₂) hvv'
    rw [h1CoordGammaA_x0SecClass b F En l h ρ hcomp hcompat hA₂ hmem v,
      h1CoordGammaA_x0SecClass b F En l h ρ hcomp hcompat hA₂ hmem v'] at h1
    exact hsec.1 h1
  · intro x
    obtain ⟨v, hv⟩ := hsec.2 (h1CoordGammaA b F En l h ρ hcomp hcompat hA₂ x)
    exact ⟨v, (h1CoordGammaA_bijective b F En l h ρ hcomp hcompat hA₂).1
      ((h1CoordGammaA_x0SecClass b F En l h ρ hcomp hcompat hA₂ hmem v).trans hv)⟩

end X0Sections

/-! ## The twins -/

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable (T : MarkedTarget H E Y) (Blk : MinimalBlock T.LY)
variable [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]

/-! ### The head-slot projections (stage 2/6 of both twins)

`blockProjF ∘ θ = cF ∘ B.tameA` (`boundaryLift_head_gammaA` through `mk' (headActKer)`),
evaluated at the four `Γ_A`-generators: the tame slots project to the fixed
`headTameSurj`-values, the wild slots to `1`.  Both twins consume these at `markC θ` (via
`markC_map`) and at the mapped `Sd`-marking's `cc`-slots (via the `rho0`-roundtrip). -/

section HeadSlots

variable (hE2 : ∀ e : E, e ^ 2 = 1) (B : BoundaryMaps) (F : BoundaryFrame H E)
  (ρ : BoundaryLifts B.bA F (blockFrame T Blk hE2).TC)

omit [Blk.frattiniK.Normal] in
/-- The head factorization of the `Γ_A` boundary lift, through `mk' (headActKer)`. -/
theorem blockProjF_thetaGA (γ : GA) :
    blockProjF T Blk (thetaGA B.bA F ρ γ) = headTameSurj T Blk F (B.tameA γ) :=
  congrArg (⇑(QuotientGroup.mk' (headActKer T Blk)))
    (boundaryLift_head_gammaA T Blk hE2 B F ρ γ)

omit [Blk.frattiniK.Normal] in
/-- The `σ`-slot projects to the fixed tame `σ`-value. -/
theorem blockProjF_thetaGA_sigma :
    blockProjF T Blk (thetaGA B.bA F ρ gammaGen.σ) = headTameSurj T Blk F tameSigma := by
  calc blockProjF T Blk (thetaGA B.bA F ρ gammaGen.σ)
      = headTameSurj T Blk F (B.tameA (quotientMk NA univMarking.σ)) :=
        blockProjF_thetaGA T Blk hE2 B F ρ _
    _ = headTameSurj T Blk F tameSigma := by rw [B.tameA_sigma]

omit [Blk.frattiniK.Normal] in
/-- The `τ`-slot projects to the fixed tame `τ`-value. -/
theorem blockProjF_thetaGA_tau :
    blockProjF T Blk (thetaGA B.bA F ρ gammaGen.τ) = headTameSurj T Blk F tameTau := by
  calc blockProjF T Blk (thetaGA B.bA F ρ gammaGen.τ)
      = headTameSurj T Blk F (B.tameA (quotientMk NA univMarking.τ)) :=
        blockProjF_thetaGA T Blk hE2 B F ρ _
    _ = headTameSurj T Blk F tameTau := by rw [B.tameA_tau]

omit [Blk.frattiniK.Normal] in
/-- The `x₀`-slot projects to `1` (the wild generators die at the tame head). -/
theorem blockProjF_thetaGA_x0 :
    blockProjF T Blk (thetaGA B.bA F ρ gammaGen.x₀) = 1 := by
  calc blockProjF T Blk (thetaGA B.bA F ρ gammaGen.x₀)
      = headTameSurj T Blk F (B.tameA (quotientMk NA univMarking.x₀)) :=
        blockProjF_thetaGA T Blk hE2 B F ρ _
    _ = 1 := by rw [B.tameA_x0, map_one]

omit [Blk.frattiniK.Normal] in
/-- The `x₁`-slot projects to `1` (the wild generators die at the tame head). -/
theorem blockProjF_thetaGA_x1 :
    blockProjF T Blk (thetaGA B.bA F ρ gammaGen.x₁) = 1 := by
  calc blockProjF T Blk (thetaGA B.bA F ρ gammaGen.x₁)
      = headTameSurj T Blk F (B.tameA (quotientMk NA univMarking.x₁)) :=
        blockProjF_thetaGA T Blk hE2 B F ρ _
    _ = 1 := by rw [B.tameA_x1, map_one]

omit [Blk.frattiniK.Normal] in
/-- The head projection of the `markC θ` `σ`-slot is the fixed tame `σ`-value (stage 2 of both
twins, at `markC θ` via `markC_map`). -/
theorem blockProjF_markC_sigma :
    blockProjF T Blk ((markC (thetaGA B.bA F ρ)).σ) = headTameSurj T Blk F tameSigma := by
  rw [congrArg Marking.σ (markC_map (thetaGA B.bA F ρ))]
  exact blockProjF_thetaGA_sigma T Blk hE2 B F ρ

omit [Blk.frattiniK.Normal] in
/-- The head projection of the `markC θ` `τ`-slot is the fixed tame `τ`-value (stage 2 of both
twins, at `markC θ` via `markC_map`). -/
theorem blockProjF_markC_tau :
    blockProjF T Blk ((markC (thetaGA B.bA F ρ)).τ) = headTameSurj T Blk F tameTau := by
  rw [congrArg Marking.τ (markC_map (thetaGA B.bA F ρ))]
  exact blockProjF_thetaGA_tau T Blk hE2 B F ρ

omit [Blk.frattiniK.Normal] in
/-- The head projection of the `markC θ` `x₀`-slot is `1` (the wild generators die at the tame
head; the ramified twin's stage 2). -/
theorem blockProjF_markC_x0 :
    blockProjF T Blk ((markC (thetaGA B.bA F ρ)).x₀) = 1 := by
  rw [congrArg Marking.x₀ (markC_map (thetaGA B.bA F ρ))]
  exact blockProjF_thetaGA_x0 T Blk hE2 B F ρ

omit [Blk.frattiniK.Normal] in
/-- The head projection of the `markC θ` `x₁`-slot is `1` (the wild generators die at the tame
head; the ramified twin's stage 2). -/
theorem blockProjF_markC_x1 :
    blockProjF T Blk ((markC (thetaGA B.bA F ρ)).x₁) = 1 := by
  rw [congrArg Marking.x₁ (markC_map (thetaGA B.bA F ρ))]
  exact blockProjF_thetaGA_x1 T Blk hE2 B F ρ

end HeadSlots

/-- **`hGaussZA` at the head-inflated enrichment, unramified case** (P4d): for the block
enrichment `blockEnrichmentD`, `GaussZResidue B.bA F (blockEnrichmentD …) l h (−2^m)` with
**no per-lift tame package** — the dichotomy hypothesis is the head-level
`F.alpha tameTau`-triviality, uniform in `ρ`. -/
theorem gaussZResidueD_gammaA_unramified (hE2 : ∀ e : E, e ^ 2 = 1) (B : BoundaryMaps)
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
    GaussZResidue B.bA F (blockEnrichmentD T Blk hE2 F) l h (-(2 ^ m : ℤ)) := by
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
  set EnD := blockEnrichmentD T Blk hE2 F with hEnDdef
  intro ρ
  set ρM := (blockFrame T Blk hE2).rhoPrime B.bA F (EnD.radData l h) rfl ρ with hρMdef
  -- ===== the fixed tame surjection into the faithful head quotient =====
  set cF : ContinuousMonoidHom Ttame (HVq T Blk) := headTameSurj T Blk F with hcFdef
  have hcF : Function.Surjective ⇑cF := headTameSurj_surjective T Blk F
  -- ===== stage 0: GA-instances and the letI pack =====
  letI : DistribMulAction GA (ZMod 2) :=
    inferInstanceAs (DistribMulAction GammaA (ZMod 2))
  haveI : ContinuousSMul GA (ZMod 2) := inferInstanceAs (ContinuousSMul GammaA (ZMod 2))
  haveI : IsTopologicalGroup GA := inferInstanceAs (IsTopologicalGroup (GammaA : Type))
  letI instT : TopologicalSpace EnD.Vmod := ⊥
  haveI instD : DiscreteTopology EnD.Vmod := ⟨rfl⟩
  letI instA : DistribMulAction GA EnD.Vmod :=
    DistribMulAction.compHom _ (thetaGA B.bA F ρ).toMonoidHom
  haveI instC : ContinuousSMul GA EnD.Vmod := ⟨by
    show Continuous fun p : GA × EnD.Vmod => (thetaGA B.bA F ρ) p.1 • p.2
    exact (continuous_of_discreteTopology
      (f := fun s : (blockFrame T Blk hE2).YC × EnD.Vmod => s.1 • s.2)).comp
      (((thetaGA B.bA F ρ).continuous.comp continuous_fst).prodMk continuous_snd)⟩
  letI : TopologicalSpace (EnD.descData l h).Vmod := instT
  haveI : DiscreteTopology (EnD.descData l h).Vmod := instD
  letI : DistribMulAction GA (EnD.descData l h).Vmod := instA
  haveI : ContinuousSMul GA (EnD.descData l h).Vmod := instC
  haveI : Finite (EnD.descData l h).Vmod := (inferInstance : Finite EnD.Vmod)
  letI : TopologicalSpace (EnD.descData l h).C0 :=
    (inferInstance : TopologicalSpace (blockFrame T Blk hE2).YC)
  haveI : DiscreteTopology (EnD.descData l h).C0 :=
    (inferInstance : DiscreteTopology (blockFrame T Blk hE2).YC)
  haveI : Finite (EnD.descData l h).C0 := (inferInstance : Finite (blockFrame T Blk hE2).YC)
  -- spelling covers (the P4c pack): shadow the global quotient-topology at raw `Y ⧸ K`,
  -- pin the `YC`-action on both module spellings to `blockActV`, and key the `HVq`-action
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
  have hθsurj : Function.Surjective ⇑(thetaGA B.bA F ρ) := thetaGA_surjective B.bA F ρ
  have hcompat : ∀ (γ : GA) (v : (EnD.descData l h).Vmod),
      γ • v = thetaGA B.bA F ρ γ • v := fun _ _ => rfl
  have hround : ∀ γ : GA,
      rho0 (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ) γ = thetaGA B.bA F ρ γ :=
    roundtripGA B.bA F EnD l h ρ
  have hcomp : ∀ (γ : GA) (v : (EnD.descData l h).Vmod),
      γ • v = rho0 (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ) γ • v := fun γ v =>
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
  -- ===== stage 2: the head-slot projections of `markC θ` =====
  have hσP : blockProjF T Blk ((markC (thetaGA B.bA F ρ)).σ) = cF tameSigma :=
    blockProjF_markC_sigma T Blk hE2 B F ρ
  have hτP : blockProjF T Blk ((markC (thetaGA B.bA F ρ)).τ) = cF tameTau :=
    blockProjF_markC_tau T Blk hE2 B F ρ
  have hadm := markC_admissible (thetaGA B.bA F ρ) hθsurj
  -- ===== stage 3: the split hypothesis pack at `markC θ`, through the head =====
  have hsimpleM : IsSimpleModTwo (blockFrame T Blk hE2).YC (EnD.descData l h).Vmod := by
    constructor
    · obtain ⟨v, hv⟩ := hVne
      exact ⟨v, 0, hv⟩
    · intro W hW
      exact hsimple W fun g w hw => hW g w hw
  have htauM : ∀ v : (EnD.descData l h).Vmod,
      (markC (thetaGA B.bA F ρ)).τ • v = v := fun v => by
    rw [show (markC (thetaGA B.bA F ρ)).τ • v
        = blockProjF T Blk ((markC (thetaGA B.bA F ρ)).τ) • v from hpc _ v, hτP]
    exact hunramF v
  have hUM : ∀ v : (EnD.descData l h).Vmod,
      (markC (thetaGA B.bA F ρ)).sigma2 • v = v := fun v => by
    show powOmega2 ((markC (thetaGA B.bA F ρ)).σ) • v = v
    rw [show powOmega2 ((markC (thetaGA B.bA F ρ)).σ) • v
        = blockProjF T Blk (powOmega2 ((markC (thetaGA B.bA F ρ)).σ)) • v from hpc _ v,
      powOmega2_map (blockProjF T Blk) ((markC (thetaGA B.bA F ρ)).σ), hσP]
    exact powOmega2_smul_eq_of_gen (cF tameSigma) (cF tameTau) hgenHV hunramF
      (hv_simple T Blk) hdvd v
  have hVSM : ∀ v : (EnD.descData l h).Vmod,
      (markC (thetaGA B.bA F ρ)).σ • v = v → v = 0 := fun v hv =>
    sigma_fixed_eq_zero_of_gen (cF tameSigma) (cF tameTau) hgenHV hunramF
      (hv_simple T Blk) hntHV v (by
        rwa [show (markC (thetaGA B.bA F ρ)).σ • v
          = blockProjF T Blk ((markC (thetaGA B.bA F ρ)).σ) • v from hpc _ v, hσP] at hv)
  have hmem : ∀ v : (EnD.descData l h).Vmod,
      x0Supported v ∈ Z1w (A := (EnD.descData l h).Vmod) (markC (thetaGA B.bA F ρ)) :=
    fun v => x0Supported_mem_Z1w_split (markC (thetaGA B.bA F ρ)) hadm.2.1 hadm.2.2.1 hA₂
      hsimpleM hadm.2.2.2 htauM hUM hVSM v
  have hsec := x0Section_bijective_split (markC (thetaGA B.bA F ρ)) hadm.2.1 hadm.2.2.1 hA₂
    hsimpleM hadm.2.2.2 htauM hUM hVSM
  -- ===== stage 4/5: the section classes ψ, their coordinate, and bijectivity =====
  set secC : (EnD.descData l h).Vmod →
      VCocycle (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ) :=
    x0SecC B.bA F EnD l h ρ hcomp hcompat hA₂ hmem with hsecCdef
  set ψ : (EnD.descData l h).Vmod →
      (VCocycle (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ)
        ⧸ vCobRange (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ)) :=
    x0SecClass B.bA F EnD l h ρ hcomp hcompat hA₂ hmem with hψdef
  have hcoordψ : ∀ v, h1CoordGammaA B.bA F EnD l h ρ hcomp hcompat hA₂ (ψ v)
      = h1wMk (markC (thetaGA B.bA F ρ)) ⟨x0Supported v, hmem v⟩ :=
    h1CoordGammaA_x0SecClass B.bA F EnD l h ρ hcomp hcompat hA₂ hmem
  have hψbij : Function.Bijective ψ :=
    x0SecClass_bijective B.bA F EnD l h ρ hcomp hcompat hA₂ hmem hsec
  -- ===== stage 6: the value on section classes is `q̄` at the head quotient =====
  have hdat : IsEquivariantFactorSet ((EnD.descData l h).qbar) (EnD.descData l h).dat :=
    EnD.hdat l h
  have hevalx : ∀ v : (EnD.descData l h).Vmod,
      eval (ofZ1w (thetaGA B.bA F ρ) hcompat hθsurj hA₂ ⟨x0Supported v, hmem v⟩)
        = x0Supported v :=
    eval_ofZ1w_x0Supported B.bA F EnD l h ρ hcompat hA₂ hmem
  have hval : ∀ v, QZeroBar (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ)
      htriv_gammaA (ψ v) = blockQbar T Blk F.alpha F.alpha_surjective l hl' v := fun v => by
    show QZero (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ) (secC v)
      = blockQbar T Blk F.alpha F.alpha_surjective l hl' v
    haveI : ContinuousSMul GA (ZMod 2) :=
      inferInstanceAs (ContinuousSMul GammaA (ZMod 2))
    -- slot facts at the `sdProjHom`-mapped marking (v-slots survive; cc-slots are cF-values)
    have hσv' : (((gammaGen.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).σ).v = 0 := by
      show (secC v).c gammaGen.σ = 0
      exact congrFun (hevalx v) 0
    have hτv' : (((gammaGen.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).τ).v = 0 := by
      show (secC v).c gammaGen.τ = 0
      exact congrFun (hevalx v) 1
    have hx1v' : (((gammaGen.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).x₁).v = 0 := by
      show (secC v).c gammaGen.x₁ = 0
      exact congrFun (hevalx v) 3
    have hx0v' : (((gammaGen.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).x₀).v = v := by
      show (secC v).c gammaGen.x₀ = v
      exact congrFun (hevalx v) 2
    have hccσ' : (((gammaGen.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).σ).cc = cF tameSigma := by
      show blockProjF T Blk
        (rho0 (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ) gammaGen.σ) = cF tameSigma
      rw [hround gammaGen.σ]
      exact blockProjF_thetaGA_sigma T Blk hE2 B F ρ
    have hccτ' : (((gammaGen.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).τ).cc = cF tameTau := by
      show blockProjF T Blk
        (rho0 (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ) gammaGen.τ) = cF tameTau
      rw [hround gammaGen.τ]
      exact blockProjF_thetaGA_tau T Blk hE2 B F ρ
    have hccx0' : (((gammaGen.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).x₀).cc = 1 := by
      show blockProjF T Blk
        (rho0 (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ) gammaGen.x₀) = 1
      rw [hround gammaGen.x₀]
      exact blockProjF_thetaGA_x0 T Blk hE2 B F ρ
    have hccx1' : (((gammaGen.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).x₁).cc = 1 := by
      show blockProjF T Blk
        (rho0 (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ) gammaGen.x₁) = 1
      rw [hround gammaGen.x₁]
      exact blockProjF_thetaGA_x1 T Blk hE2 B F ρ
    -- the wild value at the mapped marking is `q̄(v)` (the A-4.3c peel at `C := HVq`)
    have hwild : (liftMark ((gammaGen.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc))
        (kappa0Cocycle (blockDatHV T Blk F l hl') (blockDatHV_spec T Blk F l hl'))).wildValue.fib
        = blockQbar T Blk F.alpha F.alpha_surjective l hl' v := by
      have htauS : ∀ w : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P),
          (((gammaGen.map (graphSdHom (secC v))).map
            (sdProjHom (blockProjF T Blk) hpc)).τ).cc • w = w := fun w => by
        rw [hccτ']
        exact hunramF w
      have hτoddS : Odd (orderOf (((gammaGen.map (graphSdHom (secC v))).map
          (sdProjHom (blockProjF T Blk) hpc)).τ).cc) := by
        rw [hccτ']
        exact LocalKummer.odd_orderOf_tameInertia cF
      have hUS : ∀ w : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P),
          Marking.sigma2 (sdBaseMarking ((gammaGen.map (graphSdHom (secC v))).map
            (sdProjHom (blockProjF T Blk) hpc))) • w = w := fun w => by
        show powOmega2 (((gammaGen.map (graphSdHom (secC v))).map
          (sdProjHom (blockProjF T Blk) hpc)).σ).cc • w = w
        rw [hccσ']
        exact powOmega2_smul_eq_of_gen (cF tameSigma) (cF tameTau) hgenHV hunramF
          (hv_simple T Blk) hdvd w
      rw [liftMark_kappa0_wildValue_fib_split (blockDatHV T Blk F l hl')
        (blockDatHV_spec T Blk F l hl') _ hσv' hτv' hx1v' hccx0' hccx1' hA₂ htauS hUS hτoddS,
        hx0v']
    -- assemble: keystone → the `Sd`-reindex transport → fst-peel → wild peel
    rw [QZero_eq_relZPair_kappa0 (fun x m => rfl) hdat (secC v)]
    have htrans : relZPair (gammaGen.map (graphSdHom (secC v)))
        (kappa0Cocycle (EnD.descData l h).dat hdat)
        = relZPair ((gammaGen.map (graphSdHom (secC v))).map
            (sdProjHom (blockProjF T Blk) hpc))
          (kappa0Cocycle (blockDatHV T Blk F l hl') (blockDatHV_spec T Blk F l hl')) :=
      relZPair_kappa0_reindexHom (blockDatHV T Blk F l hl') (blockDatHV_spec T Blk F l hl')
        (blockProjF T Blk) hpc hdat (gammaGen.map (graphSdHom (secC v)))
    rw [htrans, relZPair_kappa0_fst_eq_zero (blockDatHV T Blk F l hl')
      (blockDatHV_spec T Blk F l hl') _ hσv' hτv', zero_add]
    exact hwild
  -- ===== stage 7: finiteness, freeness, reindex, count (at the `GammaA`-typed `ρM`) =====
  haveI hfinZ : Finite (VCocycle (EnD.descData l h) ρM) :=
    finite_vcocycle_gammaA B.bA F EnD l h ρ hsimple hVne hnt
  have hsurjρ' : Function.Surjective
      (fun γ : GammaA => rho0 (EnD.descData l h) ρM γ) := fun y => by
    obtain ⟨γ, hγ⟩ := ρ.1.2 y
    exact ⟨γ, (rho0_descData_rhoPrime B.bA F EnD l h ρ γ).trans hγ⟩
  have hfix : ∀ v : (EnD.descData l h).Vmod,
      (∀ γ : GammaA, rho0 (EnD.descData l h) ρM γ • v = v) → v = 0 :=
    fun v hv => hfix_of_simple_nt hsurjρ' hsimple hnt v hv
  have hQbar : ∑ᶠ x : VCocycle (EnD.descData l h) ρM
      ⧸ vCobRange (EnD.descData l h) ρM,
      SectionEight.sign (QZeroBar (EnD.descData l h) ρM htriv_gammaA x)
      = -(2 ^ m : ℤ) := by
    show ∑ᶠ x : VCocycle (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ)
        ⧸ vCobRange (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ),
      SectionEight.sign (QZeroBar (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ)
        htriv_gammaA x) = -(2 ^ m : ℤ)
    calc ∑ᶠ x : VCocycle (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ)
        ⧸ vCobRange (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ),
        SectionEight.sign (QZeroBar (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ)
          htriv_gammaA x)
        = ∑ᶠ v : (EnD.descData l h).Vmod,
            SectionEight.sign (blockQbar T Blk F.alpha F.alpha_surjective l hl' v) := by
          refine (finsum_eq_of_bijective ψ hψbij fun v => ?_).symm
          show SectionEight.sign (blockQbar T Blk F.alpha F.alpha_surjective l hl' v)
            = SectionEight.sign (QZeroBar (EnD.descData l h)
                (rhoPrimeGA B.bA F EnD l h ρ) htriv_gammaA (ψ v))
          rw [hval v]
      _ = -(2 ^ m : ℤ) :=
          finsum_sign_unramified_of_action cF hcF (hv_simple T Blk) hVne hunramF
            (blockQbar T Blk F.alpha F.alpha_surjective l hl')
            (blockHquad T Blk F.alpha F.alpha_surjective l hl')
            (blockHns T Blk F.alpha F.alpha_surjective l hl')
            (hv_inv T Blk F l hl') m hm hcard
  calc ∑ᶠ cc : VCocycle (EnD.descData l h) ρM,
      SectionEight.sign (QZero (EnD.descData l h) ρM cc)
      = (Nat.card EnD.Vmod : ℤ) * ∑ᶠ x, SectionEight.sign
          (QZeroBar (EnD.descData l h) ρM htriv_gammaA x) :=
        gaussZ_reduction htriv_gammaA hfix
    _ = (Nat.card EnD.Vmod : ℤ) * (-(2 ^ m : ℤ)) := by rw [hQbar]

/-- **`hGaussZA` at the head-inflated enrichment, ramified case** (P4d): inertia moves the
module at the head — `GaussZResidue B.bA F (blockEnrichmentD …) l h (+2^m)`, no per-lift
package. -/
theorem gaussZResidueD_gammaA_ramified (hE2 : ∀ e : E, e ^ 2 = 1) (B : BoundaryMaps)
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
    GaussZResidue B.bA F (blockEnrichmentD T Blk hE2 F) l h (2 ^ m : ℤ) := by
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
  set EnD := blockEnrichmentD T Blk hE2 F with hEnDdef
  intro ρ
  set ρM := (blockFrame T Blk hE2).rhoPrime B.bA F (EnD.radData l h) rfl ρ with hρMdef
  -- ===== the fixed tame surjection into the faithful head quotient =====
  set cF : ContinuousMonoidHom Ttame (HVq T Blk) := headTameSurj T Blk F with hcFdef
  have hcF : Function.Surjective ⇑cF := headTameSurj_surjective T Blk F
  -- ===== stage 0: GA-instances and the letI pack =====
  letI : DistribMulAction GA (ZMod 2) :=
    inferInstanceAs (DistribMulAction GammaA (ZMod 2))
  haveI : ContinuousSMul GA (ZMod 2) := inferInstanceAs (ContinuousSMul GammaA (ZMod 2))
  haveI : IsTopologicalGroup GA := inferInstanceAs (IsTopologicalGroup (GammaA : Type))
  letI instT : TopologicalSpace EnD.Vmod := ⊥
  haveI instD : DiscreteTopology EnD.Vmod := ⟨rfl⟩
  letI instA : DistribMulAction GA EnD.Vmod :=
    DistribMulAction.compHom _ (thetaGA B.bA F ρ).toMonoidHom
  haveI instC : ContinuousSMul GA EnD.Vmod := ⟨by
    show Continuous fun p : GA × EnD.Vmod => (thetaGA B.bA F ρ) p.1 • p.2
    exact (continuous_of_discreteTopology
      (f := fun s : (blockFrame T Blk hE2).YC × EnD.Vmod => s.1 • s.2)).comp
      (((thetaGA B.bA F ρ).continuous.comp continuous_fst).prodMk continuous_snd)⟩
  letI : TopologicalSpace (EnD.descData l h).Vmod := instT
  haveI : DiscreteTopology (EnD.descData l h).Vmod := instD
  letI : DistribMulAction GA (EnD.descData l h).Vmod := instA
  haveI : ContinuousSMul GA (EnD.descData l h).Vmod := instC
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
  have hθsurj : Function.Surjective ⇑(thetaGA B.bA F ρ) := thetaGA_surjective B.bA F ρ
  have hcompat : ∀ (γ : GA) (v : (EnD.descData l h).Vmod),
      γ • v = thetaGA B.bA F ρ γ • v := fun _ _ => rfl
  have hround : ∀ γ : GA,
      rho0 (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ) γ = thetaGA B.bA F ρ γ :=
    roundtripGA B.bA F EnD l h ρ
  have hcomp : ∀ (γ : GA) (v : (EnD.descData l h).Vmod),
      γ • v = rho0 (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ) γ • v := fun γ v =>
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
  -- ===== stage 2: the head-slot projections of `markC θ` =====
  have hσP : blockProjF T Blk ((markC (thetaGA B.bA F ρ)).σ) = cF tameSigma :=
    blockProjF_markC_sigma T Blk hE2 B F ρ
  have hτP : blockProjF T Blk ((markC (thetaGA B.bA F ρ)).τ) = cF tameTau :=
    blockProjF_markC_tau T Blk hE2 B F ρ
  have hx0P : blockProjF T Blk ((markC (thetaGA B.bA F ρ)).x₀) = 1 :=
    blockProjF_markC_x0 T Blk hE2 B F ρ
  have hx1P : blockProjF T Blk ((markC (thetaGA B.bA F ρ)).x₁) = 1 :=
    blockProjF_markC_x1 T Blk hE2 B F ρ
  have hadm := markC_admissible (thetaGA B.bA F ρ) hθsurj
  -- ===== stage 3: the ramified hypothesis pack at `markC θ`, through the head =====
  have hx0M : ∀ v : (EnD.descData l h).Vmod,
      (markC (thetaGA B.bA F ρ)).x₀ • v = v := fun v => by
    rw [show (markC (thetaGA B.bA F ρ)).x₀ • v
        = blockProjF T Blk ((markC (thetaGA B.bA F ρ)).x₀) • v from hpc _ v, hx0P, one_smul]
  have hx1M : ∀ v : (EnD.descData l h).Vmod,
      (markC (thetaGA B.bA F ρ)).x₁ • v = v := fun v => by
    rw [show (markC (thetaGA B.bA F ρ)).x₁ • v
        = blockProjF T Blk ((markC (thetaGA B.bA F ρ)).x₁) • v from hpc _ v, hx1P, one_smul]
  have htauM : ∀ v : (EnD.descData l h).Vmod,
      (markC (thetaGA B.bA F ρ)).τ • v = v → v = 0 := fun v hv =>
    tau_fixed_eq_zero_of_gen (cF tameSigma) (cF tameTau) hgenHV hrelHV hoddHV
      (hv_simple T Blk) hramF v (by
        rwa [show (markC (thetaGA B.bA F ρ)).τ • v
          = blockProjF T Blk ((markC (thetaGA B.bA F ρ)).τ) • v from hpc _ v, hτP] at hv)
  have hToddM : ∀ v : (EnD.descData l h).Vmod,
      powOmega2 (markC (thetaGA B.bA F ρ)).τ • v = v := fun v => by
    rw [show powOmega2 (markC (thetaGA B.bA F ρ)).τ • v
        = blockProjF T Blk (powOmega2 (markC (thetaGA B.bA F ρ)).τ) • v from hpc _ v,
      powOmega2_map (blockProjF T Blk) ((markC (thetaGA B.bA F ρ)).τ), hτP,
      powOmega2_eq_one_of_odd hoddHV, one_smul]
  have hmem : ∀ v : (EnD.descData l h).Vmod,
      x0Supported v ∈ Z1w (A := (EnD.descData l h).Vmod) (markC (thetaGA B.bA F ρ)) :=
    fun v => FoxH.x0Supported_mem_Z1w_ramified (markC (thetaGA B.bA F ρ)) hadm.2.1 hA₂
      hx0M hx1M htauM hToddM v
  have hsec := x0Section_bijective_ramified (markC (thetaGA B.bA F ρ)) hadm.2.1 hadm.2.2.1
    hA₂ hx0M hx1M htauM hToddM
  -- ===== stage 4/5: the section classes ψ, their coordinate, and bijectivity =====
  set secC : (EnD.descData l h).Vmod →
      VCocycle (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ) :=
    x0SecC B.bA F EnD l h ρ hcomp hcompat hA₂ hmem with hsecCdef
  set ψ : (EnD.descData l h).Vmod →
      (VCocycle (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ)
        ⧸ vCobRange (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ)) :=
    x0SecClass B.bA F EnD l h ρ hcomp hcompat hA₂ hmem with hψdef
  have hcoordψ : ∀ v, h1CoordGammaA B.bA F EnD l h ρ hcomp hcompat hA₂ (ψ v)
      = h1wMk (markC (thetaGA B.bA F ρ)) ⟨x0Supported v, hmem v⟩ :=
    h1CoordGammaA_x0SecClass B.bA F EnD l h ρ hcomp hcompat hA₂ hmem
  have hψbij : Function.Bijective ψ :=
    x0SecClass_bijective B.bA F EnD l h ρ hcomp hcompat hA₂ hmem hsec
  -- ===== stage 6: the value on section classes is the Wall double at the head quotient =====
  have hdat : IsEquivariantFactorSet ((EnD.descData l h).qbar) (EnD.descData l h).dat :=
    EnD.hdat l h
  have hevalx : ∀ v : (EnD.descData l h).Vmod,
      eval (ofZ1w (thetaGA B.bA F ρ) hcompat hθsurj hA₂ ⟨x0Supported v, hmem v⟩)
        = x0Supported v :=
    eval_ofZ1w_x0Supported B.bA F EnD l h ρ hcompat hA₂ hmem
  have hval : ∀ v, QZeroBar (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ)
      htriv_gammaA (ψ v)
      = qDouble (blockQbar T Blk F.alpha F.alpha_surjective l hl')
          (powOmega2 (cF tameSigma) • ·) v := fun v => by
    show QZero (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ) (secC v)
      = qDouble (blockQbar T Blk F.alpha F.alpha_surjective l hl')
          (powOmega2 (cF tameSigma) • ·) v
    haveI : ContinuousSMul GA (ZMod 2) :=
      inferInstanceAs (ContinuousSMul GammaA (ZMod 2))
    have hσv' : (((gammaGen.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).σ).v = 0 := by
      show (secC v).c gammaGen.σ = 0
      exact congrFun (hevalx v) 0
    have hτv' : (((gammaGen.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).τ).v = 0 := by
      show (secC v).c gammaGen.τ = 0
      exact congrFun (hevalx v) 1
    have hx1v' : (((gammaGen.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).x₁).v = 0 := by
      show (secC v).c gammaGen.x₁ = 0
      exact congrFun (hevalx v) 3
    have hx0v' : (((gammaGen.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).x₀).v = v := by
      show (secC v).c gammaGen.x₀ = v
      exact congrFun (hevalx v) 2
    have hccσ' : (((gammaGen.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).σ).cc = cF tameSigma := by
      show blockProjF T Blk
        (rho0 (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ) gammaGen.σ) = cF tameSigma
      rw [hround gammaGen.σ]
      exact blockProjF_thetaGA_sigma T Blk hE2 B F ρ
    have hccτ' : (((gammaGen.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).τ).cc = cF tameTau := by
      show blockProjF T Blk
        (rho0 (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ) gammaGen.τ) = cF tameTau
      rw [hround gammaGen.τ]
      exact blockProjF_thetaGA_tau T Blk hE2 B F ρ
    have hccx0' : (((gammaGen.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).x₀).cc = 1 := by
      show blockProjF T Blk
        (rho0 (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ) gammaGen.x₀) = 1
      rw [hround gammaGen.x₀]
      exact blockProjF_thetaGA_x0 T Blk hE2 B F ρ
    have hccx1' : (((gammaGen.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc)).x₁).cc = 1 := by
      show blockProjF T Blk
        (rho0 (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ) gammaGen.x₁) = 1
      rw [hround gammaGen.x₁]
      exact blockProjF_thetaGA_x1 T Blk hE2 B F ρ
    -- the wild value at the mapped marking is the Wall double (the A-4.4b peel at `HVq`)
    have hwild : (liftMark ((gammaGen.map (graphSdHom (secC v))).map
        (sdProjHom (blockProjF T Blk) hpc))
        (kappa0Cocycle (blockDatHV T Blk F l hl')
          (blockDatHV_spec T Blk F l hl'))).wildValue.fib
        = blockQbar T Blk F.alpha F.alpha_surjective l hl' v
          + polar (blockQbar T Blk F.alpha F.alpha_surjective l hl') v
              (powOmega2 (cF tameSigma) • v) := by
      have htaufS : ∀ w : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P),
          (((gammaGen.map (graphSdHom (secC v))).map
            (sdProjHom (blockProjF T Blk) hpc)).τ).cc • w = w → w = 0 := fun w hw =>
        tau_fixed_eq_zero_of_gen (cF tameSigma) (cF tameTau) hgenHV hrelHV hoddHV
          (hv_simple T Blk) hramF w (by rwa [hccτ'] at hw)
      have hτoddS : Odd (orderOf (((gammaGen.map (graphSdHom (secC v))).map
          (sdProjHom (blockProjF T Blk) hpc)).τ).cc) := by
        rw [hccτ']
        exact hoddHV
      have hqg0S : blockQbar T Blk F.alpha F.alpha_surjective l hl'
          ((Marking.g0 (sdBaseMarking ((gammaGen.map (graphSdHom (secC v))).map
            (sdProjHom (blockProjF T Blk) hpc))))⁻¹
            • (((gammaGen.map (graphSdHom (secC v))).map
              (sdProjHom (blockProjF T Blk) hpc)).x₀).v)
          = blockQbar T Blk F.alpha F.alpha_surjective l hl'
              ((((gammaGen.map (graphSdHom (secC v))).map
                (sdProjHom (blockProjF T Blk) hpc)).x₀).v) :=
        hv_inv T Blk F l hl' _ _
      rw [liftMark_kappa0_wildValue_fib_ramified (blockDatHV T Blk F l hl')
        (blockDatHV_spec T Blk F l hl') _ hσv' hτv' hx1v' hccx0' hccx1' hA₂ htaufS hτoddS
        hqg0S, hx0v',
        show Marking.sigma2 (sdBaseMarking ((gammaGen.map (graphSdHom (secC v))).map
          (sdProjHom (blockProjF T Blk) hpc))) = powOmega2 (cF tameSigma) from
          congrArg powOmega2 hccσ']
      exact congrArg
        (fun z => blockQbar T Blk F.alpha F.alpha_surjective l hl' v + z)
        (polar_smul_inv_eq (C := HVq T Blk)
          (blockQbar T Blk F.alpha F.alpha_surjective l hl') (powOmega2 (cF tameSigma))
          (fun w => hv_inv T Blk F l hl' _ w) v)
    -- assemble: keystone → the `Sd`-reindex transport → fst-peel → wild peel
    rw [QZero_eq_relZPair_kappa0 (fun x m => rfl) hdat (secC v)]
    have htrans : relZPair (gammaGen.map (graphSdHom (secC v)))
        (kappa0Cocycle (EnD.descData l h).dat hdat)
        = relZPair ((gammaGen.map (graphSdHom (secC v))).map
            (sdProjHom (blockProjF T Blk) hpc))
          (kappa0Cocycle (blockDatHV T Blk F l hl') (blockDatHV_spec T Blk F l hl')) :=
      relZPair_kappa0_reindexHom (blockDatHV T Blk F l hl') (blockDatHV_spec T Blk F l hl')
        (blockProjF T Blk) hpc hdat (gammaGen.map (graphSdHom (secC v)))
    rw [htrans, relZPair_kappa0_fst_eq_zero (blockDatHV T Blk F l hl')
      (blockDatHV_spec T Blk F l hl') _ hσv' hτv', zero_add]
    exact hwild
  -- ===== stage 7: finiteness, freeness, reindex, count (at the `GammaA`-typed `ρM`) =====
  haveI hfinZ : Finite (VCocycle (EnD.descData l h) ρM) :=
    finite_vcocycle_gammaA B.bA F EnD l h ρ hsimple hVne hnt
  have hsurjρ' : Function.Surjective
      (fun γ : GammaA => rho0 (EnD.descData l h) ρM γ) := fun y => by
    obtain ⟨γ, hγ⟩ := ρ.1.2 y
    exact ⟨γ, (rho0_descData_rhoPrime B.bA F EnD l h ρ γ).trans hγ⟩
  have hfix : ∀ v : (EnD.descData l h).Vmod,
      (∀ γ : GammaA, rho0 (EnD.descData l h) ρM γ • v = v) → v = 0 :=
    fun v hv => hfix_of_simple_nt hsurjρ' hsimple hnt v hv
  have hQbar : ∑ᶠ x : VCocycle (EnD.descData l h) ρM
      ⧸ vCobRange (EnD.descData l h) ρM,
      SectionEight.sign (QZeroBar (EnD.descData l h) ρM htriv_gammaA x)
      = (2 ^ m : ℤ) := by
    show ∑ᶠ x : VCocycle (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ)
        ⧸ vCobRange (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ),
      SectionEight.sign (QZeroBar (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ)
        htriv_gammaA x) = (2 ^ m : ℤ)
    calc ∑ᶠ x : VCocycle (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ)
        ⧸ vCobRange (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ),
        SectionEight.sign (QZeroBar (EnD.descData l h) (rhoPrimeGA B.bA F EnD l h ρ)
          htriv_gammaA x)
        = ∑ᶠ v : (EnD.descData l h).Vmod,
            SectionEight.sign (qDouble (blockQbar T Blk F.alpha F.alpha_surjective l hl')
              (powOmega2 (cF tameSigma) • ·) v) := by
          refine (finsum_eq_of_bijective ψ hψbij fun v => ?_).symm
          show SectionEight.sign (qDouble (blockQbar T Blk F.alpha F.alpha_surjective l hl')
              (powOmega2 (cF tameSigma) • ·) v)
            = SectionEight.sign (QZeroBar (EnD.descData l h)
                (rhoPrimeGA B.bA F EnD l h ρ) htriv_gammaA (ψ v))
          rw [hval v]
      _ = (2 ^ m : ℤ) :=
          finsum_sign_ramified_of_action cF hcF (hv_simple T Blk) hramF
            (blockQbar T Blk F.alpha F.alpha_surjective l hl')
            (blockHquad T Blk F.alpha F.alpha_surjective l hl')
            (blockHns T Blk F.alpha F.alpha_surjective l hl')
            (hv_inv T Blk F l hl') m hm hcard
  calc ∑ᶠ cc : VCocycle (EnD.descData l h) ρM,
      SectionEight.sign (QZero (EnD.descData l h) ρM cc)
      = (Nat.card EnD.Vmod : ℤ) * ∑ᶠ x, SectionEight.sign
          (QZeroBar (EnD.descData l h) ρM htriv_gammaA x) :=
        gaussZ_reduction htriv_gammaA hfix
    _ = (Nat.card EnD.Vmod : ℤ) * (2 ^ m : ℤ) := by rw [hQbar]

/-! ## P4e: the hypothesis-free G0-obtain at the head-inflated enrichment

The `⟨G0, hGaussZA, hGaussZF⟩`-obtain of the ThmFourTwo R-stage lane, at
`En := blockEnrichmentD`: `m` comes free from the nonsingular form (A-4.6b), and the
un/ramified dichotomy is a single `by_cases` on the head-level `F.alpha tameTau`-action —
ρ- and source-uniform, so ONE case split serves all four twin applications.  `D6` is the
global `tateDuality 2`; the tame-unit orientation (needed by the local ramified twin) is
carried as a hypothesis — it is provable at the concrete `boundaryMapsWitness`
(`tameUnitOrientation_witness`), the P5 consumer's discharge point. -/

/-- **The G0-obtain at `blockEnrichmentD`** (P4e): shared `G0 = ∓2^m` with the four
`gaussZResidueD_*` twins dispatched by the head dichotomy. -/
theorem gaussZ_obtain_blockD [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    [IsTopologicalGroup AbsGalQ2]
    (hE2 : ∀ e : E, e ^ 2 = 1) (B : BoundaryMaps) (F : BoundaryFrame H E)
    (R : LocalReciprocity) (horient : TameUnitOrientation R B.tameF)
    (hsimple : ∀ W : AddSubgroup (blockEnrichmentD T Blk hE2 F).Vmod,
      (∀ g : (blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : (blockEnrichmentD T Blk hE2 F).Vmod, v ≠ 0)
    (hnt : ∃ (g : (blockFrame T Blk hE2).YC) (v : (blockEnrichmentD T Blk hE2 F).Vmod),
      g • v ≠ v) :
    ∃ G0 : ℤ,
      (∀ (l : (blockFrame T Blk hE2).DR) (h : l ≠ (blockFrame T Blk hE2).zeroDR),
        GaussZResidue B.bA F (blockEnrichmentD T Blk hE2 F) l h G0) ∧
      (∀ (l : (blockFrame T Blk hE2).DR) (h : l ≠ (blockFrame T Blk hE2).zeroDR),
        GaussZResidue B.bF F (blockEnrichmentD T Blk hE2 F) l h G0) := by
  classical
  letI := blockPS_commGroup Blk
  letI := headAct T Blk
  by_cases hex : ∃ l : (blockFrame T Blk hE2).DR, l ≠ (blockFrame T Blk hE2).zeroDR
  · obtain ⟨l₀, hl₀⟩ := hex
    have hl₀' : l₀.1 ≠ Blk.frattiniK := fun heq => hl₀ (Subtype.ext heq)
    -- `m` from the nonsingular form on `V` (A-4.6b), `l`-free through `#V`
    obtain ⟨m, hm, hcard⟩ := exists_one_le_card_eq_two_pow_of_nonsingular
      (blockQbar T Blk F.alpha F.alpha_surjective l₀ hl₀')
      (blockHquad T Blk F.alpha F.alpha_surjective l₀ hl₀')
      (blockHns T Blk F.alpha F.alpha_surjective l₀ hl₀')
      (blockPS_exp2 T Blk) hVne
    -- the ρ/source-uniform head dichotomy
    by_cases hd : ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P),
        F.alpha tameTau • v = v
    · exact ⟨-(2 ^ m : ℤ),
        fun l h => gaussZResidueD_gammaA_unramified T Blk hE2 B F hsimple hVne hnt
          m hm hcard l h hd,
        fun l h => gaussZResidueD_local_unramified T Blk hE2 B F (tateDuality 2)
          hsimple hVne hnt m hm hcard l h hd⟩
    · push Not at hd
      exact ⟨(2 ^ m : ℤ),
        fun l h => gaussZResidueD_gammaA_ramified T Blk hE2 B F hsimple hVne hnt
          m hm hcard l h hd,
        fun l h => gaussZResidueD_local_ramified T Blk hE2 B F (tateDuality 2) R horient
          hsimple hVne hnt m hm hcard l h hd⟩
  · push Not at hex
    exact ⟨0, fun l h => absurd (hex l) h, fun l h => absurd (hex l) h⟩

end SectionNine

end GQ2

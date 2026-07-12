import GQ2.GaussZ.Final
import GQ2.GaussZ.CoordGammaA
import GQ2.Block.HeadDat

/-!
# P-16d6e4aA-P4c — the local `GaussZResidue` twins at the head-inflated enrichment

The P4 reshape's local side (`docs/p16d6e4aA-p4-tame-package.md` §3): the two
`gaussZResidue_local_*` twins of `GQ2/GaussZFinal.lean` replayed at
`En := blockEnrichmentD` — **without the refuted per-lift `hpack`**.  For an arbitrary
boundary lift `ρ` the tame factorization is recovered at the faithful head quotient:

* `blockEnrichmentD`'s datum is *definitionally* `(blockDatHV).reindexHom blockProjF`, so
  `Q0loc` transports down `Q0loc_reindexHom_hom` (the `MonoidHom`-level variant of the banked
  `Q0loc_reindexHom`) from `(dat, ρ.1.1)` to `(blockDatHV, blockProjF ∘ ρ.1.1)`;
* the boundary equation's head component (`boundaryLift_head_local`) identifies
  `blockProjF ∘ ρ.1.1 = cF ∘ B.tameF` with the **fixed** surjection `cF := mk' ∘ F.alpha` —
  tame-factored uniformly in `ρ`;
* the workers `sum_sign_Q0loc_{unramified,ramified}` then run at `C := HVq T Blk`, where
  `hfaith` is `hvAct_faithful` (true by construction) and the invariance/simplicity inputs
  are the `hv_inv`/`hv_simple` transports;
* the `V^{C₀} = 0` freeness runs on `hfix_of_simple_nt` (no `hfaith` at `Y⧸K` — it is false
  there whenever `K < L_Y`).

The un/ramified dichotomy hypothesis is taken at the **head** (`F.alpha tameTau`-action,
`headAct`) — ρ-free and source-free, so the P4e obtain can `by_cases` on it once for both
sources.  Everything std-3.
-/

namespace GQ2

namespace SectionNine

open ContCoh QuadraticFp2 SectionSix SectionSeven SectionEight SectionEight.AffineTLift

open scoped Classical

/-! ## The `MonoidHom`-level `Q0loc` reindexing transport -/

section ReindexHom

variable {C C' : Type} [Group C] [TopologicalSpace C] [Group C'] [TopologicalSpace C']
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V]
  [DistribMulAction C V] [DistribMulAction C' V]

/-- **`Q0loc` reindexing along a `MonoidHom`-composite** (the P4c transport): `Q⁰_loc` of the
`φ`-reindexed datum along `ρ'` equals `Q⁰_loc` of the datum along any continuous hom `ρc`
whose values are `φ ∘ ρ'`.  The `MonoidHom`-level variant of the banked
`ShapiroDeepness.Q0loc_reindexHom` (which requires `φ` bundled continuous); here `φ` is a
plain `→*` and the composite is supplied as `ρc`, matching the `blockProjF`-composite
construction. -/
theorem Q0loc_reindexHom_hom (D : TateDuality 2) (dat : FactorSet C V) (φ : C' →* C)
    (hφ : ∀ (c' : C') (v : V), c' • v = φ c' • v)
    (ρ' : ContinuousMonoidHom AbsGalQ2 C') (ρc : ContinuousMonoidHom AbsGalQ2 C)
    (hρc : ∀ g : AbsGalQ2, ρc g = φ (ρ' g)) (x : H1 AbsGalQ2 V) :
    Q0loc D (dat.reindexHom ⇑φ) ρ' x = Q0loc D dat ρc x := by
  show iotaF D (H2ofFun AbsGalQ2 (graphPullback (dat.reindexHom ⇑φ) ⇑ρ' (Quotient.out x).1))
    = iotaF D (H2ofFun AbsGalQ2 (graphPullback dat ⇑ρc (Quotient.out x).1))
  rw [ShapiroDeepness.graphPullback_reindexHom dat ⇑φ hφ ⇑ρ' (Quotient.out x).1,
    show (⇑φ ∘ ⇑ρ') = ⇑ρc from funext fun g => (hρc g).symm]

end ReindexHom

/-! ## The twins -/

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable (T : MarkedTarget H E Y) (Blk : MinimalBlock T.LY)
variable [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  [IsTopologicalGroup AbsGalQ2]

/-- **`hGaussZF` at the head-inflated enrichment, unramified case** (P4c): for the block
enrichment `blockEnrichmentD`, `GaussZResidue B.bF F (blockEnrichmentD …) l h (−2^m)` with
**no per-lift tame package** — the dichotomy hypothesis is the head-level
`F.alpha tameTau`-triviality, uniform in `ρ`. -/
theorem gaussZResidueD_local_unramified (hE2 : ∀ e : E, e ^ 2 = 1) (B : BoundaryMaps)
    (F : BoundaryFrame H E) (D6 : TateDuality 2)
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
    GaussZResidue B.bF F (blockEnrichmentD T Blk hE2 F) l h (-(2 ^ m : ℤ)) := by
  classical
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := headAct T Blk
  letI := hvAct T Blk
  letI : TopologicalSpace (HVq T Blk) := ⊥
  haveI : DiscreteTopology (HVq T Blk) := ⟨rfl⟩
  have hl' : l.1 ≠ Blk.frattiniK := fun heq => h (Subtype.ext heq)
  set EnD := blockEnrichmentD T Blk hE2 F with hEnDdef
  intro ρ
  set ρM := (blockFrame T Blk hE2).rhoPrime B.bF F (EnD.radData l h) rfl ρ with hρMdef
  -- the fixed tame surjection into the faithful head quotient, and the per-`ρ` composite
  set cF : ContinuousMonoidHom Ttame (HVq T Blk) :=
    ⟨(QuotientGroup.mk' (headActKer T Blk)).comp F.alpha.toMonoidHom,
      (continuous_of_discreteTopology
        (f := fun hh : H => QuotientGroup.mk' (headActKer T Blk) hh)).comp
        F.alpha.continuous_toFun⟩ with hcFdef
  have hcF : Function.Surjective ⇑cF :=
    (QuotientGroup.mk'_surjective _).comp F.alpha_surjective
  set ρHV : ContinuousMonoidHom AbsGalQ2 (HVq T Blk) :=
    ⟨(blockProjF T Blk).comp ρ.1.1.toMonoidHom,
      (continuous_of_discreteTopology
        (f := fun c : (blockFrame T Blk hE2).YC => blockProjF T Blk c)).comp
        ρ.1.1.continuous_toFun⟩ with hρHVdef
  have hfacHV : ∀ g : AbsGalQ2, ρHV g = cF (B.tameF g) := fun g =>
    congrArg (⇑(QuotientGroup.mk' (headActKer T Blk)))
      (boundaryLift_head_local T Blk hE2 B F ρ g)
  -- the module structure on `V` through the head-quotient composite
  letI instT : TopologicalSpace (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) := ⊥
  haveI instD : DiscreteTopology (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) := ⟨rfl⟩
  letI instA : DistribMulAction AbsGalQ2 (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) :=
    DistribMulAction.compHom _ ρHV.toMonoidHom
  haveI instC : ContinuousSMul AbsGalQ2 (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) := ⟨by
    show Continuous fun p : AbsGalQ2 × Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P) =>
      ρHV p.1 • p.2
    exact (continuous_of_discreteTopology
        (f := fun q : HVq T Blk × Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P) =>
          q.1 • q.2)).comp
      ((ρHV.continuous.comp continuous_fst).prodMk continuous_snd)⟩
  -- the same instances re-keyed at the syntactic projections
  letI : TopologicalSpace EnD.Vmod := instT
  haveI : DiscreteTopology EnD.Vmod := instD
  letI : DistribMulAction AbsGalQ2 EnD.Vmod := instA
  haveI : ContinuousSMul AbsGalQ2 EnD.Vmod := instC
  letI : TopologicalSpace (EnD.descData l h).Vmod := instT
  haveI : DiscreteTopology (EnD.descData l h).Vmod := instD
  letI : DistribMulAction AbsGalQ2 (EnD.descData l h).Vmod := instA
  haveI : ContinuousSMul AbsGalQ2 (EnD.descData l h).Vmod := instC
  letI : DistribMulAction (HVq T Blk) EnD.Vmod := hvAct T Blk
  letI : DistribMulAction (HVq T Blk) (EnD.descData l h).Vmod := hvAct T Blk
  letI : TopologicalSpace (EnD.descData l h).C0 :=
    (inferInstance : TopologicalSpace (blockFrame T Blk hE2).YC)
  haveI : DiscreteTopology (EnD.descData l h).C0 :=
    (inferInstance : DiscreteTopology (blockFrame T Blk hE2).YC)
  haveI : Finite (EnD.descData l h).C0 := (inferInstance : Finite (blockFrame T Blk hE2).YC)
  -- spelling covers: shadow the global quotient-topology at the raw `Y ⧸ K` spelling with
  -- the frame's instances, and provide the `YC`-spelled action on the raw module
  letI : TopologicalSpace (Y ⧸ Blk.K) :=
    (inferInstance : TopologicalSpace (blockFrame T Blk hE2).YC)
  haveI : DiscreteTopology (Y ⧸ Blk.K) :=
    (inferInstance : DiscreteTopology (blockFrame T Blk hE2).YC)
  haveI : Finite (Y ⧸ Blk.K) := (inferInstance : Finite (blockFrame T Blk hE2).YC)
  letI : DistribMulAction ((blockFrame T Blk hE2).YC)
      (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) := blockActV Blk
  letI : DistribMulAction ((blockFrame T Blk hE2).YC) (EnD.descData l h).Vmod :=
    blockActV Blk
  -- the roundtrip and the bridge
  have hround : ∀ γ : AbsGalQ2, rho0 (EnD.descData l h) ρM γ = ρ.1.1 γ :=
    rho0_descData_rhoPrime B.bF F EnD l h ρ
  have hcomp : ∀ (γ : AbsGalQ2) (v : (EnD.descData l h).Vmod),
      γ • v = rho0 (EnD.descData l h) ρM γ • v := by
    intro γ v
    rw [show rho0 (EnD.descData l h) ρM γ • v
        = blockProjF T Blk (rho0 (EnD.descData l h) ρM γ) • v from blockProjF_compat T Blk _ v,
      hround γ]
    rfl
  -- finiteness of `Z¹`, σ-free from the e3 count
  haveI hfinZ : Finite (VCocycle (EnD.descData l h) ρM) :=
    (Nat.card_ne_zero.mp (by
      rw [hZcard_local B.bF F EnD l h hsimple hVne hnt ρ]
      exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')).2
  -- the `V^{C₀} = 0` freeness input (hfaith-free)
  have hsurjρ' : Function.Surjective (fun γ : AbsGalQ2 => rho0 (EnD.descData l h) ρM γ) :=
    fun y => by
      obtain ⟨γ, hγ⟩ := ρ.1.2 y
      exact ⟨γ, (hround γ).trans hγ⟩
  have hfix : ∀ v : (EnD.descData l h).Vmod,
      (∀ γ : AbsGalQ2, rho0 (EnD.descData l h) ρM γ • v = v) → v = 0 :=
    hfix_of_simple_nt hsurjρ' hsimple hnt
  -- the transport bijection `Z¹⧸B¹ ≅ H¹`
  have hbij : Function.Bijective (h1OfVQuot hcomp) :=
    ⟨h1OfVQuot_injective hcomp, h1OfVQuot_surjective hcomp⟩
  -- the pinned value at the faithful head quotient
  have hunramF : ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), cF tameTau • v = v :=
    hunram
  have hpinned := sum_sign_Q0loc_unramified D6 B cF hcF ρHV hfacHV (fun _ _ => rfl)
    (hvAct_faithful T Blk) (hv_simple T Blk) hVne hunramF
    (blockQbar T Blk F.alpha F.alpha_surjective l hl')
    (blockHquad T Blk F.alpha F.alpha_surjective l hl')
    (blockHns T Blk F.alpha F.alpha_surjective l hl')
    (hv_inv T Blk F l hl') (blockDatHV T Blk F l hl') (blockDatHV_spec T Blk F l hl')
    m hm hcard
  have hQbar : ∑ᶠ x, SectionEight.sign (QZeroBar (EnD.descData l h) ρM htriv_local' x)
      = -(2 ^ m : ℤ) := by
    rw [← hpinned]
    refine finsum_eq_of_bijective (h1OfVQuot hcomp) hbij fun x => ?_
    rw [QZeroBar_eq_Q0loc D6 hcomp ρ.1.1 (fun γ => (hround γ).symm) htriv_local' x]
    exact congrArg SectionEight.sign
      (Q0loc_reindexHom_hom (C := HVq T Blk) (C' := (blockFrame T Blk hE2).YC) D6
        (blockDatHV T Blk F l hl') (blockProjF T Blk) (blockProjF_compat T Blk)
        ρ.1.1 ρHV (fun g => rfl) (h1OfVQuot hcomp x))
  calc ∑ᶠ cc : VCocycle (EnD.descData l h) ρM,
        SectionEight.sign (QZero (EnD.descData l h) ρM cc)
      = (Nat.card EnD.Vmod : ℤ)
          * ∑ᶠ x, SectionEight.sign (QZeroBar (EnD.descData l h) ρM htriv_local' x) :=
        gaussZ_reduction htriv_local' hfix
    _ = (Nat.card EnD.Vmod : ℤ) * (-(2 ^ m : ℤ)) := by rw [hQbar]

/-- **`hGaussZF` at the head-inflated enrichment, ramified case** (P4c): inertia moves the
module at the head — `GaussZResidue B.bF F (blockEnrichmentD …) l h (+2^m)`, no per-lift
package; the local side carries the tame-unit orientation as before. -/
theorem gaussZResidueD_local_ramified (hE2 : ∀ e : E, e ^ 2 = 1) (B : BoundaryMaps)
    (F : BoundaryFrame H E) (D6 : TateDuality 2) (R : LocalReciprocity)
    (horient : TameUnitOrientation R B.tameF)
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
    GaussZResidue B.bF F (blockEnrichmentD T Blk hE2 F) l h (2 ^ m : ℤ) := by
  classical
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := headAct T Blk
  letI := hvAct T Blk
  letI : TopologicalSpace (HVq T Blk) := ⊥
  haveI : DiscreteTopology (HVq T Blk) := ⟨rfl⟩
  have hl' : l.1 ≠ Blk.frattiniK := fun heq => h (Subtype.ext heq)
  set EnD := blockEnrichmentD T Blk hE2 F with hEnDdef
  intro ρ
  set ρM := (blockFrame T Blk hE2).rhoPrime B.bF F (EnD.radData l h) rfl ρ with hρMdef
  set cF : ContinuousMonoidHom Ttame (HVq T Blk) :=
    ⟨(QuotientGroup.mk' (headActKer T Blk)).comp F.alpha.toMonoidHom,
      (continuous_of_discreteTopology
        (f := fun hh : H => QuotientGroup.mk' (headActKer T Blk) hh)).comp
        F.alpha.continuous_toFun⟩ with hcFdef
  have hcF : Function.Surjective ⇑cF :=
    (QuotientGroup.mk'_surjective _).comp F.alpha_surjective
  set ρHV : ContinuousMonoidHom AbsGalQ2 (HVq T Blk) :=
    ⟨(blockProjF T Blk).comp ρ.1.1.toMonoidHom,
      (continuous_of_discreteTopology
        (f := fun c : (blockFrame T Blk hE2).YC => blockProjF T Blk c)).comp
        ρ.1.1.continuous_toFun⟩ with hρHVdef
  have hfacHV : ∀ g : AbsGalQ2, ρHV g = cF (B.tameF g) := fun g =>
    congrArg (⇑(QuotientGroup.mk' (headActKer T Blk)))
      (boundaryLift_head_local T Blk hE2 B F ρ g)
  letI instT : TopologicalSpace (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) := ⊥
  haveI instD : DiscreteTopology (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) := ⟨rfl⟩
  letI instA : DistribMulAction AbsGalQ2 (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) :=
    DistribMulAction.compHom _ ρHV.toMonoidHom
  haveI instC : ContinuousSMul AbsGalQ2 (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) := ⟨by
    show Continuous fun p : AbsGalQ2 × Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P) =>
      ρHV p.1 • p.2
    exact (continuous_of_discreteTopology
        (f := fun q : HVq T Blk × Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P) =>
          q.1 • q.2)).comp
      ((ρHV.continuous.comp continuous_fst).prodMk continuous_snd)⟩
  letI : TopologicalSpace EnD.Vmod := instT
  haveI : DiscreteTopology EnD.Vmod := instD
  letI : DistribMulAction AbsGalQ2 EnD.Vmod := instA
  haveI : ContinuousSMul AbsGalQ2 EnD.Vmod := instC
  letI : TopologicalSpace (EnD.descData l h).Vmod := instT
  haveI : DiscreteTopology (EnD.descData l h).Vmod := instD
  letI : DistribMulAction AbsGalQ2 (EnD.descData l h).Vmod := instA
  haveI : ContinuousSMul AbsGalQ2 (EnD.descData l h).Vmod := instC
  letI : DistribMulAction (HVq T Blk) EnD.Vmod := hvAct T Blk
  letI : DistribMulAction (HVq T Blk) (EnD.descData l h).Vmod := hvAct T Blk
  letI : TopologicalSpace (EnD.descData l h).C0 :=
    (inferInstance : TopologicalSpace (blockFrame T Blk hE2).YC)
  haveI : DiscreteTopology (EnD.descData l h).C0 :=
    (inferInstance : DiscreteTopology (blockFrame T Blk hE2).YC)
  haveI : Finite (EnD.descData l h).C0 := (inferInstance : Finite (blockFrame T Blk hE2).YC)
  -- spelling covers: shadow the global quotient-topology at the raw `Y ⧸ K` spelling with
  -- the frame's instances, and provide the `YC`-spelled action on the raw module
  letI : TopologicalSpace (Y ⧸ Blk.K) :=
    (inferInstance : TopologicalSpace (blockFrame T Blk hE2).YC)
  haveI : DiscreteTopology (Y ⧸ Blk.K) :=
    (inferInstance : DiscreteTopology (blockFrame T Blk hE2).YC)
  haveI : Finite (Y ⧸ Blk.K) := (inferInstance : Finite (blockFrame T Blk hE2).YC)
  letI : DistribMulAction ((blockFrame T Blk hE2).YC)
      (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) := blockActV Blk
  letI : DistribMulAction ((blockFrame T Blk hE2).YC) (EnD.descData l h).Vmod :=
    blockActV Blk
  have hround : ∀ γ : AbsGalQ2, rho0 (EnD.descData l h) ρM γ = ρ.1.1 γ :=
    rho0_descData_rhoPrime B.bF F EnD l h ρ
  have hcomp : ∀ (γ : AbsGalQ2) (v : (EnD.descData l h).Vmod),
      γ • v = rho0 (EnD.descData l h) ρM γ • v := by
    intro γ v
    rw [show rho0 (EnD.descData l h) ρM γ • v
        = blockProjF T Blk (rho0 (EnD.descData l h) ρM γ) • v from blockProjF_compat T Blk _ v,
      hround γ]
    rfl
  haveI hfinZ : Finite (VCocycle (EnD.descData l h) ρM) :=
    (Nat.card_ne_zero.mp (by
      rw [hZcard_local B.bF F EnD l h hsimple hVne hnt ρ]
      exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')).2
  have hsurjρ' : Function.Surjective (fun γ : AbsGalQ2 => rho0 (EnD.descData l h) ρM γ) :=
    fun y => by
      obtain ⟨γ, hγ⟩ := ρ.1.2 y
      exact ⟨γ, (hround γ).trans hγ⟩
  have hfix : ∀ v : (EnD.descData l h).Vmod,
      (∀ γ : AbsGalQ2, rho0 (EnD.descData l h) ρM γ • v = v) → v = 0 :=
    hfix_of_simple_nt hsurjρ' hsimple hnt
  have hbij : Function.Bijective (h1OfVQuot hcomp) :=
    ⟨h1OfVQuot_injective hcomp, h1OfVQuot_surjective hcomp⟩
  have hramF : ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), cF tameTau • v ≠ v := hram
  have hpinned := sum_sign_Q0loc_ramified D6 R B cF hcF ρHV hfacHV horient (fun _ _ => rfl)
    (hvAct_faithful T Blk) (hv_simple T Blk) hramF
    (blockQbar T Blk F.alpha F.alpha_surjective l hl')
    (blockHquad T Blk F.alpha F.alpha_surjective l hl')
    (blockHns T Blk F.alpha F.alpha_surjective l hl')
    (hv_inv T Blk F l hl') (blockDatHV T Blk F l hl') (blockDatHV_spec T Blk F l hl')
    m hm hcard
  have hQbar : ∑ᶠ x, SectionEight.sign (QZeroBar (EnD.descData l h) ρM htriv_local' x)
      = (2 ^ m : ℤ) := by
    rw [← hpinned]
    refine finsum_eq_of_bijective (h1OfVQuot hcomp) hbij fun x => ?_
    rw [QZeroBar_eq_Q0loc D6 hcomp ρ.1.1 (fun γ => (hround γ).symm) htriv_local' x]
    exact congrArg SectionEight.sign
      (Q0loc_reindexHom_hom (C := HVq T Blk) (C' := (blockFrame T Blk hE2).YC) D6
        (blockDatHV T Blk F l hl') (blockProjF T Blk) (blockProjF_compat T Blk)
        ρ.1.1 ρHV (fun g => rfl) (h1OfVQuot hcomp x))
  calc ∑ᶠ cc : VCocycle (EnD.descData l h) ρM,
        SectionEight.sign (QZero (EnD.descData l h) ρM cc)
      = (Nat.card EnD.Vmod : ℤ)
          * ∑ᶠ x, SectionEight.sign (QZeroBar (EnD.descData l h) ρM htriv_local' x) :=
        gaussZ_reduction htriv_local' hfix
    _ = (Nat.card EnD.Vmod : ℤ) * (2 ^ m : ℤ) := by rw [hQbar]

end SectionNine

end GQ2

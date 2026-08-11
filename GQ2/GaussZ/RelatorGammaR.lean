/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.IotaGammaR
import GQ2.GaussZ.RelatorGammaA

/-!
# `Q⁰` over `Γ_R` as a Roe relator value in the `κ⁰`-extension

The `Γ_R` twin of `GQ2/GaussZ/RelatorGammaA.lean`'s `GammaA` section (the A-3 keystone,
obligation ii.7): over the raw candidate carrier `GR = F₄ ⧸ N_R`, the base determinant form
`Q⁰` of a crossed `V`-cocycle is the **Roe relator pair value in the concrete
`κ⁰`-extension**:

  `Q⁰_{Γ_R,ρ'}(c) = relZPairR (graph-marking) κ⁰-cocycle |₁ + |₂`,

where the graph marking is the image of the `Γ_R`-generator marking `gammaGenR` under the
graph homomorphism — the four explicit pairs `(c(gᵢ), ρ'₀(gᵢ)) ∈ V ⋊ C`.  The route is the
`Γ_A` one verbatim: A-2 over `Γ_R` (`IotaGammaR.QZero_eq_levelFactor_obsR`, the R31c layer)
at the explicit `LevelFactorR` through the `κ⁰`-cocycle (kernel level of the graph hom),
transported by the Roe level-change naturality (`WordCoh2R.relZPairR_comap`).

The carrier `Sd C V`, the cocycle `kappa0Cocycle`, and the graph homomorphism `graphSdHom`
are **generic in `Γ` and imported from `GQ2/GaussZ/RelatorGammaA.lean`**, never cloned; the
only genuine clone is the 15-line continuity lemma `continuous_vcocycle_c_R` (its `Γ_A`
original is stated against `ρM : ContinuousMonoidHom GA _`).

All std-3; no axioms, no sorries.
-/

namespace GQ2

namespace SectionEight

namespace AffineTLift

open CentralObstruction WordCohBridge WordCohBridgeR WordCoh2 WordCoh2R ContCoh

section GammaR

variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
variable {ρM : ContinuousMonoidHom GR (Bg ⧸ D.M)}
variable [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
variable [TopologicalSpace DD.C0] [DiscreteTopology DD.C0] [Finite DD.C0] [Finite DD.Vmod]

omit [DiscreteTopology DD.Vmod] [TopologicalSpace DD.C0] [DiscreteTopology DD.C0] [Finite DD.C0]
  [Finite DD.Vmod] in
/-- A crossed cocycle's underlying function is continuous into the (discrete) module — the
`Γ_R` retyping of `continuous_vcocycle_c` (`GQ2/GaussZ/RelatorGammaA.lean`; the original is
pinned to `GA`-typed lower maps). -/
theorem continuous_vcocycle_c_R (c : VCocycle DD ρM) : Continuous c.c := by
  have hlc : IsLocallyConstant c.c := by
    intro s
    have hpre : c.c ⁻¹' s
        = (fun γ => iV DD (Multiplicative.ofAdd (c.c γ)))
          ⁻¹' ((fun v => iV DD (Multiplicative.ofAdd v)) '' s) := by
      ext γ
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro h
        exact ⟨c.c γ, h, rfl⟩
      · rintro ⟨v, hv, heq⟩
        rwa [← iV_ofAdd_inj DD heq]
    rw [hpre]
    exact IsOpen.preimage c.cont (isOpen_discrete _)
  exact hlc.continuous

/-- **The A-3 keystone over `Γ_R`**: the base determinant form `Q⁰` of a crossed `V`-cocycle
is the **Roe relator value in the concrete `κ⁰`-extension**: the (tame + Roe wild)
relator-`z` pair of the `κ⁰`-cocycle on `V ⋊ C` at the marking `graph(gammaGenR)` — the four
explicit pairs `(c(gᵢ), ρ'₀(gᵢ))`.  (A-2 over `Γ_R` — `QZero_eq_levelFactor_obsR` — at the
kernel level of the graph hom, transported by `relZPairR_comap`.) -/
theorem QZero_eq_relZPair_kappa0_R [DistribMulAction GR (ZMod 2)]
    [ContinuousSMul GR (ZMod 2)]
    (htriv : ∀ (x : GR) (m : ZMod 2), x • m = m)
    {q : DD.Vmod → ZMod 2} (hdat : IsEquivariantFactorSet q DD.dat)
    (c : VCocycle DD ρM) :
    QZero DD ρM c
      = (relZPairR (gammaGenR.map (graphSdHom c)) (kappa0Cocycle DD.dat hdat)).1
        + (relZPairR (gammaGenR.map (graphSdHom c)) (kappa0Cocycle DD.dat hdat)).2 := by
  classical
  -- the graph hom is continuous into the finite discrete `V ⋊ C`
  haveI : DiscreteTopology (Bg ⧸ D.M) := CentralObstruction.discreteTopology_quotient D
  have hgcont : Continuous (graphSdHom c) := by
    show Continuous fun γ => ((c.c γ, rho0 DD ρM γ) : DD.Vmod × DD.C0)
    exact (continuous_vcocycle_c_R c).prodMk
      ((continuous_of_discreteTopology (f := fun x : Bg ⧸ D.M => liftC0 DD x)).comp
        ρM.continuous)
  -- the composite from `F₄` and its (open, normal) kernel level
  set full : FreeProfiniteGroup (Fin 4) →* Sd DD.C0 DD.Vmod :=
    (graphSdHom c).comp (quotientMk NR).toMonoidHom with hfulldef
  have hfullcont : Continuous full := hgcont.comp (quotientMk NR).continuous
  have hkeropen : IsOpen (full.ker : Set (FreeProfiniteGroup (Fin 4))) := by
    rw [MonoidHom.coe_ker]
    exact IsOpen.preimage hfullcont (isOpen_discrete _)
  set U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) :=
    ⟨⟨full.ker, hkeropen⟩, full.normal_ker⟩ with hUdef
  have hNRle : NR ≤ U.toSubgroup := by
    intro n hn
    show full n = 1
    show (graphSdHom c) (quotientMk NR n) = 1
    rw [show quotientMk NR n = 1 from (quotientMk_eq_one_iff NR).mpr hn, map_one]
  -- the descended level map, agreeing with the graph through `levelProjR`
  set φU : (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup) →* Sd DD.C0 DD.Vmod :=
    QuotientGroup.lift U.toSubgroup full (fun _ hu => hu) with hφUdef
  have hφlev : ∀ g : GR, φU (levelProjR U hNRle g) = graphSdHom c g := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H x => rfl
  -- the graph pullback is already `(1,1)`-normalized
  have h11 : graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c (1, 1) = 0 := by
    show DD.dat.f (c.c 1) (rho0 DD ρM 1 • c.c 1) + DD.dat.m (rho0 DD ρM 1) (c.c 1) = 0
    rw [c.c_one, smul_zero, hdat.f_zero_left, map_one, hdat.m_one, add_zero]
  have hnorm : normalizeCochainR (graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c)
      = graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c := by
    funext p
    show graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c p
        - graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c (1, 1)
      = graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c p
    rw [h11, sub_zero]
  -- the explicit level factorization through the `κ⁰`-cocycle
  set F : LevelFactorR
      (normalizeCochainR (graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c)) :=
    ⟨U, hNRle, (kappa0Cocycle DD.dat hdat).comap φU, by
      intro x y
      rw [hnorm]
      show graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c (x, y)
        = (kappa0Cocycle DD.dat hdat).κ (φU (levelProjR U hNRle x))
            (φU (levelProjR U hNRle y))
      rw [hφlev, hφlev]
      exact graphPullback_eq_kappa0_graph hdat c (x, y)⟩ with hFdef
  -- assemble: A-2 over `Γ_R` + the level-change naturality (`relZPairR_comap`); the marking
  -- identification `(univMarking.map mk'_U).map φU = gammaGenR.map (graphSdHom c)` holds
  -- definitionally (`QuotientGroup.lift` computes at `mk`), so the rewrite closes by `rfl`
  have hA2 := IotaGammaR.QZero_eq_levelFactor_obsR htriv c F
  rw [hA2]
  show (relZPairR (univMarking.map (QuotientGroup.mk' U.toSubgroup))
        ((kappa0Cocycle DD.dat hdat).comap φU)).1
      + (relZPairR (univMarking.map (QuotientGroup.mk' U.toSubgroup))
        ((kappa0Cocycle DD.dat hdat).comap φU)).2 = _
  rw [← relZPairR_comap]
  rfl

end GammaR

end AffineTLift

end SectionEight

end GQ2

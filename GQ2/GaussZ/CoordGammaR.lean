/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.GaussZ.CoordGammaA
import GQ2.WordCohBridgeR
import GQ2.Phase140.GammaR

/-!
# The `Γ_R` (83)-coordinates — `Z¹⧸B¹` in Roe word generator coordinates

The `Γ_R` twin of `GQ2/GaussZ/CoordGammaA.lean`'s `CoordGammaA` section (brick A-1 of the
ii.7 supply layer): the per-`ρ` `GammaR → GR` retypes of the two lower maps, composed with
the banked Roe degree-1 word comparison (`WordCohBridgeR.h1EquivR`) into the
generator-coordinate model of the `Γ_R` Gauss domain

    `h1CoordGammaR : Z¹_{Γ_R,ρ'}(V) ⧸ B¹ → H¹_{R,word} (markC_R θ)`   (`θ = ρ.1.1`),

bijective, so the A-3 keystone (`GQ2/GaussZ/RelatorGammaR.lean`) can evaluate the descended
`Q̄⁰` as an explicit `𝔽₂`-function of Roe word-cocycle classes.  Contents mirror the `Γ_A`
file declaration-for-declaration:

* `rhoPrimeGR`/`thetaGR` — the `GammaR → GR` retypes (the e6 Stage-0 idiom), with
  `thetaGR_surjective` and the roundtrip `roundtripGR` (the generic
  `rho0_descData_rhoPrime`, which is `Γ`-agnostic — no `Γ_R` re-derivation needed);
* `finite_vcocycle_gammaR` — `Z¹` finiteness, σ-free from `Phase140GammaR.hZcard_gammaR`
  (the R31f count);
* `h1CoordGammaR` + `h1CoordGammaR_bijective`.

The `hnt`-variant fixed-point freeness `hfix_of_simple_nt` is generic and imported from the
`Γ_A` file, never cloned.  All std-3.
-/

namespace GQ2

namespace SectionEight

namespace AffineTLift

open CentralObstruction ContCoh WordCohBridgeR FoxH

section CoordGammaR

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
variable {RF : RecursionFrame T Blk}
variable (b : ContinuousMonoidHom GammaR ↥boundarySubgroup) (F : BoundaryFrame H E)
  (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR) (ρ : BoundaryLifts b F RF.TC)

/-- The lower map `ρ' : Γ_R → Y_B ⧸ M`, retyped against the raw quotient `GR` (the e6
Stage-0 idiom as a declaration; `Γ_R` twin of `rhoPrimeGA`). -/
noncomputable def rhoPrimeGR : ContinuousMonoidHom GR (RF.YB ⧸ (En.radData l h).M) :=
  RF.rhoPrime b F (En.radData l h) rfl ρ

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **`Z¹` is finite** — σ-free from the R31f count (`Phase140GammaR.hZcard_gammaR`);
`Γ_R` twin of `finite_vcocycle_gammaA`. -/
theorem finite_vcocycle_gammaR
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v) :
    Finite (VCocycle (En.descData l h) (rhoPrimeGR b F En l h ρ)) :=
  (Nat.card_ne_zero.mp (by
    show Nat.card (VCocycle (En.descData l h)
      (RF.rhoPrime b F (En.radData l h) rfl ρ)) ≠ 0
    rw [Phase140GammaR.hZcard_gammaR b F En l h hsimple hVne hnt ρ]
    exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')).2

variable [TopologicalSpace (En.descData l h).Vmod] [DiscreteTopology (En.descData l h).Vmod]
  [DistribMulAction GR (En.descData l h).Vmod] [ContinuousSMul GR (En.descData l h).Vmod]
  [DistribMulAction RF.YC (En.descData l h).Vmod]
  [Finite (En.descData l h).Vmod]

/-- The boundary-lift head `θ = ρ.1.1 : Γ_R → Y_C`, retyped against `GR` — the marking map
of the Roe word complex (`markC_R (thetaGR …)`); `Γ_R` twin of `thetaGA`. -/
noncomputable def thetaGR : ContinuousMonoidHom GR RF.YC :=
  ρ.1.1

omit [TopologicalSpace Y] [DiscreteTopology Y] in
theorem thetaGR_surjective : Function.Surjective ⇑(thetaGR b F ρ) :=
  ρ.1.2

omit [TopologicalSpace Y] [DiscreteTopology Y]
  [TopologicalSpace (En.descData l h).Vmod] [DiscreteTopology (En.descData l h).Vmod]
  [DistribMulAction GR (En.descData l h).Vmod] [ContinuousSMul GR (En.descData l h).Vmod]
  [DistribMulAction RF.YC (En.descData l h).Vmod] [Finite (En.descData l h).Vmod] in
/-- The roundtrip `rho0 ∘ rhoPrime = θ` over `GR` (`rho0_descData_rhoPrime` is `Γ`-generic,
so this is a pure retype).  Callers derive the `h1OfVQuot`-compatibility from their
letI-pack through this, exactly as on the `Γ_A` side. -/
theorem roundtripGR : ∀ γ : GR,
    rho0 (En.descData l h) (rhoPrimeGR b F En l h ρ) γ = thetaGR b F ρ γ :=
  fun γ => rho0_descData_rhoPrime b F En l h ρ γ

/-- **The A-1 result for `Γ_R`**: the generator-coordinate model of the `Γ_R` Gauss domain —
the quotient bijection `h1OfVQuot` into `H¹(Γ_R, V)` composed with the banked Roe degree-1
word comparison `h1EquivR` into `H¹_{R,word}(markC_R θ)` (classes of `Fin 4 → V` generator
tuples).  Binder shape mirrors `h1CoordGammaA` exactly. -/
noncomputable def h1CoordGammaR
    (hcomp : ∀ (γ : GR) (v : (En.descData l h).Vmod),
      γ • v = rho0 (En.descData l h) (rhoPrimeGR b F En l h ρ) γ • v)
    (hcompat : ∀ (γ : GR) (v : (En.descData l h).Vmod), γ • v = thetaGR b F ρ γ • v)
    (hA₂ : ∀ v : (En.descData l h).Vmod, v + v = 0)
    (x : VCocycle (En.descData l h) (rhoPrimeGR b F En l h ρ)
      ⧸ vCobRange (En.descData l h) (rhoPrimeGR b F En l h ρ)) :
    H1wR (A := (En.descData l h).Vmod) (markC_R (thetaGR b F ρ)) :=
  h1EquivR (thetaGR b F ρ) hcompat (thetaGR_surjective b F ρ) hA₂
    (h1OfVQuot hcomp x)

omit [TopologicalSpace Y] [DiscreteTopology Y] in
theorem h1CoordGammaR_bijective
    (hcomp : ∀ (γ : GR) (v : (En.descData l h).Vmod),
      γ • v = rho0 (En.descData l h) (rhoPrimeGR b F En l h ρ) γ • v)
    (hcompat : ∀ (γ : GR) (v : (En.descData l h).Vmod), γ • v = thetaGR b F ρ γ • v)
    (hA₂ : ∀ v : (En.descData l h).Vmod, v + v = 0) :
    Function.Bijective (h1CoordGammaR b F En l h ρ hcomp hcompat hA₂) :=
  ⟨(h1EquivR (thetaGR b F ρ) hcompat (thetaGR_surjective b F ρ) hA₂).injective.comp
      (h1OfVQuot_injective hcomp),
    (h1EquivR (thetaGR b F ρ) hcompat (thetaGR_surjective b F ρ) hA₂).surjective.comp
      (h1OfVQuot_surjective hcomp)⟩

end CoordGammaR

end AffineTLift

end SectionEight

end GQ2

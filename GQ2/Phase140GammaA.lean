import GQ2.Phase140Assembly
import GQ2.WordCohBridge
import GQ2.DualityAssembly
import GQ2.FinitelyGenerated
import GQ2.HalfTorsorGammaA

/-!
# P-16d6e6: the `Γ_A` (140) counting residues

The candidate-source mirrors of the `G_ℚ₂` (140) counting residues of `GQ2/Phase140Local.lean`.
Where the local file counts `#Z¹_{Γ,ρ'}(V)` with `card_Z1_eq` (the 5.16 local Euler characteristic,
axioms B6/B7), here the same count comes from the **candidate duality** `prop_5_15` (`IsSelfDual`)
through the word-complex bridge `z1Equiv : Z1 GA A ≃+ Z1w (markC ρ')` (`WordCohBridge`) — **no
B-axioms on the word side** (the same swap as `RStageGammaA.hZcount_gammaA`).

* **`hZcard_gammaA`** — `#Z¹_{Γ_A,ρ'}(V) = #V²`, the `Γ_A` twin of `Phase140Local.hZcard_local`.
  The `#fixedPts` factor is `1` by `card_fixedPts_elemDual_eq_one_of_nontrivial` (`V` is a simple
  `𝔽₂[Y_C]`-module with nontrivial action), exactly as in the local file.

All declarations are std-3 (no B-axioms): the candidate route is axiom-free.
-/

namespace GQ2

namespace Phase140GammaA

open SectionEight AffineTLift CentralObstruction ContCoh WordCohBridge GQ2.FoxH

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
variable {RF : RecursionFrame T Blk}
variable (b : ContinuousMonoidHom GammaA ↥boundarySubgroup) (F : BoundaryFrame H E)
  (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)

/-- **`hZcard` for `Γ_A`** — `#Z¹_{Γ_A,ρ'}(V) = #V²`.  Mirror of `Phase140Local.hZcard_local` with
the candidate count: the `VCocycle ≃ Z¹_cont(Γ_A, V)` bridge (structurally `Γ`-generic, copied
from the local file), then `z1Equiv` + `prop_5_15` clause 2 (`#Z1w = #V²·#fixedPts`) instead of
`card_Z1_eq`, and the `#fixedPts = 1` factor from the simple nontrivial `Y_C`-action
(`card_fixedPts_elemDual_eq_one_of_nontrivial`).

`hnt` (the nontrivial `Y_C`-action) is REQUIRED — in the `#V = 2 ∧ Y_C = 1` corner
`#(V^∨)^{Y_C} = 2 ≠ 1` and the identity is false; it is discharged at the capstone from the
block's chief-factor structure (same amendment as the local file). -/
theorem hZcard_gammaA
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v)
    (ρ : BoundaryLifts b F RF.TC) :
    Nat.card (VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
      = Nat.card En.Vmod * Nat.card En.Vmod := by
  classical
  -- the lower map `θ = ρ.1.1 : Γ_A ↠ Y_C`, retyped against the raw quotient `GA`
  let θ : ContinuousMonoidHom GA RF.YC := ρ.1.1
  have hθs : Function.Surjective ⇑θ := ρ.1.2
  have hroundtrip : ∀ γ : GA,
      rho0 (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) γ = θ γ :=
    fun γ => rho0_descData_rhoPrime b F En l h ρ γ
  -- `En.Vmod` (with its `Y_C`-action) as a `GA`-module through `θ`
  letI : TopologicalSpace En.Vmod := ⊥
  haveI : DiscreteTopology En.Vmod := ⟨rfl⟩
  letI actG : DistribMulAction GA En.Vmod := DistribMulAction.compHom En.Vmod θ.toMonoidHom
  have hcomp : ∀ (γ : GA) (v : En.Vmod), γ • v = θ γ • v := fun _ _ => rfl
  haveI : ContinuousSMul GA En.Vmod := by
    constructor
    have hfac : (fun p : GA × En.Vmod => p.1 • p.2)
        = (fun q : RF.YC × En.Vmod => q.1 • q.2) ∘ (fun p : GA × En.Vmod => (θ p.1, p.2)) := by
      funext p; rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((θ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hA₂ : ∀ v : En.Vmod, v + v = 0 := fun v => Vmod_exp2 (En.descData l h) v
  -- the `VCocycle ≃ Z¹_cont(GA, En.Vmod)` bridge (continuity through the `iV ∘ ofAdd` injection)
  have hequiv : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)
      ≃ ↥(Z1 GA En.Vmod) :=
    { toFun := fun c =>
        ⟨fun γ => (c.c γ : En.Vmod), by
          refine mem_Z1_iff.mpr ⟨?_, ?_⟩
          · have hinj : Function.Injective
                (fun v : En.Vmod => iV (En.descData l h) (Multiplicative.ofAdd v)) :=
              fun a a' haa' => iV_ofAdd_inj (En.descData l h) haa'
            have hlc : IsLocallyConstant
                (fun γ => iV (En.descData l h) (Multiplicative.ofAdd (c.c γ : En.Vmod))) :=
              (IsLocallyConstant.iff_continuous _).mpr c.cont
            exact (IsLocallyConstant.desc (α := En.Vmod) (fun γ => (c.c γ : En.Vmod))
              (fun v : En.Vmod => iV (En.descData l h) (Multiplicative.ofAdd v))
              hlc hinj).continuous
          · intro γ δ
            have H := c.crossed γ δ
            rw [hroundtrip γ] at H
            exact H⟩
      invFun := fun z =>
        { c := fun γ => (z.1 γ : (En.descData l h).Vmod)
          cont := by
            have hc : Continuous (fun v : En.Vmod => iV (En.descData l h) (Multiplicative.ofAdd v)) :=
              continuous_of_discreteTopology
            exact hc.comp (mem_Z1_iff.mp z.2).1
          crossed := fun γ δ => by
            have hz := (mem_Z1_iff.mp z.2).2 γ δ
            rw [hroundtrip γ]
            exact hz }
      left_inv := fun c => by cases c; rfl
      right_inv := fun z => rfl }
  -- the count: `#Z¹(GA, V) = #Z1w(markC θ) = #V² · #fixedPts Y_C (V^∨)` (candidate duality)
  have adm := markC_admissible θ hθs
  rw [Nat.card_congr hequiv, Nat.card_congr (z1Equiv θ hcomp hθs hA₂).toEquiv,
    (GQ2.FoxH.prop_5_15 (markC θ) adm.2.1 adm.2.2.1 adm.1 hA₂ adm.2.2.2).2.1]
  -- `#fixedPts Y_C (V^∨) = 1` (simple module, nontrivial action)
  obtain ⟨v, hv⟩ := hVne
  have hsimpleMod : IsSimpleModTwo RF.YC En.Vmod :=
    ⟨nontrivial_of_ne (0 : En.Vmod) v (Ne.symm hv), fun W hW => hsimple W (fun g w hw => hW g w hw)⟩
  rw [card_fixedPts_elemDual_eq_one_of_nontrivial hsimpleMod hnt, mul_one, pow_two]

end Phase140GammaA

end GQ2

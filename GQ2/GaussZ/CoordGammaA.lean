import GQ2.GaussZ.Local
import GQ2.Phase140.GammaA

/-!
# P-16d6e4aA-1: the `Γ_A` (83)-coordinates — `Z¹⧸B¹` in word generator coordinates

Route W brick **A-1** (`docs/p16d6e4aA-gammaA-gauss-design.md` §2): the e6 Stage-0 bridge
as reusable per-`ρ` declarations, composed with the banked degree-1 word comparison
(`WordCohBridge.h1Equiv`) into the generator-coordinate model of the `Γ_A` Gauss domain:

    `h1CoordGammaA : Z¹_{Γ_A,ρ'}(V) ⧸ B¹ → H¹_w (markC θ)`      (`θ = ρ.1.1`),  bijective,

so A-3 can evaluate the descended `Q̄⁰` as an explicit `𝔽₂`-function of word-cocycle
classes (`Fin 4 → V` generator tuples).  Contents:

* `rhoPrimeGA`/`thetaGA` — the `GammaA → GA` retypes of the two lower maps (the e6 Stage-0
  idiom as top-level declarations), with `thetaGA_surjective` and the roundtrip
  `roundtripGA`; all A-lane objects live uniformly at `GA`, with ONE defeq-bridge to the
  `GammaA`-spelled `GaussZResidue` statement at the A-4 finale;
* `coordHcomp_of_hcompat` — the `h1OfVQuot` compatibility from the `θ`-compatibility
  (callers hold the latter as `fun _ _ => rfl` under the `compHom (thetaGA …)` letI-pack,
  the `GaussZFinal` per-`ρ` idiom);
* `finite_vcocycle_gammaA` — `Z¹` finiteness, σ-free from `Phase140GammaA.hZcard_gammaA`;
* `hfix_of_simple_nt` — the **`hnt`-variant** of `GaussZReduction.hfix_of_simple`:
  `V^{C₀} = 0` from `ρ'`-surjectivity + `hsimple` + `hnt` alone — the `W = ⊤` branch
  contradicts `hnt` directly, so the NON-block-derivable `hfaith` (the P-17i flag) and the
  `[Nontrivial C0]` instance are both dropped; the A-lane runs entirely on the `prop_8_9`
  ledger hypotheses;
* `h1CoordGammaA` + `h1CoordGammaA_bijective` + `card_H1w_gammaA` (`#H¹_w = #V`).

All std-3 (no B-axioms).  Consumed by A-3 (the explicit relator quadratic) and A-4 (form
identification + `gaussZResidue_gammaA_*`); A-2 (the `iotaB` relator-evaluation rule) is
independent.
-/

namespace GQ2

namespace SectionEight

namespace AffineTLift

open CentralObstruction ContCoh WordCohBridge FoxH

/-! ## The `hnt`-variant of the fixed-point freeness  (generic; drops `hfaith`) -/

section HfixNt

variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg}
variable {DD : DescData D}
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
variable {ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)}

omit [DiscreteTopology Bg] in
/-- **`V^{C₀} = 0` from the ledger hypotheses alone** — the `hnt`-variant of
`GaussZReduction.hfix_of_simple`: faithfulness is NOT needed (nor block-derivable — the
P-17i coordination flag); in the `W = ⊤` branch every `C₀`-element acts trivially,
contradicting `hnt` directly. -/
theorem hfix_of_simple_nt
    (hsurj : Function.Surjective (fun γ : Γ => rho0 DD ρ γ))
    (hsimple : ∀ W : AddSubgroup DD.Vmod,
      (∀ g : DD.C0, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hnt : ∃ (g : DD.C0) (v : DD.Vmod), g • v ≠ v)
    (v : DD.Vmod) (hv : ∀ γ : Γ, rho0 DD ρ γ • v = v) : v = 0 := by
  -- `v` is fixed by all of `C₀` (surjectivity of `ρ'`)
  have hvC : ∀ cc : DD.C0, cc • v = v := by
    intro cc
    obtain ⟨γ, hγ⟩ := hsurj cc
    rw [← hγ]; exact hv γ
  -- the fixed submodule
  let W : AddSubgroup DD.Vmod :=
    { carrier := {w | ∀ cc : DD.C0, cc • w = w}
      zero_mem' := fun cc => smul_zero cc
      add_mem' := fun {a b} ha hb cc => by rw [smul_add, ha cc, hb cc]
      neg_mem' := fun {a} ha cc => by rw [smul_neg, ha cc] }
  have hWinv : ∀ (g : DD.C0), ∀ w ∈ W, g • w ∈ W := fun g w hw cc => by
    show cc • g • w = g • w
    rw [hw g, hw cc]
  rcases hsimple W hWinv with hbot | htop
  · rw [← AddSubgroup.mem_bot, ← hbot]; exact hvC
  · -- `W = ⊤` ⟹ every `cc` acts trivially — against `hnt`
    exfalso
    obtain ⟨g, w, hgw⟩ := hnt
    exact hgw ((by rw [htop]; exact AddSubgroup.mem_top w : w ∈ W) g)

end HfixNt

/-! ## The per-`ρ` retypes and the coordinate bijection -/

section CoordGammaA

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
variable {RF : RecursionFrame T Blk}
variable (b : ContinuousMonoidHom GammaA ↥boundarySubgroup) (F : BoundaryFrame H E)
  (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR) (ρ : BoundaryLifts b F RF.TC)

/-- The lower map `ρ' : Γ_A → Y_B ⧸ M`, retyped against the raw quotient `GA` (the e6
Stage-0 idiom as a declaration). -/
noncomputable def rhoPrimeGA : ContinuousMonoidHom GA (RF.YB ⧸ (En.radData l h).M) :=
  RF.rhoPrime b F (En.radData l h) rfl ρ

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **`Z¹` is finite** — σ-free from the e6 count (`Phase140GammaA.hZcard_gammaA`). -/
theorem finite_vcocycle_gammaA
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v) :
    Finite (VCocycle (En.descData l h) (rhoPrimeGA b F En l h ρ)) :=
  (Nat.card_ne_zero.mp (by
    show Nat.card (VCocycle (En.descData l h)
      (RF.rhoPrime b F (En.radData l h) rfl ρ)) ≠ 0
    rw [Phase140GammaA.hZcard_gammaA b F En l h hsimple hVne hnt ρ]
    exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')).2

variable [TopologicalSpace (En.descData l h).Vmod] [DiscreteTopology (En.descData l h).Vmod]
  [DistribMulAction GA (En.descData l h).Vmod] [ContinuousSMul GA (En.descData l h).Vmod]
  [DistribMulAction RF.YC (En.descData l h).Vmod]
  [Finite (En.descData l h).Vmod]

/-- The boundary-lift head `θ = ρ.1.1 : Γ_A → Y_C`, retyped against `GA` — the marking map
of the word complex (`markC (thetaGA …)`). -/
noncomputable def thetaGA : ContinuousMonoidHom GA RF.YC :=
  ρ.1.1

omit [TopologicalSpace Y] [DiscreteTopology Y] in
theorem thetaGA_surjective : Function.Surjective ⇑(thetaGA b F ρ) :=
  ρ.1.2

omit [TopologicalSpace Y] [DiscreteTopology Y]
  [TopologicalSpace (En.descData l h).Vmod] [DiscreteTopology (En.descData l h).Vmod]
  [DistribMulAction GA (En.descData l h).Vmod] [ContinuousSMul GA (En.descData l h).Vmod]
  [DistribMulAction RF.YC (En.descData l h).Vmod] [Finite (En.descData l h).Vmod] in
/-- The roundtrip `rho0 ∘ rhoPrime = θ` over `GA` (`rho0_descData_rhoPrime`, retyped).
Callers derive the `h1OfVQuot`-compatibility from their letI-pack through this:
`hcomp γ v := congrArg (· • v) (roundtripGA … γ).symm`-composed with the `compHom`-`rfl`. -/
theorem roundtripGA : ∀ γ : GA,
    rho0 (En.descData l h) (rhoPrimeGA b F En l h ρ) γ = thetaGA b F ρ γ :=
  fun γ => rho0_descData_rhoPrime b F En l h ρ γ


/-- **The A-1 deliverable**: the generator-coordinate model of the `Γ_A` Gauss domain —
the quotient bijection `h1OfVQuot` into `H¹(Γ_A, V)` composed with the banked degree-1
word comparison `h1Equiv` into `H¹_w(markC θ)` (classes of `Fin 4 → V` generator tuples).
The two compatibility hypotheses are the same fact at the two actions the banked pieces
pin (`h1OfVQuot`: the `DescData`-internal `actVmod`; `h1Equiv`: the ambient `Y_C`-action):
under the caller's letI-pack (`compHom (thetaGA …)` + the `actVmod` re-key) both are
`rfl`-flavored (`hcompat := fun _ _ => rfl`; `hcomp` via `roundtripGA`). -/
noncomputable def h1CoordGammaA
    (hcomp : ∀ (γ : GA) (v : (En.descData l h).Vmod),
      γ • v = rho0 (En.descData l h) (rhoPrimeGA b F En l h ρ) γ • v)
    (hcompat : ∀ (γ : GA) (v : (En.descData l h).Vmod), γ • v = thetaGA b F ρ γ • v)
    (hA₂ : ∀ v : (En.descData l h).Vmod, v + v = 0)
    (x : VCocycle (En.descData l h) (rhoPrimeGA b F En l h ρ)
      ⧸ vCobRange (En.descData l h) (rhoPrimeGA b F En l h ρ)) :
    H1w (A := (En.descData l h).Vmod) (markC (thetaGA b F ρ)) :=
  h1Equiv (thetaGA b F ρ) hcompat (thetaGA_surjective b F ρ) hA₂
    (h1OfVQuot hcomp x)

omit [TopologicalSpace Y] [DiscreteTopology Y] in
theorem h1CoordGammaA_bijective
    (hcomp : ∀ (γ : GA) (v : (En.descData l h).Vmod),
      γ • v = rho0 (En.descData l h) (rhoPrimeGA b F En l h ρ) γ • v)
    (hcompat : ∀ (γ : GA) (v : (En.descData l h).Vmod), γ • v = thetaGA b F ρ γ • v)
    (hA₂ : ∀ v : (En.descData l h).Vmod, v + v = 0) :
    Function.Bijective (h1CoordGammaA b F En l h ρ hcomp hcompat hA₂) :=
  ⟨(h1Equiv (thetaGA b F ρ) hcompat (thetaGA_surjective b F ρ) hA₂).injective.comp
      (h1OfVQuot_injective hcomp),
    (h1Equiv (thetaGA b F ρ) hcompat (thetaGA_surjective b F ρ) hA₂).surjective.comp
      (h1OfVQuot_surjective hcomp)⟩


end CoordGammaA

end AffineTLift

end SectionEight

end GQ2

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLSimpleDualReduction
import GQ2.Dyadic.Instances.GammaLH2Surjectivity

/-!
# One-map simple H² surjectivity for the improved L presentation

`GammaLH2Surjectivity` asks separately for surjectivity of the canonical flexible `H²` maps
at a simple module and its elementary dual.  Since `isSimpleModTwo_elemDual` proves that the
dual is simple, one map-shaped hypothesis quantified over all simple modules supplies both
clauses.

As in the cardinal version, there is an action-instance qualification.  Pulling the
contragredient `C`-action back through `rho` and dualizing the pulled-back action are
propositionally, but not definitionally, equal.  In the absence of a continuous-cohomology
action-transport equivalence, the single-map provider therefore quantifies over discrete
`GammaL`-actions compatible with `rho`.  This is formally stronger than only the strictly
canonical single-action hypothesis; no equivalence between those formulations is claimed.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH
open ContCoh
open GQ2.Dyadic.Count
open GQ2.Dyadic.Certificates.LSqStokes

/-- Continuity of a discrete coefficient action compatible with a finite quotient. -/
private theorem continuousSMul_comp_finite_single_surjective
    {G C A : Type*} [Monoid G] [TopologicalSpace G]
    [Monoid C] [TopologicalSpace C] [DiscreteTopology C]
    [TopologicalSpace A] [DiscreteTopology A] [SMul C A]
    (rho : ContinuousMonoidHom G C) [SMul G A]
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a) : ContinuousSMul G A := by
  constructor
  have hfac : (fun p : G × A ↦ p.1 • p.2) =
      (fun p : C × A ↦ p.1 • p.2) ∘ (fun p : G × A ↦ (rho p.1, p.2)) := by
    funext p
    exact hcompat p.1 p.2
  rw [hfac]
  exact continuous_of_discreteTopology.comp
    ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)

section UniformSingleSurjectivity

variable {h q : ℕ} {C : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "eC" => omega2Exp (4 * Monoid.exponent C)
local notation "wC" => lSqFam h q eC

/-- Surjectivity of the one canonical flexible `H²` comparison selected by a compatible
source action. -/
noncomputable abbrev UniformSimpleH2SurjectiveSingleAt
    (rho : ContinuousMonoidHom GammaL C)
    (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V]
    [TopologicalSpace V] [DiscreteTopology V]
    [DistribMulAction GammaL V] [ContinuousSMul GammaL V]
    (hcompat : ∀ (g : GammaL) (v : V), g • v = rho g • v)
    (hV₂ : ∀ v : V, v + v = 0) : Prop :=
  Function.Surjective
    (lModuleH2WordFlexible rho hcompat hV₂ (lUniform_wordLift_resolver hV₂))

/-- One map-shaped surjectivity hypothesis, quantified over simple modules and compatible
discrete source actions. -/
noncomputable abbrev UniformSimpleH2SurjectiveSingleProvider
    (rho : ContinuousMonoidHom GammaL C) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V]
    [TopologicalSpace V] [DiscreteTopology V]
    [DistribMulAction GammaL V] [ContinuousSMul GammaL V]
    (hcompat : ∀ (g : GammaL) (v : V), g • v = rho g • v)
    (hV₂ : ∀ v : V, v + v = 0),
      IsSimpleModTwo C V → UniformSimpleH2SurjectiveSingleAt rho V hcompat hV₂

/-- The compatible-action single-map provider supplies the existing paired canonical-map
provider. -/
theorem uniformSimpleH2SurjectiveProvider_of_single
    (rho : ContinuousMonoidHom GammaL C)
    (hsurj : UniformSimpleH2SurjectiveSingleProvider rho) :
    UniformSimpleH2SurjectiveProvider rho := by
  intro V _ _ _ hV₂ hsimple
  letI : TopologicalSpace V := ⊥
  letI : DiscreteTopology V := ⟨rfl⟩
  letI : DistribMulAction GammaL V :=
    DistribMulAction.compHom V rho.toMonoidHom
  letI : ContinuousSMul GammaL V :=
    continuousSMul_comp_finite_single_surjective rho (fun _ _ ↦ rfl)
  letI : TopologicalSpace (ElemDual V) := ⊥
  letI : DiscreteTopology (ElemDual V) := ⟨rfl⟩
  letI : ContinuousSMul GammaL (ElemDual V) :=
    continuousSMul_comp_finite_single_surjective rho (fun g lam ↦ by
      apply ElemDual.ext
      intro v
      rw [ElemDual.smul_apply, ElemDual.smul_apply]
      change lam (rho (g⁻¹) • v) = lam ((rho g)⁻¹ • v)
      rw [map_inv])
  have hcompatV : ∀ (g : GammaL) (v : V), g • v = rho g • v := fun _ _ ↦ rfl
  have hcompatDual : ∀ (g : GammaL) (lam : ElemDual V), g • lam = rho g • lam := by
    intro g lam
    apply ElemDual.ext
    intro v
    rw [ElemDual.smul_apply, ElemDual.smul_apply]
    change lam (rho (g⁻¹) • v) = lam ((rho g)⁻¹ • v)
    rw [map_inv]
  exact
    ⟨hsurj V hcompatV hV₂ hsimple,
      hsurj (ElemDual V) hcompatDual (fun lam ↦ lam.add_self_eq_zero)
        (isSimpleModTwo_elemDual hV₂ hsimple)⟩

/-- A single-map surjectivity supply at every finite quotient of `GammaL`. -/
noncomputable abbrev UniformSimpleH2SurjectiveSingleSupply : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom GammaL C),
      UniformSimpleH2SurjectiveSingleProvider rho

/-- The single-map supply generates the established paired surjectivity supply. -/
theorem uniformSimpleH2SurjectiveSupply_of_single
    (hsurj : UniformSimpleH2SurjectiveSingleSupply (h := h) (q := q)) :
    UniformSimpleH2SurjectiveSupply (h := h) (q := q) := by
  intro C _ _ _ _ rho
  exact uniformSimpleH2SurjectiveProvider_of_single rho (hsurj C rho)

/-- End-to-end corrected L regression from Tate duality and one compatible-action map-shaped
surjectivity hypothesis on every simple coefficient. -/
theorem exactLiftingRN_of_uniformSingleH2Surjective_tateDuality
    [DistribMulAction GammaL (MuN 2)] [ContinuousSMul GammaL (MuN 2)]
    (hq : Even q) (D : TateDualityG GammaL 2)
    (hsurj : UniformSimpleH2SurjectiveSingleSupply (h := h) (q := q))
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (gamma h q) (2 * h + 1) q P nuP
      (standardNumerics (2 * h + 1)) :=
  exactLiftingRN_of_uniformH2Surjective_tateDuality hq D
    (uniformSimpleH2SurjectiveSupply_of_single hsurj) nuP

end UniformSingleSurjectivity

end

end GQ2.Dyadic.LSquare

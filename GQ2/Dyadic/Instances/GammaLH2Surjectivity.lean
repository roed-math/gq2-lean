/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLSimpleSource

/-!
# The map-level H² defect for the improved L presentation

`GammaLSimpleSource` isolates the remaining continuous-to-word input as two cardinal
equalities for every simple elementary coefficient.  This file exposes the sharper canonical
interface: surjectivity of the already-constructed flexible `H²` comparison maps.  Those maps
are unconditionally injective, so surjectivity produces the existing cardinal provider and all
of its exact-lifting consequences.

The uniform provider is deliberately paired, once for `V` and once for `ElemDual V`.  Reducing
it to one map per simple module additionally needs closure of simple modules under elementary
duality; that independent representation-theoretic bridge is not duplicated here.

No source/cardinality equivalence is assumed or used to define the maps.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG
open GQ2.Dyadic.Certificates.LSqStokes

section UniformSurjectivity

variable {h q : ℕ} {C : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "levelC" => 4 * Monoid.exponent C
local notation "eC" => omega2Exp levelC
local notation "wC" => lSqFam h q eC

/-- Continuity for a discrete coefficient action pulled back through a finite discrete
quotient.  This is local plumbing for the canonical source actions below. -/
private theorem continuousSMul_comp_finite_surjective
    {G D A : Type} [Monoid G] [TopologicalSpace G]
    [Monoid D] [TopologicalSpace D] [DiscreteTopology D]
    [TopologicalSpace A] [DiscreteTopology A] [SMul D A]
    (rho : ContinuousMonoidHom G D) [SMul G A]
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a) : ContinuousSMul G A := by
  constructor
  have hfac : (fun p : G × A ↦ p.1 • p.2) =
      (fun p : D × A ↦ p.1 • p.2) ∘ (fun p : G × A ↦ (rho p.1, p.2)) := by
    funext p
    exact hcompat p.1 p.2
  rw [hfac]
  exact continuous_of_discreteTopology.comp
    ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)

omit [TopologicalSpace C] [DiscreteTopology C] in
/-- The common coefficient-independent L word resolves every elementary split target.

The tighter split-target bound is `2 * exponent C`; the extra factor two aligns this map with
the Heisenberg resolver and hence with the fixed word used by simple devissage. -/
theorem lUniform_wordLift_resolver
    {A : Type} [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    ResolvesAt
      (gammaFam (2 * h + 1) q (Words.LSq.lSqW h)) wC (WordLift A C) := by
  have hbase : ∀ g : C, orderOf g ∣ Monoid.exponent C :=
    fun g ↦ Monoid.order_dvd_exponent g
  have horder : ∀ p : WordLift A C, orderOf p ∣ levelC := fun p ↦
    (WordLift.orderOf_dvd_two_mul hA₂ hbase p).trans ⟨2, by ring⟩
  exact resolvesAt_lSqFam (fourMulExponent_ne_zero_and_even C).1 horder h q

/-- The exact map-level `H²` defect at one simple coefficient.

Both displayed maps are the canonical flexible continuous-to-word comparisons at the single
uniform word `wC`.  All coefficient topologies and source actions are installed canonically.
The two clauses remain separate so this interface does not assume dual-simplicity closure. -/
noncomputable abbrev UniformSimpleH2SurjectiveAt
    (rho : ContinuousMonoidHom GammaL C)
    (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V]
    (hV₂ : ∀ v : V, v + v = 0) : Prop := by
  letI : TopologicalSpace V := ⊥
  letI : DiscreteTopology V := ⟨rfl⟩
  letI : DistribMulAction GammaL V :=
    DistribMulAction.compHom V rho.toMonoidHom
  letI : ContinuousSMul GammaL V :=
    continuousSMul_comp_finite_surjective rho (fun _ _ ↦ rfl)
  letI : TopologicalSpace (ElemDual V) := ⊥
  letI : DiscreteTopology (ElemDual V) := ⟨rfl⟩
  letI : ContinuousSMul GammaL (ElemDual V) :=
    continuousSMul_comp_finite_surjective rho (fun g lam ↦ by
      apply ElemDual.ext
      intro v
      rw [ElemDual.smul_apply, ElemDual.smul_apply]
      change lam (rho (g⁻¹) • v) = lam ((rho g)⁻¹ • v)
      rw [map_inv])
  let hcompatV : ∀ (g : GammaL) (v : V), g • v = rho g • v := fun _ _ ↦ rfl
  let hcompatDual : ∀ (g : GammaL) (lam : ElemDual V), g • lam = rho g • lam := by
    intro g lam
    apply ElemDual.ext
    intro v
    rw [ElemDual.smul_apply, ElemDual.smul_apply]
    change lam (rho (g⁻¹) • v) = lam ((rho g)⁻¹ • v)
    rw [map_inv]
  exact
    Function.Surjective
        (lModuleH2WordFlexible rho hcompatV hV₂ (lUniform_wordLift_resolver hV₂)) ∧
      Function.Surjective
        (lModuleH2WordFlexible rho hcompatDual
          (fun lam : ElemDual V ↦ lam.add_self_eq_zero)
          (lUniform_wordLift_resolver (fun lam : ElemDual V ↦ lam.add_self_eq_zero)))

/-- The uniform map-level residue at one finite quotient, quantified only over simple
elementary modules and always at the same coefficient-independent word. -/
noncomputable abbrev UniformSimpleH2SurjectiveProvider
    (rho : ContinuousMonoidHom GammaL C) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V]
    (hV₂ : ∀ v : V, v + v = 0),
      IsSimpleModTwo C V → UniformSimpleH2SurjectiveAt rho V hV₂

/-- Paired surjectivity of the canonical flexible maps implies the paired cardinal equalities
used by the existing no-Euler source constructor. -/
theorem uniformSimpleH2CardAt_of_surjective
    (rho : ContinuousMonoidHom GammaL C)
    (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V]
    (hV₂ : ∀ v : V, v + v = 0)
    (hsurj : UniformSimpleH2SurjectiveAt rho V hV₂) :
    UniformSimpleH2CardAt rho V := by
  letI : TopologicalSpace V := ⊥
  letI : DiscreteTopology V := ⟨rfl⟩
  letI : DistribMulAction GammaL V :=
    DistribMulAction.compHom V rho.toMonoidHom
  letI : ContinuousSMul GammaL V :=
    continuousSMul_comp_finite_surjective rho (fun _ _ ↦ rfl)
  letI : TopologicalSpace (ElemDual V) := ⊥
  letI : DiscreteTopology (ElemDual V) := ⟨rfl⟩
  letI : ContinuousSMul GammaL (ElemDual V) :=
    continuousSMul_comp_finite_surjective rho (fun g lam ↦ by
      apply ElemDual.ext
      intro v
      rw [ElemDual.smul_apply, ElemDual.smul_apply]
      change lam (rho (g⁻¹) • v) = lam ((rho g)⁻¹ • v)
      rw [map_inv])
  let hcompatV : ∀ (g : GammaL) (v : V), g • v = rho g • v := fun _ _ ↦ rfl
  let hcompatDual : ∀ (g : GammaL) (lam : ElemDual V), g • lam = rho g • lam := by
    intro g lam
    apply ElemDual.ext
    intro v
    rw [ElemDual.smul_apply, ElemDual.smul_apply]
    change lam (rho (g⁻¹) • v) = lam ((rho g)⁻¹ • v)
    rw [map_inv]
  obtain ⟨hsurjV, hsurjDual⟩ := hsurj
  exact
    ⟨lModuleH2_card_eq_wordH2_of_surjective rho hcompatV hV₂
        (lUniform_wordLift_resolver hV₂) hsurjV,
      lModuleH2_card_eq_wordH2_of_surjective rho hcompatDual
        (fun lam : ElemDual V ↦ lam.add_self_eq_zero)
        (lUniform_wordLift_resolver (fun lam : ElemDual V ↦ lam.add_self_eq_zero))
        hsurjDual⟩

/-- The map-level simple provider supplies the existing cardinal provider. -/
theorem uniformSimpleH2CardProvider_of_surjective
    (rho : ContinuousMonoidHom GammaL C)
    (hsurj : UniformSimpleH2SurjectiveProvider rho) :
    UniformSimpleH2CardProvider rho := by
  intro V _ _ _ hV₂ hsimp
  exact uniformSimpleH2CardAt_of_surjective rho V hV₂ (hsurj V hV₂ hsimp)

/-- Paired map-level surjectivity plus Tate duality constructs the fixed-word simple source
provider. -/
noncomputable def uniformSimpleSourceProvider_of_h2Surjective_tateDuality
    [DistribMulAction GammaL (MuN 2)] [ContinuousSMul GammaL (MuN 2)]
    (rho : ContinuousMonoidHom GammaL C) (hq : Even q)
    (D : TateDualityG GammaL 2) (hsurj : UniformSimpleH2SurjectiveProvider rho) :
    UniformSimpleSourceProvider rho hq :=
  uniformSimpleSourceProvider_of_h2Card_tateDuality rho hq D
    (uniformSimpleH2CardProvider_of_surjective rho hsurj)

/-- End-to-end fixed-quotient regression from the canonical map-level `H²` defect. -/
theorem stokesDuality_lUniform_of_h2Surjective_tateDuality
    [DistribMulAction GammaL (MuN 2)] [ContinuousSMul GammaL (MuN 2)]
    (rho : ContinuousMonoidHom GammaL C) (hq : Even q)
    (D : TateDualityG GammaL 2) (hsurj : UniformSimpleH2SurjectiveProvider rho)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality (fun g ↦ rho (genL g)) wC A :=
  stokesDuality_lUniform_of_h2Card_tateDuality rho hq D
    (uniformSimpleH2CardProvider_of_surjective rho hsurj) A hA₂

/-! ## Uniform supply and corrected exact lifting -/

/-- The paired canonical-map surjectivity residue at every finite quotient of `GammaL`. -/
noncomputable abbrev UniformSimpleH2SurjectiveSupply : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom GammaL C),
      UniformSimpleH2SurjectiveProvider rho

/-- A uniform map-level supply gives the cardinal supply expected by the established exact
lifting chain. -/
theorem uniformSimpleH2CardSupply_of_surjective
    (hsurj : UniformSimpleH2SurjectiveSupply (h := h) (q := q)) :
    UniformSimpleH2CardSupply (h := h) (q := q) := by
  intro C _ _ _ _ rho
  exact uniformSimpleH2CardProvider_of_surjective rho (hsurj C rho)

/-- A uniform map-level supply and Tate duality prove the direct-Stokes residue. -/
theorem uniformPushedHsimp_of_h2Surjective_tateDuality
    [DistribMulAction GammaL (MuN 2)] [ContinuousSMul GammaL (MuN 2)]
    (hq : Even q) (D : TateDualityG GammaL 2)
    (hsurj : UniformSimpleH2SurjectiveSupply (h := h) (q := q)) :
    UniformPushedHsimp h q :=
  uniformPushedHsimp_of_h2Card_tateDuality hq D
    (uniformSimpleH2CardSupply_of_surjective hsurj)

/-- End-to-end corrected L regression from Tate duality and surjectivity of the canonical
continuous-to-word `H²` maps on simple coefficients. -/
theorem exactLiftingRN_of_uniformH2Surjective_tateDuality
    [DistribMulAction GammaL (MuN 2)] [ContinuousSMul GammaL (MuN 2)]
    (hq : Even q) (D : TateDualityG GammaL 2)
    (hsurj : UniformSimpleH2SurjectiveSupply (h := h) (q := q))
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (gamma h q) (2 * h + 1) q P nuP
      (standardNumerics (2 * h + 1)) :=
  exactLiftingRN_of_uniformH2Card_tateDuality hq D
    (uniformSimpleH2CardSupply_of_surjective hsurj) nuP

end UniformSurjectivity

end

end GQ2.Dyadic.LSquare

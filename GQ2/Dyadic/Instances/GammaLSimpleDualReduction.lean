/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.DimAssembly
import GQ2.Dyadic.Instances.GammaLSimpleSource

/-!
# Dual simplicity and a one-cardinality source interface

The source-facing `UniformSimpleH2CardProvider` records the source-to-word `H²` cardinality
for both a simple `F₂[C]`-module `V` and its contragredient dual `Vᵛ`.  Since the dual of a
finite elementary simple module is again simple, one can apply a *single-shaped* equality to
`V` and to `Vᵛ`.

There is one formal typeclass subtlety.  Pulling the contragredient `C`-action on `Vᵛ` back
through `rho` is propositionally equal, but not definitionally equal, to dualizing the pulled-back
action on `V` (the comparison uses `map_inv`).  The repository does not currently expose an
action-change equivalence for continuous `H²`.  Accordingly the single provider below quantifies
over discrete `GammaL`-actions *compatible* with `rho`; it can be specialized to both of those
instances directly.  This is a cleaner one-equality interface, but its action-polymorphic
quantifier is a formal strengthening of merely assuming the canonical primal equality.  We do
not claim that the canonical single hypothesis alone implies the paired provider without an
additional action-transport lemma.

This file packages that algebraic reduction and threads it through the uniform L exact-lifting
regression.  The existing paired APIs remain available unchanged.
-/

namespace GQ2

namespace FoxH

open GQ2.DimAssembly

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V] [Finite V]

/-- The contragredient dual of a finite elementary simple `C`-module is simple.

The stable-subgroup argument is `DimAssembly.dual_simple`; the extra point here is the
nontriviality conjunct in `IsSimpleModTwo`, obtained from functional separation. -/
theorem isSimpleModTwo_elemDual (hV₂ : ∀ v : V, v + v = 0)
    (hsimple : IsSimpleModTwo C V) : IsSimpleModTwo C (ElemDual V) := by
  constructor
  · haveI : Nontrivial V := hsimple.1
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨lam, hlam⟩ := elemDual_separates hV₂ hv
    refine ⟨lam, 0, ?_⟩
    intro h
    apply hlam
    exact DFunLike.congr_fun h v
  · intro W hW
    exact dual_simple hV₂ hsimple.2 W (fun g lam hlam => hW g lam hlam)

end FoxH

namespace Dyadic.LSquare

noncomputable section

open GQ2.FoxH
open ContCoh
open GQ2.Dyadic.Count
open GQ2.Dyadic.Certificates.LSqStokes

/-- Continuity of an action pulled back from a finite discrete quotient. -/
private theorem continuousSMul_comp_finite_single
    {G C A : Type*} [Monoid G] [TopologicalSpace G]
    [Monoid C] [TopologicalSpace C] [DiscreteTopology C]
    [TopologicalSpace A] [DiscreteTopology A] [SMul C A]
    (rho : ContinuousMonoidHom G C) [SMul G A]
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a) : ContinuousSMul G A := by
  constructor
  have hfac : (fun p : G × A => p.1 • p.2) =
      (fun p : C × A => p.1 • p.2) ∘ (fun p : G × A => (rho p.1, p.2)) := by
    funext p
    exact hcompat p.1 p.2
  rw [hfac]
  exact continuous_of_discreteTopology.comp
    ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)

section UniformSingleProvider

variable {h q : ℕ}
variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "eC" => omega2Exp (4 * Monoid.exponent C)
local notation "wC" => lSqFam h q eC

/-- One source-to-word `H²` cardinal equality at the coefficient-independent L word.

Unlike `UniformSimpleH2CardAt`, this proposition has no separately stated dual entry. -/
noncomputable abbrev UniformSimpleH2CardSingleAt
    (rho : ContinuousMonoidHom GammaL C)
    (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V]
    [TopologicalSpace V] [DiscreteTopology V]
    [DistribMulAction GammaL V] [ContinuousSMul GammaL V] : Prop :=
  Nat.card (H2 GammaL V) =
    Nat.card (WordH2 (fun g => rho (genL g)) wC V)

/-- The single-cardinality residue, universally quantified over simple elementary
`F₂[C]`-modules and over discrete source actions compatible with `rho`.

The compatible-action binder is intentional: it covers both the pulled-back action on `V` and
the induced contragredient action on `Vᵛ`, which are propositionally compatible with `rho` but
not definitionally the same action construction. -/
noncomputable abbrev UniformSimpleH2CardSingleProvider
    (rho : ContinuousMonoidHom GammaL C) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V]
    [TopologicalSpace V] [DiscreteTopology V]
    [DistribMulAction GammaL V] [ContinuousSMul GammaL V],
    (∀ (g : GammaL) (v : V), g • v = rho g • v) →
    (∀ v : V, v + v = 0) → IsSimpleModTwo C V → UniformSimpleH2CardSingleAt rho V

omit [Finite C] in
/-- The compatible-action single-cardinality provider generates the paired provider expected
by the existing source-comparison construction. -/
theorem uniformSimpleH2CardProvider_of_single
    (rho : ContinuousMonoidHom GammaL C)
    (hcard : UniformSimpleH2CardSingleProvider rho) :
    UniformSimpleH2CardProvider rho := by
  intro V _ _ _ hV₂ hsimple
  letI : TopologicalSpace V := ⊥
  letI : DiscreteTopology V := ⟨rfl⟩
  letI : DistribMulAction GammaL V :=
    DistribMulAction.compHom V rho.toMonoidHom
  letI : ContinuousSMul GammaL V :=
    continuousSMul_comp_finite_single rho (fun _ _ => rfl)
  letI : TopologicalSpace (ElemDual V) := ⊥
  letI : DiscreteTopology (ElemDual V) := ⟨rfl⟩
  letI : ContinuousSMul GammaL (ElemDual V) :=
    continuousSMul_comp_finite_single rho (fun g lam => by
      apply ElemDual.ext
      intro v
      rw [ElemDual.smul_apply, ElemDual.smul_apply]
      change lam (rho (g⁻¹) • v) = lam ((rho g)⁻¹ • v)
      rw [map_inv])
  have hcompatV : ∀ (g : GammaL) (v : V), g • v = rho g • v := fun _ _ => rfl
  have hcompatDual : ∀ (g : GammaL) (lam : ElemDual V), g • lam = rho g • lam := by
    intro g lam
    apply ElemDual.ext
    intro v
    rw [ElemDual.smul_apply, ElemDual.smul_apply]
    change lam (rho (g⁻¹) • v) = lam ((rho g)⁻¹ • v)
    rw [map_inv]
  constructor
  · exact hcard V hcompatV hV₂ hsimple
  · exact hcard (ElemDual V) hcompatDual (fun lam => lam.add_self_eq_zero)
      (isSimpleModTwo_elemDual hV₂ hsimple)

/-- A uniform supply of one `H²` equality per universally quantified simple coefficient and
finite quotient. -/
noncomputable abbrev UniformSimpleH2CardSingleSupply : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom GammaL C),
      UniformSimpleH2CardSingleProvider rho

/-- The single-cardinality supply generates the existing paired uniform supply. -/
theorem uniformSimpleH2CardSupply_of_single
    (hcard : UniformSimpleH2CardSingleSupply (h := h) (q := q)) :
    UniformSimpleH2CardSupply (h := h) (q := q) := by
  intro C _ _ _ _ rho
  exact uniformSimpleH2CardProvider_of_single rho (hcard C rho)

/-- End-to-end corrected L regression with one compatible-action simple-module `H²`
cardinality schema, rather than a primitive pair of primal and dual hypotheses. -/
theorem exactLiftingRN_of_uniformSingleH2Card_tateDuality
    [DistribMulAction GammaL (MuN 2)] [ContinuousSMul GammaL (MuN 2)]
    (hq : Even q) (D : TateDualityG GammaL 2)
    (hcard : UniformSimpleH2CardSingleSupply (h := h) (q := q))
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (gamma h q) (2 * h + 1) q P nuP
      (standardNumerics (2 * h + 1)) :=
  exactLiftingRN_of_uniformH2Card_tateDuality hq D
    (uniformSimpleH2CardSupply_of_single hcard) nuP

end UniformSingleProvider

end

end Dyadic.LSquare

end GQ2

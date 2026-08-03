/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoRelationModule
import GQ2.Dyadic.Instances.GammaLRelatorRealization

/-!
# Uniform resolution for L relation-module transgression

The relation-module transgression theorem has two explicit resolver inputs.  For the improved
L presentation at the fixed level `4 * exponent C`, both are automatic on elementary
coefficients:

* the split target `WordLift A C` is handled by `lUniform_wordLift_resolver`;
* every twisted target `ModuleExt z`, including every extension transgressed from a relation
  character, has the same order bound and is handled by the same `resolvesAt_lSqFam` API.

Thus relation-module evaluation surjectivity at a generating finite L target feeds finite
cocycle realization with no residual resolver assumption.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.Certificates.LSqStokes

section UniformModuleExtensionResolver

variable {h q : ℕ} {C A : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [DistribMulAction C A] [Finite A]

local notation "WL" => gammaFam (2 * h + 1) q (Words.LSq.lSqW h)
local notation "levelC" => 4 * Monoid.exponent C
local notation "wC" => lSqFam h q (omega2Exp levelC)

omit [TopologicalSpace C] [DiscreteTopology C] in
/-- The coefficient-independent improved L word resolves every normalized twisted module
extension over `C`.  The proof is uniform in the cocycle, so it applies directly to the
Schreier cocycle transgressed from any relation-module character. -/
theorem lUniform_moduleExt_resolver
    (hA₂ : ∀ a : A, a + a = 0) (z : ModuleTwoCocycle C A) :
    ResolvesAt WL wC (ModuleExt z) := by
  have hbase : ∀ g : C, orderOf g ∣ Monoid.exponent C :=
    fun g ↦ Monoid.order_dvd_exponent g
  have horder : ∀ p : ModuleExt z, orderOf p ∣ levelC := fun p ↦
    (ModuleExt.orderOf_dvd_two_mul z hA₂ hbase p).trans ⟨2, by ring⟩
  exact resolvesAt_lSqFam (fourMulExponent_ne_zero_and_even C).1 horder h q

end UniformModuleExtensionResolver

section RelationModuleClosure

variable {h q : ℕ} {C A : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction ((gamma h q : Type)) A]
  [ContinuousSMul ((gamma h q : Type)) A]
  [DistribMulAction C A]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "WL" => gammaFam (2 * h + 1) q (Words.LSq.lSqW h)
local notation "levelC" => 4 * Monoid.exponent C
local notation "wC" => lSqFam h q (omega2Exp levelC)

omit [TopologicalSpace A] [IsTopologicalAddGroup A] [DiscreteTopology A]
  [DistribMulAction GammaL A] [ContinuousSMul GammaL A] in
/-- At a surjective finite L target, relation-module evaluation surjectivity is now the only
input to finite cocycle relator realization.  In particular, the split and transgressed
extension resolver hypotheses of `relatorRealization_of_relationModule` are discharged by the
two uniform L resolver theorems. -/
theorem lRelatorRealization_of_relationModule
    (rho : ContinuousMonoidHom GammaL C) (hrho : Function.Surjective rho)
    (hA₂ : ∀ a : A, a + a = 0)
    (hRM : RelationModuleRelatorSurjective (A := A) wC
      (lUniform_rel_death rho)) :
    ∀ r : Fin 2 → A, ∃ z : ModuleTwoCocycle C A,
      (fun k => moduleRel (WL k) (fun i ↦ rho (genL i)) z) - r ∈
        (heisD1 (A := A) (fun i ↦ rho (genL i)) wC).range := by
  exact relatorRealization_of_relationModule WL wC
    (lUniform_wordLift_resolver hA₂)
    (closure_range_lower_eq_top rho (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR
        (2 * h + 1) q (Words.LSq.lSqW h)) hrho)
    (lUniform_rel_death rho) hRM
    (fun _ ↦ lUniform_moduleExt_resolver hA₂ _)

end RelationModuleClosure

end

end GQ2.Dyadic.LSquare

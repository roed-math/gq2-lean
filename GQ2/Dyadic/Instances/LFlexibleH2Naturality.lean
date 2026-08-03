/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.LFlexibleH2
import GQ2.Dyadic.Count.HTwoModuleNaturality

/-!
# Coefficient naturality of the flexible L degree-two comparison

The global relator obstruction is already natural under equivariant coefficient maps.
This file descends that representative statement through the continuous and word
degree-two quotients, producing the comparison square required by coefficient
dévissage.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG

section WordMap

variable {ι ρ C A B : Type*} [Group C]
  [AddCommGroup A] [DistribMulAction C A]
  [AddCommGroup B] [DistribMulAction C B]

/-- A coefficient map induces a map on the degree-two word cokernel. -/
noncomputable def moduleWordH2Map (c : ι → C) (w : ρ → FreeGroup ι) (f : A →+ B)
    (hfC : ∀ (g : C) (a : A), f (g • a) = g • f a) :
    WordH2 c w A →+ WordH2 c w B :=
  stokesH2Map
    (dX₁ := heisD1 (A := A) c w) (dY₁ := heisD1 (A := B) c w)
    (φ₁ := stokesPi ι f) (φ₂ := stokesPi ρ f) (heisD1_map c w f hfC)

/-- Representative formula for the induced coefficient map on `WordH2`. -/
@[simp] theorem moduleWordH2Map_mk (c : ι → C) (w : ρ → FreeGroup ι) (f : A →+ B)
    (hfC : ∀ (g : C) (a : A), f (g • a) = g • f a) (z : ρ → A) :
    moduleWordH2Map c w f hfC (QuotientAddGroup.mk z) =
      QuotientAddGroup.mk (fun k ↦ f (z k)) :=
  rfl

/-- `mk'`-shaped representative formula, matching comparison maps built as quotient lifts. -/
@[simp] theorem moduleWordH2Map_mk' (c : ι → C) (w : ρ → FreeGroup ι) (f : A →+ B)
    (hfC : ∀ (g : C) (a : A), f (g • a) = g • f a) (z : ρ → A) :
    moduleWordH2Map c w f hfC
        (QuotientAddGroup.mk' (heisD1 (A := A) c w).range z) =
      QuotientAddGroup.mk' (heisD1 (A := B) c w).range (fun k ↦ f (z k)) :=
  rfl

end WordMap

section LMapNaturality

variable {h q e : ℕ} {C A B : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction ((gamma h q : Type)) A]
  [ContinuousSMul ((gamma h q : Type)) A]
  [DistribMulAction C A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [DiscreteTopology B] [Finite B]
  [DistribMulAction ((gamma h q : Type)) B]
  [ContinuousSMul ((gamma h q : Type)) B]
  [DistribMulAction C B]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "WL" => gammaFam (2 * h + 1) q (Words.LSq.lSqW h)
local notation "wL" => Certificates.LSqStokes.lSqFam h q e

/-- The flexible continuous-to-word `H²` comparison commutes with every coefficient map
that is equivariant for both the source action and its prescribed finite target action. -/
theorem lModuleH2WordFlexible_natural
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatA : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hcompatB : ∀ (g : GammaL) (b : B), g • b = rho g • b)
    (hA₂ : ∀ a : A, a + a = 0) (hB₂ : ∀ b : B, b + b = 0)
    (hresA : ResolvesAt WL wL (WordLift A C))
    (hresB : ResolvesAt WL wL (WordLift B C))
    (f : A →+ B)
    (hfG : ∀ (g : GammaL) (a : A), f (g • a) = g • f a)
    (hfC : ∀ (c : C) (a : A), f (c • a) = c • f a)
    (x : H2 GammaL A) :
    moduleWordH2Map (fun i ↦ rho (genL i)) wL f hfC
        (lModuleH2WordFlexible rho hcompatA hA₂ hresA x) =
      lModuleH2WordFlexible rho hcompatB hB₂ hresB
        (mapCoeff2 f continuous_of_discreteTopology hfG x) := by
  obtain ⟨z, rfl⟩ := H2mk_surjective (G := GammaL) (M := A) x
  change moduleWordH2Map (fun i ↦ rho (genL i)) wL f hfC
      (lModuleH2WordFlexible rho hcompatA hA₂ hresA (H2mk GammaL A z)) =
    lModuleH2WordFlexible rho hcompatB hB₂ hresB
      (H2mk GammaL B
        (Z2comap (ContinuousMonoidHom.id GammaL) f continuous_of_discreteTopology
          (fun g a ↦ hfG g a) z))
  rw [lModuleH2WordFlexible_mk, lModuleH2WordFlexible_mk, moduleWordH2Map_mk']
  apply congrArg (QuotientAddGroup.mk'
    (heisD1 (A := B) (fun i ↦ rho (genL i)) wL).range)
  exact (moduleObsFun_mapCoeff WL genL rho hcompatA hcompatB f hfG z).symm

end LMapNaturality

end

end GQ2.Dyadic.LSquare

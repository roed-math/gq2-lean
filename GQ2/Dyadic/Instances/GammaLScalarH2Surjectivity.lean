/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLAnalyticLeaves
import GQ2.Dyadic.Instances.GammaLTateProviderCore

/-!
# Direct scalar H² surjectivity for the improved L presentation

The action-image Stokes theorem computes both sides of the canonical scalar
continuous-to-word comparison.  The continuous group has cardinality two by
`cardH2_of_uniformPushed`; the word group has cardinality two by the explicit L trace.
Since the flexible comparison is already injective, it is bijective.

This removes scalar finite-extension asphericity from the direct Tate route.  No Tate
duality, Euler characteristic, field realization, or relator-realization hypothesis is used.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH
open ContCoh
open GQ2.Dyadic.Count
open GQ2.Dyadic.Certificates.LSqStokes

section Scalar

variable {h q : ℕ} {C : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "eC" => omega2Exp (4 * Monoid.exponent C)
local notation "wC" => lSqFam h q eC

/-- The canonical scalar flexible H² map at the coefficient-independent L resolver is
surjective, directly from action-image word duality and the scalar H² count. -/
theorem lUniform_scalarH2WordFlexible_surjective_of_actionImage
    (rho : ContinuousMonoidHom GammaL C) (hq : Even q) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
    letI : DistribMulAction GammaL (ZMod 2) := scalarActionZmodTwo GammaL
    letI : ContinuousSMul GammaL (ZMod 2) := scalarActionZmodTwo_continuousSMul GammaL
    Function.Surjective
      (lScalarH2WordFlexible rho (fun _ _ ↦ rfl)
        (odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
          (fourMulExponent_ne_zero_and_even C).2)) := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
  letI : DistribMulAction GammaL (ZMod 2) := scalarActionZmodTwo GammaL
  letI : ContinuousSMul GammaL (ZMod 2) := scalarActionZmodTwo_continuousSMul GammaL
  have he : Odd eC := odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
    (fourMulExponent_ne_zero_and_even C).2
  have hres : ResolvesAt
      (gammaFam (2 * h + 1) q (Words.LSq.lSqW h)) wC (WordLift (ZMod 2) C) :=
    lUniform_wordLift_resolver (C := C) (h := h) (q := q) (by decide)
  have hr : ∀ k, FreeGroup.lift (fun i ↦ rho (genL i)) (wC k) = 1 :=
    lSource_rel_death rho hres
  let f := lScalarH2WordFlexible rho (fun _ _ ↦ rfl) he
  have hinj : Function.Injective f :=
    lScalarH2WordFlexible_injective rho (fun _ _ ↦ rfl) he
  letI : Finite (H2 GammaL (ZMod 2)) := Finite.of_injective f hinj
  letI : Fintype (H2 GammaL (ZMod 2)) := Fintype.ofFinite _
  letI : Fintype (WordH2 (fun i ↦ rho (genL i)) wC (ZMod 2)) := Fintype.ofFinite _
  have hcard : Nat.card (H2 GammaL (ZMod 2)) =
      Nat.card (WordH2 (fun i ↦ rho (genL i)) wC (ZMod 2)) := by
    calc
      Nat.card (H2 GammaL (ZMod 2)) = 2 :=
        cardH2_of_uniformPushed (uniformPushedHsimp_of_actionImage hq) hq
      _ = Nat.card (ZMod 2) := (Nat.card_zmod 2).symm
      _ = Nat.card (WordH2 (fun i ↦ rho (genL i)) wC (ZMod 2)) :=
        (Nat.card_congr (lWordH2TraceEquiv (fun i ↦ rho (genL i)) hq he hr).toEquiv).symm
  exact ((Fintype.bijective_iff_injective_and_card f).mpr
    ⟨hinj, by simpa only [Nat.card_eq_fintype_card] using hcard⟩).2

end Scalar

end

end GQ2.Dyadic.LSquare

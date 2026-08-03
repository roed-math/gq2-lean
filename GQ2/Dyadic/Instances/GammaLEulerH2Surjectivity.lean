/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLSimpleDualSurjectivity
import GQ2.Dyadic.Instances.LSourceEulerCard
import GQ2.Dyadic.Instances.GammaLDualityBoundary

/-!
# Euler characteristic closes the simple L H²-surjectivity supply

For the improved L presentation, the canonical flexible continuous-to-word `H²` map is
unconditionally injective.  A local Euler-characteristic bundle gives equality of the finite
source and word-side cardinalities, so the same concrete map is bijective and hence surjective.

This closes both the one-map and paired uniform simple-surjectivity interfaces from
`LocalEulerChar` alone.  No Tate-duality input is used.  A `GammaLFieldRealization` therefore
supplies these interfaces through its Euler-characteristic theorem.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH
open ContCoh
open GQ2.Dyadic.Count
open GQ2.Dyadic.LiftingDualityG
open GQ2.Dyadic.Certificates.LSqStokes

section EulerSupply

variable {h q : ℕ}

local notation "GammaL" => (gamma h q : Type)

/-- The all-coefficient local Euler characteristic makes every canonical flexible L `H²`
comparison at a simple coefficient surjective.

The simplicity hypothesis is not needed in the proof: injectivity and the Euler cardinality
calculation apply to every finite exponent-two coefficient with a compatible finite action. -/
theorem uniformSimpleH2SurjectiveSingleSupply_of_localEulerChar
    (hE : LocalEulerChar GammaL (2 * h + 1)) :
    UniformSimpleH2SurjectiveSingleSupply (h := h) (q := q) := by
  intro C _ _ _ _ rho V _ _ _ _ _ _ _ hcompat hV₂ _hsimple
  let hres := lUniform_wordLift_resolver (h := h) (q := q) (C := C) hV₂
  exact
    (lModuleH2WordFlexible_bijective_of_card_eq rho hcompat hV₂ hres
      (l_card_H2_eq_WordH2_of_localEulerChar rho hcompat hV₂ hres hE)).2

/-- Local Euler characteristic also supplies the established paired primal/dual
simple-surjectivity interface. -/
theorem uniformSimpleH2SurjectiveSupply_of_localEulerChar
    (hE : LocalEulerChar GammaL (2 * h + 1)) :
    UniformSimpleH2SurjectiveSupply (h := h) (q := q) :=
  uniformSimpleH2SurjectiveSupply_of_single
    (uniformSimpleH2SurjectiveSingleSupply_of_localEulerChar hE)

/-- A field realization closes the one-map uniform simple `H²`-surjectivity supply through
Euler characteristic alone. -/
theorem uniformSimpleH2SurjectiveSingleSupply_of_fieldRealization
    (R : GammaLFieldRealization h q) :
    UniformSimpleH2SurjectiveSingleSupply (h := h) (q := q) :=
  uniformSimpleH2SurjectiveSingleSupply_of_localEulerChar (gammaL_localEulerChar R)

/-- A field realization likewise closes the paired uniform simple `H²`-surjectivity supply. -/
theorem uniformSimpleH2SurjectiveSupply_of_fieldRealization
    (R : GammaLFieldRealization h q) :
    UniformSimpleH2SurjectiveSupply (h := h) (q := q) :=
  uniformSimpleH2SurjectiveSupply_of_localEulerChar (gammaL_localEulerChar R)

end EulerSupply

end

end GQ2.Dyadic.LSquare

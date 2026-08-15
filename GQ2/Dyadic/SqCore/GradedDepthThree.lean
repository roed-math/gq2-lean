/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedAbsorption

/-!
# W79-DEPTH3: the depth-3 base by absorption

Wave 78 formalized Labute's Theorem 5 absorption at depth 2 and re-seeded the odd-route
reduction so that its sole remaining layer-side input is the depth-3 base
`GDecideBaseThree h`: at every selected marking, every exactly row-trivial `γ₄`-element
reaches at depth 3.  This file attempts that base by the same absorption one level up:

* the depth-3 leftover normal form (reach times explicit coker classes with
  `𝔽₂`-coefficients), and
* the coefficient kill on the handle-corrected rows.
-/

open Multiplicative

namespace GQ2

open Roe Roe.Labute FoxH

namespace Dyadic

namespace SqCore

open MarkedCore
open scoped commutatorElement

/-! ## §1 The target, unfolded -/

section Target

variable {h : ℕ}

/-- The depth-3 base, unfolded: at every selected marking, every exactly row-trivial
`γ₄`-element's level-5 class lies in the depth-3 reach. -/
theorem gDeep_baseThree_iff :
    GDecideBaseThree h ↔
      ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
        nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
          ∀ g ∈ twoCentralSeries (DSq h : Type) 4, nuLam h g = 1 → nu' g = 1 →
            levelMk (DSq h : Type) 5 g ∈ gTowerReach h nu' 3 :=
  Iff.rfl

end Target

/-! ## Axiom pins -/

section AxiomPins

#print axioms gDeep_baseThree_iff

end AxiomPins

end SqCore

end Dyadic

end GQ2

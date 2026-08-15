/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedJoinBase

/-!
# W77-DECIDE: the depth-two residual at `h = 0`

Wave 76 reduced `GJoinBase h` to `GBaseResidual h`, the `3 + 2h` layer classes
`⁅⁅x₁, xᵢ⁆, x₁⁆ ∈ gTowerReach h ν' 2`, and argued **outside the tree** that two of them are
unreachable.  This file works at `h = 0`, where the letter list is `σ, x₀, x₁` and the third
class is trivial on the nose, so the residual is exactly two classes.

Prefix: `gDecide`.
-/

namespace GQ2

open Roe.Labute

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The residual at `h = 0` is two classes -/

section Zero

variable {nu' : ContinuousMonoidHom (DSq 0 : Type) (Multiplicative ℤ_[2])}

/-- The `x₁`-slot triple bracket at `x₁` itself is trivial on the nose, at every `h`. -/
theorem gDecide_triple_self (h : ℕ)
    {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} :
    commP (commP (gBaseT h) (levelMk (DSq h : Type) 4 (sqGen h 2))) (gBaseT h)
      ∈ gTowerReach h nu' 2 := by
  rw [show levelMk (DSq h : Type) 4 (sqGen h 2) = gBaseT h from rfl, cfour_comm_self,
    cfour_one_comm]
  exact Subgroup.one_mem _

/-- ⭐⭐ **The residual at `h = 0`, spelled out**: the `3 + 2h = 3` classes of
`GBaseXOneTriple` are the two at `σ` and `x₀`, the third being trivial. -/
theorem gDecide_residual_zero_iff :
    GBaseXOneTriple 0 nu' ↔
      (commP (commP (gBaseT 0) (gBaseS 0)) (gBaseT 0) ∈ gTowerReach 0 nu' 2 ∧
        commP (commP (gBaseT 0) (gBaseX 0)) (gBaseT 0) ∈ gTowerReach 0 nu' 2) := by
  constructor
  · intro H
    exact ⟨H 0, H 1⟩
  · rintro ⟨hs, hx⟩ i
    have hlt : (i : ℕ) < 3 := i.isLt
    interval_cases hv : (i : ℕ)
    · have : i = 0 := Fin.ext (by simpa using hv)
      subst this; exact hs
    · have : i = 1 := Fin.ext (by simpa using hv)
      subst this; exact hx
    · have : i = 2 := Fin.ext (by simpa using hv)
      subst this; exact gDecide_triple_self 0

end Zero

/-! ## §2 Axiom pins -/

section AxiomPins

#print axioms gDecide_triple_self
#print axioms gDecide_residual_zero_iff

end AxiomPins

end SqCore

end Dyadic

end GQ2

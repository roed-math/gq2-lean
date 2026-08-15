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

/-! ## §2 The witness group: generalized quaternion of order sixteen

`Q₁₆ = ⟨X, Y | X⁸ = 1, Y² = X⁴, Y⁻¹XY = X⁻¹⟩`, carried on `Bool × ZMod 8` with
`(false, i) = Xⁱ` and `(true, i) = XⁱY`.  Every group law is a `decide` over at most `16³`
tuples.  `Mathlib.GroupTheory.SpecificGroups.Quaternion` is not in this project's import
closure, so the group is built here.

Why this group.  At `h = 0` the relator is `sqWord σ x₀ x₁`, which at `σ = 1` collapses to
`x₀⁻⁴ · x₁²`; so any group with `Y² = X⁴` receives `D_sq 0` by `σ ↦ 1`, `x₀ ↦ X`, `x₁ ↦ Y`.
`Q₁₆` is the smallest such group in which `⁅x₁, x₀⁆²` survives: `⁅Y, X⁆ = X²` and
`⁅Y, X⁆² = X⁴ ≠ 1`, while its whole depth-`2` reach collapses to `1` (§5). -/

section Witness

/-- The witness group `Q₁₆`, on `Bool × ZMod 8`: `(false, i) = Xⁱ`, `(true, i) = XⁱY`. -/
def GDecideQ : Type := Bool × ZMod 8

namespace GDecideQ

instance : DecidableEq GDecideQ := inferInstanceAs (DecidableEq (Bool × ZMod 8))
instance : Fintype GDecideQ := inferInstanceAs (Fintype (Bool × ZMod 8))
instance : Inhabited GDecideQ := ⟨(false, 0)⟩

instance : Mul GDecideQ :=
  ⟨fun p q =>
    match p, q with
    | (false, i), (false, j) => (false, i + j)
    | (false, i), (true, j) => (true, j - i)
    | (true, i), (false, j) => (true, i + j)
    | (true, i), (true, j) => (false, 4 + j - i)⟩

instance : One GDecideQ := ⟨(false, 0)⟩

instance : Inv GDecideQ :=
  ⟨fun p =>
    match p with
    | (false, i) => (false, -i)
    | (true, i) => (true, i + 4)⟩

instance : Group GDecideQ where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide

instance : TopologicalSpace GDecideQ := ⊥
instance : DiscreteTopology GDecideQ := ⟨rfl⟩
instance : ContinuousMul GDecideQ := ⟨continuous_of_discreteTopology⟩
instance : ContinuousInv GDecideQ := ⟨continuous_of_discreteTopology⟩
instance : IsTopologicalGroup GDecideQ := { }
instance : CompactSpace GDecideQ := Finite.compactSpace
instance : T2Space GDecideQ := DiscreteTopology.toT2Space
instance : TotallyDisconnectedSpace GDecideQ := inferInstance

end GDecideQ

/-- The letter `X ∈ Q₁₆`, of order eight. -/
def gDecideX : GDecideQ := (false, 1)

/-- The letter `Y ∈ Q₁₆`, of order four, with `Y² = X⁴`. -/
def gDecideY : GDecideQ := (true, 0)

/-- The central involution `Z = X⁴ = Y²`, the single nontrivial class of `γ₃(Q₁₆)`. -/
def gDecideZ : GDecideQ := (false, 4)

theorem gDecideQ_exp_eight (g : GDecideQ) : g ^ 8 = 1 := by revert g; decide

/-- `Q₁₆` is a `2`-group, hence pro-`2`, so it classifies markings of `D_sq`. -/
theorem gDecideQ_isPGroup : IsPGroup 2 GDecideQ := fun g => ⟨3, gDecideQ_exp_eight g⟩

theorem gDecideQ_isProP : IsProP 2 GDecideQ := isProP_of_isPGroup gDecideQ_isPGroup

end Witness

/-! ## §3 Axiom pins -/

section AxiomPins

#print axioms gDecide_triple_self
#print axioms gDecide_residual_zero_iff
#print axioms GQ2.Dyadic.SqCore.GDecideQ
#print axioms gDecideX
#print axioms gDecideY
#print axioms gDecideZ
#print axioms gDecideQ_exp_eight
#print axioms gDecideQ_isPGroup
#print axioms gDecideQ_isProP

end AxiomPins

end SqCore

end Dyadic

end GQ2

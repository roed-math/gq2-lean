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

/-! ## §3 The marking `σ ↦ 1`, `x₀ ↦ X`, `x₁ ↦ Y`, and the classifying hom -/

section Marking

/-- The marking of `Q₁₆` by the three letters of `D_sq 0`. -/
def gDecideMark : Fin (sqRank 0) → GDecideQ := ![1, gDecideX, gDecideY]

/-- ⭐ **The relator dies at the marking.**  At `σ = 1` the core word `sqWord σ x₀ x₁`
collapses to `x₀⁻⁴ · x₁²`, and `Y² = X⁴` in `Q₁₆`. -/
theorem gDecideMark_rel : sqRelWord gDecideMark = 1 := by
  rw [sqRelWord_zero]
  decide

/-- ⭐⭐⭐ **The classifying hom** `D_sq 0 → Q₁₆`, through the presentation's universal
property `sqLiftHom`. -/
noncomputable def gDecideHom : ContinuousMonoidHom (DSq 0 : Type) GDecideQ :=
  sqLiftHom 0 gDecideQ_isProP gDecideMark gDecideMark_rel

@[simp] theorem gDecideHom_gen (i : Fin (sqRank 0)) :
    gDecideHom (sqGen 0 i) = gDecideMark i :=
  sqLiftHom_gen 0 gDecideQ_isProP gDecideMark gDecideMark_rel i

@[simp] theorem gDecideHom_sigma : gDecideHom (dsqSigma 0) = 1 := gDecideHom_gen 0

@[simp] theorem gDecideHom_x0 : gDecideHom (dsqX0 0) = gDecideX := gDecideHom_gen 1

@[simp] theorem gDecideHom_x1 : gDecideHom (dsqX1 0) = gDecideY := gDecideHom_gen 2

end Marking

/-! ## §4 The lower `2`-central tower of `Q₁₆` stops at four

`λ₂ = ⟨X²⟩`, `λ₃ = ⟨X⁴⟩`, `λ₄ = 1`, each step a `decide` against an explicit subgroup.  The
last one is what lets `gDecideHom` descend to `Q₄ = levelQuot (D_sq 0) 4`. -/

section Tower

open scoped commutatorElement

/-- Membership in `⟨X⟩`, as a decidable predicate. -/
abbrev GDecideInA (g : GDecideQ) : Prop :=
  g = 1 ∨ g = gDecideX ∨ g = gDecideX ^ 2 ∨ g = gDecideX ^ 3 ∨
    g = gDecideX ^ 4 ∨ g = gDecideX ^ 5 ∨ g = gDecideX ^ 6 ∨ g = gDecideX ^ 7

/-- Membership in `⟨X²⟩`, as a decidable predicate. -/
abbrev GDecideInA2 (g : GDecideQ) : Prop :=
  g = 1 ∨ g = gDecideX ^ 2 ∨ g = gDecideX ^ 4 ∨ g = gDecideX ^ 6

/-- Membership in `⟨X⁴⟩ = ⟨Z⟩`, as a decidable predicate. -/
abbrev GDecideInZ (g : GDecideQ) : Prop := g = 1 ∨ g = gDecideZ

/-- `⟨X⟩ ≤ Q₁₆`, the cyclic subgroup of order eight.  It is abelian and receives the far
span. -/
def gDecideA : Subgroup GDecideQ where
  carrier := {g | GDecideInA g}
  mul_mem' := fun ha hb => (by decide : ∀ x y : GDecideQ,
    GDecideInA x → GDecideInA y → GDecideInA (x * y)) _ _ ha hb
  one_mem' := by decide
  inv_mem' := fun ha => (by decide : ∀ x : GDecideQ, GDecideInA x → GDecideInA x⁻¹) _ ha

/-- `⟨X²⟩ ≤ Q₁₆`, the second term of the lower `2`-central series. -/
def gDecideA2 : Subgroup GDecideQ where
  carrier := {g | GDecideInA2 g}
  mul_mem' := fun ha hb => (by decide : ∀ x y : GDecideQ,
    GDecideInA2 x → GDecideInA2 y → GDecideInA2 (x * y)) _ _ ha hb
  one_mem' := by decide
  inv_mem' := fun ha => (by decide : ∀ x : GDecideQ, GDecideInA2 x → GDecideInA2 x⁻¹) _ ha

/-- `⟨X⁴⟩ = ⟨Z⟩ ≤ Q₁₆`, the third term of the lower `2`-central series, and the centre. -/
def gDecideZsub : Subgroup GDecideQ where
  carrier := {g | GDecideInZ g}
  mul_mem' := fun ha hb => (by decide : ∀ x y : GDecideQ,
    GDecideInZ x → GDecideInZ y → GDecideInZ (x * y)) _ _ ha hb
  one_mem' := by decide
  inv_mem' := fun ha => (by decide : ∀ x : GDecideQ, GDecideInZ x → GDecideInZ x⁻¹) _ ha

@[simp] theorem gDecide_mem_A {g : GDecideQ} : g ∈ gDecideA ↔ GDecideInA g := Iff.rfl

@[simp] theorem gDecide_mem_A2 {g : GDecideQ} : g ∈ gDecideA2 ↔ GDecideInA2 g := Iff.rfl

@[simp] theorem gDecide_mem_Zsub {g : GDecideQ} : g ∈ gDecideZsub ↔ GDecideInZ g := Iff.rfl

/-- One step of the tower, bounded against an explicit subgroup. -/
theorem gDecide_succ_le {H K : Subgroup GDecideQ}
    (hsq : ∀ v ∈ H, v ^ 2 ∈ K) (hcomm : ∀ v ∈ H, ∀ g : GDecideQ, ⁅v, g⁆ ∈ K) :
    twoCentralSucc H ≤ K := by
  refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) (isClosed_discrete _)
  · refine Subgroup.closure_le _ |>.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    exact hsq v hv
  · exact Subgroup.commutator_le.2 fun v hv g _ => hcomm v hv g

theorem gDecide_lambdaTwo : twoCentralSeries GDecideQ 2 ≤ gDecideA2 := by
  rw [twoCentralSeries_succ GDecideQ le_rfl]
  refine gDecide_succ_le (fun v _ => ?_) (fun v _ g => ?_)
  · exact (by decide : ∀ w : GDecideQ, GDecideInA2 (w ^ 2)) v
  · exact (by decide : ∀ w u : GDecideQ, GDecideInA2 ⁅w, u⁆) v g

theorem gDecide_lambdaThree : twoCentralSeries GDecideQ 3 ≤ gDecideZsub := by
  rw [twoCentralSeries_succ GDecideQ (by norm_num)]
  refine le_trans (twoCentralSucc_mono gDecide_lambdaTwo) (gDecide_succ_le
    (fun v hv => ?_) (fun v hv g => ?_))
  · exact (by decide : ∀ w : GDecideQ, GDecideInA2 w → GDecideInZ (w ^ 2)) v hv
  · exact (by decide : ∀ w u : GDecideQ, GDecideInA2 w → GDecideInZ ⁅w, u⁆) v g hv

/-- ⭐⭐ **`λ₄(Q₁₆) = 1`**, so `gDecideHom` descends to `Q₄ = levelQuot (D_sq 0) 4`. -/
theorem gDecide_lambdaFour : twoCentralSeries GDecideQ 4 = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [twoCentralSeries_succ GDecideQ (by norm_num)]
  refine le_trans (twoCentralSucc_mono gDecide_lambdaThree) (gDecide_succ_le
    (fun v hv => ?_) (fun v hv g => ?_))
  · exact (by decide : ∀ w : GDecideQ, GDecideInZ w → w ^ 2 = 1) v hv
  · exact (by decide : ∀ w u : GDecideQ, GDecideInZ w → ⁅w, u⁆ = 1) v g hv

end Tower

/-! ## §5 Axiom pins -/

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
#print axioms gDecideMark
#print axioms gDecideMark_rel
#print axioms gDecideHom
#print axioms gDecideHom_gen
#print axioms gDecideHom_sigma
#print axioms gDecideHom_x0
#print axioms gDecideHom_x1
#print axioms gDecideA
#print axioms gDecideA2
#print axioms gDecideZsub
#print axioms gDecide_mem_A
#print axioms gDecide_mem_A2
#print axioms gDecide_mem_Zsub
#print axioms gDecide_succ_le
#print axioms gDecide_lambdaTwo
#print axioms gDecide_lambdaThree
#print axioms gDecide_lambdaFour

end AxiomPins

end SqCore

end Dyadic

end GQ2

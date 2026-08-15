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

open Multiplicative

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

/-! ## §4 Two markings of `Q₁₆` by the letters of `D_sq 0`

Both send `x₁ ↦ Y` and the two far letters into `⟨X⟩`, and both kill the relator:

* `σ ↦ 1`, `x₀ ↦ X`: the word collapses to `x₀⁻⁴·x₁² = X⁻⁴Y² = 1`;
* `σ ↦ X`, `x₀ ↦ 1`: the word collapses to `x₁²·⁅x₁, x₁^σ⁆ = Y²·X⁴ = 1`.

The first sees `⁅x₁, x₀⁆`, the second sees `⁅x₁, σ⁆`; between them they cover the whole
wave-76 residual. -/

section Markings

/-- The marking `σ ↦ 1`, `x₀ ↦ X`, `x₁ ↦ Y`: the one that sees the `x₀` class. -/
def gDecideMarkX : Fin (sqRank 0) → GDecideQ := ![1, gDecideX, gDecideY]

/-- The marking `σ ↦ X`, `x₀ ↦ 1`, `x₁ ↦ Y`: the one that sees the `σ` class. -/
def gDecideMarkS : Fin (sqRank 0) → GDecideQ := ![gDecideX, 1, gDecideY]

theorem gDecideMarkX_rel : sqRelWord gDecideMarkX = 1 := by rw [sqRelWord_zero]; decide

theorem gDecideMarkS_rel : sqRelWord gDecideMarkS = 1 := by rw [sqRelWord_zero]; decide

end Markings

/-! ## §5 The classifying hom, and the collapse of the whole depth-two reach

Three families, three collapses, none of them using the row conditions:

* **knobs** `⁅t, q⁆`: the correction `t` lands in `λ₂(Q₁₆) = ⟨X²⟩` and the far slot `q` lands
  in `⟨X⟩`, which is abelian, so the bracket is `1`;
* **bundles** `t²·⁅t, x₁⁆`: for `t ↦ X^{2k}` this is `X^{4k}·X^{-4k} = 1`, exactly the
  cancellation the wave-76 note calls the vacuous bundle;
* **towers** `x̃₁^{4a}`: `x̃₁ ↦ Y·(m x₀)⁻²`, an element of order four.

Dropping the admissibility hypotheses is deliberate: `GTowerAdm`'s row conditions are never
used, so the refutation is **stronger** than the wave-76 argument, which needs them to cut
`W` down to `⟨x₁⟩`. -/

section Model

open scoped commutatorElement

variable {m : Fin (sqRank 0) → GDecideQ} (hrel : sqRelWord m = 1)
  {nu' : ContinuousMonoidHom (DSq 0 : Type) (Multiplicative ℤ_[2])}

/-- ⭐⭐⭐ **The classifying hom** `D_sq 0 → Q₁₆` at a relator-killing marking, through the
presentation's universal property `sqLiftHom`. -/
noncomputable def gDecideHom : ContinuousMonoidHom (DSq 0 : Type) GDecideQ :=
  sqLiftHom 0 gDecideQ_isProP m hrel

@[simp] theorem gDecideHom_gen (i : Fin (sqRank 0)) : gDecideHom hrel (sqGen 0 i) = m i :=
  sqLiftHom_gen 0 gDecideQ_isProP m hrel i

@[simp] theorem gDecideHom_sigma : gDecideHom hrel (dsqSigma 0) = m 0 := gDecideHom_gen hrel 0

@[simp] theorem gDecideHom_x0 : gDecideHom hrel (dsqX0 0) = m 1 := gDecideHom_gen hrel 1

@[simp] theorem gDecideHom_x1 : gDecideHom hrel (dsqX1 0) = m 2 := gDecideHom_gen hrel 2

theorem gDecide_map_lambda (k : ℕ) {g : (DSq 0 : Type)}
    (hg : g ∈ twoCentralSeries (DSq 0 : Type) k) :
    gDecideHom hrel g ∈ twoCentralSeries GDecideQ k :=
  map_twoCentralSeries_le (gDecideHom hrel).toMonoidHom (gDecideHom hrel).continuous_toFun k
    ⟨g, hg, rfl⟩

/-- ⭐ **The descent to `Q₄`**: `λ₄(Q₁₆) = 1`, so the classifying hom factors through the
level quotient in which the whole depth-`2` reach lives. -/
noncomputable def gDecideQuot : levelQuot (DSq 0 : Type) 4 →* GDecideQ :=
  QuotientGroup.lift (twoCentralSeries (DSq 0 : Type) 4) (gDecideHom hrel).toMonoidHom
    (fun g hg => by
      have h := gDecide_map_lambda hrel 4 hg
      rwa [gDecide_lambdaFour, Subgroup.mem_bot] at h)

@[simp] theorem gDecideQuot_levelMk (g : (DSq 0 : Type)) :
    gDecideQuot hrel (levelMk (DSq 0 : Type) 4 g) = gDecideHom hrel g := rfl

@[simp] theorem gDecideQuot_baseT : gDecideQuot hrel (gBaseT 0) = m 2 := gDecideHom_x1 hrel

@[simp] theorem gDecideQuot_baseX : gDecideQuot hrel (gBaseX 0) = m 1 := gDecideHom_x0 hrel

@[simp] theorem gDecideQuot_baseS : gDecideQuot hrel (gBaseS 0) = m 0 := gDecideHom_sigma hrel

theorem gDecideHom_commP (a b : (DSq 0 : Type)) :
    gDecideHom hrel (commP a b) = commP (gDecideHom hrel a) (gDecideHom hrel b) := by
  simp only [commP, map_mul, map_inv]

/-- The image of `γ₂(D_sq 0)` lands in `⟨X²⟩`. -/
theorem gDecide_gammaTwo_mem {t : (DSq 0 : Type)}
    (ht : t ∈ twoCentralSeries (DSq 0 : Type) 2) : GDecideInA2 (gDecideHom hrel t) :=
  gDecide_lambdaTwo (gDecide_map_lambda hrel 2 ht)

/-- The image of the `x₁`-free letter span lands in the abelian `⟨X⟩`, provided both far
letters do. -/
theorem gDecide_far_mem (h0 : GDecideInA (m 0)) (h1 : GDecideInA (m 1))
    {q : (DSq 0 : Type)} (hq : q ∈ gTowerFar 0) : GDecideInA (gDecideHom hrel q) := by
  have hle : gTowerFar 0 ≤ Subgroup.comap (gDecideHom hrel).toMonoidHom gDecideA := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.closure_le _ |>.2 ?_) ?_
    · rintro x hx
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at hx
      rcases hx with ((rfl | rfl) | ⟨j, -⟩) | ⟨j, -⟩
      · exact show GDecideInA (gDecideHom hrel (dsqSigma 0)) by
          rw [gDecideHom_sigma]; exact h0
      · exact show GDecideInA (gDecideHom hrel (dsqX0 0)) by rw [gDecideHom_x0]; exact h1
      · exact absurd j.isLt (by omega)
      · exact absurd j.isLt (by omega)
    · exact (isClosed_discrete (gDecideA : Set GDecideQ)).preimage
        (gDecideHom hrel).continuous_toFun
  exact hle hq

/-- ⭐⭐ **The knobs die**: both slots land in the cyclic `⟨X⟩`. -/
theorem gDecide_knob_one (h0 : GDecideInA (m 0)) (h1 : GDecideInA (m 1))
    {t q : (DSq 0 : Type)} (ht : t ∈ twoCentralSeries (DSq 0 : Type) 2)
    (hq : q ∈ gTowerFar 0) : gDecideHom hrel (commP t q) = 1 := by
  rw [gDecideHom_commP]
  exact (by decide : ∀ u v : GDecideQ, GDecideInA2 u → GDecideInA v → commP u v = 1) _ _
    (gDecide_gammaTwo_mem hrel ht) (gDecide_far_mem hrel h0 h1 hq)

/-- ⭐⭐ **The bundles die**: `X^{4k} · X^{-4k} = 1`, the wave-76 cancellation, verified. -/
theorem gDecide_bundle_one (h2 : m 2 = gDecideY) {t : (DSq 0 : Type)}
    (ht : t ∈ twoCentralSeries (DSq 0 : Type) 2) :
    gDecideHom hrel (t ^ 2 * commP t (dsqX1 0)) = 1 := by
  rw [map_mul, map_pow, gDecideHom_commP, gDecideHom_x1, h2]
  exact (by decide : ∀ u : GDecideQ, GDecideInA2 u → u ^ 2 * commP u gDecideY = 1) _
    (gDecide_gammaTwo_mem hrel ht)

/-- The cleared letter `x̃₁ = x₁·x₀⁻²` maps to `Y·(m x₀)⁻²`. -/
theorem gDecideHom_xOne : gDecideHom hrel (gTowerXOne 0) = m 2 * ((m 1) ^ 2)⁻¹ := by
  rw [gTowerXOne, map_mul, map_inv, gDecideHom_x1,
    map_zpowZtwo (isProP_DSq 0) gDecideQ_isProP (gDecideHom hrel) (dsqX0 0) 2, gDecideHom_x0,
    show ((2 : ℤ_[2])) = ((2 : ℕ) : ℤ_[2]) by norm_num, zpowZtwo_natCast]

/-- ⭐⭐ **The towers die**: `Y·X^{-2k}` has order four for every `k`. -/
theorem gDecide_tower_one (h1 : GDecideInA (m 1)) (h2 : m 2 = gDecideY)
    {x : (DSq 0 : Type)} (hx : x ∈ gTowerXLetters 0 nu') (a : ℤ_[2]) :
    gDecideHom hrel (zpowZtwo (isProP_DSq 0) x ((2 : ℤ_[2]) ^ 2 * a)) = 1 := by
  have hxeq : x = gTowerXOne 0 := by
    simp only [gTowerXLetters, Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at hx
    rcases hx with (hx | ⟨j, -⟩) | ⟨j, -⟩
    · exact hx
    · exact absurd j.isLt (by omega)
    · exact absurd j.isLt (by omega)
  subst hxeq
  rw [map_zpowZtwo (isProP_DSq 0) gDecideQ_isProP (gDecideHom hrel) _ _,
    ← zpowZtwo_zpowZtwo gDecideQ_isProP,
    show ((2 : ℤ_[2]) ^ 2) = ((4 : ℕ) : ℤ_[2]) by norm_num, zpowZtwo_natCast, gDecideHom_xOne,
    h2, show ∀ u : GDecideQ, GDecideInA u → (gDecideY * (u ^ 2)⁻¹) ^ 4 = 1 from by decide,
    zpowZtwo_one_base]
  exact h1

/-- ⭐⭐⭐ **The whole depth-two reach lies in the kernel.**  No admissibility is used: the
statement holds for every `γ₂`-correction, not only the exactly row-trivial ones. -/
theorem gDecide_reach_le_ker (h0 : GDecideInA (m 0)) (h1 : GDecideInA (m 1))
    (h2 : m 2 = gDecideY) : gTowerReach 0 nu' 2 ≤ MonoidHom.ker (gDecideQuot hrel) := by
  refine Subgroup.closure_le _ |>.2 ?_
  rintro z ((⟨t, q, ht, hq, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨x, hx, a, rfl⟩)
  · exact gDecide_knob_one hrel h0 h1 ht.1 hq
  · exact gDecide_bundle_one hrel h2 ht.1
  · exact gDecide_tower_one hrel h1 h2 hx a

include hrel in
/-- ⭐⭐⭐ **The separation criterion.**  If the marking sees the letter `m i` as `X`, the
class `⁅⁅x₁, xᵢ⁆, x₁⁆` reads `Z ≠ 1` while the whole reach reads `1`. -/
theorem gDecide_triple_not_mem (h0 : GDecideInA (m 0)) (h1 : GDecideInA (m 1))
    (h2 : m 2 = gDecideY) {i : Fin (sqRank 0)} (hi : m i = gDecideX) :
    commP (commP (gBaseT 0) (levelMk (DSq 0 : Type) 4 (sqGen 0 i))) (gBaseT 0)
      ∉ gTowerReach 0 nu' 2 := by
  intro hmem
  have hker := gDecide_reach_le_ker hrel h0 h1 h2 hmem
  rw [MonoidHom.mem_ker] at hker
  rw [show gBaseT 0 = levelMk (DSq 0 : Type) 4 (dsqX1 0) from rfl, ← gBase_levelMk_triple,
    gDecideQuot_levelMk, gDecideHom_commP, gDecideHom_commP, gDecideHom_x1, gDecideHom_gen,
    hi, h2] at hker
  exact absurd hker (by decide)

end Model

/-! ## §6 The decision: both residual classes are unreachable at `h = 0` -/

section Decision

variable {nu' : ContinuousMonoidHom (DSq 0 : Type) (Multiplicative ℤ_[2])}

/-- ⭐⭐⭐ **The `x₀` class is not reachable**: `⁅⁅x₁, x₀⁆, x₁⁆ ∉ gTowerReach 0 ν' 2`. -/
theorem gDecide_x0_not_mem :
    commP (commP (gBaseT 0) (gBaseX 0)) (gBaseT 0) ∉ gTowerReach 0 nu' 2 :=
  gDecide_triple_not_mem gDecideMarkX_rel (by decide) (by decide) (by decide)
    (i := 1) (by decide)

/-- ⭐⭐⭐ **The `σ` class is not reachable**: `⁅⁅x₁, σ⁆, x₁⁆ ∉ gTowerReach 0 ν' 2`. -/
theorem gDecide_sigma_not_mem :
    commP (commP (gBaseT 0) (gBaseS 0)) (gBaseT 0) ∉ gTowerReach 0 nu' 2 :=
  gDecide_triple_not_mem gDecideMarkS_rel (by decide) (by decide) (by decide)
    (i := 0) (by decide)

/-- ⭐⭐⭐ **The wave-76 residual is FALSE at `h = 0`, at every marking.**  Both classes fail,
so the two-dimensional gap of the wave-76 note's §4 is a theorem here, and it needed no
structure theorem: one group of order sixteen and two markings. -/
theorem gDecide_not_xOneTriple : ¬ GBaseXOneTriple 0 nu' := fun H => gDecide_x0_not_mem (H 1)

end Decision

/-! ## §7 A selected marking exists, so the named `Prop`s are refuted outright -/

section Selected

/-- The selected marking `ν'(σ) = 1`, `ν'(x₀) = 0` at `h = 0` (and `ν'(x₁) = 0`, which the
relator forces). -/
noncomputable def gDecideNu : ContinuousMonoidHom (DSq 0 : Type) (Multiplicative ℤ_[2]) :=
  sqLiftHom 0 PropOneOne.isProP_two_multPadicInt
    (![ofAdd (1 : ℤ_[2]), ofAdd (0 : ℤ_[2]), ofAdd (0 : ℤ_[2])] :
      Fin (sqRank 0) → Multiplicative ℤ_[2])
    (by rw [sqRelWord_comm]; simp)

@[simp] theorem gDecideNu_sigma : gDecideNu (dsqSigma 0) = ofAdd (1 : ℤ_[2]) :=
  sqLiftHom_gen 0 _ _ _ 0

@[simp] theorem gDecideNu_x0 : gDecideNu (dsqX0 0) = ofAdd (0 : ℤ_[2]) :=
  sqLiftHom_gen 0 _ _ _ 1

/-- ⭐⭐⭐ **`GBaseResidual 0` is FALSE.** -/
theorem gDecide_not_baseResidual : ¬ GBaseResidual 0 :=
  fun H => gDecide_not_xOneTriple (H gDecideNu gDecideNu_sigma gDecideNu_x0)

/-- The `x₀` residual class is an exactly row-trivial `γ₃`-element, so it is inside what
`GTowerLayerReach 0 ν' 2` quantifies over: the failure is not a quantifier artefact. -/
theorem gDecide_triple_mem_three :
    commP (commP (dsqX1 0) (dsqX0 0)) (dsqX1 0) ∈ twoCentralSeries (DSq 0 : Type) 3 :=
  cfour_commP_mem_three (cfour_commP_mem_two _ _) _

/-- ⭐⭐⭐ **`GTowerLayerReach 0 ν' 2` is FALSE at every marking** — wave 74's depth-`2` layer
statement itself, not merely wave 76's sufficient condition for it.  The witness class is the
`x₀` one, and it really is an exactly row-trivial `γ₃`-element, so the failure is not a
quantifier artefact. -/
theorem gDecide_not_layerReach
    (nu' : ContinuousMonoidHom (DSq 0 : Type) (Multiplicative ℤ_[2])) :
    ¬ GTowerLayerReach 0 nu' 2 := by
  intro H
  have hadm := gBase_adm_commP (h := 0) (nu' := nu') (commP (dsqX1 0) (dsqX0 0)) (dsqX1 0)
  have hmem := H _ gDecide_triple_mem_three hadm.2.1 hadm.2.2
  rw [gBase_levelMk_triple] at hmem
  exact gDecide_x0_not_mem hmem

/-- ⭐⭐⭐ **`GJoinBase 0` is FALSE**: wave 75's first named input to `SqLamMarkTransitivity`
fails at `h = 0`. -/
theorem gDecide_not_joinBase : ¬ GJoinBase 0 :=
  fun H => gDecide_not_layerReach gDecideNu (H gDecideNu gDecideNu_sigma gDecideNu_x0)

end Selected

/-! ## §8 Axiom pins -/

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
#print axioms GQ2.Dyadic.SqCore.GDecideInA
#print axioms GQ2.Dyadic.SqCore.GDecideInA2
#print axioms GQ2.Dyadic.SqCore.GDecideInZ
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
#print axioms gDecideMarkX
#print axioms gDecideMarkS
#print axioms gDecideMarkX_rel
#print axioms gDecideMarkS_rel
#print axioms gDecideHom
#print axioms gDecideHom_gen
#print axioms gDecideHom_sigma
#print axioms gDecideHom_x0
#print axioms gDecideHom_x1
#print axioms gDecide_map_lambda
#print axioms gDecideQuot
#print axioms gDecideQuot_levelMk
#print axioms gDecideQuot_baseT
#print axioms gDecideQuot_baseX
#print axioms gDecideQuot_baseS
#print axioms gDecideHom_commP
#print axioms gDecide_gammaTwo_mem
#print axioms gDecide_far_mem
#print axioms gDecide_knob_one
#print axioms gDecide_bundle_one
#print axioms gDecideHom_xOne
#print axioms gDecide_tower_one
#print axioms gDecide_reach_le_ker
#print axioms gDecide_triple_not_mem
#print axioms gDecide_x0_not_mem
#print axioms gDecide_sigma_not_mem
#print axioms gDecide_not_xOneTriple
#print axioms gDecideNu
#print axioms gDecideNu_sigma
#print axioms gDecideNu_x0
#print axioms gDecide_not_baseResidual
#print axioms gDecide_triple_mem_three
#print axioms gDecide_not_layerReach
#print axioms gDecide_not_joinBase

end AxiomPins

end SqCore

end Dyadic

end GQ2

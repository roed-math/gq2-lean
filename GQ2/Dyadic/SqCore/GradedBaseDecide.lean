/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedJoinBase

/-!
# W77-DECIDE: the depth-two residual is false, at every `h`

Wave 76 reduced `GJoinBase h` to `GBaseResidual h`, the `2 + 2h` layer classes with content
`⁅⁅x₁, xᵢ⁆, x₁⁆ ∈ gTowerReach h ν' 2` (the family is indexed by all `sqRank h = 3 + 2h` letters,
but `gDecide_triple_self` below puts the `x₁` one in the reach for free at every `h`), and
argued **outside the tree**, from Labute's
structure theorem for `gr(D_sq h)`, that two of them are unreachable.  This file proves that,
inside the tree and with no structure theorem, from a single finite group:

```
gDecide_not_baseResidual : ¬ GBaseResidual h
gDecide_not_layerReach   : ¬ GTowerLayerReach h (gDecideNu h) 2
gDecide_not_joinBase     : ¬ GJoinBase h
```

The witness is the generalized quaternion group `Q₁₆` of order sixteen, with two markings of
`D_sq h` that both kill the relator.  In each, the whole depth-`2` reach maps to `1` and one
of the two residual classes maps to the central involution.

**Scope.**  This is a statement about wave 74's depth-`2` inventory
`gTowerKnobSet`/`gTowerTowSet`, nothing more.  `SqClassClearingSupply h k` is untouched: the
same kind of finding as wave 74's `gDelta_cfourCmp_span_hyp_false`, a route's sufficient
condition failing while the residual stands.  The refutation is in fact **stronger** than the
wave-76 argument, since it never uses `GTowerAdm`'s row conditions: see §5.

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

/-! ## §3 The lower `2`-central tower of `Q₁₆` stops at four

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

/-! ## §4 Two markings of `Q₁₆` by the letters of `D_sq h`, at every `h`

Both send `x₁ ↦ Y`, every handle letter to `1`, and the two core far letters into `⟨X⟩`; both
kill the relator, because on the committed standard shape `sqMark` the handles drop out
(`sqRelWord_sqMark`) and the core word collapses:

* `σ ↦ 1`, `x₀ ↦ X`: `sqWord 1 X Y = X⁻⁴·Y² = 1`;
* `σ ↦ X`, `x₀ ↦ 1`: `sqWord X 1 Y = Y²·⁅Y, Y^X⁆ = X⁴·X⁴ = 1`.

The first sees `⁅x₁, x₀⁆`, the second sees `⁅x₁, σ⁆`; between them they cover the whole
wave-76 residual. -/

section Markings

variable (h : ℕ)

/-- The marking `σ ↦ 1`, `x₀ ↦ X`, `x₁ ↦ Y`: the one that sees the `x₀` class. -/
def gDecideMarkX : Fin (sqRank h) → GDecideQ := sqMark 1 gDecideX gDecideY

/-- The marking `σ ↦ X`, `x₀ ↦ 1`, `x₁ ↦ Y`: the one that sees the `σ` class. -/
def gDecideMarkS : Fin (sqRank h) → GDecideQ := sqMark gDecideX 1 gDecideY

theorem gDecideMarkX_rel : sqRelWord (gDecideMarkX h) = 1 := by
  rw [gDecideMarkX, sqRelWord_sqMark]; decide

theorem gDecideMarkS_rel : sqRelWord (gDecideMarkS h) = 1 := by
  rw [gDecideMarkS, sqRelWord_sqMark]; decide

end Markings

/-! ## §5 The classifying hom, and the collapse of the whole depth-two reach

Three families, three collapses, none of them using the row conditions:

* **knobs** `⁅t, q⁆`: the correction `t` lands in `λ₂(Q₁₆) = ⟨X²⟩` and the far slot `q` lands
  in `⟨X⟩`, which is abelian, so the bracket is `1`;
* **bundles** `t²·⁅t, x₁⁆`: for `t ↦ X^{2k}` this is `X^{4k}·X^{-4k} = 1`, exactly the
  cancellation the wave-76 note calls the vacuous bundle;
* **towers** `x̃₁^{4a}` and the Eichler-cleared handle towers: `x̃₁ ↦ Y·(m x₀)⁻²`, of order
  four, and at a marking whose handle rows vanish the Eichler letters are the plain handle
  letters, which go to `1`.

Dropping the admissibility hypotheses is deliberate: `GTowerAdm`'s row conditions are never
used, so the refutation is **stronger** than the wave-76 argument, which needs them to cut
`W` down to `⟨x₁⟩`. -/

section Model

open scoped commutatorElement

variable {h : ℕ} {m : Fin (sqRank h) → GDecideQ} (hrel : sqRelWord m = 1)
  {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- What a marking of `Q₁₆` must satisfy for the depth-`2` reach to collapse: `x₁ ↦ Y`, the
two core far letters into `⟨X⟩`, every handle letter to `1`. -/
def GDecideGoodMark (m : Fin (sqRank h) → GDecideQ) : Prop :=
  GDecideInA (m 0) ∧ GDecideInA (m 1) ∧ m 2 = gDecideY ∧
    (∀ j : Fin h, m (sqHandleIdxU j) = 1) ∧ (∀ j : Fin h, m (sqHandleIdxV j) = 1)

/-- ⭐⭐⭐ **The classifying hom** `D_sq h → Q₁₆` at a relator-killing marking, through the
presentation's universal property `sqLiftHom`. -/
noncomputable def gDecideHom : ContinuousMonoidHom (DSq h : Type) GDecideQ :=
  sqLiftHom h gDecideQ_isProP m hrel

@[simp] theorem gDecideHom_gen (i : Fin (sqRank h)) : gDecideHom hrel (sqGen h i) = m i :=
  sqLiftHom_gen h gDecideQ_isProP m hrel i

@[simp] theorem gDecideHom_sigma : gDecideHom hrel (dsqSigma h) = m 0 := gDecideHom_gen hrel 0

@[simp] theorem gDecideHom_x0 : gDecideHom hrel (dsqX0 h) = m 1 := gDecideHom_gen hrel 1

@[simp] theorem gDecideHom_x1 : gDecideHom hrel (dsqX1 h) = m 2 := gDecideHom_gen hrel 2

theorem gDecide_map_lambda (k : ℕ) {g : (DSq h : Type)}
    (hg : g ∈ twoCentralSeries (DSq h : Type) k) :
    gDecideHom hrel g ∈ twoCentralSeries GDecideQ k :=
  map_twoCentralSeries_le (gDecideHom hrel).toMonoidHom (gDecideHom hrel).continuous_toFun k
    ⟨g, hg, rfl⟩

/-- ⭐ **The descent to `Q₄`**: `λ₄(Q₁₆) = 1`, so the classifying hom factors through the
level quotient in which the whole depth-`2` reach lives. -/
noncomputable def gDecideQuot : levelQuot (DSq h : Type) 4 →* GDecideQ :=
  QuotientGroup.lift (twoCentralSeries (DSq h : Type) 4) (gDecideHom hrel).toMonoidHom
    (fun g hg => by
      have hb := gDecide_map_lambda hrel 4 hg
      rwa [gDecide_lambdaFour, Subgroup.mem_bot] at hb)

@[simp] theorem gDecideQuot_levelMk (g : (DSq h : Type)) :
    gDecideQuot hrel (levelMk (DSq h : Type) 4 g) = gDecideHom hrel g := rfl

theorem gDecideHom_commP (a b : (DSq h : Type)) :
    gDecideHom hrel (commP a b) = commP (gDecideHom hrel a) (gDecideHom hrel b) := by
  simp only [commP, map_mul, map_inv]

/-- The image of `γ₂(D_sq h)` lands in `⟨X²⟩`. -/
theorem gDecide_gammaTwo_mem {t : (DSq h : Type)}
    (ht : t ∈ twoCentralSeries (DSq h : Type) 2) : GDecideInA2 (gDecideHom hrel t) :=
  gDecide_lambdaTwo (gDecide_map_lambda hrel 2 ht)

/-- The image of the `x₁`-free letter span lands in the abelian `⟨X⟩`. -/
theorem gDecide_far_mem (hm : GDecideGoodMark m) {q : (DSq h : Type)}
    (hq : q ∈ gTowerFar h) : GDecideInA (gDecideHom hrel q) := by
  have hle : gTowerFar h ≤ Subgroup.comap (gDecideHom hrel).toMonoidHom gDecideA := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.closure_le _ |>.2 ?_) ?_
    · rintro x hx
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at hx
      rcases hx with ((rfl | rfl) | ⟨j, rfl⟩) | ⟨j, rfl⟩
      · exact show GDecideInA (gDecideHom hrel (dsqSigma h)) by
          rw [gDecideHom_sigma]; exact hm.1
      · exact show GDecideInA (gDecideHom hrel (dsqX0 h)) by rw [gDecideHom_x0]; exact hm.2.1
      · exact show GDecideInA (gDecideHom hrel (sqGen h (sqHandleIdxU j))) by
          rw [gDecideHom_gen, hm.2.2.2.1 j]; exact (by decide : GDecideInA (1 : GDecideQ))
      · exact show GDecideInA (gDecideHom hrel (sqGen h (sqHandleIdxV j))) by
          rw [gDecideHom_gen, hm.2.2.2.2 j]; exact (by decide : GDecideInA (1 : GDecideQ))
    · exact (isClosed_discrete (gDecideA : Set GDecideQ)).preimage
        (gDecideHom hrel).continuous_toFun
  exact hle hq

/-- ⭐⭐ **The knobs die**: both slots land in the cyclic `⟨X⟩`. -/
theorem gDecide_knob_one (hm : GDecideGoodMark m) {t q : (DSq h : Type)}
    (ht : t ∈ twoCentralSeries (DSq h : Type) 2) (hq : q ∈ gTowerFar h) :
    gDecideHom hrel (commP t q) = 1 := by
  rw [gDecideHom_commP]
  exact (by decide : ∀ u v : GDecideQ, GDecideInA2 u → GDecideInA v → commP u v = 1) _ _
    (gDecide_gammaTwo_mem hrel ht) (gDecide_far_mem hrel hm hq)

/-- ⭐⭐ **The bundles die**: `X^{4k} · X^{-4k} = 1`, the wave-76 cancellation, verified. -/
theorem gDecide_bundle_one (hm : GDecideGoodMark m) {t : (DSq h : Type)}
    (ht : t ∈ twoCentralSeries (DSq h : Type) 2) :
    gDecideHom hrel (t ^ 2 * commP t (dsqX1 h)) = 1 := by
  rw [map_mul, map_pow, gDecideHom_commP, gDecideHom_x1, hm.2.2.1]
  exact (by decide : ∀ u : GDecideQ, GDecideInA2 u → u ^ 2 * commP u gDecideY = 1) _
    (gDecide_gammaTwo_mem hrel ht)

/-- The cleared letter `x̃₁ = x₁·x₀⁻²` maps to `Y·(m x₀)⁻²`. -/
theorem gDecideHom_xOne : gDecideHom hrel (gTowerXOne h) = m 2 * ((m 1) ^ 2)⁻¹ := by
  rw [gTowerXOne, map_mul, map_inv, gDecideHom_x1,
    map_zpowZtwo (isProP_DSq h) gDecideQ_isProP (gDecideHom hrel) (dsqX0 h) 2, gDecideHom_x0,
    show ((2 : ℤ_[2])) = ((2 : ℕ) : ℤ_[2]) by norm_num, zpowZtwo_natCast]

/-- ⭐⭐ **Every cleared letter has order dividing four in `Q₁₆`**, at a marking whose handle
rows vanish: `x̃₁ ↦ Y·X^{-2k}`, and the Eichler letters are the plain handle letters. -/
theorem gDecide_xLetter_pow (hm : GDecideGoodMark m)
    (hu : ∀ j : Fin h, nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : ∀ j : Fin h, nu' (sqGen h (sqHandleIdxV j)) = 1)
    {x : (DSq h : Type)} (hx : x ∈ gTowerXLetters h nu') :
    (gDecideHom hrel x) ^ 4 = 1 := by
  simp only [gTowerXLetters, Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at hx
  rcases hx with (rfl | ⟨j, rfl⟩) | ⟨j, rfl⟩
  · rw [gDecideHom_xOne, hm.2.2.1]
    exact (by decide : ∀ u : GDecideQ, GDecideInA u → (gDecideY * (u ^ 2)⁻¹) ^ 4 = 1) _ hm.2.1
  · rw [sqEichU, map_mul, map_inv, gDecideHom_gen, hm.2.2.2.1 j, hu j, toAdd_one,
      show ((0 : ℤ_[2])) = ((0 : ℕ) : ℤ_[2]) by norm_num,
      map_zpowZtwo (isProP_DSq h) gDecideQ_isProP, zpowZtwo_natCast]
    simp
  · rw [sqEichV, map_mul, map_inv, gDecideHom_gen, hm.2.2.2.2 j, hv j, toAdd_one,
      show ((0 : ℤ_[2])) = ((0 : ℕ) : ℤ_[2]) by norm_num,
      map_zpowZtwo (isProP_DSq h) gDecideQ_isProP, zpowZtwo_natCast]
    simp

/-- ⭐⭐ **The towers die.** -/
theorem gDecide_tower_one (hm : GDecideGoodMark m)
    (hu : ∀ j : Fin h, nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : ∀ j : Fin h, nu' (sqGen h (sqHandleIdxV j)) = 1)
    {x : (DSq h : Type)} (hx : x ∈ gTowerXLetters h nu') (a : ℤ_[2]) :
    gDecideHom hrel (zpowZtwo (isProP_DSq h) x ((2 : ℤ_[2]) ^ 2 * a)) = 1 := by
  rw [map_zpowZtwo (isProP_DSq h) gDecideQ_isProP (gDecideHom hrel) _ _,
    ← zpowZtwo_zpowZtwo gDecideQ_isProP,
    show ((2 : ℤ_[2]) ^ 2) = ((4 : ℕ) : ℤ_[2]) by norm_num, zpowZtwo_natCast,
    gDecide_xLetter_pow hrel hm hu hv hx, zpowZtwo_one_base]

/-- ⭐⭐⭐ **The whole depth-two reach lies in the kernel.**  No admissibility is used: the
statement holds for every `γ₂`-correction, not only the exactly row-trivial ones. -/
theorem gDecide_reach_le_ker (hm : GDecideGoodMark m)
    (hu : ∀ j : Fin h, nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : ∀ j : Fin h, nu' (sqGen h (sqHandleIdxV j)) = 1) :
    gTowerReach h nu' 2 ≤ MonoidHom.ker (gDecideQuot hrel) := by
  refine Subgroup.closure_le _ |>.2 ?_
  rintro z ((⟨t, q, ht, hq, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨x, hx, a, rfl⟩)
  · exact gDecide_knob_one hrel hm ht.1 hq
  · exact gDecide_bundle_one hrel hm ht.1
  · exact gDecide_tower_one hrel hm hu hv hx a

include hrel in
/-- ⭐⭐⭐ **The separation criterion.**  If the marking sees the letter `xᵢ` as `X`, the class
`⁅⁅x₁, xᵢ⁆, x₁⁆` reads `Z ≠ 1` while the whole reach reads `1`. -/
theorem gDecide_triple_not_mem (hm : GDecideGoodMark m)
    (hu : ∀ j : Fin h, nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : ∀ j : Fin h, nu' (sqGen h (sqHandleIdxV j)) = 1)
    {i : Fin (sqRank h)} (hi : m i = gDecideX) :
    commP (commP (gBaseT h) (levelMk (DSq h : Type) 4 (sqGen h i))) (gBaseT h)
      ∉ gTowerReach h nu' 2 := by
  intro hmem
  have hker := gDecide_reach_le_ker hrel hm hu hv hmem
  rw [MonoidHom.mem_ker] at hker
  rw [show gBaseT h = levelMk (DSq h : Type) 4 (dsqX1 h) from rfl, ← gBase_levelMk_triple,
    gDecideQuot_levelMk, gDecideHom_commP, gDecideHom_commP, gDecideHom_x1, gDecideHom_gen,
    hi, hm.2.2.1] at hker
  exact absurd hker (by decide)

end Model

/-! ## §6 The selected marking with vanishing handle rows -/

section Selected

variable (h : ℕ)

/-- The selected marking `ν'(σ) = 1`, `ν'(x₀) = 0` with every handle row zero (and
`ν'(x₁) = 0`, which the relator forces).  It exists at every `h`. -/
noncomputable def gDecideNu : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
  sqLiftHom h PropOneOne.isProP_two_multPadicInt
    (sqMark (ofAdd (1 : ℤ_[2])) (ofAdd (0 : ℤ_[2])) (ofAdd (0 : ℤ_[2])))
    (by rw [sqRelWord_sqMark, sqWord_comm]; simp)

@[simp] theorem gDecideNu_sigma : gDecideNu h (dsqSigma h) = ofAdd (1 : ℤ_[2]) :=
  (sqLiftHom_gen h _ _ _ 0).trans (sqMark_zero _ _ _)

@[simp] theorem gDecideNu_x0 : gDecideNu h (dsqX0 h) = ofAdd (0 : ℤ_[2]) :=
  (sqLiftHom_gen h _ _ _ 1).trans (sqMark_one _ _ _)

theorem gDecideNu_handleU (j : Fin h) : gDecideNu h (sqGen h (sqHandleIdxU j)) = 1 :=
  (sqLiftHom_gen h _ _ _ _).trans (sqMark_handleU _ _ _ j)

theorem gDecideNu_handleV (j : Fin h) : gDecideNu h (sqGen h (sqHandleIdxV j)) = 1 :=
  (sqLiftHom_gen h _ _ _ _).trans (sqMark_handleV _ _ _ j)

end Selected

/-! ## §7 The decision: both residual classes are unreachable, at every `h` -/

section Decision

variable (h : ℕ)

theorem gDecideMarkX_good : GDecideGoodMark (gDecideMarkX h) :=
  ⟨by rw [gDecideMarkX, sqMark_zero]; decide, by rw [gDecideMarkX, sqMark_one]; decide,
    by rw [gDecideMarkX, sqMark_two], fun j => by rw [gDecideMarkX, sqMark_handleU],
    fun j => by rw [gDecideMarkX, sqMark_handleV]⟩

theorem gDecideMarkS_good : GDecideGoodMark (gDecideMarkS h) :=
  ⟨by rw [gDecideMarkS, sqMark_zero]; decide, by rw [gDecideMarkS, sqMark_one]; decide,
    by rw [gDecideMarkS, sqMark_two], fun j => by rw [gDecideMarkS, sqMark_handleU],
    fun j => by rw [gDecideMarkS, sqMark_handleV]⟩

/-- ⭐⭐⭐ **The `x₀` class is not reachable**:
`⁅⁅x₁, x₀⁆, x₁⁆ ∉ gTowerReach h (gDecideNu h) 2`, at the selected marking of §6.  (One marking
is all a refutation of the marking-quantified `GBaseResidual h` needs; §7's last theorem gives
`h = 0` at every marking.) -/
theorem gDecide_x0_not_mem :
    commP (commP (gBaseT h) (gBaseX h)) (gBaseT h) ∉ gTowerReach h (gDecideNu h) 2 :=
  gDecide_triple_not_mem (gDecideMarkX_rel h) (gDecideMarkX_good h) (gDecideNu_handleU h)
    (gDecideNu_handleV h) (i := 1) (by rw [gDecideMarkX, sqMark_one])

/-- ⭐⭐⭐ **The `σ` class is not reachable**:
`⁅⁅x₁, σ⁆, x₁⁆ ∉ gTowerReach h (gDecideNu h) 2`, at the same selected marking. -/
theorem gDecide_sigma_not_mem :
    commP (commP (gBaseT h) (gBaseS h)) (gBaseT h) ∉ gTowerReach h (gDecideNu h) 2 :=
  gDecide_triple_not_mem (gDecideMarkS_rel h) (gDecideMarkS_good h) (gDecideNu_handleU h)
    (gDecideNu_handleV h) (i := 0) (by rw [gDecideMarkS, sqMark_zero])

/-- ⭐⭐⭐ **The wave-76 residual is FALSE at every `h`.**  Both classes fail, so the
two-dimensional gap of the wave-76 note's §4 is a theorem, and it needed no structure theorem:
one group of order sixteen and two markings. -/
theorem gDecide_not_xOneTriple : ¬ GBaseXOneTriple h (gDecideNu h) :=
  fun H => gDecide_x0_not_mem h (H 1)

/-- ⭐⭐⭐ **`GBaseResidual h` is FALSE, at every `h`.** -/
theorem gDecide_not_baseResidual : ¬ GBaseResidual h :=
  fun H => gDecide_not_xOneTriple h (H (gDecideNu h) (gDecideNu_sigma h) (gDecideNu_x0 h))

/-- The `x₀` residual class is an exactly row-trivial `γ₃`-element, so it is inside what
`GTowerLayerReach h ν' 2` quantifies over: the failure is not a quantifier artefact. -/
theorem gDecide_triple_mem_three :
    commP (commP (dsqX1 h) (dsqX0 h)) (dsqX1 h) ∈ twoCentralSeries (DSq h : Type) 3 :=
  cfour_commP_mem_three (cfour_commP_mem_two _ _) _

/-- ⭐⭐⭐ **`GTowerLayerReach h ν' 2` is FALSE**: wave 74's depth-`2` layer statement itself,
not merely wave 76's sufficient condition for it. -/
theorem gDecide_not_layerReach : ¬ GTowerLayerReach h (gDecideNu h) 2 := by
  intro H
  have hadm := gBase_adm_commP (h := h) (nu' := gDecideNu h)
    (commP (dsqX1 h) (dsqX0 h)) (dsqX1 h)
  have hmem := H _ (gDecide_triple_mem_three h) hadm.2.1 hadm.2.2
  rw [gBase_levelMk_triple] at hmem
  exact gDecide_x0_not_mem h hmem

/-- ⭐⭐⭐ **`GJoinBase h` is FALSE, at every `h`**: wave 75's first named input to
`SqLamMarkTransitivity` fails outright. -/
theorem gDecide_not_joinBase : ¬ GJoinBase h :=
  fun H => gDecide_not_layerReach h (H (gDecideNu h) (gDecideNu_sigma h) (gDecideNu_x0 h))

/-- ⭐⭐ **At `h = 0` the layer statement fails at every marking**, selected or not: there are
no handle letters, so the two hypotheses on `ν'` are vacuous. -/
theorem gDecide_not_layerReach_zero
    (nu' : ContinuousMonoidHom (DSq 0 : Type) (Multiplicative ℤ_[2])) :
    ¬ GTowerLayerReach 0 nu' 2 := by
  intro H
  have hadm := gBase_adm_commP (h := 0) (nu' := nu') (commP (dsqX1 0) (dsqX0 0)) (dsqX1 0)
  have hmem := H _ (gDecide_triple_mem_three 0) hadm.2.1 hadm.2.2
  rw [gBase_levelMk_triple] at hmem
  exact gDecide_triple_not_mem (gDecideMarkX_rel 0) (gDecideMarkX_good 0) (fun j => j.elim0)
    (fun j => j.elim0) (i := 1) (by rw [gDecideMarkX, sqMark_one]) hmem

end Decision

/-! ## §8 The depth-three re-cut, stated

Wave 76's item 2 was to re-cut the base one level up.  The engine step really does restart
from any `k₀ ≥ 2` (`gTower_layerReach_step` carries `2 ≤ k`, not `k = 2`), and
`gDecide_layerReach_of_baseAt` packages that; the committed `gTower_layerReach_of_base` is
stated only at `k₀ = 2`, so the re-cut needs this restatement.

What it does **not** give is recorded in the lane note: the supply recursion
`gJoin_supply_of_vanishing` seeds at the committed class-three witness `gJoin_chiSupply_three`
and runs `gJoin_clear_step` at `k = K + 2`, so its **first** step consumes the vanishing at
`k = 2`.  A depth-`3` base supplies the layer statement only for `k ≥ 3`, hence the vanishing
only for `k ≥ 3`, hence nothing that seeds the recursion.  A depth-`3` re-cut therefore needs a
**class-four** supply witness as well - which is the wave-69-to-73 open question. -/

section DepthThree

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

variable (h) in
/-- **The depth-`3` base**: `GJoinBase` one level up, at every selected marking.

[W79-HOUSE, as of `527adf51`: clause added so that naming `GJoinBase` here does not read as
inheriting its status.  `GJoinBase`, the depth-`2` statement, is **refuted** earlier in this file
(`gDecide_not_joinBase`).  `GDecideBaseThree` is the depth-`3` analogue.  It is **open at this
tree** (this file's witness is silent about it, and wave 78 made it the sole layer-side input),
but ⚠⚠ **a refutation is IN FLIGHT and unmerged**: `gDeep_not_baseThree : ¬ GDecideBaseThree h`
at every `h`, on branch `claude/w79-depth3` at `74d01ee9`, together with
`gDeep_not_layerReach` killing `GTowerLayerReach h nu' (k + 2)` at **every** depth and every
marking.  Do not restart this `Prop` as a lane target without checking whether that branch
landed; if it did, `gAbs_markTransitivity_of_baseThree` (`SqCore/GradedAbsorption.lean`) becomes
vacuous and needs the same marker the two `gBase_*_of_residual` composites carry.] -/
def GDecideBaseThree : Prop :=
  ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      GTowerLayerReach h nu' 3

/-- ⭐⭐ **The engine restarts from any base depth `k₀ ≥ 2`.**  The committed
`gTower_layerReach_of_base` is the `k₀ = 2` case; the induction step itself only ever needs
`2 ≤ k`. -/
theorem gDecide_layerReach_of_baseAt {k0 : ℕ} (hk0 : 2 ≤ k0)
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (hbase : GTowerLayerReach h nu' k0) :
    ∀ k, k0 ≤ k → GTowerLayerReach h nu' k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hbase
  | succ k hk ih => exact gTower_layerReach_step (le_trans hk0 hk) hsigma hx0 ih

/-- The depth-`3` base drives the tower from depth `3` upwards. -/
theorem gDecide_tower_of_baseThree (H : GDecideBaseThree h)
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    ∀ k, 3 ≤ k → GTowerLayerReach h nu' k :=
  gDecide_layerReach_of_baseAt (by norm_num) hsigma hx0 (H nu' hsigma hx0)

end DepthThree

/-! ## §9 Axiom pins -/

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
#print axioms GQ2.Dyadic.SqCore.GDecideGoodMark
#print axioms gDecideHom
#print axioms gDecideHom_gen
#print axioms gDecideHom_sigma
#print axioms gDecideHom_x0
#print axioms gDecideHom_x1
#print axioms gDecide_map_lambda
#print axioms gDecideQuot
#print axioms gDecideQuot_levelMk
#print axioms gDecideHom_commP
#print axioms gDecide_gammaTwo_mem
#print axioms gDecide_far_mem
#print axioms gDecide_knob_one
#print axioms gDecide_bundle_one
#print axioms gDecideHom_xOne
#print axioms gDecide_xLetter_pow
#print axioms gDecide_tower_one
#print axioms gDecide_reach_le_ker
#print axioms gDecide_triple_not_mem
#print axioms gDecideNu
#print axioms gDecideNu_sigma
#print axioms gDecideNu_x0
#print axioms gDecideNu_handleU
#print axioms gDecideNu_handleV
#print axioms gDecideMarkX_good
#print axioms gDecideMarkS_good
#print axioms gDecide_x0_not_mem
#print axioms gDecide_sigma_not_mem
#print axioms gDecide_not_xOneTriple
#print axioms gDecide_not_baseResidual
#print axioms gDecide_triple_mem_three
#print axioms gDecide_not_layerReach
#print axioms gDecide_not_joinBase
#print axioms gDecide_not_layerReach_zero
#print axioms GQ2.Dyadic.SqCore.GDecideBaseThree
#print axioms gDecide_layerReach_of_baseAt
#print axioms gDecide_tower_of_baseThree

end AxiomPins

end SqCore

end Dyadic

end GQ2

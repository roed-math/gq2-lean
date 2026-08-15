/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedClassFiveJoin
import GQ2.Dyadic.SqCore.GradedClassFourCompose
import GQ2.Dyadic.SqCore.GradedClassFourKnob

/-!
# W74-ENGINE: the uniform-in-class tower - rows, the squaring engine, and the level-free knobs

Every committed class (three, four, five) has so far been its own campaign: its own quotient
`Q_k`, its own knob inventory, its own spanning argument.  This file begins the **uniform**
formalization, following Labute, "Classification of Demushkin groups" (Canad. J. Math. 19
(1967)), §2 and §4, whose apparatus the graded route has been re-deriving one class at a time.
The campaign core is his `q = 2`, `n` odd case: `sqRelWord`'s leading form is
`π·ξ_{x₁} - [ξ_{x₀}, ξ_σ] + Σ_j [ξ_{u_j}, ξ_{v_j}]` (his Theorem 3(2) with `2^f = 4`), so the
campaign's `x₁` is his special letter `x₁`, and the `(σ, x₀)`-pair plays his `(x₂, x₃)`.

## §1 The row-kernel grading (his §4 Lemma 1, campaign form)

Labute's `X = ker χ` is here the **exactly row-trivial** subgroup `ker λ ∩ ker ν'`, with
`λ = nuLam` the χ-exponent row and `ν'` the selected marking.  His one-character exact sequence
`0 → gr(X) → gr(F) → πF₂[π] → 0` becomes a TWO-row statement, and it is *cleaner* than his: the
rows are already `ℤ₂`-valued (logged), so no `±1`-torsion adjustment survives at any level, and
the complement is TWO named towers at **every** level `k ≥ 1`:

* `gTower_row_dvd`: every `ℤ₂`-valued row of a `γ_k`-element is divisible by `2^{k-1}` - the
  containment converse to the committed `bridge_row_image`.
* ⭐⭐ `gTower_decomp`: every `g ∈ γ_k` factors **exactly** (not just modulo `γ_{k+1}`) as
  `g = d · x₀^{λ(g)} · w^{ν'(g)}` with `d ∈ γ_k` exactly row-trivial and `w = sqPivot h` the
  pivot.  The two tower exponents are the two rows, `2^{k-1}`-divisible by the row bound, so
  both tower factors are honest `γ_k`-elements.
* `gTower_tower_rows` / `gTower_tower_row_trivial_iff` / `gTower_tower_mem_succ_dvd`: the tower
  coordinates are read off by the rows, so the complement is exactly two-dimensional at every
  level: an `x₀`/`w`-tower product is row-trivial iff both exponents vanish, and it lies in
  `γ_{k+1}` only if both exponents are `2^k`-divisible.

This makes the `x₁`-scarcity structural: `x₁` is **not** one of the complement letters - its
row vector `(2, 0)` is `2`-divisible, so its cleared version `gTowerXOne = x₁·x₀^{-2}` is
exactly row-trivial (`ν'(x₁) = 0` is *forced* at a selected marking by the relator,
`gTower_nu_x1`), and the `x₁`-tower lies on the admissible side of the grading at every level.
The complement letters are `x₀` and the pivot `w`, uniformly in the level.

## §2 The engine: `δ ∘ π = π ∘ δ` (his one line on p. 125, "`δ_i π = π δ_{i-1}` for `i ≥ 3`")

The knob of a squared correction is the square of the knob, one layer up.  Pointwise, level
free, for `t ∈ γ_k` with `k ≥ 2`:

* ⭐⭐⭐ `gTower_engine_bracket`: `commP (t²) g ≡ (commP t g)² mod γ_{k+3}`.  The proof content
  is his Proposition 1(2) at `a = 2`: the exact free identity
  `commP (t²) g = commP t g · commP (commP t g) t · commP t g` (`gTower_engine_free`), whose
  correction term lies in `⁅γ_{k+1}, γ₂⁆ ≤ γ_{k+3}` (`gTower_engine_corr_mem`) - the committed
  `cfive_commutator_lambdaTwo` is exactly deep enough, **including at the marginal `k = 2`**,
  where the correction lands in `γ₅` and the identity is read in `Q₅`.
* ⭐⭐⭐ `gTower_engine_bundle`: the same for the `x₁`-slot bundle:
  `(t²)² · commP (t²) g ≡ (t² · commP t g)² mod γ_{k+3}`.  So **every** slot of the knob
  inventory commutes with squaring, and the whole tower of knob inventories follows from any
  one level: this is the statement that replaces the one-class-per-wave ladder.
* `gTower_sq_congr` / `gTower_sq_slack`: squaring is additive on `γ_k` modulo `γ_{k+2}` and
  blind to a `γ_{k+1}`-factor (his Proposition 2(1) at `i > 1`), the transport laws the
  spanning induction consumes.
* `gTower_comm_near_add` / `gTower_comm_near_slack`: the bracket's near slot is additive on
  `γ_k` and blind to `γ_{k+1}`, modulo `γ_{k+2}` (his Proposition 2(3); the far slot is the
  committed `cfiveCommHom`).

Every hypothesis is pointwise and satisfiable at every layer (the instantiations at `k = 2, 3`
land in the committed class-four and class-five quotients; nothing is claimed through a binder
that a binder check could not distinguish - wave 71's lesson).

## §3 The level-free knob inventory

The five dress lemmas of the class-five file (`cfiveKnob_dress_*`), restated in `Q_{k+2}` for a
correction in `lambdaImage G k (k+2)`, any `k ≥ 2`.  At `k = 2` these recover the class-four
inventory, at `k = 3` the class-five one; from `k = 4` on they are new.  The proofs are the
wave-71 proofs run on the committed level-free calculus (`cfive_*`), plus the two vanishing
statements `gTower_commP_vanish`/`gTower_commP_vanish'` (`⁅γ₂, γ_k⁆ ≤ γ_{k+2}` read in
`Q_{k+2}`), which at `k = 2` degenerate to the abelianness of `Y` that the class-four proofs
used.  ⭐ `gTower_dress_core` composes the three core knobs and `gTower_kills` is the identity
form, both level-free.

## Dictionary against the committed classes

| here (`Q_{k+2}`, `c ∈ lambdaImage G k (k+2)`) | `k = 2` (class four) | `k = 3` (class five) |
| --- | --- | --- |
| `gTower_dress_zero` | `cfour_dress_zero` | `cfiveKnob_dress_zero` |
| `gTower_dress_one` | `cfour_dress_one` | `cfiveKnob_dress_one` |
| `gTower_dress_two` | `cfour_dress_two` | `cfiveKnob_dress_two` |
| `gTower_dress_handleU/V` | `cfourId_dress_handleU/V` | `cfiveKnob_dress_handleU/V` |
| `gTower_sq_dress` | `cfour_sq_mul` collapsed | `gFourFive_sq_dress` |

Lane W74-ENGINE.  New file; no edits to existing files.  Prefix `gTower`.
-/

open Multiplicative

namespace GQ2

open Roe.Labute

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The row-kernel grading

The two rows `λ = nuLam h` and `ν'` are continuous characters into `Multiplicative ℤ₂`.  The
statements of this section are for an **arbitrary** such character where possible, and for the
committed pair where the letter values enter. -/

section RowDivisibility

variable {h : ℕ}

/-- The divisibility locus `c·ℤ₂` is closed: it is the continuous image of the compact `ℤ₂`. -/
theorem gTower_isClosed_dvd (c : ℤ_[2]) : IsClosed {x : ℤ_[2] | c ∣ x} := by
  have himg : {x : ℤ_[2] | c ∣ x} = Set.range (fun y : ℤ_[2] => c * y) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_range]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩
  rw [himg]
  exact (isCompact_range (continuous_const_mul c)).isClosed

variable (h) in
/-- The subgroup of `D_sq h` on which a fixed `ℤ₂`-valued row is `2^m`-divisible. -/
def gTowerRowSub (f : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (m : ℕ) :
    Subgroup (DSq h : Type) where
  carrier := {g | (2 ^ m : ℤ_[2]) ∣ toAdd (f g)}
  one_mem' := by
    simp only [Set.mem_setOf_eq, map_one, toAdd_one]
    exact dvd_zero _
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_mul, toAdd_mul] at ha hb ⊢
    exact dvd_add ha hb
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, map_inv, toAdd_inv] at ha ⊢
    exact ha.neg_right

theorem gTower_mem_rowSub {f : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}
    {m : ℕ} {g : (DSq h : Type)} :
    g ∈ gTowerRowSub h f m ↔ (2 ^ m : ℤ_[2]) ∣ toAdd (f g) := Iff.rfl

/-- The divisibility subgroup is closed: preimage of the closed locus under a continuous row. -/
theorem gTower_isClosed_rowSub (f : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (m : ℕ) : IsClosed ((gTowerRowSub h f m : Subgroup (DSq h : Type)) : Set (DSq h : Type)) := by
  have hset : ((gTowerRowSub h f m : Subgroup (DSq h : Type)) : Set (DSq h : Type))
      = (fun g : (DSq h : Type) => toAdd (f g)) ⁻¹' {x : ℤ_[2] | (2 ^ m : ℤ_[2]) ∣ x} := rfl
  rw [hset]
  exact (gTower_isClosed_dvd _).preimage (continuous_toAdd.comp f.continuous)

/-- Any character of `D_sq h` kills every commutator: the target is commutative. -/
theorem gTower_row_commP (f : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (a b : (DSq h : Type)) : f (commP a b) = 1 := cfourKnob_comm_row f a b

/-- ⭐ **The row bound** (his §4 Lemma 1, containment direction; the converse of the committed
`bridge_row_image`): every `ℤ₂`-valued row of a `γ_k`-element is `2^{k-1}`-divisible.  The
induction is the verbal generation of `γ_{k+1}`: squares double a row, commutators are killed,
and the divisibility locus is closed, so the topological closure costs nothing. -/
theorem gTower_row_dvd (f : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    {k : ℕ} {g : (DSq h : Type)} (hg : g ∈ twoCentralSeries (DSq h : Type) k) :
    (2 ^ (k - 1) : ℤ_[2]) ∣ toAdd (f g) := by
  have hmain : ∀ m : ℕ, twoCentralSeries (DSq h : Type) (m + 1) ≤ gTowerRowSub h f m := by
    intro m
    induction m with
    | zero =>
      intro v _
      rw [gTower_mem_rowSub, pow_zero]
      exact one_dvd _
    | succ m ih =>
      rw [twoCentralSeries_succ (G := (DSq h : Type)) (by omega), twoCentralSucc]
      refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_)
        (gTower_isClosed_rowSub f (m + 1))
      · refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨v, hv, rfl⟩
        rw [SetLike.mem_coe, gTower_mem_rowSub, map_pow, toAdd_pow]
        obtain ⟨c, hc⟩ := (gTower_mem_rowSub).1 (ih hv)
        refine ⟨c, ?_⟩
        rw [hc]
        ring
      · refine Subgroup.commutator_le.2 fun a _ b _ => ?_
        rw [gTower_mem_rowSub, commutatorElement_def]
        have hf : f (a * b * a⁻¹ * b⁻¹) = 1 := by
          refine Multiplicative.toAdd.injective ?_
          simp only [map_mul, map_inv, toAdd_mul, toAdd_inv, toAdd_one]
          ring
        rw [hf, toAdd_one]
        exact dvd_zero _
  match k with
  | 0 =>
    rw [Nat.zero_sub, pow_zero]
    exact one_dvd _
  | (k + 1) =>
    rw [Nat.add_sub_cancel]
    exact (gTower_mem_rowSub).1 (hmain k hg)

end RowDivisibility

section TowerPart

variable {h : ℕ}

/-- A `ℤ₂`-power of an element of a closed subgroup of `D_sq h` stays in the subgroup. -/
theorem gTower_zpow_mem {H : Subgroup (DSq h : Type)}
    (hcl : IsClosed ((H : Subgroup (DSq h : Type)) : Set (DSq h : Type)))
    {x : (DSq h : Type)} (hx : x ∈ H) (u : ℤ_[2]) : zpowZtwo (isProP_DSq h) x u ∈ H := by
  have hle : (Subgroup.closure ({x} : Set (DSq h : Type))).topologicalClosure ≤ H :=
    Subgroup.topologicalClosure_minimal _
      ((Subgroup.closure_le _).2 (by simpa using hx)) hcl
  exact hle (zpowZtwo_mem_topologicalClosure (isProP_DSq h) x u)

/-- A `ℤ₂`-power with `2^{k-1}`-divisible exponent lies in `γ_k` (the committed
`bridge_zpow_pow_two_mem`, with the divisibility as a hypothesis rather than a shape). -/
theorem gTower_zpow_dvd_mem {a : ℤ_[2]} {k : ℕ} (hk : 1 ≤ k)
    (ha : (2 ^ (k - 1) : ℤ_[2]) ∣ a) (g : (DSq h : Type)) :
    zpowZtwo (isProP_DSq h) g a ∈ twoCentralSeries (DSq h : Type) k := by
  obtain ⟨c, rfl⟩ := ha
  have hmem := bridge_zpow_pow_two_mem g (k - 1) c
  rwa [Nat.sub_add_cancel hk] at hmem

variable (h) in
/-- **The two-tower correction** at exponents `(a, b)`: the `x₀`-tower times the pivot tower.
Its rows are exactly `(a, b)` at a selected marking, so it is the canonical transversal of the
row kernel at every level. -/
noncomputable def gTowerTower (a b : ℤ_[2]) : (DSq h : Type) :=
  zpowZtwo (isProP_DSq h) (dsqX0 h) a * zpowZtwo (isProP_DSq h) (sqPivot h) b

/-- The `λ`-row of the tower correction is its first exponent: `λ(x₀) = 1`, `λ(w) = 0`. -/
theorem gTower_tower_nuLam (a b : ℤ_[2]) : toAdd (nuLam h (gTowerTower h a b)) = a := by
  rw [gTowerTower, map_mul, toAdd_mul, toAdd_map_zpowZtwo, toAdd_map_zpowZtwo,
    toAdd_nuLam_sqPivot, nuLam_x0, toAdd_ofAdd, mul_one, mul_zero, add_zero]

/-- The `ν'`-row of the tower correction is its second exponent, at a selected marking:
`ν'(x₀) = 0`, `ν'(w) = 1`. -/
theorem gTower_tower_nu (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (a b : ℤ_[2]) :
    toAdd (nu' (gTowerTower h a b)) = b := by
  rw [gTowerTower, map_mul, toAdd_mul, toAdd_map_zpowZtwo, toAdd_map_zpowZtwo,
    toAdd_nu_sqPivot_selected nu' hsigma hx0, hx0, toAdd_ofAdd, mul_zero, mul_one, zero_add]

/-- **The tower correction is a `γ_k`-element when both exponents are `2^{k-1}`-divisible.** -/
theorem gTower_tower_mem {a b : ℤ_[2]} {k : ℕ} (hk : 1 ≤ k)
    (ha : (2 ^ (k - 1) : ℤ_[2]) ∣ a) (hb : (2 ^ (k - 1) : ℤ_[2]) ∣ b) :
    gTowerTower h a b ∈ twoCentralSeries (DSq h : Type) k :=
  Subgroup.mul_mem _ (gTower_zpow_dvd_mem hk ha _) (gTower_zpow_dvd_mem hk hb _)

/-- ⭐ **Row independence of the two towers**: the tower correction is exactly row-trivial iff
both exponents vanish.  With `gTower_decomp` this is the direct-sum half of the grading: the
complement of the admissible part is *exactly* two-dimensional, at every level. -/
theorem gTower_tower_row_trivial_iff
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (a b : ℤ_[2]) :
    (nuLam h (gTowerTower h a b) = 1 ∧ nu' (gTowerTower h a b) = 1) ↔ a = 0 ∧ b = 0 := by
  constructor
  · rintro ⟨hl, hn⟩
    have hA : a = 0 := by
      have := gTower_tower_nuLam (h := h) a b
      rwa [hl, toAdd_one, eq_comm] at this
    have hB : b = 0 := by
      have := gTower_tower_nu nu' hsigma hx0 a b
      rwa [hn, toAdd_one, eq_comm] at this
    exact ⟨hA, hB⟩
  · rintro ⟨rfl, rfl⟩
    constructor
    · refine Multiplicative.toAdd.injective ?_
      rw [gTower_tower_nuLam, toAdd_one]
    · refine Multiplicative.toAdd.injective ?_
      rw [gTower_tower_nu nu' hsigma hx0, toAdd_one]

/-- ⭐ **The towers inject into every graded layer**: if the tower correction has died to
`γ_{k+1}`, both exponents are `2^k`-divisible.  Contrapositively, a tower with an exponent of
`2`-valuation exactly `k-1` represents a **nonzero** class in `γ_k/γ_{k+1}`, so the complement
of the admissible part has dimension exactly two at every level (`≤` by `gTower_decomp`,
`≥` here). -/
theorem gTower_tower_mem_succ_dvd
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {a b : ℤ_[2]} {k : ℕ}
    (hmem : gTowerTower h a b ∈ twoCentralSeries (DSq h : Type) (k + 1)) :
    (2 ^ k : ℤ_[2]) ∣ a ∧ (2 ^ k : ℤ_[2]) ∣ b := by
  constructor
  · have hd := gTower_row_dvd (nuLam h) hmem
    rwa [Nat.add_sub_cancel, gTower_tower_nuLam] at hd
  · have hd := gTower_row_dvd nu' hmem
    rwa [Nat.add_sub_cancel, gTower_tower_nu nu' hsigma hx0] at hd

/-- ⭐⭐ **The row-kernel grading** (his §4 Lemma 1, campaign form, exact): every `γ_k`-element
factors as an exactly row-trivial `γ_k`-element times the two named towers, with the tower
exponents the two rows of `g` themselves.  No `±1`-letter correction survives at any level: the
campaign rows are already logged, so the statement is uniform in `k ≥ 1` with a complement of
size exactly two. -/
theorem gTower_decomp (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {k : ℕ} (hk : 1 ≤ k)
    {g : (DSq h : Type)} (hg : g ∈ twoCentralSeries (DSq h : Type) k) :
    ∃ d ∈ twoCentralSeries (DSq h : Type) k, nuLam h d = 1 ∧ nu' d = 1 ∧
      g = d * gTowerTower h (toAdd (nuLam h g)) (toAdd (nu' g)) := by
  set a := toAdd (nuLam h g) with ha
  set b := toAdd (nu' g) with hb
  have htow : gTowerTower h a b ∈ twoCentralSeries (DSq h : Type) k :=
    gTower_tower_mem hk (gTower_row_dvd (nuLam h) hg) (gTower_row_dvd nu' hg)
  refine ⟨g * (gTowerTower h a b)⁻¹, Subgroup.mul_mem _ hg (Subgroup.inv_mem _ htow), ?_, ?_, ?_⟩
  · refine Multiplicative.toAdd.injective ?_
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, gTower_tower_nuLam, ← ha, toAdd_one,
      add_neg_cancel]
  · refine Multiplicative.toAdd.injective ?_
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, gTower_tower_nu nu' hsigma hx0, ← hb, toAdd_one,
      add_neg_cancel]
  · rw [inv_mul_cancel_right]

end TowerPart

section XOneLetter

variable {h : ℕ}

/-- ⭐ **`ν'(x₁) = 0` is forced at every selected marking**: apply `ν'` to the relator.  The
abelianized relation is `-4·x̄₀ + 2·x̄₁`, so `2·ν'(x₁) = 4·ν'(x₀) = 0` and `ℤ₂` is a domain.
This is why the `x₁`-letter is on the **admissible** side of the row grading: its row vector is
`(λ, ν') = (2, 0)`, which is `2`-divisible, unlike `x₀`'s `(1, 0)` and the pivot's `(0, 1)`. -/
theorem gTower_nu_x1 (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) : nu' (dsqX1 h) = 1 := by
  have hrel := dsq_relation h
  have happ : sqRelWord (fun i => nu' (sqGen h i)) = 1 := by
    rw [← map_sqRelWord, hrel, map_one]
  rw [sqRelWord_comm] at happ
  have hx0' : nu' (sqGen h 1) = ofAdd (0 : ℤ_[2]) := hx0
  rw [hx0'] at happ
  have hpow : (ofAdd (0 : ℤ_[2]) ^ 4)⁻¹ = 1 := by
    refine Multiplicative.toAdd.injective ?_
    rw [toAdd_inv, toAdd_pow, toAdd_ofAdd, toAdd_one]
    ring
  rw [hpow, one_mul] at happ
  have htoadd : (2 : ℤ_[2]) * toAdd (nu' (sqGen h 2)) = 0 := by
    have := congrArg toAdd happ
    rw [toAdd_pow, toAdd_one] at this
    rw [← this]
    ring
  have hzero : toAdd (nu' (sqGen h 2)) = 0 :=
    (mul_eq_zero.mp htoadd).resolve_left two_ne_zero
  refine Multiplicative.toAdd.injective ?_
  rw [toAdd_one]
  exact hzero

variable (h) in
/-- **The cleared `x₁`-letter** `x̃₁ = x₁ · x₀^{-2}`: the `x₁`-letter with its `λ`-row
subtracted off along `x₀`.  Its rows are exactly trivial at every selected marking
(`ν'(x₁) = 0` being forced), so its towers `x̃₁^{2^{k-1}}` are admissible layer classes at
every level - the `x₁`-scarcity in structural form. -/
noncomputable def gTowerXOne : (DSq h : Type) :=
  dsqX1 h * (zpowZtwo (isProP_DSq h) (dsqX0 h) 2)⁻¹

/-- The `λ`-row of the cleared `x₁`-letter is exactly trivial, unconditionally. -/
theorem gTower_xOne_nuLam : nuLam h (gTowerXOne h) = 1 := by
  refine Multiplicative.toAdd.injective ?_
  rw [gTowerXOne, map_mul, map_inv, toAdd_mul, toAdd_inv, toAdd_map_zpowZtwo, nuLam_x1,
    nuLam_x0, toAdd_ofAdd, toAdd_ofAdd, toAdd_one]
  ring

/-- The `ν'`-row of the cleared `x₁`-letter is exactly trivial at every selected marking. -/
theorem gTower_xOne_nu (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) : nu' (gTowerXOne h) = 1 := by
  refine Multiplicative.toAdd.injective ?_
  rw [gTowerXOne, map_mul, map_inv, toAdd_mul, toAdd_inv, toAdd_map_zpowZtwo,
    gTower_nu_x1 nu' hx0, hx0, toAdd_ofAdd, toAdd_one]
  ring

end XOneLetter

/-! ## §2 The engine: the knob of a squared correction is the square of the knob

His `δ_i π = π δ_{i-1}`, per slot, pointwise, level free.  Throughout `t ∈ γ_k` with `2 ≤ k`
and the identities are read in `Q_{k+3}` - the quotient in which the layer-`(k+1)` knob of the
squared correction `t² ∈ γ_{k+1}` lives. -/

section Engine

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The exact free identity behind his Proposition 1(2) at `a = 2`**:
`(t², g) = (t,g) · ((t,g),t) · (t,g)`, in any group. -/
theorem gTower_engine_free {Q : Type*} [Group Q] (t g : Q) :
    commP (t ^ 2) g = commP t g * commP (commP t g) t * commP t g := by
  rw [pow_two, cfour_commP_mul_left]

/-- **The correction term dies three layers up**: for `t ∈ γ_k` the Hall-Petrescu correction
`((t,g),t)` lies in `⁅γ_{k+1}, γ₂⁆ ≤ γ_{k+3}`, valid from `k = 2` on - the marginal case is
`⁅γ₃, γ₂⁆ ≤ γ₅`, and no deeper commitment is needed. -/
theorem gTower_engine_corr_mem {k : ℕ} (hk : 2 ≤ k) {t : G}
    (ht : t ∈ twoCentralSeries G k) (g : G) :
    commP (commP t g) t ∈ twoCentralSeries G (k + 3) := by
  have h1 : commP t g ∈ twoCentralSeries G (k + 1) := cfive_commP_mem_succ ht g
  have h2 : t ∈ twoCentralSeries G 2 := twoCentralSeries_antitone G hk ht
  have h3 := cfive_commutator_lambdaTwo h1 h2
  have harith : k + 1 + 2 = k + 3 := by omega
  rwa [harith] at h3

/-- ⭐⭐⭐ **The engine, bracket slot**: `commP (t²) g ≡ (commP t g)² mod γ_{k+3}` for
`t ∈ γ_k`, `k ≥ 2`.  The knob a squared correction buys against a fixed far slot is the square
of the knob the correction bought, one layer up.  This is the identity that makes the knob
tower follow from any one committed level. -/
theorem gTower_engine_bracket {k : ℕ} (hk : 2 ≤ k) {t : G}
    (ht : t ∈ twoCentralSeries G k) (g : G) :
    levelMk G (k + 3) (commP (t ^ 2) g) = levelMk G (k + 3) (commP t g ^ 2) := by
  have hcorr : levelMk G (k + 3) (commP (commP t g) t) = 1 :=
    (lim_mem_twoCentralSeries_iff_levelMk (k + 3) _).mp (gTower_engine_corr_mem hk ht g)
  rw [gTower_engine_free, map_mul, map_mul, hcorr, mul_one, map_pow, pow_two]

/-- The engine with the correction in the **far** slot: `commP g (t²) ≡ (commP g t)²`. -/
theorem gTower_engine_bracket' {k : ℕ} (hk : 2 ≤ k) {t : G}
    (ht : t ∈ twoCentralSeries G k) (g : G) :
    levelMk G (k + 3) (commP g (t ^ 2)) = levelMk G (k + 3) (commP g t ^ 2) := by
  have hswap : ∀ a b : G, commP a b = (commP b a)⁻¹ := by
    intro a b
    simp only [commP]
    group
  conv_lhs => rw [hswap g (t ^ 2)]
  conv_rhs => rw [hswap g t]
  rw [map_inv, gTower_engine_bracket hk ht g, inv_pow, map_inv]

/-- **Squaring is additive on `γ_k` modulo `γ_{k+2}`** (his Proposition 2(1) at `i > 1`): the
correction terms of the free square-of-product identity lie in `⁅γ_k, γ₂⁆ ≤ γ_{k+2}`. -/
theorem gTower_sq_congr {k : ℕ} (hk : 2 ≤ k) {t t' : G}
    (ht : t ∈ twoCentralSeries G k) (ht' : t' ∈ twoCentralSeries G k) :
    levelMk G (k + 2) ((t * t') ^ 2) = levelMk G (k + 2) (t ^ 2) * levelMk G (k + 2) (t' ^ 2) := by
  have hc1 : commP t' t ∈ twoCentralSeries G (k + 2) :=
    cfive_commutator_lambdaTwo ht' (twoCentralSeries_antitone G hk ht)
  have hc2 : commP (commP t' t) t' ∈ twoCentralSeries G (k + 2) :=
    twoCentralSeries_antitone G (by omega : k + 2 ≤ k + 3) (cfive_commP_mem_succ hc1 t')
  rw [cfour_sq_mul, map_mul, map_mul, map_mul,
    (lim_mem_twoCentralSeries_iff_levelMk (k + 2) _).mp hc1,
    (lim_mem_twoCentralSeries_iff_levelMk (k + 2) _).mp hc2, mul_one, mul_one]

/-- **Squaring is blind to a `γ_{k+1}`-factor modulo `γ_{k+2}`**: the slack of a layer
representative does not reach the next layer's class. -/
theorem gTower_sq_slack {k : ℕ} (hk : 2 ≤ k) {t u : G}
    (ht : t ∈ twoCentralSeries G k) (hu : u ∈ twoCentralSeries G (k + 1)) :
    levelMk G (k + 2) ((t * u) ^ 2) = levelMk G (k + 2) (t ^ 2) := by
  have hu2 : u ^ 2 ∈ twoCentralSeries G (k + 2) := sq_mem_twoCentralSeries_succ G hu
  have hc1 : commP u t ∈ twoCentralSeries G (k + 3) :=
    cfive_commutator_lambdaTwo hu (twoCentralSeries_antitone G hk ht)
  have hc1' : commP u t ∈ twoCentralSeries G (k + 2) :=
    twoCentralSeries_antitone G (by omega : k + 2 ≤ k + 3) hc1
  have hc2 : commP (commP u t) u ∈ twoCentralSeries G (k + 2) :=
    twoCentralSeries_antitone G (by omega : k + 2 ≤ k + 4) (cfive_commP_mem_succ hc1 u)
  rw [cfour_sq_mul, map_mul, map_mul, map_mul,
    (lim_mem_twoCentralSeries_iff_levelMk (k + 2) _).mp hu2,
    (lim_mem_twoCentralSeries_iff_levelMk (k + 2) _).mp hc1',
    (lim_mem_twoCentralSeries_iff_levelMk (k + 2) _).mp hc2, mul_one, mul_one, mul_one]

/-- **The bracket's near slot is additive on `γ_k` modulo `γ_{k+2}`** (his Proposition 2(3);
the far slot is the committed `cfiveCommHom`). -/
theorem gTower_comm_near_add {k : ℕ} (hk : 2 ≤ k) {t t' : G}
    (ht : t ∈ twoCentralSeries G k) (ht' : t' ∈ twoCentralSeries G k) (q : G) :
    levelMk G (k + 2) (commP (t * t') q)
      = levelMk G (k + 2) (commP t q) * levelMk G (k + 2) (commP t' q) := by
  have hc : commP (commP t q) t' ∈ twoCentralSeries G (k + 2) := by
    have h1 := cfive_commutator_lambdaTwo (cfive_commP_mem_succ ht q)
      (twoCentralSeries_antitone G hk ht')
    exact twoCentralSeries_antitone G (by omega : k + 2 ≤ k + 1 + 2) h1
  rw [cfour_commP_mul_left, map_mul, map_mul,
    (lim_mem_twoCentralSeries_iff_levelMk (k + 2) _).mp hc, mul_one]

/-- **The bracket's near slot is blind to a `γ_{k+1}`-factor modulo `γ_{k+2}`.** -/
theorem gTower_comm_near_slack {k : ℕ} {t u : G}
    (hu : u ∈ twoCentralSeries G (k + 1)) (t' : G) (q : G) (hteq : t' = t * u) :
    levelMk G (k + 2) (commP t' q) = levelMk G (k + 2) (commP t q) := by
  subst hteq
  have hcu : commP u q ∈ twoCentralSeries G (k + 2) := cfive_commP_mem_succ hu q
  have hc : commP (commP t q) u ∈ twoCentralSeries G (k + 2) := by
    have h1 : commP (commP t q) u
        = (commP u (commP t q))⁻¹ := by
      simp only [commP]
      group
    rw [h1]
    exact Subgroup.inv_mem _ (cfive_commP_mem_succ hu (commP t q))
  rw [cfour_commP_mul_left, map_mul, map_mul,
    (lim_mem_twoCentralSeries_iff_levelMk (k + 2) _).mp hc,
    (lim_mem_twoCentralSeries_iff_levelMk (k + 2) _).mp hcu, mul_one, mul_one]

/-- ⭐⭐⭐ **The engine, `x₁`-slot bundle**: `(t²)² · commP (t²) g ≡ (t² · commP t g)² mod
γ_{k+3}` for `t ∈ γ_k`, `k ≥ 2`.  The `x₁`-slot knob (the only slot bundling a square with a
bracket) also commutes with squaring, so **every** slot of the inventory does. -/
theorem gTower_engine_bundle {k : ℕ} (hk : 2 ≤ k) {t : G}
    (ht : t ∈ twoCentralSeries G k) (g : G) :
    levelMk G (k + 3) ((t ^ 2) ^ 2 * commP (t ^ 2) g)
      = levelMk G (k + 3) ((t ^ 2 * commP t g) ^ 2) := by
  have ht2 : t ^ 2 ∈ twoCentralSeries G (k + 1) := sq_mem_twoCentralSeries_succ G ht
  have htg : commP t g ∈ twoCentralSeries G (k + 1) := cfive_commP_mem_succ ht g
  have hc1 : commP (commP t g) (t ^ 2) ∈ twoCentralSeries G (k + 3) := by
    have h1 := cfive_commutator_lambdaTwo htg
      (twoCentralSeries_antitone G (by omega : 2 ≤ k + 1) ht2)
    rwa [(by omega : k + 1 + 2 = k + 3)] at h1
  have hc2 : commP (commP (commP t g) (t ^ 2)) (commP t g) ∈ twoCentralSeries G (k + 3) :=
    twoCentralSeries_antitone G (by omega : k + 3 ≤ k + 4) (cfive_commP_mem_succ hc1 _)
  rw [cfour_sq_mul, map_mul, map_mul, map_mul,
    (lim_mem_twoCentralSeries_iff_levelMk (k + 3) _).mp hc1,
    (lim_mem_twoCentralSeries_iff_levelMk (k + 3) _).mp hc2, mul_one, mul_one,
    map_mul, gTower_engine_bracket hk ht g]

end Engine

/-! ## §3 The level-free knob inventory

The wave-71 class-five dress calculus (`cfiveKnob_dress_*`), restated in `Q_{k+2}` for a
correction in `lambdaImage G k (k+2)`.  The committed level-free calculus (`cfive_*`) already
carries every membership; the only new inputs are the two vanishing statements, which are
`⁅γ₂, γ_k⁆ ≤ γ_{k+2}` read in `Q_{k+2}` and hold at **every** `k`. -/

section LayerCalculus

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {k : ℕ}

/-- Every bracket of `Q_{k+2}` lies in the `γ₂`-image (the generic form of
`gFourFive_commP_mem_lambdaTwo`). -/
theorem gTower_commP_mem_lambdaTwo (p q : levelQuot G (k + 2)) :
    commP p q ∈ lambdaImage G 2 (k + 2) := by
  obtain ⟨a, rfl⟩ := levelMk_surjective G (k + 2) p
  obtain ⟨b, rfl⟩ := levelMk_surjective G (k + 2) q
  exact ⟨commP a b, cfive_commP_mem_succ (Subgroup.mem_top a) b,
    by simp only [commP, map_mul, map_inv]⟩

/-- The `λ`-images are antitone in the depth index. -/
theorem gTower_lambdaImage_le {j j' m : ℕ} (hjj : j' ≤ j) :
    lambdaImage G j m ≤ lambdaImage G j' m :=
  Subgroup.map_mono (twoCentralSeries_antitone G hjj)

/-- **The vanishing that runs every layer**: a bracket of a `γ_k`-image slot against a
`γ₂`-image slot dies in `Q_{k+2}`, at every `k`.  This is `⁅γ_k, γ₂⁆ ≤ γ_{k+2}` downstairs;
at `k = 2` it is the abelianness of `Y` in `Q₄` that the class-four proofs used, and at
`k = 3` it is `gFourFive_commP_vanish`. -/
theorem gTower_commP_vanish {z y : levelQuot G (k + 2)} (hz : z ∈ lambdaImage G k (k + 2))
    (hy : y ∈ lambdaImage G 2 (k + 2)) : commP z y = 1 := by
  obtain ⟨v, hv, rfl⟩ := hz
  obtain ⟨w, hw, rfl⟩ := hy
  have hmem : commP v w ∈ twoCentralSeries G (k + 2) := cfive_commutator_lambdaTwo hv hw
  have := (lim_mem_twoCentralSeries_iff_levelMk (k + 2) _).mp hmem
  rwa [show commP (levelMk G (k + 2) v) (levelMk G (k + 2) w)
    = levelMk G (k + 2) (commP v w) by simp only [commP, map_mul, map_inv]]

/-- The symmetric vanishing, `γ₂`-image slot first. -/
theorem gTower_commP_vanish' {y z : levelQuot G (k + 2)} (hy : y ∈ lambdaImage G 2 (k + 2))
    (hz : z ∈ lambdaImage G k (k + 2)) : commP y z = 1 := by
  have hswap : commP y z = (commP z y)⁻¹ := by
    simp only [commP]
    group
  rw [hswap, gTower_commP_vanish hz hy, inv_one]

/-- The square of a `γ_k`-image slot lands in the top layer of `Q_{k+2}`. -/
theorem gTower_sq_mem_zLayer {c : levelQuot G (k + 2)} (hc : c ∈ lambdaImage G k (k + 2)) :
    c ^ 2 ∈ zLayer G (k + 1) := by
  obtain ⟨v, hv, rfl⟩ := hc
  exact ⟨v ^ 2, sq_mem_twoCentralSeries_succ G hv, by rw [map_pow]⟩

/-- A top-layer element of `Q_{k+2}` commutes with everything. -/
theorem gTower_zLayer_comm {z : levelQuot G (k + 2)} (hz : z ∈ zLayer G (k + 1))
    (x : levelQuot G (k + 2)) : x * z = z * x :=
  (zLayer_commute hz x).symm.eq

/-- A top-layer element kills a bracket from the right slot. -/
theorem gTower_commP_zLayer_right {z : levelQuot G (k + 2)} (hz : z ∈ zLayer G (k + 1))
    (q : levelQuot G (k + 2)) : commP q z = 1 := by
  have hswap : commP q z = (commP z q)⁻¹ := by
    simp only [commP]
    group
  rw [hswap, cfive_commP_zLayer_left hz q, inv_one]

/-- Moving a top-layer factor from the first slot of a five-fold product to the end. -/
theorem gTower_shuffle {z : levelQuot G (k + 2)} (hz : z ∈ zLayer G (k + 1))
    (A B C D E : levelQuot G (k + 2)) : A * z * B * C * D * E = A * B * C * D * E * z := by
  simp only [mul_assoc]
  rw [← gTower_zLayer_comm hz]
  simp only [mul_assoc]

/-- Moving a top-layer factor from the third slot of a five-fold product to the end. -/
theorem gTower_shuffle_mid {z : levelQuot G (k + 2)} (hz : z ∈ zLayer G (k + 1))
    (A B C D E : levelQuot G (k + 2)) : A * B * (C * z) * D * E = A * B * C * D * E * z := by
  simp only [mul_assoc]
  rw [← gTower_zLayer_comm hz]
  simp only [mul_assoc]

/-- A central right factor in the far slot of a bracket is invisible. -/
theorem gTower_drop_right (p q : levelQuot G (k + 2)) {z : levelQuot G (k + 2)}
    (hz : z ∈ zLayer G (k + 1)) : commP p (q * z) = commP p q := by
  rw [cfour_commP_mul_right, gTower_commP_zLayer_right hz p, one_mul,
    gTower_commP_zLayer_right hz (commP p q), mul_one]

/-- **A square with a correction one layer down**: `(p·c)² = p²·(c²·commP c p)`, the correction
central of exponent two (`gFourFive_sq_dress`, level free). -/
theorem gTower_sq_dress {p c : levelQuot G (k + 2)} (hc : c ∈ lambdaImage G k (k + 2)) :
    (p * c) ^ 2 = p ^ 2 * (c ^ 2 * commP c p) := by
  rw [cfour_sq_mul, cfive_commP_zLayer_left (cfive_commP_mem_zLayer_left hc p) c, mul_one,
    mul_assoc]

/-- A top-layer correction is invisible to a square. -/
theorem gTower_sq_zLayer_dress {p z : levelQuot G (k + 2)} (hz : z ∈ zLayer G (k + 1)) :
    (p * z) ^ 2 = p ^ 2 := by
  rw [cfour_sq_mul, cfive_commP_zLayer_left hz p, cfour_one_comm, zLayer_sq G hz, mul_one,
    mul_one, mul_one]

/-- **The fourth power is blind to a correction one layer down**, in the relator's `((·)²)²`
shape (`gFourFive_pow_four_dress`, level free). -/
theorem gTower_pow_four_dress {p c : levelQuot G (k + 2)} (hc : c ∈ lambdaImage G k (k + 2)) :
    ((p * c) ^ 2) ^ 2 = (p ^ 2) ^ 2 := by
  rw [gTower_sq_dress hc,
    gTower_sq_zLayer_dress
      (Subgroup.mul_mem _ (gTower_sq_mem_zLayer hc) (cfive_commP_mem_zLayer_left hc p))]

/-- **The relator's `conjP` factor is blind to a correction of the `x₁`-slot**
(`gFourFive_dress_two_conj_factor`, level free): the two terms it produces cancel in the
exponent-two top layer, the far slot being blind to `γ₂`-images. -/
theorem gTower_conj_factor {p s c : levelQuot G (k + 2)} (hc : c ∈ lambdaImage G k (k + 2)) :
    commP (p * c) (conjP (p * c) s) = commP p (conjP p s) := by
  have hz2 : commP p c ∈ zLayer G (k + 1) := cfive_commP_mem_zLayer_right p hc
  have hinvXY : commP p c * commP c p = 1 := by
    have hi : commP p c = (commP c p)⁻¹ := by
      simp only [commP]
      group
    rw [hi, inv_mul_cancel]
  have hcP : commP c (conjP p s) = commP c p := by
    rw [gFourFive_conj_eq p s, cfive_commP_right_hom hc,
      gTower_commP_vanish hc (gTower_commP_mem_lambdaTwo p s), one_mul]
  have hinner : conjP (p * c) s = conjP p s * c * commP c s := by
    rw [gFourFive_conj_mul_left, gFourFive_conj_eq c s, ← mul_assoc]
  have hmid : commP p (conjP p s * c) = commP p c * commP p (conjP p s) := by
    rw [cfour_commP_mul_right,
      gTower_commP_vanish' (gTower_commP_mem_lambdaTwo p (conjP p s)) hc, mul_one]
  have hkill : commP (commP p c * commP p (conjP p s)) c = 1 := by
    rw [cfour_commP_mul_left (commP p c) (commP p (conjP p s)) c,
      cfive_commP_zLayer_left hz2 c, cfour_one_comm, one_mul, one_mul,
      gTower_commP_vanish' (gTower_commP_mem_lambdaTwo p (conjP p s)) hc]
  have hlast : commP c (conjP p s * c) = commP c p := by
    rw [cfour_commP_mul_right, cfour_comm_self, one_mul,
      cfive_commP_zLayer_left (cfive_commP_mem_zLayer_left hc (conjP p s)) c, mul_one, hcP]
  rw [hinner, gTower_drop_right _ _ (cfive_commP_mem_zLayer_left hc s),
    cfour_commP_mul_left, hmid, hkill, hlast, mul_one, ← gTower_zLayer_comm hz2, mul_assoc,
    hinvXY, mul_one]

end LayerCalculus

section DressLemmas

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {k : ℕ}

/-- ⭐ **The `σ`-slot knob, level free**: a correction one layer down moves the relator of
`Q_{k+2}` by the single bracket `commP c (m 1)`.  At `k = 2` this is `cfour_dress_zero`, at
`k = 3` it is `cfiveKnob_dress_zero`; from `k = 4` on it is new. -/
theorem gTower_dress_zero {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G (k + 2))
    {c : levelQuot G (k + 2)} (hc : c ∈ lambdaImage G k (k + 2))
    (h0 : m' 0 = m 0 * c) (h1 : m' 1 = m 1) (h2 : m' 2 = m 2)
    (hU : ∀ i, m' (sqHandleIdxU i) = m (sqHandleIdxU i))
    (hV : ∀ i, m' (sqHandleIdxV i) = m (sqHandleIdxV i)) :
    sqRelWord m' = sqRelWord m * commP c (m 1) := by
  have hA : commP (m' 0) (m' 1) = commP (m 0) (m 1) * commP c (m 1) := by
    rw [h0, h1, cfour_commP_mul_left,
      gTower_commP_vanish' (gTower_commP_mem_lambdaTwo (m 0) (m 1)) hc, mul_one]
  have hD : commP (m' 2) (conjP (m' 2) (m' 0)) = commP (m 2) (conjP (m 2) (m 0)) := by
    rw [h0, h2, gFourFive_conj_mul_right, gFourFive_conj_eq (conjP (m 2) (m 0)) c,
      gTower_drop_right _ _ (cfive_commP_mem_zLayer_right (conjP (m 2) (m 0)) hc)]
  rw [gFourFive_sqRelWord, gFourFive_sqRelWord, hA, hD, h1, h2]
  simp only [hU, hV]
  exact gTower_shuffle (cfive_commP_mem_zLayer_left hc (m 1)) _ _ _ _ _

/-- ⭐ **The `x₀`-slot knob, level free**: the move is `commP (m 0) c`; the fourth power
contributes nothing. -/
theorem gTower_dress_one {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G (k + 2))
    {c : levelQuot G (k + 2)} (hc : c ∈ lambdaImage G k (k + 2))
    (h0 : m' 0 = m 0) (h1 : m' 1 = m 1 * c) (h2 : m' 2 = m 2)
    (hU : ∀ i, m' (sqHandleIdxU i) = m (sqHandleIdxU i))
    (hV : ∀ i, m' (sqHandleIdxV i) = m (sqHandleIdxV i)) :
    sqRelWord m' = sqRelWord m * commP (m 0) c := by
  have hz : commP (m 0) c ∈ zLayer G (k + 1) := cfive_commP_mem_zLayer_right (m 0) hc
  have hA : commP (m' 0) (m' 1) = commP (m 0) (m 1) * commP (m 0) c := by
    rw [h0, h1, cfour_commP_mul_right,
      gTower_commP_vanish' (gTower_commP_mem_lambdaTwo (m 0) (m 1)) hc, mul_one,
      ← gTower_zLayer_comm hz]
  have hB : ((m' 1 ^ 2) ^ 2)⁻¹ = ((m 1 ^ 2) ^ 2)⁻¹ := by rw [h1, gTower_pow_four_dress hc]
  rw [gFourFive_sqRelWord, gFourFive_sqRelWord, hA, hB, h0, h2]
  simp only [hU, hV]
  exact gTower_shuffle hz _ _ _ _ _

/-- ⭐ **The `x₁`-slot knob, level free**: the move is the bundle `c² · commP c (m 2)`, the
only knob carrying a square, exactly as at classes four and five. -/
theorem gTower_dress_two {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G (k + 2))
    {c : levelQuot G (k + 2)} (hc : c ∈ lambdaImage G k (k + 2))
    (h0 : m' 0 = m 0) (h1 : m' 1 = m 1) (h2 : m' 2 = m 2 * c)
    (hU : ∀ i, m' (sqHandleIdxU i) = m (sqHandleIdxU i))
    (hV : ∀ i, m' (sqHandleIdxV i) = m (sqHandleIdxV i)) :
    sqRelWord m' = sqRelWord m * (c ^ 2 * commP c (m 2)) := by
  have hzc : commP c (m 2) ∈ zLayer G (k + 1) := cfive_commP_mem_zLayer_left hc (m 2)
  have hC : (m' 2) ^ 2 = m 2 ^ 2 * (c ^ 2 * commP c (m 2)) := by rw [h2, gTower_sq_dress hc]
  have hD : commP (m' 2) (conjP (m' 2) (m' 0)) = commP (m 2) (conjP (m 2) (m 0)) := by
    rw [h0, h2, gTower_conj_factor hc]
  rw [gFourFive_sqRelWord, gFourFive_sqRelWord, hC, hD, h0, h1]
  simp only [hU, hV]
  exact gTower_shuffle_mid (Subgroup.mul_mem _ (gTower_sq_mem_zLayer hc) hzc) _ _ _ _ _

/-- A relator whose only change is one handle bracket, changed by a top-layer factor. -/
theorem gTower_dress_handle {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G (k + 2)) (j' : Fin n)
    {z : levelQuot G (k + 2)} (hz : z ∈ zLayer G (k + 1))
    (h0 : m' 0 = m 0) (h1 : m' 1 = m 1) (h2 : m' 2 = m 2)
    (hne : ∀ i, i ≠ j' → commP (m' (sqHandleIdxU i)) (m' (sqHandleIdxV i))
        = commP (m (sqHandleIdxU i)) (m (sqHandleIdxV i)))
    (hj : commP (m' (sqHandleIdxU j')) (m' (sqHandleIdxV j'))
        = commP (m (sqHandleIdxU j')) (m (sqHandleIdxV j')) * z) :
    sqRelWord m' = sqRelWord m * z := by
  have hhandle := cfour_handleWord_update (fun i => m' (sqHandleIdxU i))
    (fun i => m' (sqHandleIdxV i)) (fun i => m (sqHandleIdxU i)) (fun i => m (sqHandleIdxV i))
    j' z (fun i => (zLayer_commute hz _).symm) hne hj
  rw [sqRelWord, sqRelWord, h0, h1, h2, hhandle, ← mul_assoc]

/-- ⭐ **The `u_{j'}`-slot knob, level free**: `commP c (m (sqHandleIdxV j'))`. -/
theorem gTower_dress_handleU {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G (k + 2)) (j' : Fin n)
    {c : levelQuot G (k + 2)} (hc : c ∈ lambdaImage G k (k + 2))
    (h0 : m' 0 = m 0) (h1 : m' 1 = m 1) (h2 : m' 2 = m 2)
    (hUj : m' (sqHandleIdxU j') = m (sqHandleIdxU j') * c)
    (hUne : ∀ i, i ≠ j' → m' (sqHandleIdxU i) = m (sqHandleIdxU i))
    (hV : ∀ i, m' (sqHandleIdxV i) = m (sqHandleIdxV i)) :
    sqRelWord m' = sqRelWord m * commP c (m (sqHandleIdxV j')) := by
  refine gTower_dress_handle m m' j' (cfive_commP_mem_zLayer_left hc _) h0 h1 h2 ?_ ?_
  · intro i hi
    rw [hUne i hi, hV i]
  · rw [hUj, hV j', cfour_commP_mul_left,
      gTower_commP_vanish'
        (gTower_commP_mem_lambdaTwo (m (sqHandleIdxU j')) (m (sqHandleIdxV j'))) hc, mul_one]

/-- ⭐ **The `v_{j'}`-slot knob, level free**: `commP (m (sqHandleIdxU j')) c`. -/
theorem gTower_dress_handleV {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G (k + 2)) (j' : Fin n)
    {c : levelQuot G (k + 2)} (hc : c ∈ lambdaImage G k (k + 2))
    (h0 : m' 0 = m 0) (h1 : m' 1 = m 1) (h2 : m' 2 = m 2)
    (hVj : m' (sqHandleIdxV j') = m (sqHandleIdxV j') * c)
    (hVne : ∀ i, i ≠ j' → m' (sqHandleIdxV i) = m (sqHandleIdxV i))
    (hU : ∀ i, m' (sqHandleIdxU i) = m (sqHandleIdxU i)) :
    sqRelWord m' = sqRelWord m * commP (m (sqHandleIdxU j')) c := by
  refine gTower_dress_handle m m' j' (cfive_commP_mem_zLayer_right _ hc) h0 h1 h2 ?_ ?_
  · intro i hi
    rw [hU i, hVne i hi]
  · rw [hVj, hU j', cfour_commP_mul_right,
      gTower_commP_vanish'
        (gTower_commP_mem_lambdaTwo (m (sqHandleIdxU j')) (m (sqHandleIdxV j'))) hc, mul_one,
      ← gTower_zLayer_comm (cfive_commP_mem_zLayer_right (m (sqHandleIdxU j')) hc)]

/-- ⭐⭐ **The three core knobs composed, level free** (`cfiveKnob_dress_core` at every `k ≥ 2`):
the only cross term is `commP c₀ c₁`, killed because `lambdaImage k ≤ lambdaImage 2` and
`⁅γ₂, γ_k⁆` dies in `Q_{k+2}`. -/
theorem gTower_dress_core {n : ℕ} (hk : 2 ≤ k) (m m' : Fin (sqRank n) → levelQuot G (k + 2))
    {c0 c1 c2 : levelQuot G (k + 2)} (hc0 : c0 ∈ lambdaImage G k (k + 2))
    (hc1 : c1 ∈ lambdaImage G k (k + 2)) (hc2 : c2 ∈ lambdaImage G k (k + 2))
    (h0 : m' 0 = m 0 * c0) (h1 : m' 1 = m 1 * c1) (h2 : m' 2 = m 2 * c2)
    (hU : ∀ i, m' (sqHandleIdxU i) = m (sqHandleIdxU i))
    (hV : ∀ i, m' (sqHandleIdxV i) = m (sqHandleIdxV i)) :
    sqRelWord m' = sqRelWord m *
      (commP c0 (m 1) * commP (m 0) c1 * (c2 ^ 2 * commP c2 (m 2))) := by
  classical
  obtain ⟨mA, hA0, hA1, hA2, hAU, hAV⟩ :
      ∃ mA : Fin (sqRank n) → levelQuot G (k + 2),
        mA 0 = m 0 * c0 ∧ mA 1 = m 1 ∧ mA 2 = m 2 ∧
          (∀ i, mA (sqHandleIdxU i) = m (sqHandleIdxU i)) ∧
            (∀ i, mA (sqHandleIdxV i) = m (sqHandleIdxV i)) := by
    refine ⟨fun i => if (i : ℕ) = 0 then m 0 * c0 else m i, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [sqVal_zero, if_pos]
    · simp only [sqVal_one]
      norm_num
    · simp only [sqVal_two]
      norm_num
    · intro i
      simp only [sqHandleIdxU_val]
      rw [if_neg (by omega)]
    · intro i
      simp only [sqHandleIdxV_val]
      rw [if_neg (by omega)]
  obtain ⟨mB, hB0, hB1, hB2, hBU, hBV⟩ :
      ∃ mB : Fin (sqRank n) → levelQuot G (k + 2),
        mB 0 = mA 0 ∧ mB 1 = mA 1 * c1 ∧ mB 2 = mA 2 ∧
          (∀ i, mB (sqHandleIdxU i) = mA (sqHandleIdxU i)) ∧
            (∀ i, mB (sqHandleIdxV i) = mA (sqHandleIdxV i)) := by
    refine ⟨fun i => if (i : ℕ) = 1 then mA 1 * c1 else mA i, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [sqVal_zero]
      norm_num
    · simp only [sqVal_one, if_pos]
    · simp only [sqVal_two]
      norm_num
    · intro i
      simp only [sqHandleIdxU_val]
      rw [if_neg (by omega)]
    · intro i
      simp only [sqHandleIdxV_val]
      rw [if_neg (by omega)]
  have step0 := gTower_dress_zero m mA hc0 hA0 hA1 hA2 hAU hAV
  have step1 := gTower_dress_one mA mB hc1 hB0 hB1 hB2 hBU hBV
  have step2 := gTower_dress_two mB m' hc2 (by rw [h0, ← hA0, ← hB0])
    (by rw [h1, ← hA1, ← hB1]) (by rw [h2, ← hA2, ← hB2])
    (fun i => by rw [hU i, ← hAU i, ← hBU i]) (fun i => by rw [hV i, ← hAV i, ← hBV i])
  have hknob1 : commP (mA 0) c1 = commP (m 0) c1 := by
    rw [hA0, cfive_commP_left_hom (m 0) c0 hc1,
      gTower_commP_vanish' (gTower_lambdaImage_le hk hc0) hc1, mul_one]
  rw [step2, step1, step0, hknob1, hB2, hA2]
  simp only [mul_assoc]

/-- ⭐ **The level-free obligation, as an identity** (`cfiveKnob_kills` at every `k ≥ 2`): if
the composed knob of a correction one layer down inverts the base relator value, the corrected
relator dies in `Q_{k+2}`. -/
theorem gTower_kills {n : ℕ} (hk : 2 ≤ k) (m m' : Fin (sqRank n) → levelQuot G (k + 2))
    {c0 c1 c2 : levelQuot G (k + 2)} (hc0 : c0 ∈ lambdaImage G k (k + 2))
    (hc1 : c1 ∈ lambdaImage G k (k + 2)) (hc2 : c2 ∈ lambdaImage G k (k + 2))
    (h0 : m' 0 = m 0 * c0) (h1 : m' 1 = m 1 * c1) (h2 : m' 2 = m 2 * c2)
    (hU : ∀ i, m' (sqHandleIdxU i) = m (sqHandleIdxU i))
    (hV : ∀ i, m' (sqHandleIdxV i) = m (sqHandleIdxV i))
    (hkill : commP c0 (m 1) * commP (m 0) c1 * (c2 ^ 2 * commP c2 (m 2))
      = (sqRelWord m)⁻¹) :
    sqRelWord m' = 1 := by
  rw [gTower_dress_core hk m m' hc0 hc1 hc2 h0 h1 h2 hU hV, hkill, mul_inv_cancel]

end DressLemmas

/-! ## §4 The reachable subgroups, and the engine step

His ℌ_i (§4 Lemma 3), campaign form.  For a correction depth `k` the knob values live in the
layer `γ_{k+1}/γ_{k+2}`, read in `Q_{k+2}`:

* **knobs**: brackets `commP t q` of an admissible correction `t` (a `γ_k`-element with both
  rows exactly trivial) against a far slot `q` in the `x₁`-free letter span `gTowerFar`, and
  the `x₁`-slot bundles `t² · commP t x₁`.  The bracket against `x₁` *alone* is deliberately
  **not** a generator: it is the open defect of waves 71-73, and everything below tracks
  exactly how the engine manufactures it one level up.
* **towers**: `2^k`-divisible `ℤ₂`-powers of the `1 + 2h` cleared letters (`x̃₁ = x₁·x₀⁻²`
  and the Eichler-cleared handle letters), the admissible Frobenius towers of §1.

`gTowerReach` is their span; `gTowerFullReach` adds the two non-admissible towers of §1 (the
`x₀`- and pivot-powers), and is the span the *full* layer maps into. -/

section ReachDefs

variable {h : ℕ}

variable (h) in
/-- **The admissible corrections at depth `k`**: `γ_k`-elements with both rows exactly
trivial.  His `X ∩ F_k`. -/
def GTowerAdm (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (k : ℕ)
    (t : (DSq h : Type)) : Prop :=
  t ∈ twoCentralSeries (DSq h : Type) k ∧ nuLam h t = 1 ∧ nu' t = 1

variable (h) in
/-- **The `x₁`-free letter span**: the closed subgroup generated by every letter except `x₁`.
The far slots of the four bracket knobs land here (the frame values differ from the letters by
pivot powers and dressings, both inside this span or blind to the bracket). -/
noncomputable def gTowerFar : Subgroup (DSq h : Type) :=
  (Subgroup.closure ({dsqSigma h, dsqX0 h} ∪ Set.range (fun j => sqGen h (sqHandleIdxU j)) ∪
    Set.range (fun j => sqGen h (sqHandleIdxV j)))).topologicalClosure

variable (h) in
/-- **The cleared letters**: `x̃₁` and the two Eichler-cleared letters of every handle.  All
are exactly row-trivial at a selected marking, and their `2^{k-1}`-divisible `ℤ₂`-powers are
the admissible Frobenius towers of depth `k`. -/
noncomputable def gTowerXLetters (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    Set (DSq h : Type) :=
  {gTowerXOne h} ∪ Set.range (sqEichU h nu') ∪ Set.range (sqEichV h nu')

variable (h) in
/-- **The knob generators at correction depth `k`**, as layer classes in `Q_{k+2}`: brackets
of admissible corrections against the `x₁`-free span, and the `x₁`-slot bundles. -/
def gTowerKnobSet (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (k : ℕ) :
    Set (levelQuot (DSq h : Type) (k + 2)) :=
  {z | ∃ t q, GTowerAdm h nu' k t ∧ q ∈ gTowerFar h ∧
    z = levelMk (DSq h : Type) (k + 2) (commP t q)} ∪
  {z | ∃ t, GTowerAdm h nu' k t ∧
    z = levelMk (DSq h : Type) (k + 2) (t ^ 2 * commP t (dsqX1 h))}

variable (h) in
/-- **The admissible tower generators at correction depth `k`**: `2^k`-divisible `ℤ₂`-powers
of the cleared letters, as layer classes in `Q_{k+2}`. -/
noncomputable def gTowerTowSet (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (k : ℕ) :
    Set (levelQuot (DSq h : Type) (k + 2)) :=
  {z | ∃ x ∈ gTowerXLetters h nu', ∃ a : ℤ_[2],
    z = levelMk (DSq h : Type) (k + 2) (zpowZtwo (isProP_DSq h) x (2 ^ k * a))}

variable (h) in
/-- ⭐ **The reachable subgroup at correction depth `k`** (his ℌ_{k+1}): the span of the knob
values and the admissible towers, inside `Q_{k+2}`. -/
noncomputable def gTowerReach (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (k : ℕ) :
    Subgroup (levelQuot (DSq h : Type) (k + 2)) :=
  Subgroup.closure (gTowerKnobSet h nu' k ∪ gTowerTowSet h nu' k)

variable (h) in
/-- **The non-admissible tower span at correction depth `k`**: `2^k`-divisible two-tower
corrections `x₀^A·w^B`, the §1 complement, as layer classes. -/
noncomputable def gTowerTowXW (k : ℕ) : Subgroup (levelQuot (DSq h : Type) (k + 2)) :=
  Subgroup.closure {z | ∃ A B : ℤ_[2], (2 ^ k : ℤ_[2]) ∣ A ∧ (2 ^ k : ℤ_[2]) ∣ B ∧
    z = levelMk (DSq h : Type) (k + 2) (gTowerTower h A B)}

variable (h) in
/-- **The full reach**: admissible knobs and towers together with the §1 complement towers.
The *full* layer lands here (`gTower_layer_step`); the admissible part lands in
`gTowerReach` alone (`gTower_cut`). -/
noncomputable def gTowerFullReach (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (k : ℕ) : Subgroup (levelQuot (DSq h : Type) (k + 2)) :=
  gTowerReach h nu' k ⊔ gTowerTowXW h k

theorem gTower_reach_le_fullReach
    {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {k : ℕ} :
    gTowerReach h nu' k ≤ gTowerFullReach h nu' k := le_sup_left

/-- Admissible corrections square to admissible corrections one depth up (the §1/§2 row
laws `cfourKnob_sq_nuLam`/`cfourKnob_sq_nu`, packaged). -/
theorem gTower_adm_sq {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}
    {k : ℕ} {t : (DSq h : Type)} (ht : GTowerAdm h nu' k t) : GTowerAdm h nu' (k + 1) (t ^ 2) :=
  ⟨sq_mem_twoCentralSeries_succ (G := (DSq h : Type)) ht.1, cfourKnob_sq_nuLam ht.2.1,
    cfourKnob_sq_nu nu' ht.2.2⟩

/-- Admissible corrections at depth `k` are admissible at every lower depth. -/
theorem gTower_adm_mono {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}
    {k k' : ℕ} (hkk : k' ≤ k) {t : (DSq h : Type)} (ht : GTowerAdm h nu' k t) :
    GTowerAdm h nu' k' t :=
  ⟨twoCentralSeries_antitone (DSq h : Type) hkk ht.1, ht.2.1, ht.2.2⟩

end ReachDefs

section ZpowLaws

variable {h : ℕ}

/-- The square of a `ℤ₂`-power doubles the exponent. -/
theorem gTower_zpow_sq (x : (DSq h : Type)) (u : ℤ_[2]) :
    zpowZtwo (isProP_DSq h) x u ^ 2 = zpowZtwo (isProP_DSq h) x (2 * u) := by
  rw [pow_two, two_mul, zpowZtwo_add]

/-- A `2^k`-divisible `ℤ₂`-power (`k ≥ 1`) is the square of the half-exponent power, itself a
`γ_k`-element.  This is what feeds the tower brackets to the engine. -/
theorem gTower_zpow_half (x : (DSq h : Type)) {a : ℤ_[2]} {k : ℕ} (hk : 1 ≤ k)
    (ha : (2 ^ k : ℤ_[2]) ∣ a) :
    ∃ t : (DSq h : Type), t ∈ twoCentralSeries (DSq h : Type) k ∧
      zpowZtwo (isProP_DSq h) x a = t ^ 2 := by
  obtain ⟨c, rfl⟩ := ha
  match k, hk with
  | (k + 1), _ =>
    refine ⟨zpowZtwo (isProP_DSq h) x (2 ^ k * c),
      gTower_zpow_dvd_mem (by omega) ⟨c, by rw [Nat.add_sub_cancel]⟩ x, ?_⟩
    rw [gTower_zpow_sq]
    congr 1
    ring

end ZpowLaws

/-! ## §5 The engine step: `π` carries reach into reach

The subgroup-level consequence of §2: if the class of an admissible `t ∈ γ_k` lies in the
depth-`(k-1)` reach, the class of `t²` lies in the depth-`k` reach.  The proof is a closure
induction whose generator cases are exactly the three engine identities: bracket knobs square
to bracket knobs of the squared correction, bundles to bundles, towers to towers. -/

section EngineStep

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- **The bracket-knob case of the engine step**: for an admissible `t` at depth `k ≥ 2` and
`q` in the far span, the square of the knob realization `commP t q` reads, one level up, as
the knob of the squared correction - a depth-`(k+1)` knob generator. -/
theorem gTower_step_knob {k : ℕ} (hk : 2 ≤ k) {t q : (DSq h : Type)}
    (ht : GTowerAdm h nu' k t) (hq : q ∈ gTowerFar h) :
    levelMk (DSq h : Type) (k + 3) (commP t q ^ 2) ∈ gTowerKnobSet h nu' (k + 1) := by
  refine Or.inl ⟨t ^ 2, q, gTower_adm_sq ht, hq, ?_⟩
  exact (gTower_engine_bracket hk ht.1 q).symm

/-- **The bundle case of the engine step**: the square of a bundle realization reads, one
level up, as the bundle of the squared correction. -/
theorem gTower_step_bundle {k : ℕ} (hk : 2 ≤ k) {t : (DSq h : Type)}
    (ht : GTowerAdm h nu' k t) :
    levelMk (DSq h : Type) (k + 3) ((t ^ 2 * commP t (dsqX1 h)) ^ 2)
      ∈ gTowerKnobSet h nu' (k + 1) := by
  refine Or.inr ⟨t ^ 2, gTower_adm_sq ht, ?_⟩
  have hb := gTower_engine_bundle hk ht.1 (dsqX1 h)
  rw [← pow_mul, (by norm_num : 2 * 2 = 4)] at hb ⊢
  exact hb.symm

/-- **The tower case of the engine step**: the square of an admissible tower is the next
admissible tower. -/
theorem gTower_step_tower {k : ℕ} {x : (DSq h : Type)} (hx : x ∈ gTowerXLetters h nu')
    (a : ℤ_[2]) :
    levelMk (DSq h : Type) (k + 3) (zpowZtwo (isProP_DSq h) x (2 ^ k * a) ^ 2)
      ∈ gTowerTowSet h nu' (k + 1) := by
  refine ⟨x, hx, a, ?_⟩
  rw [gTower_zpow_sq]
  congr 2
  ring

/-- ⭐⭐⭐ **The engine step** (`δ ∘ π = π ∘ δ` at the subgroup level, his Lemma 3 step (a)):
for `k ≥ 2`, any admissible `t ∈ γ_k` whose class lies in the depth-`(k-1)` reach has its
square's class in the depth-`k` reach.  The proof is a closure induction over the reach: the
predicate carries a canonical `γ_k`-realization together with the reach membership of the
square of **every** realization, products go through `gTower_sq_congr`, slack through
`gTower_sq_slack`, and the generators are the three engine cases above. -/
theorem gTower_reach_step {k : ℕ} (hk : 2 ≤ k) {t : (DSq h : Type)}
    (ht : t ∈ twoCentralSeries (DSq h : Type) (k + 1))
    (hmem : levelMk (DSq h : Type) (k + 2) t ∈ gTowerReach h nu' k) :
    levelMk (DSq h : Type) (k + 1 + 2) (t ^ 2) ∈ gTowerReach h nu' (k + 1) := by
  -- the transfer predicate: a canonical realization, and the conclusion for every realization
  set P : levelQuot (DSq h : Type) (k + 2) → Prop := fun z =>
    (∃ s ∈ twoCentralSeries (DSq h : Type) (k + 1),
        levelMk (DSq h : Type) (k + 2) s = z) ∧
      ∀ s ∈ twoCentralSeries (DSq h : Type) (k + 1),
        levelMk (DSq h : Type) (k + 2) s = z →
          levelMk (DSq h : Type) (k + 1 + 2) (s ^ 2) ∈ gTowerReach h nu' (k + 1) with hP
  have hslack : ∀ s₀ ∈ twoCentralSeries (DSq h : Type) (k + 1),
      ∀ s ∈ twoCentralSeries (DSq h : Type) (k + 1),
      levelMk (DSq h : Type) (k + 2) s = levelMk (DSq h : Type) (k + 2) s₀ →
      levelMk (DSq h : Type) (k + 1 + 2) (s ^ 2)
        = levelMk (DSq h : Type) (k + 1 + 2) (s₀ ^ 2) := by
    intro s₀ hs₀ s hs heq
    have hu : s₀⁻¹ * s ∈ twoCentralSeries (DSq h : Type) (k + 1 + 1) := by
      rw [lim_mem_twoCentralSeries_iff_levelMk]
      show levelMk (DSq h : Type) (k + 2) (s₀⁻¹ * s) = 1
      rw [map_mul, map_inv, heq, inv_mul_cancel]
    have hform : s = s₀ * (s₀⁻¹ * s) := by group
    rw [hform, gTower_sq_slack (by omega) hs₀ hu]
  have hgen : ∀ z ∈ gTowerKnobSet h nu' k ∪ gTowerTowSet h nu' k, P z := by
    intro z hz
    simp only [gTowerKnobSet, gTowerTowSet, Set.mem_union, Set.mem_setOf_eq] at hz
    obtain (⟨t', q, ht', hq, rfl⟩ | ⟨t', ht', rfl⟩) | ⟨x, hx, a, rfl⟩ := hz
    · have hreal : commP t' q ∈ twoCentralSeries (DSq h : Type) (k + 1) :=
        cfive_commP_mem_succ ht'.1 q
      refine ⟨⟨_, hreal, rfl⟩, fun s hs heq => ?_⟩
      rw [hslack _ hreal s hs heq]
      exact Subgroup.subset_closure (Or.inl (gTower_step_knob hk ht' hq))
    · have hreal : t' ^ 2 * commP t' (dsqX1 h) ∈ twoCentralSeries (DSq h : Type) (k + 1) :=
        Subgroup.mul_mem _ (sq_mem_twoCentralSeries_succ (G := (DSq h : Type)) ht'.1)
          (cfive_commP_mem_succ ht'.1 _)
      refine ⟨⟨_, hreal, rfl⟩, fun s hs heq => ?_⟩
      rw [hslack _ hreal s hs heq]
      exact Subgroup.subset_closure (Or.inl (gTower_step_bundle hk ht'))
    · have hreal : zpowZtwo (isProP_DSq h) x (2 ^ k * a)
          ∈ twoCentralSeries (DSq h : Type) (k + 1) :=
        gTower_zpow_dvd_mem (by omega) ⟨a, by rw [Nat.add_sub_cancel]⟩ x
      refine ⟨⟨_, hreal, rfl⟩, fun s hs heq => ?_⟩
      rw [hslack _ hreal s hs heq]
      exact Subgroup.subset_closure (Or.inr (gTower_step_tower hx a))
  have hall : ∀ z ∈ gTowerReach h nu' k, P z := by
    intro z hz
    refine Subgroup.closure_induction hgen ?_ ?_ ?_ hz
    · refine ⟨⟨1, Subgroup.one_mem _, map_one _⟩, fun s hs heq => ?_⟩
      have hsm : s ∈ twoCentralSeries (DSq h : Type) (k + 2) := by
        rwa [lim_mem_twoCentralSeries_iff_levelMk]
      have hsq : s ^ 2 ∈ twoCentralSeries (DSq h : Type) (k + 1 + 2) := by
        have := sq_mem_twoCentralSeries_succ (G := (DSq h : Type)) hsm
        rwa [(by omega : k + 2 + 1 = k + 1 + 2)] at this
      rw [(lim_mem_twoCentralSeries_iff_levelMk (k + 1 + 2) _).mp hsq]
      exact Subgroup.one_mem _
    · rintro z₁ z₂ - - ⟨⟨s₁, hs₁, rfl⟩, H₁⟩ ⟨⟨s₂, hs₂, rfl⟩, H₂⟩
      refine ⟨⟨s₁ * s₂, Subgroup.mul_mem _ hs₁ hs₂, map_mul _ _ _⟩, fun s hs heq => ?_⟩
      rw [hslack _ (Subgroup.mul_mem _ hs₁ hs₂) s hs (by rw [heq, map_mul]),
        gTower_sq_congr (by omega) hs₁ hs₂]
      exact Subgroup.mul_mem _ (H₁ s₁ hs₁ rfl) (H₂ s₂ hs₂ rfl)
    · rintro z - ⟨⟨s₁, hs₁, rfl⟩, H⟩
      refine ⟨⟨s₁⁻¹, Subgroup.inv_mem _ hs₁, map_inv _ _⟩, fun s hs heq => ?_⟩
      rw [hslack _ (Subgroup.inv_mem _ hs₁) s hs (by rw [heq, map_inv]), inv_pow, map_inv]
      exact Subgroup.inv_mem _ (H s₁ hs₁ rfl)
  exact (hall _ hmem).2 t ht rfl

end EngineStep

/-! ## §6 The two step obligations: squares and brackets of the full layer

His Lemma 2 and Lemma 3 step (b), campaign form.  Under the layer hypothesis one depth down
(`GTowerLayerReach k`: every exactly row-trivial `γ_{k+1}`-element reaches), every square and
every bracket of a `γ_{k+1}`-element lands in the depth-`(k+1)` full reach.  The `x₁`-bracket
of an admissible correction - the waves-71-to-73 open defect - is manufactured here by the
engine: `[d, x₁] = (d²·[d, x₁]) · (d²)⁻¹`, the bundle knob times the engine-step square. -/

section LayerHypothesis

variable {h : ℕ}

variable (h) in
/-- **The layer statement at correction depth `k`** (his Lemma 3 conclusion for the layer
`γ_{k+1}/γ_{k+2}`): every exactly row-trivial `γ_{k+1}`-element reaches. -/
def GTowerLayerReach (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (k : ℕ) : Prop :=
  ∀ g ∈ twoCentralSeries (DSq h : Type) (k + 1), nuLam h g = 1 → nu' g = 1 →
    levelMk (DSq h : Type) (k + 2) g ∈ gTowerReach h nu' k

end LayerHypothesis

section StepObligations

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- The level quotients of `D_sq h` are discrete, at every level. -/
theorem gTower_discrete (m : ℕ) : DiscreteTopology (levelQuot (DSq h : Type) m) :=
  discreteTopology_levelQuot (DSq h : Type) (lim_dsq_finsetGen h) (isProP_DSq h) m

/-- Every subgroup of a level quotient of `D_sq h` is closed. -/
theorem gTower_isClosed_subgroup {m : ℕ} (S : Subgroup (levelQuot (DSq h : Type) m)) :
    IsClosed ((S : Subgroup (levelQuot (DSq h : Type) m)) : Set (levelQuot (DSq h : Type) m)) := by
  haveI : DiscreteTopology (levelQuot (DSq h : Type) m) := gTower_discrete m
  exact isClosed_discrete _

/-- **The far-slot letter reduction**: for `v ∈ γ_k` the bracket class `[v, g]` lies, for
*every* `g`, in the span of the letter brackets `[v, letters]`.  The bracket against a fixed
`γ_k`-element is the committed homomorphism `cfiveCommHom`; its kernel-side is closed because
the level quotients are discrete, so topological generation by the letters transfers. -/
theorem gTower_commHom_span {k : ℕ} {v : (DSq h : Type)}
    (hv : v ∈ twoCentralSeries (DSq h : Type) k) (g : (DSq h : Type)) :
    levelMk (DSq h : Type) (k + 2) (commP v g) ∈
      Subgroup.closure
        (Set.range (fun i => levelMk (DSq h : Type) (k + 2) (commP v (sqGen h i)))) := by
  haveI : DiscreteTopology (levelQuot (DSq h : Type) (k + 2)) := gTower_discrete (k + 2)
  set S' := Subgroup.closure
    (Set.range (fun i => levelMk (DSq h : Type) (k + 2) (commP v (sqGen h i)))) with hS'
  have hpre : IsClosed ((Subgroup.comap (cfiveCommHom hv) S' :
      Subgroup (DSq h : Type)) : Set (DSq h : Type)) := by
    rw [Subgroup.coe_comap]
    refine IsClosed.preimage ?_ (isClosed_discrete _)
    show Continuous fun g => levelMk (DSq h : Type) (k + 2) (commP v g)
    simp only [commP]
    exact (continuous_levelMk (DSq h : Type) (k + 2)).comp (by fun_prop)
  have hsub : (Subgroup.closure (Set.range (sqGen h))).topologicalClosure ≤
      Subgroup.comap (cfiveCommHom hv) S' := by
    refine Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le _).2 ?_) hpre
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hg : g ∈ (Subgroup.closure (Set.range (sqGen h))).topologicalClosure := by
    rw [dsq_topGen h]
    trivial
  exact hsub hg

/-- The non-`x₁` letters lie in the far span. -/
theorem gTower_letters_mem_far (i : Fin (sqRank h)) (hne : i ≠ 2) :
    sqGen h i ∈ gTowerFar h := by
  refine Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ?_)
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact Or.inl (Or.inl (Or.inl rfl))
  · exact Or.inl (Or.inl (Or.inr rfl))
  · exact absurd rfl hne
  · exact Or.inl (Or.inr ⟨j, rfl⟩)
  · exact Or.inr ⟨j, rfl⟩

/-- ⭐ **The engine manufactures the `x₁`-defect**: for an admissible `d` at depth `k + 1`
(`k ≥ 2`) whose class reaches at depth `k`, the bare bracket class `[d, x₁]` lies in the
depth-`(k+1)` reach: it is the bundle knob times the inverse of the engine-step square.  This
is the statement waves 71, 72 and 73 could not commit at any single class: the split of the
`x₁`-slot bundle costs one level of the tower, not a new idea per class. -/
theorem gTower_comm_x1_split {k : ℕ} (hk : 2 ≤ k) {d : (DSq h : Type)}
    (hd : GTowerAdm h nu' (k + 1) d)
    (hreach : levelMk (DSq h : Type) (k + 2) d ∈ gTowerReach h nu' k) :
    levelMk (DSq h : Type) (k + 1 + 2) (commP d (dsqX1 h)) ∈ gTowerReach h nu' (k + 1) := by
  have hbundle : levelMk (DSq h : Type) (k + 1 + 2) (d ^ 2 * commP d (dsqX1 h))
      ∈ gTowerReach h nu' (k + 1) :=
    Subgroup.subset_closure (Or.inl (Or.inr ⟨d, hd, rfl⟩))
  have hsq : levelMk (DSq h : Type) (k + 1 + 2) (d ^ 2) ∈ gTowerReach h nu' (k + 1) :=
    gTower_reach_step hk hd.1 hreach
  have hsplit : levelMk (DSq h : Type) (k + 1 + 2) (commP d (dsqX1 h))
      = (levelMk (DSq h : Type) (k + 1 + 2) (d ^ 2))⁻¹ *
        levelMk (DSq h : Type) (k + 1 + 2) (d ^ 2 * commP d (dsqX1 h)) := by
    rw [map_mul, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hsplit]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hsq) hbundle

/-- ⭐⭐ **The bracket obligation for admissible elements**: under the layer hypothesis at
depth `k ≥ 2`, the bracket class of an admissible `γ_{k+1}`-element against **any** element
lies in the depth-`(k+1)` reach.  Letter reduction, then per letter: the four non-`x₁`
letters are far-span knobs, and the `x₁`-letter is the engine split. -/
theorem gTower_comm_adm_step {k : ℕ} (hk : 2 ≤ k) (HL : GTowerLayerReach h nu' k)
    {d : (DSq h : Type)} (hd : GTowerAdm h nu' (k + 1) d) (g : (DSq h : Type)) :
    levelMk (DSq h : Type) (k + 1 + 2) (commP d g) ∈ gTowerReach h nu' (k + 1) := by
  have hspan := gTower_commHom_span (k := k + 1) hd.1 g
  refine Subgroup.closure_le (K := gTowerReach h nu' (k + 1)) |>.2 ?_ hspan
  rintro _ ⟨i, rfl⟩
  by_cases hi : i = 2
  · subst hi
    have hreach : levelMk (DSq h : Type) (k + 2) d ∈ gTowerReach h nu' k :=
      HL d hd.1 hd.2.1 hd.2.2
    exact gTower_comm_x1_split hk hd hreach
  · exact Subgroup.subset_closure
      (Or.inl (Or.inl ⟨d, sqGen h i, hd, gTower_letters_mem_far i hi, rfl⟩))

/-- ⭐⭐ **The bracket obligation for tower parts**: under the layer hypothesis at depth
`k ≥ 2`, the bracket class of a `2^k`-divisible `ℤ₂`-power of any element against any element
lies in the depth-`(k+1)` reach.  The tower power is the square of its half (his
`π^{j-1}·ξ = π(π^{j-2}·ξ)`), the engine turns the bracket of the square into the square of
the bracket, and the bracket of the half is exactly row-trivial and one depth down, where the
layer hypothesis applies. -/
theorem gTower_comm_tower_step {k : ℕ} (hk : 2 ≤ k) (HL : GTowerLayerReach h nu' k)
    (x : (DSq h : Type)) {a : ℤ_[2]} (ha : (2 ^ k : ℤ_[2]) ∣ a) (g : (DSq h : Type)) :
    levelMk (DSq h : Type) (k + 1 + 2) (commP (zpowZtwo (isProP_DSq h) x a) g)
      ∈ gTowerReach h nu' (k + 1) := by
  obtain ⟨t, htmem, hteq⟩ := gTower_zpow_half x (by omega) ha
  rw [hteq]
  have hcomm : commP t g ∈ twoCentralSeries (DSq h : Type) (k + 1) :=
    cfive_commP_mem_succ htmem g
  have hrows : nuLam h (commP t g) = 1 ∧ nu' (commP t g) = 1 :=
    ⟨gTower_row_commP _ t g, gTower_row_commP nu' t g⟩
  have hreach : levelMk (DSq h : Type) (k + 2) (commP t g) ∈ gTowerReach h nu' k :=
    HL _ hcomm hrows.1 hrows.2
  have hstep := gTower_reach_step hk hcomm hreach
  have hengine := gTower_engine_bracket hk htmem g
  rw [(by omega : k + 3 = k + 1 + 2)] at hengine
  rw [hengine]
  exact hstep

/-- ⭐⭐ **The square obligation** (his Lemma 3 step (a) assembled over the §1 grading): under
the layer hypothesis at depth `k ≥ 2` and a selected marking, the square class of **any**
`γ_{k+1}`-element lies in the depth-`(k+1)` full reach: the admissible part squares into the
reach by the engine step, and the two §1 towers square into the complement towers. -/
theorem gTower_sq_step {k : ℕ} (hk : 2 ≤ k) (HL : GTowerLayerReach h nu' k)
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {v : (DSq h : Type)}
    (hv : v ∈ twoCentralSeries (DSq h : Type) (k + 1)) :
    levelMk (DSq h : Type) (k + 1 + 2) (v ^ 2) ∈ gTowerFullReach h nu' (k + 1) := by
  obtain ⟨d, hdmem, hdl, hdn, hdec⟩ := gTower_decomp nu' hsigma hx0 (by omega) hv
  set a := toAdd (nuLam h v) with ha
  set b := toAdd (nu' v) with hb
  have hda : (2 ^ k : ℤ_[2]) ∣ a := by
    have := gTower_row_dvd (nuLam h) hv
    rwa [Nat.add_sub_cancel] at this
  have hdb : (2 ^ k : ℤ_[2]) ∣ b := by
    have := gTower_row_dvd nu' hv
    rwa [Nat.add_sub_cancel] at this
  have hxa : zpowZtwo (isProP_DSq h) (dsqX0 h) a ∈ twoCentralSeries (DSq h : Type) (k + 1) :=
    gTower_zpow_dvd_mem (by omega) (by rwa [Nat.add_sub_cancel]) _
  have hwb : zpowZtwo (isProP_DSq h) (sqPivot h) b ∈ twoCentralSeries (DSq h : Type) (k + 1) :=
    gTower_zpow_dvd_mem (by omega) (by rwa [Nat.add_sub_cancel]) _
  have htow : gTowerTower h a b ∈ twoCentralSeries (DSq h : Type) (k + 1) :=
    Subgroup.mul_mem _ hxa hwb
  rw [hdec, gTower_sq_congr (by omega) hdmem htow]
  refine Subgroup.mul_mem _ ?_ ?_
  · -- the admissible part squares into the reach
    have hreach : levelMk (DSq h : Type) (k + 2) d ∈ gTowerReach h nu' k :=
      HL d hdmem hdl hdn
    exact gTower_reach_le_fullReach (gTower_reach_step hk hdmem hreach)
  · -- the tower part squares into the complement towers
    rw [gTowerTower, gTower_sq_congr (by omega) hxa hwb, gTower_zpow_sq, gTower_zpow_sq,
      ← map_mul]
    refine le_sup_right (α := Subgroup _) ?_
    refine Subgroup.subset_closure ⟨2 * a, 2 * b, ?_, ?_, ?_⟩
    · obtain ⟨c, hc⟩ := hda
      exact ⟨c, by rw [hc]; ring⟩
    · obtain ⟨c, hc⟩ := hdb
      exact ⟨c, by rw [hc]; ring⟩
    · rw [gTowerTower]

/-- ⭐⭐ **The bracket obligation assembled** (his Lemma 2, campaign form): under the layer
hypothesis at depth `k ≥ 2` and a selected marking, the bracket class of **any**
`γ_{k+1}`-element against any element lies in the depth-`(k+1)` full reach. -/
theorem gTower_comm_step {k : ℕ} (hk : 2 ≤ k) (HL : GTowerLayerReach h nu' k)
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {v : (DSq h : Type)}
    (hv : v ∈ twoCentralSeries (DSq h : Type) (k + 1)) (g : (DSq h : Type)) :
    levelMk (DSq h : Type) (k + 1 + 2) (commP v g) ∈ gTowerFullReach h nu' (k + 1) := by
  obtain ⟨d, hdmem, hdl, hdn, hdec⟩ := gTower_decomp nu' hsigma hx0 (by omega) hv
  set a := toAdd (nuLam h v) with ha
  set b := toAdd (nu' v) with hb
  have hda : (2 ^ k : ℤ_[2]) ∣ a := by
    have := gTower_row_dvd (nuLam h) hv
    rwa [Nat.add_sub_cancel] at this
  have hdb : (2 ^ k : ℤ_[2]) ∣ b := by
    have := gTower_row_dvd nu' hv
    rwa [Nat.add_sub_cancel] at this
  have hxa : zpowZtwo (isProP_DSq h) (dsqX0 h) a ∈ twoCentralSeries (DSq h : Type) (k + 1) :=
    gTower_zpow_dvd_mem (by omega) (by rwa [Nat.add_sub_cancel]) _
  have hwb : zpowZtwo (isProP_DSq h) (sqPivot h) b ∈ twoCentralSeries (DSq h : Type) (k + 1) :=
    gTower_zpow_dvd_mem (by omega) (by rwa [Nat.add_sub_cancel]) _
  rw [hdec, gTowerTower, gTower_comm_near_add (by omega) hdmem (Subgroup.mul_mem _ hxa hwb) g,
    gTower_comm_near_add (by omega) hxa hwb g]
  refine Subgroup.mul_mem _ ?_ (Subgroup.mul_mem _ ?_ ?_)
  · exact gTower_reach_le_fullReach (gTower_comm_adm_step hk HL ⟨hdmem, hdl, hdn⟩ g)
  · exact gTower_reach_le_fullReach (gTower_comm_tower_step hk HL _ hda g)
  · exact gTower_reach_le_fullReach (gTower_comm_tower_step hk HL _ hdb g)

end StepObligations

/-! ## §7 The layer step and the tower induction

His Lemma 3, assembled: the full layer maps into the full reach (`gTower_full_layer_step`),
the row grading cuts the admissible part back to the admissible reach (`gTower_cut`), and the
two together push the layer statement up the tower from any base (`gTower_layerReach_of_base`).
The base index is `k = 2`: the layer `γ₃/γ₄` of class four, which is where the committed
per-class record stops being needed. -/

section LayerStep

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- ⭐⭐ **The full layer maps into the full reach** (his Lemma 3, generation half): under the
layer hypothesis at depth `k ≥ 2` and a selected marking, every `γ_{k+2}`-element lands, at
level `k+3`, in the depth-`(k+1)` full reach.  The verbal generation of `γ_{k+2}` is matched
clause by clause: squares by `gTower_sq_step`, commutators by `gTower_comm_step`, closure by
discreteness of the level quotient. -/
theorem gTower_full_layer_step {k : ℕ} (hk : 2 ≤ k) (HL : GTowerLayerReach h nu' k)
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {g : (DSq h : Type)}
    (hg : g ∈ twoCentralSeries (DSq h : Type) (k + 2)) :
    levelMk (DSq h : Type) (k + 1 + 2) g ∈ gTowerFullReach h nu' (k + 1) := by
  have hsub : twoCentralSeries (DSq h : Type) (k + 2) ≤
      Subgroup.comap (levelMk (DSq h : Type) (k + 1 + 2)) (gTowerFullReach h nu' (k + 1)) := by
    have hrec : twoCentralSeries (DSq h : Type) (k + 2)
        = twoCentralSucc (twoCentralSeries (DSq h : Type) (k + 1)) :=
      twoCentralSeries_succ (G := (DSq h : Type)) (by omega)
    rw [hrec, twoCentralSucc]
    have hpre : IsClosed ((Subgroup.comap (levelMk (DSq h : Type) (k + 1 + 2))
        (gTowerFullReach h nu' (k + 1)) : Subgroup (DSq h : Type)) : Set (DSq h : Type)) := by
      rw [Subgroup.coe_comap]
      exact (gTower_isClosed_subgroup _).preimage (continuous_levelMk (DSq h : Type) (k + 1 + 2))
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hpre
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨v, hv, rfl⟩
      show levelMk (DSq h : Type) (k + 1 + 2) (v ^ 2) ∈ gTowerFullReach h nu' (k + 1)
      exact gTower_sq_step hk HL hsigma hx0 hv
    · refine Subgroup.commutator_le.2 fun v hv g' _ => ?_
      rw [commutatorElement_def]
      show levelMk (DSq h : Type) (k + 1 + 2) (v * g' * v⁻¹ * g'⁻¹)
        ∈ gTowerFullReach h nu' (k + 1)
      have hshape : v * g' * v⁻¹ * g'⁻¹ = commP v⁻¹ g'⁻¹ := by
        simp only [commP]
        group
      rw [hshape]
      exact gTower_comm_step hk HL hsigma hx0 (Subgroup.inv_mem _ hv) g'⁻¹
  exact hsub hg

/-- The two-tower correction at exponents `(0, 0)` is the identity. -/
theorem gTower_tower_zero : gTowerTower h 0 0 = 1 := by
  rw [gTowerTower, zpowZtwo_zero_exp, zpowZtwo_zero_exp, mul_one]

/-- The image of a `γ_{k+1}`-element is central in `Q_{k+2}`. -/
theorem gTower_img_central {k : ℕ} {r : (DSq h : Type)}
    (hr : r ∈ twoCentralSeries (DSq h : Type) (k + 1))
    (x : levelQuot (DSq h : Type) (k + 2)) :
    x * levelMk (DSq h : Type) (k + 2) r = levelMk (DSq h : Type) (k + 2) r * x := by
  have hz : levelMk (DSq h : Type) (k + 2) r ∈ zLayer (DSq h : Type) (k + 1) := ⟨r, hr, rfl⟩
  exact Subgroup.mem_center_iff.mp (zLayer_le_center (DSq h : Type) (k + 1) hz) x

/-- **Tower images add in the exponents** (for `2^k`-divisible exponents, whose zpow factors
are central at level `k+2`). -/
theorem gTower_towXW_img_mul {k : ℕ} {A₁ B₁ A₂ B₂ : ℤ_[2]}
    (hB₁ : (2 ^ k : ℤ_[2]) ∣ B₁) :
    levelMk (DSq h : Type) (k + 2) (gTowerTower h A₁ B₁) *
      levelMk (DSq h : Type) (k + 2) (gTowerTower h A₂ B₂)
      = levelMk (DSq h : Type) (k + 2) (gTowerTower h (A₁ + A₂) (B₁ + B₂)) := by
  have hwmem : ∀ {C : ℤ_[2]}, (2 ^ k : ℤ_[2]) ∣ C →
      zpowZtwo (isProP_DSq h) (sqPivot h) C ∈ twoCentralSeries (DSq h : Type) (k + 1) :=
    fun hC => gTower_zpow_dvd_mem (by omega) (by rwa [Nat.add_sub_cancel]) _
  simp only [gTowerTower, map_mul]
  set a1 := levelMk (DSq h : Type) (k + 2) (zpowZtwo (isProP_DSq h) (dsqX0 h) A₁) with ha1
  set b1 := levelMk (DSq h : Type) (k + 2) (zpowZtwo (isProP_DSq h) (sqPivot h) B₁) with hb1
  set a2 := levelMk (DSq h : Type) (k + 2) (zpowZtwo (isProP_DSq h) (dsqX0 h) A₂) with ha2
  have hswap : b1 * a2 = a2 * b1 := (gTower_img_central (hwmem hB₁) a2).symm
  calc a1 * b1 * (a2 * levelMk (DSq h : Type) (k + 2) (zpowZtwo (isProP_DSq h) (sqPivot h) B₂))
      = a1 * (b1 * a2) * levelMk (DSq h : Type) (k + 2)
          (zpowZtwo (isProP_DSq h) (sqPivot h) B₂) := by
        simp only [mul_assoc]
    _ = a1 * (a2 * b1) * levelMk (DSq h : Type) (k + 2)
          (zpowZtwo (isProP_DSq h) (sqPivot h) B₂) := by rw [hswap]
    _ = a1 * a2 * (b1 * levelMk (DSq h : Type) (k + 2)
          (zpowZtwo (isProP_DSq h) (sqPivot h) B₂)) := by
        simp only [mul_assoc]
    _ = levelMk (DSq h : Type) (k + 2) (zpowZtwo (isProP_DSq h) (dsqX0 h) (A₁ + A₂)) *
        levelMk (DSq h : Type) (k + 2) (zpowZtwo (isProP_DSq h) (sqPivot h) (B₁ + B₂)) := by
        rw [ha1, hb1, ha2, ← map_mul, ← zpowZtwo_add, ← map_mul, ← zpowZtwo_add]

/-- ⭐⭐ **The realization of the full reach** (the closure induction behind the cut): every
element of the depth-`k` full reach is the image of an exactly row-trivial `γ_{k+1}`-element
whose class already lies in the admissible reach, times a two-tower image with
`2^k`-divisible exponents. -/
theorem gTower_fullReach_realize {k : ℕ}
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {z : levelQuot (DSq h : Type) (k + 2)}
    (hz : z ∈ gTowerFullReach h nu' k) :
    ∃ r A B, r ∈ twoCentralSeries (DSq h : Type) (k + 1) ∧ nuLam h r = 1 ∧ nu' r = 1 ∧
      levelMk (DSq h : Type) (k + 2) r ∈ gTowerReach h nu' k ∧
        (2 ^ k : ℤ_[2]) ∣ A ∧ (2 ^ k : ℤ_[2]) ∣ B ∧
          z = levelMk (DSq h : Type) (k + 2) r *
            levelMk (DSq h : Type) (k + 2) (gTowerTower h A B) := by
  have hz' : z ∈ Subgroup.closure ((gTowerKnobSet h nu' k ∪ gTowerTowSet h nu' k) ∪
      {z | ∃ A B : ℤ_[2], (2 ^ k : ℤ_[2]) ∣ A ∧ (2 ^ k : ℤ_[2]) ∣ B ∧
        z = levelMk (DSq h : Type) (k + 2) (gTowerTower h A B)}) := by
    rw [Subgroup.closure_union]
    exact hz
  clear hz
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hz'
  · rintro z (hgen | ⟨A, B, hA, hB, rfl⟩)
    · -- knob and admissible-tower generators: row-trivial `γ_{k+1}`-realizations, no tower
      have hreal : ∃ r, r ∈ twoCentralSeries (DSq h : Type) (k + 1) ∧ nuLam h r = 1 ∧
          nu' r = 1 ∧ z = levelMk (DSq h : Type) (k + 2) r := by
        simp only [gTowerKnobSet, gTowerTowSet, Set.mem_union, Set.mem_setOf_eq] at hgen
        obtain (⟨t, q, ht, hq, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨x, hx, a, rfl⟩ := hgen
        · exact ⟨commP t q, cfive_commP_mem_succ ht.1 q, gTower_row_commP _ t q,
            gTower_row_commP nu' t q, rfl⟩
        · refine ⟨t ^ 2 * commP t (dsqX1 h),
            Subgroup.mul_mem _ (sq_mem_twoCentralSeries_succ (G := (DSq h : Type)) ht.1)
              (cfive_commP_mem_succ ht.1 _), ?_, ?_, rfl⟩
          · rw [map_mul, cfourKnob_sq_nuLam ht.2.1, gTower_row_commP _ t _, one_mul]
          · rw [map_mul, cfourKnob_sq_nu nu' ht.2.2, gTower_row_commP nu' t _, one_mul]
        · have hxrow : nuLam h x = 1 ∧ nu' x = 1 := by
            simp only [gTowerXLetters, Set.mem_union, Set.mem_singleton_iff,
              Set.mem_range] at hx
            obtain (rfl | ⟨j, rfl⟩) | ⟨j, rfl⟩ := hx
            · exact ⟨gTower_xOne_nuLam, gTower_xOne_nu nu' hx0⟩
            · constructor
              · refine Multiplicative.toAdd.injective ?_
                rw [toAdd_nuLam_sqEichU, toAdd_one]
              · refine Multiplicative.toAdd.injective ?_
                rw [sqEichU, map_mul, map_inv, toAdd_mul, toAdd_inv, toAdd_map_zpowZtwo,
                  toAdd_nu_sqPivot_selected nu' hsigma hx0, toAdd_one, mul_one]
                ring
            · constructor
              · refine Multiplicative.toAdd.injective ?_
                rw [toAdd_nuLam_sqEichV, toAdd_one]
              · refine Multiplicative.toAdd.injective ?_
                rw [sqEichV, map_mul, map_inv, toAdd_mul, toAdd_inv, toAdd_map_zpowZtwo,
                  toAdd_nu_sqPivot_selected nu' hsigma hx0, toAdd_one, mul_one]
                ring
          refine ⟨zpowZtwo (isProP_DSq h) x (2 ^ k * a),
            gTower_zpow_dvd_mem (by omega) ⟨a, by rw [Nat.add_sub_cancel]⟩ x, ?_, ?_, rfl⟩
          · refine Multiplicative.toAdd.injective ?_
            rw [toAdd_map_zpowZtwo, hxrow.1, toAdd_one, mul_zero]
          · refine Multiplicative.toAdd.injective ?_
            rw [toAdd_map_zpowZtwo, hxrow.2, toAdd_one, mul_zero]
      obtain ⟨r, hrmem, hrl, hrn, rfl⟩ := hreal
      refine ⟨r, 0, 0, hrmem, hrl, hrn, Subgroup.subset_closure hgen, dvd_zero _, dvd_zero _, ?_⟩
      rw [gTower_tower_zero, map_one, mul_one]
    · -- complement-tower generators: trivial admissible part
      exact ⟨1, A, B, Subgroup.one_mem _, map_one _, map_one _,
        by rw [map_one]; exact Subgroup.one_mem _, hA, hB, by rw [map_one, one_mul]⟩
  · exact ⟨1, 0, 0, Subgroup.one_mem _, map_one _, map_one _,
      by rw [map_one]; exact Subgroup.one_mem _, dvd_zero _, dvd_zero _,
      by rw [map_one, one_mul, gTower_tower_zero, map_one]⟩
  · rintro z₁ z₂ - - ⟨r₁, A₁, B₁, hm₁, hl₁, hn₁, hR₁, hA₁, hB₁, rfl⟩
      ⟨r₂, A₂, B₂, hm₂, hl₂, hn₂, hR₂, hA₂, hB₂, rfl⟩
    refine ⟨r₁ * r₂, A₁ + A₂, B₁ + B₂, Subgroup.mul_mem _ hm₁ hm₂, ?_, ?_, ?_,
      dvd_add hA₁ hA₂, dvd_add hB₁ hB₂, ?_⟩
    · rw [map_mul, hl₁, hl₂, one_mul]
    · rw [map_mul, hn₁, hn₂, one_mul]
    · rw [map_mul]
      exact Subgroup.mul_mem _ hR₁ hR₂
    · rw [map_mul, ← gTower_towXW_img_mul hB₁]
      have hcen := gTower_img_central hm₂
      calc levelMk (DSq h : Type) (k + 2) r₁ *
            levelMk (DSq h : Type) (k + 2) (gTowerTower h A₁ B₁) *
            (levelMk (DSq h : Type) (k + 2) r₂ *
              levelMk (DSq h : Type) (k + 2) (gTowerTower h A₂ B₂))
          = levelMk (DSq h : Type) (k + 2) r₁ *
            (levelMk (DSq h : Type) (k + 2) (gTowerTower h A₁ B₁) *
              levelMk (DSq h : Type) (k + 2) r₂) *
              levelMk (DSq h : Type) (k + 2) (gTowerTower h A₂ B₂) := by
            simp only [mul_assoc]
        _ = levelMk (DSq h : Type) (k + 2) r₁ *
            (levelMk (DSq h : Type) (k + 2) r₂ *
              levelMk (DSq h : Type) (k + 2) (gTowerTower h A₁ B₁)) *
              levelMk (DSq h : Type) (k + 2) (gTowerTower h A₂ B₂) := by
            rw [hcen]
        _ = levelMk (DSq h : Type) (k + 2) r₁ * levelMk (DSq h : Type) (k + 2) r₂ *
            (levelMk (DSq h : Type) (k + 2) (gTowerTower h A₁ B₁) *
              levelMk (DSq h : Type) (k + 2) (gTowerTower h A₂ B₂)) := by
            simp only [mul_assoc]
  · rintro z - ⟨r, A, B, hm, hl, hn, hR, hA, hB, rfl⟩
    refine ⟨r⁻¹, -A, -B, Subgroup.inv_mem _ hm, ?_, ?_, ?_, hA.neg_right, hB.neg_right, ?_⟩
    · rw [map_inv, hl, inv_one]
    · rw [map_inv, hn, inv_one]
    · rw [map_inv]
      exact Subgroup.inv_mem _ hR
    · have hTinv : (levelMk (DSq h : Type) (k + 2) (gTowerTower h A B))⁻¹
          = levelMk (DSq h : Type) (k + 2) (gTowerTower h (-A) (-B)) := by
        refine inv_eq_of_mul_eq_one_left ?_
        rw [gTower_towXW_img_mul (hB.neg_right), neg_add_cancel,
          neg_add_cancel, gTower_tower_zero, map_one]
      rw [mul_inv_rev, hTinv, ← map_inv]
      exact gTower_img_central (Subgroup.inv_mem _ hm) _

/-- ⭐⭐ **The cut** (his Lemma 3, row half): at a selected marking, an exactly row-trivial
`γ_{k+1}`-element whose class lies in the full reach already lies in the admissible reach.
The realization writes the class as an admissible image times a two-tower image; the rows of
the element read off the tower exponents modulo `2^{k+1}`, so row-triviality pushes the tower
factor into `γ_{k+2}`, where it is invisible. -/
theorem gTower_cut {k : ℕ}
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {g : (DSq h : Type)} (hgl : nuLam h g = 1)
    (hgn : nu' g = 1)
    (hfull : levelMk (DSq h : Type) (k + 2) g ∈ gTowerFullReach h nu' k) :
    levelMk (DSq h : Type) (k + 2) g ∈ gTowerReach h nu' k := by
  obtain ⟨r, A, B, hrmem, hrl, hrn, hrReach, hA, hB, heq⟩ :=
    gTower_fullReach_realize hsigma hx0 hfull
  have hAmem : zpowZtwo (isProP_DSq h) (dsqX0 h) A ∈ twoCentralSeries (DSq h : Type) (k + 1) :=
    gTower_zpow_dvd_mem (by omega) (by rwa [Nat.add_sub_cancel]) _
  have hBmem : zpowZtwo (isProP_DSq h) (sqPivot h) B ∈ twoCentralSeries (DSq h : Type) (k + 1) :=
    gTower_zpow_dvd_mem (by omega) (by rwa [Nat.add_sub_cancel]) _
  have htmem : gTowerTower h A B ∈ twoCentralSeries (DSq h : Type) (k + 1) :=
    Subgroup.mul_mem _ hAmem hBmem
  -- the slack element
  set u := (r * gTowerTower h A B)⁻¹ * g with hu
  have humem : u ∈ twoCentralSeries (DSq h : Type) (k + 2) := by
    rw [lim_mem_twoCentralSeries_iff_levelMk]
    show levelMk (DSq h : Type) (k + 2) ((r * gTowerTower h A B)⁻¹ * g) = 1
    rw [map_mul, map_inv, map_mul, heq]
    group
  have hgform : g = r * gTowerTower h A B * u := by
    rw [hu, mul_inv_cancel_left]
  -- the rows read off the tower exponents
  have hrowA : toAdd (nuLam h g) = A + toAdd (nuLam h u) := by
    rw [hgform, map_mul, toAdd_mul, map_mul, toAdd_mul, hrl, toAdd_one, gTower_tower_nuLam,
      zero_add]
  have hrowB : toAdd (nu' g) = B + toAdd (nu' u) := by
    rw [hgform, map_mul, toAdd_mul, map_mul, toAdd_mul, hrn, toAdd_one,
      gTower_tower_nu nu' hsigma hx0, zero_add]
  have hAdeep : (2 ^ (k + 1) : ℤ_[2]) ∣ A := by
    have hud := gTower_row_dvd (nuLam h) humem
    rw [show k + 2 - 1 = k + 1 from by omega] at hud
    have : A = -toAdd (nuLam h u) := by
      have h0 := hrowA
      rw [hgl, toAdd_one] at h0
      exact eq_neg_of_add_eq_zero_left h0.symm
    rw [this]
    exact hud.neg_right
  have hBdeep : (2 ^ (k + 1) : ℤ_[2]) ∣ B := by
    have hud := gTower_row_dvd nu' humem
    rw [show k + 2 - 1 = k + 1 from by omega] at hud
    have : B = -toAdd (nu' u) := by
      have h0 := hrowB
      rw [hgn, toAdd_one] at h0
      exact eq_neg_of_add_eq_zero_left h0.symm
    rw [this]
    exact hud.neg_right
  -- the tower factor is `γ_{k+2}`-deep, hence invisible at level `k+2`
  have htdeep : gTowerTower h A B ∈ twoCentralSeries (DSq h : Type) (k + 2) :=
    gTower_tower_mem (by omega)
      (by rw [show k + 2 - 1 = k + 1 from by omega]; exact hAdeep)
      (by rw [show k + 2 - 1 = k + 1 from by omega]; exact hBdeep)
  have htimg : levelMk (DSq h : Type) (k + 2) (gTowerTower h A B) = 1 :=
    (lim_mem_twoCentralSeries_iff_levelMk (k + 2) _).mp htdeep
  rw [heq, htimg, mul_one]
  exact hrReach

/-- ⭐⭐⭐ **The tower induction step**: at a selected marking and `k ≥ 2`, the layer statement
at depth `k` implies it at depth `k + 1`. -/
theorem gTower_layerReach_step {k : ℕ} (hk : 2 ≤ k)
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (HL : GTowerLayerReach h nu' k) :
    GTowerLayerReach h nu' (k + 1) := by
  intro g hg hgl hgn
  exact gTower_cut hsigma hx0 hgl hgn (gTower_full_layer_step hk HL hsigma hx0 hg)

/-- ⭐⭐⭐ **The tower follows from the base** (his §4, the uniform-in-class statement): at a
selected marking, the depth-`2` layer statement - the class-four instance, over the committed
per-class record - implies the layer statement at **every** depth `k ≥ 2`.  This replaces the
one-class-per-wave ladder: no statement below depends on the class. -/
theorem gTower_layerReach_of_base
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (hbase : GTowerLayerReach h nu' 2) :
    ∀ k, 2 ≤ k → GTowerLayerReach h nu' k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hbase
  | succ k hk ih => exact gTower_layerReach_step hk hsigma hx0 ih

end LayerStep

/-! ## Axiom pins (§1 and §2) -/

section AxiomPinsOne

#print axioms gTower_isClosed_dvd
#print axioms gTowerRowSub
#print axioms gTower_mem_rowSub
#print axioms gTower_isClosed_rowSub
#print axioms gTower_row_commP
#print axioms gTower_row_dvd
#print axioms gTower_zpow_mem
#print axioms gTower_zpow_dvd_mem
#print axioms gTowerTower
#print axioms gTower_tower_nuLam
#print axioms gTower_tower_nu
#print axioms gTower_tower_mem
#print axioms gTower_tower_row_trivial_iff
#print axioms gTower_tower_mem_succ_dvd
#print axioms gTower_decomp
#print axioms gTower_nu_x1
#print axioms gTowerXOne
#print axioms gTower_xOne_nuLam
#print axioms gTower_xOne_nu
#print axioms gTower_engine_free
#print axioms gTower_engine_corr_mem
#print axioms gTower_engine_bracket
#print axioms gTower_engine_bracket'
#print axioms gTower_sq_congr
#print axioms gTower_sq_slack
#print axioms gTower_comm_near_add
#print axioms gTower_comm_near_slack
#print axioms gTower_engine_bundle
#print axioms gTower_commP_mem_lambdaTwo
#print axioms gTower_lambdaImage_le
#print axioms gTower_commP_vanish
#print axioms gTower_commP_vanish'
#print axioms gTower_sq_mem_zLayer
#print axioms gTower_zLayer_comm
#print axioms gTower_commP_zLayer_right
#print axioms gTower_shuffle
#print axioms gTower_shuffle_mid
#print axioms gTower_drop_right
#print axioms gTower_sq_dress
#print axioms gTower_sq_zLayer_dress
#print axioms gTower_pow_four_dress
#print axioms gTower_conj_factor
#print axioms gTower_dress_zero
#print axioms gTower_dress_one
#print axioms gTower_dress_two
#print axioms gTower_dress_handle
#print axioms gTower_dress_handleU
#print axioms gTower_dress_handleV
#print axioms gTower_dress_core
#print axioms gTower_kills
#print axioms GTowerAdm
#print axioms gTowerFar
#print axioms gTowerXLetters
#print axioms gTowerKnobSet
#print axioms gTowerTowSet
#print axioms gTowerReach
#print axioms gTowerTowXW
#print axioms gTowerFullReach
#print axioms gTower_reach_le_fullReach
#print axioms gTower_adm_sq
#print axioms gTower_adm_mono
#print axioms gTower_zpow_sq
#print axioms gTower_zpow_half
#print axioms gTower_step_knob
#print axioms gTower_step_bundle
#print axioms gTower_step_tower
#print axioms gTower_reach_step
#print axioms GTowerLayerReach
#print axioms gTower_discrete
#print axioms gTower_isClosed_subgroup
#print axioms gTower_commHom_span
#print axioms gTower_letters_mem_far
#print axioms gTower_comm_x1_split
#print axioms gTower_comm_adm_step
#print axioms gTower_comm_tower_step
#print axioms gTower_sq_step
#print axioms gTower_comm_step
#print axioms gTower_full_layer_step
#print axioms gTower_tower_zero
#print axioms gTower_img_central
#print axioms gTower_towXW_img_mul
#print axioms gTower_fullReach_realize
#print axioms gTower_cut
#print axioms gTower_layerReach_step
#print axioms gTower_layerReach_of_base

end AxiomPinsOne

end SqCore

end Dyadic

end GQ2

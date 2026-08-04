/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Roe.Labute.GradedLie.SpanIdentities

/-!
# GL-C: the span base case `k = 3`

Design record: `docs/orchestration/span-gradedlie-plan.md` §2.2 (which follows L4b's
by-hand closure of k = 3 — "colπ-at-π-towers, tails, left-normed columns").
**Statements frozen (GL0); fills ticket GL-C.**

`Q₄(F₃)` has order `2^23` — no `decide`; the proof is structural.  Everything happens in
`Q₄ = levelQuot freeProTwo 4`, where the λ-calculus is *exact* (`λ₄`-image `= ⊥`), so no
"mod λ" bookkeeping is needed anywhere:

* `Λ₂ := lambdaImage _ 2 4` is abelian (`[λ₂,λ₂] ⊆ λ₄ = 1`);
* `Λ₃ := lambdaImage _ 3 4 = zLayer _ 3` is central of exponent 2;
* every `commP` lands in `Λ₂`, every square lands in `Λ₂`, every `commP` against a
  `Λ₂`-element lands in `Λ₃`.

The two frozen statements are instances of one private core lemma `span_base_core`,
parameterized by the **twisted** generator `τ = mgen t` (r₀: `t = 0`; r₂: `t = 2`) and
the two **bracket/tail** generators.  The route (orchestrator-derived ordering — the
naive "triples first" order is circular):

1. *Generator fourth powers.*  `β⁴` are the two tails (`2^{3-1} = 4`); `τ⁴` is the
   twisted column at the modification `τ²`, where `commP (τ²) τ = 1` (diagonal trick).
2. *Squares of generator brackets.*  The **exact** identity
   `commP u g ^ 2 = commP (u²) g · (commP (commP u g) u)⁻¹` (`commP_sq_eq`) at
   `u = β`: the first factor is a single-slot column at the modification `β² ∈ Λ₂`
   (or the twisted column corrected by `β⁴`), the second is a single-slot column at
   the modification `commP β g ∈ Λ₂`.  `commP_symm` transports to the `τ`-left pairs.
3. *Squares of all brackets.*  `(a, b) ↦ (commP a b)²` is **exactly** bimultiplicative
   in `Q₄` (`commP_sq_mul_left/right`: the corrections are `Λ₃`-central involutions and
   `Λ₂`-elements commute), so two closure inductions reduce to step 2.  This replaces
   the memo's word-length induction: no measure is needed.
4. *Fourth powers.*  `(ab)⁴ = a⁴·b⁴·(commP b a)²` **exactly** (`pow_four_mul`), so
   `{a | a⁴ ∈ K}` is a subgroup once step 3 is known; step 1 seeds the generators.
5. *`key_sq`*: `v² ∈ K` for all `v ∈ Λ₂`, by `lambdaImage_induction` at `j = 1` — the
   two atom families are exactly steps 3 and 4.
6. *Bracket atoms*: `commP v g ∈ K` for `v ∈ Λ₂` and all `g` (β-slots directly, the
   τ-slot after dividing the twisted column by `v² ∈ K` from step 5).
7. Assemble by `lambdaImage_induction` at `j = 2`.

No new axioms, no `decide`, no `native_decide`.  Small `private` helpers restated
binder-for-binder from `StageLemma.lean` (house precedent; this file must not import it).
-/

namespace GQ2.Roe.Labute

/-! ## Stage 0: pure group identities -/

section PureCalculus

variable {H : Type*} [Group H]

/-- The fundamental move rule (restated from `StageLemma.lean`). -/
private theorem mul_swap_commP (v a : H) : v * a = a * v * commP v a := by
  simp only [commP]; group

/-- Left expansion of `commP` (restated from `StageLemma.lean`). -/
private theorem commP_mul_left (x u g : H) :
    commP (x * u) g = u⁻¹ * commP x g * u * commP u g := by simp only [commP]; group

/-- Right expansion of `commP` (restated from `StageLemma.lean`). -/
private theorem commP_mul_right (x g v : H) :
    commP x (g * v) = commP x v * (v⁻¹ * commP x g * v) := by simp only [commP]; group

/-- `commP` is antisymmetric (restated from `StageLemma.lean`). -/
private theorem commP_symm (x y : H) : commP x y = (commP y x)⁻¹ := by
  simp only [commP]; group

/-- Conjugation expressed through `commP` (restated from `StageLemma.lean`). -/
private theorem conj_eq_mul_commP (v a : H) : v⁻¹ * a * v = a * (commP v a)⁻¹ := by
  simp only [commP]; group

private theorem commP_one_left (g : H) : commP (1 : H) g = 1 := by simp only [commP]; group

private theorem commP_one_right (g : H) : commP g (1 : H) = 1 := by simp only [commP]; group

private theorem commP_self' (g : H) : commP g g = 1 := by simp only [commP]; group

/-- Commuting elements have trivial `commP` (restated from `StageLemma.lean`). -/
private theorem commP_eq_one_of_mul_comm {x y : H} (h : x * y = y * x) : commP x y = 1 := by
  simp only [commP]
  calc x⁻¹ * y⁻¹ * x * y = x⁻¹ * (y⁻¹ * (x * y)) := by group
    _ = x⁻¹ * (y⁻¹ * (y * x)) := by rw [h]
    _ = 1 := by group

/-- Converse of `commP_eq_one_of_mul_comm`. -/
private theorem mul_comm_of_commP_eq_one {x y : H} (h : commP x y = 1) : x * y = y * x := by
  simp only [commP] at h
  calc x * y = y * x * (x⁻¹ * y⁻¹ * x * y) := by group
    _ = y * x := by rw [h, mul_one]

/-- A central factor slides to the right. -/
private theorem mul_central_mul {D : H} (hD : ∀ w : H, D * w = w * D) (A B : H) :
    A * D * B = A * B * D := by rw [mul_assoc, hD B, ← mul_assoc]

/-- A central involution is invisible to squares. -/
private theorem sq_mul_central {D : H} (hD : ∀ w : H, D * w = w * D) (hD2 : D * D = 1)
    (C : H) : (C * D) ^ 2 = C ^ 2 := by
  calc (C * D) ^ 2 = C * (D * C) * D := by rw [pow_two]; group
    _ = C * (C * D) * D := by rw [hD C]
    _ = C * C * (D * D) := by group
    _ = C * C := by rw [hD2, mul_one]
    _ = C ^ 2 := (pow_two C).symm

/-! ### Single-slot evaluations of the two shift words -/

private theorem dbarWordR0_slot0 (a s y v : H) :
    dbarWordR0 a s y ![v, 1, 1] = v ^ 2 * commP v a := by
  have h0 : (![v, 1, 1] : Fin 3 → H) 0 = v := rfl
  have h1 : (![v, 1, 1] : Fin 3 → H) 1 = 1 := rfl
  have h2 : (![v, 1, 1] : Fin 3 → H) 2 = 1 := rfl
  simp only [dbarWordR0, h0, h1, h2, commP_one_left, mul_one]

private theorem dbarWordR0_slot1 (a s y v : H) :
    dbarWordR0 a s y ![1, v, 1] = commP v y := by
  have h0 : (![1, v, 1] : Fin 3 → H) 0 = 1 := rfl
  have h1 : (![1, v, 1] : Fin 3 → H) 1 = v := rfl
  have h2 : (![1, v, 1] : Fin 3 → H) 2 = 1 := rfl
  simp only [dbarWordR0, h0, h1, h2, commP_one_left, one_pow, mul_one, one_mul]

private theorem dbarWordR0_slot2 (a s y v : H) :
    dbarWordR0 a s y ![1, 1, v] = commP v s := by
  have h0 : (![1, 1, v] : Fin 3 → H) 0 = 1 := rfl
  have h1 : (![1, 1, v] : Fin 3 → H) 1 = 1 := rfl
  have h2 : (![1, 1, v] : Fin 3 → H) 2 = v := rfl
  simp only [dbarWordR0, h0, h1, h2, commP_one_left, one_pow, mul_one, one_mul]

private theorem dbarWordR2_slot2 (s x y v : H) :
    dbarWordR2 s x y ![1, 1, v] = v ^ 2 * commP v y := by
  have h0 : (![1, 1, v] : Fin 3 → H) 0 = 1 := rfl
  have h1 : (![1, 1, v] : Fin 3 → H) 1 = 1 := rfl
  have h2 : (![1, 1, v] : Fin 3 → H) 2 = v := rfl
  simp only [dbarWordR2, h0, h1, h2, commP_one_left, mul_one]

private theorem dbarWordR2_slot0 (s x y v : H) :
    dbarWordR2 s x y ![v, 1, 1] = commP v x := by
  have h0 : (![v, 1, 1] : Fin 3 → H) 0 = v := rfl
  have h1 : (![v, 1, 1] : Fin 3 → H) 1 = 1 := rfl
  have h2 : (![v, 1, 1] : Fin 3 → H) 2 = 1 := rfl
  simp only [dbarWordR2, h0, h1, h2, commP_one_left, one_pow, mul_one, one_mul]

private theorem dbarWordR2_slot1 (s x y v : H) :
    dbarWordR2 s x y ![1, v, 1] = commP v s := by
  have h0 : (![1, v, 1] : Fin 3 → H) 0 = 1 := rfl
  have h1 : (![1, v, 1] : Fin 3 → H) 1 = v := rfl
  have h2 : (![1, v, 1] : Fin 3 → H) 2 = 1 := rfl
  simp only [dbarWordR2, h0, h1, h2, commP_one_left, one_pow, mul_one, one_mul]

end PureCalculus

/-! ## Stage 0': the exact λ-calculus of `Q₄`

All statements below are for the level-4 quotient of an arbitrary pro-2-style `G`; the
only input is `lambdaImage G 4 4 = ⊥`, which makes every "mod λ" congruence an equality.
-/

section LevelFour

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- `λₘ` dies in `Qₘ` (restated from `StageLemma.lean`). -/
private theorem lambdaImage_self' (m : ℕ) : lambdaImage G m m = ⊥ := by
  rw [lambdaImage, Subgroup.map_eq_bot_iff, levelMk, QuotientGroup.ker_mk']

/-- `λ₁ = ⊤` survives to every level quotient (restated from `StageLemma.lean`). -/
private theorem lambdaImage_one_eq_top' (m : ℕ) : lambdaImage G 1 m = ⊤ := by
  rw [lambdaImage, twoCentralSeries_one]
  exact Subgroup.map_top_of_surjective _ (levelMk_surjective G m)

private theorem mem_lambdaImage_one {m : ℕ} (q : levelQuot G m) : q ∈ lambdaImage G 1 m := by
  rw [lambdaImage_one_eq_top']; trivial

open scoped commutatorElement in
/-- The λ-grading lemma in `commP` form (restated from `StageLemma.lean`). -/
private theorem commP_mem_lambdaImage_add {a b m : ℕ} {v g : levelQuot G m}
    (hv : v ∈ lambdaImage G a m) (hg : g ∈ lambdaImage G b m) :
    commP v g ∈ lambdaImage G (a + b) m := by
  obtain ⟨x, hx, rfl⟩ := hv
  obtain ⟨y, hy, rfl⟩ := hg
  refine ⟨commP x y, ?_, by simp only [commP, map_mul, map_inv]⟩
  have h : commP x y = ⁅x⁻¹, y⁻¹⁆ := by simp only [commP, commutatorElement_def, inv_inv]
  rw [h]
  exact commutator_mem_twoCentralSeries_add G ((twoCentralSeries G a).inv_mem hx)
    ((twoCentralSeries G b).inv_mem hy)

/-- Squares deepen the λ-index by one. -/
private theorem sq_mem_lambdaImage_succ {j m : ℕ} {v : levelQuot G m}
    (hv : v ∈ lambdaImage G j m) : v ^ 2 ∈ lambdaImage G (j + 1) m := by
  obtain ⟨x, hx, rfl⟩ := hv
  exact ⟨x ^ 2, sq_mem_twoCentralSeries_succ G hx, by rw [map_pow]⟩

open scoped commutatorElement in
/-- The convention bridge: mathlib's commutator is `commP` at inverted slots. -/
private theorem levelMk_commutator {m : ℕ} (v g : G) :
    levelMk G m ⁅v, g⁆ = commP (levelMk G m v)⁻¹ (levelMk G m g)⁻¹ := by
  simp only [commutatorElement_def, commP, map_mul, map_inv, inv_inv]

private theorem commP_mem_lam2 (x y : levelQuot G 4) : commP x y ∈ lambdaImage G 2 4 :=
  commP_mem_lambdaImage_add (mem_lambdaImage_one x) (mem_lambdaImage_one y)

private theorem sq_mem_lam2 (a : levelQuot G 4) : a ^ 2 ∈ lambdaImage G 2 4 :=
  sq_mem_lambdaImage_succ (mem_lambdaImage_one a)

private theorem commP_mem_lam3 {v : levelQuot G 4} (hv : v ∈ lambdaImage G 2 4)
    (g : levelQuot G 4) : commP v g ∈ lambdaImage G 3 4 :=
  commP_mem_lambdaImage_add hv (mem_lambdaImage_one g)

private theorem commP_mem_lam3' {v : levelQuot G 4} (hv : v ∈ lambdaImage G 2 4)
    (g : levelQuot G 4) : commP g v ∈ lambdaImage G 3 4 :=
  commP_mem_lambdaImage_add (mem_lambdaImage_one g) hv

/-- `Λ₃ = Z₃` is central in `Q₄`. -/
private theorem lam3_central {z : levelQuot G 4} (hz : z ∈ lambdaImage G 3 4)
    (w : levelQuot G 4) : z * w = w * z :=
  (zLayer_commute (G := G) (k := 3) hz w).eq

/-- `Λ₃ = Z₃` has exponent 2. -/
private theorem lam3_sq {z : levelQuot G 4} (hz : z ∈ lambdaImage G 3 4) : z * z = 1 := by
  have h := zLayer_sq G (k := 3) hz
  rwa [pow_two] at h

private theorem lam3_inv_central {z : levelQuot G 4} (hz : z ∈ lambdaImage G 3 4)
    (w : levelQuot G 4) : z⁻¹ * w = w * z⁻¹ :=
  lam3_central (Subgroup.inv_mem _ hz) w

private theorem lam3_inv_sq {z : levelQuot G 4} (hz : z ∈ lambdaImage G 3 4) :
    z⁻¹ * z⁻¹ = 1 :=
  lam3_sq (Subgroup.inv_mem _ hz)

/-- Conjugation is trivial on the central layer. -/
private theorem conj_lam3 {z : levelQuot G 4} (hz : z ∈ lambdaImage G 3 4)
    (g : levelQuot G 4) : g⁻¹ * z * g = z := by
  rw [conj_eq_mul_commP, commP_eq_one_of_mul_comm (lam3_central hz g).symm, inv_one, mul_one]

/-- `Λ₂` is abelian in `Q₄` (`[λ₂, λ₂] ⊆ λ₄ = 1`). -/
private theorem lam2_mul_comm {u v : levelQuot G 4} (hu : u ∈ lambdaImage G 2 4)
    (hv : v ∈ lambdaImage G 2 4) : u * v = v * u := by
  refine mul_comm_of_commP_eq_one ?_
  have h := commP_mem_lambdaImage_add hu hv
  rw [show (2 : ℕ) + 2 = 4 from rfl, lambdaImage_self'] at h
  simpa using h

private theorem lam2_commute {u v : levelQuot G 4} (hu : u ∈ lambdaImage G 2 4)
    (hv : v ∈ lambdaImage G 2 4) : Commute u v :=
  (commute_iff_eq u v).mpr (lam2_mul_comm hu hv)

/-! ### The three exact identities -/

/-- **(ID)** the exact square-transport identity in `Q₄`:
`[u,g]² = [u², g] · [[u,g], u]⁻¹`, with no error term. -/
private theorem commP_sq_eq (u g : levelQuot G 4) :
    commP u g ^ 2 = commP (u ^ 2) g * (commP (commP u g) u)⁻¹ := by
  have hD : commP u (commP u g) ∈ lambdaImage G 3 4 := commP_mem_lam3' (commP_mem_lam2 u g) u
  have hkey : commP (u ^ 2) g = commP u g ^ 2 * (commP u (commP u g))⁻¹ := by
    calc commP (u ^ 2) g = commP (u * u) g := by rw [pow_two]
      _ = u⁻¹ * commP u g * u * commP u g := commP_mul_left u u g
      _ = commP u g * (commP u (commP u g))⁻¹ * commP u g := by rw [conj_eq_mul_commP]
      _ = commP u g * commP u g * (commP u (commP u g))⁻¹ :=
          mul_central_mul (lam3_inv_central hD) _ _
      _ = commP u g ^ 2 * (commP u (commP u g))⁻¹ := by rw [pow_two]
  rw [hkey, commP_symm (commP u g) u, inv_inv, mul_assoc, inv_mul_cancel, mul_one]

/-- Squares of `commP` are **exactly** multiplicative in the left slot. -/
private theorem commP_sq_mul_left (x u g : levelQuot G 4) :
    commP (x * u) g ^ 2 = commP x g ^ 2 * commP u g ^ 2 := by
  have hA : commP x g ∈ lambdaImage G 2 4 := commP_mem_lam2 x g
  have hB : commP u g ∈ lambdaImage G 2 4 := commP_mem_lam2 u g
  have hD : commP u (commP x g) ∈ lambdaImage G 3 4 := commP_mem_lam3' hA u
  have hexp : commP (x * u) g = commP x g * commP u g * (commP u (commP x g))⁻¹ := by
    calc commP (x * u) g = u⁻¹ * commP x g * u * commP u g := commP_mul_left x u g
      _ = commP x g * (commP u (commP x g))⁻¹ * commP u g := by rw [conj_eq_mul_commP]
      _ = commP x g * commP u g * (commP u (commP x g))⁻¹ :=
          mul_central_mul (lam3_inv_central hD) _ _
  rw [hexp, sq_mul_central (lam3_inv_central hD) (lam3_inv_sq hD)]
  exact (lam2_commute hA hB).mul_pow 2

/-- Squares of `commP` are **exactly** multiplicative in the right slot. -/
private theorem commP_sq_mul_right (x g v : levelQuot G 4) :
    commP x (g * v) ^ 2 = commP x v ^ 2 * commP x g ^ 2 := by
  have hA : commP x v ∈ lambdaImage G 2 4 := commP_mem_lam2 x v
  have hB : commP x g ∈ lambdaImage G 2 4 := commP_mem_lam2 x g
  have hD : commP v (commP x g) ∈ lambdaImage G 3 4 := commP_mem_lam3' hB v
  have hexp : commP x (g * v) = commP x v * commP x g * (commP v (commP x g))⁻¹ := by
    calc commP x (g * v) = commP x v * (v⁻¹ * commP x g * v) := commP_mul_right x g v
      _ = commP x v * (commP x g * (commP v (commP x g))⁻¹) := by rw [conj_eq_mul_commP]
      _ = commP x v * commP x g * (commP v (commP x g))⁻¹ := (mul_assoc _ _ _).symm
  rw [hexp, sq_mul_central (lam3_inv_central hD) (lam3_inv_sq hD)]
  exact (lam2_commute hA hB).mul_pow 2

/-- **The fourth-power expansion** in `Q₄`: `(ab)⁴ = a⁴·b⁴·[b,a]²`, exactly. -/
private theorem pow_four_mul (a b : levelQuot G 4) :
    (a * b) ^ 4 = a ^ 4 * b ^ 4 * commP b a ^ 2 := by
  have hd : commP b a ∈ lambdaImage G 2 4 := commP_mem_lam2 b a
  have he : commP b (commP b a) ∈ lambdaImage G 3 4 := commP_mem_lam3' hd b
  have hconj : commP b a * b = b * (commP b a * (commP b (commP b a))⁻¹) := by
    rw [← conj_eq_mul_commP b (commP b a)]; group
  have hsq : (a * b) ^ 2
      = a ^ 2 * b ^ 2 * commP b a * (commP b (commP b a))⁻¹ := by
    calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
      _ = a * (a * b * commP b a) * b := by rw [mul_swap_commP b a]
      _ = a * a * b * (commP b a * b) := by group
      _ = a * a * b * (b * (commP b a * (commP b (commP b a))⁻¹)) := by rw [hconj]
      _ = a ^ 2 * b ^ 2 * commP b a * (commP b (commP b a))⁻¹ := by
          rw [pow_two a, pow_two b]; group
  have hab2 : a ^ 2 * b ^ 2 ∈ lambdaImage G 2 4 :=
    (lambdaImage G 2 4).mul_mem (sq_mem_lam2 a) (sq_mem_lam2 b)
  have h4 : (a * b) ^ 4 = ((a * b) ^ 2) ^ 2 := by rw [← pow_mul]
  rw [h4, hsq, sq_mul_central (lam3_inv_central he) (lam3_inv_sq he),
    (lam2_commute hab2 hd).mul_pow 2,
    (lam2_commute (sq_mem_lam2 a) (sq_mem_lam2 b)).mul_pow 2, ← pow_mul, ← pow_mul]

/-! ### Support subgroups -/

/-- `{b | [a,b]² ∈ K}` is a subgroup (right-slot bimultiplicativity). -/
private def brSqRight (K : Subgroup (levelQuot G 4)) (a : levelQuot G 4) :
    Subgroup (levelQuot G 4) where
  carrier := {b | commP a b ^ 2 ∈ K}
  one_mem' := by
    show commP a 1 ^ 2 ∈ K
    rw [commP_one_right, one_pow]
    exact K.one_mem
  mul_mem' := by
    intro b₁ b₂ h₁ h₂
    show commP a (b₁ * b₂) ^ 2 ∈ K
    rw [commP_sq_mul_right]
    exact K.mul_mem h₂ h₁
  inv_mem' := by
    intro b hb
    show commP a b⁻¹ ^ 2 ∈ K
    have h := commP_sq_mul_right a b b⁻¹
    rw [mul_inv_cancel, commP_one_right, one_pow] at h
    rw [eq_inv_of_mul_eq_one_left h.symm]
    exact K.inv_mem hb

/-- `{a | ∀ b, [a,b]² ∈ K}` is a subgroup (left-slot bimultiplicativity). -/
private def brSqLeft (K : Subgroup (levelQuot G 4)) : Subgroup (levelQuot G 4) where
  carrier := {a | ∀ b, commP a b ^ 2 ∈ K}
  one_mem' := by
    intro b
    show commP 1 b ^ 2 ∈ K
    rw [commP_one_left, one_pow]
    exact K.one_mem
  mul_mem' := by
    intro a₁ a₂ h₁ h₂ b
    show commP (a₁ * a₂) b ^ 2 ∈ K
    rw [commP_sq_mul_left]
    exact K.mul_mem (h₁ b) (h₂ b)
  inv_mem' := by
    intro a ha b
    show commP a⁻¹ b ^ 2 ∈ K
    have h := commP_sq_mul_left a a⁻¹ b
    rw [mul_inv_cancel, commP_one_left, one_pow] at h
    rw [eq_inv_of_mul_eq_one_right h.symm]
    exact K.inv_mem (ha b)

/-- `{a | a⁴ ∈ K}` is a subgroup once all bracket squares lie in `K`. -/
private def powFourSupport (K : Subgroup (levelQuot G 4))
    (hbrsq : ∀ a b : levelQuot G 4, commP a b ^ 2 ∈ K) : Subgroup (levelQuot G 4) where
  carrier := {a | a ^ 4 ∈ K}
  one_mem' := by
    show (1 : levelQuot G 4) ^ 4 ∈ K
    rw [one_pow]
    exact K.one_mem
  mul_mem' := by
    intro a b ha hb
    show (a * b) ^ 4 ∈ K
    rw [pow_four_mul]
    exact K.mul_mem (K.mul_mem ha hb) (hbrsq b a)
  inv_mem' := by
    intro a ha
    show (a⁻¹) ^ 4 ∈ K
    rw [inv_pow]
    exact K.inv_mem ha

/-- `{g | [v,g] ∈ K}` is a subgroup for `v ∈ Λ₂` (values are central). -/
private def brAtomSupport (K : Subgroup (levelQuot G 4)) {v : levelQuot G 4}
    (hv : v ∈ lambdaImage G 2 4) : Subgroup (levelQuot G 4) where
  carrier := {g | commP v g ∈ K}
  one_mem' := by
    show commP v 1 ∈ K
    rw [commP_one_right]
    exact K.one_mem
  mul_mem' := by
    intro g₁ g₂ h₁ h₂
    show commP v (g₁ * g₂) ∈ K
    rw [commP_mul_right, conj_lam3 (commP_mem_lam3 hv g₁)]
    exact K.mul_mem h₂ h₁
  inv_mem' := by
    intro g hg
    show commP v g⁻¹ ∈ K
    have h : commP v (g * g⁻¹) = commP v g⁻¹ * commP v g := by
      rw [commP_mul_right, conj_lam3 (commP_mem_lam3 hv g)]
    rw [mul_inv_cancel, commP_one_right] at h
    rw [eq_inv_of_mul_eq_one_left h.symm]
    exact K.inv_mem hg

end LevelFour

/-! ## Stage 0'': the marked classes generate `Q₄(F₃)` -/

/-- The marked generator classes of `Q₄ = levelQuot F₃ 4`. -/
private noncomputable def mgen (i : Fin 3) : levelQuot (freeProTwo : Type) 4 :=
  levelMk (freeProTwo : Type) 4 (freeGen i)

private theorem closure_mgen : Subgroup.closure (Set.range mgen) = ⊤ := by
  haveI := discreteTopology_levelQuot (freeProTwo : Type) freeTopGenFinset
    isProP_maxProPQuotient 4
  have h := map_topologicalClosure_eq_of_discrete (freeProTwo : Type)
    (Subgroup.closure (Set.range freeGen)) (levelMk (freeProTwo : Type) 4)
    (continuous_levelMk (freeProTwo : Type) 4)
  rw [topGen_freeProTwo, Subgroup.map_top_of_surjective _
      (levelMk_surjective (freeProTwo : Type) 4), MonoidHom.map_closure,
    ← Set.range_comp] at h
  exact h.symm

/-! ## The base case, role-generic core -/

/-- **The `k = 3` span base case for an arbitrary marked generating family.**

This is the rank-free algebraic core of `span_base_core`.  One distinguished generator
`marked t` carries the diagonal column `v² [v,marked t]`; every other generator carries a
plain bracket column and a fourth-power tail.  These data generate `Z₃` for any topologically
finitely generated pro-`2` ambient group once the displayed classes generate `Q₄`.

The proof is the same cubic calculation as the original `Fin 3` theorem.  Generalizing the
index is what allows the improved square presentation's hyperbolic handle rows to participate
without reducing them to the rank-three model. -/
theorem span_base_core_of_generators
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {ι : Type*} (marked : ι → levelQuot G 4)
    (hgen : Subgroup.closure (Set.range marked) = ⊤)
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G)
    (K : Subgroup (levelQuot G 4)) (t : ι)
    (hcol : ∀ v ∈ lambdaImage G 2 4, v ^ 2 * commP v (marked t) ∈ K)
    (hbr : ∀ i : ι, i ≠ t → ∀ v ∈ lambdaImage G 2 4,
      commP v (marked i) ∈ K)
    (htail : ∀ i : ι, i ≠ t → marked i ^ 4 ∈ K) :
    zLayer G 3 ≤ K := by
  have mem_of_marked_mem {S : Subgroup (levelQuot G 4)}
      (hs : ∀ i, marked i ∈ S) (a : levelQuot G 4) : a ∈ S := by
    have hle : Subgroup.closure (Set.range marked) ≤ S := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact hs i
    exact hle (by rw [hgen]; trivial)
  -- Generator fourth powers: tails away from `t`, and the diagonal row at `t`.
  have hgen4 : ∀ i : ι, marked i ^ 4 ∈ K := by
    intro i
    by_cases hi : i = t
    · subst hi
      have h := hcol _ (sq_mem_lam2 (marked i))
      have hc : commP (marked i ^ 2) (marked i) = 1 :=
        commP_eq_one_of_mul_comm ((Commute.refl (marked i)).pow_left 2).eq
      have hpm : (marked i ^ 2) ^ 2 = marked i ^ 4 := by rw [← pow_mul]
      rwa [hc, mul_one, hpm] at h
    · exact htail i hi
  -- Every square-generator bracket column is available.
  have hcolsq : ∀ i j : ι, commP (marked i ^ 2) (marked j) ∈ K := by
    intro i j
    by_cases hj : j = t
    · subst hj
      have h := hcol _ (sq_mem_lam2 (marked i))
      have hpm : (marked i ^ 2) ^ 2 = marked i ^ 4 := by rw [← pow_mul]
      rw [hpm] at h
      have h3 := K.mul_mem (K.inv_mem (hgen4 i)) h
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at h3
    · exact hbr j hj _ (sq_mem_lam2 (marked i))
  -- Squares of brackets between displayed generators.
  have hbrsq_gen : ∀ i j : ι, commP (marked i) (marked j) ^ 2 ∈ K := by
    have main : ∀ i j : ι, i ≠ t → commP (marked i) (marked j) ^ 2 ∈ K := by
      intro i j hi
      rw [commP_sq_eq]
      exact K.mul_mem (hcolsq i j)
        (K.inv_mem (hbr i hi _ (commP_mem_lam2 (marked i) (marked j))))
    intro i j
    by_cases hi : i = t
    · by_cases hj : j = t
      · subst i
        subst j
        rw [commP_self', one_pow]
        exact K.one_mem
      · rw [commP_symm (marked i) (marked j), inv_pow]
        exact K.inv_mem (main j i hj)
    · exact main i j hi
  -- Bimultiplicativity upgrades displayed bracket squares to all bracket squares.
  have hbrsq : ∀ a b : levelQuot G 4, commP a b ^ 2 ∈ K := by
    have inner : ∀ i : ι, ∀ b, commP (marked i) b ^ 2 ∈ K := fun i b =>
      mem_of_marked_mem (S := brSqRight K (marked i)) (fun j => hbrsq_gen i j) b
    intro a b
    exact mem_of_marked_mem (S := brSqLeft K) inner a b
  -- Hence all fourth powers are in the target.
  have hpow4 : ∀ a : levelQuot G 4, a ^ 4 ∈ K := fun a =>
    mem_of_marked_mem (S := powFourSupport K hbrsq) hgen4 a
  -- Squares of arbitrary `Λ₂` elements.
  have key_sq : ∀ v ∈ lambdaImage G 2 4, v ^ 2 ∈ K := by
    intro v hv
    have H : v ∈ lambdaImage G 2 4 ∧ v ^ 2 ∈ K := by
      refine lambdaImage_induction G hfg hpro
        (j := 1) (m := 4) le_rfl
        (p := fun q => q ∈ lambdaImage G 2 4 ∧ q ^ 2 ∈ K)
        ?_ ?_ ⟨one_mem _, by rw [one_pow]; exact K.one_mem⟩ ?_ ?_ hv
      · intro u _
        rw [map_pow]
        refine ⟨sq_mem_lam2 _, ?_⟩
        rw [← pow_mul]
        exact hpow4 _
      · intro u _ g
        rw [levelMk_commutator]
        exact ⟨commP_mem_lam2 _ _, hbrsq _ _⟩
      · rintro x y ⟨hx, hx2⟩ ⟨hy, hy2⟩
        exact ⟨Subgroup.mul_mem _ hx hy, by
          rw [(lam2_commute hx hy).mul_pow]
          exact K.mul_mem hx2 hy2⟩
      · rintro x ⟨hx, hx2⟩
        exact ⟨Subgroup.inv_mem _ hx, by rw [inv_pow]; exact K.inv_mem hx2⟩
    exact H.2
  -- Brackets of arbitrary `Λ₂` elements against arbitrary ambient classes.
  have hbratom : ∀ v ∈ lambdaImage G 2 4,
      ∀ g : levelQuot G 4, commP v g ∈ K := by
    intro v hv g
    refine mem_of_marked_mem (S := brAtomSupport K hv) (fun i => ?_) g
    show commP v (marked i) ∈ K
    by_cases hi : i = t
    · subst hi
      have h3 := K.mul_mem (K.inv_mem (key_sq v hv)) (hcol v hv)
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at h3
    · exact hbr i hi v hv
  -- Atomize `Z₃ = Λ₃` and assemble.
  intro q hq
  refine lambdaImage_induction G hfg hpro
    (j := 2) (m := 4) (by omega) ?_ ?_ K.one_mem
    (fun x y hx hy => K.mul_mem hx hy) (fun x hx => K.inv_mem hx) hq
  · intro u hu
    rw [map_pow]
    exact key_sq _ ⟨u, hu, rfl⟩
  · intro u hu g
    rw [levelMk_commutator]
    exact hbratom _ (Subgroup.inv_mem _ ⟨u, hu, rfl⟩) _

/-- **The `k = 3` span base case, uniform in the twisted role** (memo §2.2).

`K` is the span target; `mgen t` is the twisted generator `τ` (whose bracket column is
coupled to the square `v²`), and the other two marked generators carry a plain bracket
column and a fourth-power tail. -/
private theorem span_base_core (K : Subgroup (levelQuot (freeProTwo : Type) 4)) (t : Fin 3)
    (hcol : ∀ v ∈ lambdaImage (freeProTwo : Type) 2 4, v ^ 2 * commP v (mgen t) ∈ K)
    (hbr : ∀ i : Fin 3, i ≠ t → ∀ v ∈ lambdaImage (freeProTwo : Type) 2 4,
      commP v (mgen i) ∈ K)
    (htail : ∀ i : Fin 3, i ≠ t → mgen i ^ 4 ∈ K) :
    zLayer (freeProTwo : Type) 3 ≤ K := by
  exact span_base_core_of_generators mgen closure_mgen freeTopGenFinset
    isProP_maxProPQuotient K t hcol hbr htail

/-! ## The two frozen statements -/

/-- **The span base case, `r₀` shape** (memo §2.2).  Fill: GL-C. -/
theorem span_base_r0 : zLayer (freeProTwo : Type) 3 ≤ SpanTargetR0 3 := by
  refine span_base_core (SpanTargetR0 3) 0 (fun v hv => ?_) (fun i hi v hv => ?_)
    (fun i hi => ?_)
  · exact Subgroup.subset_closure (Or.inl ⟨![v, 1, 1], fun j => by fin_cases j <;> simp [hv],
      dbarWordR0_slot0 _ _ _ v⟩)
  · fin_cases i
    · exact absurd rfl hi
    · exact Subgroup.subset_closure (Or.inl ⟨![1, 1, v], fun j => by fin_cases j <;> simp [hv],
        dbarWordR0_slot2 _ _ _ v⟩)
    · exact Subgroup.subset_closure (Or.inl ⟨![1, v, 1], fun j => by fin_cases j <;> simp [hv],
        dbarWordR0_slot1 _ _ _ v⟩)
  · fin_cases i
    · exact absurd rfl hi
    · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
    · exact Subgroup.subset_closure (Or.inr (Or.inr rfl))

/-- The span base case, `r₂` shape.  Fill: GL-C. -/
theorem span_base_r2 : zLayer (freeProTwo : Type) 3 ≤ SpanTargetR2 3 := by
  refine span_base_core (SpanTargetR2 3) 2 (fun v hv => ?_) (fun i hi v hv => ?_)
    (fun i hi => ?_)
  · exact Subgroup.subset_closure (Or.inl ⟨![1, 1, v], fun j => by fin_cases j <;> simp [hv],
      dbarWordR2_slot2 _ _ _ v⟩)
  · fin_cases i
    · exact Subgroup.subset_closure (Or.inl ⟨![1, v, 1], fun j => by fin_cases j <;> simp [hv],
        dbarWordR2_slot1 _ _ _ v⟩)
    · exact Subgroup.subset_closure (Or.inl ⟨![v, 1, 1], fun j => by fin_cases j <;> simp [hv],
        dbarWordR2_slot0 _ _ _ v⟩)
    · exact absurd rfl hi
  · fin_cases i
    · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
    · exact Subgroup.subset_closure (Or.inr (Or.inr rfl))
    · exact absurd rfl hi

end GQ2.Roe.Labute

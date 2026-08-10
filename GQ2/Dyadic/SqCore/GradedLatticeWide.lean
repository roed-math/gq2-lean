/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedObstructionPlus
import GQ2.Dyadic.SqCore.GradedFourRow

/-!
# W56-WIDEN: the class-four obstruction over the honest `γ₂(im Φ)`

`GradedObstructionPlus` proved the class-four obstruction `sqRelWord_selLamTwo_ne_one` over
`selLamTwo`: `γ₂`-shaped, even `g`-column, and `(h, i)`-data in `selLamThreePlus`.  Its own
scope paragraph priced the remaining gap exactly:

> `selLamTwo`, the lattice the `γ₂`-level obstruction quantifies over, is an
> **over-approximation** of the honest achievable lattice.

The over-approximation is in the `γ₂`-shape and the even `g`-column; in the `(h, i)`-direction
it is an **under**-approximation, and that is the gap.  `selLamThreePlus` carries the
`(h, i)`-data of three of the ten frame-slot commutators; the honest `γ₂(im Φ)` carries all
ten, the fifty triple commutators, the `x₁`-square and its five commutators - the very
generating set the wave-54 census computed its residual verdict over
(`docs/dyadic/w54-gamma2-note.md` §5.1).  Those were **not** shown to lie in
`selLamThreePlus`, and §5 below exhibits a binder point where `⁅σ, V⁆` provably does not
(`selLamThreePlus_not_commP_zero_handleV`).  So the theorem's model did not match the
census's model, and the wave-54 verdict was not yet certified.

This file closes that, and closes it **without a lattice at all**.

* ⭐⭐ **The obstruction over the honest object** (`selGaTwoIm`,
  `sqRelWord_selGaTwoIm_ne_one`, `_fourteen`): at a stage-three survivor of the witness with an
  **odd** class-four residue, **no** five-slot dressing drawn from `γ₂(im Φ)` - the commutator
  subgroup of the marking's image, together with the `x₁`-square, quadratic terms and triple
  commutators included - kills the relator.  Nothing is quantified over a generating model: the
  hypothesis is membership in a subgroup of `SqU5`, so the statement is stable under any change
  of generating set, which is what the wave-54 census's verdict needs.
* ⭐⭐ **The one algebraic input** (`selFrameSub`, `selWideSub`, `commP_mem_selWideSub`): the
  marking's subgroup has an **even first abelian column**, its `(c, d)`-columns are an
  `𝔽₂`-combination of the two handle letters' `(C, E)` and `(D, F)`, and its first class-two
  column is a `P`-multiple; those three invariants force **every** commutator of two of its
  elements to have an even `g`-column and to pair evenly against both handle letters' outer
  columns.  This is the technique of `GradedFourRow` §6 (`commP_mem_rowGaTwoSub`), carried off
  that lane's single point to the whole committed witness family.
* ⭐⭐ **`A` and `B` are even** (`selLiftWit_ab_even_of_odd`).  The wave-54 note observed
  (§5.2) that all ten mod-2 classes of its residual `33792` corners have `A` and `B` both even.
  That is a **theorem**: four of the fourteen pairings - `R·B`, `A·R`,
  `(P·D − Q·B)·F − Q·F·B` and `A·Q·E − E·(P·C − Q·A)` - together with the oddness of the
  class-four selection bit force `A` and `B` even, and with them `P·C·E`, `P·C·F`, `P·D·E`,
  `P·D·F`.  A `2048`-case 𝔽₂ core.  The observed structure of the residual set is the
  hypothesis set, seen from the other side.
* **Only four of the fourteen hypotheses are consumed.**  `sqRelWord_selGaTwoIm_ne_one`
  carries `h₅`, `h₇`, `h₅'`, `h₆'` and nothing else from the pairing list;
  `sqRelWord_selGaTwoIm_ne_one_fourteen` restates it with the committed fourteen so that it can
  be read against `sqRelWord_selLamTwo_ne_one` line by line - same hypotheses, the census's own
  object in place of the lattice.  **Neither statement implies the other**: `selLamTwo` holds
  `γ₂`-shaped elements that are no commutator of anything, and `γ₂(im Φ)` holds commutators
  whose `(h, i)`-data `selLamThreePlus` misses (§5).  What the new one adds is that its
  quantifier is the object the census computed in.

## Honest scope

What is *modelled* rather than proved is unchanged and is now the **only** thing modelled: the
achievability convention that a test hom carries `γ₂` of the honest group onto `γ₂` of its
image, so that a dressing may be drawn from `γ₂(im Φ) = ⟨⁅im Φ, im Φ⁆, Φ(x₁)²⟩`.  That is
exactly the convention `GradedGammaTwo` and `GradedFourRow` carry.  No lattice, no generating
set and no over-approximation is carried beyond it.  In particular `selLamTwo` is not used:
the two statements are independent, and neither implies the other.

Measured, not proved (`scripts/w56_widen/results/`): at **all** `98304` live corners of the
whole binder - the points where the fourteen pairings are even and the class-four bit is odd -
every one of the `66` census generators' `(h, i)`-data does land in the `selLamThreePlus` span,
so on the locus where the committed theorem applies the two models happen to coincide.  That is
a measurement of `(Z/8)^2`-spans at `98304` points, not an identity: off the live set the
containment fails (§5), and no wave has a uniform witness for it.  The theorems below do not
use it.

## Contents

* **§1** ⭐⭐ the 𝔽₂ core and `selLiftWit_ab_even_of_odd`;
* **§2** ⭐⭐ the two subgroups and the commutator bound `commP_mem_selWideSub`;
* **§3** the marking inside `selFrameSub`, the honest object `selGaTwoIm`, and the containment;
* **§4** ⭐⭐ the obstruction over `γ₂(im Φ)`, in both hypothesis shapes;
* **§5** the three further frame-slot commutators in closed form, the census's whole
  generating set inside `selGaTwoIm`, and the binder point at which `selLamThreePlus` provably
  misses one of them;
* **§6** the residual corner run end to end;
* **§7** committed axiom prints (all std-3).

Companion computations: `scripts/w56_widen/` (`widen_core.py`, `widen_gens.py`,
`widen_sweep.py`), certified outputs in `scripts/w56_widen/results/`.  Every claim above was
derived and validated before transcription: the 𝔽₂ core exhaustively over all `4096` mod-2
parameter points; the commutator bound over every ordered pair of the mod-2 marking subgroup;
the `66` census generators over every live mod-2 class by honest `U₅` arithmetic; the live set
exhaustively over the whole `4194304`-point binder; and `4800` five-slot `γ₂(im Φ)` dressings
against honest group collection.  **Zero mismatches.**
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 ⭐⭐ The 𝔽₂ core: the hypotheses force `A` and `B` even

The wave-54 note's §5.2 observation, turned around.  Four of the fourteen pairings and the
oddness of the class-four selection bit `(A·C·F + B·D·E)·T + P·R` leave no room for an odd `A`
or an odd `B`, and then the four `P`-products the next section needs are even too.  Eleven
mod-2 variables, `2048` cases.

Read the mechanism off the core: an odd `A` forces `R` even (`h₅'`) and `E·P·C` even
(`h₆'`), an odd `B` forces `R` even (`h₅`); the bit then has to be carried by its `T`-term,
which the remaining pairing `h₇` kills. -/

section AbEven

variable {A B C D E F T S P Q R W2 : gr3R}

private theorem selPar_two : selPar (2 : gr3R) = 0 := by decide

set_option synthInstance.maxSize 512 in
/-- The 𝔽₂ core: eleven mod-2 variables, the four parity rows, four of the fourteen pairings
and the odd bit.  `2048` cases. -/
private theorem widenAb_core : ∀ a b c d e f t s p q r : ZMod 2,
    a * s - b * t = 0 → t * d - s * c = 0 → c * f - d * e = 0 → e * s - f * t = 0 →
    r * b = 0 →
    (p * d - q * b) * f - (q * f) * b = 0 →
    a * r = 0 →
    a * (q * e) - e * (p * c - q * a) = 0 →
    (a * (c * f) + b * (d * e)) * t + p * r = 1 →
    a = 0 ∧ b = 0 ∧ p * (c * e) = 0 ∧ p * (c * f) = 0 ∧ p * (d * e) = 0 ∧
      p * (d * f) = 0 := by
  decide

/-- ⭐⭐ **The obstruction's own hypotheses force `A` and `B` even.**  At a marking satisfying
the four parity rows where the four pairings `R·B`, `(P·D − Q·B)·F − Q·F·B`, `A·R` and
`A·Q·E − E·(P·C − Q·A)` are even and the class-four selection bit is **odd**, the two handle
letters' first abelian columns `A` and `B` are both even, and so are the four products
`P·C·E`, `P·C·F`, `P·D·E`, `P·D·F`.

This is `docs/dyadic/w54-gamma2-note.md` §5.2 as a theorem: the note *measured* that all ten
mod-2 classes of its residual corners have `A = B = 0`; here that is forced by the hypothesis
set itself.  It subsumes `GradedObstructionPlus.selLiftWit_ae_bf_even_of_odd`, whose
conclusions `A·E` and `B·F` even are immediate from it. -/
theorem selLiftWit_ab_even_of_odd
    (hd : 2 * P + (A * S - B * T) = 0) (he : 2 * Q + (T * D - S * C) = 0)
    (hg : 2 * R + (C * F - D * E) = 0) (hb : 2 * W2 + (E * S - F * T) = 0)
    (h₅ : ∃ k, R * B = 2 * k)
    (h₇ : ∃ k, (P * D - Q * B) * F - (Q * F) * B = 2 * k)
    (h₅' : ∃ k, A * R = 2 * k)
    (h₆' : ∃ k, A * (Q * E) - E * (P * C - Q * A) = 2 * k)
    (hbit : selPar ((A * (C * F) + B * (D * E)) * T + P * R) = 1) :
    (∃ k, A = 2 * k) ∧ (∃ k, B = 2 * k) ∧ (∃ k, P * (C * E) = 2 * k)
      ∧ (∃ k, P * (C * F) = 2 * k) ∧ (∃ k, P * (D * E) = 2 * k)
      ∧ (∃ k, P * (D * F) = 2 * k) := by
  have qd : selPar A * selPar S - selPar B * selPar T = 0 := by
    have hh := congrArg selPar hd
    simp only [selPar_add, selPar_sub, selPar_mul, selPar_two, selPar_zero, zero_mul,
      zero_add] at hh
    linear_combination hh
  have qe : selPar T * selPar D - selPar S * selPar C = 0 := by
    have hh := congrArg selPar he
    simp only [selPar_add, selPar_sub, selPar_mul, selPar_two, selPar_zero, zero_mul,
      zero_add] at hh
    linear_combination hh
  have qg : selPar C * selPar F - selPar D * selPar E = 0 := by
    have hh := congrArg selPar hg
    simp only [selPar_add, selPar_sub, selPar_mul, selPar_two, selPar_zero, zero_mul,
      zero_add] at hh
    linear_combination hh
  have qb : selPar E * selPar S - selPar F * selPar T = 0 := by
    have hh := congrArg selPar hb
    simp only [selPar_add, selPar_sub, selPar_mul, selPar_two, selPar_zero, zero_mul,
      zero_add] at hh
    linear_combination hh
  have q₅ : selPar R * selPar B = 0 := by
    have hh := (selPar_eq_zero_iff _).mpr h₅
    simp only [selPar_mul] at hh
    linear_combination hh
  have q₇ : (selPar P * selPar D - selPar Q * selPar B) * selPar F
      - (selPar Q * selPar F) * selPar B = 0 := by
    have hh := (selPar_eq_zero_iff _).mpr h₇
    simp only [selPar_sub, selPar_mul] at hh
    linear_combination hh
  have q₅' : selPar A * selPar R = 0 := by
    have hh := (selPar_eq_zero_iff _).mpr h₅'
    simp only [selPar_mul] at hh
    linear_combination hh
  have q₆' : selPar A * (selPar Q * selPar E)
      - selPar E * (selPar P * selPar C - selPar Q * selPar A) = 0 := by
    have hh := (selPar_eq_zero_iff _).mpr h₆'
    simp only [selPar_sub, selPar_mul] at hh
    linear_combination hh
  have qbit : (selPar A * (selPar C * selPar F) + selPar B * (selPar D * selPar E)) * selPar T
      + selPar P * selPar R = 1 := by
    simp only [selPar_add, selPar_mul] at hbit
    linear_combination hbit
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := widenAb_core (selPar A) (selPar B) (selPar C) (selPar D)
    (selPar E) (selPar F) (selPar T) (selPar S) (selPar P) (selPar Q) (selPar R)
    qd qe qg qb q₅ q₇ q₅' q₆' qbit
  refine ⟨(selPar_eq_zero_iff _).mp e₁, (selPar_eq_zero_iff _).mp e₂,
    (selPar_eq_zero_iff _).mp (by rw [selPar_mul, selPar_mul]; exact e₃),
    (selPar_eq_zero_iff _).mp (by rw [selPar_mul, selPar_mul]; exact e₄),
    (selPar_eq_zero_iff _).mp (by rw [selPar_mul, selPar_mul]; exact e₅),
    (selPar_eq_zero_iff _).mp (by rw [selPar_mul, selPar_mul]; exact e₆)⟩

end AbEven

/-! ## §2 ⭐⭐ The two subgroups, and the commutator bound

`selFrameSub` collects the three invariants every slot of the class-four witness satisfies once
`A` and `B` are known even: an **even** first abelian column, a `(c, d)`-column that is an
`𝔽₂`-combination `α·(C, E) + β·(D, F)` of the two handle letters', and a first class-two column
that is a multiple of `P`.  It is a subgroup with no hypothesis whatever: the first two columns
are additive and the third's only correction is `p.a·q.b`, even by the first invariant.

`selWideSub` is where the class-four obstruction needs a dressing to land: `γ₂`-shaped, even
`g`-column, and the two `(h, i)`-pairings against the handle letters' outer columns `(F, B)`
and `(E, A)` even.  These are exactly the five families of hypotheses
`GradedObstructionPlus.sqRelWord_conFourDress_selLiftWit_ne_one` consumes, so nothing else has
to be arranged.

⭐⭐ `commP_mem_selWideSub` is the bridge, and it is the whole mathematical content of the
file: `⁅selFrameSub, selFrameSub⁆ ≤ selWideSub`.  Two facts drive it.  The `g`-column of the
commutator is `(α₁·β₂ − β₁·α₂)·(C·F − D·E) = −2·R·(α₁·β₂ − β₁·α₂)` by the `hg`-row.  And the
left class-three form `u5Comm3L` collapses, modulo `2`, to `u·(P·C) + v·(P·D)`: every term
carrying a first abelian column is even, and the surviving `p.e·q.c − p.c·q.e` is `P` against
the `(C, D)`-columns.  Pairing that against `F` or `E` gives the four `P`-products of §1, and
the `(h, i)`-pairings' other halves carry the even `A` or `B` outright. -/

section WideSubgroups

variable {A B C D E F P R : gr3R} {p q : SqU5 gr3R}

/-- **The three invariants of the class-four marking's subgroup.**  An even first abelian
column; a `(c, d)`-column in the `𝔽₂`-span of the two handle letters' `(C, E)` and `(D, F)`;
and a first class-two column that is a multiple of `P`.  A subgroup of `SqU5 gr3R` outright. -/
def selFrameSub (C D E F P : gr3R) : Subgroup (SqU5 gr3R) where
  carrier := {p | (∃ k, p.a = 2 * k)
    ∧ (∃ α β k₁ k₂, p.c = α * C + β * D + 2 * k₁ ∧ p.d = α * E + β * F + 2 * k₂)
    ∧ (∃ ε k, p.e = ε * P + 2 * k)}
  mul_mem' := fun {p q} hp hq => by
    obtain ⟨⟨ka, hka⟩, ⟨α₁, β₁, kc₁, kd₁, hpc, hpd⟩, ⟨ε₁, ke₁, hpe⟩⟩ := hp
    obtain ⟨⟨ka', hka'⟩, ⟨α₂, β₂, kc₂, kd₂, hqc, hqd⟩, ⟨ε₂, ke₂, hqe⟩⟩ := hq
    refine ⟨⟨ka + ka', by rw [SqU5.mul_a, hka, hka']; ring⟩,
      ⟨α₁ + α₂, β₁ + β₂, kc₁ + kc₂, kd₁ + kd₂,
        by rw [SqU5.mul_c, hpc, hqc]; ring, by rw [SqU5.mul_d, hpd, hqd]; ring⟩,
      ⟨ε₁ + ε₂, ke₁ + ke₂ + ka * q.b, by rw [SqU5.mul_e, hpe, hqe, hka]; ring⟩⟩
  one_mem' := ⟨⟨0, by rw [SqU5.one_a]; ring⟩,
    ⟨0, 0, 0, 0, by rw [SqU5.one_c]; ring, by rw [SqU5.one_d]; ring⟩,
    ⟨0, 0, by rw [SqU5.one_e]; ring⟩⟩
  inv_mem' := fun {p} hp => by
    obtain ⟨⟨ka, hka⟩, ⟨α₁, β₁, kc₁, kd₁, hpc, hpd⟩, ⟨ε₁, ke₁, hpe⟩⟩ := hp
    refine ⟨⟨-ka, by rw [SqU5.inv_a, hka]; ring⟩,
      ⟨-α₁, -β₁, -kc₁, -kd₁, by rw [SqU5.inv_c, hpc]; ring, by rw [SqU5.inv_d, hpd]; ring⟩,
      ⟨-ε₁, ka * p.b - ke₁, by rw [SqU5.inv_e, hka, hpe]; ring⟩⟩

theorem mem_selFrameSub : p ∈ selFrameSub C D E F P ↔ (∃ k, p.a = 2 * k)
    ∧ (∃ α β k₁ k₂, p.c = α * C + β * D + 2 * k₁ ∧ p.d = α * E + β * F + 2 * k₂)
    ∧ (∃ ε k, p.e = ε * P + 2 * k) := Iff.rfl

/-- **Where a `γ₂`-level dressing of the class-four witness has to land**: `γ₂`-shaped, even
`g`-column, and even pairing against both handle letters' outer columns.  Exactly the five
families of hypotheses `sqRelWord_conFourDress_selLiftWit_ne_one` consumes, packaged as a
subgroup: on `γ₂` all three of `g`, `h`, `i` are additive, so the package is closed. -/
def selWideSub (A B E F : gr3R) : Subgroup (SqU5 gr3R) where
  carrier := {p | p.a = 0 ∧ p.b = 0 ∧ p.c = 0 ∧ p.d = 0 ∧ (∃ k, p.g = 2 * k)
    ∧ (∃ k, p.h * F - p.i * B = 2 * k) ∧ (∃ k, A * p.i - E * p.h = 2 * k)}
  mul_mem' := fun {p q} hp hq => by
    obtain ⟨hpa, hpb, hpc, hpd, ⟨gp, hgp⟩, ⟨up, hup⟩, ⟨vp, hvp⟩⟩ := hp
    obtain ⟨hqa, hqb, hqc, hqd, ⟨gq, hgq⟩, ⟨uq, huq⟩, ⟨vq, hvq⟩⟩ := hq
    refine ⟨by rw [SqU5.mul_a, hpa, hqa]; ring, by rw [SqU5.mul_b, hpb, hqb]; ring,
      by rw [SqU5.mul_c, hpc, hqc]; ring, by rw [SqU5.mul_d, hpd, hqd]; ring,
      ⟨gp + gq, by rw [SqU5.mul_g, hgp, hgq, hpc]; ring⟩,
      ⟨up + uq, ?_⟩, ⟨vp + vq, ?_⟩⟩
    · rw [SqU5.mul_h, SqU5.mul_i, hpa, hqc, hpb, hqd]
      linear_combination hup + huq
    · rw [SqU5.mul_h, SqU5.mul_i, hpa, hqc, hpb, hqd]
      linear_combination hvp + hvq
  one_mem' := ⟨rfl, rfl, rfl, rfl, ⟨0, by rw [SqU5.one_g]; ring⟩,
    ⟨0, by rw [SqU5.one_h, SqU5.one_i]; ring⟩, ⟨0, by rw [SqU5.one_h, SqU5.one_i]; ring⟩⟩
  inv_mem' := fun {p} hp => by
    obtain ⟨hpa, hpb, hpc, hpd, ⟨gp, hgp⟩, ⟨up, hup⟩, ⟨vp, hvp⟩⟩ := hp
    refine ⟨by rw [SqU5.inv_a, hpa]; ring, by rw [SqU5.inv_b, hpb]; ring,
      by rw [SqU5.inv_c, hpc]; ring, by rw [SqU5.inv_d, hpd]; ring,
      ⟨-gp, by rw [SqU5.inv_g, hpc, hgp]; ring⟩, ⟨-up, ?_⟩, ⟨-vp, ?_⟩⟩
    · rw [SqU5.inv_h, SqU5.inv_i, hpa, hpb, hpc, hpd]
      linear_combination -hup
    · rw [SqU5.inv_h, SqU5.inv_i, hpa, hpb, hpc, hpd]
      linear_combination -hvp

theorem mem_selWideSub : p ∈ selWideSub A B E F ↔ p.a = 0 ∧ p.b = 0 ∧ p.c = 0 ∧ p.d = 0
    ∧ (∃ k, p.g = 2 * k) ∧ (∃ k, p.h * F - p.i * B = 2 * k)
    ∧ (∃ k, A * p.i - E * p.h = 2 * k) := Iff.rfl

/-- **The left class-three form collapses to `P` against the `(C, D)`-columns**, modulo `2`.
Every one of the six terms of `u5Comm3L` that carries a first abelian column is even by the
first invariant, and the two that survive are `p.e·q.c − p.c·q.e`, whose `P`-content is the
alternating combination shown.  This is what makes the whole file a two-monomial argument. -/
private theorem comm3L_shape (hp : p ∈ selFrameSub C D E F P)
    (hq : q ∈ selFrameSub C D E F P) :
    ∃ u v k, SqU5.u5Comm3L p q = u * (P * C) + v * (P * D) + 2 * k := by
  obtain ⟨⟨ka, hka⟩, ⟨α₁, β₁, kc₁, kd₁, hpc, hpd⟩, ⟨ε₁, ke₁, hpe⟩⟩ := hp
  obtain ⟨⟨ka', hka'⟩, ⟨α₂, β₂, kc₂, kd₂, hqc, hqd⟩, ⟨ε₂, ke₂, hqe⟩⟩ := hq
  refine ⟨ε₁ * α₂ - α₁ * ε₂, ε₁ * β₂ - β₁ * ε₂,
    ka * q.f - p.f * ka' + ka * (α₁ * C + β₁ * D + 2 * kc₁) * q.b
      - ka * p.b * (α₂ * C + β₂ * D + 2 * kc₂)
      + (α₁ * C + β₁ * D + 2 * kc₁) * ka' * q.b
      - p.b * ka' * (α₂ * C + β₂ * D + 2 * kc₂)
      + ε₁ * P * kc₂ + ke₁ * (α₂ * C + β₂ * D + 2 * kc₂)
      - (α₁ * C + β₁ * D) * ke₂ - kc₁ * (ε₂ * P + 2 * ke₂), ?_⟩
  simp only [SqU5.u5Comm3L, hka, hka', hpc, hpe, hqc, hqe]
  ring

/-- The commutator's `g`-column is even: the `(c, d)`-invariant makes it
`(α₁·β₂ − β₁·α₂)·(C·F − D·E)`, and the `hg`-parity row makes that `−2·R·(α₁·β₂ − β₁·α₂)`. -/
private theorem commP_g_even_of_selFrameSub (hg : 2 * R + (C * F - D * E) = 0)
    (hp : p ∈ selFrameSub C D E F P) (hq : q ∈ selFrameSub C D E F P) :
    ∃ k, (commP p q).g = 2 * k := by
  obtain ⟨-, ⟨α₁, β₁, kc₁, kd₁, hpc, hpd⟩, -⟩ := hp
  obtain ⟨-, ⟨α₂, β₂, kc₂, kd₂, hqc, hqd⟩, -⟩ := hq
  refine ⟨-((α₁ * β₂ - β₁ * α₂) * R) + (α₁ * C + β₁ * D) * kd₂
    + kc₁ * (α₂ * E + β₂ * F + 2 * kd₂) - (α₁ * E + β₁ * F) * kc₂
    - kd₁ * (α₂ * C + β₂ * D + 2 * kc₂), ?_⟩
  rw [SqU5.commP_g, hpc, hpd, hqc, hqd]
  linear_combination (α₁ * β₂ - β₁ * α₂) * hg

/-- ⭐⭐ **The commutator bound**: `⁅selFrameSub, selFrameSub⁆ ≤ selWideSub`.  A commutator of
two elements carrying the three marking invariants has an even `g`-column and pairs evenly
against both handle letters' outer columns, given only the `hg`-parity row, the evenness of `A`
and `B`, and the evenness of the four `P`-products.  No shape hypothesis on the commutator is
needed, and none of the six invariants of the *other* columns (`b`, `f`, `g`) is used: the
`(h, i)`-pairings' `i`-halves carry the even `A` or `B` outright. -/
theorem commP_mem_selWideSub (hg : 2 * R + (C * F - D * E) = 0)
    (hA : ∃ k, A = 2 * k) (hB : ∃ k, B = 2 * k)
    (hPCE : ∃ k, P * (C * E) = 2 * k) (hPCF : ∃ k, P * (C * F) = 2 * k)
    (hPDE : ∃ k, P * (D * E) = 2 * k) (hPDF : ∃ k, P * (D * F) = 2 * k)
    (hp : p ∈ selFrameSub C D E F P) (hq : q ∈ selFrameSub C D E F P) :
    commP p q ∈ selWideSub A B E F := by
  obtain ⟨u, v, kL, hL⟩ := comm3L_shape hp hq
  obtain ⟨kg, hkg⟩ := commP_g_even_of_selFrameSub hg hp hq
  obtain ⟨kA, hkA⟩ := hA
  obtain ⟨kB, hkB⟩ := hB
  obtain ⟨m₁, hm₁⟩ := hPCE
  obtain ⟨m₂, hm₂⟩ := hPCF
  obtain ⟨m₃, hm₃⟩ := hPDE
  obtain ⟨m₄, hm₄⟩ := hPDF
  have hh : (commP p q).h = u * (P * C) + v * (P * D) + 2 * kL := by
    rw [SqU5.commP_h]; exact hL
  refine ⟨SqU5.commP_a p q, SqU5.commP_b p q, SqU5.commP_c p q, SqU5.commP_d p q, ⟨kg, hkg⟩,
    ⟨u * m₂ + v * m₄ + kL * F - kB * (commP p q).i, ?_⟩,
    ⟨kA * (commP p q).i - (u * m₁ + v * m₃ + kL * E), ?_⟩⟩
  · rw [hh]
    linear_combination u * hm₂ + v * hm₄ - (commP p q).i * hkB
  · rw [hh]
    linear_combination (commP p q).i * hkA - u * hm₁ - v * hm₃

end WideSubgroups

/-! ## §3 The marking, the honest object, and the containment

Every slot of `selLiftWit` carries the three invariants, and the two that are not outright are
the two handle letters', whose first abelian columns are `A` and `B`: §1 has just made them
even.  The `x₀`-slot's three columns are the three halves `2·P`, `−2·Q`, `2·W₂` of the `hd`-,
`he`- and `hb`-rows, and its class-two column `−2·T·S·B` is even outright.

`selGaTwoIm` is the honest achievable object under the campaign's standing convention: the
commutator subgroup of the marking's image (`GradedFourRow`'s `rowGaTwoOf`) together with the
`x₁`-square, which is what generates `γ₂(im Φ)` for a hom of the class-four selection family
(the `x₁`-square is the `Λ₅`-generator `(−2·P, −2·Q, −2·R)` of `GradedLift` §3, and it is the
only non-commutator generator).  It contains the ten frame-slot commutators, the fifty triple
commutators and the five commutators of the square - the wave-54 census's generating set - and
everything they generate. -/

section FrameMembership

variable {h : ℕ} {j : Fin h} {A B C D E F T S P Q R W2 : gr3R}

/-- Every slot of the class-four witness carries the three marking invariants, once `A` and `B`
are even.  Three parity rows are consumed, one per column of the `x₀`-slot. -/
theorem selLiftWit_mem_selFrameSub (hd : 2 * P + (A * S - B * T) = 0)
    (he : 2 * Q + (T * D - S * C) = 0) (hb : 2 * W2 + (E * S - F * T) = 0)
    (hA : ∃ k, A = 2 * k) (hB : ∃ k, B = 2 * k) (i : Fin (sqRank h)) :
    selLiftWit h j A B C D E F T S P Q R i ∈ selFrameSub C D E F P := by
  obtain ⟨kA, hkA⟩ := hA
  obtain ⟨kB, hkB⟩ := hB
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · exact ⟨⟨0, by simp [selLiftWit_zero]⟩,
      ⟨0, 0, 0, 0, by simp [selLiftWit_zero], by simp [selLiftWit_zero]⟩,
      ⟨0, 0, by simp [selLiftWit_zero]⟩⟩
  · refine ⟨⟨P, by simp only [selLiftWit_one]; linear_combination -hd⟩,
      ⟨0, 0, -Q, W2, by simp only [selLiftWit_one]; linear_combination he,
        by simp only [selLiftWit_one]; linear_combination -hb⟩,
      ⟨0, -(T * S * B), by simp only [selLiftWit_one]; ring⟩⟩
  · exact ⟨⟨0, by simp [selLiftWit_two]⟩,
      ⟨0, 0, 0, 0, by simp [selLiftWit_two], by simp [selLiftWit_two]⟩,
      ⟨1, 0, by simp [selLiftWit_two]⟩⟩
  · by_cases hj : j' = j
    · subst hj
      exact ⟨⟨kA, by simp only [selLiftWit_handleU]; exact hkA⟩,
        ⟨1, 0, 0, 0, by simp only [selLiftWit_handleU]; ring,
          by simp only [selLiftWit_handleU]; ring⟩,
        ⟨0, 0, by simp [selLiftWit_handleU]⟩⟩
    · exact ⟨⟨0, by simp [selLiftWit_handleU_ne hj]⟩,
        ⟨0, 0, 0, 0, by simp [selLiftWit_handleU_ne hj], by simp [selLiftWit_handleU_ne hj]⟩,
        ⟨0, 0, by simp [selLiftWit_handleU_ne hj]⟩⟩
  · by_cases hj : j' = j
    · subst hj
      refine ⟨⟨kB, by simp only [selLiftWit_handleV]; exact hkB⟩,
        ⟨0, 1, 0, 0, by simp only [selLiftWit_handleV]; ring,
          by simp only [selLiftWit_handleV]; ring⟩,
        ⟨0, -(kB * S), by simp only [selLiftWit_handleV]; linear_combination -S * hkB⟩⟩
    · exact ⟨⟨0, by simp [selLiftWit_handleV_ne hj]⟩,
        ⟨0, 0, 0, 0, by simp [selLiftWit_handleV_ne hj], by simp [selLiftWit_handleV_ne hj]⟩,
        ⟨0, 0, by simp [selLiftWit_handleV_ne hj]⟩⟩

/-- …hence the whole subgroup the marking generates does. -/
theorem selLiftWit_closure_le_selFrameSub (hd : 2 * P + (A * S - B * T) = 0)
    (he : 2 * Q + (T * D - S * C) = 0) (hb : 2 * W2 + (E * S - F * T) = 0)
    (hA : ∃ k, A = 2 * k) (hB : ∃ k, B = 2 * k) :
    Subgroup.closure (Set.range (selLiftWit h j A B C D E F T S P Q R))
      ≤ selFrameSub C D E F P := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact selLiftWit_mem_selFrameSub (W2 := W2) hd he hb hA hB i

/-- **The honest `γ₂`-level dressing set of the class-four witness**: the commutator subgroup
of the marking's image, together with the `x₁`-square.  Under the campaign's achievability
convention (a test hom carries `γ₂` of the honest group onto `γ₂` of its image) this is exactly
`γ₂(im Φ)`: `γ₂` of the ambient group is generated by its commutator subgroup and the square
whose image is `Φ(x₁)²`, the `Λ₅`-generator `(−2·P, −2·Q, −2·R)` of `GradedLift` §3.  It
contains the whole wave-54 census generating set and everything it generates, quadratic terms
and triple commutators included. -/
def selGaTwoIm (h : ℕ) (j : Fin h) (A B C D E F T S P Q R : gr3R) : Subgroup (SqU5 gr3R) :=
  rowGaTwoOf (Subgroup.closure (Set.range (selLiftWit h j A B C D E F T S P Q R)))
    ⊔ Subgroup.closure {selLiftWit h j A B C D E F T S P Q R 2
        * selLiftWit h j A B C D E F T S P Q R 2}

/-- ⭐⭐ **The containment**: the whole honest `γ₂(im Φ)` lands in `selWideSub`, i.e. every
`γ₂`-level dressing of the class-four witness is `γ₂`-shaped with an even `g`-column and pairs
evenly against both handle letters.  This is what replaces the lattice model. -/
theorem selGaTwoIm_le_selWideSub (hd : 2 * P + (A * S - B * T) = 0)
    (he : 2 * Q + (T * D - S * C) = 0) (hg : 2 * R + (C * F - D * E) = 0)
    (hb : 2 * W2 + (E * S - F * T) = 0)
    (hA : ∃ k, A = 2 * k) (hB : ∃ k, B = 2 * k)
    (hPCE : ∃ k, P * (C * E) = 2 * k) (hPCF : ∃ k, P * (C * F) = 2 * k)
    (hPDE : ∃ k, P * (D * E) = 2 * k) (hPDF : ∃ k, P * (D * F) = 2 * k) :
    selGaTwoIm h j A B C D E F T S P Q R ≤ selWideSub A B E F := by
  obtain ⟨kA, hkA⟩ := hA
  obtain ⟨kB, hkB⟩ := hB
  refine sup_le ?_ ?_
  · rw [rowGaTwoOf, Subgroup.closure_le]
    rintro z ⟨x, hx, y, hy, rfl⟩
    exact commP_mem_selWideSub hg ⟨kA, hkA⟩ ⟨kB, hkB⟩ hPCE hPCF hPDE hPDF
      (selLiftWit_closure_le_selFrameSub (W2 := W2) hd he hb ⟨kA, hkA⟩ ⟨kB, hkB⟩ hx)
      (selLiftWit_closure_le_selFrameSub (W2 := W2) hd he hb ⟨kA, hkA⟩ ⟨kB, hkB⟩ hy)
  · rw [Subgroup.closure_le]
    rintro z rfl
    refine ⟨by simp [selLiftWit_two], by simp [selLiftWit_two], by simp [selLiftWit_two],
      by simp [selLiftWit_two], ⟨R, by simp only [selLiftWit_two, SqU5.mul_g]; ring⟩,
      ⟨-((A + B) * Q * F), ?_⟩, ⟨E * ((A + B) * Q), ?_⟩⟩
    · simp only [selLiftWit_two, SqU5.mul_h, SqU5.mul_i]
      ring
    · simp only [selLiftWit_two, SqU5.mul_h, SqU5.mul_i]
      ring

end FrameMembership

/-! ## §4 ⭐⭐ The obstruction over `γ₂(im Φ)`

The committed `sqRelWord_conFourDress_selLiftWit_ne_one` already quantifies over an arbitrary
five-slot `γ₂`-dressing and consumes exactly five families of hypotheses about it: `γ₂`-shape,
even `g`-column, the two handle pairings, and the two `f`-column terms.  §2 and §3 supply the
first four for every dressing drawn from the honest object, and §1's `A`- and `B`-evenness
supplies the last two outright.  So the obstruction transfers with no further work, and with
four of the fourteen pairings rather than all of them. -/

section GaTwoImObstruction

variable {h : ℕ} {j : Fin h} {A B C D E F T S P Q R W2 res : gr3R}
  {z : Fin (sqRank h) → SqU5 gr3R}

/-- ⭐⭐ **The class-four obstruction over the honest `γ₂(im Φ)`**, with no lattice model at
all: at a stage-three survivor of the class-four witness whose residue is **odd**, where the
four pairings `R·B`, `(P·D − Q·B)·F − Q·F·B`, `A·R` and `A·Q·E − E·(P·C − Q·A)` are even, no
five-slot dressing with every slot in `γ₂(im Φ)` kills the relator.

This is the statement the wave-54 census's residual verdict needs: the census computed its
increment lattice over a *generating set* of `γ₂(im Φ)` (the ten frame-slot commutators, the
fifty triple commutators, the `x₁`-square and its five commutators), and the conclusion here
quantifies over the subgroup those generate, so no change of generating set can escape it.
Unlike `GradedObstructionPlus.sqRelWord_selLamTwo_ne_one` it carries no lattice
over-approximation, and it consumes four hypotheses rather than fourteen. -/
theorem sqRelWord_selGaTwoIm_ne_one
    (hz : ∀ i, z i ∈ selGaTwoIm h j A B C D E F T S P Q R)
    (hd : 2 * P + (A * S - B * T) = 0) (he : 2 * Q + (T * D - S * C) = 0)
    (hg : 2 * R + (C * F - D * E) = 0) (hb : 2 * W2 + (E * S - F * T) = 0)
    (h₅ : ∃ k, R * B = 2 * k)
    (h₇ : ∃ k, (P * D - Q * B) * F - (Q * F) * B = 2 * k)
    (h₅' : ∃ k, A * R = 2 * k)
    (h₆' : ∃ k, A * (Q * E) - E * (P * C - Q * A) = 2 * k)
    (h5 : sqRelWord (selLiftWit h j A B C D E F T S P Q R) = liftC res)
    (hodd : selPar res = 1) :
    sqRelWord (conFourDress (selLiftWit h j A B C D E F T S P Q R) z) ≠ 1 := by
  have hj5 : (sqRelWord (selLiftWit h j A B C D E F T S P Q R)).j = res := by
    rw [h5, liftC_j]
  have hbit : selPar ((A * (C * F) + B * (D * E)) * T + P * R) = 1 :=
    (selLiftWit_bit (h := h) (j := j) (S := S) (Q := Q) hg).symm.trans (by rw [hj5]; exact hodd)
  obtain ⟨hA, hB, hPCE, hPCF, hPDE, hPDF⟩ :=
    selLiftWit_ab_even_of_odd (W2 := W2) hd he hg hb h₅ h₇ h₅' h₆' hbit
  have hle := selGaTwoIm_le_selWideSub (h := h) (j := j) (W2 := W2) hd he hg hb hA hB
    hPCE hPCF hPDE hPDF
  obtain ⟨kA, hkA⟩ := hA
  obtain ⟨kB, hkB⟩ := hB
  refine sqRelWord_conFourDress_selLiftWit_ne_one (W2 := W2)
    (fun i => ⟨(hle (hz i)).1, (hle (hz i)).2.1, (hle (hz i)).2.2.1, (hle (hz i)).2.2.2.1⟩)
    (fun i => (hle (hz i)).2.2.2.2.1) hd hg hb
    (hle (hz (sqHandleIdxU j))).2.2.2.2.2.1 (hle (hz (sqHandleIdxV j))).2.2.2.2.2.2
    ⟨kB * (F * (z (sqHandleIdxU j)).f), by rw [hkB]; ring⟩
    ⟨kA * (E * (z (sqHandleIdxV j)).f), by rw [hkA]; ring⟩ h5 hodd

set_option linter.unusedVariables false in
/-- ⭐⭐ **The same, in the committed fourteen-hypothesis shape**: the exact hypotheses of
`GradedObstructionPlus.sqRelWord_selLamTwo_ne_one`, with the honest `γ₂(im Φ)` in place of
`selLamTwo`.  Ten of the fourteen are never used; they are carried only so that the two
statements can be compared line by line, and so that the wave-54 note's §7 item 1 is answered
in its own terms. -/
theorem sqRelWord_selGaTwoIm_ne_one_fourteen
    (hz : ∀ i, z i ∈ selGaTwoIm h j A B C D E F T S P Q R)
    (hd : 2 * P + (A * S - B * T) = 0) (he : 2 * Q + (T * D - S * C) = 0)
    (hg : 2 * R + (C * F - D * E) = 0) (hb : 2 * W2 + (E * S - F * T) = 0)
    (h₁ : ∃ k, (2 * (A * C)) * F + (C * E) * B = 2 * k)
    (h₂ : ∃ k, (A * D + B * C) * F + (D * E) * B = 2 * k)
    (h₃ : ∃ k, (A * D + B * C) * F + (C * F) * B = 2 * k)
    (h₄ : ∃ k, (2 * (B * D)) * F + (D * F) * B = 2 * k)
    (h₅ : ∃ k, R * B = 2 * k)
    (h₆ : ∃ k, (P * C - Q * A) * F - (Q * E) * B = 2 * k)
    (h₇ : ∃ k, (P * D - Q * B) * F - (Q * F) * B = 2 * k)
    (h₁' : ∃ k, A * (C * E) + E * (2 * (A * C)) = 2 * k)
    (h₂' : ∃ k, A * (D * E) + E * (A * D + B * C) = 2 * k)
    (h₃' : ∃ k, A * (C * F) + E * (A * D + B * C) = 2 * k)
    (h₄' : ∃ k, A * (D * F) + E * (2 * (B * D)) = 2 * k)
    (h₅' : ∃ k, A * R = 2 * k)
    (h₆' : ∃ k, A * (Q * E) - E * (P * C - Q * A) = 2 * k)
    (h₇' : ∃ k, A * (Q * F) - E * (P * D - Q * B) = 2 * k)
    (h5 : sqRelWord (selLiftWit h j A B C D E F T S P Q R) = liftC res)
    (hodd : selPar res = 1) :
    sqRelWord (conFourDress (selLiftWit h j A B C D E F T S P Q R) z) ≠ 1 :=
  sqRelWord_selGaTwoIm_ne_one (W2 := W2) hz hd he hg hb h₅ h₇ h₅' h₆' h5 hodd

end GaTwoImObstruction

/-! ## §5 What the honest object carries that `selLamThreePlus` does not

The three `x₁`-slot commutators of `GradedGammaTwo` §3 are three of the ten frame-slot
commutators.  Here are the three the `σ`-slot and the two handle slots contribute, in closed
form: `⁅σ, U⁆` and `⁅σ, V⁆` are the `(−A, C)`- and `(−B, D)`-generators of `Λ₅` with class-three
data `(−A·C, 0)` and `(−B·D, 0)`, and `⁅U, V⁆` is the handle commutator, whose `g`-column
`C·F − D·E = −2·R` is the `hg`-row.  (The remaining four - `⁅σ, x₀⁆`, `⁅x₀, x₁⁆`, `⁅x₀, U⁆`,
`⁅x₀, V⁆` - are recorded in `scripts/w56_widen/results/widen_gens.txt` together with all fifty
triple commutators; nothing below depends on them.)

`selLamThreePlus_not_commP_zero_handleV` is the separation: at the binder point
`(A, …, S) = (0, 2, 0, 2, 0, 2, 1, 1)` with halves `(1, 3, 0, 1)` all four parity rows hold and
`⁅σ, V⁆` has `(h, i) = (4, 0)`, which is **not** in the `selLamThreePlus` span there - that span
is `{(0, 0), (4, 6), (0, 4), (4, 2)}`.  So the committed lattice does not contain the honest
object, the caveat `GradedObstructionPlus` recorded was real, and §4 is what retires it.

(The point is not on the live locus: measurement says that where the fourteen pairings are even
and the bit is odd, all `66` census generators do land in the span.  See the Honest scope.) -/

section Separation

variable {h : ℕ} {j : Fin h} {A B C D E F T S P Q R : gr3R}

/-- ⭐ **The `σ`-`U` commutator of the witness frame**: the `Λ₅`-generator `(−A, C, 0)` on the
class-two columns, with class-three data `(−A·C, 0)` and no class-four part. -/
theorem selLiftWit_commP_zero_handleU :
    commP (selLiftWit h j A B C D E F T S P Q R 0)
        (selLiftWit h j A B C D E F T S P Q R (sqHandleIdxU j))
      = ⟨0, 0, 0, 0, -A, C, 0, -(A * C), 0, 0⟩ := by
  rw [selLiftWit_zero, selLiftWit_handleU]
  ext <;> simp only [commP, SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d, SqU5.mul_e,
    SqU5.mul_f, SqU5.mul_g, SqU5.mul_h, SqU5.mul_i, SqU5.mul_j, SqU5.inv_a, SqU5.inv_b,
    SqU5.inv_c, SqU5.inv_d, SqU5.inv_e, SqU5.inv_f, SqU5.inv_g, SqU5.inv_h, SqU5.inv_i,
    SqU5.inv_j] <;> ring

/-- ⭐ **The `σ`-`V` commutator**: the `Λ₅`-generator `(−B, D, 0)`, with `(h, i) = (−B·D, 0)`. -/
theorem selLiftWit_commP_zero_handleV :
    commP (selLiftWit h j A B C D E F T S P Q R 0)
        (selLiftWit h j A B C D E F T S P Q R (sqHandleIdxV j))
      = ⟨0, 0, 0, 0, -B, D, 0, -(B * D), 0, 0⟩ := by
  rw [selLiftWit_zero, selLiftWit_handleV]
  ext <;> simp only [commP, SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d, SqU5.mul_e,
    SqU5.mul_f, SqU5.mul_g, SqU5.mul_h, SqU5.mul_i, SqU5.mul_j, SqU5.inv_a, SqU5.inv_b,
    SqU5.inv_c, SqU5.inv_d, SqU5.inv_e, SqU5.inv_f, SqU5.inv_g, SqU5.inv_h, SqU5.inv_i,
    SqU5.inv_j] <;> ring

/-- ⭐ **The handle commutator**: `γ₂`-shaped with `g`-column `C·F − D·E`, the `hg`-row's own
expression, and class-three data `(B·C·(S + T), −C·F·T)`. -/
theorem selLiftWit_commP_handleU_handleV :
    commP (selLiftWit h j A B C D E F T S P Q R (sqHandleIdxU j))
        (selLiftWit h j A B C D E F T S P Q R (sqHandleIdxV j))
      = ⟨0, 0, 0, 0, 0, 0, C * F - D * E, B * C * S + B * C * T, -(C * F * T),
          A * C * F * T + B * C * F * S + B * C * F * T - B * D * E * S⟩ := by
  rw [selLiftWit_handleU, selLiftWit_handleV]
  ext <;> simp only [commP, SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d, SqU5.mul_e,
    SqU5.mul_f, SqU5.mul_g, SqU5.mul_h, SqU5.mul_i, SqU5.mul_j, SqU5.inv_a, SqU5.inv_b,
    SqU5.inv_c, SqU5.inv_d, SqU5.inv_e, SqU5.inv_f, SqU5.inv_g, SqU5.inv_h, SqU5.inv_i,
    SqU5.inv_j] <;> ring

/-- A subgroup contains the commutator of any two of its elements. -/
private theorem commP_mem_of_mem {G : Type} [Group G] {K : Subgroup G} {p q : G}
    (hp : p ∈ K) (hq : q ∈ K) : commP p q ∈ K :=
  mul_mem (mul_mem (mul_mem (inv_mem hp) (inv_mem hq)) hp) hq

/-- **Every commutator of two elements of the marking's image is an honest `γ₂`-level
dressing**: the general membership, from which the census's whole generating set follows. -/
theorem commP_mem_selGaTwoIm {p q : SqU5 gr3R}
    (hp : p ∈ Subgroup.closure (Set.range (selLiftWit h j A B C D E F T S P Q R)))
    (hq : q ∈ Subgroup.closure (Set.range (selLiftWit h j A B C D E F T S P Q R))) :
    commP p q ∈ selGaTwoIm h j A B C D E F T S P Q R :=
  Subgroup.mem_sup_left (Subgroup.subset_closure ⟨p, hp, q, hq, rfl⟩)

/-- Each of the **ten frame-slot commutators** is one. -/
theorem commP_selLiftWit_mem_selGaTwoIm (i k : Fin (sqRank h)) :
    commP (selLiftWit h j A B C D E F T S P Q R i)
        (selLiftWit h j A B C D E F T S P Q R k)
      ∈ selGaTwoIm h j A B C D E F T S P Q R :=
  commP_mem_selGaTwoIm (Subgroup.subset_closure ⟨i, rfl⟩) (Subgroup.subset_closure ⟨k, rfl⟩)

/-- Each of the **fifty triple commutators** is one. -/
theorem commP_commP_selLiftWit_mem_selGaTwoIm (i k l : Fin (sqRank h)) :
    commP (commP (selLiftWit h j A B C D E F T S P Q R i)
        (selLiftWit h j A B C D E F T S P Q R k)) (selLiftWit h j A B C D E F T S P Q R l)
      ∈ selGaTwoIm h j A B C D E F T S P Q R :=
  commP_mem_selGaTwoIm
    (commP_mem_of_mem (Subgroup.subset_closure ⟨i, rfl⟩)
      (Subgroup.subset_closure ⟨k, rfl⟩))
    (Subgroup.subset_closure ⟨l, rfl⟩)

/-- The **`x₁`-square** is one… -/
theorem selLiftWit_two_sq_mem_selGaTwoIm :
    selLiftWit h j A B C D E F T S P Q R 2 * selLiftWit h j A B C D E F T S P Q R 2
      ∈ selGaTwoIm h j A B C D E F T S P Q R :=
  Subgroup.mem_sup_right (Subgroup.subset_closure rfl)

/-- …and so are its **five commutators** with the frame slots.  With the three previous
lemmas this is the wave-54 census's whole generating set, inside `selGaTwoIm`. -/
theorem commP_selLiftWit_two_sq_mem_selGaTwoIm (l : Fin (sqRank h)) :
    commP (selLiftWit h j A B C D E F T S P Q R 2 * selLiftWit h j A B C D E F T S P Q R 2)
        (selLiftWit h j A B C D E F T S P Q R l)
      ∈ selGaTwoIm h j A B C D E F T S P Q R :=
  commP_mem_selGaTwoIm
    (mul_mem (Subgroup.subset_closure ⟨2, rfl⟩) (Subgroup.subset_closure ⟨2, rfl⟩))
    (Subgroup.subset_closure ⟨l, rfl⟩)

/-- The separating binder point satisfies all four parity rows, at halves `(1, 3, 0, 1)`. -/
theorem selLamThreePlus_sep_rows :
    (2 * (1 : gr3R) + (0 * 1 - 2 * 1) = 0) ∧ (2 * (3 : gr3R) + (1 * 2 - 1 * 0) = 0)
      ∧ (2 * (0 : gr3R) + (0 * 2 - 2 * 0) = 0) ∧ (2 * (1 : gr3R) + (0 * 1 - 2 * 1) = 0) := by
  decide

/-- The `σ`-`V` commutator there is the `γ₃`-element `(h, i) = (4, 0)`. -/
theorem selLiftWit_commP_zero_handleV_sep :
    commP (selLiftWit 1 0 0 2 0 2 0 2 1 1 1 3 0 0)
        (selLiftWit 1 0 0 2 0 2 0 2 1 1 1 3 0 (sqHandleIdxV 0))
      = (⟨0, 0, 0, 0, 6, 2, 0, 4, 0, 0⟩ : SqU5 gr3R) := by decide

/-- ⭐⭐ **The committed lattice does not contain the honest object.**  At the binder point
`(A, …, S) = (0, 2, 0, 2, 0, 2, 1, 1)` with halves `(P, Q, R, W₂) = (1, 3, 0, 1)`, where all
four parity rows hold, the `(h, i)`-data `(4, 0)` of the honest `γ₂(im Φ)`-element `⁅σ, V⁆` is
**not** `selLamThreePlus`-achievable: doubling the `i`-row kills every generator except `t₃`
and leaves `4·t₃ = 0`, while the `h`-row forces `4·t₃ = 4`.

So `selLamThreePlus ⊉ γ₂(im Φ)`, `GradedObstructionPlus`'s scope caveat was not vacuous, and
`sqRelWord_selGaTwoIm_ne_one` is what closes it. -/
theorem selLamThreePlus_not_commP_zero_handleV :
    ¬ selLamThreePlus 0 2 0 2 0 2 1 1 1 3 0 ⟨0, 0, 0, 0, 0, 0, 0, 4, 0, 0⟩ := by
  rintro ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, t₁, t₂, t₃, hh, hi⟩
  have hcon : (0 : gr3R) = 4 := by
    have hh' : (4 : gr3R) = -(r₁ * (2 * (0 * 0))) - r₂ * (0 * 2 + 2 * 0)
        - r₃ * (0 * 2 + 2 * 0) - r₄ * (2 * (2 * 2))
        + 2 * (r₆ * (3 * 0 - 1 * 0)) + 2 * (r₇ * (3 * 2 - 1 * 2))
        + t₂ * (1 * 0 - 3 * 0) + t₃ * (1 * 2 - 3 * 2) := hh
    have hi' : (0 : gr3R) = r₁ * (0 * 0) + r₂ * (2 * 0) + r₃ * (0 * 2) + r₄ * (2 * 2)
        + 2 * (r₅ * 0) + 2 * (r₆ * (0 * 1 - 3 * 0)) + 2 * (r₇ * (0 * 1 - 3 * 2))
        + t₁ * 0 + t₂ * (3 * 0) + t₃ * (3 * 2) := hi
    have h8 : (8 : gr3R) = 0 := by decide
    linear_combination 2 * hi' - hh' + (2 * r₄ - 4 * r₇ + 2 * t₃) * h8
  exact absurd hcon (by decide)

end Separation

/-! ## §6 The residual corner, over the honest object

The corner `GradedObstructionPlus` runs end to end:
`(A, B, C, D, E, F, T, S) = (2, 0, 2, 0, 0, 1, 0, 1)` with halves `(P, Q, R, W₂) = (3, 1, 3, 0)`,
one of the wave-54 note's `33792` residual corners, where the bare witness survives stage 3
with the **odd** residue `5`.  There the committed theorem says no `Λ₂`-dressing kills the
relator; here the same is said of **every** dressing drawn from the honest `γ₂(im Φ)`, with
four hypotheses. -/

/-- ⭐⭐ **The payoff at the residual corner**: no five-slot dressing with every slot in the
honest `γ₂(im Φ)` kills the relator.  Every hypothesis by `decide`. -/
example {z : Fin (sqRank 1) → SqU5 gr3R}
    (hz : ∀ i, z i ∈ selGaTwoIm 1 0 2 0 2 0 0 1 0 1 3 1 3) :
    sqRelWord (conFourDress (selLiftWit 1 0 2 0 2 0 0 1 0 1 3 1 3) z) ≠ 1 :=
  sqRelWord_selGaTwoIm_ne_one (W2 := 0) (res := 5) hz (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The four hypotheses really are the four pairings, at that corner: `R·B = 0`,
`(P·D − Q·B)·F − Q·F·B = 0`, `A·R = 6` and `A·Q·E − E·(P·C − Q·A) = 0`, all even. -/
example : ((3 : gr3R) * 0 = 0) ∧ (((3 : gr3R) * 0 - 1 * 0) * 1 - (1 * 1) * 0 = 0)
    ∧ ((2 : gr3R) * 3 = 6) ∧ ((2 : gr3R) * (1 * 0) - 0 * (3 * 2 - 1 * 2) = 0) := by decide

/-- The `σ`-`U` commutator there is an honest dressing with `(h, i) = (4, 0)`, and the
`x₁`-square is one with `(h, i) = (4, 0)` as well: two members of `selGaTwoIm` outside the
committed `Λ₃`. -/
example : commP (selLiftWit 1 0 2 0 2 0 0 1 0 1 3 1 3 0)
      (selLiftWit 1 0 2 0 2 0 0 1 0 1 3 1 3 (sqHandleIdxU 0))
      = (⟨0, 0, 0, 0, 6, 2, 0, 4, 0, 0⟩ : SqU5 gr3R) := by decide

/-! ## §7 Axiom pins

Committed prints for every public declaration of this file: all **std-3** (`propext`,
`Classical.choice`, `Quot.sound`) or a subset; no census axiom is reachable.  Every `decide` is
on `ZMod 8`, `ZMod 2`, `SqU5 (ZMod 8)` or tuples over them. -/

section AxiomPins

#print axioms selLiftWit_ab_even_of_odd
#print axioms selFrameSub
#print axioms mem_selFrameSub
#print axioms selWideSub
#print axioms mem_selWideSub
#print axioms commP_mem_selWideSub
#print axioms selLiftWit_mem_selFrameSub
#print axioms selLiftWit_closure_le_selFrameSub
#print axioms selGaTwoIm
#print axioms selGaTwoIm_le_selWideSub
#print axioms sqRelWord_selGaTwoIm_ne_one
#print axioms sqRelWord_selGaTwoIm_ne_one_fourteen
#print axioms selLiftWit_commP_zero_handleU
#print axioms selLiftWit_commP_zero_handleV
#print axioms selLiftWit_commP_handleU_handleV
#print axioms commP_mem_selGaTwoIm
#print axioms commP_selLiftWit_mem_selGaTwoIm
#print axioms commP_commP_selLiftWit_mem_selGaTwoIm
#print axioms selLiftWit_two_sq_mem_selGaTwoIm
#print axioms commP_selLiftWit_two_sq_mem_selGaTwoIm
#print axioms selLamThreePlus_sep_rows
#print axioms selLiftWit_commP_zero_handleV_sep
#print axioms selLamThreePlus_not_commP_zero_handleV

end AxiomPins

end SqCore

end Dyadic

end GQ2

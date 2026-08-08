/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenModel

/-!
# W51-EV3F1, part 1: the even literal shift word and the raw span

Ticket **EV-3f** of `docs/dyadic/ev4b-stage-abstraction.md` §4 (the even stage climb), span
half.  The chain map this file sits in is recorded in `docs/dyadic/w51-ev3f-seam.md`; the
short version is that the committed L template splits the material of
`GammaLSylowPreimageFieldLabuteStageHandles.lean` into a character-free *literal
factorization* block (that file's lines 31-415) and a *sharp-neutral* block (416-1293), and
that only the first is needed below `RawSpan`.  This file re-derives the first block at the
even words and then clones `GammaLSylowPreimageFieldLabuteRawSpan.lean`.

## What is genuinely new here

The crossed-derivation word does **not** clone.  For the L relator the shift is the
committed `dbarWordR2 s x y w = w₂² · [w₂,y] · [w₀,x] · [w₁,s]`: the diagonal square sits on
coordinate `2` and its bracket partner is that same letter.  At the even cores

`nWord α a b c d = a ^ (2 + 2 ^ α) · [a,b] · [c,d]`,
`mWord α a b c d = a ^ 2 · [a,b] · c ^ (2 ^ α) · [c,d]`

the diagonal square moves to coordinate `0` and acquires the *product* partner
`base 0 · base 1`, while coordinates `2,3` are cross-paired.  Both even relators have the
**same** crossed derivation once `2 ≤ α` (§3), so the "M twin" of the ticket is one word
datum substituted for another rather than a second development.

The mechanism is §1: for a depth-`k-1` correction `p`, the element `p² · [p,x]` is central of
exponent two, and `(x · p) ^ (2 * t) = x ^ (2 * t) · (p² · [p,x]) ^ t`.  So an even exponent
`2 * t` contributes the diagonal atom exactly when `t` is **odd**.  The three exponents of
the two even cores give

| exponent | `t` | `t` odd? (at `2 ≤ α`) | contribution |
|---|---|---|---|
| `2` (M's first letter) | `1` | yes | `p² · [p,a]` |
| `2 + 2 ^ α` (N's first letter) | `1 + 2 ^ (α-1)` | yes | `p² · [p,a]` |
| `2 ^ α` (M's third letter) | `2 ^ (α-1)` | no | trivial |

At `α = 1` the middle row flips parity (`t = 2`) and the N diagonal atom disappears
altogether, which is the machine-level form of the board's "at `α = 1` the mod-2 quadratic
initial form dies".  So `2 ≤ α` is load-bearing, not conventional.

## Contents

* §1 the central power expansion `evenRawPow_two_mul` and its two parity corollaries.
* §2 the handle block `evenRawHandleDbarWord` (`_mem_zLayer`, `_one`, `_mul`) and the handle
  factorization, cloned from the committed `sqHandleDbarWord` material at
  `MarkedCore.handleIdxU/V`.
* §3 the even crossed-derivation word `evenRawDbarWord` and the two literal factorizations
  `evenRawStageShift_n` / `evenRawStageShift_m`.
* §4 the raw depth corrections, their shift homomorphism, and the five exact coordinate rows.
* §5 the raw shift span, the pure-square supply, and `evenRawShiftSpan_eq_zLayer`.
* §6 the `Tuple`-level bridge to the generic `rawDefectReachable`.
* §7 axiom pins.

## The `α` hypothesis, per declaration

§1 and §2 are `α`-free.  §3 onwards is stated at **`2 ≤ α`**, which is the lane's standing
assumption and is genuinely consumed (see above).  Nothing here weakens to `1 ≤ α`: the
coordinate-`0` row is false at `α = 1`.
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2
open GQ2.Roe.Labute

/-! ## §1 Central power expansion for a depth correction

The single arithmetic engine of the file.  Nothing here mentions a word. -/

section Power

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {k : ℕ}

/-- The commutator swap in the repo's convention `commP p x = p⁻¹ x⁻¹ p x`: moving `p` past
`x` costs exactly one bracket.  A group identity, no hypotheses. -/
theorem evenRawSwap {H : Type*} [Group H] (p x : H) : p * x = x * p * commP p x := by
  simp only [commP]
  group

/-- **The diagonal atom of a depth correction**: `p² · [p,x]`, the element that an
exponent-two step of the relator contributes.  It is central of exponent two, which is what
makes the whole span calculus linear. -/
theorem evenRawDiagonalAtom_mem_zLayer (k : ℕ) (hk : 3 ≤ k)
    {p : levelQuot G (k + 1)} (hp : p ∈ lambdaImage G (k - 1) (k + 1))
    (x : levelQuot G (k + 1)) : p ^ 2 * commP p x ∈ zLayer G k :=
  Subgroup.mul_mem _ (sq_mem_zLayer k hk hp) (commP_mem_zLayer k hk hp x)

/-- **The exponent-two step**: modifying `x` by a depth-`k-1` correction `p` changes `x ^ 2`
by the diagonal atom `p² · [p,x]`.  This is the even analogue of the square slot of
`dbarWordR2`, and the only place a square enters the even shift word. -/
theorem evenRawSq_mul (k : ℕ) (hk : 3 ≤ k)
    {p : levelQuot G (k + 1)} (hp : p ∈ lambdaImage G (k - 1) (k + 1))
    (x : levelQuot G (k + 1)) :
    (x * p) ^ 2 = x ^ 2 * (p ^ 2 * commP p x) := by
  have hc : commP p x ∈ zLayer G k := commP_mem_zLayer k hk hp x
  calc
    (x * p) ^ 2 = x * (p * x) * p := by rw [pow_two]; group
    _ = x * (x * p * commP p x) * p := by rw [evenRawSwap p x]
    _ = x ^ 2 * p * (commP p x * p) := by rw [pow_two]; group
    _ = x ^ 2 * p * (p * commP p x) := by rw [(zLayer_commute hc p).eq]
    _ = x ^ 2 * (p ^ 2 * commP p x) := by rw [pow_two p]; group

/-- **The even power expansion.**  For an even exponent `2 * t`, a depth-`k-1` modification
multiplies the power by the `t`-th power of the diagonal atom.  Proved by induction on `t`
from `evenRawSq_mul`; the atom is central, so it collects at the right. -/
theorem evenRawPow_two_mul (k : ℕ) (hk : 3 ≤ k)
    {p : levelQuot G (k + 1)} (hp : p ∈ lambdaImage G (k - 1) (k + 1))
    (x : levelQuot G (k + 1)) (t : ℕ) :
    (x * p) ^ (2 * t) = x ^ (2 * t) * (p ^ 2 * commP p x) ^ t := by
  have hZ : p ^ 2 * commP p x ∈ zLayer G k := evenRawDiagonalAtom_mem_zLayer k hk hp x
  induction t with
  | zero => simp
  | succ t ih =>
      rw [show 2 * (t + 1) = 2 * t + 2 by ring, pow_add (x * p) (2 * t) 2, ih,
        evenRawSq_mul k hk hp x, pow_add x (2 * t) 2,
        pow_succ (p ^ 2 * commP p x) t,
        mul_assoc (x ^ (2 * t)), mul_assoc (x ^ (2 * t))]
      congr 1
      rw [← mul_assoc, ((zLayer_commute hZ (x ^ 2)).pow_left t).eq, mul_assoc]

/-- A central involution is unchanged by an odd power. -/
theorem evenRawZLayer_pow_odd {z : levelQuot G (k + 1)} (hz : z ∈ zLayer G k)
    {t : ℕ} (ht : Odd t) : z ^ t = z := by
  obtain ⟨s, rfl⟩ := ht
  rw [pow_add, pow_mul, zLayer_sq G hz, one_pow, one_mul, pow_one]

/-- A central involution is killed by an even power. -/
theorem evenRawZLayer_pow_even {z : levelQuot G (k + 1)} (hz : z ∈ zLayer G k)
    {t : ℕ} (ht : Even t) : z ^ t = 1 := by
  obtain ⟨s, rfl⟩ := ht
  rw [show s + s = 2 * s by ring, pow_mul, zLayer_sq G hz, one_pow]

/-- **Odd half: the diagonal atom survives.**  The case of the exponents `2` and `2 + 2 ^ α`
(the latter at `2 ≤ α`). -/
theorem evenRawPow_of_odd_half (k : ℕ) (hk : 3 ≤ k)
    {p : levelQuot G (k + 1)} (hp : p ∈ lambdaImage G (k - 1) (k + 1))
    (x : levelQuot G (k + 1)) {t : ℕ} (ht : Odd t) :
    (x * p) ^ (2 * t) = x ^ (2 * t) * (p ^ 2 * commP p x) := by
  rw [evenRawPow_two_mul k hk hp x t,
    evenRawZLayer_pow_odd (evenRawDiagonalAtom_mem_zLayer k hk hp x) ht]

/-- **Even half: nothing survives.**  The case of the exponent `2 ^ α` at `2 ≤ α`, which is
why `mWord`'s third letter contributes no row to the even shift word. -/
theorem evenRawPow_of_even_half (k : ℕ) (hk : 3 ≤ k)
    {p : levelQuot G (k + 1)} (hp : p ∈ lambdaImage G (k - 1) (k + 1))
    (x : levelQuot G (k + 1)) {t : ℕ} (ht : Even t) :
    (x * p) ^ (2 * t) = x ^ (2 * t) := by
  rw [evenRawPow_two_mul k hk hp x t,
    evenRawZLayer_pow_even (evenRawDiagonalAtom_mem_zLayer k hk hp x) ht, mul_one]

end Power

/-! ### The three exponent parities

The arithmetic separating the even lane from the L lane, isolated so the word computations of
§3 read off a single `rcases`. -/

/-- `2 + 2 ^ α = 2 * (1 + 2 ^ (α - 1))` with an **odd** half, for `2 ≤ α`. -/
theorem evenRawNExp_odd_half {α : ℕ} (hα : 2 ≤ α) :
    ∃ t : ℕ, Odd t ∧ 2 + 2 ^ α = 2 * t := by
  obtain ⟨β, rfl⟩ : ∃ β, α = β + 2 := ⟨α - 2, by omega⟩
  exact ⟨1 + 2 * 2 ^ β, ⟨2 ^ β, by ring⟩, by rw [pow_add]; ring⟩

/-- `2 ^ α = 2 * 2 ^ (α - 1)` with an **even** half, for `2 ≤ α`. -/
theorem evenRawMExp_even_half {α : ℕ} (hα : 2 ≤ α) :
    ∃ t : ℕ, Even t ∧ 2 ^ α = 2 * t := by
  obtain ⟨β, rfl⟩ : ∃ β, α = β + 2 := ⟨α - 2, by omega⟩
  exact ⟨2 * 2 ^ β, ⟨2 ^ β, by ring⟩, by rw [pow_add]; ring⟩

/-- The exponent `2` has the odd half `1`; recorded for uniformity with the other two. -/
theorem evenRawTwoExp_odd_half : ∃ t : ℕ, Odd t ∧ (2 : ℕ) = 2 * t :=
  ⟨1, odd_one, by ring⟩

end

end GQ2.Dyadic.StageGeneric

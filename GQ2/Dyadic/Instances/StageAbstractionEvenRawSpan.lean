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

/-! ## §2 The handle block

A port of the committed `sqHandleDbarWord` material
(`GammaLSylowPreimageFieldLabuteStageHandles.lean` lines 31-364) from `SqCore.sqHandleIdxU/V`
at rank `SqCore.sqRank h` to `MarkedCore.handleIdxU/V` at rank `MarkedCore.coreRank h`.  The
statements are word-generic (they mention only `commP`, `lambdaImage` and
`MarkedCore.handleWord`), but the committed file is not an ancestor of the even lane and two
of the list helpers are `private` there, so the block is re-derived rather than imported.
Per `docs/dyadic/w51-ev3f-seam.md` §2 this block belongs to the span half; the assembly half
consumes it and must not re-derive it. -/

section Handles

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {h k : ℕ}

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Every commutator in a lower two-central quotient lies in the image of `λ₂`. -/
theorem evenRawCommP_mem_lambdaImage_two (m : ℕ) (x y : levelQuot G m) :
    commP x y ∈ lambdaImage G 2 m := by
  have hx : x ∈ lambdaImage G 1 m := by rw [lambdaImage_one_eq_top]; trivial
  have hy : y ∈ lambdaImage G 1 m := by rw [lambdaImage_one_eq_top]; trivial
  exact commP_mem_lambdaImage_add hx hy

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Conjugation by a depth-`k-1` element fixes everything coming from `λ₂`. -/
theorem evenRawConj_lambdaImage_two (k : ℕ) (hk : 3 ≤ k) {c v : levelQuot G (k + 1)}
    (hc : c ∈ lambdaImage G 2 (k + 1)) (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    v⁻¹ * c * v = c := by
  apply conj_eq_self_of_commP_eq_one
  have hmem := commP_mem_lambdaImage_add hc hv
  rw [show 2 + (k - 1) = k + 1 by omega, lambdaImage_self] at hmem
  simpa using hmem

/-- **The handle-pair expansion**: a simultaneous depth correction of a hyperbolic handle
linearizes into its two bracket atoms.  Both atoms are central involutions, which is what
removes the apparent inverse in the first one. -/
theorem evenRawHandlePair_mul (k : ℕ) (hk : 3 ≤ k) (u v : levelQuot G (k + 1))
    {p q : levelQuot G (k + 1)} (hp : p ∈ lambdaImage G (k - 1) (k + 1))
    (hq : q ∈ lambdaImage G (k - 1) (k + 1)) :
    commP (u * p) (v * q) = commP u v * (commP q u * commP p v) := by
  have hqu : commP q u ∈ zLayer G k := commP_mem_zLayer k hk hq u
  have hpu : commP p v ∈ zLayer G k := commP_mem_zLayer k hk hp v
  have huq : commP u q = commP q u := by
    calc
      commP u q = (commP q u)⁻¹ := by simp only [commP]; group
      _ = commP q u := zLayer_inv_self hqu
  have huv : commP u v ∈ lambdaImage G 2 (k + 1) :=
    evenRawCommP_mem_lambdaImage_two (k + 1) u v
  have huq2 : commP u q ∈ lambdaImage G 2 (k + 1) :=
    lambdaImage_le_of_le (by omega) (huq ▸ hqu)
  have hconjQUV : q⁻¹ * commP u v * q = commP u v :=
    evenRawConj_lambdaImage_two k hk huv hq
  have hconjQPV : q⁻¹ * commP p v * q = commP p v := by
    calc
      q⁻¹ * commP p v * q = q⁻¹ * (commP p v * q) := by group
      _ = q⁻¹ * (q * commP p v) := by rw [(zLayer_commute hpu q).eq]
      _ = commP p v := by group
  have hpq : commP p q = 1 :=
    commP_eq_one_of_mul_comm (mul_comm_lambdaImage k hk hp hq)
  have hprod : commP u q * commP u v ∈ lambdaImage G 2 (k + 1) :=
    Subgroup.mul_mem _ huq2 huv
  have hconjP : p⁻¹ * (commP u q * commP u v) * p = commP u q * commP u v :=
    evenRawConj_lambdaImage_two k hk hprod hp
  rw [commP_mul_left, commP_mul_right, commP_mul_right, hconjQUV, hpq, one_mul,
    hconjQPV, hconjP, huq, (zLayer_commute hqu (commP u v)).eq]
  group

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- One-coordinate linearity of the bracket in a depth-`k-1` slot. -/
theorem evenRawCommP_mul_left_of_depth (k : ℕ) (hk : 3 ≤ k)
    {p p' u : levelQuot G (k + 1)} (hp : p ∈ lambdaImage G (k - 1) (k + 1)) :
    commP (p * p') u = commP p u * commP p' u := by
  rw [commP_mul_left, conj_eq_self_of_commP_eq_one
    (commP_eq_one_of_mul_comm (zLayer_commute (commP_mem_zLayer k hk hp u) p').eq)]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The linearized contribution of one handle pair is multiplicative in the correction. -/
theorem evenRawHandlePairDbar_mul (k : ℕ) (hk : 3 ≤ k) (u v : levelQuot G (k + 1))
    {p q p' q' : levelQuot G (k + 1)} (hp : p ∈ lambdaImage G (k - 1) (k + 1))
    (hq : q ∈ lambdaImage G (k - 1) (k + 1))
    (_hp' : p' ∈ lambdaImage G (k - 1) (k + 1))
    (hq' : q' ∈ lambdaImage G (k - 1) (k + 1)) :
    commP (q * q') u * commP (p * p') v =
      commP q u * commP p v * (commP q' u * commP p' v) := by
  rw [evenRawCommP_mul_left_of_depth k hk hq, evenRawCommP_mul_left_of_depth k hk hp]
  have hq'u : commP q' u ∈ zLayer G k := commP_mem_zLayer k hk hq' u
  calc
    commP q u * commP q' u * (commP p v * commP p' v) =
        commP q u * (commP q' u * commP p v) * commP p' v := by group
    _ = commP q u * (commP p v * commP q' u) * commP p' v := by
      rw [(zLayer_commute hq'u (commP p v)).eq]
    _ = commP q u * commP p v * (commP q' u * commP p' v) := by group

private theorem evenRaw_list_prod_mul_of_right_central
    {H Ι : Type*} [Group H] (l : List Ι) (a d : Ι → H) (hd : ∀ i t, d i * t = t * d i) :
    (l.map fun i ↦ a i * d i).prod = (l.map a).prod * (l.map d).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, ih]
      calc
        a i * d i * ((List.map a l).prod * (List.map d l).prod) =
            a i * (d i * (List.map a l).prod) * (List.map d l).prod := by group
        _ = a i * ((List.map a l).prod * d i) * (List.map d l).prod := by rw [hd i]
        _ = a i * (List.map a l).prod * (d i * (List.map d l).prod) := by group

private theorem evenRaw_list_map_prod_eq_single_of_nodup
    {H Ι : Type*} [Monoid H] (l : List Ι) (j : Ι) (f : Ι → H)
    (hj : j ∈ l) (hnodup : l.Nodup) (hf : ∀ i ∈ l, i ≠ j → f i = 1) :
    (l.map f).prod = f j := by
  induction l with
  | nil => simp at hj
  | cons a l ih =>
      have hnd := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hj with haj | hj
      · subst a
        have htail : (l.map f).prod = 1 := by
          apply List.prod_eq_one
          intro x hx
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
          exact hf b (List.mem_cons_of_mem _ hb) (fun hbj ↦ hnd.1 (hbj ▸ hb))
        simp only [List.map_cons, List.prod_cons, htail, mul_one]
      · have haj : a ≠ j := fun haj ↦ hnd.1 (haj ▸ hj)
        have hfa : f a = 1 := hf a (by simp) haj
        have htail := ih hj hnd.2 (fun i hi hij ↦ hf i (List.mem_cons_of_mem _ hi) hij)
        simp only [List.map_cons, List.prod_cons, hfa, one_mul, htail]

/-- **The linearized contribution of every hyperbolic handle** at the even index families.
For the `j`-th pair the `V`-correction brackets with the old `U`-slot and conversely. -/
def evenRawHandleDbarWord (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) :
    levelQuot G (k + 1) :=
  ((List.finRange h).map fun j ↦
    commP (correction (MarkedCore.handleIdxV j)) (base (MarkedCore.handleIdxU j)) *
      commP (correction (MarkedCore.handleIdxU j)) (base (MarkedCore.handleIdxV j))).prod

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The complete handle contribution lands in the central involutive layer. -/
theorem evenRawHandleDbarWord_mem_zLayer (h k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    evenRawHandleDbarWord base correction ∈ zLayer G k := by
  rw [evenRawHandleDbarWord]
  apply Subgroup.list_prod_mem
  intro z hz
  simp only [List.mem_map] at hz
  obtain ⟨j, _hj, rfl⟩ := hz
  exact Subgroup.mul_mem _
    (commP_mem_zLayer k hk (hdepth (MarkedCore.handleIdxV j)) _)
    (commP_mem_zLayer k hk (hdepth (MarkedCore.handleIdxU j)) _)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The trivial correction has trivial handle shift. -/
theorem evenRawHandleDbarWord_one
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) :
    evenRawHandleDbarWord base (fun _ ↦ 1) = 1 := by
  simp [evenRawHandleDbarWord, commP]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The handle block is multiplicative in the depth correction, so every handle pair
contributes a genuine linear coordinate of the central graded layer. -/
theorem evenRawHandleDbarWord_mul (h k : ℕ) (hk : 3 ≤ k)
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    {correction correction' : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)}
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1))
    (hdepth' : ∀ i, correction' i ∈ lambdaImage G (k - 1) (k + 1)) :
    evenRawHandleDbarWord base (fun i ↦ correction i * correction' i) =
      evenRawHandleDbarWord base correction * evenRawHandleDbarWord base correction' := by
  rw [evenRawHandleDbarWord, evenRawHandleDbarWord, evenRawHandleDbarWord]
  simp_rw [evenRawHandlePairDbar_mul k hk _ _
    (hdepth (MarkedCore.handleIdxU _)) (hdepth (MarkedCore.handleIdxV _))
    (hdepth' (MarkedCore.handleIdxU _)) (hdepth' (MarkedCore.handleIdxV _))]
  apply evenRaw_list_prod_mul_of_right_central
  intro j t
  have hz : commP (correction' (MarkedCore.handleIdxV j)) (base (MarkedCore.handleIdxU j)) *
      commP (correction' (MarkedCore.handleIdxU j)) (base (MarkedCore.handleIdxV j)) ∈
        zLayer G k :=
    Subgroup.mul_mem _
      (commP_mem_zLayer k hk (hdepth' (MarkedCore.handleIdxV j)) _)
      (commP_mem_zLayer k hk (hdepth' (MarkedCore.handleIdxU j)) _)
  exact (zLayer_commute hz t).eq

/-- The full handle product factors into its old value and the linearized handle word. -/
theorem evenRawHandleWord_mul_lambdaImage (h k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    MarkedCore.handleWord
        (fun j ↦ base (MarkedCore.handleIdxU j) * correction (MarkedCore.handleIdxU j))
        (fun j ↦ base (MarkedCore.handleIdxV j) * correction (MarkedCore.handleIdxV j)) =
      MarkedCore.handleWord (fun j ↦ base (MarkedCore.handleIdxU j))
          (fun j ↦ base (MarkedCore.handleIdxV j)) *
        evenRawHandleDbarWord base correction := by
  rw [MarkedCore.handleWord, MarkedCore.handleWord, evenRawHandleDbarWord]
  simp_rw [evenRawHandlePair_mul k hk _ _
    (hdepth (MarkedCore.handleIdxU _)) (hdepth (MarkedCore.handleIdxV _))]
  apply evenRaw_list_prod_mul_of_right_central
  intro j t
  have hz : commP (correction (MarkedCore.handleIdxV j)) (base (MarkedCore.handleIdxU j)) *
      commP (correction (MarkedCore.handleIdxU j)) (base (MarkedCore.handleIdxV j)) ∈
        zLayer G k :=
    Subgroup.mul_mem _
      (commP_mem_zLayer k hk (hdepth (MarkedCore.handleIdxV j)) _)
      (commP_mem_zLayer k hk (hdepth (MarkedCore.handleIdxU j)) _)
  exact (zLayer_commute hz t).eq

/-! ### Central regrouping

Two arithmetic-free helpers: a product of pairs whose right members are central splits into
the product of the left members times the product of the right ones.  Everything the shift
word is built from is central, so these two carry all the bookkeeping of §3. -/

private theorem evenRawRegroup₂ {H : Type*} [Group H] (x₁ y₁ x₂ y₂ : H)
    (hy₁ : ∀ t : H, Commute y₁ t) : x₁ * y₁ * (x₂ * y₂) = x₁ * x₂ * (y₁ * y₂) := by
  calc
    x₁ * y₁ * (x₂ * y₂) = x₁ * (y₁ * x₂) * y₂ := by group
    _ = x₁ * (x₂ * y₁) * y₂ := by rw [(hy₁ x₂).eq]
    _ = x₁ * x₂ * (y₁ * y₂) := by group

private theorem evenRawRegroup₃ {H : Type*} [Group H] (x₁ y₁ x₂ y₂ x₃ y₃ : H)
    (hy₁ : ∀ t : H, Commute y₁ t) (hy₂ : ∀ t : H, Commute y₂ t) :
    x₁ * y₁ * (x₂ * y₂) * (x₃ * y₃) = x₁ * x₂ * x₃ * (y₁ * y₂ * y₃) := by
  calc
    x₁ * y₁ * (x₂ * y₂) * (x₃ * y₃) = x₁ * (y₁ * x₂) * y₂ * x₃ * y₃ := by group
    _ = x₁ * (x₂ * y₁) * y₂ * x₃ * y₃ := by rw [(hy₁ x₂).eq]
    _ = x₁ * x₂ * (y₁ * y₂ * x₃) * y₃ := by group
    _ = x₁ * x₂ * (x₃ * (y₁ * y₂)) * y₃ := by rw [((hy₁ x₃).mul_left (hy₂ x₃)).eq]
    _ = x₁ * x₂ * x₃ * (y₁ * y₂ * y₃) := by group

end Handles

/-! ## §3 The even crossed-derivation word

The heart of the file.  `evenRawCoreDbarWord` is written in exactly the order the word
computation produces it, so the factorizations below are assembly plus two central swaps. -/

section Dbar

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {h k : ℕ}

/-- **The core block of the even shift word.**  Three central atoms:

* the *diagonal* atom `w₀² · [w₀, base 0]` from the first letter's even power;
* the pair `[w₁, base 0] · [w₀, base 1]` from the commutator `[base 0, base 1]`;
* the pair `[w₃, base 2] · [w₂, base 3]` from the commutator `[base 2, base 3]`.

Collecting the two occurrences of `w₀` gives the presentation of the seam note: `w₀²` times
the *product* partner `[w₀, base 0 · base 1]` (see `evenRawCoreDbarWord_zero_row`). -/
def evenRawCoreDbarWord
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) :
    levelQuot G (k + 1) :=
  correction 0 ^ 2 * commP (correction 0) (base 0) *
    (commP (correction 1) (base 0) * commP (correction 0) (base 1)) *
    (commP (correction 3) (base 2) * commP (correction 2) (base 3))

/-- **The full even shift word**: the core block times the handle block.  The even analogue
of the committed `sqCoreHandleDbarWord`. -/
def evenRawDbarWord
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) :
    levelQuot G (k + 1) :=
  evenRawCoreDbarWord base correction * evenRawHandleDbarWord base correction

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The core block lands in the central involutive layer. -/
theorem evenRawCoreDbarWord_mem_zLayer (k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    evenRawCoreDbarWord base correction ∈ zLayer G k := by
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _
    (evenRawDiagonalAtom_mem_zLayer k hk (hdepth 0) _) (Subgroup.mul_mem _ ?_ ?_))
    (Subgroup.mul_mem _ ?_ ?_) <;>
  exact commP_mem_zLayer k hk (hdepth _) _

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The full shift word lands in the central involutive layer. -/
theorem evenRawDbarWord_mem_zLayer (h k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    evenRawDbarWord base correction ∈ zLayer G k :=
  Subgroup.mul_mem _ (evenRawCoreDbarWord_mem_zLayer k hk base correction hdepth)
    (evenRawHandleDbarWord_mem_zLayer h k hk base correction hdepth)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The trivial correction has trivial core shift. -/
theorem evenRawCoreDbarWord_one
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) :
    evenRawCoreDbarWord base (fun _ ↦ 1) = 1 := by
  simp [evenRawCoreDbarWord, commP]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The trivial correction has trivial shift. -/
theorem evenRawDbarWord_one
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) :
    evenRawDbarWord base (fun _ ↦ 1) = 1 := by
  rw [evenRawDbarWord, evenRawCoreDbarWord_one, evenRawHandleDbarWord_one, mul_one]

/-- **The core block is multiplicative in the depth correction.**  Each of its three atoms is
separately multiplicative (the diagonal one by `evenRawSq_mul` together with the vanishing of
`[w₀', w₀]` between two depth-`k-1` elements, the other two by one-coordinate linearity), and
all values are central, so the three products regroup. -/
theorem evenRawCoreDbarWord_mul (k : ℕ) (hk : 3 ≤ k)
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    {c c' : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)}
    (hdepth : ∀ i, c i ∈ lambdaImage G (k - 1) (k + 1))
    (hdepth' : ∀ i, c' i ∈ lambdaImage G (k - 1) (k + 1)) :
    evenRawCoreDbarWord base (fun i ↦ c i * c' i) =
      evenRawCoreDbarWord base c * evenRawCoreDbarWord base c' := by
  have hzero : commP (c' 0) (c 0) = 1 :=
    commP_eq_one_of_mul_comm (mul_comm_lambdaImage k hk (hdepth' 0) (hdepth 0))
  have hdiag : (c 0 * c' 0) ^ 2 * (commP (c 0) (base 0) * commP (c' 0) (base 0)) =
      c 0 ^ 2 * commP (c 0) (base 0) * (c' 0 ^ 2 * commP (c' 0) (base 0)) := by
    rw [evenRawSq_mul k hk (hdepth' 0) (c 0), hzero, mul_one]
    exact evenRawRegroup₂ _ _ _ _ (zLayer_commute (sq_mem_zLayer k hk (hdepth' 0)))
  have hpair : ∀ i j : Fin (MarkedCore.coreRank h),
      commP (c i * c' i) (base j) = commP (c i) (base j) * commP (c' i) (base j) :=
    fun i j ↦ evenRawCommP_mul_left_of_depth k hk (hdepth i)
  simp only [evenRawCoreDbarWord, hpair]
  rw [hdiag, evenRawRegroup₂ (commP (c 1) (base 0)) (commP (c' 1) (base 0))
      (commP (c 0) (base 1)) (commP (c' 0) (base 1))
      (zLayer_commute (commP_mem_zLayer k hk (hdepth' 1) _)),
    evenRawRegroup₂ (commP (c 3) (base 2)) (commP (c' 3) (base 2))
      (commP (c 2) (base 3)) (commP (c' 2) (base 3))
      (zLayer_commute (commP_mem_zLayer k hk (hdepth' 3) _))]
  exact evenRawRegroup₃ _ _ _ _ _ _
    (zLayer_commute (evenRawDiagonalAtom_mem_zLayer k hk (hdepth' 0) _))
    (zLayer_commute (Subgroup.mul_mem _ (commP_mem_zLayer k hk (hdepth' 1) _)
      (commP_mem_zLayer k hk (hdepth' 0) _)))

/-- **The full shift word is a homomorphism on depth corrections.**  This is what reduces the
span problem to the images of individual coordinates in §4. -/
theorem evenRawDbarWord_mul (h k : ℕ) (hk : 3 ≤ k)
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    {c c' : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)}
    (hdepth : ∀ i, c i ∈ lambdaImage G (k - 1) (k + 1))
    (hdepth' : ∀ i, c' i ∈ lambdaImage G (k - 1) (k + 1)) :
    evenRawDbarWord base (fun i ↦ c i * c' i) =
      evenRawDbarWord base c * evenRawDbarWord base c' := by
  rw [evenRawDbarWord, evenRawDbarWord, evenRawDbarWord,
    evenRawCoreDbarWord_mul k hk base hdepth hdepth',
    evenRawHandleDbarWord_mul h k hk base hdepth hdepth']
  exact evenRawRegroup₂ _ _ _ _
    (zLayer_commute (evenRawCoreDbarWord_mem_zLayer k hk base c' hdepth'))

end Dbar

end

end GQ2.Dyadic.StageGeneric

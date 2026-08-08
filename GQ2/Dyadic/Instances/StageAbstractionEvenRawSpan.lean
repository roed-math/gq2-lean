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

/-! ### The two core assemblies

Pure group identities: given that `A` and `A * B` are central, the order in which the blocks
of the shift word come out of the computation can be normalised.  `evenRawAssembleN` is for
`nWord` (three blocks), `evenRawAssembleM` for `mWord`, whose third letter contributes an
inert power `Y`. -/

private theorem evenRawAssembleN {H' : Type*} [Group H'] (X P Q A B C : H')
    (hA : ∀ t : H', Commute A t) (hAB : ∀ t : H', Commute (A * B) t) :
    X * A * (P * B) * (Q * C) = X * P * Q * (A * B * C) := by
  calc
    X * A * (P * B) * (Q * C) = X * (A * P) * (B * (Q * C)) := by group
    _ = X * (P * A) * (B * (Q * C)) := by rw [(hA P).eq]
    _ = X * P * (A * B * Q) * C := by group
    _ = X * P * (Q * (A * B)) * C := by rw [(hAB Q).eq]
    _ = X * P * Q * (A * B * C) := by group

private theorem evenRawAssembleM {H' : Type*} [Group H'] (X P Y Q A B C : H')
    (hA : ∀ t : H', Commute A t) (hAB : ∀ t : H', Commute (A * B) t) :
    X * A * (P * B) * Y * (Q * C) = X * P * Y * Q * (A * B * C) := by
  calc
    X * A * (P * B) * Y * (Q * C) = X * (A * P) * (B * (Y * (Q * C))) := by group
    _ = X * (P * A) * (B * (Y * (Q * C))) := by rw [(hA P).eq]
    _ = X * P * (A * B * (Y * Q)) * C := by group
    _ = X * P * (Y * Q * (A * B)) * C := by rw [(hAB (Y * Q)).eq]
    _ = X * P * Y * Q * (A * B * C) := by group

private theorem evenRawShiftAssemble {H' : Type*} [Group H'] (C Hh d D : H')
    (hd : ∀ t : H', Commute d t) : (C * Hh)⁻¹ * (C * d * (Hh * D)) = d * D := by
  calc
    (C * Hh)⁻¹ * (C * d * (Hh * D)) = (C * Hh)⁻¹ * (C * (d * Hh) * D) := by group
    _ = (C * Hh)⁻¹ * (C * (Hh * d) * D) := by rw [(hd Hh).eq]
    _ = d * D := by group

/-! ## §4 The literal factorizations at the two even words

The crux of the ticket.  Both even relators shift by the *same* word `evenRawDbarWord`, and
both statements need `2 ≤ α`: for `N_α` because the exponent `2 + 2 ^ α` must have an odd
half for the diagonal atom to survive, for `M_α` because the exponent `2 ^ α` must have an
even half for its letter to contribute nothing.  At `α = 1` both parities flip. -/

section Factorization

variable {α : ℕ}

/-- **The `N_α` core factorization.**  Requires `2 ≤ α`: at `α = 1` the exponent is `4`, whose
half `2` is even, so the diagonal atom `w₀² · [w₀, base 0]` drops out of the right-hand side
and the statement is false as written. -/
theorem evenRawNWord_mul_lambdaImage (hα : 2 ≤ α) (k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    MarkedCore.nWord α (base 0 * correction 0) (base 1 * correction 1)
        (base 2 * correction 2) (base 3 * correction 3) =
      MarkedCore.nWord α (base 0) (base 1) (base 2) (base 3) *
        evenRawCoreDbarWord base correction := by
  obtain ⟨t, ht, hexp⟩ := evenRawNExp_odd_half hα
  simp only [MarkedCore.nWord, evenRawCoreDbarWord, hexp]
  rw [evenRawPow_of_odd_half k hk (hdepth 0) (base 0) ht,
    evenRawHandlePair_mul k hk (base 0) (base 1) (hdepth 0) (hdepth 1),
    evenRawHandlePair_mul k hk (base 2) (base 3) (hdepth 2) (hdepth 3)]
  exact evenRawAssembleN _ _ _ _ _ _
    (zLayer_commute (evenRawDiagonalAtom_mem_zLayer k hk (hdepth 0) _))
    (zLayer_commute (Subgroup.mul_mem _
      (evenRawDiagonalAtom_mem_zLayer k hk (hdepth 0) _)
      (Subgroup.mul_mem _ (commP_mem_zLayer k hk (hdepth 1) _)
        (commP_mem_zLayer k hk (hdepth 0) _))))

/-- **The `M_α` core factorization.**  Requires `2 ≤ α`: the third letter's exponent `2 ^ α`
has an even half exactly then, so `(base 2 · w₂) ^ (2 ^ α) = base 2 ^ (2 ^ α)` and that letter
contributes no row.  At `α = 1` the exponent is `2` and it would contribute
`w₂² · [w₂, base 2]`. -/
theorem evenRawMWord_mul_lambdaImage (hα : 2 ≤ α) (k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    MarkedCore.mWord α (base 0 * correction 0) (base 1 * correction 1)
        (base 2 * correction 2) (base 3 * correction 3) =
      MarkedCore.mWord α (base 0) (base 1) (base 2) (base 3) *
        evenRawCoreDbarWord base correction := by
  obtain ⟨t, ht, hexp⟩ := evenRawMExp_even_half hα
  simp only [MarkedCore.mWord, evenRawCoreDbarWord, hexp]
  rw [evenRawSq_mul k hk (hdepth 0) (base 0),
    evenRawPow_of_even_half k hk (hdepth 2) (base 2) ht,
    evenRawHandlePair_mul k hk (base 0) (base 1) (hdepth 0) (hdepth 1),
    evenRawHandlePair_mul k hk (base 2) (base 3) (hdepth 2) (hdepth 3)]
  exact evenRawAssembleM _ _ _ _ _ _ _
    (zLayer_commute (evenRawDiagonalAtom_mem_zLayer k hk (hdepth 0) _))
    (zLayer_commute (Subgroup.mul_mem _
      (evenRawDiagonalAtom_mem_zLayer k hk (hdepth 0) _)
      (Subgroup.mul_mem _ (commP_mem_zLayer k hk (hdepth 1) _)
        (commP_mem_zLayer k hk (hdepth 0) _))))

/-- **The `N_α` relator shift is the even crossed-derivation word.**  An equality in
`Q_(k+1)`, not merely in an associated graded quotient: the even analogue of the committed
`stageShift_eq_dbarWordR2_mul_sqHandleDbarWord`.  The word datum's own hypothesis `1 ≤ α` is
a separate argument so that the statement mentions the caller's `nStageWord α h hα₁`
verbatim; the content needs the stronger `2 ≤ α`. -/
theorem evenRawStageShift_n (hα : 2 ≤ α) (hα₁ : 1 ≤ α) (h k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    stageShift (nStageWord α h hα₁) base correction = evenRawDbarWord base correction := by
  show (MarkedCore.nRelWord α base)⁻¹ *
    MarkedCore.nRelWord α (fun i ↦ base i * correction i) = _
  simp only [MarkedCore.nRelWord]
  rw [evenRawNWord_mul_lambdaImage hα k hk base correction hdepth,
    evenRawHandleWord_mul_lambdaImage h k hk base correction hdepth, evenRawDbarWord]
  exact evenRawShiftAssemble _ _ _ _
    (zLayer_commute (evenRawCoreDbarWord_mem_zLayer k hk base correction hdepth))

/-- **The `M_α` relator shift is the same even crossed-derivation word.**  From here on the N
and M branches of the even lane share their entire span calculus. -/
theorem evenRawStageShift_m (hα : 2 ≤ α) (hα₁ : 1 ≤ α) (h k : ℕ) (hk : 3 ≤ k)
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)) :
    stageShift (mStageWord α h hα₁) base correction = evenRawDbarWord base correction := by
  show (MarkedCore.mRelWord α base)⁻¹ *
    MarkedCore.mRelWord α (fun i ↦ base i * correction i) = _
  simp only [MarkedCore.mRelWord]
  rw [evenRawMWord_mul_lambdaImage hα k hk base correction hdepth,
    evenRawHandleWord_mul_lambdaImage h k hk base correction hdepth, evenRawDbarWord]
  exact evenRawShiftAssemble _ _ _ _
    (zLayer_commute (evenRawCoreDbarWord_mem_zLayer k hk base correction hdepth))

end Factorization

end Dbar

/-! ## §5 Raw depth corrections and the raw shift span

The clone of `GammaLSylowPreimageFieldLabuteRawSpan.lean`.  Nothing below mentions a
cyclotomic character: this is the presentation-theoretic half of the climb, and the exact
mismatch with generic two-central tower generation is isolated as
`EvenRawPureSquareSpanSupply`. -/

section RawSpan

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {h k : ℕ}

/-- A depth-`k-1` correction of the even marking, with no character constraint. -/
structure EvenRawDepthCorrection (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (h k : ℕ) where
  /-- The correction, one coordinate per even generator. -/
  correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)
  /-- Every coordinate has depth `k-1`. -/
  depth : ∀ i, correction i ∈ lambdaImage G (k - 1) (k + 1)

@[ext]
theorem EvenRawDepthCorrection.ext {V V' : EvenRawDepthCorrection G h k}
    (H : V.correction = V'.correction) : V = V' := by
  cases V; cases V'; cases H; rfl

/-- The trivial correction. -/
protected noncomputable def EvenRawDepthCorrection.one :
    EvenRawDepthCorrection G h k where
  correction _ := 1
  depth _ := Subgroup.one_mem _

/-- Coordinatewise product of corrections. -/
protected noncomputable def EvenRawDepthCorrection.mul
    (V V' : EvenRawDepthCorrection G h k) : EvenRawDepthCorrection G h k where
  correction i := V.correction i * V'.correction i
  depth i := Subgroup.mul_mem _ (V.depth i) (V'.depth i)

/-- Coordinatewise inverse of a correction. -/
protected noncomputable def EvenRawDepthCorrection.inv
    (V : EvenRawDepthCorrection G h k) : EvenRawDepthCorrection G h k where
  correction i := (V.correction i)⁻¹
  depth i := Subgroup.inv_mem _ (V.depth i)

noncomputable instance : Group (EvenRawDepthCorrection G h k) where
  one := EvenRawDepthCorrection.one
  mul := EvenRawDepthCorrection.mul
  inv := EvenRawDepthCorrection.inv
  mul_assoc V₁ V₂ V₃ := by ext i; exact mul_assoc _ _ _
  one_mul V := by ext i; exact one_mul _
  mul_one V := by ext i; exact mul_one _
  inv_mul_cancel V := by ext i; exact inv_mul_cancel _

@[simp] theorem EvenRawDepthCorrection.one_correction (i : Fin (MarkedCore.coreRank h)) :
    (1 : EvenRawDepthCorrection G h k).correction i = 1 := rfl

@[simp] theorem EvenRawDepthCorrection.mul_correction
    (V V' : EvenRawDepthCorrection G h k) (i : Fin (MarkedCore.coreRank h)) :
    (V * V').correction i = V.correction i * V'.correction i := rfl

/-- A raw correction supported at one generator coordinate. -/
noncomputable def evenRawDepthCoordinateCorrection (i : Fin (MarkedCore.coreRank h))
    (p : lambdaImage G (k - 1) (k + 1)) : EvenRawDepthCorrection G h k where
  correction j := if j = i then p.1 else 1
  depth j := by
    by_cases hji : j = i <;> simp [hji]

@[simp] theorem evenRawDepthCoordinateCorrection_apply
    (i j : Fin (MarkedCore.coreRank h)) (p : lambdaImage G (k - 1) (k + 1)) :
    (evenRawDepthCoordinateCorrection i p : EvenRawDepthCorrection G h k).correction j =
      if j = i then p.1 else 1 := rfl

/-! ### Index disequalities

The even alphabet is `0,1,2,3` for the core and `4+2j, 5+2j` for the `j`-th handle
(`MarkedCore.coreRank h = 4 + 2 * h`), so every disequality below is `omega` on `Fin.val`. -/

private theorem evenRawHandleU_ne_core (j : Fin h) {i : Fin (MarkedCore.coreRank h)}
    (hi : (i : ℕ) < 4) : MarkedCore.handleIdxU j ≠ i := by
  intro hj
  have hv := congrArg Fin.val hj
  rw [MarkedCore.handleIdxU_val] at hv
  omega

private theorem evenRawHandleV_ne_core (j : Fin h) {i : Fin (MarkedCore.coreRank h)}
    (hi : (i : ℕ) < 4) : MarkedCore.handleIdxV j ≠ i := by
  intro hj
  have hv := congrArg Fin.val hj
  rw [MarkedCore.handleIdxV_val] at hv
  omega

private theorem evenRawCore_ne_handleU {i : Fin (MarkedCore.coreRank h)} (hi : (i : ℕ) < 4)
    (j : Fin h) : i ≠ MarkedCore.handleIdxU j :=
  fun hj ↦ evenRawHandleU_ne_core j hi hj.symm

private theorem evenRawCore_ne_handleV {i : Fin (MarkedCore.coreRank h)} (hi : (i : ℕ) < 4)
    (j : Fin h) : i ≠ MarkedCore.handleIdxV j :=
  fun hj ↦ evenRawHandleV_ne_core j hi hj.symm

private theorem evenRawHandleV_ne_handleU (l j : Fin h) :
    MarkedCore.handleIdxV l ≠ (MarkedCore.handleIdxU j : Fin (MarkedCore.coreRank h)) := by
  intro hEq
  have hv := congrArg Fin.val hEq
  rw [MarkedCore.handleIdxV_val, MarkedCore.handleIdxU_val] at hv
  omega

private theorem evenRawHandleU_ne_handleV (l j : Fin h) :
    MarkedCore.handleIdxU l ≠ (MarkedCore.handleIdxV j : Fin (MarkedCore.coreRank h)) :=
  fun hEq ↦ evenRawHandleV_ne_handleU j l hEq.symm

private theorem evenRawHandleU_ne_handleU {l j : Fin h} (hlj : l ≠ j) :
    MarkedCore.handleIdxU l ≠ (MarkedCore.handleIdxU j : Fin (MarkedCore.coreRank h)) := by
  intro hEq
  refine hlj (Fin.ext ?_)
  have hv := congrArg Fin.val hEq
  rw [MarkedCore.handleIdxU_val, MarkedCore.handleIdxU_val] at hv
  omega

private theorem evenRawHandleV_ne_handleV {l j : Fin h} (hlj : l ≠ j) :
    MarkedCore.handleIdxV l ≠ (MarkedCore.handleIdxV j : Fin (MarkedCore.coreRank h)) := by
  intro hEq
  refine hlj (Fin.ext ?_)
  have hv := congrArg Fin.val hEq
  rw [MarkedCore.handleIdxV_val, MarkedCore.handleIdxV_val] at hv
  omega

/-- The four core letters have `Fin.val` equal to `0,1,2,3`; packaged for the `omega` calls
in the disequalities above. -/
private theorem evenRawCoreVal_lt_four :
    (((0 : Fin (MarkedCore.coreRank h)) : ℕ) < 4) ∧ (((1 : Fin (MarkedCore.coreRank h)) : ℕ) < 4)
      ∧ (((2 : Fin (MarkedCore.coreRank h)) : ℕ) < 4)
      ∧ (((3 : Fin (MarkedCore.coreRank h)) : ℕ) < 4) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [MarkedCore.coreVal_zero]; omega
  · rw [MarkedCore.coreVal_one]; omega
  · rw [MarkedCore.coreVal_two]; omega
  · rw [MarkedCore.coreVal_three]; omega

private theorem evenRawCoreIdx_ne {i j : Fin (MarkedCore.coreRank h)}
    (hij : (i : ℕ) ≠ (j : ℕ)) : i ≠ j := fun hh ↦ hij (congrArg Fin.val hh)

private theorem evenRawIdx01 : (0 : Fin (MarkedCore.coreRank h)) ≠ 1 :=
  evenRawCoreIdx_ne (by rw [MarkedCore.coreVal_zero, MarkedCore.coreVal_one]; omega)

private theorem evenRawIdx02 : (0 : Fin (MarkedCore.coreRank h)) ≠ 2 :=
  evenRawCoreIdx_ne (by rw [MarkedCore.coreVal_zero, MarkedCore.coreVal_two]; omega)

private theorem evenRawIdx03 : (0 : Fin (MarkedCore.coreRank h)) ≠ 3 :=
  evenRawCoreIdx_ne (by rw [MarkedCore.coreVal_zero, MarkedCore.coreVal_three]; omega)

private theorem evenRawIdx12 : (1 : Fin (MarkedCore.coreRank h)) ≠ 2 :=
  evenRawCoreIdx_ne (by rw [MarkedCore.coreVal_one, MarkedCore.coreVal_two]; omega)

private theorem evenRawIdx13 : (1 : Fin (MarkedCore.coreRank h)) ≠ 3 :=
  evenRawCoreIdx_ne (by rw [MarkedCore.coreVal_one, MarkedCore.coreVal_three]; omega)

private theorem evenRawIdx23 : (2 : Fin (MarkedCore.coreRank h)) ≠ 3 :=
  evenRawCoreIdx_ne (by rw [MarkedCore.coreVal_two, MarkedCore.coreVal_three]; omega)

/-! ### The literal shift homomorphism -/

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- **The literal even-relator shift on all raw depth corrections.**  A homomorphism into the
central layer by §3; §4 identifies its value with the actual `stageShift` of either even word
datum. -/
noncomputable def evenRawDepthShiftHom
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) (hk : 3 ≤ k) :
    EvenRawDepthCorrection G h k →* zLayer G k where
  toFun V := ⟨evenRawDbarWord base V.correction,
    evenRawDbarWord_mem_zLayer h k hk base V.correction V.depth⟩
  map_one' := Subtype.ext (evenRawDbarWord_one base)
  map_mul' V V' := Subtype.ext (evenRawDbarWord_mul h k hk base V.depth V'.depth)

/-! ### The six exact coordinate rows

Read off from `evenRawCoreDbarWord`.  Note the asymmetry the L template does not have:
coordinate `0` carries the diagonal square *and two* brackets, while coordinate `1` carries a
single bracket against `base 0`.  Coordinates `2,3` are cross-paired, as are the handles. -/

/-- The `x₀`-row (coordinate `0`): the inseparable diagonal `p² · [p, base 0] · [p, base 1]`.
This is the even lane's replacement for the L template's `p² · [p, x₁]`, and the extra
bracket is what forces the additional step in `evenRawBracket_base_mem_shiftSpan`. -/
theorem evenRawDepthShiftHom_zero_apply
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) (hk : 3 ≤ k)
    (p : lambdaImage G (k - 1) (k + 1)) :
    ((evenRawDepthShiftHom base hk)
        (evenRawDepthCoordinateCorrection 0 p)).1 =
      p.1 ^ 2 * commP p.1 (base 0) * commP p.1 (base 1) := by
  have hh : evenRawHandleDbarWord base
      (evenRawDepthCoordinateCorrection (0 : Fin (MarkedCore.coreRank h)) p :
        EvenRawDepthCorrection G h k).correction = 1 := by
    simp [evenRawHandleDbarWord, evenRawHandleU_ne_core _ evenRawCoreVal_lt_four.1,
      evenRawHandleV_ne_core _ evenRawCoreVal_lt_four.1, commP]
  have c0 : (evenRawDepthCoordinateCorrection (0 : Fin (MarkedCore.coreRank h)) p :
      EvenRawDepthCorrection G h k).correction 0 = p.1 := by
    rw [evenRawDepthCoordinateCorrection_apply, if_pos rfl]
  have c1 : (evenRawDepthCoordinateCorrection (0 : Fin (MarkedCore.coreRank h)) p :
      EvenRawDepthCorrection G h k).correction 1 = 1 := by
    rw [evenRawDepthCoordinateCorrection_apply, if_neg evenRawIdx01.symm]
  have c2 : (evenRawDepthCoordinateCorrection (0 : Fin (MarkedCore.coreRank h)) p :
      EvenRawDepthCorrection G h k).correction 2 = 1 := by
    rw [evenRawDepthCoordinateCorrection_apply, if_neg evenRawIdx02.symm]
  have c3 : (evenRawDepthCoordinateCorrection (0 : Fin (MarkedCore.coreRank h)) p :
      EvenRawDepthCorrection G h k).correction 3 = 1 := by
    rw [evenRawDepthCoordinateCorrection_apply, if_neg evenRawIdx03.symm]
  change evenRawDbarWord base _ = _
  rw [evenRawDbarWord, hh, mul_one, evenRawCoreDbarWord, c0, c1, c2, c3]
  simp only [commP]
  group

/-- The `x₁`-row (coordinate `1`): the single bracket `[p, base 0]`. -/
theorem evenRawDepthShiftHom_one_apply
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) (hk : 3 ≤ k)
    (p : lambdaImage G (k - 1) (k + 1)) :
    ((evenRawDepthShiftHom base hk)
        (evenRawDepthCoordinateCorrection 1 p)).1 = commP p.1 (base 0) := by
  have hh : evenRawHandleDbarWord base
      (evenRawDepthCoordinateCorrection (1 : Fin (MarkedCore.coreRank h)) p :
        EvenRawDepthCorrection G h k).correction = 1 := by
    simp [evenRawHandleDbarWord, evenRawHandleU_ne_core _ evenRawCoreVal_lt_four.2.1,
      evenRawHandleV_ne_core _ evenRawCoreVal_lt_four.2.1, commP]
  have c0 : (evenRawDepthCoordinateCorrection (1 : Fin (MarkedCore.coreRank h)) p :
      EvenRawDepthCorrection G h k).correction 0 = 1 := by
    rw [evenRawDepthCoordinateCorrection_apply, if_neg evenRawIdx01]
  have c1 : (evenRawDepthCoordinateCorrection (1 : Fin (MarkedCore.coreRank h)) p :
      EvenRawDepthCorrection G h k).correction 1 = p.1 := by
    rw [evenRawDepthCoordinateCorrection_apply, if_pos rfl]
  have c2 : (evenRawDepthCoordinateCorrection (1 : Fin (MarkedCore.coreRank h)) p :
      EvenRawDepthCorrection G h k).correction 2 = 1 := by
    rw [evenRawDepthCoordinateCorrection_apply, if_neg evenRawIdx12.symm]
  have c3 : (evenRawDepthCoordinateCorrection (1 : Fin (MarkedCore.coreRank h)) p :
      EvenRawDepthCorrection G h k).correction 3 = 1 := by
    rw [evenRawDepthCoordinateCorrection_apply, if_neg evenRawIdx13.symm]
  change evenRawDbarWord base _ = _
  rw [evenRawDbarWord, hh, mul_one, evenRawCoreDbarWord, c0, c1, c2, c3]
  simp only [commP]
  group

/-- The `σ`-row (coordinate `2`): the cross bracket `[p, base 3]`. -/
theorem evenRawDepthShiftHom_two_apply
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) (hk : 3 ≤ k)
    (p : lambdaImage G (k - 1) (k + 1)) :
    ((evenRawDepthShiftHom base hk)
        (evenRawDepthCoordinateCorrection 2 p)).1 = commP p.1 (base 3) := by
  have hh : evenRawHandleDbarWord base
      (evenRawDepthCoordinateCorrection (2 : Fin (MarkedCore.coreRank h)) p :
        EvenRawDepthCorrection G h k).correction = 1 := by
    simp [evenRawHandleDbarWord, evenRawHandleU_ne_core _ evenRawCoreVal_lt_four.2.2.1,
      evenRawHandleV_ne_core _ evenRawCoreVal_lt_four.2.2.1, commP]
  have c0 : (evenRawDepthCoordinateCorrection (2 : Fin (MarkedCore.coreRank h)) p :
      EvenRawDepthCorrection G h k).correction 0 = 1 := by
    rw [evenRawDepthCoordinateCorrection_apply, if_neg evenRawIdx02]
  have c1 : (evenRawDepthCoordinateCorrection (2 : Fin (MarkedCore.coreRank h)) p :
      EvenRawDepthCorrection G h k).correction 1 = 1 := by
    rw [evenRawDepthCoordinateCorrection_apply, if_neg evenRawIdx12]
  have c2 : (evenRawDepthCoordinateCorrection (2 : Fin (MarkedCore.coreRank h)) p :
      EvenRawDepthCorrection G h k).correction 2 = p.1 := by
    rw [evenRawDepthCoordinateCorrection_apply, if_pos rfl]
  have c3 : (evenRawDepthCoordinateCorrection (2 : Fin (MarkedCore.coreRank h)) p :
      EvenRawDepthCorrection G h k).correction 3 = 1 := by
    rw [evenRawDepthCoordinateCorrection_apply, if_neg evenRawIdx23.symm]
  change evenRawDbarWord base _ = _
  rw [evenRawDbarWord, hh, mul_one, evenRawCoreDbarWord, c0, c1, c2, c3]
  simp only [commP]
  group

/-- The `x₂`-row (coordinate `3`): the cross bracket `[p, base 2]`. -/
theorem evenRawDepthShiftHom_three_apply
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) (hk : 3 ≤ k)
    (p : lambdaImage G (k - 1) (k + 1)) :
    ((evenRawDepthShiftHom base hk)
        (evenRawDepthCoordinateCorrection 3 p)).1 = commP p.1 (base 2) := by
  have hh : evenRawHandleDbarWord base
      (evenRawDepthCoordinateCorrection (3 : Fin (MarkedCore.coreRank h)) p :
        EvenRawDepthCorrection G h k).correction = 1 := by
    simp [evenRawHandleDbarWord, evenRawHandleU_ne_core _ evenRawCoreVal_lt_four.2.2.2,
      evenRawHandleV_ne_core _ evenRawCoreVal_lt_four.2.2.2, commP]
  have c0 : (evenRawDepthCoordinateCorrection (3 : Fin (MarkedCore.coreRank h)) p :
      EvenRawDepthCorrection G h k).correction 0 = 1 := by
    rw [evenRawDepthCoordinateCorrection_apply, if_neg evenRawIdx03]
  have c1 : (evenRawDepthCoordinateCorrection (3 : Fin (MarkedCore.coreRank h)) p :
      EvenRawDepthCorrection G h k).correction 1 = 1 := by
    rw [evenRawDepthCoordinateCorrection_apply, if_neg evenRawIdx13]
  have c2 : (evenRawDepthCoordinateCorrection (3 : Fin (MarkedCore.coreRank h)) p :
      EvenRawDepthCorrection G h k).correction 2 = 1 := by
    rw [evenRawDepthCoordinateCorrection_apply, if_neg evenRawIdx23]
  have c3 : (evenRawDepthCoordinateCorrection (3 : Fin (MarkedCore.coreRank h)) p :
      EvenRawDepthCorrection G h k).correction 3 = p.1 := by
    rw [evenRawDepthCoordinateCorrection_apply, if_pos rfl]
  change evenRawDbarWord base _ = _
  rw [evenRawDbarWord, hh, mul_one, evenRawCoreDbarWord, c0, c1, c2, c3]
  simp only [commP]
  group

/-- The `U_j`-handle row: the bracket `[p, base (V_j)]`, exactly as in the L template. -/
theorem evenRawDepthShiftHom_handleU_apply
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) (hk : 3 ≤ k)
    (j : Fin h) (p : lambdaImage G (k - 1) (k + 1)) :
    ((evenRawDepthShiftHom base hk)
        (evenRawDepthCoordinateCorrection (MarkedCore.handleIdxU j) p)).1 =
      commP p.1 (base (MarkedCore.handleIdxV j)) := by
  set c := (evenRawDepthCoordinateCorrection (MarkedCore.handleIdxU j) p :
    EvenRawDepthCorrection G h k).correction with hc
  have hcore : evenRawCoreDbarWord base c = 1 := by
    have e0 : c 0 = 1 := if_neg (evenRawCore_ne_handleU evenRawCoreVal_lt_four.1 j)
    have e1 : c 1 = 1 := if_neg (evenRawCore_ne_handleU evenRawCoreVal_lt_four.2.1 j)
    have e2 : c 2 = 1 := if_neg (evenRawCore_ne_handleU evenRawCoreVal_lt_four.2.2.1 j)
    have e3 : c 3 = 1 := if_neg (evenRawCore_ne_handleU evenRawCoreVal_lt_four.2.2.2 j)
    rw [evenRawCoreDbarWord, e0, e1, e2, e3]
    simp only [commP]
    group
  have hf : ∀ l ∈ List.finRange h, l ≠ j →
      commP (c (MarkedCore.handleIdxV l)) (base (MarkedCore.handleIdxU l)) *
        commP (c (MarkedCore.handleIdxU l)) (base (MarkedCore.handleIdxV l)) = 1 := by
    intro l _ hlj
    rw [show c (MarkedCore.handleIdxV l) = 1 from if_neg (evenRawHandleV_ne_handleU l j),
      show c (MarkedCore.handleIdxU l) = 1 from if_neg (evenRawHandleU_ne_handleU hlj)]
    simp only [commP]
    group
  have hprod := evenRaw_list_map_prod_eq_single_of_nodup (List.finRange h) j
    (fun l ↦ commP (c (MarkedCore.handleIdxV l)) (base (MarkedCore.handleIdxU l)) *
      commP (c (MarkedCore.handleIdxU l)) (base (MarkedCore.handleIdxV l)))
    (by simp) (List.nodup_finRange h) hf
  have hhandle : evenRawHandleDbarWord base c =
      commP p.1 (base (MarkedCore.handleIdxV j)) := by
    rw [evenRawHandleDbarWord, hprod,
      show c (MarkedCore.handleIdxV j) = 1 from if_neg (evenRawHandleV_ne_handleU j j),
      show c (MarkedCore.handleIdxU j) = p.1 from if_pos rfl]
    simp only [commP]
    group
  change evenRawDbarWord base c = _
  rw [evenRawDbarWord, hcore, one_mul, hhandle]

/-- The `V_j`-handle row: the bracket `[p, base (U_j)]`. -/
theorem evenRawDepthShiftHom_handleV_apply
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) (hk : 3 ≤ k)
    (j : Fin h) (p : lambdaImage G (k - 1) (k + 1)) :
    ((evenRawDepthShiftHom base hk)
        (evenRawDepthCoordinateCorrection (MarkedCore.handleIdxV j) p)).1 =
      commP p.1 (base (MarkedCore.handleIdxU j)) := by
  set c := (evenRawDepthCoordinateCorrection (MarkedCore.handleIdxV j) p :
    EvenRawDepthCorrection G h k).correction with hc
  have hcore : evenRawCoreDbarWord base c = 1 := by
    have e0 : c 0 = 1 := if_neg (evenRawCore_ne_handleV evenRawCoreVal_lt_four.1 j)
    have e1 : c 1 = 1 := if_neg (evenRawCore_ne_handleV evenRawCoreVal_lt_four.2.1 j)
    have e2 : c 2 = 1 := if_neg (evenRawCore_ne_handleV evenRawCoreVal_lt_four.2.2.1 j)
    have e3 : c 3 = 1 := if_neg (evenRawCore_ne_handleV evenRawCoreVal_lt_four.2.2.2 j)
    rw [evenRawCoreDbarWord, e0, e1, e2, e3]
    simp only [commP]
    group
  have hf : ∀ l ∈ List.finRange h, l ≠ j →
      commP (c (MarkedCore.handleIdxV l)) (base (MarkedCore.handleIdxU l)) *
        commP (c (MarkedCore.handleIdxU l)) (base (MarkedCore.handleIdxV l)) = 1 := by
    intro l _ hlj
    rw [show c (MarkedCore.handleIdxV l) = 1 from if_neg (evenRawHandleV_ne_handleV hlj),
      show c (MarkedCore.handleIdxU l) = 1 from if_neg (evenRawHandleU_ne_handleV l j)]
    simp only [commP]
    group
  have hprod := evenRaw_list_map_prod_eq_single_of_nodup (List.finRange h) j
    (fun l ↦ commP (c (MarkedCore.handleIdxV l)) (base (MarkedCore.handleIdxU l)) *
      commP (c (MarkedCore.handleIdxU l)) (base (MarkedCore.handleIdxV l)))
    (by simp) (List.nodup_finRange h) hf
  have hhandle : evenRawHandleDbarWord base c =
      commP p.1 (base (MarkedCore.handleIdxU j)) := by
    rw [evenRawHandleDbarWord, hprod,
      show c (MarkedCore.handleIdxV j) = p.1 from if_pos rfl,
      show c (MarkedCore.handleIdxU j) = 1 from if_neg (evenRawHandleU_ne_handleV j j)]
    simp only [commP]
    group
  change evenRawDbarWord base c = _
  rw [evenRawDbarWord, hcore, one_mul, hhandle]

/-! ### The raw span and the exact central-tower mismatch -/

/-- The literal even-shift image, viewed inside the ambient level quotient. -/
noncomputable def evenRawShiftSpan
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) (hk : 3 ≤ k) :
    Subgroup (levelQuot G (k + 1)) :=
  Subgroup.map (zLayer G k).subtype (evenRawDepthShiftHom base hk).range

/-- Every literal even shift lies in the raw shift span. -/
theorem evenRawDepthShift_mem_shiftSpan
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) (hk : 3 ≤ k)
    (V : EvenRawDepthCorrection G h k) :
    ((evenRawDepthShiftHom base hk) V).1 ∈ evenRawShiftSpan base hk :=
  ⟨(evenRawDepthShiftHom base hk) V, ⟨V, rfl⟩, rfl⟩

/-- The raw shift span sits inside the central defect layer. -/
theorem evenRawShiftSpan_le_zLayer
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) (hk : 3 ≤ k) :
    evenRawShiftSpan base hk ≤ zLayer G k := by
  rintro z ⟨q, _, rfl⟩
  exact q.2

/-- **The sole atom family the literal even rows do not separate**: every pure square of a
depth-`k-1` element belongs to the raw shift span.  Exactly the L template's
`RawPureSquareSpanSupply`, and by `evenRawPureSquareSpanSupply_iff_shiftSpan_eq_zLayer` it is
precisely the gap between the literal shift and generic tower generation. -/
def EvenRawPureSquareSpanSupply
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) (hk : 3 ≤ k) : Prop :=
  ∀ p : lambdaImage G (k - 1) (k + 1), p.1 ^ 2 ∈ evenRawShiftSpan base hk

/-- **Under the pure-square supply every bracket against a displayed generator lies in the raw
shift span.**  The L template reads four of its five index families straight off the rows and
divides the fifth by the supplied square.  The even case needs one step more: coordinate `1`
delivers `[p, base 0]` directly, and only then can `[p, base 1]` be extracted from the
coordinate-`0` row by dividing off *both* `p²` and `[p, base 0]`.  That extra division is the
whole visible cost of the diagonal atom's product partner. -/
theorem evenRawBracket_base_mem_shiftSpan
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) (hk : 3 ≤ k)
    (Hsq : EvenRawPureSquareSpanSupply base hk)
    (p : lambdaImage G (k - 1) (k + 1)) (i : Fin (MarkedCore.coreRank h)) :
    commP p.1 (base i) ∈ evenRawShiftSpan base hk := by
  have hb0 : commP p.1 (base 0) ∈ evenRawShiftSpan base hk := by
    have hmem := evenRawDepthShift_mem_shiftSpan base hk
      (evenRawDepthCoordinateCorrection 1 p : EvenRawDepthCorrection G h k)
    rwa [evenRawDepthShiftHom_one_apply base hk p] at hmem
  refine evenIndex_cases (P := fun i ↦ commP p.1 (base i) ∈ evenRawShiftSpan base hk)
    hb0 ?_ ?_ ?_ ?_ ?_ i
  · have h0 := evenRawDepthShift_mem_shiftSpan base hk
      (evenRawDepthCoordinateCorrection 0 p : EvenRawDepthCorrection G h k)
    rw [evenRawDepthShiftHom_zero_apply base hk p] at h0
    have h := Subgroup.mul_mem _
      (Subgroup.inv_mem _ (Subgroup.mul_mem _ (Hsq p) hb0)) h0
    simpa only [inv_mul_cancel_left] using h
  · have hmem := evenRawDepthShift_mem_shiftSpan base hk
      (evenRawDepthCoordinateCorrection 3 p : EvenRawDepthCorrection G h k)
    rwa [evenRawDepthShiftHom_three_apply base hk p] at hmem
  · have hmem := evenRawDepthShift_mem_shiftSpan base hk
      (evenRawDepthCoordinateCorrection 2 p : EvenRawDepthCorrection G h k)
    rwa [evenRawDepthShiftHom_two_apply base hk p] at hmem
  · intro j
    have hmem := evenRawDepthShift_mem_shiftSpan base hk
      (evenRawDepthCoordinateCorrection (MarkedCore.handleIdxV j) p :
        EvenRawDepthCorrection G h k)
    rwa [evenRawDepthShiftHom_handleV_apply base hk j p] at hmem
  · intro j
    have hmem := evenRawDepthShift_mem_shiftSpan base hk
      (evenRawDepthCoordinateCorrection (MarkedCore.handleIdxU j) p :
        EvenRawDepthCorrection G h k)
    rwa [evenRawDepthShiftHom_handleU_apply base hk j p] at hmem

open scoped commutatorElement in
private theorem evenRawCommutator_eq_commP_inv {H' : Type*} [Group H'] (v g : H') :
    ⁅v, g⁆ = commP v⁻¹ g⁻¹ := by
  simp only [commutatorElement_def, commP, inv_inv]

/-- **Generic square/bracket generation closes the whole central layer.**  No character
statement is used: the only extra input beyond the literal rows is the pure-square family.
The even analogue of `rawShiftSpan_eq_zLayer_of_pureSquares`. -/
theorem evenRawShiftSpan_eq_zLayer_of_pureSquares
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) (hk : 3 ≤ k)
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G)
    (hbase : Subgroup.closure (Set.range base) = ⊤)
    (Hsq : EvenRawPureSquareSpanSupply base hk) :
    evenRawShiftSpan base hk = zLayer G k := by
  apply le_antisymm (evenRawShiftSpan_le_zLayer base hk)
  intro q hq
  have hq' : q ∈ lambdaImage G (k - 1 + 1) (k + 1) := by rwa [show k - 1 + 1 = k by omega]
  refine lambdaImage_induction G hfg hpro (j := k - 1) (by omega)
    (p := fun z ↦ z ∈ evenRawShiftSpan base hk) ?_ ?_
    (Subgroup.one_mem _) (fun _ _ ↦ Subgroup.mul_mem _) (fun _ ↦ Subgroup.inv_mem _) hq'
  · intro v hv
    let p : lambdaImage G (k - 1) (k + 1) := ⟨levelMk G (k + 1) v, ⟨v, hv, rfl⟩⟩
    simpa only [map_pow] using Hsq p
  · intro v hv g
    let p : lambdaImage G (k - 1) (k + 1) :=
      ⟨(levelMk G (k + 1) v)⁻¹, ⟨v⁻¹, Subgroup.inv_mem _ hv, by rw [map_inv]⟩⟩
    have hp : ∀ z : levelQuot G (k + 1), commP p.1 z ∈ evenRawShiftSpan base hk := by
      intro z
      have hz : z ∈ Subgroup.closure (Set.range base) := by rw [hbase]; trivial
      refine Subgroup.closure_induction
        (p := fun x _ ↦ commP p.1 x ∈ evenRawShiftSpan base hk) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨i, rfl⟩
        exact evenRawBracket_base_mem_shiftSpan base hk Hsq p i
      · simp [commP]
      · intro x y _ _ hx hy
        rw [commP_mul_right_of_mem k hk p.2 x y]
        exact Subgroup.mul_mem _ hx hy
      · intro x _ hx
        rw [commP_inv_right_of_mem k hk p.2 x]
        exact Subgroup.inv_mem _ hx
    rw [map_commutatorElement, evenRawCommutator_eq_commP_inv]
    exact hp (levelMk G (k + 1) g)⁻¹

/-- **The pure-square family is not merely sufficient but equivalent** to raw shift
surjectivity onto the central layer, given a generating displayed tuple.  This pins the exact
gap between generic square/bracket tower generation and the literal even relator shift. -/
theorem evenRawPureSquareSpanSupply_iff_shiftSpan_eq_zLayer
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) (hk : 3 ≤ k)
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G)
    (hbase : Subgroup.closure (Set.range base) = ⊤) :
    EvenRawPureSquareSpanSupply base hk ↔ evenRawShiftSpan base hk = zLayer G k := by
  refine ⟨evenRawShiftSpan_eq_zLayer_of_pureSquares base hk hfg hpro hbase, ?_⟩
  intro hspan p
  rw [hspan]
  exact sq_mem_zLayer k hk p.2

end RawSpan

end

end GQ2.Dyadic.StageGeneric

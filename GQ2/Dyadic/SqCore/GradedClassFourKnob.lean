/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.GradedClassFourIdentity

/-!
# W71-CFOUR: the class-four leftover, and the two directions believed to be missing

Wave 70 relocated the class-four obligation to a single element `cfourIdLeftover nu' j` of the
central layer `Z = γ₃/γ₄`, and left as **uncommitted analysis** (its note, §4) the question
whether that element is reachable by `γ₂`-valued, exactly row-trivial corrections of wave 68's
frame - `CfourIdReachable h`.  That analysis put the reachable subgroup at codimension exactly
two in `Z`, missing the fourth powers of the two odd-row generators, and expected a `w⁴`
cancellation to close the gap.

This file evaluates the leftover and settles both directions the analysis flagged.  Neither
turns out to be missing, and neither is closed by the mechanism the analysis proposed.

## §1 and §2 Squares of exactly row-trivial elements are legal knobs, with no repair

The analysis measured admissibility of a square knob `c = d²` by asking both rows of `c` to lie
in `4ℤ₂` - a codimension-two condition on the class of `d` - and repaired the remainder inside
`γ₃` (`cfourId_row_repair`).  That measurement is sound but it is not what governs the terms
that occur, because of a triviality the analysis did not use: if `d` is **exactly** row-trivial
then so is `d²` (`cfourKnob_sq_admissible`), so `d²` is a legal correction on the nose, and its
square knob is the fourth power `d⁴` (`cfourKnob_sq_knob`).

⭐⭐ `cfourKnob_dressSq_admissible`: wave 68's dressing `A = bridgeDress nu' j` is exactly
row-trivial by construction (`bridge_nuLam_dress`, `bridge_nu_dress`; that is what wave 68's
pivot factor was inserted to arrange), so `A²` is an admissible correction and `A⁴` is free.
⭐ `cfourKnob_comm_admissible`: a commutator is exactly row-trivial too, the rows being
homomorphisms into a commutative group.

## §3 The leftover in closed form

⭐⭐⭐ `cfourKnob_leftover_eq`.  Wave 68's tuple dresses the `σ`- and `x₀`-slots by `A` and
nothing else, so against the undressed frame - whose class-four relator is exactly
`cfourEichDefect nu' j` (`cfour_relator_base`) - only three factors of `cfour_sqRelWord` move,
the `x₁`-square and the handle word being untouched:

```text
  LEFTOVER = ⁅σA, x₀A⁆ · ⁅σ, x₀⁆⁻¹ · cfourEichDefect · (A⁴ · ⁅A, x₀⁆²) · ⁅x₁, ⁅x₁, A⁆⁆ .
```

The fourth-power factor is `cfour_pow_four_mul`; the triple bracket is
`cfourKnob_triple_right_hom`, the statement that `ad(p)²` is additive in its far slot.

**First half of the wave-70 question, answered.**  The only fourth power in the leftover is
`A⁴`.  The fourth powers `σ⁴` and `x₀⁴` occur in the frame's relator and in the generator
relation alike and cancel, so they never reach the leftover; the directions the analysis named
as missing are not directions the leftover has a component in.  And `A⁴` is the square knob of
the admissible correction `A²`.

## §4 The pairing that frees the `ad(x₁)²`-direction

The remaining term `⁅x₁, ⁅x₁, A⁆⁆` is the direction the wave-69 and wave-70 analyses both
identified as delicate.  The wave-70 argument for `K ⊇ L₃(V)` read it off the `x₁`-square knob,
but the committed `cfourId_x1_sq_direction` says that knob is
`(commP x₁ q)² · commP (commP x₁ q) x₁` - an iterated bracket **times a square** - and the
`x₁`-slot bundle is the only source of squares, so the square cannot be supplied separately to
cancel it.

⭐⭐⭐ `cfourKnob_sq_knob_pair` removes it by pairing two knobs instead of reading one.  Run the
`x₁`-slot knob `c ↦ c² · ⁅c, q⁆` at `c = p²` and at `c = ⁅p, q⁆` and multiply: each contributes
`⁅p, q⁆²`, and the two cancel because `⁅p, q⁆` is a `Y`-element and `Y`-elements have trivial
fourth power (`cfourKnob_pow_four_lambdaTwo`).  What is left is

```text
  p⁴ · ⁅⁅p, q⁆, p⁆ · ⁅⁅p, q⁆, q⁆ ,
```

a fourth power and two **pure** iterated brackets.  ⭐⭐ `cfourKnob_dress_pair` is the instance
`p = A`, `q = x₁`, where both corrections are admissible by §1 and §2 and, through
`cfourKnob_triple_swap`, the last factor is literally the leftover's triple bracket
`⁅x₁, ⁅x₁, A⁆⁆`.  So the leftover's fourth power and its triple bracket are delivered together
by two admissible corrections, and the residue `⁅⁅A, x₁⁆, A⁆` is a bracket whose **outer** slot
is `A`, a slot the handle knobs `cfourId_dress_handleU` / `cfourId_dress_handleV` reach without
touching the `x₁`-slot.

**Verdict.**  `SqClassClearingSupply h 4` is **not** discharged here, and nothing here refutes
it.  What is settled is that neither of the two directions the wave-70 analysis named as the
obstruction is one: the `σ⁴`/`x₀⁴` directions do not occur in the leftover, and the
`ad(x₁)²`-direction is reachable, though not by the argument that was recorded.  What is left is
the leftover's remaining factor `⁅σA, x₀A⁆ · ⁅σ, x₀⁆⁻¹ · cfourEichDefect nu' j`, the two
class-four defects whose class-three images cancel, and the assembly of the knobs above into one
correction tuple.

Lane W71-CFOUR.  New file; no edits to existing files.  Prefix `cfourKnob`.
-/

open Multiplicative

namespace GQ2

open Roe.Labute

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 Squares of exactly row-trivial elements -/

section RowTrivialSquare

variable {h : ℕ}

/-- Every square is a `γ₂`-element. -/
theorem cfourKnob_sq_mem (g : (DSq h : Type)) : g ^ 2 ∈ twoCentralSeries (DSq h : Type) 2 :=
  sq_mem_twoCentralSeries_succ (G := (DSq h : Type)) (Subgroup.mem_top _)

/-- **The `λ`-row of a square doubles.**  In particular an exactly `λ`-trivial element has an
exactly `λ`-trivial square. -/
theorem cfourKnob_sq_nuLam {d : (DSq h : Type)} (hl : nuLam h d = 1) : nuLam h (d ^ 2) = 1 := by
  rw [map_pow, hl, one_pow]

/-- **The `ν'`-row of a square doubles.** -/
theorem cfourKnob_sq_nu (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    {d : (DSq h : Type)} (hn : nu' d = 1) : nu' (d ^ 2) = 1 := by
  rw [map_pow, hn, one_pow]

/-- ⭐⭐ **The square of an exactly row-trivial element is an admissible knob.**  This is the
observation the wave-70 analysis did not make.  That analysis measured admissibility of a square
knob `c = d²` by asking both rows of `c` to lie in `4ℤ₂`, a **codimension-two** condition on the
class of `d` in `V`, and then repaired the remainder inside `γ₃` (`cfourId_row_repair`).  When
`d` is exactly row-trivial no such measurement is needed: `d²` is a `γ₂`-element whose two rows
are exactly trivial, so it is a legal correction on the nose. -/
theorem cfourKnob_sq_admissible (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    {d : (DSq h : Type)} (hl : nuLam h d = 1) (hn : nu' d = 1) :
    d ^ 2 ∈ twoCentralSeries (DSq h : Type) 2 ∧ nuLam h (d ^ 2) = 1 ∧ nu' (d ^ 2) = 1 :=
  ⟨cfourKnob_sq_mem d, cfourKnob_sq_nuLam hl, cfourKnob_sq_nu nu' hn⟩

/-- ⭐ **The square part of the `d²`-knob is the fourth power `d⁴`.**  The `x₁`-slot knob of
`cfour_dress_two` at `c = d²` is `c² · commP c (m 2)`, and this evaluates its first factor. -/
theorem cfourKnob_sq_knob (d : (DSq h : Type)) :
    (levelMk (DSq h : Type) 4 (d ^ 2)) ^ 2 = (levelMk (DSq h : Type) 4 d) ^ 4 := by
  rw [map_pow, ← pow_mul]

end RowTrivialSquare

/-! ## §2 Wave 68's dressing has an admissible square -/

section DressSquare

variable {h : ℕ} (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)

/-- ⭐⭐⭐ **Wave 68's dressing has an admissible square.**  `bridgeDress nu' j` is exactly
row-trivial by construction: `bridge_nuLam_dress` is unconditional and `bridge_nu_dress` holds at
every selected marking, the pivot factor `w^{-2ν'(u)ν'(v)}` having been inserted for exactly that
purpose.  So `A²` is a `γ₂`-valued, exactly row-trivial correction, and by `cfourKnob_sq_knob`
its square knob is `A⁴`.

This is the fourth-power direction the wave-70 analysis expected to have to reach by a
cancellation argument.  There is nothing to cancel: the knob is `A²`, and it is legal because
wave 68 already made `A` row-trivial. -/
theorem cfourKnob_dressSq_admissible (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    bridgeDress nu' j ^ 2 ∈ twoCentralSeries (DSq h : Type) 2 ∧
      nuLam h (bridgeDress nu' j ^ 2) = 1 ∧ nu' (bridgeDress nu' j ^ 2) = 1 :=
  cfourKnob_sq_admissible nu' (bridge_nuLam_dress nu' j) (bridge_nu_dress nu' j hsigma hx0)

/-- **The fourth power of wave 68's dressing, as the square knob of `A²`.** -/
theorem cfourKnob_dressSq_knob :
    (levelMk (DSq h : Type) 4 (bridgeDress nu' j ^ 2)) ^ 2
      = (levelMk (DSq h : Type) 4 (bridgeDress nu' j)) ^ 4 :=
  cfourKnob_sq_knob _

end DressSquare

/-! ## §3 The leftover in closed form -/

section ClosedForm

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- ⭐ **The triple bracket is additive in its far slot.**  Both correction terms of
`cfour_commP_mul_right` are killed: the inner one is a bracket of a `Y`-element, hence a
`Z`-element, and `Z` kills every bracket it meets.  This is the class-four form of the statement
that `ad(p)²` is a homomorphism, and it is what makes the leftover's triple-bracket term depend
on the dressing alone. -/
theorem cfourKnob_triple_right_hom (p q c : levelQuot G 4) :
    commP p (commP p (q * c)) = commP p (commP p q) * commP p (commP p c) := by
  have hz0 : commP (commP p q) c ∈ zLayer G 3 :=
    cfour_commP_mem_zLayer_left (cfour_commP_mem_lambdaTwo p q) c
  have hin : commP p (q * c) = commP p c * commP p q * commP (commP p q) c :=
    cfour_commP_mul_right p q c
  have hy1 : commP p c ∈ lambdaImage G 2 4 := cfour_commP_mem_lambdaTwo p c
  have houter : commP p (commP p c * commP p q) = commP p (commP p q) * commP p (commP p c) := by
    rw [cfour_commP_mul_right p (commP p c) (commP p q),
      cfour_commP_zLayer_left (cfour_commP_mem_zLayer_right p hy1) (commP p q), mul_one]
  rw [hin, cfour_commP_mul_right p (commP p c * commP p q) (commP (commP p q) c),
    cfour_commP_zLayer_right hz0 p, one_mul, houter, cfour_commP_zLayer_right hz0 _, mul_one]

/-- A central factor in the second slot of a five-fold product moves to the end. -/
theorem cfourKnob_push_two {z : levelQuot G 4} (hz : z ∈ zLayer G 3)
    (a b c d e : levelQuot G 4) : a * (b * z) * c * d * e = a * b * c * d * e * z := by
  simp only [mul_assoc]
  rw [cfour_zLayer_comm hz]
  simp only [mul_assoc]

/-- A central factor in the fourth slot of a five-fold product moves to the end. -/
theorem cfourKnob_push_four {z : levelQuot G 4} (hz : z ∈ zLayer G 3)
    (a b c d e : levelQuot G 4) : a * b * c * (d * z) * e = a * b * c * d * e * z := by
  simp only [mul_assoc]
  rw [cfour_zLayer_comm hz]

end ClosedForm

section Leftover

variable {h : ℕ} (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)

/-- ⭐⭐⭐ **The class-four leftover, in closed form.**  Write `A = bridgeDress nu' j` for wave
68's dressing.  Then

```text
  LEFTOVER = ⁅σA, x₀A⁆ · ⁅σ, x₀⁆⁻¹ · cfourEichDefect · (A⁴ · ⁅A, x₀⁆²) · ⁅x₁, ⁅x₁, A⁆⁆ .
```

Wave 68's tuple dresses the `σ`- and `x₀`-slots by `A` and nothing else, so against the
**undressed** frame - whose class-four relator is exactly `cfourEichDefect nu' j`
(`cfour_relator_base`) - only three factors of `cfour_sqRelWord` move, and the `x₁`-square and
the handle word are untouched:

* the core bracket, giving the `Y`-valued first two factors;
* the `x₀`-slot's **fourth power**, giving `A⁴ · ⁅A, x₀⁆²` by `cfour_pow_four_mul`;
* the **triple bracket**, giving `⁅x₁, ⁅x₁, A⁆⁆` by `cfourKnob_triple_right_hom`.

The last two are `Z`-elements, hence central, which is why they may be listed at the end.

**Consequence for the fourth-power question.**  The only fourth power in the leftover is `A⁴`.
The generators' own fourth powers `σ⁴` and `x₀⁴` occur in the frame's relator and in the
generator relation alike and cancel; they never reach the leftover.  This is the first half of
the wave-70 §4 question, answered: the leftover has no `σ⁴`- or `x₀⁴`-component to begin with,
and its one fourth-power term `A⁴` is the square knob of the admissible correction `A²`
(`cfourKnob_dressSq_admissible`). -/
theorem cfourKnob_leftover_eq :
    cfourIdLeftover nu' j
      = commP (levelMk (DSq h : Type) 4 (dsqSigma h) * levelMk (DSq h : Type) 4 (bridgeDress nu' j))
            (levelMk (DSq h : Type) 4 (dsqX0 h) * levelMk (DSq h : Type) 4 (bridgeDress nu' j)) *
          (commP (levelMk (DSq h : Type) 4 (dsqSigma h)) (levelMk (DSq h : Type) 4 (dsqX0 h)))⁻¹ *
          cfourEichDefect nu' j *
          (levelMk (DSq h : Type) 4 (bridgeDress nu' j) ^ 4 *
            commP (levelMk (DSq h : Type) 4 (bridgeDress nu' j))
              (levelMk (DSq h : Type) 4 (dsqX0 h)) ^ 2) *
          commP (levelMk (DSq h : Type) 4 (dsqX1 h))
            (commP (levelMk (DSq h : Type) 4 (dsqX1 h))
              (levelMk (DSq h : Type) 4 (bridgeDress nu' j))) := by
  classical
  set s := levelMk (DSq h : Type) 4 (dsqSigma h) with hs
  set x0 := levelMk (DSq h : Type) 4 (dsqX0 h) with hx0
  set x1 := levelMk (DSq h : Type) 4 (dsqX1 h) with hx1
  set A := levelMk (DSq h : Type) 4 (bridgeDress nu' j) with hA
  set H := handleWord
    (fun i => levelMk (DSq h : Type) 4 (sqArbBase h nu' j (sqHandleIdxU i)))
    (fun i => levelMk (DSq h : Type) 4 (sqArbBase h nu' j (sqHandleIdxV i))) with hH
  have hz2 : A ^ 4 * commP A x0 ^ 2 ∈ zLayer (DSq h : Type) 3 :=
    Subgroup.mul_mem _ (cfour_pow_four_mem_zLayer A)
      (cfour_sq_mem_zLayer (cfour_commP_mem_lambdaTwo A x0))
  have hz4 : commP x1 (commP x1 A) ∈ zLayer (DSq h : Type) 3 :=
    cfour_commP_mem_zLayer_right x1 (cfour_commP_mem_lambdaTwo x1 A)
  have hbase : commP s x0 * x0 ^ 4 * x1 ^ 2 * commP x1 (commP x1 s) * H
      = cfourEichDefect nu' j := by
    have h := cfour_relator_base nu' j
    rw [cfour_sqRelWord] at h
    simpa only [sqArbBase_zero, sqArbBase_one, sqArbBase_two, hs, hx0, hx1, hH] using h
  have hfr : cfourIdLeftover nu' j
      = commP (s * A) (x0 * A) * (x0 ^ 4 * (A ^ 4 * commP A x0 ^ 2)) * x1 ^ 2 *
        (commP x1 (commP x1 s) * commP x1 (commP x1 A)) * H := by
    rw [← cfourId_leftover_eq nu' j, cfour_sqRelWord]
    simp only [bridge_frame_zero, bridge_frame_one, bridge_frame_two, bridge_frame_handleU,
      bridge_frame_handleV, map_mul, hs, hx0, hx1, hA, hH]
    rw [cfour_pow_four_mul x0 A, cfourKnob_triple_right_hom x1 s A, mul_assoc (x0 ^ 4)]
  rw [hfr, cfourKnob_push_four hz4, cfourKnob_push_two hz2, ← hbase]
  group

end Leftover

/-! ## §4 The pairing that frees the `ad(x₁)²`-direction -/

section Pair

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A `Y`-element has trivial fourth power: its square is already a `Z`-element, and `Z` has
exponent two.  This is the cancellation the pairing below runs on. -/
theorem cfourKnob_pow_four_lambdaTwo {y : levelQuot G 4} (hy : y ∈ lambdaImage G 2 4) :
    y ^ 2 * y ^ 2 = 1 := by
  rw [← pow_two]
  exact zLayer_sq G (cfour_sq_mem_zLayer hy)

/-- **The iterated bracket is symmetric between its two outer readings**: `⁅⁅q, p⁆, p⁆` and
`⁅p, ⁅p, q⁆⁆` are the same element of `Z`.  Both swaps are inverses (`commP a b = (commP b a)⁻¹`
in any group), an inverse in a `Y`-slot is invisible (`gThreeFour_ad_inv_left`), and a bracket
against a `Y`-element is its own inverse.  This is what lets `cfourKnob_sq_knob_pair` be read
against `cfourKnob_leftover_eq`, whose triple bracket is written the second way. -/
theorem cfourKnob_triple_swap (p q : levelQuot G 4) :
    commP (commP q p) p = commP p (commP p q) := by
  have hsw : ∀ a b : levelQuot G 4, commP a b = (commP b a)⁻¹ := by
    intro a b; simp only [commP]; group
  have hy : commP p q ∈ lambdaImage G 2 4 := cfour_commP_mem_lambdaTwo p q
  rw [hsw q p, gThreeFour_ad_inv_left hy p, hsw (commP p q) p,
    zLayer_inv_self (cfour_commP_mem_zLayer_right p hy)]

/-- ⭐⭐⭐ **The two `x₁`-slot knobs whose squares cancel.**  The `x₁`-slot knob is
`c ↦ c² · ⁅c, q⁆` (`cfour_dress_two`, at `q = m 2`), the only knob carrying a square, and the
square always arrives bundled.  Run it at the two corrections `c = p²` and `c = ⁅p, q⁆` and
multiply: by `gThreeFour_commP_sq_left` the first contributes `⁅p, q⁆²` and the second
contributes `⁅p, q⁆²` again, and the two cancel because `⁅p, q⁆` is a `Y`-element and `Y`-elements
have trivial fourth power.  What is left is

```text
  p⁴ · ⁅⁅p, q⁆, p⁆ · ⁅⁅p, q⁆, q⁆ ,
```

a fourth power times **two pure iterated brackets, with no square attached**.

This is the step the wave-70 §4 analysis was missing.  That analysis reached the delicate
direction `⁅⁅p, q⁆, q⁆ = ad(q)²(p)` by identifying it with the `x₁`-square knob, citing
`cfourId_x1_sq_direction`; but that committed statement reads
`commP (x₁²) q = (commP x₁ q)² · commP (commP x₁ q) x₁`, so the identification drops a square,
and the bundle is the only source of squares, so the dropped term cannot be supplied separately.
Pairing two knobs instead of reading one removes the square honestly. -/
theorem cfourKnob_sq_knob_pair (p q : levelQuot G 4) :
    ((p ^ 2) ^ 2 * commP (p ^ 2) q) * (commP p q ^ 2 * commP (commP p q) q)
      = p ^ 4 * (commP (commP p q) p * commP (commP p q) q) := by
  have hy : commP p q ∈ lambdaImage G 2 4 := cfour_commP_mem_lambdaTwo p q
  have hz1 : commP p q ^ 2 ∈ zLayer G 3 := cfour_sq_mem_zLayer hy
  have hT1 : commP (commP p q) p ∈ zLayer G 3 := cfour_commP_mem_zLayer_left hy p
  have hsq : (p ^ 2 : levelQuot G 4) ^ 2 = p ^ 4 := by rw [← pow_mul]
  have hmid : commP (commP p q) p * (commP p q ^ 2 * commP (commP p q) q)
      = commP p q ^ 2 * (commP (commP p q) p * commP (commP p q) q) := by
    rw [← mul_assoc, ← cfour_zLayer_comm hz1 (commP (commP p q) p), mul_assoc]
  rw [hsq, gThreeFour_commP_sq_left]
  simp only [mul_assoc]
  rw [hmid, ← mul_assoc (commP p q ^ 2), cfourKnob_pow_four_lambdaTwo hy, one_mul]

end Pair

section Rows

variable {h : ℕ}

/-- **A commutator is exactly row-trivial**: the two rows are homomorphisms into a commutative
group, so they kill every commutator.  No `4ℤ₂` computation and no `cfourId_row_repair` is
needed for a commutator correction. -/
theorem cfourKnob_comm_row (f : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (a b : (DSq h : Type)) : f (commP a b) = 1 := by
  simp only [commP, map_mul, map_inv]
  rw [mul_comm (f a)⁻¹ (f b)⁻¹, mul_assoc, mul_assoc, ← mul_assoc (f a)⁻¹, inv_mul_cancel,
    one_mul, inv_mul_cancel]

/-- ⭐⭐ **A commutator is an admissible knob.**  It lies in `γ₂` and both its rows are exactly
trivial, so it is a legal correction with no repair.  Together with `cfourKnob_sq_admissible`
this says the two corrections of `cfourKnob_sq_knob_pair` are admissible whenever `p` is: `p²`
by §1 and `⁅p, q⁆` here. -/
theorem cfourKnob_comm_admissible (nu' : ContinuousMonoidHom (DSq h : Type)
    (Multiplicative ℤ_[2])) (a b : (DSq h : Type)) :
    commP a b ∈ twoCentralSeries (DSq h : Type) 2 ∧ nuLam h (commP a b) = 1 ∧
      nu' (commP a b) = 1 :=
  ⟨cfour_commP_mem_two a b, cfourKnob_comm_row _ a b, cfourKnob_comm_row nu' a b⟩

end Rows

section Application

variable {h : ℕ} (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)

/-- ⭐⭐⭐ **The leftover's two hard terms are reached together.**  Instantiate
`cfourKnob_sq_knob_pair` at `p = A` (wave 68's dressing) and `q = x₁`.  Both corrections are
admissible - `A²` by `cfourKnob_dressSq_admissible`, `⁅A, x₁⁆` by `cfourKnob_comm_admissible` -
and the product of their two `x₁`-slot knobs is

```text
  A⁴ · ⁅⁅A, x₁⁆, A⁆ · ⁅⁅A, x₁⁆, x₁⁆ .
```

By `cfourKnob_leftover_eq` the leftover carries exactly `A⁴` as its only fourth power and
exactly `⁅x₁, ⁅x₁, A⁆⁆` as its triple bracket, and in the exponent-two layer `Z` that triple
bracket is `⁅⁅A, x₁⁆, x₁⁆`.  So the pair delivers both of the leftover's `x₁`-involving terms at
once, leaving only `⁅⁅A, x₁⁆, A⁆` - a pure bracket whose **outer** slot is `A`, hence one the
handle knobs of `cfourId_dress_handleU` / `cfourId_dress_handleV` reach without touching the
`x₁`-slot. -/
theorem cfourKnob_dress_pair :
    (((levelMk (DSq h : Type) 4 (bridgeDress nu' j)) ^ 2) ^ 2 *
        commP ((levelMk (DSq h : Type) 4 (bridgeDress nu' j)) ^ 2)
          (levelMk (DSq h : Type) 4 (dsqX1 h))) *
      (commP (levelMk (DSq h : Type) 4 (bridgeDress nu' j))
          (levelMk (DSq h : Type) 4 (dsqX1 h)) ^ 2 *
        commP (commP (levelMk (DSq h : Type) 4 (bridgeDress nu' j))
          (levelMk (DSq h : Type) 4 (dsqX1 h))) (levelMk (DSq h : Type) 4 (dsqX1 h)))
      = (levelMk (DSq h : Type) 4 (bridgeDress nu' j)) ^ 4 *
        (commP (commP (levelMk (DSq h : Type) 4 (bridgeDress nu' j))
              (levelMk (DSq h : Type) 4 (dsqX1 h)))
            (levelMk (DSq h : Type) 4 (bridgeDress nu' j)) *
          commP (levelMk (DSq h : Type) 4 (dsqX1 h))
            (commP (levelMk (DSq h : Type) 4 (dsqX1 h))
              (levelMk (DSq h : Type) 4 (bridgeDress nu' j)))) := by
  rw [cfourKnob_sq_knob_pair, cfourKnob_triple_swap]

end Application

/-! ## §5 Axiom pins -/

section AxiomPins

#print axioms cfourKnob_sq_mem
#print axioms cfourKnob_sq_nuLam
#print axioms cfourKnob_sq_nu
#print axioms cfourKnob_sq_admissible
#print axioms cfourKnob_sq_knob
#print axioms cfourKnob_dressSq_admissible
#print axioms cfourKnob_dressSq_knob
#print axioms cfourKnob_triple_right_hom
#print axioms cfourKnob_push_two
#print axioms cfourKnob_push_four
#print axioms cfourKnob_leftover_eq
#print axioms cfourKnob_pow_four_lambdaTwo
#print axioms cfourKnob_triple_swap
#print axioms cfourKnob_sq_knob_pair
#print axioms cfourKnob_comm_row
#print axioms cfourKnob_comm_admissible
#print axioms cfourKnob_dress_pair

end AxiomPins

end SqCore

end Dyadic

end GQ2

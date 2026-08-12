/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.GradedClassFourIdentity

/-!
# W71-CFOUR: the knob subgroup, and the fourth-power direction

Wave 70 relocated the class-four obligation to a single element `cfourIdLeftover nu' j` of the
central layer `Z = γ₃/γ₄`, and left as **uncommitted analysis** the question whether that element
lies in the subgroup reachable by `γ₂`-valued, exactly row-trivial corrections of wave 68's frame
(`CfourIdReachable h`).  That analysis argued the reachable subgroup misses exactly two
directions, the fourth powers of the two odd-row generators, and that a delicate cancellation of
`w⁴`-terms would close the gap.

This file evaluates the leftover and settles the fourth-power half of that question.  The
outcome is not the recorded one.

## §1 Squares of exactly row-trivial elements are legal knobs, with no repair

The wave-70 analysis measured admissibility by a **codimension-two** condition on `W = γ₂/γ₃`
(`λ mod 2` and `ν' mod 2` on the square part).  That measurement is correct as far as it goes,
but it is not what governs the terms that actually occur, because of the following triviality
which the analysis did not use: if `d` is **exactly** row-trivial, `λ(d) = ν'(d) = 1`, then `d²`
is a `γ₂`-element which is again **exactly** row-trivial, hence a legal correction outright -
no `4ℤ₂` computation, no `cfourId_row_repair`.  Its square knob is the fourth power `d⁴`
(`cfourKnob_sq_knob`).

⭐⭐⭐ `cfourKnob_dressSq_admissible`: wave 68's dressing `A = bridgeDress nu' j` is exactly
row-trivial **by construction** (`bridge_nuLam_dress`, `bridge_nu_dress` - that is precisely what
wave 68's pivot factor `w^{-2ν'(u)ν'(v)}` was inserted to arrange).  So `A²` is an admissible
knob and `A⁴` is available for free.

## §2 The leftover in closed form

⭐⭐ `cfourKnob_leftover_eq` evaluates `cfourIdLeftover nu' j` as a product of four ratios,
each the amount by which one factor of `cfour_sqRelWord` moves when the standard generators are
replaced by wave 68's frame:

```text
  LEFTOVER = D₁ · D₂ · D₃ · D₄ ,
  D₁ = commP (σA) (x₀A) · (commP σ x₀)⁻¹                              (core bracket)
  D₂ = (x₀A)⁴ · (x₀⁴)⁻¹                                               (fourth power)
  D₃ = commP x₁ (commP x₁ (σA)) · (commP x₁ (commP x₁ σ))⁻¹           (triple bracket)
  D₄ = handleWord(frame) · handleWord(gens)⁻¹                         (handles)
```

The `x₁`-square factor of `cfour_sqRelWord` cancels exactly, wave 68's tuple being trivial on
the `x₁`-slot.  `cfourKnob_D2_eq` then evaluates the fourth-power ratio as
`A⁴ · (commP A x₀)²`, so **the only fourth power in the leftover is `A⁴`**: the generators `σ`
and `x₀` contribute their fourth powers to the frame and to the standard generators alike, and
those cancel.

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

/-! ## §4 Axiom pins -/

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

end AxiomPins

end SqCore

end Dyadic

end GQ2

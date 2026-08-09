/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedLift

/-!
# W53-CONTAIN: the relator containment at class four

W52-VANISH located the sharpest remaining step of the `h ≥ 1` route: the defect of a
`K`-dressed frame of a RELATOR is a pure dressing artefact, so at class four it should be
the graded Fox form of the dressing, exactly the shape the stage engine's completion
theorems kill (`docs/dyadic/w52-vanish-note.md` §7 item 2).  This file commits that
statement on the class-four carrier `SqU5` of `GradedFour`, at every handle count, over an
arbitrary commutative ring wherever the arithmetic allows.

The `K`-dressing at the class-four stage is the **five-slot `γ₃`-dressing**: every slot of
the frame multiplied on the right by an element with only class-`≥ 3` coordinates, the
slice shadow of a level-one dressing at the stage the class-four solve consumes.  Three
results carry the weight.

* **The translation identity on the whole frame** (`sqRelWord_conFourDress`): a five-slot
  `γ₃`-dressing moves the relator by an explicit `γ₃`-element: the two class-three rows
  move by the Frobenius weights `(−4, 2)` on the exponent slots alone, and the class-four
  row by `−4·(z 1).j + 2·(z 2).j` plus the pairing form `conFourShift`, **the class-four
  graded Fox form**: each slot's `(h, i)`-data paired against the *permuted* letter's
  outermost abelian columns `(d, a)`: the σ-slot against the `x₀`-letter, the `x₀`-slot
  against `10·x₀ − σ − 8·x₁` (the σ-letter mod 2), the `x₁`-slot against itself, and each
  handle against the opposite handle letter.  This extends the committed four-slot
  `sqRelWord_selLift` to the full frame including the σ-slot, and is the exact
  transposition of `GradedVanish`'s five-slot `γ₂`-action one level up.
* **The pure-artefact containment** (`sqRelWord_conFourDress_of_rel`, `conFour_contain_odd`,
  `conFour_contain_odd'`, `conFour_contain_even`, `conFourDress_conFourDress_inv`): at a
  frame where the relator DIES, the defect of any `γ₃`-`K`-dressed frame is central and
  reads the dressing alone through the Fox form: `R(m·z) = liftC (−4·z₁.j + 2·z₂.j + Φ)`
  once the two Frobenius rows vanish (the stage-three survival condition, and the only
  obstruction).  The residue is therefore in the containment target by construction, and
  the kills are exhibited: the inverse dressing restores the solution unconditionally; one
  committed engine move kills the dressed frame at any unit-pairing point (odd regime,
  arbitrary residue), and at any `2`-pairing point when the residue is even (even regime),
  the live hypotheses carried exactly where consumed, as in the committed class-three
  containment.
* **The even-regime obstruction** (`selLamThree_pair_even`, `selLamThree_pair_even'`,
  `sqRelWord_selLift_ne_one`): where the four odd-capable generator pairings of `Λ₃` are
  even on both handle slots, every achievable increment is even, so a survivor with an
  **odd** class-four residue outlives every achievable engine refinement.  This commits
  the even-regime converse that `GradedLift` §3 recorded as measured-not-proved, in the
  `Λ₃`-restricted form, and makes the degenerate corners provable dead ends of the engine.

The witness section instantiates all of it on the committed class-four witness
`selLiftWit`: the **tenth row in closed form** (`sqRelWord_selLiftWit_j`, the row
`GradedFour`'s scope note deferred; hypothesis-free, an odd core of seven terms plus twice
an explicit bookkeeping half), the gate corollary (`sqRelWord_selLiftWit_liftC`), ⭐ **the
class-four selection bit at the witness** (`selLiftWit_bit`): the parity of the class-four
residue is `(A·C·F + B·D·E)·T + P·R`, consuming only the `(c, d)`-parity row `hg`, and the
odd-regime completions through the three generator pairings the committed
`selLiftWit_complete_odd` (which uses `κ₄ = B·D·F`) does not cover: `B·C·E`, `A·D·F`, and
the mirror `A·C·E` (`selLiftWit_complete_odd_bce`, `_adf`, `_ace`).

## Honest scope

The containment is committed here along the `γ₃`-dressing torsor of a class-four solution
and at the witness under the live hypotheses; the whole-binder unconditional form is
**false for the bare witness through the achievable engine**, and this is measured
exactly (`scripts/w53_contain/`, `results/w53gate.txt`): of the binder points on the
`8^8`-grid of column tuples, `737280` have an odd witness `j`-row but only `196608` of
them carry an odd achievable pairing; among the `1806336` points where the bare witness
survives stage 3, `131072` have odd residue and only `16384` of those are covered; at the
uncovered corners (all eight generator pairings even, e.g. `(A,…,S) = (0,1,1,1,2,0,2,0)`)
the obstruction theorem PROVES the engine is stuck.  The containment along the honest
tower at such corners must route through `γ₂`-level moves or a different stage-three
completion, which is exactly the located remaining gap: the `γ₂`-torsor transport of the
class-four residue.  The stage-three completion moves themselves (killing the witness's
`h`- and `i`-rows) are likewise out of scope here: the gate corollary carries them as
hypotheses, and the `i`-row's parity `C·F·T` shows the witness needs a `γ₂`-move to reach
stage 3 at `C·F·T`-odd points, which no `γ₃`-dressing supplies (their `i`-increment
`−4·z₁.i + 2·z₂.i` is even).

## Contents

* **§1** the `γ₃`-calculus on `SqU5`: commutation, conjugation, the handle-product lemmas;
* **§2** ⭐⭐ the five-slot dressing `conFourDress`, the class-four graded Fox form
  `conFourShift`, the core identity `sqWord_mul_gaThree` and the translation identity
  `sqRelWord_conFourDress`, with the row corollaries and the torsor identity;
* **§3** ⭐⭐ the pure-artefact containment at a relator-solution: the defect form, the
  stage-survival reduction, the two-regime kills;
* **§3b** ⭐ the `Λ₃`-parity engine and the even-regime obstruction;
* **§4** ⭐⭐ the witness: the tenth row, the gate, the class-four selection bit, the new
  odd-regime completions, and concrete instances including a provable engine dead end;
* **§5** committed axiom prints (all std-3).

Companion scripts: `scripts/w53_contain/` (`w53_shift.m`: the symbolic validation of the
translation identity at `h = 1, 2` and of the witness rows; `w53_gate.m`: the whole-binder
coverage census and the closed-form checks; `w53_inst.m`: the concrete instances),
committed outputs under `results/`.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The `γ₃`-calculus on `SqU5`

A `γ₃`-shaped element commutes with everything whose outermost abelian columns vanish,
conjugation moves it only in the class-four coordinate (by the pairing of its `(h, i)`-data
against the conjugator's outermost columns), and a product of commutators dressed pairwise
by `γ₃`-elements is the undressed product times one central translation.  These facts are
the whole engine of §2. -/

section GaThreeCalculus

variable {R : Type} [CommRing R]

/-- A `γ₃`-element commutes with anything whose outermost abelian columns `(a, d)` vanish:
the only obstruction to centrality of `γ₃` is the class-four pairing, and that reads only
`a` and `d`. -/
theorem gaThree_mul_comm {z p : SqU5 R} (hz : z.IsGaThree) (ha : p.a = 0) (hd : p.d = 0) :
    z * p = p * z := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hz
  ext <;> simp only [SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d, SqU5.mul_e, SqU5.mul_f,
    SqU5.mul_g, SqU5.mul_h, SqU5.mul_i, SqU5.mul_j, h1, h2, h3, h4, h5, h6, h7, ha, hd] <;>
    ring

/-- **Conjugation moves a `γ₃`-element centrally**: by the pairing of its `(h, i)`-data
against the conjugator's outermost abelian columns. -/
theorem conjP_gaThree {z : SqU5 R} (hz : z.IsGaThree) (g : SqU5 R) :
    conjP z g = z * liftC (g.d * z.h - g.a * z.i) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hz
  ext <;> simp only [conjP, liftC, SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d,
    SqU5.mul_e, SqU5.mul_f, SqU5.mul_g, SqU5.mul_h, SqU5.mul_i, SqU5.mul_j, SqU5.inv_a,
    SqU5.inv_b, SqU5.inv_c, SqU5.inv_d, SqU5.inv_e, SqU5.inv_f, SqU5.inv_g, SqU5.inv_h,
    SqU5.inv_i, SqU5.inv_j, h1, h2, h3, h4, h5, h6, h7] <;> ring

/-- The `a`-coordinate of a product list vanishes when every factor's does. -/
private theorem prod_a_eq_zero : ∀ l : List (SqU5 R), (∀ p ∈ l, p.a = 0) → l.prod.a = 0
  | [], _ => rfl
  | p :: l, hl => by
    rw [List.prod_cons, SqU5.mul_a, hl p (by simp),
      prod_a_eq_zero l fun q hq => hl q (by simp [hq]), add_zero]

/-- …and likewise the `d`-coordinate. -/
private theorem prod_d_eq_zero : ∀ l : List (SqU5 R), (∀ p ∈ l, p.d = 0) → l.prod.d = 0
  | [], _ => rfl
  | p :: l, hl => by
    rw [List.prod_cons, SqU5.mul_d, hl p (by simp),
      prod_d_eq_zero l fun q hq => hl q (by simp [hq]), add_zero]

/-- The handle word has no `a`-column: commutators do not. -/
theorem handleWord_a {h : ℕ} (u v : Fin h → SqU5 R) : (handleWord u v).a = 0 :=
  prod_a_eq_zero _ fun p hp => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
    exact SqU5.commP_a _ _

/-- …and no `d`-column. -/
theorem handleWord_d {h : ℕ} (u v : Fin h → SqU5 R) : (handleWord u v).d = 0 :=
  prod_d_eq_zero _ fun p hp => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
    exact SqU5.commP_d _ _

/-- Central right factors of a product of two dressed factors collect. -/
private theorem mul_liftC_mul_liftC (a b : SqU5 R) (w v : R) :
    (a * liftC w) * (b * liftC v) = a * b * liftC (w + v) := by
  rw [mul_assoc, ← mul_assoc (liftC w), ← liftC_comm, mul_assoc, liftC_mul_liftC,
    ← mul_assoc]

/-- **The handle block swallows an all-pair `γ₃`-dressing centrally**: dressing every
handle pair by `γ₃`-elements multiplies `handleWord` by one central translation, the sum
of the committed per-pair pairings of `commP_mul_gaThree`. -/
theorem handleWord_mul_gaThree_all : ∀ (n : ℕ) (u v zu zv : Fin n → SqU5 R),
    (∀ k, (zu k).IsGaThree) → (∀ k, (zv k).IsGaThree) →
    handleWord (fun k => u k * zu k) (fun k => v k * zv k)
      = handleWord u v
        * liftC (∑ k : Fin n, (((zu k).h * (v k).d - (zu k).i * (v k).a)
            + ((u k).a * (zv k).i - (u k).d * (zv k).h)))
  | 0, u, v, zu, zv, _, _ => by
    simp [handleWord]
  | n + 1, u, v, zu, zv, hzu, hzv => by
    have htail := handleWord_mul_gaThree_all n (fun k => u k.succ) (fun k => v k.succ)
      (fun k => zu k.succ) (fun k => zv k.succ) (fun k => hzu _) (fun k => hzv _)
    rw [handleWord, handleWord] at htail ⊢
    rw [List.finRange_succ, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
      List.map_map, List.map_map]
    have hL : (List.finRange n).map ((fun k => commP (u k * zu k) (v k * zv k)) ∘ Fin.succ)
        = (List.finRange n).map fun k => commP (u k.succ * zu k.succ) (v k.succ * zv k.succ) :=
      List.map_congr_left fun k _ => rfl
    have hR : (List.finRange n).map ((fun k => commP (u k) (v k)) ∘ Fin.succ)
        = (List.finRange n).map fun k => commP (u k.succ) (v k.succ) :=
      List.map_congr_left fun k _ => rfl
    rw [hL, hR, htail, commP_mul_gaThree _ _ (hzu 0) (hzv 0), mul_liftC_mul_liftC,
      Fin.sum_univ_succ]

end GaThreeCalculus

/-! ## §2 The five-slot `γ₃`-dressing and ⭐⭐ the translation identity

The `K`-dressing of the class-four stage dresses **every** slot: the committed `selLift`
reaches the two exponent slots (by `γ₄`) and one handle pair (by `γ₃`), but the graded Fox
form of the defect reads all `3 + 2h` Fox rows, σ-slot included.  `conFourDress` multiplies
every slot on the right by its own `γ₃`-dressing; the relator then moves by the explicit
`γ₃`-element of `sqRelWord_conFourDress`: Frobenius weights `(−4, 2)` on the two exponent
slots in the class-three rows, and in the class-four row the affine pairing form
`conFourShift`, whose coefficients are the *permuted* letters' outermost abelian columns:

* the σ-slot pairs against the `x₀`-letter,
* the `x₀`-slot against `10·x₀ − σ − 8·x₁`, which is the σ-letter mod 2,
* the `x₁`-slot against the `x₁`-letter itself,
* each handle slot against the opposite handle letter, in the `selLift` orientation.

This is the class-four instance of the memo's graded Fox form `δ(z) = Σᵢ [zᵢ, βᵢ] + F(z)`
with `βᵢ` the Fox rows (the marking letters `(σ x₀)(u v)`-permuted) and the Frobenius on
the exponent slots, one level above the committed `GradedVanish` instance, and it was
validated symbolically before transcription (`scripts/w53_contain/w53_shift.m`: zero
mismatches in all ten rows at `h = 1` and `h = 2` over `ℤ[m, z]`). -/

section DressAction

variable {R : Type} [CommRing R] {h : ℕ}

/-- **The five-slot `γ₃`-dressing** of a frame: every slot multiplied on the right by its
own dressing element, the class-four `K`-dressing shape. -/
def conFourDress (m z : Fin (sqRank h) → SqU5 R) : Fin (sqRank h) → SqU5 R :=
  fun i => m i * z i

@[simp] theorem conFourDress_apply (m z : Fin (sqRank h) → SqU5 R) (i : Fin (sqRank h)) :
    conFourDress m z i = m i * z i := rfl

variable (h) in
/-- **The class-four graded Fox form**: the amount by which the class-four residue moves
under a five-slot `γ₃`-dressing, beyond the Frobenius part `−4·(z 1).j + 2·(z 2).j`.  Each
slot's `(h, i)`-data pairs against the permuted letter's outermost abelian columns
`(d, a)`: σ against the `x₀`-letter, `x₀` against `10·x₀ − σ − 8·x₁` (the σ-letter mod 2),
`x₁` against itself, handles crosswise in the committed `selLift` orientation. -/
def conFourShift (m z : Fin (sqRank h) → SqU5 R) : R :=
  ((m 1).d * (z 0).h - (m 1).a * (z 0).i)
    + ((10 * (m 1).d - (m 0).d - 8 * (m 2).d) * (z 1).h
      - (10 * (m 1).a - (m 0).a - 8 * (m 2).a) * (z 1).i)
    + ((m 2).d * (z 2).h - (m 2).a * (z 2).i)
    + ∑ j : Fin h,
        (((z (sqHandleIdxU j)).h * (m (sqHandleIdxV j)).d
            - (z (sqHandleIdxU j)).i * (m (sqHandleIdxV j)).a)
          + ((m (sqHandleIdxU j)).a * (z (sqHandleIdxV j)).i
            - (m (sqHandleIdxU j)).d * (z (sqHandleIdxV j)).h))

/-- ⭐ **The core word under `γ₃`-dressings of its three slots**: the two class-three rows
pick up the Frobenius weights, and the class-four row the core block of the Fox form.  No
closed form of the word is consumed: componentwise expansion. -/
theorem sqWord_mul_gaThree {z₀ z₁ z₂ : SqU5 R} (s x y : SqU5 R) (h₀ : z₀.IsGaThree)
    (h₁ : z₁.IsGaThree) (h₂ : z₂.IsGaThree) :
    sqWord (s * z₀) (x * z₁) (y * z₂)
      = sqWord s x y * ⟨0, 0, 0, 0, 0, 0, 0, -4 * z₁.h + 2 * z₂.h, -4 * z₁.i + 2 * z₂.i,
          -4 * z₁.j + 2 * z₂.j
            + ((x.d * z₀.h - x.a * z₀.i)
              + ((10 * x.d - s.d - 8 * y.d) * z₁.h - (10 * x.a - s.a - 8 * y.a) * z₁.i)
              + (y.d * z₂.h - y.a * z₂.i))⟩ := by
  obtain ⟨h₀a, h₀b, h₀c, h₀d, h₀e, h₀f, h₀g⟩ := h₀
  obtain ⟨h₁a, h₁b, h₁c, h₁d, h₁e, h₁f, h₁g⟩ := h₁
  obtain ⟨h₂a, h₂b, h₂c, h₂d, h₂e, h₂f, h₂g⟩ := h₂
  ext <;> simp only [sqWord, conjP, commP, pow_succ, pow_zero, one_mul,
    SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d, SqU5.mul_e, SqU5.mul_f, SqU5.mul_g,
    SqU5.mul_h, SqU5.mul_i, SqU5.mul_j, SqU5.inv_a, SqU5.inv_b, SqU5.inv_c, SqU5.inv_d,
    SqU5.inv_e, SqU5.inv_f, SqU5.inv_g, SqU5.inv_h, SqU5.inv_i, SqU5.inv_j,
    h₀a, h₀b, h₀c, h₀d, h₀e, h₀f, h₀g, h₁a, h₁b, h₁c, h₁d, h₁e, h₁f, h₁g,
    h₂a, h₂b, h₂c, h₂d, h₂e, h₂f, h₂g] <;> ring

variable {m z : Fin (sqRank h) → SqU5 R}

/-- A five-slot `γ₃`-dressing leaves all four abelian columns of every slot unchanged. -/
theorem conFourDress_abcd (hz : ∀ i, (z i).IsGaThree) (i : Fin (sqRank h)) :
    (conFourDress m z i).a = (m i).a ∧ (conFourDress m z i).b = (m i).b
      ∧ (conFourDress m z i).c = (m i).c ∧ (conFourDress m z i).d = (m i).d :=
  ⟨by simp [(hz i).1], by simp [(hz i).2.1], by simp [(hz i).2.2.1],
    by simp [(hz i).2.2.2.1]⟩

/-- ⭐⭐ **The translation identity on the whole frame** (the class-four graded Fox form of
the `K`-dressing action): a five-slot `γ₃`-dressing moves the relator by the explicit
`γ₃`-element with Frobenius `(−4, 2)`-rows and the Fox pairing form in the class-four row.
Every class-`≤ 2` row is untouched.  No closed form of the relator is consumed: the core
slots are componentwise, the handle block is the §1 product lemma, and the two blocks
interact only through the handle word's vanishing outermost columns. -/
theorem sqRelWord_conFourDress (hz : ∀ i, (z i).IsGaThree) :
    sqRelWord (conFourDress m z)
      = sqRelWord m * ⟨0, 0, 0, 0, 0, 0, 0, -4 * (z 1).h + 2 * (z 2).h,
          -4 * (z 1).i + 2 * (z 2).i,
          -4 * (z 1).j + 2 * (z 2).j + conFourShift h m z⟩ := by
  have hhand : handleWord (fun k => m (sqHandleIdxU k) * z (sqHandleIdxU k))
      (fun k => m (sqHandleIdxV k) * z (sqHandleIdxV k))
      = handleWord (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
        * liftC (∑ k : Fin h, (((z (sqHandleIdxU k)).h * (m (sqHandleIdxV k)).d
            - (z (sqHandleIdxU k)).i * (m (sqHandleIdxV k)).a)
          + ((m (sqHandleIdxU k)).a * (z (sqHandleIdxV k)).i
            - (m (sqHandleIdxU k)).d * (z (sqHandleIdxV k)).h))) :=
    handleWord_mul_gaThree_all h _ _ _ _ (fun k => hz _) (fun k => hz _)
  rw [sqRelWord, sqRelWord]
  simp only [conFourDress_apply]
  rw [sqWord_mul_gaThree (m 0) (m 1) (m 2) (hz 0) (hz 1) (hz 2), hhand, mul_liftC_apply]
  ext <;> simp only [conFourShift, SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d,
    SqU5.mul_e, SqU5.mul_f, SqU5.mul_g, SqU5.mul_h, SqU5.mul_i, SqU5.mul_j,
    handleWord_a, handleWord_d] <;> ring

/-- The two class-three rows of the dressed relator move by the Frobenius action alone. -/
theorem sqRelWord_conFourDress_h (hz : ∀ i, (z i).IsGaThree) :
    (sqRelWord (conFourDress m z)).h = (sqRelWord m).h + (-4 * (z 1).h + 2 * (z 2).h) := by
  rw [sqRelWord_conFourDress hz, SqU5.mul_h]
  ring

/-- …and the second likewise. -/
theorem sqRelWord_conFourDress_i (hz : ∀ i, (z i).IsGaThree) :
    (sqRelWord (conFourDress m z)).i = (sqRelWord m).i + (-4 * (z 1).i + 2 * (z 2).i) := by
  rw [sqRelWord_conFourDress hz, SqU5.mul_i]
  ring

/-- ⭐ **The class-four row of the dressed relator**: the Frobenius part, the Fox form, and
one cross term reading the relator's own `a`-row against the dressing's Frobenius
`i`-part, which dies on any class-two-admissible frame. -/
theorem sqRelWord_conFourDress_j (hz : ∀ i, (z i).IsGaThree) :
    (sqRelWord (conFourDress m z)).j
      = (sqRelWord m).j + (-4 * (z 1).j + 2 * (z 2).j + conFourShift h m z)
        + (sqRelWord m).a * (-4 * (z 1).i + 2 * (z 2).i) := by
  rw [sqRelWord_conFourDress hz, SqU5.mul_j]
  ring

/-- **The `K`-dressing torsor is a torsor**: the pointwise inverse dressing restores the
frame.  At a solution this is the containment in the full dressing action's image,
unconditionally: the defect of a dressed solution is killed by the inverse dressing. -/
theorem conFourDress_conFourDress_inv (m z : Fin (sqRank h) → SqU5 R) :
    conFourDress (conFourDress m z) (fun i => (z i)⁻¹) = m := by
  funext i
  rw [conFourDress_apply, conFourDress_apply, mul_assoc, mul_inv_cancel, mul_one]

end DressAction

/-! ## §3 ⭐⭐ The pure-artefact containment at a relator-solution

The vanish note's located mechanism, as theorems: at a frame `m` where the relator dies,
the relator's value at any `γ₃`-`K`-dressed frame `m·z` is a **pure dressing artefact**: it
is the explicit `γ₃`-element of the translation identity, reading only the dressing and
the frame's level-one columns.  Once the two Frobenius rows of the dressing vanish (the
stage-three survival condition, and the only obstruction), the defect is central with
residue `−4·(z 1).j + 2·(z 2).j + conFourShift m z`, and the committed engine kills it:

* **odd regime** (`conFour_contain_odd`, mirror `conFour_contain_odd'`): at any unit
  pairing witness against the `V`-slot (resp. `U`-slot) columns of the *solution* (the
  dressing does not move columns), one explicit handle-`γ₃` move kills the dressed frame,
  for **every** `K`-dressing `z`, with no hypothesis on the residue;
* **even regime** (`conFour_contain_even`): at a `2`-pairing witness, the same one-move
  kill whenever the artefact residue is even, the evenness exhibited.

The tautological kill by the inverse dressing (`conFourDress_conFourDress_inv`) needs no
live hypothesis at all; the engine kills matter because they stay inside the committed
achievable move set of one handle pair. -/

section ArtefactContainment

variable {R : Type} [CommRing R] {h : ℕ} {j : Fin h} {m z : Fin (sqRank h) → SqU5 R}

/-- ⭐⭐ **The defect of a `K`-dressed frame of the relator is a pure dressing artefact**:
at a relator-solution the dressed relator IS the translation `γ₃`-element: the Frobenius
rows of the dressing and the class-four Fox form.  Nothing about `m` beyond its solution
property and its level-one columns enters. -/
theorem sqRelWord_conFourDress_of_rel (hz : ∀ i, (z i).IsGaThree)
    (hm : sqRelWord m = 1) :
    sqRelWord (conFourDress m z)
      = ⟨0, 0, 0, 0, 0, 0, 0, -4 * (z 1).h + 2 * (z 2).h, -4 * (z 1).i + 2 * (z 2).i,
          -4 * (z 1).j + 2 * (z 2).j + conFourShift h m z⟩ := by
  rw [sqRelWord_conFourDress hz, hm, one_mul]

/-- **Stage-three survival of a dressed solution is exactly the vanishing of the two
Frobenius rows**, and then the defect is central with the artefact residue. -/
theorem sqRelWord_conFourDress_liftC (hz : ∀ i, (z i).IsGaThree) (hm : sqRelWord m = 1)
    (hh : -4 * (z 1).h + 2 * (z 2).h = 0) (hi : -4 * (z 1).i + 2 * (z 2).i = 0) :
    sqRelWord (conFourDress m z)
      = liftC (-4 * (z 1).j + 2 * (z 2).j + conFourShift h m z) := by
  rw [sqRelWord_conFourDress_of_rel hz hm]
  exact SqU5.IsGaFour.eq_liftC ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hh, hi⟩

/-- ⭐⭐ **The containment through the engine, odd regime**: at a solution whose `j`-handle
`V`-columns admit a unit pairing, EVERY stage-surviving `γ₃`-`K`-dressed frame is killed by
one explicit achievable engine move, whatever its residue.  The pairing hypothesis reads
the solution's own columns; the dressing cannot move them. -/
theorem conFour_contain_odd {zh zi rr : R} (hz : ∀ i, (z i).IsGaThree)
    (hm : sqRelWord m = 1)
    (hh : -4 * (z 1).h + 2 * (z 2).h = 0) (hi : -4 * (z 1).i + 2 * (z 2).i = 0)
    (hmu : rr * (zh * (m (sqHandleIdxV j)).d - zi * (m (sqHandleIdxV j)).a) = 1) :
    sqRelWord (selLift j (conFourDress m z) 1 1
      ⟨0, 0, 0, 0, 0, 0, 0,
        -(rr * (-4 * (z 1).j + 2 * (z 2).j + conFourShift h m z) * zh),
        -(rr * (-4 * (z 1).j + 2 * (z 2).j + conFourShift h m z) * zi), 0⟩ 1) = 1 := by
  refine sqRelWord_selLift_eq_one_odd (sqRelWord_conFourDress_liftC hz hm hh hi) ?_
  rw [(conFourDress_abcd hz (sqHandleIdxV j)).2.2.2, (conFourDress_abcd hz (sqHandleIdxV j)).1]
  exact hmu

/-- ⭐⭐ …the mirror odd-regime containment, through the `V`-handle slot against the
`U`-slot columns. -/
theorem conFour_contain_odd' {zh zi rr : R} (hz : ∀ i, (z i).IsGaThree)
    (hm : sqRelWord m = 1)
    (hh : -4 * (z 1).h + 2 * (z 2).h = 0) (hi : -4 * (z 1).i + 2 * (z 2).i = 0)
    (hmu : rr * ((m (sqHandleIdxU j)).a * zi - (m (sqHandleIdxU j)).d * zh) = 1) :
    sqRelWord (selLift j (conFourDress m z) 1 1 1
      ⟨0, 0, 0, 0, 0, 0, 0,
        -(rr * (-4 * (z 1).j + 2 * (z 2).j + conFourShift h m z) * zh),
        -(rr * (-4 * (z 1).j + 2 * (z 2).j + conFourShift h m z) * zi), 0⟩) = 1 := by
  refine sqRelWord_selLift_eq_one_odd' (sqRelWord_conFourDress_liftC hz hm hh hi) ?_
  rw [(conFourDress_abcd hz (sqHandleIdxU j)).1, (conFourDress_abcd hz (sqHandleIdxU j)).2.2.2]
  exact hmu

/-- ⭐⭐ **The containment through the engine, even regime**: at a `2`-pairing witness, a
stage-surviving `K`-dressed frame with an **even** artefact residue (the half exhibited) is
killed by one explicit engine move: the class-four transposition of the committed
class-three containment's completion step. -/
theorem conFour_contain_even {zh zi rr res : R} (hz : ∀ i, (z i).IsGaThree)
    (hm : sqRelWord m = 1)
    (hh : -4 * (z 1).h + 2 * (z 2).h = 0) (hi : -4 * (z 1).i + 2 * (z 2).i = 0)
    (hres : -4 * (z 1).j + 2 * (z 2).j + conFourShift h m z = 2 * res)
    (hmu : rr * (zh * (m (sqHandleIdxV j)).d - zi * (m (sqHandleIdxV j)).a) = 2) :
    sqRelWord (selLift j (conFourDress m z) 1 1
      ⟨0, 0, 0, 0, 0, 0, 0, -(rr * res * zh), -(rr * res * zi), 0⟩ 1) = 1 := by
  refine sqRelWord_selLift_eq_one (res := res) ?_ ?_
  · rw [sqRelWord_conFourDress_liftC hz hm hh hi, hres]
  · rw [(conFourDress_abcd hz (sqHandleIdxV j)).2.2.2, (conFourDress_abcd hz (sqHandleIdxV j)).1]
    exact hmu

end ArtefactContainment

/-! ## §3b ⭐ The `Λ₃`-parity engine and the even-regime obstruction

The class-four analogue of `GradedSelect` §5b's parity engine, in the form the containment
needs: a `Λ₃`-achievable `(h, i)`-pair pairs **evenly** against any column pair at which
the four odd-capable generator pairings are even, because the three remaining generators
are explicit `2`-multiples.  Consequently, at a marking where all eight generator pairings
(four per handle slot) are even, every achievable engine increment is even, and a survivor
with an odd class-four residue outlives every achievable refinement: the even-regime
selection converse that `GradedLift` §3 recorded as measured, committed here in the
`Λ₃`-restricted form. -/

section ParityObstruction

variable {h : ℕ} {j : Fin h}

/-- ⭐ **`Λ₃` pairs evenly against a column pair with even generator pairings** (the
`U`-slot orientation `z.h·d − z.i·a`): the four odd-capable generator pairings even force
every achievable pairing even; the three `2`-multiple generators contribute evenly
outright. -/
theorem selLamThree_pair_even {A B C D E F T S P Q R va vd : gr3R} {z : SqU5 gr3R}
    (hz : selLamThree A B C D E F T S P Q R z)
    (h₁ : ∃ k, (2 * (A * C)) * vd + (C * E) * va = 2 * k)
    (h₂ : ∃ k, (A * D + B * C) * vd + (D * E) * va = 2 * k)
    (h₃ : ∃ k, (A * D + B * C) * vd + (C * F) * va = 2 * k)
    (h₄ : ∃ k, (2 * (B * D)) * vd + (D * F) * va = 2 * k) :
    ∃ k, z.h * vd - z.i * va = 2 * k := by
  obtain ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, hzh, hzi⟩ := hz
  obtain ⟨k₁, hk₁⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  obtain ⟨k₃, hk₃⟩ := h₃
  obtain ⟨k₄, hk₄⟩ := h₄
  refine ⟨-(r₁ * k₁) - r₂ * k₂ - r₃ * k₃ - r₄ * k₄
    + (r₆ * ((Q * A - P * C) * vd - (R * T - Q * E) * va)
      + r₇ * ((Q * B - P * D) * vd - (R * S - Q * F) * va))
    - r₅ * (R * va), ?_⟩
  rw [hzh, hzi]
  linear_combination (-r₁) * hk₁ - r₂ * hk₂ - r₃ * hk₃ - r₄ * hk₄

/-- ⭐ …and the mirror orientation `a·z.i − d·z.h` of the `V`-slot increment. -/
theorem selLamThree_pair_even' {A B C D E F T S P Q R ua ud : gr3R} {z : SqU5 gr3R}
    (hz : selLamThree A B C D E F T S P Q R z)
    (h₁ : ∃ k, ua * (C * E) + ud * (2 * (A * C)) = 2 * k)
    (h₂ : ∃ k, ua * (D * E) + ud * (A * D + B * C) = 2 * k)
    (h₃ : ∃ k, ua * (C * F) + ud * (A * D + B * C) = 2 * k)
    (h₄ : ∃ k, ua * (D * F) + ud * (2 * (B * D)) = 2 * k) :
    ∃ k, ua * z.i - ud * z.h = 2 * k := by
  obtain ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, hzh, hzi⟩ := hz
  obtain ⟨k₁, hk₁⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  obtain ⟨k₃, hk₃⟩ := h₃
  obtain ⟨k₄, hk₄⟩ := h₄
  refine ⟨r₁ * k₁ + r₂ * k₂ + r₃ * k₃ + r₄ * k₄
    + (r₅ * (ua * R)
      + r₆ * (ua * (R * T - Q * E) - ud * (Q * A - P * C))
      + r₇ * (ua * (R * S - Q * F) - ud * (Q * B - P * D))), ?_⟩
  rw [hzh, hzi]
  linear_combination r₁ * hk₁ + r₂ * hk₂ + r₃ * hk₃ + r₄ * hk₄

/-- ⭐⭐ **The even-regime obstruction**: a class-four residue of **odd** parity outlives
every achievable engine refinement, at any marking where the eight generator pairings are
even.  The refinement's increment is even (`γ₄`-exponent moves are even outright; the
handle moves by the parity lemmas), so it cannot cancel the odd residue: the committed
converse of the even-regime completion, and the exact class-four transposition of
`GradedSelect.sqRelWord_selRefine_ne_one`. -/
theorem sqRelWord_selLift_ne_one {A B C D E F T S P Q R : gr3R}
    {m : Fin (sqRank h) → SqU5 gr3R} {w₁ w₂ z₃ z₄ : SqU5 gr3R}
    (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour) (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (hz₃L : selLamThree A B C D E F T S P Q R z₃)
    (hz₄L : selLamThree A B C D E F T S P Q R z₄)
    (h₁ : ∃ k, (2 * (A * C)) * (m (sqHandleIdxV j)).d
        + (C * E) * (m (sqHandleIdxV j)).a = 2 * k)
    (h₂ : ∃ k, (A * D + B * C) * (m (sqHandleIdxV j)).d
        + (D * E) * (m (sqHandleIdxV j)).a = 2 * k)
    (h₃ : ∃ k, (A * D + B * C) * (m (sqHandleIdxV j)).d
        + (C * F) * (m (sqHandleIdxV j)).a = 2 * k)
    (h₄ : ∃ k, (2 * (B * D)) * (m (sqHandleIdxV j)).d
        + (D * F) * (m (sqHandleIdxV j)).a = 2 * k)
    (h₁' : ∃ k, (m (sqHandleIdxU j)).a * (C * E)
        + (m (sqHandleIdxU j)).d * (2 * (A * C)) = 2 * k)
    (h₂' : ∃ k, (m (sqHandleIdxU j)).a * (D * E)
        + (m (sqHandleIdxU j)).d * (A * D + B * C) = 2 * k)
    (h₃' : ∃ k, (m (sqHandleIdxU j)).a * (C * F)
        + (m (sqHandleIdxU j)).d * (A * D + B * C) = 2 * k)
    (h₄' : ∃ k, (m (sqHandleIdxU j)).a * (D * F)
        + (m (sqHandleIdxU j)).d * (2 * (B * D)) = 2 * k)
    (hodd : selPar (sqRelWord m).j = 1) :
    sqRelWord (selLift j m w₁ w₂ z₃ z₄) ≠ 1 := by
  obtain ⟨k₃, hk₃⟩ := selLamThree_pair_even hz₃L h₁ h₂ h₃ h₄
  obtain ⟨k₄, hk₄⟩ := selLamThree_pair_even' hz₄L h₁' h₂' h₃' h₄'
  intro hc
  rw [sqRelWord_selLift hw₁ hw₂ hz₃ hz₄, mul_liftC_apply] at hc
  have hj : (sqRelWord m).j
      + (-4 * w₁.j + 2 * w₂.j
        + ((z₃.h * (m (sqHandleIdxV j)).d - z₃.i * (m (sqHandleIdxV j)).a)
          + ((m (sqHandleIdxU j)).a * z₄.i - (m (sqHandleIdxU j)).d * z₄.h))) = 0 :=
    congrArg SqU5.j hc
  have hval : (sqRelWord m).j = 2 * (2 * w₁.j - w₂.j - k₃ - k₄) := by
    linear_combination hj - hk₃ - hk₄
  have hpar := congrArg selPar hval
  rw [selPar_two_mul] at hpar
  rw [hpar] at hodd
  exact absurd hodd (by decide)

end ParityObstruction

/-! ## §4 ⭐⭐ The witness: the tenth row, the gate, the bit, and the completions

`GradedLift` §4 computed nine of the ten relator rows of the class-four witness
`selLiftWit` and left the tenth as "the engine's target".  Here it is, in closed form with
**no hypotheses**: an odd core of seven terms plus twice the bookkeeping half
`selLiftWitJEven` (`sqRelWord_selLiftWit_j`; validated against honest group collection at
400 random binder points, `w53_gate.m`).  Consequences:

* **the gate** (`sqRelWord_selLiftWit_liftC`): where the four parity rows hold and the two
  committed class-three residues die, the witness relator is central with the closed-form
  residue: the class-four gate at the witness, the stage-three state carried as hypotheses
  exactly where the numerics say it is not free;
* ⭐ **the class-four selection bit at the witness** (`selLiftWit_bit`): the residue parity
  is `(A·C·F + B·D·E)·T + P·R`, consuming only the `(c, d)`-parity row `hg`.  The
  class-three bit `B·C·(T+S)` read only level-one columns; the class-four bit reads the
  halves `P`, `R`: one level deeper, exactly the vanish note's mod-2 hierarchy;
* **the odd-regime completions** for the generator pairings the committed
  `selLiftWit_complete_odd` (`κ₄ = B·D·F`) does not reach: `B·C·E` and `A·D·F` through the
  `U`-slot, and the mirror `κ₄' = A·C·E` through the `V`-slot. -/

section Witness

variable {h : ℕ} {j : Fin h} {A B C D E F T S P Q R W2 : gr3R}

variable (A B C D E F T S P R) in
/-- **The bookkeeping half of the witness's class-four residue**: the even part of the
tenth row, exhibited.  Mod 2 it is invisible; the odd core of `sqRelWord_selLiftWit_j`
carries the whole selection content.  (`Q` does not occur: the tenth row never reads the
`x₁`-slot's second class-two half.) -/
def selLiftWitJEven : gr3R :=
  A * C * (E * S ^ 3 * (3 - 10 * T) + F * T * S * (10 * T * S - 3 * S - 2))
    + A * D * (E * T * S ^ 2 * (-(10 * S) - 3) + F * T ^ 2 * S * (10 * S + 3))
    + A * S * R
    + B * C * (E * T * S ^ 2 * (10 * T + 20 * S - 3)
      + F * T * (-(10 * T ^ 2 * S) - 20 * T * S ^ 2 + 3 * T * S + 2 * T + 4 * S))
    + B * D * (E * T * S * (-(10 * T * S) + 3 * T - 4) + F * T ^ 3 * (10 * S - 3))
    + B * T * R * (8 * S - 1) + C * F * P - D * E * P

/-- ⭐⭐ **The tenth row of the class-four witness, in closed form**: the relator's
class-four coordinate at `selLiftWit` is the seven-term odd core
`A·C·F·(T+S) + B·(C·F·S + D·E·T) − (A+B)·D·E·S + P·R` plus twice the bookkeeping half.
No hypotheses: a polynomial identity on the whole binder, the tenth row `GradedFour`'s
scope note deferred, and the class-four analogue of the committed `sqRelWord_selConWit`
`f`-row one level up. -/
theorem sqRelWord_selLiftWit_j :
    (sqRelWord (selLiftWit h j A B C D E F T S P Q R)).j
      = A * C * F * (T + S) + B * (C * F * S + D * E * T) - (A + B) * (D * E * S) + P * R
        + 2 * selLiftWitJEven A B C D E F T S P R := by
  have hone : ∀ j' : Fin h, j' ≠ j →
      commP (selLiftWit h j A B C D E F T S P Q R (sqHandleIdxU j'))
        (selLiftWit h j A B C D E F T S P Q R (sqHandleIdxV j')) = 1 := by
    intro j' hne
    rw [selLiftWit_handleU_ne hne, selLiftWit_handleV_ne hne]
    simp [commP]
  rw [sqRelWord, handleWord_eq_single _ _ j hone, SqU5.mul_j, selLiftWit_zero, selLiftWit_one,
    selLiftWit_two, selLiftWit_handleU, selLiftWit_handleV]
  simp only [selLiftWitJEven, sqWord, conjP, commP, pow_succ, pow_zero, one_mul,
    SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d, SqU5.mul_e, SqU5.mul_f, SqU5.mul_g,
    SqU5.mul_h, SqU5.mul_i, SqU5.mul_j, SqU5.inv_a, SqU5.inv_b, SqU5.inv_c, SqU5.inv_d,
    SqU5.inv_e, SqU5.inv_f, SqU5.inv_g, SqU5.inv_h, SqU5.inv_i, SqU5.inv_j]
  ring

/-- **The gate at the witness**: where the four parity rows hold and the two committed
class-three residues die, the witness relator is central with the closed-form residue.
The stage-three hypotheses `hh`, `hi` are genuine: neither row vanishes identically, and
the stage-three completion torsor is out of this file's scope (the `i`-row's parity
`C·F·T` even needs a `γ₂`-move where it is odd). -/
theorem sqRelWord_selLiftWit_liftC (hd : 2 * P + (A * S - B * T) = 0)
    (he : 2 * Q + (T * D - S * C) = 0) (hg : 2 * R + (C * F - D * E) = 0)
    (hb : 2 * W2 + (E * S - F * T) = 0)
    (hh : 4 * (P * Q) - 2 * ((A + B) * Q) + B * C * (T + S) = 0)
    (hi : 2 * (2 * (S * T * ((C + D) * W2))) - C * F * T = 0) :
    sqRelWord (selLiftWit h j A B C D E F T S P Q R)
      = liftC (A * C * F * (T + S) + B * (C * F * S + D * E * T) - (A + B) * (D * E * S)
          + P * R + 2 * selLiftWitJEven A B C D E F T S P R) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ :=
    sqRelWord_selLiftWit_isGaThree (h := h) (j := j) (W2 := W2) hd he hg hb
  have h8 : (sqRelWord (selLiftWit h j A B C D E F T S P Q R)).h = 0 := by
    rw [sqRelWord_selLiftWit_h hd he]
    exact hh
  have h9 : (sqRelWord (selLiftWit h j A B C D E F T S P Q R)).i = 0 := by
    rw [sqRelWord_selLiftWit_i (W2 := W2) hb]
    exact hi
  have hfour : (sqRelWord (selLiftWit h j A B C D E F T S P Q R)).IsGaFour :=
    ⟨g1, g2, g3, g4, g5, g6, g7, h8, h9⟩
  rw [hfour.eq_liftC, sqRelWord_selLiftWit_j]

/-- ⭐⭐ **The class-four selection bit at the witness**: the parity of the class-four
residue is `(A·C·F + B·D·E)·T + P·R`, at every binder point satisfying the `(c, d)`-parity
row; the other three rows are not consumed.  The whole difference to the displayed bit is
`(A+B)·S` times the `hg`-row plus an exhibited even term: no 𝔽₂ case analysis is needed. -/
theorem selLiftWit_bit (hg : 2 * R + (C * F - D * E) = 0) :
    selPar ((sqRelWord (selLiftWit h j A B C D E F T S P Q R)).j)
      = selPar ((A * (C * F) + B * (D * E)) * T + P * R) := by
  have hdiff : (sqRelWord (selLiftWit h j A B C D E F T S P Q R)).j
      = (A * (C * F) + B * (D * E)) * T + P * R
        + 2 * (selLiftWitJEven A B C D E F T S P R - (A + B) * (R * S)) := by
    rw [sqRelWord_selLiftWit_j]
    linear_combination ((A + B) * S) * hg
  rw [hdiff, selPar_add, selPar_two_mul, add_zero]

/-- **Odd-regime completion at the `B·C·E` pairing**: the `(−A, C)⋆U`-type generator
`(−2·A·C, C·E)` of `Λ₃` pairs to `−2·A·C·F − B·C·E` against the `V`-columns, a unit when
`B·C·E` is odd, and then any surviving residue dies by one explicit achievable `U`-slot
move.  Covers odd points the committed `κ₄ = B·D·F` completion cannot. -/
theorem selLiftWit_complete_odd_bce (hκ : selPar (B * (C * E)) = 1) {res : gr3R}
    (h5 : sqRelWord (selLiftWit h j A B C D E F T S P Q R) = liftC res) :
    ∃ z₃ : SqU5 gr3R, z₃.IsGaThree ∧ selLamThree A B C D E F T S P Q R z₃ ∧
      sqRelWord (selLift j (selLiftWit h j A B C D E F T S P Q R) 1 1 z₃ 1) = 1 := by
  have h3 : selPar (-(2 * (A * C)) * F - (C * E) * B) = 1 := by
    have hsplit : -(2 * (A * C)) * F - (C * E) * B
        = B * (C * E) + 2 * (-(A * C * F) - B * (C * E)) := by ring
    rw [hsplit, selPar_add, selPar_two_mul, add_zero]
    exact hκ
  obtain ⟨rr, hrr⟩ := gr3R_exists_inv_of_odd _ h3
  refine ⟨⟨0, 0, 0, 0, 0, 0, 0, -(rr * res * -(2 * (A * C))), -(rr * res * (C * E)), 0⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨-(rr * res), 0, 0, 0, 0, 0, 0, by ring, by ring⟩, ?_⟩
  refine sqRelWord_selLift_eq_one_odd (zh := -(2 * (A * C))) (zi := C * E) (rr := rr)
    h5 ?_
  rw [selLiftWit_handleV]
  linear_combination hrr

/-- **Odd-regime completion at the `A·D·F` pairing**: the generator
`(−(A·D + B·C), C·F)` pairs to `−(A·D + B·C)·F − B·C·F` against the `V`-columns, odd
exactly when `A·D·F` is, with its explicit achievable move. -/
theorem selLiftWit_complete_odd_adf (hκ : selPar (A * (D * F)) = 1) {res : gr3R}
    (h5 : sqRelWord (selLiftWit h j A B C D E F T S P Q R) = liftC res) :
    ∃ z₃ : SqU5 gr3R, z₃.IsGaThree ∧ selLamThree A B C D E F T S P Q R z₃ ∧
      sqRelWord (selLift j (selLiftWit h j A B C D E F T S P Q R) 1 1 z₃ 1) = 1 := by
  have h3 : selPar (-(A * D + B * C) * F - (C * F) * B) = 1 := by
    have hsplit : -(A * D + B * C) * F - (C * F) * B
        = A * (D * F) + 2 * (-(A * (D * F)) - B * (C * F)) := by ring
    rw [hsplit, selPar_add, selPar_two_mul, add_zero]
    exact hκ
  obtain ⟨rr, hrr⟩ := gr3R_exists_inv_of_odd _ h3
  refine ⟨⟨0, 0, 0, 0, 0, 0, 0, -(rr * res * -(A * D + B * C)), -(rr * res * (C * F)), 0⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨0, 0, -(rr * res), 0, 0, 0, 0, by ring, by ring⟩, ?_⟩
  refine sqRelWord_selLift_eq_one_odd (zh := -(A * D + B * C)) (zi := C * F) (rr := rr)
    h5 ?_
  rw [selLiftWit_handleV]
  linear_combination hrr

/-- **The mirror odd-regime completion at `κ₄' = A·C·E`**: the `(−A, C)⋆U` generator pairs
to `3·A·C·E` through the `V`-handle slot against the `U`-columns, with its explicit
achievable move: the witness instance of the committed mirror completion
`sqRelWord_selLift_eq_one_odd'`. -/
theorem selLiftWit_complete_odd_ace (hκ : selPar (A * (C * E)) = 1) {res : gr3R}
    (h5 : sqRelWord (selLiftWit h j A B C D E F T S P Q R) = liftC res) :
    ∃ z₄ : SqU5 gr3R, z₄.IsGaThree ∧ selLamThree A B C D E F T S P Q R z₄ ∧
      sqRelWord (selLift j (selLiftWit h j A B C D E F T S P Q R) 1 1 1 z₄) = 1 := by
  have h3 : selPar (A * (C * E) - E * -(2 * (A * C))) = 1 := by
    have hsplit : A * (C * E) - E * -(2 * (A * C))
        = A * (C * E) + 2 * (A * (C * E)) := by ring
    rw [hsplit, selPar_add, selPar_two_mul, add_zero]
    exact hκ
  obtain ⟨rr, hrr⟩ := gr3R_exists_inv_of_odd _ h3
  refine ⟨⟨0, 0, 0, 0, 0, 0, 0, -(rr * res * -(2 * (A * C))), -(rr * res * (C * E)), 0⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨-(rr * res), 0, 0, 0, 0, 0, 0, by ring, by ring⟩, ?_⟩
  refine sqRelWord_selLift_eq_one_odd' (zh := -(2 * (A * C))) (zi := C * E) (rr := rr)
    h5 ?_
  rw [selLiftWit_handleU]
  linear_combination hrr

end Witness

/-! ### Concrete instances

Three pipes end to end at one handle, all cross-validated numerically before transcription
(`scripts/w53_contain/`).

* **A completion the committed generator cannot make.**  At the binder point
  `(A,…,S) = (1, 0, 0, 1, 2, 1, 0, 2)` with halves `(P, Q, R) = (3, 0, 1)` (all four
  parity rows check, `W2 = 2`), the witness survives stage 3 outright with the **odd**
  residue `7`, but `κ₄ = B·D·F = 0` and `κ₄' = A·C·E = 0`: the committed completions are
  silent.  The `A·D·F`-pairing is odd, and `selLiftWit_complete_odd_adf` kills the
  relator.
* **The artefact pipeline.**  The killed frame of `GradedLift`'s engine instance is a
  genuine class-four solution; dressing its `U`-handle slot by the `γ₃`-element with
  `(h, i) = (1, 0)` is a five-slot `K`-dressing whose Frobenius rows vanish trivially, the
  defect is the pure artefact `liftC 1` (**odd**, so no class-three-style completion
  could exist), and the explicit odd-regime move `(h, i) = (2, 3)` on the `U`-slot kills
  the dressed solution: the located mechanism of the vanish note, executed end to end.
* **A provable dead end.**  At the uncovered corner `(A,…,S) = (0, 1, 1, 1, 2, 0, 2, 0)`
  with halves `(1, 3, 1)`, the witness survives stage 3 with odd residue `5` and all eight
  generator pairings even: `sqRelWord_selLift_ne_one` shows **no** achievable engine
  refinement kills it, the class-four form of the sweep's degenerate-weight caveat, now a
  theorem rather than a measurement. -/

/-- The witness at the showcase point: a stage-three survivor with odd residue `7`. -/
example : sqRelWord (selLiftWit 1 0 1 0 0 1 2 1 0 2 3 0 1) = liftC (7 : gr3R) := by decide

/-- …whose committed `κ₄`- and `κ₄'`-completions are silent… -/
example : selPar ((0 : gr3R) * 1 * 1) = 0 ∧ selPar ((1 : gr3R) * (0 * 2)) = 0 := by decide

/-- …and the `A·D·F`-completion kills it. -/
example : ∃ z₃ : SqU5 gr3R, z₃.IsGaThree ∧ selLamThree 1 0 0 1 2 1 0 2 3 0 1 z₃ ∧
    sqRelWord (selLift 0 (selLiftWit 1 0 1 0 0 1 2 1 0 2 3 0 1) 1 1 z₃ 1) = 1 :=
  selLiftWit_complete_odd_adf (by decide) (res := 7) (by decide)

/-- The bit form agrees with the showcase residue's parity: `(ACF + BDE)·T + P·R = 3`. -/
example : selPar ((((1 : gr3R) * (0 * 1) + 0 * (1 * 2)) * 0 + 3 * 1)) = 1 := by decide

/-- **The artefact pipeline, step 1**: the engine instance's killed frame is a genuine
class-four solution. -/
example : sqRelWord (selLift 0 (selLiftWit 1 0 2 1 0 1 2 1 0 1 3 0 1) 1 1
    (⟨0, 0, 0, 0, 0, 0, 0, 2, 7, 0⟩ : SqU5 gr3R) 1) = 1 := by decide

/-- **Step 2**: the `U`-handle `γ₃`-dressing of that solution has defect the pure artefact
`liftC 1`: odd, which class three can never repair. -/
example : sqRelWord (conFourDress
    (selLift 0 (selLiftWit 1 0 2 1 0 1 2 1 0 1 3 0 1) 1 1
      (⟨0, 0, 0, 0, 0, 0, 0, 2, 7, 0⟩ : SqU5 gr3R) 1)
    (fun i => if (i : ℕ) = 3 then ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩ else 1))
    = liftC (1 : gr3R) := by decide

/-- **Step 3**: the explicit odd-regime engine move kills the dressed solution. -/
example : sqRelWord (selLift 0 (conFourDress
    (selLift 0 (selLiftWit 1 0 2 1 0 1 2 1 0 1 3 0 1) 1 1
      (⟨0, 0, 0, 0, 0, 0, 0, 2, 7, 0⟩ : SqU5 gr3R) 1)
    (fun i => if (i : ℕ) = 3 then ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩ else 1)) 1 1
    ⟨0, 0, 0, 0, 0, 0, 0, 2, 3, 0⟩ 1) = 1 := by decide

/-- **The provable dead end**: at the uncovered corner the witness's odd residue `5`
survives every achievable engine refinement, hypotheses by `decide`, conclusion through
the obstruction theorem. -/
example {w₁ w₂ z₃ z₄ : SqU5 gr3R} (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (hz₃L : selLamThree 0 1 1 1 2 0 2 0 1 3 1 z₃)
    (hz₄L : selLamThree 0 1 1 1 2 0 2 0 1 3 1 z₄) :
    sqRelWord (selLift 0 (selLiftWit 1 0 0 1 1 1 2 0 2 0 1 3 1) w₁ w₂ z₃ z₄) ≠ 1 :=
  sqRelWord_selLift_ne_one hw₁ hw₂ hz₃ hz₄ hz₃L hz₄L
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## §5 Axiom pins

Committed prints for every public declaration of this file: all **std-3** (`propext`,
`Classical.choice`, `Quot.sound`) or a subset; no census axiom is reachable.  Every
`decide` is on `ZMod 8`, `ZMod 2`, `SqU5 (ZMod 8)` or tuples and words over them. -/

section AxiomPins

#print axioms gaThree_mul_comm
#print axioms conjP_gaThree
#print axioms handleWord_a
#print axioms handleWord_d
#print axioms handleWord_mul_gaThree_all
#print axioms conFourDress
#print axioms conFourDress_apply
#print axioms conFourShift
#print axioms sqWord_mul_gaThree
#print axioms conFourDress_abcd
#print axioms sqRelWord_conFourDress
#print axioms sqRelWord_conFourDress_h
#print axioms sqRelWord_conFourDress_i
#print axioms sqRelWord_conFourDress_j
#print axioms conFourDress_conFourDress_inv
#print axioms sqRelWord_conFourDress_of_rel
#print axioms sqRelWord_conFourDress_liftC
#print axioms conFour_contain_odd
#print axioms conFour_contain_odd'
#print axioms conFour_contain_even
#print axioms selLamThree_pair_even
#print axioms selLamThree_pair_even'
#print axioms sqRelWord_selLift_ne_one
#print axioms selLiftWitJEven
#print axioms sqRelWord_selLiftWit_j
#print axioms sqRelWord_selLiftWit_liftC
#print axioms selLiftWit_bit
#print axioms selLiftWit_complete_odd_bce
#print axioms selLiftWit_complete_odd_adf
#print axioms selLiftWit_complete_odd_ace

end AxiomPins

end SqCore

end Dyadic

end GQ2

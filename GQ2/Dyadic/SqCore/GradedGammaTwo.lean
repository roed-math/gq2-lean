/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedContainFour

/-!
# W54-GAMMA2: the `γ₂`-torsor transport at class four

`GradedContainFour` committed the class-four containment along the `γ₃`-dressing torsor and
located its frontier exactly (its "Honest scope"): at the binder corners the committed
engine does not cover, the honest tower's containment must route through **`γ₂`-level
moves**, whose class-four defect has genuinely quadratic terms that the affine calculus of
that file cannot express.  This file supplies the calculus and the transport.

* **The `γ₂` translation identity** (`sqWord_mul_gaTwo`, `commP_mul_gaTwo`,
  `handleWord_mul_gaTwo_all`, ⭐⭐ `sqRelWord_gaTwoDress`): a five-slot `γ₂`-dressing of the
  relator moves it by an explicit `γ₂`-element.  The three class-two rows move by the
  Frobenius weights `(−4, 2)` on the exponent slots alone; each class-three row moves by the
  class-three graded Fox form of the corresponding `U₄`-quotient; and the class-four row
  moves by **three** blocks: the class-four graded Fox pairing `gaTwoPair z β` of each
  dressing against its permuted letter (which is exactly `u5Comm4 z β`, the class-four
  commutator form), an explicit correction `gaTwoCorr` quadratic in the frame's own columns,
  and the genuinely quadratic form `gaTwoQuad` in the dressings themselves, whose
  coefficients `(1, 10, −8, 1)` are the binomials `C(n, 2)` of the relator's exponent vector
  and the commutator pairing `z.e·w.g − z.g·w.e` of `γ₂` at class four.  The whole identity
  was derived and validated symbolically before transcription (`scripts/w54_gamma2/`,
  `w54_shift.m`: ten zero rows at `h = 1` and `h = 2` over `ℤ[m, z]`, and the two
  class-three rows against the committed `GradedVanish` shift through `toU4L`, `toU4R`).
* ⭐⭐ **The three moves the committed lattice misses** (`selLiftWit_commP_zero_two`,
  `_two_handleU`, `_two_handleV`): the commutators of the witness's `x₁`-slot letter against
  the `σ`-, `U`- and `V`-slots are **`γ₃`-shaped** and carry the `(h, i)`-data
  `(0, R)`, `(P·C − Q·A, Q·E)`, `(P·D − Q·B, Q·F)`.  The committed `selLamThree` carries
  exactly their **doubles** (it pairs `Λ₅ ∋ x₁^{−2}` against the letters rather than `x₁`
  itself), and that factor two is the whole of the recorded dead end: these are honest
  commutators of two frame slots, hence `γ₂`-level dressings of the honest tower, and they
  are odd exactly where the committed lattice is even.
* ⭐⭐ **The transport** (`selLamThreePlus`, `selLiftWit_complete_odd_plus`, `_plus'`,
  `_rb`, `_ar`): at any point where one of the six new pairings is a unit, **every**
  class-four residue dies by one explicit achievable move; in particular the
  `(A,…,S) = (0, 1, 1, 1, 2, 0, 2, 0)` corner that `GradedContainFour`'s obstruction theorem
  certifies as a dead end **of the committed engine** is killed here, by a power of
  `⁅σ, x₁⁆`.  The obstruction theorem is not contradicted: it quantifies over `selLamThree`,
  and the move is outside it.

## Honest scope

Everything below is a theorem about the committed test group `SqU5` and the committed
witness; what is *modelled* rather than proved is the achievability convention, namely that
a test hom carries `γ₂` of the honest group onto `γ₂` of its image, so that any commutator
of two frame slots is a legitimate dressing.  Under that convention the census
(`scripts/w54_gamma2/results/w54gate.txt`, `w54dead.txt`) reads: of the `131072` binder
points where the bare witness survives stage 3 with an odd residue, the committed engine
covers `16384`, the three new moves cover a further `80896`, and the residual `33792` are
**exhaustively certified dead at the `γ₂` level**: the full achievable increment lattice of
`γ₂(im Φ)`, quadratic terms included, meets the residue line in `2·ℤ/8` at every one of
them.  Of those, `18432` would be killed by an unrestricted `γ₂`-dressing, so their
obstruction is achievability; the remaining `15360` resist every `γ₂`-level move whatever.
All ten mod-2 classes of the residual set have `A` and `B` **both even**, which is exactly
the condition that kills the six new pairings.  Committing the residual obstruction as a
theorem needs the `γ₂`-analogue of `selLamThree_pair_even` for the whole lattice and is left
to the next wave (`docs/dyadic/w54-gamma2-note.md` §7).

## Contents

* **§1** the `γ₂`-calculus on `SqU5`: the pairing forms, the swap lemma, the handle word's
  four vanishing columns and its two outer class-two rows;
* **§2** ⭐⭐ the five-slot `γ₂`-dressing and the translation identity;
* **§3** ⭐⭐ the three `γ₂`-level moves at the witness, the extended lattice `selLamThreePlus`
  and the completions, with the recorded dead-end corner killed end to end;
* **§4** committed axiom prints (all std-3).

Companion memo: `docs/dyadic/w54-gamma2-note.md`.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The `γ₂`-calculus on `SqU5`

A `γ₂`-dressing moves no abelian column but every deeper one.  Three facts carry §2: the
class-four commutator form of a `γ₂`-element against a letter is the pairing `gaTwoPair`;
two `γ₂`-elements commute up to the central `e`-against-`g` pairing (`gaTwo_swap`); and the
handle word has all four abelian columns zero, with its two outer class-two rows the
explicit handle sums. -/

section GaTwoCalculus

variable {R : Type} [CommRing R]

/-- **The class-four pairing form**: the class-four commutator of a `γ₂`-element against a
letter, `u5Comm4 z L` with the `γ₂`-shape of `z` used (`gaTwoPair_eq_u5Comm4`).  Beyond the
`γ₃`-part `z.h·L.d − z.i·L.a` of the committed `conFourShift` it reads the dressing's
class-two data against the letter's class-two data and against the products of its outer
abelian columns. -/
def gaTwoPair (z L : SqU5 R) : R :=
  z.h * L.d - z.i * L.a + z.e * L.g - z.g * L.e + z.g * (L.a * L.b) - z.f * (L.a * L.d)

/-- The pairing form really is the class-four commutator form on `γ₂`. -/
theorem gaTwoPair_eq_u5Comm4 {z : SqU5 R} (hz : z.IsGaTwo) (L : SqU5 R) :
    gaTwoPair z L = SqU5.u5Comm4 z L := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  simp only [gaTwoPair, SqU5.u5Comm4, h1, h2, h3, h4]
  ring

/-- The **left** class-three pairing form: the `toU4L`-shadow of the graded Fox form. -/
def gaTwoPairL (z L : SqU5 R) : R := z.e * L.c - z.f * L.a

/-- The **right** class-three pairing form: the `toU4R`-shadow. -/
def gaTwoPairR (z L : SqU5 R) : R := z.f * L.d - z.g * L.b

/-- **The `x₀`-slot Fox letter** `10·x₀ − σ − 8·x₁`, columnwise: the `σ`-letter mod 2, the
same integer combination the committed `conFourShift` uses one filtration step up. -/
def sqFoxX (s x y : SqU5 R) : SqU5 R :=
  ⟨10 * x.a - s.a - 8 * y.a, 10 * x.b - s.b - 8 * y.b, 10 * x.c - s.c - 8 * y.c,
    10 * x.d - s.d - 8 * y.d, 10 * x.e - s.e - 8 * y.e, 10 * x.f - s.f - 8 * y.f,
    10 * x.g - s.g - 8 * y.g, 10 * x.h - s.h - 8 * y.h, 10 * x.i - s.i - 8 * y.i,
    10 * x.j - s.j - 8 * y.j⟩

/-- **Two `γ₂`-elements swap up to a central pairing**: the class-four commutator of `γ₂`
with `γ₂` is central with value `p.e·q.g − q.e·p.g`.  This is the one genuinely non-abelian
fact of the `γ₂`-torsor at class four, and the source of the quadratic terms. -/
theorem gaTwo_swap {p q : SqU5 R} (hp : p.IsGaTwo) (hq : q.IsGaTwo) :
    p * q = q * (p * liftC (p.e * q.g - q.e * p.g)) := by
  obtain ⟨p1, p2, p3, p4⟩ := hp
  obtain ⟨q1, q2, q3, q4⟩ := hq
  ext <;> simp only [liftC, SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d, SqU5.mul_e,
    SqU5.mul_f, SqU5.mul_g, SqU5.mul_h, SqU5.mul_i, SqU5.mul_j,
    p1, p2, p3, p4, q1, q2, q3, q4] <;> ring

/-- The `b`-coordinate of a product list vanishes when every factor's does. -/
private theorem prod_b_eq_zero : ∀ l : List (SqU5 R), (∀ p ∈ l, p.b = 0) → l.prod.b = 0
  | [], _ => rfl
  | p :: l, hl => by
    rw [List.prod_cons, SqU5.mul_b, hl p (by simp),
      prod_b_eq_zero l fun q hq => hl q (by simp [hq]), add_zero]

/-- …and likewise the `c`-coordinate. -/
private theorem prod_c_eq_zero : ∀ l : List (SqU5 R), (∀ p ∈ l, p.c = 0) → l.prod.c = 0
  | [], _ => rfl
  | p :: l, hl => by
    rw [List.prod_cons, SqU5.mul_c, hl p (by simp),
      prod_c_eq_zero l fun q hq => hl q (by simp [hq]), add_zero]

/-- The handle word has no `b`-column (the companion of the committed `handleWord_a`). -/
@[simp] theorem SqU5.handleWord_b {h : ℕ} (u v : Fin h → SqU5 R) : (handleWord u v).b = 0 :=
  prod_b_eq_zero _ fun p hp => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
    exact SqU5.commP_b _ _

/-- …and no `c`-column. -/
@[simp] theorem SqU5.handleWord_c {h : ℕ} (u v : Fin h → SqU5 R) : (handleWord u v).c = 0 :=
  prod_c_eq_zero _ fun p hp => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
    exact SqU5.commP_c _ _

/-- The handle word is `γ₂`-shaped. -/
theorem SqU5.handleWord_isGaTwo {h : ℕ} (u v : Fin h → SqU5 R) :
    (handleWord u v).IsGaTwo :=
  ⟨SqU5.handleWord_a u v, SqU5.handleWord_b u v, SqU5.handleWord_c u v,
    SqU5.handleWord_d u v⟩

/-- **The handle word's first outer class-two row**: the sum of the `(a, b)`-pairings. -/
theorem SqU5.handleWord_e : ∀ (n : ℕ) (u v : Fin n → SqU5 R),
    (handleWord u v).e = ∑ k : Fin n, ((u k).a * (v k).b - (u k).b * (v k).a)
  | 0, _, _ => by simp [handleWord]
  | n + 1, u, v => by
    have htail := SqU5.handleWord_e n (fun k => u k.succ) (fun k => v k.succ)
    rw [handleWord] at htail ⊢
    rw [List.finRange_succ, List.map_cons, List.prod_cons, List.map_map]
    have hL : (List.finRange n).map ((fun k => commP (u k) (v k)) ∘ Fin.succ)
        = (List.finRange n).map fun k => commP (u k.succ) (v k.succ) :=
      List.map_congr_left fun k _ => rfl
    rw [hL, SqU5.mul_e, SqU5.commP_a, zero_mul, add_zero, htail, SqU5.commP_e,
      Fin.sum_univ_succ]

/-- **The handle word's last outer class-two row**: the sum of the `(c, d)`-pairings. -/
theorem SqU5.handleWord_g : ∀ (n : ℕ) (u v : Fin n → SqU5 R),
    (handleWord u v).g = ∑ k : Fin n, ((u k).c * (v k).d - (u k).d * (v k).c)
  | 0, _, _ => by simp [handleWord]
  | n + 1, u, v => by
    have htail := SqU5.handleWord_g n (fun k => u k.succ) (fun k => v k.succ)
    rw [handleWord] at htail ⊢
    rw [List.finRange_succ, List.map_cons, List.prod_cons, List.map_map]
    have hL : (List.finRange n).map ((fun k => commP (u k) (v k)) ∘ Fin.succ)
        = (List.finRange n).map fun k => commP (u k.succ) (v k.succ) :=
      List.map_congr_left fun k _ => rfl
    rw [hL, SqU5.mul_g, SqU5.commP_c, zero_mul, add_zero, htail, SqU5.commP_g,
      Fin.sum_univ_succ]

/-- Two `γ₃`-elements multiply coordinatewise. -/
private theorem gaThree_mul_rec {γ : SqU5 R} (hγ : γ.IsGaThree) (d e f : R) :
    γ * ⟨0, 0, 0, 0, 0, 0, 0, d, e, f⟩
      = ⟨0, 0, 0, 0, 0, 0, 0, γ.h + d, γ.i + e, γ.j + f⟩ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hγ
  ext <;> simp [h1, h2, h3, h4, h5, h6, h7]

/-- The `a`-coordinate of a product list vanishes when every factor's does. -/
private theorem prodA_zero : ∀ l : List (SqU5 R), (∀ p ∈ l, p.a = 0) → l.prod.a = 0
  | [], _ => rfl
  | p :: l, hl => by
    rw [List.prod_cons, SqU5.mul_a, hl p (by simp),
      prodA_zero l fun q hq => hl q (by simp [hq]), add_zero]

/-- …and likewise the `d`-coordinate. -/
private theorem prodD_zero : ∀ l : List (SqU5 R), (∀ p ∈ l, p.d = 0) → l.prod.d = 0
  | [], _ => rfl
  | p :: l, hl => by
    rw [List.prod_cons, SqU5.mul_d, hl p (by simp),
      prodD_zero l fun q hq => hl q (by simp [hq]), add_zero]

/-- A `γ₃`-right-factor moves past any factor with vanishing outer abelian columns. -/
private theorem mul_gaThree_swap {a b γ δ : SqU5 R} (hγ : γ.IsGaThree) (hb : b.a = 0)
    (hbd : b.d = 0) : (a * γ) * (b * δ) = a * b * (γ * δ) := by
  rw [mul_assoc, ← mul_assoc γ b δ, gaThree_mul_comm hγ hb hbd, mul_assoc, ← mul_assoc]

end GaTwoCalculus

/-! ## §2 ⭐⭐ The five-slot `γ₂`-dressing and the translation identity

`conFourDress m z` is the committed five-slot dressing; with `γ₂`-dressings it moves the
relator by the `γ₂`-element `gaTwoShift`.  The three blocks of the class-four row are the
graded Fox pairing, the correction, and the quadratic form; the correction and the quadratic
coefficients are exactly the ones the symbolic derivation produced, transcribed verbatim. -/

section DressAction

variable {R : Type} [CommRing R]

/-- **The correction block** of the class-four core shift: the part of the defect that reads
the dressings' class-two data against products of the frame's own columns, beyond the graded
Fox pairing.  It is the collection artefact of moving each dressing to the end of the word
past the suffix of its own occurrences; mod 2 it is the suffixes' class-two data.  At the
committed witness every one of the nine coefficients is even. -/
def gaTwoCorr (s x y z₀ z₁ z₂ : SqU5 R) : R :=
  z₀.e * (-(s.c * x.d) + s.d * x.c - 4 * (x.c * x.d) + 2 * (x.c * y.d) + y.c * y.d)
    + z₀.f * (8 * (x.a * x.d) - 2 * (x.a * y.d) - 2 * (x.d * y.a) - 2 * (y.a * y.d))
    + z₀.g * (s.a * x.b - s.b * x.a - 4 * (x.a * x.b) + 2 * (x.b * y.a) + y.a * y.b)
    + z₁.e * (3 * (s.c * x.d) - 2 * (s.c * y.d) + s.d * x.c - 20 * (x.c * x.d)
        + 20 * (x.c * y.d) - 4 * (y.c * y.d))
    + z₁.f * (2 * (s.a * s.d) - 14 * (s.a * x.d) + 10 * (s.a * y.d) - 14 * (s.d * x.a)
        + 10 * (s.d * y.a) + 130 * (x.a * x.d) - 100 * (x.a * y.d) - 100 * (x.d * y.a)
        + 80 * (y.a * y.d))
    + z₁.g * (-2 * (s.a * s.b) + 11 * (s.a * x.b) - 8 * (s.a * y.b) + 13 * (s.b * x.a)
        - 10 * (s.b * y.a) - 110 * (x.a * x.b) + 80 * (x.a * y.b) + 100 * (x.b * y.a)
        - 76 * (y.a * y.b))
    + z₂.e * (-2 * (s.c * y.d) + s.d * y.c)
    + z₂.f * (s.a * y.d + s.d * y.a)
    + z₂.g * (s.a * y.b - 2 * (s.b * y.a))

/-- ⭐ **The quadratic block**: the genuinely quadratic part of the class-four defect of a
`γ₂`-dressing, and the object no affine calculus can carry.  The cross coefficient `1` is the
`γ₂`-commutator pairing `z.e·w.g − z.g·w.e` of the `σ`- and `x₀`-slots, and `10 = C(−4, 2)`,
`1 = C(2, 2)` are the exponent binomials of the relator's `(−4, 2)`-weights (the `−8` is the
mixed exponent term).  It is `m`-free: by weight, a quadratic term in the dressings has no
room for a frame coordinate. -/
def gaTwoQuad (z₀ z₁ z₂ : SqU5 R) : R :=
  (z₀.e * z₁.g - z₀.g * z₁.e) + 10 * (z₁.e * z₁.g) - 8 * (z₁.e * z₂.g) + z₂.e * z₂.g

/-- **The core shift**: the `γ₂`-element by which the core word moves under a three-slot
`γ₂`-dressing.  Class-two rows: the Frobenius weights on the exponent slots.  Class-three
rows: the Frobenius weights plus the class-three graded Fox pairings against the permuted
letters `(x₀, σ*, x₁)`.  Class-four row: the Frobenius weight, the class-four Fox pairings,
the correction and the quadratic block. -/
def gaTwoCore (s x y z₀ z₁ z₂ : SqU5 R) : SqU5 R :=
  ⟨0, 0, 0, 0, -4 * z₁.e + 2 * z₂.e, -4 * z₁.f + 2 * z₂.f, -4 * z₁.g + 2 * z₂.g,
    -4 * z₁.h + 2 * z₂.h
      + (gaTwoPairL z₀ x + gaTwoPairL z₁ (sqFoxX s x y) + gaTwoPairL z₂ y),
    -4 * z₁.i + 2 * z₂.i
      + (gaTwoPairR z₀ x + gaTwoPairR z₁ (sqFoxX s x y) + gaTwoPairR z₂ y),
    -4 * z₁.j + 2 * z₂.j
      + (gaTwoPair z₀ x + gaTwoPair z₁ (sqFoxX s x y) + gaTwoPair z₂ y)
      + gaTwoCorr s x y z₀ z₁ z₂ + gaTwoQuad z₀ z₁ z₂⟩

/-- The core shift is `γ₂`-shaped. -/
theorem gaTwoCore_isGaTwo (s x y z₀ z₁ z₂ : SqU5 R) :
    (gaTwoCore s x y z₀ z₁ z₂).IsGaTwo := ⟨rfl, rfl, rfl, rfl⟩

/-- ⭐⭐ **The core word under `γ₂`-dressings of its three slots**.  No closed form of the
word is consumed: componentwise expansion. -/
theorem sqWord_mul_gaTwo {z₀ z₁ z₂ : SqU5 R} (s x y : SqU5 R) (h₀ : z₀.IsGaTwo)
    (h₁ : z₁.IsGaTwo) (h₂ : z₂.IsGaTwo) :
    sqWord (s * z₀) (x * z₁) (y * z₂) = sqWord s x y * gaTwoCore s x y z₀ z₁ z₂ := by
  obtain ⟨h₀a, h₀b, h₀c, h₀d⟩ := h₀
  obtain ⟨h₁a, h₁b, h₁c, h₁d⟩ := h₁
  obtain ⟨h₂a, h₂b, h₂c, h₂d⟩ := h₂
  ext <;> simp only [gaTwoCore, gaTwoPair, gaTwoPairL, gaTwoPairR, gaTwoCorr, gaTwoQuad,
    sqFoxX, sqWord, conjP, commP, pow_succ, pow_zero, one_mul,
    SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d, SqU5.mul_e, SqU5.mul_f, SqU5.mul_g,
    SqU5.mul_h, SqU5.mul_i, SqU5.mul_j, SqU5.inv_a, SqU5.inv_b, SqU5.inv_c, SqU5.inv_d,
    SqU5.inv_e, SqU5.inv_f, SqU5.inv_g, SqU5.inv_h, SqU5.inv_i, SqU5.inv_j,
    h₀a, h₀b, h₀c, h₀d, h₁a, h₁b, h₁c, h₁d, h₂a, h₂b, h₂c, h₂d] <;> ring

/-- **The handle shift**: the `γ₃`-element by which one handle commutator moves under a
`γ₂`-dressing of both its slots.  The two class-three rows are the crosswise class-three Fox
pairings; the class-four row is the crosswise class-four pairing, the commutator's own
class-two rows against the dressings' class-two data, and the `γ₂`-commutator of the two
dressings. -/
def gaTwoHandle (p q z w : SqU5 R) : SqU5 R :=
  ⟨0, 0, 0, 0, 0, 0, 0,
    gaTwoPairL z q - gaTwoPairL w p,
    gaTwoPairR z q - gaTwoPairR w p,
    gaTwoPair z q - gaTwoPair w p
      - (p.c * q.d - p.d * q.c) * (z.e + w.e) + (p.a * q.b - p.b * q.a) * (z.g + w.g)
      + (z.e * w.g - z.g * w.e)⟩

/-- The handle shift is `γ₃`-shaped. -/
theorem gaTwoHandle_isGaThree (p q z w : SqU5 R) : (gaTwoHandle p q z w).IsGaThree :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⭐ **Dressing both arguments of a commutator by `γ₂`-elements** moves it by the handle
shift.  Unlike the committed `γ₃`-version the translation is not central: the commutator's
two class-three rows move as well. -/
theorem commP_mul_gaTwo {z w : SqU5 R} (p q : SqU5 R) (hz : z.IsGaTwo) (hw : w.IsGaTwo) :
    commP (p * z) (q * w) = commP p q * gaTwoHandle p q z w := by
  obtain ⟨hza, hzb, hzc, hzd⟩ := hz
  obtain ⟨hwa, hwb, hwc, hwd⟩ := hw
  ext <;> simp only [gaTwoHandle, gaTwoPair, gaTwoPairL, gaTwoPairR, commP,
    SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d, SqU5.mul_e, SqU5.mul_f, SqU5.mul_g,
    SqU5.mul_h, SqU5.mul_i, SqU5.mul_j, SqU5.inv_a, SqU5.inv_b, SqU5.inv_c, SqU5.inv_d,
    SqU5.inv_e, SqU5.inv_f, SqU5.inv_g, SqU5.inv_h, SqU5.inv_i, SqU5.inv_j,
    hza, hzb, hzc, hzd, hwa, hwb, hwc, hwd] <;> ring

/-- ⭐ **The handle block under an all-pair `γ₂`-dressing**: the handle word moves by the
`γ₃`-element summing the per-pair handle shifts.  The cross-handle coupling of the class-four
row does **not** move, because it reads only the commutators' class-two rows, which a
`γ₂`-dressing leaves alone. -/
theorem handleWord_mul_gaTwo_all : ∀ (n : ℕ) (u v zu zv : Fin n → SqU5 R),
    (∀ k, (zu k).IsGaTwo) → (∀ k, (zv k).IsGaTwo) →
    handleWord (fun k => u k * zu k) (fun k => v k * zv k)
      = handleWord u v
        * ⟨0, 0, 0, 0, 0, 0, 0,
            ∑ k : Fin n, (gaTwoHandle (u k) (v k) (zu k) (zv k)).h,
            ∑ k : Fin n, (gaTwoHandle (u k) (v k) (zu k) (zv k)).i,
            ∑ k : Fin n, (gaTwoHandle (u k) (v k) (zu k) (zv k)).j⟩
  | 0, u, v, zu, zv, _, _ => by
    ext <;> simp [handleWord]
  | n + 1, u, v, zu, zv, hzu, hzv => by
    have htail := handleWord_mul_gaTwo_all n (fun k => u k.succ) (fun k => v k.succ)
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
    have hPa : (((List.finRange n).map fun k => commP (u k.succ) (v k.succ)).prod).a = 0 :=
      prodA_zero _ fun p hp => by
        obtain ⟨k, -, rfl⟩ := List.mem_map.mp hp
        exact SqU5.commP_a _ _
    have hPd : (((List.finRange n).map fun k => commP (u k.succ) (v k.succ)).prod).d = 0 :=
      prodD_zero _ fun p hp => by
        obtain ⟨k, -, rfl⟩ := List.mem_map.mp hp
        exact SqU5.commP_d _ _
    rw [hL, hR, htail, commP_mul_gaTwo _ _ (hzu 0) (hzv 0),
      mul_gaThree_swap (gaTwoHandle_isGaThree _ _ _ _) hPa hPd,
      gaThree_mul_rec (gaTwoHandle_isGaThree _ _ _ _),
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]

variable {h : ℕ}

variable (h) in
/-- The frame's first outer handle pairing sum, the handle word's `e`-row. -/
def sqHandlePairE (m : Fin (sqRank h) → SqU5 R) : R :=
  ∑ k : Fin h, ((m (sqHandleIdxU k)).a * (m (sqHandleIdxV k)).b
    - (m (sqHandleIdxU k)).b * (m (sqHandleIdxV k)).a)

variable (h) in
/-- The frame's last outer handle pairing sum, the handle word's `g`-row. -/
def sqHandlePairG (m : Fin (sqRank h) → SqU5 R) : R :=
  ∑ k : Fin h, ((m (sqHandleIdxU k)).c * (m (sqHandleIdxV k)).d
    - (m (sqHandleIdxU k)).d * (m (sqHandleIdxV k)).c)

variable (h) in
/-- ⭐⭐ **The `γ₂`-shift of the relator**: the core shift, times the summed handle shifts,
times the central collection term by which the core shift's class-two rows commute past the
handle word.  The last factor is even (the Frobenius weights are), and vanishes as soon as
the exponent slots are dressed by `γ₃`. -/
def gaTwoShift (m z : Fin (sqRank h) → SqU5 R) : SqU5 R :=
  gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)
    * ⟨0, 0, 0, 0, 0, 0, 0,
        ∑ k : Fin h, (gaTwoHandle (m (sqHandleIdxU k)) (m (sqHandleIdxV k))
          (z (sqHandleIdxU k)) (z (sqHandleIdxV k))).h,
        ∑ k : Fin h, (gaTwoHandle (m (sqHandleIdxU k)) (m (sqHandleIdxV k))
          (z (sqHandleIdxU k)) (z (sqHandleIdxV k))).i,
        ∑ k : Fin h, (gaTwoHandle (m (sqHandleIdxU k)) (m (sqHandleIdxV k))
          (z (sqHandleIdxU k)) (z (sqHandleIdxV k))).j⟩
    * liftC ((-4 * (z 1).e + 2 * (z 2).e) * sqHandlePairG h m
        - sqHandlePairE h m * (-4 * (z 1).g + 2 * (z 2).g))

variable {m z : Fin (sqRank h) → SqU5 R}

/-- ⭐⭐ **The translation identity for a five-slot `γ₂`-dressing**: the relator moves by the
explicit `γ₂`-element `gaTwoShift`, at every handle count and over any commutative ring.
This is the object `GradedContainFour` located but could not express: its class-four row
carries the quadratic form `gaTwoQuad`.  No closed form of the relator is consumed: the core
is componentwise, the handle block is §2's product lemma, and the two blocks interact only
through the handle word's vanishing abelian columns and its two outer class-two rows. -/
theorem sqRelWord_gaTwoDress (hz : ∀ i, (z i).IsGaTwo) :
    sqRelWord (conFourDress m z) = sqRelWord m * gaTwoShift h m z := by
  have hhand := handleWord_mul_gaTwo_all h (fun k => m (sqHandleIdxU k))
    (fun k => m (sqHandleIdxV k)) (fun k => z (sqHandleIdxU k)) (fun k => z (sqHandleIdxV k))
    (fun k => hz _) (fun k => hz _)
  have hswap := gaTwo_swap (gaTwoCore_isGaTwo (m 0) (m 1) (m 2) (z 0) (z 1) (z 2))
    (SqU5.handleWord_isGaTwo (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k)))
  have hce : (gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).e
      = -4 * (z 1).e + 2 * (z 2).e := rfl
  have hcg : (gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).g
      = -4 * (z 1).g + 2 * (z 2).g := rfl
  rw [SqU5.handleWord_e, SqU5.handleWord_g, hce, hcg] at hswap
  rw [sqRelWord, sqRelWord]
  simp only [conFourDress_apply]
  rw [sqWord_mul_gaTwo (m 0) (m 1) (m 2) (hz 0) (hz 1) (hz 2), hhand, gaTwoShift,
    sqHandlePairE, sqHandlePairG]
  simp only [mul_assoc]
  refine congrArg _ ?_
  rw [← mul_assoc, hswap, mul_assoc, mul_assoc, ← liftC_comm]

end DressAction

/-! ## §3 ⭐⭐ The `γ₂`-level moves at the witness, and the transport

The committed `selLamThree` is the `(h, i)`-image of `γ₃(im Φ)`: the pairings of the
`γ₂`-image lattice `Λ₅` against the letters.  The `γ₂`-image lattice itself carries more:
every commutator of two frame slots lies in `γ₂(im Φ)`, and the three commutators of the
`x₁`-slot letter against `σ`, `U` and `V` are **`γ₃`-shaped**, so they act as class-three
moves without disturbing a single lower row.  Their `(h, i)`-data are the **halves** of three
committed `Λ₃`-generators, and that is the whole gap. -/

section GaTwoMoves

variable {h : ℕ} {j : Fin h} {A B C D E F T S P Q R : gr3R}

/-- ⭐⭐ **The `σ`-`x₁` commutator of the witness frame**: a `γ₃`-shaped element of
`γ₂(im Φ)` with `(h, i) = (0, R)` and no class-four part.  The committed `selLamThree`
carries only its double `(0, 2·R)`. -/
theorem selLiftWit_commP_zero_two :
    commP (selLiftWit h j A B C D E F T S P Q R 0) (selLiftWit h j A B C D E F T S P Q R 2)
      = ⟨0, 0, 0, 0, 0, 0, 0, 0, R, 0⟩ := by
  rw [selLiftWit_zero, selLiftWit_two]
  ext <;> simp only [commP, SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d, SqU5.mul_e,
    SqU5.mul_f, SqU5.mul_g, SqU5.mul_h, SqU5.mul_i, SqU5.mul_j, SqU5.inv_a, SqU5.inv_b,
    SqU5.inv_c, SqU5.inv_d, SqU5.inv_e, SqU5.inv_f, SqU5.inv_g, SqU5.inv_h, SqU5.inv_i,
    SqU5.inv_j] <;> ring

/-- ⭐ **The `x₁`-`U` commutator**: `γ₃`-shaped with `(h, i) = (P·C − Q·A, Q·E)`, the half of
the committed `2·(Q·A − P·C, …)` generator. -/
theorem selLiftWit_commP_two_handleU :
    commP (selLiftWit h j A B C D E F T S P Q R 2)
        (selLiftWit h j A B C D E F T S P Q R (sqHandleIdxU j))
      = ⟨0, 0, 0, 0, 0, 0, 0, P * C - Q * A, Q * E, -(2 * (A * (E * Q))) - B * (E * Q)⟩ := by
  rw [selLiftWit_two, selLiftWit_handleU]
  ext <;> simp only [commP, SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d, SqU5.mul_e,
    SqU5.mul_f, SqU5.mul_g, SqU5.mul_h, SqU5.mul_i, SqU5.mul_j, SqU5.inv_a, SqU5.inv_b,
    SqU5.inv_c, SqU5.inv_d, SqU5.inv_e, SqU5.inv_f, SqU5.inv_g, SqU5.inv_h, SqU5.inv_i,
    SqU5.inv_j] <;> ring

/-- ⭐ **The `x₁`-`V` commutator**: `γ₃`-shaped with `(h, i) = (P·D − Q·B, Q·F)`. -/
theorem selLiftWit_commP_two_handleV :
    commP (selLiftWit h j A B C D E F T S P Q R 2)
        (selLiftWit h j A B C D E F T S P Q R (sqHandleIdxV j))
      = ⟨0, 0, 0, 0, 0, 0, 0, P * D - Q * B, Q * F,
          -(A * (F * Q)) - 2 * (B * (F * Q)) + B * (S * R)⟩ := by
  rw [selLiftWit_two, selLiftWit_handleV]
  ext <;> simp only [commP, SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d, SqU5.mul_e,
    SqU5.mul_f, SqU5.mul_g, SqU5.mul_h, SqU5.mul_i, SqU5.mul_j, SqU5.inv_a, SqU5.inv_b,
    SqU5.inv_c, SqU5.inv_d, SqU5.inv_e, SqU5.inv_f, SqU5.inv_g, SqU5.inv_h, SqU5.inv_i,
    SqU5.inv_j] <;> ring

/-- **Membership in `Λ₃⁺`**, the achievable `γ₃`-shaped lattice of the `γ₂` level: the
committed `Λ₃` together with the three `x₁`-slot commutators of the frame, whose `(h, i)`-data
are `(0, R)`, `(P·C − Q·A, Q·E)` and `(P·D − Q·B, Q·F)`.  `Λ₃ ⊆ Λ₃⁺` (`selLamThree_plus`),
strictly whenever any of the three is odd. -/
def selLamThreePlus (A B C D E F T S P Q R : gr3R) (z : SqU5 gr3R) : Prop :=
  ∃ r₁ r₂ r₃ r₄ r₅ r₆ r₇ t₁ t₂ t₃ : gr3R,
    z.h = -(r₁ * (2 * (A * C))) - r₂ * (A * D + B * C) - r₃ * (A * D + B * C)
        - r₄ * (2 * (B * D)) + 2 * (r₆ * (Q * A - P * C)) + 2 * (r₇ * (Q * B - P * D))
        + t₂ * (P * C - Q * A) + t₃ * (P * D - Q * B) ∧
    z.i = r₁ * (C * E) + r₂ * (D * E) + r₃ * (C * F) + r₄ * (D * F) + 2 * (r₅ * R)
        + 2 * (r₆ * (R * T - Q * E)) + 2 * (r₇ * (R * S - Q * F))
        + t₁ * R + t₂ * (Q * E) + t₃ * (Q * F)

/-- The committed lattice sits inside the extended one. -/
theorem selLamThree_plus {z : SqU5 gr3R} (hz : selLamThree A B C D E F T S P Q R z) :
    selLamThreePlus A B C D E F T S P Q R z := by
  obtain ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, hh, hi⟩ := hz
  exact ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, 0, 0, 0, by rw [hh]; ring, by rw [hi]; ring⟩

/-- The `σ`-`x₁` move and all its multiples are achievable. -/
theorem selLamThreePlus_zero_two (c : gr3R) :
    selLamThreePlus A B C D E F T S P Q R ⟨0, 0, 0, 0, 0, 0, 0, 0, c * R, 0⟩ :=
  ⟨0, 0, 0, 0, 0, 0, 0, c, 0, 0, by ring, by ring⟩

/-- …the `x₁`-`U` move and all its multiples. -/
theorem selLamThreePlus_two_handleU (c : gr3R) :
    selLamThreePlus A B C D E F T S P Q R
      ⟨0, 0, 0, 0, 0, 0, 0, c * (P * C - Q * A), c * (Q * E), 0⟩ :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, c, 0, by ring, by ring⟩

/-- …and the `x₁`-`V` move. -/
theorem selLamThreePlus_two_handleV (c : gr3R) :
    selLamThreePlus A B C D E F T S P Q R
      ⟨0, 0, 0, 0, 0, 0, 0, c * (P * D - Q * B), c * (Q * F), 0⟩ :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, c, by ring, by ring⟩

/-- ⭐⭐ **The transport, `U`-slot**: at a stage-three survivor of the witness, if the
`Λ₃⁺`-move `(zh, zi)` pairs to a **unit** against the `V`-slot's outer columns `(F, B)`, then
**every** class-four residue dies by one explicit achievable move.  The move is a scalar
multiple of `(zh, zi)`, so it stays inside `Λ₃⁺` whenever `(zh, zi)` does. -/
theorem selLiftWit_complete_odd_plus {zh zi rr res : gr3R}
    (hmem : ∀ c : gr3R, selLamThreePlus A B C D E F T S P Q R
      ⟨0, 0, 0, 0, 0, 0, 0, c * zh, c * zi, 0⟩)
    (hmu : rr * (zh * F - zi * B) = 1)
    (h5 : sqRelWord (selLiftWit h j A B C D E F T S P Q R) = liftC res) :
    ∃ z₃ : SqU5 gr3R, z₃.IsGaThree ∧ selLamThreePlus A B C D E F T S P Q R z₃ ∧
      sqRelWord (selLift j (selLiftWit h j A B C D E F T S P Q R) 1 1 z₃ 1) = 1 := by
  refine ⟨⟨0, 0, 0, 0, 0, 0, 0, -(rr * res) * zh, -(rr * res) * zi, 0⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hmem (-(rr * res)), ?_⟩
  have hfix : (⟨0, 0, 0, 0, 0, 0, 0, -(rr * res) * zh, -(rr * res) * zi, 0⟩ : SqU5 gr3R)
      = ⟨0, 0, 0, 0, 0, 0, 0, -(rr * res * zh), -(rr * res * zi), 0⟩ := by
    ext <;> ring
  rw [hfix]
  refine sqRelWord_selLift_eq_one_odd (zh := zh) (zi := zi) (rr := rr) h5 ?_
  rw [selLiftWit_handleV]
  linear_combination hmu

/-- ⭐⭐ **The transport, `V`-slot**: the mirror, pairing against the `U`-slot's outer
columns `(A, E)`. -/
theorem selLiftWit_complete_odd_plus' {zh zi rr res : gr3R}
    (hmem : ∀ c : gr3R, selLamThreePlus A B C D E F T S P Q R
      ⟨0, 0, 0, 0, 0, 0, 0, c * zh, c * zi, 0⟩)
    (hmu : rr * (A * zi - E * zh) = 1)
    (h5 : sqRelWord (selLiftWit h j A B C D E F T S P Q R) = liftC res) :
    ∃ z₄ : SqU5 gr3R, z₄.IsGaThree ∧ selLamThreePlus A B C D E F T S P Q R z₄ ∧
      sqRelWord (selLift j (selLiftWit h j A B C D E F T S P Q R) 1 1 1 z₄) = 1 := by
  refine ⟨⟨0, 0, 0, 0, 0, 0, 0, -(rr * res) * zh, -(rr * res) * zi, 0⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hmem (-(rr * res)), ?_⟩
  have hfix : (⟨0, 0, 0, 0, 0, 0, 0, -(rr * res) * zh, -(rr * res) * zi, 0⟩ : SqU5 gr3R)
      = ⟨0, 0, 0, 0, 0, 0, 0, -(rr * res * zh), -(rr * res * zi), 0⟩ := by
    ext <;> ring
  rw [hfix]
  refine sqRelWord_selLift_eq_one_odd' (zh := zh) (zi := zi) (rr := rr) h5 ?_
  rw [selLiftWit_handleU]
  linear_combination hmu

/-- ⭐⭐ **The `R·B` completion**: where `R·B` is odd, the `σ`-`x₁` move kills every
class-four residue at the witness.  This is the pairing the committed engine sees only as
`2·R·B`, and it is exactly what covers the recorded dead-end corners. -/
theorem selLiftWit_complete_odd_rb (hκ : selPar (R * B) = 1) {res : gr3R}
    (h5 : sqRelWord (selLiftWit h j A B C D E F T S P Q R) = liftC res) :
    ∃ z₃ : SqU5 gr3R, z₃.IsGaThree ∧ selLamThreePlus A B C D E F T S P Q R z₃ ∧
      sqRelWord (selLift j (selLiftWit h j A B C D E F T S P Q R) 1 1 z₃ 1) = 1 := by
  have h3 : selPar ((0 : gr3R) * F - R * B) = 1 := by
    have hsplit : (0 : gr3R) * F - R * B = R * B + 2 * (-(R * B)) := by ring
    rw [hsplit, selPar_add, selPar_two_mul, add_zero]
    exact hκ
  obtain ⟨rr, hrr⟩ := gr3R_exists_inv_of_odd _ h3
  refine selLiftWit_complete_odd_plus (zh := 0) (zi := R) (rr := rr)
    (fun c => ?_) (by linear_combination hrr) h5
  have hc : (⟨0, 0, 0, 0, 0, 0, 0, c * 0, c * R, 0⟩ : SqU5 gr3R)
      = ⟨0, 0, 0, 0, 0, 0, 0, 0, c * R, 0⟩ := by ext <;> ring
  rw [hc]
  exact selLamThreePlus_zero_two c

/-- ⭐ **The mirror `A·R` completion**, through the `V`-handle slot. -/
theorem selLiftWit_complete_odd_ar (hκ : selPar (A * R) = 1) {res : gr3R}
    (h5 : sqRelWord (selLiftWit h j A B C D E F T S P Q R) = liftC res) :
    ∃ z₄ : SqU5 gr3R, z₄.IsGaThree ∧ selLamThreePlus A B C D E F T S P Q R z₄ ∧
      sqRelWord (selLift j (selLiftWit h j A B C D E F T S P Q R) 1 1 1 z₄) = 1 := by
  have h3 : selPar (A * R - E * 0) = 1 := by
    have hsplit : A * R - E * (0 : gr3R) = A * R + 2 * 0 := by ring
    rw [hsplit, selPar_add, selPar_two_mul, add_zero]
    exact hκ
  obtain ⟨rr, hrr⟩ := gr3R_exists_inv_of_odd _ h3
  refine selLiftWit_complete_odd_plus' (zh := 0) (zi := R) (rr := rr)
    (fun c => ?_) (by linear_combination hrr) h5
  have hc : (⟨0, 0, 0, 0, 0, 0, 0, c * 0, c * R, 0⟩ : SqU5 gr3R)
      = ⟨0, 0, 0, 0, 0, 0, 0, 0, c * R, 0⟩ := by ext <;> ring
  rw [hc]
  exact selLamThreePlus_zero_two c

end GaTwoMoves

/-! ### The recorded dead end, killed

`GradedContainFour`'s last concrete instance certifies that at the binder corner
`(A,…,S) = (0, 1, 1, 1, 2, 0, 2, 0)` with halves `(1, 3, 1)` the witness is a stage-three
survivor with the **odd** residue `5` and that **no** `selLamThree`-achievable refinement
kills it.  Here it is killed, by the fifth power of the honest commutator `⁅σ, x₁⁆` on the
`U`-handle slot: `(h, i) = (0, 5·R) = (0, 5)`, a move whose double the committed lattice
contains but which it does not itself contain.
The two statements are consistent: the obstruction theorem quantifies over `selLamThree`, and
this move lies in `selLamThreePlus \ selLamThree`.  A second, independent corner
`(0, 1, 1, 1, 2, 4, 2, 0)` with halves `(1, 3, 3)` runs the same way. -/

/-- The `σ`-`x₁` commutator at the dead-end corner is the `γ₃`-element `(0, 1)`. -/
example : commP (selLiftWit 1 0 0 1 1 1 2 0 2 0 1 3 1 0)
    (selLiftWit 1 0 0 1 1 1 2 0 2 0 1 3 1 2)
      = (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩ : SqU5 gr3R) := by decide

/-- The witness at the dead-end corner is a stage-three survivor with odd residue `5`. -/
example : sqRelWord (selLiftWit 1 0 0 1 1 1 2 0 2 0 1 3 1) = liftC (5 : gr3R) := by decide

/-- The four committed odd-regime completions are all silent there: `κ₄ = B·D·F`,
`κ₄' = A·C·E`, `B·C·E` and `A·D·F` are even, and so are the other four generator pairings
(`scripts/w54_gamma2/results/w54inst.txt`); the new pairing `R·B = 1` is odd. -/
example : selPar ((1 : gr3R) * 1 * 0) = 0 ∧ selPar ((0 : gr3R) * (1 * 2)) = 0
    ∧ selPar ((1 : gr3R) * (1 * 2)) = 0 ∧ selPar ((0 : gr3R) * (1 * 0)) = 0
    ∧ selPar ((1 : gr3R) * 1) = 1 := by decide

/-- ⭐⭐ **The kill**: five times the `σ`-`x₁` commutator on the `U`-handle slot kills the
relator at the recorded dead-end corner. -/
example : sqRelWord (selLift 0 (selLiftWit 1 0 0 1 1 1 2 0 2 0 1 3 1) 1 1
    ⟨0, 0, 0, 0, 0, 0, 0, 0, 5, 0⟩ 1) = 1 := by decide

/-- …through the general theorem, with `R·B = 1` odd. -/
example : ∃ z₃ : SqU5 gr3R, z₃.IsGaThree ∧ selLamThreePlus 0 1 1 1 2 0 2 0 1 3 1 z₃ ∧
    sqRelWord (selLift 0 (selLiftWit 1 0 0 1 1 1 2 0 2 0 1 3 1) 1 1 z₃ 1) = 1 :=
  selLiftWit_complete_odd_rb (by decide) (res := 5) (by decide)

/-- The second corner: an odd residue `7`, again killed by an `R`-multiple move. -/
example : sqRelWord (selLiftWit 1 0 0 1 1 1 2 4 2 0 1 3 3) = liftC (7 : gr3R) := by decide

/-- …and its kill through the same theorem. -/
example : ∃ z₃ : SqU5 gr3R, z₃.IsGaThree ∧ selLamThreePlus 0 1 1 1 2 4 2 0 1 3 3 z₃ ∧
    sqRelWord (selLift 0 (selLiftWit 1 0 0 1 1 1 2 4 2 0 1 3 3) 1 1 z₃ 1) = 1 :=
  selLiftWit_complete_odd_rb (by decide) (res := 7) (by decide)

/-! ## §4 Axiom pins

Committed prints for every public declaration of this file: all **std-3** (`propext`,
`Classical.choice`, `Quot.sound`) or a subset; no census axiom is reachable.  Every `decide`
is on `ZMod 8`, `ZMod 2`, `SqU5 (ZMod 8)` or tuples and words over them. -/

section AxiomPins

#print axioms gaTwoPair
#print axioms gaTwoPair_eq_u5Comm4
#print axioms gaTwoPairL
#print axioms gaTwoPairR
#print axioms sqFoxX
#print axioms gaTwo_swap
#print axioms SqU5.handleWord_b
#print axioms SqU5.handleWord_c
#print axioms SqU5.handleWord_isGaTwo
#print axioms SqU5.handleWord_e
#print axioms SqU5.handleWord_g
#print axioms gaTwoCorr
#print axioms gaTwoQuad
#print axioms gaTwoCore
#print axioms gaTwoCore_isGaTwo
#print axioms sqWord_mul_gaTwo
#print axioms gaTwoHandle
#print axioms gaTwoHandle_isGaThree
#print axioms commP_mul_gaTwo
#print axioms handleWord_mul_gaTwo_all
#print axioms sqHandlePairE
#print axioms sqHandlePairG
#print axioms gaTwoShift
#print axioms sqRelWord_gaTwoDress
#print axioms selLiftWit_commP_zero_two
#print axioms selLiftWit_commP_two_handleU
#print axioms selLiftWit_commP_two_handleV
#print axioms selLamThreePlus
#print axioms selLamThree_plus
#print axioms selLamThreePlus_zero_two
#print axioms selLamThreePlus_two_handleU
#print axioms selLamThreePlus_two_handleV
#print axioms selLiftWit_complete_odd_plus
#print axioms selLiftWit_complete_odd_plus'
#print axioms selLiftWit_complete_odd_rb
#print axioms selLiftWit_complete_odd_ar

end AxiomPins

end SqCore

end Dyadic

end GQ2

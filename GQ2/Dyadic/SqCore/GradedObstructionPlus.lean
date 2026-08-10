/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedGammaTwo

/-!
# W55-OBST: the class-four obstruction on the extended lattice, and at the `γ₂` level

`GradedContainFour` committed the even-regime obstruction `sqRelWord_selLift_ne_one`
**relative to the committed lattice** `selLamThree`: where the eight committed generator
pairings are even, an odd class-four residue outlives every `Λ₃`-achievable engine
refinement.  `GradedGammaTwo` then showed that `Λ₃` is not the honest achievable set: three
commutators of the witness's `x₁`-slot letter against `σ`, `U` and `V` are `γ₂`-level moves
whose `(h, i)`-data are the exact **halves** of committed `Λ₃`-generators, and the extended
lattice `selLamThreePlus` contains them.  This file retires the resulting caveat.

* ⭐⭐ **The migrated obstruction** (`selLamThreePlus_pair_even`, `_pair_even'`,
  `sqRelWord_selLift_ne_one_plus`): the exact analogue of `sqRelWord_selLift_ne_one` over
  `selLamThreePlus`, whose hypotheses are the eight committed generator pairings together
  with the **six new pairings** of the `γ₂`-level moves (`R·B`, `A·R`,
  `(P·C − Q·A)·F − Q·E·B`, `A·Q·E − E·(P·C − Q·A)`, `(P·D − Q·B)·F − Q·F·B`,
  `A·Q·F − E·(P·D − Q·B)`).  This is the statement `docs/dyadic/w54-gamma2-note.md` §7
  item 1 asks for, in the `selLift` layer.
* ⭐⭐ **The `γ₂`-level obstruction** (`gaTwoShift_selLiftWit_j_even`,
  `sqRelWord_conFourDress_selLiftWit_ne_one`, `sqRelWord_selLamTwo_ne_one`): the same
  conclusion against a **five-slot `γ₂`-dressing** of the whole frame, through the committed
  translation identity `sqRelWord_gaTwoDress`.  The class-four defect of such a dressing has
  the quadratic block `gaTwoQuad`, the correction block `gaTwoCorr`, the handle collection
  terms and the graded Fox pairings; at the witness every block except the two marked handle
  Fox pairings is **even**, so the odd residue survives.  No stage hypothesis is needed: the
  class-two row of a would-be kill supplies the one fact (`(z 2).e` even) the argument
  consumes beyond the parity rows.
* **The two ingredients the note predicted**, both parity-row arguments as it said:
  `selLiftWit_commP_g_even` and `selLiftWit_two_sq_g` (⭐ **ingredient (i)**, every generator
  of the achievable `γ₂` lattice has even `g`-column, whence `gaTwoQuad` is even) and
  `gaTwoCorr_selLiftWit_even` (⭐ **ingredient (iii)**, the nine correction coefficients are
  even at the witness, on the `hd` parity row alone).

## Honest scope, and a refinement of the note's route

The note's §7 sketch lists four ingredients and asserts in (iv) that "the surviving Fox
pairings are the fourteen hypotheses".  **The hypothesis set is right; the sketch is one step
short.**  The class-four graded Fox pairing is
`gaTwoPair z L = z.h·L.d − z.i·L.a + z.e·L.g − z.g·L.e + z.g·(L.a·L.b) − z.f·(L.a·L.d)`, and
its **last** term also survives mod 2 at the two marked handle slots, contributing
`z_U.f·(B·F)` and `z_V.f·(A·E)`.  Neither `A·E` nor `B·F` is even as a consequence of the
fourteen alone: at `(A, B, C, D, E, F, T, S) = (1, 0, 0, 0, 1, 0, 0, 0)` with halves
`(P, Q, R, W2) = (0, 0, 0, 0)` all four parity rows hold, all fourteen pairings **vanish**,
and `A·E = 1` is odd (the instances at the end of the file check this by `decide`).  What
closes the gap is the conclusion's own hypothesis: seven of the fourteen together with the
**oddness of the class-four residue**, read through the committed selection bit
`selLiftWit_bit`, force `A·E` and `B·F` even (`selLiftWit_ae_bf_even_of_odd`, a `512`-case
𝔽₂ core).  So `sqRelWord_selLamTwo_ne_one` carries exactly the note's fourteen hypotheses,
and the extra input the route needs is not an extra hypothesis but a feedback: the odd residue
constrains the marking, not only the residue line.  Consistently, all ten mod-2 classes of the
note's residual `33792` corners have `A` and `B` **both even** (§5.2), so both terms die
outright there.

Everything below is a theorem about the committed test group `SqU5` and the committed
witness.  What is *modelled* rather than proved is unchanged from `GradedGammaTwo`: the
achievability convention under which a commutator of two frame slots is a legitimate
dressing.  `selLamTwo`, the lattice the `γ₂`-level obstruction quantifies over, is an
**over-approximation** of the honest achievable lattice (`γ₂`-shaped, even `g`-column,
`(h, i)`-data in `Λ₃⁺`), so the obstruction is correspondingly stronger; the three `γ₂`-level
generators of `GradedGammaTwo` §3 are exhibited inside it (`selLamTwo_commP_zero_two`,
`_two_handleU`, `_two_handleV`) and it is closed under the group law
(`selLamTwo_one`, `selLamTwo_mul`).

## Contents

* **§1** the parity toolkit over `ℤ/8` and the Frobenius-forces-even lemma;
* **§2** ⭐⭐ the `Λ₃⁺` parity engine and the migrated obstruction
  `sqRelWord_selLift_ne_one_plus`;
* **§3** ⭐ ingredient (i): the even `g`-column of the achievable `γ₂` generators;
* **§4** ⭐ ingredient (iii): the correction block is even at the witness, with the three core
  Fox pairings and the handle terms;
* **§5** ⭐⭐ the `γ₂`-level obstruction: the `j`-row of `gaTwoShift` at the witness is even,
  the `f`-column reduction, the lattice `selLamTwo`, and the two obstruction theorems;
* **§6** the bridge corollaries carrying every committed `selLamThree` conclusion onto
  `selLamThreePlus`;
* **§7** committed axiom prints (all std-3).

Companion memo: `docs/dyadic/w54-gamma2-note.md` (§7 item 1 is this file's target, §7 item 2
is §6).
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The parity toolkit

Evenness in `ℤ/8` in the shape the committed parity lemmas use, `∃ k, x = 2·k`, with the
half always exhibited.  The one genuinely arithmetic fact is `gr3R_even_of_frobenius`: the
Frobenius weights `(−4, 2)` of the relator's exponent slots can only kill a class-two row of
the dressed relator by making the `x₁`-slot's own class-two coordinate even. -/

section ParityToolkit

private theorem ev_add {x y : gr3R} (hx : ∃ k, x = 2 * k) (hy : ∃ k, y = 2 * k) :
    ∃ k, x + y = 2 * k := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a + b, by rw [ha, hb]; ring⟩

private theorem ev_mul_left (y : gr3R) {x : gr3R} (hx : ∃ k, x = 2 * k) :
    ∃ k, y * x = 2 * k := by
  obtain ⟨a, ha⟩ := hx
  exact ⟨y * a, by rw [ha]; ring⟩

private theorem ev_sum {n : ℕ} (f : Fin n → gr3R) (hf : ∀ k, ∃ c, f k = 2 * c) :
    ∃ c, ∑ k, f k = 2 * c := by
  choose c hc using hf
  refine ⟨∑ k, c k, ?_⟩
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => hc k

/-- **The Frobenius weights force the `x₁`-slot even**: if the `(−4, 2)`-combination of two
`ℤ/8`-elements vanishes then the second is even.  This is the whole of the note's ingredient
(ii): a `γ₂`-dressing that leaves a class-two row of the relator alone has an even class-two
coordinate on the `x₁`-slot, which is what kills the `x₁`-slot's graded Fox pairing. -/
theorem gr3R_even_of_frobenius : ∀ a b : gr3R, -4 * a + 2 * b = 0 → ∃ k, b = 2 * k := by
  decide

end ParityToolkit

/-! ## §2 ⭐⭐ The `Λ₃⁺` parity engine and the migrated obstruction

The transposition of `GradedContainFour` §3b onto the extended lattice.  `selLamThreePlus`
has ten generators rather than seven: the four odd-capable `Λ₃` generators, the three even
`x₁`-pairings, and the three `γ₂`-level moves `(0, R)`, `(P·C − Q·A, Q·E)`,
`(P·D − Q·B, Q·F)`.  A `Λ₃⁺`-achievable pair therefore pairs evenly against a column pair as
soon as **fourteen** pairings are even: the eight committed ones and the six new ones the
`γ₂`-level moves contribute, `R·B`, `A·R`, `(P·C − Q·A)·F − Q·E·B`,
`A·Q·E − E·(P·C − Q·A)`, `(P·D − Q·B)·F − Q·F·B`, `A·Q·F − E·(P·D − Q·B)` at the witness's
handle columns. -/

section PlusParityObstruction

variable {h : ℕ} {j : Fin h}

/-- ⭐ **`Λ₃⁺` pairs evenly against a column pair with even generator pairings** (the
`U`-slot orientation `z.h·vd − z.i·va`).  Beyond `selLamThree_pair_even`'s four hypotheses,
the three `γ₂`-level generators contribute the three new pairings `R·va`,
`(P·C − Q·A)·vd − Q·E·va` and `(P·D − Q·B)·vd − Q·F·va`; the three even `Λ₃`-generators
contribute evenly outright, as before. -/
theorem selLamThreePlus_pair_even {A B C D E F T S P Q R va vd : gr3R} {z : SqU5 gr3R}
    (hz : selLamThreePlus A B C D E F T S P Q R z)
    (h₁ : ∃ k, (2 * (A * C)) * vd + (C * E) * va = 2 * k)
    (h₂ : ∃ k, (A * D + B * C) * vd + (D * E) * va = 2 * k)
    (h₃ : ∃ k, (A * D + B * C) * vd + (C * F) * va = 2 * k)
    (h₄ : ∃ k, (2 * (B * D)) * vd + (D * F) * va = 2 * k)
    (h₅ : ∃ k, R * va = 2 * k)
    (h₆ : ∃ k, (P * C - Q * A) * vd - (Q * E) * va = 2 * k)
    (h₇ : ∃ k, (P * D - Q * B) * vd - (Q * F) * va = 2 * k) :
    ∃ k, z.h * vd - z.i * va = 2 * k := by
  obtain ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, t₁, t₂, t₃, hzh, hzi⟩ := hz
  obtain ⟨k₁, hk₁⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  obtain ⟨k₃, hk₃⟩ := h₃
  obtain ⟨k₄, hk₄⟩ := h₄
  obtain ⟨k₅, hk₅⟩ := h₅
  obtain ⟨k₆, hk₆⟩ := h₆
  obtain ⟨k₇, hk₇⟩ := h₇
  refine ⟨-(r₁ * k₁) - r₂ * k₂ - r₃ * k₃ - r₄ * k₄
    + (r₆ * ((Q * A - P * C) * vd - (R * T - Q * E) * va)
      + r₇ * ((Q * B - P * D) * vd - (R * S - Q * F) * va))
    - r₅ * (R * va) - t₁ * k₅ + t₂ * k₆ + t₃ * k₇, ?_⟩
  rw [hzh, hzi]
  linear_combination (-r₁) * hk₁ - r₂ * hk₂ - r₃ * hk₃ - r₄ * hk₄ - t₁ * hk₅ + t₂ * hk₆
    + t₃ * hk₇

/-- ⭐ …and the mirror orientation `ua·z.i − ud·z.h` of the `V`-slot increment. -/
theorem selLamThreePlus_pair_even' {A B C D E F T S P Q R ua ud : gr3R} {z : SqU5 gr3R}
    (hz : selLamThreePlus A B C D E F T S P Q R z)
    (h₁ : ∃ k, ua * (C * E) + ud * (2 * (A * C)) = 2 * k)
    (h₂ : ∃ k, ua * (D * E) + ud * (A * D + B * C) = 2 * k)
    (h₃ : ∃ k, ua * (C * F) + ud * (A * D + B * C) = 2 * k)
    (h₄ : ∃ k, ua * (D * F) + ud * (2 * (B * D)) = 2 * k)
    (h₅ : ∃ k, ua * R = 2 * k)
    (h₆ : ∃ k, ua * (Q * E) - ud * (P * C - Q * A) = 2 * k)
    (h₇ : ∃ k, ua * (Q * F) - ud * (P * D - Q * B) = 2 * k) :
    ∃ k, ua * z.i - ud * z.h = 2 * k := by
  obtain ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, t₁, t₂, t₃, hzh, hzi⟩ := hz
  obtain ⟨k₁, hk₁⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  obtain ⟨k₃, hk₃⟩ := h₃
  obtain ⟨k₄, hk₄⟩ := h₄
  obtain ⟨k₅, hk₅⟩ := h₅
  obtain ⟨k₆, hk₆⟩ := h₆
  obtain ⟨k₇, hk₇⟩ := h₇
  refine ⟨r₁ * k₁ + r₂ * k₂ + r₃ * k₃ + r₄ * k₄
    + (r₅ * (ua * R)
      + r₆ * (ua * (R * T - Q * E) - ud * (Q * A - P * C))
      + r₇ * (ua * (R * S - Q * F) - ud * (Q * B - P * D)))
    + t₁ * k₅ + t₂ * k₆ + t₃ * k₇, ?_⟩
  rw [hzh, hzi]
  linear_combination r₁ * hk₁ + r₂ * hk₂ + r₃ * hk₃ + r₄ * hk₄ + t₁ * hk₅ + t₂ * hk₆
    + t₃ * hk₇

/-- ⭐⭐ **The migrated even-regime obstruction**: a class-four residue of **odd** parity
outlives every `Λ₃⁺`-achievable engine refinement, at any marking where the eight committed
generator pairings **and** the six new `γ₂`-level pairings are even.  This is
`GradedContainFour.sqRelWord_selLift_ne_one` with its lattice replaced by the extended one:
the dead ends it certifies are no longer dead ends of the `Λ₃` engine alone, and by the
containment `selLamThree_plus` every hypothesis of the committed statement is a hypothesis
of this one. -/
theorem sqRelWord_selLift_ne_one_plus {A B C D E F T S P Q R : gr3R}
    {m : Fin (sqRank h) → SqU5 gr3R} {w₁ w₂ z₃ z₄ : SqU5 gr3R}
    (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour) (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (hz₃L : selLamThreePlus A B C D E F T S P Q R z₃)
    (hz₄L : selLamThreePlus A B C D E F T S P Q R z₄)
    (h₁ : ∃ k, (2 * (A * C)) * (m (sqHandleIdxV j)).d
        + (C * E) * (m (sqHandleIdxV j)).a = 2 * k)
    (h₂ : ∃ k, (A * D + B * C) * (m (sqHandleIdxV j)).d
        + (D * E) * (m (sqHandleIdxV j)).a = 2 * k)
    (h₃ : ∃ k, (A * D + B * C) * (m (sqHandleIdxV j)).d
        + (C * F) * (m (sqHandleIdxV j)).a = 2 * k)
    (h₄ : ∃ k, (2 * (B * D)) * (m (sqHandleIdxV j)).d
        + (D * F) * (m (sqHandleIdxV j)).a = 2 * k)
    (h₅ : ∃ k, R * (m (sqHandleIdxV j)).a = 2 * k)
    (h₆ : ∃ k, (P * C - Q * A) * (m (sqHandleIdxV j)).d
        - (Q * E) * (m (sqHandleIdxV j)).a = 2 * k)
    (h₇ : ∃ k, (P * D - Q * B) * (m (sqHandleIdxV j)).d
        - (Q * F) * (m (sqHandleIdxV j)).a = 2 * k)
    (h₁' : ∃ k, (m (sqHandleIdxU j)).a * (C * E)
        + (m (sqHandleIdxU j)).d * (2 * (A * C)) = 2 * k)
    (h₂' : ∃ k, (m (sqHandleIdxU j)).a * (D * E)
        + (m (sqHandleIdxU j)).d * (A * D + B * C) = 2 * k)
    (h₃' : ∃ k, (m (sqHandleIdxU j)).a * (C * F)
        + (m (sqHandleIdxU j)).d * (A * D + B * C) = 2 * k)
    (h₄' : ∃ k, (m (sqHandleIdxU j)).a * (D * F)
        + (m (sqHandleIdxU j)).d * (2 * (B * D)) = 2 * k)
    (h₅' : ∃ k, (m (sqHandleIdxU j)).a * R = 2 * k)
    (h₆' : ∃ k, (m (sqHandleIdxU j)).a * (Q * E)
        - (m (sqHandleIdxU j)).d * (P * C - Q * A) = 2 * k)
    (h₇' : ∃ k, (m (sqHandleIdxU j)).a * (Q * F)
        - (m (sqHandleIdxU j)).d * (P * D - Q * B) = 2 * k)
    (hodd : selPar (sqRelWord m).j = 1) :
    sqRelWord (selLift j m w₁ w₂ z₃ z₄) ≠ 1 := by
  obtain ⟨k₃, hk₃⟩ := selLamThreePlus_pair_even hz₃L h₁ h₂ h₃ h₄ h₅ h₆ h₇
  obtain ⟨k₄, hk₄⟩ := selLamThreePlus_pair_even' hz₄L h₁' h₂' h₃' h₄' h₅' h₆' h₇'
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

end PlusParityObstruction

/-! ## §3 ⭐ Ingredient (i): the achievable `γ₂` lattice has an even `g`-column

The note's §2.3, as theorems.  At the witness the `(c, d)`-columns of the five frame slots
are `(0, 0)` for `σ` and `x₁`, `(−2·Q, 2·W₂)` for the `x₀`-slot (the `he`- and `hb`-parity
rows), `(C, E)` for `U` and `(D, F)` for `V`; every other slot is trivial.  So the only
commutator whose `g`-column `p.c·q.d − p.d·q.c` is not even for trivial reasons is `⁅U, V⁆`,
whose value `C·F − E·D` is `−2·R` by the `hg`-row.  The `x₁`-square has `g = 2·R`, triple
commutators are `γ₃`-shaped, and `g` is additive on products of `γ₂`-elements, so the whole
lattice has even `g`.  This is what makes the quadratic block `gaTwoQuad` of the class-four
defect even, and the note's "the `γ₂` transport is a mod-2 **affine** phenomenon" a
theorem. -/

section EvenG

variable {h : ℕ} {j : Fin h} {A B C D E F T S P Q R W2 : gr3R}

/-- The `(c, d)`-column of any witness slot is either even in both entries, or the `U`-letter
`(C, E)`, or the `V`-letter `(D, F)`. -/
private theorem selLiftWit_cd_cases (he : 2 * Q + (T * D - S * C) = 0)
    (hb : 2 * W2 + (E * S - F * T) = 0) (i : Fin (sqRank h)) :
    ((∃ kc, (selLiftWit h j A B C D E F T S P Q R i).c = 2 * kc)
        ∧ ∃ kd, (selLiftWit h j A B C D E F T S P Q R i).d = 2 * kd)
      ∨ ((selLiftWit h j A B C D E F T S P Q R i).c = C
        ∧ (selLiftWit h j A B C D E F T S P Q R i).d = E)
      ∨ ((selLiftWit h j A B C D E F T S P Q R i).c = D
        ∧ (selLiftWit h j A B C D E F T S P Q R i).d = F) := by
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · exact Or.inl ⟨⟨0, by simp [selLiftWit_zero]⟩, ⟨0, by simp [selLiftWit_zero]⟩⟩
  · exact Or.inl ⟨⟨-Q, by simp only [selLiftWit_one]; linear_combination he⟩,
      ⟨W2, by simp only [selLiftWit_one]; linear_combination -hb⟩⟩
  · exact Or.inl ⟨⟨0, by simp [selLiftWit_two]⟩, ⟨0, by simp [selLiftWit_two]⟩⟩
  · by_cases hj : j' = j
    · subst hj
      exact Or.inr (Or.inl ⟨by simp only [selLiftWit_handleU], by simp only [selLiftWit_handleU]⟩)
    · exact Or.inl ⟨⟨0, by simp [selLiftWit_handleU_ne hj]⟩,
        ⟨0, by simp [selLiftWit_handleU_ne hj]⟩⟩
  · by_cases hj : j' = j
    · subst hj
      exact Or.inr (Or.inr ⟨by simp only [selLiftWit_handleV], by simp only [selLiftWit_handleV]⟩)
    · exact Or.inl ⟨⟨0, by simp [selLiftWit_handleV_ne hj]⟩,
        ⟨0, by simp [selLiftWit_handleV_ne hj]⟩⟩

/-- ⭐ **Ingredient (i), the ten frame-slot commutators**: the `g`-column of a commutator of
any two slots of the witness frame is **even**, consuming the `he`-, `hg`- and `hb`-parity
rows.  These are the generators of `γ₂(im Φ)` that are not `γ₃`-shaped, so with the
`x₁`-square (`selLiftWit_two_sq_g`) and the additivity of `g` on `γ₂` (`gaTwo_mul_g_even`)
this is the note's §2.3 in full. -/
theorem selLiftWit_commP_g_even (he : 2 * Q + (T * D - S * C) = 0)
    (hg : 2 * R + (C * F - D * E) = 0) (hb : 2 * W2 + (E * S - F * T) = 0)
    (i₁ i₂ : Fin (sqRank h)) :
    ∃ k, (commP (selLiftWit h j A B C D E F T S P Q R i₁)
        (selLiftWit h j A B C D E F T S P Q R i₂)).g = 2 * k := by
  rw [SqU5.commP_g]
  rcases selLiftWit_cd_cases (W2 := W2) he hb i₁ with ⟨⟨c₁, hc₁⟩, ⟨d₁, hd₁⟩⟩ | ⟨hc₁, hd₁⟩ |
      ⟨hc₁, hd₁⟩ <;>
    rcases selLiftWit_cd_cases (W2 := W2) he hb i₂ with ⟨⟨c₂, hc₂⟩, ⟨d₂, hd₂⟩⟩ | ⟨hc₂, hd₂⟩ |
      ⟨hc₂, hd₂⟩ <;>
    rw [hc₁, hd₁, hc₂, hd₂]
  · exact ⟨2 * (c₁ * d₂ - d₁ * c₂), by ring⟩
  · exact ⟨c₁ * E - d₁ * C, by ring⟩
  · exact ⟨c₁ * F - d₁ * D, by ring⟩
  · exact ⟨C * d₂ - E * c₂, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨-R, by linear_combination hg⟩
  · exact ⟨D * d₂ - F * c₂, by ring⟩
  · exact ⟨R, by linear_combination -hg⟩
  · exact ⟨0, by ring⟩

/-- ⭐ **Ingredient (i), the `x₁`-square**: the remaining non-`γ₃` generator of the
achievable lattice has `g`-column `2·R`, even with no hypothesis at all. -/
theorem selLiftWit_two_sq_g :
    ((selLiftWit h j A B C D E F T S P Q R 2)
        * (selLiftWit h j A B C D E F T S P Q R 2)).g = 2 * R := by
  simp only [selLiftWit_two, SqU5.mul_g]
  ring

/-- **Even `g` is additive on `γ₂`**: the `g`-column of a product of `γ₂`-elements is the sum
of the two, so evenness passes to the whole lattice the generators span. -/
theorem gaTwo_mul_g_even {p q : SqU5 gr3R} (hp : p.IsGaTwo)
    (hpg : ∃ k, p.g = 2 * k) (hqg : ∃ k, q.g = 2 * k) : ∃ k, (p * q).g = 2 * k := by
  obtain ⟨a, ha⟩ := hpg
  obtain ⟨b, hb⟩ := hqg
  exact ⟨a + b, by rw [SqU5.mul_g, ha, hb, hp.2.2.1]; ring⟩

/-- A `γ₃`-shaped element (a triple commutator, say) has `g`-column zero. -/
theorem gaThree_g_even {p : SqU5 gr3R} (hp : p.IsGaThree) : ∃ k, p.g = 2 * k :=
  ⟨0, by rw [hp.2.2.2.2.2.2]; ring⟩

end EvenG

/-! ## §4 ⭐ Ingredient (iii): the correction block and the core pairings at the witness

The four blocks of the class-four core shift, one lemma each.  Only the `x₁`-slot's own Fox
pairing needs anything beyond the parity rows and even `g`: it is `z₂.e·R − z₂.g·P`, and the
note's ingredient (ii) supplies `z₂.e` even.  The correction block `gaTwoCorr` collapses at
the witness to six terms whose coefficients are `−4·x.c·x.d`, `8·x.a·x.d`, `−x.a`,
`−20·x.c·x.d`, `130·x.a·x.d` and `13·x.a`, and `x.a = B·T − A·S = 2·P` by the `hd`-row: the
whole block is even on that one row. -/

section WitnessBlocks

variable {h : ℕ} {j : Fin h} {A B C D E F T S P Q R W2 : gr3R}
  {z : Fin (sqRank h) → SqU5 gr3R}

/-- The `σ`-slot's graded Fox pairing against the `x₀`-letter is even: the letter's `a`- and
`d`-columns are the halves `2·P` and `2·W₂`, its `e`-column is visibly even and its `b`- and
`g`-columns vanish. -/
theorem gaTwoPair_selLiftWit_zero_even (hd : 2 * P + (A * S - B * T) = 0)
    (hb : 2 * W2 + (E * S - F * T) = 0) :
    ∃ k, gaTwoPair (z 0) (selLiftWit h j A B C D E F T S P Q R 1) = 2 * k := by
  refine ⟨(z 0).h * W2 - (z 0).i * P + (z 0).g * (T * S * B) - 2 * ((z 0).f * (P * W2)), ?_⟩
  simp only [gaTwoPair, selLiftWit_one]
  linear_combination ((z 0).i + (z 0).f * (F * T - E * S)) * hd
    + (-(z 0).h + 2 * ((z 0).f * P)) * hb

/-- The `x₀`-slot's graded Fox pairing against the `σ`-letter `10·x₀ − σ − 8·x₁` is even with
**no** hypothesis: every column of that letter which the pairing reads carries an even
integer coefficient. -/
theorem gaTwoPair_selLiftWit_one_even :
    ∃ k, gaTwoPair (z 1) (sqFoxX (selLiftWit h j A B C D E F T S P Q R 0)
      (selLiftWit h j A B C D E F T S P Q R 1)
      (selLiftWit h j A B C D E F T S P Q R 2)) = 2 * k := by
  refine ⟨5 * ((z 1).h * (F * T - E * S)) - 5 * ((z 1).i * (B * T - A * S))
    - 4 * ((z 1).e * R) - 5 * ((z 1).g * (-(2 * (T * S * B)))) + 4 * ((z 1).g * P)
    - 5 * ((z 1).g * (B * T - A * S))
    - 50 * ((z 1).f * ((B * T - A * S) * (F * T - E * S))), ?_⟩
  simp only [gaTwoPair, sqFoxX, selLiftWit_zero, selLiftWit_one, selLiftWit_two]
  ring

/-- The `x₁`-slot's own graded Fox pairing is `z₂.e·R − z₂.g·P`: even exactly on the note's
ingredients (i) and (ii). -/
theorem gaTwoPair_selLiftWit_two_even (h2e : ∃ k, (z 2).e = 2 * k)
    (h2g : ∃ k, (z 2).g = 2 * k) :
    ∃ k, gaTwoPair (z 2) (selLiftWit h j A B C D E F T S P Q R 2) = 2 * k := by
  obtain ⟨ke, hke⟩ := h2e
  obtain ⟨kg, hkg⟩ := h2g
  refine ⟨ke * R - kg * P, ?_⟩
  simp only [gaTwoPair, selLiftWit_two, hke, hkg]
  ring

/-- ⭐ **Ingredient (iii)**: the correction block of the class-four `γ₂`-defect is **even at
the witness**, on the `hd`-parity row alone.  Six of the nine coefficients survive the
witness's vanishing columns, and each is either an even integer multiple of a product of
frame columns or a multiple of `x.a = 2·P`. -/
theorem gaTwoCorr_selLiftWit_even (hd : 2 * P + (A * S - B * T) = 0) :
    ∃ k, gaTwoCorr (selLiftWit h j A B C D E F T S P Q R 0)
      (selLiftWit h j A B C D E F T S P Q R 1) (selLiftWit h j A B C D E F T S P Q R 2)
      (z 0) (z 1) (z 2) = 2 * k := by
  refine ⟨-2 * ((z 0).e * ((D * T - C * S) * (F * T - E * S)))
    + 4 * ((z 0).f * ((B * T - A * S) * (F * T - E * S))) - (z 0).g * P
    - 10 * ((z 1).e * ((D * T - C * S) * (F * T - E * S)))
    + 65 * ((z 1).f * ((B * T - A * S) * (F * T - E * S))) + 13 * ((z 1).g * P), ?_⟩
  simp only [gaTwoCorr, selLiftWit_zero, selLiftWit_one, selLiftWit_two]
  linear_combination ((z 0).g - 13 * (z 1).g) * hd

/-- **The quadratic block is even** whenever the three core dressings have even `g`-column:
every one of its five monomials carries a `g`-factor.  This is the note's headline reading,
that the quadratic content of the `γ₂` transport is invisible mod 2 on the achievable
lattice. -/
theorem gaTwoQuad_even (h0g : ∃ k, (z 0).g = 2 * k) (h1g : ∃ k, (z 1).g = 2 * k)
    (h2g : ∃ k, (z 2).g = 2 * k) : ∃ k, gaTwoQuad (z 0) (z 1) (z 2) = 2 * k := by
  obtain ⟨a, ha⟩ := h0g
  obtain ⟨b, hb⟩ := h1g
  obtain ⟨c, hc⟩ := h2g
  refine ⟨(z 0).e * b - a * (z 1).e + 10 * ((z 1).e * b) - 8 * ((z 1).e * c)
    + (z 2).e * c, ?_⟩
  simp only [gaTwoQuad, ha, hb, hc]
  ring

end WitnessBlocks

/-! ## §5 ⭐⭐ The `γ₂`-level obstruction at the witness

The two rows of the `γ₂`-shift that the argument reads, in closed form (`gaTwoShift_e`,
`gaTwoShift_j`), the parity of the class-four row at the witness
(`gaTwoShift_selLiftWit_j_even`), and the obstruction itself.  The handle block splits into
the marked pair, where the two Fox pairings and the two `f`-column terms survive mod 2, and
the unmarked pairs, where both frame letters are trivial and only the `γ₂`-commutator of the
two dressings survives, evenly.

`selLamTwo` packages the three properties the obstruction consumes: `γ₂`-shape, even
`g`-column, and `Λ₃⁺`-achievable `(h, i)`-data.  It is an over-approximation of the honest
achievable lattice, so the obstruction over it is stronger than the obstruction over
`γ₂(im Φ)`; the three `γ₂`-level generators of `GradedGammaTwo` §3 are exhibited inside
it. -/

section GaTwoObstruction

variable {R : Type} [CommRing R] {h : ℕ}

/-- **The first class-two row of the `γ₂`-shift**: the Frobenius weights on the exponent
slots alone.  Neither the handle block nor the collection term reaches it. -/
theorem gaTwoShift_e (m z : Fin (sqRank h) → SqU5 R) :
    (gaTwoShift h m z).e = -4 * (z 1).e + 2 * (z 2).e := by
  simp only [gaTwoShift, SqU5.mul_e, liftC, gaTwoCore]
  ring

/-- ⭐ **The class-four row of the `γ₂`-shift, expanded**: the core block (Frobenius weights,
the three graded Fox pairings against the permuted letters, the correction and the quadratic
form), the summed handle block, and the central collection term by which the core's class-two
rows commute past the handle word. -/
theorem gaTwoShift_j (m z : Fin (sqRank h) → SqU5 R) :
    (gaTwoShift h m z).j
      = (-4 * (z 1).j + 2 * (z 2).j
          + (gaTwoPair (z 0) (m 1) + gaTwoPair (z 1) (sqFoxX (m 0) (m 1) (m 2))
            + gaTwoPair (z 2) (m 2))
          + gaTwoCorr (m 0) (m 1) (m 2) (z 0) (z 1) (z 2) + gaTwoQuad (z 0) (z 1) (z 2))
        + (∑ k : Fin h, (gaTwoHandle (m (sqHandleIdxU k)) (m (sqHandleIdxV k))
            (z (sqHandleIdxU k)) (z (sqHandleIdxV k))).j)
        + ((-4 * (z 1).e + 2 * (z 2).e) * sqHandlePairG h m
            - sqHandlePairE h m * (-4 * (z 1).g + 2 * (z 2).g)) := by
  simp only [gaTwoShift, SqU5.mul_j, liftC, gaTwoCore]
  ring

end GaTwoObstruction

section GaTwoWitness

variable {h : ℕ} {j : Fin h} {A B C D E F T S P Q R W2 res : gr3R}
  {z : Fin (sqRank h) → SqU5 gr3R}

/-- The handle term of an **unmarked** pair is the `γ₂`-commutator of the two dressings
alone, hence even: both frame letters are trivial there, so every pairing against them
vanishes. -/
private theorem handle_term_even_of_ne (hzg : ∀ i, ∃ k, (z i).g = 2 * k) {k : Fin h}
    (hk : k ≠ j) :
    ∃ c, (gaTwoHandle (selLiftWit h j A B C D E F T S P Q R (sqHandleIdxU k))
      (selLiftWit h j A B C D E F T S P Q R (sqHandleIdxV k))
      (z (sqHandleIdxU k)) (z (sqHandleIdxV k))).j = 2 * c := by
  obtain ⟨gU, hgU⟩ := hzg (sqHandleIdxU k)
  obtain ⟨gV, hgV⟩ := hzg (sqHandleIdxV k)
  refine ⟨(z (sqHandleIdxU k)).e * gV - gU * (z (sqHandleIdxV k)).e, ?_⟩
  rw [selLiftWit_handleU_ne hk, selLiftWit_handleV_ne hk]
  simp only [gaTwoHandle, gaTwoPair, SqU5.one_a, SqU5.one_b, SqU5.one_c, SqU5.one_d,
    SqU5.one_e, SqU5.one_g, hgU, hgV]
  ring

/-- The handle term of the **marked** pair, mod 2: the two graded Fox pairings against the
opposite handle letters, plus the two `f`-column terms `z_U.f·(B·F)` and `z_V.f·(A·E)` that
the note's §7 sketch omits.  Everything else dies on the `hg`-parity row and even `g`. -/
private theorem handle_term_even_at (hzg : ∀ i, ∃ k, (z i).g = 2 * k)
    (hg : 2 * R + (C * F - D * E) = 0)
    (hU : ∃ k, (z (sqHandleIdxU j)).h * F - (z (sqHandleIdxU j)).i * B = 2 * k)
    (hV : ∃ k, A * (z (sqHandleIdxV j)).i - E * (z (sqHandleIdxV j)).h = 2 * k)
    (hUf : ∃ k, (z (sqHandleIdxU j)).f * (B * F) = 2 * k)
    (hVf : ∃ k, (z (sqHandleIdxV j)).f * (A * E) = 2 * k) :
    ∃ c, (gaTwoHandle (selLiftWit h j A B C D E F T S P Q R (sqHandleIdxU j))
      (selLiftWit h j A B C D E F T S P Q R (sqHandleIdxV j))
      (z (sqHandleIdxU j)) (z (sqHandleIdxV j))).j = 2 * c := by
  obtain ⟨kU, hkU⟩ := hU
  obtain ⟨kV, hkV⟩ := hV
  obtain ⟨kUf, hkUf⟩ := hUf
  obtain ⟨kVf, hkVf⟩ := hVf
  obtain ⟨gU, hgU⟩ := hzg (sqHandleIdxU j)
  obtain ⟨gV, hgV⟩ := hzg (sqHandleIdxV j)
  refine ⟨kU + kV + gU * (B * S) - kUf + kVf
    + R * ((z (sqHandleIdxU j)).e + (z (sqHandleIdxV j)).e)
    + ((z (sqHandleIdxU j)).e * gV - gU * (z (sqHandleIdxV j)).e), ?_⟩
  simp only [gaTwoHandle, gaTwoPair, selLiftWit_handleU, selLiftWit_handleV, hgU, hgV]
  linear_combination hkU + hkV - hkUf + hkVf
    - ((z (sqHandleIdxU j)).e + (z (sqHandleIdxV j)).e) * hg

/-- ⭐⭐ **The class-four row of the `γ₂`-shift is even at the witness.**  The whole content
of the file's second target: the Frobenius weights, the correction block, the quadratic
block, the collection term, the two core Fox pairings and every unmarked handle term are even
outright; the `x₁`-slot's Fox pairing is even by ingredient (ii); and the marked handle term
reduces to the four surviving pairings the hypotheses supply. -/
theorem gaTwoShift_selLiftWit_j_even (hzg : ∀ i, ∃ k, (z i).g = 2 * k)
    (hd : 2 * P + (A * S - B * T) = 0) (hg : 2 * R + (C * F - D * E) = 0)
    (hb : 2 * W2 + (E * S - F * T) = 0)
    (h2e : ∃ k, (z 2).e = 2 * k)
    (hU : ∃ k, (z (sqHandleIdxU j)).h * F - (z (sqHandleIdxU j)).i * B = 2 * k)
    (hV : ∃ k, A * (z (sqHandleIdxV j)).i - E * (z (sqHandleIdxV j)).h = 2 * k)
    (hUf : ∃ k, (z (sqHandleIdxU j)).f * (B * F) = 2 * k)
    (hVf : ∃ k, (z (sqHandleIdxV j)).f * (A * E) = 2 * k) :
    ∃ k, (gaTwoShift h (selLiftWit h j A B C D E F T S P Q R) z).j = 2 * k := by
  rw [gaTwoShift_j]
  refine ev_add (ev_add (ev_add (ev_add (ev_add ?_ ?_) ?_) ?_) ?_) ?_
  · exact ⟨-2 * (z 1).j + (z 2).j, by ring⟩
  · exact ev_add (ev_add (gaTwoPair_selLiftWit_zero_even (W2 := W2) hd hb)
      gaTwoPair_selLiftWit_one_even) (gaTwoPair_selLiftWit_two_even h2e (hzg 2))
  · exact gaTwoCorr_selLiftWit_even hd
  · exact gaTwoQuad_even (hzg 0) (hzg 1) (hzg 2)
  · refine ev_sum _ fun k => ?_
    by_cases hk : k = j
    · subst hk
      exact handle_term_even_at hzg hg hU hV hUf hVf
    · exact handle_term_even_of_ne hzg hk
  · exact ⟨(-2 * (z 1).e + (z 2).e) * sqHandlePairG h (selLiftWit h j A B C D E F T S P Q R)
      - sqHandlePairE h (selLiftWit h j A B C D E F T S P Q R)
        * (-2 * (z 1).g + (z 2).g), by ring⟩

/-- ⭐⭐ **The `γ₂`-level obstruction at the witness**, in its sharpest form: at a binder
point where the four surviving pairings are even, an **odd** class-four residue survives
every five-slot `γ₂`-dressing of the frame whose slots have even `g`-column.  No stage
hypothesis is imposed: a would-be kill has all ten rows zero, and its class-two row supplies
`(z 2).e` even (ingredient (ii)) for free.

This is the `γ₂`-analogue of `GradedContainFour.sqRelWord_selLift_ne_one`.  It turns the
note's exhaustive §5 census into a theorem: the residual corners are not merely measured to
be dead at the `γ₂` level, they are proved to be. -/
theorem sqRelWord_conFourDress_selLiftWit_ne_one (hz : ∀ i, (z i).IsGaTwo)
    (hzg : ∀ i, ∃ k, (z i).g = 2 * k)
    (hd : 2 * P + (A * S - B * T) = 0) (hg : 2 * R + (C * F - D * E) = 0)
    (hb : 2 * W2 + (E * S - F * T) = 0)
    (hU : ∃ k, (z (sqHandleIdxU j)).h * F - (z (sqHandleIdxU j)).i * B = 2 * k)
    (hV : ∃ k, A * (z (sqHandleIdxV j)).i - E * (z (sqHandleIdxV j)).h = 2 * k)
    (hUf : ∃ k, (z (sqHandleIdxU j)).f * (B * F) = 2 * k)
    (hVf : ∃ k, (z (sqHandleIdxV j)).f * (A * E) = 2 * k)
    (h5 : sqRelWord (selLiftWit h j A B C D E F T S P Q R) = liftC res)
    (hodd : selPar res = 1) :
    sqRelWord (conFourDress (selLiftWit h j A B C D E F T S P Q R) z) ≠ 1 := by
  intro hc
  rw [sqRelWord_gaTwoDress hz, h5, ← liftC_comm, mul_liftC_apply] at hc
  have hje : (gaTwoShift h (selLiftWit h j A B C D E F T S P Q R) z).j + res = 0 :=
    congrArg SqU5.j hc
  have hee : (gaTwoShift h (selLiftWit h j A B C D E F T S P Q R) z).e = 0 :=
    congrArg SqU5.e hc
  rw [gaTwoShift_e] at hee
  obtain ⟨w, hw⟩ := gaTwoShift_selLiftWit_j_even (W2 := W2) hzg hd hg hb
    (gr3R_even_of_frobenius _ _ hee) hU hV hUf hVf
  have hres : res = -(2 * w) := by linear_combination hje - hw
  rw [hres, selPar_neg, selPar_two_mul] at hodd
  exact absurd hodd (by decide)

/-- **Membership in `Λ₂`**, the `γ₂`-level achievable lattice of the class-four witness, in
the form the obstruction consumes: a `γ₂`-shaped element with an **even `g`-column** whose
`(h, i)`-data is `Λ₃⁺`-achievable.  Ingredient (i) (§3) says every generator of `γ₂(im Φ)`
has even `g`, and `GradedGammaTwo` §3 says the three new `γ₂`-level moves have `Λ₃⁺`-data, so
this is an over-approximation of the honest achievable lattice and the obstruction over it is
correspondingly stronger.  It is closed under the group law (`selLamTwo_one`,
`selLamTwo_mul`). -/
def selLamTwo (A B C D E F T S P Q R : gr3R) (z : SqU5 gr3R) : Prop :=
  z.IsGaTwo ∧ (∃ k, z.g = 2 * k) ∧
    selLamThreePlus A B C D E F T S P Q R ⟨0, 0, 0, 0, 0, 0, 0, z.h, z.i, 0⟩

/-- `Λ₃⁺` is closed under addition of the `(h, i)`-data: the ten coefficients add. -/
theorem selLamThreePlus_add {A B C D E F T S P Q R : gr3R} {p q : SqU5 gr3R}
    (hp : selLamThreePlus A B C D E F T S P Q R p)
    (hq : selLamThreePlus A B C D E F T S P Q R q) :
    selLamThreePlus A B C D E F T S P Q R
      ⟨0, 0, 0, 0, 0, 0, 0, p.h + q.h, p.i + q.i, 0⟩ := by
  obtain ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, t₁, t₂, t₃, hph, hpi⟩ := hp
  obtain ⟨s₁, s₂, s₃, s₄, s₅, s₆, s₇, u₁, u₂, u₃, hqh, hqi⟩ := hq
  refine ⟨r₁ + s₁, r₂ + s₂, r₃ + s₃, r₄ + s₄, r₅ + s₅, r₆ + s₆, r₇ + s₇, t₁ + u₁, t₂ + u₂,
    t₃ + u₃, ?_, ?_⟩
  · show p.h + q.h = _
    rw [hph, hqh]; ring
  · show p.i + q.i = _
    rw [hpi, hqi]; ring

/-- The trivial dressing is achievable. -/
theorem selLamTwo_one {A B C D E F T S P Q R : gr3R} :
    selLamTwo A B C D E F T S P Q R 1 :=
  ⟨SqU5.isGaTwo_one, ⟨0, by simp⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, by simp, by simp⟩⟩

/-- `Λ₂` is closed under products: on `γ₂` every one of `e`, `f`, `g`, `h`, `i` is
additive. -/
theorem selLamTwo_mul {A B C D E F T S P Q R : gr3R} {p q : SqU5 gr3R}
    (hp : selLamTwo A B C D E F T S P Q R p) (hq : selLamTwo A B C D E F T S P Q R q) :
    selLamTwo A B C D E F T S P Q R (p * q) := by
  obtain ⟨⟨hpa, hpb, hpc, hpd⟩, hpg, hpL⟩ := hp
  obtain ⟨⟨hqa, hqb, hqc, hqd⟩, hqg, hqL⟩ := hq
  refine ⟨⟨by simp [hpa, hqa], by simp [hpb, hqb], by simp [hpc, hqc], by simp [hpd, hqd]⟩,
    gaTwo_mul_g_even ⟨hpa, hpb, hpc, hpd⟩ hpg hqg, ?_⟩
  have hh : (p * q).h = p.h + q.h := by rw [SqU5.mul_h, hpa, hqc]; ring
  have hi : (p * q).i = p.i + q.i := by rw [SqU5.mul_i, hpb, hqd]; ring
  rw [hh, hi]
  exact selLamThreePlus_add hpL hqL

/-- A `γ₃`-shaped element with `Λ₃⁺`-achievable `(h, i)`-data is a `Λ₂`-dressing. -/
theorem selLamTwo_of_gaThree {A B C D E F T S P Q R : gr3R} {p : SqU5 gr3R}
    (hp : p.IsGaThree)
    (hL : selLamThreePlus A B C D E F T S P Q R ⟨0, 0, 0, 0, 0, 0, 0, p.h, p.i, 0⟩) :
    selLamTwo A B C D E F T S P Q R p :=
  ⟨hp.isGaTwo, gaThree_g_even hp, hL⟩

/-- ⭐ **The `σ`-`x₁` move is a `Λ₂`-dressing**: the commutator of two frame slots, with
`(h, i) = (0, R)`, the move whose double alone the committed lattice carries. -/
theorem selLamTwo_commP_zero_two :
    selLamTwo A B C D E F T S P Q R
      (commP (selLiftWit h j A B C D E F T S P Q R 0)
        (selLiftWit h j A B C D E F T S P Q R 2)) := by
  rw [selLiftWit_commP_zero_two]
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨0, by simp⟩, ?_⟩
  have hR : (⟨0, 0, 0, 0, 0, 0, 0, (0 : gr3R), R, 0⟩ : SqU5 gr3R)
      = ⟨0, 0, 0, 0, 0, 0, 0, 0, 1 * R, 0⟩ := by ext <;> ring
  rw [show (⟨0, 0, 0, 0, 0, 0, 0,
      (⟨0, 0, 0, 0, 0, 0, 0, (0 : gr3R), R, 0⟩ : SqU5 gr3R).h,
      (⟨0, 0, 0, 0, 0, 0, 0, (0 : gr3R), R, 0⟩ : SqU5 gr3R).i, 0⟩ : SqU5 gr3R)
      = ⟨0, 0, 0, 0, 0, 0, 0, 0, R, 0⟩ from rfl, hR]
  exact selLamThreePlus_zero_two 1

/-- ⭐ **The `x₁`-`U` move is a `Λ₂`-dressing**, with `(h, i) = (P·C − Q·A, Q·E)`. -/
theorem selLamTwo_commP_two_handleU :
    selLamTwo A B C D E F T S P Q R
      (commP (selLiftWit h j A B C D E F T S P Q R 2)
        (selLiftWit h j A B C D E F T S P Q R (sqHandleIdxU j))) := by
  rw [selLiftWit_commP_two_handleU]
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨0, by simp⟩, ?_⟩
  have hR : (⟨0, 0, 0, 0, 0, 0, 0, P * C - Q * A, Q * E, (0 : gr3R)⟩ : SqU5 gr3R)
      = ⟨0, 0, 0, 0, 0, 0, 0, 1 * (P * C - Q * A), 1 * (Q * E), 0⟩ := by ext <;> ring
  rw [show (⟨0, 0, 0, 0, 0, 0, 0,
      (⟨0, 0, 0, 0, 0, 0, 0, P * C - Q * A, Q * E,
        -(2 * (A * (E * Q))) - B * (E * Q)⟩ : SqU5 gr3R).h,
      (⟨0, 0, 0, 0, 0, 0, 0, P * C - Q * A, Q * E,
        -(2 * (A * (E * Q))) - B * (E * Q)⟩ : SqU5 gr3R).i, 0⟩ : SqU5 gr3R)
      = ⟨0, 0, 0, 0, 0, 0, 0, P * C - Q * A, Q * E, (0 : gr3R)⟩ from rfl, hR]
  exact selLamThreePlus_two_handleU 1

/-- ⭐ **The `x₁`-`V` move is a `Λ₂`-dressing**, with `(h, i) = (P·D − Q·B, Q·F)`. -/
theorem selLamTwo_commP_two_handleV :
    selLamTwo A B C D E F T S P Q R
      (commP (selLiftWit h j A B C D E F T S P Q R 2)
        (selLiftWit h j A B C D E F T S P Q R (sqHandleIdxV j))) := by
  rw [selLiftWit_commP_two_handleV]
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨0, by simp⟩, ?_⟩
  have hR : (⟨0, 0, 0, 0, 0, 0, 0, P * D - Q * B, Q * F, (0 : gr3R)⟩ : SqU5 gr3R)
      = ⟨0, 0, 0, 0, 0, 0, 0, 1 * (P * D - Q * B), 1 * (Q * F), 0⟩ := by ext <;> ring
  rw [show (⟨0, 0, 0, 0, 0, 0, 0,
      (⟨0, 0, 0, 0, 0, 0, 0, P * D - Q * B, Q * F,
        -(A * (F * Q)) - 2 * (B * (F * Q)) + B * (S * R)⟩ : SqU5 gr3R).h,
      (⟨0, 0, 0, 0, 0, 0, 0, P * D - Q * B, Q * F,
        -(A * (F * Q)) - 2 * (B * (F * Q)) + B * (S * R)⟩ : SqU5 gr3R).i, 0⟩ : SqU5 gr3R)
      = ⟨0, 0, 0, 0, 0, 0, 0, P * D - Q * B, Q * F, (0 : gr3R)⟩ from rfl, hR]
  exact selLamThreePlus_two_handleV 1

/-- **An even factor makes a pairing even**: the arithmetic behind "the two `f`-column
pairings are free on the residual set".  All ten mod-2 classes of the note's residual `33792`
corners have `A` and `B` both even, and then `A·E` and `B·F` are even whatever `E` and `F`
do. -/
theorem ev_mul_of_selPar_zero {x : gr3R} (y : gr3R) (hx : selPar x = 0) :
    ∃ k, x * y = 2 * k :=
  (selPar_eq_zero_iff _).mp (by rw [selPar_mul, hx, zero_mul])

private theorem selPar_two : selPar (2 : gr3R) = 0 := by decide

/-- The 𝔽₂ core of the `f`-column reduction: nine mod-2 variables, `512` cases.  Suppose the
`B·C·E`-, `A·D·F`+`B·C·F`+`B·D·E`-, `B·D·F`-, `R·B`-, `A·C·E`-, `A·C·F`+`A·D·E`+`B·C·E`- and
`A·R`-pairings are all even and the class-four selection bit `(A·C·F + B·D·E)·T + P·R` is
**odd**.  Then `A·E` and `B·F` are even.  Two three-step eliminations: `A·E` odd forces `C`
and `R` even, hence the bit to read `B·D·T`, hence `B`, `D`, `T` odd, which makes the
`A·C·F + A·D·E + B·C·E` pairing odd; `B·F` odd forces `D` and `R` even, hence the bit to read
`A·C·T`, hence `A`, `C`, `T` odd and (by the `B·C·E`-pairing) `E` even, which makes the
`A·D·F + B·C·F + B·D·E` pairing odd. -/
private theorem obstPlus_core : ∀ a b c d e f t p r : ZMod 2,
    c * e * b = 0 →
    (a * d + b * c) * f + d * e * b = 0 →
    d * f * b = 0 →
    r * b = 0 →
    a * (c * e) = 0 →
    a * (c * f) + e * (a * d + b * c) = 0 →
    a * r = 0 →
    (a * (c * f) + b * (d * e)) * t + p * r = 1 →
    a * e = 0 ∧ b * f = 0 := by
  decide

/-- ⭐⭐ **The `f`-column pairings are not extra hypotheses after all.**  Seven of the
fourteen pairings together with the **oddness of the class-four residue** (through the
committed selection bit `selLiftWit_bit`) force `A·E` and `B·F` even.  This is the step the
wave-54 note's §7 sketch omits: its ingredient (iv) says "the surviving Fox pairings are the
fourteen hypotheses", but the graded Fox pairing's last term `z.f·(L.a·L.d)` also survives
mod 2 at the two marked handle slots, contributing `z_U.f·(B·F)` and `z_V.f·(A·E)`.  The
fourteen alone do **not** imply those even (see the instance at the end of the file); the
conclusion's own hypothesis, an odd residue, is what closes the gap.  So the note's
hypothesis set is right and its route needs one more input than it lists. -/
theorem selLiftWit_ae_bf_even_of_odd {A B C D E F T P R : gr3R}
    (h₁ : ∃ k, (2 * (A * C)) * F + (C * E) * B = 2 * k)
    (h₂ : ∃ k, (A * D + B * C) * F + (D * E) * B = 2 * k)
    (h₄ : ∃ k, (2 * (B * D)) * F + (D * F) * B = 2 * k)
    (h₅ : ∃ k, R * B = 2 * k)
    (h₁' : ∃ k, A * (C * E) + E * (2 * (A * C)) = 2 * k)
    (h₃' : ∃ k, A * (C * F) + E * (A * D + B * C) = 2 * k)
    (h₅' : ∃ k, A * R = 2 * k)
    (hbit : selPar ((A * (C * F) + B * (D * E)) * T + P * R) = 1) :
    (∃ k, A * E = 2 * k) ∧ (∃ k, B * F = 2 * k) := by
  have q₁ : selPar C * selPar E * selPar B = 0 := by
    have hh := (selPar_eq_zero_iff _).mpr h₁
    simp only [selPar_add, selPar_mul, selPar_two, zero_mul, zero_add] at hh
    linear_combination hh
  have q₂ : (selPar A * selPar D + selPar B * selPar C) * selPar F
      + selPar D * selPar E * selPar B = 0 := by
    have hh := (selPar_eq_zero_iff _).mpr h₂
    simp only [selPar_add, selPar_mul] at hh
    linear_combination hh
  have q₄ : selPar D * selPar F * selPar B = 0 := by
    have hh := (selPar_eq_zero_iff _).mpr h₄
    simp only [selPar_add, selPar_mul, selPar_two, zero_mul, zero_add] at hh
    linear_combination hh
  have q₅ : selPar R * selPar B = 0 := by
    have hh := (selPar_eq_zero_iff _).mpr h₅
    simp only [selPar_mul] at hh
    linear_combination hh
  have q₁' : selPar A * (selPar C * selPar E) = 0 := by
    have hh := (selPar_eq_zero_iff _).mpr h₁'
    simp only [selPar_add, selPar_mul, selPar_two, zero_mul, mul_zero, add_zero] at hh
    linear_combination hh
  have q₃' : selPar A * (selPar C * selPar F)
      + selPar E * (selPar A * selPar D + selPar B * selPar C) = 0 := by
    have hh := (selPar_eq_zero_iff _).mpr h₃'
    simp only [selPar_add, selPar_mul] at hh
    linear_combination hh
  have q₅' : selPar A * selPar R = 0 := by
    have hh := (selPar_eq_zero_iff _).mpr h₅'
    simp only [selPar_mul] at hh
    linear_combination hh
  have qbit : (selPar A * (selPar C * selPar F) + selPar B * (selPar D * selPar E)) * selPar T
      + selPar P * selPar R = 1 := by
    simp only [selPar_add, selPar_mul] at hbit
    linear_combination hbit
  obtain ⟨e₁, e₂⟩ := obstPlus_core (selPar A) (selPar B) (selPar C) (selPar D) (selPar E)
    (selPar F) (selPar T) (selPar P) (selPar R) q₁ q₂ q₄ q₅ q₁' q₃' q₅' qbit
  exact ⟨(selPar_eq_zero_iff _).mp (by rw [selPar_mul]; exact e₁),
    (selPar_eq_zero_iff _).mp (by rw [selPar_mul]; exact e₂)⟩

/-- ⭐⭐ **The `γ₂`-level obstruction over the lattice**, exactly the statement the wave-54
note asks for (§7 item 1) and with exactly its **fourteen** hypotheses: where the eight
committed generator pairings and the six new `γ₂`-level pairings are even at the witness's
handle columns, an odd class-four residue survives **every** `Λ₂`-dressing of the whole
frame.

The `f`-column terms the note's sketch omits are discharged by `selLiftWit_ae_bf_even_of_odd`
from the odd-residue hypothesis itself, so no hypothesis beyond the fourteen is needed.  This
turns the note's exhaustive §5 census into a theorem: the residual corners are not merely
measured to be dead at the `γ₂` level, they are proved to be. -/
theorem sqRelWord_selLamTwo_ne_one
    (hz : ∀ i, selLamTwo A B C D E F T S P Q R (z i))
    (hd : 2 * P + (A * S - B * T) = 0) (hg : 2 * R + (C * F - D * E) = 0)
    (hb : 2 * W2 + (E * S - F * T) = 0)
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
    sqRelWord (conFourDress (selLiftWit h j A B C D E F T S P Q R) z) ≠ 1 := by
  have hj5 : (sqRelWord (selLiftWit h j A B C D E F T S P Q R)).j = res := by
    rw [h5, liftC_j]
  have hbit : selPar ((A * (C * F) + B * (D * E)) * T + P * R) = 1 :=
    (selLiftWit_bit (h := h) (j := j) (S := S) (Q := Q) hg).symm.trans (by rw [hj5]; exact hodd)
  obtain ⟨hAE, hBF⟩ := selLiftWit_ae_bf_even_of_odd h₁ h₂ h₄ h₅ h₁' h₃' h₅' hbit
  exact sqRelWord_conFourDress_selLiftWit_ne_one (W2 := W2) (fun i => (hz i).1)
    (fun i => (hz i).2.1) hd hg hb
    (selLamThreePlus_pair_even (hz (sqHandleIdxU j)).2.2 h₁ h₂ h₃ h₄ h₅ h₆ h₇)
    (selLamThreePlus_pair_even' (hz (sqHandleIdxV j)).2.2 h₁' h₂' h₃' h₄' h₅' h₆' h₇')
    (ev_mul_left _ hBF) (ev_mul_left _ hAE) h5 hodd

end GaTwoWitness

/-! ## §6 The bridge corollaries

The note's §7 item 2: `selLamThree` should eventually be replaced by `selLamThreePlus`
throughout, and nothing breaks because the containment `selLamThree_plus` is committed.  Here
is every committed conclusion that quantifies over the old lattice, restated over the extended
one, so that a future wave can perform the replacement mechanically.  No committed statement
is touched. -/

section Bridge

variable {h : ℕ} {j : Fin h} {A B C D E F T S P Q R : gr3R}

/-- The `U`-slot completion move is `Λ₃⁺`-achievable (`selLamThree_completion_move`). -/
theorem selLamThreePlus_completion_move (A B C D E F T S P Q R rr res : gr3R) :
    selLamThreePlus A B C D E F T S P Q R
      ⟨0, 0, 0, 0, 0, 0, 0, -(rr * res * -(2 * (B * D))), -(rr * res * (D * F)), 0⟩ :=
  selLamThree_plus (selLamThree_completion_move A B C D E F T S P Q R rr res)

/-- …and the mirror move (`selLamThree_completion_move'`). -/
theorem selLamThreePlus_completion_move' (A B C D E F T S P Q R rr res : gr3R) :
    selLamThreePlus A B C D E F T S P Q R
      ⟨0, 0, 0, 0, 0, 0, 0, -(rr * res * -(2 * (A * C))), -(rr * res * (C * E)), 0⟩ :=
  selLamThree_plus (selLamThree_completion_move' A B C D E F T S P Q R rr res)

/-- The committed `κ₄ = B·D·F` completion, over the extended lattice
(`GradedLift.selLiftWit_complete_odd`). -/
theorem selLiftWit_complete_odd_plus_bdf (hκ : selPar (B * D * F) = 1) {res : gr3R}
    (h5 : sqRelWord (selLiftWit h j A B C D E F T S P Q R) = liftC res) :
    ∃ z₃ : SqU5 gr3R, z₃.IsGaThree ∧ selLamThreePlus A B C D E F T S P Q R z₃ ∧
      sqRelWord (selLift j (selLiftWit h j A B C D E F T S P Q R) 1 1 z₃ 1) = 1 := by
  obtain ⟨z₃, h3, hL, hkill⟩ := selLiftWit_complete_odd hκ h5
  exact ⟨z₃, h3, selLamThree_plus hL, hkill⟩

/-- The `B·C·E` completion, over the extended lattice
(`GradedContainFour.selLiftWit_complete_odd_bce`). -/
theorem selLiftWit_complete_odd_plus_bce (hκ : selPar (B * (C * E)) = 1) {res : gr3R}
    (h5 : sqRelWord (selLiftWit h j A B C D E F T S P Q R) = liftC res) :
    ∃ z₃ : SqU5 gr3R, z₃.IsGaThree ∧ selLamThreePlus A B C D E F T S P Q R z₃ ∧
      sqRelWord (selLift j (selLiftWit h j A B C D E F T S P Q R) 1 1 z₃ 1) = 1 := by
  obtain ⟨z₃, h3, hL, hkill⟩ := selLiftWit_complete_odd_bce hκ h5
  exact ⟨z₃, h3, selLamThree_plus hL, hkill⟩

/-- The `A·D·F` completion, over the extended lattice
(`GradedContainFour.selLiftWit_complete_odd_adf`). -/
theorem selLiftWit_complete_odd_plus_adf (hκ : selPar (A * (D * F)) = 1) {res : gr3R}
    (h5 : sqRelWord (selLiftWit h j A B C D E F T S P Q R) = liftC res) :
    ∃ z₃ : SqU5 gr3R, z₃.IsGaThree ∧ selLamThreePlus A B C D E F T S P Q R z₃ ∧
      sqRelWord (selLift j (selLiftWit h j A B C D E F T S P Q R) 1 1 z₃ 1) = 1 := by
  obtain ⟨z₃, h3, hL, hkill⟩ := selLiftWit_complete_odd_adf hκ h5
  exact ⟨z₃, h3, selLamThree_plus hL, hkill⟩

/-- The mirror `κ₄' = A·C·E` completion, over the extended lattice
(`GradedContainFour.selLiftWit_complete_odd_ace`). -/
theorem selLiftWit_complete_odd_plus_ace (hκ : selPar (A * (C * E)) = 1) {res : gr3R}
    (h5 : sqRelWord (selLiftWit h j A B C D E F T S P Q R) = liftC res) :
    ∃ z₄ : SqU5 gr3R, z₄.IsGaThree ∧ selLamThreePlus A B C D E F T S P Q R z₄ ∧
      sqRelWord (selLift j (selLiftWit h j A B C D E F T S P Q R) 1 1 1 z₄) = 1 := by
  obtain ⟨z₄, h3, hL, hkill⟩ := selLiftWit_complete_odd_ace hκ h5
  exact ⟨z₄, h3, selLamThree_plus hL, hkill⟩

end Bridge

/-! ### Concrete instances

A corner of the note's residual set, run end to end, plus the two consistency checks.

**The residual corner.**  `(A, B, C, D, E, F, T, S) = (2, 0, 2, 0, 0, 1, 0, 1)` with halves
`(P, Q, R, W2) = (3, 1, 3, 0)`.  All four parity rows hold; the mod-2 class is
`[0,0,0,0,0,1,0,1,1,1,1,0]`, the first of the ten classes of the note's §5.2, so this is one
of the `33792` corners the wave-54 census certified dead at the `γ₂` level by exhaustive
measurement.  The bare witness survives stage 3 outright with the **odd** residue `5`; all
eight committed pairings and all six new ones are even; and the `γ₂`-level obstruction then
**proves** that no `Λ₂`-dressing of the whole frame kills it.  That is the measurement turned
into a theorem.

**The `γ₂`-transportable corner.**  At `GradedGammaTwo` §3.3's corner
`(A, …, S) = (0, 1, 1, 1, 2, 0, 2, 0)`, halves `(1, 3, 1)`, the new pairing `R·B = 1` is a
**unit**, so the migrated obstruction is silent there, exactly as it must be: that corner is
killed by `selLiftWit_complete_odd_rb`.

**Why the route needs the odd residue.**  At
`(A, B, C, D, E, F, T, S) = (1, 0, 0, 0, 1, 0, 0, 0)` with halves `(P, Q, R, W2) = 0` all four
parity rows hold and all **fourteen** of the note's pairings vanish, yet `A·E = 1` is odd.  So
`selLiftWit_ae_bf_even_of_odd` really does need its bit hypothesis: the fourteen alone do not
kill the `f`-column terms.  (At that point the class-four bit
`(A·C·F + B·D·E)·T + P·R = 0` is even, so the obstruction has nothing to say there anyway,
which is exactly how the two facts coexist.) -/

/-- The residual corner satisfies the four parity rows. -/
example : (2 * (3 : gr3R) + (2 * 1 - 0 * 0) = 0) ∧ (2 * (1 : gr3R) + (0 * 0 - 1 * 2) = 0)
    ∧ (2 * (3 : gr3R) + (2 * 1 - 0 * 0) = 0) ∧ (2 * (0 : gr3R) + (0 * 1 - 1 * 0) = 0) := by
  decide

/-- The witness there is a stage-three survivor with the **odd** class-four residue `5`. -/
example : sqRelWord (selLiftWit 1 0 2 0 2 0 0 1 0 1 3 1 3) = liftC (5 : gr3R) := by decide

/-- All fourteen pairings are even there: the eight committed ones and the six new
`γ₂`-level ones (the two `f`-column ones `A·E = 0`, `B·F = 0` come for free, `A` being
even). -/
example :
    (∃ k : gr3R, (2 * ((2 : gr3R) * 2)) * 1 + (2 * 0) * 0 = 2 * k)
    ∧ (∃ k : gr3R, ((2 : gr3R) * 0 + 0 * 2) * 1 + (0 * 0) * 0 = 2 * k)
    ∧ (∃ k : gr3R, ((2 : gr3R) * 0 + 0 * 2) * 1 + (2 * 1) * 0 = 2 * k)
    ∧ (∃ k : gr3R, (2 * ((0 : gr3R) * 0)) * 1 + (0 * 1) * 0 = 2 * k)
    ∧ (∃ k : gr3R, (3 : gr3R) * 0 = 2 * k)
    ∧ (∃ k : gr3R, ((3 : gr3R) * 2 - 1 * 2) * 1 - (1 * 0) * 0 = 2 * k)
    ∧ (∃ k : gr3R, ((3 : gr3R) * 0 - 1 * 0) * 1 - (1 * 1) * 0 = 2 * k)
    ∧ (∃ k : gr3R, (2 : gr3R) * (2 * 0) + 0 * (2 * (2 * 2)) = 2 * k)
    ∧ (∃ k : gr3R, (2 : gr3R) * (0 * 0) + 0 * (2 * 0 + 0 * 2) = 2 * k)
    ∧ (∃ k : gr3R, (2 : gr3R) * (2 * 1) + 0 * (2 * 0 + 0 * 2) = 2 * k)
    ∧ (∃ k : gr3R, (2 : gr3R) * (0 * 1) + 0 * (2 * (0 * 0)) = 2 * k)
    ∧ (∃ k : gr3R, (2 : gr3R) * 3 = 2 * k)
    ∧ (∃ k : gr3R, (2 : gr3R) * (1 * 0) - 0 * (3 * 2 - 1 * 2) = 2 * k)
    ∧ (∃ k : gr3R, (2 : gr3R) * (1 * 1) - 0 * (3 * 0 - 1 * 0) = 2 * k)
    ∧ (∃ k : gr3R, (2 : gr3R) * 0 = 2 * k) ∧ (∃ k : gr3R, (0 : gr3R) * 1 = 2 * k) := by decide

/-- ⭐⭐ **The payoff**: at that residual corner **no** `Λ₂`-dressing of the whole frame kills
the relator.  Every hypothesis by `decide`, conclusion through the `γ₂`-level obstruction. -/
example {z : Fin (sqRank 1) → SqU5 gr3R}
    (hz : ∀ i, selLamTwo 2 0 2 0 0 1 0 1 3 1 3 (z i)) :
    sqRelWord (conFourDress (selLiftWit 1 0 2 0 2 0 0 1 0 1 3 1 3) z) ≠ 1 :=
  sqRelWord_selLamTwo_ne_one (W2 := 0) (res := 5) hz (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-- …and the migrated `Λ₃⁺` obstruction fires there too: no `selLift` refinement with
`Λ₃⁺`-achievable handle moves kills it either. -/
example {w₁ w₂ z₃ z₄ : SqU5 gr3R} (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (hz₃L : selLamThreePlus 2 0 2 0 0 1 0 1 3 1 3 z₃)
    (hz₄L : selLamThreePlus 2 0 2 0 0 1 0 1 3 1 3 z₄) :
    sqRelWord (selLift 0 (selLiftWit 1 0 2 0 2 0 0 1 0 1 3 1 3) w₁ w₂ z₃ z₄) ≠ 1 :=
  sqRelWord_selLift_ne_one_plus hw₁ hw₂ hz₃ hz₄ hz₃L hz₄L
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- The `γ₂`-transportable corner does **not** satisfy the migrated obstruction's hypotheses:
its new pairing `R·B` is a unit, which is exactly why the transport reaches it. -/
example : selPar ((1 : gr3R) * 1) = 1 := by decide

/-- The `f`-column terms are **not** killed by the fourteen alone: the four parity rows hold
at `(1, 0, 0, 0, 1, 0, 0, 0)` with zero halves… -/
example : (2 * (0 : gr3R) + (1 * 0 - 0 * 0) = 0) ∧ (2 * (0 : gr3R) + (0 * 0 - 0 * 0) = 0)
    ∧ (2 * (0 : gr3R) + (0 * 0 - 0 * 1) = 0) ∧ (2 * (0 : gr3R) + (1 * 0 - 0 * 0) = 0) := by
  decide

/-- …all fourteen pairings vanish there… -/
example : ((2 * ((1 : gr3R) * 0)) * 0 + (0 * 1) * 0 = 0)
    ∧ (((1 : gr3R) * 0 + 0 * 0) * 0 + (0 * 1) * 0 = 0)
    ∧ (((1 : gr3R) * 0 + 0 * 0) * 0 + (0 * 0) * 0 = 0)
    ∧ ((2 * ((0 : gr3R) * 0)) * 0 + (0 * 0) * 0 = 0)
    ∧ ((0 : gr3R) * 0 = 0)
    ∧ (((0 : gr3R) * 0 - 0 * 1) * 0 - (0 * 1) * 0 = 0)
    ∧ (((0 : gr3R) * 0 - 0 * 0) * 0 - (0 * 0) * 0 = 0)
    ∧ ((1 : gr3R) * (0 * 1) + 1 * (2 * (1 * 0)) = 0)
    ∧ ((1 : gr3R) * (0 * 1) + 1 * (1 * 0 + 0 * 0) = 0)
    ∧ ((1 : gr3R) * (0 * 0) + 1 * (1 * 0 + 0 * 0) = 0)
    ∧ ((1 : gr3R) * (0 * 0) + 1 * (2 * (0 * 0)) = 0)
    ∧ ((1 : gr3R) * 0 = 0)
    ∧ ((1 : gr3R) * (0 * 1) - 1 * (0 * 0 - 0 * 1) = 0)
    ∧ ((1 : gr3R) * (0 * 0) - 1 * (0 * 0 - 0 * 0) = 0) := by decide

/-- …and yet `A·E = 1` is odd, while the class-four bit `(A·C·F + B·D·E)·T + P·R` is even
there, so the obstruction's own hypothesis fails and the two facts coexist. -/
example : selPar ((1 : gr3R) * 1) = 1
    ∧ selPar (((1 : gr3R) * (0 * 0) + 0 * (0 * 1)) * 0 + 0 * 0) = 0 := by decide

/-! ## §7 Axiom pins

Committed prints for every public declaration of this file: all **std-3** (`propext`,
`Classical.choice`, `Quot.sound`) or a subset; no census axiom is reachable.  Every `decide`
is on `ZMod 8`, `ZMod 2` or tuples over them. -/

section AxiomPins

#print axioms gr3R_even_of_frobenius
#print axioms selLamThreePlus_pair_even
#print axioms selLamThreePlus_pair_even'
#print axioms sqRelWord_selLift_ne_one_plus
#print axioms selLiftWit_commP_g_even
#print axioms selLiftWit_two_sq_g
#print axioms gaTwo_mul_g_even
#print axioms gaThree_g_even
#print axioms gaTwoPair_selLiftWit_zero_even
#print axioms gaTwoPair_selLiftWit_one_even
#print axioms gaTwoPair_selLiftWit_two_even
#print axioms gaTwoCorr_selLiftWit_even
#print axioms gaTwoQuad_even
#print axioms gaTwoShift_e
#print axioms gaTwoShift_j
#print axioms gaTwoShift_selLiftWit_j_even
#print axioms sqRelWord_conFourDress_selLiftWit_ne_one
#print axioms selLamTwo
#print axioms selLamThreePlus_add
#print axioms selLamTwo_one
#print axioms selLamTwo_mul
#print axioms selLamTwo_of_gaThree
#print axioms selLamTwo_commP_zero_two
#print axioms selLamTwo_commP_two_handleU
#print axioms selLamTwo_commP_two_handleV
#print axioms ev_mul_of_selPar_zero
#print axioms selLiftWit_ae_bf_even_of_odd
#print axioms sqRelWord_selLamTwo_ne_one
#print axioms selLamThreePlus_completion_move
#print axioms selLamThreePlus_completion_move'
#print axioms selLiftWit_complete_odd_plus_bdf
#print axioms selLiftWit_complete_odd_plus_bce
#print axioms selLiftWit_complete_odd_plus_adf
#print axioms selLiftWit_complete_odd_plus_ace

end AxiomPins

end SqCore

end Dyadic

end GQ2

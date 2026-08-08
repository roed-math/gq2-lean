/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedSelect

/-!
# W51-CONTAIN: the containment identity over the whole marking binder

`GradedSelect` §5 and §6 characterised the class-three selection at a fixed selected marking:
the refinement action translates the relator by even amounts, the selection bit (the parity of
the class-three residue) is the cokernel functional, an odd residue is unrepairable
(`sqRelWord_selRefine_ne_one`), and an even residue at a live pairing is repaired by one
explicit move (`sqRelWord_selRefine_eq_one`).  The W50 depth sweep measured the structural fact
behind this: the dressing-defect map is never onto, its image has corank `sqRank h + 1` at
every level and marking, and yet the relator's actual defect lands inside the image every time
(`docs/dyadic/w50-depth-sweep.md` §6.3, 20/20 against a 1.6 % random baseline).

This file formalizes the slice form of that containment over the **whole marking binder**: all
`ν'`-row pairs `(T, S)`, all weight tuples `(A, B, C, D, P, Q)` subject to the two adjacency
parities of the selection family, at every handle count and every handle.  Two results carry
the weight.

* **The selection-bit form** (`selCon_bit`, the note's §3 display as a theorem): on any binder
  tuple whose `x₀`- and `x₁`-slot abelian data satisfy the class-two parities, the parity of
  the class-three residue equals the explicit 𝔽₂-form `selConForm` with coefficients
  `κ₁ = (A+B)·T·D`, `κ₂ = A·Q + C·P`, `κ₃ = B·Q + D·P`.  The form reads **only** the eleven
  level-one coordinates `(m₀, n₀, m₁, n₁, k₁, m₃, n₃, k₃, m₄, n₄, k₄)`: the `x₁`-slot data,
  every `Λ`-junk coefficient, every class-three coordinate and the σ-slot `t̄`-component are
  invisible, because they do not occur in the statement.
* **The whole-binder existence** (`selConWit_even`, `selCon_contain`): at *every* binder point
  there are class-two-admissible level-one data with selection bit zero, namely the class-two
  forced dressing `a₁ = U^{−S}·V^{T}` with one `Λ`-generator correction; the five lower rows
  of the relator vanish exactly and the class-three residue is
  `4·P·Q − 2·(A+B)·Q + B·C·(T+S)`, even at every binder point with no uncleared hypothesis.
  On the live locus (`2`-pairing witness present) the committed completion move then kills the
  relator outright: the containment, constructively.

The existence is **unconditional on the binder**; the uncleared hypothesis `hTS` enters only
the bit-form identity (through `selCross_even`, exactly as in the committed §5b), and the live
hypothesis enters only the final refinement step, as the sweep's sharpness caveat requires (at
degenerate weights the achievable-increment group can shrink below `2·ℤ/8`, and evenness of the
residue alone does not produce a survivor; nothing here claims it does).

## Contents

* **§1** the binder dressing data: `SelConDress`, `selConVal` and the three letter images;
* **§2** the binder tuple `selConTuple` and its slot lemmas;
* **§3** the parity engine extension: `selPar_neg`, `selPar_eq_of_two_mul_eq`, and the
  κ-arithmetic of the note's §3 (`selConKappa1_even`, `selConKappa2_even01`,
  `selConKappa3_par01`, and the `(1,0)` mirrors);
* **§4** the two exact even-decompositions: `selCon_core_decomp`, `selCon_handle_decomp`;
* **§5** ⭐⭐ the selection-bit form over the whole binder: `selConForm`, `selCon_relWord_f`,
  `selCon_bit`;
* **§6** ⭐⭐ the whole-binder witness: `selConWit`, `sqRelWord_selConWit`, `selConWit_even`;
* **§7** ⭐⭐ the containment on the live locus: `sqRelWord_selConWit_refine`,
  `selCon_contain`, `selCon_increment_exact`, and concrete instances;
* **§8** committed axiom prints (all std-3).

Companion memo: `docs/dyadic/w50-selection-note.md` §3 and §5 (recommended ticket 1).
-/

namespace GQ2

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The binder dressing data

A level-one dressing of one slot, as seen by a hom of the selection family, is a word in the
three cleared letters `Ū`, `V̄`, `t̄` times an achievable `γ₂`-correction and a central part.
Because all three letter images have `b`-column zero, the `(d, e)`-columns of any such word add
slot by slot, so the whole achievable set is captured by seven scalars: the three letter
components `u`, `v`, `w`, the three `Λ`-generator coefficients `r`, `s`, `t`, and a free
class-three coordinate `f`.  The letter images themselves are the committed closed forms:
`selConU` is `selHom_sqEichU`'s value, `selConV` is `selHom_sqEichV`'s, and `selConX1` is the
`x₁`-slot value `selMark_two`, which is also `selHom_selTee`'s image of `t`. -/

section BinderData

/-- A level-one dressing datum with its achievable junk: `u`, `v`, `w` are the `Ū`-, `V̄`- and
`t̄`-components of a slot dressing read in `ℤ/8`; `r`, `s`, `t` are the coefficients on the
three `Λ`-generators `(−A, C)`, `(−B, D)`, `(−2P, −2Q)` (the achievable `γ₂`-corrections, in
the parametrisation of `selLam`); `f` is a free class-three coordinate. -/
structure SelConDress where
  /-- The `Ū`-component of the dressing. -/
  u : gr3R
  /-- The `V̄`-component of the dressing. -/
  v : gr3R
  /-- The `t̄`-component of the dressing. -/
  w : gr3R
  /-- The coefficient on the `Λ`-generator `(−A, C)`. -/
  r : gr3R
  /-- The coefficient on the `Λ`-generator `(−B, D)`. -/
  s : gr3R
  /-- The coefficient on the `Λ`-generator `(−2P, −2Q)`. -/
  t : gr3R
  /-- A free class-three coordinate. -/
  f : gr3R

/-- The trivial dressing datum. -/
def selConTriv : SelConDress := ⟨0, 0, 0, 0, 0, 0, 0⟩

/-- The image of the cleared letter `Ū` at the row pair `(T, S)`: the committed
`selHom_sqEichU`, with `selT` replaced by the free row parameter `T`. -/
def selConU (A C T : gr3R) : SqU4 gr3R := ⟨A, 0, C, 0, -(T * C), 0⟩

/-- The image of the cleared letter `V̄`: the committed `selHom_sqEichV` at row `S`. -/
def selConV (B D S : gr3R) : SqU4 gr3R := ⟨B, 0, D, -(B * S), 0, 0⟩

/-- The `x₁`-slot value of the selection marking, which is also the image of the `λ`- and
`ν'`-trivial element `t = x₁x₀⁻²` (`selMark_two`, `selHom_selTee`). -/
def selConX1 (A B P Q : gr3R) : SqU4 gr3R := ⟨0, 0, 0, P, Q, -((A + B) * Q)⟩

/-- **The image of a level-one dressing datum.**  The abelian columns are the two free
characters on the `Ū`- and `V̄`-components; the `(d, e)`-columns collect the letter images'
class-two parts (`−u·TC` from `Ū`, `−v·BS` from `V̄`, `w·(P, Q)` from `t̄`) plus the
`Λ`-correction in the generator parametrisation of `selLam`; the class-three coordinate is
free.  Because all letter images have `b = 0`, the `(d, e)`-columns of an arbitrary word in
them add exactly, so this closed form covers every product of letter powers in any order. -/
def selConVal (A B C D P Q T S : gr3R) (x : SelConDress) : SqU4 gr3R :=
  ⟨A * x.u + B * x.v, 0, C * x.u + D * x.v,
    -(x.v * (B * S)) + x.w * P + (-(x.r * A) - x.s * B - 2 * (x.t * P)),
    -(x.u * (T * C)) + x.w * Q + (x.r * C + x.s * D - 2 * (x.t * Q)),
    x.f⟩

@[simp] theorem selConVal_triv (A B C D P Q T S : gr3R) :
    selConVal A B C D P Q T S selConTriv = 1 := by
  ext <;> simp [selConVal, selConTriv]

/-- The `(d, e)`-junk of a dressing datum with trivial letter components is an achievable
`γ₂`-element: its `(d, e)`-pair lies in `Λ`, by construction. -/
theorem selConVal_lam (A B C D P Q T S : gr3R) (x : SelConDress) (hu : x.u = 0) (hv : x.v = 0)
    (hw : x.w = 0) : selLam A B C D P Q (selConVal A B C D P Q T S x) :=
  ⟨x.r, x.s, x.t, by simp [selConVal, hu, hv, hw], by simp [selConVal, hu, hv, hw]⟩

end BinderData

/-! ## §2 The binder tuple

The five-slot tuple of a level-one dressed frame, in the image of a selection-family hom: the
σ-slot is the `ν'`-column generator times its dressing, the `x₀`-slot is a bare dressing, the
`x₁`-slot is the marking value times its dressing, the two `j`-handle slots are the cleared
letters times their dressings, and every other handle slot is trivial.  At the canonical row
`(T, S) = (0, 1)` and trivial data this is exactly the committed slot-image tuple of
`sqRelWord_selHom_sqArbFrame`; the `t`-dressed instances of §6c are the data
`x₃ = ⟨0, 0, 1, 0, 0, 0, 0⟩`. -/

section BinderTuple

variable {h : ℕ} {j : Fin h}

/-- **The binder tuple**: the five slot images of a level-one dressed frame at the binder
point `(A, B, C, D, P, Q, T, S)`, with dressing data `x₀, …, x₄` on the σ-, `x₀`-, `x₁`- and
two `j`-handle slots, and every other slot trivial. -/
def selConTuple (h : ℕ) (j : Fin h) (A B C D P Q T S : gr3R)
    (x₀ x₁ x₂ x₃ x₄ : SelConDress) : Fin (sqRank h) → SqU4 gr3R :=
  fun i =>
    if (i : ℕ) = 0 then ⟨0, 1, 0, 0, 0, 0⟩ * selConVal A B C D P Q T S x₀ else
    if (i : ℕ) = 1 then selConVal A B C D P Q T S x₁ else
    if (i : ℕ) = 2 then selConX1 A B P Q * selConVal A B C D P Q T S x₂ else
    if i = sqHandleIdxU j then selConU A C T * selConVal A B C D P Q T S x₃ else
    if i = sqHandleIdxV j then selConV B D S * selConVal A B C D P Q T S x₄ else 1

private theorem selCon_ne_handleU_of_lt {i : Fin (sqRank h)} (hi : (i : ℕ) < 3) :
    i ≠ sqHandleIdxU j := by
  intro hc
  rw [hc, sqHandleIdxU_val] at hi
  omega

private theorem selCon_ne_handleV_of_lt {i : Fin (sqRank h)} (hi : (i : ℕ) < 3) :
    i ≠ sqHandleIdxV j := by
  intro hc
  rw [hc, sqHandleIdxV_val] at hi
  omega

private theorem selCon_handleV_ne_handleU (j' : Fin h) : sqHandleIdxV j' ≠ sqHandleIdxU j := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [sqHandleIdxV_val, sqHandleIdxU_val] at hv
  omega

private theorem selCon_handleU_ne_handleU {j' : Fin h} (hne : j' ≠ j) :
    sqHandleIdxU j' ≠ sqHandleIdxU j := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [sqHandleIdxU_val, sqHandleIdxU_val] at hv
  exact hne (Fin.val_injective (by omega))

private theorem selCon_handleU_ne_handleV (j' : Fin h) : sqHandleIdxU j' ≠ sqHandleIdxV j := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [sqHandleIdxU_val, sqHandleIdxV_val] at hv
  omega

private theorem selCon_handleV_ne_handleV {j' : Fin h} (hne : j' ≠ j) :
    sqHandleIdxV j' ≠ sqHandleIdxV j := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [sqHandleIdxV_val, sqHandleIdxV_val] at hv
  exact hne (Fin.val_injective (by omega))

variable {A B C D P Q T S : gr3R} {x₀ x₁ x₂ x₃ x₄ : SelConDress}

@[simp] theorem selConTuple_zero :
    selConTuple h j A B C D P Q T S x₀ x₁ x₂ x₃ x₄ 0
      = (⟨0, 1, 0, 0, 0, 0⟩ : SqU4 gr3R) * selConVal A B C D P Q T S x₀ := by
  simp only [selConTuple, sqVal_zero]
  norm_num

@[simp] theorem selConTuple_one :
    selConTuple h j A B C D P Q T S x₀ x₁ x₂ x₃ x₄ 1 = selConVal A B C D P Q T S x₁ := by
  simp only [selConTuple, sqVal_one]
  norm_num

@[simp] theorem selConTuple_two :
    selConTuple h j A B C D P Q T S x₀ x₁ x₂ x₃ x₄ 2
      = selConX1 A B P Q * selConVal A B C D P Q T S x₂ := by
  simp only [selConTuple, sqVal_two]
  norm_num

@[simp] theorem selConTuple_handleU :
    selConTuple h j A B C D P Q T S x₀ x₁ x₂ x₃ x₄ (sqHandleIdxU j)
      = selConU A C T * selConVal A B C D P Q T S x₃ := by
  simp only [selConTuple, sqHandleIdxU_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

@[simp] theorem selConTuple_handleV :
    selConTuple h j A B C D P Q T S x₀ x₁ x₂ x₃ x₄ (sqHandleIdxV j)
      = selConV B D S * selConVal A B C D P Q T S x₄ := by
  simp only [selConTuple, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (selCon_handleV_ne_handleU j)]
  simp

theorem selConTuple_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    selConTuple h j A B C D P Q T S x₀ x₁ x₂ x₃ x₄ (sqHandleIdxU j') = 1 := by
  simp only [selConTuple, sqHandleIdxU_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (selCon_handleU_ne_handleU hne), if_neg (selCon_handleU_ne_handleV j')]

theorem selConTuple_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    selConTuple h j A B C D P Q T S x₀ x₁ x₂ x₃ x₄ (sqHandleIdxV j') = 1 := by
  simp only [selConTuple, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (selCon_handleV_ne_handleU j'), if_neg (selCon_handleV_ne_handleV hne)]

end BinderTuple

/-! ## §3 The parity engine extension, and the κ-arithmetic

Two small additions to `GradedSelect` §5b's `selPar` toolkit, then the κ-arithmetic of the
note's §3: under the two adjacency parities `κ₁ = (A+B)·T·D` is even at **every** binder point
(the quadratic block of the bit form never fires in this slice); at an uncleared type `(0, 1)`
the weights `A`, `C` are forced even, `κ₂ = A·Q + C·P` is even, and the parity of
`κ₃ = B·Q + D·P` is the mod-2 second-order datum `B·(C/2) + D·(A/2)`; the type `(1, 0)`
mirrors with the two κ's exchanged.  At type `(1, 1)` both `κ₂` and `κ₃` can fire; the
committed §6c instances live at type `(0, 1)`. -/

section ParityEngine

/-- Parity is invariant under negation. -/
theorem selPar_neg : ∀ x : gr3R, selPar (-x) = selPar x := by decide

/-- Parities can be compared after multiplication by `2`: over `ℤ/8` the equation `2x = 2y`
pins `x − y` to `{0, 4}`, which parity cannot see. -/
theorem selPar_eq_of_two_mul_eq : ∀ x y : gr3R, 2 * x = 2 * y → selPar x = selPar y := by
  decide

variable {A B C D P Q T S : gr3R}

/-- The mod-2 shadow of the `(a, b)`-adjacency parity, as in `selCross_even`. -/
private theorem selCon_par_hd (hd : 2 * P + (A * S - B * T) = 0) :
    selPar A * selPar S - selPar B * selPar T = 0 := by
  have hc := congrArg selPar hd
  rw [selPar_add, selPar_two_mul, selPar_sub, selPar_mul, selPar_mul, selPar_zero,
    zero_add] at hc
  exact hc

/-- …and of the `(b, c)`-adjacency parity. -/
private theorem selCon_par_he (he : 2 * Q + (T * D - S * C) = 0) :
    selPar T * selPar D - selPar S * selPar C = 0 := by
  have hc := congrArg selPar he
  rw [selPar_add, selPar_two_mul, selPar_sub, selPar_mul, selPar_mul, selPar_zero,
    zero_add] at hc
  exact hc

/-- The 𝔽₂ core of the κ₁-vanishing: the two adjacency parities alone kill `(a+b)·t·d`. -/
private theorem selConPar_kappa1 : ∀ a b c d t s : ZMod 2,
    a * s - b * t = 0 → t * d - s * c = 0 → (a + b) * (t * d) = 0 := by
  decide

/-- ⭐ **The quadratic coefficient of the bit form is even at every binder point**: the two
adjacency parities force `κ₁ = (A+B)·T·D ∈ 2·ℤ/8`, with no uncleared hypothesis.  This is the
note's "the quadratic block never fires in this slice". -/
theorem selConKappa1_even (hd : 2 * P + (A * S - B * T) = 0)
    (he : 2 * Q + (T * D - S * C) = 0) : ∃ k : gr3R, (A + B) * (T * D) = 2 * k := by
  rw [← selPar_eq_zero_iff, selPar_mul, selPar_mul, selPar_add]
  exact selConPar_kappa1 (selPar A) (selPar B) (selPar C) (selPar D) (selPar T) (selPar S)
    (selCon_par_hd hd) (selCon_par_he he)

/-- At an uncleared type `(0, 1)` the `(a, b)`-parity forces the `u`-weight `A` even. -/
theorem selConA_even01 (hd : 2 * P + (A * S - B * T) = 0) (hT : selPar T = 0)
    (hS : selPar S = 1) : ∃ a₂ : gr3R, A = 2 * a₂ := by
  rw [← selPar_eq_zero_iff]
  have h1 := selCon_par_hd hd
  rw [hT, hS, mul_one, mul_zero, sub_zero] at h1
  exact h1

/-- …and the `(b, c)`-parity forces `C` even. -/
theorem selConC_even01 (he : 2 * Q + (T * D - S * C) = 0) (hT : selPar T = 0)
    (hS : selPar S = 1) : ∃ c₂ : gr3R, C = 2 * c₂ := by
  rw [← selPar_eq_zero_iff]
  have h2 := selCon_par_he he
  rw [hT, hS, zero_mul, one_mul, zero_sub, neg_eq_zero] at h2
  exact h2

/-- ⭐ At an uncleared type `(0, 1)` the coefficient `κ₂ = A·Q + C·P` is even: the `U`-side
`t̄`-couplings of the bit form are invisible there. -/
theorem selConKappa2_even01 (hd : 2 * P + (A * S - B * T) = 0)
    (he : 2 * Q + (T * D - S * C) = 0) (hT : selPar T = 0) (hS : selPar S = 1) :
    ∃ k : gr3R, A * Q + C * P = 2 * k := by
  obtain ⟨a₂, ha⟩ := selConA_even01 hd hT hS
  obtain ⟨c₂, hc⟩ := selConC_even01 he hT hS
  exact ⟨a₂ * Q + c₂ * P, by rw [ha, hc]; ring⟩

/-- The 𝔽₂ finish of the κ₃-criterion at type `(0, 1)`. -/
private theorem selConPar_kappa3 : ∀ b d s c₂ t₂ a₂ q p : ZMod 2,
    q = s * c₂ - t₂ * d → p = b * t₂ - a₂ * s → s = 1 → b * q + d * p = b * c₂ + d * a₂ := by
  decide

/-- ⭐ **The κ₃-criterion at type `(0, 1)`** (the note's `κ₃ ≡ B·(C/2) + D·(A/2)`): with the
even halves `A = 2·A₂`, `C = 2·C₂`, `T = 2·T₂` exhibited, the parity of `κ₃ = B·Q + D·P` is
the parity of `B·C₂ + D·A₂`.  The adjacency parities determine `P`, `Q` only through the
halves of `B·T − A·S` and `S·C − T·D`: the bit reads second-order data of the weights, one
level below the class-two realizability parity. -/
theorem selConKappa3_par01 (hd : 2 * P + (A * S - B * T) = 0)
    (he : 2 * Q + (T * D - S * C) = 0) (hT : selPar T = 0) (hS : selPar S = 1) :
    ∃ A₂ C₂ T₂ : gr3R, A = 2 * A₂ ∧ C = 2 * C₂ ∧ T = 2 * T₂ ∧
      selPar (B * Q + D * P) = selPar (B * C₂ + D * A₂) := by
  obtain ⟨A₂, hA⟩ := selConA_even01 hd hT hS
  obtain ⟨C₂, hC⟩ := selConC_even01 he hT hS
  obtain ⟨T₂, hT₂⟩ := (selPar_eq_zero_iff T).mp hT
  refine ⟨A₂, C₂, T₂, hA, hC, hT₂, ?_⟩
  have hQ : selPar Q = selPar (S * C₂ - T₂ * D) :=
    selPar_eq_of_two_mul_eq _ _ (by linear_combination he + S * hC - D * hT₂)
  have hP : selPar P = selPar (B * T₂ - A₂ * S) :=
    selPar_eq_of_two_mul_eq _ _ (by linear_combination hd - S * hA + B * hT₂)
  rw [selPar_add, selPar_mul, selPar_mul, hQ, hP, selPar_add, selPar_mul, selPar_mul]
  exact selConPar_kappa3 (selPar B) (selPar D) (selPar S) (selPar C₂) (selPar T₂) (selPar A₂)
    _ _ (by rw [selPar_sub, selPar_mul, selPar_mul])
    (by rw [selPar_sub, selPar_mul, selPar_mul]) hS

/-- At an uncleared type `(1, 0)` the `(a, b)`-parity forces the `v`-weight `B` even. -/
theorem selConB_even10 (hd : 2 * P + (A * S - B * T) = 0) (hT : selPar T = 1)
    (hS : selPar S = 0) : ∃ b₂ : gr3R, B = 2 * b₂ := by
  rw [← selPar_eq_zero_iff]
  have h1 := selCon_par_hd hd
  rw [hT, hS, mul_zero, mul_one, zero_sub, neg_eq_zero] at h1
  exact h1

/-- …and the `(b, c)`-parity forces `D` even. -/
theorem selConD_even10 (he : 2 * Q + (T * D - S * C) = 0) (hT : selPar T = 1)
    (hS : selPar S = 0) : ∃ d₂ : gr3R, D = 2 * d₂ := by
  rw [← selPar_eq_zero_iff]
  have h2 := selCon_par_he he
  rw [hT, hS, one_mul, zero_mul, sub_zero] at h2
  exact h2

/-- ⭐ The mirror of `selConKappa2_even01`: at type `(1, 0)` the coefficient `κ₃ = B·Q + D·P`
is even, so the `V`-side `t̄`-couplings are invisible there. -/
theorem selConKappa3_even10 (hd : 2 * P + (A * S - B * T) = 0)
    (he : 2 * Q + (T * D - S * C) = 0) (hT : selPar T = 1) (hS : selPar S = 0) :
    ∃ k : gr3R, B * Q + D * P = 2 * k := by
  obtain ⟨b₂, hb⟩ := selConB_even10 hd hT hS
  obtain ⟨d₂, hdd⟩ := selConD_even10 he hT hS
  exact ⟨b₂ * Q + d₂ * P, by rw [hb, hdd]; ring⟩

/-- The 𝔽₂ finish of the κ₂-criterion at type `(1, 0)`. -/
private theorem selConPar_kappa2 : ∀ a c t d₂ s₂ b₂ q p : ZMod 2,
    q = s₂ * c - t * d₂ → p = b₂ * t - a * s₂ → t = 1 → a * q + c * p = a * d₂ + c * b₂ := by
  decide

/-- ⭐ The mirror of `selConKappa3_par01`: at type `(1, 0)`, with `B = 2·B₂`, `D = 2·D₂`,
`S = 2·S₂` exhibited, the parity of `κ₂ = A·Q + C·P` is the parity of `A·D₂ + C·B₂`. -/
theorem selConKappa2_par10 (hd : 2 * P + (A * S - B * T) = 0)
    (he : 2 * Q + (T * D - S * C) = 0) (hT : selPar T = 1) (hS : selPar S = 0) :
    ∃ B₂ D₂ S₂ : gr3R, B = 2 * B₂ ∧ D = 2 * D₂ ∧ S = 2 * S₂ ∧
      selPar (A * Q + C * P) = selPar (A * D₂ + C * B₂) := by
  obtain ⟨B₂, hB⟩ := selConB_even10 hd hT hS
  obtain ⟨D₂, hD⟩ := selConD_even10 he hT hS
  obtain ⟨S₂, hS₂⟩ := (selPar_eq_zero_iff S).mp hS
  refine ⟨B₂, D₂, S₂, hB, hD, hS₂, ?_⟩
  have hQ : selPar Q = selPar (S₂ * C - T * D₂) :=
    selPar_eq_of_two_mul_eq _ _ (by linear_combination he + C * hS₂ - T * hD)
  have hP : selPar P = selPar (B₂ * T - A * S₂) :=
    selPar_eq_of_two_mul_eq _ _ (by linear_combination hd - A * hS₂ + T * hB)
  rw [selPar_add, selPar_mul, selPar_mul, hQ, hP, selPar_add, selPar_mul, selPar_mul]
  exact selConPar_kappa2 (selPar A) (selPar C) (selPar T) (selPar D₂) (selPar S₂) (selPar B₂)
    _ _ (by rw [selPar_sub, selPar_mul, selPar_mul])
    (by rw [selPar_sub, selPar_mul, selPar_mul]) hT

/-- The 𝔽₂ core of the `T·S·(C+D)`-evenness used by the witness rows. -/
private theorem selConPar_ts : ∀ c d t s : ZMod 2,
    t * d - s * c = 0 → t * s * (c + d) = 0 := by
  decide

/-- The `(b, c)`-adjacency parity forces `T·S·(C+D)` even, at every binder point: the row
product `T·S` is even off type `(1, 1)`, and at type `(1, 1)` the parity forces `C ≡ D`. -/
theorem selCon_ts_even (he : 2 * Q + (T * D - S * C) = 0) :
    ∃ k : gr3R, T * S * (C + D) = 2 * k := by
  rw [← selPar_eq_zero_iff, selPar_mul, selPar_mul, selPar_add]
  exact selConPar_ts (selPar C) (selPar D) (selPar T) (selPar S) (selCon_par_he he)

end ParityEngine

/-! ## §4 The two exact even-decompositions

The class-three residue of a binder tuple splits into the core contribution
`sqU4Core (m 0) (m 1) (m 2)` and the handle contribution `u4Comm3 (m U) (m V)` (the cross term
carries the vanishing `b`-columns, and the exponent-slot class-three coordinates are even
multiples).  Each contribution is here decomposed **exactly** as its κ-leading part plus an
explicit even remainder: every `Λ`-junk pairing is even through `selCross_even`'s witness
`A·D + B·C = 2·k₀`, the note's replacement `B·C·(T+S) = (A+B)·T·D + 2·(A·Q + P·C + B·Q)` is an
exact consequence of the two adjacency parities, and the one genuinely mod-2 step (the core
block pairing the σ-slot columns against the `x₀`-slot letter data) is the 𝔽₂ lemma
`selCon_block_even`, which consumes the class-two admissibility parities of the `x₀`-slot
data. -/

section Decompositions

variable {h : ℕ} {j : Fin h} {A B C D P Q T S : gr3R}

/-- The 𝔽₂ core of the block evenness: ten variables, four parity hypotheses. -/
private theorem selConPar_block : ∀ a b c d t s u₀ v₀ u₁ v₁ : ZMod 2,
    a * s - b * t = 0 → t * d - s * c = 0 → a * u₁ + b * v₁ = 0 → c * u₁ + d * v₁ = 0 →
    (c * u₀ + d * v₀) * (v₁ * (b * s)) - (a * u₀ + b * v₀) * (u₁ * (t * c)) = 0 := by
  decide

/-- **The core block is even on the admissible locus**: the pairing of the σ-slot column data
against the `x₀`-slot letter data is even whenever the `x₀`-slot data satisfy the two
class-two parities.  This is the single step of the bit-form derivation that is genuinely
mod 2; every uncleared type kills it through a different factor. -/
theorem selCon_block_even (hd : 2 * P + (A * S - B * T) = 0)
    (he : 2 * Q + (T * D - S * C) = 0) {u₀ v₀ u₁ v₁ : gr3R}
    (hα : ∃ x, A * u₁ + B * v₁ = 2 * x) (hγ : ∃ x, C * u₁ + D * v₁ = 2 * x) :
    ∃ k : gr3R, (C * u₀ + D * v₀) * (v₁ * (B * S)) - (A * u₀ + B * v₀) * (u₁ * (T * C))
      = 2 * k := by
  obtain ⟨xα, hxα⟩ := hα
  obtain ⟨xγ, hxγ⟩ := hγ
  have h3 : selPar A * selPar u₁ + selPar B * selPar v₁ = 0 := by
    have hc := congrArg selPar hxα
    rw [selPar_add, selPar_mul, selPar_mul, selPar_two_mul] at hc
    exact hc
  have h4 : selPar C * selPar u₁ + selPar D * selPar v₁ = 0 := by
    have hc := congrArg selPar hxγ
    rw [selPar_add, selPar_mul, selPar_mul, selPar_two_mul] at hc
    exact hc
  rw [← selPar_eq_zero_iff, selPar_sub, selPar_mul, selPar_mul, selPar_mul, selPar_mul,
    selPar_add, selPar_add, selPar_mul, selPar_mul, selPar_mul, selPar_mul, selPar_mul,
    selPar_mul]
  exact selConPar_block (selPar A) (selPar B) (selPar C) (selPar D) (selPar T) (selPar S)
    (selPar u₀) (selPar v₀) (selPar u₁) (selPar v₁)
    (selCon_par_hd hd) (selCon_par_he he) h3 h4

/-- ⭐ **The handle contribution, decomposed exactly.**  The cubic commutator form of the two
dressed handle slots is the κ-leading part of the bit form plus an explicit even remainder;
the only inputs are the two adjacency parities and the uncleared hypothesis (through
`selCross_even`).  All six junk scalars of each handle datum land in the remainder. -/
theorem selCon_handle_decomp (hd : 2 * P + (A * S - B * T) = 0)
    (he : 2 * Q + (T * D - S * C) = 0) (hTS : selPar T = 1 ∨ selPar S = 1)
    (x₃ x₄ : SelConDress) :
    ∃ k : gr3R, SqU4.u4Comm3 (selConU A C T * selConVal A B C D P Q T S x₃)
        (selConV B D S * selConVal A B C D P Q T S x₄)
      = (A + B) * (T * D) * ((1 + x₃.u) * (1 + x₄.v) + x₃.v * x₄.u)
        + (A * Q + C * P) * ((1 + x₃.u) * x₄.w + x₄.u * x₃.w)
        + (B * Q + D * P) * (x₃.v * x₄.w + (1 + x₄.v) * x₃.w) + 2 * k := by
  obtain ⟨k₀, hk₀⟩ := selCross_even hd he hTS
  refine ⟨-((A + B) * (T * D) * (x₃.v * x₄.u))
    + (A * Q + P * C + B * Q) * ((1 + x₃.u) * (1 + x₄.v) - x₃.v * x₄.u)
    - A * Q * (x₄.u * x₃.w) - C * P * ((1 + x₃.u) * x₄.w)
    - B * Q * ((1 + x₄.v) * x₃.w) - D * P * (x₃.v * x₄.w)
    + (x₄.r * (A * C * (1 + x₃.u) + k₀ * x₃.v) + x₄.s * (k₀ * (1 + x₃.u) + B * D * x₃.v)
        - x₄.t * ((A + (A * x₃.u + B * x₃.v)) * Q - (C + (C * x₃.u + D * x₃.v)) * P))
    - (x₃.r * (k₀ * (1 + x₄.v) + A * C * x₄.u) + x₃.s * (B * D * (1 + x₄.v) + k₀ * x₄.u)
        + x₃.t * (P * (D + (C * x₄.u + D * x₄.v)) - Q * (B + (A * x₄.u + B * x₄.v)))), ?_⟩
  simp only [selConU, selConV, selConVal, SqU4.u4Comm3, SqU4.mul_a, SqU4.mul_b, SqU4.mul_c,
    SqU4.mul_d, SqU4.mul_e]
  linear_combination (-(C * ((1 + x₃.u) * (1 + x₄.v) - x₃.v * x₄.u))) * hd
    + (-((A + B) * ((1 + x₃.u) * (1 + x₄.v) - x₃.v * x₄.u))) * he
    + (x₄.r * x₃.v + x₄.s * (1 + x₃.u) - x₃.r * (1 + x₄.v) - x₃.s * x₄.u) * hk₀

/-- ⭐ **The core contribution, decomposed exactly.**  The `sqU4Core` of the three dressed core
slots is the κ-leading part of the bit form plus an even remainder, given the class-two
admissibility parities of the `x₀`- and `x₁`-slot abelian data (the witnesses `xα₁, …` are the
exhibited halves).  The `κ₁`-part `(A+B)·T·D·(m₀n₁ + n₀m₁)` is kept for fidelity to the note's
display; it is itself even by `selConKappa1_even`, and the remainder absorbs it. -/
theorem selCon_core_decomp (hd : 2 * P + (A * S - B * T) = 0)
    (he : 2 * Q + (T * D - S * C) = 0) (hTS : selPar T = 1 ∨ selPar S = 1)
    (x₀ x₁ x₂ : SelConDress) {xα₁ xγ₁ xα₂ xγ₂ : gr3R}
    (hα₁ : A * x₁.u + B * x₁.v = 2 * xα₁) (hγ₁ : C * x₁.u + D * x₁.v = 2 * xγ₁)
    (hα₂ : A * x₂.u + B * x₂.v = 2 * xα₂) (hγ₂ : C * x₂.u + D * x₂.v = 2 * xγ₂) :
    ∃ k : gr3R, sqU4Core ((⟨0, 1, 0, 0, 0, 0⟩ : SqU4 gr3R) * selConVal A B C D P Q T S x₀)
        (selConVal A B C D P Q T S x₁) (selConX1 A B P Q * selConVal A B C D P Q T S x₂)
      = (A + B) * (T * D) * (x₀.u * x₁.v + x₀.v * x₁.u)
        + (A * Q + C * P) * (x₁.w * x₀.u) + (B * Q + D * P) * (x₁.w * x₀.v) + 2 * k := by
  obtain ⟨k₀, hk₀⟩ := selCross_even hd he hTS
  obtain ⟨kb, hkb⟩ := selCon_block_even hd he (u₀ := x₀.u) (v₀ := x₀.v)
    ⟨xα₁, hα₁⟩ ⟨xγ₁, hγ₁⟩
  obtain ⟨kk₁, hkk₁⟩ := selConKappa1_even hd he
  refine ⟨-((A * x₀.u + B * x₀.v) * xγ₁) + kb
    - x₁.w * (x₀.u * (C * P) + x₀.v * (D * P))
    + (x₁.r * (A * C * x₀.u + k₀ * x₀.v) + x₁.s * (k₀ * x₀.u + B * D * x₀.v)
        - x₁.t * ((A * x₀.u + B * x₀.v) * Q - (C * x₀.u + D * x₀.v) * P))
    + (-(x₀.v * (B * S)) + x₀.w * P + (-(x₀.r * A) - x₀.s * B - 2 * (x₀.t * P))) * xγ₁
    - (-(x₀.u * (T * C)) + x₀.w * Q + (x₀.r * C + x₀.s * D - 2 * (x₀.t * Q))
        + (C * x₀.u + D * x₀.v)) * xα₁
    + 3 * (xα₁ * (C * x₁.u + D * x₁.v))
    - (A * x₁.u + B * x₁.v) * (C * x₂.u + D * x₂.v)
    - (A * x₂.u + B * x₂.v) * (C * x₂.u + D * x₂.v)
    + 5 * ((A * x₁.u + B * x₁.v)
        * (-(x₁.u * (T * C)) + x₁.w * Q + (x₁.r * C + x₁.s * D - 2 * (x₁.t * Q))))
    - 4 * ((A * x₁.u + B * x₁.v)
        * (Q + (-(x₂.u * (T * C)) + x₂.w * Q + (x₂.r * C + x₂.s * D - 2 * (x₂.t * Q)))))
    + 5 * ((C * x₁.u + D * x₁.v)
        * (-(x₁.v * (B * S)) + x₁.w * P + (-(x₁.r * A) - x₁.s * B - 2 * (x₁.t * P))))
    - 4 * ((-(x₁.v * (B * S)) + x₁.w * P + (-(x₁.r * A) - x₁.s * B - 2 * (x₁.t * P)))
        * (C * x₂.u + D * x₂.v))
    + xα₂ * (Q + (-(x₂.u * (T * C)) + x₂.w * Q + (x₂.r * C + x₂.s * D - 2 * (x₂.t * Q))))
    + xγ₂ * (P + (-(x₂.v * (B * S)) + x₂.w * P + (-(x₂.r * A) - x₂.s * B - 2 * (x₂.t * P))))
    - kk₁ * (x₀.u * x₁.v + x₀.v * x₁.u), ?_⟩
  simp only [selConX1, selConVal, sqU4Core, SqU4.mul_a, SqU4.mul_b, SqU4.mul_c, SqU4.mul_d,
    SqU4.mul_e]
  linear_combination (-(A * x₀.u + B * x₀.v)
      + (-(x₀.v * (B * S)) + x₀.w * P + (-(x₀.r * A) - x₀.s * B - 2 * (x₀.t * P)))) * hγ₁
    + (-(-(x₀.u * (T * C)) + x₀.w * Q + (x₀.r * C + x₀.s * D - 2 * (x₀.t * Q))
        + (C * x₀.u + D * x₀.v)) + 3 * (C * x₁.u + D * x₁.v)) * hα₁
    + (Q + (-(x₂.u * (T * C)) + x₂.w * Q + (x₂.r * C + x₂.s * D - 2 * (x₂.t * Q)))) * hα₂
    + (P + (-(x₂.v * (B * S)) + x₂.w * P + (-(x₂.r * A) - x₂.s * B - 2 * (x₂.t * P)))) * hγ₂
    + hkb + (x₁.r * x₀.v + x₁.s * x₀.u) * hk₀
    + (-(x₀.u * x₁.v + x₀.v * x₁.u)) * hkk₁

end Decompositions

/-! ## §5 ⭐⭐ The selection-bit form over the whole binder

The centerpiece: on any binder tuple whose `x₀`- and `x₁`-slot abelian data satisfy the
class-two parities, the class-three residue of the relator is the κ-weighted lift of the
𝔽₂-form `selConForm` plus an even remainder (`selCon_relWord_f`), so its parity **is** the
form evaluated at the data parities (`selCon_bit`).  The hypotheses do not constrain the σ- or
handle-slot data at all, and the conclusion mentions only the eleven coordinates
`(m₀, n₀, m₁, n₁, k₁, m₃, n₃, k₃, m₄, n₄, k₄)`: the `x₁`-slot data `x₂`, all `Λ`-junk and all
class-three coordinates are invisible to the bit, and so is the σ-slot `t̄`-component `x₀.w`,
which is the slice-blindness of `GradedSelect` §6b seen from the formula side. -/

section BitForm

variable {h : ℕ} {j : Fin h} {A B C D P Q T S : gr3R}

/-- ⭐⭐ **The selection bit as an explicit 𝔽₂-form**: the display of the note's §3.  The
arguments are the three κ-parities and the eleven level-one data parities of the σ-, `x₀`- and
two handle slots, in the note's naming. -/
def selConForm (κ₁ κ₂ κ₃ m₀ n₀ m₁ n₁ k₁ m₃ n₃ k₃ m₄ n₄ k₄ : ZMod 2) : ZMod 2 :=
  κ₁ * (m₀ * n₁ + n₀ * m₁ + (1 + m₃) * (1 + n₄) + n₃ * m₄)
    + κ₂ * ((1 + m₃) * k₄ + m₄ * k₃ + k₁ * m₀)
    + κ₃ * (n₃ * k₄ + (1 + n₄) * k₃ + k₁ * n₀)

/-- ⭐⭐ **The class-three residue of a binder tuple, decomposed over the whole binder.**  At
every binder point (both adjacency parities, uncleared row) and any dressing data whose `x₀`-
and `x₁`-slot abelian columns satisfy the class-two parities (witnesses `xα₁, xγ₁, xα₂, xγ₂`),
the relator's class-three coordinate is the κ-weighted lift of the bit form plus an even
remainder.  The five lower rows are not assumed to vanish: only their mod-2 shadows on the two
exponent slots are consumed, which every class-two-admissible tuple satisfies. -/
theorem selCon_relWord_f (hd : 2 * P + (A * S - B * T) = 0)
    (he : 2 * Q + (T * D - S * C) = 0) (hTS : selPar T = 1 ∨ selPar S = 1)
    {x₀ x₁ x₂ x₃ x₄ : SelConDress} {xα₁ xγ₁ xα₂ xγ₂ : gr3R}
    (hα₁ : A * x₁.u + B * x₁.v = 2 * xα₁) (hγ₁ : C * x₁.u + D * x₁.v = 2 * xγ₁)
    (hα₂ : A * x₂.u + B * x₂.v = 2 * xα₂) (hγ₂ : C * x₂.u + D * x₂.v = 2 * xγ₂) :
    ∃ k : gr3R, (sqRelWord (selConTuple h j A B C D P Q T S x₀ x₁ x₂ x₃ x₄)).f
      = (A + B) * (T * D)
          * (x₀.u * x₁.v + x₀.v * x₁.u + (1 + x₃.u) * (1 + x₄.v) + x₃.v * x₄.u)
        + (A * Q + C * P) * ((1 + x₃.u) * x₄.w + x₄.u * x₃.w + x₁.w * x₀.u)
        + (B * Q + D * P) * (x₃.v * x₄.w + (1 + x₄.v) * x₃.w + x₁.w * x₀.v) + 2 * k := by
  obtain ⟨kc, hkc⟩ := selCon_core_decomp hd he hTS x₀ x₁ x₂ hα₁ hγ₁ hα₂ hγ₂
  obtain ⟨kh, hkh⟩ := selCon_handle_decomp hd he hTS x₃ x₄
  have hbc : (∑ j' : Fin h,
      ((selConTuple h j A B C D P Q T S x₀ x₁ x₂ x₃ x₄ (sqHandleIdxU j')).b
          * (selConTuple h j A B C D P Q T S x₀ x₁ x₂ x₃ x₄ (sqHandleIdxV j')).c
        - (selConTuple h j A B C D P Q T S x₀ x₁ x₂ x₃ x₄ (sqHandleIdxV j')).b
          * (selConTuple h j A B C D P Q T S x₀ x₁ x₂ x₃ x₄ (sqHandleIdxU j')).c)) = 0 := by
    refine Finset.sum_eq_zero fun j' _ => ?_
    by_cases hjj : j' = j
    · subst hjj
      rw [selConTuple_handleU, selConTuple_handleV]
      simp [selConU, selConV, selConVal]
    · rw [selConTuple_handleU_ne hjj, selConTuple_handleV_ne hjj]
      simp
  have hcm : (∑ j' : Fin h,
      SqU4.u4Comm3 (selConTuple h j A B C D P Q T S x₀ x₁ x₂ x₃ x₄ (sqHandleIdxU j'))
        (selConTuple h j A B C D P Q T S x₀ x₁ x₂ x₃ x₄ (sqHandleIdxV j')))
      = SqU4.u4Comm3 (selConTuple h j A B C D P Q T S x₀ x₁ x₂ x₃ x₄ (sqHandleIdxU j))
        (selConTuple h j A B C D P Q T S x₀ x₁ x₂ x₃ x₄ (sqHandleIdxV j)) := by
    refine sum_eq_at _ fun j' hne => ?_
    rw [selConTuple_handleU_ne hne, selConTuple_handleV_ne hne]
    simp [SqU4.u4Comm3]
  refine ⟨kc + kh + (-2 * (selConVal A B C D P Q T S x₁).f
    + (selConX1 A B P Q * selConVal A B C D P Q T S x₂).f), ?_⟩
  rw [SqU4.sqRelWord_f]
  simp only [sqU4Defect]
  rw [hbc, hcm, selConTuple_zero, selConTuple_one, selConTuple_two, selConTuple_handleU,
    selConTuple_handleV]
  linear_combination hkc + hkh

/-- ⭐⭐ **The selection bit over the whole binder** (deliverable 1, the note's §3 as a
theorem): the parity of the class-three residue equals `selConForm` at the κ-parities and the
eleven data parities.  Everything else, including the `x₁`-slot data, the σ-slot
`t̄`-component and every junk scalar, is invisible: it does not occur in the right-hand
side. -/
theorem selCon_bit (hd : 2 * P + (A * S - B * T) = 0)
    (he : 2 * Q + (T * D - S * C) = 0) (hTS : selPar T = 1 ∨ selPar S = 1)
    {x₀ x₁ x₂ x₃ x₄ : SelConDress} {xα₁ xγ₁ xα₂ xγ₂ : gr3R}
    (hα₁ : A * x₁.u + B * x₁.v = 2 * xα₁) (hγ₁ : C * x₁.u + D * x₁.v = 2 * xγ₁)
    (hα₂ : A * x₂.u + B * x₂.v = 2 * xα₂) (hγ₂ : C * x₂.u + D * x₂.v = 2 * xγ₂) :
    selPar ((sqRelWord (selConTuple h j A B C D P Q T S x₀ x₁ x₂ x₃ x₄)).f)
      = selConForm (selPar ((A + B) * (T * D))) (selPar (A * Q + C * P))
          (selPar (B * Q + D * P)) (selPar x₀.u) (selPar x₀.v) (selPar x₁.u) (selPar x₁.v)
          (selPar x₁.w) (selPar x₃.u) (selPar x₃.v) (selPar x₃.w) (selPar x₄.u)
          (selPar x₄.v) (selPar x₄.w) := by
  obtain ⟨k, hk⟩ := selCon_relWord_f hd he hTS hα₁ hγ₁ hα₂ hγ₂
  rw [hk]
  simp only [selPar_add, selPar_two_mul, add_zero]
  simp only [selConForm, selPar_add, selPar_mul, selPar_one]

end BitForm

end SqCore

end Dyadic

end GQ2

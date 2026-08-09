/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedFour

/-!
# W52-LIFT: the level-wise lift engine, instantiated at stage 3 → 4

`GradedContain` proved the class-three containment over the whole marking binder: at every
binder point there are admissible level-one data with selection bit zero, and on the live
locus the committed completion move kills the relator.  This file builds the **stage engine**
one level up, on the `U₅`-carrier of `GradedFour`: the affine-linear action of `γ₃`-dressings
on the class-four residue, its achievable image, the two-regime completion, and the schema a
later wave iterates.  Everything was validated numerically before transcription
(`scripts/w52_lift/sweep_u5.py` and successors).

What the class-four layer turned out to look like (the file's findings, all machine-checked
below or recorded honestly as measured):

* **the translation identity survives verbatim** (`sqRelWord_selLift`): dressing the two
  exponent slots by `γ₄` and the two `j`-handle slots by `γ₃` translates the relator by a
  central element, affine-linear in the dressings, with the *outermost* abelian columns
  `(a, d)` as coefficients, exactly as the note's stage-`k` conjecture predicts;
* **stage 3 is two functionals wide from up here.**  `U₅` has two class-three rows (`h`, `i`);
  a "class-three survivor" in this file means both die.  The committed `GradedSelect`
  machinery governs the `h`-row through `toU4L`; the `i`-row is genuinely new and its residue
  at the witness is `2·N − C·F·T` (§4): the class-three story of the columns that class three
  could not see;
* **the completion has two regimes, collapsed by parity** (the W51 sweep's mod-2 structure
  entering): with `κ₄ = B·D·F` a unit the `γ₃`-action is *surjective* and any residue dies
  (`sqRelWord_selLift_eq_one_odd`), something that never happens at class three; with
  `κ₄ = 2·unit⁻¹`-type pairing only even residues die (`sqRelWord_selLift_eq_one`), and the
  class-four selection bit is real (measured: odd residues at `F`-even live points survive
  every sampled achievable refinement);
* **the mirror regime** `κ₄' = A·C·E` acts through the `V`-handle slot
  (`sqRelWord_selLift_eq_one_odd'`).

## Contents

* **§1** `γ`-filtration predicates, the central calculus of `liftC`, and the word-level
  update lemmas (`sqWord_mul_liftC`, `handleWord_update_liftC`);
* **§2** the lift refinement `selLift` and ⭐⭐ the translation identity `sqRelWord_selLift`;
* **§3** the achievable `γ₃`-lattice `selLamThree` and ⭐⭐ the two-regime completion;
* **§4** ⭐⭐ the whole-binder witness at class four: the lifted tuple, its ten rows, the
  new `i`-row residue, and the stage-3 → stage-4 engine instance;
* **§5** the stage schema `LiftStep` and its 3 → 4 instance;
* **§6** committed axiom prints.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The `γ`-filtration and the central calculus

`γ₂`-, `γ₃`- and `γ₄`-shaped elements of `SqU5`, the central `(1,5)`-translations `liftC`,
and the two word-level update lemmas the translation identity needs: multiplying the two
exponent slots of the core word by central elements multiplies the word by a central element
with the relator weights `(−4, 2)`, and multiplying one entry of a product list by a central
element multiplies the product by it.  This is the class-four shadow of the fact that the
whole refinement calculus happens inside a two-step central extension. -/

section Filtration

variable {R : Type} [CommRing R]

/-- A `γ₂`-shaped element of the class-four test group: all four abelian columns vanish. -/
def SqU5.IsGaTwo (z : SqU5 R) : Prop := z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0

/-- A `γ₃`-shaped element: abelian and class-two coordinates vanish. -/
def SqU5.IsGaThree (z : SqU5 R) : Prop :=
  z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0 ∧ z.f = 0 ∧ z.g = 0

/-- A `γ₄`-shaped element: only the class-four coordinate may be non-zero. -/
def SqU5.IsGaFour (z : SqU5 R) : Prop :=
  z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0 ∧ z.f = 0 ∧ z.g = 0 ∧ z.h = 0 ∧ z.i = 0

theorem SqU5.IsGaThree.isGaTwo {z : SqU5 R} (hz : z.IsGaThree) : z.IsGaTwo :=
  ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1⟩

theorem SqU5.IsGaFour.isGaThree {z : SqU5 R} (hz : z.IsGaFour) : z.IsGaThree :=
  ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2.1, hz.2.2.2.2.2.2.1⟩

@[simp] theorem SqU5.isGaThree_one : (1 : SqU5 R).IsGaThree :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

@[simp] theorem SqU5.isGaTwo_one : (1 : SqU5 R).IsGaTwo := ⟨rfl, rfl, rfl, rfl⟩

/-- The central `(1,5)`-translation by `w`. -/
def liftC (w : R) : SqU5 R := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, w⟩

@[simp] theorem liftC_zero : liftC (0 : R) = 1 := rfl

@[simp] theorem liftC_j (w : R) : (liftC w).j = w := rfl

theorem liftC_isGaFour (w : R) : (liftC w).IsGaFour :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

@[simp] theorem liftC_mul_liftC (v w : R) : liftC v * liftC w = liftC (v + w) := by
  ext <;> simp [liftC]

@[simp] theorem liftC_inv (w : R) : (liftC w)⁻¹ = liftC (-w) := by
  ext <;> simp [liftC]

/-- `liftC` is central. -/
theorem liftC_comm (p : SqU5 R) (w : R) : p * liftC w = liftC w * p := by
  ext <;> simp [liftC, add_comm]

/-- Multiplying on the right by `liftC` translates the class-four coordinate and nothing
else (`SqU5.mul_center_j` in `liftC` form). -/
theorem mul_liftC_apply (p : SqU5 R) (w : R) :
    p * liftC w = ⟨p.a, p.b, p.c, p.d, p.e, p.f, p.g, p.h, p.i, p.j + w⟩ :=
  SqU5.mul_center_j p w

/-- Conjugation fixes the centre. -/
theorem conjP_liftC (w : R) (g : SqU5 R) : conjP (liftC w) g = liftC w := by
  ext <;> simp [liftC, SqU5.conjP_j]

/-- Commutators ignore a central right factor in either argument. -/
theorem commP_mul_liftC_left (p q : SqU5 R) (w : R) :
    commP (p * liftC w) q = commP p q := by
  ext <;> simp only [SqU5.commP_a, SqU5.commP_b, SqU5.commP_c, SqU5.commP_d, SqU5.commP_e,
    SqU5.commP_f, SqU5.commP_g, SqU5.commP_h, SqU5.commP_i, SqU5.commP_j, SqU5.u5Comm3L,
    SqU5.u5Comm3R, SqU5.u5Comm4, liftC, SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d,
    SqU5.mul_e, SqU5.mul_f, SqU5.mul_g, SqU5.mul_h, SqU5.mul_i] <;> ring

theorem commP_mul_liftC_right (p q : SqU5 R) (w : R) :
    commP p (q * liftC w) = commP p q := by
  ext <;> simp only [SqU5.commP_a, SqU5.commP_b, SqU5.commP_c, SqU5.commP_d, SqU5.commP_e,
    SqU5.commP_f, SqU5.commP_g, SqU5.commP_h, SqU5.commP_i, SqU5.commP_j, SqU5.u5Comm3L,
    SqU5.u5Comm3R, SqU5.u5Comm4, liftC, SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d,
    SqU5.mul_e, SqU5.mul_f, SqU5.mul_g, SqU5.mul_h, SqU5.mul_i] <;> ring

/-- ⭐ **The core word swallows exponent-slot central dressings with the relator weights**:
dressing the `x₀`-slot by `liftC α` and the `x₁`-slot by `liftC β` multiplies the core word by
`liftC (−4·α + 2·β)`.  No closed form of the word is consumed: the proof is componentwise
expansion of both sides. -/
theorem sqWord_mul_liftC (s x y : SqU5 R) (α β : R) :
    sqWord s (x * liftC α) (y * liftC β) = sqWord s x y * liftC (-4 * α + 2 * β) := by
  ext <;> simp only [sqWord, conjP, commP, pow_succ, pow_zero, one_mul, liftC,
    SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d, SqU5.mul_e, SqU5.mul_f, SqU5.mul_g,
    SqU5.mul_h, SqU5.mul_i, SqU5.mul_j, SqU5.inv_a, SqU5.inv_b, SqU5.inv_c, SqU5.inv_d,
    SqU5.inv_e, SqU5.inv_f, SqU5.inv_g, SqU5.inv_h, SqU5.inv_i, SqU5.inv_j] <;> ring

end Filtration

/-! ## §2 The lift refinement and ⭐⭐ the translation identity

The four-slot refinement one level up from `GradedSelect`'s `selRefine`: dress the two
exponent slots by `γ₄`-elements and the two `j`-handle slots by `γ₃`-elements.  The relator is
translated by a central element whose value is affine-linear in the dressings

```text
Δ = −4·w₁.j + 2·w₂.j + (z₃.h·(m V).d − z₃.i·(m V).a) + ((m U).a·z₄.i − (m U).d·z₄.h),
```

the exact transposition of the committed `sqRelWord_selRefine` with `(d, e)`-parts replaced by
`(h, i)`-parts and the *inner* coefficient columns `(a, c)` replaced by the *outermost* ones
`(a, d)`.  The proof consumes no closed form of the relator: the exponent slots are handled by
`sqWord_mul_liftC`, the handle slots by the dressed-commutator lemma and a one-entry central
update of the handle product. -/

section LiftCalculus

variable {R : Type} [CommRing R] {h : ℕ} {j : Fin h}

/-- A `γ₄`-shaped element is a central translation. -/
theorem SqU5.IsGaFour.eq_liftC {z : SqU5 R} (hz : z.IsGaFour) : z = liftC z.j := by
  obtain ⟨ha, hb, hc, hd, he, hf, hg, hh, hi⟩ := hz
  ext <;> simp [liftC, ha, hb, hc, hd, he, hf, hg, hh, hi]

/-- ⭐ **Dressing both arguments of a commutator by `γ₃`-elements translates it centrally**,
by the `(h, i)`-parts paired against the other argument's outermost abelian columns.  This is
`u5Comm4`'s linearity in the class-three coordinates, packaged at the group level. -/
theorem commP_mul_gaThree {z₃ z₄ : SqU5 R} (p q : SqU5 R) (hz₃ : z₃.IsGaThree)
    (hz₄ : z₄.IsGaThree) :
    commP (p * z₃) (q * z₄)
      = commP p q * liftC ((z₃.h * q.d - z₃.i * q.a) + (p.a * z₄.i - p.d * z₄.h)) := by
  obtain ⟨h3a, h3b, h3c, h3d, h3e, h3f, h3g⟩ := hz₃
  obtain ⟨h4a, h4b, h4c, h4d, h4e, h4f, h4g⟩ := hz₄
  ext <;> simp only [SqU5.commP_a, SqU5.commP_b, SqU5.commP_c, SqU5.commP_d, SqU5.commP_e,
    SqU5.commP_f, SqU5.commP_g, SqU5.commP_h, SqU5.commP_i, SqU5.commP_j, SqU5.u5Comm3L,
    SqU5.u5Comm3R, SqU5.u5Comm4, liftC, SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d,
    SqU5.mul_e, SqU5.mul_f, SqU5.mul_g, SqU5.mul_h, SqU5.mul_i, SqU5.mul_j,
    h3a, h3b, h3c, h3d, h3e, h3f, h3g, h4a, h4b, h4c, h4d, h4e, h4f, h4g] <;> ring

/-- One entry of a product over `Fin n` picking up a central right factor passes it to the
whole product. -/
private theorem prod_map_update_center {G : Type*} [Group G] (n : ℕ) :
    ∀ (F : Fin n → G) (j : Fin n) (z : G), (∀ g : G, g * z = z * g) →
      ((List.finRange n).map fun k => if k = j then F k * z else F k).prod
        = ((List.finRange n).map F).prod * z := by
  induction n with
  | zero => exact fun F j z _ => j.elim0
  | succ n ih =>
    intro F j z hz
    rw [List.finRange_succ, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
      List.map_map, List.map_map]
    cases j using Fin.cases with
    | zero =>
      rw [if_pos rfl]
      have htail : (List.finRange n).map ((fun k => if k = 0 then F k * z else F k)
            ∘ Fin.succ) = (List.finRange n).map (F ∘ Fin.succ) := by
        refine List.map_congr_left fun k _ => ?_
        simp [Fin.succ_ne_zero]
      rw [htail, mul_assoc, ← hz ((List.finRange n).map (F ∘ Fin.succ)).prod, ← mul_assoc]
    | succ j' =>
      rw [if_neg (Fin.succ_ne_zero j').symm]
      have htail : (List.finRange n).map ((fun k => if k = Fin.succ j' then F k * z else F k)
            ∘ Fin.succ)
          = (List.finRange n).map fun k => if k = j' then (F ∘ Fin.succ) k * z
              else (F ∘ Fin.succ) k := by
        refine List.map_congr_left fun k _ => ?_
        simp only [Function.comp_apply, Fin.succ_inj]
      rw [htail, ih (F ∘ Fin.succ) j' z hz, ← mul_assoc]

/-- ⭐ **The handle block swallows one dressed handle pair centrally**: dressing the `j`-th
handle pair by `γ₃`-elements multiplies `handleWord` by the central translation of the
commutator lemma. -/
theorem handleWord_mul_gaThree {z₃ z₄ : SqU5 R} (u v : Fin h → SqU5 R) (hz₃ : z₃.IsGaThree)
    (hz₄ : z₄.IsGaThree) :
    handleWord (fun k => if k = j then u k * z₃ else u k)
        (fun k => if k = j then v k * z₄ else v k)
      = handleWord u v
        * liftC ((z₃.h * (v j).d - z₃.i * (v j).a) + ((u j).a * z₄.i - (u j).d * z₄.h)) := by
  rw [handleWord, handleWord]
  have hmap : ((List.finRange h).map fun k => commP (if k = j then u k * z₃ else u k)
        (if k = j then v k * z₄ else v k))
      = (List.finRange h).map fun k => if k = j then (fun k' => commP (u k') (v k')) k
          * liftC ((z₃.h * (v j).d - z₃.i * (v j).a) + ((u j).a * z₄.i - (u j).d * z₄.h))
          else (fun k' => commP (u k') (v k')) k := by
    refine List.map_congr_left fun k _ => ?_
    by_cases hk : k = j
    · subst hk
      rw [if_pos rfl, if_pos rfl, if_pos rfl, commP_mul_gaThree _ _ hz₃ hz₄]
    · rw [if_neg hk, if_neg hk, if_neg hk]
  rw [hmap, prod_map_update_center h _ j _ (fun g => liftC_comm g _)]

/-- **The four-slot lift refinement**: dress the two exponent slots by `w₁`, `w₂` and the two
`j`-handle slots by `z₃`, `z₄`, all on the right; leave every other slot alone.  With `w`'s in
`γ₄` and `z`'s in `γ₃` this is the action on markings of the dressings that the class-`≤ 3`
rows cannot see. -/
def selLift (j : Fin h) (m : Fin (sqRank h) → SqU5 R) (w₁ w₂ z₃ z₄ : SqU5 R) :
    Fin (sqRank h) → SqU5 R :=
  fun i =>
    if (i : ℕ) = 1 then m i * w₁ else
    if (i : ℕ) = 2 then m i * w₂ else
    if i = sqHandleIdxU j then m i * z₃ else
    if i = sqHandleIdxV j then m i * z₄ else m i

variable {m : Fin (sqRank h) → SqU5 R} {w₁ w₂ z₃ z₄ : SqU5 R}

private theorem lift_ne_handleU_of_lt {i : Fin (sqRank h)} (hi : (i : ℕ) < 3) :
    i ≠ sqHandleIdxU j := by
  intro hc
  rw [hc, sqHandleIdxU_val] at hi
  omega

private theorem lift_ne_handleV_of_lt {i : Fin (sqRank h)} (hi : (i : ℕ) < 3) :
    i ≠ sqHandleIdxV j := by
  intro hc
  rw [hc, sqHandleIdxV_val] at hi
  omega

private theorem lift_handleV_ne_handleU (j' : Fin h) : sqHandleIdxV j' ≠ sqHandleIdxU j := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [sqHandleIdxV_val, sqHandleIdxU_val] at hv
  omega

private theorem lift_handleU_ne_handleV (j' : Fin h) : sqHandleIdxU j' ≠ sqHandleIdxV j := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [sqHandleIdxU_val, sqHandleIdxV_val] at hv
  omega

@[simp] theorem selLift_zero : selLift j m w₁ w₂ z₃ z₄ 0 = m 0 := by
  simp only [selLift, sqVal_zero]
  rw [if_neg (by omega), if_neg (by omega),
    if_neg (lift_ne_handleU_of_lt (by rw [sqVal_zero]; omega)),
    if_neg (lift_ne_handleV_of_lt (by rw [sqVal_zero]; omega))]

@[simp] theorem selLift_one : selLift j m w₁ w₂ z₃ z₄ 1 = m 1 * w₁ := by
  simp only [selLift, sqVal_one]
  norm_num

@[simp] theorem selLift_two : selLift j m w₁ w₂ z₃ z₄ 2 = m 2 * w₂ := by
  simp only [selLift, sqVal_two]
  norm_num

@[simp] theorem selLift_handleU {j' : Fin h} :
    selLift j m w₁ w₂ z₃ z₄ (sqHandleIdxU j')
      = if j' = j then m (sqHandleIdxU j') * z₃ else m (sqHandleIdxU j') := by
  simp only [selLift, sqHandleIdxU_val]
  rw [if_neg (by omega), if_neg (by omega),
    if_neg (lift_handleU_ne_handleV j')]
  by_cases hj : j' = j
  · subst hj
    rw [if_pos rfl, if_pos rfl]
  · rw [if_neg hj, if_neg fun hc => hj (Fin.val_injective (by
      have hv := congrArg Fin.val hc
      rw [sqHandleIdxU_val, sqHandleIdxU_val] at hv
      omega))]

@[simp] theorem selLift_handleV {j' : Fin h} :
    selLift j m w₁ w₂ z₃ z₄ (sqHandleIdxV j')
      = if j' = j then m (sqHandleIdxV j') * z₄ else m (sqHandleIdxV j') := by
  simp only [selLift, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (lift_handleV_ne_handleU j')]
  by_cases hj : j' = j
  · subst hj
    rw [if_pos rfl, if_pos rfl]
  · rw [if_neg hj, if_neg fun hc => hj (Fin.val_injective (by
      have hv := congrArg Fin.val hc
      rw [sqHandleIdxV_val, sqHandleIdxV_val] at hv
      omega))]

/-- ⭐⭐ **The translation identity at class four** (the stage-`k` conjecture's linear layer,
instantiated at `k = 4`): the lift refinement translates the relator by a **central** element,
affine-linear in the four dressings, with the two handle moves reading the *other* handle
letter's outermost abelian columns.  Every class-`≤ 3` row is untouched.  No closed form of
the relator is consumed. -/
theorem sqRelWord_selLift (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour) (hz₃ : z₃.IsGaThree)
    (hz₄ : z₄.IsGaThree) :
    sqRelWord (selLift j m w₁ w₂ z₃ z₄)
      = sqRelWord m * liftC (-4 * w₁.j + 2 * w₂.j
          + ((z₃.h * (m (sqHandleIdxV j)).d - z₃.i * (m (sqHandleIdxV j)).a)
            + ((m (sqHandleIdxU j)).a * z₄.i - (m (sqHandleIdxU j)).d * z₄.h))) := by
  have hu : (fun j' => selLift j m w₁ w₂ z₃ z₄ (sqHandleIdxU j'))
      = fun k => if k = j then (fun j' => m (sqHandleIdxU j')) k * z₃
          else (fun j' => m (sqHandleIdxU j')) k := by
    funext k
    rw [selLift_handleU]
  have hv : (fun j' => selLift j m w₁ w₂ z₃ z₄ (sqHandleIdxV j'))
      = fun k => if k = j then (fun j' => m (sqHandleIdxV j')) k * z₄
          else (fun j' => m (sqHandleIdxV j')) k := by
    funext k
    rw [selLift_handleV]
  rw [sqRelWord, sqRelWord, selLift_zero, selLift_one, selLift_two, hu, hv,
    handleWord_mul_gaThree _ _ hz₃ hz₄, hw₁.eq_liftC, hw₂.eq_liftC,
    sqWord_mul_liftC, mul_assoc, ← mul_assoc (liftC _), ← liftC_comm, mul_assoc, ← mul_assoc,
    liftC_mul_liftC]
  simp only [liftC_j]

end LiftCalculus

end SqCore

end Dyadic

end GQ2

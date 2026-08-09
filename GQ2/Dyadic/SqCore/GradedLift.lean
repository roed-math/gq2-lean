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

@[simp] theorem SqU5.isGaFour_one : (1 : SqU5 R).IsGaFour :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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

/-! ## §3 The achievable `γ₃`-lattice and ⭐⭐ the two-regime completion

The translation identity moves the class-four residue of a stage-three survivor by
`−4·w₁.j + 2·w₂.j` (exponent slots, even outright) plus the two handle pairings
`z₃.h·(m V).d − z₃.i·(m V).a` and `(m U).a·z₄.i − (m U).d·z₄.h`.  Which `(h, i)`-pairs a
level-one dressing can actually place on a handle slot is the `γ₃`-image lattice `Λ₃`
(`selLamThree`): the commutator pairings of the `γ₂`-image lattice `Λ₅` (generated on the
`(e, f, g)`-columns by `(−A, C, 0)`, `(−B, D, 0)`, `(−2P, −2Q, −2R)`, `(0, 0, −2R)`) against
the three letter columns `σ = (0, 1, 0, 0)`, `U = (A, T, C, E)`, `V = (B, S, D, F)`, exactly
one level up from `GradedSelect.selLam` (validated in `scripts/w52_lift/sweep_u5.py`,
`lam3_gens`).

The completion has **two regimes**, separated by the mod-2 class of the pairing value — the
W51 sweep's parity collapse (`δ` and its image depend on the marking only mod 2) entering the
statements:

* **odd regime** (`sqRelWord_selLift_eq_one_odd`): a *unit* pairing witness `rr` makes the
  `γ₃`-action on the residue line surjective (`selLift_increment_exact` at `μ = 1`) and
  **any** central residue dies — something that never happens at class three, where every
  achievable increment is even (`GradedSelect.selPair_even`).  At the §4 witness the
  `(−B, D)⋆V` generator pairs to `−3·κ₄` with `κ₄ = B·D·F`, so this regime is exactly "`κ₄`
  odd";
* **even regime** (`sqRelWord_selLift_eq_one`): a `2`-pairing witness kills exactly the even
  residues (`selLift_increment_exact` at `μ = 2`), the verbatim transposition of the committed
  class-three completion (`GradedSelect.sqRelWord_selRefine_eq_one`).  The converse selection
  claim — at `κ₄`-even live points an odd residue survives every achievable refinement — is
  **measured, not proved** (`sweep4_u5.py`, `sweep5_u5.py`: zero kills across all sampled
  achievable moves); transcribing it needs the class-four analogue of `GradedSelect` §5b's
  parity engine, which no wave has consumed yet;
* **mirror regime** (`sqRelWord_selLift_eq_one_odd'`): the same completion through the
  `V`-handle slot, reading the `U`-slot's outer columns; at the witness the `(−A, C)⋆U`
  generator pairs to `3·κ₄'` with `κ₄' = A·C·E`.

`GradedVanish` (W52-VANISH) develops the same translation-calculus structure one level down:
its `vanShift` is the class-three shift of an all-slot `γ₂`-dressing, with the identical
affine-linear shape; the two files share the pattern but no lemmas. -/

section LiftCompletion

variable {R : Type} [CommRing R] {h : ℕ} {j : Fin h} {m : Fin (sqRank h) → SqU5 R}

/-- ⭐⭐ **The even-regime completion.**  A stage-three survivor with an **even** class-four
residue `2·res`, at a marking where some achievable `(zh, zi)`-pair pairs to `2·unit⁻¹`
against the `V`-slot's outermost columns (witness `rr`), is repaired by **one explicit**
handle-`γ₃` move on the `U`-slot.  The transposition of the committed
`GradedSelect.sqRelWord_selRefine_eq_one`, one level up. -/
theorem sqRelWord_selLift_eq_one {zh zi res rr : R}
    (h5 : sqRelWord m = liftC (2 * res))
    (hmu : rr * (zh * (m (sqHandleIdxV j)).d - zi * (m (sqHandleIdxV j)).a) = 2) :
    sqRelWord (selLift j m 1 1
      ⟨0, 0, 0, 0, 0, 0, 0, -(rr * res * zh), -(rr * res * zi), 0⟩ 1) = 1 := by
  rw [sqRelWord_selLift SqU5.isGaFour_one SqU5.isGaFour_one
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ SqU5.isGaThree_one, h5, liftC_mul_liftC]
  refine Eq.trans (congrArg liftC ?_) liftC_zero
  simp only [SqU5.one_h, SqU5.one_i, SqU5.one_j]
  linear_combination (-res) * hmu

/-- ⭐⭐ **The odd-regime completion**: with a **unit** pairing witness the `γ₃`-action is
surjective on the residue line and **any** central residue dies — even an odd one.  No
class-three analogue exists: there the achievable-increment group is always inside `2·ℤ/8`. -/
theorem sqRelWord_selLift_eq_one_odd {zh zi res rr : R}
    (h5 : sqRelWord m = liftC res)
    (hmu : rr * (zh * (m (sqHandleIdxV j)).d - zi * (m (sqHandleIdxV j)).a) = 1) :
    sqRelWord (selLift j m 1 1
      ⟨0, 0, 0, 0, 0, 0, 0, -(rr * res * zh), -(rr * res * zi), 0⟩ 1) = 1 := by
  rw [sqRelWord_selLift SqU5.isGaFour_one SqU5.isGaFour_one
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ SqU5.isGaThree_one, h5, liftC_mul_liftC]
  refine Eq.trans (congrArg liftC ?_) liftC_zero
  simp only [SqU5.one_h, SqU5.one_i, SqU5.one_j]
  linear_combination (-res) * hmu

/-- ⭐⭐ **The mirror odd-regime completion**: the same engine through the `V`-handle slot,
reading the `U`-slot's outermost abelian columns with the opposite orientation. -/
theorem sqRelWord_selLift_eq_one_odd' {zh zi res rr : R}
    (h5 : sqRelWord m = liftC res)
    (hmu : rr * ((m (sqHandleIdxU j)).a * zi - (m (sqHandleIdxU j)).d * zh) = 1) :
    sqRelWord (selLift j m 1 1 1
      ⟨0, 0, 0, 0, 0, 0, 0, -(rr * res * zh), -(rr * res * zi), 0⟩) = 1 := by
  rw [sqRelWord_selLift SqU5.isGaFour_one SqU5.isGaFour_one SqU5.isGaThree_one
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, h5, liftC_mul_liftC]
  refine Eq.trans (congrArg liftC ?_) liftC_zero
  simp only [SqU5.one_h, SqU5.one_i, SqU5.one_j]
  linear_combination (-res) * hmu

/-- ⭐ **The achievable increments fill `μ·R` exactly** (deliverable form of the two regimes):
a pairing witness of value `μ` realises every multiple of `μ` as the increment of a `γ₃`-move
on the `U`-handle slot.  At `μ = 1` this is the odd regime's surjectivity, at `μ = 2` the even
regime's exact image `2·ℤ/8`, the class-four form of `GradedContain.selCon_increment_exact`. -/
theorem selLift_increment_exact {zh zi rr μ : R}
    (hmu : rr * (zh * (m (sqHandleIdxV j)).d - zi * (m (sqHandleIdxV j)).a) = μ) (x : R) :
    ∃ z₃ : SqU5 R, z₃.IsGaThree ∧
      z₃.h * (m (sqHandleIdxV j)).d - z₃.i * (m (sqHandleIdxV j)).a = μ * x := by
  refine ⟨⟨0, 0, 0, 0, 0, 0, 0, rr * x * zh, rr * x * zi, 0⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  linear_combination x * hmu

end LiftCompletion

section LiftLattice

/-- **Membership in `Λ₃`**, the achievable `γ₃`-lattice of a class-four selection marking:
the `(h, i)`-coordinates of `z` are an `R`-combination of the seven commutator pairings of
the `γ₂`-image lattice `Λ₅` against the three letter columns — `(−A, C)⋆U = (−2AC, CE)`,
`(−B, D)⋆U = (−(AD + BC), DE)`, `(−A, C)⋆V = (−(AD + BC), CF)`, `(−B, D)⋆V = (−2BD, DF)`,
and the three even `x₁`-pairings `(0, 2R)`, `2·(QA − PC, RT − QE)`, `2·(QB − PD, RS − QF)`.
This is the `(h, i)`-image of `γ₃(im Φ)` for a hom of the class-four selection family, the
level-up transposition of `GradedSelect.selLam` (`scripts/w52_lift/sweep_u5.py`,
`lam3_gens`). -/
def selLamThree (A B C D E F T S P Q R : gr3R) (z : SqU5 gr3R) : Prop :=
  ∃ r₁ r₂ r₃ r₄ r₅ r₆ r₇ : gr3R,
    z.h = -(r₁ * (2 * (A * C))) - r₂ * (A * D + B * C) - r₃ * (A * D + B * C)
        - r₄ * (2 * (B * D)) + 2 * (r₆ * (Q * A - P * C)) + 2 * (r₇ * (Q * B - P * D)) ∧
    z.i = r₁ * (C * E) + r₂ * (D * E) + r₃ * (C * F) + r₄ * (D * F) + 2 * (r₅ * R)
        + 2 * (r₆ * (R * T - Q * E)) + 2 * (r₇ * (R * S - Q * F))

/-- The completion move of the two `U`-slot regimes really is achievable: its `(h, i)`-pair
lies in `Λ₃`, on the `(−B, D)⋆V` generator alone. -/
theorem selLamThree_completion_move (A B C D E F T S P Q R rr res : gr3R) :
    selLamThree A B C D E F T S P Q R
      ⟨0, 0, 0, 0, 0, 0, 0, -(rr * res * -(2 * (B * D))), -(rr * res * (D * F)), 0⟩ :=
  ⟨0, 0, 0, -(rr * res), 0, 0, 0, by ring, by ring⟩

/-- …and the mirror move likewise, on the `(−A, C)⋆U` generator alone. -/
theorem selLamThree_completion_move' (A B C D E F T S P Q R rr res : gr3R) :
    selLamThree A B C D E F T S P Q R
      ⟨0, 0, 0, 0, 0, 0, 0, -(rr * res * -(2 * (A * C))), -(rr * res * (C * E)), 0⟩ :=
  ⟨-(rr * res), 0, 0, 0, 0, 0, 0, by ring, by ring⟩

/-- Odd elements of `ℤ/8` are units: the arithmetic core of the odd regime. -/
theorem gr3R_exists_inv_of_odd : ∀ x : gr3R, selPar x = 1 → ∃ y : gr3R, y * x = 1 := by
  decide

/-- `2·odd` elements of `ℤ/8` divide `2`: the arithmetic core of the even regime. -/
theorem gr3R_exists_half_of_odd : ∀ x : gr3R, selPar x = 1 → ∃ y : gr3R, y * (2 * x) = 2 := by
  decide

end LiftLattice

/-! ## §4 ⭐⭐ The whole-binder witness at class four

The `U₅`-lift of `GradedContain.selConWit`: the same five slot values with the class-four
binder's new column `χ_d` (weights `E` on `U`, `F` on `V`, half `W2` with parity row `hb`)
and the `x₁`-slot's new class-two weight `R` (half row `hg`), all deep coordinates zero.  Its
ten relator rows, through the two `U₄`-quotients:

* rows `a, b, c, e, f` **vanish** and row `h` is the **committed class-three residue**
  `4·P·Q − 2·(A+B)·Q + B·C·(T+S)`: the left quotient of the lifted tuple *is* `selConWit`
  (`toU4L_selLiftWit`), so `GradedContain`'s whole-binder theorem answers all six rows at
  once, and the committed completion machinery of `GradedSelect` §6 governs the `h`-row;
* rows `d, g` **vanish** (`sqRelWord_selLiftWit_d`, `_g`), through the right quotient and the
  committed `SqU4` closed forms; these are the class-`≤ 2` stories of the `(c, d)`-columns;
* row `i` is **genuinely new** (`sqRelWord_selLiftWit_i`): its closed form at the witness is
  `2·N − C·F·T` with `N = 2·S·T·(C+D)·W2`, so its parity is `C·F·T` — the class-three
  selection bit of the columns class three could not see, the `(c, d)`-analogue of the
  committed `B·C·(T+S)`-bit one level down;
* row `j` is the engine's target: it is not computed in closed form here, and the stage
  hypothesis `sqRelWord = liftC res` of §3's completions is exactly "rows `h` and `i` have
  been killed too" — stage 3 is **two functionals wide** from up here, and a class-three
  survivor means both die.

`selLiftWit_complete_odd` is the stage-3 → stage-4 engine instance at the witness: at a
`κ₄ = B·D·F` odd point, **any** stage-three survivor residue is killed by one explicit
achievable `γ₃`-move, with all objects exhibited.  The concrete instances at the end run the
whole pipe by `decide` at a binder point with an **odd** surviving residue. -/

section LiftWitness

variable {h : ℕ} {j : Fin h} {A B C D E F T S P Q R W2 : gr3R}

/-- **The whole-binder witness tuple at class four**: the `U₅`-lift of
`GradedContain.selConWit` — slot `0` the marked `σ`, slot `1` the forced dressing value with
the `Λ`-correction, slot `2` the `x₁`-letter, the `j`-handle pair the `U`-, `V`-letters, all
other slots trivial, every deep (class-`≥ 3`) coordinate zero. -/
def selLiftWit (h : ℕ) (j : Fin h) (A B C D E F T S P Q R : gr3R) :
    Fin (sqRank h) → SqU5 gr3R :=
  fun i =>
    if (i : ℕ) = 0 then ⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩ else
    if (i : ℕ) = 1 then
      ⟨B * T - A * S, 0, D * T - C * S, F * T - E * S, -(2 * (T * S * B)),
        S * (T * C) + T * S * D, 0, 0, 0, 0⟩ else
    if (i : ℕ) = 2 then ⟨0, 0, 0, 0, P, Q, R, -((A + B) * Q), 0, 0⟩ else
    if i = sqHandleIdxU j then ⟨A, 0, C, E, 0, -(T * C), 0, 0, 0, 0⟩ else
    if i = sqHandleIdxV j then ⟨B, 0, D, F, -(B * S), 0, 0, 0, 0, 0⟩ else 1

private theorem lift_handleU_ne_handleU {j' : Fin h} (hne : j' ≠ j) :
    sqHandleIdxU j' ≠ sqHandleIdxU j := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [sqHandleIdxU_val, sqHandleIdxU_val] at hv
  exact hne (Fin.val_injective (by omega))

private theorem lift_handleV_ne_handleV {j' : Fin h} (hne : j' ≠ j) :
    sqHandleIdxV j' ≠ sqHandleIdxV j := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [sqHandleIdxV_val, sqHandleIdxV_val] at hv
  exact hne (Fin.val_injective (by omega))

@[simp] theorem selLiftWit_zero :
    selLiftWit h j A B C D E F T S P Q R 0 = ⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩ := by
  rw [selLiftWit, if_pos (sqVal_zero h)]

@[simp] theorem selLiftWit_one :
    selLiftWit h j A B C D E F T S P Q R 1
      = ⟨B * T - A * S, 0, D * T - C * S, F * T - E * S, -(2 * (T * S * B)),
          S * (T * C) + T * S * D, 0, 0, 0, 0⟩ := by
  rw [selLiftWit, if_neg (by rw [sqVal_one]; omega), if_pos (sqVal_one h)]

@[simp] theorem selLiftWit_two :
    selLiftWit h j A B C D E F T S P Q R 2
      = ⟨0, 0, 0, 0, P, Q, R, -((A + B) * Q), 0, 0⟩ := by
  rw [selLiftWit, if_neg (by rw [sqVal_two]; omega), if_neg (by rw [sqVal_two]; omega),
    if_pos (sqVal_two h)]

@[simp] theorem selLiftWit_handleU :
    selLiftWit h j A B C D E F T S P Q R (sqHandleIdxU j)
      = ⟨A, 0, C, E, 0, -(T * C), 0, 0, 0, 0⟩ := by
  rw [selLiftWit, if_neg (by rw [sqHandleIdxU_val]; omega),
    if_neg (by rw [sqHandleIdxU_val]; omega), if_neg (by rw [sqHandleIdxU_val]; omega),
    if_pos rfl]

@[simp] theorem selLiftWit_handleV :
    selLiftWit h j A B C D E F T S P Q R (sqHandleIdxV j)
      = ⟨B, 0, D, F, -(B * S), 0, 0, 0, 0, 0⟩ := by
  rw [selLiftWit, if_neg (by rw [sqHandleIdxV_val]; omega),
    if_neg (by rw [sqHandleIdxV_val]; omega), if_neg (by rw [sqHandleIdxV_val]; omega),
    if_neg (lift_handleV_ne_handleU j), if_pos rfl]

theorem selLiftWit_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    selLiftWit h j A B C D E F T S P Q R (sqHandleIdxU j') = 1 := by
  rw [selLiftWit, if_neg (by rw [sqHandleIdxU_val]; omega),
    if_neg (by rw [sqHandleIdxU_val]; omega), if_neg (by rw [sqHandleIdxU_val]; omega),
    if_neg (lift_handleU_ne_handleU hne), if_neg (lift_handleU_ne_handleV j')]

theorem selLiftWit_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    selLiftWit h j A B C D E F T S P Q R (sqHandleIdxV j') = 1 := by
  rw [selLiftWit, if_neg (by rw [sqHandleIdxV_val]; omega),
    if_neg (by rw [sqHandleIdxV_val]; omega), if_neg (by rw [sqHandleIdxV_val]; omega),
    if_neg (lift_handleV_ne_handleU j'), if_neg (lift_handleV_ne_handleV hne)]

/-- ⭐ **The left `U₄`-quotient of the lifted witness is the committed class-three witness**,
slot for slot: the class-`≤ 3` face of the class-four binder is `GradedContain`'s binder on
the nose, which is what hands rows `a, b, c, e, f, h` to the committed machinery. -/
theorem toU4L_selLiftWit :
    (fun i => SqU5.toU4L (selLiftWit h j A B C D E F T S P Q R i))
      = selConWit h j A B C D P Q T S := by
  funext i
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [selLiftWit_zero, selConWit_zero]; rfl
  · rw [selLiftWit_one, selConWit_one]; rfl
  · rw [selLiftWit_two, selConWit_two]; rfl
  · by_cases hj : j' = j
    · subst hj; rw [selLiftWit_handleU, selConWit_handleU]; rfl
    · rw [selLiftWit_handleU_ne hj, selConWit_handleU_ne hj]; rfl
  · by_cases hj : j' = j
    · subst hj; rw [selLiftWit_handleV, selConWit_handleV]; rfl
    · rw [selLiftWit_handleV_ne hj, selConWit_handleV_ne hj]; rfl

/-- The whole `U₄`-image of the witness relator, from the committed whole-binder theorem: the
five low rows die and the `f`-row is the committed class-three residue. -/
theorem sqRelWord_selLiftWit_toU4L (hd : 2 * P + (A * S - B * T) = 0)
    (he : 2 * Q + (T * D - S * C) = 0) :
    SqU5.toU4L (sqRelWord (selLiftWit h j A B C D E F T S P Q R))
      = ⟨0, 0, 0, 0, 0, 4 * (P * Q) - 2 * ((A + B) * Q) + B * C * (T + S)⟩ := by
  rw [map_sqRelWord, toU4L_selLiftWit, sqRelWord_selConWit hd he]

/-- ⭐ **The `h`-row of the lifted witness is the committed class-three residue**, verbatim:
even at every binder point (`GradedContain.selConWit_even`), killed on the live locus by the
committed completion move (`GradedSelect.sqRelWord_selRefine_eq_one` through `toU4L`). -/
theorem sqRelWord_selLiftWit_h (hd : 2 * P + (A * S - B * T) = 0)
    (he : 2 * Q + (T * D - S * C) = 0) :
    (sqRelWord (selLiftWit h j A B C D E F T S P Q R)).h
      = 4 * (P * Q) - 2 * ((A + B) * Q) + B * C * (T + S) := by
  have h1 := congrArg SqU4.f
    (sqRelWord_selLiftWit_toU4L (h := h) (j := j) (E := E) (F := F) (R := R) hd he)
  simpa only [SqU5.toU4L_apply] using h1

/-- The new abelian row `d` (the `χ_d`-column's `ρ_sq`-balance) dies at every binder point:
`−4·(F·T − E·S) = −8·W2 = 0`, the `hb`-parity's job. -/
theorem sqRelWord_selLiftWit_d (hb : 2 * W2 + (E * S - F * T) = 0) :
    (sqRelWord (selLiftWit h j A B C D E F T S P Q R)).d = 0 := by
  have h8 : (8 : gr3R) = 0 := by decide
  have h1 := congrArg SqU4.c
    (map_sqRelWord SqU5.toU4R (selLiftWit h j A B C D E F T S P Q R))
  simp only [SqU4.sqRelWord_c, SqU5.toU4R_apply, selLiftWit_one, selLiftWit_two] at h1
  rw [h1]
  linear_combination 4 * hb + (-W2) * h8

/-- The new class-two row `g` (the `(c, d)`-pairing) dies at every binder point, through the
right quotient and the committed `SqHeis` defect form. -/
theorem sqRelWord_selLiftWit_g (he : 2 * Q + (T * D - S * C) = 0)
    (hg : 2 * R + (C * F - D * E) = 0) (hb : 2 * W2 + (E * S - F * T) = 0) :
    (sqRelWord (selLiftWit h j A B C D E F T S P Q R)).g = 0 := by
  have h8 : (8 : gr3R) = 0 := by decide
  have h1 := congrArg SqU4.e
    (map_sqRelWord SqU5.toU4R (selLiftWit h j A B C D E F T S P Q R))
  simp only [SqU4.sqRelWord_e, sqHeisDefect] at h1
  rw [sum_eq_at _ (fun j' hne => by
    rw [selLiftWit_handleU_ne hne, selLiftWit_handleV_ne hne]; simp)] at h1
  simp only [SqU5.toU4R_apply, SqU4.toHeisBC_apply, selLiftWit_zero, selLiftWit_one,
    selLiftWit_two, selLiftWit_handleU, selLiftWit_handleV] at h1
  rw [h1]
  linear_combination (2 * (C * S - D * T)) * hb + (4 * W2) * he + hg
    + (C * E * S ^ 2 - C * F * S * T - D * E * S * T + D * F * T ^ 2 - Q * W2) * h8

/-- ⭐⭐ **The new `i`-row, in closed form**: `2·N − C·F·T` with `N = 2·S·T·(C+D)·W2`.  This is
the class-three residue of the columns class three could not see: its parity is `C·F·T`, the
`(c, d)`-column selection bit, the mirror of the committed `B·C·(T+S)`-bit of the `h`-row.  A
stage-three survivor at the witness needs *both* bits dead — stage 3 is two functionals wide
from class four. -/
theorem sqRelWord_selLiftWit_i (hb : 2 * W2 + (E * S - F * T) = 0) :
    (sqRelWord (selLiftWit h j A B C D E F T S P Q R)).i
      = 2 * (2 * (S * T * ((C + D) * W2))) - C * F * T := by
  have h8 : (8 : gr3R) = 0 := by decide
  have h1 := congrArg SqU4.f
    (map_sqRelWord SqU5.toU4R (selLiftWit h j A B C D E F T S P Q R))
  simp only [SqU4.sqRelWord_f, sqU4Defect] at h1
  rw [sum_eq_at _ (fun j' hne => by
      rw [selLiftWit_handleU_ne hne, selLiftWit_handleV_ne hne]; simp),
    sum_eq_at _ (fun j' hne => by
      rw [selLiftWit_handleU_ne hne, selLiftWit_handleV_ne hne]
      simp [SqU4.u4Comm3])] at h1
  simp only [SqU5.toU4R_apply, sqU4Core, SqU4.u4Comm3, selLiftWit_zero, selLiftWit_one,
    selLiftWit_two, selLiftWit_handleU, selLiftWit_handleV] at h1
  rw [h1]
  linear_combination (-(2 * (S * T * (C + D))) - 4 * (C * S - D * T)) * hb
    + (-(C * E * S ^ 2 * T) + C * F * S * T ^ 2 + C * S * W2 - D * E * S ^ 2 * T
        + D * F * S * T ^ 2 - D * T * W2) * h8

/-- ⭐ **The witness relator is `γ₃`-shaped at every binder point**: all seven class-`≤ 2` rows
die, with only `h`, `i`, `j` possibly alive.  The four parity rows are consumed exactly where
the numerics said they would be. -/
theorem sqRelWord_selLiftWit_isGaThree (hd : 2 * P + (A * S - B * T) = 0)
    (he : 2 * Q + (T * D - S * C) = 0) (hg : 2 * R + (C * F - D * E) = 0)
    (hb : 2 * W2 + (E * S - F * T) = 0) :
    (sqRelWord (selLiftWit h j A B C D E F T S P Q R)).IsGaThree := by
  have hL := sqRelWord_selLiftWit_toU4L (h := h) (j := j) (E := E) (F := F) (R := R) hd he
  refine ⟨?_, ?_, ?_, sqRelWord_selLiftWit_d (W2 := W2) hb, ?_, ?_,
    sqRelWord_selLiftWit_g (W2 := W2) he hg hb⟩
  · simpa only [SqU5.toU4L_apply] using congrArg SqU4.a hL
  · simpa only [SqU5.toU4L_apply] using congrArg SqU4.b hL
  · simpa only [SqU5.toU4L_apply] using congrArg SqU4.c hL
  · simpa only [SqU5.toU4L_apply] using congrArg SqU4.d hL
  · simpa only [SqU5.toU4L_apply] using congrArg SqU4.e hL

/-- ⭐⭐ **The stage-3 → stage-4 engine at the witness, odd regime**: at a `κ₄ = B·D·F` odd
binder point, any stage-three survivor residue at the lifted witness is killed by one explicit
handle-`γ₃` move, exhibited with its `Λ₃`-membership.  The stage hypothesis `h5` is the honest
"rows `h` and `i` are dead too" state that §3's completions consume; the concrete instances
below realise it by `decide`. -/
theorem selLiftWit_complete_odd (hκ : selPar (B * D * F) = 1) {res : gr3R}
    (h5 : sqRelWord (selLiftWit h j A B C D E F T S P Q R) = liftC res) :
    ∃ z₃ : SqU5 gr3R, z₃.IsGaThree ∧ selLamThree A B C D E F T S P Q R z₃ ∧
      sqRelWord (selLift j (selLiftWit h j A B C D E F T S P Q R) 1 1 z₃ 1) = 1 := by
  have h3 : selPar (-(3 * (B * D * F))) = 1 := by
    rw [selPar_neg, selPar_mul, hκ]
    decide
  obtain ⟨rr, hrr⟩ := gr3R_exists_inv_of_odd _ h3
  refine ⟨⟨0, 0, 0, 0, 0, 0, 0, -(rr * res * -(2 * (B * D))), -(rr * res * (D * F)), 0⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    selLamThree_completion_move A B C D E F T S P Q R rr res, ?_⟩
  refine sqRelWord_selLift_eq_one_odd (zh := -(2 * (B * D))) (zi := D * F) (rr := rr) h5 ?_
  rw [selLiftWit_handleV]
  linear_combination hrr

/-! ### Concrete instances

The pipe end to end at one handle, at the binder point
`(A, B, C, D, E, F, T, S) = (2, 1, 0, 1, 2, 1, 0, 1)` with halves
`(P, Q, R, W2) = (3, 0, 1, 3)` (all four parity rows check by `decide`): the lifted witness
kills all nine lower rows outright — stage 3 needs no completion move here — and survives
with the **odd** central residue `5`.  With `κ₄ = B·D·F = 1` odd, the `(−B, D)⋆V` pairing is
`−3 = 5`, its inverse is `rr = 5`, and the odd-regime move `(h, i) = (2, 7)` on the `U`-handle
slot kills the relator: a completion at odd residue, which class three can never do. -/

/-- The lifted witness is a stage-three survivor with odd central residue `5`. -/
example : sqRelWord (selLiftWit 1 0 2 1 0 1 2 1 0 1 3 0 1) = liftC (5 : gr3R) := by decide

/-- …and the explicit odd-regime `γ₃`-move kills it. -/
example : sqRelWord (selLift 0 (selLiftWit 1 0 2 1 0 1 2 1 0 1 3 0 1) 1 1
    ⟨0, 0, 0, 0, 0, 0, 0, 2, 7, 0⟩ 1) = 1 := by decide

/-- The engine instance, through the general theorem: hypotheses by `decide`, conclusion by
`selLiftWit_complete_odd`. -/
example : ∃ z₃ : SqU5 gr3R, z₃.IsGaThree ∧ selLamThree 2 1 0 1 2 1 0 1 3 0 1 z₃ ∧
    sqRelWord (selLift 0 (selLiftWit 1 0 2 1 0 1 2 1 0 1 3 0 1) 1 1 z₃ 1) = 1 :=
  selLiftWit_complete_odd (by decide) (res := 5) (by decide)

end LiftWitness

/-! ## §5 The stage schema `LiftStep` and its 3 → 4 instance

What the note's stage-`k` conjecture asks a class-`k` engine to supply, as data: a central
`R`-line in the test group, an action of dressing data on marking tuples, an increment
functional, and the translation identity binding them.  The completion is then **generic**
(`LiftStep.complete`): any stage instance kills any central residue whose negative is an
achievable increment.  This is deliberately refutation-friendly: a claimed stage-`k` engine
is exactly a term of `LiftStep`, and a failed stage is a provably empty one.  The stage-3 → 4
instance `liftStepFour` packages §1–§2; its dressing data type `LiftDress` carries the two
`γ₄` exponent dressings and the two `γ₃` handle dressings with their filtration proofs. -/

section LiftSchema

variable {R : Type} [CommRing R] {G D : Type} [Group G]

/-- **The dressing datum of the stage-3 → 4 engine**: `γ₄`-elements for the two exponent
slots, `γ₃`-elements for the two `j`-handle slots. -/
structure LiftDress (R : Type) [CommRing R] where
  /-- The `x₀`-slot dressing. -/
  w₁ : SqU5 R
  /-- The `x₁`-slot dressing. -/
  w₂ : SqU5 R
  /-- The `U`-handle-slot dressing. -/
  z₃ : SqU5 R
  /-- The `V`-handle-slot dressing. -/
  z₄ : SqU5 R
  /-- The exponent dressings are `γ₄`-shaped. -/
  hw₁ : w₁.IsGaFour
  /-- The exponent dressings are `γ₄`-shaped. -/
  hw₂ : w₂.IsGaFour
  /-- The handle dressings are `γ₃`-shaped. -/
  hz₃ : z₃.IsGaThree
  /-- The handle dressings are `γ₃`-shaped. -/
  hz₄ : z₄.IsGaThree

/-- ⭐ **The stage schema**: what a class-`k` engine instance must supply.  `cen` is the
central `R`-line of the class-`k` test group, `act` the dressing action on marking tuples,
`incr` the increment functional, and `translate` the affine translation identity.  A later
wave iterates this schema at `k = 5, 6, …`; a stage that fails is an empty type of
instances. -/
structure LiftStep (R : Type) [CommRing R] (G : Type) [Group G] (D : Type) where
  /-- The central `R`-line. -/
  cen : R → G
  /-- The line is central. -/
  cen_comm : ∀ (g : G) (w : R), g * cen w = cen w * g
  /-- The line is additive. -/
  cen_add : ∀ v w : R, cen v * cen w = cen (v + w)
  /-- The line is based. -/
  cen_zero : cen 0 = 1
  /-- The dressing action on marking tuples. -/
  act : ∀ {h : ℕ}, Fin h → (Fin (sqRank h) → G) → D → Fin (sqRank h) → G
  /-- The increment functional. -/
  incr : ∀ {h : ℕ}, Fin h → (Fin (sqRank h) → G) → D → R
  /-- ⭐ The translation identity. -/
  translate : ∀ {h : ℕ} (j : Fin h) (m : Fin (sqRank h) → G) (d : D),
    sqRelWord (act j m d) = sqRelWord m * cen (incr j m d)

/-- ⭐ **The generic stage completion**: a central residue whose negative is an achievable
increment dies.  Both regimes of §3, and every later stage's completion, factor through
this. -/
theorem LiftStep.complete (L : LiftStep R G D) {h : ℕ} (j : Fin h)
    {m : Fin (sqRank h) → G} {r : R} (d : D) (h5 : sqRelWord m = L.cen r)
    (hincr : L.incr j m d = -r) : sqRelWord (L.act j m d) = 1 := by
  rw [L.translate, h5, hincr, L.cen_add, add_neg_cancel, L.cen_zero]

/-- ⭐⭐ **The stage-3 → stage-4 engine instance**: `U₅`'s central line `liftC`, the four-slot
refinement `selLift`, the affine increment of the translation identity
`sqRelWord_selLift`. -/
def liftStepFour (R : Type) [CommRing R] : LiftStep R (SqU5 R) (LiftDress R) where
  cen := liftC
  cen_comm := liftC_comm
  cen_add := liftC_mul_liftC
  cen_zero := liftC_zero
  act j m d := selLift j m d.w₁ d.w₂ d.z₃ d.z₄
  incr j m d := -4 * d.w₁.j + 2 * d.w₂.j
    + ((d.z₃.h * (m (sqHandleIdxV j)).d - d.z₃.i * (m (sqHandleIdxV j)).a)
      + ((m (sqHandleIdxU j)).a * d.z₄.i - (m (sqHandleIdxU j)).d * d.z₄.h))
  translate _ _ d := sqRelWord_selLift d.hw₁ d.hw₂ d.hz₃ d.hz₄

end LiftSchema

/-! ## §6 Axiom pins

Committed prints for every public declaration of this file: all **std-3** (`propext`,
`Classical.choice`, `Quot.sound`) or a subset; no census axiom is reachable.  The `decide`
instances of §4 are anonymous `example`s and elaborate under the same flags. -/

section AxiomPins

#print axioms SqU5.IsGaTwo
#print axioms SqU5.IsGaThree
#print axioms SqU5.IsGaFour
#print axioms SqU5.IsGaThree.isGaTwo
#print axioms SqU5.IsGaFour.isGaThree
#print axioms SqU5.isGaThree_one
#print axioms SqU5.isGaTwo_one
#print axioms SqU5.isGaFour_one
#print axioms liftC
#print axioms liftC_mul_liftC
#print axioms liftC_inv
#print axioms liftC_comm
#print axioms mul_liftC_apply
#print axioms conjP_liftC
#print axioms commP_mul_liftC_left
#print axioms commP_mul_liftC_right
#print axioms sqWord_mul_liftC
#print axioms SqU5.IsGaFour.eq_liftC
#print axioms commP_mul_gaThree
#print axioms handleWord_mul_gaThree
#print axioms selLift
#print axioms selLift_zero
#print axioms selLift_one
#print axioms selLift_two
#print axioms selLift_handleU
#print axioms selLift_handleV
#print axioms sqRelWord_selLift
#print axioms sqRelWord_selLift_eq_one
#print axioms sqRelWord_selLift_eq_one_odd
#print axioms sqRelWord_selLift_eq_one_odd'
#print axioms selLift_increment_exact
#print axioms selLamThree
#print axioms selLamThree_completion_move
#print axioms selLamThree_completion_move'
#print axioms gr3R_exists_inv_of_odd
#print axioms gr3R_exists_half_of_odd
#print axioms selLiftWit
#print axioms toU4L_selLiftWit
#print axioms sqRelWord_selLiftWit_toU4L
#print axioms sqRelWord_selLiftWit_h
#print axioms sqRelWord_selLiftWit_d
#print axioms sqRelWord_selLiftWit_g
#print axioms sqRelWord_selLiftWit_i
#print axioms sqRelWord_selLiftWit_isGaThree
#print axioms selLiftWit_complete_odd
#print axioms LiftDress
#print axioms LiftStep
#print axioms LiftStep.complete
#print axioms liftStepFour

end AxiomPins

end SqCore

end Dyadic

end GQ2

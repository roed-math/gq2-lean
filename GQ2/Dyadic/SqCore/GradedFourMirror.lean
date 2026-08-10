/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFourRow

/-!
# W56-MIRROR: the remaining selected rows at class four, at every handle count

`GradedFourHom` (wave 54) ran the class-four sigma forcing at the **cleared** row
`nuSel 1 0 0 0`; `GradedFourRow` (wave 55) reached the **uncleared-`v`** row `nuSel 1 0 0 1`
with a new ten-row solve at a displaced binder point, and named what it did not do:

> One handle, `h = 1`, and one row: `nuSel 1 0 0 1`.  The mirror row `nuSel 1 0 1 0` is the
> same argument with the letters exchanged (`sqRelWord_e_displace` is stated generally enough to
> drive it), and the doubly-uncleared row `nuSel 1 0 1 1` is not attempted.

This file settles both remaining rows, widens wave 55's own row to arbitrary handle count, and
corrects that passage on two points of substance.

## Headline: every selected row is now covered, at every handle count

```text
row (t, s)          status before          status now
(0, 0)  cleared     GradedFourHom, h = 1   unchanged
(0, 1)  uncleared v GradedFourRow, h = 1   ⭐ every h, every handle j   (§8, rowWide…)
(1, 0)  MIRROR      not attempted          ⭐⭐ every h, every handle j (§3-§6, mirFour…)
(1, 1)  DOUBLY      not attempted          ⭐⭐ every h, every handle j (§7, dblFour…)
```

⭐⭐ `sqArbFrame_sigma_forced_mirror`, ⭐⭐ `sqArbFrame_sigma_forced_double` and ⭐⭐
`sqArbFrame_sigma_forced_row_wide` (with their `_gaTwo` companions): at **every** handle count
`h`, at **every** live handle `j`, at the honest continuous homomorphism built by the committed
lift from the row's own displaced binder point, **every `ν'`-trivial sigma dressing of the
arbitrary-dressing frame whose image is killed by any achievable five-slot class-four refinement
has an even `chi_a`-character.**  Nothing is carried beyond the dressing's own legality, and the
handle-clearing hypotheses of `GradedFourHom.sqArbFrame_sigma_forced` are gone at all three rows.

At each of the three rows the three verdicts are executed on the frame itself, with both
regression dressings exhibited as `λ`-trivial and `ν'`-trivial slotwise:

```text
a0 = 1                            relator dies outright     sqRelWord_{mir,dbl,wide}Frame_sigTriv
a0 = (cleared letter)²  (χ_a = 2) residue 2, dies to one    …_sig{U,U,V}sq[_complete]
a0 = cleared letter     (χ_a = 1) residue 1, survives none  …_sig{U,U,V}[_ne_one]
```

and `mirFrame_class_three_blind` / `dblFrame_class_three_blind` record that both `U₄`-quotients
are trivial in all three cases, so the committed class-three machinery cannot see the
separation.

## ⭐⭐ The unified row obstruction (§1), and where wave 55's guess was wrong

For **any** five-slot-plus-handles tuple over **any** commutative ring, displacing the `u`-slot
on the **left** by `P` and the `v`-slot on the **right** by `Q` moves the relator's class-two
`e`-row by exactly

```text
(P.a·V.b − P.b·V.a) + (U.a·Q.b − U.b·Q.a) + (P.a·Q.b − P.b·Q.a)     (sqRelWord_e_displace_two)
```

Two corrections to wave 55's forecast, both load-bearing:

⚠ **The sidedness matters, so `sqRelWord_e_displace` does not drive the mirror row.**  The
Eichler correction is asymmetric by construction: `sqEichV = v_j · w^{−s}` puts the pivot power
on the **right** of the `v`-letter, `sqEichU = w^{−t} · u_j` on the **left** of the `u`-letter
(the relator meets `u_j` first inside `⁅u_j, v_j⁆`).  Wave 55's identity is the `Q`-only case;
the mirror row needs the `P`-only case `sqRelWord_e_displace_left`, a different identity with a
different closed form.  The proofs mirror in one line each, but the *statement* does not
transport, and a lane that tried to reuse it verbatim would not typecheck.

⚠ **The two displacements interact.**  The third term above is not a bookkeeping artefact: it is
the alternating pairing of the two displacing elements against each other, and dropping it makes
the identity false on `336` of `400` random tuples (`scripts/w56_mirror/results/`).  It vanishes
at the doubly-uncleared row only because both displacements are by the **same** pivot image -
which is exactly why that row has a point at all.

With both cleared letters `ν'`-trivial (`U.b = V.b = 0`) and the two displacements aligned
(`P.a·Q.b = P.b·Q.a`, automatic for powers of one pivot), the `e`-row equation becomes ⭐⭐
`chiA_row_forced`:

```text
t · χ_a(V₀)  =  s · χ_a(U₀)          at the row (t, s) = (ν'(u_j), ν'(v_j)).
```

One statement, all four rows.  `(0, 0)`: no constraint.  `(0, 1)`: `χ_a(U₀) = 0`, which is wave
55's `rowFour_chiA_handleU_forced`.  `(1, 0)`: ⭐⭐ `chiA_mirror_forced`, `χ_a(V₀) = 0` - the
exact dual, the other letter.  `(1, 1)`: ⭐⭐ `chiA_double_forced`, `χ_a(U₀) = χ_a(V₀)`.

## Did the mirror mirror?  Yes - and the doubly-uncleared row did not

⭐⭐ `mirFour_letters_swapped`: `mirFourU = rowFourV` and `mirFourV = rowFourU`, on the nose.
**The mirror point is wave 55's point with the two handle letters exchanged.**  The forced
channel swaps letters, the open channel swaps letters, the lattice parameters
`(A, B, C, D, E, F, T, S)` swap from `(0, 1, 0, 0, 1, 0, 0, 1)` to `(1, 0, 0, 0, 0, 1, 1, 0)`,
and the two `x₁`-slot commutators that wave 54 needed swap roles as well
(`mirFourWit_commP_two_handleU` is `6` where wave 55's `_handleV` was, and vice versa).  The
only thing that did **not** mirror is the displacement identity's statement, above.

⚠ The doubly-uncleared row is **not** a swap of anything, and the brief's worry - "if both
channels close, the forcing has nothing to separate with" - does not happen.  §1 does not close
a channel there: it *couples* the two, and an equality is not a vanishing.  Taking both cleared
letters to be the **same** odd letter satisfies it, and then ⭐⭐ `dblFour_forcing_nonvacuous`
exhibits **two** legal odd sigma dressings instead of one.  There is no obstruction to certify.

## What is new beyond the two rows: arbitrary handle count (§2)

The whole lane runs at general `h`.  The mechanism is ⭐ `sqRelWord_mirTuple`: a tuple whose
handle pairs are all trivial except at `j` has relator `sqWord S X Y · ⁅U, V⁆` at every handle
count, by `EichRefutation.handleWord_eq_single`.  Wave 55's `decide` on the whole five-slot
tuple is replaced by a `decide` on the core word alone, and the ten-row solve, the verdicts, the
bit, the increment, the pivot anchor, the `b`-column and the frame identification all become
`h`-generic.

The economy that makes three rows affordable is §2's observation that ⭐⭐ **the forcing itself
is row-independent**: `mirWit_bit`, `mirWit_increment_even` and `mirWit_sigma_forced` are proved
once for arbitrary cleared letters `U, V`, and `mirHom_sqPivot`, `mirHom_b`,
`mirHom_sqArbFrame` once for an arbitrary test hom with the right generator values.  What the
row fixes is only (i) which marking reaches it - §1's displacement - and (ii) which channel is
open.  Each of the three rows is then about eighty lines.

## Soundness

At each new point, the same three statements wave 55 introduced, in increasing strength.

* `mirFourWit_lamThree_even` / `dblFourWit_lamThree_even`: the committed achievable lattice
  `selLamThree` at the point's parameters is even in both class-three coordinates, at every
  `(P, Q, R)`.  The wide row reuses the **committed** `rowFourWit_lamThree_even` verbatim,
  because the lattice parameters do not depend on `h`.
* `mirFourWit_lamThreePlus_even` / `dblFourWit_lamThreePlus_even`: the extended lattice of
  `GradedGammaTwo` is even too, at each point's own data `(P, Q, R) = (0, 0, 4)`, computed
  outright from the three `x₁`-slot commutators.  Wave 54's moves cannot unlock either point.
* ⭐⭐ `mirFour_commutator_le` / `dblFour_commutator_le` / `rowWide_commutator_le`: **no lattice
  model at all.**  Every slot of every marking - the trivial handle letters of the other handles
  included - lies in `GradedFourRow.rowFrameSub`, and `commP_mem_rowGaTwoSub` then forces every
  commutator of two elements of the generated subgroup into `rowGaTwoSub`.  So the whole
  commutator subgroup `γ₂(im Φ)` is even where the translation identity reads, and the
  sigma-slot dressing needs no constraint whatsoever.  `mirFourHom_mem_closure` /
  `dblFourHom_mem_closure` identify the closure with the image through `dsq_topGen`.

## PROVED versus carried versus measured

**PROVED**, with no live hypothesis: the general one-handle-live relator; the three displacement
identities and the unified obstruction (any ring, any tuple, any handle count); the ten-row
solve at both new points and at wave 55's, at every handle count, every handle and every pivot
residue; the shared bit, increment and forcing; the three homs, their pivot anchors, both
cleared-letter images each, the `b`-column identifications and the frame identifications; all
verdicts; the three soundness statements at each point; the forcings in both the lattice and the
`γ₂`-level form; and the non-vacuity at each row.

**Carried, and named**: nothing beyond legality in the headlines.  `mirWit_sigma_forced` takes
`hvb` (the dressing's `b`-column vanishes), discharged at the frame level by `mirFourHom_b` /
`dblFourHom_b` / `rowWideHom_b` from the row's own `ν'`-triviality.  The `γ₂`-level statements
carry the campaign's standing **achievability convention** (a test hom carries `γ₂` of the honest
group onto `γ₂` of its image), exactly as `GradedGammaTwo` does; the lattice-level statements
carry `selLamThree` / `selLamThreePlus` as models instead.

**Measured, not proved** (`scripts/w56_mirror/results/`): at each new point the exhaustive kill
sweep - over all `2097152` five-slot refinements built from the achievable class-three data,
**zero** kill the odd dressing and `524288` kill the even one - and the subgroup census, with
the three invariants verified elementwise at each of the eight pivot residues plus `20000`
random commutators and all generator pairs landing in the even subgroup
(`|⟨slots⟩| = 524288` at the mirror point, `65536` at the doubly-uncleared one).  Also measured:
`8` of the `64` **unrestricted** `γ₃`-moves on each handle slot kill the odd dressing, so
achievability is load-bearing here exactly as it is at the committed points.

Every explicit claim of this file is mirrored numerically one for one in
`scripts/w56_mirror/instance_mirror.py`, at `h = 1, 2, 3, 4`, every handle `j < h` and every
pivot residue, and the library is validated against the committed `GradedSigmaFour`,
`GradedFourHom` and `GradedFourRow` facts before anything new is derived.  **4242 checks, zero
mismatches.**

## What this does NOT do

* The **cleared** row `nuSel h j 0 0` is left where `GradedFourHom` put it, at `h = 1`.  Its
  point is not of this file's shape - its `x₀`-slot dressing and handle letters are the committed
  `sigFourU`, `sigFourV` with `⁅sigFourU, sigFourV⁆ = 1` - so widening it would be a fourth
  instantiation of §2, not new mathematics; it was not attempted for length.
* The residual obstruction of `GradedSigmaFour` §7 - class four identifies the depth sweep's
  `a0 = a1` with `a0 = 1` - is untouched, and still needs class five or the universal quotient.
* The handle commutator is trivial in the image at both new points (`commP_mirFour`,
  `commP_dblFour`), exactly as at both committed points; no point with a live handle block is
  produced.  At general `h` the *other* handles are trivial too, so nothing in this file exhibits
  a marking with two live handles.
* Only the `2`-adic row values `t, s ∈ {0, 1}` are covered.  A row with `ν'(u_j)` a
  non-unit-but-nonzero `2`-adic integer would displace by a higher pivot power; §1's obstruction
  is stated for arbitrary `P`, `Q` and covers it, but no point is built.

## Contents

* **1** the one-handle-live tuple `mirTuple`, its relator at every handle count, the three
  displacement identities and ⭐⭐ the unified row obstruction;
* **2** the shared machinery: the witness shape `mirWit`, its relator, ⭐⭐ its selection bit,
  ⭐⭐ its increment and forcing, and the three hom-level shape lemmas;
* **3** ⭐⭐ the mirror point and its ten-row solve at every handle count, and the verdicts;
* **4** the mirror point as a continuous homomorphism;
* **5** soundness at the mirror point, including ⭐⭐ the model-independent `γ₂`-level bound;
* **6** ⭐⭐ the sigma forcing at the mirror row and the verdicts on `sqArbFrame`;
* **7** ⭐⭐ the doubly-uncleared row, end to end, with the coupling realised;
* **8** ⭐⭐ wave 55's own row widened to every handle count;
* **9** committed axiom prints.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`; every `decide` is on `ZMod 8`, `ZMod 2` or tuples
and words over them.  All **230** committed prints are **std-3** (`propext`, `Classical.choice`,
`Quot.sound`) or a subset; no census axiom is reachable, `sqPivotExp` included.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The one-handle-live tuple, the displacement calculus, and the row obstruction -/

section Displacement

variable {R : Type} [CommRing R] {h : ℕ} {j : Fin h}

variable (R h j) in
/-- **The one-handle-live tuple**: the three core slots `σ, x₀, x₁`, the `j`-th handle pair
carrying `(U, V)`, and every other handle letter sent to `1`.  At `h = 1` this is
`GradedFourRow.rowTuple`; the extra generality is what carries the whole lane to arbitrary
handle count. -/
def mirTuple (S X Y U V : SqU5 R) : Fin (sqRank h) → SqU5 R :=
  fun i =>
    if (i : ℕ) = 0 then S else
    if (i : ℕ) = 1 then X else
    if (i : ℕ) = 2 then Y else
    if (i : ℕ) = (sqHandleIdxU j : ℕ) then U else
    if (i : ℕ) = (sqHandleIdxV j : ℕ) then V else 1

variable {S X Y U V : SqU5 R}

@[simp] theorem mirTuple_zero : mirTuple R h j S X Y U V 0 = S := by
  simp only [mirTuple, sqVal_zero]; norm_num

@[simp] theorem mirTuple_one : mirTuple R h j S X Y U V 1 = X := by
  simp only [mirTuple, sqVal_one, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega)]
  norm_num

@[simp] theorem mirTuple_two : mirTuple R h j S X Y U V 2 = Y := by
  simp only [mirTuple, sqVal_two, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega)]
  norm_num

@[simp] theorem mirTuple_handleU : mirTuple R h j S X Y U V (sqHandleIdxU j) = U := by
  simp only [mirTuple]
  rw [if_neg (by rw [sqHandleIdxU_val]; omega), if_neg (by rw [sqHandleIdxU_val]; omega),
    if_neg (by rw [sqHandleIdxU_val]; omega)]
  simp

@[simp] theorem mirTuple_handleV : mirTuple R h j S X Y U V (sqHandleIdxV j) = V := by
  simp only [mirTuple]
  rw [if_neg (by rw [sqHandleIdxV_val]; omega), if_neg (by rw [sqHandleIdxV_val]; omega),
    if_neg (by rw [sqHandleIdxV_val]; omega),
    if_neg (by rw [sqHandleIdxU_val, sqHandleIdxV_val]; omega)]
  simp

theorem mirTuple_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    mirTuple R h j S X Y U V (sqHandleIdxU j') = 1 := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [mirTuple, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

theorem mirTuple_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    mirTuple R h j S X Y U V (sqHandleIdxV j') = 1 := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [mirTuple, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

/-- **The relator of a one-handle-live tuple**, at every handle count: the core word times the
single surviving commutator.  Every other handle block is `⁅1, 1⁆`, so `handleWord_eq_single`
collapses the product. -/
theorem sqRelWord_mirTuple :
    sqRelWord (mirTuple R h j S X Y U V) = sqWord S X Y * commP U V := by
  rw [sqRelWord, mirTuple_zero, mirTuple_one, mirTuple_two,
    handleWord_eq_single _ _ j (fun j' hj' => by
      rw [mirTuple_handleU_ne hj', mirTuple_handleV_ne hj']
      simp [commP]),
    mirTuple_handleU, mirTuple_handleV]

/-- The `e`-row of the one-handle-live relator: the core word's own, plus the alternating
pairing of the handle letters' `(a, b)`-columns. -/
theorem sqRelWord_mirTuple_e :
    (sqRelWord (mirTuple R h j S X Y U V)).e = (sqWord S X Y).e + (U.a * V.b - U.b * V.a) := by
  rw [sqRelWord_mirTuple]
  simp only [SqU5.mul_e, SqU5.commP_e, SqU5.commP_b]
  ring

/-- ⭐⭐ **The two-sided displacement identity.**  Displacing the `u`-slot on the **left** by
`P` and the `v`-slot on the **right** by `Q` moves the relator's class-two `e`-row by

```text
(P.a·V.b − P.b·V.a) + (U.a·Q.b − U.b·Q.a) + (P.a·Q.b − P.b·Q.a) .
```

The first two terms are the two one-sided displacements; ⚠ the third is their **interaction**,
the alternating pairing of the two displacing elements against each other.  The two
displacements do **not** simply add, and this is exactly the term the doubly-uncleared row has
to dispose of: it vanishes there because both displacements are by the *same* pivot image.

The sidedness is forced by the Eichler correction and is not a convention: `sqEichV` writes the
pivot power on the right of the `v`-letter, `sqEichU` on the **left** of the `u`-letter (the
relator meets `u_j` first inside `⁅u_j, v_j⁆`).  So `GradedFourRow.sqRelWord_e_displace`, which
is the `Q`-only case, does not drive the mirror row: the mirror row needs the `P`-only case,
which is a different identity with a different closed form. -/
theorem sqRelWord_e_displace_two (P Q : SqU5 R) :
    (sqRelWord (mirTuple R h j S X Y (P * U) (V * Q))).e
      = (sqRelWord (mirTuple R h j S X Y U V)).e
        + ((P.a * V.b - P.b * V.a) + (U.a * Q.b - U.b * Q.a) + (P.a * Q.b - P.b * Q.a)) := by
  rw [sqRelWord_mirTuple_e, sqRelWord_mirTuple_e]
  simp only [SqU5.mul_a, SqU5.mul_b]
  ring

/-- ⭐ **The left displacement identity**, the mirror row's own: displacing the `u`-slot on the
left by `P` moves the `e`-row by `P.a·V.b − P.b·V.a`.  This is the exact dual of
`GradedFourRow.sqRelWord_e_displace`, on the other letter and the other side. -/
theorem sqRelWord_e_displace_left (P : SqU5 R) :
    (sqRelWord (mirTuple R h j S X Y (P * U) V)).e
      = (sqRelWord (mirTuple R h j S X Y U V)).e + (P.a * V.b - P.b * V.a) := by
  have h1 := sqRelWord_e_displace_two (R := R) (h := h) (j := j) (S := S) (X := X) (Y := Y)
    (U := U) (V := V) P 1
  rw [mul_one] at h1
  rw [h1]
  simp only [SqU5.one_a, SqU5.one_b]
  ring

/-- ⭐ **The right displacement identity**, wave 55's, restated at every handle count. -/
theorem sqRelWord_e_displace_right (Q : SqU5 R) :
    (sqRelWord (mirTuple R h j S X Y U (V * Q))).e
      = (sqRelWord (mirTuple R h j S X Y U V)).e + (U.a * Q.b - U.b * Q.a) := by
  have h1 := sqRelWord_e_displace_two (R := R) (h := h) (j := j) (S := S) (X := X) (Y := Y)
    (U := U) (V := V) 1 Q
  rw [one_mul] at h1
  rw [h1]
  simp only [SqU5.one_a, SqU5.one_b]
  ring

/-- ⭐⭐ **THE ROW OBSTRUCTION, unified over all four selected rows.**  A class-four witness at
a selected row has to meet **two** standards: the marking kills the relator (else there is no
hom) and the cleared frame kills it (else the frame is not even a stage-two survivor).  With
both cleared handle letters `ν'`-trivial (`U.b = V.b = 0`) and the two displacements aligned
(`P.a·Q.b = P.b·Q.a`, automatic when both are powers of the pivot), the `e`-row equation reads

```text
P.b · χ_a(V)  =  Q.b · χ_a(U) ,   i.e.   t · χ_a(V₀) = s · χ_a(U₀)
```

since `P = Φ(w)^t`, `Q = Φ(w)^s` and `ν'(w) = 1`.  All four rows are corollaries:

```text
(t, s) = (0, 0)   cleared row          no constraint          GradedSigmaFour / GradedFourHom
(t, s) = (0, 1)   uncleared v-row      χ_a(U₀) = 0            GradedFourRow      (wave 55)
(t, s) = (1, 0)   MIRROR row           χ_a(V₀) = 0            this file, §2-§7
(t, s) = (1, 1)   DOUBLY uncleared     χ_a(U₀) = χ_a(V₀)      this file, §8
```

⚠ The doubly-uncleared row does **not** close a channel: it *couples* the two.  That is the
one place where the picture is genuinely new rather than mirrored. -/
theorem chiA_row_forced {P Q : SqU5 R} (hUb : U.b = 0) (hVb : V.b = 0)
    (halign : P.a * Q.b = P.b * Q.a)
    (hmark : sqRelWord (mirTuple R h j S X Y (P * U) (V * Q)) = 1)
    (hframe : sqRelWord (mirTuple R h j S X Y U V) = 1) :
    P.b * V.a = Q.b * U.a := by
  have hd := sqRelWord_e_displace_two (R := R) (h := h) (j := j) (S := S) (X := X) (Y := Y)
    (U := U) (V := V) P Q
  rw [hmark, hframe, hUb, hVb, SqU5.one_e] at hd
  linear_combination hd + halign

/-- ⭐⭐ **The mirror row's obstruction**: at `ν'(u₀) = 1`, `ν'(v₀) = 0` the **`v`-letter's**
`χ_a`-character is forced to vanish.  The exact dual of `GradedFourRow`'s
`rowFour_chiA_handleU_forced`; the odd channel that opens instead is the cleared `u`-letter. -/
theorem chiA_mirror_forced {P : SqU5 R} (hPb : P.b = 1) (hUb : U.b = 0) (hVb : V.b = 0)
    (hmark : sqRelWord (mirTuple R h j S X Y (P * U) V) = 1)
    (hframe : sqRelWord (mirTuple R h j S X Y U V) = 1) : V.a = 0 := by
  have hc := chiA_row_forced (P := P) (Q := 1) hUb hVb
    (by simp only [SqU5.one_a, SqU5.one_b]; ring) (by rwa [mul_one]) hframe
  rw [hPb, one_mul, SqU5.one_b, zero_mul] at hc
  exact hc

/-- ⭐⭐ **The doubly-uncleared row's obstruction**: at `ν'(u₀) = ν'(v₀) = 1` the two cleared
letters' `χ_a`-characters are forced **equal**.  Neither channel is closed; they are coupled,
and a point with an odd channel exists precisely because the coupling is an equality rather
than a vanishing. -/
theorem chiA_double_forced {P : SqU5 R} (hPb : P.b = 1) (hUb : U.b = 0) (hVb : V.b = 0)
    (hmark : sqRelWord (mirTuple R h j S X Y (P * U) (V * P)) = 1)
    (hframe : sqRelWord (mirTuple R h j S X Y U V) = 1) : V.a = U.a := by
  have hc := chiA_row_forced (P := P) (Q := P) hUb hVb (by ring) hmark hframe
  rwa [hPb, one_mul, one_mul] at hc

end Displacement

/-! ## 2 The shared machinery: the witness shape, its bit, its soundness and its forcing

Both new rows use the **same** witness shape - the committed sigma-, `x₀`- and `x₁`-slots, one
live handle pair, every other handle letter trivial - and the selection bit, the increment and
the forcing depend only on that shape, not on the row.  They are proved once here, for
arbitrary cleared handle letters `U, V` at arbitrary handle count.

That is the structural content of "the mirror mirrors": **the forcing is row-independent**.
What the row fixes is (i) which marking reaches it, through the displacement of §1, and
(ii) which channel is left open for a legal dressing to be odd on. -/

section Shared

variable {h : ℕ} {j : Fin h}

variable (h j) in
/-- **The witness shape**: the committed sigma-, `x₀`- and `x₁`-slots, the `j`-th handle pair
carrying `(U, V)`, every other handle letter trivial, and the sigma slot dressed by `v`.

Used twice: with `(U, V)` the two **cleared** letters and `v` the sigma dressing it is the frame
image; with `(U, V)` the two **displaced** letters (the raw generator images) and `v = 1` it is
the marking. -/
def mirWit (U V v : SqU5 gr3R) : Fin (sqRank h) → SqU5 gr3R :=
  mirTuple gr3R h j (sigFourMark gr3R * v) sigFourX sigFourY U V

variable {U V v : SqU5 gr3R}

@[simp] theorem mirWit_zero : mirWit h j U V v 0 = sigFourMark gr3R * v := mirTuple_zero

@[simp] theorem mirWit_one : mirWit h j U V v 1 = sigFourX := mirTuple_one

@[simp] theorem mirWit_two : mirWit h j U V v 2 = sigFourY := mirTuple_two

@[simp] theorem mirWit_handleU : mirWit h j U V v (sqHandleIdxU j) = U := mirTuple_handleU

@[simp] theorem mirWit_handleV : mirWit h j U V v (sqHandleIdxV j) = V := mirTuple_handleV

theorem mirWit_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    mirWit h j U V v (sqHandleIdxU j') = 1 := mirTuple_handleU_ne hne

theorem mirWit_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    mirWit h j U V v (sqHandleIdxV j') = 1 := mirTuple_handleV_ne hne

/-- The dressed witness really is the sigma-dressing of the undressed one, so
`GradedSigmaFour`'s general reading applies to it verbatim. -/
theorem mirWit_eq_dress : mirWit h j U V v = sigFourDress (mirWit h j U V 1) v := by
  funext i
  by_cases h0 : (i : ℕ) = 0
  · have hi : i = 0 := Fin.val_injective (by rw [h0, sqVal_zero])
    subst hi
    rw [sigFourDress_zero, mirWit_zero, mirWit_zero, mul_one]
  · rw [sigFourDress_ne h0]
    simp only [mirWit, mirTuple, if_neg h0]

/-- ⭐ **The relator at the witness shape**, whenever the live handle block is trivial: the
core word alone, at **every** handle count.  This is the one place the general-`h` extension
costs anything, and `handleWord_eq_single` pays it. -/
theorem sqRelWord_mirWit (hUV : commP U V = 1) :
    sqRelWord (mirWit h j U V v) = sqWord (sigFourMark gr3R * v) sigFourX sigFourY := by
  rw [mirWit, sqRelWord_mirTuple, hUV, mul_one]

/-- …and at the trivial dressing it vanishes: the core word of the committed slots is `1`. -/
theorem sqRelWord_mirWit_triv (hUV : commP U V = 1) :
    sqRelWord (mirWit h j U V 1) = 1 := by
  rw [sqRelWord_mirWit hUV]
  decide

/-- ⭐⭐ **The class-four selection bit at the witness shape is the sigma dressing's
`chi_a`-character, mod 2** - the same functional as at every committed point, because the
`x₀`- and `x₁`-slots are the committed ones and the gauge is untouched.  It knows nothing about
the row or about the handle letters. -/
theorem mirWit_bit (hUV : commP U V = 1) (hvb : v.b = 0) :
    selPar ((sqRelWord (mirWit h j U V v)).j) = selPar v.a := by
  have hm0 : mirWit h j U V (1 : SqU5 gr3R) 0 = sigFourMark gr3R := by
    rw [mirWit_zero, mul_one]
  have hxb : (mirWit h j U V (1 : SqU5 gr3R) 1).b = 0 := by rw [mirWit_one]; decide
  have hyb : (mirWit h j U V (1 : SqU5 gr3R) 2).b = 0 := by rw [mirWit_two]; decide
  obtain ⟨-, -, -, hjj⟩ :=
    sqRelWord_sigFourDress (m := mirWit h j U V 1) (v := v) hm0 hxb hyb hvb
  rw [mirWit_eq_dress, hjj, sqRelWord_mirWit_triv hUV, mirWit_one, mirWit_two,
    SqU5.one_j, zero_add,
    sigFourRead_gauge_par (v := v) (x := sigFourX) (y := sigFourY) (xa := 1) (xc := 0)
      (xd := 0) (xe := 0) (xf := 0) (ya := 0) (yc := 0) (yd := 0)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide),
    show (sigFourX.g + sigFourX.i : gr3R) = 1 by decide,
    show (sigFourX.h : gr3R) = 0 by decide, show (sigFourX.g : gr3R) = 0 by decide,
    mul_one, mul_zero, mul_zero, selPar_zero, add_zero, add_zero]

/-- ⭐⭐ **The five-slot increment at the witness shape is even** as soon as both handle
dressings are even in both class-three coordinates.  The sigma-slot dressing is
**unconstrained**: its increment reads the committed `x₀`-slot's columns `(a, d) = (2, 0)` and
is even outright.  No hypothesis on `U`, `V` or the row. -/
theorem mirWit_increment_even {z₀ z₃ z₄ w₁ w₂ : SqU5 gr3R}
    (h₃ : (∃ a : gr3R, z₃.h = 2 * a) ∧ (∃ b : gr3R, z₃.i = 2 * b))
    (h₄ : (∃ a : gr3R, z₄.h = 2 * a) ∧ (∃ b : gr3R, z₄.i = 2 * b)) :
    ∃ k : gr3R, (z₀.h * (mirWit h j U V v 1).d - z₀.i * (mirWit h j U V v 1).a)
        + (-4 * w₁.j + 2 * w₂.j)
        + ((z₃.h * (mirWit h j U V v (sqHandleIdxV j)).d
            - z₃.i * (mirWit h j U V v (sqHandleIdxV j)).a)
          + ((mirWit h j U V v (sqHandleIdxU j)).a * z₄.i
            - (mirWit h j U V v (sqHandleIdxU j)).d * z₄.h)) = 2 * k := by
  obtain ⟨⟨a₃, ha₃⟩, b₃, hb₃⟩ := h₃
  obtain ⟨⟨a₄, ha₄⟩, b₄, hb₄⟩ := h₄
  refine ⟨-z₀.i - 2 * w₁.j + w₂.j + (a₃ * V.d - b₃ * V.a) + (U.a * b₄ - U.d * a₄), ?_⟩
  rw [mirWit_one, mirWit_handleU, mirWit_handleV, ha₃, hb₃, ha₄, hb₄]
  simp only [sigFourX]
  ring

/-- ⭐⭐ **The sigma forcing at the witness shape**: a sigma dressing whose frame is killed by a
five-slot class-four refinement whose two handle moves are even in both class-three coordinates
has an **even** `chi_a`-character.  Row-independent, letter-independent, handle-count
independent. -/
theorem mirWit_sigma_forced {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} (hUV : commP U V = 1) (hvb : v.b = 0)
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (h₃ : (∃ a : gr3R, z₃.h = 2 * a) ∧ (∃ b : gr3R, z₃.i = 2 * b))
    (h₄ : (∃ a : gr3R, z₄.h = 2 * a) ∧ (∃ b : gr3R, z₄.i = 2 * b))
    (hkill : sqRelWord (sigLift j (mirWit h j U V v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 := by
  rw [sqRelWord_sigLift hz₀ hw₁ hw₂ hz₃ hz₄] at hkill
  obtain ⟨k, hk⟩ := mirWit_increment_even (U := U) (V := V) (v := v) (z₀ := z₀) (w₁ := w₁)
    (w₂ := w₂) h₃ h₄
  rw [hk, mul_liftC_apply] at hkill
  have hjj := congrArg SqU5.j hkill
  simp only [SqU5.one_j] at hjj
  have hp := congrArg selPar hjj
  rw [selPar_add, selPar_two_mul, add_zero, mirWit_bit hUV hvb, selPar_zero] at hp
  exact hp

/-! ### The hom-level shape lemmas

The pivot anchor, the `b`-column identification and the frame identification depend only on the
five generator values of the test hom, so they too are proved once, for an arbitrary continuous
homomorphism with the right generator values, at arbitrary handle count and arbitrary row. -/

/-- ⭐ **The pivot anchor**, for any test hom with the committed sigma- and `x₀`-slot values:
the even-obstruction power lemma applies verbatim and the pivot image is
`GradedFourRow.rowPivotVal`. -/
theorem mirHom_sqPivot {Φ : ContinuousMonoidHom (DSq h : Type) (SqU5 gr3R)}
    (h0 : Φ (dsqSigma h) = sigFourMark gr3R) (h1 : Φ (dsqX0 h) = sigFourX) :
    Φ (sqPivot h) = rowPivotVal (gr3Pi sqPivotExp) := by
  rw [sqPivot, sqMixPivotElem, map_mul, map_inv,
    map_zpowZtwo (isProP_DSq h) isProP_two_gr5, h1, sigFourX_zpowZtwo, h0]
  ext <;> simp [sigFourMark, rowPivotVal]
  ring

/-- The selected row is trivial on every handle letter other than its own. -/
theorem nuSel_handleU_ne {t s : ℤ_[2]} {j' : Fin h} (hne : j' ≠ j) :
    nuSel h j t s (sqGen h (sqHandleIdxU j')) = 1 := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  rw [nuSel, sqLiftHom_gen]
  simp only [sqSelMark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem nuSel_handleV_ne {t s : ℤ_[2]} {j' : Fin h} (hne : j' ≠ j) :
    nuSel h j t s (sqGen h (sqHandleIdxV j')) = 1 := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  rw [nuSel, sqLiftHom_gen]
  simp only [sqSelMark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- ⭐ **The `b`-column of a test hom of this shape is the selected row**, reduced mod `8`, at
every handle count and every row `(t, s)`.  Two continuous homs agreeing on the `3 + 2h`
generators.  This is what turns the `b`-column hypothesis of the forcing from a carried side
condition into a consequence of the dressing's own legality. -/
theorem mirHom_b {Φ : ContinuousMonoidHom (DSq h : Type) (SqU5 gr3R)} {t s : ℤ_[2]}
    (h0 : (Φ (dsqSigma h)).b = 1) (h1 : (Φ (dsqX0 h)).b = 0) (h2 : (Φ (dsqX1 h)).b = 0)
    (hU : (Φ (sqGen h (sqHandleIdxU j))).b = gr3Pi t)
    (hV : (Φ (sqGen h (sqHandleIdxV j))).b = gr3Pi s)
    (hne : ∀ j' : Fin h, j' ≠ j → (Φ (sqGen h (sqHandleIdxU j'))).b = 0 ∧
      (Φ (sqGen h (sqHandleIdxV j'))).b = 0) (x : (DSq h : Type)) :
    (Φ x).b = gr3Pi (toAdd (nuSel h j t s x)) := by
  have hext : bProjC.comp Φ = nuBC.comp (nuSel h j t s) := by
    refine dsq_hom_ext _ _ fun i => ?_
    rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
    · show bProjC (Φ (dsqSigma h)) = nuBC (nuSel h j t s (dsqSigma h))
      rw [nuSel_sigma, bProjC_apply, nuBC_apply, toAdd_ofAdd, map_one, h0]
    · show bProjC (Φ (dsqX0 h)) = nuBC (nuSel h j t s (dsqX0 h))
      rw [nuSel_x0, bProjC_apply, nuBC_apply, toAdd_ofAdd, map_zero, h1]
    · show bProjC (Φ (dsqX1 h)) = nuBC (nuSel h j t s (dsqX1 h))
      rw [nuSel_x1, bProjC_apply, nuBC_apply, toAdd_one, map_zero, h2]
    · by_cases hjj : j' = j
      · subst hjj
        show bProjC (Φ (sqGen h (sqHandleIdxU j'))) = nuBC (nuSel h j' t s
          (sqGen h (sqHandleIdxU j')))
        rw [nuSel_handleU, bProjC_apply, nuBC_apply, toAdd_ofAdd, hU]
      · show bProjC (Φ (sqGen h (sqHandleIdxU j'))) = nuBC (nuSel h j t s
          (sqGen h (sqHandleIdxU j')))
        rw [nuSel_handleU_ne hjj, bProjC_apply, nuBC_apply, toAdd_one, map_zero, (hne j' hjj).1]
    · by_cases hjj : j' = j
      · subst hjj
        show bProjC (Φ (sqGen h (sqHandleIdxV j'))) = nuBC (nuSel h j' t s
          (sqGen h (sqHandleIdxV j')))
        rw [nuSel_handleV, bProjC_apply, nuBC_apply, toAdd_ofAdd, hV]
      · show bProjC (Φ (sqGen h (sqHandleIdxV j'))) = nuBC (nuSel h j t s
          (sqGen h (sqHandleIdxV j')))
        rw [nuSel_handleV_ne hjj, bProjC_apply, nuBC_apply, toAdd_one, map_zero, (hne j' hjj).2]
  exact congrArg SqU5.b (DFunLike.congr_fun hext x)

/-- ⭐⭐ **The frame identification**, for any test hom whose two Eichler-cleared handle letters
have the prescribed images: the arbitrary-dressing frame with a sigma-only dressing `g` goes to
exactly the witness shape at the dressing value.  Row-independent and handle-count independent:
the pivot power the row puts in the handle slot is absorbed by the marking, so it never appears
here. -/
theorem mirHom_sqArbFrame {Φ : ContinuousMonoidHom (DSq h : Type) (SqU5 gr3R)}
    {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}
    (h0 : Φ (dsqSigma h) = sigFourMark gr3R) (h1 : Φ (dsqX0 h) = sigFourX)
    (h2 : Φ (dsqX1 h) = sigFourY) (hEU : Φ (sqEichU h nu' j) = U) (hEV : Φ (sqEichV h nu' j) = V)
    (hne : ∀ j' : Fin h, j' ≠ j → Φ (sqGen h (sqHandleIdxU j')) = 1 ∧
      Φ (sqGen h (sqHandleIdxV j')) = 1) (g : (DSq h : Type)) :
    (fun i => Φ (sqArbFrame h nu' j (sigArbDress h g) i)) = mirWit h j U V (Φ g) := by
  funext i
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [sqArbFrame, sqArbBase_zero, sigArbDress_zero, map_mul, h0, mirWit_zero]
  · rw [sqArbFrame, sqArbBase_one, sigArbDress_ne (by rw [sqVal_one]; omega), mul_one, h1,
      mirWit_one]
  · rw [sqArbFrame, sqArbBase_two, sigArbDress_ne (by rw [sqVal_two]; omega), mul_one, h2,
      mirWit_two]
  · by_cases hjj : j' = j
    · subst hjj
      rw [sqArbFrame, sqArbBase_handleU, sigArbDress_ne (by rw [sqHandleIdxU_val]; omega),
        mul_one, hEU, mirWit_handleU]
    · rw [sqArbFrame, sqArbBase_handleU_ne hjj,
        sigArbDress_ne (by rw [sqHandleIdxU_val]; omega), mul_one, (hne j' hjj).1,
        mirWit_handleU_ne hjj]
  · by_cases hjj : j' = j
    · subst hjj
      rw [sqArbFrame, sqArbBase_handleV, sigArbDress_ne (by rw [sqHandleIdxV_val]; omega),
        mul_one, hEV, mirWit_handleV]
    · rw [sqArbFrame, sqArbBase_handleV_ne hjj,
        sigArbDress_ne (by rw [sqHandleIdxV_val]; omega), mul_one, (hne j' hjj).2,
        mirWit_handleV_ne hjj]

end Shared

/-! ## 3 The mirror point `nuSel h j 1 0`: the ten-row solve at every handle count -/

section MirrorPoint

variable {h : ℕ} {j : Fin h}

/-- **The cleared `u`-letter of the mirror point**: `chi_a = 1`, everything deeper zero.  This
is the odd channel the forcing reads, and it is `GradedFourRow.rowFourV` on the **other** handle
slot - the role swap the row type forces. -/
def mirFourU : SqU5 gr3R := ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- **The `v`-letter of the mirror point**: `chi_a = 0` - forced by `chiA_mirror_forced` - and
`chi_d = 1`.  This is `GradedFourRow.rowFourU`. -/
def mirFourV : SqU5 gr3R := ⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩

/-- ⭐⭐ **The mirror point IS wave 55's point with the two handle letters exchanged**, on the
nose: the same two values, swapped between the `u`- and `v`-slots.  This is the sharpest form of
"the mirror mirrors". -/
theorem mirFour_letters_swapped : mirFourU = rowFourV ∧ mirFourV = rowFourU := ⟨rfl, rfl⟩

/-- **The `u`-slot of the marking**: the cleared letter displaced by the pivot **on the left**,
`Φ(u_j) = Φ(w) · U₀`.  The sidedness is `sqEichU`'s, not a choice. -/
def mirFourUGen (c : gr3R) : SqU5 gr3R := ⟨1 - 2 * c, 1, 0, 0, 0, 0, 0, 0, -c, c * c + c⟩

/-- …and it really is the left displacement. -/
theorem mirFourUGen_eq (c : gr3R) : mirFourUGen c = rowPivotVal c * mirFourU := by
  ext <;> simp only [mirFourUGen, mirFourU, rowPivotVal, SqU5.mul_a, SqU5.mul_b, SqU5.mul_c,
    SqU5.mul_d, SqU5.mul_e, SqU5.mul_f, SqU5.mul_g, SqU5.mul_h, SqU5.mul_i, SqU5.mul_j] <;> ring

/-- …and the cleared letter is recovered from it, by an inverse pivot **on the left**. -/
theorem mirFourU_eq (c : gr3R) : (rowPivotVal c)⁻¹ * mirFourUGen c = mirFourU := by
  rw [mirFourUGen_eq, inv_mul_cancel_left]

/-- The live handle block of the marking is trivial, at every pivot residue. -/
theorem commP_mirFourUGen : ∀ c : gr3R, commP (mirFourUGen c) mirFourV = 1 := by decide

/-- …and so is the cleared frame's. -/
theorem commP_mirFour : commP mirFourU mirFourV = 1 := by decide

variable (h j) in
/-- **The marking of the mirror point**: committed sigma-, `x₀`- and `x₁`-slots, the `j`-th
handle pair carrying the left-displaced `u`-letter and the `chi_a`-trivial `v`-letter, every
other handle letter trivial. -/
def mirFourMark (c : gr3R) : Fin (sqRank h) → SqU5 gr3R :=
  mirWit h j (mirFourUGen c) mirFourV 1

/-- ⭐⭐ **The ten-row solve at the mirror point**, at **every** handle count `h`, **every**
handle `j` and **every** residue `c` of the pivot exponent.  Wave 55 did the `h = 1` case of the
other row by `decide` on the whole five-slot tuple; here the general-`h` collapse of the handle
block does the work and the residual `decide` is on the core word alone. -/
theorem sqRelWord_mirFourMark : ∀ c : gr3R, sqRelWord (mirFourMark h j c) = 1 :=
  fun c => sqRelWord_mirWit_triv (commP_mirFourUGen c)

variable (h j) in
/-- The mirror witness at sigma-dressing value `v`: the same tuple with the `u`-slot replaced
by the **cleared** letter.  This is what the Eichler-corrected frame maps to. -/
def mirFourWit (v : SqU5 gr3R) : Fin (sqRank h) → SqU5 gr3R := mirWit h j mirFourU mirFourV v

/-- …and the cleared frame kills the relator too, so both standards of §1 are met on the nose
and the `chi_a`-obstruction is discharged. -/
theorem sqRelWord_mirFourWit_triv : sqRelWord (mirFourWit h j 1) = 1 := by
  rw [mirFourWit, sqRelWord_mirWit_triv commP_mirFour]

/-- The forced vanishing of the `v`-letter's `chi_a`, exhibited at the point. -/
theorem mirFourV_chiA : mirFourV.a = 0 := rfl

/-- …and the cleared `u`-letter's `chi_a` is **odd**: this is the channel the forcing reads. -/
theorem mirFourU_chiA : selPar mirFourU.a = 1 := by decide

/-- The square of the cleared `u`-letter is the committed lane's `V`-letter value. -/
theorem mirFourU_sq : mirFourU * mirFourU = sigFourV := by decide

/-! ### The three verdicts at the mirror point -/

/-- The relator at the mirror witness is the core word alone, at every handle count. -/
theorem sqRelWord_mirFourWit (v : SqU5 gr3R) :
    sqRelWord (mirFourWit h j v) = sqWord (sigFourMark gr3R * v) sigFourX sigFourY := by
  rw [mirFourWit, sqRelWord_mirWit commP_mirFour]

/-- ⭐⭐ **The cleared-`u` dressing leaves the odd residue `1`**: the class-four slice separates
two legal sigma dressings of the same frame at the **mirror** row. -/
theorem sqRelWord_mirFourWit_U : sqRelWord (mirFourWit h j mirFourU) = liftC 1 := by
  rw [sqRelWord_mirFourWit]; decide

/-- ⭐ **The squared cleared-`u` dressing leaves the even residue `2`.** -/
theorem sqRelWord_mirFourWit_Usq :
    sqRelWord (mirFourWit h j (mirFourU * mirFourU)) = liftC 2 := by
  rw [sqRelWord_mirFourWit]; decide

/-- The `v`-letter dressing leaves no residue at all - it is `chi_a`-trivial by
`chiA_mirror_forced`, and the reading sees nothing else. -/
theorem sqRelWord_mirFourWit_V : sqRelWord (mirFourWit h j mirFourV) = 1 := by
  rw [sqRelWord_mirFourWit]; decide

/-- The even residue dies by one explicit achievable `γ₄`-move on the `x₁` slot, exactly as at
the committed cleared-row point. -/
theorem sqRelWord_mirFourWit_Usq_complete :
    sqRelWord (sigLift j (mirFourWit h j (mirFourU * mirFourU)) 1 1 (liftC 7) 1 1)
      = 1 := by
  rw [sqRelWord_sigLift SqU5.isGaThree_one SqU5.isGaFour_one (liftC_isGaFour 7)
    SqU5.isGaThree_one SqU5.isGaThree_one, sqRelWord_mirFourWit_Usq, liftC_mul_liftC]
  refine Eq.trans (congrArg liftC ?_) liftC_zero
  simp only [mirFourWit, mirWit_one, mirWit_handleU, mirWit_handleV, SqU5.one_h, SqU5.one_i,
    SqU5.one_j, mirFourU, mirFourV, sigFourX]
  decide

/-- ⭐ **Every class-`≤ 3` verdict at the mirror point is the same for all four dressings**:
both `U₄`-quotients of the relator are trivial in each case, so the whole committed class-three
machinery cannot tell them apart.  The separation is purely class-four. -/
theorem mirFourWit_class_three_blind :
    (SqU5.toU4L (sqRelWord (mirFourWit h j 1)) = 1 ∧
      SqU5.toU4R (sqRelWord (mirFourWit h j 1)) = 1) ∧
    (SqU5.toU4L (sqRelWord (mirFourWit h j (mirFourU * mirFourU))) = 1 ∧
      SqU5.toU4R (sqRelWord (mirFourWit h j (mirFourU * mirFourU))) = 1) ∧
    (SqU5.toU4L (sqRelWord (mirFourWit h j mirFourU)) = 1 ∧
      SqU5.toU4R (sqRelWord (mirFourWit h j mirFourU)) = 1) ∧
    (SqU5.toU4L (sqRelWord (mirFourWit h j mirFourV)) = 1 ∧
      SqU5.toU4R (sqRelWord (mirFourWit h j mirFourV)) = 1) := by
  rw [sqRelWord_mirFourWit_triv, sqRelWord_mirFourWit_Usq, sqRelWord_mirFourWit_U,
    sqRelWord_mirFourWit_V]
  refine ⟨⟨map_one _, map_one _⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, map_one _, map_one _⟩ <;> decide

end MirrorPoint

/-! ## 4 The mirror point as a continuous homomorphism -/

section MirrorHom

variable {h : ℕ} {j : Fin h}

@[simp] theorem mirFourMark_zero (c : gr3R) : mirFourMark h j c 0 = sigFourMark gr3R := by
  rw [mirFourMark, mirWit_zero, mul_one]

@[simp] theorem mirFourMark_one (c : gr3R) : mirFourMark h j c 1 = sigFourX := by
  rw [mirFourMark, mirWit_one]

@[simp] theorem mirFourMark_two (c : gr3R) : mirFourMark h j c 2 = sigFourY := by
  rw [mirFourMark, mirWit_two]

@[simp] theorem mirFourMark_handleU (c : gr3R) :
    mirFourMark h j c (sqHandleIdxU j) = mirFourUGen c := by
  rw [mirFourMark, mirWit_handleU]

@[simp] theorem mirFourMark_handleV (c : gr3R) : mirFourMark h j c (sqHandleIdxV j) = mirFourV := by
  rw [mirFourMark, mirWit_handleV]

theorem mirFourMark_handleU_ne (c : gr3R) {j' : Fin h} (hne : j' ≠ j) :
    mirFourMark h j c (sqHandleIdxU j') = 1 := by
  rw [mirFourMark, mirWit_handleU_ne hne]

theorem mirFourMark_handleV_ne (c : gr3R) {j' : Fin h} (hne : j' ≠ j) :
    mirFourMark h j c (sqHandleIdxV j') = 1 := by
  rw [mirFourMark, mirWit_handleV_ne hne]

variable (h j) in
/-- ⭐⭐ **The mirror-point test hom.**  The §3 marking kills the relator at every handle count,
so the committed lift turns it into an honest continuous homomorphism `D_sq h → U_5(ℤ/8)` whose
`u`-slot value is the cleared letter left-displaced by the pivot image. -/
noncomputable def mirFourHom : ContinuousMonoidHom (DSq h : Type) (SqU5 gr3R) :=
  sqU5Hom gr3R_card h (mirFourMark h j (gr3Pi sqPivotExp))
    (sqRelWord_mirFourMark (gr3Pi sqPivotExp))

@[simp] theorem mirFourHom_gen (i : Fin (sqRank h)) :
    mirFourHom h j (sqGen h i) = mirFourMark h j (gr3Pi sqPivotExp) i :=
  sqU5Hom_gen _ _ _ i

@[simp] theorem mirFourHom_sigma : mirFourHom h j (dsqSigma h) = sigFourMark gr3R := by
  rw [dsqSigma, mirFourHom_gen, mirFourMark_zero]

@[simp] theorem mirFourHom_x0 : mirFourHom h j (dsqX0 h) = sigFourX := by
  rw [dsqX0, mirFourHom_gen, mirFourMark_one]

@[simp] theorem mirFourHom_x1 : mirFourHom h j (dsqX1 h) = sigFourY := by
  rw [dsqX1, mirFourHom_gen, mirFourMark_two]

@[simp] theorem mirFourHom_handleU :
    mirFourHom h j (sqGen h (sqHandleIdxU j)) = mirFourUGen (gr3Pi sqPivotExp) := by
  rw [mirFourHom_gen, mirFourMark_handleU]

@[simp] theorem mirFourHom_handleV : mirFourHom h j (sqGen h (sqHandleIdxV j)) = mirFourV := by
  rw [mirFourHom_gen, mirFourMark_handleV]

theorem mirFourHom_handle_ne {j' : Fin h} (hne : j' ≠ j) :
    mirFourHom h j (sqGen h (sqHandleIdxU j')) = 1 ∧
      mirFourHom h j (sqGen h (sqHandleIdxV j')) = 1 :=
  ⟨by rw [mirFourHom_gen, mirFourMark_handleU_ne _ hne],
    by rw [mirFourHom_gen, mirFourMark_handleV_ne _ hne]⟩

/-- ⭐ **The pivot anchor at the mirror point.**  The sigma- and `x₀`-slots are the committed
ones, so the even-obstruction power lemma applies verbatim. -/
theorem mirFourHom_sqPivot :
    mirFourHom h j (sqPivot h) = rowPivotVal (gr3Pi sqPivotExp) :=
  mirHom_sqPivot mirFourHom_sigma mirFourHom_x0

/-- The mirror row leaves the `u`-letter `ν'`-**nontrivial**… -/
theorem nuSelMir_handleU :
    nuSel h j 1 0 (sqGen h (sqHandleIdxU j)) = ofAdd (1 : ℤ_[2]) := nuSel_handleU

/-- …and the `v`-letter `ν'`-trivial.  This is exactly the mirror of `GradedFourRow`'s row. -/
theorem nuSelMir_handleV : nuSel h j 1 0 (sqGen h (sqHandleIdxV j)) = 1 := by
  rw [nuSel_handleV, ofAdd_zero]

/-- ⭐ The cleared `v`-letter is the raw letter: `ν'(v_j) = 0`, so no pivot power is
subtracted. -/
theorem mirFourHom_sqEichV : mirFourHom h j (sqEichV h (nuSel h j 1 0) j) = mirFourV := by
  rw [sqEichV_of_cleared nuSelMir_handleV, mirFourHom_handleV]

/-- ⭐⭐ **The cleared `u`-letter is the point's `U`-letter.**  `ν'(u_j) = 1` on the nose, so
exactly one inverse pivot is subtracted **on the left** - and the marking was built so that the
subtraction lands on `mirFourU`.  This is the payoff of the ten-row solve at the mirror row. -/
theorem mirFourHom_sqEichU : mirFourHom h j (sqEichU h (nuSel h j 1 0) j) = mirFourU := by
  rw [sqEichU, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_gr5, nuSel_handleU,
    toAdd_ofAdd, zpowZtwo_one_exp, mirFourHom_sqPivot, mirFourHom_handleU, mirFourU_eq]

/-- ⭐ **The `b`-column of the mirror hom is the mirror selected row** `nuSel h j 1 0`, reduced
mod `8`: the `u`-slot's `b`-entry is `1` precisely because the row is uncleared there. -/
theorem mirFourHom_b (x : (DSq h : Type)) :
    (mirFourHom h j x).b = gr3Pi (toAdd (nuSel h j 1 0 x)) :=
  mirHom_b (by rw [mirFourHom_sigma]; rfl) (by rw [mirFourHom_x0]; rfl)
    (by rw [mirFourHom_x1]; rfl) (by rw [mirFourHom_handleU, map_one]; rfl)
    (by rw [mirFourHom_handleV, map_zero]; rfl)
    (fun j' hj' => by rw [(mirFourHom_handle_ne hj').1, (mirFourHom_handle_ne hj').2]; exact
      ⟨rfl, rfl⟩) x

/-- A `ν'`-trivial element has vanishing `b`-column at the mirror hom. -/
theorem mirFourHom_b_eq_zero {g : (DSq h : Type)} (hg : nuSel h j 1 0 g = 1) :
    (mirFourHom h j g).b = 0 := by
  rw [mirFourHom_b, hg, toAdd_one, map_zero]

/-- ⭐⭐ **The frame identification at the MIRROR row.**  The mirror hom sends the
arbitrary-dressing frame with a sigma-only dressing `g` to exactly the mirror witness at the
dressing value, at every handle count. -/
theorem mirFourHom_sqArbFrame (g : (DSq h : Type)) :
    (fun i => mirFourHom h j (sqArbFrame h (nuSel h j 1 0) j (sigArbDress h g) i))
      = mirFourWit h j (mirFourHom h j g) := by
  rw [mirFourWit]
  exact
  mirHom_sqArbFrame mirFourHom_sigma mirFourHom_x0 mirFourHom_x1 mirFourHom_sqEichU
    mirFourHom_sqEichV (fun j' hj' => mirFourHom_handle_ne hj') g

end MirrorHom

/-! ## 5 Soundness at the mirror point -/

section MirrorSoundness

variable {h : ℕ} {j : Fin h}

/-- ⭐ **The committed achievable lattice is even at the mirror point**, both coordinates, at
every `(P, Q, R)`.  The point's parameters are `(A, B, C, D, E, F, T, S) = (1, 0, 0, 0, 0, 1,
1, 0)`: `A = 1` is the odd `chi_a` of the cleared `u`-letter, `B = 0` is the forced vanishing of
`chi_a(v_j)`, and `(T, S) = (1, 0)` is the mirror row itself.  Wave 55's parameters were
`(0, 1, 0, 0, 1, 0, 0, 1)`: the same eight numbers with the two letters exchanged. -/
theorem mirFourWit_lamThree_even {P Q R : gr3R} {z : SqU5 gr3R}
    (hz : selLamThree 1 0 0 0 0 1 1 0 P Q R z) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) := by
  obtain ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, hh, hi⟩ := hz
  exact ⟨⟨r₆ * Q, by rw [hh]; ring⟩,
    ⟨r₅ * R + r₆ * R - r₇ * Q, by rw [hi]; ring⟩⟩

/-- The `σ`-`x₁` commutator at the mirror point: `(h, i) = (0, 4)`, i.e. `R = 4`. -/
theorem mirFourWit_commP_zero_two :
    commP (mirFourWit h j 1 0) (mirFourWit h j 1 2)
      = (⟨0, 0, 0, 0, 0, 0, 0, 0, 4, 0⟩ : SqU5 gr3R) := by
  simp only [mirFourWit, mirWit_zero, mul_one, mirWit_two]
  decide

/-- The `x₁`-`U` commutator: central, i.e. `(P·C − Q·A, Q·E) = (0, 0)`.  At wave 55's row this
was the `x₁`-`V` commutator; the two swap with the row type, exactly as the letters do. -/
theorem mirFourWit_commP_two_handleU :
    commP (mirFourWit h j 1 2) (mirFourWit h j 1 (sqHandleIdxU j))
      = (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 6⟩ : SqU5 gr3R) := by
  simp only [mirFourWit, mirWit_two, mirWit_handleU]
  decide

/-- The `x₁`-`V` commutator: trivial, i.e. `(P·D − Q·B, Q·F) = (0, 0)`. -/
theorem mirFourWit_commP_two_handleV :
    commP (mirFourWit h j 1 2) (mirFourWit h j 1 (sqHandleIdxV j))
      = 1 := by
  simp only [mirFourWit, mirWit_two, mirWit_handleV]
  decide

/-- ⭐ **The extended lattice of `GradedGammaTwo` is even at the mirror point too**, at the
point's own extended-lattice data `(P, Q, R) = (0, 0, 4)` read off the three commutators above.
Wave 54's new moves cannot unlock this point either. -/
theorem mirFourWit_lamThreePlus_even {z : SqU5 gr3R}
    (hz : selLamThreePlus 1 0 0 0 0 1 1 0 0 0 4 z) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) := by
  obtain ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, t₁, t₂, t₃, hh, hi⟩ := hz
  exact ⟨⟨0, by rw [hh]; ring⟩,
    ⟨4 * r₅ + 4 * r₆ + 2 * t₁, by rw [hi]; ring⟩⟩

/-- Every slot of the mirror marking satisfies `GradedFourRow`'s three invariants - vanishing
third abelian column, vanishing second class-two coordinate, even third one - the trivial
handle letters of the other handles included. -/
theorem mirFourMark_le_rowFrameSub (c : gr3R) :
    Subgroup.closure (Set.range (mirFourMark h j c)) ≤ rowFrameSub gr3R := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [mirFourMark_zero]
    exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩
  · rw [mirFourMark_one]
    exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩
  · rw [mirFourMark_two]
    exact ⟨rfl, rfl, 2, by show (4 : gr3R) = 2 * 2; decide⟩
  · by_cases hjj : j' = j
    · subst hjj
      rw [mirFourMark_handleU]
      exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩
    · rw [mirFourMark_handleU_ne _ hjj]
      exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩
  · by_cases hjj : j' = j
    · subst hjj
      rw [mirFourMark_handleV]
      exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩
    · rw [mirFourMark_handleV_ne _ hjj]
      exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩

/-- ⭐⭐ **The model-independent soundness at the mirror point.**  The whole commutator subgroup
of the marking's image - the object `GradedGammaTwo`'s achievability convention lets a
`γ₂`-level dressing be drawn from, quadratic terms included - has vanishing first class-three
coordinate and even second one. -/
theorem mirFour_commutator_le (c : gr3R) :
    rowGaTwoOf (Subgroup.closure (Set.range (mirFourMark h j c))) ≤ rowGaTwoSub gr3R := by
  rw [rowGaTwoOf, Subgroup.closure_le]
  rintro z ⟨p, hp, q, hq, rfl⟩
  exact commP_mem_rowGaTwoSub (mirFourMark_le_rowFrameSub c hp)
    (mirFourMark_le_rowFrameSub c hq)

/-- …in the form the increment lemma consumes. -/
theorem mirFour_gaTwo_even {c : gr3R} {z : SqU5 gr3R}
    (hz : z ∈ rowGaTwoOf (Subgroup.closure (Set.range (mirFourMark h j c)))) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) := by
  obtain ⟨-, -, -, -, -, -, hh, hi⟩ := mirFour_commutator_le c hz
  exact ⟨⟨0, by rw [hh]; ring⟩, hi⟩

/-- **The image of the mirror hom is the closure of the marking**, so the previous theorem
really is a statement about `γ₂(im Φ)`. -/
theorem mirFourHom_mem_closure (x : (DSq h : Type)) :
    mirFourHom h j x ∈ Subgroup.closure (Set.range (mirFourMark h j (gr3Pi sqPivotExp))) := by
  have hgen : Subgroup.closure (Set.range (sqGen h))
      ≤ Subgroup.comap (mirFourHom h j).toMonoidHom
        (Subgroup.closure (Set.range (mirFourMark h j (gr3Pi sqPivotExp)))) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    show mirFourHom h j (sqGen h i)
      ∈ Subgroup.closure (Set.range (mirFourMark h j (gr3Pi sqPivotExp)))
    rw [mirFourHom_gen]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hclosed : IsClosed ((Subgroup.comap (mirFourHom h j).toMonoidHom
      (Subgroup.closure (Set.range (mirFourMark h j (gr3Pi sqPivotExp)))) :
        Subgroup (DSq h : Type)) : Set (DSq h : Type)) := by
    have hpre : ((Subgroup.comap (mirFourHom h j).toMonoidHom
        (Subgroup.closure (Set.range (mirFourMark h j (gr3Pi sqPivotExp)))) :
          Subgroup (DSq h : Type)) : Set (DSq h : Type))
        = mirFourHom h j ⁻¹' ((Subgroup.closure
            (Set.range (mirFourMark h j (gr3Pi sqPivotExp)))) : Set (SqU5 gr3R)) := rfl
    rw [hpre]
    exact (isClosed_discrete _).preimage (mirFourHom h j).continuous_toFun
  have hle := Subgroup.topologicalClosure_minimal _ hgen hclosed
  rw [dsq_topGen h] at hle
  exact hle (Subgroup.mem_top x)

end MirrorSoundness

/-! ## 6 The sigma forcing at the mirror row -/

section MirrorForcing

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐ **The sigma-slot forcing at the mirror point**, against the committed achievable
lattice. -/
theorem mirFourWit_sigma_forced {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hvb : v.b = 0) (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : selLamThree 1 0 0 0 0 1 1 0 P Q R z₃)
    (l₄ : selLamThree 1 0 0 0 0 1 1 0 P Q R z₄)
    (hkill : sqRelWord (sigLift j (mirFourWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  mirWit_sigma_forced commP_mirFour hvb hz₀ hw₁ hw₂ hz₃ hz₄
    (mirFourWit_lamThree_even l₃) (mirFourWit_lamThree_even l₄) hkill

/-- ⭐⭐ **The same forcing with no lattice model**: the two handle dressings are only required
to lie in the commutator subgroup of the marking's image, and the sigma-slot dressing is
**unconstrained**. -/
theorem mirFourWit_sigma_forced_gaTwo {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hvb : v.b = 0) (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (mirFourMark h j c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (mirFourMark h j c))))
    (hkill : sqRelWord (sigLift j (mirFourWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  mirWit_sigma_forced commP_mirFour hvb hz₀ hw₁ hw₂ hz₃ hz₄
    (mirFour_gaTwo_even l₃) (mirFour_gaTwo_even l₄) hkill

/-! ### The legal dressings at the mirror row -/

/-- The cleared `u`-letter is `λ`-trivial. -/
theorem nuLam_mirEichU : nuLam h (sqEichU h (nuSel h j 1 0) j) = 1 :=
  Multiplicative.toAdd.injective (by rw [toAdd_nuLam_sqEichU, toAdd_one])

/-- …and `ν'`-trivial: it lies in the class the residual quantifies over, even though the
`u`-letter itself does not. -/
theorem nu_mirEichU : nuSel h j 1 0 (sqEichU h (nuSel h j 1 0) j) = 1 :=
  Multiplicative.toAdd.injective (by rw [toAdd_nu_sqEichU nuSel_sigma nuSel_x0, toAdd_one])

theorem nuLam_mirEichU_sq :
    nuLam h (sqEichU h (nuSel h j 1 0) j * sqEichU h (nuSel h j 1 0) j) = 1 := by
  rw [map_mul, nuLam_mirEichU, one_mul]

theorem nu_mirEichU_sq :
    nuSel h j 1 0 (sqEichU h (nuSel h j 1 0) j * sqEichU h (nuSel h j 1 0) j) = 1 := by
  rw [map_mul, nu_mirEichU, one_mul]

/-- ⭐⭐ **The forcing is not vacuous**: the cleared `u`-letter is a legal sigma dressing - `λ`-
and `ν'`-trivial - with an **odd** `chi_a`-character.  This is the channel the mirror row opens
in place of the one it closes. -/
theorem mirFour_forcing_nonvacuous :
    nuLam h (sqEichU h (nuSel h j 1 0) j) = 1 ∧
      nuSel h j 1 0 (sqEichU h (nuSel h j 1 0) j) = 1 ∧
      selPar (mirFourHom h j (sqEichU h (nuSel h j 1 0) j)).a = 1 :=
  ⟨nuLam_mirEichU, nu_mirEichU, by rw [mirFourHom_sqEichU]; exact mirFourU_chiA⟩

theorem nuLam_sigArbDress_mirU (i : Fin (sqRank h)) :
    nuLam h (sigArbDress h (sqEichU h (nuSel h j 1 0) j) i) = 1 :=
  nuLam_sigArbDress nuLam_mirEichU i

theorem nu_sigArbDress_mirU (i : Fin (sqRank h)) :
    nuSel h j 1 0 (sigArbDress h (sqEichU h (nuSel h j 1 0) j) i) = 1 :=
  nu_sigArbDress nu_mirEichU i

theorem nuLam_sigArbDress_mirUsq (i : Fin (sqRank h)) :
    nuLam h (sigArbDress h
      (sqEichU h (nuSel h j 1 0) j * sqEichU h (nuSel h j 1 0) j) i) = 1 :=
  nuLam_sigArbDress nuLam_mirEichU_sq i

theorem nu_sigArbDress_mirUsq (i : Fin (sqRank h)) :
    nuSel h j 1 0 (sigArbDress h
      (sqEichU h (nuSel h j 1 0) j * sqEichU h (nuSel h j 1 0) j) i) = 1 :=
  nu_sigArbDress nu_mirEichU_sq i

/-! ### The verdicts on `sqArbFrame` at the mirror row -/

/-- ⭐ **The undressed frame kills the relator outright** at the mirror row. -/
theorem sqRelWord_mirFrame_sigTriv :
    sqRelWord (fun i =>
      mirFourHom h j (sqArbFrame h (nuSel h j 1 0) j (sigArbDress h 1) i)) = 1 := by
  rw [mirFourHom_sqArbFrame, map_one]
  exact sqRelWord_mirFourWit_triv

/-- ⭐ **The squared cleared-`u` dressing leaves the even residue `2`.** -/
theorem sqRelWord_mirFrame_sigUsq :
    sqRelWord (fun i => mirFourHom h j (sqArbFrame h (nuSel h j 1 0) j
      (sigArbDress h (sqEichU h (nuSel h j 1 0) j * sqEichU h (nuSel h j 1 0) j)) i))
      = liftC 2 := by
  rw [mirFourHom_sqArbFrame, map_mul, mirFourHom_sqEichU]
  exact sqRelWord_mirFourWit_Usq

/-- ⭐⭐ **The cleared-`u` dressing leaves the odd residue `1`**: the class-four slice separates
two legal sigma dressings of the same frame over the same hom, at the **mirror** row. -/
theorem sqRelWord_mirFrame_sigU :
    sqRelWord (fun i => mirFourHom h j (sqArbFrame h (nuSel h j 1 0) j
      (sigArbDress h (sqEichU h (nuSel h j 1 0) j)) i)) = liftC 1 := by
  rw [mirFourHom_sqArbFrame, mirFourHom_sqEichU]
  exact sqRelWord_mirFourWit_U

/-- The even residue dies by one explicit achievable `γ₄`-move on the `x₁` slot. -/
theorem sqRelWord_mirFrame_sigUsq_complete :
    sqRelWord (sigLift j (fun i => mirFourHom h j (sqArbFrame h (nuSel h j 1 0) j
      (sigArbDress h (sqEichU h (nuSel h j 1 0) j * sqEichU h (nuSel h j 1 0) j)) i))
      1 1 (liftC 7) 1 1) = 1 := by
  rw [mirFourHom_sqArbFrame, map_mul, mirFourHom_sqEichU]
  exact sqRelWord_mirFourWit_Usq_complete

/-- ⭐⭐ **The odd dressing survives nothing**: no achievable five-slot class-four refinement of
the frame's image kills the relator. -/
theorem sqRelWord_mirFrame_sigU_ne_one {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : selLamThree 1 0 0 0 0 1 1 0 P Q R z₃)
    (l₄ : selLamThree 1 0 0 0 0 1 1 0 P Q R z₄) :
    sqRelWord (sigLift j (fun i => mirFourHom h j (sqArbFrame h (nuSel h j 1 0) j
      (sigArbDress h (sqEichU h (nuSel h j 1 0) j)) i)) z₀ w₁ w₂ z₃ z₄) ≠ 1 := by
  rw [mirFourHom_sqArbFrame, mirFourHom_sqEichU]
  intro hc
  have hpar := mirFourWit_sigma_forced (v := mirFourU) (by decide) hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄ hc
  rw [show (mirFourU.a : gr3R) = 1 from rfl] at hpar
  exact absurd hpar (by decide)

/-- ⭐⭐ …and it survives nothing at the `γ₂` level either. -/
theorem sqRelWord_mirFrame_sigU_ne_one_gaTwo {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (mirFourMark h j c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (mirFourMark h j c)))) :
    sqRelWord (sigLift j (fun i => mirFourHom h j (sqArbFrame h (nuSel h j 1 0) j
      (sigArbDress h (sqEichU h (nuSel h j 1 0) j)) i)) z₀ w₁ w₂ z₃ z₄) ≠ 1 := by
  rw [mirFourHom_sqArbFrame, mirFourHom_sqEichU]
  intro hc
  have hpar := mirFourWit_sigma_forced_gaTwo (v := mirFourU) (by decide) hz₀ hw₁ hw₂ hz₃ hz₄
    l₃ l₄ hc
  rw [show (mirFourU.a : gr3R) = 1 from rfl] at hpar
  exact absurd hpar (by decide)

/-! ### The headline at the mirror row -/

/-- ⭐⭐ **The class-four selection bit on `sqArbFrame` at the mirror row.** -/
theorem sqArbFrame_sigma_bit_mirror {g : (DSq h : Type)} (hg : nuSel h j 1 0 g = 1) :
    selPar ((sqRelWord fun i =>
        mirFourHom h j (sqArbFrame h (nuSel h j 1 0) j (sigArbDress h g) i)).j)
      = selPar (mirFourHom h j g).a := by
  rw [mirFourHom_sqArbFrame g]
  exact mirWit_bit commP_mirFour (mirFourHom_b_eq_zero hg)

/-- ⭐⭐ **THE HEADLINE AT THE MIRROR ROW `nuSel h j 1 0`, at every handle count.**  Every
`ν'`-trivial sigma dressing of the arbitrary-dressing frame whose image is killed by any
achievable five-slot class-four refinement has an even `chi_a`-character.  Nothing is carried
beyond the dressing's own legality. -/
theorem sqArbFrame_sigma_forced_mirror {g : (DSq h : Type)} (hg : nuSel h j 1 0 g = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : selLamThree 1 0 0 0 0 1 1 0 P Q R z₃)
    (l₄ : selLamThree 1 0 0 0 0 1 1 0 P Q R z₄)
    (hkill : sqRelWord (sigLift j
      (fun i => mirFourHom h j (sqArbFrame h (nuSel h j 1 0) j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (mirFourHom h j g).a = 0 := by
  rw [mirFourHom_sqArbFrame g] at hkill
  exact mirFourWit_sigma_forced (mirFourHom_b_eq_zero hg) hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄ hkill

/-- ⭐⭐ **The headline at the `γ₂` level**: the achievability lattice replaced by the
commutator subgroup of the image itself. -/
theorem sqArbFrame_sigma_forced_mirror_gaTwo {g : (DSq h : Type)} (hg : nuSel h j 1 0 g = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (mirFourMark h j c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (mirFourMark h j c))))
    (hkill : sqRelWord (sigLift j
      (fun i => mirFourHom h j (sqArbFrame h (nuSel h j 1 0) j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (mirFourHom h j g).a = 0 := by
  rw [mirFourHom_sqArbFrame g] at hkill
  exact mirFourWit_sigma_forced_gaTwo (mirFourHom_b_eq_zero hg) hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄ hkill

/-- ⭐⭐ **The escape separates the sigma dressings on `sqArbFrame` at the mirror row**, with
the legality of both dressings exhibited. -/
theorem mirFour_escape_separates :
    ((∀ i, nuLam h (sigArbDress h
        (sqEichU h (nuSel h j 1 0) j * sqEichU h (nuSel h j 1 0) j) i) = 1) ∧
      ∀ i, nuSel h j 1 0 (sigArbDress h
        (sqEichU h (nuSel h j 1 0) j * sqEichU h (nuSel h j 1 0) j) i) = 1) ∧
    ((∀ i, nuLam h (sigArbDress h (sqEichU h (nuSel h j 1 0) j) i) = 1) ∧
      ∀ i, nuSel h j 1 0 (sigArbDress h (sqEichU h (nuSel h j 1 0) j) i) = 1) ∧
    sqRelWord (fun i => mirFourHom h j (sqArbFrame h (nuSel h j 1 0) j
      (sigArbDress h (sqEichU h (nuSel h j 1 0) j * sqEichU h (nuSel h j 1 0) j)) i))
      = liftC 2 ∧
    sqRelWord (fun i => mirFourHom h j (sqArbFrame h (nuSel h j 1 0) j
      (sigArbDress h (sqEichU h (nuSel h j 1 0) j)) i)) = liftC 1 :=
  ⟨⟨nuLam_sigArbDress_mirUsq, nu_sigArbDress_mirUsq⟩,
    ⟨nuLam_sigArbDress_mirU, nu_sigArbDress_mirU⟩,
    sqRelWord_mirFrame_sigUsq, sqRelWord_mirFrame_sigU⟩

/-- ⭐ **Every class-`≤ 3` verdict on the frame is the same for all three dressings** at the
mirror row as well. -/
theorem mirFrame_class_three_blind :
    (SqU5.toU4L (sqRelWord fun i => mirFourHom h j (sqArbFrame h (nuSel h j 1 0) j
        (sigArbDress h 1) i)) = 1 ∧
      SqU5.toU4R (sqRelWord fun i => mirFourHom h j (sqArbFrame h (nuSel h j 1 0) j
        (sigArbDress h 1) i)) = 1) ∧
    (SqU5.toU4L (sqRelWord fun i => mirFourHom h j (sqArbFrame h (nuSel h j 1 0) j
        (sigArbDress h (sqEichU h (nuSel h j 1 0) j
          * sqEichU h (nuSel h j 1 0) j)) i)) = 1 ∧
      SqU5.toU4R (sqRelWord fun i => mirFourHom h j (sqArbFrame h (nuSel h j 1 0) j
        (sigArbDress h (sqEichU h (nuSel h j 1 0) j
          * sqEichU h (nuSel h j 1 0) j)) i)) = 1) ∧
    (SqU5.toU4L (sqRelWord fun i => mirFourHom h j (sqArbFrame h (nuSel h j 1 0) j
        (sigArbDress h (sqEichU h (nuSel h j 1 0) j)) i)) = 1 ∧
      SqU5.toU4R (sqRelWord fun i => mirFourHom h j (sqArbFrame h (nuSel h j 1 0) j
        (sigArbDress h (sqEichU h (nuSel h j 1 0) j)) i)) = 1) := by
  rw [sqRelWord_mirFrame_sigTriv, sqRelWord_mirFrame_sigUsq, sqRelWord_mirFrame_sigU]
  refine ⟨⟨map_one _, map_one _⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

end MirrorForcing

/-! ## 7 The doubly-uncleared row `nuSel h j 1 1`

⚠ This row is **not** a swap of anything.  §1 does not close a channel here: it *couples* the
two, `χ_a(U₀) = χ_a(V₀)`, because both handle letters are displaced and the two displacements
interact.  The interaction term `P.a·Q.b − P.b·Q.a` of `sqRelWord_e_displace_two` vanishes only
because both displacements are by the **same** pivot image, and that is the whole reason a point
exists at all.

The coupling is an equality, not a vanishing, so the row is **not** obstructed: taking both
cleared letters to be the *same* odd letter satisfies it, and then **both** channels are open.
The point below does that, with wave 55's `rowFourV` in both handle slots. -/

section DoublePoint

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐ **The forced coupling, realised.**  At the doubly-uncleared row the two cleared letters
must have equal `χ_a`; the point takes them to be the *same* letter - the mirror point's
`mirFourU`, which is wave 55's `rowFourV`, which is `GradedSigmaFour`'s `sigFourU`.  All three
committed odd channels are the same tuple, and here it sits in both handle slots at once. -/
theorem dblFour_letters_equal : mirFourU = rowFourV ∧ mirFourU = sigFourU := ⟨rfl, rfl⟩

/-- The live handle block of the doubly-uncleared marking is trivial, at every pivot residue:
the `u`-slot is left-displaced and the `v`-slot right-displaced, by the same pivot image. -/
theorem commP_dblFourGen : ∀ c : gr3R, commP (mirFourUGen c) (rowFourVGen c) = 1 := by decide

/-- …and so is the cleared frame's. -/
theorem commP_dblFour : commP mirFourU rowFourV = 1 := by decide

variable (h j) in
/-- **The marking of the doubly-uncleared point**: the committed core slots, the `j`-th handle
pair carrying the **left**-displaced `u`-letter and the **right**-displaced `v`-letter, every
other handle letter trivial. -/
def dblFourMark (c : gr3R) : Fin (sqRank h) → SqU5 gr3R :=
  mirWit h j (mirFourUGen c) (rowFourVGen c) 1

variable (h j) in
/-- The doubly-uncleared witness at sigma-dressing value `v`: both handle slots carry the
**cleared** letters. -/
def dblFourWit (v : SqU5 gr3R) : Fin (sqRank h) → SqU5 gr3R := mirWit h j mirFourU rowFourV v

/-- ⭐⭐ **The ten-row solve at the doubly-uncleared point**, at every handle count, every
handle and every residue of the pivot exponent. -/
theorem sqRelWord_dblFourMark : ∀ c : gr3R, sqRelWord (dblFourMark h j c) = 1 :=
  fun c => sqRelWord_mirWit_triv (commP_dblFourGen c)

theorem sqRelWord_dblFourWit_triv : sqRelWord (dblFourWit h j 1) = 1 := by
  rw [dblFourWit, sqRelWord_mirWit_triv commP_dblFour]

theorem sqRelWord_dblFourWit (v : SqU5 gr3R) :
    sqRelWord (dblFourWit h j v) = sqWord (sigFourMark gr3R * v) sigFourX sigFourY := by
  rw [dblFourWit, sqRelWord_mirWit commP_dblFour]

/-- ⭐⭐ **The cleared-letter dressing leaves the odd residue `1`** at the doubly-uncleared row
too. -/
theorem sqRelWord_dblFourWit_U : sqRelWord (dblFourWit h j mirFourU) = liftC 1 := by
  rw [sqRelWord_dblFourWit]; decide

/-- ⭐ …and its square the even residue `2`. -/
theorem sqRelWord_dblFourWit_Usq :
    sqRelWord (dblFourWit h j (mirFourU * mirFourU)) = liftC 2 := by
  rw [sqRelWord_dblFourWit]; decide

theorem sqRelWord_dblFourWit_Usq_complete :
    sqRelWord (sigLift j (dblFourWit h j (mirFourU * mirFourU)) 1 1 (liftC 7) 1 1) = 1 := by
  rw [sqRelWord_sigLift SqU5.isGaThree_one SqU5.isGaFour_one (liftC_isGaFour 7)
    SqU5.isGaThree_one SqU5.isGaThree_one, sqRelWord_dblFourWit_Usq, liftC_mul_liftC]
  refine Eq.trans (congrArg liftC ?_) liftC_zero
  simp only [dblFourWit, mirWit_one, mirWit_handleU, mirWit_handleV, SqU5.one_h, SqU5.one_i,
    SqU5.one_j, mirFourU, rowFourV, sigFourX]
  decide

/-- ⭐ Class-`≤ 3` blindness at the doubly-uncleared point. -/
theorem dblFourWit_class_three_blind :
    (SqU5.toU4L (sqRelWord (dblFourWit h j 1)) = 1 ∧
      SqU5.toU4R (sqRelWord (dblFourWit h j 1)) = 1) ∧
    (SqU5.toU4L (sqRelWord (dblFourWit h j (mirFourU * mirFourU))) = 1 ∧
      SqU5.toU4R (sqRelWord (dblFourWit h j (mirFourU * mirFourU))) = 1) ∧
    (SqU5.toU4L (sqRelWord (dblFourWit h j mirFourU)) = 1 ∧
      SqU5.toU4R (sqRelWord (dblFourWit h j mirFourU)) = 1) := by
  rw [sqRelWord_dblFourWit_triv, sqRelWord_dblFourWit_Usq, sqRelWord_dblFourWit_U]
  refine ⟨⟨map_one _, map_one _⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

@[simp] theorem dblFourMark_zero (c : gr3R) : dblFourMark h j c 0 = sigFourMark gr3R := by
  rw [dblFourMark, mirWit_zero, mul_one]

@[simp] theorem dblFourMark_one (c : gr3R) : dblFourMark h j c 1 = sigFourX := by
  rw [dblFourMark, mirWit_one]

@[simp] theorem dblFourMark_two (c : gr3R) : dblFourMark h j c 2 = sigFourY := by
  rw [dblFourMark, mirWit_two]

@[simp] theorem dblFourMark_handleU (c : gr3R) :
    dblFourMark h j c (sqHandleIdxU j) = mirFourUGen c := by
  rw [dblFourMark, mirWit_handleU]

@[simp] theorem dblFourMark_handleV (c : gr3R) :
    dblFourMark h j c (sqHandleIdxV j) = rowFourVGen c := by
  rw [dblFourMark, mirWit_handleV]

theorem dblFourMark_handleU_ne (c : gr3R) {j' : Fin h} (hne : j' ≠ j) :
    dblFourMark h j c (sqHandleIdxU j') = 1 := by rw [dblFourMark, mirWit_handleU_ne hne]

theorem dblFourMark_handleV_ne (c : gr3R) {j' : Fin h} (hne : j' ≠ j) :
    dblFourMark h j c (sqHandleIdxV j') = 1 := by rw [dblFourMark, mirWit_handleV_ne hne]

variable (h j) in
/-- ⭐⭐ **The doubly-uncleared test hom.** -/
noncomputable def dblFourHom : ContinuousMonoidHom (DSq h : Type) (SqU5 gr3R) :=
  sqU5Hom gr3R_card h (dblFourMark h j (gr3Pi sqPivotExp))
    (sqRelWord_dblFourMark (gr3Pi sqPivotExp))

@[simp] theorem dblFourHom_gen (i : Fin (sqRank h)) :
    dblFourHom h j (sqGen h i) = dblFourMark h j (gr3Pi sqPivotExp) i :=
  sqU5Hom_gen _ _ _ i

@[simp] theorem dblFourHom_sigma : dblFourHom h j (dsqSigma h) = sigFourMark gr3R := by
  rw [dsqSigma, dblFourHom_gen, dblFourMark_zero]

@[simp] theorem dblFourHom_x0 : dblFourHom h j (dsqX0 h) = sigFourX := by
  rw [dsqX0, dblFourHom_gen, dblFourMark_one]

@[simp] theorem dblFourHom_x1 : dblFourHom h j (dsqX1 h) = sigFourY := by
  rw [dsqX1, dblFourHom_gen, dblFourMark_two]

@[simp] theorem dblFourHom_handleU :
    dblFourHom h j (sqGen h (sqHandleIdxU j)) = mirFourUGen (gr3Pi sqPivotExp) := by
  rw [dblFourHom_gen, dblFourMark_handleU]

@[simp] theorem dblFourHom_handleV :
    dblFourHom h j (sqGen h (sqHandleIdxV j)) = rowFourVGen (gr3Pi sqPivotExp) := by
  rw [dblFourHom_gen, dblFourMark_handleV]

theorem dblFourHom_handle_ne {j' : Fin h} (hne : j' ≠ j) :
    dblFourHom h j (sqGen h (sqHandleIdxU j')) = 1 ∧
      dblFourHom h j (sqGen h (sqHandleIdxV j')) = 1 :=
  ⟨by rw [dblFourHom_gen, dblFourMark_handleU_ne _ hne],
    by rw [dblFourHom_gen, dblFourMark_handleV_ne _ hne]⟩

theorem dblFourHom_sqPivot : dblFourHom h j (sqPivot h) = rowPivotVal (gr3Pi sqPivotExp) :=
  mirHom_sqPivot dblFourHom_sigma dblFourHom_x0

/-- ⭐⭐ **Both cleared letters have honest prescribed images** at the doubly-uncleared row:
one inverse pivot on the left of the `u`-letter, one on the right of the `v`-letter. -/
theorem dblFourHom_sqEichU : dblFourHom h j (sqEichU h (nuSel h j 1 1) j) = mirFourU := by
  rw [sqEichU, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_gr5, nuSel_handleU,
    toAdd_ofAdd, zpowZtwo_one_exp, dblFourHom_sqPivot, dblFourHom_handleU, mirFourU_eq]

theorem dblFourHom_sqEichV : dblFourHom h j (sqEichV h (nuSel h j 1 1) j) = rowFourV := by
  rw [sqEichV, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_gr5, nuSel_handleV,
    toAdd_ofAdd, zpowZtwo_one_exp, dblFourHom_sqPivot, dblFourHom_handleV, rowFourV_eq]

/-- ⭐ **The `b`-column of the doubly-uncleared hom is its row**: both handle letters have
`b`-entry `1`, because both are uncleared. -/
theorem dblFourHom_b (x : (DSq h : Type)) :
    (dblFourHom h j x).b = gr3Pi (toAdd (nuSel h j 1 1 x)) :=
  mirHom_b (by rw [dblFourHom_sigma]; rfl) (by rw [dblFourHom_x0]; rfl)
    (by rw [dblFourHom_x1]; rfl) (by rw [dblFourHom_handleU, map_one]; rfl)
    (by rw [dblFourHom_handleV, map_one]; rfl)
    (fun j' hj' => by rw [(dblFourHom_handle_ne hj').1, (dblFourHom_handle_ne hj').2]; exact
      ⟨rfl, rfl⟩) x

theorem dblFourHom_b_eq_zero {g : (DSq h : Type)} (hg : nuSel h j 1 1 g = 1) :
    (dblFourHom h j g).b = 0 := by
  rw [dblFourHom_b, hg, toAdd_one, map_zero]

/-- ⭐⭐ **The frame identification at the DOUBLY-UNCLEARED row.** -/
theorem dblFourHom_sqArbFrame (g : (DSq h : Type)) :
    (fun i => dblFourHom h j (sqArbFrame h (nuSel h j 1 1) j (sigArbDress h g) i))
      = dblFourWit h j (dblFourHom h j g) := by
  rw [dblFourWit]
  exact mirHom_sqArbFrame dblFourHom_sigma dblFourHom_x0 dblFourHom_x1 dblFourHom_sqEichU
    dblFourHom_sqEichV (fun j' hj' => dblFourHom_handle_ne hj') g

/-! ### Soundness at the doubly-uncleared point -/

/-- ⭐ **The committed achievable lattice is even at the doubly-uncleared point.**  Its
parameters are `(A, B, C, D, E, F, T, S) = (1, 1, 0, 0, 0, 0, 1, 1)`: **both** `χ_a`'s odd -
the coupling - and both rows uncleared. -/
theorem dblFourWit_lamThree_even {P Q R : gr3R} {z : SqU5 gr3R}
    (hz : selLamThree 1 1 0 0 0 0 1 1 P Q R z) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) := by
  obtain ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, hh, hi⟩ := hz
  exact ⟨⟨r₆ * Q + r₇ * Q, by rw [hh]; ring⟩,
    ⟨r₅ * R + r₆ * R + r₇ * R, by rw [hi]; ring⟩⟩

theorem dblFourWit_commP_zero_two :
    commP (dblFourWit h j 1 0) (dblFourWit h j 1 2)
      = (⟨0, 0, 0, 0, 0, 0, 0, 0, 4, 0⟩ : SqU5 gr3R) := by
  simp only [dblFourWit, mirWit_zero, mul_one, mirWit_two]
  decide

theorem dblFourWit_commP_two_handleU :
    commP (dblFourWit h j 1 2) (dblFourWit h j 1 (sqHandleIdxU j))
      = (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 6⟩ : SqU5 gr3R) := by
  simp only [dblFourWit, mirWit_two, mirWit_handleU]
  decide

theorem dblFourWit_commP_two_handleV :
    commP (dblFourWit h j 1 2) (dblFourWit h j 1 (sqHandleIdxV j))
      = (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 6⟩ : SqU5 gr3R) := by
  simp only [dblFourWit, mirWit_two, mirWit_handleV]
  decide

/-- ⭐ **The extended lattice is even at the doubly-uncleared point too**, at its own data
`(P, Q, R) = (0, 0, 4)`. -/
theorem dblFourWit_lamThreePlus_even {z : SqU5 gr3R}
    (hz : selLamThreePlus 1 1 0 0 0 0 1 1 0 0 4 z) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) := by
  obtain ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, t₁, t₂, t₃, hh, hi⟩ := hz
  exact ⟨⟨0, by rw [hh]; ring⟩,
    ⟨4 * r₅ + 4 * r₆ + 4 * r₇ + 2 * t₁, by rw [hi]; ring⟩⟩

theorem dblFourMark_le_rowFrameSub (c : gr3R) :
    Subgroup.closure (Set.range (dblFourMark h j c)) ≤ rowFrameSub gr3R := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [dblFourMark_zero]
    exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩
  · rw [dblFourMark_one]
    exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩
  · rw [dblFourMark_two]
    exact ⟨rfl, rfl, 2, by show (4 : gr3R) = 2 * 2; decide⟩
  · by_cases hjj : j' = j
    · subst hjj
      rw [dblFourMark_handleU]
      exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩
    · rw [dblFourMark_handleU_ne _ hjj]
      exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩
  · by_cases hjj : j' = j
    · subst hjj
      rw [dblFourMark_handleV]
      exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩
    · rw [dblFourMark_handleV_ne _ hjj]
      exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩

/-- ⭐⭐ **The model-independent soundness at the doubly-uncleared point.** -/
theorem dblFour_commutator_le (c : gr3R) :
    rowGaTwoOf (Subgroup.closure (Set.range (dblFourMark h j c))) ≤ rowGaTwoSub gr3R := by
  rw [rowGaTwoOf, Subgroup.closure_le]
  rintro z ⟨p, hp, q, hq, rfl⟩
  exact commP_mem_rowGaTwoSub (dblFourMark_le_rowFrameSub c hp)
    (dblFourMark_le_rowFrameSub c hq)

theorem dblFour_gaTwo_even {c : gr3R} {z : SqU5 gr3R}
    (hz : z ∈ rowGaTwoOf (Subgroup.closure (Set.range (dblFourMark h j c)))) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) := by
  obtain ⟨-, -, -, -, -, -, hh, hi⟩ := dblFour_commutator_le c hz
  exact ⟨⟨0, by rw [hh]; ring⟩, hi⟩

theorem dblFourHom_mem_closure (x : (DSq h : Type)) :
    dblFourHom h j x ∈ Subgroup.closure (Set.range (dblFourMark h j (gr3Pi sqPivotExp))) := by
  have hgen : Subgroup.closure (Set.range (sqGen h))
      ≤ Subgroup.comap (dblFourHom h j).toMonoidHom
        (Subgroup.closure (Set.range (dblFourMark h j (gr3Pi sqPivotExp)))) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    show dblFourHom h j (sqGen h i)
      ∈ Subgroup.closure (Set.range (dblFourMark h j (gr3Pi sqPivotExp)))
    rw [dblFourHom_gen]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hclosed : IsClosed ((Subgroup.comap (dblFourHom h j).toMonoidHom
      (Subgroup.closure (Set.range (dblFourMark h j (gr3Pi sqPivotExp)))) :
        Subgroup (DSq h : Type)) : Set (DSq h : Type)) := by
    have hpre : ((Subgroup.comap (dblFourHom h j).toMonoidHom
        (Subgroup.closure (Set.range (dblFourMark h j (gr3Pi sqPivotExp)))) :
          Subgroup (DSq h : Type)) : Set (DSq h : Type))
        = dblFourHom h j ⁻¹' ((Subgroup.closure
            (Set.range (dblFourMark h j (gr3Pi sqPivotExp)))) : Set (SqU5 gr3R)) := rfl
    rw [hpre]
    exact (isClosed_discrete _).preimage (dblFourHom h j).continuous_toFun
  have hle := Subgroup.topologicalClosure_minimal _ hgen hclosed
  rw [dsq_topGen h] at hle
  exact hle (Subgroup.mem_top x)

/-! ### The forcing at the doubly-uncleared row -/

theorem dblFourWit_sigma_forced {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hvb : v.b = 0) (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : selLamThree 1 1 0 0 0 0 1 1 P Q R z₃)
    (l₄ : selLamThree 1 1 0 0 0 0 1 1 P Q R z₄)
    (hkill : sqRelWord (sigLift j (dblFourWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  mirWit_sigma_forced commP_dblFour hvb hz₀ hw₁ hw₂ hz₃ hz₄
    (dblFourWit_lamThree_even l₃) (dblFourWit_lamThree_even l₄) hkill

theorem dblFourWit_sigma_forced_gaTwo {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hvb : v.b = 0) (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (dblFourMark h j c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (dblFourMark h j c))))
    (hkill : sqRelWord (sigLift j (dblFourWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  mirWit_sigma_forced commP_dblFour hvb hz₀ hw₁ hw₂ hz₃ hz₄
    (dblFour_gaTwo_even l₃) (dblFour_gaTwo_even l₄) hkill

theorem nuLam_dblEichU : nuLam h (sqEichU h (nuSel h j 1 1) j) = 1 :=
  Multiplicative.toAdd.injective (by rw [toAdd_nuLam_sqEichU, toAdd_one])

theorem nu_dblEichU : nuSel h j 1 1 (sqEichU h (nuSel h j 1 1) j) = 1 :=
  Multiplicative.toAdd.injective (by rw [toAdd_nu_sqEichU nuSel_sigma nuSel_x0, toAdd_one])

theorem nuLam_dblEichV : nuLam h (sqEichV h (nuSel h j 1 1) j) = 1 :=
  Multiplicative.toAdd.injective (by rw [toAdd_nuLam_sqEichV, toAdd_one])

theorem nu_dblEichV : nuSel h j 1 1 (sqEichV h (nuSel h j 1 1) j) = 1 :=
  Multiplicative.toAdd.injective (by rw [toAdd_nu_sqEichV nuSel_sigma nuSel_x0, toAdd_one])

theorem nuLam_dblEichU_sq :
    nuLam h (sqEichU h (nuSel h j 1 1) j * sqEichU h (nuSel h j 1 1) j) = 1 := by
  rw [map_mul, nuLam_dblEichU, one_mul]

theorem nu_dblEichU_sq :
    nuSel h j 1 1 (sqEichU h (nuSel h j 1 1) j * sqEichU h (nuSel h j 1 1) j) = 1 := by
  rw [map_mul, nu_dblEichU, one_mul]

/-- ⭐⭐ **The forcing is not vacuous at the doubly-uncleared row, and it is doubly so**:
**both** cleared letters are legal sigma dressings with an **odd** `chi_a`-character.  The
coupling `χ_a(U₀) = χ_a(V₀)` of §1 does not close a channel - it opens two. -/
theorem dblFour_forcing_nonvacuous :
    (nuLam h (sqEichU h (nuSel h j 1 1) j) = 1 ∧
      nuSel h j 1 1 (sqEichU h (nuSel h j 1 1) j) = 1 ∧
      selPar (dblFourHom h j (sqEichU h (nuSel h j 1 1) j)).a = 1) ∧
    (nuLam h (sqEichV h (nuSel h j 1 1) j) = 1 ∧
      nuSel h j 1 1 (sqEichV h (nuSel h j 1 1) j) = 1 ∧
      selPar (dblFourHom h j (sqEichV h (nuSel h j 1 1) j)).a = 1) :=
  ⟨⟨nuLam_dblEichU, nu_dblEichU, by rw [dblFourHom_sqEichU]; exact mirFourU_chiA⟩,
    ⟨nuLam_dblEichV, nu_dblEichV, by rw [dblFourHom_sqEichV]; exact rowFourV_chiA⟩⟩

theorem nuLam_sigArbDress_dblU (i : Fin (sqRank h)) :
    nuLam h (sigArbDress h (sqEichU h (nuSel h j 1 1) j) i) = 1 :=
  nuLam_sigArbDress nuLam_dblEichU i

theorem nu_sigArbDress_dblU (i : Fin (sqRank h)) :
    nuSel h j 1 1 (sigArbDress h (sqEichU h (nuSel h j 1 1) j) i) = 1 :=
  nu_sigArbDress nu_dblEichU i

theorem nuLam_sigArbDress_dblUsq (i : Fin (sqRank h)) :
    nuLam h (sigArbDress h
      (sqEichU h (nuSel h j 1 1) j * sqEichU h (nuSel h j 1 1) j) i) = 1 :=
  nuLam_sigArbDress nuLam_dblEichU_sq i

theorem nu_sigArbDress_dblUsq (i : Fin (sqRank h)) :
    nuSel h j 1 1 (sigArbDress h
      (sqEichU h (nuSel h j 1 1) j * sqEichU h (nuSel h j 1 1) j) i) = 1 :=
  nu_sigArbDress nu_dblEichU_sq i

/-! ### The verdicts on `sqArbFrame` at the doubly-uncleared row -/

theorem sqRelWord_dblFrame_sigTriv :
    sqRelWord (fun i =>
      dblFourHom h j (sqArbFrame h (nuSel h j 1 1) j (sigArbDress h 1) i)) = 1 := by
  rw [dblFourHom_sqArbFrame, map_one]
  exact sqRelWord_dblFourWit_triv

theorem sqRelWord_dblFrame_sigUsq :
    sqRelWord (fun i => dblFourHom h j (sqArbFrame h (nuSel h j 1 1) j
      (sigArbDress h (sqEichU h (nuSel h j 1 1) j * sqEichU h (nuSel h j 1 1) j)) i))
      = liftC 2 := by
  rw [dblFourHom_sqArbFrame, map_mul, dblFourHom_sqEichU]
  exact sqRelWord_dblFourWit_Usq

/-- ⭐⭐ **The odd residue at the doubly-uncleared row.** -/
theorem sqRelWord_dblFrame_sigU :
    sqRelWord (fun i => dblFourHom h j (sqArbFrame h (nuSel h j 1 1) j
      (sigArbDress h (sqEichU h (nuSel h j 1 1) j)) i)) = liftC 1 := by
  rw [dblFourHom_sqArbFrame, dblFourHom_sqEichU]
  exact sqRelWord_dblFourWit_U

theorem sqRelWord_dblFrame_sigUsq_complete :
    sqRelWord (sigLift j (fun i => dblFourHom h j (sqArbFrame h (nuSel h j 1 1) j
      (sigArbDress h (sqEichU h (nuSel h j 1 1) j * sqEichU h (nuSel h j 1 1) j)) i))
      1 1 (liftC 7) 1 1) = 1 := by
  rw [dblFourHom_sqArbFrame, map_mul, dblFourHom_sqEichU]
  exact sqRelWord_dblFourWit_Usq_complete

theorem sqRelWord_dblFrame_sigU_ne_one {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : selLamThree 1 1 0 0 0 0 1 1 P Q R z₃)
    (l₄ : selLamThree 1 1 0 0 0 0 1 1 P Q R z₄) :
    sqRelWord (sigLift j (fun i => dblFourHom h j (sqArbFrame h (nuSel h j 1 1) j
      (sigArbDress h (sqEichU h (nuSel h j 1 1) j)) i)) z₀ w₁ w₂ z₃ z₄) ≠ 1 := by
  rw [dblFourHom_sqArbFrame, dblFourHom_sqEichU]
  intro hc
  have hpar := dblFourWit_sigma_forced (v := mirFourU) (by decide) hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄ hc
  rw [show (mirFourU.a : gr3R) = 1 from rfl] at hpar
  exact absurd hpar (by decide)

theorem sqRelWord_dblFrame_sigU_ne_one_gaTwo {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (dblFourMark h j c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (dblFourMark h j c)))) :
    sqRelWord (sigLift j (fun i => dblFourHom h j (sqArbFrame h (nuSel h j 1 1) j
      (sigArbDress h (sqEichU h (nuSel h j 1 1) j)) i)) z₀ w₁ w₂ z₃ z₄) ≠ 1 := by
  rw [dblFourHom_sqArbFrame, dblFourHom_sqEichU]
  intro hc
  have hpar := dblFourWit_sigma_forced_gaTwo (v := mirFourU) (by decide) hz₀ hw₁ hw₂ hz₃ hz₄
    l₃ l₄ hc
  rw [show (mirFourU.a : gr3R) = 1 from rfl] at hpar
  exact absurd hpar (by decide)

/-- ⭐⭐ **The class-four selection bit on `sqArbFrame` at the doubly-uncleared row.** -/
theorem sqArbFrame_sigma_bit_double {g : (DSq h : Type)} (hg : nuSel h j 1 1 g = 1) :
    selPar ((sqRelWord fun i =>
        dblFourHom h j (sqArbFrame h (nuSel h j 1 1) j (sigArbDress h g) i)).j)
      = selPar (dblFourHom h j g).a := by
  rw [dblFourHom_sqArbFrame g, dblFourWit]
  exact mirWit_bit commP_dblFour (dblFourHom_b_eq_zero hg)

/-- ⭐⭐ **THE HEADLINE AT THE DOUBLY-UNCLEARED ROW `nuSel h j 1 1`, at every handle count.** -/
theorem sqArbFrame_sigma_forced_double {g : (DSq h : Type)} (hg : nuSel h j 1 1 g = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : selLamThree 1 1 0 0 0 0 1 1 P Q R z₃)
    (l₄ : selLamThree 1 1 0 0 0 0 1 1 P Q R z₄)
    (hkill : sqRelWord (sigLift j
      (fun i => dblFourHom h j (sqArbFrame h (nuSel h j 1 1) j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (dblFourHom h j g).a = 0 := by
  rw [dblFourHom_sqArbFrame g] at hkill
  exact dblFourWit_sigma_forced (dblFourHom_b_eq_zero hg) hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄ hkill

/-- ⭐⭐ **…and at the `γ₂` level.** -/
theorem sqArbFrame_sigma_forced_double_gaTwo {g : (DSq h : Type)} (hg : nuSel h j 1 1 g = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (dblFourMark h j c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (dblFourMark h j c))))
    (hkill : sqRelWord (sigLift j
      (fun i => dblFourHom h j (sqArbFrame h (nuSel h j 1 1) j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (dblFourHom h j g).a = 0 := by
  rw [dblFourHom_sqArbFrame g] at hkill
  exact dblFourWit_sigma_forced_gaTwo (dblFourHom_b_eq_zero hg) hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄ hkill

/-- ⭐⭐ **The escape separates the sigma dressings at the doubly-uncleared row.** -/
theorem dblFour_escape_separates :
    ((∀ i, nuLam h (sigArbDress h
        (sqEichU h (nuSel h j 1 1) j * sqEichU h (nuSel h j 1 1) j) i) = 1) ∧
      ∀ i, nuSel h j 1 1 (sigArbDress h
        (sqEichU h (nuSel h j 1 1) j * sqEichU h (nuSel h j 1 1) j) i) = 1) ∧
    ((∀ i, nuLam h (sigArbDress h (sqEichU h (nuSel h j 1 1) j) i) = 1) ∧
      ∀ i, nuSel h j 1 1 (sigArbDress h (sqEichU h (nuSel h j 1 1) j) i) = 1) ∧
    sqRelWord (fun i => dblFourHom h j (sqArbFrame h (nuSel h j 1 1) j
      (sigArbDress h (sqEichU h (nuSel h j 1 1) j * sqEichU h (nuSel h j 1 1) j)) i))
      = liftC 2 ∧
    sqRelWord (fun i => dblFourHom h j (sqArbFrame h (nuSel h j 1 1) j
      (sigArbDress h (sqEichU h (nuSel h j 1 1) j)) i)) = liftC 1 :=
  ⟨⟨nuLam_sigArbDress_dblUsq, nu_sigArbDress_dblUsq⟩,
    ⟨nuLam_sigArbDress_dblU, nu_sigArbDress_dblU⟩,
    sqRelWord_dblFrame_sigUsq, sqRelWord_dblFrame_sigU⟩

theorem dblFrame_class_three_blind :
    (SqU5.toU4L (sqRelWord fun i => dblFourHom h j (sqArbFrame h (nuSel h j 1 1) j
        (sigArbDress h 1) i)) = 1 ∧
      SqU5.toU4R (sqRelWord fun i => dblFourHom h j (sqArbFrame h (nuSel h j 1 1) j
        (sigArbDress h 1) i)) = 1) ∧
    (SqU5.toU4L (sqRelWord fun i => dblFourHom h j (sqArbFrame h (nuSel h j 1 1) j
        (sigArbDress h (sqEichU h (nuSel h j 1 1) j
          * sqEichU h (nuSel h j 1 1) j)) i)) = 1 ∧
      SqU5.toU4R (sqRelWord fun i => dblFourHom h j (sqArbFrame h (nuSel h j 1 1) j
        (sigArbDress h (sqEichU h (nuSel h j 1 1) j
          * sqEichU h (nuSel h j 1 1) j)) i)) = 1) ∧
    (SqU5.toU4L (sqRelWord fun i => dblFourHom h j (sqArbFrame h (nuSel h j 1 1) j
        (sigArbDress h (sqEichU h (nuSel h j 1 1) j)) i)) = 1 ∧
      SqU5.toU4R (sqRelWord fun i => dblFourHom h j (sqArbFrame h (nuSel h j 1 1) j
        (sigArbDress h (sqEichU h (nuSel h j 1 1) j)) i)) = 1) := by
  rw [sqRelWord_dblFrame_sigTriv, sqRelWord_dblFrame_sigUsq, sqRelWord_dblFrame_sigU]
  refine ⟨⟨map_one _, map_one _⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

end DoublePoint

/-! ## 8 Wave 55's own row `nuSel h j 0 1`, widened to every handle count

`GradedFourRow` solved the uncleared-`v` row at `h = 1` only, and named the general handle count
as what it did not do.  The shared machinery of §2 widens it for free: the same two cleared
letters, the same displaced `v`-slot, the same lattice parameters `(0, 1, 0, 0, 1, 0, 0, 1)` and
therefore the **committed** soundness lemmas `rowFourWit_lamThree_even` and
`rowFourWit_lamThreePlus_even` verbatim, now at arbitrary `h` and arbitrary live handle `j`. -/

section WideRow

variable {h : ℕ} {j : Fin h}

/-- The live handle block of wave 55's marking is trivial, at every pivot residue. -/
theorem commP_rowWideGen : ∀ c : gr3R, commP rowFourU (rowFourVGen c) = 1 := by decide

theorem commP_rowWide : commP rowFourU rowFourV = 1 := by decide

variable (h j) in
/-- **Wave 55's marking at every handle count**: the `u`-slot is the cleared letter (the row
clears it), the `v`-slot is the cleared letter **right**-displaced by the pivot. -/
def rowWideMark (c : gr3R) : Fin (sqRank h) → SqU5 gr3R :=
  mirWit h j rowFourU (rowFourVGen c) 1

variable (h j) in
/-- Wave 55's witness at every handle count. -/
def rowWideWit (v : SqU5 gr3R) : Fin (sqRank h) → SqU5 gr3R := mirWit h j rowFourU rowFourV v

/-- ⭐⭐ **The ten-row solve of `GradedFourRow`, at every handle count.** -/
theorem sqRelWord_rowWideMark : ∀ c : gr3R, sqRelWord (rowWideMark h j c) = 1 :=
  fun c => sqRelWord_mirWit_triv (commP_rowWideGen c)

theorem sqRelWord_rowWideWit_triv : sqRelWord (rowWideWit h j 1) = 1 := by
  rw [rowWideWit, sqRelWord_mirWit_triv commP_rowWide]

theorem sqRelWord_rowWideWit (v : SqU5 gr3R) :
    sqRelWord (rowWideWit h j v) = sqWord (sigFourMark gr3R * v) sigFourX sigFourY := by
  rw [rowWideWit, sqRelWord_mirWit commP_rowWide]

theorem sqRelWord_rowWideWit_V : sqRelWord (rowWideWit h j rowFourV) = liftC 1 := by
  rw [sqRelWord_rowWideWit]; decide

theorem sqRelWord_rowWideWit_Vsq :
    sqRelWord (rowWideWit h j (rowFourV * rowFourV)) = liftC 2 := by
  rw [sqRelWord_rowWideWit]; decide

theorem sqRelWord_rowWideWit_Vsq_complete :
    sqRelWord (sigLift j (rowWideWit h j (rowFourV * rowFourV)) 1 1 (liftC 7) 1 1) = 1 := by
  rw [sqRelWord_sigLift SqU5.isGaThree_one SqU5.isGaFour_one (liftC_isGaFour 7)
    SqU5.isGaThree_one SqU5.isGaThree_one, sqRelWord_rowWideWit_Vsq, liftC_mul_liftC]
  refine Eq.trans (congrArg liftC ?_) liftC_zero
  simp only [rowWideWit, mirWit_one, mirWit_handleU, mirWit_handleV, SqU5.one_h, SqU5.one_i,
    SqU5.one_j, rowFourU, rowFourV, sigFourX]
  decide

@[simp] theorem rowWideMark_zero (c : gr3R) : rowWideMark h j c 0 = sigFourMark gr3R := by
  rw [rowWideMark, mirWit_zero, mul_one]

@[simp] theorem rowWideMark_one (c : gr3R) : rowWideMark h j c 1 = sigFourX := by
  rw [rowWideMark, mirWit_one]

@[simp] theorem rowWideMark_two (c : gr3R) : rowWideMark h j c 2 = sigFourY := by
  rw [rowWideMark, mirWit_two]

@[simp] theorem rowWideMark_handleU (c : gr3R) :
    rowWideMark h j c (sqHandleIdxU j) = rowFourU := by rw [rowWideMark, mirWit_handleU]

@[simp] theorem rowWideMark_handleV (c : gr3R) :
    rowWideMark h j c (sqHandleIdxV j) = rowFourVGen c := by rw [rowWideMark, mirWit_handleV]

theorem rowWideMark_handleU_ne (c : gr3R) {j' : Fin h} (hne : j' ≠ j) :
    rowWideMark h j c (sqHandleIdxU j') = 1 := by rw [rowWideMark, mirWit_handleU_ne hne]

theorem rowWideMark_handleV_ne (c : gr3R) {j' : Fin h} (hne : j' ≠ j) :
    rowWideMark h j c (sqHandleIdxV j') = 1 := by rw [rowWideMark, mirWit_handleV_ne hne]

variable (h j) in
/-- ⭐⭐ **Wave 55's test hom at every handle count.** -/
noncomputable def rowWideHom : ContinuousMonoidHom (DSq h : Type) (SqU5 gr3R) :=
  sqU5Hom gr3R_card h (rowWideMark h j (gr3Pi sqPivotExp))
    (sqRelWord_rowWideMark (gr3Pi sqPivotExp))

@[simp] theorem rowWideHom_gen (i : Fin (sqRank h)) :
    rowWideHom h j (sqGen h i) = rowWideMark h j (gr3Pi sqPivotExp) i := sqU5Hom_gen _ _ _ i

@[simp] theorem rowWideHom_sigma : rowWideHom h j (dsqSigma h) = sigFourMark gr3R := by
  rw [dsqSigma, rowWideHom_gen, rowWideMark_zero]

@[simp] theorem rowWideHom_x0 : rowWideHom h j (dsqX0 h) = sigFourX := by
  rw [dsqX0, rowWideHom_gen, rowWideMark_one]

@[simp] theorem rowWideHom_x1 : rowWideHom h j (dsqX1 h) = sigFourY := by
  rw [dsqX1, rowWideHom_gen, rowWideMark_two]

@[simp] theorem rowWideHom_handleU : rowWideHom h j (sqGen h (sqHandleIdxU j)) = rowFourU := by
  rw [rowWideHom_gen, rowWideMark_handleU]

@[simp] theorem rowWideHom_handleV :
    rowWideHom h j (sqGen h (sqHandleIdxV j)) = rowFourVGen (gr3Pi sqPivotExp) := by
  rw [rowWideHom_gen, rowWideMark_handleV]

theorem rowWideHom_handle_ne {j' : Fin h} (hne : j' ≠ j) :
    rowWideHom h j (sqGen h (sqHandleIdxU j')) = 1 ∧
      rowWideHom h j (sqGen h (sqHandleIdxV j')) = 1 :=
  ⟨by rw [rowWideHom_gen, rowWideMark_handleU_ne _ hne],
    by rw [rowWideHom_gen, rowWideMark_handleV_ne _ hne]⟩

theorem rowWideHom_sqPivot : rowWideHom h j (sqPivot h) = rowPivotVal (gr3Pi sqPivotExp) :=
  mirHom_sqPivot rowWideHom_sigma rowWideHom_x0

theorem nuSelWide_handleU : nuSel h j 0 1 (sqGen h (sqHandleIdxU j)) = 1 := by
  rw [nuSel_handleU, ofAdd_zero]

theorem rowWideHom_sqEichU : rowWideHom h j (sqEichU h (nuSel h j 0 1) j) = rowFourU := by
  rw [sqEichU_of_cleared nuSelWide_handleU, rowWideHom_handleU]

theorem rowWideHom_sqEichV : rowWideHom h j (sqEichV h (nuSel h j 0 1) j) = rowFourV := by
  rw [sqEichV, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_gr5, nuSel_handleV,
    toAdd_ofAdd, zpowZtwo_one_exp, rowWideHom_sqPivot, rowWideHom_handleV, rowFourV_eq]

theorem rowWideHom_b (x : (DSq h : Type)) :
    (rowWideHom h j x).b = gr3Pi (toAdd (nuSel h j 0 1 x)) :=
  mirHom_b (by rw [rowWideHom_sigma]; rfl) (by rw [rowWideHom_x0]; rfl)
    (by rw [rowWideHom_x1]; rfl) (by rw [rowWideHom_handleU, map_zero]; rfl)
    (by rw [rowWideHom_handleV, map_one]; rfl)
    (fun j' hj' => by rw [(rowWideHom_handle_ne hj').1, (rowWideHom_handle_ne hj').2]; exact
      ⟨rfl, rfl⟩) x

theorem rowWideHom_b_eq_zero {g : (DSq h : Type)} (hg : nuSel h j 0 1 g = 1) :
    (rowWideHom h j g).b = 0 := by
  rw [rowWideHom_b, hg, toAdd_one, map_zero]

theorem rowWideHom_sqArbFrame (g : (DSq h : Type)) :
    (fun i => rowWideHom h j (sqArbFrame h (nuSel h j 0 1) j (sigArbDress h g) i))
      = rowWideWit h j (rowWideHom h j g) := by
  rw [rowWideWit]
  exact mirHom_sqArbFrame rowWideHom_sigma rowWideHom_x0 rowWideHom_x1 rowWideHom_sqEichU
    rowWideHom_sqEichV (fun j' hj' => rowWideHom_handle_ne hj') g

theorem rowWideMark_le_rowFrameSub (c : gr3R) :
    Subgroup.closure (Set.range (rowWideMark h j c)) ≤ rowFrameSub gr3R := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [rowWideMark_zero]
    exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩
  · rw [rowWideMark_one]
    exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩
  · rw [rowWideMark_two]
    exact ⟨rfl, rfl, 2, by show (4 : gr3R) = 2 * 2; decide⟩
  · by_cases hjj : j' = j
    · subst hjj
      rw [rowWideMark_handleU]
      exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩
    · rw [rowWideMark_handleU_ne _ hjj]
      exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩
  · by_cases hjj : j' = j
    · subst hjj
      rw [rowWideMark_handleV]
      exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩
    · rw [rowWideMark_handleV_ne _ hjj]
      exact ⟨rfl, rfl, 0, by show (0 : gr3R) = 2 * 0; ring⟩

theorem rowWide_commutator_le (c : gr3R) :
    rowGaTwoOf (Subgroup.closure (Set.range (rowWideMark h j c))) ≤ rowGaTwoSub gr3R := by
  rw [rowGaTwoOf, Subgroup.closure_le]
  rintro z ⟨p, hp, q, hq, rfl⟩
  exact commP_mem_rowGaTwoSub (rowWideMark_le_rowFrameSub c hp)
    (rowWideMark_le_rowFrameSub c hq)

theorem rowWide_gaTwo_even {c : gr3R} {z : SqU5 gr3R}
    (hz : z ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowWideMark h j c)))) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) := by
  obtain ⟨-, -, -, -, -, -, hh, hi⟩ := rowWide_commutator_le c hz
  exact ⟨⟨0, by rw [hh]; ring⟩, hi⟩

/-- ⭐⭐ **Wave 55's forcing at every handle count**, against the committed achievable lattice -
with the committed evenness lemma `rowFourWit_lamThree_even` reused verbatim, because the
lattice parameters do not depend on `h`. -/
theorem rowWideWit_sigma_forced {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hvb : v.b = 0) (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : selLamThree 0 1 0 0 1 0 0 1 P Q R z₃)
    (l₄ : selLamThree 0 1 0 0 1 0 0 1 P Q R z₄)
    (hkill : sqRelWord (sigLift j (rowWideWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  mirWit_sigma_forced commP_rowWide hvb hz₀ hw₁ hw₂ hz₃ hz₄
    (rowFourWit_lamThree_even l₃) (rowFourWit_lamThree_even l₄) hkill

theorem rowWideWit_sigma_forced_gaTwo {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hvb : v.b = 0) (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowWideMark h j c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowWideMark h j c))))
    (hkill : sqRelWord (sigLift j (rowWideWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 :=
  mirWit_sigma_forced commP_rowWide hvb hz₀ hw₁ hw₂ hz₃ hz₄
    (rowWide_gaTwo_even l₃) (rowWide_gaTwo_even l₄) hkill

theorem nuLam_wideEichV : nuLam h (sqEichV h (nuSel h j 0 1) j) = 1 :=
  Multiplicative.toAdd.injective (by rw [toAdd_nuLam_sqEichV, toAdd_one])

theorem nu_wideEichV : nuSel h j 0 1 (sqEichV h (nuSel h j 0 1) j) = 1 :=
  Multiplicative.toAdd.injective (by rw [toAdd_nu_sqEichV nuSel_sigma nuSel_x0, toAdd_one])

theorem nuLam_wideEichV_sq :
    nuLam h (sqEichV h (nuSel h j 0 1) j * sqEichV h (nuSel h j 0 1) j) = 1 := by
  rw [map_mul, nuLam_wideEichV, one_mul]

theorem nu_wideEichV_sq :
    nuSel h j 0 1 (sqEichV h (nuSel h j 0 1) j * sqEichV h (nuSel h j 0 1) j) = 1 := by
  rw [map_mul, nu_wideEichV, one_mul]

/-- ⭐⭐ Wave 55's non-vacuity, at every handle count. -/
theorem rowWide_forcing_nonvacuous :
    nuLam h (sqEichV h (nuSel h j 0 1) j) = 1 ∧
      nuSel h j 0 1 (sqEichV h (nuSel h j 0 1) j) = 1 ∧
      selPar (rowWideHom h j (sqEichV h (nuSel h j 0 1) j)).a = 1 :=
  ⟨nuLam_wideEichV, nu_wideEichV, by rw [rowWideHom_sqEichV]; exact rowFourV_chiA⟩

theorem nuLam_sigArbDress_wideV (i : Fin (sqRank h)) :
    nuLam h (sigArbDress h (sqEichV h (nuSel h j 0 1) j) i) = 1 :=
  nuLam_sigArbDress nuLam_wideEichV i

theorem nu_sigArbDress_wideV (i : Fin (sqRank h)) :
    nuSel h j 0 1 (sigArbDress h (sqEichV h (nuSel h j 0 1) j) i) = 1 :=
  nu_sigArbDress nu_wideEichV i

theorem nuLam_sigArbDress_wideVsq (i : Fin (sqRank h)) :
    nuLam h (sigArbDress h
      (sqEichV h (nuSel h j 0 1) j * sqEichV h (nuSel h j 0 1) j) i) = 1 :=
  nuLam_sigArbDress nuLam_wideEichV_sq i

theorem nu_sigArbDress_wideVsq (i : Fin (sqRank h)) :
    nuSel h j 0 1 (sigArbDress h
      (sqEichV h (nuSel h j 0 1) j * sqEichV h (nuSel h j 0 1) j) i) = 1 :=
  nu_sigArbDress nu_wideEichV_sq i

theorem sqRelWord_wideFrame_sigTriv :
    sqRelWord (fun i =>
      rowWideHom h j (sqArbFrame h (nuSel h j 0 1) j (sigArbDress h 1) i)) = 1 := by
  rw [rowWideHom_sqArbFrame, map_one]
  exact sqRelWord_rowWideWit_triv

theorem sqRelWord_wideFrame_sigVsq :
    sqRelWord (fun i => rowWideHom h j (sqArbFrame h (nuSel h j 0 1) j
      (sigArbDress h (sqEichV h (nuSel h j 0 1) j * sqEichV h (nuSel h j 0 1) j)) i))
      = liftC 2 := by
  rw [rowWideHom_sqArbFrame, map_mul, rowWideHom_sqEichV]
  exact sqRelWord_rowWideWit_Vsq

theorem sqRelWord_wideFrame_sigV :
    sqRelWord (fun i => rowWideHom h j (sqArbFrame h (nuSel h j 0 1) j
      (sigArbDress h (sqEichV h (nuSel h j 0 1) j)) i)) = liftC 1 := by
  rw [rowWideHom_sqArbFrame, rowWideHom_sqEichV]
  exact sqRelWord_rowWideWit_V

theorem sqRelWord_wideFrame_sigV_ne_one {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : selLamThree 0 1 0 0 1 0 0 1 P Q R z₃)
    (l₄ : selLamThree 0 1 0 0 1 0 0 1 P Q R z₄) :
    sqRelWord (sigLift j (fun i => rowWideHom h j (sqArbFrame h (nuSel h j 0 1) j
      (sigArbDress h (sqEichV h (nuSel h j 0 1) j)) i)) z₀ w₁ w₂ z₃ z₄) ≠ 1 := by
  rw [rowWideHom_sqArbFrame, rowWideHom_sqEichV]
  intro hc
  have hpar := rowWideWit_sigma_forced (v := rowFourV) (by decide) hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄ hc
  rw [show (rowFourV.a : gr3R) = 1 from rfl] at hpar
  exact absurd hpar (by decide)

/-- ⭐⭐ **The class-four selection bit on `sqArbFrame` at wave 55's row, at every handle
count.** -/
theorem sqArbFrame_sigma_bit_row_wide {g : (DSq h : Type)} (hg : nuSel h j 0 1 g = 1) :
    selPar ((sqRelWord fun i =>
        rowWideHom h j (sqArbFrame h (nuSel h j 0 1) j (sigArbDress h g) i)).j)
      = selPar (rowWideHom h j g).a := by
  rw [rowWideHom_sqArbFrame g, rowWideWit]
  exact mirWit_bit commP_rowWide (rowWideHom_b_eq_zero hg)

/-- ⭐⭐ **`GradedFourRow.sqArbFrame_sigma_forced_row` at every handle count.** -/
theorem sqArbFrame_sigma_forced_row_wide {g : (DSq h : Type)} (hg : nuSel h j 0 1 g = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : selLamThree 0 1 0 0 1 0 0 1 P Q R z₃)
    (l₄ : selLamThree 0 1 0 0 1 0 0 1 P Q R z₄)
    (hkill : sqRelWord (sigLift j
      (fun i => rowWideHom h j (sqArbFrame h (nuSel h j 0 1) j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (rowWideHom h j g).a = 0 := by
  rw [rowWideHom_sqArbFrame g] at hkill
  exact rowWideWit_sigma_forced (rowWideHom_b_eq_zero hg) hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄ hkill

/-- ⭐⭐ **…and at the `γ₂` level.** -/
theorem sqArbFrame_sigma_forced_row_wide_gaTwo {g : (DSq h : Type)} (hg : nuSel h j 0 1 g = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowWideMark h j c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowWideMark h j c))))
    (hkill : sqRelWord (sigLift j
      (fun i => rowWideHom h j (sqArbFrame h (nuSel h j 0 1) j (sigArbDress h g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (rowWideHom h j g).a = 0 := by
  rw [rowWideHom_sqArbFrame g] at hkill
  exact rowWideWit_sigma_forced_gaTwo (rowWideHom_b_eq_zero hg) hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄ hkill

theorem rowWide_escape_separates :
    ((∀ i, nuLam h (sigArbDress h
        (sqEichV h (nuSel h j 0 1) j * sqEichV h (nuSel h j 0 1) j) i) = 1) ∧
      ∀ i, nuSel h j 0 1 (sigArbDress h
        (sqEichV h (nuSel h j 0 1) j * sqEichV h (nuSel h j 0 1) j) i) = 1) ∧
    ((∀ i, nuLam h (sigArbDress h (sqEichV h (nuSel h j 0 1) j) i) = 1) ∧
      ∀ i, nuSel h j 0 1 (sigArbDress h (sqEichV h (nuSel h j 0 1) j) i) = 1) ∧
    sqRelWord (fun i => rowWideHom h j (sqArbFrame h (nuSel h j 0 1) j
      (sigArbDress h (sqEichV h (nuSel h j 0 1) j * sqEichV h (nuSel h j 0 1) j)) i))
      = liftC 2 ∧
    sqRelWord (fun i => rowWideHom h j (sqArbFrame h (nuSel h j 0 1) j
      (sigArbDress h (sqEichV h (nuSel h j 0 1) j)) i)) = liftC 1 :=
  ⟨⟨nuLam_sigArbDress_wideVsq, nu_sigArbDress_wideVsq⟩,
    ⟨nuLam_sigArbDress_wideV, nu_sigArbDress_wideV⟩,
    sqRelWord_wideFrame_sigVsq, sqRelWord_wideFrame_sigV⟩

end WideRow





/-! ## 9 Axiom pins

Committed prints for every public declaration of this file. -/

section AxiomPins

#print axioms mirTuple
#print axioms mirTuple_zero
#print axioms mirTuple_one
#print axioms mirTuple_two
#print axioms mirTuple_handleU
#print axioms mirTuple_handleV
#print axioms mirTuple_handleU_ne
#print axioms mirTuple_handleV_ne
#print axioms sqRelWord_mirTuple
#print axioms sqRelWord_mirTuple_e
#print axioms sqRelWord_e_displace_two
#print axioms sqRelWord_e_displace_left
#print axioms sqRelWord_e_displace_right
#print axioms chiA_row_forced
#print axioms chiA_mirror_forced
#print axioms chiA_double_forced
#print axioms mirWit
#print axioms mirWit_zero
#print axioms mirWit_one
#print axioms mirWit_two
#print axioms mirWit_handleU
#print axioms mirWit_handleV
#print axioms mirWit_handleU_ne
#print axioms mirWit_handleV_ne
#print axioms mirWit_eq_dress
#print axioms sqRelWord_mirWit
#print axioms sqRelWord_mirWit_triv
#print axioms mirWit_bit
#print axioms mirWit_increment_even
#print axioms mirWit_sigma_forced
#print axioms mirHom_sqPivot
#print axioms nuSel_handleU_ne
#print axioms nuSel_handleV_ne
#print axioms mirHom_b
#print axioms mirHom_sqArbFrame
#print axioms mirFourU
#print axioms mirFourV
#print axioms mirFour_letters_swapped
#print axioms mirFourUGen
#print axioms mirFourUGen_eq
#print axioms mirFourU_eq
#print axioms commP_mirFourUGen
#print axioms commP_mirFour
#print axioms mirFourMark
#print axioms sqRelWord_mirFourMark
#print axioms mirFourWit
#print axioms sqRelWord_mirFourWit_triv
#print axioms mirFourV_chiA
#print axioms mirFourU_chiA
#print axioms mirFourU_sq
#print axioms sqRelWord_mirFourWit
#print axioms sqRelWord_mirFourWit_U
#print axioms sqRelWord_mirFourWit_Usq
#print axioms sqRelWord_mirFourWit_V
#print axioms sqRelWord_mirFourWit_Usq_complete
#print axioms mirFourWit_class_three_blind
#print axioms mirFourMark_zero
#print axioms mirFourMark_one
#print axioms mirFourMark_two
#print axioms mirFourMark_handleU
#print axioms mirFourMark_handleV
#print axioms mirFourMark_handleU_ne
#print axioms mirFourMark_handleV_ne
#print axioms mirFourHom
#print axioms mirFourHom_gen
#print axioms mirFourHom_sigma
#print axioms mirFourHom_x0
#print axioms mirFourHom_x1
#print axioms mirFourHom_handleU
#print axioms mirFourHom_handleV
#print axioms mirFourHom_handle_ne
#print axioms mirFourHom_sqPivot
#print axioms nuSelMir_handleU
#print axioms nuSelMir_handleV
#print axioms mirFourHom_sqEichV
#print axioms mirFourHom_sqEichU
#print axioms mirFourHom_b
#print axioms mirFourHom_b_eq_zero
#print axioms mirFourHom_sqArbFrame
#print axioms mirFourWit_lamThree_even
#print axioms mirFourWit_commP_zero_two
#print axioms mirFourWit_commP_two_handleU
#print axioms mirFourWit_commP_two_handleV
#print axioms mirFourWit_lamThreePlus_even
#print axioms mirFourMark_le_rowFrameSub
#print axioms mirFour_commutator_le
#print axioms mirFour_gaTwo_even
#print axioms mirFourHom_mem_closure
#print axioms mirFourWit_sigma_forced
#print axioms mirFourWit_sigma_forced_gaTwo
#print axioms nuLam_mirEichU
#print axioms nu_mirEichU
#print axioms nuLam_mirEichU_sq
#print axioms nu_mirEichU_sq
#print axioms mirFour_forcing_nonvacuous
#print axioms nuLam_sigArbDress_mirU
#print axioms nu_sigArbDress_mirU
#print axioms nuLam_sigArbDress_mirUsq
#print axioms nu_sigArbDress_mirUsq
#print axioms sqRelWord_mirFrame_sigTriv
#print axioms sqRelWord_mirFrame_sigUsq
#print axioms sqRelWord_mirFrame_sigU
#print axioms sqRelWord_mirFrame_sigUsq_complete
#print axioms sqRelWord_mirFrame_sigU_ne_one
#print axioms sqRelWord_mirFrame_sigU_ne_one_gaTwo
#print axioms sqArbFrame_sigma_bit_mirror
#print axioms sqArbFrame_sigma_forced_mirror
#print axioms sqArbFrame_sigma_forced_mirror_gaTwo
#print axioms mirFour_escape_separates
#print axioms mirFrame_class_three_blind
#print axioms dblFour_letters_equal
#print axioms commP_dblFourGen
#print axioms commP_dblFour
#print axioms dblFourMark
#print axioms dblFourWit
#print axioms sqRelWord_dblFourMark
#print axioms sqRelWord_dblFourWit_triv
#print axioms sqRelWord_dblFourWit
#print axioms sqRelWord_dblFourWit_U
#print axioms sqRelWord_dblFourWit_Usq
#print axioms sqRelWord_dblFourWit_Usq_complete
#print axioms dblFourWit_class_three_blind
#print axioms dblFourMark_zero
#print axioms dblFourMark_one
#print axioms dblFourMark_two
#print axioms dblFourMark_handleU
#print axioms dblFourMark_handleV
#print axioms dblFourMark_handleU_ne
#print axioms dblFourMark_handleV_ne
#print axioms dblFourHom
#print axioms dblFourHom_gen
#print axioms dblFourHom_sigma
#print axioms dblFourHom_x0
#print axioms dblFourHom_x1
#print axioms dblFourHom_handleU
#print axioms dblFourHom_handleV
#print axioms dblFourHom_handle_ne
#print axioms dblFourHom_sqPivot
#print axioms dblFourHom_sqEichU
#print axioms dblFourHom_sqEichV
#print axioms dblFourHom_b
#print axioms dblFourHom_b_eq_zero
#print axioms dblFourHom_sqArbFrame
#print axioms dblFourWit_lamThree_even
#print axioms dblFourWit_commP_zero_two
#print axioms dblFourWit_commP_two_handleU
#print axioms dblFourWit_commP_two_handleV
#print axioms dblFourWit_lamThreePlus_even
#print axioms dblFourMark_le_rowFrameSub
#print axioms dblFour_commutator_le
#print axioms dblFour_gaTwo_even
#print axioms dblFourHom_mem_closure
#print axioms dblFourWit_sigma_forced
#print axioms dblFourWit_sigma_forced_gaTwo
#print axioms nuLam_dblEichU
#print axioms nu_dblEichU
#print axioms nuLam_dblEichV
#print axioms nu_dblEichV
#print axioms nuLam_dblEichU_sq
#print axioms nu_dblEichU_sq
#print axioms dblFour_forcing_nonvacuous
#print axioms nuLam_sigArbDress_dblU
#print axioms nu_sigArbDress_dblU
#print axioms nuLam_sigArbDress_dblUsq
#print axioms nu_sigArbDress_dblUsq
#print axioms sqRelWord_dblFrame_sigTriv
#print axioms sqRelWord_dblFrame_sigUsq
#print axioms sqRelWord_dblFrame_sigU
#print axioms sqRelWord_dblFrame_sigUsq_complete
#print axioms sqRelWord_dblFrame_sigU_ne_one
#print axioms sqRelWord_dblFrame_sigU_ne_one_gaTwo
#print axioms sqArbFrame_sigma_bit_double
#print axioms sqArbFrame_sigma_forced_double
#print axioms sqArbFrame_sigma_forced_double_gaTwo
#print axioms dblFour_escape_separates
#print axioms dblFrame_class_three_blind
#print axioms commP_rowWideGen
#print axioms commP_rowWide
#print axioms rowWideMark
#print axioms rowWideWit
#print axioms sqRelWord_rowWideMark
#print axioms sqRelWord_rowWideWit_triv
#print axioms sqRelWord_rowWideWit
#print axioms sqRelWord_rowWideWit_V
#print axioms sqRelWord_rowWideWit_Vsq
#print axioms sqRelWord_rowWideWit_Vsq_complete
#print axioms rowWideMark_zero
#print axioms rowWideMark_one
#print axioms rowWideMark_two
#print axioms rowWideMark_handleU
#print axioms rowWideMark_handleV
#print axioms rowWideMark_handleU_ne
#print axioms rowWideMark_handleV_ne
#print axioms rowWideHom
#print axioms rowWideHom_gen
#print axioms rowWideHom_sigma
#print axioms rowWideHom_x0
#print axioms rowWideHom_x1
#print axioms rowWideHom_handleU
#print axioms rowWideHom_handleV
#print axioms rowWideHom_handle_ne
#print axioms rowWideHom_sqPivot
#print axioms nuSelWide_handleU
#print axioms rowWideHom_sqEichU
#print axioms rowWideHom_sqEichV
#print axioms rowWideHom_b
#print axioms rowWideHom_b_eq_zero
#print axioms rowWideHom_sqArbFrame
#print axioms rowWideMark_le_rowFrameSub
#print axioms rowWide_commutator_le
#print axioms rowWide_gaTwo_even
#print axioms rowWideWit_sigma_forced
#print axioms rowWideWit_sigma_forced_gaTwo
#print axioms nuLam_wideEichV
#print axioms nu_wideEichV
#print axioms nuLam_wideEichV_sq
#print axioms nu_wideEichV_sq
#print axioms rowWide_forcing_nonvacuous
#print axioms nuLam_sigArbDress_wideV
#print axioms nu_sigArbDress_wideV
#print axioms nuLam_sigArbDress_wideVsq
#print axioms nu_sigArbDress_wideVsq
#print axioms sqRelWord_wideFrame_sigTriv
#print axioms sqRelWord_wideFrame_sigVsq
#print axioms sqRelWord_wideFrame_sigV
#print axioms sqRelWord_wideFrame_sigV_ne_one
#print axioms sqArbFrame_sigma_bit_row_wide
#print axioms sqArbFrame_sigma_forced_row_wide
#print axioms sqArbFrame_sigma_forced_row_wide_gaTwo
#print axioms rowWide_escape_separates

end AxiomPins

end SqCore

end Dyadic

end GQ2

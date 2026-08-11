/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedBlockFrame

/-!
# W63-SECOND: the second block reading, and what the pair of readings pins

`docs/dyadic/w61-block-note.md` section 6.3 left two items, and `GradedBlockFrame`'s closing
paragraph says both are untouched: the `(5,6)`-row variant of the block equation, and a **second
block reading** `s_34 x_45 - s_45 x_34` at the `(3,5)` row, "a SECOND alternating form on
`D_sq h` built from a different pair of columns, and whether the two together pin more than
either alone is not measured anywhere".

This file builds the second reading and answers the question.  The answer has three parts, and
the middle one is a negative.

## ⭐⭐ Headline 1: the block equation, handle-count forcing and minor selection transpose verbatim

`SqU6.blockReadCD s x = s.c * x.d - s.d * x.c`.  The `(3,5)` row of the core word has the same
shape as the `(4,6)` row (`SqU6.sqWord_h`), so the same argument gives the same three theorems:
⭐⭐ `SqU6.selPar_handleWord_h_of_relator` (the second block equation: the parity of the handle
block's `(3,5)` coordinate is a closed form in four entries of the two core slots, at every
relator-killing marking over `gr3R`, at every handle count, at **every** sigma slot, with no
gauge); ⭐⭐ `SqU6.pos_of_blockReadCD_odd`; ⭐ `SqU6.exists_handle_minorCD_odd`.  At the hom
level `blockParCD` is an alternating bi-additive form that kills commutators and the torsion
letter, ⭐⭐ `blockParCD_relator_frame` is a second symplectic identity, ⭐⭐⭐
`blockParCD_handleFree` kills it on every pair at `h = 0`, and ⭐⭐
`exists_blockParCD_odd_iff_pos` is the characterisation.  Section 5 adds the dressing-invariance
analogues `SqU6.blockReadCD_gaTwoDress` and `SqU6.blockReadCD_gaThreeDress`.

⚠ **What does NOT transpose, and is not attempted here**, so "everything wave 61 proved holds of
it" would be too strong: `GradedBlockRead.blindCexCore_not_relator_handleFree`, the concrete core
pair at which the `h = 0` exclusion is exhibited to have content (nothing here plays that role
for the CD reading); `SqU6.blockCoupling` and its suite
(`SqU6.sqRelWord_sigFiveDress_o_blockCoupling`, `SqU6.blockCoupling_gaThreeDress`); and
`SqU6.blockChannel_gaThreeDress`, the coupled-channel invariance.  The coupled channel has no CD
analogue anywhere in this file.

⚠ **This is a REFORMULATION of `0 < h`, exactly as wave 62's was, and it is stated as one.**
`exists_blockPar_odd_iff_pos` and `exists_blockParCD_odd_iff_pos` are both equivalences with
`0 < h`, so as handle-count instruments the two readings are the same instrument twice.

## ⭐⭐⭐ Headline 2: but the two forms are INDEPENDENT, and the second fires where the first is dead

`secCexHom`, the witness this file adds, is a continuous homomorphism at every handle count
`h >= 1` and every handle at which

* ⭐⭐⭐ `blockParCD_secCexHom`: the **second** form is odd on the core pair, and
* ⭐⭐⭐ `blockPar_secCexHom_eq_zero`: the **first** form is `0` on **every pair of elements of
  `D_sq h`**.

So the second reading is not a function of the first.  Wave 59's counterexample is the mirror
image (`blockParCD_blockCexHom_eq_zero`: the second form is `0` on every pair there, where the
first is odd), so neither reading is a function of the other, and the pair is a strictly finer
invariant of a homomorphism than either member.

⚠ **What the pair does NOT pin is the handle count.**  Measured, not proved:
`scripts/w63_second/results/pair_second.txt` section K exhibits a relator-killing marking at
`h = 1` on which **both** readings are odd, so `both live => 0 < h` is the sharpest handle-count
statement the pair supports, and each member already gives it.  All four liveness cells are
realized at `h = 1`.

## ⚠ Headline 3: the correction, and it is about the FIRST reading

`GradedBlockFrame`'s Honesty 3 says the two committed class-five witnesses are "block-blind" and
that "the instrument says nothing at either of the two points the class-five lanes actually run
at".  That file computes the first form on two pairs, the core pair and the live handle pair, and
both are even.  But `pos_of_blockPar_odd` quantifies over **all** pairs, and the form is **odd**
elsewhere at both points:

* ⭐⭐ `blockPar_fiveFrameHom_x0_handleU` and `blockPar_fiveFrameHom_x0_handleV`,
* ⭐⭐ `blockPar_stageFrameHom_x0_handleU` and `blockPar_stageFrameHom_x0_handleV`.

The `x0` slot's `(5,6)`-column and the handle letters' `(4,5)`-columns are both odd at both
points.  No committed theorem is wrong: `blockPar_fiveFrameHom` and its three companions are
true as stated, and what the instrument produces at those points (`0 < h`) is free there anyway,
since `fiveFrameHom h j` is indexed by a handle.  What is wrong is the **description**, and a
lane looking for a point with a live block channel does not need to move off either point.

The **second** form, by contrast, is genuinely dead at both: ⭐⭐
`blockParCD_fiveFrameHom_eq_zero` and `blockParCD_stageFrameHom_eq_zero` kill it on **every**
pair of group elements, not on two pairs.

## Also here: the `(5,6)`-row variant

`SqU6.handleWord_i_eq_blockRead_of_relator_e` and `SqU6.selPar_handleWord_i_of_relator_e`: wave
61's block equation proved from the relator's `(5,6)`-row instead of its `(4,5)`-row, the other
cheap item of section 6.3.  It really is one lemma plus one corollary.

## PROVED versus MEASURED

**PROVED** (this file, no `sorry`, no new axiom, no `native_decide`; every `decide` is on
`ZMod 8` or `ZMod 2`): every declaration named above, with the single exception of the three
wave-61 families listed in Headline 1's ⚠ paragraph, which are named there precisely because they
are **not** transposed here.

**MEASURED** (`scripts/w63_second/`, certified outputs in `scripts/w63_second/results/`;
`88` named checks in three scripts, `0` failures, on `scripts/w61_block/blocklib.py` over the
independently certified `U_6(Z/8)` of `scripts/w59_blind5/u6lib.py`):

| measurement | scale | result |
|---|---|---|
| the four class-two rows of the core word have the same shape, over `Z` | symbolic | exact |
| ⚠ the outer flip pairs `(2,4)` with `(3,5)`, NOT `(3,5)` with `(4,6)` | `120` pairs, `20` markings | the two readings lie in different flip-orbits |
| the second block parity law, **exhaustive** on `ZMod 8` | `4194304` points | `0` failures |
| …and its failure without the `(3,4)`-row | `4096` correction terms | `1024` odd |
| the `(5,6)`-row variant, exact witness, **exhaustive** | `16777216` points | `0` failures |
| the block equation at all four rows, honest relators | `225` markings | `0` mismatches |
| the solve's class-two rows characterise the equations | `30000` trials | `0` disagreements |
| the `h = 0` exclusion at the second reading's core pair | `128` exhaustive + `200000` | `0` kills |
| the second pairing's form laws, and bi-additivity exhaustively | `262144` points | `0` failures |
| the `h = 0` death on every pair, exhaustive on the mod-2 data | `10` admissible data | `0` live |
| the four liveness cells over honest relators | `233` markings | all four occur |
| both readings live at `h = 1` | witness | realized |
| the two forms span a `2`-dimensional space | `114` markings | `83` of them |

## Contents

* **1** the second reading, and the `(3,5)` row of the core word;
* **2** ⭐⭐ the second block equation;
* **3** ⭐⭐ the handle-count forcing, and the dressing forcing;
* **4** the `(5,6)`-row variant of wave 61's first block equation;
* **5** soundness: the second channel is below the achievable lattice too;
* **6** the second block pairing at the hom level, and the second symplectic identity;
* **7** ⭐⭐⭐ the `h = 0` death on every pair, and the forcing;
* **8** ⭐⭐⭐ the witness, the characterisation, and the independence of the two forms;
* **9** ⚠ the committed points, and the correction to Honesty 3;
* **10** axiom pins.

## Axiom hygiene

All prints are **std-3** (`propext`, `Classical.choice`, `Quot.sound`) or a subset; no census
axiom is reachable.

## Merge notes

Everything new here carries a distinctive `CD` (the two columns it reads) or `secCex` (the
witness) marker, except the four `SqU6` row lemmas `sqWord_h`, `sqRelWord_h`,
`handleWord_h_of_relator` and the two `_of_relator_e` variants, which are named after the rows
they are about in the committed style.  Reused without redefinition: `SqU6.blockRead`,
`SqU6.selPar_handleWord_i_of_relator`, `SqU6.sqWord_i_eq_blockRead`, `SqU6.sqWord_i`,
`SqU6.sqRelWord_i` from `GradedBlockRead`/`GradedFiveBlind`; `blockPar`, `blockPar_def`,
`blockPar_eq_zero_of_gen_left`, `blockPar_eq_zero_of_gen_right`, `blockPar_swap` from
`GradedBlockFrame`; `SqU6.handleWord_h`, `sqU6BlockH` from `GradedFiveDefect`; `SqU6.mul_c`,
`SqU6.mul_d`, `SqU6.mul_h`, `SqU6.one_c`, `SqU6.one_h`, `SqU6.commP_h`, `SqU6.conjP_*`,
`SqU6.pow_*`, `SqU6.inv_*`, `sqRelWord_c`, `sqRelWord_d`, `handleWord_d`, `fiveTuple` and its
projections, `sqRelWord_fiveTuple`, `sqU6Hom`, `sqU6Hom_gen`, `sqU6Balance`, `sqU6Balance_gen`,
`sigFiveDress` and its projections from `GradedFive`; `abelRow_even` from `GradedSigmaFive`;
`selPar` and its laws from `GradedSelect`; `sqIdx_cases` from `Certificate`; `dsq_hom_ext`,
`sqGen`, `dsqSigma`, `dsqX0`, `dsqX1`, `sqRelWord`, `sqHandleIdxU`, `sqHandleIdxV` from `Cores`;
`fiveWit`, `forceX`, `forceU`, `forceV`, `fiveSigMark` from `GradedFiveForce`; `stageWit`,
`stageX`, `stageU`, `stageV` from `GradedFiveStageFour`; `blindCexMark` and its letters from
`GradedFiveBlind`; `fiveFrameHom` from `GradedFiveFrame`; `stageFrameHom` from
`GradedStageFrame`; `blockCexHom` from `GradedBlockFrame`.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The second reading, and the `(3,5)` row of the core word -/

section SecondRead

variable {R : Type} [CommRing R]

/-- ⭐⭐ **THE SECOND BLOCK READING** `s_34 * x_45 - s_45 * x_34`: the `2 x 2` minor of the sigma
slot against the `x0` slot in the two **middle** abelian columns, one column in from
`SqU6.blockRead`.

`docs/dyadic/w61-block-note.md` section 6.3 asked for it by name.  ⚠ It is **not** the image of
`SqU6.blockRead` under the OUTER FLIP of `U_6`, which pairs the `(1,3)` row with the `(4,6)` row
and the `(2,4)` row with the `(3,5)` row, so this reading is in the flip-orbit the campaign has
never looked at.  ⚠ That is the only symmetry checked, it is MEASURED rather than proved
(`scripts/w63_second/results/derive_second.txt` section 7), and **no claim is made about the
whole symmetry group of `U_6`**.  What makes the reading work is in any case not symmetry but
that all four class-two rows of `sqWord` have the same shape, which section 1 proves directly. -/
def SqU6.blockReadCD (s x : SqU6 R) : R := s.c * x.d - s.d * x.c

theorem SqU6.blockReadCD_def (s x : SqU6 R) : SqU6.blockReadCD s x = s.c * x.d - s.d * x.c := rfl

/-- At a sigma slot with vanishing `(3,4)`- and `(4,5)`-columns the second reading vanishes. -/
theorem SqU6.blockReadCD_eq_zero_of_slot {s x : SqU6 R} (hsc : s.c = 0) (hsd : s.d = 0) :
    SqU6.blockReadCD s x = 0 := by
  simp only [SqU6.blockReadCD, hsc, hsd]
  ring

theorem SqU6.blockReadCD_sigFiveMark (x : SqU6 R) : SqU6.blockReadCD (sigFiveMark R) x = 0 :=
  SqU6.blockReadCD_eq_zero_of_slot rfl rfl

/-- **The third class-two row of the core word**, at an arbitrary sigma slot.  It is the
committed `SqU6.sqWord_i` with the columns `(4,5)`, `(5,6)` and the class-two coordinate `(4,6)`
replaced by `(3,4)`, `(4,5)` and `(3,5)`, and equally the committed `SqU6.sqWord_f` with
`(1,2)`, `(2,3)`, `(1,3)` so replaced.

⚠ The sigma slot does not drop out here either: the pairing `s.c * x.d - s.d * x.c` survives. -/
theorem SqU6.sqWord_h (s x y : SqU6 R) :
    (sqWord s x y).h = -4 * x.h + 2 * y.h
      + (s.c * x.d - s.d * x.c + 10 * (x.c * x.d) - 8 * (x.c * y.d) + y.c * y.d) := by
  simp only [sqWord, SqU6.mul_c, SqU6.mul_h, SqU6.inv_c, SqU6.inv_d, SqU6.inv_h,
    SqU6.conjP_c, SqU6.conjP_d, SqU6.conjP_h, SqU6.pow_c, SqU6.pow_d, SqU6.pow_h,
    SqU6.commP_d, SqU6.commP_h]
  norm_num
  ring

/-- **The `(3,5)` row of the relator**: the core word's plus the block's, with no cross term,
because the handle block's fourth abelian column vanishes. -/
theorem SqU6.sqRelWord_h {h : ℕ} (m : Fin (sqRank h) → SqU6 R) :
    (sqRelWord m).h = (sqWord (m 0) (m 1) (m 2)).h
      + (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).h := by
  rw [sqRelWord, SqU6.mul_h, SqU6.handleWord_d, mul_zero, add_zero]

/-- ⭐ **The relator pins the block's `(3,5)` coordinate**, over any ring, at any handle count
and any handle: it is minus the core word's own `(3,5)` row. -/
theorem SqU6.handleWord_h_of_relator {h : ℕ} {m : Fin (sqRank h) → SqU6 R}
    (hrel : sqRelWord m = 1) :
    (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).h
      = -(sqWord (m 0) (m 1) (m 2)).h := by
  have hz : (0 : R) = (sqWord (m 0) (m 1) (m 2)).h
      + (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).h := by
    rw [← SqU6.sqRelWord_h, hrel, SqU6.one_h]
  linear_combination -hz

/-- ⭐ **The `(3,5)` row of the core word IS the second reading, up to an explicit even
correction** - over any commutative ring, as soon as the `x1` slot's `(3,4)`-column is even.
The exact analogue of `SqU6.sqWord_i_eq_blockRead`. -/
theorem SqU6.sqWord_h_eq_blockReadCD (s x y : SqU6 R) {k : R} (hyc : y.c = 2 * k) :
    (sqWord s x y).h = SqU6.blockReadCD s x
      + 2 * (-2 * x.h + y.h + 5 * (x.c * x.d) - 4 * (x.c * y.d) + k * y.d) := by
  rw [SqU6.sqWord_h, SqU6.blockReadCD, hyc]
  ring

end SecondRead

/-! ## 2 ⭐⭐ The second block equation -/

section SecondEquation

variable {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R}

/-- ⭐⭐ **THE SECOND BLOCK EQUATION, integral form.**  At every relator-killing marking over
`gr3R = ZMod 8`, at every handle count and every handle, at **every** sigma slot and with no
gauge hypothesis anywhere: the handle block's `(3,5)` coordinate is the second reading of the two
core slots, up to a multiple of `2`.

Two of the fifteen relator rows are used and no more: the `(3,5)`-row, through
`SqU6.handleWord_h_of_relator`, and the `(3,4)`-row, which forces the `x1` slot's `(3,4)`-column
even.  The `(4,5)`-row would do the second one's job equally well
(`scripts/w63_second/results/derive_second.txt` section 3). -/
theorem SqU6.handleWord_h_eq_blockReadCD_of_relator (hrel : sqRelWord m = 1) :
    ∃ t : gr3R, (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).h
      = SqU6.blockReadCD (m 0) (m 1) + 2 * t := by
  have hc : -(4 * (m 1).c) + 2 * (m 2).c = 0 := by
    have h0 : (sqRelWord m).c = 0 := by rw [hrel]; rfl
    rw [SqU6.sqRelWord_c] at h0
    linear_combination h0
  obtain ⟨kc, hkc⟩ := abelRow_even _ _ hc
  refine ⟨-(SqU6.blockReadCD (m 0) (m 1))
    - (-2 * (m 1).h + (m 2).h + 5 * ((m 1).c * (m 1).d) - 4 * ((m 1).c * (m 2).d)
        + kc * (m 2).d), ?_⟩
  rw [SqU6.handleWord_h_of_relator hrel, SqU6.sqWord_h_eq_blockReadCD _ _ _ hkc]
  ring

/-- ⭐⭐ **THE SECOND BLOCK EQUATION.**  The parity of the handle block's `(3,5)` coordinate is a
closed form in four entries of the two core slots, at every relator-killing marking over `gr3R`,
at every handle count, at every sigma slot, with no gauge.

⚠ Read this the way wave 61 asked its own equation to be read: it makes the `(3,5)` block
coordinate a **functional of the two core slots**, so the second reading is blind to the handle
letters for exactly the reason the first one is, and this does **not** reopen the handle-letter
question that `SqU6.selPar_sqRelWord_sigFiveDress_o_eq_of_core` closed. -/
theorem SqU6.selPar_handleWord_h_of_relator (hrel : sqRelWord m = 1) :
    selPar (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).h
      = selPar (SqU6.blockReadCD (m 0) (m 1)) := by
  obtain ⟨t, ht⟩ := SqU6.handleWord_h_eq_blockReadCD_of_relator hrel
  rw [ht, selPar_add, selPar_two_mul, add_zero]

/-- An odd second reading forces an **odd** `(3,5)` block coordinate. -/
theorem SqU6.handleWord_h_odd_of_relator (hrel : sqRelWord m = 1)
    (hodd : selPar (SqU6.blockReadCD (m 0) (m 1)) = 1) :
    selPar (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).h = 1 :=
  (SqU6.selPar_handleWord_h_of_relator hrel).trans hodd

end SecondEquation

/-! ## 3 ⭐⭐ The handle-count forcing for the second reading -/

section SecondForcing

private theorem zmodTwo_eq_zero_of_ne_one_cd : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide

/-- ⭐⭐ **At `h = 0` the second reading is forced even.** -/
theorem SqU6.blockReadCD_even_of_relator_handleFree {m : Fin (sqRank 0) → SqU6 gr3R}
    (hrel : sqRelWord m = 1) : ∃ t : gr3R, SqU6.blockReadCD (m 0) (m 1) = 2 * t := by
  obtain ⟨t, ht⟩ := SqU6.handleWord_h_eq_blockReadCD_of_relator hrel
  rw [handleWord_zero, SqU6.one_h] at ht
  exact ⟨-t, by linear_combination -ht⟩

/-- ⭐⭐ **THE SECOND HANDLE-COUNT FORCING.**  A relator-killing marking whose second reading is
odd has a positive handle count.

⚠ By `exists_blockPar_odd_iff_pos` the first reading's datum is already **equivalent** to
`0 < h`, and section 8 proves the same of this one, so this is a second reformulation of the
same fact and not a strengthening of anything. -/
theorem SqU6.pos_of_blockReadCD_odd {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R}
    (hrel : sqRelWord m = 1) (hodd : selPar (SqU6.blockReadCD (m 0) (m 1)) = 1) : 0 < h := by
  rcases Nat.eq_zero_or_pos h with rfl | hp
  · obtain ⟨t, ht⟩ := SqU6.blockReadCD_even_of_relator_handleFree hrel
    rw [ht, selPar_two_mul] at hodd
    exact absurd hodd (by decide)
  · exact hp

/-- ⭐ **…and it is one handle in particular**, whose two letters are independent mod `2` in the
`(3,4)`- and `(4,5)`-columns.  `SqU6.handleWord_h` writes the `(3,5)` block coordinate as
`sqU6BlockH`, a sum of `2 x 2` minors, one per handle. -/
theorem SqU6.exists_handle_minorCD_odd {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R}
    (hrel : sqRelWord m = 1) (hodd : selPar (SqU6.blockReadCD (m 0) (m 1)) = 1) :
    ∃ j : Fin h, selPar ((m (sqHandleIdxU j)).c * (m (sqHandleIdxV j)).d
      - (m (sqHandleIdxV j)).c * (m (sqHandleIdxU j)).d) = 1 := by
  by_contra hcon
  have hall : ∀ j : Fin h, ∃ t : gr3R, (m (sqHandleIdxU j)).c * (m (sqHandleIdxV j)).d
      - (m (sqHandleIdxV j)).c * (m (sqHandleIdxU j)).d = 2 * t := fun j =>
    (selPar_eq_zero_iff _).mp (zmodTwo_eq_zero_of_ne_one_cd _ (not_exists.mp hcon j))
  choose t ht using hall
  have hsum : (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).h
      = 2 * ∑ j, t j := by
    rw [SqU6.handleWord_h, sqU6BlockH, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => ht j
  have hz := SqU6.selPar_handleWord_h_of_relator hrel
  rw [hsum, selPar_two_mul] at hz
  exact absurd (hz.trans hodd) (by decide)

/-- ⭐ **The second forcing in the campaign's usual shape**: a sigma dressing that keeps the
relator killed pairs evenly against the `x0` slot in the two middle abelian columns.

⚠ Its scope is wave 61's: the diagonal dressing `v = m 1` meets the conclusion outright and so
does every `gamma_2`-dressing, so it bites only on abelian dressings. -/
theorem SqU6.selPar_blockReadCD_dress_of_relator {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R}
    {v : SqU6 gr3R} (hrel : sqRelWord m = 1) (hrel' : sqRelWord (sigFiveDress m v) = 1) :
    selPar (v.c * (m 1).d - v.d * (m 1).c) = 0 := by
  have hU : ∀ j : Fin h, sigFiveDress m v (sqHandleIdxU j) = m (sqHandleIdxU j) := fun j =>
    sigFiveDress_handleU j
  have hV : ∀ j : Fin h, sigFiveDress m v (sqHandleIdxV j) = m (sqHandleIdxV j) := fun j =>
    sigFiveDress_handleV j
  have e2 := SqU6.selPar_handleWord_h_of_relator hrel'
  rw [funext hU, funext hV, sigFiveDress_zero, sigFiveDress_one,
    SqU6.selPar_handleWord_h_of_relator hrel] at e2
  have hsplit : SqU6.blockReadCD (m 0 * v) (m 1)
      = SqU6.blockReadCD (m 0) (m 1) + (v.c * (m 1).d - v.d * (m 1).c) := by
    simp only [SqU6.blockReadCD, SqU6.mul_c, SqU6.mul_d]
    ring
  rw [hsplit, selPar_add] at e2
  linear_combination -e2

end SecondForcing

/-! ## 4 The `(5,6)`-row variant of wave 61's first block equation -/

section RowVariant

variable {R : Type} [CommRing R]

/-- ⭐ **`SqU6.sqWord_i_eq_blockRead` from the other abelian row.**  The committed lemma forces
the `x1` slot's `(4,5)`-column even, from the relator's `(4,5)`-row; this one forces its
`(5,6)`-column even instead.  `docs/dyadic/w61-block-note.md` section 6.3 item 1, priced at one
line, and one line is what it is. -/
theorem SqU6.sqWord_i_eq_blockRead_of_e (s x y : SqU6 R) {k : R} (hye : y.e = 2 * k) :
    (sqWord s x y).i = SqU6.blockRead s x
      + 2 * (-2 * x.i + y.i + 5 * (x.d * x.e) - 8 * (x.d * k) + k * y.d) := by
  rw [SqU6.sqWord_i, SqU6.blockRead, hye]
  ring

end RowVariant

section RowVariantRel

variable {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R}

/-- Wave 61's block equation, proved from the relator's `(5,6)`-row instead of its
`(4,5)`-row. -/
theorem SqU6.handleWord_i_eq_blockRead_of_relator_e (hrel : sqRelWord m = 1) :
    ∃ t : gr3R, (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).i
      = SqU6.blockRead (m 0) (m 1) + 2 * t := by
  have he : -(4 * (m 1).e) + 2 * (m 2).e = 0 := by
    have h0 : (sqRelWord m).e = 0 := by rw [hrel]; rfl
    rw [SqU6.sqRelWord_e] at h0
    linear_combination h0
  obtain ⟨ke, hke⟩ := abelRow_even _ _ he
  refine ⟨-(SqU6.blockRead (m 0) (m 1))
    - (-2 * (m 1).i + (m 2).i + 5 * ((m 1).d * (m 1).e) - 8 * ((m 1).d * ke)
        + ke * (m 2).d), ?_⟩
  rw [SqU6.handleWord_i_of_relator hrel, SqU6.sqWord_i_eq_blockRead_of_e _ _ _ hke]
  ring

theorem SqU6.selPar_handleWord_i_of_relator_e (hrel : sqRelWord m = 1) :
    selPar (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).i
      = selPar (SqU6.blockRead (m 0) (m 1)) := by
  obtain ⟨t, ht⟩ := SqU6.handleWord_i_eq_blockRead_of_relator_e hrel
  rw [ht, selPar_add, selPar_two_mul, add_zero]

end RowVariantRel

/-! ## 5 Soundness: the second channel is below the achievable lattice too -/

section BelowLattice

variable {R : Type} [CommRing R]

/-- **A `gamma_2`-dressing of either core slot cannot move the second reading**, for wave 61's
structural reason: every `gamma_2`-element has vanishing abelian columns and the reading is
built from two of them. -/
theorem SqU6.blockReadCD_gaTwoDress (s x z w : SqU6 R) (hzc : z.c = 0) (hzd : z.d = 0)
    (hwc : w.c = 0) (hwd : w.d = 0) :
    SqU6.blockReadCD (s * z) (x * w) = SqU6.blockReadCD s x := by
  simp only [SqU6.blockReadCD, SqU6.mul_c, SqU6.mul_d, hzc, hzd, hwc, hwd]
  ring

theorem SqU6.blockReadCD_gaThreeDress (s x z w : SqU6 R) (hz : z.IsGaThree) (hw : w.IsGaThree) :
    SqU6.blockReadCD (s * z) (x * w) = SqU6.blockReadCD s x :=
  SqU6.blockReadCD_gaTwoDress s x z w hz.2.2.1 hz.2.2.2.1 hw.2.2.1 hw.2.2.2.1

end BelowLattice

/-! ## 6 The second block pairing, and the second symplectic identity -/

section PairingCD

variable {h : ℕ}

/-- **The second block pairing of a continuous homomorphism**: the wedge of the `(3,4)`- and
`(4,5)`-columns, both of which are characters of `D_sq h`. -/
noncomputable def blockParCD (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R))
    (g k : (DSq h : Type)) : ZMod 2 := selPar (SqU6.blockReadCD (Phi g) (Phi k))

theorem blockParCD_def (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R))
    (g k : (DSq h : Type)) :
    blockParCD Phi g k = selPar (SqU6.blockReadCD (Phi g) (Phi k)) := rfl

variable {Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R)}

private theorem zmodTwo_zero_sub_cd : ∀ a : ZMod 2, 0 - a = a := by decide

private theorem zmodTwo_eq_zero_of_ne_cd : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide

@[simp] theorem blockParCD_self (g : (DSq h : Type)) : blockParCD Phi g g = 0 := by
  rw [blockParCD, show SqU6.blockReadCD (Phi g) (Phi g) = 0 by rw [SqU6.blockReadCD]; ring,
    selPar_zero]

theorem blockParCD_swap (g k : (DSq h : Type)) : blockParCD Phi g k = blockParCD Phi k g := by
  rw [blockParCD, blockParCD,
    show SqU6.blockReadCD (Phi g) (Phi k) = 0 - SqU6.blockReadCD (Phi k) (Phi g) by
      rw [SqU6.blockReadCD, SqU6.blockReadCD]; ring,
    selPar_sub, selPar_zero, zmodTwo_zero_sub_cd]

theorem blockParCD_mul_right (g k k' : (DSq h : Type)) :
    blockParCD Phi g (k * k') = blockParCD Phi g k + blockParCD Phi g k' := by
  rw [blockParCD, blockParCD, blockParCD, map_mul,
    show SqU6.blockReadCD (Phi g) (Phi k * Phi k')
      = SqU6.blockReadCD (Phi g) (Phi k) + SqU6.blockReadCD (Phi g) (Phi k') by
      rw [SqU6.blockReadCD, SqU6.blockReadCD, SqU6.blockReadCD, SqU6.mul_c, SqU6.mul_d]; ring,
    selPar_add]

theorem blockParCD_mul_left (g g' k : (DSq h : Type)) :
    blockParCD Phi (g * g') k = blockParCD Phi g k + blockParCD Phi g' k := by
  rw [blockParCD_swap (Phi := Phi) (g * g') k, blockParCD_mul_right,
    blockParCD_swap (Phi := Phi) k g, blockParCD_swap (Phi := Phi) k g']

@[simp] theorem blockParCD_one_right (g : (DSq h : Type)) : blockParCD Phi g 1 = 0 := by
  rw [blockParCD, map_one, SqU6.blockReadCD, SqU6.one_c, SqU6.one_d, mul_zero, mul_zero,
    sub_zero, selPar_zero]

@[simp] theorem blockParCD_one_left (k : (DSq h : Type)) : blockParCD Phi 1 k = 0 := by
  rw [blockParCD_swap (Phi := Phi) 1 k, blockParCD_one_right]

@[simp] theorem blockParCD_inv_left (g k : (DSq h : Type)) :
    blockParCD Phi g⁻¹ k = -blockParCD Phi g k := by
  have hz : blockParCD Phi g⁻¹ k + blockParCD Phi g k = 0 := by
    rw [← blockParCD_mul_left, inv_mul_cancel, blockParCD_one_left]
  linear_combination hz

@[simp] theorem blockParCD_inv_right (g k : (DSq h : Type)) :
    blockParCD Phi g k⁻¹ = -blockParCD Phi g k := by
  rw [blockParCD_swap (Phi := Phi) g k⁻¹, blockParCD_inv_left, blockParCD_swap (Phi := Phi) k g]

/-- ⭐ **The second pairing kills the commutator subgroup too.** -/
@[simp] theorem blockParCD_commP_left (g g' k : (DSq h : Type)) :
    blockParCD Phi (commP g g') k = 0 := by
  rw [commP, blockParCD_mul_left, blockParCD_mul_left, blockParCD_mul_left, blockParCD_inv_left,
    blockParCD_inv_left]
  ring

@[simp] theorem blockParCD_commP_right (g g' k : (DSq h : Type)) :
    blockParCD Phi g (commP g' k) = 0 := by
  rw [blockParCD_swap (Phi := Phi) g (commP g' k), blockParCD_commP_left]

variable (Phi) in
/-- **The second pairing against a fixed element, as a continuous character of `D_sq h`.** -/
noncomputable def blockParCharCD (g : (DSq h : Type)) :
    ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2)) where
  toFun k := ofAdd (blockParCD Phi g k)
  map_one' := by rw [blockParCD_one_right]; rfl
  map_mul' k k' := by rw [blockParCD_mul_right, ofAdd_add]
  continuous_toFun :=
    (continuous_of_discreteTopology (f := fun p : SqU6 gr3R =>
      ofAdd (selPar (SqU6.blockReadCD (Phi g) p)))).comp Phi.continuous_toFun

@[simp] theorem blockParCharCD_apply (g k : (DSq h : Type)) :
    blockParCharCD Phi g k = ofAdd (blockParCD Phi g k) := rfl

theorem blockParCD_eq_zero_of_gen_right {g : (DSq h : Type)}
    (hgen : ∀ i, blockParCD Phi g (sqGen h i) = 0) (k : (DSq h : Type)) :
    blockParCD Phi g k = 0 := by
  have hext : blockParCharCD Phi g = blockParCharCD Phi 1 :=
    dsq_hom_ext _ _ fun i => by
      rw [blockParCharCD_apply, blockParCharCD_apply, hgen i, blockParCD_one_left]
  have hk := DFunLike.congr_fun hext k
  rw [blockParCharCD_apply, blockParCharCD_apply, blockParCD_one_left] at hk
  exact Multiplicative.ofAdd.injective hk

theorem blockParCD_eq_zero_of_gen_left {k : (DSq h : Type)}
    (hgen : ∀ i, blockParCD Phi (sqGen h i) k = 0) (g : (DSq h : Type)) :
    blockParCD Phi g k = 0 := by
  rw [blockParCD_swap]
  exact blockParCD_eq_zero_of_gen_right (fun i => by
    rw [blockParCD_swap]; exact hgen i) g

end PairingCD

section SymplecticCD

variable {h : ℕ}

private def selParAddCD : gr3R →+ ZMod 2 where
  toFun := selPar
  map_zero' := selPar_zero
  map_add' := selPar_add

private theorem selPar_sum_cd {ι : Type} [Fintype ι] (f : ι → gr3R) :
    selPar (∑ i, f i) = ∑ i, selPar (f i) := map_sum selParAddCD f Finset.univ

/-- ⭐⭐ **THE SECOND SYMPLECTIC IDENTITY.**  The second block pairing of the two core letters is
the sum of the second block pairings of the handle pairs, at every relator-killing frame of
`D_sq h` and every continuous homomorphism. -/
theorem blockParCD_relator_frame (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R))
    {n : Fin (sqRank h) → (DSq h : Type)} (hn : sqRelWord n = 1) :
    blockParCD Phi (n 0) (n 1)
      = ∑ j : Fin h, blockParCD Phi (n (sqHandleIdxU j)) (n (sqHandleIdxV j)) := by
  have hb := SqU6.selPar_handleWord_h_of_relator (sqU6Balance Phi n hn)
  rw [SqU6.handleWord_h, sqU6BlockH] at hb
  rw [blockParCD_def, ← hb, selPar_sum_cd]
  exact Finset.sum_congr rfl fun j _ => congrArg selPar (by rw [SqU6.blockReadCD]; ring)

/-- The second identity at the standard frame. -/
theorem blockParCD_relator (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R)) :
    blockParCD Phi (dsqSigma h) (dsqX0 h)
      = ∑ j : Fin h, blockParCD Phi (sqGen h (sqHandleIdxU j)) (sqGen h (sqHandleIdxV j)) :=
  blockParCD_relator_frame Phi (dsq_relation h)

end SymplecticCD

/-! ## 7 ⭐⭐⭐ The `h = 0` death on every pair -/

section HandleFreeCD

variable {h : ℕ} {Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R)}

/-- **The torsion letter has an even `(3,4)`-column** at every continuous homomorphism: the
relator's own `(3,4)`-row forces it, with no hypothesis.  The companion `selPar_d_dsqX1` is
`GradedBlockFrame`'s. -/
theorem selPar_c_dsqX1 : selPar (Phi (dsqX1 h)).c = 0 := by
  have h0 : (sqRelWord fun i => Phi (sqGen h i)).c = 0 := by rw [sqU6Balance_gen Phi]; rfl
  rw [SqU6.sqRelWord_c] at h0
  obtain ⟨c, hc⟩ :=
    abelRow_even (Phi (sqGen h 1)).c (Phi (sqGen h 2)).c (by linear_combination h0)
  rw [dsqX1]
  exact (selPar_eq_zero_iff _).mpr ⟨c, hc⟩

/-- **The torsion letter is invisible to the second pairing too**, at every handle count. -/
@[simp] theorem blockParCD_dsqX1_right (g : (DSq h : Type)) : blockParCD Phi g (dsqX1 h) = 0 := by
  rw [blockParCD_def, SqU6.blockReadCD, selPar_sub, selPar_mul, selPar_mul, selPar_c_dsqX1,
    selPar_d_dsqX1, mul_zero, mul_zero, sub_zero]

@[simp] theorem blockParCD_dsqX1_left (k : (DSq h : Type)) : blockParCD Phi (dsqX1 h) k = 0 := by
  rw [blockParCD_swap, blockParCD_dsqX1_right]

private theorem sqIdx_cases_handleFree_cd (i : Fin (sqRank 0)) : i = 0 ∨ i = 1 ∨ i = 2 := by
  rcases sqIdx_cases i with hi | hi | hi | ⟨j, _⟩ | ⟨j, _⟩
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hi)
  · exact absurd j.isLt (by omega)
  · exact absurd j.isLt (by omega)

/-- **At `h = 0` the two core letters pair evenly** for the second form: the empty sum of the
second symplectic identity. -/
theorem blockParCD_sigma_x0_handleFree (Psi : ContinuousMonoidHom (DSq 0 : Type) (SqU6 gr3R)) :
    blockParCD Psi (dsqSigma 0) (dsqX0 0) = 0 := by
  rw [blockParCD_relator Psi]
  exact Finset.sum_empty

/-- ⭐⭐⭐ **AT `h = 0` THE SECOND PAIRING VANISHES ON EVERY PAIR OF GROUP ELEMENTS.** -/
theorem blockParCD_handleFree (Psi : ContinuousMonoidHom (DSq 0 : Type) (SqU6 gr3R))
    (g k : (DSq 0 : Type)) : blockParCD Psi g k = 0 := by
  have hsx := blockParCD_sigma_x0_handleFree Psi
  have hsig : ∀ x : (DSq 0 : Type), blockParCD Psi x (dsqSigma 0) = 0 := by
    refine fun x => blockParCD_eq_zero_of_gen_left (fun i => ?_) x
    rcases sqIdx_cases_handleFree_cd i with rfl | rfl | rfl
    · exact blockParCD_self _
    · rw [show (1 : Fin (sqRank 0)) = 1 from rfl, ← dsqX0, blockParCD_swap]
      exact hsx
    · exact blockParCD_dsqX1_left _
  have hx0 : ∀ x : (DSq 0 : Type), blockParCD Psi x (dsqX0 0) = 0 := by
    refine fun x => blockParCD_eq_zero_of_gen_left (fun i => ?_) x
    rcases sqIdx_cases_handleFree_cd i with rfl | rfl | rfl
    · exact hsx
    · exact blockParCD_self _
    · exact blockParCD_dsqX1_left _
  refine blockParCD_eq_zero_of_gen_right (fun i => ?_) k
  rcases sqIdx_cases_handleFree_cd i with rfl | rfl | rfl
  · exact hsig g
  · exact hx0 g
  · exact blockParCD_dsqX1_right _

/-- ⭐⭐⭐ **THE SECOND FORCING ON AN ARBITRARY PAIR.** -/
theorem pos_of_blockParCD_odd (g k : (DSq h : Type)) (hodd : blockParCD Phi g k = 1) : 0 < h := by
  rcases Nat.eq_zero_or_pos h with rfl | hp
  · rw [blockParCD_handleFree Phi g k] at hodd
    exact absurd hodd (by decide)
  · exact hp

/-- The tuple-level forcing at the hom level, with no hypothesis, exactly as
`pos_of_blockRead_odd_hom`. -/
theorem pos_of_blockReadCD_odd_hom (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R))
    (hodd : selPar (SqU6.blockReadCD (Phi (dsqSigma h)) (Phi (dsqX0 h))) = 1) : 0 < h :=
  SqU6.pos_of_blockReadCD_odd (sqU6Balance_gen Phi) hodd

end HandleFreeCD

/-! ## 8 ⭐⭐⭐ The witness, the characterisation, and the independence of the two forms -/

section ColumnCharacters

variable {h : ℕ} {Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R)}

private def trivParChar : ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2)) where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (one_mul (1 : Multiplicative (ZMod 2))).symm
  continuous_toFun := continuous_const

variable (Phi) in
/-- **The `(3,4)`-column of a continuous homomorphism, as a character mod `2`.** -/
noncomputable def colCharC : ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2)) where
  toFun k := ofAdd (selPar (Phi k).c)
  map_one' := by rw [map_one, SqU6.one_c, selPar_zero]; rfl
  map_mul' k k' := by rw [map_mul, SqU6.mul_c, selPar_add, ofAdd_add]
  continuous_toFun :=
    (continuous_of_discreteTopology (f := fun p : SqU6 gr3R => ofAdd (selPar p.c))).comp
      Phi.continuous_toFun

variable (Phi) in
/-- **The `(5,6)`-column of a continuous homomorphism, as a character mod `2`.** -/
noncomputable def colCharE : ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2)) where
  toFun k := ofAdd (selPar (Phi k).e)
  map_one' := by rw [map_one, SqU6.one_e, selPar_zero]; rfl
  map_mul' k k' := by rw [map_mul, SqU6.mul_e, selPar_add, ofAdd_add]
  continuous_toFun :=
    (continuous_of_discreteTopology (f := fun p : SqU6 gr3R => ofAdd (selPar p.e))).comp
      Phi.continuous_toFun

/-- A column character trivial on the generators is trivial. -/
theorem selPar_c_eq_zero_of_gen (hgen : ∀ i, selPar (Phi (sqGen h i)).c = 0)
    (g : (DSq h : Type)) : selPar (Phi g).c = 0 := by
  have hext : colCharC Phi = trivParChar :=
    dsq_hom_ext _ _ fun i => by
      show ofAdd (selPar (Phi (sqGen h i)).c) = 1
      rw [hgen i]; rfl
  have hk := DFunLike.congr_fun hext g
  exact Multiplicative.ofAdd.injective hk

theorem selPar_e_eq_zero_of_gen (hgen : ∀ i, selPar (Phi (sqGen h i)).e = 0)
    (g : (DSq h : Type)) : selPar (Phi g).e = 0 := by
  have hext : colCharE Phi = trivParChar :=
    dsq_hom_ext _ _ fun i => by
      show ofAdd (selPar (Phi (sqGen h i)).e) = 1
      rw [hgen i]; rfl
  have hk := DFunLike.congr_fun hext g
  exact Multiplicative.ofAdd.injective hk

/-- ⭐ **A homomorphism whose generators all have an even `(3,4)`-column has the second form
identically `0`** - on every pair of group elements, at every handle count. -/
theorem blockParCD_eq_zero_of_even_c (hgen : ∀ i, selPar (Phi (sqGen h i)).c = 0)
    (g k : (DSq h : Type)) : blockParCD Phi g k = 0 := by
  rw [blockParCD_def, SqU6.blockReadCD, selPar_sub, selPar_mul, selPar_mul,
    selPar_c_eq_zero_of_gen hgen g, selPar_c_eq_zero_of_gen hgen k, zero_mul, mul_zero, sub_zero]

/-- ⭐ **…and one whose generators all have an even `(5,6)`-column has the FIRST form
identically `0`.** -/
theorem blockPar_eq_zero_of_even_e (hgen : ∀ i, selPar (Phi (sqGen h i)).e = 0)
    (g k : (DSq h : Type)) : blockPar Phi g k = 0 := by
  rw [blockPar_def, SqU6.blockRead, selPar_sub, selPar_mul, selPar_mul,
    selPar_e_eq_zero_of_gen hgen g, selPar_e_eq_zero_of_gen hgen k, mul_zero, zero_mul, sub_zero]

/-- The `(3,4)`-column of a one-handle-live tuple is even as soon as its five letters' are. -/
theorem selPar_c_fiveTuple {h : ℕ} {j : Fin h} {S X Y U V : SqU6 gr3R} (hS : selPar S.c = 0)
    (hX : selPar X.c = 0) (hY : selPar Y.c = 0) (hU : selPar U.c = 0) (hV : selPar V.c = 0)
    (i : Fin (sqRank h)) : selPar (fiveTuple gr3R h j S X Y U V i).c = 0 := by
  simp only [fiveTuple]
  split_ifs
  · exact hS
  · exact hX
  · exact hY
  · exact hU
  · exact hV
  · rw [SqU6.one_c, selPar_zero]

theorem selPar_e_fiveTuple {h : ℕ} {j : Fin h} {S X Y U V : SqU6 gr3R} (hS : selPar S.e = 0)
    (hX : selPar X.e = 0) (hY : selPar Y.e = 0) (hU : selPar U.e = 0) (hV : selPar V.e = 0)
    (i : Fin (sqRank h)) : selPar (fiveTuple gr3R h j S X Y U V i).e = 0 := by
  simp only [fiveTuple]
  split_ifs
  · exact hS
  · exact hX
  · exact hY
  · exact hU
  · exact hV
  · rw [SqU6.one_e, selPar_zero]

end ColumnCharacters

section Witness

variable {h : ℕ} {j : Fin h}

/-- The sigma slot of the second reading's witness: the `(3,4)`-column alone. -/
def secCexS : SqU6 gr3R := ⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The `x0` slot: the `(4,5)`-column alone, so the second reading of the core pair is `1`. -/
def secCexX : SqU6 gr3R := ⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The `x1` slot: the layered solve of the fifteen rows against the live block
(`scripts/w63_second/results/pair_second.txt` section J). -/
def secCexY : SqU6 gr3R := ⟨0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0⟩

/-- The `u`-letter of the live handle. -/
def secCexU : SqU6 gr3R := ⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The `v`-letter of the live handle.  `[U, V]` is the `(3,5)` generator, so the `(3,5)` block
coordinate is `1` and odd, and the `(4,6)` one is `0`. -/
def secCexV : SqU6 gr3R := ⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

variable (h j) in
/-- ⭐⭐ **The second reading's witness marking**, at every handle count and every handle. -/
def secCexMark : Fin (sqRank h) → SqU6 gr3R :=
  fiveTuple gr3R h j secCexS secCexX secCexY secCexU secCexV

/-- ⭐⭐ **All fifteen relator rows die**, at every handle count and every handle. -/
theorem sqRelWord_secCexMark (h : ℕ) (j : Fin h) : sqRelWord (secCexMark h j) = 1 := by
  rw [secCexMark, sqRelWord_fiveTuple]
  decide

variable (h j) in
/-- **The witness hom**: the committed class-five lift of `secCexMark`. -/
noncomputable def secCexHom : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R) :=
  sqU6Hom gr3R_card h (secCexMark h j) (sqRelWord_secCexMark h j)

@[simp] theorem secCexHom_gen (i : Fin (sqRank h)) :
    secCexHom h j (sqGen h i) = secCexMark h j i := sqU6Hom_gen _ _ _ i

@[simp] theorem secCexHom_sigma : secCexHom h j (dsqSigma h) = secCexS := by
  rw [dsqSigma, secCexHom_gen]
  simp only [secCexMark, fiveTuple_zero]

@[simp] theorem secCexHom_x0 : secCexHom h j (dsqX0 h) = secCexX := by
  rw [dsqX0, secCexHom_gen]
  simp only [secCexMark, fiveTuple_one]

@[simp] theorem secCexHom_handleU : secCexHom h j (sqGen h (sqHandleIdxU j)) = secCexU := by
  rw [secCexHom_gen]
  simp only [secCexMark, fiveTuple_handleU]

@[simp] theorem secCexHom_handleV : secCexHom h j (sqGen h (sqHandleIdxV j)) = secCexV := by
  rw [secCexHom_gen]
  simp only [secCexMark, fiveTuple_handleV]

/-- ⭐⭐⭐ **The second instrument is live at every positive handle count.** -/
theorem blockParCD_secCexHom : blockParCD (secCexHom h j) (dsqSigma h) (dsqX0 h) = 1 := by
  rw [blockParCD_def, secCexHom_sigma, secCexHom_x0]
  decide

/-- …and live on the handle pair as well, which is the right side of the second symplectic
identity. -/
theorem blockParCD_secCexHom_handle :
    blockParCD (secCexHom h j) (sqGen h (sqHandleIdxU j)) (sqGen h (sqHandleIdxV j)) = 1 := by
  rw [blockParCD_def, secCexHom_handleU, secCexHom_handleV]
  decide

/-- The composite check the doctrine asks for: both sides of the second symplectic identity are
computed from the point and they agree. -/
theorem blockParCD_secCexHom_sum :
    (∑ j' : Fin h, blockParCD (secCexHom h j) (sqGen h (sqHandleIdxU j'))
      (sqGen h (sqHandleIdxV j'))) = 1 := by
  rw [Finset.sum_eq_single j ?_ ?_]
  · exact blockParCD_secCexHom_handle
  · intro j' _ hne
    simp only [blockParCD_def, secCexHom_gen, secCexMark, fiveTuple_handleU_ne hne,
      fiveTuple_handleV_ne hne]
    decide
  · intro hcon
    exact absurd (Finset.mem_univ j) hcon

theorem blockParCD_secCexHom_crosscheck :
    blockParCD (secCexHom h j) (dsqSigma h) (dsqX0 h)
      = ∑ j' : Fin h, blockParCD (secCexHom h j) (sqGen h (sqHandleIdxU j'))
          (sqGen h (sqHandleIdxV j')) := by
  rw [blockParCD_secCexHom, blockParCD_secCexHom_sum]

/-- ⭐⭐ **THE SECOND CHARACTERISATION.**  The second block pairing is odd on some pair of
elements of `D_sq h` at some continuous homomorphism **if and only if** `0 < h`.

⚠ Compare `exists_blockPar_odd_iff_pos`: both readings are equivalent to the same thing, so as
handle-count instruments they are one instrument twice, and this file claims no more. -/
theorem exists_blockParCD_odd_iff_pos {h : ℕ} :
    (∃ (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R)) (g k : (DSq h : Type)),
      blockParCD Phi g k = 1) ↔ 0 < h := by
  constructor
  · rintro ⟨Phi, g, k, hodd⟩
    exact pos_of_blockParCD_odd (Phi := Phi) g k hodd
  · intro hp
    exact ⟨secCexHom h ⟨0, hp⟩, dsqSigma h, dsqX0 h, blockParCD_secCexHom⟩

/-- ⭐⭐⭐ **THE SEPARATION, ONE WAY.**  At the witness the FIRST form is `0` on **every pair of
elements of `D_sq h`**, while the second is odd on the core pair.  Every letter of the witness
has a vanishing `(5,6)`-column, so `blockPar_eq_zero_of_even_e` applies. -/
theorem blockPar_secCexHom_eq_zero (g k : (DSq h : Type)) :
    blockPar (secCexHom h j) g k = 0 := by
  refine blockPar_eq_zero_of_even_e (fun i => ?_) g k
  rw [secCexHom_gen, secCexMark]
  exact selPar_e_fiveTuple (by decide) (by decide) (by decide) (by decide) (by decide) i

/-- ⭐⭐⭐ **THE SEPARATION, THE OTHER WAY.**  At wave 59's counterexample the SECOND form is `0`
on every pair, while `blockPar_blockCexHom` says the first is odd on the core pair.  So neither
reading is a function of the other, and the pair is a strictly finer invariant of a homomorphism
than either member. -/
theorem blockParCD_blockCexHom_eq_zero (g k : (DSq h : Type)) :
    blockParCD (blockCexHom h j) g k = 0 := by
  refine blockParCD_eq_zero_of_even_c (fun i => ?_) g k
  rw [blockCexHom_gen, blindCexMark]
  exact selPar_c_fiveTuple (by decide) (by decide) (by decide) (by decide) (by decide) i

end Witness

/-! ## 9 ⚠ The committed points, and the correction to `GradedBlockFrame`'s Honesty 3 -/

section Points

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐ **The second form is dead at wave 60's binder point, on EVERY pair.**  Not on two pairs:
every letter of `fiveWit h j 1` has an even `(3,4)`-column, so the whole form dies. -/
theorem blockParCD_fiveFrameHom_eq_zero (g k : (DSq h : Type)) :
    blockParCD (fiveFrameHom h j) g k = 0 := by
  refine blockParCD_eq_zero_of_even_c (fun i => ?_) g k
  rw [fiveFrameHom_gen, fiveWit]
  exact selPar_c_fiveTuple (by decide) (by decide) (by decide) (by decide) (by decide) i

/-- ⭐⭐ **…and at wave 61's stage-four point, on every pair.** -/
theorem blockParCD_stageFrameHom_eq_zero (g k : (DSq h : Type)) :
    blockParCD (stageFrameHom h j) g k = 0 := by
  refine blockParCD_eq_zero_of_even_c (fun i => ?_) g k
  rw [stageFrameHom_gen, stageWit]
  exact selPar_c_fiveTuple (by decide) (by decide) (by decide) (by decide) (by decide) i

/-- ⚠ **THE CORRECTION.**  `GradedBlockFrame`'s Honesty 3 calls wave 60's binder point
"block-blind" for the FIRST reading.  Its two committed computations are correct - the core pair
and the live handle pair are both even - but the form is a form on the whole group and it is
**odd** on the pair `(x0, u_j)`, because `forceX`'s `(5,6)`-column and `forceU`'s
`(4,5)`-column are both odd.  `pos_of_blockPar_odd` quantifies over all pairs, so it does fire
at this point.

Nothing downstream changes: at `fiveFrameHom h j` the conclusion `0 < h` is already free from
the handle index `j`.  What changes is that a lane wanting a live block channel at this point
does not have to move off it. -/
theorem blockPar_fiveFrameHom_x0_handleU :
    blockPar (fiveFrameHom h j) (dsqX0 h) (sqGen h (sqHandleIdxU j)) = 1 := by
  rw [blockPar_def, fiveFrameHom_x0, fiveFrameHom_handleU]
  decide

theorem blockPar_fiveFrameHom_x0_handleV :
    blockPar (fiveFrameHom h j) (dsqX0 h) (sqGen h (sqHandleIdxV j)) = 1 := by
  rw [blockPar_def, fiveFrameHom_x0, fiveFrameHom_handleV]
  decide

/-- ⚠ **…and the same at wave 61's stage-four point.** -/
theorem blockPar_stageFrameHom_x0_handleU :
    blockPar (stageFrameHom h j) (dsqX0 h) (sqGen h (sqHandleIdxU j)) = 1 := by
  rw [blockPar_def, stageFrameHom_x0, stageFrameHom_handleU]
  decide

theorem blockPar_stageFrameHom_x0_handleV :
    blockPar (stageFrameHom h j) (dsqX0 h) (sqGen h (sqHandleIdxV j)) = 1 := by
  rw [blockPar_def, stageFrameHom_x0, stageFrameHom_handleV]
  decide

/-- The second form's readings at the two committed points and at the counterexample, on the two
pairs `GradedBlockFrame` computes, for the record: all even, as the identically-zero statements
above already imply. -/
theorem blockParCD_fiveFrameHom : blockParCD (fiveFrameHom h j) (dsqSigma h) (dsqX0 h) = 0 :=
  blockParCD_fiveFrameHom_eq_zero _ _

theorem blockParCD_stageFrameHom : blockParCD (stageFrameHom h j) (dsqSigma h) (dsqX0 h) = 0 :=
  blockParCD_stageFrameHom_eq_zero _ _

theorem blockParCD_blockCexHom : blockParCD (blockCexHom h j) (dsqSigma h) (dsqX0 h) = 0 :=
  blockParCD_blockCexHom_eq_zero _ _

end Points

/-! ## 10 Axiom pins

Committed prints for every public declaration: all **std-3** (`propext`, `Classical.choice`,
`Quot.sound`) or a strict subset; no census axiom is reachable.  Every `decide` is on `ZMod 8`
or `ZMod 2`. -/

section AxiomPins

#print axioms SqU6.blockReadCD
#print axioms SqU6.blockReadCD_def
#print axioms SqU6.blockReadCD_eq_zero_of_slot
#print axioms SqU6.blockReadCD_sigFiveMark
#print axioms SqU6.sqWord_h
#print axioms SqU6.sqRelWord_h
#print axioms SqU6.handleWord_h_of_relator
#print axioms SqU6.sqWord_h_eq_blockReadCD
#print axioms SqU6.handleWord_h_eq_blockReadCD_of_relator
#print axioms SqU6.selPar_handleWord_h_of_relator
#print axioms SqU6.handleWord_h_odd_of_relator
#print axioms SqU6.blockReadCD_even_of_relator_handleFree
#print axioms SqU6.pos_of_blockReadCD_odd
#print axioms SqU6.exists_handle_minorCD_odd
#print axioms SqU6.selPar_blockReadCD_dress_of_relator
#print axioms SqU6.sqWord_i_eq_blockRead_of_e
#print axioms SqU6.handleWord_i_eq_blockRead_of_relator_e
#print axioms SqU6.selPar_handleWord_i_of_relator_e
#print axioms SqU6.blockReadCD_gaTwoDress
#print axioms SqU6.blockReadCD_gaThreeDress
#print axioms blockParCD
#print axioms blockParCD_def
#print axioms blockParCD_self
#print axioms blockParCD_swap
#print axioms blockParCD_mul_right
#print axioms blockParCD_mul_left
#print axioms blockParCD_one_right
#print axioms blockParCD_one_left
#print axioms blockParCD_inv_left
#print axioms blockParCD_inv_right
#print axioms blockParCD_commP_left
#print axioms blockParCD_commP_right
#print axioms blockParCharCD
#print axioms blockParCharCD_apply
#print axioms blockParCD_eq_zero_of_gen_right
#print axioms blockParCD_eq_zero_of_gen_left
#print axioms blockParCD_relator_frame
#print axioms blockParCD_relator
#print axioms selPar_c_dsqX1
#print axioms blockParCD_dsqX1_right
#print axioms blockParCD_dsqX1_left
#print axioms blockParCD_sigma_x0_handleFree
#print axioms blockParCD_handleFree
#print axioms pos_of_blockParCD_odd
#print axioms pos_of_blockReadCD_odd_hom
#print axioms colCharC
#print axioms colCharE
#print axioms selPar_c_eq_zero_of_gen
#print axioms selPar_e_eq_zero_of_gen
#print axioms blockParCD_eq_zero_of_even_c
#print axioms blockPar_eq_zero_of_even_e
#print axioms selPar_c_fiveTuple
#print axioms selPar_e_fiveTuple
#print axioms secCexS
#print axioms secCexX
#print axioms secCexY
#print axioms secCexU
#print axioms secCexV
#print axioms secCexMark
#print axioms sqRelWord_secCexMark
#print axioms secCexHom
#print axioms secCexHom_gen
#print axioms secCexHom_sigma
#print axioms secCexHom_x0
#print axioms secCexHom_handleU
#print axioms secCexHom_handleV
#print axioms blockParCD_secCexHom
#print axioms blockParCD_secCexHom_handle
#print axioms blockParCD_secCexHom_sum
#print axioms blockParCD_secCexHom_crosscheck
#print axioms exists_blockParCD_odd_iff_pos
#print axioms blockPar_secCexHom_eq_zero
#print axioms blockParCD_blockCexHom_eq_zero
#print axioms blockParCD_fiveFrameHom_eq_zero
#print axioms blockParCD_stageFrameHom_eq_zero
#print axioms blockPar_fiveFrameHom_x0_handleU
#print axioms blockPar_fiveFrameHom_x0_handleV
#print axioms blockPar_stageFrameHom_x0_handleU
#print axioms blockPar_stageFrameHom_x0_handleV
#print axioms blockParCD_fiveFrameHom
#print axioms blockParCD_stageFrameHom
#print axioms blockParCD_blockCexHom

end AxiomPins

end SqCore

end Dyadic

end GQ2

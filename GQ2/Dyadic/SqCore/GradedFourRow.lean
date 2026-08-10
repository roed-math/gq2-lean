/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFourHom
import GQ2.Dyadic.SqCore.GradedGammaTwo

/-!
# W55-ROW: the ten-row solve at the displaced binder point, and the sigma forcing at the
uncleared row

`GradedFourHom` lifted the class-four sigma forcing to `sqArbFrame` and then priced, exactly,
what it could not do:

> ⚠ **The honest cost: the reachable row type is the already-cleared one.**  …  Reaching the
> uncleared row at class four is **not** transport: it needs a class-four marking solving all
> ten relator rows with `m V = V·Φ(w)`, i.e. a new solve at the displaced binder point, and the
> dressing lattice cannot compensate.

This file performs that solve and spends it.  Everything below was derived symbolically and
validated numerically against honest group collection before transcription
(`scripts/w55_row/`, certified outputs in `scripts/w55_row/results/`).

## Headline: the class-four sigma forcing now runs at the UNCLEARED row

⭐⭐ `sqArbFrame_sigma_forced_row`.  At one handle, at the **uncleared** selected row
`nuSel 1 0 0 1` (so `ν'(v₀) = 1`), at the honest continuous homomorphism
`rowFourHom : D_sq 1 → U_5(ℤ/8)` built by the committed lift from the displaced binder point:
**every `ν'`-trivial sigma dressing of the arbitrary-dressing frame whose image is killed by any
achievable five-slot class-four refinement has an even `chi_a`-character.**  Nothing is carried
beyond the dressing's own legality - and, unlike `GradedFourHom.sqArbFrame_sigma_forced`, the
two handle-clearing hypotheses `hu`, `hv` are **gone**: the frame's `V`-slot really is displaced
by the pivot, and the marking absorbs the displacement instead of assuming it away.

The three verdicts are executed on the frame itself, with both regression dressings exhibited
as `λ`-trivial and `ν'`-trivial slotwise (`rowFour_escape_separates`):

```text
a0 = 1                            relator dies outright     (sqRelWord_rowFrame_sigTriv)
a0 = (cleared V)²  (chi_a = 2)    residue 2, dies to one    (sqRelWord_rowFrame_sigVsq[_complete])
a0 = cleared V     (chi_a = 1)    residue 1, survives none  (sqRelWord_rowFrame_sigV[_ne_one])
```

and `rowFrame_class_three_blind` records that both `U_4`-quotients are trivial in all three
cases, so the whole committed class-three machinery cannot see the separation.

## What is new, and why it could not be transported

⭐⭐ **The obstruction that fixes the row type, named and proved** (§1).  For **any** five-slot
tuple over **any** commutative ring, displacing the `v`-slot on the right by `P` moves the
relator's class-two `e`-row by exactly `U.a·P.b − U.b·P.a` (`sqRelWord_e_displace`).  At the
uncleared row `P` is the pivot image, whose `b`-column is `1` because `ν'(w) = 1`, and the
`u`-letter is `ν'`-trivial, so its `b`-column is `0`.  A witness at the uncleared row has to meet
**two** standards - the marking kills the relator (else there is no hom) and the cleared frame
kills it (else the frame is not even a stage-two survivor) - and the `e`-row equation then reads
`0 = 0 + U.a`.  Hence ⭐⭐ `rowFour_chiA_handleU_forced`: **at the uncleared row the `u`-letter's
`chi_a`-character must vanish.**

That is the exact dual of `GradedFourHom`'s cost, and it is what makes the solve interesting
rather than routine.  At the cleared row the odd sigma dressing was the `U`-letter
(`sigFourU.a = 1`); at the uncleared row that channel is closed by a theorem.  The odd channel
that opens instead is the **cleared `v`-letter** `V₀ = v₀·w^{−1}`, whose `chi_a` no row
constrains, and which is `λ`- and `ν'`-trivial precisely *because* the row is uncleared
(`rowFour_forcing_nonvacuous`).  The roles of the two handle letters swap when the row type
does.

⭐⭐ **The solve** (§2).  `rowFourMark c` keeps the committed sigma-, `x₀`- and `x₁`-slots, takes
`rowFourU = ⟨0,0,0,1,0,…⟩` (the forced `chi_a = 0`, with `chi_d = 1`) on the `u`-slot, and takes
the cleared letter `rowFourV = ⟨1,0,…⟩` **times the pivot image** on the `v`-slot.  All ten rows
vanish (`sqRelWord_rowFourMark`), at **every** residue `c` of `sqPivotExp`, so the point carries
no oddness hypothesis at all - one better than the class-three precedent
(`GradedSigma` §6), which is quantified over the pivot half `h2`.  The cleared frame kills the
relator outright too (`sqRelWord_rowFourWit_triv`), so both standards of §1 are met on the nose.

Because the `x₀`- and `x₁`-slots are the committed ones, the pivot anchor
(`rowFourHom_sqPivot`), the gauge and the bit collapse are reused verbatim: the selection bit is
`selPar v.a` again (`rowFourWit_bit`).  What changed is not the functional but **which legal
dressings can realise an odd value on it**.

## Soundness: stronger than any committed class-four forcing

Three statements, in increasing strength.

* `rowFourWit_lamThree_even`: the committed achievable lattice `selLamThree` at the point's
  parameters `(A,B,C,D,E,F,T,S) = (0,1,0,0,1,0,0,1)` is even in both class-three coordinates, at
  every `(P,Q,R)`.  Same standard as `GradedSigmaFour.sigFourWit_lamThree_even`.
* `rowFourWit_lamThreePlus_even`: the **extended** lattice of `GradedGammaTwo` is even here too.
  The point's own extended-lattice data are computed outright
  (`rowFourWit_commP_zero_two/_two_handleU/_two_handleV`): the three `x₁`-slot commutators that
  unlocked wave 54's dead-end corners have `(h, i)` equal to `(0, 4)`, `(0, 0)` and `(0, 0)`, so
  `(P, Q, R) = (0, 0, 4)` and all three are even.  Wave 54's new moves cannot unlock this point.
* ⭐⭐ `rowFour_commutator_le` / `rowFourWit_sigma_forced_gaTwo`: **no lattice model at all.**
  The subgroup generated by the marking has vanishing third abelian column, vanishing second
  class-two coordinate and even third one (`rowFourMark_le_rowFrameSub`), and those three
  invariants force **every** commutator of two of its elements to have vanishing first
  class-three coordinate and even second one (`commP_mem_rowGaTwoSub`).  So the whole commutator
  subgroup `γ₂(im Φ)` - the object `GradedGammaTwo`'s achievability convention lets a dressing be
  drawn from, quadratic terms included - is even where the translation identity reads, and the
  sigma-slot dressing needs no constraint whatsoever.  `rowFourHom_mem_closure` identifies the
  closure with the image, through `dsq_topGen`.

This is the first class-four forcing in the campaign whose soundness quantifies over the group
rather than over a generating model.

## PROVED versus carried versus measured

**PROVED**, with no live hypothesis: the general `e`-row displacement identity and the
`chi_a`-obstruction (any ring, any tuple); the ten-row solve at every pivot residue; the hom,
its pivot anchor, both cleared-letter images, and the `b`-column identification with the
uncleared row; the frame identification; the bit; all four verdicts; the three soundness
statements; the forcing at the uncleared row in both the lattice and the `γ₂`-level form; and
the non-vacuity of the forcing.

**Carried, and named**: nothing beyond legality in the headline.  `rowFourWit_sigma_forced`
takes `hvb` (the dressing's `b`-column vanishes), which `rowFourHom_b` discharges from
`nuSel 1 0 0 1 g = 1` at the frame level.  The `γ₂`-level statements carry the campaign's
standing **achievability convention** (a test hom carries `γ₂` of the honest group onto `γ₂` of
its image), exactly as `GradedGammaTwo` does; the lattice-level statements carry
`selLamThree`/`selLamThreePlus` as models instead.

**Measured, not proved** (`scripts/w55_row/results/`): the exhaustive kill sweep - over all
`2097152` five-slot refinements built from the achievable class-three data, **zero** kill the
odd dressing and `524288` kill the even one - and the subgroup census, `|⟨slots⟩| = 524288` at
each of the eight pivot residues with the three invariants verified elementwise and `320000`
random commutators plus all generator pairs landing in the even subgroup.  Both are corollaries
of theorems above; they are recorded as cross-validation, not as inputs.  Also measured: `8` of
the `64` **unrestricted** `γ₃`-moves on the `U`-handle slot kill the odd dressing, so
achievability is load-bearing here exactly as it is at the committed point.

Every explicit claim of this file is mirrored numerically one for one in
`scripts/w55_row/instance_row.py`, and the library itself is validated against the committed
`GradedSigmaFour` facts before anything new is derived.  **195 checks, zero mismatches.**

## What this does NOT do

* One handle, `h = 1`, and one row: `nuSel 1 0 0 1`.  The mirror row `nuSel 1 0 1 0` is the
  same argument with the letters exchanged (`sqRelWord_e_displace` is stated generally enough to
  drive it), and the doubly-uncleared row `nuSel 1 0 1 1` is not attempted.
* The residual obstruction of `GradedSigmaFour` §7 - class four identifies the depth sweep's
  `a0 = a1` with `a0 = 1` - is untouched, and still needs class five or the universal quotient.
* The handle commutator is trivial in the image at this point (`commP U V = 1`), exactly as at
  the committed cleared-row point (`commP sigFourU sigFourV = 1`); the solve does not produce a
  point with a live handle block.

## Contents

* **1** the relator at one handle, the general `e`-row displacement identity, and ⭐⭐ the
  `chi_a`-obstruction that fixes the reachable row type;
* **2** ⭐⭐ the displaced binder point and its ten-row solve at every pivot residue;
* **3** the four tuple-level verdicts and the class-three blindness;
* **4** ⭐⭐ the point as a continuous homomorphism: the pivot anchor, both cleared letters, the
  `b`-column identification with the uncleared row, and the frame identification;
* **5** the selection bit;
* **6** soundness: the committed lattice, the extended lattice, and ⭐⭐ the model-independent
  `γ₂`-level bound;
* **7** ⭐⭐ the forcing at the uncleared row, the verdicts on `sqArbFrame`, and the non-vacuity;
* **8** committed axiom prints.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`; every `decide` is on `ZMod 8`, `ZMod 2` or tuples
and words over them.  All **93** committed prints are **std-3** (`propext`, `Classical.choice`,
`Quot.sound`) or a subset; no census axiom is reachable, `sqPivotExp` included.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The relator at one handle, and the obstruction that fixes the row type -/

section Obstruction

variable {R : Type} [CommRing R]

/-- The relator at one handle, split into core word and single commutator. -/
private theorem sqRelWord_one_handle {G : Type*} [Group G] (m : Fin (sqRank 1) → G) :
    sqRelWord m
      = sqWord (m 0) (m 1) (m 2) * commP (m (sqHandleIdxU 0)) (m (sqHandleIdxV 0)) := by
  rw [sqRelWord]
  congr 1
  rw [handleWord, List.finRange_succ]
  simp

variable (R) in
/-- **The five-slot tuple at one handle**, written out: `σ, x₀, x₁, u₀, v₀`. -/
def rowTuple (S X Y U V : SqU5 R) : Fin (sqRank 1) → SqU5 R :=
  fun i =>
    if (i : ℕ) = 0 then S else
    if (i : ℕ) = 1 then X else
    if (i : ℕ) = 2 then Y else
    if (i : ℕ) = 3 then U else V

variable {S X Y U V : SqU5 R}

@[simp] theorem rowTuple_zero : rowTuple R S X Y U V 0 = S := by
  simp only [rowTuple, sqVal_zero]; norm_num

@[simp] theorem rowTuple_one : rowTuple R S X Y U V 1 = X := by
  simp only [rowTuple, sqVal_one]; norm_num

@[simp] theorem rowTuple_two : rowTuple R S X Y U V 2 = Y := by
  simp only [rowTuple, sqVal_two]; norm_num

@[simp] theorem rowTuple_handleU : rowTuple R S X Y U V (sqHandleIdxU 0) = U := by
  simp only [rowTuple, sqHandleIdxU_val]; norm_num

@[simp] theorem rowTuple_handleV : rowTuple R S X Y U V (sqHandleIdxV 0) = V := by
  simp only [rowTuple, sqHandleIdxV_val]; norm_num

/-- The relator of a five-slot tuple, in the split form. -/
theorem sqRelWord_rowTuple :
    sqRelWord (rowTuple R S X Y U V) = sqWord S X Y * commP U V := by
  rw [sqRelWord_one_handle, rowTuple_zero, rowTuple_one, rowTuple_two, rowTuple_handleU,
    rowTuple_handleV]

/-- ⭐⭐ **The obstruction that fixes the reachable row type, in closed form.**  Displacing the
`v`-slot on the right by an element `P` moves the relator's class-two `e`-row by exactly
`u`-slot's `χ_a`-character against `P`'s `b`-column, minus the mirror term.  Nothing else in
the tuple enters: the core word does not see the handle, and the handle commutator's `e`-row is
the alternating `(a, b)`-pairing.  This is the class-four form of "the `ν'`-row lives on the
`b`-column". -/
theorem sqRelWord_e_displace (P : SqU5 R) :
    (sqRelWord (rowTuple R S X Y U (V * P))).e
      = (sqRelWord (rowTuple R S X Y U V)).e + (U.a * P.b - U.b * P.a) := by
  rw [sqRelWord_rowTuple, sqRelWord_rowTuple]
  simp only [SqU5.mul_e, SqU5.commP_e, SqU5.commP_b, SqU5.mul_a, SqU5.mul_b]
  ring

/-- ⭐⭐ **The `u`-letter's `χ_a`-character is forced to vanish at the uncleared row.**  The
displacement is by the pivot image, whose `b`-column is `1` because `ν'(w) = 1`; the `u`-letter
is `ν'`-trivial, so its `b`-column is `0`.  If both the marking and the cleared frame kill the
relator - the two standards a class-four witness at the uncleared row has to meet - then the
`e`-row equation reads `0 = 0 + U.a`.

This is the exact mirror of `GradedFourHom`'s honest cost.  There the reachable row type was
forced to be the cleared one because the witness's handle slots are the raw generator images;
here the row type is the *uncleared* one, the price is paid on the other letter, and it is a
price about `χ_a` rather than about reachability: **the `u`-letter can never be the odd sigma
dressing at this row.**  The separation must come from the cleared `v`-letter, whose
`χ_a`-character no row constrains - and that is exactly how the point of section 2 is built. -/
theorem rowFour_chiA_handleU_forced (P : SqU5 R) (hPb : P.b = 1) (hUb : U.b = 0)
    (hmark : sqRelWord (rowTuple R S X Y U (V * P)) = 1)
    (hframe : sqRelWord (rowTuple R S X Y U V) = 1) : U.a = 0 := by
  have h := sqRelWord_e_displace (S := S) (X := X) (Y := Y) (U := U) (V := V) P
  rw [hmark, hframe, hPb, hUb, SqU5.one_e] at h
  linear_combination -h

end Obstruction

/-! ## 2 The displaced binder point -/

section Point

/-- **The pivot image** at the committed sigma- and `x₀`-slots, at pivot-exponent residue `c`:
the value `GradedFourHom.sigFourHom_sqPivot` computes, as a standalone tuple. -/
def rowPivotVal (c : gr3R) : SqU5 gr3R := ⟨-(2 * c), 1, 0, 0, 0, 0, 0, 0, -c, c * c + c⟩

/-- **The cleared `V`-letter** of the displaced point: `χ_a = 1`, everything deeper zero.  This
is the committed lane's `U`-letter value, on the other handle slot - the role swap the row type
forces. -/
def rowFourV : SqU5 gr3R := ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- **The `U`-letter** of the displaced point: `χ_a = 0` (forced, by
`rowFour_chiA_handleU_forced`) and `χ_d = 1`, everything deeper zero. -/
def rowFourU : SqU5 gr3R := ⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩

/-- **The `v`-slot of the marking**: the cleared letter displaced by the pivot,
`V = V₀ · Φ(w)`.  This is the whole content of "reaching the uncleared row": the marking's
handle value is *not* the frame's letter. -/
def rowFourVGen (c : gr3R) : SqU5 gr3R := ⟨1 - 2 * c, 1, 0, 0, 1, 0, 0, 0, -c, c * c⟩

/-- …and it really is the displacement. -/
theorem rowFourVGen_eq (c : gr3R) : rowFourVGen c = rowFourV * rowPivotVal c := by
  ext <;> simp only [rowFourVGen, rowFourV, rowPivotVal, SqU5.mul_a, SqU5.mul_b, SqU5.mul_c,
    SqU5.mul_d, SqU5.mul_e, SqU5.mul_f, SqU5.mul_g, SqU5.mul_h, SqU5.mul_i, SqU5.mul_j] <;> ring

/-- …and the cleared letter is recovered from it. -/
theorem rowFourV_eq (c : gr3R) : rowFourVGen c * (rowPivotVal c)⁻¹ = rowFourV := by
  rw [rowFourVGen_eq, mul_inv_cancel_right]

/-- **The marking of the displaced binder point.**  Slots `0, 1, 2` are the committed
`GradedSigmaFour` values, the `u`-slot is the forced `χ_a`-trivial letter, and the `v`-slot is
the cleared letter displaced by the pivot. -/
def rowFourMark (c : gr3R) : Fin (sqRank 1) → SqU5 gr3R :=
  rowTuple gr3R (sigFourMark gr3R) sigFourX sigFourY rowFourU (rowFourVGen c)

/-- **The frame image at sigma-dressing value `v`**: the same tuple with the `v`-slot replaced
by the **cleared** letter.  This is what the Eichler-corrected frame maps to. -/
def rowFourWit (v : SqU5 gr3R) : Fin (sqRank 1) → SqU5 gr3R :=
  rowTuple gr3R (sigFourMark gr3R * v) sigFourX sigFourY rowFourU rowFourV

@[simp] theorem rowFourMark_zero (c : gr3R) : rowFourMark c 0 = sigFourMark gr3R := rowTuple_zero

@[simp] theorem rowFourMark_one (c : gr3R) : rowFourMark c 1 = sigFourX := rowTuple_one

@[simp] theorem rowFourMark_two (c : gr3R) : rowFourMark c 2 = sigFourY := rowTuple_two

@[simp] theorem rowFourMark_handleU (c : gr3R) :
    rowFourMark c (sqHandleIdxU 0) = rowFourU := rowTuple_handleU

@[simp] theorem rowFourMark_handleV (c : gr3R) :
    rowFourMark c (sqHandleIdxV 0) = rowFourVGen c := rowTuple_handleV

@[simp] theorem rowFourWit_zero (v : SqU5 gr3R) :
    rowFourWit v 0 = sigFourMark gr3R * v := rowTuple_zero

@[simp] theorem rowFourWit_one (v : SqU5 gr3R) : rowFourWit v 1 = sigFourX := rowTuple_one

@[simp] theorem rowFourWit_two (v : SqU5 gr3R) : rowFourWit v 2 = sigFourY := rowTuple_two

@[simp] theorem rowFourWit_handleU (v : SqU5 gr3R) :
    rowFourWit v (sqHandleIdxU 0) = rowFourU := rowTuple_handleU

@[simp] theorem rowFourWit_handleV (v : SqU5 gr3R) :
    rowFourWit v (sqHandleIdxV 0) = rowFourV := rowTuple_handleV

/-- The dressed frame image really is the sigma-dressing of the undressed one, so
`GradedSigmaFour`'s general reading applies to it verbatim. -/
theorem rowFourWit_eq_dress (v : SqU5 gr3R) :
    rowFourWit v = sigFourDress (rowFourWit 1) v := by
  funext i
  by_cases h0 : (i : ℕ) = 0
  · have hi : i = 0 := Fin.val_injective (by rw [h0, sqVal_zero])
    subst hi
    rw [sigFourDress_zero, rowFourWit_zero, rowFourWit_zero, mul_one]
  · rw [sigFourDress_ne h0]
    simp only [rowFourWit, rowTuple, if_neg h0]

/-- ⭐⭐ **The ten-row solve at the displaced binder point.**  The marking whose `v`-slot is the
cleared letter times the pivot image kills the relator - all ten rows, at **every** residue `c`
of the pivot exponent, so no oddness hypothesis is carried and the point is not
`sqPivotExp`-conditional.  This is the theorem `GradedFourHom` said was needed and was not
transport. -/
theorem sqRelWord_rowFourMark : ∀ c : gr3R, sqRelWord (rowFourMark c) = 1 := by decide

/-- …and the cleared frame kills it too, so both standards of section 1 are met and the
`χ_a`-obstruction is discharged on the nose. -/
theorem sqRelWord_rowFourWit_triv : sqRelWord (rowFourWit 1) = 1 := by decide

/-- The forced vanishing of the `u`-letter's `χ_a`, exhibited at the point. -/
theorem rowFourU_chiA : rowFourU.a = 0 := rfl

/-- …and the cleared `v`-letter's `χ_a` is **odd**: this is the channel the forcing reads. -/
theorem rowFourV_chiA : selPar rowFourV.a = 1 := by decide

/-- The square of the cleared `v`-letter is the committed lane's `V`-letter value. -/
theorem rowFourV_sq : rowFourV * rowFourV = sigFourV := by decide

end Point

/-! ## 3 The three verdicts at the displaced point -/

section Verdicts

/-- ⭐ **The `V₀²`-dressing leaves the even residue `2`.** -/
theorem sqRelWord_rowFourWit_Vsq : sqRelWord (rowFourWit sigFourV) = liftC 2 := by decide

/-- ⭐⭐ **The `V₀`-dressing leaves the odd residue `1`**: the class-four slice separates two
legal sigma dressings of the same frame at the **uncleared** row. -/
theorem sqRelWord_rowFourWit_V : sqRelWord (rowFourWit rowFourV) = liftC 1 := by decide

/-- The `u`-letter dressing leaves no residue at all - it is `χ_a`-trivial by
`rowFour_chiA_handleU_forced`, and the reading sees nothing else. -/
theorem sqRelWord_rowFourWit_U : sqRelWord (rowFourWit rowFourU) = 1 := by decide

/-- The even residue dies by one explicit achievable `γ₄`-move on the `x₁` slot, exactly as at
the committed cleared-row point. -/
theorem sqRelWord_rowFourWit_Vsq_complete :
    sqRelWord (sigLift 0 (rowFourWit sigFourV) 1 1 (liftC 7) 1 1) = 1 := by decide

/-- ⭐ **Every class-`≤ 3` verdict at the displaced point is the same for all four dressings**:
both `U₄`-quotients of the relator are trivial in each case, so the whole committed class-three
machinery cannot tell them apart.  The separation is purely class-four. -/
theorem rowFourWit_class_three_blind :
    (SqU5.toU4L (sqRelWord (rowFourWit 1)) = 1 ∧
      SqU5.toU4R (sqRelWord (rowFourWit 1)) = 1) ∧
    (SqU5.toU4L (sqRelWord (rowFourWit sigFourV)) = 1 ∧
      SqU5.toU4R (sqRelWord (rowFourWit sigFourV)) = 1) ∧
    (SqU5.toU4L (sqRelWord (rowFourWit rowFourV)) = 1 ∧
      SqU5.toU4R (sqRelWord (rowFourWit rowFourV)) = 1) ∧
    (SqU5.toU4L (sqRelWord (rowFourWit rowFourU)) = 1 ∧
      SqU5.toU4R (sqRelWord (rowFourWit rowFourU)) = 1) := by decide

end Verdicts

/-! ## 4 The displaced point as a homomorphism, and the two cleared letters -/

section RowHom

/-- ⭐⭐ **The displaced-point test hom.**  The section-2 marking kills the relator, so the
committed lift turns it into an honest continuous homomorphism `D_sq 1 → U_5(ℤ/8)` whose
`v`-slot value is the cleared letter displaced by the pivot. -/
noncomputable def rowFourHom : ContinuousMonoidHom (DSq 1 : Type) (SqU5 gr3R) :=
  sqU5Hom gr3R_card 1 (rowFourMark (gr3Pi sqPivotExp)) (sqRelWord_rowFourMark _)

@[simp] theorem rowFourHom_gen (i : Fin (sqRank 1)) :
    rowFourHom (sqGen 1 i) = rowFourMark (gr3Pi sqPivotExp) i :=
  sqU5Hom_gen _ _ _ i

@[simp] theorem rowFourHom_sigma : rowFourHom (dsqSigma 1) = sigFourMark gr3R := by
  rw [dsqSigma, rowFourHom_gen, rowFourMark_zero]

@[simp] theorem rowFourHom_x0 : rowFourHom (dsqX0 1) = sigFourX := by
  rw [dsqX0, rowFourHom_gen, rowFourMark_one]

@[simp] theorem rowFourHom_x1 : rowFourHom (dsqX1 1) = sigFourY := by
  rw [dsqX1, rowFourHom_gen, rowFourMark_two]

@[simp] theorem rowFourHom_handleU : rowFourHom (sqGen 1 (sqHandleIdxU 0)) = rowFourU := by
  rw [rowFourHom_gen, rowFourMark_handleU]

@[simp] theorem rowFourHom_handleV :
    rowFourHom (sqGen 1 (sqHandleIdxV 0)) = rowFourVGen (gr3Pi sqPivotExp) := by
  rw [rowFourHom_gen, rowFourMark_handleV]

/-- ⭐ **The pivot anchor at the displaced point.**  The sigma- and `x₀`-slots are the committed
ones, so the even-obstruction power lemma applies verbatim and the pivot image is
`GradedFourHom.sigFourHom_sqPivot`'s tuple. -/
theorem rowFourHom_sqPivot : rowFourHom (sqPivot 1) = rowPivotVal (gr3Pi sqPivotExp) := by
  rw [sqPivot, sqMixPivotElem, map_mul, map_inv,
    map_zpowZtwo (isProP_DSq 1) isProP_two_gr5, rowFourHom_x0, sigFourX_zpowZtwo,
    rowFourHom_sigma]
  ext <;> simp [sigFourMark, rowPivotVal]
  ring

/-- The uncleared row leaves the `u`-letter `ν'`-trivial… -/
theorem nuSelRow_handleU : nuSel 1 0 0 1 (sqGen 1 (sqHandleIdxU 0)) = 1 := by
  rw [nuSel_handleU, ofAdd_zero]

/-- …and the `v`-letter `ν'`-**nontrivial**: this is exactly what the cleared row does not do,
and what forces the section-2 solve. -/
theorem nuSelRow_handleV :
    nuSel 1 0 0 1 (sqGen 1 (sqHandleIdxV 0)) = ofAdd (1 : ℤ_[2]) := nuSel_handleV

/-- ⭐ The cleared `u`-letter is the raw letter: `ν'(u₀) = 0`, so no pivot power is
subtracted. -/
theorem rowFourHom_sqEichU : rowFourHom (sqEichU 1 (nuSel 1 0 0 1) 0) = rowFourU := by
  rw [sqEichU_of_cleared nuSelRow_handleU, rowFourHom_handleU]

/-- ⭐⭐ **The cleared `v`-letter is the point's `V`-letter.**  `ν'(v₀) = 1` on the nose, so
exactly one inverse pivot is subtracted - and the marking was built so that the subtraction
lands on `rowFourV`.  This is the whole payoff of the ten-row solve: at the uncleared row the
Eichler-corrected frame's `V`-slot has an honest, prescribed image. -/
theorem rowFourHom_sqEichV : rowFourHom (sqEichV 1 (nuSel 1 0 0 1) 0) = rowFourV := by
  rw [sqEichV, map_mul, map_inv, map_zpowZtwo (isProP_DSq 1) isProP_two_gr5, nuSel_handleV,
    toAdd_ofAdd, zpowZtwo_one_exp, rowFourHom_sqPivot, rowFourHom_handleV, rowFourV_eq]

/-- ⭐ **The `b`-column of the displaced hom is the uncleared selected row** `nuSel 1 0 0 1`,
reduced mod `8`.  Two continuous homs agreeing on the five generators; the `v`-slot's `b`-entry
is `1` precisely because the row is uncleared. -/
theorem rowFourHom_b (x : (DSq 1 : Type)) :
    (rowFourHom x).b = gr3Pi (toAdd (nuSel 1 0 0 1 x)) := by
  have hext : bProjC.comp rowFourHom = nuBC.comp (nuSel 1 0 0 1) := by
    refine dsq_hom_ext _ _ fun i => ?_
    rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
    · show bProjC (rowFourHom (dsqSigma 1)) = nuBC (nuSel 1 0 0 1 (dsqSigma 1))
      rw [rowFourHom_sigma, nuSel_sigma, bProjC_apply, nuBC_apply, toAdd_ofAdd, map_one]
      rfl
    · show bProjC (rowFourHom (dsqX0 1)) = nuBC (nuSel 1 0 0 1 (dsqX0 1))
      rw [rowFourHom_x0, nuSel_x0, bProjC_apply, nuBC_apply, toAdd_ofAdd, map_zero]
      rfl
    · show bProjC (rowFourHom (dsqX1 1)) = nuBC (nuSel 1 0 0 1 (dsqX1 1))
      rw [rowFourHom_x1, nuSel_x1, bProjC_apply, nuBC_apply, toAdd_one, map_zero]
      rfl
    · rw [Subsingleton.elim j' 0]
      show bProjC (rowFourHom (sqGen 1 (sqHandleIdxU 0)))
        = nuBC (nuSel 1 0 0 1 (sqGen 1 (sqHandleIdxU 0)))
      rw [rowFourHom_handleU, nuSelRow_handleU, bProjC_apply, nuBC_apply, toAdd_one, map_zero]
      rfl
    · rw [Subsingleton.elim j' 0]
      show bProjC (rowFourHom (sqGen 1 (sqHandleIdxV 0)))
        = nuBC (nuSel 1 0 0 1 (sqGen 1 (sqHandleIdxV 0)))
      rw [rowFourHom_handleV, nuSelRow_handleV, bProjC_apply, nuBC_apply, toAdd_ofAdd, map_one]
      rfl
  exact congrArg SqU5.b (DFunLike.congr_fun hext x)

/-- A `ν'`-trivial element has vanishing `b`-column at the displaced hom. -/
theorem rowFourHom_b_eq_zero {g : (DSq 1 : Type)} (hg : nuSel 1 0 0 1 g = 1) :
    (rowFourHom g).b = 0 := by
  rw [rowFourHom_b, hg, toAdd_one, map_zero]

/-- ⭐⭐ **The frame identification at the UNCLEARED row.**  The displaced hom sends the
arbitrary-dressing frame with a sigma-only dressing `g` to exactly the displaced witness at
the dressing value.  This is `GradedFourHom.sigFourHom_sqArbFrame` at the row that file could
not reach: there the identification needed both handle letters `ν'`-cleared, here the `v`-letter
carries `ν'(v₀) = 1` and the pivot power is absorbed by the marking. -/
theorem rowFourHom_sqArbFrame (g : (DSq 1 : Type)) :
    (fun i => rowFourHom (sqArbFrame 1 (nuSel 1 0 0 1) 0 (sigArbDress 1 g) i))
      = rowFourWit (rowFourHom g) := by
  funext i
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [sqArbFrame, sqArbBase_zero, sigArbDress_zero, map_mul, rowFourHom_sigma,
      rowFourWit_zero]
  · rw [sqArbFrame, sqArbBase_one, sigArbDress_ne (by rw [sqVal_one]; omega), mul_one,
      rowFourHom_x0, rowFourWit_one]
  · rw [sqArbFrame, sqArbBase_two, sigArbDress_ne (by rw [sqVal_two]; omega), mul_one,
      rowFourHom_x1, rowFourWit_two]
  · rw [Subsingleton.elim j' 0, sqArbFrame, sqArbBase_handleU,
      sigArbDress_ne (by rw [sqHandleIdxU_val]; omega), mul_one, rowFourHom_sqEichU,
      rowFourWit_handleU]
  · rw [Subsingleton.elim j' 0, sqArbFrame, sqArbBase_handleV,
      sigArbDress_ne (by rw [sqHandleIdxV_val]; omega), mul_one, rowFourHom_sqEichV,
      rowFourWit_handleV]

end RowHom

/-! ## 5 The selection bit at the displaced point -/

section Bit

/-- ⭐⭐ **The class-four selection bit at the displaced point is the sigma dressing's
`chi_a`-character, mod 2** - the same functional as at the committed cleared-row point, because
the `x₀`- and `x₁`-slots are the committed ones and the gauge is untouched.  What changed is
*which* legal dressings can realise an odd value. -/
theorem rowFourWit_bit {v : SqU5 gr3R} (hvb : v.b = 0) :
    selPar ((sqRelWord (rowFourWit v)).j) = selPar v.a := by
  have hm0 : rowFourWit (1 : SqU5 gr3R) 0 = sigFourMark gr3R := by
    rw [rowFourWit_zero, mul_one]
  have hxb : (rowFourWit (1 : SqU5 gr3R) 1).b = 0 := by rw [rowFourWit_one]; decide
  have hyb : (rowFourWit (1 : SqU5 gr3R) 2).b = 0 := by rw [rowFourWit_two]; decide
  obtain ⟨-, -, -, hj⟩ := sqRelWord_sigFourDress (m := rowFourWit 1) (v := v) hm0 hxb hyb hvb
  rw [rowFourWit_eq_dress v, hj, sqRelWord_rowFourWit_triv, rowFourWit_one, rowFourWit_two,
    SqU5.one_j, zero_add,
    sigFourRead_gauge_par (v := v) (x := sigFourX) (y := sigFourY) (xa := 1) (xc := 0)
      (xd := 0) (xe := 0) (xf := 0) (ya := 0) (yc := 0) (yd := 0)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide),
    show (sigFourX.g + sigFourX.i : gr3R) = 1 by decide,
    show (sigFourX.h : gr3R) = 0 by decide, show (sigFourX.g : gr3R) = 0 by decide,
    mul_one, mul_zero, mul_zero, selPar_zero, add_zero, add_zero]

end Bit

/-! ## 6 Soundness: every achievable increment is even -/

section Soundness

/-- ⭐ **The committed achievable lattice is even at the displaced point**, both coordinates,
at every `(P, Q, R)`.  The point's parameters are `(A, B, C, D, E, F, T, S) = (0, 1, 0, 0, 1,
0, 0, 1)`: `A = 0` is the forced vanishing of `χ_a(u₀)`, `B = 1` is the odd `χ_a` of the
cleared `v`-letter, and `(T, S) = (0, 1)` is the uncleared row itself. -/
theorem rowFourWit_lamThree_even {P Q R : gr3R} {z : SqU5 gr3R}
    (hz : selLamThree 0 1 0 0 1 0 0 1 P Q R z) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) := by
  obtain ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, hh, hi⟩ := hz
  exact ⟨⟨r₇ * Q, by rw [hh]; ring⟩,
    ⟨r₅ * R - r₆ * Q + r₇ * R, by rw [hi]; ring⟩⟩

/-! ### The three `γ₂`-level moves of `GradedGammaTwo`, at the displaced point

`GradedGammaTwo` found the three commutators of the `x₁`-slot letter against `σ`, `U` and `V`
outside the committed lattice.  At the displaced point they are computed outright below: their
`(h, i)`-data are `(0, 4)`, `(0, 0)` and `(0, 0)`, i.e. the extended lattice's parameters are
`(P, Q, R) = (0, 0, 4)` here, and every one of them is **even**.  So the three moves that
unlocked wave 54's dead-end corners cannot unlock this point. -/

/-- The `σ`-`x₁` commutator at the displaced point: `(h, i) = (0, 4)`, i.e. `R = 4`. -/
theorem rowFourWit_commP_zero_two :
    commP (rowFourWit 1 0) (rowFourWit 1 2) = (⟨0, 0, 0, 0, 0, 0, 0, 0, 4, 0⟩ : SqU5 gr3R) := by
  decide

/-- The `x₁`-`U` commutator: trivial, i.e. `(P·C − Q·A, Q·E) = (0, 0)`. -/
theorem rowFourWit_commP_two_handleU :
    commP (rowFourWit 1 2) (rowFourWit 1 (sqHandleIdxU 0)) = 1 := by decide

/-- The `x₁`-`V` commutator: central, i.e. `(P·D − Q·B, Q·F) = (0, 0)`. -/
theorem rowFourWit_commP_two_handleV :
    commP (rowFourWit 1 2) (rowFourWit 1 (sqHandleIdxV 0))
      = (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 6⟩ : SqU5 gr3R) := by decide

/-- ⭐ **The extended lattice is even at the displaced point too**, at the point's own
extended-lattice data `(P, Q, R) = (0, 0, 4)` read off the three commutators above. -/
theorem rowFourWit_lamThreePlus_even {z : SqU5 gr3R}
    (hz : selLamThreePlus 0 1 0 0 1 0 0 1 0 0 4 z) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) := by
  obtain ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, t₁, t₂, t₃, hh, hi⟩ := hz
  exact ⟨⟨0, by rw [hh]; ring⟩,
    ⟨4 * r₅ + 4 * r₇ + 2 * t₁, by rw [hi]; ring⟩⟩

/-! ### The `γ₂` level, without a lattice model

Both statements above quantify over a *model* of what is achievable.  The displaced point
admits a stronger soundness that quantifies over nothing but the group: the subgroup generated
by the marking has vanishing third abelian column, vanishing second class-two coordinate and
**even** third class-two coordinate, and those three invariants force every commutator of two
of its elements to have vanishing first class-three coordinate and **even** second one.  Hence
the whole commutator subgroup `γ₂(im Φ)` - which is what the achievability convention of
`GradedGammaTwo` allows a dressing to be drawn from, quadratic terms and all - is even in the
two coordinates the translation identity reads. -/

/-- The subgroup cut out by the three invariants the displaced marking satisfies. -/
def rowFrameSub (R : Type) [CommRing R] : Subgroup (SqU5 R) where
  carrier := {p | p.c = 0 ∧ p.f = 0 ∧ ∃ k : R, p.g = 2 * k}
  mul_mem' := fun {p q} hp hq => by
    obtain ⟨hpc, hpf, kp, hpg⟩ := hp
    obtain ⟨hqc, hqf, kq, hqg⟩ := hq
    exact ⟨by rw [SqU5.mul_c, hpc, hqc]; ring,
      by rw [SqU5.mul_f, hpf, hqf, hqc]; ring,
      kp + kq, by rw [SqU5.mul_g, hpg, hqg, hpc]; ring⟩
  one_mem' := ⟨rfl, rfl, 0, by rw [SqU5.one_g]; ring⟩
  inv_mem' := fun {p} hp => by
    obtain ⟨hpc, hpf, kp, hpg⟩ := hp
    exact ⟨by rw [SqU5.inv_c, hpc]; ring,
      by rw [SqU5.inv_f, hpc, hpf]; ring,
      -kp, by rw [SqU5.inv_g, hpc, hpg]; ring⟩

theorem mem_rowFrameSub {R : Type} [CommRing R] {p : SqU5 R} :
    p ∈ rowFrameSub R ↔ p.c = 0 ∧ p.f = 0 ∧ ∃ k : R, p.g = 2 * k := Iff.rfl

/-- The subgroup where every `γ₂`-level commutator of the displaced frame lands. -/
def rowGaTwoSub (R : Type) [CommRing R] : Subgroup (SqU5 R) where
  carrier := {p | p.a = 0 ∧ p.b = 0 ∧ p.c = 0 ∧ p.d = 0 ∧ p.f = 0 ∧ p.g = 0 ∧ p.h = 0 ∧
    ∃ k : R, p.i = 2 * k}
  mul_mem' := fun {p q} hp hq => by
    obtain ⟨hpa, hpb, hpc, hpd, hpf, hpg, hph, kp, hpi⟩ := hp
    obtain ⟨hqa, hqb, hqc, hqd, hqf, hqg, hqh, kq, hqi⟩ := hq
    exact ⟨by rw [SqU5.mul_a, hpa, hqa]; ring, by rw [SqU5.mul_b, hpb, hqb]; ring,
      by rw [SqU5.mul_c, hpc, hqc]; ring, by rw [SqU5.mul_d, hpd, hqd]; ring,
      by rw [SqU5.mul_f, hpf, hqf, hqc]; ring, by rw [SqU5.mul_g, hpg, hqg, hpc]; ring,
      by rw [SqU5.mul_h, hph, hqh, hqf, hqc]; ring,
      kp + kq, by rw [SqU5.mul_i, hpi, hqi, hpb, hpf]; ring⟩
  one_mem' := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, 0, by rw [SqU5.one_i]; ring⟩
  inv_mem' := fun {p} hp => by
    obtain ⟨hpa, hpb, hpc, hpd, hpf, hpg, hph, kp, hpi⟩ := hp
    exact ⟨by rw [SqU5.inv_a, hpa]; ring, by rw [SqU5.inv_b, hpb]; ring,
      by rw [SqU5.inv_c, hpc]; ring, by rw [SqU5.inv_d, hpd]; ring,
      by rw [SqU5.inv_f, hpc, hpf]; ring, by rw [SqU5.inv_g, hpc, hpg]; ring,
      by rw [SqU5.inv_h, hpa, hpc, hph]; ring,
      -kp, by rw [SqU5.inv_i, hpb, hpd, hpi]; ring⟩

theorem mem_rowGaTwoSub {R : Type} [CommRing R] {p : SqU5 R} :
    p ∈ rowGaTwoSub R ↔ p.a = 0 ∧ p.b = 0 ∧ p.c = 0 ∧ p.d = 0 ∧ p.f = 0 ∧ p.g = 0 ∧ p.h = 0 ∧
      ∃ k : R, p.i = 2 * k := Iff.rfl

/-- ⭐⭐ **The one algebraic fact behind the model-independent soundness**: a commutator of two
elements with vanishing `c`- and `f`-columns and even `g`-column has **vanishing** first
class-three coordinate and **even** second one.  Both class-three coordinates of the
translation identity are therefore even for any such dressing, whatever its shape. -/
theorem commP_mem_rowGaTwoSub {R : Type} [CommRing R] {p q : SqU5 R}
    (hp : p ∈ rowFrameSub R) (hq : q ∈ rowFrameSub R) : commP p q ∈ rowGaTwoSub R := by
  obtain ⟨hpc, hpf, kp, hpg⟩ := hp
  obtain ⟨hqc, hqf, kq, hqg⟩ := hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, p.b * kq - kp * q.b, ?_⟩ <;>
    simp only [SqU5.commP_a, SqU5.commP_b, SqU5.commP_c, SqU5.commP_d, SqU5.commP_f,
      SqU5.commP_g, SqU5.commP_h, SqU5.commP_i, SqU5.u5Comm3L, SqU5.u5Comm3R,
      hpc, hqc, hpf, hqf, hpg, hqg] <;>
    ring

/-- **The `γ₂`-level dressing set** of a subgroup: the subgroup generated by all commutators of
its elements.  Under `GradedGammaTwo`'s achievability convention - a test hom carries `γ₂` of
the honest group onto `γ₂` of its image - this is exactly what a `γ₂`-level dressing may be
drawn from, quadratic terms included. -/
def rowGaTwoOf {R : Type} [CommRing R] (K : Subgroup (SqU5 R)) : Subgroup (SqU5 R) :=
  Subgroup.closure {z : SqU5 R | ∃ p ∈ K, ∃ q ∈ K, z = commP p q}

/-- Every slot of the displaced marking satisfies the three invariants. -/
theorem rowFourMark_le_rowFrameSub (c : gr3R) :
    Subgroup.closure (Set.range (rowFourMark c)) ≤ rowFrameSub gr3R := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · exact ⟨rfl, rfl, 0, by rw [rowFourMark_zero]; show (0 : gr3R) = 2 * 0; ring⟩
  · exact ⟨rfl, rfl, 0, by rw [rowFourMark_one]; show (0 : gr3R) = 2 * 0; ring⟩
  · exact ⟨rfl, rfl, 2, by rw [rowFourMark_two]; show (4 : gr3R) = 2 * 2; decide⟩
  · rw [Subsingleton.elim j' 0]
    exact ⟨rfl, rfl, 0, by rw [rowFourMark_handleU]; show (0 : gr3R) = 2 * 0; ring⟩
  · rw [Subsingleton.elim j' 0]
    exact ⟨rfl, rfl, 0, by rw [rowFourMark_handleV]; show (0 : gr3R) = 2 * 0; ring⟩

/-- ⭐⭐ **The model-independent soundness at the displaced point.**  The whole commutator
subgroup of the marking's image - the object the achievability convention lets a `γ₂`-level
dressing be drawn from - has vanishing first class-three coordinate and even second one.  This
is strictly stronger than both lattice statements above: it quantifies over the group rather
than over a generating model, and it covers the quadratic part of the `γ₂` defect
automatically. -/
theorem rowFour_commutator_le (c : gr3R) :
    rowGaTwoOf (Subgroup.closure (Set.range (rowFourMark c))) ≤ rowGaTwoSub gr3R := by
  rw [rowGaTwoOf, Subgroup.closure_le]
  rintro z ⟨p, hp, q, hq, rfl⟩
  exact commP_mem_rowGaTwoSub (rowFourMark_le_rowFrameSub c hp)
    (rowFourMark_le_rowFrameSub c hq)

/-- …in the form the increment lemma consumes. -/
theorem rowFour_gaTwo_even {c : gr3R} {z : SqU5 gr3R}
    (hz : z ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowFourMark c)))) :
    z.h = 0 ∧ ∃ k : gr3R, z.i = 2 * k := by
  obtain ⟨-, -, -, -, -, -, hh, hi⟩ := rowFour_commutator_le c hz
  exact ⟨hh, hi⟩

/-- **The image of the displaced hom is the closure of the marking**, so the previous theorem
really is a statement about `γ₂(im Φ)`: `D_sq 1` is topologically generated by its five
letters (`dsq_topGen`), the preimage of a subgroup of a discrete group is closed, and the
minimality of the topological closure does the rest. -/
theorem rowFourHom_mem_closure (x : (DSq 1 : Type)) :
    rowFourHom x ∈ Subgroup.closure (Set.range (rowFourMark (gr3Pi sqPivotExp))) := by
  have hgen : Subgroup.closure (Set.range (sqGen 1))
      ≤ Subgroup.comap rowFourHom.toMonoidHom
        (Subgroup.closure (Set.range (rowFourMark (gr3Pi sqPivotExp)))) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    show rowFourHom (sqGen 1 i) ∈ Subgroup.closure (Set.range (rowFourMark (gr3Pi sqPivotExp)))
    rw [rowFourHom_gen]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hclosed : IsClosed ((Subgroup.comap rowFourHom.toMonoidHom
      (Subgroup.closure (Set.range (rowFourMark (gr3Pi sqPivotExp)))) :
        Subgroup (DSq 1 : Type)) : Set (DSq 1 : Type)) := by
    have hpre : ((Subgroup.comap rowFourHom.toMonoidHom
        (Subgroup.closure (Set.range (rowFourMark (gr3Pi sqPivotExp)))) :
          Subgroup (DSq 1 : Type)) : Set (DSq 1 : Type))
        = rowFourHom ⁻¹' ((Subgroup.closure (Set.range (rowFourMark (gr3Pi sqPivotExp)))) :
            Set (SqU5 gr3R)) := rfl
    rw [hpre]
    exact (isClosed_discrete _).preimage rowFourHom.continuous_toFun
  have hle := Subgroup.topologicalClosure_minimal _ hgen hclosed
  rw [dsq_topGen 1] at hle
  exact hle (Subgroup.mem_top x)

/-! ### The increments -/

/-- ⭐ **The five-slot increment at the displaced point is even**, for every committed-lattice
dressing. -/
theorem rowFourWit_increment_even {P Q R : gr3R} {z₀ z₃ z₄ w₁ w₂ : SqU5 gr3R}
    (_l₀ : selLamThree 0 1 0 0 1 0 0 1 P Q R z₀)
    (l₃ : selLamThree 0 1 0 0 1 0 0 1 P Q R z₃)
    (l₄ : selLamThree 0 1 0 0 1 0 0 1 P Q R z₄) (v : SqU5 gr3R) :
    ∃ k : gr3R, (z₀.h * (rowFourWit v 1).d - z₀.i * (rowFourWit v 1).a)
        + (-4 * w₁.j + 2 * w₂.j)
        + ((z₃.h * (rowFourWit v (sqHandleIdxV 0)).d
            - z₃.i * (rowFourWit v (sqHandleIdxV 0)).a)
          + ((rowFourWit v (sqHandleIdxU 0)).a * z₄.i
            - (rowFourWit v (sqHandleIdxU 0)).d * z₄.h)) = 2 * k := by
  obtain ⟨-, ⟨b₃, hb₃⟩⟩ := rowFourWit_lamThree_even l₃
  obtain ⟨⟨a₄, ha₄⟩, -⟩ := rowFourWit_lamThree_even l₄
  refine ⟨-z₀.i - 2 * w₁.j + w₂.j - b₃ - a₄, ?_⟩
  rw [rowFourWit_one, rowFourWit_handleU, rowFourWit_handleV, hb₃, ha₄]
  simp only [rowFourU, rowFourV, sigFourX]
  ring

/-- ⭐⭐ …and for every `γ₂`-level dressing, with no lattice model at all. -/
theorem rowFourWit_increment_even_gaTwo {c : gr3R} {z₀ z₃ z₄ w₁ w₂ : SqU5 gr3R}
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowFourMark c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowFourMark c)))) (v : SqU5 gr3R) :
    ∃ k : gr3R, (z₀.h * (rowFourWit v 1).d - z₀.i * (rowFourWit v 1).a)
        + (-4 * w₁.j + 2 * w₂.j)
        + ((z₃.h * (rowFourWit v (sqHandleIdxV 0)).d
            - z₃.i * (rowFourWit v (sqHandleIdxV 0)).a)
          + ((rowFourWit v (sqHandleIdxU 0)).a * z₄.i
            - (rowFourWit v (sqHandleIdxU 0)).d * z₄.h)) = 2 * k := by
  obtain ⟨-, b₃, hb₃⟩ := rowFour_gaTwo_even l₃
  obtain ⟨ha₄, -⟩ := rowFour_gaTwo_even l₄
  refine ⟨-z₀.i - 2 * w₁.j + w₂.j - b₃, ?_⟩
  rw [rowFourWit_one, rowFourWit_handleU, rowFourWit_handleV, hb₃, ha₄]
  simp only [rowFourU, rowFourV, sigFourX]
  ring

end Soundness

/-! ## 7 The sigma forcing at the uncleared row -/

section Forcing

/-- ⭐⭐ **The sigma-slot forcing at the displaced point**, against the committed achievable
lattice: a sigma dressing whose frame is killed by **any** achievable five-slot class-four
refinement has an **even** `chi_a`-character.  This is `GradedSigmaFour.sigFourWit_sigma_forced`
at the **uncleared** row. -/
theorem rowFourWit_sigma_forced {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hvb : v.b = 0) (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₀ : selLamThree 0 1 0 0 1 0 0 1 P Q R z₀)
    (l₃ : selLamThree 0 1 0 0 1 0 0 1 P Q R z₃)
    (l₄ : selLamThree 0 1 0 0 1 0 0 1 P Q R z₄)
    (hkill : sqRelWord (sigLift 0 (rowFourWit v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 := by
  rw [sqRelWord_sigLift hz₀ hw₁ hw₂ hz₃ hz₄] at hkill
  obtain ⟨k, hk⟩ := rowFourWit_increment_even (w₁ := w₁) (w₂ := w₂) l₀ l₃ l₄ v
  rw [hk, mul_liftC_apply] at hkill
  have hj := congrArg SqU5.j hkill
  simp only [SqU5.one_j] at hj
  have hp := congrArg selPar hj
  rw [selPar_add, selPar_two_mul, add_zero, rowFourWit_bit hvb, selPar_zero] at hp
  exact hp

/-- ⭐⭐ **The same forcing with no lattice model**: the two handle dressings are only required
to lie in the commutator subgroup of the marking's image, and the sigma-slot dressing is
**unconstrained** (its increment reads the `x₀`-slot's even `chi_a` and is even outright).  This
is a strictly stronger soundness than any committed class-four forcing carries. -/
theorem rowFourWit_sigma_forced_gaTwo {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hvb : v.b = 0) (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowFourMark c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowFourMark c))))
    (hkill : sqRelWord (sigLift 0 (rowFourWit v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 := by
  rw [sqRelWord_sigLift hz₀ hw₁ hw₂ hz₃ hz₄] at hkill
  obtain ⟨k, hk⟩ := rowFourWit_increment_even_gaTwo (z₀ := z₀) (w₁ := w₁) (w₂ := w₂) l₃ l₄ v
  rw [hk, mul_liftC_apply] at hkill
  have hj := congrArg SqU5.j hkill
  simp only [SqU5.one_j] at hj
  have hp := congrArg selPar hj
  rw [selPar_add, selPar_two_mul, add_zero, rowFourWit_bit hvb, selPar_zero] at hp
  exact hp

/-! ### The legal dressings at the uncleared row

At `nuSel 1 0 0 1` the letters `σ`, `x₀` and `x₁` are all `λ`- or `ν'`-nontrivial, so the class
the residual quantifies over is generated by the `u`-letter and the **cleared** `v`-letter.  The
`u`-letter's `chi_a` is forced to vanish (section 1); the cleared `v`-letter's is odd.  That is
the whole separation, and it is the exact dual of the cleared-row picture. -/

/-- The cleared `v`-letter is `λ`-trivial. -/
theorem nuLam_rowEichV : nuLam 1 (sqEichV 1 (nuSel 1 0 0 1) 0) = 1 :=
  Multiplicative.toAdd.injective (by rw [toAdd_nuLam_sqEichV, toAdd_one])

/-- …and `ν'`-trivial: it lies in the class the residual quantifies over, even though the
`v`-letter itself does not. -/
theorem nu_rowEichV : nuSel 1 0 0 1 (sqEichV 1 (nuSel 1 0 0 1) 0) = 1 :=
  Multiplicative.toAdd.injective (by rw [toAdd_nu_sqEichV nuSel_sigma nuSel_x0, toAdd_one])

/-- The square of the cleared `v`-letter is legal too. -/
theorem nuLam_rowEichV_sq :
    nuLam 1 (sqEichV 1 (nuSel 1 0 0 1) 0 * sqEichV 1 (nuSel 1 0 0 1) 0) = 1 := by
  rw [map_mul, nuLam_rowEichV, one_mul]

theorem nu_rowEichV_sq :
    nuSel 1 0 0 1 (sqEichV 1 (nuSel 1 0 0 1) 0 * sqEichV 1 (nuSel 1 0 0 1) 0) = 1 := by
  rw [map_mul, nu_rowEichV, one_mul]

/-- ⭐⭐ **The forcing is not vacuous**: the cleared `v`-letter is a legal sigma dressing - `λ`-
and `ν'`-trivial - with an **odd** `chi_a`-character.  Without this the forcing would be an
empty statement; it is what makes the displaced point worth reaching. -/
theorem rowFour_forcing_nonvacuous :
    nuLam 1 (sqEichV 1 (nuSel 1 0 0 1) 0) = 1 ∧
      nuSel 1 0 0 1 (sqEichV 1 (nuSel 1 0 0 1) 0) = 1 ∧
      selPar (rowFourHom (sqEichV 1 (nuSel 1 0 0 1) 0)).a = 1 :=
  ⟨nuLam_rowEichV, nu_rowEichV, by rw [rowFourHom_sqEichV]; exact rowFourV_chiA⟩

/-- The cleared-`v` dressing is `λ`-trivial slotwise. -/
theorem nuLam_sigArbDress_rowV (i : Fin (sqRank 1)) :
    nuLam 1 (sigArbDress 1 (sqEichV 1 (nuSel 1 0 0 1) 0) i) = 1 :=
  nuLam_sigArbDress nuLam_rowEichV i

/-- …and `ν'`-trivial slotwise. -/
theorem nu_sigArbDress_rowV (i : Fin (sqRank 1)) :
    nuSel 1 0 0 1 (sigArbDress 1 (sqEichV 1 (nuSel 1 0 0 1) 0) i) = 1 :=
  nu_sigArbDress nu_rowEichV i

theorem nuLam_sigArbDress_rowVsq (i : Fin (sqRank 1)) :
    nuLam 1 (sigArbDress 1
      (sqEichV 1 (nuSel 1 0 0 1) 0 * sqEichV 1 (nuSel 1 0 0 1) 0) i) = 1 :=
  nuLam_sigArbDress nuLam_rowEichV_sq i

theorem nu_sigArbDress_rowVsq (i : Fin (sqRank 1)) :
    nuSel 1 0 0 1 (sigArbDress 1
      (sqEichV 1 (nuSel 1 0 0 1) 0 * sqEichV 1 (nuSel 1 0 0 1) 0) i) = 1 :=
  nu_sigArbDress nu_rowEichV_sq i

/-! ### The verdicts on `sqArbFrame` at the uncleared row -/

/-- ⭐ **The undressed frame kills the relator outright** at the uncleared row: all ten rows
vanish, so the displaced hom is a genuine class-four quotient of the Eichler-corrected frame
and the gate is live. -/
theorem sqRelWord_rowFrame_sigTriv :
    sqRelWord (fun i =>
      rowFourHom (sqArbFrame 1 (nuSel 1 0 0 1) 0 (sigArbDress 1 1) i)) = 1 := by
  rw [rowFourHom_sqArbFrame, map_one]
  exact sqRelWord_rowFourWit_triv

/-- ⭐ **The squared cleared-`v` dressing leaves the even residue `2`.** -/
theorem sqRelWord_rowFrame_sigVsq :
    sqRelWord (fun i => rowFourHom (sqArbFrame 1 (nuSel 1 0 0 1) 0
      (sigArbDress 1 (sqEichV 1 (nuSel 1 0 0 1) 0 * sqEichV 1 (nuSel 1 0 0 1) 0)) i))
      = liftC 2 := by
  rw [rowFourHom_sqArbFrame, map_mul, rowFourHom_sqEichV, rowFourV_sq]
  exact sqRelWord_rowFourWit_Vsq

/-- ⭐⭐ **The cleared-`v` dressing leaves the odd residue `1`**: the class-four slice separates
two legal sigma dressings of the same frame over the same hom, at the **uncleared** row. -/
theorem sqRelWord_rowFrame_sigV :
    sqRelWord (fun i => rowFourHom (sqArbFrame 1 (nuSel 1 0 0 1) 0
      (sigArbDress 1 (sqEichV 1 (nuSel 1 0 0 1) 0)) i)) = liftC 1 := by
  rw [rowFourHom_sqArbFrame, rowFourHom_sqEichV]
  exact sqRelWord_rowFourWit_V

/-- The even residue dies by one explicit achievable `γ₄`-move on the `x₁` slot. -/
theorem sqRelWord_rowFrame_sigVsq_complete :
    sqRelWord (sigLift 0 (fun i => rowFourHom (sqArbFrame 1 (nuSel 1 0 0 1) 0
      (sigArbDress 1 (sqEichV 1 (nuSel 1 0 0 1) 0 * sqEichV 1 (nuSel 1 0 0 1) 0)) i))
      1 1 (liftC 7) 1 1) = 1 := by
  rw [rowFourHom_sqArbFrame, map_mul, rowFourHom_sqEichV, rowFourV_sq]
  exact sqRelWord_rowFourWit_Vsq_complete

/-- ⭐⭐ **The odd dressing survives nothing**: no achievable five-slot class-four refinement of
the frame's image kills the relator.  Soundness is a theorem, not a hypothesis. -/
theorem sqRelWord_rowFrame_sigV_ne_one {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₀ : selLamThree 0 1 0 0 1 0 0 1 P Q R z₀)
    (l₃ : selLamThree 0 1 0 0 1 0 0 1 P Q R z₃)
    (l₄ : selLamThree 0 1 0 0 1 0 0 1 P Q R z₄) :
    sqRelWord (sigLift 0 (fun i => rowFourHom (sqArbFrame 1 (nuSel 1 0 0 1) 0
      (sigArbDress 1 (sqEichV 1 (nuSel 1 0 0 1) 0)) i)) z₀ w₁ w₂ z₃ z₄) ≠ 1 := by
  rw [rowFourHom_sqArbFrame, rowFourHom_sqEichV]
  intro hc
  have hpar := rowFourWit_sigma_forced (v := rowFourV) (by decide) hz₀ hw₁ hw₂ hz₃ hz₄
    l₀ l₃ l₄ hc
  rw [show (rowFourV.a : gr3R) = 1 from rfl] at hpar
  exact absurd hpar (by decide)

/-- ⭐⭐ …and it survives nothing at the `γ₂` level either, with the two handle dressings drawn
from the commutator subgroup of the image and the sigma dressing free. -/
theorem sqRelWord_rowFrame_sigV_ne_one_gaTwo {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowFourMark c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowFourMark c)))) :
    sqRelWord (sigLift 0 (fun i => rowFourHom (sqArbFrame 1 (nuSel 1 0 0 1) 0
      (sigArbDress 1 (sqEichV 1 (nuSel 1 0 0 1) 0)) i)) z₀ w₁ w₂ z₃ z₄) ≠ 1 := by
  rw [rowFourHom_sqArbFrame, rowFourHom_sqEichV]
  intro hc
  have hpar := rowFourWit_sigma_forced_gaTwo (v := rowFourV) (by decide) hz₀ hw₁ hw₂ hz₃ hz₄
    l₃ l₄ hc
  rw [show (rowFourV.a : gr3R) = 1 from rfl] at hpar
  exact absurd hpar (by decide)

/-! ### The headline -/

/-- ⭐⭐ **The class-four selection bit on `sqArbFrame` at the uncleared row.** -/
theorem sqArbFrame_sigma_bit_row {g : (DSq 1 : Type)} (hg : nuSel 1 0 0 1 g = 1) :
    selPar ((sqRelWord fun i =>
        rowFourHom (sqArbFrame 1 (nuSel 1 0 0 1) 0 (sigArbDress 1 g) i)).j)
      = selPar (rowFourHom g).a := by
  rw [rowFourHom_sqArbFrame g]
  exact rowFourWit_bit (rowFourHom_b_eq_zero hg)

/-- ⭐⭐ **THE HEADLINE: the class-four sigma forcing on `sqArbFrame` at the UNCLEARED row
`nuSel 1 0 0 1`.**  Every `ν'`-trivial sigma dressing of the arbitrary-dressing frame whose
image is killed by any achievable five-slot class-four refinement has an even
`chi_a`-character.  Nothing is carried beyond the dressing's own legality: the `b`-column
hypothesis is discharged by `rowFourHom_b`, and the handle hypotheses of
`GradedFourHom.sqArbFrame_sigma_forced` are **gone**, because the frame's displaced `V`-slot is
matched by the marking rather than assumed away.

This is what `GradedFourHom`'s honest-cost passage priced: not transport, a new ten-row solve at
the displaced binder point. -/
theorem sqArbFrame_sigma_forced_row {g : (DSq 1 : Type)} (hg : nuSel 1 0 0 1 g = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₀ : selLamThree 0 1 0 0 1 0 0 1 P Q R z₀)
    (l₃ : selLamThree 0 1 0 0 1 0 0 1 P Q R z₃)
    (l₄ : selLamThree 0 1 0 0 1 0 0 1 P Q R z₄)
    (hkill : sqRelWord (sigLift 0
      (fun i => rowFourHom (sqArbFrame 1 (nuSel 1 0 0 1) 0 (sigArbDress 1 g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (rowFourHom g).a = 0 := by
  rw [rowFourHom_sqArbFrame g] at hkill
  exact rowFourWit_sigma_forced (rowFourHom_b_eq_zero hg) hz₀ hw₁ hw₂ hz₃ hz₄ l₀ l₃ l₄ hkill

/-- ⭐⭐ **The headline at the `γ₂` level**: the same forcing with the achievability lattice
replaced by the commutator subgroup of the image itself. -/
theorem sqArbFrame_sigma_forced_row_gaTwo {g : (DSq 1 : Type)} (hg : nuSel 1 0 0 1 g = 1)
    {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {c : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₃ : z₃ ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowFourMark c))))
    (l₄ : z₄ ∈ rowGaTwoOf (Subgroup.closure (Set.range (rowFourMark c))))
    (hkill : sqRelWord (sigLift 0
      (fun i => rowFourHom (sqArbFrame 1 (nuSel 1 0 0 1) 0 (sigArbDress 1 g) i))
      z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (rowFourHom g).a = 0 := by
  rw [rowFourHom_sqArbFrame g] at hkill
  exact rowFourWit_sigma_forced_gaTwo (rowFourHom_b_eq_zero hg) hz₀ hw₁ hw₂ hz₃ hz₄ l₃ l₄ hkill

/-- ⭐⭐ **The escape separates the sigma dressings on `sqArbFrame` at the uncleared row**, with
the legality of both dressings exhibited: same hom, same frame, same uncleared row, both
dressings `λ`-trivial and `ν'`-trivial slotwise; the squared cleared-`v` dressing has even
class-four residue and the cleared-`v` dressing odd. -/
theorem rowFour_escape_separates :
    ((∀ i, nuLam 1 (sigArbDress 1
        (sqEichV 1 (nuSel 1 0 0 1) 0 * sqEichV 1 (nuSel 1 0 0 1) 0) i) = 1) ∧
      ∀ i, nuSel 1 0 0 1 (sigArbDress 1
        (sqEichV 1 (nuSel 1 0 0 1) 0 * sqEichV 1 (nuSel 1 0 0 1) 0) i) = 1) ∧
    ((∀ i, nuLam 1 (sigArbDress 1 (sqEichV 1 (nuSel 1 0 0 1) 0) i) = 1) ∧
      ∀ i, nuSel 1 0 0 1 (sigArbDress 1 (sqEichV 1 (nuSel 1 0 0 1) 0) i) = 1) ∧
    sqRelWord (fun i => rowFourHom (sqArbFrame 1 (nuSel 1 0 0 1) 0
      (sigArbDress 1 (sqEichV 1 (nuSel 1 0 0 1) 0 * sqEichV 1 (nuSel 1 0 0 1) 0)) i))
      = liftC 2 ∧
    sqRelWord (fun i => rowFourHom (sqArbFrame 1 (nuSel 1 0 0 1) 0
      (sigArbDress 1 (sqEichV 1 (nuSel 1 0 0 1) 0)) i)) = liftC 1 :=
  ⟨⟨nuLam_sigArbDress_rowVsq, nu_sigArbDress_rowVsq⟩,
    ⟨nuLam_sigArbDress_rowV, nu_sigArbDress_rowV⟩,
    sqRelWord_rowFrame_sigVsq, sqRelWord_rowFrame_sigV⟩

/-- ⭐ **Every class-`≤ 3` verdict on the frame is the same for all three dressings**: both
`U₄`-quotients of the frame's relator image are trivial in each case, so the separation is
purely class-four at the uncleared row as well. -/
theorem rowFrame_class_three_blind :
    (SqU5.toU4L (sqRelWord fun i => rowFourHom (sqArbFrame 1 (nuSel 1 0 0 1) 0
        (sigArbDress 1 1) i)) = 1 ∧
      SqU5.toU4R (sqRelWord fun i => rowFourHom (sqArbFrame 1 (nuSel 1 0 0 1) 0
        (sigArbDress 1 1) i)) = 1) ∧
    (SqU5.toU4L (sqRelWord fun i => rowFourHom (sqArbFrame 1 (nuSel 1 0 0 1) 0
        (sigArbDress 1 (sqEichV 1 (nuSel 1 0 0 1) 0
          * sqEichV 1 (nuSel 1 0 0 1) 0)) i)) = 1 ∧
      SqU5.toU4R (sqRelWord fun i => rowFourHom (sqArbFrame 1 (nuSel 1 0 0 1) 0
        (sigArbDress 1 (sqEichV 1 (nuSel 1 0 0 1) 0
          * sqEichV 1 (nuSel 1 0 0 1) 0)) i)) = 1) ∧
    (SqU5.toU4L (sqRelWord fun i => rowFourHom (sqArbFrame 1 (nuSel 1 0 0 1) 0
        (sigArbDress 1 (sqEichV 1 (nuSel 1 0 0 1) 0)) i)) = 1 ∧
      SqU5.toU4R (sqRelWord fun i => rowFourHom (sqArbFrame 1 (nuSel 1 0 0 1) 0
        (sigArbDress 1 (sqEichV 1 (nuSel 1 0 0 1) 0)) i)) = 1) := by
  rw [sqRelWord_rowFrame_sigTriv, sqRelWord_rowFrame_sigVsq, sqRelWord_rowFrame_sigV]
  refine ⟨⟨map_one _, map_one _⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

end Forcing

/-! ## 8 Axiom pins

Committed prints for every public declaration of this file. -/

section AxiomPins

#print axioms rowTuple
#print axioms rowTuple_zero
#print axioms rowTuple_one
#print axioms rowTuple_two
#print axioms rowTuple_handleU
#print axioms rowTuple_handleV
#print axioms sqRelWord_rowTuple
#print axioms sqRelWord_e_displace
#print axioms rowFour_chiA_handleU_forced
#print axioms rowPivotVal
#print axioms rowFourV
#print axioms rowFourU
#print axioms rowFourVGen
#print axioms rowFourVGen_eq
#print axioms rowFourV_eq
#print axioms rowFourMark
#print axioms rowFourWit
#print axioms rowFourMark_zero
#print axioms rowFourMark_one
#print axioms rowFourMark_two
#print axioms rowFourMark_handleU
#print axioms rowFourMark_handleV
#print axioms rowFourWit_zero
#print axioms rowFourWit_one
#print axioms rowFourWit_two
#print axioms rowFourWit_handleU
#print axioms rowFourWit_handleV
#print axioms rowFourWit_eq_dress
#print axioms sqRelWord_rowFourMark
#print axioms sqRelWord_rowFourWit_triv
#print axioms rowFourU_chiA
#print axioms rowFourV_chiA
#print axioms rowFourV_sq
#print axioms sqRelWord_rowFourWit_Vsq
#print axioms sqRelWord_rowFourWit_V
#print axioms sqRelWord_rowFourWit_U
#print axioms sqRelWord_rowFourWit_Vsq_complete
#print axioms rowFourWit_class_three_blind
#print axioms rowFourHom
#print axioms rowFourHom_gen
#print axioms rowFourHom_sigma
#print axioms rowFourHom_x0
#print axioms rowFourHom_x1
#print axioms rowFourHom_handleU
#print axioms rowFourHom_handleV
#print axioms rowFourHom_sqPivot
#print axioms nuSelRow_handleU
#print axioms nuSelRow_handleV
#print axioms rowFourHom_sqEichU
#print axioms rowFourHom_sqEichV
#print axioms rowFourHom_b
#print axioms rowFourHom_b_eq_zero
#print axioms rowFourHom_sqArbFrame
#print axioms rowFourWit_bit
#print axioms rowFourWit_lamThree_even
#print axioms rowFourWit_commP_zero_two
#print axioms rowFourWit_commP_two_handleU
#print axioms rowFourWit_commP_two_handleV
#print axioms rowFourWit_lamThreePlus_even
#print axioms rowFrameSub
#print axioms mem_rowFrameSub
#print axioms rowGaTwoSub
#print axioms mem_rowGaTwoSub
#print axioms commP_mem_rowGaTwoSub
#print axioms rowGaTwoOf
#print axioms rowFourMark_le_rowFrameSub
#print axioms rowFour_commutator_le
#print axioms rowFour_gaTwo_even
#print axioms rowFourHom_mem_closure
#print axioms rowFourWit_increment_even
#print axioms rowFourWit_increment_even_gaTwo
#print axioms rowFourWit_sigma_forced
#print axioms rowFourWit_sigma_forced_gaTwo
#print axioms nuLam_rowEichV
#print axioms nu_rowEichV
#print axioms nuLam_rowEichV_sq
#print axioms nu_rowEichV_sq
#print axioms rowFour_forcing_nonvacuous
#print axioms nuLam_sigArbDress_rowV
#print axioms nu_sigArbDress_rowV
#print axioms nuLam_sigArbDress_rowVsq
#print axioms nu_sigArbDress_rowVsq
#print axioms sqRelWord_rowFrame_sigTriv
#print axioms sqRelWord_rowFrame_sigVsq
#print axioms sqRelWord_rowFrame_sigV
#print axioms sqRelWord_rowFrame_sigVsq_complete
#print axioms sqRelWord_rowFrame_sigV_ne_one
#print axioms sqRelWord_rowFrame_sigV_ne_one_gaTwo
#print axioms sqArbFrame_sigma_bit_row
#print axioms sqArbFrame_sigma_forced_row
#print axioms sqArbFrame_sigma_forced_row_gaTwo
#print axioms rowFour_escape_separates
#print axioms rowFrame_class_three_blind

end AxiomPins

end SqCore

end Dyadic

end GQ2

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedStageNecessity

/-!
# W62-SEPARATE: the PARITY LINE is strictly stronger than the STAGE-FOUR FORCING, and so is the
SHARP LINE

Wave 61 proved `stageForces_iff_stageCentral`: at a marking whose relator is a central
translation with an odd class-five residue, the stage-four forcing holds exactly when every
achievable dressing acting **centrally** moves the class-five row evenly.  It recorded the
strictness of the parity line `StageOrth` as a **measurement** - four of 1650 admissible
markings where the parity line fails and the forcing holds.  This file makes the strictness a
**theorem**, by a different and cheaper mechanism than the four; it does not prove the four, and
section 4 says precisely why they are out of reach.

## ⭐⭐⭐ Headline 1: THE SEPARATION IS A THEOREM

⭐⭐⭐ `stageForces_not_imp_stageOrth`, `sepMark_separates`: at the marking `sepMark`, at every
handle count and every handle, the stage-four forcing HOLDS and the parity line FAILS - an
achievable double commutator of the marking's own letters, `[[sigma, U], U] = <l=1, m=1>`, moves
the class-five row by `7`.  Together with wave 61's `stageForces_of_stageOrth` this is
`stageOrth_strictly_stronger`: the implication runs one way and does not come back.

## ⭐⭐⭐ Headline 2: THE MECHANISM IS THE CLASS-THREE ROW, WHICH IS INVISIBLE MOD 2

The shift's three class-three rows are `-4 (z 1).x + 2 (z 2).x` (`gaThreeShift_j/k/l`): the
Frobenius weights on the exponent slots and **nothing else**.  Wave 61 read that as a reason to
ignore them - "the class-three rows carry the Frobenius weights `(-4, 2)` and are even for free,
so they never enter" - and mod `2` that is right, the rows vanish identically and no covector
sees them.  Over `ZMod 8` even is not nothing:

* ⭐⭐⭐ `stageForces_of_odd_relJ`: at **any** marking whose relator has an ODD class-three row
  `j`, the forcing holds, because no `gamma_3`-dressing at all - achievable or not - can move an
  even amount onto an odd one.  The relator of `sepMark` is `<j=7, o=7>`: `gamma_3`-SHAPED, so
  it lies in the very filtration layer the dressings move it in and no shape mismatch protects
  it, and with an ODD class-five residue, so the forcing's conclusion is FALSE there and
  `StageForces` says exactly that no achievable stage-four dressing kills.
* ⭐⭐ `stageCentral_x1_j_even` (and `_k_`, `_l_`): the same weights, read the other way.  A
  shift that is a central translation forces the `x1`-slot's own class-three coordinates EVEN,
  at every marking and with no achievability at all, because `2 b = 4 a` in `ZMod 8` forces `b`
  even.  Mod `2` that equation is vacuous.

⚠ **Scope, against wave 61's "at stage four the forcing is never free".**  That reading is about
the ADMISSIBLE family - relator a central translation - and inside it the class-three row of the
relator is `0` and this obstruction is silent, so nothing here contradicts it.  What the
obstruction shows is that the family is where the difficulty lives: one row outside it and the
forcing is free.

## ⭐⭐⭐ Headline 3: THE SHARP LINE IS NOT NECESSARY EITHER, so wave 61's hypothesis is
load-bearing

⭐⭐⭐ `stageForces_not_imp_stageCentral`.  The same dressing acts **centrally** (its shift is
`liftO 7`), so `StageCentral` fails at `sepMark` while the forcing holds.  Wave 61's
`stageCentral_of_stageForces` therefore cannot drop its hypothesis that the relator is a central
translation with an odd residue: `sepMark`'s relator is central in every row **but its
class-three one**, and that single row is enough to break the converse.  This is where the
hypothesis bears.

## ⭐⭐ Headline 4: the parity line needs only TWO columns, not three

⭐⭐⭐ `stageOrth_of_ae`: at any marking whose slots have an even `(1,2)`-column and an even
`(5,6)`-column, the parity line holds.  Wave 61's `stageOrth_of_outer` asks for a third column,
the outer class-two `i`; it is **not needed**.  The `i`-channel of the class-five covector is
paired against the dressing's `j`, and ⭐⭐ `forceLcs_two_le_sepEvenJ` - the mirror of wave 61's
`forceLcs_two_le_fiveEvenL` under `a <-> e, b <-> d, f <-> i, j <-> l, m <-> n`, which the tree
did not own - delivers an even `j` from the `(1,2)`-column already assumed.

⚠ **This is what makes section 2 rare, and it explains wave 61's `MODLOW` count of 0.**  A
marking at which the parity line fails must have an ODD `(1,2)`- or `(5,6)`-column somewhere;
`sepMark` has `sepS.a = sepV.a = 1`.  And the mod-`2` span candidate `MODLOW` forces those two
columns even at every letter (measured: the class-five covector reads the dressing's `(m, n)`
against `L.e` and `L.a`, which the two class-four covectors do not read at all), so by
`stageOrth_of_ae` **`MODLOW` implies the parity line** and could never have separated anything.
Wave 61 found it at 0 of 1650 markings; this is the reason.

## PROVED versus MEASURED

**PROVED**: the evenness of the shift's three class-three rows over any commutative ring; the
class-three obstruction and the `ZMod 8` reading of centrality; the separating marking end to
end at every handle count and every handle - its relator, the achievability of its dressing, the
dressing's shift, the failure of both lines and the forcing; the two strictness statements; the
mirror chain and the two-column parity line, and that it covers wave 61's own mixed point.

**MEASURED** (`scripts/w62_separate/results/`, `verify_sep.txt` has **20** named checks and **0**
failures, taken on wave 59's honest `6 x 6` matrices through wave 61's `sharp4lib`): every claim
about `sepMark` independently of the Lean file, including the exact kill search (no achievable
stage-four dressing kills), the parity line failing, and the sharp line failing.

⚠ **NOT proved, and honestly not provable at reasonable cost: wave 61's FOUR gap markings.**
They were re-derived from the recorded letters and survive inspection completely
(`inspect_four.txt`): all four are admissible, at all four the exact kill search finds no kill,
the parity line fails and the sharp line holds, exactly as wave 61 reported.  What the
re-derivation adds is a diagnosis of the cost.

* `diagnose.txt`: at each of the four, the implication "central shift => even class-five row"
  fails for the FULL `gamma_3`-tuple lattice, so achievability is genuinely consumed; and of the
  63 conditions "coordinate `c` of every dressing is even", the minimal ones that repair it are
  `m, n` (the first pair of markings) and `j, l, m, n` (the second), **neither of which holds on
  the achievable lattice**.  No per-coordinate congruence can do it.
* `mod2_probe.txt`: nor can any mod-`2` linear condition.  The achievable lattice's mod-`2`
  image repairs nothing at any of the four; adding the mod-`4` structure repairs the first pair
  and still fails on the second, which needs the lattice mod `8` - that is, the exact subgroup.
* `feasible3.txt`: the chains a Lean file can run are letter-column conditions, and their
  measured reach is `a => j`, `b => j, k`, `c => j, k, l`, `d => k, l`, `e => l`, with
  `f, g, h, i` giving nothing.  Two of those are proved: `e => l` is wave 61's
  `forceLcs_two_le_fiveEvenL`, `a => j` is section 4's `forceLcs_two_le_sepEvenJ`.  A search over
  the column conditions and the covector identities they allow finds **no** condition at which
  the parity line can fail with the forcing provable from it.  The four are hard for a reason,
  and the reason is that their forcing reads the achievable lattice mod `4` or finer.

## Contents

* **1** ⭐⭐⭐ the class-three obstruction; **2** ⭐⭐⭐ the separating marking;
* **3** ⭐⭐⭐ the two strictness statements; **4** ⭐⭐ the sharpened parity line;
* **5** axiom pins.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`; every `decide` is on `ZMod 8`, `ZMod 2` or tuples
over them.  All **49** committed prints are std-3 (`propext`, `Classical.choice`, `Quot.sound`)
or a subset: `27` std-3, `22` `propext` + `Quot.sound`.
-/

open scoped commutatorElement

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The class-three obstruction -/

section ClassThree

variable {R : Type} [CommRing R] {h : ℕ}

/-- ⭐ **The stage-four shift's first class-three row is EVEN**, at every marking, for every
dressing, over every ring: it is the Frobenius weights `(-4, 2)` on the exponent slots and
nothing else (`gaThreeShift_j`).  Wave 61 read this as "even for free, so the class-three rows
never enter"; over `ZMod 8` even is not free, and section 2 is what it buys. -/
theorem gaThreeShift_j_even (m z : Fin (sqRank h) → SqU6 R) :
    (2 : R) ∣ (gaThreeShift h m z).j :=
  ⟨-2 * (z 1).j + (z 2).j, by rw [gaThreeShift_j]; ring⟩

/-- …and so is the second. -/
theorem gaThreeShift_k_even (m z : Fin (sqRank h) → SqU6 R) :
    (2 : R) ∣ (gaThreeShift h m z).k :=
  ⟨-2 * (z 1).k + (z 2).k, by rw [gaThreeShift_k]; ring⟩

/-- …and the third. -/
theorem gaThreeShift_l_even (m z : Fin (sqRank h) → SqU6 R) :
    (2 : R) ∣ (gaThreeShift h m z).l :=
  ⟨-2 * (z 1).l + (z 2).l, by rw [gaThreeShift_l]; ring⟩

end ClassThree

section Obstruction

variable {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R}

/-- The class-three row of a relator moved by a `gamma_3`-dressing: the shift's own row, added.
Both cross terms of `SqU6.mul_j` meet a coordinate the shift does not have. -/
theorem gaThreeDress_relJ {z : Fin (sqRank h) → SqU6 gr3R} (hz : ∀ i, (z i).IsGaThree) :
    (sqRelWord (conFiveDress m z)).j = (sqRelWord m).j + (gaThreeShift h m z).j := by
  rw [sqRelWord_gaThreeDress hz, SqU6.mul_j,
    (gaThreeShift_isGaThree (m := m) (z := z)).2.2.2.2.2.2.1,
    (gaThreeShift_isGaThree (m := m) (z := z)).2.2.1]
  ring

/-- ⭐⭐⭐ **THE CLASS-THREE OBSTRUCTION.**  At **any** marking whose relator has an ODD
class-three row, the stage-four forcing holds - and holds for a reason the class-five pairing
cannot see.  No achievable dressing kills, because no `gamma_3`-dressing at all can: the shift's
class-three row is `-4 (z 1).j + 2 (z 2).j`, hence even, so it can never cancel an odd one.

⚠ This is arithmetic over `ZMod 8`, not a covector condition: mod `2` the shift's class-three
row is identically `0` and says nothing. -/
theorem stageForces_of_odd_relJ (hj : ¬ (2 : gr3R) ∣ (sqRelWord m).j) : StageForces m := by
  intro z hz hkill
  refine absurd ?_ hj
  have hga : ∀ i, (z i).IsGaThree := fun i => isGaThree_of_mem_forceLcs (hz i)
  have h0 : (sqRelWord m).j + (gaThreeShift h m z).j = 0 := by
    rw [← gaThreeDress_relJ hga, hkill, SqU6.one_j]
  obtain ⟨t, ht⟩ := gaThreeShift_j_even m z
  exact ⟨-t, by linear_combination h0 - ht⟩

/-- ⭐⭐ **The `ZMod 8` sharpening of centrality.**  A stage-four shift that is a central
translation forces the `x1`-slot's own class-three coordinates EVEN, at every marking and with
no achievability: `-4 (z 1).j + 2 (z 2).j = 0` in `ZMod 8` gives `(z 2).j` even, because `2` is
not a zero divisor modulo `4`.  Mod `2` the same equation is vacuous. -/
theorem stageCentral_x1_j_even {z : Fin (sqRank h) → SqU6 gr3R} {w : gr3R}
    (hcen : gaThreeShift h m z = SqU6.liftO w) : (2 : gr3R) ∣ (z 2).j := by
  have h0 : -4 * (z 1).j + 2 * (z 2).j = 0 := by
    rw [← gaThreeShift_j, hcen]
    rfl
  exact (by decide : ∀ a b : gr3R, -4 * a + 2 * b = 0 → ∃ t : gr3R, b = 2 * t) _ _ h0

theorem stageCentral_x1_k_even {z : Fin (sqRank h) → SqU6 gr3R} {w : gr3R}
    (hcen : gaThreeShift h m z = SqU6.liftO w) : (2 : gr3R) ∣ (z 2).k := by
  have h0 : -4 * (z 1).k + 2 * (z 2).k = 0 := by
    rw [← gaThreeShift_k, hcen]
    rfl
  exact (by decide : ∀ a b : gr3R, -4 * a + 2 * b = 0 → ∃ t : gr3R, b = 2 * t) _ _ h0

theorem stageCentral_x1_l_even {z : Fin (sqRank h) → SqU6 gr3R} {w : gr3R}
    (hcen : gaThreeShift h m z = SqU6.liftO w) : (2 : gr3R) ∣ (z 2).l := by
  have h0 : -4 * (z 1).l + 2 * (z 2).l = 0 := by
    rw [← gaThreeShift_l, hcen]
    rfl
  exact (by decide : ∀ a b : gr3R, -4 * a + 2 * b = 0 → ∃ t : gr3R, b = 2 * t) _ _ h0

end Obstruction

/-! ## 2 The separating marking -/

section SepPoint

variable {h : ℕ} {j : Fin h}

/-- The sigma slot of the separating marking: `<a=1, c=1, h=1>`. -/
def sepS : SqU6 gr3R := ⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩

/-- Its `x0`-slot: `<a=1>`. -/
def sepX : SqU6 gr3R := ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Its `x1`-slot: `<a=2>`, the layered solve of the class-one and class-two rows. -/
def sepY : SqU6 gr3R := ⟨2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Its handle-`U` letter: `<d=1, e=1, g=1, m=1, n=1>`. -/
def sepU : SqU6 gr3R := ⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0⟩

/-- Its handle-`V` letter: `<a=1, i=1, k=1, n=1>`. -/
def sepV : SqU6 gr3R := ⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩

variable (h j) in
/-- **The separating marking**, at every handle count and every handle. -/
def sepMark : Fin (sqRank h) → SqU6 gr3R := fiveTuple gr3R h j sepS sepX sepY sepU sepV

/-- ⭐⭐ **The relator is `<j=7, o=7>`**: `gamma_3`-SHAPED, so it lies in the very filtration
layer a stage-four dressing moves it in and no shape mismatch protects it; with an ODD
class-three row, which is what protects it; and with an ODD class-five residue, so the forcing's
conclusion is FALSE here and `StageForces` says exactly that no achievable stage-four dressing
kills. -/
theorem sqRelWord_sepMark :
    sqRelWord (sepMark h j) = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 7⟩ := by
  rw [sepMark, sqRelWord_fiveTuple]
  decide

/-- The handle block is live. -/
theorem commP_sepUV_live : commP sepU sepV ≠ 1 := by decide

/-- Every slot of a one-handle-live tuple is one of its five letters or trivial.
(`GradedFiveStageFour`'s and `GradedStageNecessity`'s copies are both `private`.) -/
private theorem sepTuple_cases {R : Type} [CommRing R] {hh : ℕ} {jj : Fin hh}
    (S X Y U V : SqU6 R) (i : Fin (sqRank hh)) :
    fiveTuple R hh jj S X Y U V i = S ∨ fiveTuple R hh jj S X Y U V i = X
      ∨ fiveTuple R hh jj S X Y U V i = Y ∨ fiveTuple R hh jj S X Y U V i = U
      ∨ fiveTuple R hh jj S X Y U V i = V ∨ fiveTuple R hh jj S X Y U V i = 1 := by
  simp only [fiveTuple]
  split_ifs <;> tauto

/-- Dressing a one-handle-live tuple slotwise by another is again one, letter by letter. -/
private theorem conFiveDress_fiveTuple {R : Type} [CommRing R] {hh : ℕ} {jj : Fin hh}
    (S X Y U V S' X' Y' U' V' : SqU6 R) :
    conFiveDress (fiveTuple R hh jj S X Y U V) (fiveTuple R hh jj S' X' Y' U' V')
      = fiveTuple R hh jj (S * S') (X * X') (Y * Y') (U * U') (V * V') := by
  funext i
  simp only [conFiveDress_apply, fiveTuple]
  split_ifs <;> simp

/-- ⭐ **THE ACHIEVABLE DRESSING** `[[sigma, U], U] = <l=1, m=1>`: a double commutator of the
marking's own letters, so it lies in `gamma_3` of the image with nothing assumed. -/
def sepZ : SqU6 gr3R := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩

theorem sepZ_generator : commP (commP sepS sepU) sepU = sepZ := by decide

theorem sepZ_isGaThree : sepZ.IsGaThree := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

variable (h j) in
/-- …placed on the handle-`V` slot, every other slot undressed. -/
def sepDress : Fin (sqRank h) → SqU6 gr3R := fiveTuple gr3R h j 1 1 1 1 sepZ

theorem sepDress_isGaThree (i : Fin (sqRank h)) : (sepDress h j i).IsGaThree := by
  rcases sepTuple_cases (R := gr3R) (jj := j) 1 1 1 1 sepZ i with
    h1 | h1 | h1 | h1 | h1 | h1 <;> rw [sepDress, h1]
  exacts [SqU6.isGaThree_one, SqU6.isGaThree_one, SqU6.isGaThree_one, SqU6.isGaThree_one,
    sepZ_isGaThree, SqU6.isGaThree_one]

/-- **The dressing is achievable**: every slot value is either trivial or the double commutator
`[[sigma, U], U]` of two of the marking's own letters. -/
theorem sepDress_mem (i : Fin (sqRank h)) :
    sepDress h j i ∈ forceLcs (Subgroup.closure (Set.range (sepMark h j))) 2 := by
  have hS : sepS ∈ Subgroup.closure (Set.range (sepMark h j)) :=
    Subgroup.subset_closure ⟨0, by rw [sepMark, fiveTuple_zero]⟩
  have hU : sepU ∈ Subgroup.closure (Set.range (sepMark h j)) :=
    Subgroup.subset_closure ⟨sqHandleIdxU j, by rw [sepMark, fiveTuple_handleU]⟩
  have hZ : sepZ ∈ forceLcs (Subgroup.closure (Set.range (sepMark h j))) 2 := by
    rw [← sepZ_generator]
    exact commP_mem_commSub (commP_mem_commSub hS hU) hU
  rcases sepTuple_cases (R := gr3R) (jj := j) 1 1 1 1 sepZ i with
    h1 | h1 | h1 | h1 | h1 | h1 <;> rw [sepDress, h1]
  exacts [one_mem _, one_mem _, one_mem _, one_mem _, hZ, one_mem _]

/-- ⭐⭐ **The dressing's shift is the CENTRAL translation `liftO 7`**, at every handle count and
every handle: it moves the class-five row by an ODD amount and moves nothing else.  Read off the
translation identity, not from any transcribed covector. -/
theorem sepMark_shift : gaThreeShift h (sepMark h j) (sepDress h j) = SqU6.liftO 7 := by
  have key := sqRelWord_gaThreeDress (m := sepMark h j) (z := sepDress h j)
    (fun i => sepDress_isGaThree i)
  rw [sepMark, sepDress, conFiveDress_fiveTuple, sqRelWord_fiveTuple, sqRelWord_fiveTuple] at key
  rw [sepMark, sepDress]
  refine mul_left_cancel (a := sqWord sepS sepX sepY * commP sepU sepV) ?_
  rw [← key]
  decide

/-- …so the class-five row moves by `7`. -/
theorem sepMark_shiftO : gaThreeShiftO h (sepMark h j) (sepDress h j) = 7 := by
  rw [← gaThreeShift_o, sepMark_shift, SqU6.liftO_o]

/-- ⭐⭐⭐ **THE PARITY LINE FAILS AT THE SEPARATING MARKING**, at every handle count and every
handle: an achievable stage-four dressing moves the class-five row by `7`. -/
theorem sepMark_not_stageOrth : ¬ StageOrth (sepMark h j) := by
  intro hO
  obtain ⟨t, ht⟩ := hO (sepDress h j) sepDress_mem
  rw [sepMark_shiftO] at ht
  exact absurd ht (by revert t; decide)

/-- ⭐⭐ …and so does the SHARP line, because that same dressing acts **centrally**. -/
theorem sepMark_not_stageCentral : ¬ StageCentral (sepMark h j) := by
  intro hC
  obtain ⟨t, ht⟩ := hC (sepDress h j) 7 sepDress_mem sepMark_shift
  exact absurd ht (by revert t; decide)

/-- ⭐⭐⭐ **THE FORCING HOLDS ANYWAY.**  The relator's class-three row is `7`, and every
stage-four shift's class-three row is `-4 (z 1).j + 2 (z 2).j`, hence even.  So no
`gamma_3`-dressing whatsoever kills the relator, achievable or not, and the exclusion is
unconditional. -/
theorem sepMark_stageForces : StageForces (sepMark h j) := by
  refine stageForces_of_odd_relJ ?_
  rw [sqRelWord_sepMark]
  rintro ⟨t, ht⟩
  exact absurd ht (by revert t; decide)

/-- …in the shape wave 60 and wave 61 state it. -/
theorem sepMark_diag_ne_one {z : Fin (sqRank h) → SqU6 gr3R}
    (hz : ∀ i, z i ∈ forceLcs (Subgroup.closure (Set.range (sepMark h j))) 2) :
    sqRelWord (conFiveDress (sepMark h j) z) ≠ 1 := by
  intro hc
  have hp := sepMark_stageForces z hz hc
  rw [sqRelWord_sepMark] at hp
  exact absurd hp (by decide)

/-- ⭐⭐⭐ **THE SEPARATION, AT ONE MARKING.**  The stage-four forcing holds, the parity line
fails, and the sharp line fails: at every handle count and every handle. -/
theorem sepMark_separates :
    StageForces (sepMark h j) ∧ ¬ StageOrth (sepMark h j) ∧ ¬ StageCentral (sepMark h j) :=
  ⟨sepMark_stageForces, sepMark_not_stageOrth, sepMark_not_stageCentral⟩

/-- **Independent check of the point**, at one handle, straight from `sqRelWord` by kernel
computation, without `sqRelWord_fiveTuple`. -/
theorem sepMark_decide_crosscheck :
    sqRelWord (sepMark 1 0) = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 7⟩ := by decide

end SepPoint

/-! ## 3 The two strictness statements -/

section Strict

/-- ⭐⭐⭐ **THE PARITY LINE IS STRICTLY STRONGER THAN THE FORCING.**  Wave 61's
`stageForces_of_stageOrth` sends it one way at any central relator; it does not come back.
Wave 61 recorded the failure of the converse as a **measurement** at four of 1650 admissible
markings; this is the statement as a theorem. -/
theorem stageForces_not_imp_stageOrth :
    ¬ ∀ (h : ℕ) (m : Fin (sqRank h) → SqU6 gr3R), StageForces m → StageOrth m := by
  intro hc
  exact sepMark_not_stageOrth (h := 1) (j := 0)
    (hc 1 (sepMark 1 0) (sepMark_stageForces (h := 1) (j := 0)))

/-- ⭐⭐⭐ **THE SHARP LINE IS STRICTLY STRONGER TOO**, so wave 61's
`stageCentral_of_stageForces` cannot drop its hypothesis that the relator is a central
translation with an odd residue: that hypothesis is **load-bearing**, and this is where it
bears.  At the separating marking the relator is `gamma_3`-shaped and central in every row but
its class-three one, and the sharp line fails while the forcing holds. -/
theorem stageForces_not_imp_stageCentral :
    ¬ ∀ (h : ℕ) (m : Fin (sqRank h) → SqU6 gr3R), StageForces m → StageCentral m := by
  intro hc
  exact sepMark_not_stageCentral (h := 1) (j := 0)
    (hc 1 (sepMark 1 0) (sepMark_stageForces (h := 1) (j := 0)))

/-- ⭐⭐⭐ **BOTH DIRECTIONS, IN ONE STATEMENT.**  The parity line implies the forcing at any
central relator, and the forcing does not imply the parity line anywhere. -/
theorem stageOrth_strictly_stronger :
    (∀ {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R} {c : gr3R}, sqRelWord m = SqU6.liftO c →
        StageOrth m → StageForces m)
      ∧ ¬ ∀ (h : ℕ) (m : Fin (sqRank h) → SqU6 gr3R), StageForces m → StageOrth m :=
  ⟨fun hres hO => stageForces_of_stageOrth hres hO, stageForces_not_imp_stageOrth⟩

end Strict

/-! ## 4 The sharpened parity line: the `(1,2)`- and `(5,6)`-columns suffice -/

section EvenA

/-- **`A_1`**: an even `(1,2)`-column.  `stageN1` without its `(3,4)`-condition. -/
def sepEvenA : Subgroup (SqU6 gr3R) where
  carrier := {z | (2 : gr3R) ∣ z.a}
  mul_mem' := by
    rintro p q ha ha'
    rw [Set.mem_setOf_eq, SqU6.mul_a]
    exact dvd_add ha ha'
  one_mem' := by rw [Set.mem_setOf_eq, SqU6.one_a]; exact dvd_zero _
  inv_mem' := by
    rintro p ha
    rw [Set.mem_setOf_eq, SqU6.inv_a]
    exact ha.neg_right

/-- **`A_2`**: a `gamma_2`-element with an even first class-two column. -/
def sepEvenF : Subgroup (SqU6 gr3R) where
  carrier := {z | z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0 ∧ (2 : gr3R) ∣ z.f}
  mul_mem' := by
    rintro p q ⟨pa, pb, pc, pd, pe, pf⟩ ⟨qa, qb, qc, qd, qe, qf⟩
    refine ⟨by rw [SqU6.mul_a, pa, qa]; ring, by rw [SqU6.mul_b, pb, qb]; ring,
      by rw [SqU6.mul_c, pc, qc]; ring, by rw [SqU6.mul_d, pd, qd]; ring,
      by rw [SqU6.mul_e, pe, qe]; ring, ?_⟩
    rw [SqU6.mul_f, pa, zero_mul, add_zero]
    exact dvd_add pf qf
  one_mem' := ⟨rfl, rfl, rfl, rfl, rfl, by rw [SqU6.one_f]; exact dvd_zero _⟩
  inv_mem' := by
    rintro p ⟨pa, pb, pc, pd, pe, pf⟩
    refine ⟨by rw [SqU6.inv_a, pa]; ring, by rw [SqU6.inv_b, pb]; ring,
      by rw [SqU6.inv_c, pc]; ring, by rw [SqU6.inv_d, pd]; ring,
      by rw [SqU6.inv_e, pe]; ring, ?_⟩
    rw [SqU6.inv_f, pa, zero_mul, zero_sub]
    exact pf.neg_right

/-- **`A_3`**: a `gamma_3`-element with an even class-three row `j`.  ⭐ This is the mirror of
`GradedFiveNecessity`'s `fiveEvenL` chain under the transpose-anti-automorphism
`a <-> e, b <-> d, f <-> i, j <-> l, m <-> n`, and the tree did not own it. -/
def sepEvenJ : Subgroup (SqU6 gr3R) where
  carrier := {z | z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0 ∧ z.f = 0 ∧ z.g = 0
    ∧ z.h = 0 ∧ z.i = 0 ∧ (2 : gr3R) ∣ z.j}
  mul_mem' := by
    rintro p q ⟨pa, pb, pc, pd, pe, pf, pg, ph, pi, pj⟩ ⟨qa, qb, qc, qd, qe, qf, qg, qh, qi, qj⟩
    refine ⟨by rw [SqU6.mul_a, pa, qa]; ring, by rw [SqU6.mul_b, pb, qb]; ring,
      by rw [SqU6.mul_c, pc, qc]; ring, by rw [SqU6.mul_d, pd, qd]; ring,
      by rw [SqU6.mul_e, pe, qe]; ring, by rw [SqU6.mul_f, pf, qf, pa]; ring,
      by rw [SqU6.mul_g, pg, qg, pb]; ring, by rw [SqU6.mul_h, ph, qh, pc]; ring,
      by rw [SqU6.mul_i, pi, qi, pd]; ring, ?_⟩
    rw [SqU6.mul_j, pa, zero_mul, add_zero, pf, zero_mul, add_zero]
    exact dvd_add pj qj
  one_mem' := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by rw [SqU6.one_j]; exact dvd_zero _⟩
  inv_mem' := by
    rintro p ⟨pa, pb, pc, pd, pe, pf, pg, ph, pi, pj⟩
    refine ⟨by rw [SqU6.inv_a, pa]; ring, by rw [SqU6.inv_b, pb]; ring,
      by rw [SqU6.inv_c, pc]; ring, by rw [SqU6.inv_d, pd]; ring,
      by rw [SqU6.inv_e, pe]; ring, by rw [SqU6.inv_f, pf, pa, pb]; ring,
      by rw [SqU6.inv_g, pg, pb, pc]; ring, by rw [SqU6.inv_h, ph, pc, pd]; ring,
      by rw [SqU6.inv_i, pi, pd, pe]; ring, ?_⟩
    rw [SqU6.inv_j, pa, pb, pc, pf, pg]
    simpa using pj.neg_right

theorem mem_sepEvenA {z : SqU6 gr3R} : z ∈ sepEvenA ↔ (2 : gr3R) ∣ z.a := Iff.rfl

theorem sepEvenJ_even {z : SqU6 gr3R} (hz : z ∈ sepEvenJ) : (2 : gr3R) ∣ z.j :=
  hz.2.2.2.2.2.2.2.2.2

/-- ⭐ **Step one**: a commutator of two even-`(1,2)`-column elements is a `gamma_2`-element
with an even first class-two column, that column being the `(a, b)`-pairing. -/
theorem sepEvenF_of_commutator {p q : SqU6 gr3R} (hp : p ∈ sepEvenA) (hq : q ∈ sepEvenA) :
    ⁅p, q⁆ ∈ sepEvenF := by
  obtain ⟨s₁, hs₁⟩ := mem_sepEvenA.mp hp
  obtain ⟨t₁, ht₁⟩ := mem_sepEvenA.mp hq
  rw [commutatorElement_eq_commP]
  refine ⟨SqU6.commP_a _ _, SqU6.commP_b _ _, SqU6.commP_c _ _, SqU6.commP_d _ _,
    SqU6.commP_e _ _, ⟨s₁ * q.b - p.b * t₁, ?_⟩⟩
  simp only [SqU6.commP_f, SqU6.inv_a, SqU6.inv_b, hs₁, ht₁]
  ring

/-- ⭐ **Step two**: pairing such an element against an even-`(1,2)`-column letter gives a
`gamma_3`-element with an even `j`.  `u6Comm3L` reduces on a `gamma_2`-element to
`p.f * q.c - p.g * q.a` plus terms carrying `p.a`, `p.b` or `p.c`, and both survivors meet an
even entry.  ⭐ Wave 60's `stageN3_of_commutator` gets the same `j` out of `stageN1`, which also
asks for an even `(3,4)`-column; the `(3,4)`-column is not needed for `j`. -/
theorem sepEvenJ_of_commutator {p q : SqU6 gr3R} (hp : p ∈ sepEvenF) (hq : q ∈ sepEvenA) :
    ⁅p, q⁆ ∈ sepEvenJ := by
  obtain ⟨pa, pb, pc, pd, pe, ⟨f', hf⟩⟩ := hp
  obtain ⟨t₁, ht₁⟩ := mem_sepEvenA.mp hq
  rw [commutatorElement_eq_commP]
  refine ⟨SqU6.commP_a _ _, SqU6.commP_b _ _, SqU6.commP_c _ _, SqU6.commP_d _ _,
    SqU6.commP_e _ _, ?_, ?_, ?_, ?_, ⟨f' * q.c - p.g * t₁, ?_⟩⟩
  · simp only [SqU6.commP_f, SqU6.inv_a, SqU6.inv_b, pa, pb]
    ring
  · simp only [SqU6.commP_g, SqU6.inv_b, SqU6.inv_c, pb, pc]
    ring
  · simp only [SqU6.commP_h, SqU6.inv_c, SqU6.inv_d, pc, pd]
    ring
  · simp only [SqU6.commP_i, SqU6.inv_d, SqU6.inv_e, pd, pe]
    ring
  · simp only [SqU6.commP_j, SqU6.u6Comm3L, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_f,
      SqU6.inv_g, pa, pb, pc, hf, ht₁]
    ring

/-- ⭐⭐ **THE MIRROR CHAIN**: at any marking all of whose slots have an even `(1,2)`-column,
every achievable stage-four dressing has an even class-three row `j`.  The mirror of wave 61's
`forceLcs_two_le_fiveEvenL`, which gets `l` from the even `(5,6)`-columns. -/
theorem forceLcs_two_le_sepEvenJ {H : Subgroup (SqU6 gr3R)} (hH : H ≤ sepEvenA) :
    forceLcs H 2 ≤ sepEvenJ := by
  have h1 : forceLcs H 1 ≤ sepEvenF :=
    Subgroup.commutator_le.mpr fun p hp q hq => sepEvenF_of_commutator (hH hp) (hH hq)
  exact Subgroup.commutator_le.mpr fun p hp q hq => sepEvenJ_of_commutator (h1 hp) (hH hq)

end EvenA

section PairAE

variable {R : Type} [CommRing R] {h : ℕ}

/-- ⭐ **The class-five pairing form is even** as soon as the letter's `(1,2)`- and
`(5,6)`-columns are even and the dressing's two class-three rows are.  Wave 60's
`gaThreePair_even` reads one letter column and three dressing coordinates, wave 61's
`gaThreePair_even_of_outer` three letter columns and one; this reads two and two, and the two
dressing coordinates are exactly the two the mirror pair of chains delivers. -/
theorem gaThreePair_even_of_ae {z L : SqU6 R} (ha : (2 : R) ∣ L.a) (he : (2 : R) ∣ L.e)
    (hj : (2 : R) ∣ z.j) (hl : (2 : R) ∣ z.l) : (2 : R) ∣ gaThreePair z L := by
  obtain ⟨a', ha⟩ := ha
  obtain ⟨e', he⟩ := he
  obtain ⟨j', hj⟩ := hj
  obtain ⟨l', hl⟩ := hl
  refine ⟨z.m * e' - z.n * a' + j' * L.i - l' * L.f + l' * (L.a * L.b) - z.k * (a' * L.e), ?_⟩
  rw [gaThreePair, ha, he, hj, hl]
  ring

/-- …and so is the correction block.  Six of its nine coefficient blocks meet an even dressing
row, the two `z0.k`- and `z1.k`-blocks have even coefficients outright, and the `z2.k`-block is
the `(1,2)`/`(5,6)` cross pairing of the sigma and `x1` letters. -/
theorem gaThreeCorr_even_of_ae {s x y z₀ z₁ z₂ : SqU6 R}
    (hsa : (2 : R) ∣ s.a) (hya : (2 : R) ∣ y.a) (hse : (2 : R) ∣ s.e) (hye : (2 : R) ∣ y.e)
    (h0j : (2 : R) ∣ z₀.j) (h1j : (2 : R) ∣ z₁.j) (h2j : (2 : R) ∣ z₂.j)
    (h0l : (2 : R) ∣ z₀.l) (h1l : (2 : R) ∣ z₁.l) (h2l : (2 : R) ∣ z₂.l) :
    (2 : R) ∣ gaThreeCorr s x y z₀ z₁ z₂ := by
  obtain ⟨sa, hsa⟩ := hsa
  obtain ⟨ya, hya⟩ := hya
  obtain ⟨se, hse⟩ := hse
  obtain ⟨ye, hye⟩ := hye
  rw [gaThreeCorr]
  refine dvd_add (dvd_add (dvd_add (dvd_add (dvd_add (dvd_add (dvd_add (dvd_add
    (Dvd.dvd.mul_right h0j _) ?_) (Dvd.dvd.mul_right h0l _)) (Dvd.dvd.mul_right h1j _)) ?_)
    (Dvd.dvd.mul_right h1l _)) (Dvd.dvd.mul_right h2j _)) ?_) (Dvd.dvd.mul_right h2l _)
  · exact Dvd.dvd.mul_left ⟨4 * (x.a * x.e) - x.a * y.e - x.e * y.a - y.a * y.e, by ring⟩ _
  · refine Dvd.dvd.mul_left ⟨s.a * s.e - 7 * (s.a * x.e) + 5 * (s.a * y.e) - 7 * (s.e * x.a)
      + 5 * (s.e * y.a) + 65 * (x.a * x.e) - 50 * (x.a * y.e) - 50 * (x.e * y.a)
      + 40 * (y.a * y.e), by ring⟩ _
  · exact Dvd.dvd.mul_left ⟨sa * y.e + s.e * ya, by rw [hsa, hya]; ring⟩ _

/-- ⭐ **The core shift's class-five row is even** under the two letter columns and the two
dressing rows. -/
theorem gaThreeCore_o_even_of_ae {s x y z₀ z₁ z₂ : SqU6 R}
    (hsa : (2 : R) ∣ s.a) (hxa : (2 : R) ∣ x.a) (hya : (2 : R) ∣ y.a)
    (hse : (2 : R) ∣ s.e) (hxe : (2 : R) ∣ x.e) (hye : (2 : R) ∣ y.e)
    (h0j : (2 : R) ∣ z₀.j) (h1j : (2 : R) ∣ z₁.j) (h2j : (2 : R) ∣ z₂.j)
    (h0l : (2 : R) ∣ z₀.l) (h1l : (2 : R) ∣ z₁.l) (h2l : (2 : R) ∣ z₂.l) :
    (2 : R) ∣ (gaThreeCore s x y z₀ z₁ z₂).o := by
  have hfa : (2 : R) ∣ (sqFoxX6 s x y).a := by
    rw [sqFoxX6_a]
    exact dvd_sub (dvd_sub (Dvd.dvd.mul_left hxa 10) hsa) (Dvd.dvd.mul_left hya 8)
  have hfe : (2 : R) ∣ (sqFoxX6 s x y).e := by
    rw [sqFoxX6_e]
    exact dvd_sub (dvd_sub (Dvd.dvd.mul_left hxe 10) hse) (Dvd.dvd.mul_left hye 8)
  have hfrob : (2 : R) ∣ (-4 * z₁.o + 2 * z₂.o) := ⟨-2 * z₁.o + z₂.o, by ring⟩
  exact dvd_add (dvd_add hfrob (dvd_add (dvd_add (gaThreePair_even_of_ae hxa hxe h0j h0l)
      (gaThreePair_even_of_ae hfa hfe h1j h1l)) (gaThreePair_even_of_ae hya hye h2j h2l)))
    (gaThreeCorr_even_of_ae hsa hya hse hye h0j h1j h2j h0l h1l h2l)

/-- ⭐ **…and so is each handle shift's class-five row**: its two extra blocks pair the letters'
`(5,6)`- and `(1,2)`-columns against the dressings' class-three rows, and both factors are
even. -/
theorem gaThreeHandle_o_even_of_ae {p q z w : SqU6 R} (hpa : (2 : R) ∣ p.a) (hqa : (2 : R) ∣ q.a)
    (hpe : (2 : R) ∣ p.e) (hqe : (2 : R) ∣ q.e) (hzj : (2 : R) ∣ z.j) (hwj : (2 : R) ∣ w.j)
    (hzl : (2 : R) ∣ z.l) (hwl : (2 : R) ∣ w.l) :
    (2 : R) ∣ (gaThreeHandle p q z w).o := by
  refine dvd_add (dvd_sub (dvd_sub (gaThreePair_even_of_ae hqa hqe hzj hzl)
    (gaThreePair_even_of_ae hpa hpe hwj hwl)) ?_) ?_
  · exact Dvd.dvd.mul_right (dvd_sub (Dvd.dvd.mul_left hqe _) (Dvd.dvd.mul_right hpe _)) _
  · exact Dvd.dvd.mul_right (dvd_sub (Dvd.dvd.mul_right hpa _) (Dvd.dvd.mul_left hqa _)) _

/-- ⭐⭐ **THE TWO-COLUMN SOUNDNESS.**  At any marking all of whose slots have an even
`(1,2)`-column and an even `(5,6)`-column, every five-slot `gamma_3`-dressing whose slots have
even class-three rows `j` and `l` moves the relator's class-five row by an EVEN amount. -/
theorem gaThreeShiftO_even_of_ae {m z : Fin (sqRank h) → SqU6 R}
    (ha : ∀ i, (2 : R) ∣ (m i).a) (he : ∀ i, (2 : R) ∣ (m i).e)
    (hj : ∀ i, (2 : R) ∣ (z i).j) (hl : ∀ i, (2 : R) ∣ (z i).l) :
    (2 : R) ∣ gaThreeShiftO h m z := by
  have hblocks : (2 : R) ∣ (sqU6BlockI (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
        * (-4 * (z 1).j + 2 * (z 2).j)
      - sqU6BlockF (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
        * (-4 * (z 1).l + 2 * (z 2).l)) :=
    dvd_sub (Dvd.dvd.mul_left ⟨-2 * (z 1).j + (z 2).j, by ring⟩ _)
      (Dvd.dvd.mul_left ⟨-2 * (z 1).l + (z 2).l, by ring⟩ _)
  refine dvd_add (dvd_add (gaThreeCore_o_even_of_ae (ha 0) (ha 1) (ha 2) (he 0) (he 1) (he 2)
    (hj 0) (hj 1) (hj 2) (hl 0) (hl 1) (hl 2)) ?_) hblocks
  exact Finset.dvd_sum fun k _ =>
    gaThreeHandle_o_even_of_ae (ha _) (ha _) (he _) (he _) (hj _) (hj _) (hl _) (hl _)

end PairAE

section OrthAE

/-- ⭐⭐⭐ **THE PARITY LINE HOLDS ON TWO COLUMNS.**  At any marking all of whose slots have an
even `(1,2)`-column and an even `(5,6)`-column, every achievable stage-four dressing pairs
evenly.  ⭐ Wave 61's `stageOrth_of_outer` asks for a third column, the outer class-two `i`; it
is not needed, because the `i`-channel is closed by the dressing's `j` and the mirror chain
delivers that `j` from the `(1,2)`-column already assumed.

⚠ **Consequence, and it is what makes section 2 rare**: a marking at which the parity line fails
must have an ODD `(1,2)`- or `(5,6)`-column somewhere.  The separating marking has `sepS.a = 1`
and `sepV.a = 1`. -/
theorem stageOrth_of_ae {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R}
    (ha : ∀ i, (2 : gr3R) ∣ (m i).a) (he : ∀ i, (2 : gr3R) ∣ (m i).e) : StageOrth m := by
  have hlA : Subgroup.closure (Set.range m) ≤ sepEvenA := by
    rw [Subgroup.closure_le]
    rintro z ⟨i, rfl⟩
    exact ha i
  have hlE : Subgroup.closure (Set.range m) ≤ fiveEvenE gr3R := by
    rw [Subgroup.closure_le]
    rintro z ⟨i, rfl⟩
    obtain ⟨t, ht⟩ := he i
    exact ⟨t, ht⟩
  intro z hz
  exact gaThreeShiftO_even_of_ae ha he
    (fun i => sepEvenJ_even (forceLcs_two_le_sepEvenJ hlA (hz i)))
    (fun i => (forceLcs_two_le_fiveEvenL hlE (hz i)).2.2.2.2.2.2.2.2.2.imp fun _ ht => ht)

/-- **…so the forcing follows from two columns**, at any central relator. -/
theorem stageForces_of_ae {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R} {c : gr3R}
    (hres : sqRelWord m = SqU6.liftO c) (ha : ∀ i, (2 : gr3R) ∣ (m i).a)
    (he : ∀ i, (2 : gr3R) ∣ (m i).e) : StageForces m :=
  stageForces_of_stageOrth hres (stageOrth_of_ae ha he)

/-- ⭐ **The sharpening is strict**: wave 61's own mixed point has an ODD outer class-two column
at its handle-`V` letter, so `stageOrth_of_outer` does not apply to it as stated with `i`
replaced by nothing - while the two-column condition does, and both columns are even there. -/
theorem stageOrth_of_ae_at_mixStage {h : ℕ} {j : Fin h} : StageOrth (mixStageMark h j) :=
  stageOrth_of_ae (fun i => (mixStage_columns i).1) (fun i => (mixStage_columns i).2.1)

end OrthAE

/-! ## 5 Axiom pins -/

section AxiomPins

#print axioms gaThreeShift_j_even
#print axioms gaThreeShift_k_even
#print axioms gaThreeShift_l_even
#print axioms gaThreeDress_relJ
#print axioms stageForces_of_odd_relJ
#print axioms stageCentral_x1_j_even
#print axioms stageCentral_x1_k_even
#print axioms stageCentral_x1_l_even
#print axioms sepS
#print axioms sepX
#print axioms sepY
#print axioms sepU
#print axioms sepV
#print axioms sepMark
#print axioms sqRelWord_sepMark
#print axioms commP_sepUV_live
#print axioms sepZ
#print axioms sepZ_generator
#print axioms sepZ_isGaThree
#print axioms sepDress
#print axioms sepDress_isGaThree
#print axioms sepDress_mem
#print axioms sepMark_shift
#print axioms sepMark_shiftO
#print axioms sepMark_not_stageOrth
#print axioms sepMark_not_stageCentral
#print axioms sepMark_stageForces
#print axioms sepMark_diag_ne_one
#print axioms sepMark_separates
#print axioms sepMark_decide_crosscheck
#print axioms stageForces_not_imp_stageOrth
#print axioms stageForces_not_imp_stageCentral
#print axioms stageOrth_strictly_stronger
#print axioms sepEvenA
#print axioms sepEvenF
#print axioms sepEvenJ
#print axioms mem_sepEvenA
#print axioms sepEvenJ_even
#print axioms sepEvenF_of_commutator
#print axioms sepEvenJ_of_commutator
#print axioms forceLcs_two_le_sepEvenJ
#print axioms gaThreePair_even_of_ae
#print axioms gaThreeCorr_even_of_ae
#print axioms gaThreeCore_o_even_of_ae
#print axioms gaThreeHandle_o_even_of_ae
#print axioms gaThreeShiftO_even_of_ae
#print axioms stageOrth_of_ae
#print axioms stageForces_of_ae
#print axioms stageOrth_of_ae_at_mixStage

end AxiomPins

end SqCore

end Dyadic

end GQ2

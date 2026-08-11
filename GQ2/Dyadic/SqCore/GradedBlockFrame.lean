/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedBlockRead
import GQ2.Dyadic.SqCore.GradedStageFrame

/-!
# W62-COUNTHOM: the handle-count forcing at the level of continuous homomorphisms

Wave 61's block lane returned a certified negative and one unexpected instrument.  The negative:
the block reading sees nothing about the handle **letters** that the sigma reading does not.  The
instrument: it does see the handle **count**.  `SqU6.pos_of_blockRead_odd` proves that a
relator-killing marking with an odd block reading has `0 < h`, and its soundness is structural
rather than arithmetic, the channel being read at class two, below the achievable lattice.

That instrument lived at the level of marking tuples.  Section 6 of
`docs/dyadic/w61-block-note.md` specified its hom-level transposition and priced it as cheaper
than the class-five sigma transposition, "applied to a statement with **no** soundness hypothesis
at all".  This file does it, and the price is lower still than that.

## ⭐⭐⭐ Headline 1: the transposition, and it carries NO hypothesis whatsoever

`pos_of_blockRead_odd_hom`.  For **every** continuous homomorphism
`Phi : D_sq h -> U_6(Z/8)`, at **every** handle count:

```text
selPar (blockRead (Phi sigma) (Phi x0)) = 1   =>   0 < h
```

No frame hypothesis, no row hypothesis, no gauge, no legality, no lattice, and - the point -
**no relator hypothesis**.  The wave-61 note's statement asked for a homomorphism "whose relator
image is trivial"; that is not a hypothesis at the hom level, it is a theorem, because
`GradedFive.sqU6Balance_gen` says every continuous homomorphism on `D_sq h` kills the relator in
every class-five test group.  The tuple-level statement's single hypothesis is discharged by the
gate, so the transposition is a one-line composite and the result is strictly stronger than the
statement that was ordered.  ⭐ The sharper handle-selection form comes with it
(`exists_handle_minor_odd_hom`), and the arbitrary-frame form
(`pos_of_blockRead_odd_frame`) covers every relator-killing frame of `D_sq h` at once, hence
every automorphic image of the standard one.

## ⭐⭐⭐ Headline 2: what the hom level sees that the tuple level did not

At the hom level the block reading is not a function of two matrices: the `(4,5)`- and
`(5,6)`-columns are **characters** of `D_sq h`, so `blockPar Phi g k` is the wedge of two
characters and therefore an **alternating bi-additive form** on the group.  Four consequences,
none of them statable at the tuple level, where there is no group behind the slots:

* `blockPar_mul_left`, `blockPar_mul_right`, `blockPar_inv_left`, `blockPar_self`,
  `blockPar_swap`: bi-additive, alternating, and symmetric mod `2`;
* ⭐ `blockPar_commP_left`: it **kills commutators**, so it is a form on the abelianisation;
* ⭐ `blockPar_dsqX1_right`: the **torsion letter is invisible** to it at every handle count,
  because the relator's own `(4,5)`- and `(5,6)`-rows force both of its columns even
  (`selPar_d_dsqX1`, `selPar_e_dsqX1`);
* ⭐⭐⭐ `blockPar_handleFree`: at `h = 0` the form dies on **every pair of elements of
  `D_sq 0`**, not merely on the two committed slots.  Hence ⭐⭐⭐ `pos_of_blockPar_odd`: an odd
  block pairing of **any two elements** of `D_sq h`, at **any** continuous homomorphism, forces
  `0 < h`.

That last statement is the one to consume.  It mentions no marking, no frame and no generator,
so it is an invariant of the topological group `D_sq h` and of the set of its continuous
`U_6(Z/8)`-quotients, and it is a strict generalisation: `blockPar_blockCexHom_handle` shows the
pairing is live on a **handle** pair as well as on the core pair, which the tuple statement
cannot reach.

## ⭐⭐⭐ Headline 3: the mechanism, as a symplectic identity

`blockPar_relator_frame`.  At every relator-killing frame `n` of `D_sq h` and every continuous
homomorphism:

```text
omega(n 0, n 1)  =  sum_j  omega(n u_j, n v_j)      (mod 2)
```

the relator's class-two content, read through the wedge of the two abelian columns.  The
handle-count forcing is the `h = 0` instance, where the right-hand side is the empty sum, and
`SqU6.exists_handle_minor_odd` is the statement that a non-zero left-hand side needs a non-zero
summand.  ⭐ `blockPar_blockCexHom_crosscheck` computes both sides at wave 59's counterexample
independently and they agree.

## ⭐⭐ Headline 4: it is a CHARACTERISATION, not only a forcing

`exists_blockPar_odd_iff_pos`:

```text
(exists Phi, exists g k in D_sq h, blockPar Phi g k = 1)   <->   0 < h
```

The forward half is Headline 2.  The backward half is `blockCexHom h j`, the committed
class-five lift of wave 59's counterexample marking, which is an honest continuous homomorphism
at **every** `h >= 1` and every handle and whose core pairing is `1`
(`blockPar_blockCexHom`).  So the instrument decides `0 < h` exactly, and by doctrine the sharp
form is what is stated.

## ⚠ Honesty 1: on `sqArbFrame` the conclusion `0 < h` is FREE, and this file says so

The brief asked for the forcing "for an honest continuous homomorphism on `D_sq h` and an honest
`sqArbFrame`".  It is here (`pos_of_blockPar_odd_sqArbFrame`) and it is one line, but the
conclusion is **not content**: `sqArbFrame h nu' j a` is indexed by a handle `j : Fin h`, so
`0 < h` is available from `j` before the block reading is consulted.  Reporting that statement as
the deliverable would be technically true and useless.

What the instrument actually says at the arbitrary-dressing frame is three things, and they are
the ones stated:

* ⭐⭐ `blockPar_sqArbFrame`: the symplectic identity on the frame - the two dressed core slots
  pair as the sum of the frame's own handle pairs, at every relator-killing arbitrary-dressing
  frame;
* ⭐ `exists_handle_blockPar_odd_sqArbFrame`: an odd core pairing names a **handle of the
  frame** that carries it;
* ⭐⭐ `blockPar_dress_eq_zero` and `blockPar_sigArbDress_sqArbFrame`: the dressing forcing in
  the campaign's usual shape, with the dressing an honest element of `D_sq h` rather than a
  matrix - a sigma-only dressing that keeps a relator-killing frame relator-killing pairs
  **evenly** against that frame's `x0` slot.  This is
  `SqU6.selPar_blockRead_dress_of_relator` transposed, and it inherits that theorem's scope:
  the handle letters are untouched by a sigma-only dressing, so the whole right-hand side of the
  identity cancels and only the dressing's own pairing is left.

## ⚠ Honesty 2: NO committed statement can drop its `0 < h`, and that is certified here

The brief asked which committed statements could drop their positivity hypothesis by consuming
this one.  The answer is **none**, and the reason is not that the instrument is weak but that
`0 < h` is never an incidental hypothesis in this lane: the statements that carry it are **false
at `h = 0`**.  Certified rather than asserted:

* `sqEichRelWord_handleFree`: `SqEichRelWord 0` is TRUE (its `j : Fin h` binder is empty), so
  `EichRefutation.not_sqEichRelWord` cannot drop `0 < h`.  The same one-line argument covers
  `SqEichRelWordT`, `SqEichRelWordMix`, `SqEichRelWordUV` and `SqArbRelWord` - `ArbFrames`
  already records the last of these;
* `sqHandleMixFixesCore_handleFree`: `SqHandleMixFixesCore 0 c` is TRUE for **every** `c`, by
  the identity automorphism, since at `h = 0` both handle clauses are empty.  So
  `HandleMixFixesCore.not_sqHandleMixFixesCore` and `isUnit_of_sqHandleMixFixesCore` cannot drop
  theirs either;
* `PivotClimb.sqPivotUnitizer_zero` is already committed and says the same about
  `not_sqPivotUnitizer`.

⭐ What the instrument does instead is **supply** the hypothesis from a hom-level datum, and four
composites are proved to show the shape: `not_sqEichRelWord_of_blockPar_odd`,
`not_sqEichRelWordUV_of_blockPar_odd`, `not_sqHandleMixFixesCore_of_blockPar_odd`,
`not_sqPivotUnitizer_of_blockPar_odd`.  ⚠ Read them for what they are: by Headline 4 the
supplied hypothesis is **equivalent** to `0 < h`, so these are not stronger theorems, they are
the same theorems with an input another lane can produce without counting handles.

## ⚠ Honesty 3: the committed class-five witnesses are BLOCK-BLIND

`blockPar_fiveFrameHom`, `blockPar_fiveFrameHom_handle`, `blockPar_stageFrameHom`,
`blockPar_stageFrameHom_handle`: wave 60's binder point and wave 61's stage-four point have an
**even** block pairing on the core pair *and* on the live handle pair.  So the instrument says
nothing at either of the two points the class-five lanes actually run at, and wave 59's
counterexample remains the only committed point at which the channel is live.  Any lane hoping
to feed this into the class-five stack has to move the point first.

## ⭐ The legality analysis does NOT arise, and that is the structural difference

Wave 61 warned that `GradedFiveFrame`'s legality argument had to be **redone** at
`GradedStageFrame`'s point rather than inherited, and the warning was right about that file.  It
does not transfer here, and not because the argument was easier: **there is no legality analysis
at all.**  `ArbFrames` asks the dressings of `sqArbFrame` to lie in `ker lambda ∩ ker nu'`, and
that question arises only when a statement quantifies over a dressing class.  Every statement in
this file quantifies over the whole of `D_sq h` or over an arbitrary relator-killing frame, so
there is no dressing class to be legal in.  For the same reason no statement here carries a row
hypothesis: `fiveFrameHom_sqArbFrame` and `stageFrameHom_sqArbFrame` need `nu'(u_j) = nu'(v_j) = 1`
because they identify the frame's image with a **binder point**, and nothing here identifies
anything with a point - the gate `sqU6Balance` fires at every frame that kills the relator.
This is the first statement of the lane for which the `ArbFrames` legality question and the
forced-row certificate both simply do not apply.

## PROVED versus MEASURED

**PROVED** (this file, no `sorry`, no new axiom, no `native_decide`; every `decide` is on
`ZMod 8` or `ZMod 2`): everything above, at every handle count and every handle, for every
continuous homomorphism, with no hypothesis anywhere except the ones displayed in the statements.

**MEASURED** (`scripts/w62_counthom/`, certified output in `results/verify_counthom.txt`;
`37` named checks, `0` failures, on the independently certified `U_6(Z/8)` of
`scripts/w59_blind5/u6lib.py` through `scripts/w61_block/blocklib.py`):

| measurement | scale | result |
|---|---|---|
| the pairing is bi-additive, alternating, symmetric, inverse- and commutator-killing | `20000` each | `0` failures |
| bi-additivity, **exhaustive** on the four live columns | `262144` points | `0` failures |
| the relator's two abelian rows force the `x1` columns even, **exhaustive** | `16 + 16` | `0` odd |
| the symplectic identity at honestly collected relator-killing markings | `201` markings, `h = 0..4` | `0` mismatches |
| the `h = 0` vanishing on the generated subgroup, **exhaustive** over `F_2^2` | `10` admissible data | `0` live pairs |
| …with both hypotheses dropped in turn, as controls | `16` and `64` | live, so neither is idle |
| the committed points, all six readings | - | as in the Lean `decide`s |
| the composite check at `blindCexMark` | `h = 1..4`, every handle | both sides `1` |
| non-vacuity, and the `h = 0` exclusion | `129` and `477` markings | `32.6 %` live, `0` live |

## Contents

* **1** ⭐⭐⭐ the forcing at the hom level, and at an arbitrary relator-killing frame;
* **2** the block pairing, its bi-additivity, and the character it defines;
* **3** ⭐⭐⭐ the symplectic identity;
* **4** ⭐⭐⭐ the torsion letter, the `h = 0` vanishing on every pair, and the pair forcing;
* **5** the counterexample hom, ⭐⭐ the characterisation, and the block-blindness of the two
  committed class-five witnesses;
* **6** ⚠ the arbitrary-dressing frame, honestly;
* **7** ⚠ composability: why no committed statement drops `0 < h`, and the four composites;
* **8** axiom pins.

## Axiom hygiene

All **56** committed prints are **std-3** (`propext`, `Classical.choice`, `Quot.sound`); no
census axiom is reachable, `sqPivotExp` included, and it is reachable neither through
`blockCexHom` nor through the four composites.

## Merge notes

Nothing is redefined.  `SqU6.blockRead`, `SqU6.pos_of_blockRead_odd`,
`SqU6.exists_handle_minor_odd`, `SqU6.selPar_handleWord_i_of_relator`,
`SqU6.selPar_blockRead_dress_of_relator` come from `GradedBlockRead`; `SqU6.handleWord_i`,
`SqU6.sqRelWord_d`, `SqU6.sqRelWord_e`, `SqU6.mul_d`, `SqU6.mul_e`, `SqU6.one_d`, `SqU6.one_e`,
`sqU6Hom`, `sqU6Hom_gen`, `sqU6Balance`, `sqU6Balance_gen`, `fiveTuple_zero`, `fiveTuple_one`,
`fiveTuple_handleU`, `fiveTuple_handleV`, `fiveTuple_handleU_ne`, `fiveTuple_handleV_ne` come
from `GradedFive`; `blindCexMark`, `sqRelWord_blindCexMark`, `blindCexS`, `blindCexX`,
`blindCexU`, `blindCexV`, `blindCex_blockRead_odd` come from `GradedFiveBlind`; `abelRow_even`
from `GradedSigmaFive`; `selPar` and its laws from `GradedSelect`; `gr3R`, `gr3R_card` from
`GradedSelect`; `dsq_relation`, `dsq_hom_ext`, `sqGen`, `dsqSigma`, `dsqX0`, `dsqX1`, `sqRank`,
`sqRelWord`, `sqHandleIdxU`, `sqHandleIdxV`, `sqVal_one`, `sqHandleIdxU_val`, `sqHandleIdxV_val`
from `Cores`; `sqIdx_cases` from `Certificate`; `sqArbFrame`, `sqArbBase_zero`, `sqArbBase_one`,
`SqEichRelWord` from `ArbFrames`/`LamFrames`; `sigArbDress`, `sigArbDress_zero`,
`sigArbDress_ne` from `GradedFourHom`; `fiveFrameHom` and its letter values from
`GradedFiveFrame`; `stageFrameHom` and its letter values from `GradedStageFrame`;
`not_sqEichRelWord`, `not_sqEichRelWordUV` from `EichRefutation`; `SqHandleMixFixesCore`,
`not_sqHandleMixFixesCore` from `Certificate`/`HandleMixFixesCore`; `SqPivotUnitizer`,
`not_sqPivotUnitizer` from `PivotUnitizer`/`PivotClimb`; `commP` from `GQ2/Words.lean`.
`sqArbFrame_zero` and `sqArbFrame_one` are new here and are the only additions to imported API.

## What this file does NOT do

The two smaller items of `docs/dyadic/w61-block-note.md` section 6.3 are untouched: the
`(5,6)`-row variant of the block equation, and the second block reading `s_34 x_45 - s_45 x_34`
at the `(3,5)` row under the corner symmetry.  The second one is the interesting one at the hom
level, because it would be a **second** alternating form on `D_sq h` built from a different pair
of columns, and whether the two together pin more than either alone is not measured anywhere.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The forcing at the hom level -/

section HomForcing

variable {h : ℕ}

/-- ⭐⭐⭐ **THE HANDLE-COUNT FORCING AT THE HOM LEVEL, AND IT CARRIES NO HYPOTHESIS.** -/
theorem pos_of_blockRead_odd_hom (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R))
    (hodd : selPar (SqU6.blockRead (Phi (dsqSigma h)) (Phi (dsqX0 h))) = 1) : 0 < h :=
  SqU6.pos_of_blockRead_odd (sqU6Balance_gen Phi) hodd

/-- The same at an arbitrary relator-killing frame of `D_sq h`. -/
theorem pos_of_blockRead_odd_frame (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R))
    {n : Fin (sqRank h) → (DSq h : Type)} (hn : sqRelWord n = 1)
    (hodd : selPar (SqU6.blockRead (Phi (n 0)) (Phi (n 1))) = 1) : 0 < h :=
  SqU6.pos_of_blockRead_odd (sqU6Balance Phi n hn) hodd

/-- The sharper form: some handle pair's letters are independent mod `2`. -/
theorem exists_handle_minor_odd_hom (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R))
    (hodd : selPar (SqU6.blockRead (Phi (dsqSigma h)) (Phi (dsqX0 h))) = 1) :
    ∃ j : Fin h, selPar ((Phi (sqGen h (sqHandleIdxU j))).d * (Phi (sqGen h (sqHandleIdxV j))).e
      - (Phi (sqGen h (sqHandleIdxV j))).d * (Phi (sqGen h (sqHandleIdxU j))).e) = 1 := by
  obtain ⟨j, hj⟩ := SqU6.exists_handle_minor_odd (m := fun i => Phi (sqGen h i))
    (sqU6Balance_gen Phi) hodd
  exact ⟨j, hj⟩

end HomForcing

/-! ## 2 The block pairing -/

section Pairing

variable {h : ℕ}

/-- **The block pairing of a continuous homomorphism.** -/
noncomputable def blockPar (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R))
    (g k : (DSq h : Type)) : ZMod 2 := selPar (SqU6.blockRead (Phi g) (Phi k))

theorem blockPar_def (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R))
    (g k : (DSq h : Type)) :
    blockPar Phi g k = selPar (SqU6.blockRead (Phi g) (Phi k)) := rfl

variable {Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R)}

private theorem zmodTwo_zero_sub : ∀ a : ZMod 2, 0 - a = a := by decide

private theorem zmodTwo_eq_zero_of_ne : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide

/-- The pairing is alternating. -/
@[simp] theorem blockPar_self (g : (DSq h : Type)) : blockPar Phi g g = 0 := by
  rw [blockPar, show SqU6.blockRead (Phi g) (Phi g) = 0 by rw [SqU6.blockRead]; ring, selPar_zero]

/-- …hence symmetric mod `2`. -/
theorem blockPar_swap (g k : (DSq h : Type)) : blockPar Phi g k = blockPar Phi k g := by
  rw [blockPar, blockPar,
    show SqU6.blockRead (Phi g) (Phi k) = 0 - SqU6.blockRead (Phi k) (Phi g) by
      rw [SqU6.blockRead, SqU6.blockRead]; ring,
    selPar_sub, selPar_zero, zmodTwo_zero_sub]

/-- The pairing is additive in its right argument. -/
theorem blockPar_mul_right (g k k' : (DSq h : Type)) :
    blockPar Phi g (k * k') = blockPar Phi g k + blockPar Phi g k' := by
  rw [blockPar, blockPar, blockPar, map_mul,
    show SqU6.blockRead (Phi g) (Phi k * Phi k')
      = SqU6.blockRead (Phi g) (Phi k) + SqU6.blockRead (Phi g) (Phi k') by
      rw [SqU6.blockRead, SqU6.blockRead, SqU6.blockRead, SqU6.mul_d, SqU6.mul_e]; ring,
    selPar_add]

/-- …and in its left argument. -/
theorem blockPar_mul_left (g g' k : (DSq h : Type)) :
    blockPar Phi (g * g') k = blockPar Phi g k + blockPar Phi g' k := by
  rw [blockPar_swap (Phi := Phi) (g * g') k, blockPar_mul_right,
    blockPar_swap (Phi := Phi) k g, blockPar_swap (Phi := Phi) k g']

@[simp] theorem blockPar_one_right (g : (DSq h : Type)) : blockPar Phi g 1 = 0 := by
  rw [blockPar, map_one, SqU6.blockRead, SqU6.one_d, SqU6.one_e, mul_zero, mul_zero, sub_zero,
    selPar_zero]

@[simp] theorem blockPar_one_left (k : (DSq h : Type)) : blockPar Phi 1 k = 0 := by
  rw [blockPar_swap (Phi := Phi) 1 k, blockPar_one_right]

@[simp] theorem blockPar_inv_left (g k : (DSq h : Type)) :
    blockPar Phi g⁻¹ k = -blockPar Phi g k := by
  have hz : blockPar Phi g⁻¹ k + blockPar Phi g k = 0 := by
    rw [← blockPar_mul_left, inv_mul_cancel, blockPar_one_left]
  linear_combination hz

@[simp] theorem blockPar_inv_right (g k : (DSq h : Type)) :
    blockPar Phi g k⁻¹ = -blockPar Phi g k := by
  rw [blockPar_swap (Phi := Phi) g k⁻¹, blockPar_inv_left, blockPar_swap (Phi := Phi) k g]

/-- ⭐ **The pairing kills the commutator subgroup**, so it is a form on the abelianization: a
statement the tuple level cannot make, because a tuple has no group structure behind it. -/
@[simp] theorem blockPar_commP_left (g g' k : (DSq h : Type)) :
    blockPar Phi (commP g g') k = 0 := by
  rw [commP, blockPar_mul_left, blockPar_mul_left, blockPar_mul_left, blockPar_inv_left,
    blockPar_inv_left]
  ring

@[simp] theorem blockPar_commP_right (g g' k : (DSq h : Type)) :
    blockPar Phi g (commP g' k) = 0 := by
  rw [blockPar_swap (Phi := Phi) g (commP g' k), blockPar_commP_left]

variable (Phi) in
/-- **The pairing against a fixed element, as a continuous character of `D_sq h`.** -/
noncomputable def blockParChar (g : (DSq h : Type)) :
    ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2)) where
  toFun k := ofAdd (blockPar Phi g k)
  map_one' := by rw [blockPar_one_right]; rfl
  map_mul' k k' := by rw [blockPar_mul_right, ofAdd_add]
  continuous_toFun :=
    (continuous_of_discreteTopology (f := fun p : SqU6 gr3R =>
      ofAdd (selPar (SqU6.blockRead (Phi g) p)))).comp Phi.continuous_toFun

@[simp] theorem blockParChar_apply (g k : (DSq h : Type)) :
    blockParChar Phi g k = ofAdd (blockPar Phi g k) := rfl

/-- A character vanishing on the generators vanishes. -/
theorem blockPar_eq_zero_of_gen_right {g : (DSq h : Type)}
    (hgen : ∀ i, blockPar Phi g (sqGen h i) = 0) (k : (DSq h : Type)) :
    blockPar Phi g k = 0 := by
  have hext : blockParChar Phi g = blockParChar Phi 1 :=
    dsq_hom_ext _ _ fun i => by
      rw [blockParChar_apply, blockParChar_apply, hgen i, blockPar_one_left]
  have hk := DFunLike.congr_fun hext k
  rw [blockParChar_apply, blockParChar_apply, blockPar_one_left] at hk
  exact Multiplicative.ofAdd.injective hk

/-- …and the same in the left argument. -/
theorem blockPar_eq_zero_of_gen_left {k : (DSq h : Type)}
    (hgen : ∀ i, blockPar Phi (sqGen h i) k = 0) (g : (DSq h : Type)) :
    blockPar Phi g k = 0 := by
  rw [blockPar_swap]
  exact blockPar_eq_zero_of_gen_right (fun i => by
    rw [blockPar_swap]; exact hgen i) g

end Pairing

/-! ## 3 The symplectic identity -/

section Symplectic

variable {h : ℕ}

private def selParHom : gr3R →+ ZMod 2 where
  toFun := selPar
  map_zero' := selPar_zero
  map_add' := selPar_add

private theorem selPar_sum {ι : Type} [Fintype ι] (f : ι → gr3R) :
    selPar (∑ i, f i) = ∑ i, selPar (f i) := map_sum selParHom f Finset.univ

/-- ⭐⭐⭐ **THE SYMPLECTIC IDENTITY.**  The block pairing of the two core letters is the sum of
the block pairings of the handle pairs, at every relator-killing frame of `D_sq h` and every
continuous homomorphism. -/
theorem blockPar_relator_frame (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R))
    {n : Fin (sqRank h) → (DSq h : Type)} (hn : sqRelWord n = 1) :
    blockPar Phi (n 0) (n 1)
      = ∑ j : Fin h, blockPar Phi (n (sqHandleIdxU j)) (n (sqHandleIdxV j)) := by
  have hb := SqU6.selPar_handleWord_i_of_relator (sqU6Balance Phi n hn)
  rw [SqU6.handleWord_i] at hb
  rw [blockPar_def, ← hb, selPar_sum]
  exact Finset.sum_congr rfl fun j _ => congrArg selPar (by rw [SqU6.blockRead]; ring)

/-- The identity at the standard frame, where the relator hypothesis is `dsq_relation`. -/
theorem blockPar_relator (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R)) :
    blockPar Phi (dsqSigma h) (dsqX0 h)
      = ∑ j : Fin h, blockPar Phi (sqGen h (sqHandleIdxU j)) (sqGen h (sqHandleIdxV j)) :=
  blockPar_relator_frame Phi (dsq_relation h)

end Symplectic

/-! ## 4 The torsion letter, and the handle-free vanishing -/

section HandleFree

variable {h : ℕ} {Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R)}

/-- **The torsion letter has an even `(4,5)`-column** at every continuous homomorphism: the
relator's own `(4,5)`-row forces it, with no hypothesis. -/
theorem selPar_d_dsqX1 : selPar (Phi (dsqX1 h)).d = 0 := by
  have h0 : (sqRelWord fun i => Phi (sqGen h i)).d = 0 := by rw [sqU6Balance_gen Phi]; rfl
  rw [SqU6.sqRelWord_d] at h0
  obtain ⟨c, hc⟩ :=
    abelRow_even (Phi (sqGen h 1)).d (Phi (sqGen h 2)).d (by linear_combination h0)
  rw [dsqX1]
  exact (selPar_eq_zero_iff _).mpr ⟨c, hc⟩

/-- …and an even `(5,6)`-column, by the relator's `(5,6)`-row. -/
theorem selPar_e_dsqX1 : selPar (Phi (dsqX1 h)).e = 0 := by
  have h0 : (sqRelWord fun i => Phi (sqGen h i)).e = 0 := by rw [sqU6Balance_gen Phi]; rfl
  rw [SqU6.sqRelWord_e] at h0
  obtain ⟨c, hc⟩ :=
    abelRow_even (Phi (sqGen h 1)).e (Phi (sqGen h 2)).e (by linear_combination h0)
  rw [dsqX1]
  exact (selPar_eq_zero_iff _).mpr ⟨c, hc⟩

/-- **The torsion letter is invisible to the block pairing**, at every handle count. -/
@[simp] theorem blockPar_dsqX1_right (g : (DSq h : Type)) : blockPar Phi g (dsqX1 h) = 0 := by
  rw [blockPar_def, SqU6.blockRead, selPar_sub, selPar_mul, selPar_mul, selPar_d_dsqX1,
    selPar_e_dsqX1, mul_zero, mul_zero, sub_zero]

@[simp] theorem blockPar_dsqX1_left (k : (DSq h : Type)) : blockPar Phi (dsqX1 h) k = 0 := by
  rw [blockPar_swap, blockPar_dsqX1_right]

private theorem sqIdx_cases_handleFree (i : Fin (sqRank 0)) : i = 0 ∨ i = 1 ∨ i = 2 := by
  rcases sqIdx_cases i with hi | hi | hi | ⟨j, _⟩ | ⟨j, _⟩
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hi)
  · exact absurd j.isLt (by omega)
  · exact absurd j.isLt (by omega)

/-- **At `h = 0` the two core letters pair evenly**: the empty sum of the symplectic
identity. -/
theorem blockPar_sigma_x0_handleFree (Psi : ContinuousMonoidHom (DSq 0 : Type) (SqU6 gr3R)) :
    blockPar Psi (dsqSigma 0) (dsqX0 0) = 0 := by
  rw [blockPar_relator Psi]
  exact Finset.sum_empty

/-- ⭐⭐⭐ **AT `h = 0` THE BLOCK PAIRING VANISHES ON EVERY PAIR OF GROUP ELEMENTS.**  Not merely
on the two committed slots: the pairing is a wedge of two continuous characters, the torsion
letter is in the kernel of both mod `2`, and the relator kills the one remaining pairing, so the
whole form dies. -/
theorem blockPar_handleFree (Psi : ContinuousMonoidHom (DSq 0 : Type) (SqU6 gr3R))
    (g k : (DSq 0 : Type)) : blockPar Psi g k = 0 := by
  have hsx := blockPar_sigma_x0_handleFree Psi
  have hsig : ∀ x : (DSq 0 : Type), blockPar Psi x (dsqSigma 0) = 0 := by
    refine fun x => blockPar_eq_zero_of_gen_left (fun i => ?_) x
    rcases sqIdx_cases_handleFree i with rfl | rfl | rfl
    · exact blockPar_self _
    · rw [show (1 : Fin (sqRank 0)) = 1 from rfl, ← dsqX0, blockPar_swap]
      exact hsx
    · exact blockPar_dsqX1_left _
  have hx0 : ∀ x : (DSq 0 : Type), blockPar Psi x (dsqX0 0) = 0 := by
    refine fun x => blockPar_eq_zero_of_gen_left (fun i => ?_) x
    rcases sqIdx_cases_handleFree i with rfl | rfl | rfl
    · exact hsx
    · exact blockPar_self _
    · exact blockPar_dsqX1_left _
  refine blockPar_eq_zero_of_gen_right (fun i => ?_) k
  rcases sqIdx_cases_handleFree i with rfl | rfl | rfl
  · exact hsig g
  · exact hx0 g
  · exact blockPar_dsqX1_right _

/-- ⭐⭐⭐ **THE FORCING ON AN ARBITRARY PAIR.**  An odd block pairing of *any two elements* of
`D_sq h` at *any* continuous homomorphism forces `0 < h`.  No frame, no marking, no relator
hypothesis: this is the shape the tuple level cannot state. -/
theorem pos_of_blockPar_odd (g k : (DSq h : Type)) (hodd : blockPar Phi g k = 1) : 0 < h := by
  rcases Nat.eq_zero_or_pos h with rfl | hp
  · rw [blockPar_handleFree Phi g k] at hodd
    exact absurd hodd (by decide)
  · exact hp

end HandleFree

/-! ## 5 Realizability, and the characterisation -/

section Realize

variable {h : ℕ} {j : Fin h}

variable (h j) in
/-- **The counterexample hom.**  Wave 59's counterexample marking kills the relator at every
handle count and every handle (`sqRelWord_blindCexMark`), so the committed class-five lift turns
it into an honest continuous homomorphism `D_sq h → U_6(ℤ/8)`. -/
noncomputable def blockCexHom : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R) :=
  sqU6Hom gr3R_card h (blindCexMark h j) (sqRelWord_blindCexMark h j)

@[simp] theorem blockCexHom_gen (i : Fin (sqRank h)) :
    blockCexHom h j (sqGen h i) = blindCexMark h j i := sqU6Hom_gen _ _ _ i

@[simp] theorem blockCexHom_sigma : blockCexHom h j (dsqSigma h) = blindCexS := by
  rw [dsqSigma, blockCexHom_gen]
  simp only [blindCexMark, fiveTuple_zero]

@[simp] theorem blockCexHom_x0 : blockCexHom h j (dsqX0 h) = blindCexX := by
  rw [dsqX0, blockCexHom_gen]
  simp only [blindCexMark, fiveTuple_one]

@[simp] theorem blockCexHom_handleU :
    blockCexHom h j (sqGen h (sqHandleIdxU j)) = blindCexU := by
  rw [blockCexHom_gen]
  simp only [blindCexMark, fiveTuple_handleU]

@[simp] theorem blockCexHom_handleV :
    blockCexHom h j (sqGen h (sqHandleIdxV j)) = blindCexV := by
  rw [blockCexHom_gen]
  simp only [blindCexMark, fiveTuple_handleV]

/-- ⭐⭐ **The instrument is live at every positive handle count.** -/
theorem blockPar_blockCexHom : blockPar (blockCexHom h j) (dsqSigma h) (dsqX0 h) = 1 := by
  rw [blockPar_def, blockCexHom_sigma, blockCexHom_x0]
  exact blindCex_blockRead_odd

/-- …and it is live on a **handle pair** as well as on the core pair, which is what makes
`pos_of_blockPar_odd` a strict generalisation rather than a restatement. -/
theorem blockPar_blockCexHom_handle :
    blockPar (blockCexHom h j) (sqGen h (sqHandleIdxU j)) (sqGen h (sqHandleIdxV j)) = 1 := by
  rw [blockPar_def, blockCexHom_handleU, blockCexHom_handleV]
  decide

/-- The right-hand side of the symplectic identity at the counterexample hom, computed
independently: only the live handle contributes and it contributes `1`. -/
theorem blockPar_blockCexHom_sum :
    (∑ j' : Fin h, blockPar (blockCexHom h j) (sqGen h (sqHandleIdxU j'))
      (sqGen h (sqHandleIdxV j'))) = 1 := by
  rw [Finset.sum_eq_single j ?_ ?_]
  · exact blockPar_blockCexHom_handle
  · intro j' _ hne
    simp only [blockPar_def, blockCexHom_gen, blindCexMark, fiveTuple_handleU_ne hne,
      fiveTuple_handleV_ne hne]
    decide
  · intro hcon
    exact absurd (Finset.mem_univ j) hcon

/-- ⭐ **The composite check the doctrine asks for.**  Both sides of the symplectic identity at
the counterexample hom are computed from the point rather than from the identity, and they
agree. -/
theorem blockPar_blockCexHom_crosscheck :
    blockPar (blockCexHom h j) (dsqSigma h) (dsqX0 h)
      = ∑ j' : Fin h, blockPar (blockCexHom h j) (sqGen h (sqHandleIdxU j'))
          (sqGen h (sqHandleIdxV j')) := by
  rw [blockPar_blockCexHom, blockPar_blockCexHom_sum]

/-- ⭐⭐⭐ **THE CHARACTERISATION.**  The block pairing is odd on some pair of elements of
`D_sq h` at some continuous homomorphism **if and only if** `0 < h`.  Both halves are proved:
the forward one is the forcing, the backward one is the counterexample hom. -/
theorem exists_blockPar_odd_iff_pos {h : ℕ} :
    (∃ (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R)) (g k : (DSq h : Type)),
      blockPar Phi g k = 1) ↔ 0 < h := by
  constructor
  · rintro ⟨Phi, g, k, hodd⟩
    exact pos_of_blockPar_odd (Phi := Phi) g k hodd
  · intro hp
    exact ⟨blockCexHom h ⟨0, hp⟩, dsqSigma h, dsqX0 h, blockPar_blockCexHom⟩

/-- ⚠ **The committed class-five witnesses are block-blind.**  Wave 60's binder point and wave
61's stage-four point both have an **even** block pairing on the core pair and on the live handle
pair, so the instrument says nothing at either.  Wave 59's counterexample is the only committed
point at which the block channel is live, and `blockPar_blockCexHom` is that fact. -/
theorem blockPar_fiveFrameHom : blockPar (fiveFrameHom h j) (dsqSigma h) (dsqX0 h) = 0 := by
  rw [blockPar_def, fiveFrameHom_sigma, fiveFrameHom_x0]
  decide

theorem blockPar_fiveFrameHom_handle :
    blockPar (fiveFrameHom h j) (sqGen h (sqHandleIdxU j)) (sqGen h (sqHandleIdxV j)) = 0 := by
  rw [blockPar_def, fiveFrameHom_handleU, fiveFrameHom_handleV]
  decide

theorem blockPar_stageFrameHom : blockPar (stageFrameHom h j) (dsqSigma h) (dsqX0 h) = 0 := by
  rw [blockPar_def, stageFrameHom_sigma, stageFrameHom_x0]
  decide

theorem blockPar_stageFrameHom_handle :
    blockPar (stageFrameHom h j) (sqGen h (sqHandleIdxU j)) (sqGen h (sqHandleIdxV j)) = 0 := by
  rw [blockPar_def, stageFrameHom_handleU, stageFrameHom_handleV]
  decide

end Realize

/-! ## 6 The arbitrary-dressing frame -/

section ArbFrame

variable {h : ℕ} {j : Fin h}
variable {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}
variable {a : Fin (sqRank h) → (DSq h : Type)}

@[simp] theorem sqArbFrame_zero : sqArbFrame h nu' j a 0 = dsqSigma h * a 0 := by
  rw [sqArbFrame, sqArbBase_zero]

@[simp] theorem sqArbFrame_one : sqArbFrame h nu' j a 1 = dsqX0 h * a 1 := by
  rw [sqArbFrame, sqArbBase_one]

/-- ⚠ **The forcing on `sqArbFrame`, and the honest reading of it.**  The statement is true and
the proof is one line, but the conclusion is **free**: `sqArbFrame` is indexed by a handle
`j : Fin h`, so `0 < h` is already available from `j` before the block reading is consulted.
The content of the instrument at the arbitrary-dressing frame is therefore **not** the handle
count but `blockPar_sqArbFrame` below, which says *which* handles carry it. -/
theorem pos_of_blockPar_odd_sqArbFrame (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R))
    (hrel : sqRelWord (sqArbFrame h nu' j a) = 1)
    (hodd : blockPar Phi (sqArbFrame h nu' j a 0) (sqArbFrame h nu' j a 1) = 1) : 0 < h :=
  pos_of_blockRead_odd_frame Phi hrel hodd

/-- ⭐⭐ **The symplectic identity on the arbitrary-dressing frame.**  At every relator-killing
arbitrary-dressing frame and every continuous homomorphism, the block pairing of the two dressed
core slots is the sum of the block pairings of the frame's own handle pairs. -/
theorem blockPar_sqArbFrame (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R))
    (hrel : sqRelWord (sqArbFrame h nu' j a) = 1) :
    blockPar Phi (dsqSigma h * a 0) (dsqX0 h * a 1)
      = ∑ j' : Fin h, blockPar Phi (sqArbFrame h nu' j a (sqHandleIdxU j'))
          (sqArbFrame h nu' j a (sqHandleIdxV j')) := by
  have hb := blockPar_relator_frame Phi hrel
  rwa [sqArbFrame_zero, sqArbFrame_one] at hb

/-- …hence an odd pairing of the dressed core slots forces an odd pairing at some handle of the
frame: `SqU6.exists_handle_minor_odd` on `sqArbFrame`. -/
theorem exists_handle_blockPar_odd_sqArbFrame
    (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R))
    (hrel : sqRelWord (sqArbFrame h nu' j a) = 1)
    (hodd : blockPar Phi (dsqSigma h * a 0) (dsqX0 h * a 1) = 1) :
    ∃ j' : Fin h, blockPar Phi (sqArbFrame h nu' j a (sqHandleIdxU j'))
      (sqArbFrame h nu' j a (sqHandleIdxV j')) = 1 := by
  by_contra hcon
  have hz : ∀ j' : Fin h, blockPar Phi (sqArbFrame h nu' j a (sqHandleIdxU j'))
      (sqArbFrame h nu' j a (sqHandleIdxV j')) = 0 := fun j' =>
    zmodTwo_eq_zero_of_ne _ (not_exists.mp hcon j')
  rw [blockPar_sqArbFrame Phi hrel, Finset.sum_congr rfl fun j' _ => hz j',
    Finset.sum_const_zero] at hodd
  exact absurd hodd (by decide)

/-- ⭐⭐ **The dressing forcing at the hom level.**  A sigma-only dressing that keeps a
relator-killing frame relator-killing pairs **evenly** against the frame's `x0` slot.  The handle
letters are untouched by a sigma-only dressing, so the whole right-hand side of the symplectic
identity cancels and the dressing's own pairing is all that is left.

This is `SqU6.selPar_blockRead_dress_of_relator` at the hom level, and unlike it the dressing is
an honest element of `D_sq h` rather than a matrix. -/
theorem blockPar_dress_eq_zero (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R))
    {n : Fin (sqRank h) → (DSq h : Type)} (g : (DSq h : Type)) (hn : sqRelWord n = 1)
    (hn' : sqRelWord (fun i => n i * sigArbDress h g i) = 1) :
    blockPar Phi g (n 1) = 0 := by
  have h1 := blockPar_relator_frame Phi hn
  have h2 := blockPar_relator_frame Phi hn'
  have e0 : n 0 * sigArbDress h g 0 = n 0 * g := by rw [sigArbDress_zero]
  have e1 : n 1 * sigArbDress h g 1 = n 1 := by
    rw [sigArbDress_ne (by rw [sqVal_one]; omega), mul_one]
  have eU : ∀ j' : Fin h, n (sqHandleIdxU j') * sigArbDress h g (sqHandleIdxU j')
      = n (sqHandleIdxU j') := fun j' => by
    rw [sigArbDress_ne (by rw [sqHandleIdxU_val]; omega), mul_one]
  have eV : ∀ j' : Fin h, n (sqHandleIdxV j') * sigArbDress h g (sqHandleIdxV j')
      = n (sqHandleIdxV j') := fun j' => by
    rw [sigArbDress_ne (by rw [sqHandleIdxV_val]; omega), mul_one]
  have esum : (∑ j' : Fin h,
        blockPar Phi (n (sqHandleIdxU j') * sigArbDress h g (sqHandleIdxU j'))
          (n (sqHandleIdxV j') * sigArbDress h g (sqHandleIdxV j')))
      = ∑ j' : Fin h, blockPar Phi (n (sqHandleIdxU j')) (n (sqHandleIdxV j')) :=
    Finset.sum_congr rfl fun j' _ => by rw [eU j', eV j']
  rw [e0, e1, esum, blockPar_mul_left, h1] at h2
  linear_combination h2

/-- The dressing forcing on `sqArbFrame` itself: dressing the sigma slot of a relator-killing
arbitrary-dressing frame by `g` and staying relator-killing forces the pairing of `g` against the
frame's `x0` slot even. -/
theorem blockPar_sigArbDress_sqArbFrame (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R))
    (g : (DSq h : Type)) (hrel : sqRelWord (sqArbFrame h nu' j a) = 1)
    (hrel' : sqRelWord (sqArbFrame h nu' j fun i => a i * sigArbDress h g i) = 1) :
    blockPar Phi g (dsqX0 h * a 1) = 0 := by
  have hshift : (sqArbFrame h nu' j fun i => a i * sigArbDress h g i)
      = fun i => sqArbFrame h nu' j a i * sigArbDress h g i :=
    funext fun i => by rw [sqArbFrame, sqArbFrame, mul_assoc]
  rw [hshift] at hrel'
  have := blockPar_dress_eq_zero Phi (n := sqArbFrame h nu' j a) g hrel hrel'
  rwa [sqArbFrame_one] at this

end ArbFrame

/-! ## 7 Composability with the committed forcings -/

section Compose

variable {h : ℕ} {Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R)}

/-- ⚠ **`SqEichRelWord` is vacuously TRUE at `h = 0`**, so `EichRefutation.not_sqEichRelWord`
**cannot** drop its `0 < h`: the hypothesis is not incidental, it is the range on which the
statement holds.  The same argument covers `SqEichRelWordT`, `SqEichRelWordMix`,
`SqEichRelWordUV` and `SqArbRelWord`, all of which quantify over a handle. -/
theorem sqEichRelWord_handleFree : SqEichRelWord 0 := fun _ j _ _ => absurd j.isLt (by omega)

/-- ⚠ …and `SqHandleMixFixesCore 0 c` is TRUE for every `c`, by the identity automorphism: at
`h = 0` both handle clauses are empty.  So `HandleMixFixesCore.not_sqHandleMixFixesCore` and
`isUnit_of_sqHandleMixFixesCore` cannot drop their `0 < h` either. -/
theorem sqHandleMixFixesCore_handleFree (c : ℤ_[2]) : SqHandleMixFixesCore 0 c :=
  fun _ _ => ⟨ContinuousMulEquiv.refl _, fun _ => rfl, fun j => absurd j.isLt (by omega),
    fun j => absurd j.isLt (by omega), rfl, rfl⟩

/-- ⭐ **The instrument SUPPLIES the hypothesis instead.**  A continuous homomorphism with an odd
block pairing on any pair of elements refutes the Eichler word equation, with no handle count in
sight. -/
theorem not_sqEichRelWord_of_blockPar_odd (g k : (DSq h : Type))
    (hodd : blockPar Phi g k = 1) : ¬ SqEichRelWord h :=
  not_sqEichRelWord (pos_of_blockPar_odd g k hodd)

/-- …and the two-letter family likewise. -/
theorem not_sqEichRelWordUV_of_blockPar_odd (g k : (DSq h : Type))
    (hodd : blockPar Phi g k = 1) : ¬ SqEichRelWordUV h :=
  not_sqEichRelWordUV (pos_of_blockPar_odd g k hodd)

/-- …and the handle stratum. -/
theorem not_sqHandleMixFixesCore_of_blockPar_odd {c : ℤ_[2]}
    (hc : IsUnit (sqPivotExp - c)) (g k : (DSq h : Type)) (hodd : blockPar Phi g k = 1) :
    ¬ SqHandleMixFixesCore h c :=
  not_sqHandleMixFixesCore (pos_of_blockPar_odd g k hodd) hc

/-- …and the pivot unitizer. -/
theorem not_sqPivotUnitizer_of_blockPar_odd (g k : (DSq h : Type))
    (hodd : blockPar Phi g k = 1) : ¬ SqPivotUnitizer h :=
  not_sqPivotUnitizer (pos_of_blockPar_odd g k hodd)

end Compose

/-! ## 8 Axiom pins -/

section AxiomPins

#print axioms pos_of_blockRead_odd_hom
#print axioms pos_of_blockRead_odd_frame
#print axioms exists_handle_minor_odd_hom
#print axioms blockPar
#print axioms blockPar_def
#print axioms blockPar_self
#print axioms blockPar_swap
#print axioms blockPar_mul_right
#print axioms blockPar_mul_left
#print axioms blockPar_one_right
#print axioms blockPar_one_left
#print axioms blockPar_inv_left
#print axioms blockPar_inv_right
#print axioms blockPar_commP_left
#print axioms blockPar_commP_right
#print axioms blockParChar
#print axioms blockParChar_apply
#print axioms blockPar_eq_zero_of_gen_right
#print axioms blockPar_eq_zero_of_gen_left
#print axioms blockPar_relator_frame
#print axioms blockPar_relator
#print axioms selPar_d_dsqX1
#print axioms selPar_e_dsqX1
#print axioms blockPar_dsqX1_right
#print axioms blockPar_dsqX1_left
#print axioms blockPar_sigma_x0_handleFree
#print axioms blockPar_handleFree
#print axioms pos_of_blockPar_odd
#print axioms blockCexHom
#print axioms blockCexHom_gen
#print axioms blockCexHom_sigma
#print axioms blockCexHom_x0
#print axioms blockCexHom_handleU
#print axioms blockCexHom_handleV
#print axioms blockPar_blockCexHom
#print axioms blockPar_blockCexHom_handle
#print axioms blockPar_blockCexHom_sum
#print axioms blockPar_blockCexHom_crosscheck
#print axioms exists_blockPar_odd_iff_pos
#print axioms blockPar_fiveFrameHom
#print axioms blockPar_fiveFrameHom_handle
#print axioms blockPar_stageFrameHom
#print axioms blockPar_stageFrameHom_handle
#print axioms sqArbFrame_zero
#print axioms sqArbFrame_one
#print axioms pos_of_blockPar_odd_sqArbFrame
#print axioms blockPar_sqArbFrame
#print axioms exists_handle_blockPar_odd_sqArbFrame
#print axioms blockPar_dress_eq_zero
#print axioms blockPar_sigArbDress_sqArbFrame
#print axioms sqEichRelWord_handleFree
#print axioms sqHandleMixFixesCore_handleFree
#print axioms not_sqEichRelWord_of_blockPar_odd
#print axioms not_sqEichRelWordUV_of_blockPar_odd
#print axioms not_sqHandleMixFixesCore_of_blockPar_odd
#print axioms not_sqPivotUnitizer_of_blockPar_odd

end AxiomPins

end SqCore

end Dyadic

end GQ2

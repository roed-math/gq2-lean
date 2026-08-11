/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedBlockFrame

/-!
# W63-LIVE5: a class-five witness whose CORE block pairing is live, and what it does not buy

`GradedBlockFrame`'s Honesty 3 closed with a challenge.  The handle-count instrument
(`pos_of_blockPar_odd`, `exists_blockPar_odd_iff_pos`) is a genuine invariant of the topological
group `D_sq h`, and W62 computed it at two pairs at each of the two committed class-five points:
`blockPar_fiveFrameHom`, `blockPar_fiveFrameHom_handle`, `blockPar_stageFrameHom` and
`blockPar_stageFrameHom_handle` are all `0`, on the **core pair** `(sigma, x0)` and on the
**handle pair** `(u_j, v_j)`.

⚠⚠ **Honesty 3 generalised that two-pair computation into a claim about the points, and the
generalisation is FALSE.**  W63-SECOND proved by kernel computation that
`blockPar (stageFrameHom h j) (dsqX0 h) (sqGen h (sqHandleIdxU j)) = 1`, and the same at wave
60's point: the underlying readings are `blockRead stageX stageU = -5` and
`blockRead forceX forceU = -3`, both **odd**.  So the committed points are **not** block-blind.
W62's four theorems are true exactly as stated - they compute two pairs - and it is the sentence
about the *points* that does not follow.  This file does not repeat it.

⚠ No statement here is affected, and the reason is scoping rather than luck: Headline 1 requires
its **second** argument to be on the committed gauge, and `stageU` is a handle letter and is not
gauged, so the live pair `(x0, u_j)` is outside every hypothesis this file uses.

What is true, and is what this file proves and then consumes, is the sharper localised
statement: **at both committed points the CORE pair is dead, and Headline 1 says exactly why.**
That is the pair the handle-count forcing needs, and it is the only one of the three that still
exists at `h = 0` - a pairing against `u_j` cannot exclude `h = 0`, there being no `u_j` there to
pair with, so `blockPar Phi x0 u_j = 1` is necessarily free of content for the forcing.  This
file therefore builds a class-five witness whose **core** pairing is live, which is a genuine
first, and then reports honestly on how little even that buys.

## ⭐⭐⭐ Headline 1: the core-pair channel is one coordinate, and the theorem says which

`SqU6.selPar_blockRead_of_gauge`.  At **any** two slots `s`, `x` with `x` on the committed
class-two-forced gauge - `(2 : gr3R) ∣ x.d` and `selPar x.e = 1`, the two conditions
`GradedFiveForce.forceX_gauge` and `GradedFiveStageFour.stageX_gauge` both record:

```text
selPar (blockRead s x)  =  selPar s.d
```

⚠ Read the quantifier: the reduction is about a pair whose **second** argument is gauged, that
is, about a pairing against the `x0` slot.  It says nothing about pairings against a handle
letter, and the live pairs `(x0, u_j)` at the committed points are exactly such pairings.

So at every gauged class-five witness the pairing against the `x0` slot is **exactly the parity
of the first slot's `(4,5)`-entry**, and nothing else about the point can move it.  On the core
pair the first slot is the sigma mark; both committed witnesses carry `fiveSigMark = E_23`, whose
`(4,5)`-entry is `0`, and that single zero is the whole of the death of their **core** pairing
(`blockRead_fiveSigMark_gauge`).  ⭐ This is a sharper and more useful statement than "the points
are blind" would have been, and it is the reason the corrected picture is coherent: the same
theorem that kills `(sigma, x0)` at both committed points leaves `(x0, u_j)` untouched, because
`u_j` is not gauged and `stageU.d = 1` is odd.  It locates the blindness exactly.

⭐ The corollary is the answer to the cheaper question the brief asked first: **the relator's
`(4,5)`-row does not force the core channel even.**  That row reads only the `x0`- and
`x1`-slots (`SqU6.sqRelWord_d`), so it is independent of the sigma slot, which is exactly what
`sqRelWord_d_indep_sigma` records.  There are **five** abelian rows `a`-`e`, and `d` is the only
one recorded here.

⚠⚠ **That is NOT the statement that the fifteen-row standard places no condition on the sigma
slot's `(4,5)`-entry, and THIS FILE REFUTES the stronger reading.**  The higher rows do see the
sigma slot: `liveBlkCore_not_relator_handleFree` shows that with `m 0 = liveBlkSig`, whose `d` is
`1`, and `m 1 = stageX`, **no** `h = 0` marking kills the relator at all, and it proves that
through `SqU6.pos_of_blockRead_odd`, which reads the `(4,6)`-row.  So the standard does constrain
the sigma slot's `(4,5)`-entry.  What is true is that at `h >= 1` the handle block absorbs an odd
core reading, and that is what the witness of section 2 exhibits.

⭐ It also says which of the two obvious repairs of the **core** pair is available.  Wave 59's
live counterexample gets its odd core reading the other way round: `blindCexS` has `d = 0` and
`e = 1`, and the reading is live because `blindCexX` has an **odd** `(4,5)`-entry.  ⚠ **A witness
on the committed gauge cannot copy that**, because the gauge forces the `x0` slot's
`(4,5)`-column even; the evidence is `stageX_gauge` and `forceX_gauge`, two `decide` facts about
the two committed letters, and nothing here rules the repair out for a class-five witness off
that gauge.  So on the gauge the sigma slot is the only slot left to move, and moving it by
`E_45` is the whole of the construction below.

## ⭐⭐⭐ Headline 2: the witness, and it moves exactly that one coordinate

`liveBlkWit h j v = fiveTuple gr3R h j (liveBlkSig * v) stageX liveBlkY liveBlkU liveBlkV` with

```text
liveBlkSig = E_23 * E_45 = <b = 1, d = 1>        (the committed sigma mark, times E_45)
stageX     = <a = 2, e = 5>                      (the committed x0 slot, UNCHANGED)
liveBlkY   = <e = 2, f = 5, h = 5, l = 5, n = 7, o = 3>
liveBlkU   = <c = 2, d = 1>
liveBlkV   = <c = 2, e = 3, j = 5>
```

It meets the whole standard of `GradedFiveStageFour.stageWit`, at every handle count and every
handle: the fifteen rows die undressed (`sqRelWord_liveBlkWit_triv`); the `a0 = a1` dressing
leaves the **purely central, odd** class-five residue `1` (`sqRelWord_liveBlkWit_diag`), so the
separation is class-five and both `U_5`-quotients are blind to it
(`liveBlkWit_class_four_blind`); every letter has an even `(1,2)`- and an even `(3,4)`-column,
which is the stage-four soundness input (`liveBlkImage_le_stageN1`), so the stage-four exclusion
goes through verbatim (`sqRelWord_liveBlkWit_diag_ne_one`, and
`sqRelWord_liveBlkFrame_diag_ne_one_sharp`, ⚠ which is unconditional in its **dressing**
quantifier but carries the two row hypotheses `hu` and `hv`, as the pivot-anchor bullet below
discloses); the handle block is live and live in the class-four row (`commP_liveBlkUV_live`); and
the point sits on the sharp class-five line (`liveBlkWit_fiveOrth`).

⭐ And the block pairing is `1` on the **core** pair *and* on the live handle pair
(`blockPar_liveBlkHom`, `blockPar_liveBlkHom_handle`), so
`GradedBlockFrame.blockPar_relator_frame` has content on both sides at it and
`blockPar_liveBlkHom_crosscheck` checks them independently.  ⚠ **The first of those two is the
one that is new**, and it is what the composite of Headline 3 consumes: both committed points
have live pairs (W63-SECOND), but at both of them the live pairs known to the tree pair the `x0`
slot against a **handle** generator, and no such pair can exclude `h = 0`.  This is the first
class-five witness whose **core** pairing is odd; wave 59's `blockCexHom` has an odd core pairing
and is a counterexample rather than a witness.

## ⭐⭐ Headline 3: what genuinely composes - the core pair now REQUIRES a handle

`liveBlkCore_not_relator_handleFree`.  The witness's two core slots `(liveBlkSig, stageX)` admit
a relator-killing marking at **every** `h >= 1` and every handle, and admit **none** at `h = 0`,
whatever the `x1` slot.  This is `GradedBlockRead.blindCexCore_not_relator_handleFree`'s shape,
now carried by a point that also executes the class-five separation, and it is the one statement
that needs both instruments: the class-five side supplies the separation, the block side supplies
the impossibility at `h = 0`.

⚠ It is sharp, and the control is proved rather than asserted:
`sqRelWord_blindCore_handleFree` exhibits an explicit `x1` slot completing the **committed**
core pair `(fiveSigMark, stageX)` at `h = 0`.  So `stageWit`'s core slots do **not** require a
handle, and the block instrument is not merely silent about them - the underlying obstruction
genuinely fails there.  ⚠ `sqRelWord_blindCore_handleFree_bit` adds that the `a0 = a1` dressing
of that `h = 0` completion leaves the class-five residue `0`: the separation dies at `h = 0`
there for a reason the block channel does not see.

## ⚠ Headline 4: THE HONEST ANSWER - the class-five stack cannot consume the live point

The brief asked what the class-five stack gains once a live point exists.  Ruthlessly: **beyond
Headline 3 it gains nothing at all**, and the first two theorems below say so outright.  ⚠ The
third does not: it is about the handle block's `(4,6)`-parity rather than about the class-five
selection bit, and the bullet says so.

* ⚠ `liveBlkHom_pos_free`: the instrument's conclusion `0 < h` is **free** at the point.  Every
  class-five statement of this lane is indexed by a handle `j : Fin h`, so `0 < h` is available
  from `j` before any pairing is consulted.  This is `GradedBlockFrame`'s Honesty 1 in its
  sharpest form: the forcing fires, and its output was already in the context.
* ⚠ `exists_handle_minor_odd_liveBlkHom_free`: the sharper handle-**selection** form names a
  handle whose letters are independent mod `2`, and the handle it names is `j` itself
  (`liveBlkUV_minor_odd`), which is again already in the context.
* ⚠ `liveBlkWit_bit_eq_core`: at the undressed marking the **handle block's `(4,6)`-parity** is a
  functional of the **two** core slots `m 0` and `m 1`, by wave 61's
  `SqU6.selPar_handleWord_i_of_relator` collapse.
  ⚠⚠ **That quantity is not the class-five selection bit**, and the two differ at this very
  point.  In this file the bit is `selPar (sqRelWord ...).o`: `liveBlkWit_bit_separates` gives it
  the value `0` at `liveBlkWit h j 1`, where `liveBlkWit_bit_eq_core_value` gives the handle
  block's parity `1`.  So this theorem does **not** license "a live block channel cannot add a
  datum to the bit even in principle".  To retire the route on that ground one would have to
  prove the corresponding collapse for `selPar (sqRelWord ...).o` itself; that is not proved
  here, and the retirement rests on the first two bullets.

And by `GradedBlockFrame`'s Headline 4 the supplied datum is **equivalent** to `0 < h`
(`exists_blockPar_odd_iff_pos`), so no committed statement drops a hypothesis by consuming it.
⚠ **Do not report this file as letting anything drop `0 < h`.**

⭐ **W63-SECOND's correction strengthens this retirement rather than weakening it**, and the
check is worth stating because it is doctrine rule iii applied to this file's own composite.  All
three theorems above are about the **content of the datum**, not about which pair carries it: the
first says `0 < h` was already in the context, the second says the handle named was already
named, the third says the handle block's `(4,6)`-parity is a functional of the two core slots.
None of them depends on which pairs are live, so none of them is disturbed by learning that other
pairs were live all along.  What the correction adds is that the committed points could
**already** produce `0 < h` from the block instrument, at `(x0, u_j)` - and vacuously, since that
pair does not exist at `h = 0`.  So the route was doubly empty: the datum was already available
at the old points, and it was already free there.

What retires is therefore the direction, not the phenomenon.  The committed points' **core**
pairing is dead, Headline 1 says why in one coordinate, and repairing it does not open a route,
because the only thing on the other side of the door was a hypothesis the class-five statements
already have.  What survives is Headline 3, which is the one statement that needs the core pair
specifically.

## ⚠ The legality audit, REDONE, and the column that has to change

`ArbFrames` asks the dressings of `sqArbFrame` to lie in `ker lambda ∩ ker nu'`.  The
`x0`-dressing is `nu'`-trivial and **not** `lambda`-trivial exactly as before
(`nuLam_sigArbDress_x0_ne_one`, imported: it is a statement about `D_sq h`).  The obstruction
argument is again different, and again recorded here rather than formalised.  Write
`(a_s, a_0, a_1, a_U, a_V)` for the generator exponents.  The abelian columns of `Phi` are
characters, so at this point

```text
(Phi g).a = 2 a_0        (Phi g).b = a_s        (Phi g).c = 2 (a_U + a_V)
(Phi g).d = a_s + a_U    (Phi g).e = 5 a_0 + 2 a_1 + 3 a_V
```

while `lambda g = c a_s + a_0 + 2 a_1` with `c = sqPivotExp` a unit and `nu' g = a_s` at the
cleared row.  Legality forces `a_s = 0` and `a_0 + 2 a_1 = 0`, so `a_0` is **even**, so
`(Phi g).a = 2 a_0` is `0` or `4` and never `stageX.a = 2`.  So no legal dressing has
`Phi g = stageX`.  ⚠ The route is neither wave 60's nor wave 61's: there the obstruction was
read off the fifth abelian column, and here that column is reachable (`3 * 7 = 5`); it is the
**first** abelian column that closes the door.  The measurement is
`scripts/w63_live5/results/verify_live5.txt` section 6.

## ⚠ What this file does NOT do

* The `gamma_2`-level exclusion, and the sharp stage-four line of `GradedStageNecessity`: the
  forcing here is stated against `stageN3` exactly as `GradedFiveStageFour`'s is, and
  `GradedStageSharp`'s migration onto `StageCentral` is not repeated at this point.
* The class-four-blind legal escape dressing (`GradedStageFrame.stageLegalDress`) is not
  recomputed here; the escape census would have to be redone at the new sigma mark.
* The pivot anchor is not recomputed either.  Its **inputs** are inherited, not assumed: the
  `x0` slot is literally the committed `stageX`, so `GradedFiveStageFour.stageX_flat` and
  `GradedStageFrame.stageX_zpowZtwo` apply unchanged, and only the closed form of
  `Phi (sqPivot h)` moves, by the single entry `d = 1`.  Recording it would pin the census axiom
  `sqPivotExp`, and nothing here needs it.
  ⚠ **The consequence that is therefore NOT transported** is
  `GradedStageFrame.stageFrameHom_sqArbBase_handleU_ne` and its `V`-side twin: at the committed
  point those prove the frame identification **fails** at a row bumping the selected handle, so
  the two hypotheses `hu`, `hv` are forced rather than chosen.  This file carries `hu` and `hv`
  in every frame statement exactly as `GradedStageFrame` does, but does not prove they are
  forced at the new point.  They are expected to be, by the same argument and the same
  non-trivial pivot image; that is a claim about a proof not run, and it is flagged as such.

## PROVED versus MEASURED

**PROVED** (this file, no `sorry`, no new axiom, no `native_decide`; every `decide` is on
`ZMod 8` or `ZMod 2`): everything named in **Headlines 1-4**, at every handle count and every
handle, for an arbitrary continuous `nu'` cleared at the selected handle, and for every
continuous homomorphism where the statement quantifies over one.

⚠ **The legality audit above is deliberately NOT in that list.**  It says in its own words that
it is "recorded here rather than formalised", and it reappears as a MEASURED row below.  Nor are
the two expectations flagged in the pivot-anchor bullet: that `hu` and `hv` are forced at the new
point is a claim about a proof not run.

**MEASURED** (`scripts/w63_live5/`, certified output in `results/verify_live5.txt`; **50** named
checks, **0** failures, on the independently certified `U_6(Z/8)` of
`scripts/w59_blind5/u6lib.py` through `scripts/w61_block/blocklib.py`, re-certified against
honest `6 x 6` matrix arithmetic in section 0 before any measurement is taken):

| measurement | scale | result |
|---|---|---|
| the witness standard, entry by entry, and its calibration at `stageWit` / `fiveWit` | `12` entries | all hold; `fiveWit` fails exactly the stage-four column |
| ⚠ the committed points: core pair and handle pair even, but `(x0, u_j)` **odd** | `2` points | W63-SECOND's correction, re-measured here |
| the relator and the residue, at every handle count and handle | `h = 1..5` | `1` and `liftO 1` |
| no `h = 0` completion of the live core pair | `200000` random `x1` slots + `400` layered solves | `0` completions, all failing at row `(4,6)` |
| an odd handle minor never completes at the even-`(4,5)` sigma slot | `3000` letter pairs | `0` completions |
| the block reading is unmoved by `gamma_2`-dressings, with a live control | `2000` + `2000` | `0` moves, `1725` control moves |
| the legality obstruction on the first abelian column | exhaustive over even `a_0` | no legal dressing reaches `stageX` |
| the gauge reduction, **exhaustive** on `ZMod 8` | `1024` gauged pairs | `0` failures |
| the relator's abelian rows do not see the sigma slot | `4000` sigma pairs, `5` rows each | `0` mismatches |
| the search that produced the point | `24576` letter pairs, weight-ordered | minimum `(U, V, x1)` weight `11`, whole point `15` |

⚠ **MEASURED and NOT proved anywhere**: that no gauged `h = 0` marking at all admits the
class-five separation.  `scripts/w63_live5/results/h0_sweep.txt`: `200000` random gauged
triples produce `6277` relator-killing `h = 0` markings, `994` of them with a purely central
`a0 = a1` residue, and **`0`** with an odd one.  This file proves the statement only for the two
named core pairs, and for the live one only; ⚠ and the block instrument cannot settle the
general question, because at a core pair with an even reading its hypothesis is false and
`sqRelWord_blindCore_handleFree` shows the conclusion is too.  ⚠ Nor do the live pairs
W63-SECOND found at the committed points help: they pair against a handle generator, so they
exclude nothing at `h = 0`.  It is the obvious next question and it is open.

## Contents

* **1** ⭐⭐⭐ the gauge reduction: the block channel IS the sigma slot's `(4,5)`-parity;
* **2** the live point, and the fifteen-row standard;
* **3** the stage-four soundness inputs, and the exclusion at the tuple level;
* **4** the hom, the frame identification, and the exclusion on `sqArbFrame`;
* **5** ⭐⭐ the block pairing at the point, and the composite that needs both instruments;
* **6** ⚠ what the class-five stack does NOT gain, in three theorems;
* **7** axiom pins.

## Axiom hygiene

All prints are **std-3** (`propext`, `Classical.choice`, `Quot.sound`) or a subset.  No census
axiom is reachable; `sqPivotExp` in particular is not, because the pivot anchor is deliberately
not recomputed here.

## Merge notes

Nothing is redefined.  `SqU6.blockRead`, `SqU6.blockRead_def`, `SqU6.pos_of_blockRead_odd`,
`SqU6.selPar_handleWord_i_of_relator`, `SqU6.exists_handle_minor_odd` come from
`GradedBlockRead`; `blockPar`, `blockPar_def`, `blockPar_relator`, `blockPar_relator_frame`,
`pos_of_blockPar_odd`, `pos_of_blockRead_odd_hom`, `exists_handle_minor_odd_hom` from
`GradedBlockFrame`; `stageX`, `stageX_gauge`, `stageN1`, `stageN3`, `mem_stageN1`,
`stageN3_isGaThree`, `stageN3_even`, `forceLcs_two_le_stageN3`, `stageImage`, `gaThreeShift`,
`gaThreeShift_l`, `gaThreeShift_o`, `gaThreeShift_isGaThree`, `gaThreeShiftO_even`,
`sqRelWord_gaThreeDress` from `GradedFiveStageFour`; `stageN1_le_forceN1` from
`GradedStageFrame`; `fiveSigMark`, `liftC6`, `forceLcs`, `conFiveDress`, `fiveTuple` (and its
slot lemmas), `sqRelWord_fiveTuple` from `GradedFiveForce`/`GradedFive`; `FiveOrth`,
`fiveOrth_of_le_forceN1` from `GradedFiveNecessity`; `SqU6.liftO`, `SqU6.liftO_o` from
`GradedFiveDefect`; `SqU6.toU5L`, `SqU6.toU5R`, `SqU6.toU5L_sqRelWord`, `SqU6.toU5R_sqRelWord`,
`sqU6Hom`, `sqU6Hom_gen`, `gr3R`, `gr3R_card`, `SqU6.mul_a`, `SqU6.mul_c`, `SqU6.one_a`,
`SqU6.one_c`, `SqU6.sqRelWord_a` from `GradedFive`; `selPar` and its laws from `GradedSelect`;
`dsq_hom_ext`, `sqGen`, `dsqSigma`, `dsqX0`, `dsqX1`, `sqRank`, `sqRelWord`, `sqRelWord_zero`,
`sqWord`, `sqHandleIdxU`, `sqHandleIdxV`, `sqVal_zero` from `Cores`; `sqArbFrame`,
`sqArbBase_of_cleared` from `ArbFrames`/`GradedFourHom`; `sigArbDress`, `sigArbDress_zero`,
`sigArbDress_ne` from `GradedFourHom`.

⚠ **Collision watch for the merge** (doctrine v).  Every new name carries the `liveBlk` prefix
except the four general lemmas `SqU6.selPar_blockRead_of_gauge`,
`SqU6.selPar_blockRead_of_gauge_zero`, `blockRead_fiveSigMark_gauge` and `blindCoreY` /
`sqRelWord_blindCore_handleFree` / `sqRelWord_blindCore_handleFree_bit`.  The prefix `liveBlk`
was chosen because `liveWit`, `liveFiveMark` and `liveFive_blockRead` are already taken
(`GradedFourTwoLive`, `GradedFive`, `GradedBlockRead`).  The name most likely to be landed
independently by `w63-second`, which is working a second block reading at a different column
pair, is `SqU6.selPar_blockRead_of_gauge`; if it lands one too, the two should be checked for
statement-identity and merged.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 ⭐⭐⭐ The gauge reduction -/

section GaugeReduction

/-- ⭐⭐⭐ **THE BLOCK CHANNEL OF A GAUGED WITNESS IS THE SIGMA SLOT'S `(4,5)`-PARITY.**  On the
committed class-two-forced gauge - an even `(4,5)`-column and an odd `(5,6)`-column at the `x0`
slot, which is exactly what `GradedFiveForce.forceX_gauge` and
`GradedFiveStageFour.stageX_gauge` record - the block reading collapses to one entry of the
sigma slot.  Nothing else about a class-five witness can move the channel. -/
theorem SqU6.selPar_blockRead_of_gauge {s x : SqU6 gr3R} (hxd : (2 : gr3R) ∣ x.d)
    (hxe : selPar x.e = 1) : selPar (SqU6.blockRead s x) = selPar s.d := by
  obtain ⟨t, ht⟩ := hxd
  rw [SqU6.blockRead, selPar_sub, selPar_mul, selPar_mul, hxe, mul_one, ht, selPar_two_mul,
    mul_zero, sub_zero]

/-- …so a slot with an even `(4,5)`-entry pairs EVENLY against every gauged slot.  ⚠ This is a
statement about pairings whose second argument is gauged; it says nothing about pairings against
a handle letter. -/
theorem SqU6.selPar_blockRead_of_gauge_zero {s x : SqU6 gr3R} (hxd : (2 : gr3R) ∣ x.d)
    (hxe : selPar x.e = 1) (hsd : (2 : gr3R) ∣ s.d) : selPar (SqU6.blockRead s x) = 0 := by
  obtain ⟨t, ht⟩ := hsd
  rw [SqU6.selPar_blockRead_of_gauge hxd hxe, ht, selPar_two_mul]

/-- ⚠ **The dead CORE pairing of the two committed witnesses, explained in one line.**  Both
carry the sigma mark `fiveSigMark = E_23`, whose `(4,5)`-entry is `0`, so their pairing against
any gauged `x0` slot is dead for a structural reason and not by accident of the letters.
`blockPar_fiveFrameHom` and `blockPar_stageFrameHom` are the two instances.

⚠⚠ **This is a statement about the core pair only, and it must not be read as one about the
points.**  W63-SECOND proved `blockPar Phi (dsqX0 h) (sqGen h (sqHandleIdxU j)) = 1` at both
committed points, so neither point is block-blind.  There is no tension: the hypothesis here
gauges the **second** argument, and a handle letter is not gauged - `stageU.d = 1` is odd, which
is precisely why that pair is live while this one is dead. -/
theorem blockRead_fiveSigMark_gauge {x : SqU6 gr3R} (hxd : (2 : gr3R) ∣ x.d)
    (hxe : selPar x.e = 1) : selPar (SqU6.blockRead (fiveSigMark gr3R) x) = 0 :=
  SqU6.selPar_blockRead_of_gauge_zero hxd hxe ⟨0, by decide⟩

/-- ⭐ **…and the relator's `(4,5)`-ROW does not force it.**  That row reads only the `x0`- and
`x1`-slots (`SqU6.sqRelWord_d`), so it is independent of the sigma slot.  It is one of the five
abelian rows `a`-`e` and the only one recorded here.

⚠⚠ **This does NOT say that the fifteen-row standard places no condition on the sigma slot's
`(4,5)`-entry, and this file refutes that stronger claim.**  The higher rows do see the sigma
slot: `liveBlkCore_not_relator_handleFree` excludes **every** `h = 0` relator-killing marking
whose core slots are `(liveBlkSig, stageX)`, and `liveBlkSig.d = 1` is odd.  What is true is that
at `h >= 1` the handle block absorbs an odd core reading. -/
theorem sqRelWord_d_indep_sigma {h : ℕ} (m m' : Fin (sqRank h) → SqU6 gr3R)
    (h1 : m 1 = m' 1) (h2 : m 2 = m' 2) : (sqRelWord m).d = (sqRelWord m').d := by
  rw [SqU6.sqRelWord_d, SqU6.sqRelWord_d, h1, h2]

end GaugeReduction

/-! ## 2 The live point -/

section Point

/-- **The live sigma mark** `E_23 * E_45 = <b = 1, d = 1>`: the committed `fiveSigMark`, moved
in the one coordinate that the block channel reads and the witness standard does not
constrain.  The `nu'`-column `b = 1` is untouched, so the row-forcing argument and the pivot
anchor of `GradedStageFrame` transfer. -/
def liveBlkSig : SqU6 gr3R := ⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- `liveBlkSig` **is** the committed sigma mark times `E_45`. -/
theorem liveBlkSig_eq : liveBlkSig = fiveSigMark gr3R * ⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0⟩ := by decide

/-- The `x1`-slot of the live point: `<e = 2, f = 5, h = 5, l = 5, n = 7, o = 3>`, the layered
solve of the fifteen rows against the live block at the moved sigma mark. -/
def liveBlkY : SqU6 gr3R := ⟨0, 0, 0, 0, 2, 5, 0, 5, 0, 0, 0, 5, 0, 7, 3⟩

/-- The `U`-letter: `<c = 2, d = 1>`.  Both columns the stage-four soundness reads are even,
and its `(4,5)`-entry is odd, which is half of the live handle minor. -/
def liveBlkU : SqU6 gr3R := ⟨0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The `V`-letter: `<c = 2, e = 3, j = 5>`.  Its `(5,6)`-entry is odd, so the handle minor
`u_45 v_56 - u_56 v_45` is odd, and its commutator with `liveBlkU` is live in the class-four
row as well. -/
def liveBlkV : SqU6 gr3R := ⟨0, 0, 2, 0, 3, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0⟩

variable {h : ℕ} {j : Fin h}

variable (h j) in
/-- **The live class-five binder point**, at every handle count and every handle, with the sigma
slot dressed by `v`.  The `x0` slot is the committed `GradedFiveStageFour.stageX`, unchanged. -/
def liveBlkWit (v : SqU6 gr3R) : Fin (sqRank h) → SqU6 gr3R :=
  fiveTuple gr3R h j (liveBlkSig * v) stageX liveBlkY liveBlkU liveBlkV

@[simp] theorem liveBlkWit_zero (v : SqU6 gr3R) : liveBlkWit h j v 0 = liveBlkSig * v := by
  rw [liveBlkWit, fiveTuple_zero]

@[simp] theorem liveBlkWit_one (v : SqU6 gr3R) : liveBlkWit h j v 1 = stageX := by
  rw [liveBlkWit, fiveTuple_one]

@[simp] theorem liveBlkWit_two (v : SqU6 gr3R) : liveBlkWit h j v 2 = liveBlkY := by
  rw [liveBlkWit, fiveTuple_two]

@[simp] theorem liveBlkWit_handleU (v : SqU6 gr3R) :
    liveBlkWit h j v (sqHandleIdxU j) = liveBlkU := by
  rw [liveBlkWit, fiveTuple_handleU]

@[simp] theorem liveBlkWit_handleV (v : SqU6 gr3R) :
    liveBlkWit h j v (sqHandleIdxV j) = liveBlkV := by
  rw [liveBlkWit, fiveTuple_handleV]

theorem liveBlkWit_handleU_ne (v : SqU6 gr3R) {j' : Fin h} (hne : j' ≠ j) :
    liveBlkWit h j v (sqHandleIdxU j') = 1 := by
  rw [liveBlkWit, fiveTuple_handleU_ne hne]

theorem liveBlkWit_handleV_ne (v : SqU6 gr3R) {j' : Fin h} (hne : j' ≠ j) :
    liveBlkWit h j v (sqHandleIdxV j') = 1 := by
  rw [liveBlkWit, fiveTuple_handleV_ne hne]

/-- **Only the sigma slot sees the dressing**, which is the one shape fact the frame
identification of section 4 consumes. -/
theorem liveBlkWit_of_ne_zero {v : SqU6 gr3R} {i : Fin (sqRank h)} (hi : (i : ℕ) ≠ 0) :
    liveBlkWit h j v i = liveBlkWit h j 1 i := by
  simp only [liveBlkWit, fiveTuple]
  rw [if_neg hi, if_neg hi]

/-- ⭐⭐ **The undressed marking kills the relator outright**: all fifteen rows vanish, at every
handle count and every handle. -/
theorem sqRelWord_liveBlkWit_triv (h : ℕ) (j : Fin h) : sqRelWord (liveBlkWit h j 1) = 1 := by
  rw [liveBlkWit, sqRelWord_fiveTuple]
  decide

/-- ⭐⭐ **The `a0 = a1` dressing leaves the ODD, PURELY CENTRAL class-five residue `1`**, at
every handle count and every handle: the fourteen lower rows die and the top row does not. -/
theorem sqRelWord_liveBlkWit_diag (h : ℕ) (j : Fin h) :
    sqRelWord (liveBlkWit h j stageX) = SqU6.liftO 1 := by
  rw [liveBlkWit, sqRelWord_fiveTuple]
  decide

/-- …and the bit really does separate the two dressings. -/
theorem liveBlkWit_bit_separates (h : ℕ) (j : Fin h) :
    selPar (sqRelWord (liveBlkWit h j 1)).o = 0
      ∧ selPar (sqRelWord (liveBlkWit h j stageX)).o = 1 := by
  refine ⟨?_, ?_⟩
  · rw [sqRelWord_liveBlkWit_triv]
    decide
  · rw [sqRelWord_liveBlkWit_diag, SqU6.liftO_o]
    decide

/-- ⭐⭐ **The whole committed class-`<= 4` machinery cannot separate the two dressings**: the
residue is central, so both `U_5`-quotients kill the relator at both dressings and the
separation is purely class five, exactly as at the two committed witnesses. -/
theorem liveBlkWit_class_four_blind (h : ℕ) (j : Fin h) :
    (sqRelWord (fun i => SqU6.toU5L (liveBlkWit h j 1 i)) = 1
        ∧ sqRelWord (fun i => SqU6.toU5R (liveBlkWit h j 1 i)) = 1)
      ∧ (sqRelWord (fun i => SqU6.toU5L (liveBlkWit h j stageX i)) = 1
        ∧ sqRelWord (fun i => SqU6.toU5R (liveBlkWit h j stageX i)) = 1) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [← SqU6.toU5L_sqRelWord, sqRelWord_liveBlkWit_triv, map_one]
  · rw [← SqU6.toU5R_sqRelWord, sqRelWord_liveBlkWit_triv, map_one]
  · rw [← SqU6.toU5L_sqRelWord, sqRelWord_liveBlkWit_diag]
    decide
  · rw [← SqU6.toU5R_sqRelWord, sqRelWord_liveBlkWit_diag]
    decide

/-- ⭐ **The point sits on the committed class-two-forced gauge**, with the same single datum
escaping it as at both committed points: the `x0`-slot's fifth abelian column is odd.  The `x0`
slot is `stageX` itself, so this is `GradedFiveStageFour.stageX_gauge` for the two core slots
and one extra line for the `x1` slot. -/
theorem liveBlkWit_gauge :
    stageX.a = 2 * 1 ∧ stageX.c = 2 * 0 ∧ stageX.d = 2 * 0 ∧ stageX.f = 2 * 0
      ∧ stageX.g = 2 * 0 ∧ liveBlkY.a = 2 * 0 ∧ liveBlkY.c = 2 * 0 ∧ liveBlkY.d = 2 * 0
      ∧ stageX.b = 0 ∧ selPar stageX.e = 1 := by decide

/-- The handle block of the point is **live**, live in the class-four row `x_{15}` (which is
what the two committed points record), and - new here - live in the class-two row `x_{46}`,
which is the block channel. -/
theorem commP_liveBlkUV_live : commP liveBlkU liveBlkV ≠ 1
    ∧ selPar (commP liveBlkU liveBlkV).m = 1 ∧ selPar (commP liveBlkU liveBlkV).i = 1 := by
  refine ⟨?_, by decide, by decide⟩
  decide

end Point

/-! ## 3 The block channel at the point, and the stage-four soundness -/

section Channel

/-- ⭐⭐⭐ **THE BLOCK READING AT THE LIVE POINT IS ODD.**  `blockRead liveBlkSig stageX = 5`. -/
theorem blockRead_liveBlkSig_stageX : SqU6.blockRead liveBlkSig stageX = 5 := by decide

theorem blockRead_liveBlkSig_stageX_odd :
    selPar (SqU6.blockRead liveBlkSig stageX) = 1 := by decide

/-- …and it is the gauge reduction firing: the reading is the sigma slot's `(4,5)`-parity. -/
theorem blockRead_liveBlkSig_stageX_gauge :
    selPar (SqU6.blockRead liveBlkSig stageX) = selPar liveBlkSig.d :=
  SqU6.selPar_blockRead_of_gauge ⟨0, by decide⟩ (by decide)

/-- ⭐ **The handle minor is odd**, so the symplectic identity has content at the point on both
sides. -/
theorem liveBlkUV_minor_odd :
    selPar (liveBlkU.d * liveBlkV.e - liveBlkV.d * liveBlkU.e) = 1 := by decide

end Channel

section Soundness

variable {h : ℕ} {j : Fin h}

/-- Every slot of a one-handle-live tuple is one of its five letters or trivial. -/
private theorem liveTuple_cases {R : Type} [CommRing R] {hh : ℕ} {jj : Fin hh}
    (S X Y U V : SqU6 R) (i : Fin (sqRank hh)) :
    fiveTuple R hh jj S X Y U V i = S ∨ fiveTuple R hh jj S X Y U V i = X
      ∨ fiveTuple R hh jj S X Y U V i = Y ∨ fiveTuple R hh jj S X Y U V i = U
      ∨ fiveTuple R hh jj S X Y U V i = V ∨ fiveTuple R hh jj S X Y U V i = 1 := by
  simp only [fiveTuple]
  split_ifs <;> tauto

variable (h j) in
/-- The subgroup generated by the point's slots, at the dressing `v`. -/
def liveBlkImage (v : SqU6 gr3R) : Subgroup (SqU6 gr3R) :=
  Subgroup.closure (Set.range (liveBlkWit h j v))

/-- ⭐ **The point's letters all lie in `M_1`**, the only input the stage-four chain needs.
Every letter has an even `(1,2)`- and an even `(3,4)`-column, exactly as at
`GradedFiveStageFour.stageWit`. -/
theorem liveBlkImage_le_stageN1 {v : SqU6 gr3R} (hv : (2 : gr3R) ∣ v.a ∧ (2 : gr3R) ∣ v.c) :
    liveBlkImage h j v ≤ stageN1 := by
  obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := hv
  rw [liveBlkImage, Subgroup.closure_le]
  rintro z ⟨i, rfl⟩
  simp only [liveBlkWit]
  rcases liveTuple_cases (liveBlkSig * v) stageX liveBlkY liveBlkU liveBlkV i with
    h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1, SetLike.mem_coe, mem_stageN1]
  · exact ⟨⟨s, by rw [SqU6.mul_a, hs]; simp [liveBlkSig]⟩,
      ⟨t, by rw [SqU6.mul_c, ht]; simp [liveBlkSig]⟩⟩
  · exact ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
  · exact ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩
  · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩
  · exact ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩

/-- Every slot of the marking has an even `(1,2)`-column, which is what
`GradedFiveStageFour.gaThreeShiftO_even` reads. -/
theorem liveBlkWit_a_even {v : SqU6 gr3R} (hv : (2 : gr3R) ∣ v.a) (i : Fin (sqRank h)) :
    (2 : gr3R) ∣ (liveBlkWit h j v i).a := by
  obtain ⟨s, hs⟩ := hv
  simp only [liveBlkWit]
  rcases liveTuple_cases (liveBlkSig * v) stageX liveBlkY liveBlkU liveBlkV i with
    h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1]
  · exact ⟨s, by rw [SqU6.mul_a, hs]; simp [liveBlkSig]⟩
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨0, by decide⟩

/-- ⭐ **The point satisfies the SHARP class-five invariant** of `GradedFiveNecessity`, at every
dressing whose two columns are even: the stage-four hypothesis is strictly stronger than the
stage-five one, exactly as at the committed point. -/
theorem liveBlkWit_fiveOrth {v : SqU6 gr3R} (hv : (2 : gr3R) ∣ v.a ∧ (2 : gr3R) ∣ v.c) :
    FiveOrth (liveBlkWit h j v) j :=
  fiveOrth_of_le_forceN1 (le_trans (liveBlkImage_le_stageN1 hv) stageN1_le_forceN1)

/-- ⭐⭐ **The stage-four selection bit is forced even at the live point.**  ⚠ At a sigma
parameter `v` **whose `(1,2)`- and `(3,4)`-columns are even** (`2 ∣ v.a` and `2 ∣ v.c`, the
hypothesis `hv`): if the marking is killed by **any** achievable five-slot stage-four refinement
then it leaves an even class-five residue.  This is `GradedFiveStageFour.stageWit_sigma_forced`
verbatim at the new point, restriction on `v` included: the argument reads only the even
`(1,2)`-columns, which the new letters have. -/
theorem liveBlkWit_sigma_forced {v : SqU6 gr3R} {z : Fin (sqRank h) → SqU6 gr3R}
    (hv : (2 : gr3R) ∣ v.a ∧ (2 : gr3R) ∣ v.c)
    (hz : ∀ i, z i ∈ forceLcs (liveBlkImage h j v) 2)
    (hkill : sqRelWord (conFiveDress (liveBlkWit h j v) z) = 1) :
    selPar (sqRelWord (liveBlkWit h j v)).o = 0 := by
  have hle := forceLcs_two_le_stageN3 (liveBlkImage_le_stageN1 (h := h) (j := j) hv)
  have hga : ∀ i, (z i).IsGaThree := fun i => stageN3_isGaThree (hle (hz i))
  have heven : ∀ i, (2 : gr3R) ∣ (z i).j ∧ (2 : gr3R) ∣ (z i).l ∧ (2 : gr3R) ∣ (z i).m :=
    fun i => stageN3_even (hle (hz i))
  rw [sqRelWord_gaThreeDress hga] at hkill
  have ho := congrArg SqU6.o hkill
  rw [SqU6.mul_o, SqU6.one_o] at ho
  have hsh := gaThreeShift_isGaThree (h := h) (m := liveBlkWit h j v) (z := z)
  obtain ⟨ca, hca⟩ : (2 : gr3R) ∣ (sqRelWord (liveBlkWit h j v)).a :=
    ⟨-2 * (liveBlkWit h j v 1).a + (liveBlkWit h j v 2).a, by rw [SqU6.sqRelWord_a]; ring⟩
  obtain ⟨cl, hcl⟩ : (2 : gr3R) ∣ (gaThreeShift h (liveBlkWit h j v) z).l := by
    rw [gaThreeShift_l]
    exact ⟨-2 * (z 1).l + (z 2).l, by ring⟩
  obtain ⟨co, hco⟩ : (2 : gr3R) ∣ (gaThreeShift h (liveBlkWit h j v) z).o := by
    rw [gaThreeShift_o]
    exact gaThreeShiftO_even (liveBlkWit_a_even hv.1) heven
  rw [hca, hcl, hco, hsh.2.2.2.2.1, hsh.2.2.2.2.2.2.2.2] at ho
  have hfin : (sqRelWord (liveBlkWit h j v)).o
      = 2 * (-(co + ca * (gaThreeShift h (liveBlkWit h j v) z).n
        + (sqRelWord (liveBlkWit h j v)).f * cl)) := by
    linear_combination ho
  rw [hfin, selPar_two_mul]

/-- ⭐⭐ **The sharp form**, with the achievability convention spent: the refinement is asked
only to be `gamma_3`-shaped with `j`, `l` and `m` even. -/
theorem liveBlkWit_sigma_forced_sharp {v : SqU6 gr3R} {z : Fin (sqRank h) → SqU6 gr3R}
    (hv : (2 : gr3R) ∣ v.a) (hz : ∀ i, z i ∈ stageN3)
    (hkill : sqRelWord (conFiveDress (liveBlkWit h j v) z) = 1) :
    selPar (sqRelWord (liveBlkWit h j v)).o = 0 := by
  have hga : ∀ i, (z i).IsGaThree := fun i => stageN3_isGaThree (hz i)
  have heven : ∀ i, (2 : gr3R) ∣ (z i).j ∧ (2 : gr3R) ∣ (z i).l ∧ (2 : gr3R) ∣ (z i).m :=
    fun i => stageN3_even (hz i)
  rw [sqRelWord_gaThreeDress hga] at hkill
  have ho := congrArg SqU6.o hkill
  rw [SqU6.mul_o, SqU6.one_o] at ho
  have hsh := gaThreeShift_isGaThree (h := h) (m := liveBlkWit h j v) (z := z)
  obtain ⟨ca, hca⟩ : (2 : gr3R) ∣ (sqRelWord (liveBlkWit h j v)).a :=
    ⟨-2 * (liveBlkWit h j v 1).a + (liveBlkWit h j v 2).a, by rw [SqU6.sqRelWord_a]; ring⟩
  obtain ⟨cl, hcl⟩ : (2 : gr3R) ∣ (gaThreeShift h (liveBlkWit h j v) z).l := by
    rw [gaThreeShift_l]
    exact ⟨-2 * (z 1).l + (z 2).l, by ring⟩
  obtain ⟨co, hco⟩ : (2 : gr3R) ∣ (gaThreeShift h (liveBlkWit h j v) z).o := by
    rw [gaThreeShift_o]
    exact gaThreeShiftO_even (liveBlkWit_a_even hv) heven
  rw [hca, hcl, hco, hsh.2.2.2.2.1, hsh.2.2.2.2.2.2.2.2] at ho
  have hfin : (sqRelWord (liveBlkWit h j v)).o
      = 2 * (-(co + ca * (gaThreeShift h (liveBlkWit h j v) z).n
        + (sqRelWord (liveBlkWit h j v)).f * cl)) := by
    linear_combination ho
  rw [hfin, selPar_two_mul]

/-- ⭐⭐⭐ **THE UNCONDITIONAL EXCLUSION AT THE LIVE POINT.**  No achievable five-slot
`gamma_3`-dressing kills the `a0 = a1`-dressed marking, at any handle count and any handle. -/
theorem sqRelWord_liveBlkWit_diag_ne_one {z : Fin (sqRank h) → SqU6 gr3R}
    (hz : ∀ i, z i ∈ forceLcs (liveBlkImage h j stageX) 2) :
    sqRelWord (conFiveDress (liveBlkWit h j stageX) z) ≠ 1 := by
  intro hc
  have hp := liveBlkWit_sigma_forced ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩ hz hc
  rw [sqRelWord_liveBlkWit_diag, SqU6.liftO_o] at hp
  exact absurd hp (by decide)

/-- …and against the declared stage-four class, which consumes no achievability convention. -/
theorem sqRelWord_liveBlkWit_diag_ne_one_sharp {z : Fin (sqRank h) → SqU6 gr3R}
    (hz : ∀ i, z i ∈ stageN3) :
    sqRelWord (conFiveDress (liveBlkWit h j stageX) z) ≠ 1 := by
  intro hc
  have hp := liveBlkWit_sigma_forced_sharp ⟨1, by decide⟩ hz hc
  rw [sqRelWord_liveBlkWit_diag, SqU6.liftO_o] at hp
  exact absurd hp (by decide)

end Soundness

/-! ## 4 The hom, the frame, and the exclusion on `sqArbFrame` -/

section Hom

variable {h : ℕ} {j : Fin h}

variable (h j) in
/-- ⭐⭐ **The live class-five binder hom.**  The point kills the relator at every handle count
and every handle, so the committed class-five lift turns it into an honest continuous
homomorphism `D_sq h → U_6(ℤ/8)`. -/
noncomputable def liveBlkHom : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R) :=
  sqU6Hom gr3R_card h (liveBlkWit h j 1) (sqRelWord_liveBlkWit_triv h j)

@[simp] theorem liveBlkHom_gen (i : Fin (sqRank h)) :
    liveBlkHom h j (sqGen h i) = liveBlkWit h j 1 i := sqU6Hom_gen _ _ _ i

@[simp] theorem liveBlkHom_sigma : liveBlkHom h j (dsqSigma h) = liveBlkSig := by
  rw [dsqSigma, liveBlkHom_gen, liveBlkWit_zero, mul_one]

@[simp] theorem liveBlkHom_x0 : liveBlkHom h j (dsqX0 h) = stageX := by
  rw [dsqX0, liveBlkHom_gen, liveBlkWit_one]

@[simp] theorem liveBlkHom_x1 : liveBlkHom h j (dsqX1 h) = liveBlkY := by
  rw [dsqX1, liveBlkHom_gen, liveBlkWit_two]

@[simp] theorem liveBlkHom_handleU :
    liveBlkHom h j (sqGen h (sqHandleIdxU j)) = liveBlkU := by
  rw [liveBlkHom_gen, liveBlkWit_handleU]

@[simp] theorem liveBlkHom_handleV :
    liveBlkHom h j (sqGen h (sqHandleIdxV j)) = liveBlkV := by
  rw [liveBlkHom_gen, liveBlkWit_handleV]

/-- The `(1,2)`- and `(3,4)`-columns of the hom are characters vanishing mod `2` on every
generator, hence even everywhere.  This is the short route to
`GradedStageFrame.stageFrameHom_mem_stageN1`: no closure argument is needed, because both
columns are additive. -/
private noncomputable def liveBlkAChar (c : SqU6 gr3R → gr3R)
    (hone : c 1 = 0) (hmul : ∀ p q : SqU6 gr3R, c (p * q) = c p + c q) :
    ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2)) where
  toFun g := ofAdd (selPar (c (liveBlkHom h j g)))
  map_one' := by rw [map_one, hone, selPar_zero]; rfl
  map_mul' p q := by rw [map_mul, hmul, selPar_add, ofAdd_add]
  continuous_toFun :=
    (continuous_of_discreteTopology (f := fun p : SqU6 gr3R => ofAdd (selPar (c p)))).comp
      (liveBlkHom h j).continuous_toFun

private noncomputable def liveBlkTrivChar (hh : ℕ) :
    ContinuousMonoidHom (DSq hh : Type) (Multiplicative (ZMod 2)) where
  toFun _ := ofAdd (0 : ZMod 2)
  map_one' := rfl
  map_mul' _ _ := by rw [← ofAdd_add, add_zero]
  continuous_toFun := continuous_const

private theorem liveBlkHom_col_even (c : SqU6 gr3R → gr3R) (hone : c 1 = 0)
    (hmul : ∀ p q : SqU6 gr3R, c (p * q) = c p + c q)
    (hgen : ∀ i, selPar (c (liveBlkWit h j 1 i)) = 0) (g : (DSq h : Type)) :
    (2 : gr3R) ∣ c (liveBlkHom h j g) := by
  have hext : liveBlkAChar (h := h) (j := j) c hone hmul = liveBlkTrivChar h :=
    dsq_hom_ext (liveBlkAChar (h := h) (j := j) c hone hmul) (liveBlkTrivChar h) fun i => by
      show ofAdd (selPar (c (liveBlkHom h j (sqGen h i)))) = ofAdd (0 : ZMod 2)
      rw [liveBlkHom_gen, hgen i]
  have hg : ofAdd (selPar (c (liveBlkHom h j g))) = ofAdd (0 : ZMod 2) :=
    DFunLike.congr_fun hext g
  exact (selPar_eq_zero_iff _).mp (Multiplicative.ofAdd.injective hg)

/-- ⭐⭐ **Both soundness columns are automatic at the live point**: every value of the hom has
an even `(1,2)`- and an even `(3,4)`-column, with no row hypothesis and no condition on `g`. -/
theorem liveBlkHom_columns_even (g : (DSq h : Type)) :
    (2 : gr3R) ∣ (liveBlkHom h j g).a ∧ (2 : gr3R) ∣ (liveBlkHom h j g).c := by
  refine ⟨liveBlkHom_col_even SqU6.a (SqU6.one_a) (fun p q => SqU6.mul_a p q) (fun i => ?_) g,
    liveBlkHom_col_even SqU6.c (SqU6.one_c) (fun p q => SqU6.mul_c p q) (fun i => ?_) g⟩
  · obtain ⟨t, ht⟩ := liveBlkWit_a_even (v := (1 : SqU6 gr3R)) ⟨0, by decide⟩ i
    rw [ht, selPar_two_mul]
  · obtain ⟨t, ht⟩ : (2 : gr3R) ∣ (liveBlkWit h j 1 i).c :=
      mem_stageN1.mp (liveBlkImage_le_stageN1 (v := (1 : SqU6 gr3R))
        ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ (Subgroup.subset_closure ⟨i, rfl⟩)) |>.2
    rw [ht, selPar_two_mul]

theorem liveBlkHom_mem_stageN1 (g : (DSq h : Type)) : liveBlkHom h j g ∈ stageN1 :=
  mem_stageN1.mpr (liveBlkHom_columns_even g)

/-- ⭐ **The achievable stage-four lattice at any dressed image point is sound.** -/
theorem forceLcs_liveBlkHom_le_stageN3 (g : (DSq h : Type)) :
    forceLcs (liveBlkImage h j (liveBlkHom h j g)) 2 ≤ stageN3 :=
  forceLcs_two_le_stageN3 (liveBlkImage_le_stageN1 (liveBlkHom_columns_even g))

variable {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- ⭐⭐ **The frame identification at the live point.**  At a row cleared at the selected
handle, the live binder hom sends the arbitrary-dressing frame with a sigma-only dressing `g` to
exactly the live binder point at the dressing value `liveBlkHom h j g`.  The proof consumes only
`liveBlkWit_zero` and `liveBlkWit_of_ne_zero`, that is, only the `fiveTuple` shape, so the change
of sigma mark costs it nothing. -/
theorem liveBlkHom_sqArbFrame (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) (g : (DSq h : Type)) :
    (fun i => liveBlkHom h j (sqArbFrame h nu' j (sigArbDress h g) i))
      = liveBlkWit h j (liveBlkHom h j g) := by
  funext i
  by_cases h0 : (i : ℕ) = 0
  · have hi : i = 0 := Fin.val_injective (by rw [h0, sqVal_zero])
    subst hi
    rw [sqArbFrame, sqArbBase_of_cleared hu hv, sigArbDress_zero, map_mul, liveBlkHom_gen,
      liveBlkWit_zero, liveBlkWit_zero, mul_one]
  · rw [sqArbFrame, sqArbBase_of_cleared hu hv, sigArbDress_ne h0, mul_one, liveBlkHom_gen,
      liveBlkWit_of_ne_zero (v := liveBlkHom h j g) h0]

/-- ⭐ **The undressed frame kills the relator outright** at the live binder hom. -/
theorem sqRelWord_liveBlkFrame_triv (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    sqRelWord (fun i => liveBlkHom h j (sqArbFrame h nu' j (sigArbDress h 1) i)) = 1 := by
  rw [liveBlkHom_sqArbFrame hu hv, map_one]
  exact sqRelWord_liveBlkWit_triv h j

/-- ⭐⭐ **The `x0`-dressed frame leaves the ODD class-five residue `1`.** -/
theorem sqRelWord_liveBlkFrame_diag (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    sqRelWord (fun i =>
        liveBlkHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i)) = SqU6.liftO 1 := by
  rw [liveBlkHom_sqArbFrame hu hv, liveBlkHom_x0]
  exact sqRelWord_liveBlkWit_diag h j

/-- ⭐⭐⭐ **THE EXCLUSION ON `sqArbFrame` AT THE LIVE POINT, UNCONDITIONAL.**  No five-slot
`gamma_3`-refinement with `j`, `l` and `m` even kills the relator image of the `x0`-dressed
arbitrary-dressing frame, at any handle count, any handle, and any row cleared at the selected
handle.  This is `GradedStageFrame.sqRelWord_stageFrame_diag_ne_one_sharp` at a point where the
block channel is live. -/
theorem sqRelWord_liveBlkFrame_diag_ne_one_sharp (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1)
    {z : Fin (sqRank h) → SqU6 gr3R} (hz : ∀ i, z i ∈ stageN3) :
    sqRelWord (conFiveDress
      (fun i => liveBlkHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i)) z) ≠ 1 := by
  rw [liveBlkHom_sqArbFrame hu hv, liveBlkHom_x0]
  exact sqRelWord_liveBlkWit_diag_ne_one_sharp hz

/-- …and in the committed achievability convention. -/
theorem sqRelWord_liveBlkFrame_diag_ne_one (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1)
    {z : Fin (sqRank h) → SqU6 gr3R}
    (hz : ∀ i, z i ∈ forceLcs (liveBlkImage h j (liveBlkHom h j (dsqX0 h))) 2) :
    sqRelWord (conFiveDress
      (fun i => liveBlkHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i)) z) ≠ 1 :=
  sqRelWord_liveBlkFrame_diag_ne_one_sharp hu hv
    (fun i => forceLcs_liveBlkHom_le_stageN3 (dsqX0 h) (hz i))

/-- ⭐ **Every class-`<= 4` verdict on the frame is the same for both dressings.** -/
theorem liveBlkFrame_class_four_blind (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    (sqRelWord (fun i => SqU6.toU5L
        (liveBlkHom h j (sqArbFrame h nu' j (sigArbDress h 1) i))) = 1
      ∧ sqRelWord (fun i => SqU6.toU5R
        (liveBlkHom h j (sqArbFrame h nu' j (sigArbDress h 1) i))) = 1)
    ∧ (sqRelWord (fun i => SqU6.toU5L
        (liveBlkHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i))) = 1
      ∧ sqRelWord (fun i => SqU6.toU5R
        (liveBlkHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i))) = 1) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [← SqU6.toU5L_sqRelWord, sqRelWord_liveBlkFrame_triv hu hv, map_one]
  · rw [← SqU6.toU5R_sqRelWord, sqRelWord_liveBlkFrame_triv hu hv, map_one]
  · rw [← SqU6.toU5L_sqRelWord, sqRelWord_liveBlkFrame_diag hu hv]
    decide
  · rw [← SqU6.toU5R_sqRelWord, sqRelWord_liveBlkFrame_diag hu hv]
    decide

end Hom

/-! ## 5 ⭐⭐ The block pairing at the point, and the composite -/

section Pairing

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐⭐ **THE CORE BLOCK PAIRING IS LIVE AT A CLASS-FIVE WITNESS.**  This is the pairing
`GradedBlockFrame`'s `blockPar_fiveFrameHom` and `blockPar_stageFrameHom` compute as `0` at the
two committed witnesses, and it is the only one of the three computed pairs that can exclude
`h = 0`, both generators being core generators. -/
theorem blockPar_liveBlkHom : blockPar (liveBlkHom h j) (dsqSigma h) (dsqX0 h) = 1 := by
  rw [blockPar_def, liveBlkHom_sigma, liveBlkHom_x0]
  exact blockRead_liveBlkSig_stageX_odd

/-- ⭐⭐ …and it is live on the **handle pair** as well, so the symplectic identity
`blockPar_relator_frame` has content on both sides at the point. -/
theorem blockPar_liveBlkHom_handle :
    blockPar (liveBlkHom h j) (sqGen h (sqHandleIdxU j)) (sqGen h (sqHandleIdxV j)) = 1 := by
  rw [blockPar_def, liveBlkHom_handleU, liveBlkHom_handleV]
  decide

/-- The right-hand side of the symplectic identity, computed independently: only the live handle
contributes and it contributes `1`. -/
theorem blockPar_liveBlkHom_sum :
    (∑ j' : Fin h, blockPar (liveBlkHom h j) (sqGen h (sqHandleIdxU j'))
      (sqGen h (sqHandleIdxV j'))) = 1 := by
  rw [Finset.sum_eq_single j ?_ ?_]
  · exact blockPar_liveBlkHom_handle
  · intro j' _ hne
    simp only [blockPar_def, liveBlkHom_gen, liveBlkWit_handleU_ne _ hne,
      liveBlkWit_handleV_ne _ hne]
    decide
  · intro hcon
    exact absurd (Finset.mem_univ j) hcon

/-- ⭐ **The composite check the doctrine asks for.**  Both sides of the symplectic identity are
computed from the point rather than from the identity, and they agree. -/
theorem blockPar_liveBlkHom_crosscheck :
    blockPar (liveBlkHom h j) (dsqSigma h) (dsqX0 h)
      = ∑ j' : Fin h, blockPar (liveBlkHom h j) (sqGen h (sqHandleIdxU j'))
          (sqGen h (sqHandleIdxV j')) := by
  rw [blockPar_liveBlkHom, blockPar_liveBlkHom_sum]

/-- …and it agrees with `GradedBlockFrame.blockPar_relator`, which derives it from the relator
rather than from the point.  Wave 57's process finding, applied to this file's own composite. -/
theorem blockPar_liveBlkHom_relator_agrees :
    blockPar (liveBlkHom h j) (dsqSigma h) (dsqX0 h)
      = ∑ j' : Fin h, blockPar (liveBlkHom h j) (sqGen h (sqHandleIdxU j'))
          (sqGen h (sqHandleIdxV j')) :=
  blockPar_relator (liveBlkHom h j)

end Pairing

/-! ### The composite that needs both instruments -/

section Composite

/-- ⭐⭐⭐ **THE CORE PAIR OF THE LIVE WITNESS REQUIRES A HANDLE.**  The two core slots of the
live class-five point admit a relator-killing marking at **every** `h >= 1` and every handle
(`sqRelWord_liveBlkWit_triv`), and admit **none** at `h = 0`, whatever the `x1` slot.

This is the one statement that genuinely needs both instruments: the class-five stack supplies a
witness carrying the separation, and `SqU6.pos_of_blockRead_odd` supplies the impossibility at
`h = 0`.  Neither committed class-five witness can state it, and not for want of a live pairing:
W63-SECOND's live pairs at those points pair the `x0` slot against a **handle** generator, and
such a pair excludes nothing at `h = 0`.  It is the **core** pair that is needed and the core
pair that is dead there - see `sqRelWord_blindCore_handleFree` for the proved control. -/
theorem liveBlkCore_not_relator_handleFree (m : Fin (sqRank 0) → SqU6 gr3R)
    (h0 : m 0 = liveBlkSig) (h1 : m 1 = stageX) : sqRelWord m ≠ 1 := by
  intro hrel
  exact absurd (SqU6.pos_of_blockRead_odd hrel
    (by rw [h0, h1]; exact blockRead_liveBlkSig_stageX_odd)) (lt_irrefl 0)

/-- …in hom form: no continuous homomorphism on `D_sq 0` sends the two core generators to the
live point's core slots. -/
theorem liveBlkCore_no_hom_handleFree (Psi : ContinuousMonoidHom (DSq 0 : Type) (SqU6 gr3R))
    (h0 : Psi (dsqSigma 0) = liveBlkSig) (h1 : Psi (dsqX0 0) = stageX) : False := by
  have hodd : blockPar Psi (dsqSigma 0) (dsqX0 0) = 1 := by
    rw [blockPar_def, h0, h1]
    exact blockRead_liveBlkSig_stageX_odd
  exact absurd (pos_of_blockPar_odd (Phi := Psi) _ _ hodd) (lt_irrefl 0)

/-- The `x1` slot that completes the **committed** core pair `(fiveSigMark, stageX)` at
`h = 0`: `<c = 4, d = 4, e = 6, f = 5, g = 4, j = 2, k = 4, m = 4, o = 4>`, found by the layered
solve of `scripts/w61_block/blocklib.py`. -/
def blindCoreY : SqU6 gr3R := ⟨0, 0, 4, 4, 6, 5, 4, 0, 0, 2, 4, 0, 4, 0, 4⟩

/-- ⚠⚠ **THE CONTROL, PROVED: the committed witness's core pair does NOT require a handle.**
`GradedFiveStageFour.stageWit`'s two core slots admit a relator-killing marking at `h = 0`.  So
the dead core pairing at the committed point is not a gap in the instrument: the obstruction the
instrument reads genuinely fails there, and this exhibits the completion it fails to exclude.

⚠ The same is **expected** at wave 60's point, whose `x0` slot differs only in the fifth abelian
column, but nothing here establishes it: no theorem exhibits an `h = 0` completion for
`(fiveSigMark, forceX)`, and no measurement of this lane records one.  Treat it as an
expectation, not as a result.

⚠ This is also why the live pairs W63-SECOND found at the committed points cannot substitute.
`blockPar Phi (dsqX0 h) (sqGen h (sqHandleIdxU j)) = 1` does force `0 < h`, but vacuously: the
pair names a handle generator, so there is nothing at `h = 0` for it to exclude, and the theorem
below shows there really is a completion there to be excluded.  Only a live **core** pair
reaches it. -/
theorem sqRelWord_blindCore_handleFree :
    sqRelWord (fun i : Fin (sqRank 0) =>
      if (i : ℕ) = 0 then fiveSigMark gr3R else
      if (i : ℕ) = 1 then stageX else blindCoreY) = 1 := by decide

/-- ⚠ …and its `a0 = a1` dressing leaves the class-five residue `0`.  So at `h = 0` the
separation dies at the committed core pair for a reason the block channel does not see, which is
exactly why the composite above needs the point to move. -/
theorem sqRelWord_blindCore_handleFree_bit :
    sqRelWord (fun i : Fin (sqRank 0) =>
      if (i : ℕ) = 0 then fiveSigMark gr3R * stageX else
      if (i : ℕ) = 1 then stageX else blindCoreY) = 1 := by decide

end Composite

/-! ## 6 ⚠ What the class-five stack does NOT gain -/

section NoGain

variable {h : ℕ} {j : Fin h}

/-- ⚠ **The instrument's conclusion is FREE at the point.**  `pos_of_blockPar_odd` fires at the
live witness and returns `0 < h`, and `0 < h` was already in the context: every class-five
statement of this lane is indexed by a handle `j : Fin h`.  This is `GradedBlockFrame`'s
Honesty 1 in its sharpest form, and it is the reason the live point does not open a route. -/
theorem liveBlkHom_pos_free : 0 < h ∧ pos_of_blockPar_odd (Phi := liveBlkHom h j)
    (dsqSigma h) (dsqX0 h) blockPar_liveBlkHom = j.pos :=
  ⟨j.pos, rfl⟩

/-- ⚠ **The handle-selection form names the handle that was already named.**
`exists_handle_minor_odd_hom` produces a handle whose two letters are independent mod `2` in the
two outer abelian columns; at the live point that handle is `j`, the handle the point is built
on.  So the sharper form supplies no information either. -/
theorem exists_handle_minor_odd_liveBlkHom_free :
    selPar ((liveBlkHom h j (sqGen h (sqHandleIdxU j))).d
        * (liveBlkHom h j (sqGen h (sqHandleIdxV j))).e
      - (liveBlkHom h j (sqGen h (sqHandleIdxV j))).d
        * (liveBlkHom h j (sqGen h (sqHandleIdxU j))).e) = 1 := by
  rw [liveBlkHom_handleU, liveBlkHom_handleV]
  exact liveBlkUV_minor_odd

/-- ⚠ **The handle block's `(4,6)`-parity is a functional of the TWO core slots**, at the live
point as everywhere else, by wave 61's collapse `SqU6.selPar_handleWord_i_of_relator`.  Stated as
the instance of that collapse at the undressed marking.

⚠⚠ **This is not the class-five selection bit.**  In this file the bit is
`selPar (sqRelWord ...).o`, and the two quantities differ at this very marking:
`liveBlkWit_bit_separates` gives the bit `0` at `liveBlkWit h j 1`, where
`liveBlkWit_bit_eq_core_value` gives this parity `1`.  So the theorem does not by itself say that
a live block channel cannot add a datum to the bit; that would need the same collapse for the bit
itself, which is not proved here. -/
theorem liveBlkWit_bit_eq_core (h : ℕ) (j : Fin h) :
    selPar (handleWord (fun j' => liveBlkWit h j 1 (sqHandleIdxU j'))
        (fun j' => liveBlkWit h j 1 (sqHandleIdxV j'))).i
      = selPar (SqU6.blockRead (liveBlkWit h j 1 0) (liveBlkWit h j 1 1)) :=
  SqU6.selPar_handleWord_i_of_relator (sqRelWord_liveBlkWit_triv h j)

/-- …and both sides are `1` at the live point, where at both committed witnesses both sides are
`0` (`blockPar_stageFrameHom`, and the even handle minor of `commP_stageUV_live`).  ⚠ That is the
whole of the difference the move makes to the handle block's `(4,6)`-parity.  It says nothing
directly about the class-five selection bit, which is `0` at this undressed marking either way
(`liveBlkWit_bit_separates`). -/
theorem liveBlkWit_bit_eq_core_value (h : ℕ) (j : Fin h) :
    selPar (handleWord (fun j' => liveBlkWit h j 1 (sqHandleIdxU j'))
        (fun j' => liveBlkWit h j 1 (sqHandleIdxV j'))).i = 1 := by
  rw [liveBlkWit_bit_eq_core h j, liveBlkWit_zero, liveBlkWit_one, mul_one]
  exact blockRead_liveBlkSig_stageX_odd

end NoGain

/-! ## 7 Axiom pins

Committed prints for every public declaration: all **std-3** (`propext`, `Classical.choice`,
`Quot.sound`) or a subset; no census axiom is reachable, `sqPivotExp` included.  Every `decide`
is on `ZMod 8` or `ZMod 2`. -/

section AxiomPins

#print axioms SqU6.selPar_blockRead_of_gauge
#print axioms SqU6.selPar_blockRead_of_gauge_zero
#print axioms blockRead_fiveSigMark_gauge
#print axioms sqRelWord_d_indep_sigma
#print axioms liveBlkSig
#print axioms liveBlkSig_eq
#print axioms liveBlkY
#print axioms liveBlkU
#print axioms liveBlkV
#print axioms liveBlkWit
#print axioms liveBlkWit_zero
#print axioms liveBlkWit_one
#print axioms liveBlkWit_two
#print axioms liveBlkWit_handleU
#print axioms liveBlkWit_handleV
#print axioms liveBlkWit_handleU_ne
#print axioms liveBlkWit_handleV_ne
#print axioms liveBlkWit_of_ne_zero
#print axioms sqRelWord_liveBlkWit_triv
#print axioms sqRelWord_liveBlkWit_diag
#print axioms liveBlkWit_bit_separates
#print axioms liveBlkWit_class_four_blind
#print axioms liveBlkWit_gauge
#print axioms commP_liveBlkUV_live
#print axioms blockRead_liveBlkSig_stageX
#print axioms blockRead_liveBlkSig_stageX_odd
#print axioms blockRead_liveBlkSig_stageX_gauge
#print axioms liveBlkUV_minor_odd
#print axioms liveBlkImage
#print axioms liveBlkImage_le_stageN1
#print axioms liveBlkWit_a_even
#print axioms liveBlkWit_fiveOrth
#print axioms liveBlkWit_sigma_forced
#print axioms liveBlkWit_sigma_forced_sharp
#print axioms sqRelWord_liveBlkWit_diag_ne_one
#print axioms sqRelWord_liveBlkWit_diag_ne_one_sharp
#print axioms liveBlkHom
#print axioms liveBlkHom_gen
#print axioms liveBlkHom_sigma
#print axioms liveBlkHom_x0
#print axioms liveBlkHom_x1
#print axioms liveBlkHom_handleU
#print axioms liveBlkHom_handleV
#print axioms liveBlkHom_columns_even
#print axioms liveBlkHom_mem_stageN1
#print axioms forceLcs_liveBlkHom_le_stageN3
#print axioms liveBlkHom_sqArbFrame
#print axioms sqRelWord_liveBlkFrame_triv
#print axioms sqRelWord_liveBlkFrame_diag
#print axioms sqRelWord_liveBlkFrame_diag_ne_one_sharp
#print axioms sqRelWord_liveBlkFrame_diag_ne_one
#print axioms liveBlkFrame_class_four_blind
#print axioms blockPar_liveBlkHom
#print axioms blockPar_liveBlkHom_handle
#print axioms blockPar_liveBlkHom_sum
#print axioms blockPar_liveBlkHom_crosscheck
#print axioms blockPar_liveBlkHom_relator_agrees
#print axioms liveBlkCore_not_relator_handleFree
#print axioms liveBlkCore_no_hom_handleFree
#print axioms blindCoreY
#print axioms sqRelWord_blindCore_handleFree
#print axioms sqRelWord_blindCore_handleFree_bit
#print axioms liveBlkHom_pos_free
#print axioms exists_handle_minor_odd_liveBlkHom_free
#print axioms liveBlkWit_bit_eq_core
#print axioms liveBlkWit_bit_eq_core_value

end AxiomPins

end SqCore

end Dyadic

end GQ2

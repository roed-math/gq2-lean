# W63: a class-five witness with a live CORE block pairing, and why it changes nothing

**Wave W63, worker W63-LIVE5.**  Lean: `GQ2/Dyadic/SqCore/GradedFiveLive.lean`.  Off-Lean:
`scripts/w63_live5/` (plain Python plus sympy, exact integer arithmetic, certified outputs in
`scripts/w63_live5/results/`).  Consumes `GradedBlockFrame` (W62-COUNTHOM), `GradedBlockRead`
(W61-BLOCK), `GradedFiveStageFour` and `GradedStageFrame` (W60, W61).  Discharges the closing
line of `GradedBlockFrame`'s Honesty 3, and **corrects that Honesty note's overreach**, jointly
with `w63-second`.

> ⚠⚠ **Correction carried by this note.**  `GradedBlockFrame`'s Honesty 3 computed the block
> pairing at two pairs at each committed class-five point - the core pair `(sigma, x0)` and the
> handle pair `(u_j, v_j)` - found both even, and concluded that the points are block-blind.
> **They are not.**  W63-SECOND proved
> `blockPar (stageFrameHom h j) (dsqX0 h) (sqGen h (sqHandleIdxU j)) = 1`, and the same at wave
> 60's point; the readings are `blockRead(stageX, stageU) = -5` and
> `blockRead(forceX, forceU) = -3`, both odd.  W62's four theorems are true exactly as stated.
> The generalisation from two pairs to the points is what fails.
>
> ⚠ Nothing in `GradedFiveLive.lean` is affected, and the reason is scoping rather than luck:
> the gauge reduction of section 1 requires its **second** argument to be gauged, and a handle
> letter is not.  Indeed `stageU_45 = 1` is odd, which is exactly why that pair is live while
> the core pair is dead.  Every theorem stands as proved; four passages of prose were rewritten,
> and this note is one of them.

---

## 0.  Headline

| question | answer |
|---|---|
| **does a class-five witness with a live CORE block pairing exist?** | **YES**, and the construction is one coordinate wide.  `liveBlkWit` meets the whole `stageWit` standard and has `blockPar = 1` on the core pair and on the live handle pair.  The core pair is the new part: it is the only one of the three pairs that still exists at `h = 0`, hence the only one that can exclude it. |
| **is the core channel forced even by the witness standard?** (the cheaper question, asked first) | **NO**, and the reason is a theorem: for a pairing whose second argument is on the committed gauge, the reading is *exactly* the parity of the first slot's `(4,5)`-entry (`SqU6.selPar_blockRead_of_gauge`), and the fifteen-row standard places no condition at all on the sigma slot's entry, the relator's abelian rows reading only the `x0`- and `x1`-slots. |
| **why is the CORE pair dead at both committed witnesses?** | Because both carry the sigma mark `fiveSigMark = E_23`, whose `(4,5)`-entry is `0`.  One zero, never load-bearing.  ⭐ The same theorem explains why `(x0, u_j)` is live at those points: `u_j` is not gauged, and `stageU_45 = 1`.  It locates the blindness exactly, which is a better result than the mistaken "the points are blind" would have been. |
| **⭐⭐ what genuinely composes?** | One statement: `liveBlkCore_not_relator_handleFree`.  The witness's core pair is realised at every `h >= 1` and at no `h = 0`, whatever the `x1` slot - so a class-five separation point now provably needs a handle at the level of its core slots alone.  It is the first point in the tree that is a class-five witness and a live block point at once. |
| **⚠⚠ what does the class-five stack GAIN?** | **Beyond that one statement, nothing, and this is proved three times over.**  The `0 < h` the instrument produces is free at the point (`j : Fin h`); the handle it selects is the handle already named; and the class-five selection bit is a functional of the core slots, so a live channel cannot add a datum to it in principle.  By `exists_blockPar_odd_iff_pos` the supplied datum is *equivalent* to `0 < h`, so **no committed statement drops a hypothesis.**  ⭐ W63-SECOND's correction **reinforces** this: the committed points could already produce `0 < h` from the instrument, at `(x0, u_j)`, and vacuously.  The route was doubly empty. |
| **verdict on the direction** | **RETIRED as a source of new class-five leverage**, with the one composite above kept.  The core-pair blindness was real, localised, removable, and not the obstacle. |

**PROVED** (Lean, 66 public declarations, all prints std-3 or a subset, no `sorry`, no new
axiom, no `native_decide`): everything named above.
**MEASURED** (`scripts/w63_live5/results/`, `53` named checks across three scripts, `0`
failures): the standard at the point and its calibration at the two committed points; the `h = 0`
exclusion and its control; the gauge reduction exhaustively; the search.

---

## 1.  The gauge reduction, which is the whole story

`SqU6.blockRead(s, x) = s_45 x_56 - s_56 x_45`.  The committed class-two-forced gauge, recorded
identically by `GradedFiveForce.forceX_gauge` and `GradedFiveStageFour.stageX_gauge`, asks the
`x0` slot for

```text
x_12, x_34, x_45, x_13, x_24 even,   x_23 = 0,   x_56 ODD
```

so the second term of the reading dies and the first has an odd cofactor:

> ⭐⭐⭐ **THE GAUGE REDUCTION.**  `selPar (blockRead s x) = selPar s_45` whenever the **second**
> slot is gauged.  So the core-pair channel of a class-five witness is the parity of the **sigma
> slot's `(4,5)`-entry**, and nothing else about the point can move it.

⚠ Read the quantifier.  The gauge is on the *second* argument, so this governs pairings against
the `x0` slot and says nothing about pairings against a handle letter.  That is precisely the
distinction W63-SECOND's correction turns on: `stageU` is a handle letter, is not gauged, and
has odd `(4,5)`-entry.

That answers three questions at once.

* *Why is the core pair dead at `fiveFrameHom` and `stageFrameHom`?*  Both have sigma mark
  `E_23`, with `(4,5)`-entry `0`.  `blockRead_fiveSigMark_gauge`.  ⭐ And the same theorem says
  why `(x0, u_j)` is live there, so it explains both halves of the corrected picture.
* *Is the core-pair blindness forced?*  No.  The relator's four abelian rows are
  `-4 (m 1)_col + 2 (m 2)_col` (`SqU6.sqRelWord_d` and its siblings) and mention the sigma slot
  nowhere; `sqRelWord_d_indep_sigma` is that fact, and `derive_live5.py` section 3 measures it
  on `4000` sigma pairs with `0` mismatches.
* *Could the repair of the core pair have gone the other way?*  No.  Wave 59's live
  counterexample has `blindCexS_45 = 0` and gets its odd core reading from `blindCexX_45 = 1` -
  an **off-gauge** `x0` slot.  A class-five witness cannot copy that, because the gauge forces
  `x_45` even.  The sigma slot is the only slot left, and `E_45` is the minimal move.

---

## 2.  The point

```text
liveBlkSig = E_23 * E_45 = <b = 1, d = 1>            the committed sigma mark, times E_45
stageX     = <a = 2, e = 5>                          the committed x0 slot, UNCHANGED
liveBlkY   = <e = 2, f = 5, h = 5, l = 5, n = 7, o = 3>
liveBlkU   = <c = 2, d = 1>
liveBlkV   = <c = 2, e = 3, j = 5>
```

`liveBlkWit h j v = fiveTuple gr3R h j (liveBlkSig * v) stageX liveBlkY liveBlkU liveBlkV`, at
every handle count and every handle.  It meets the whole standard:

| condition | at `stageWit` | at `liveBlkWit` |
|---|---|---|
| fifteen rows die undressed | yes | yes, `sqRelWord_liveBlkWit_triv` |
| `a0 = a1` residue purely central and odd | `liftO 1` | `liftO 1`, `sqRelWord_liveBlkWit_diag` |
| both `U_5`-quotients blind at both dressings | yes | yes, `liveBlkWit_class_four_blind` |
| every letter has even `(1,2)`- and `(3,4)`-columns | yes | yes, `liveBlkImage_le_stageN1` |
| unconditional stage-four exclusion | yes | yes, `sqRelWord_liveBlkFrame_diag_ne_one_sharp` |
| sharp class-five line `FiveOrth` | yes | yes, `liveBlkWit_fiveOrth` |
| handle block live in the class-four row | yes | yes, `commP_liveBlkUV_live` |
| the `x0` slot's ten flat obstructions vanish | yes | inherited: the slot **is** `stageX` |
| core pair `(sigma, x0)` block pairing | `0` | **`1`**, `blockPar_liveBlkHom` |
| handle pair `(u_j, v_j)` block pairing | `0` | **`1`**, `blockPar_liveBlkHom_handle` |
| `(x0, u_j)` block pairing | `1` (W63-SECOND) | `1` |

The `x0` slot being literally `stageX` is deliberate: `stageX_flat`, `stageX_zpowZtwo` and the
whole pivot analysis of `GradedStageFrame` apply unchanged, and only the closed form of
`Phi (sqPivot h)` moves, by the single entry `d = 1`.  It is not recomputed here, because doing
so would pin the census axiom `sqPivotExp` for no gain.

**The search.**  `minimise_live5.py` enumerates `24576` handle-letter pairs from the mod-2 shape
of the commutator, derived symbolically in `derive_live5.py`:

```text
[u, v]_46 = u_45 v_56 + u_56 v_45                                  (mod 2)
[u, v]_15 = u_45 v_14 + u_13 v_35 + u_35 v_13 + u_14 v_45          (mod 2)
```

once both letters have even `(1,2)`- and `(3,4)`-columns; the other six `gamma_2` rows are then
even outright.  So a handle pair live in the block row **and** in the class-four row needs `d`,
`e` and `j` entries, which is exactly the family searched.  Minimum total weight of
`(U, V, x1)` over the family is `11`, attained by the point above; the whole point weighs `15`,
against `stageWit`'s `20`.

---

## 3.  ⚠ The legality audit, redone

`ArbFrames` asks the dressings of `sqArbFrame` to lie in `ker lambda ∩ ker nu'`.  The
`x0`-dressing is `nu'`-trivial and not `lambda`-trivial exactly as before
(`nuLam_sigArbDress_x0_ne_one`, a statement about `D_sq h` and so carrier-independent).  The
obstruction argument is again different and again recorded rather than formalised.  With
`(a_s, a_0, a_1, a_U, a_V)` the generator exponents, the abelian columns of `Phi` at this point
are

```text
(Phi g)_12 = 2 a_0     (Phi g)_23 = a_s      (Phi g)_34 = 2 (a_U + a_V)
(Phi g)_45 = a_s + a_U (Phi g)_56 = 5 a_0 + 2 a_1 + 3 a_V
```

Legality forces `a_s = 0` and `a_0 + 2 a_1 = 0`, so `a_0` is even, so `(Phi g)_12 = 2 a_0` is
`0` or `4` and never `stageX_12 = 2`.  No legal dressing has `Phi g = stageX`.

⚠ **This is the third distinct route to the same conclusion, and the previous two both fail
here.**  Wave 60 read the obstruction off `lambda + nu'` mod two; wave 61 read it off the fifth
abelian column, using `7` being a unit.  Here the fifth abelian column is *reachable*
(`3 * 7 = 5` mod `8`, so `a_V = 7` produces it), and the door is closed by the **first** abelian
column instead.  Anybody transporting this file's statements to another point must redo the
audit a fourth time.

---

## 4.  ⭐⭐ What composes: the core pair requires a handle

> `liveBlkCore_not_relator_handleFree`.  For every `m : Fin (sqRank 0) -> U_6(Z/8)` with
> `m 0 = liveBlkSig` and `m 1 = stageX`, `sqRelWord m /= 1`.

and in hom form, `liveBlkCore_no_hom_handleFree`: no continuous homomorphism on `D_sq 0` sends
the two core generators there.  Together with `sqRelWord_liveBlkWit_triv`, which realises the
same core pair at every `h >= 1` and every handle, this is a **core pair that requires a
handle** and that also carries the full class-five separation.  Neither ingredient can produce
it alone: the class-five stack supplies the separation, `SqU6.pos_of_blockRead_odd` supplies the
`h = 0` impossibility.

⚠ **And the live pairs at the committed points cannot substitute**, which is why the point still
had to move for *this* statement even though the committed points are not blind.
`blockPar Phi (dsqX0 h) (sqGen h (sqHandleIdxU j)) = 1` does force `0 < h`, but the pair names a
handle generator, so at `h = 0` there is nothing for it to exclude.  Only a pair of **core**
generators reaches an `h = 0` marking at all, and `sqRelWord_blindCore_handleFree` below shows
there really is a completion there to be excluded.

**The control is proved, not asserted.**  `sqRelWord_blindCore_handleFree` exhibits an explicit
`x1` slot `<c = 4, d = 4, e = 6, f = 5, g = 4, j = 2, k = 4, m = 4, o = 4>` completing the
**committed** core pair `(fiveSigMark, stageX)` at `h = 0`.  So `stageWit`'s core slots do not
require a handle, and the dead core pairing there is not a gap in the instrument: the obstruction
it reads genuinely fails.  `sqRelWord_blindCore_handleFree_bit` adds that the `a0 = a1`
dressing of that completion leaves residue `0` - so at `h = 0` the separation dies at the
committed core pair for a reason the block channel does not see.

Measured alongside: `200000` random `x1` slots and `400` layered solves against the live core
pair, `0` completions, every solve failing at the `(4,6)` row; and `3000` letter pairs with an
odd handle minor, `0` of which complete at the even-`(4,5)` sigma slot.

---

## 5.  ⚠⚠ What does NOT compose, and why the direction retires

The brief asked, ruthlessly, what the class-five stack gains from a live point.  Three theorems
in the Lean file answer, and the answer is: past section 4, nothing.

1. **`liveBlkHom_pos_free`.**  The instrument fires at the live point and returns `0 < h`.
   Every class-five statement of this lane is indexed by a handle `j : Fin h`, so `0 < h` was
   in the context before the pairing was consulted; the theorem states the equality of the two
   proofs.  This is `GradedBlockFrame`'s Honesty 1 in its sharpest form.
2. **`exists_handle_minor_odd_liveBlkHom_free`.**  The sharper handle-**selection** form,
   `exists_handle_minor_odd_hom`, names a handle whose two letters are independent mod `2` in
   the two outer abelian columns.  At the live point that handle is `j`, the handle the point is
   built on.  No information.
3. **`liveBlkWit_bit_eq_core`.**  Wave 61's collapse `SqU6.selPar_handleWord_i_of_relator` says
   the block coordinate's parity is a functional of the two **core** slots at every
   relator-killing marking.  So the block channel cannot add a datum to the class-five selection
   bit even in principle: `blockRead` *is* a core functional, and making it odd changes the
   bit's input, not the bit's information content.  `liveBlkWit_bit_eq_core_value` computes both
   sides as `1`, where at both committed witnesses both sides are `0`; that is the entire
   difference the move makes.

And on top of all three, `GradedBlockFrame`'s Headline 4: `exists_blockPar_odd_iff_pos` makes
the supplied datum **equivalent** to `0 < h`.  ⚠ **Nothing drops a hypothesis by consuming
this**, and any report saying otherwise is wrong.

⭐ **W63-SECOND's correction strengthens this argument; it was checked rather than assumed**
(doctrine rule iii on this lane's own composite).  All three theorems are about the **content of
the datum**, not about which pair carries it - `0 < h` was in the context, the handle was already
named, the bit is a core functional - so none of them is disturbed by learning that other pairs
were live at the committed points all along.  What the correction adds is that those points could
**already** produce `0 < h` from the block instrument, at `(x0, u_j)`, and vacuously.  The route
was doubly empty: the datum was already available at the old points, and it was already free
there.

So the honest disposition: the committed class-five points have a dead **core** pairing, section
1 says why in one coordinate, and repairing it does not open a route, because the only thing on
the other side of the door was a hypothesis the class-five statements already have.  The lane's
own hypothesis - that a live channel would let the block instrument feed the class-five stack -
is **refuted**, and the composite of section 4 is what survives.

---

## 6.  ⚠ MEASURED and open: does the class-five separation need a handle at all?

`scripts/w63_live5/results/h0_sweep.txt`.  At `h = 0` the relator is the bare core word, so a
class-five separation would be a gauged triple `(s, x, y)` with `sqWord(s, x, y) = 1` and
`sqWord(s x, x, y)` purely central with an odd class-five coordinate.  `200000` random gauged
triples produce

| stage | count |
|---|---|
| relator-killing `h = 0` markings on the gauge | `6277` |
| ...whose `a0 = a1` residue is purely central | `994` |
| ...and **odd** there, i.e. a class-five separation | **`0`** |

so the separation looks to need a handle, and the sweep is plainly not vacuous.  **Nothing in
the tree proves it**, and this file proves it only for the live core pair, by the block
instrument.  ⚠ The instrument cannot settle the general question: at a core pair with an even reading its
hypothesis is false, and `sqRelWord_blindCore_handleFree` shows the conclusion is false there
too; and the live `(x0, u_j)` pairs at the committed points exclude nothing at `h = 0`.  A proof
would have to come from the class-five rows themselves.

---

## 7.  What the next wave should take from this

1. **Do not build further on the block channel at class five.**  Section 5 is a refutation of
   the lane's own hypothesis, and it is structural rather than circumstantial: the collapse of
   the bit onto the core slots (wave 61) and the equivalence of the block datum with `0 < h`
   (wave 62) together close the route at both ends, and W63-SECOND's correction closes it a third
   time by showing the datum was already obtainable at the old points.  The live point is worth
   keeping only for the section-4 composite.

   ⚠ **And carry the process lesson.**  W62's Honesty 3 generalised a two-pair computation into
   a claim about points; that claim shaped this lane's charter and very nearly cost it the whole
   lane, and it cost `w63-second` a wave to correct.  When a docstring reports a computed value,
   it should name the arguments it was computed at.

2. **⭐ The question worth taking is section 6.**  "Does the class-five sigma separation force
   `0 < h`?" is a sharp, self-contained statement about the rank-3 core word `sqWord` over
   `ZMod 8` - no frames, no homomorphisms, no lattices - it is `0` for `0` in `200000` gauged
   trials, and a proof would be a genuine handle-count forcing for the *separation* rather than
   for a core pair.  The natural attack is the class-five row of `sqWord(s x, x, y)` against
   `sqWord(s, x, y) = 1`, in the shape of wave 58's closed form
   `x_12 y_24 y_46 + x_56 y_13 y_35`, with the gauge substituted.

3. **⚠ One proof not run.**  `GradedStageFrame.stageFrameHom_sqArbBase_handleU_ne` and its
   `V`-side twin prove, at the committed point, that the frame identification **fails** at a row
   bumping the selected handle, so the two hypotheses `hu`, `hv` are forced rather than chosen.
   That statement is not transported here, because it goes through the pivot anchor and the
   anchor is deliberately not recomputed (it would pin the census axiom `sqPivotExp`).  Every
   frame statement in `GradedFiveLive` carries `hu` and `hv` exactly as `GradedStageFrame` does;
   they are expected to be forced at the new point by the same argument and the same non-trivial
   pivot image, but that is a claim about a proof not run.

4. **Two smaller items.**  The class-four-blind legal escape dressing
   (`GradedStageFrame.stageLegalDress`) is not recomputed at the new sigma mark; the `gamma_2`
   census that produced `1024` of them at wave 61's point would have to be redone.  And the
   legality audit (section 3) now has three incomparable routes at three points, which is a sign
   that it wants a lemma rather than a per-point argument.

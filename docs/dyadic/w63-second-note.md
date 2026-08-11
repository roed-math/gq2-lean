# W63: the second block reading, and what the pair of readings pins

**Wave W63, worker W63-SECOND.**  Lean: `GQ2/Dyadic/SqCore/GradedBlockSecond.lean`.  Off-Lean:
`scripts/w63_second/` (plain Python, exact integer arithmetic, certified outputs in
`scripts/w63_second/results/`), layered on `scripts/w61_block/blocklib.py` over the
independently certified `U_6(Z/8)` of `scripts/w59_blind5/u6lib.py`.  Consumes `GradedBlockRead`
(wave 61) and `GradedBlockFrame` (wave 62).  Discharges both items of
`docs/dyadic/w61-block-note.md` section 6.3.

---

## 0.  Headline

| question | answer |
|---|---|
| **does the second reading exist?** | **YES, and everything wave 61 proved holds of it.**  ⭐⭐ `SqU6.selPar_handleWord_h_of_relator`, ⭐⭐ `SqU6.pos_of_blockReadCD_odd`, ⭐⭐ `blockParCD_relator_frame`, ⭐⭐⭐ `blockParCD_handleFree`, ⭐⭐ `exists_blockParCD_odd_iff_pos`.  The `(3,4)`- and `(4,5)`-columns are characters of `D_sq h`, so it is an honest second alternating form.  PROVED. |
| **do the two together pin more than either alone?** | **ABOUT THE GROUP, NO.  ABOUT A HOMOMORPHISM, YES.**  Each reading separately is EQUIVALENT to `0 < h`, and so is their conjunction (a marking at `h = 1` carries both, measured), so the pair is not a sharper handle-count instrument.  But the two forms are independent: ⭐⭐⭐ `blockPar_secCexHom_eq_zero` and ⭐⭐⭐ `blockParCD_blockCexHom_eq_zero` are two homomorphisms at which one form is odd on the core pair and the other is `0` on **every** pair.  PROVED both ways. |
| **is the second reading live at `fiveFrameHom` or `stageFrameHom`?** | **NO, and it is dead on every pair, not merely on two.**  ⭐⭐ `blockParCD_fiveFrameHom_eq_zero`, `blockParCD_stageFrameHom_eq_zero`.  Every letter of both witnesses has an even `(3,4)`-column. |
| ⚠ **but the FIRST reading is live at both** | ⭐⭐ `blockPar_fiveFrameHom_x0_handleU`, `blockPar_stageFrameHom_x0_handleU` (and the `v_j` versions).  `GradedBlockFrame`'s Honesty 3 computed the first form on two pairs; the form is odd on `(x0, u_j)` at both points.  **The description was wrong, no theorem was.**  A lane wanting a live block channel at those points does not have to move off them. |
| **does the second reading buy the class-five stack anything?** | **NO, and there is a structural reason.**  The `(3,5)` block coordinate enters the relator only at the class-four row `m`, with coefficient `sqWord.f`, and that coefficient is dressing-invariant on the `nu'` gauge, so it cancels: that is the committed `SqU6.sqRelWord_sigFiveDress_handle_blind_four`.  The first reading's `(4,6)` coordinate enters at the class-five row `o` with coefficient `sqWord.j`, which does move.  **The second reading has no live channel into any committed selection bit.** |
| **the cheap item** | Landed: `SqU6.handleWord_i_eq_blockRead_of_relator_e`, wave 61's block equation from the relator's `(5,6)`-row instead of its `(4,5)`-row.  One lemma, one corollary. |

**PROVED** (Lean, `82` public declarations, all prints std-3 or a strict subset, no `sorry`, no
new axiom, no `native_decide`; every `decide` is on `ZMod 8` or `ZMod 2`): everything named
above.
**MEASURED** (`scripts/w63_second/results/`, `88` named checks in three scripts, `0` failures):
the second parity law exhaustively over `ZMod 8`; the `(5,6)`-row variant exhaustively; the block
equation at all four class-two rows against `225` honestly collected relator-killing markings;
the two-directional characterisation by the layered solve; the four liveness cells; the `h = 1`
realizability of both readings at once; the span of the two forms.

---

## 1.  The reading, and where it comes from

`U_6` has four class-two coordinates, and each is the wedge of the two abelian columns beneath
it:

```text
row (1,3) = f    columns (a, b)      row (3,5) = h    columns (c, d)
row (2,4) = g    columns (b, c)      row (4,6) = i    columns (d, e)
```

⭐ **All four rows of the core word have the same shape**
(`results/derive_second.txt` section 2, symbolically over `Z`):

```text
W_row = -4*x_row + 2*y_row + (s_lo*x_hi - s_hi*x_lo + 10*x_lo*x_hi - 8*x_lo*y_hi + y_lo*y_hi)
```

Wave 61 read the `(4,6)` one.  This lane reads the `(3,5)` one:

> ⭐⭐ **THE SECOND BLOCK READING.**  `blockReadCD(s, x) = s_34 * x_45 - s_45 * x_34`
> (`SqU6.blockReadCD`), and the row it reads is `SqU6.sqWord_h`.

> ⚠ **SCOPE CORRECTION to `w61-block-note.md` section 6.3.**  That section says the `(3,5)`
> coordinate "has the same shape as `i` under the campaign's corner symmetry".  The **shape**
> claim is right, and section 2 of `derive_second.txt` proves it directly for all four rows at
> once.  The **symmetry** claim is not: `U_6`'s outer flip `p |-> J (p^{-1})^T J` acts on entries
> by `(i,j) |-> (7-j, 7-i)`, so it pairs `(1,3)` with `(4,6)` and `(2,4)` with `(3,5)`.  The four
> readings fall into two flip-orbits `{(1,3),(4,6)}` and `{(2,4),(3,5)}`, and the second reading
> is in the orbit the campaign has never looked at.  Nothing here follows from wave 61 by
> symmetry; the flip is certified as an automorphism commuting with `sqWord`
> (`derive_second.txt` section 7), and it is the wrong one.

---

## 2.  The second block equation, and the second symplectic identity

> ⭐⭐ **THE SECOND BLOCK EQUATION.**  `SqU6.selPar_handleWord_h_of_relator`:
> `selPar (handle block)_35 = selPar (blockReadCD (m 0) (m 1))` at **every** relator-killing
> marking over `ZMod 8`, at every handle count, at **every** sigma slot, with no gauge.

Two of the fifteen relator rows are used, the `(3,4)`-row (which forces the `x1` slot's
`(3,4)`-column even) and the `(3,5)`-row; the `(4,5)`-row does the first one's job equally well.
Certified **exhaustively** over `ZMod 8` (`4194304` points, `0` failures), and it needs the
abelian row: dropped, `1024` of `4096` correction terms are odd
(`results/derive_second.txt` section 3).

**It is characterised by the layered solve, not merely implied by it.**  `blocklib`'s solve is
written without any parity fact: at each of the fifteen rows it computes `sqWord` honestly and
only asks whether the residual is even.  Over `30000` random `(sigma, x0, handle letters)`, the
first class-two row at which the solve fails is exactly the first of the four block equations
that fails, and the solve gets past all four exactly when all four hold: `0` disagreements in
either direction (`results/census_second.txt` section B).

At the hom level the `(3,4)`- and `(4,5)`-columns are characters of `D_sq h`, so `blockParCD` is
an alternating bi-additive form that kills commutators (`blockParCD_commP_left`) and the torsion
letter (`blockParCD_dsqX1_right`, via the new `selPar_c_dsqX1`), and

> ⭐⭐ **THE SECOND SYMPLECTIC IDENTITY** (`blockParCD_relator_frame`):
> `omegaCD(n 0, n 1) = sum_j omegaCD(n u_j, n v_j)` (mod `2`) at every relator-killing frame and
> every continuous homomorphism.

Its `h = 0` instance is the empty sum, and with the two kernel facts it gives ⭐⭐⭐
`blockParCD_handleFree`: at `h = 0` the second form dies on **every** pair of elements of
`D_sq 0`.  Hence ⭐⭐⭐ `pos_of_blockParCD_odd` and ⭐⭐ `exists_blockParCD_odd_iff_pos`.

---

## 3.  The headline question, in three sharpenings

`w61-block-note.md` asked whether "the two together pin more than either alone".  The question
has to be split, because the answer differs.

### 3.1  As handle-count instruments: NO, and this is the honest reading of the whole lane

`exists_blockPar_odd_iff_pos` (wave 62) and `exists_blockParCD_odd_iff_pos` (this lane) are both
equivalences with `0 < h`.  So each reading alone decides the handle count exactly, and neither
can be sharpened by the other.  The only shape in which the pair could still be sharper is a
statement about their **conjunction**, and the cheapest such statement is
`both live => h >= 2`.

> ⚠ **It is FALSE.**  `results/pair_second.txt` section K exhibits a relator-killing marking at
> `h = 1` on which both readings are odd on the core pair:
> `S = <c=1, e=1>`, `X = <d=1>`, `U = <c=1, d=1>`, `V = <d=1, e=1>`,
> `Y = <d=6, f=4, h=3, j=4, m=6, o=6>`, with all fifteen relator rows verified.  One handle
> carries both.  All four liveness cells are realized at `h = 1`.

**So about the group `D_sq h` and its continuous `U_6(Z/8)`-quotients the pair pins exactly what
either member pins, namely `0 < h`, and nothing more.**  This is the trap `w63`'s charter
flagged: a second reading with the same `h = 0` consequence is a **reformulation**, and it is
stated as one in the Lean file.

### 3.2  As invariants of a homomorphism: YES, and both separations are PROVED

The two forms are not the same form, and neither is a function of the other.  Both directions
are witnessed in Lean, by homomorphisms rather than by markings:

* ⭐⭐⭐ `blockParCD_secCexHom = 1` and `blockPar_secCexHom_eq_zero`: at the new witness
  `secCexHom h j` the **second** form is odd on the core pair and the **first** is `0` on
  **every** pair of elements of `D_sq h`.  The witness is
  `S = U = <c=1>`, `X = V = <d=1>`, `Y = <d=2, h=3>`, a one-handle-live tuple whose relator dies
  at every handle count and every handle (`sqRelWord_secCexMark`).  Every letter has a vanishing
  `(5,6)`-column, which is what kills the first form outright.
* ⭐⭐⭐ `blockParCD_blockCexHom_eq_zero` against the committed `blockPar_blockCexHom = 1`: at
  wave 59's counterexample the **first** form is odd on the core pair and the **second** is `0`
  on every pair.

Measured on top of that, over `233` honestly collected relator-killing markings at handle counts
`0..4`: all four liveness cells occur, `181 / 16 / 17 / 19`
(`results/pair_second.txt` section I); and as alternating forms on the generator space the pair
spans a **two-dimensional** space at `83` of `114` markings with `h >= 1` (section L).

So the pair is a strictly finer invariant of a homomorphism than either member.  ⚠ That is a
statement about homomorphisms, not about the group: it says the map
`Phi |-> (omegaCD, omega_de)` has a larger image than either coordinate, not that the extra
coordinate constrains `h`.

### 3.3  As channels into the committed selection bits: NO, and structurally so

The relator's two selection rows are committed:

```text
relator_15 = W_15 + H_15 + W_12 * H_25 + W_13 * H_35        (SqU6.sqRelWord_m)
relator_16 = W_16 + H_16 + W_12 * H_26 + W_13 * H_36 + W_14 * H_46   (SqU6.sqRelWord_o)
```

Of the four class-two block coordinates only two appear at all: `H_35`, the second reading's, at
the class-**four** row, and `H_46`, the first reading's, at the class-**five** row.  `H_13` and
`H_24` appear nowhere.  The difference between the two that do appear is the coefficient, and it
is decisive:

* `W_13 = sqWord.f` is **dressing-invariant** on the `nu'` gauge (`SqU6.sqWord_f_dress`,
  committed; re-derived symbolically in `results/pair_second.txt` section M), so `H_35` **cancels**
  in the class-four response.  That is exactly the committed
  `SqU6.sqRelWord_sigFiveDress_handle_blind_four`;
* `W_14 = sqWord.j` is **not**: its response is `SqU6.blockCoupling`, and that is the whole of
  wave 61's class-five channel.

> ⭐⭐ **So the second reading has no live coupling into any committed selection bit.**  Its
> content is the handle-count forcing and nothing else, and the handle-count forcing is already
> supplied by the first reading.

---

## 4.  ⚠ The correction: the first reading is LIVE at both committed class-five points

`GradedBlockFrame`'s Honesty 3 reads:

> "wave 60's binder point and wave 61's stage-four point have an **even** block pairing on the
> core pair *and* on the live handle pair.  So the instrument says nothing at either of the two
> points the class-five lanes actually run at [...] Any lane hoping to feed this into the
> class-five stack has to move the point first."

The two computations are correct.  The conclusion drawn from them is not, because `blockPar` is a
form on the **whole** group and `pos_of_blockPar_odd` quantifies over all pairs.  At both points:

```text
blockRead(forceX, forceU) = 0*0 - 1*3 = -3      odd
blockRead(stageX, stageU) = 0*3 - 5*1 = -5      odd
```

because the `x0` slot's `(5,6)`-column (`forceX.e = 1`, `stageX.e = 5`) and the handle letters'
`(4,5)`-columns (`forceU.d = 3`, `stageU.d = 1`) are both odd.  Landed as ⭐⭐
`blockPar_fiveFrameHom_x0_handleU`, `blockPar_fiveFrameHom_x0_handleV`,
`blockPar_stageFrameHom_x0_handleU`, `blockPar_stageFrameHom_x0_handleV`, each by `decide`.

**What this changes and what it does not.**  No committed theorem is affected:
`blockPar_fiveFrameHom` and its three companions are true as stated, and the conclusion the
instrument produces at those points (`0 < h`) is free there anyway, because `fiveFrameHom h j` is
indexed by a handle `j : Fin h`.  What changes is the advice: **a lane looking for a committed
class-five point with a live block channel already has two, and does not have to move.**

The second reading is genuinely dead at both, and dead in the strong sense: ⭐⭐
`blockParCD_fiveFrameHom_eq_zero` and `blockParCD_stageFrameHom_eq_zero` kill it on every pair of
group elements, because every letter of `fiveWit h j 1` and of `stageWit h j 1` has an even
`(3,4)`-column.  The general tool is `blockParCD_eq_zero_of_even_c`, and its mirror
`blockPar_eq_zero_of_even_e` is what proves the separation of section 3.2.

---

## 5.  Where the second reading lives, and the one place it beats the first

`results/derive_second.txt` section 6.  `blockRead` uses coordinates `d, e, i`; `blockReadCD`
uses `c, d, h`.

```text
toU5L  keeps (a,b,c,d,f,g,h,j,k,m):   blockRead NO,   blockReadCD YES
toU5R  keeps (b,c,d,e,g,h,i,k,l,n):   blockRead YES,  blockReadCD YES
toU4RR keeps (c,d,e,h,i,l):           blockRead YES,  blockReadCD YES
```

Wave 61 recorded that the first reading survives only in the `toU5R` corner, and that `toU5R`
carries the class-five sigma marking `E_23 = <b=1>` to `<a=1>` rather than to
`sigFourMark = <b=1>`, so "the corner that can see the block is not the corner any committed
sigma instrument is built on".  ⭐ **The second reading survives in the `toU5L` corner too**, and
`toU5L` does carry `E_23` to `sigFourMark` (`SqU6.toU5L_fiveSigMark`, committed).  So the second
reading is expressible in the corner the committed sigma instruments live in and the first is
not.

⚠ **Do not over-read this.**  Being expressible in a corner is not the same as having a channel
into that corner's selection bit, and section 3.3 shows the channel is zero.  This is recorded
because it is a structural difference and might matter to a lane working inside `toU5L`, not
because it buys anything here.

Soundness is wave 61's, unchanged and for the same structural reason: the second channel is read
at class **two**, below the achievable lattice, so no `gamma_2`-dressing of either core slot can
move it (`SqU6.blockReadCD_gaTwoDress`, `SqU6.blockReadCD_gaThreeDress`), with the control that
full dressings do move it in `8656` of `10000` trials (`results/census_second.txt` section G).

---

## 6.  Scope notes

1. **Everything in section 3.1 is a REFORMULATION claim, and the lane claims nothing more.**  The
   second reading's handle-count content is `0 < h`, exactly like the first's.  No committed
   statement drops a hypothesis because of this lane, and the reasons `GradedBlockFrame`'s
   Honesty 2 gives are unchanged.
2. **The second block equation does not reopen the handle-letter question.**  It makes the
   `(3,5)` block coordinate a functional of the two core slots at every relator-killing marking,
   so the second reading is blind to the handle letters for exactly the reason the first one is.
   `SqU6.selPar_sqRelWord_sigFiveDress_o_eq_of_core` stands.
3. **Section 3.2's independence is about homomorphisms.**  Two homomorphisms can be separated by
   the pair and not by either member; no statement here says the pair constrains the group more
   than a member does, and section 3.1 says it does not.
4. **The `h = 1` both-live witness is MEASURED, not proved.**  It is an explicit relator-killing
   marking with all fifteen rows verified in Python (`results/pair_second.txt` section K); it is
   not in Lean, because what it refutes (`both live => h >= 2`) is not a committed statement.
   The Lean witness `secCexHom` covers the case the file does need.
5. **The correction of section 4 is to a docstring, not to a theorem.**  Nothing in
   `GradedBlockFrame` is false.  The four new `decide` theorems are the corrected reading.
6. The four-cell table of section 3.2 is over honestly collected markings; the per-cell witness
   search of `results/pair_second.txt` section J pre-filters on the block equation and is
   therefore used only to produce witnesses, never to test the equation.

**Sweep against the tree's refutations** (doctrine rule 4), recorded in full in
`results/pair_second.txt` section N: seven refutations and scope notes checked, including wave
62's reformulation warning (accepted and stated), wave 61's handle-letter closure (not
reopened), W62-CHANNELS' `gaTwoChannel_even_bit_even` (not touched: this reading is class-one
data, not a `gamma_2` channel), wave 60's three-covector line and wave 61's `gamma_2`-affineness
(not used), the wave-56 carried-input structures (not quoted), and wave 62's centrality
migration (not used).

---

## 7.  PROVED versus MEASURED

**PROVED** (Lean, `GQ2/Dyadic/SqCore/GradedBlockSecond.lean`, `82` public declarations, all
prints std-3 or a strict subset, no `sorry`, no new axiom, no `native_decide`; every `decide` is
on `ZMod 8` or `ZMod 2`): the second reading and the closed form of the `(3,5)` row over an
arbitrary commutative ring; the second block equation in integral and parity form; the `h = 0`
evenness, the handle-count forcing, the odd-minor refinement and the dressing forcing; the two
`gamma_2`/`gamma_3` invariances; the `(5,6)`-row variant of wave 61's equation; the hom-level
pairing with all its laws, the second symplectic identity, the `h = 0` death on every pair, the
forcing and the characterisation; the witness `secCexHom` and both separations; the second form's
identical vanishing at the two committed class-five points; and the four correction theorems
about the first form at those points.

**MEASURED** (`scripts/w63_second/`, `88` named checks in three scripts, `0` failures):

| measurement | scale | result |
|---|---|---|
| `U_6` law and `sqWord` vs honest `6 x 6` matrices | `2000` + `60` | `0` mismatches |
| the four class-two rows have the same shape, over `Z` | symbolic | exact |
| the second parity law, **exhaustive** on `ZMod 8` | `4194304` points | `0` failures |
| …without the `(3,4)`-row | `4096` correction terms | `1024` odd, so it is needed |
| the `(4,5)`-row does the same job | exhaustive | `0` failures |
| the `(5,6)`-row variant of the first equation, **exhaustive** | `16777216` points | `0` failures |
| the block equation at all four rows, honest relators | `225` markings, `h = 0..4` | `0` mismatches |
| the solve's class-two rows characterise the four equations | `30000` trials | `0` disagreements, both ways |
| the `h = 0` exclusion at the CD core pair | `128` exhaustive + `200000` random | `0` kills |
| …without the relator's `(3,4)`-row | `512` exhaustive | `32` kills, so the row is needed |
| the CD core pair realized at `h = 1..4` | `4` handle counts | all four |
| the second pairing's form laws | `20000` each | `0` failures |
| bi-additivity, **exhaustive** on the four live columns | `262144` points | `0` failures |
| the `x1` columns forced even, **exhaustive** | `16 + 16` | `0` odd |
| the `h = 0` death on every pair, exhaustive on the mod-2 data | `10` admissible data | `0` live |
| …with each hypothesis dropped in turn | `16` and `40` | live, so neither is idle |
| `gamma_2` invariance of both readings, with controls | `10000` each | `0` moves, controls nonzero |
| the committed points, both readings, every generator pair | `4` points | as in the Lean `decide`s |
| the four liveness cells, honest relators | `233` markings | `181/16/17/19`, all four |
| witnesses for each off-diagonal cell at `h = 1..4` | `12` searches | all found |
| both readings live at `h = 1` | witness | realized, relator verified |
| the pair spans a `2`-dimensional space | `114` markings, `h >= 1` | `83` of them |
| the class-four coefficient is dressing-invariant, the class-five one is not | symbolic | exact |

---

## 8.  What the next wave should take from this

1. **⭐ Read the correction of section 4 first, and tell `w63-live5`.**  The first block reading
   is **live** at `fiveFrameHom` and at `stageFrameHom`, on the pairs `(x0, u_j)` and
   `(x0, v_j)`.  A lane moving off those points because the block channel looked dead there was
   moving for a reason that does not exist.  The four theorems are one `decide` each.

2. **Do not build any more class-two readings.**  There are exactly four
   (`derive_second.txt` section 2), two of them appear in no selection row at all, and of the two
   that do, the second's coefficient is dressing-invariant so its channel is zero
   (section 3.3).  The `(4,6)` reading is the only one with a live channel, and wave 61 already
   has it.  This direction is **closed**.

3. **The handle-count question is closed too, in both readings.**  Both are equivalent to
   `0 < h`; their conjunction is realized at `h = 1`; the pair pins nothing more about the group.
   Anything wanting a sharper handle-count statement has to come from a different class, not a
   different column pair.

4. **What survives is what wave 61 already named**, unchanged by this lane: (i) which core
   triples are relator-killing at a given handle count, a `gamma_2`-realizability question about
   `sqWord(s, x, y)` rather than a reading question, and (ii) the class-eight
   coefficient/coordinate opening of `w58-sigma5-note.md` section 4.3.  Neither is touched here.

5. **If a lane still wants the second form**, the useful pieces are the two general tools rather
   than the reading: `blockParCD_eq_zero_of_even_c` and `blockPar_eq_zero_of_even_e` decide
   whether a *whole* form vanishes at a point from a one-column check on the generators, and they
   are what turned wave 62's two-pair computations into statements about every pair.  Any future
   claim that a form is "blind at a point" should be made with those, not by computing two pairs.

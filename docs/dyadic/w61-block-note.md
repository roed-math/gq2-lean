# W61: reading the handle block, and the first handle-count forcing

**Wave W61, worker W61-BLOCK.**  Lean: `GQ2/Dyadic/SqCore/GradedBlockRead.lean`.  Off-Lean:
`scripts/w61_block/` (plain Python plus sympy, exact integer arithmetic, certified outputs in
`scripts/w61_block/results/`).  Consumes `GradedFive`, `GradedFiveBlind` (wave 59) and
`GradedFiveStageFour` (wave 60).  Scopes rows (c) and 4.1-4.3 of
`docs/dyadic/w58-sigma5-note.md` a second time, in the opposite direction from wave 59.

---

## 0.  Headline

| question | answer |
|---|---|
| **does the block reading see anything the sigma reading does not?** | **NO about the handle letters, YES about the handle COUNT.**  At every relator-killing marking the block coordinate's parity is a closed form in four entries of the two core slots, so the class-five selection bit reads no handle datum at any sigma slot.  But the same equation, run backwards at `h = 0`, forces a core-slot minor even, and that is a handle-count separation no committed instrument can state. |
| **(a) the reading** | ⭐⭐⭐ `selPar H_46 = selPar (s_45 x_56 - s_56 x_45)`, at every relator-killing marking over `ZMod 8`, every handle count, **every** sigma slot, no gauge.  Two relator rows, and one of those two is interchangeable.  PROVED (`SqU6.selPar_handleWord_i_of_relator`). |
| what it separates that the sigma reading cannot | **Nothing about the handle letters.**  ⭐⭐⭐ `SqU6.selPar_sqRelWord_sigFiveDress_o_eq_of_core`: two relator-killing markings with the same three core slots have the same class-five bit, at different handle counts, with different handle letters, at any sigma slot.  Wave 59's committed blindness theorem is the `blockRead = 0` instance; wave 59's counterexample is the odd-`blockRead` instance, and what the bit separates there is the sigma slot, not the block. |
| **(b) is it a forcing?** | **YES, and of a kind the campaign has not had.**  ⭐⭐ `SqU6.pos_of_blockRead_odd`: a relator-killing marking with odd block reading has `0 < h`.  ⭐⭐⭐ `blindCexCore_not_relator_handleFree`: wave 59's counterexample core slots are realized at **every** `h >= 1` and at **no** `h = 0`, whatever the `x1` slot.  In the campaign's usual shape, `SqU6.selPar_blockRead_dress_of_relator`: a sigma dressing that keeps the relator killed pairs evenly against the `x0` slot in the two outer abelian columns. |
| soundness | ⭐⭐ **Structural, not arithmetic.**  `SqU6.blockChannel_gaThreeDress`: the channel is read at class **two**, below the whole achievable lattice, so no `gamma_2`-dressing moves the reading and no `gamma_3`-dressing moves the coupling.  No soundness chain, no even-column hypothesis, no covector condition, and **no analogue of wave 59's stage-four hole**. |
| **(c) what it buys the `h >= 1` route** | One instrument and one closed door.  The door: the class-five instrument set is complete as it stands with respect to handle data, so the route's residual uncertainty is not about information class four cannot see.  The instrument: a class-**one** invariant that separates `h = 0` from `h >= 1` and is invariant under every refinement the campaign uses. |

**PROVED** (Lean, 30 public declarations, all prints std-3 or a subset, no `sorry`, no new
axiom, no `native_decide`): everything named above.
**MEASURED** (`scripts/w61_block/results/`, `50` named checks, `0` failures): the parity law
exhaustively over `ZMod 8`; the equation at `410` relator-killing markings at handle counts
`0..4` against honest `6 x 6` matrix collection; the characterisation of admissible sigma
slots; the `h = 0` exclusion; the bit collapse; the lattice invariances with their controls.

---

## 1.  The reading

`SqU6.sqWord_i` (wave 59) gives the core word's `(4,6)` row at an arbitrary sigma slot:

```text
W_46 = -4*x_46 + 2*y_46 + (s_45*x_56 - s_56*x_45) + 10*x_45*x_56 - 8*x_45*y_56 + y_45*y_56
```

Wave 58 printed this at `sigma = E_23` and therefore without the bracket.  The bracket is the
whole subject of this file:

> ⭐⭐ **THE BLOCK READING.**  `blockRead(s, x) = s_45 * x_56 - s_56 * x_45`, the `2 x 2` minor
> of the sigma slot against the `x0` slot in the two outer abelian columns.

Over `ZMod 8` every other term of `W_46` is even once the relator's `(4,5)`-row forces `y_45`
even (`-8*x_45*y_56` is `0` outright), and the relator's `(4,6)`-row pins `H_46 = -W_46`.  So

> ⭐⭐⭐ **THE BLOCK EQUATION.**  `selPar H_46 = selPar blockRead(m 0, m 1)` at **every**
> relator-killing marking over `ZMod 8`, at every handle count and every handle, at **every**
> sigma slot, with no gauge hypothesis of any kind.

Two of the fifteen relator rows are used, the `(4,5)`-row and the `(4,6)`-row, and the
`(5,6)`-row does the first one's job equally well (`results/derive_block.txt` section 3).

**This is an equality where wave 59 has an implication.**
`GradedFiveBlind.SqU6.handleWord_i_even_of_relator` assumes
`(m 0).d * (m 1).e - (m 0).e * (m 1).d = 2 * t`, which is exactly "the block reading is even",
and concludes the block coordinate is even.  The converse half is new, and it is the half that
makes this a reading: an odd block reading forces an **odd** block coordinate
(`SqU6.handleWord_i_odd_of_relator`).

**The measurement that certifies it is the layered solve, not a restatement.**  Take random
handle letters and a random `(sigma, x0)` pair, and solve for an `x1` slot against the target
`handleWord^{-1}`, row by row, asking only whether each residual is even.  Row `(4,6)` is
solvable **if and only if** the block equation holds: `20000` trials, `0` disagreements
(`results/census_block.txt` section B).  So the equation is not a consequence of relator-killing
that one could have weakened; it **characterises** which sigma slots admit a relator-killing
completion at all, for fixed handle letters and a fixed `x0` slot
(`results/forcing_block.txt` section A).

---

## 2.  What it sees, and what it does not

### 2.1  The collapse

The wave-58 coupling identity `Delta_v(relator top row) = Delta_v(core top row) + coupling * H_46`
is committed (`GradedFive.SqU6.sqRelWord_sigFiveDress_o`).  Substituting the block equation:

> ⭐⭐⭐ ```text
> selPar (Delta_v relator top row)
>   =  selPar (Delta_v core word top row)  +  selPar (coupling)  *  selPar (blockRead)
> ```

at every relator-killing marking on the `nu'`-gauge, at every sigma slot.  **Every symbol on the
right is a core slot.**  Hence two relator-killing markings with the same three core slots have
the same class-five selection bit, at different handle counts, with different handle letters,
and with no hypothesis on the sigma slot.

Measured against honestly collected relators: `1360` comparisons, `0` mismatches, with the
block channel live (odd) at `3.0 %` of them, so the statement is not vacuous
(`results/census_block.txt` section D).

### 2.2  The honest control, and why waves 57-59 read this the way they did

`sqRelWord m = 1` says `handleWord = sqWord^{-1}`: the relator pins the **whole** block element,
not merely its `(4,6)` coordinate (`SqU6.handleWord_eq_inv_sqWord_of_relator`).  So
core-determinacy of the bit is cheap, and the content of the block equation is not that fact but
the closed form - four core entries out of thirty, computed without evaluating the core word.

This also explains the appearance of visibility that waves 58 and 59 recorded.  Wave 58's
separating pair is `GradedFive.liveFiveMark` against `GradedFive.deadFiveMark`, and
`deadFiveMark` does **not** kill the relator; its own docstring says so.  Wave 59's
counterexample does kill the relator and does have an odd block, and its block equation is the
`blockRead = 7` instance: `blindCex_block_equation` derives the committed
`blindCex_handleWord_i = 1` from the counterexample's core slots alone.  What the class-five bit
separates there is the sigma slot `E_23 * <e=1>`, which is the only thing that moved.

> **SCOPE NOTE for `docs/dyadic/w58-sigma5-note.md` section 4 and its wave-59 amendment.**  The
> wave-59 amendment says the block is "invisible at the committed sigma slot and visible away
> from it".  Both halves stand as stated about the *bit*.  What is now proved is that the
> visible quantity is a functional of `(m 0, m 1)`, so no reading of the class-five top row
> distinguishes two relator-killing markings by their handle data, anywhere.  The class-eight
> forecast of section 4.3 is untouched: it is about coefficients and block coordinates of
> higher class, and this file says nothing about those.

---

## 3.  The forcing

Run the equation backwards.  At `h = 0` there is no block, `H_46 = 0`, and the equation reads

> ⭐⭐ **`blockRead(sigma, x0)` is EVEN at every relator-killing marking with no handles.**

Contrapositive: ⭐⭐ a relator-killing marking with an **odd** block reading has `0 < h`
(`SqU6.pos_of_blockRead_odd`).  Sharper, ⭐ some handle pair's `(4,5)/(5,6)` minor is odd, that
is, its two letters are independent mod `2` in those two columns
(`SqU6.exists_handle_minor_odd`), since `H_46` is the sum of those minors.

**It is not vacuous, and the witness is already committed.**  Wave 59's counterexample core
slots `(sigma, x0) = (E_23 * <e=1>, <x_45=1, x_24=1, x_36=1>)` are realized by a relator-killing
marking at **every** handle count `h >= 1` and every handle (`sqRelWord_blindCexMark`), and by
**none** at `h = 0`, whatever the `x1` slot (⭐⭐⭐ `blindCexCore_not_relator_handleFree`).
Measured independently, exhaustively over the three `x1` coordinates that can enter the `(4,6)`
row and subject to the relator's own `(4,5)`-row, and by a `300000`-point random sweep of the
whole `x1` slot: `0` kills.  The `(4,5)`-row is load-bearing there and the census says so:
dropped, `32` of the `512` values do kill the `(4,6)` row
(`results/forcing_block.txt` section C).

**In the campaign's usual shape.**  `SqU6.selPar_blockRead_dress_of_relator`: a sigma dressing
`v` that keeps the relator killed satisfies `selPar (v_45 * x_56 - v_56 * x_45) = 0`.

> ⚠ **Its exact scope, because it decides what the forcing is worth.**  The diagonal dressing
> `v = x0` - the `a0 = a1` forcing - meets the conclusion outright, a minor of a slot against
> itself being `0`; and so does every `gamma_2`-dressing, both columns vanishing.  The forcing
> therefore bites only on **abelian** dressings, where it is not vacuous
> (`results/forcing_block.txt` section B).  It is a channel no committed forcing reads, and it
> is not the channel the committed exclusions run on.

---

## 4.  Soundness, and the one place the block reading is better behaved

The campaign's class-five soundness is arithmetic: wave 59 needs a four-step lower-central-series
chain and an even `(3,4)`-column at every slot; wave 60 replaces the chain by three covectors and
shows the condition is merely sufficient; and wave 59's exclusion has a **stage-four hole**, a
`gamma_3`-move of the point's own letters that kills the dressed frame, which wave 60 had to
close by strengthening the point.

The block channel has none of that, for a structural reason:

* every element of `gamma_2` has vanishing abelian columns, so **no `gamma_2`-dressing of any
  slot moves the block reading** (`SqU6.blockRead_gaTwoDress`);
* every element of `gamma_3` has vanishing class-two columns too, so **no `gamma_3`-dressing
  moves the coupling** (`SqU6.blockCoupling_gaThreeDress`);
* hence ⭐⭐ the block channel's contribution to the class-five bit is invariant under the whole
  lattice (`SqU6.blockChannel_gaThreeDress`), the campaign's achievable refinements being
  `gamma_4`-shaped at class five and `gamma_3`-shaped one filtration step wider.

Both controls are measured, so neither invariance is vacuous: `gamma_2`-dressings **do** move
the coupling parity (`3875` of `10000`) and full dressings **do** move the block reading
(`2981` of `10000`), and the honest lower central series of the image subgroup at wave 59's
point is computed rather than assumed (`results/forcing_block.txt` section D).

The reason is one line: **the block channel is read at class two, below everything the
achievable lattice can reach.**  That is the only respect in which it beats the sigma reading.

---

## 5.  PROVED versus MEASURED

**PROVED** (Lean, `GQ2/Dyadic/SqCore/GradedBlockRead.lean`, 30 public declarations, all prints
std-3 or a strict subset, no `sorry`, no new axiom, no `native_decide`; every `decide` is on
`ZMod 8` or `ZMod 2`): the block reading and the closed form of the `(4,6)` row over an
arbitrary commutative ring; the block equation in integral and parity form and both of its
halves; the pinning of the whole block element; the `h = 0` evenness, the handle-count forcing,
the odd-minor refinement and the dressing forcing; the collapse of the class-five bit onto the
core slots and the handle blindness across handle counts; the three lattice invariances; and the
two committed points.

**MEASURED** (`scripts/w61_block/`, `50` named checks in three scripts, `0` failures):

| measurement | scale | result |
|---|---|---|
| `U_6` law vs honest `6 x 6` matrices | `2000` comparisons | `0` mismatches |
| `W_46` closed form, symbolically over `Z` | - | exact |
| the parity law, **exhaustive** on `ZMod 8` | `4194304` points | `0` failures |
| …without the abelian row | `4096` correction terms | `1024` odd, so the row is needed |
| the block equation at relator-killing markings | `410` markings, `h = 0..4` | `0` mismatches |
| row `(4,6)` solvable `<=>` the equation | `20000` trials | `0` disagreements |
| admissible sigma slots characterised | `30000` trials | `0` disagreements |
| `h = 0` and an odd block reading | `3074` odd core pairs | `0` completions |
| the bit collapse | `1360` comparisons | `0` mismatches, `3.0 %` live |
| the handle-count separation at blindCex | `512` exhaustive + `300000` random | `0` kills |
| …without the relator's `(4,5)`-row | `512` exhaustive | `32` kills, so the row is needed |
| relator-preserving sigma dressings | `85` found by solve | `0` odd pairings |
| `gamma_2` / `gamma_3` invariance | `10000` dressings each | `0` moves, controls nonzero |
| `gamma_k` of the honest image at blindCex | `k = 2..5`, sizes `512, 8, 1, 1` | `0` elements with a live `(4,5)` or `(5,6)` column |

---

## 6.  What the next wave should take from this

1. **Do not look for a class-five instrument that reads handle data.**  There is none: the bit
   is a functional of the three core slots at every relator-killing marking, at every sigma
   slot, at every handle count.  The remaining uncertainty on the `h >= 1` route is not about
   information the class-four machinery cannot see, and it must be attacked another way.  The
   two directions that survive are (i) which core triples are relator-killing at a given handle
   count, which is a `gamma_2`-realizability question about `sqWord(s, x, y)` and not a reading
   question, and (ii) the class-eight coefficient/coordinate opening of
   `w58-sigma5-note.md` section 4.3, which this file does not touch.

2. **The forcing to try to build on is the handle-count one.**  `blockRead` is a class-one
   invariant, invariant under every achievable refinement, that separates `h = 0` from
   `h >= 1`.  The obvious next statement is its hom-level transposition:

   > ⭐⭐ **THE STATEMENT.**  For a continuous homomorphism `Phi : D_sq h -> U_6(Z/8)` whose
   > relator image is trivial, `selPar (blockRead (Phi sigma) (Phi x0)) = 1` implies `0 < h`,
   > and some handle pair `(u_j, v_j)` has `selPar ((Phi u_j)_45 (Phi v_j)_56 -
   > (Phi u_j)_56 (Phi v_j)_45) = 1`.

   The marking-level statement is `SqU6.pos_of_blockRead_odd` and is proved; the transposition
   is `GradedFiveFrame`'s pattern applied to a statement with **no** soundness hypothesis at
   all, so it should be materially cheaper than the class-five sigma transposition was.

3. **Two smaller items.**  The `(5,6)`-row variant of the block equation (measured, section 3 of
   `results/derive_block.txt`, one line in Lean).  And the same construction one column in: the
   `(3,5)` coordinate `h` has the same shape as `i` under the campaign's corner symmetry, so
   there is a second block reading `s_34 x_45 - s_45 x_34` waiting at the `(3,5)` row, with the
   same `h = 0` consequence and a different pair of columns; whether the two together pin more
   than either alone is not measured here.

# W64: the class-five sigma separation forces a handle, and it does so with no gauge

**Wave W64, worker W64-SEP0H.**  Lean: `GQ2/Dyadic/SqCore/GradedFiveSepZero.lean`.  Off-Lean:
`scripts/w64_sep0h/` (plain Python, exact integer arithmetic, no `sympy`; certified outputs in
`scripts/w64_sep0h/results/`).  Answers the single question
`docs/dyadic/w63-live5-note.md` section 6 left open and section 7 priced as the wave's best
remaining item.

---

## 0.  Headline

| question | answer |
|---|---|
| **does the class-five sigma separation force `0 < h`?** | ⭐⭐⭐ **YES.**  `sepZero_pos_of_bit_odd`: at every handle count, a marking over `gr3R` that kills the relator and whose `a0 = a1` dressing has an odd class-five coordinate has `0 < h`.  Equivalently `sepZero_bit_even`: at `h = 0` every relator-killing marking has an even class-five separation bit. |
| **at what price in hypotheses?** | ⭐⭐ **None.**  The charter asked for the *gauged* statement.  What is proved needs no gauge: no condition on the sigma slot, none on the `x0` slot, none on the `x1` slot beyond what the relator itself supplies.  It is the exact class-five transposition of `GradedSigmaFive.sigFourRead_diag_even_of_abelRows`. |
| **what is the mechanism?** | ⭐⭐⭐ **The response is a combination of lower rows of the UNDRESSED word.**  `SqU6.sqWord_diagDress_o`, over an arbitrary commutative ring: the class-five response equals an explicit polynomial-coefficient combination of the nine class-`2`-to-`4` rows of `sqWord s x y`, modulo `2`.  At `h = 0` the relator *is* the core word, so all nine vanish. |
| **how much of the residue is even?** | **All of it.**  `SqU6.sqWord_diagDress_low` (any ring, no hypothesis): the `a0 = a1` dressing moves **no** row of class at most two.  `SqU6.selPar_sqWord_diagDress_high`: the remaining six are even at every relator-killing `h = 0` marking.  So the dressing is congruent to the undressed marking modulo `2` in every coordinate. |
| **hom level?** | **Yes**, and cheaply: `sepZero_pos_of_bit_odd_hom` through `GradedFive.sqU6Balance_gen`.  ⚠ The tuple statement is primary; the gate is an equality of markings, so the hom form is a corollary and carries no extra content. |
| ⭐ **the instrument that made it possible** | `SqU6.sepShiftRow`, the monoid endomorphism carrying the `(2..6)`-corner onto the `(1..5)`-corner and killing the sixth column.  The tree had closed forms for the core word's rows `f, h, i, j, m`; the four remaining rows `g, k, l, n` are their images one step outwards, by naturality of `sqWord`.  No new polynomial is transcribed for them. |
| ⚠ **what it does NOT buy** | **No committed statement drops `0 < h`.**  Every class-five statement of the stack is indexed by a handle `j : Fin h`.  The gain is architectural: the handle in the committed witnesses is *necessary*, not incidental. |

**PROVED** (Lean, 44 public declarations of which 15 are projection lemmas, no `sorry`, no new axiom, no
`native_decide`; all prints std-3 or a subset, no census axiom reachable): everything named
above.
**MEASURED** (`scripts/w64_sep0h/results/`, `31 + 24` named checks, `0` failures): the
coordinate law against honest integer `6 x 6` matrices written from scratch; every emitted
witness against exact integer evaluation; the minimality of every hypothesis of the gauge
collapse; wave 58's closed form rederived; and seven sweep families.

---

## 1.  The statement, pinned

The charter asked for this to be pinned before anything was proved, because the campaign has
repeatedly been bitten by statements that were true but not the ones wanted.

* **The carrier.**  `SqU6 R = U_6(R)`, fifteen strictly-upper entries, class-graded as
  `a..e` (abelian), `f..i`, `j..l`, `m,n`, `o`; `gr3R = ZMod 8`.
* **The core word.**  `sqWord s x y = (conjP x s)⁻¹ * (x³)⁻¹ * y² * commP y (conjP y s)`.
* **The relator.**  `sqRelWord m = sqWord (m 0) (m 1) (m 2) * prod_j [u_j, v_j]`.  At `h = 0`
  the product is empty, so `sqRelWord m = sqWord (m 0) (m 1) (m 2)` (`Cores.sqRelWord_zero`).
* **The `a0 = a1` dressing** is `sigFiveDress m v` at `v = m 1`: the sigma slot becomes
  `m 0 * m 1` and nothing else moves.  This is the depth sweep's forced dressing
  (`GradedSigmaFour.sigFourRead_gauge_sigma_eq_x0`).
* **The class-five sigma separation** is: the undressed marking kills all fifteen relator rows,
  and the dressed one leaves a residue that is purely central with an **odd** `(1,6)`
  coordinate.  Its **bit** is `selPar (sqRelWord (sigFiveDress m (m 1))).o`.
* **The gauge**, as the charter recorded it and as `GradedFiveForce.forceX_gauge` and
  `GradedFiveStageFour.stageX_gauge` state it: `x_12, x_34, x_45, x_13, x_24` even, `x_23 = 0`,
  `x_56` odd, and the `x1` slot's `x_12, x_34, x_45` even.

The question, as asked: *at `h = 0`, does every **gauged** relator-killing marking have an even
class-five separation bit?*  The answer is yes, and the word **gauged** can be deleted.  ⚠ Note
that centrality of the residue is not needed either: what is proved is that the residue is even
in every coordinate, which is strictly stronger than "not a separation".

---

## 2.  ⭐⭐⭐ The row expansion, which is the whole proof

Write `W = sqWord s x y` for the undressed word.  With the five abelian columns of the `x1` slot
even - the relator's own abelian rows, `GradedSigmaFive.abelRow_even` - and **nothing else**,
over an arbitrary commutative ring:

```text
(sqWord (s*x) x y).o - W.o
   =  x_36 * W_13
    + x_12 x_46 * W_24
    + (x_56 x_13 + x_12 x_23 x_56) * W_35
    + (x_14 + x_12 x_24 + x_34 x_13 + x_12 x_23 x_34) * W_46
    + x_46 * W_14
    + x_12 x_56 * W_25
    + (x_13 + x_12 x_23) * W_36
    + x_56 * W_15
    + x_12 * W_26
    + 2 * sepZeroWitO                                  (230 explicit monomials)
```

and the same shape one and two levels down:

| row | response |
|---|---|
| `(1,4)` | `x_34 W_13 + x_12 W_24 + 2 * (10 terms)` |
| `(2,5)` | `x_45 W_24 + x_23 W_35 + 2 * (10 terms)` |
| `(3,6)` | `x_56 W_35 + x_34 W_46 + 2 * (10 terms)` |
| `(1,5)` | `x_35 W_13 + x_12 x_45 W_24 + (x_13 + x_12 x_23) W_35 + x_45 W_14 + x_12 W_25 + 2 * (52)` |
| `(2,6)` | `x_46 W_24 + x_23 x_56 W_35 + (x_24 + x_23 x_34) W_46 + x_56 W_25 + x_23 W_36 + 2 * (52)` |

and, one level below that, **nothing at all**: `SqU6.sqWord_diagDress_low` says the nine rows of
class at most two do not move, over any ring and with no hypothesis.  (The five abelian rows do
not read the sigma slot; each class-two row reads it through an antisymmetric pairing against
the `x0` slot, and on this dressing that pairing is against the `x0` slot itself.  ⚠ At a
general dressing `v` the `(3,5)` and `(4,6)` rows *do* move, which is wave 58's response table;
the vanishing is a property of the diagonal.)

So at `h = 0` a relator-killing marking has `W = 1`, every row on the right is `0`, and the
whole response is twice something.  That is the proof.

**How the expansion was found.**  `scripts/w64_sep0h/derive_sep0h.py` derives the response over
`Z` (202 monomials at the top row) and reduces modulo `2` with the abelian rows substituted; the
coefficients are then obtained by Gaussian elimination over `F_2` in the module generated by
`monomial * row`, and lifted back to an exact identity over `Z` whose remainder is even
coefficient by coefficient.  Every emitted witness is re-certified by exact integer evaluation
of `sqWord` at `1500` random points before transcription, and then again by `ring` in Lean.

---

## 3.  ⭐ The shift endomorphism

The expansion reads all nine rows of class two to four.  The tree had closed forms for `f`, `h`,
`i` (class two), `j` (class three) and `m` (class four); it had none for `g`, `k`, `l`, `n`, the
four rows living in the sixth column below the top.

`SqU6.sepShiftRow p = <p_23, p_34, p_45, p_56, 0, p_24, p_35, p_46, 0, p_25, p_36, 0, p_26, 0, 0>`
is a monoid endomorphism (it is the right `U_5`-quotient followed by the padding of `U_5` into
the top-left corner of `U_6`, written directly because the tree has no padding map).  It carries
row `g` to row `f`, row `k` to `j`, row `l` to `k` and row `n` to `m`, so naturality of `sqWord`
transports each committed row lemma one step outwards:

```text
SqU6.sqWord_g_of_shift   from  SqU6.sqWord_f_core        (GradedFiveDefect)
SqU6.sqWord_k_of_shift   from  SqU6.sqWord_j             (GradedFive)
SqU6.sqWord_l_of_shift   from  SqU6.sqWord_k_of_shift    (twice shifted)
SqU6.sqWord_n_of_shift   from  SqU6.sqWord_m             (GradedFiveDefect)
```

⭐ Each is a four-line proof and no new polynomial is transcribed.  The four rows are of general
use well beyond this file; they are named with an `_of_shift` suffix rather than
`SqU6.sqWord_g` and so on precisely so that a concurrent lane landing the general names
independently does not collide, and so that a later consolidation is an obvious rename.

---

## 4.  ⭐ The gauge collapse, and a correction to how wave 58 is quoted

On the committed class-two-forced gauge - `x_23 = 0` and `x_12, x_34, x_13, x_24` even - seven
of the nine coefficients become even and the response is carried by exactly two rows:

> `SqU6.sqWord_diagDress_o_gauge`:
> `(sqWord (s*x) x y).o = W.o + x_56 * W_15 + x_14 * W_46 + 2 * sepZeroWitGauge`.

⭐ **Note which two gauge hypotheses are absent.**  The `x0` slot's fourth and fifth abelian
columns `x_45` and `x_56` are free, and `x_56` is exactly the datum wave 58 calls "the escape",
the column `U_5` does not possess.  So the collapse does not run on the escape column.  Every
one of the ten hypotheses it *does* use is consumed: `derive_sep0h.py` section 5 drops each in
turn and prints the surviving monomials.  The one trade available is `y_56` even for `x_45`
even; the committed gauge supplies both.

⚠ **Two things about wave 58 that must not be quoted loosely**, both checked here rather than
assumed:

1. `docs/dyadic/w58-sigma5-note.md` section 3.1's closed form
   `x_12 y_24 y_46 + x_56 y_13 y_35` is the `sigma = E_23` instance.  `derive_sep0h.py`
   section 3 reproduces it exactly from scratch (a good end-to-end check on this lane's
   library), and records that at a **general** sigma slot the same reduction has `42` monomials,
   not `2`.
2. Section 3.3's sketch - "with a dead block the relator forces the core word trivial, hence
   `x_12` even, and the class-four row is `x_12 x_35 + y_13 y_35`, so `y_13 y_35` must be even" -
   is also at `sigma = E_23`.  At a general slot the class-four row reads
   `s_12 x_25 + s_45 x_14 + s_13 x_35 + y_13 y_35 + s_12 s_23 x_35 + ...` and `y_13 y_35` is not
   forced even on its own.  This is why the identity above is stated as a multiple of the whole
   row rather than as a statement about `y_13 y_35`; the sketch is right in spirit and the
   general proof is not a transcription of it.

---

## 5.  Calibration, and what is load-bearing

* ⭐ **The tree's own `h = 0` datum agrees.**  `GradedFiveLive.blindCoreY` completes the
  committed core pair `(fiveSigMark, stageX)` at `h = 0`, and W63-LIVE5 computed by `decide`
  that its `a0 = a1` dressing leaves residue `1`.  `sepZero_blindCore_bit` re-derives the
  class-five half of that from the general theorem, computing nothing at the point.  This is the
  composite check of doctrine rule iii against a committed value, and it passes.
* ⚠ **`h = 0` is load-bearing.**  `sepZero_fiveWit_bit_odd`: `GradedFiveForce.fiveWit` kills the
  relator at every `h >= 1` and has class-five bit `1`.  The expansion is not contradicted,
  because at `h >= 1` the relator pins the core word to the handle word's inverse rather than to
  `1`, and the nine rows the response reads are then free to be odd.  `sweep_sep0h.py`'s
  calibration section computes them at `fiveWit` and finds `x_56 W_15 + x_14 W_46 = 1` there.
  ⭐ **That is the sharpest reading of what a handle is FOR at class five: it is what lets the
  core word be non-trivial while the relator dies.**
* ⚠ **The `a0 = a1` dressing is load-bearing.**  Nothing here says that no sigma dressing
  separates at `h = 0`; `SqU6.sqWord_diagDress_low` is false at a general `v`.
* ⚠ **The refutation sweep.**  Doctrine rule iv: this file's statements were swept against
  `EvenRouteCarriedDeep{N,M}` (not quoted; nothing here touches the even route), wave 60's
  three-covector line (not used), wave 61's gamma-2 affineness (not used), W63-SECOND's
  block-blindness correction (not used - no block quantity occurs anywhere in the file), and
  W62's `exists_blockPar_odd_iff_pos` (not used, and the forcing here is independent of the
  block instrument in both directions).

---

## 6.  ⚠ PROVED versus MEASURED, honestly

Everything in section 0's table is **proved in Lean**.  The measurements are corroboration and
tooling:

| measured | where | scale |
|---|---|---|
| the coordinate law against honest integer `6 x 6` matrices, written from scratch in this lane | `derive_sep0h.py` section 1 | `2400` comparisons, `0` mismatches |
| wave 58's closed form rederived, and the general slot's `42` monomials | section 3 | exact |
| the seven emitted Lean witnesses against exact integer evaluation | section 6 | `10500` points, `0` mismatches |
| minimality of the ten hypotheses of the gauge collapse | section 5 | each drop prints surviving monomials |
| seven `h = 0` sweep families, gauged / ungauged / gauge broken one column at a time | `sweep_sep0h.py` | `1000000` trials, `0` separations, `0` odd coordinates anywhere |

⚠ The sweep is now redundant as evidence; it is kept because it tests families the theorem was
not tuned on and because a discrepancy would have been a bug report against the Lean.

---

## 7.  What the next wave should take from this

1. ⭐⭐ **The four transported rows are reusable and should probably be consolidated.**
   `SqU6.sqWord_g_of_shift`, `_k_`, `_l_`, `_n_` complete the tree's closed forms for all fifteen
   rows of the core word for the first time.  Any lane that wants a row of the core word now has
   one, and `SqU6.sepShiftRow` will give the same service at class six.  A consolidation pass
   should rename them to `SqU6.sqWord_g` and so on once the concurrent lanes have landed.
2. ⚠ **Do not read this as opening the `h >= 1` route.**  It closes `h = 0` and says nothing
   about which `h >= 1` markings separate.  What it does supply is a clean statement of what the
   handle contributes: it is the only way the core word can be non-trivial at a relator-killing
   marking, and the class-five response reads the core word's rows and nothing else.
3. ⭐ **The obvious next question is the same one one class up**, and the machinery is now in
   place: is the class-**six** separation also forced?  The response there will read the
   class-five rows, which are the ones this file proves even at `h = 0`, so the induction has a
   base.  What is not obvious is whether the coefficients stay inside the ideal; the `F_2`
   elimination in `derive_sep0h.py` is written generically enough to answer it.
4. **A smaller item.**  `SqU6.selPar_sqWord_diagDress_high` proves the six high rows even but not
   zero.  Whether the dressed residue at `h = 0` is forced to lie in `2 * gamma_4`, or can be
   any even element, is not settled and is one more `F_2` elimination away.

# W61: the gamma-2 translation identity at class five, and its quadratic block

**Wave W61, worker W61-WIDER.**  Lean: `GQ2/Dyadic/SqCore/GradedFiveGammaTwo.lean` (1419 lines,
committed, all 80 prints std-3 or a subset, zero sorries, no new axiom, no `native_decide`).
Off-Lean: `scripts/w61_wider/` (plain Python, exact integer arithmetic).  Continues
`GQ2/Dyadic/SqCore/GradedFiveStageFour.lean` "Scope, honestly", which named this step and
predicted its difficulty.

---

## 0.  Headline

| question | answer |
|---|---|
| does the gamma-2 identity at class five exist? | **Yes, and it is proved in Lean at every handle count, every handle, and over any commutative ring** (`SqU6.sqRelWord_gaTwoDress`).  Class-two rows: Frobenius `(-4, 2)`.  Class-three rows: Frobenius + class-three Fox pairings.  Class-four and class-five rows: Frobenius + Fox pairings + correction + **quadratic block**. |
| is the quadratic block real? | **Yes.**  `SqU6.gaTwoQuadO` has 52 terms in 10 blocks; it is generically non-zero (1030 of 1200 random unrestricted dressings).  Wave 60's prediction that the identity "WILL carry a quadratic block" is correct. |
| is it even on the achievable lattice? | **YES.**  `SqU6.gaTwoQuadO_even`, PROVED in Lean under wave 60's own hypotheses (`stageN1` on the frame, `stageN2` on the dressing).  So the gamma-2 transport at class five is **affine mod two**, exactly as wave 54 found one class down.  The difficulty the campaign had been anticipating since wave 59 collapses. |
| what survives mod two, then? | **Exactly three channels** (`SqU6.gaTwoShiftChan`): `z.m * L.e`, `z.i * L.j`, `z.l * L.f`, summed over the slots against the permuted letters.  `SqU6.sqRelWord_gaTwoDress_o_channel`: the class-five residue moves by that functional and by **nothing else** mod two - correction, collection element, cross-handle term and quadratic block all die. |
| does that give an exclusion one step wider? | **No, and this is the honest limit.**  The three channels are live at wave 60's point: the functional is odd on six of the ten commutator generators of the achievable lattice.  `SqU6.stageWit_gaTwo_forced` says the residue is forced even *modulo* the functional, which is the exact obstruction and nothing more. |
| is wave 60's exclusion refuted one step wider? | **No.**  None of those ten generators, at any power, on any single slot, kills the dressed frame.  The question is undecided, not settled either way. |
| anything that does NOT go through? | **One row.**  `SqU6.gaTwoQuadN`, the class-four RIGHT quadratic block, is generically ODD on the same lattice (530 of 1200).  The class-five row is affine mod two; the `(2,6)`-row is not. |

---

## 1.  The closed form

Notation.  Frame slots `m = (sigma, x0, x1; U_1, V_1, ...)`; dressings `z_i` in
`gamma_2(SqU6 R) = {a = b = c = d = e = 0}`, ten free coordinates `(f,g,h,i; j,k,l; m,n; o)`.
Write `beta = (x0, 10 x0 - sigma - 8 x1, x1; V_k, U_k)` for the permuted letters, and let
`pair_c(z, L)` be the class-`c` coordinate of `[z, L]` (six forms, `SqU6.gaTwoPairJ` through
`SqU6.gaTwoPairO`, certified equal to the honest commutator forms by
`SqU6.commP_gaTwo_eq`).

> **THE IDENTITY.**  For `z` a five-slot (in general `(3 + 2h)`-slot) `gamma_2` dressing,
> `R(m . z) = R(m) . G` with `G` in `gamma_2` and
>
> ```
> G.f..G.i  = -4 z1.* + 2 z2.*                            (Frobenius only)
>
> G.j..G.l  = -4 z1.* + 2 z2.* + sum_i pair_*(z_i, beta_i)
>                              + sum_k ( pair_*(zu_k, V_k) - pair_*(zv_k, U_k) )
>
> G.m, G.n  = the same, plus corr_{M,N}(m, z) + quad_{M,N}(z)
>             + per-handle blocks + the collection element
>
> G.o       = the same, plus corr_O(m, z) + quad_O(m, z)
>             + per-handle blocks + the CROSS-HANDLE term + the collection element
> ```

Three readings.

* **The two class-four rows are `GradedGammaTwo` verbatim, twice.**  `SqU6.gaTwoCorrM` and
  `SqU6.gaTwoQuadM` are wave 54's `gaTwoCorr` and `gaTwoQuad` transposed through the
  `toU5L`-quotient - all forty-four coefficients and all five - and `SqU6.gaTwoCorrN`,
  `SqU6.gaTwoQuadN` the same through `toU5R`.  Certified verbatim in
  `results/derive.txt` section B.  Only the `(1,6)`-row is genuinely new.
* **The class-five quadratic block is NOT frame-free.**  Wave 54 could argue by weight that a
  term quadratic in the dressings has no room for a frame coordinate: its top row has weight
  four and `2 + 2` fills it.  At class five the top row has weight five, `2 + 2 + 1` fits, and
  `SqU6.gaTwoQuadO` has ten blocks: one frame-free (the two channels `(f, l)` and `(j, i)` with
  the exponent binomials `C(-4,2) = 10`, `C(2,2) = 1`, mixed `-8`), and nine carrying the `a`-,
  `c`- and `e`-columns of the three core slots.
* **The per-handle shifts no longer collect for free.**  At class four a `gamma_3`-shaped handle
  shift is central against the handle word.  At class five `[gamma_3, gamma_2] <= gamma_5` is
  non-trivial (`SqU6.gaThree_past_gaTwo`: the price is `c.j * b.i - b.f * c.l`), so each
  handle's shift pays as it passes the LATER commutators.  The term is a `sqCross`, hence
  strictly triangular and **order-dependent**, the same shape as wave 59's class-five defect.

---

## 2.  Why the quadratic block dies

The hypotheses are wave 60's, unchanged:

```
frame letters in  M_1 = { 2 | z.a  and  2 | z.c }                  (GradedFiveStageFour.stageN1)
dressings     in  M_2 = { gamma_2, 2 | z.f, 2 | z.h, 2 | z.j }     (GradedFiveStageFour.stageN2)
```

and `stageN2_of_commutator` (wave 60) proves `[M_1, M_1] <= M_2`, so `M_2` really is the honest
`gamma_2` of the image subgroup and not a declared lattice.  `forceLcs_one_le_stageN2` names
that step.

The commutator of two `gamma_2`-elements at class five has three coordinates
(`SqU6.gaTwo_commP`):

```
[z, w].m = z.f w.h - z.h w.f        [z, w].n = z.g w.i - z.i w.g
[z, w].o = z.f w.l - z.l w.f + z.j w.i - z.i w.j
```

Three of these four channels - `f`-against-`h`, `f`-against-`l`, `j`-against-`i` - carry a
dressing coordinate that `M_2` makes even.  Only the second, `g`-against-`i`, does not, and it
lives in the `n`-row alone.  That single fact is the whole of the finding: the class-five
quadratic block is even and the class-four right one is not.  The frame-carrying blocks of
`SqU6.gaTwoQuadO` die for the complementary reason: their `a`- and `c`-blocks meet `M_1`
directly, and their `e`-blocks all pair against `f * h`, which `M_2` makes divisible by four.

Certified block by block in `results/parity_blocks.txt`, with the exact halves emitted to
`results/witnesses.txt` and pasted into the Lean proofs mechanically
(`scripts/w61_wider/emit_soundness.py`, `assemble_lean.py`): a 276-term witness is never typed
by hand.

---

## 3.  What is left: the three channels

`SqU6.sqRelWord_gaTwoDress_o_channel` is the sharpest statement of the wave:

> On the achievable lattice the class-five residue of a `gamma_2`-dressed frame differs from the
> undressed one by `SqU6.gaTwoShiftChan` and by nothing else, modulo two.

so a `gamma_2`-level exclusion is exactly as hard as making

```
   z.m * L.e  +  z.i * L.j  +  z.l * L.f
```

vanish mod two for every achievable `z`, summed over the slots.  The three channels are the
three terms of `u6Comm5` the frame does not close.  Compare wave 60's stage-four soundness,
where the same three coordinates `j`, `l`, `m` survive one filtration step narrower: the list is
the same, read one class down on the dressing.

**At wave 60's point the functional is live** (`results/census.txt`).  The ten pairwise
commutators of the letters all satisfy `M_2` (confirming wave 60's chain concretely), and six of
them have an odd channel value on some slot:

| generator | `(i, l, m)` parities | odd channel on slots |
|---|---|---|
| `[U, V]` | `0, 0, 1` | sigma, U, V |
| `[x0, U]`, `[x0, V]`, `[x0, x1]`, `[x1, V]` | `*, 1, *` | x1, U |
| `[x1, U]` | `0, 1, 1` | sigma, x1, V |

None of the ten, at any power and on any single slot, kills the dressed frame.  So wave 60's
exclusion is neither extended nor refuted one filtration step wider; what this wave supplies is
the exact price of extending it.

⚠ **Scope of that census.**  It is over the ten commutator GENERATORS of `[H, H]` and their
powers, not over all of `[H, H]`, and it is single-slot.  A full element-by-element closure was
started and abandoned as too slow for this lane; it is the obvious next measurement.

---

## 4.  Validation

`scripts/w61_wider/`; plain Python, exact integer arithmetic, no sampling in the derivation.

### 4.1  Symbolic (`derive_wider.py`, `derive_blocks.py`, `derive_assemble.py`)

Exact polynomial arithmetic in `SqU6(Z[m, z])` on the engine of `scripts/w59_defect5/u6poly.py`,
whose group law is the committed one of `GradedFive.lean`.

| test | result |
|---|---|
| `[gamma_2, gamma_2]` is `gamma_4`-shaped, `[[gamma_2, gamma_2], gamma_2] = 1` | true, so the shift is at most quadratic |
| the six pairing forms against `[z, L]` | **six exact matches** |
| the handle shift, all fifteen rows | **EXACT** |
| the handle WORD product law, `h = 0, 1, 2, 3` | **EXACT at all four** |
| the collection element, all three rows | **EXACT** |
| the assembled relator identity, `h = 0, 1, 2` | **EXACT, all fifteen rows, at all three** |
| the class-four rows against `GradedGammaTwo` transposed | **VERBATIM** through `toU5L` and `toU5R` |

### 4.2  Against honest 6 x 6 collection (`validate_wider.py`, `results/validate.txt`)

**11 named checks, 0 failures.**

* the transcribed group law vs matrices: 1600 comparisons, 0 mismatches;
* the six pairing forms: 1600 comparisons over `Z`, `Z/4`, `Z/8`, `Z/16`, 0 mismatches;
* `SqU6.gaTwoHandle`: 1600, 0 mismatches;
* `SqU6.gaTwoCore`: 1200, 0 mismatches;
* `SqU6.gaTwoShift`, the five-slot identity: 1200 over four rings at handle counts `0` to `4`,
  0 mismatches; plus 600 more on the `gamma_3` specialisation;
* the soundness by brute force: 3000 achievable dressings, the class-five row equals the channel
  functional mod two, **0 exceptions**; `SqU6.gaTwoQuadO` even at 2400 more, 0 exceptions;
* sharpness: without the hypotheses 734 of 1500 unrestricted dressings move the row oddly; the
  quadratic block is non-zero at 1030 of 1200 unrestricted points; and `SqU6.gaTwoQuadN` is odd
  at 530 of 1200 lattice points.

### 4.3  Kernel cross-check (in Lean)

`gaTwoDress_decide_crosscheck` evaluates both sides of the identity at wave 60's binder point
with a concrete ten-coordinate `gamma_2`-dressing, by `decide` on `ZMod 8`, so the structural
route of sections 2 to 4 and the machine route meet inside the Lean file.

---

## 5.  What is proved and what is measured

**Proved (Lean, this wave, all pins std-3 or a subset):** the `gamma_2`-calculus and its six
pairing forms; the core shift `SqU6.sqWord_mul_gaTwo`; the handle shift
`SqU6.commP_mul_gaTwo`; the handle-word product law `SqU6.handleWord_mul_gaTwo_all` with its
cross-handle term; the assembled `SqU6.sqRelWord_gaTwoDress`; the evenness of every block of the
class-five row (`SqU6.gaTwoQuadO_even`, `SqU6.gaTwoCorrO_even`,
`SqU6.gaTwoPairO_channel_even`, `SqU6.gaTwoHandle_o_channel_even`, and the assembled
`SqU6.gaTwoShift_o_channel_even`); the complete mod-two transport
`SqU6.sqRelWord_gaTwoDress_o_channel`; the achievability step `forceLcs_one_le_stageN2`; and
`SqU6.stageWit_gaTwo_forced` at wave 60's point.  All at every handle count and handle, over any
commutative ring where the statement is ring-generic.

**Measured, not proved:** everything in section 4, and the census of section 3.

**Not attempted:** a point at which the three channels are even (the object a `gamma_2`-level
exclusion needs); the full element-by-element closure of `[H, H]`; five-slot achievable
refinements; and the sharpness of the soundness hypotheses, which - as at stage four - are
sufficient but not shown minimal.

---

## 6.  What the next wave should do

In value order.

1. **Search for a point with even channels.**  The condition is now explicit and cheap to test:
   at a candidate marking, compute `[H, H]` (or just its commutator generators) and ask whether
   `z.m * L.e + z.i * L.j + z.l * L.f` is even for every achievable `z` and the permuted letter
   `L`.  Wave 60's own point fails it on six of ten generators, and the pattern in section 3
   suggests where to look: the odd channels are carried by the letters' `e`-columns and by the
   handle block's class-three rows, so a point with even `(5,6)`-columns is the first thing to
   try.  If one exists with an odd class-five residue, the exclusion goes one filtration step
   wider than wave 60's by the theorems already committed here.
2. **Finish the census.**  The element-by-element closure of `[H, H]` at wave 60's point, and
   the five-slot (not just single-slot) kill test, would settle whether wave 60's exclusion is
   FALSE one step wider.  This wave leaves that open in both directions.
3. **The `(2,6)`-row.**  `SqU6.gaTwoQuadN` is odd on the lattice, so any statement that needs
   the class-four RIGHT row of a `gamma_2`-dressed frame is genuinely quadratic.  Nothing in the
   campaign currently needs it; it is recorded so that no later wave assumes otherwise.
4. **The cross-handle term.**  `SqU6.gaTwoHandleSum`'s `sqCross` block is order-dependent, like
   wave 59's defect.  It is even on the lattice, so nothing here depends on the handle ORDER;
   but any `gamma_2`-level statement away from the lattice will.

---

## 7.  Reproduction

Working directory `scripts/w61_wider/`; plain Python 3, no dependencies.

```
derive_wider.py     the raw shifts and their shapes                       -> results/derive.txt
derive_split.py     the pure class-two half, for size comparison          (diagnostic)
derive_blocks.py    the named blocks, each certified by subtraction       (diagnostic)
derive_assemble.py  the handle-word law and the assembled identity        -> results/assemble.txt
parity.py           the mod-two reduction on the achievable lattice       -> results/parity.txt
parity_blocks.py    block-by-block evenness + the exact halves            -> results/parity_blocks.txt
                                                                          -> results/witnesses.txt
emit_lean.py        the Lean defs and the matching Python evaluator       -> results/lean_defs.txt
                                                                          -> forms.py
emit_soundness.py   the Lean soundness lemmas with their witnesses        -> results/lean_soundness.txt
assemble_lean.py    splices section 5 into the Lean file                  (writes the .lean)
validate_wider.py   every form vs honest 6 x 6 collection, four rings     -> results/validate.txt
census_fast.py      the three channels at wave 60's point                 -> results/census.txt
wlib.py             the shared closed forms (imported by the above)
```

Verification of the Lean file, from the worktree root:

```
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true \
  GQ2/Dyadic/SqCore/GradedFiveGammaTwo.lean
```

zero errors, zero warnings, 80 axiom prints, every one a subset of
`[propext, Classical.choice, Quot.sound]`.  The module is not yet registered: `GQ2.lean` needs
`import GQ2.Dyadic.SqCore.GradedFiveGammaTwo` next to the other `SqCore` imports.

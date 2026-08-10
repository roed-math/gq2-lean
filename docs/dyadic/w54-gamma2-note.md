# W54: the gamma-2 torsor transport at class four, and a correction to the W53 dead end

**Wave W54, worker W54-GAMMA2.**  Lean: `GQ2/Dyadic/SqCore/GradedGammaTwo.lean` (693 lines,
committed, all prints std-3 or a subset).  Off-Lean: `scripts/w54_gamma2/` (Magma V2.29-4,
local).  Continues `GQ2/Dyadic/SqCore/GradedContainFour.lean` "Honest scope": the located
remaining gap, the `gamma2`-torsor transport of the class-four residue.

---

## 0.  Headline

| question | answer |
|---|---|
| what is the exact class-four defect of a `gamma2` dressing? | **Frobenius + graded Fox + correction + a quadratic form** (§1).  The class-four row moves by `-4 z1.j + 2 z2.j`, the class-four commutator pairing `[z_i, beta_i]` of each dressing against its permuted letter, an explicit correction block quadratic in the frame's own columns, and the genuinely quadratic form `Psi(z)` whose coefficients are the exponent binomials `C(-4,2) = 10`, `C(2,2) = 1` and the `gamma2` commutator pairing `z.e w.g - z.g w.e`.  Validated symbolically at `h = 1, 2`: **ten zero rows, 0 mismatches**, plus 300 random points x random five-slot dressings against honest group collection, **0 mismatches**. |
| is the quadratic form the thing that unlocks the corners? | **No.**  Every generator of the achievable lattice has EVEN `g` (forced by the four parity rows), so `Psi` is always even, and the exponent-slot `gamma4` freedom absorbs it.  The `gamma2` transport is a **mod-2 affine** phenomenon (§2.3). |
| what unlocks them, then? | **Three moves the committed `Lam3` carries only in doubled form** (§3).  The commutators of the witness `x1`-slot letter against `sigma`, `U`, `V` are `gamma3`-SHAPED elements of `gamma2(im Phi)` with `(h, i)` data `(0, R)`, `(P C - Q A, Q E)`, `(P D - Q B, Q F)`.  `selLamThree` contains exactly their doubles, because it pairs `x1^{-2}` in `Lam5` against the letters instead of `x1` itself.  They are honest commutators of two frame slots, hence `gamma2`-level dressings, and they disturb no lower row. |
| does the transport reach the uncovered corners? | **Most of them** (§4).  Of the `131072` binder points where the bare witness survives stage 3 with an odd class-four residue, the committed engine covers `16384` (12.5 %); the three new moves cover a further `80896`, taking coverage to `97280` (**74.2 %**). |
| and the rest? | **`33792` corners are certified dead at the `gamma2` level, exhaustively** (§5).  At every one of them the FULL achievable increment lattice of `gamma2(im Phi)`, quadratic terms included, meets the residue line in `2 Z/8`: every stage-preserving achievable increment is even, so an odd residue survives.  Of these, `18432` would die under an unrestricted `gamma2` dressing (their obstruction is achievability), and `15360` resist every `gamma2` move whatever. |
| structure of the residual set? | **`A` and `B` both even.**  All ten mod-2 classes of the `33792` have `A = B = 0 mod 2` (and `P = R = 1 mod 2`), which is exactly the condition killing the six new pairings (§5.2). |
| a correction to W53 | **`GradedContainFour`'s "provable dead end" is a dead end of the ENGINE, not of the tower.**  At its recorded corner `(A..S) = (0,1,1,1,2,0,2,0)`, halves `(1,3,1)`, the odd residue `5` is killed by the fifth power of `[sigma, x1]` on the `U`-handle slot, by honest group collection and now by `decide` in Lean (§3.3).  The obstruction theorem is not contradicted: it quantifies over `selLamThree`, and the move lies outside it. |

---

## 1.  The closed form

Notation.  Frame slots `m = (s, x, y; u_1, v_1, ..., u_h, v_h)` = `(sigma, x0, x1; U, V, ...)`;
dressings `z_i` in `gamma2(SqU5 R) = {a = b = c = d = 0}`, six free coordinates
`(e, f, g, h, i, j)`.  Write

```
[z, L]_4  = z.h L.d - z.i L.a + z.e L.g - z.g L.e + z.g L.a L.b - z.f L.a L.d   ( = u5Comm4(z, L) )
<z, L>_L  = z.e L.c - z.f L.a                <z, L>_R  = z.f L.d - z.g L.b
sigma*    = 10 x - s - 8 y                   (columnwise; the sigma letter mod 2)
```

and let the Fox rows be the permuted letters `beta = (x, sigma*, y; v_k, u_k)`, the
`(sigma x0)(u v)` permutation of W52-VANISH §1.1 with `x1` fixed.

> **THE IDENTITY.**  For `z` a five-slot (in general `(3 + 2h)`-slot) `gamma2` dressing,
> `R(m . z) = R(m) . G` with `G` in `gamma2` and
>
> ```
> G.e = -4 z1.e + 2 z2.e      G.f = -4 z1.f + 2 z2.f      G.g = -4 z1.g + 2 z2.g
>
> G.h = -4 z1.h + 2 z2.h + <z0, x>_L + <z1, sigma*>_L + <z2, y>_L
>                        + sum_k ( <zu_k, v_k>_L - <zv_k, u_k>_L )
>
> G.i = -4 z1.i + 2 z2.i + <z0, x>_R + <z1, sigma*>_R + <z2, y>_R
>                        + sum_k ( <zu_k, v_k>_R - <zv_k, u_k>_R )
>
> G.j = -4 z1.j + 2 z2.j + [z0, x]_4 + [z1, sigma*]_4 + [z2, y]_4
>                        + sum_k ( [zu_k, v_k]_4 - [zv_k, u_k]_4 )
>                        + corr(m, z) + Psi(z)
>                        + sum_k ( -c_k.g (zu_k.e + zv_k.e) + c_k.e (zu_k.g + zv_k.g) )
>                        + H.g (-4 z1.e + 2 z2.e) - H.e (-4 z1.g + 2 z2.g),
> ```
>
> where `c_k = [u_k, v_k]` and `H = handleWord(m)`, so `c_k.e = u_k.a v_k.b - u_k.b v_k.a`,
> `c_k.g = u_k.c v_k.d - u_k.d v_k.c`, `H.e = sum_k c_k.e`, `H.g = sum_k c_k.g`, and
>
> ```
> Psi(z) = (z0.e z1.g - z0.g z1.e) + 10 z1.e z1.g - 8 z1.e z2.g + z2.e z2.g
>          + sum_k ( zu_k.e zv_k.g - zu_k.g zv_k.e ).
> ```

Three readings.

* **The class-three rows are the committed class-three shift.**  `G.h` and `G.i` are exactly
  `GradedVanish.vanShift` transported through the two `U4`-quotients `toU4L` (coordinates
  `a, b, c, e, f, h`) and `toU4R` (`b, c, d, f, g, i`).  Certified separately (T4 below).
  Nothing new happens at class three.
* **The class-four row is the graded Fox form with two corrections.**  `[z, L]_4` is literally
  the class-four commutator form `u5Comm4` restricted to `gamma2`, so the leading block is
  `sum_i [z_i, beta_i]` exactly as the memo's `delta(z) = sum_i [z_i, beta_i] + F(z_{x1})`
  predicts, with the Frobenius on the exponent slots.  The remaining blocks are collection
  artefacts: `corr` is the pairing of a dressing against the class-two data of the SUFFIX of
  its own occurrences (it is a polynomial in the frame's columns only, with no dressing
  cross terms), the `c_k` block is the same artefact inside a handle commutator, and the last
  line is the price of commuting the core shift past the handle word.
* **`Psi` is `m`-free, and it is the whole quadratic content.**  By weight (`a..d` weight 1,
  `e, f, g` weight 2, `h, i` weight 3, `j` weight 4) a term quadratic in the dressings has no
  room for a frame coordinate.  The self terms are the exponent binomials `C(n, 2)` at
  `n = -4` and `n = 2` (`z^n.j = n z.j + C(n,2) z.e z.g` for `z` in `gamma2`), the cross terms
  are the `gamma2` commutator pairing `[z, w].j = z.e w.g - z.g w.e`.

The nine correction coefficients (`corr(m, z) = sum` of the dressing coordinate times the
polynomial shown; `s, x, y` the three core slots):

| coordinate | coefficient |
|---|---|
| `z0.e` | `-s.c x.d + s.d x.c - 4 x.c x.d + 2 x.c y.d + y.c y.d` |
| `z0.f` | `8 x.a x.d - 2 x.a y.d - 2 x.d y.a - 2 y.a y.d` |
| `z0.g` | `s.a x.b - s.b x.a - 4 x.a x.b + 2 x.b y.a + y.a y.b` |
| `z1.e` | `3 s.c x.d - 2 s.c y.d + s.d x.c - 20 x.c x.d + 20 x.c y.d - 4 y.c y.d` |
| `z1.f` | `2 s.a s.d - 14 s.a x.d + 10 s.a y.d - 14 s.d x.a + 10 s.d y.a + 130 x.a x.d - 100 x.a y.d - 100 x.d y.a + 80 y.a y.d` |
| `z1.g` | `-2 s.a s.b + 11 s.a x.b - 8 s.a y.b + 13 s.b x.a - 10 s.b y.a - 110 x.a x.b + 80 x.a y.b + 100 x.b y.a - 76 y.a y.b` |
| `z2.e` | `-2 s.c y.d + s.d y.c` |
| `z2.f` | `s.a y.d + s.d y.a` |
| `z2.g` | `s.a y.b - 2 s.b y.a` |

At the committed class-four witness every one of the nine is **even** (`s = sigma` has
`a = c = d = 0`, `y = x1` has `a = b = c = d = 0`, and `x.a = 2P`, `x.c = -2Q`, `x.d = 2W2`
by the four parity rows), and so are `c_k.e = -2P`, `c_k.g = -2R` and the collection term.
So at the witness the whole mod-2 content of the class-four defect is the graded Fox block.

---

## 2.  Validation

### 2.1  Symbolic (`w54_shift.m`)

Exact polynomial arithmetic in `U5(R)` over `Z[m, z]`, seven frame slots at ten coordinates
and seven `gamma2` dressings at six, matching `GradedFour.lean` coordinate by coordinate.

| test | result |
|---|---|
| T0 group sanity | true |
| T1 core block, all ten rows, against the conjectured form | **ten zeros**; the correction residual rebuilt exactly (`0`) |
| T2 handle block, all ten rows | **ten zeros** |
| T3 assembled relator identity at `h = 1` | **ten zeros** |
| T3 assembled relator identity at `h = 2` | **ten zeros** |
| T4 `h`-row against `toU4L(vanShift)`, `i`-row against `toU4R(vanShift)`, `h = 1, 2` | **0, 0, 0, 0** |

### 2.2  Numeric, against honest collection (`w54_lat.m` L0, `w54_gate.m` Q0)

* the six-coordinate increment `(G.e, G.f, G.g, G.h, G.i, G.j)` computed from the closed
  form against `R(m)^{-1} R(m . z)` computed by group collection, at **300** random binder
  points with a random `gamma2` dressing on **every** slot: **0 mismatches**;
* the committed class-four closed forms (`w53_gate.m`'s `candH`, `candI`, `cand`) at 400
  random binder points: all OK;
* the three new generators against honest commutators of frame slots at 400 points: all OK;
* 11 explicit kills of odd residues by the new moves, checked by collection: all OK.

### 2.3  The quadratic form is even on the achievable lattice

Every generator of `gamma2(im Phi)` has even `g`-column: the commutators of frame slots have
`g` equal to `0`, `C F - E D = -2R`, `(D T - C S) E - (F T - E S) C = -2QE - 2 W2 C`,
`(D T - C S) F - (F T - E S) D`, all even by the parity rows `hg`, `he`, `hb`; the `x1`-square
has `g = 2R`; triple commutators are `gamma3`-shaped.  `g` is additive on products of
`gamma2` elements, so the whole lattice has even `g`.  Asserted at every point of the census:
**true** at all `33792` residual corners and at all `520` sampled covered corners.
Consequently `Psi` is even, and since `-4 w1.j + 2 w2.j` runs over `2 Z/8`, the parity of the
achievable class-four increment is a **linear** function of the dressing.

---

## 3.  The transport: three moves outside the committed lattice

### 3.1  The generators

Over `Z/8[A..R]`, at the committed witness frame, the three commutators of the `x1`-slot
letter are `gamma3`-SHAPED (all of `e, f, g` vanish):

```
[sigma, x1] = (h, i, j) = ( 0,            R,     0 )
[x1, U]     =             ( P C - Q A,    Q E,   -2 A E Q - B E Q )
[x1, V]     =             ( P D - Q B,    Q F,   -A F Q - 2 B F Q + B S R )
```

The committed `selLamThree` carries `(0, 2R)`, `2 (Q A - P C, R T - Q E)` and
`2 (Q B - P D, R S - Q F)`: **exactly the doubles** (the `(R T, R S)` discrepancy is the
`b`-column of the abstract letters `(A, T, C, E)`, `(B, S, D, F)` against the frame's own
`U = (A, 0, C, E)`, `V = (B, 0, D, F)`; it does not affect any parity).  The factor 2 enters
because `Lam5` is generated using `x1^{-2}`, a square, rather than `x1` itself.  But
`[sigma, x1]` is a commutator of two frame slots, so it lies in `[im Phi, im Phi] =
gamma2(im Phi)`, which is the image of `gamma2` of the ambient group under the test hom.  It
is therefore a legitimate dressing, and a `gamma2`-LEVEL one: it is not in `gamma3(im Phi)`,
which is what `selLamThree` models.

### 3.2  Why they cost nothing

A `gamma3`-shaped dressing contributes `0` to `G.e`, `G.f`, `G.g`, `G.h` and `G.i` (those rows
read only the dressing's class-two data), and contributes `z.h L.d - z.i L.a` to `G.j`.  So
these three moves are stage-preserving by construction, and the committed translation identity
`sqRelWord_selLift` governs them verbatim.  Their pairings against the handle columns are

```
U-slot:  z.h F - z.i B            V-slot:  A z.i - E z.h
```

giving the **six new pairings** `-R B`, `A R`, `(P C - Q A) F - Q E B`, `A Q E - E (P C - Q A)`,
`(P D - Q B) F - Q F B`, `A Q F - E (P D - Q B)`.

### 3.3  The recorded dead end, killed

At `(A, B, C, D, E, F, T, S) = (0, 1, 1, 1, 2, 0, 2, 0)` with halves `(P, Q, R) = (1, 3, 1)`,
the corner `GradedContainFour` certifies as a provable engine dead end: the witness is a
stage-3 survivor with odd residue `5`, all eight committed generator pairings are even
(`[6, 6, 0, 0, 0, 2, 2, 4]`), and `[sigma, x1] = (0, 1)`.  The new pairing is `-R B = 7`, a
unit; the move `(h, i) = (0, 5 R) = (0, 5)` on the `U`-handle slot kills the relator.
Verified by honest group collection (`w54_inst.m`) and committed by `decide` in Lean.  A
second, independent corner `(0, 1, 1, 1, 2, 4, 2, 0)`, halves `(1, 3, 3)`, residue `7`, runs
the same way.

---

## 4.  The census (`w54_gate.m`)

Whole binder: all `(A, ..., S)` in `(Z/8)^8` with the four adjacency differences even, halves
`P, Q, R, W2` the canonical lifts; `4194304` points.

| set | count |
|---|---|
| odd class-four residue | 737280 |
| ... covered by a committed `Lam3` pairing | 196608 |
| ... covered by a new `gamma2`-level pairing | 638976 |
| ... covered by both | 196608 (so `Lam3`-covered is a subset) |
| ... covered by neither | 98304 |
| bare-witness stage-3 survivors | 1806336 |
| ... odd residue | 131072 |
| ...... `Lam3`-covered | **16384** |
| ...... `gamma2`-covered | **97280** |
| ...... neither | **33792** |
| ... even residue | 1675264 |
| ...... 2-live under `Lam3` | 531456 |
| ...... 2-live under `Lam3` + the new pairings | **848896** |

Reading: on the odd stage-3 locus the `gamma2` transport takes coverage from **12.5 %** to
**74.2 %**; on the even locus the live fraction goes from 31.7 % to 50.7 %.

---

## 5.  The residual corners, exhaustively (`w54_lat.m`, `w54_dead.m`)

### 5.1  The verdict

For every one of the `33792` residual corners the exact achievable increment lattice was
computed: for each slot and each generator of `gamma2(im Phi)` (the ten frame-slot
commutators, the fifty triple commutators, the `x1`-square and its five commutators) the
six-vector `(G.e, G.f, G.g, G.h, G.i, G.j)` of the closed form, then the `Z/8`-span `S` in
`(Z/8)^6`, then `S` intersected with the last coordinate axis.  An odd residue dies iff that
intersection is the whole of `Z/8`.

| model | corners killed (of 33792) | intersection order |
|---|---|---|
| `gamma2(im Phi)`, the honest achievable lattice | **0** | `4` at every corner |
| free `gamma2` (every element of `gamma2(U5(Z/8))` allowed) | **18432** | `4` at 15360, `8` at 18432 |

Cross-checks at 60 + 60 corners covered by the committed and by the new pairings: intersection
order `8` at all 120, killed at all 120.

So: **`33792` corners are dead at the `gamma2` level, and this is certified, not sampled.**
Of them, `15360` are dead for ANY `gamma2` dressing whatever (a model-independent statement),
and `18432` are dead only because of achievability.

### 5.2  Their structure

The `33792` fall into exactly **10 mod-2 classes** of `(A, B, C, D, E, F, T, S, P, Q, R, W2)`:

```
[0,0,0,0,0,1,0,1,1,1,1,*]   [0,0,0,0,1,0,1,0,1,1,1,*]   [0,0,0,0,1,1,1,1,1,1,1,*]
[0,0,0,1,0,0,0,1,1,*,1,1]   [0,0,1,1,0,0,1,1,1,*,1,1]
```

All ten have `A = B = 0` and `P = R = 1` mod 2.  That is exactly the mechanism: the six new
pairings all carry a factor `A` or `B` (through the handle columns `(F, B)` and `(A, E)`), so
they are even as soon as `A` and `B` both are, whatever `R` does.

---

## 6.  What is measured and what is proved

**Proved (Lean, this wave, `GradedGammaTwo.lean`, all pins std-3 or a subset):**

* the `gamma2`-calculus: `gaTwoPair_eq_u5Comm4`, `gaTwo_swap`, `SqU5.handleWord_b/_c/_e/_g`,
  `SqU5.handleWord_isGaTwo`;
* the translation identity: `sqWord_mul_gaTwo`, `commP_mul_gaTwo`, `handleWord_mul_gaTwo_all`,
  and the assembled `sqRelWord_gaTwoDress`, over any commutative ring and at any handle count,
  with no hypothesis beyond `IsGaTwo` on the dressings;
* the three generators in closed form as honest commutators of witness frame slots:
  `selLiftWit_commP_zero_two`, `_two_handleU`, `_two_handleV`;
* the extended lattice `selLamThreePlus` with `selLamThree_plus` (containment) and the
  transport theorems `selLiftWit_complete_odd_plus`, `_plus'`, `_rb`, `_ar`;
* the recorded dead-end corner killed end to end, by `decide`.

**Modelled, not proved:** that a commutator of two frame slots is an admissible dressing.
The justification is that the test hom carries `gamma2` of the ambient group onto `gamma2` of
its image, so `[im Phi, im Phi]` is exactly the set of class-two moves visible in the test
group.  This is the same convention under which `selLamThree` was derived (it is
`gamma3(im Phi)`); the present observation is that `gamma2(im Phi)` is strictly bigger in the
`(h, i)`-direction, by the three halves of §3.1.

**Measured (this wave, exact arithmetic over `Z/8` and over `Z[m, z]`, no sampling in the
census):** the closed form (§2.1, §2.2), the even-`g` property (§2.3), the whole-binder census
(§4, exhaustive over all `4194304` binder points), and the residual verdict (§5, exhaustive
over all `33792` residual corners, both models).  The only sampled things are the honest
collection cross-checks (300 + 400 + 11 + 120 events, 0 failures).

**Not measured:** handle counts `h > 2` for the symbolic identity (proved in Lean for all `h`,
so this is not a gap), the even-regime (`2`-pairing) transport beyond the counts in §4, and
the effect of the mod-4 freedom in the halves `P, Q, R, W2` (the census uses the canonical
lift, as W53 did).

---

## 7.  What the next wave should prove

In value order.

1. **The residual obstruction, as a theorem.**  The exact statement, the `gamma2`-analogue of
   `GradedContainFour.sqRelWord_selLift_ne_one`:

   > Let `Lam2` be the achievable `gamma2` lattice (the `(e, f, g, h, i)`-span of the
   > frame-slot commutators, their pairings against the slots, and the `x1`-square).  At a
   > binder point where the eight committed generator pairings **and** the six new pairings of
   > §3.2 are even, let `m` be a frame with `sqRelWord m = liftC res`, `selPar res = 1`, and
   > let `z` be any `Lam2`-tuple with `(sqRelWord (conFourDress m z)).e = .f = .g = .h = .i = 0`.
   > Then `sqRelWord (conFourDress m z) != 1`.

   The proof is now fully mapped: (i) every `Lam2` element has even `g` (§2.3, from the four
   parity rows), so `gaTwoQuad` is even; (ii) preserving the class-two rows forces `(z 2).e`
   and `(z 2).g` even, so the `x1`-slot Fox pairing is even; (iii) `gaTwoCorr` and the handle
   and collection corrections are even at the witness (§1); (iv) the surviving Fox pairings are
   the fourteen hypotheses.  Only (i) and (iii) need new Lean, and both are parity-row
   `linear_combination` arguments in the style of `selLamThree_pair_even`.  This would turn
   the exhaustive §5 measurement into the campaign's first `gamma2`-level obstruction theorem
   and pin the class-four frontier exactly: `A` and `B` both even is where the tower stops
   being able to repair itself at level two.

2. **Replace `selLamThree` by the honest `gamma3(im Phi)`.**  `selLamThree` should be
   re-derived as the `(h, i)`-image of `gamma2(im Phi)` rather than of `Lam5` paired against
   letters, i.e. `selLamThreePlus` should become the definition.  Every committed theorem that
   quantifies over `selLamThree` stays true (the lattice only grows in the completion
   direction), except `sqRelWord_selLift_ne_one`, whose hypotheses must be strengthened by the
   six new pairings; §4 quantifies the change (`16384` to `97280` covered corners).

3. **Erratum pointer in `GradedContainFour`.**  Its "Honest scope" and its final concrete
   instance call the corner `(0,1,1,1,2,0,2,0)` a provable dead end.  That is correct as
   stated (relative to `selLamThree`) but reads as a statement about the tower; it should cite
   this note.  Nothing else in that file is affected: the containment, the translation
   identity and the two-regime completions all stand.

4. **The `15360`.**  The corners that resist even an unrestricted `gamma2` dressing are the
   real frontier.  They need either a `gamma1`-level move (a change of the level-one marking
   inside the selection family, i.e. a different stage-A survivor) or a different stage-three
   completion.  The next reconnaissance target is the analogue of this file's §5 one level
   further out: is the class-four residue at those corners killed anywhere on the stage-A
   torsor?

---

## 8.  Reproduction

Working directory `scripts/w54_gamma2/`; no shared preamble.

```
w54_shift.m   the closed form: derivation of the correction block and validation      (~1 s)
              magma -b w54_shift.m           -> results/w54shift.txt
w54_probe.m   the first probe of the dead-end corner, honest collection only          (~1 s)
              magma -b w54_probe.m
w54_inst.m    the three generators over Z/8[A..R]; the two dead-end corners killed    (~1 s)
              magma -b w54_inst.m            -> results/w54inst.txt
w54_gate.m    validation vs honest collection + the whole-binder census               (~100 s)
              magma -b w54_gate.m            -> results/w54gate.txt
w54_lat.m     the exact increment lattice: validation, and verdicts on samples        (~45 s)
              magma -b w54_lat.m             -> results/w54lat.txt
w54_dead.m    the residual corners exhaustively, under both dressing models           (~45 min)
              magma -b w54_dead.m            -> results/w54dead.txt
results/      committed outputs quoted above
```

Verification of the Lean file, from the worktree root:

```
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true \
  GQ2/Dyadic/SqCore/GradedGammaTwo.lean
```

zero errors, 36 axiom prints, every one a subset of `[propext, Classical.choice, Quot.sound]`.
The module is not yet registered: `GQ2.lean` needs
`import GQ2.Dyadic.SqCore.GradedGammaTwo` next to the other `SqCore` imports.

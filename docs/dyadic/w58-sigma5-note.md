# W58: the class-five sigma reading, the `a0 = a1` forcing decided, and why the handle block is still invisible

**Wave W58, worker W58-SIGMA5.**  Off-Lean: `scripts/w58_sigma5/` (plain Python, exact integer
arithmetic, certified outputs in `scripts/w58_sigma5/results/`).  Lean:
`GQ2/Dyadic/SqCore/GradedSigmaFive.lean` (the class-**four** half of the finding, which stands
on the committed carrier alone).  Discharges the residual of
`GQ2/Dyadic/SqCore/GradedSigmaFour.lean` section 7 and re-prices the question
`GQ2/Dyadic/SqCore/GradedFourCleared.lean` section 2 left open.

---

## 0.  Headline

| question | answer |
|---|---|
| **(c) does the handle block become visible at class five?** | **NO, but wave 57's cancellation does NOT recur.**  At class four the block cancels out of the dressing response *identically*, over any ring and any marking.  At class five it does not: the response is `sigFiveRead(v,x,y) + sigFourH(v,x) * H_46`, an honest coupling term.  It dies mod 2 for a different reason, and one that needs no gauge: `H_46` is the block's `(4,6)` coordinate, the relator pins the block to the core word's inverse, and the core word's `(4,6)` row is `y_45 * y_56` mod 2 while the relator's own abelian rows force `y_45` and `y_56` even.  So the block is forced even exactly where the class-five bit reads it, at every handle count, on every row, gauge or no gauge. |
| how far does that go? | **Classes four, five, six and seven are all handle-blind on the class-two-forced gauge**; the first arithmetic opening is **class eight** (§4.3).  The load-bearing fact is not an identity but the parity of the *forced* block, so the `h >= 1` route is not bought by climbing one more level. |
| **(b) does the `a0 = a1` forcing become visible?** | **YES.**  ⭐⭐ At every relator-killing marking the class-five response to the sweep's forced dressing is exactly `x_{12} * y_{24} * y_{46} + x_{56} * y_{13} * y_{35}` (mod 2).  At class four the same quantity is **identically zero** (proved in Lean, `sigFourRead_diag_even`).  The second channel runs on the `x0`-slot's fifth abelian column `x_{56}`, a matrix entry `U_5` does not have, so no class-four hypothesis constrains it. |
| is there a point? | **Yes, explicit** (§3).  A marking satisfying the whole class-two-forced gauge as `GradedSigmaFour` states it, at which the `a0 = a1` dressing kills **all fourteen lower rows** and leaves the **odd** class-five residue `7`, while the class-four row of the same dressed relator is `0`.  Soundness measured: `|gamma_3(im)| = 16384`, `|gamma_4(im)| = 128`, `|gamma_5(im)| = 4`, every element even in the coordinate the increment reads, and no achievable refinement flips the parity. |
| **(a) the class-five reading** | ⭐⭐ `sigFiveRead`, 135 terms over `Z`, thirteen dressing channels, machine-emitted into `scripts/w58_sigma5/sigfive_forms.py` and certified against honest `U_6` collection: **300000 row comparisons, 0 mismatches**.  On the class-two-forced gauge it collapses to **eight** monomials with **four** live linear channels `v_{12}, v_{56}, v_{13}, v_{46}` (class four had three), one quadratic cross-term, and, new at this level, two `x1`-slot terms. |
| what makes the escape possible | **A live handle block, live in the `x_{15}` row** (§3.3).  With a *dead* block the relator forces the core word trivial, hence `x_{12}` even and `y_{13} * y_{35}` even (the `x_{15}` row `x_{12} x_{35} + y_{13} y_{35}` has nothing to cancel against), and both channels of the response close.  The separating point's block has `[U, V]_{15} = 3`.  So the block never enters the bit and is indispensable to the point. |

**PROVED (Lean, `GradedSigmaFive.lean`)**: the class-four diagonal statements, sharply.
**MEASURED (`scripts/w58_sigma5/results/`)**: everything about class five.  No class-five Lean
is offered: the carrier is the concurrent W58-FIVE lane's, and premature Lean would be worse
than none.

---

## 1.  The carrier and the marking

`SqU6 = U_6(R)`, fifteen strictly-upper entries, the mechanical continuation of `GradedFour`'s
`SqU5`.  Coordinates in the campaign's class-graded naming:

```text
index  0  1  2  3  4   5  6  7  8   9 10 11  12 13  14
name   a  b  c  d  e   f  g  h  i   j  k  l   m  n   o
entry 12 23 34 45 56  13 24 35 46  14 25 36  15 26  16
```

`gamma_2 = {a..e = 0}`, `gamma_3` adds `f..i = 0`, `gamma_4` adds `j,k,l = 0`, `gamma_5` is the
centre `{only o}`.  Two `U_5` quotients: `toU5L` (drop row/column 6) and `toU5R` (drop row/column
1); both are homomorphisms onto the **committed** `SqU5`, certified in
`results/derive_sigma5.txt` section 1.

The class-five sigma marking is `sigFiveMark = E_23`, the unique lift with
`toU5L(sigFiveMark) = sigFourMark`, and `nu'`-triviality of a dressing is again `v.b = 0`.

⭐ **The committed class-four witness lifts coordinatewise and already kills all fifteen rows.**
`x0 = <a=2, k=1>`, `x1 = <f=1, h=4, k=2>`, letters `<a=1>` and `<a=2>`: the relator dies at every
handle count `h = 1..4` and every handle, and the three committed verdicts (`1`, residue `2`,
residue `1`) reappear in the `(1,5)` row.  The class-five row is **zero** at all three there:
every live coefficient of the class-five reading vanishes at that point, so the lift alone sees
nothing new.

---

## 2.  The class-five reading

⭐⭐ **`sigFiveRead(v, x, y)`** is the amount by which the top row `x_{16}` of
`sqWord(sigFiveMark * v, x, y)` moves.  135 monomials over `Z`; the full form is printed in
`results/derive_sigma5.txt` section 2.  The response of the other fourteen rows:

| row | class | response |
|---|---|---|
| `x12, x23, x34, x45, x56` | 1 | `0` |
| `x13, x24` | 2 | `0` |
| `x35` | 2 | the committed `sigFourG` |
| `x46` | 2 | `v.d * x.e - v.e * x.d` (new) |
| `x14` | 3 | the committed `sigFourH` |
| `x25` | 3 | the committed `sigFourI` |
| `x36` | 3 | new, 14 terms |
| `x15` | 4 | ⭐ the committed `sigFourRead`, **verbatim** |
| `x26` | 4 | new, 20 terms |
| `x16` | 5 | ⭐⭐ `sigFiveRead`, 135 terms |

The `(1,m)` entry of a product only sees the `(1..m)` corner, on which the marking restricts to
the class-`(m-1)` one; so the class-`c` reading is literally the `(1, c+1)` row of the
class-`(c+1)` one and nothing is ever lost by climbing.  That is the structural fact the whole
note rests on.

### 2.1  The gauge collapse

Naming, because the distinction decides everything below.  The **committed** gauge is
`GradedSigmaFour.sigFourRead_gauge`'s hypothesis set verbatim: `x_{12}, x_{34}, x_{45}` even,
`x_{13}, x_{24}` even, the `x1`-slot's abelian columns even.  The **extended** gauge adds the one
hypothesis class four cannot state, `x_{56}` even, and the **honest** form of it replaces the
class-two evennesses by vanishing (the `x0`-slot is `U^{-S} V^T` times a `gamma_3` element).  The
collapse below is on the extended gauge; section 3 is where the difference bites.

```text
ext     : v.a*x36 + v.a*x26 + v.e*x15 + v.f*x36 + v.i*x14 + v.j*x46
        + v.a*v.e*x35 + v.a*v.e*x25 + v.a*v.g*x46 + v.a*y24*y46
        + v.c*v.f*x46 + v.e*v.f*x35 + v.e*y13*y35                        (mod 2)

honest  : v.a*(x36 + x26)  +  v.e*x15  +  v.f*x36  +  v.i*x14
        + v.a*v.e*x25  +  v.a*y24*y46  +  v.e*y13*y35                    (mod 2)
```

| | class four | class five |
|---|---|---|
| live linear channels | `v_{12}`, `v_{45}`, `v_{13}` | `v_{12}`, `v_{56}`, `v_{13}`, `v_{46}` |
| their coefficients | `x_{35} + x_{25}`, `x_{14}`, `x_{35}` | `x_{36} + x_{26}`, `x_{15}`, `x_{36}`, `x_{14}` |
| nonlinear in the dressing | no | **yes**: `v_{12} v_{56} x_{25}` |
| the `x1` slot in the bit | no | **yes**: `v_{12} y_{24} y_{46}`, `v_{56} y_{13} y_{35}` |

`v_{46}` is the sharp one: it is a class-two coordinate at a matrix entry `U_5` does not possess,
so it is a character of the sigma dressing that class four cannot express at all.  Three explicit
points where a single channel is live, and the class-five bit is one clean character, are in
`results/instance_sigma5.txt` section B (`selPar v_{46}`, `selPar v_{56}`, `selPar v_{12}`;
4000 dressings each, 0 mismatches).

---

## 3.  (b) the `a0 = a1` forcing, decided

The depth sweep's forced sigma dressing is `v = x`, the `x0`-slot value itself
(`GradedSigmaFour.sigFourRead_gauge_sigma_eq_x0`).

### 3.1  The exact obstruction, at both levels

Impose **only** the relator's own abelian rows.  Over `gr3R = ZMod 8` the row
`-4 * x_col + 2 * y_col = 0` forces every abelian column of the `x1` slot even, and then

> ```text
> class four :   sigFourRead(x, x, y)  is EVEN, identically.
> class five :   sigFiveRead(x, x, y)  =  x_{12} * y_{24} * y_{46} + x_{56} * y_{13} * y_{35}   (mod 2).
> ```

The class-four half is now **proved**: `GradedSigmaFive.sigFourRead_diag_even` needs only the
three `x1`-slot evennesses, against eight hypotheses in the committed
`sigFourRead_gauge_sigma_eq_x0`, and `sigFourRead_diag_even_of_abelRows` discharges even those
from the abelian rows.  So class four is blind to `a0 = a1` **at every relator-killing marking**,
on the gauge or off it: there is no class-four channel to open.  Section 7 of `GradedSigmaFour`
was right that the piece needs class five, and this says why in a form the tree can use.

The class-five half is a **nonzero** functional.  Census: over `120000` markings with vanishing
abelian rows the closed form matches the honest group evaluation with `0` mismatches, and the
response is odd on `26135` of them (21.8 %); restricted to the `7502` where **all four** abelian
columns of the `x0` slot are even (the extended gauge), it is odd on **none**.  The
class-two-forced gauge of `GradedSigmaFour` constrains `x_{12}, x_{34}, x_{45}`; `x_{56}` is the
escape, and it is a column `U_5` does not have, so the committed gauge cannot mention it.
Symbolically, on the **committed** gauge the diagonal reduces to exactly `x_{56} * y_{13} * y_{35}`
(`results/derive_sigma5.txt` section 4), and on the **extended** gauge to `0`.

### 3.2  The separating point

```text
U   = <a=1, c=2, d=3, f=3, g=2, h=2, i=2>
V   = <d=1, e=2, f=3, g=2, h=3, i=3>
x0  = <a=2, e=1>
x1  = <e=2, f=1, h=3, i=1, j=2, k=2, l=2, m=3, n=2, o=2>
[U, V] = <h=2, i=6, j=4, k=4, l=6, m=3, n=2, o=6>        LIVE, and live at class four (x15 = 3)

sqRelWord(undressed)         = 1                     all fifteen rows
sqRelWord(a0 = a1 dressed)   = liftC 7               ⭐⭐ fourteen rows dead, top row ODD
```

at every handle count `h = 1..4` and every handle.  The gauge audit:

| datum the class-four gauge constrains | value |
|---|---|
| `x0` abelian columns `x_{12}, x_{34}, x_{45}` | `2, 0, 0` (even) |
| `x0` `nu'`-column `x_{23}` | `0` |
| `x0` lower class-two `x_{13}, x_{24}` | `0, 0` (even) |
| `x1` abelian columns `y_{12}, y_{34}, y_{45}` | `0, 0, 0` (even) |
| **the one odd datum**: `x0`'s fifth abelian column `x_{56}` | **`1`** |

The class-four relator is trivial at **both** dressings through `toU5L`, so the whole committed
class-`<= 4` machinery cannot tell them apart.  The separation is purely class five.

### 3.3  Soundness, and why the block is necessary

Measured at the separating point (`results/sweep_sigma5.txt` section 1):

```text
|gamma_3(im)| = 16384    every element has EVEN x14, x25, x36
|gamma_4(im)| =   128    every element has EVEN x15, x26
|gamma_5(im)| =     4    every element has EVEN x16
392 single-slot achievable refinements     : parity never flips
60000 random five-slot achievable ones     : parity never flips
UNRESTRICTED gamma_4 moves                 : 96 of 320 DO flip it
```

so the odd residue is a genuine verdict and not a gauge artefact, and achievability is
load-bearing here exactly as it is at the committed class-four points
(`GradedFourCleared`: "8 of the 64 unrestricted `gamma_3`-moves ... kill the odd dressing").

⭐⭐ **A live handle block is necessary, and it must be live in the `x_{15}` row.**  With a dead
block the relator forces `H = 1`, hence the core word `W = 1`.  Row `x_{13}` then gives `x_{12}`
even, and the core word's class-four row is

```text
W_{15} = x_{12} * x_{35} + y_{13} * y_{35}   (mod 2),
```

which a trivial block cannot help to kill; so `y_{13} * y_{35}` must be even, and the response
`x_{12} * y_{24} * y_{46} + x_{56} * y_{13} * y_{35}` is even with it.  Census over `568`
dead-block relator-killing markings produced by the layered fifteen-row solve: `y_{13} * y_{35}`
is even at every one, and **none** separates the `a0 = a1` dressing.  The separating point's
block is live exactly there, `[U, V]_{15} = 3`.  So the block never enters the selection bit and
is nonetheless the reason the escape exists, which is the sharpest form of the answer to (c):
the handle block is invisible to the class-five *bit* and indispensable to the class-five
*point*.

---

## 4.  (c) the handle block: the cancellation changes mechanism, the verdict does not

### 4.1  The coupling identity

`sqRelWord m = W * H` with `W = sqWord(m 0, m 1, m 2)` and `H` the handle word, which lies in
`gamma_2`.  In `U_6`,

> ```text
> (W * H).o  =  W.o + H.o + W.a * H.n + W.f * H.l + W.j * H.i
> ```

The sigma dressing moves neither `W.a` (`x_{12}`) nor `W.f` (`x_{13}`) - the seven rows `a..g`
are sigma-invariant - but it **does** move `W.j` (`x_{14}`), by the committed `sigFourH`.  Hence

> ⭐⭐ ```text
> Delta_v (relator top row)  =  sigFiveRead(v, x, y)  +  sigFourH(v, x) * H_{46}
> ```

verified at `40000` markings, `h = 1, 2`, arbitrary letters, live block or dead, `0` mismatches.
This is the exact failure of `GradedFourCleared.sqRelWord_sigFourDress_handle_blind`: at class
four the two coefficients the block met were both sigma-invariant, so the block cancelled from
the difference identically; at class five one of the three is not.

### 4.2  Why it dies anyway, twice over

1. **The coefficient.**  `sigFourH(v, x)` is even on the class-two-forced gauge - that is
   `GradedSigmaFour.sigFourH_gauge_even`, the class-three blindness, reused one level up.  And on
   the diagonal it is even at **every** marking: `sigFourH(x, x) = -2 * x_{12} * x_{34}`
   (proved, `GradedSigmaFive.sigFourH_diag`).
2. **The block coordinate, and this one needs no gauge at all.**  The relator pins
   `H = W^{-1}`, so `H_{46} = -W_{46}`, and
   ```text
   W_{46} = -4*x_{46} + 2*y_{46} + 10*x_{45}*x_{56} - 8*x_{45}*y_{56} + y_{45}*y_{56}
          = y_{45} * y_{56}   (mod 2)
   ```
   while the relator's abelian rows `-4*x_{45} + 2*y_{45} = 0` and `-4*x_{56} + 2*y_{56} = 0`
   force `y_{45}` and `y_{56}` even over `ZMod 8`.  So `H_{46}` is **even at every
   relator-killing marking**, at every handle count, on every row.

Either fact alone closes the channel.  The second is the important one: it says the block is
forced even *exactly where the class-five bit reads it*, by the relator itself.

### 4.3  The general price, and the first opening

At class `c` the carrier is `U_{c+1}` and the same expansion gives

> ```text
> Delta_v (relator top row)  =  [class-c reading]  +  sum_{m=2}^{c-1} [class-(m-1) reading] * H_{m, c+1}
> ```

Both factors are now computable in general.

* **coefficients.**  `[class-(m-1) reading]` is `0` for `m <= 3` (the `(1,2)` and `(1,3)` rows do
  not move); it is `sigFourH`, even on the gauge, for `m = 4`; it is odd-able for `m >= 5`
  (`sigFourRead` onwards - that is `GradedSigmaFour`'s own headline).
* **block coordinates.**  For `m >= 3` the corner `(m..c+1)` misses the sigma letter `E_23`
  entirely, so the core word restricts there to `x^{-4} y^2` and the block to its inverse.
  Derived in `results/derive_sigma5.txt` section 5, corners of size `3, 4, 5, 6`: **every
  coordinate of class `<= 3` is even** once the relator's abelian rows hold; the first that can
  be odd is the class-**four** one, `y_{13} y_{35} + x_{12} x_{23} x_{34} x_{45}` in corner
  coordinates.

Combining, a coupling term can be odd only when the coefficient is odd-able **and** the block
coordinate has class `>= 4`:

| | condition | first class |
|---|---|---|
| on the committed gauge (`x_{12}`, `x_{34}`, `x_{13}`, `x_{24}` even) | `m >= 5` and `c + 1 - m >= 4` | **class 8** |
| off it, so that `sigFourH` may be odd | `m >= 4` and `c + 1 - m >= 4` | **class 7** |

So classes four, five, six and seven are handle-blind on the committed gauge, and classes
four, five and six are handle-blind whatever the gauge.  The blindness direction is the
safe one: the table lists **necessary** conditions for a coupling term to be odd, so the
negatives are certified, while "first opening at class 8" only says the arithmetic stops
forbidding it there.  Whether a legal point realizes it is not settled here.  **This is a negative, and it
is the consequential one, but it is not the negative the brief feared**: the handle block is not
invisible at every class by the same mechanism.  Wave 57's identical cancellation is a
class-four accident that stops at class five; what replaces it is the parity of the *forced*
block, and that is an arithmetic fact with a definite expiry date.  Buying visibility by class
alone costs four more levels; the honest reading is that the `h >= 1` route wants a different
instrument.

### 4.4  The class-five gauge parity theorem

The transposition of `GradedFourCleared.sqWord_sigFourMark_gauge_even`, derived symbolically over
`Z` (`results/derive_sigma5.txt` section 6).  On the honest class-two-forced gauge the twelve
rows of class `<= 3` of the core word are **all even**, and exactly three can be odd:

```text
W.m (x15, class 4) : y13*y35
W.n (x26, class 4) : x36 + y24*y46
W.o (x16, class 5) : y13*y36 + y46*y14 + ...
```

At class four only **one** row could be odd; at class five **three** can, and the two new ones are
the class-four rows.  The class-two-forced gauge controls exactly the rows of class `<= 3` at
either level, which is why the block coordinates it pins are the shallow ones.

---

## 5.  PROVED versus MEASURED

**PROVED** (Lean, `GQ2/Dyadic/SqCore/GradedSigmaFive.lean`, 8 declarations, all prints std-3 or a
subset, no `sorry`, no new axiom, no `native_decide`; the single `decide` is on `ZMod 8`):

* `sigFourG_diag`, `sigFourH_diag`, `sigFourI_diag`: the diagonal of the three lower class-four
  readings, over an arbitrary commutative ring;
* `sigFourRead_diag_even`: the class-four reading is even on the diagonal from **three**
  hypotheses, not eight, and none of them touches the `x0` slot;
* `sigFourRead_gauge_sigma_eq_x0_of_diag`: the committed statement is the special case;
* `abelRow_even`, `sigFourRead_diag_even_of_abelRows`, `selPar_sigFourRead_diag`: those three
  hypotheses are the relator's own abelian rows, over `gr3R`.

**MEASURED** (`scripts/w58_sigma5/`, `results/*.txt`; `43 + 23 + 12` named checks, `0` failures):
every class-five statement above.  In particular the class-five reading and its channel table,
the gauge collapse, the `a0 = a1` closed form and the separating point, the coupling identity and
the evenness of the forced block, the soundness census, and the class-six-to-eight forecast.
The class-five carrier is **not** built in Lean here; that is the concurrent W58-FIVE lane's, and
none of this file's Lean depends on it.

**Validation standard.**  Every closed form is machine-emitted from the symbolic derivation into
`sigfive_forms.py` and then checked against honest `U_6` collection: `300000` row comparisons,
`0` mismatches; the coordinate law itself is checked against honest `6 x 6` matrix arithmetic and
against an independent generic unitriangular library, and both `U_5` quotients are checked to be
homomorphisms onto the **committed** `SqU5`, so every class-four fact is reused rather than
retyped.

---

## 6.  What the next wave should prove

> ⭐⭐ **THE STATEMENT.**  Build the class-five carrier `SqU6` and the class-five reading
> `sigFiveRead`, and prove, at the binder point of section 3.2 (handle letters
> `U = <a=1, c=2, d=3, f=3, g=2, h=2, i=2>`, `V = <d=1, e=2, f=3, g=2, h=3, i=3>`, `x0 = <a=2, e=1>`,
> `x1 = <e=2, f=1, h=3, i=1, j=2, k=2, l=2, m=3, n=2, o=2>`):
>
> 1. `sqRelWord (fiveWit 1) = 1` and `sqRelWord (fiveWit x0) = liftC 7`, by `decide`;
> 2. the whole class-four relator is trivial at both dressings, so the committed class-`<= 4`
>    machinery cannot separate them;
> 3. the soundness lemma: every achievable `gamma_4`-dressing at that point has even `x_{15}` and
>    `x_{26}` coordinates, whence every five-slot refinement moves the class-five residue evenly;
> 4. therefore **the sigma dressing `a0 = a1` is excluded at class five**, which is the residual
>    `GradedSigmaFour` section 7 named.
>
> The one genuinely new lemma is (3): it is the class-five transposition of
> `sigFourWit_lamThree_even`, and the census that decides it is already run
> (`|gamma_4(im)| = 128`, all even).  Everything else is `decide` on `ZMod 8` tuples plus the
> fifteen-row response, which is derived and certified here.

Two smaller items, both certified here and both cheap in Lean once the carrier exists:

* the coupling identity `Delta_v(top) = sigFiveRead + sigFourH * H_{46}` and the evenness of
  `H_{46}` at any relator-killing marking, giving **class-five handle-blindness** as a theorem
  rather than an observation;
* the class-five gauge parity theorem of section 4.4.

And one warning for whoever prices the `h >= 1` route: section 4.3 says a higher class does not
buy handle visibility until class eight.  The block is not invisible by an identity any more; it
is invisible because the relator forces it even where the bit looks.  Any instrument that is to
see it must either read a row the relator does not pin, or leave the class-two-forced gauge.

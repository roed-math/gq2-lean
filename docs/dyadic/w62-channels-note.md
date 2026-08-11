# W62: the three channels, and why no binder point can make them even

**Wave W62, worker W62-CHANNELS.**  Lean: `GQ2/Dyadic/SqCore/GradedGammaTwoPoint.lean` (499
lines, committed, all 25 prints std-3 or a subset, zero sorries, no new axiom, no
`native_decide`).  Off-Lean: `scripts/w62_channels/` (plain Python, exact integer arithmetic on
the honest `6 x 6` engine of `scripts/w59_force5/u6mat.py`).  Answers the experiment
`GradedFiveGammaTwo` and `docs/dyadic/w61-wider-note.md` section 6 named as the wave-62 queue's
first item.

---

## 0.  Headline

| question | answer |
|---|---|
| is there a binder point where all three channels are even? | **Not one that is any use.**  A point with even channels always has an EVEN class-five separation bit, so it cannot separate the two sigma dressings and there is nothing left to exclude. |
| why? | ⭐⭐⭐ **The channel functional IS the bit.**  `SqU6.gaTwoChannel_commP_low`: at the achievable dressing `[x0, x1]` placed on the `x1` slot, the three-channel value is `x0.e * x1.f * x1.h` mod two, which is wave 58's closed form for the bit once `stageN1` makes `x0.a` even. |
| does the exclusion widen at all? | **Yes, conditionally, and that is a real gain.**  `sqRelWord_stageWit_diag_gaTwo_ne_one`: at wave 60's point, at every handle count and handle, no achievable `gamma_2`-dressing whose three-channel functional is EVEN kills the dressed frame.  One filtration step wider than wave 60, with one condition. |
| is the condition vacuous? | **No, and that is the negative.**  `stageWit_gaTwoShiftChan_slotTwo_odd` exhibits an achievable dressing at wave 60's point whose functional is odd, so the condition fails there and no unconditional widening follows. |
| does the class-two-forced gauge do the work? | **No.**  The collision needs only `stageN1` and the two `x1`-columns the RELATOR itself pins (`sqRelWord_lower_x1_even`).  The gauge is not a hypothesis anywhere, so the obstruction does not evaporate off it. |
| is anything from wave 61 upgraded? | **Yes.**  Wave 61 MEASURED that the functional is odd on six of ten commutator generators at wave 60's point; the decisive one is now a Lean theorem, and its consequence (wave 61's forcing conclusion is satisfied there) is assembled as `stageWit_gaTwo_forced_not_vacuous`. |

---

## 1.  The reduction

The wave-61 transport says the class-five row of a `gamma_2`-dressed frame moves, mod two, by

```
   SqU6.gaTwoShiftChan h m z  =  sum over slots of   z.m * L.e + z.i * L.j + z.l * L.f
```

against the permuted letters, and by nothing else.  The exclusion needs this even for every
achievable `z`, i.e. every element of `forceLcs H 1 = [H, H]` in every slot independently.  Wave
61 abandoned the element-by-element closure of `[H, H]` as too slow.  It is not needed:

* **the pairing is a homomorphism.**  On the achievable lattice (which wave 60's
  `stageN2_of_commutator` puts inside `f`, `h`, `j` all even) the triple `(z.m, z.i, z.l)` mod
  two is additive, because the only correction in a product is `z.f * w.h`, divisible by four.
  Measured at 4000 random lattice pairs, zero exceptions; on unrestricted `gamma_2`-elements the
  same additivity fails at 532 of 2000, so the lattice is doing the work;
* **`gamma_3` of the image dies under it.**  For `z` in the lattice and `r` in `H`, all three
  coordinates of `[z, r]` are even, because each monomial carries one of `z.f`, `z.h`, `z.j`,
  `r.a`, `r.c`.  Measured at 4000 random pairs, zero exceptions;
* so the image of the whole lattice is the **`F_2`-span of the ten pairwise commutators of the
  point's letters**, and the whole question is finite.  Checked against 24000 deep random
  lattice elements at 400 points, zero outside the span, and the span is actually attained at
  365 of the 400.

With that, the coordinates of a commutator of two `stageN1` letters are, mod two,

```
   [p,q].m = p.j q.d + p.d q.j + p.f q.h + p.h q.f
   [p,q].i = p.d q.e + p.e q.d
   [p,q].l = p.h q.e + p.e q.h
```

(6000 random pairs, zero exceptions; without the two even columns the `m` formula fails at 850
of 2000).  Everything else in this wave is substitution into those three lines.

---

## 2.  The collision

Take `p = x0` and `q = x1`, the marking's own two core letters, so `[x0, x1]` is achievable by
definition, and put it on the `x1` slot with `1` everywhere else.  The functional collapses to a
single channel, `SqU6.gaTwoShiftChan_gaTwoSlotTwo`.  Now use the two columns the relator pins:

> **Free hypothesis.**  `(sqRelWord m).k = -4 (m 1).k + 2 (m 2).k` for each abelian row
> (`SqU6.sqRelWord_a` and its four siblings, committed), so at any marking killing those rows
> over `Z/8` the `x1` slot has ALL FIVE abelian columns even.  Both frames of wave 60's
> separation qualify: the undressed one kills the relator outright and the `a0 = a1` one leaves
> `SqU6.liftO 1`.  `sqRelWord_lower_x1_even`.

With `x1.d` and `x1.e` even the first two channels die and the third leaves

```
   SqU6.gaTwoChannel [x0, x1] x1  =  x0.e * x1.f * x1.h    (mod 2).
```

That is `SqU6.gaTwoChannel_commP_low`, proved over any commutative ring.  And the right-hand
side is exactly wave 58's closed form for the class-five separation bit, once `stageN1` makes
`x0.a` even:

```
   (a0 = a1 relator).o  -  (undressed relator).o  =  x0.a x1.g x1.i + x0.e x1.f x1.h   (mod 2)
```

re-measured here in the DIFFERENCE form, which needs no relator-killing hypothesis, at 4000
gauge markings AND at 4000 markings keeping only the relator's own `x1`-columns: zero exceptions
in both.  Drop the `x1`-columns as well and the form fails at 1022 of 4000, so the hypothesis is
precisely the free one.

**Consequence** (`SqU6.gaTwoChannel_even_bit_even`).  Even channels force an even bit.  The
functional a `gamma_2`-level exclusion must kill is the functional the point needs live in order
to separate the two sigma dressings at all.  There is no point that is both, and the search
wave 61 asked for has no target.

⚠ The class-two-forced gauge plays **no** role.  This was the wave's own surprise: the first
version of the argument was a gauge statement (the offending channel being odd whenever `x0.f`
and `x1.d` are even), and the sharper form makes the gauge unnecessary on both sides of the
collision.  What is doing the work is the relator's own class-one rows.

---

## 3.  What the wave still buys

`sqRelWord_stageWit_diag_gaTwo_ne_one`, at wave 60's binder point, every handle count, every
handle:

> No achievable `gamma_2`-dressing of the five slots whose three-channel functional is EVEN kills
> the dressed frame.

That is `GradedFiveStageFour.sqRelWord_stageWit_diag_ne_one` one filtration step wider with one
condition attached, and by section 2 the condition cannot be removed by choosing a better point.
It is the sharpest form the transport supports.

⭐ **How much of the lattice it covers: exactly half.**  By section 1 (MEASURED) the map from
achievable five-slot dressings to the parity of the functional is a group homomorphism onto
`Z/2`, onto because `stageWit_gaTwoShiftChan_slotTwo_odd` (PROVED) hits `1`.  So the dressings
the theorem excludes are an index-two subgroup of the achievable lattice: the conditional
widening is not a thin statement, and the missing half is a single coset.

Two smaller results:

* `stageWit_gaTwoShiftChan_slotTwo_odd` PROVES what wave 61 measured, for the generator that
  decides the question: at wave 60's point the functional is odd at `[x0, x1]` on the `x1` slot.
  `gaTwoSlotTwo_comm_mem_forceLcs` supplies the achievability, from `Subgroup.subset_closure`
  and `Subgroup.commutator_mem_commutator`, so the dressing is honest and not declared;
* `stageWit_gaTwo_forced_not_vacuous` assembles the negative at the point: there is an achievable
  dressing at which wave 61's `stageWit_gaTwo_forced` conclusion `selPar(residue + chan) = 0`
  HOLDS, so that theorem yields no contradiction there.  `stageWit_channel_eq_bit` checks the
  collision at the point by kernel computation, so the structural route of section 2 and the
  machine route meet inside the Lean file.

---

## 4.  The censuses

`scripts/w62_channels/`; plain Python 3, no dependencies, exact integer arithmetic.

### 4.1  The exhaustive parity sweep (`sweep_f2.py`, `results/sweep_f2.txt`)

Everything above depends on five parities per letter, `(d, e, f, h, j)`, of four letters (the
sigma slot's dressed letter `sigma * x0` agrees with `x0` in all five, because the committed
sigma marking is `<b=1>`).  That is `2^20 = 1048576` patterns and the sweep enumerates every one.

| stratum | patterns | of which channels even and bit odd |
|---|---|---|
| all | 1048576 | 2432 |
| bit odd | 131072 | 2432 |
| on the committed class-two-forced gauge | 131072 | **0** |
| with `x1.d`, `x1.e` even (what the relator forces) | 262144 | **0** |

and every one of the 2432 survivors needs `x0.d`, `x0.f` or `x1.d` odd.  So the incompatibility
is exact rather than generic, and the sweep independently confirms
`SqU6.gaTwoChannel_even_bit_even` from the other side: it uses the measured parity formulas of
section 1, not the Lean proof.

The refuting pair is always the same one: `[x0, x1]`, read against the `x1` slot (8192 of the
16384 gauge-and-bit-odd patterns report it first) or against the `x0` slot (the other 8192, where
`x0.h` is odd; the committed gauge makes `x0.h` even, so on the full gauge it is always the `x1`
slot).

### 4.2  The marking census (`census_points.py`, `results/census.txt`)

Markings rather than parity patterns, with the honest group law and the honest DIFFERENCE bit
rather than any closed form, so that nothing in section 2 is assumed.

| stratum | markings | channels even and bit ODD |
|---|---|---|
| `x0` on the gauge, `x1` with even abelian columns | 8000 | **0** |
| `x0` free (`stageN1` only), `x1` relator-shaped | 8000 | **0** |

plus a third pass over **honest live binder points**: the undressed frame kills the relator, the
`a0 = a1` frame is central with an ODD class-five residue, and every letter is `stageN1`.  Wave
60's layered solve (`pointlib.solve_y_central`) enumerates every `x1` slot making a given
`(x0, U, V)` triple live, and eight members of the `x0` gauge family are live against wave 60's
handle letters, so the pass covers

| live binder points | all three channels even | `chan([x0,x1], x1)` odd |
|---|---|---|
| **131072** | **0** | **131072** |

which is the theorem's verdict on every one of them.  A further 40 random `(x0, U, V)` triples in
665 s produced no new live triple, which is consistent with wave 60's measured rate of about one
in 430.

### 4.3  The derivation (`derive_channels.py`, `results/derive.txt`)

**15 named checks, 0 failures**, plus five sharpness measurements each showing the corresponding
hypothesis is load-bearing (532 of 2000; 850 of 2000; 1022 of 4000; 935 of 4000; and the deep
lattice sampling reaching the whole span at 365 of 400 points).

---

## 5.  What is proved and what is measured

**Proved (Lean, this wave, all pins std-3 or a subset):** the three commutator parity forms
(`SqU6.commP_m_parity`, `SqU6.commP_i_parity`, `SqU6.commP_l_parity`); the channel head and its
collapse (`SqU6.gaTwoChannelHead_low`); ⭐⭐⭐ the collision `SqU6.gaTwoChannel_commP_low` and its
marking-level form; ⭐⭐⭐ `SqU6.gaTwoChannel_even_bit_even`; the single-slot dressing calculus
`SqU6.gaTwoShiftChan_gaTwoSlotTwo`; the free `x1`-hypotheses `sqRelWord_lower_x1_even`; the
achievability `gaTwoSlotTwo_comm_mem_forceLcs`; and at wave 60's point
`stageWit_gaTwoShiftChan_slotTwo_odd`, ⭐⭐ `sqRelWord_stageWit_diag_gaTwo_ne_one` and
`stageWit_gaTwo_forced_not_vacuous`.  The channel arithmetic is over any commutative ring.

**Measured, not proved:** everything in section 4, and in particular **the identification of the
form `x0.e * x1.f * x1.h` with the honest class-five separation bit**, which is wave 58's closed
form.  Proving it would need the relator's `(1,6)`-row in closed form at an arbitrary marking,
which no wave has built.  Every Lean statement is about the FORM, and the statements at wave
60's point are `decide`d, so no Lean result depends on the measurement.

**Not attempted:** a proof that no achievable `gamma_2`-dressing kills the dressed frame.  This
wave shows the mod-two transport cannot decide that, and wave 61's single-slot census found no
kill, so the question is open in both directions, now with a reason.

---

## 6.  What the next wave should do

In value order.

1. **Stop looking for an even-channel point.**  The wave-61 queue's first item is discharged
   negatively and structurally.  Nothing in the `gamma_2` transport can widen wave 60's
   exclusion unconditionally, at any binder point, because the mod-two obstruction is the
   separation bit itself.
2. **The next honest widening is not mod two.**  W61-SHARP4 found the same thing from the
   necessity side: at the `gamma_2` level a kill must also leave the two class-four rows alone,
   and a class-four row can move by an even amount that no mod-two reading sees.  Both lanes now
   point at the same successor object: a CENTRALITY statement at the `gamma_2` level, i.e. which
   achievable `gamma_2`-dressings translate the relator centrally.  That is the object to build,
   and this wave's `SqU6.gaTwoShiftChan_gaTwoSlotTwo` plus wave 61's
   `SqU6.sqRelWord_gaTwoDress` are its inputs.
3. **If the exclusion is wanted anyway, attack the bit and not the channel.**  The collision says
   the two are the same functional, so a point whose bit is odd for a reason OUTSIDE wave 58's
   form would break it.  That needs the relator's `(1,6)`-row in closed form at an arbitrary
   marking; it is the same missing object as in 2 and would settle the measured link of
   section 5 at the same time.
4. **Record the free hypothesis.**  `sqRelWord_lower_x1_even` is cheap, general, and was not in
   the tree; several committed statements carry `x1`-column hypotheses that it discharges.
5. **Cheap: put the conditional widening at the hom level.**  `GradedStageFrame` transposes
   wave 60's stage-four exclusion to honest continuous homomorphisms without touching the
   letters, and `sqRelWord_stageWit_diag_gaTwo_ne_one` has the same shape, so the same route
   should carry it with the channel condition riding along.  Not attempted here.

---

## 7.  Reproduction

Working directory `scripts/w62_channels/`; plain Python 3, no dependencies.

```
chanlib.py          the functional, the parity triple, the span, the point predicates
derive_channels.py  the reduction and the collision, six sections   -> results/derive.txt
sweep_f2.py         the exhaustive 2^20 parity sweep                -> results/sweep_f2.txt
                                                                    -> results/survivors.txt
census_points.py    the marking census and the honest point search  -> results/census.txt
```

Verification of the Lean file, from the worktree root:

```
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true \
  GQ2/Dyadic/SqCore/GradedGammaTwoPoint.lean
```

zero errors, zero warnings, 25 axiom prints, every one a subset of
`[propext, Classical.choice, Quot.sound]`.  The module is not yet registered: `GQ2.lean` needs
`import GQ2.Dyadic.SqCore.GradedGammaTwoPoint` after
`import GQ2.Dyadic.SqCore.GradedStageNecessity`, which is currently the last `SqCore` import.

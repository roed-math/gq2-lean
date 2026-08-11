# W64: the class-four knob, its three gearings, and the `gamma_2` census

**Wave W64, worker W64-CENSUS5 (lead lane).**  Lean:
`GQ2/Dyadic/SqCore/GradedGammaTwoCensus.lean` (39 prints, all std-3 or a subset, zero sorries,
no new axiom, no `native_decide`).  Off-Lean: `scripts/w64_census5/` (plain Python, exact
integer arithmetic, layered on `scripts/w63_central2/centrallib.py` and
`scripts/w59_force5/u6mat.py`).  Answers the census question `GradedGammaTwoCentral` left open.

---

## 0.  Headline

| question | answer |
|---|---|
| what exactly is W63-CENTRAL2's mechanism? | ⭐⭐⭐ A **knob with a gearing**.  `SqU6.sqWord_mul_censKnob`: dressing the sigma letter by `censKnob t = <m = t>` multiplies the relator by the central `liftO (x0.e * t)` and moves no other row, at every marking, over any commutative ring. |
| is the sigma slot the only knob? | **No.**  `SqU6.commP_mul_censKnob_left` / `_right`: the live handle carries two more, geared by `v_j.e` and `-u_j.e`.  Three knobs in all; the two CORE slots do **not** act centrally and carry none. |
| what must a survivor satisfy? | ⭐⭐⭐ `cens_sigKnob_dichotomy` and siblings: for each of the three gearings, EITHER the gearing is even, OR the achievable lattice misses `censKnob t` for the unique odd `t` solving that knob's equation. |
| is an even gearing possible at a live point? | **Measurably no for `x0.e`.**  Over 60000 `(x0, x1)` pairs at each parity, an even `x0.e` never yields an odd residue (0 of 8489 central cases); an odd one yields them in quantity (671 of 3145). |
| is the sigma knob always achievable? | ⚠ **No.**  The census exhibits live binder points whose lattice misses it - so W63-CENTRAL2's route alone does **not** close the census. |
| do those points survive? | **No.**  At exactly those points a HANDLE SLOT kills instead - though ⚠ there the handle knobs are unachievable too, so the killer is a general lattice element and not a knob. |
| the verdict | **PARTIAL, in the "dead" direction.**  67 binder points decided exactly, **0 survivors**.  The mechanism is now a general theorem; the two side conditions are isolated and MEASURED, not proved, so "dead at EVERY binder point" is not claimed. |
| by-product | ⭐⭐⭐ **W63-LIVE5's point is killed by W63-CENTRAL2's own dressing** (`liveBlkWit_lines_false`), the composite W63 recorded as unresolved. |

---

## 1.  The knob identity

W63-CENTRAL2 named its mechanism as a coincidence of two numbers at wave 60's point: `stageX.e`
is a unit, and the killing dressing's class-four coordinate is odd.  The general statement behind
it is an identity of words.

For `censKnob t` the element of `SqU6 R` whose only non-zero coordinate is the class-four `m`:

```text
   sqWord (s * censKnob t) x y  =  sqWord s x y * liftO (x.e * t)          (any commutative ring)
   commP (p * censKnob t) q     =  commP p q     * liftO (t * q.e)
   commP p (q * censKnob t)     =  commP p q     * liftO (-(t * p.e))
```

All three are proved by componentwise expansion (`ext <;> simp only [...] <;> ring`), in the
style of `GradedFiveStageFour.SqU6.sqWord_mul_gaThree`, and each is cheap: the knob has fourteen
zero coordinates.  Because `sqRelWord (fiveTuple S X Y U V) = sqWord S X Y * commP U V`, they
give three relator identities at the one-handle-live family, with the three GEARINGS

| slot dressed | gearing |
|---|---|
| sigma | `x0.e` |
| live handle `u_j` | `v_j.e` |
| live handle `v_j` | `-u_j.e` |

`scripts/w64_census5/results/derive.txt` section 1 measures the class-five row at all FIVE slots
and finds the gearings `(x0.e, (10 x0 - sigma - 8 x1).e, x1.e, v_j.e, -u_j.e)`, i.e. the
`(5,6)`-columns of the Fox-permuted letters, which is the first of W62's three channels evaluated
at the knob.  ⚠ At the two core slots the shift is **not** central (it disturbs the class-three
and class-four rows), so those two are not knobs in this sense and no Lean statement claims they
are.  The three central identities are re-measured over `Z/3, 4, 5, 7, 8, 9, 16, 32` so the
ring-generic claim is tested and not asserted.

---

## 2.  The refutation engine

`cens_lines_false_of_central_kill` isolates what a refutation of the `gamma_2` lines actually
needs.  At a marking whose relator is `liftO c` with `c` ODD, an achievable `gamma_2`-dressing
whose effect on the relator is a CENTRAL translation `liftO g` with `c + g = 0` refutes

* `GaTwoForces` (it kills, and the residue is odd),
* `GaTwoCentral` (its `gamma_2` shift is `liftO g`, and `g = -c` is odd),
* `GaTwoOrth` (which implies `GaTwoCentral`).

Nothing about the SHAPE of the dressing enters.  W63-CENTRAL2 had to prove centrality separately
for its one dressing (`gaTwoShift_stageWit_cenKill`, by cancelling the translation identity); here
the hypothesis carries it, and the three knobs of section 1 satisfy it by construction.

Two immediate consequences beyond the census:

* `stageWit_lines_false_of_censKnob` widens W63-CENTRAL2's refutation from its single point to
  **the whole `stageWit` family**: at every sigma parameter `v` whose frame has an odd central
  relator, the gearing is `stageX.e = 5`, a unit, so the knob equation always has a solution and
  only achievability is left as a hypothesis.
* `sqRelWord_stageWit_censKnob` re-derives W63-CENTRAL2's kill from the identity rather than from
  its kernel computation; the two routes agree, which is the doctrine-rule-3 cross-check.

---

## 3.  The census machinery, and why it is fast

Deciding "does any achievable `gamma_2`-dressing of one slot kill?" naively means enumerating
`[H, H]`, which at wave 60's point has `2^26` elements; W63-CENTRAL2 could afford one exhaustive
sweep of `262144` dressings at one point and no more.  `censuslib` decides the same question
exactly, in well under a second, from structural facts about the shift

```text
   Phi_i(w)  =  sqRelWord(m)^{-1} * sqRelWord(m with slot i multiplied by w),
```

always READ OFF the relator, never from an emitted closed form.

* **WEAK fact** (all five slots, exceptionless): the shift's class-`c` rows read only the
  dressing's class-`<= c` part.  With the polycyclic sift listing its rows in COORDINATE order,
  every element of `[H, H]` factors as `p2 p3 p4 p5` by layer, so a nested sweep prunes layer by
  layer.  This licenses `slot_kill_exact`, which is valid everywhere.
* **STRONG facts** (sigma slot and both handle slots only): the class-three rows read only the
  class-two part; the class-four rows only the class-`<= 3` part; the shift ignores `w.o`; and
  `Phi(w r) = Phi(w) Phi(r)` for `r` `gamma_3`-shaped.  Since `gamma_3`-shaped elements multiply
  coordinatewise, the deep layers collapse to linear algebra over `Z/8` and only the class-two
  layer is swept.  This licenses `slot_kill_census`.
* ⚠ The strong facts **FAIL** at the two core slots (measured: A fails at 171 and 197 of 200; D
  at 135 and 165 of 200), because there the dressing enters through the powers `x^3` and `y^2`.
  The fast census asserts its slot is one of `{0, 3, 4}` and refuses otherwise; the census uses
  the nested sweep at the core slots.

Validation (`derive.txt` section 3): the fast census reproduces W63-CENTRAL2's `131072` exactly,
and on sub-lattices of wave 60's own lattice small enough to enumerate outright, three
independent routes - fast census, nested sweep, and honest brute force over every element - agree
at all five slots with zero mismatches.

---

## 4.  The census, and the two horns

`census.py` decides binder points exactly at the sigma slot and both handle slots, and at the core
slots too wherever those three all fail.  A binder point is: every letter `stageN1`, the undressed
frame kills the relator, and the `a0 = a1` frame is a central translation with an ODD class-five
residue - wave 62's condition exactly.

**Horn 1, the gearing parity.**  The liveness condition DECOUPLES from the handle letters: once
the undressed frame kills, the residue is `sqWord(sigma x0, x0, x1) * sqWord(sigma, x0, x1)^{-1}`,
so it can be swept over `(x0, x1)` pairs alone and far more widely than whole binder points.
Section 5 of `derive.txt` does that at 60000 pairs per parity, with the `x1` slot's abelian
columns pinned as the relator pins them:

| `x0.e` | central residues | of those, ODD |
|---|---|---|
| EVEN | 8489 of 60000 | **0** |
| ODD | 3145 of 60000 | 671 |

So the first horn of the criterion is (measurably) empty: **a live binder point has an odd
`x0.e`**, and the sigma knob's equation always has an odd solution there.  This is wave 58's
closed form for the separation bit - `x0.a x1.g x1.i + x0.e x1.f x1.h`, re-measured on the same
sample with zero exceptions - together with `stageN1` killing the first term.  ⚠ It is a
MEASUREMENT, not a theorem: proving it needs the relator's `(1,6)`-row in closed form, which no
wave has built.  Every Lean statement is conditional on the gearing's parity and never asserts it.

**Horn 2, achievability.**  This one is **not** empty.  The census finds live binder points whose
achievable lattice misses `censKnob t` for the solving `t` - so the sigma-slot route, which is
the only route W63-CENTRAL2 had, genuinely fails at some points, and at those points the sigma
slot has **zero** achievable killing dressings.  W62's `commP_m_parity` explains what governs it:
on `stageN1` letters `[p, q].m` is the bilinear form `p.j q.d + p.d q.j + p.f q.h + p.h q.f`
mod two, and the class-four parity is a homomorphism on the lattice (re-measured, 0 of 2000
exceptions), so the lattice's class-four parity is decided by the ten pairwise commutators.  But
having an odd class-four coordinate somewhere in the lattice is NOT the same as containing the
knob, and the census exhibits the gap.

**And that is where the handle slots earn their place.**  Of the 67 binder points decided
exactly, 18 have an unachievable sigma knob and 6 of those have **no achievable killing dressing
at the sigma slot at all**; at every one of those 6 a handle slot kills, with 4096 and 8192
dressings.  A third fresh triple has EVEN handle gearings, so both handle knobs are dead there
and the sigma knob is unachievable, and the sigma and `u` slots kill anyway.  **0 of the 67
survive.**

⚠ Honesty note: at those points the knobs are unachievable or dead, so what kills is a general
element of the lattice and not a knob.  The knob theorems are a proved SUFFICIENT mechanism and a
criterion a census can check; they are not a classification of the killers, and nothing here
claims they are.

---

## 5.  W63-LIVE5's point (the composite W63 left open)

W63 flagged that `GradedFiveLive.liveBlkWit` reuses the committed `stageX` as its `x0` slot,
which is exactly the slot W63-CENTRAL2's mechanism exploits, and recorded the question as
unresolved after an orchestrator spot-check mis-modelled the dressing.

It is resolved, in the affirmative, and it is immediate from section 1: the sigma knob's gearing
is `x0.e = stageX.e = 5`, a unit; `sqRelWord_liveBlkWit_diag` gives the residue `liftO 1`, odd;
and `1 + 5 * 3 = 0` in `ZMod 8`.  So **`censKnob 3 = gaTwoCenKill`, the very element W63-CENTRAL2
committed, kills LIVE5's diagonally dressed frame** at every handle count and every handle, and
all three `gamma_2` lines fail there (`liveBlkWit_lines_false`).  Achievability has a certificate
simpler than wave 60's:

```text
   censKnob 3  =  commP liveBlkU (liveBlkSig * stageX) * commP (liveBlkSig * stageX) liveBlkV
```

a product of two honest commutators of the point's own letters, with no inverse and no power
(`liveBlk_censKnob_comm_form`, `liveBlk_censKnob_mem`).

⚠ Nothing of `GradedFiveLive`'s own stage-four work is touched.  `censKnob_odd_not_mem_stageN3`:
an odd knob has an odd class-four coordinate, `stageN3` forces it even, and
`GradedFiveStageFour.forceLcs_two_le_stageN3` puts every achievable stage-four dressing in
`stageN3`.  So the knob lies strictly between `forceLcs _ 2` and `forceLcs _ 1`, exactly where
W63-CENTRAL2's did.

---

## 6.  What is NOT claimed

* **Not** "the `gamma_2` route is dead at every binder point".  Both horns of the criterion are
  measured rather than proved, so the theorem-level statement is the dichotomy, not the verdict.
* **Not** a five-slot decision.  `GaTwoForces` quantifies over dressings of all five slots; the
  census decides single-slot dressings exactly.  Since a single-slot kill kills outright, the
  direction the census reports is sound, but a point surviving all five single slots would still
  need a genuine five-slot search, and none was run.
* **Not** a hom-level statement.  Everything is at the level of marking tuples in `SqU6 gr3R`,
  as in `GradedFiveGammaTwo`, `GradedGammaTwoPoint` and `GradedGammaTwoCentral`.  The killing
  dressings are images of explicit commutators of the letters, so a lift is bookkeeping.
* **Not** a claim about the number of live binder points.  Live `(x0, U, V)` triples are rare
  under random search (roughly one in several hundred), so the census varies the `x1` slot
  widely, the `x0` slot over its whole `<a, e>` family at wave 60's handle letters, and the
  handle letters over the few fresh triples the search produced.  A census with many independent
  handle blocks is the obvious next step.

---

## 7.  What the next wave should do

1. **Close horn 1 in Lean.**  "A live binder point has an odd `x0.e`" is the last measured link
   in the chain, and it is now isolated to a single statement about the `(1,6)`-row of
   `sqWord(s x, x, y) * sqWord(s, x, y)^{-1}`.  Under `stageN1` and the relator's own `x1`
   columns the target is `x0.e * x1.f * x1.h` mod two.  A single-coordinate `ext` with an
   explicit even witness, in the style of `GradedGammaTwoPoint.SqU6.commP_m_parity`, would turn
   the whole census verdict into a theorem with only achievability left.
2. **Close horn 2, or find the point where it bites.**  Is there a live binder point at which
   ALL THREE knobs are unachievable?  The census says the sigma knob alone can fail; whether the
   three can fail together is the sharp question, and it is a finite condition on the ten
   pairwise commutators of the letters.
3. **Hunt more handle blocks.**  Live triples are the census's bottleneck.  The decoupling of
   section 4 suggests the productive direction: sweep `(x0, x1)` for the liveness condition
   first, then solve `commP U V = sqWord(sigma, x0, x1)^{-1}` for the handle pair.

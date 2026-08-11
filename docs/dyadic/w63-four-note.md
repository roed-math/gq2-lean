# W63-FOUR: the four gap markings, and why they are now reachable

**Verdict: PARTIAL, on route (A).**  Wave 62's diagnosis of the four is correct about the
methods it named and wrong about the target being out of reach.  This wave removes the obstacle
it identified - the need to name a subgroup containing the image - and lands the exact lattice
bound at all four markings.  The forcing itself is reduced to one `Z/8`-linear identity about
`gaThreeShift`, which is stated as a hypothesis in Lean and verified computationally, and which
a fourth attempt can discharge without any new idea.

Everything is in `GQ2/Dyadic/SqCore/GradedStageFour.lean` and `scripts/w63_four/`.

## 1  What wave 62 actually ruled out

Wave 62 measured three impossibilities at the four markings (`scripts/w62_separate/results/`):

* no per-coordinate congruence "coordinate `c` of every dressing is even" repairs the
  implication "central shift => even class-five row" (`diagnose.txt`);
* no mod-`2` linear condition on the lattice image repairs it, and at `gap-2` not even the
  mod-`4` relaxation does (`mod2_probe.txt`);
* no letter-column chain, and no covector identity such a chain allows, produces a usable
  bound (`feasible3.txt`).

All three are statements about **relaxations of the achievable lattice**.  They are statements
about a named subgroup `K0` with `H = <letters> <= K0`, because that is what the tree's only
tool for bounding `forceLcs H 2` needed.  `scripts/w63_four/results/chain_bound.txt` measures
the best such bound in the richest family the tree can actually build - the **filtered
congruence subgroups** `K(V_1, ..., V_5) = {z : level_r(z) in V_r}` - and confirms the verdict:
at `gap-1` the chain bound is `8192` against a lattice of `1024`, at `gap-2` it is `1024`
against `256`, and at all four **no separating character survives**.

## 2  What the tree never needed

`Subgroup.commutator_le` quantifies over all of both subgroups.  It does not have to.  If `K` is
a subgroup **normalised by** `H = closure S`, then

```
commLeft  K t = {g normalising K : [g, t] in K}
commRight K p = {g normalising K : [p, g] in K}
```

are subgroups, by `[p q, u] = (p [q, u] p⁻¹) * [p, u]` and
`[p, u v] = [p, u] * (u [p, v] u⁻¹)` respectively, so `Subgroup.closure_le` reduces a commutator
condition to the generators on either side.  Applied twice, with the middle term
`commAll K H = {p normalising K : [p, u] in K for every u in H}`, this gives

> **`le_of_gens_three`**: `K` normalised by `closure S` and `[[s, t], u] in K` for all
> `s, t, u in S` implies `[[closure S, closure S], closure S] <= K`.

This is standard group theory and it is not in mathlib in this form.  It is the whole content of
section 1 of the Lean file, it holds in any group, and it is what a fourth attempt would have
reused had this wave not landed it.

The bound it produces is the `H`-normal closure of finitely many explicit elements.  It reads
the lattice **exactly**: no congruence, no relaxation, no `K0`.

## 3  The four, bounded

`scripts/w63_four/results/normal_chain.txt` and `certify.txt` measure the consequences.

| marking | relator | lattice | Lean target | slack | certificate |
|---|---|---|---|---|---|
| `gap-1a` | `<o=5>` | 1024 | `gapKOne` (16384) | 16 | `l + 2n + 4o` |
| `gap-1b` | `<o=5>` | 1024 | `gapKOne` (16384) | 16 | `l + 2n + 4o` |
| `gap-2a` | `<o=1>` | 256 | `gapKTwo` (4096) | 16 | `m + 4o` |
| `gap-2b` | `<o=1>` | 256 | `gapKTwo` (4096) | 16 | `m + 4o` |

* `gapKOne = {z in gamma_3 : 2k + 4m + 4n = 0 and 2l + 4n = 0}`;
* `gapKTwo = {z in gamma_3 : k + 4n = 0, 4l = 0 and 2m = 0}`.

Neither is a per-coordinate congruence and neither is visible mod `2`; both say that certain
combinations vanish **mod 4**, which is exactly the level wave 62 identified as the difficulty.

The Lean proofs are:

* `forceLcs_two_le_gapOneA` and its three siblings, at every handle count and every handle.
  The arithmetic input is the `216` weight-three brackets of the six slot values of each
  marking, one `decide` on `ZMod 8` each.
* The normalisation hypothesis comes from a single column.  `gaThree_conj_m` and
  `gaThree_conj_n` say conjugation shifts the class-four rows by `g.a * z.k - z.j * g.d` and
  `g.b * z.l - z.k * g.e`.  The target's own conditions force `4k = 4l = 0` (`gap-1`) or
  `2k = 4l = 0` (`gap-2`), killing three of those four terms, and every `gap-1` letter has an
  even `(4,5)`-column while every `gap-2` letter has one divisible by `4`, killing the fourth.

**Normalisation by the image, not by the carrier, is load-bearing.**  `normal_chain.txt` shows
that the smallest subgroup normal in the whole carrier containing the `gap-2` brackets is four
times too big and admits no separating character at all.

## 4  What remains, and exactly what it costs

The forcing at an admissible marking with an odd central relator is the statement that the
class-five unit is **not** in the subgroup `B` of achievable shifts.  Since `B` is a subgroup of
the finite abelian group `gamma_3 = (Z/8)^6`, that holds if and only if some character of
`gamma_3` kills `B` and not the unit.  The certificates above are such characters; they are
normalised so that `psi(e_o) = 4`, which is what makes the target contain the class-five unit
and keeps the conditions short.

`stageForces_gapOneA_of_psi` and its three siblings are proved in full and say:

> if `psiOne (gaThreeShift h (gapOneMark h j) z) = 0` for every `z` all of whose slots lie in
> `gapKOne`, then `StageForces (gapOneMark h j)`.

So exactly one thing is left: that identity.  It is **not** an extra arithmetic accident.
`gapKOne` is by construction the joint kernel of the five slot pullbacks of `psiOne`, and
`gaThreeShift` is linear in the dressing tuple (`gaThreeShift_mul`), so the identity is
equivalent to the five pullbacks being what `certify.txt` measures them to be:

```
sigma  0        x0  6k + 4m + 4n     x1  2l + 4n     U  6k + 2l + 4m     V  0
```

for `gap-1`, and `0 | 5k + 4n | 2m | 4l | 6k + 4l` for `gap-2`.  A Lean proof therefore has to
supply the closed form of the shift's `l`-, `n`- and `o`-rows at the concrete letters:

* `(gaThreeShift h m z).l = -4 (z 1).l + 2 (z 2).l` is already in the tree
  (`gaThreeShift_l`), and so are `gaThreeShift_m` and `gaThreeShift_n`;
* `gaThreeShiftO` is `gaThreeCore(...).o` plus a sum of `gaThreeHandle(...).o` over the handles
  plus two block terms.  Multiplying by `4` kills both block terms outright, since each carries
  a factor `-4 (z 1).x + 2 (z 2).x`, so only the core and the handles survive;
* at a `fiveTuple` marking every handle other than the live one has both letters trivial, so the
  handle sum collapses to a single term once `gaThreeHandle 1 1 z w = 1` is available.

What is left after that is a linear identity in the `30` dressing coordinates over `ZMod 8` with
numeral coefficients.  `ring` alone will not close it, because `ring` does not reduce numerals
modulo `8`; the identity has to be closed by `linear_combination W * h8` with `h8 : (8 : gr3R) = 0`
and `W` the explicit integer-coefficient linear form `(LHS - RHS) / 8`.  Computing `W` means
reimplementing `gaThreeCore`, `gaThreeCorr`, `gaThreePair` and `gaThreeHandle` over the integers
in Python, which is safe because the result can be cross-checked mod `8` against
`sharp4lib.slot_matrix`.  **That is the whole remaining cost, and it is bookkeeping, not
mathematics.**

An alternative with the same endpoint: `gaThreeShift_mul` makes the shift a homomorphism of the
dressing tuple, so `Finset.univ_prod_mulSingle` decomposes any tuple into single-slot dressings
and the identity reduces to `6` generators per slot class - `decide`able one at a time in the
style of wave 62's `sepMark_shift` - at the cost of a lemma saying that a dressing supported on a
dead handle slot shifts by nothing.

## 5  Honesty

* The four markings are **not** proved.  What is proved is the lattice bound at all four, and
  the reduction of the forcing to one identity.  The identity itself is MEASURED
  (`scripts/w63_four/results/certify.txt`, 44 named checks, 0 failures), including on all
  `16384` members of `gapKOne` at each of the five slots.
* The Lean targets are strictly bigger than the honest lattices, by index `16` at all four.
  The certificate survives all of that slack; nothing in the file claims the targets are the
  lattices.
* Wave 62's three impossibility measurements are **not** contradicted.  They are measurements
  about congruence relaxations of the lattice, and section 2 does not relax the lattice.
* Route (B), certifying an impossibility, was considered and abandoned on evidence: the chain
  language is complete once `K0` is allowed to be the image itself, so any impossibility would
  have had to be about definability of `K0`, and section 2 shows `K0` is not needed at all.

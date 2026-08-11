# W64-VERIFY: the wave-64 verification lane

Five tasks. A: lift `le_of_gens_three` out and re-audit every committed lattice bound.
B: resolve the unresolved W63 cross-lane composite. C: fold the `ArbFrames` legality audit into
one statement. D: check W63's four landings against each other. E (added mid-wave by the
orchestrator, from `w64-psi4`'s finding): audit the certification scripts for the bracket
convention gap.

Everything below is either PROVED in Lean (file and declaration named) or MEASURED by a script
in `scripts/w64_verify/` with certified output in `scripts/w64_verify/results/`. Nothing is
asserted on any other basis.

---

## 0 Corrections demanded

These are places where a **committed** claim's prose outruns its proof. Each was read against
the actual theorem statement. They are ordered by seriousness.

### 0.1 `GradedFiveLive.lean` lines 62-64 and 335-338: a one-row lemma carrying a fifteen-row claim

Prose: *"the relator's four abelian rows read only the `x0`- and `x1`-slots, so the fifteen-row
standard places no condition whatsoever on the sigma slot's `(4,5)`-entry."*

`sqRelWord_d_indep_sigma` (line 339) proves exactly one row: if `m 1 = m' 1` and `m 2 = m' 2`
then `(sqRelWord m).d = (sqRelWord m').d`. The higher rows are not blind to the sigma slot, and
**this file proves that itself**: `liveBlkCore_not_relator_handleFree` (line 865) shows that with
`m 0 = liveBlkSig` (whose `d` is `1`) and `m 1 = stageX`, no `h = 0` marking kills the relator,
via `SqU6.pos_of_blockRead_odd`, which reads the `(4,6)`-row. So the standard does constrain the
sigma slot's `(4,5)`-entry; what is true is that at `h >= 1` the handle block absorbs it.

Two further slips in the same sentence: there are **five** abelian rows (`a`-`e`), not four, and
only the `d` row is recorded here.

**Should read**: *"the relator's `(4,5)`-row does not see the sigma slot; the higher rows do, and
at `h >= 1` the handle block absorbs an odd core reading, which is what the witness of section 2
exhibits."*

### 0.2 `GradedFiveLive.lean` lines 135-138 and 937-941: a theorem about a different quantity

Prose: *"the class-five selection bit at the point is a functional of the three core slots"*.

`liveBlkWit_bit_eq_core` (line 942) proves
`selPar (handleWord ...).i = selPar (blockRead (liveBlkWit h j 1 0) (liveBlkWit h j 1 1))`:
the **handle block's `(4,6)`-parity** equals a functional of **two** core slots. In this same
file "the bit" means `selPar (sqRelWord ...).o` (`liveBlkWit_bit_separates`, line 426), and the
two differ at this very point - line 427 gives `0`, `liveBlkWit_bit_eq_core_value` (line 952)
gives `1`.

**Should read**: *"the handle block's `(4,6)`-parity is a functional of the two core slots"*, and
the inference "a live block channel cannot add a datum to the bit even in principle" must be
re-derived from the correct quantity or dropped.

### 0.3 `GradedStageFour.lean` title, and lines 258, 651, 710, 769, 828: "bounded EXACTLY"

The title says the lattice is "bounded EXACTLY"; line 258 says the method "turns the achievable
lattice from a relaxation into an exact object"; four theorem docstrings say "BOUNDED WITHOUT
RELAXATION". The four theorems prove one-sided containments into `gapKOne` / `gapKTwo`, and the
file's own Slack paragraph (lines 97-99) says the targets are strictly bigger, index 16.

Measured here (`results/task_a_audit.txt` section 2): the honest lattices are `2^10`, `2^10`,
`2^8`, `2^8` and the targets are `2^14`, `2^14`, `2^12`, `2^12`. **Index 16 exactly, confirmed
independently.**

**Should read**: *"bounded by an explicit `Z/8`-linear target with index-16 slack; that the
method loses nothing is a separate statement"* - and that separate statement is now proved, see
1.3 below.

### 0.4 `GradedStageFour.lean` lines 52-53 and 526-528: false for two of `gapKTwo`'s three conditions

Prose: *"None of these is a per-coordinate congruence and none is visible mod `2`."* For
`gapKOne` this is right. For `gapKTwo` it is wrong: in `ZMod 8`, `4 * z.l = 0` is exactly
"`z.l` even" - a per-coordinate congruence that **is** a mod-2 condition - and `2 * z.m = 0` is
"`4 | z.m`", also per-coordinate. Only `z.k + 4 z.n = 0` is a genuine two-coordinate relation.
The same error is repeated at line 526-528 (*"the pair `4 l = 2 m = 0` is the mod-4 half that no
mod-2 condition sees"*).

### 0.5 `GradedGammaTwoCentral.lean` lines 84-85: contradicted by the file's own measurement

Prose: *"two of them (`g` and `i`) are not even on the achievable lattice"*. The file's own
MEASURED block (lines 105-107) says the achievable `gamma_2` lattice is exactly
`{z gamma_2-shaped : f, g, h, j even}`. Re-measured here at both class-five points
(`results/task_b.txt` section 1): `<g=1>` is **not** in the lattice at either. So `g` is even
there and the `g` half of the sharpening is redundant. **Should read**: *"one of them (`i`)"*.

### 0.6 `GradedGammaTwoCentral.lean` lines 39-40, 602-605: a numeric value no theorem states

Prose names the three-channel functional's value as `7`. `cenKill_chan_odd` (line 606) proves
only its **parity**. The only theorem naming `7` is `gaTwoShift_stageWit_cenKill`, about the
shift's `o`-row, a different quantity. Say "odd", or strengthen the theorem to the value.

### 0.7 `GradedGammaTwoCentral.lean` lines 96-97: wrong citation for a generality claim

Prose: *"the sigma-slot dressing as a reparametrisation ... (`cenSigDress_stageWit`, over any
commutative ring)"*. `cenSigDress_stageWit` (line 460) is `gr3R`-only. The any-`CommRing`
statement is `conFiveDress_fiveTuple_cenSigDress` (line 448). Swap the citation.

### 0.8 `GradedGammaTwoCentral.lean` lines 27-28, 130: "a product of two honest commutators"

`gaTwoCenKill_comm_form` gives `commP (...)⁻¹ stageU ^ 2 * commP stageY (...)`: the first factor
is a commutator **squared**. Wording slip only (the displayed formula shows the `^2`).

### 0.9 `GradedBlockSecond.lean` line 20: "everything wave 61 proved holds of it"

The file supplies CD analogues of the block equation, the handle-count forcing, the minor
selection and the dressing-invariance suite. It does **not** supply analogues of
`blindCexCore_not_relator_handleFree`, the `blockCoupling` suite, or `blockChannel_gaThreeDress`.
**Should read**: *"the block equation, the handle-count forcing and the minor selection transpose
verbatim"*.

### 0.10 `GradedBlockSecond.lean` lines 170-172: a claim about the whole symmetry group

*"It is not the image of `SqU6.blockRead` under any symmetry of `U_6`"* is evidenced only by the
outer-flip row pairing. Scope it to the outer flip, or move it to the MEASURED table.

### 0.11 `GradedFiveLive.lean` line 205-208: PROVED "everything above" includes an unformalised argument

"Above" includes the legality audit at lines 161-181, which says in its own words that it is
*"recorded here rather than formalised"* and which reappears as a MEASURED row at line 223.
**Should read**: *"everything named in Headlines 1-4"*.

### 0.12 Smaller items, listed for completeness

* `GradedFiveLive.lean` 68-71: *"A class-five witness cannot copy that"* is justified only by
  `stageX_gauge` / `forceX_gauge`, two `decide` facts about two letters. Should read *"a witness
  on the committed gauge cannot copy that"*.
* `GradedFiveLive.lean` 92: *"the unconditional stage-four exclusion"* - the cited
  `sqRelWord_liveBlkFrame_diag_ne_one_sharp` carries `hu` and `hv`. "Unconditional" is true only
  of the dressing quantifier (disclosed later at 195-201).
* `GradedFiveLive.lean` 888-889: *"The same holds at wave 60's point"* - no theorem exhibits the
  `h = 0` completion for `(fiveSigMark, forceX)`. Label as measured.
* `GradedFiveLive.lean` 551-554: the prose of `liveBlkWit_sigma_forced` drops the theorem's
  `2 | v.a and 2 | v.c` restriction (inherited from `GradedFiveStageFour.stageWit_sigma_forced`,
  so this is house style, but it is still a dropped hypothesis).
* `GradedGammaTwoCentral.lean` 70-74, 634-638: `stageWit_gaTwoSlotTwo_not_central` is about the
  dressed RELATOR, not the SHIFT that `GaTwoCentral` quantifies over; the bridge exists but is
  not invoked. And "counterexample to the parity line" is wave 62's result, inherited.
* `GradedGammaTwoCentral.lean` 35-38: *"the question `GradedStageFrame` recorded as open ... is
  now refuted"* - `GradedStageFrame` records it at frame/hom level, everything proved is
  marking-tuple level. The Scope note concedes this; the headline should too.
* `GradedStageFour.lean` 76-78: the PROVED list says the four markings are "ADMISSIBLE and the
  forcing's conclusion is FALSE there". The four theorems prove only the relator values
  `liftO 5` / `liftO 1`; there is no admissibility predicate in the tree and no theorem states
  `selPar (sqRelWord ...).o = 1`. One-line consequences, but not in the file.

**Checked and found accurate** (coverage, not silence): `GradedBlockSecond`'s Headline 3
correction of the block-blindness error, its `blockParCD_handleFree` and
`blockPar_secCexHom_eq_zero` (both genuinely over every pair), its `exists_blockParCD_odd_iff_pos`
and the `0 < h` reformulation warning; `GradedStageFour`'s `le_of_gens_three` statement, its
`gapKOne`/`gapKTwo` normalisation mechanism, its 216-bracket count, and its Headline 3, which is
the model case of a reduction stated honestly (`hpsi` displayed, "given that", listed as
measured); `GradedGammaTwoCentral`'s three-line refutation, `gaTwoCentral_iff_chan`, the
`ZMod 8` sharpening, and its Scope section; `GradedFiveLive`'s Headline 1 gauge reduction,
letter table, Headline 3, and its "What this file does NOT do" section.

---

## 1 Task A: the generator reduction, lifted; and the audit

### 1.1 What landed

`GQ2/Dyadic/SqCore/GradedLcsGens.lean`, namespace `LcsGens`, importing **Mathlib only**, so any
file in the tree may use it. 23 declarations, all axiom pins subsets of the std 3.

* `LcsGens.commutator_closure_le`: `⁅closure S, closure T⁆ ≤ K` when `S` and `T` both normalise
  `K` and `⁅s, t⁆ ∈ K` for generators. Two independent generating sets; nothing in the tree had
  this, and `Subgroup.commutator_le` is strictly weaker.
* `LcsGens.lcsGensSet` / `LcsGens.lcsSeries`: the left-normed generator brackets, and the
  descending series in an arbitrary group.
* ⭐ `LcsGens.lcsSeries_le_of_gens`: **arbitrary depth**. If `S` normalises `K` and `K` contains
  every left-normed bracket of `n + 2` generators, then `lcsSeries (closure S) (n+1) ≤ K`. The
  committed `le_of_gens_three` is the case `n = 1`; `LcsGens.le_of_gens_four` is `n = 2`, which
  the committed form could not reach and which is the shape of the tree's three depth-3 bounds.
* ⭐ `LcsGens.lcsSeries_le_iff_of_gens`: **the reduction is EXACT**. Among subgroups normalised
  by `S`, the bracket condition is not merely sufficient but EQUIVALENT to containing the series
  term. Supported by `lcsSeries_map_conj_le`, `le_normalizer_lcsSeries`,
  `lcsGensSet_subset_lcsSeries` and `lcsSeries_satisfies_gens`.
  **This is the half W63-FOUR asserted in prose and did not prove** (see 0.3).

**Mathlib shape.** `GradedStageFour.subset_normalizer_of_conj` is a duplicate of Mathlib's
`Subgroup.le_set_normalizer_iff` and is not restated; this file uses the Mathlib lemma. The
`commLeft` / `commRight` / `commAll` subgroups have no Mathlib counterpart and are the natural
API for the gap: Mathlib has `Subgroup.commutator_le` and the Three Subgroups Lemma, and neither
reduces a commutator of closures to its generators.

**Not done**: `GradedStageFour.lean` is untouched, so its copies remain. Replacing them with
`LcsGens.le_of_gens_three` is a one-line merge task for whoever next edits that file; `w64-psi4`
was consuming the committed form during this wave and a move would have conflicted.

### 1.2 The audit table

`scripts/w64_verify/task_a_audit.py`, output `results/task_a_audit.txt`, **60 named checks, 0
failures**. Two sharpness questions are separated, because they have different answers.

**(U) Uniform sharpness.** Every bound reads `for all H ≤ N_in, forceLcs H k ≤ N_out`. `forceLcs`
is monotone in `H`, so the join of the left side over all admissible `H` is `forceLcs N_in k`.
The bound is sharp as stated exactly when `forceLcs N_in k = N_out` - one computation, not a
search.

| bound | file | `N_in` | k | `log2 forceLcs N_in k` | `log2 N_out` | sharpest? |
|---|---|---|---|---|---|---|
| `forceLcs_one_le_gaTwoSub` | `GradedGammaTwoCentral:198` | (all) | 1 | 30 | 30 | **yes** |
| `forceLcs_two_le_gaThreeSub` | `GradedStageNecessity:393` | (all) | 2 | 18 | 18 | **yes** |
| `forceLcs_three_le_gaFourSub` | `GradedFiveNecessity:445` | (all) | 3 | 9 | 9 | **yes** |
| `forceLcs_one_le_stageN2` | `GradedFiveGammaTwo:1251` | `stageN1` | 1 | 26 | 27 | **NO, index 2** |
| `forceLcs_two_le_stageN3` | `GradedFiveStageFour:869` | `stageN1` | 2 | 13 | 15 | **NO, index 4** |
| `forceLcs_three_le_forceN4` | `GradedFiveForce:868` | `forceN1` | 3 | 7 | 7 | **yes** |
| `forceLcs_two_le_fiveEvenL` | `GradedStageNecessity:663` | `fiveEvenE` | 2 | 17 | 17 | **yes** |
| `forceLcs_three_le_fiveEvenN` | `GradedFiveNecessity:799` | `fiveEvenE` | 3 | 8 | 8 | **yes** |
| `forceLcs_two_le_sepEvenJ` | `GradedStageSeparate:515` | `sepEvenA` | 2 | 17 | 17 | **yes** |

Seven of nine are sharp as stated. The two that are not are the two the rest of the class-five
stack runs on, and the sharpened targets are explicit and certified exhaustively:

* `forceLcs H 1 ≤ stageN2'` with `stageN2' = {a..e = 0, 2|f, 2|g, 2|h, 2|j}`. `stageN2` is
  missing **`2 | g`**. (Order test: the lattice is `2^26 = |stageN2'|` and contains every
  `stageN2'` generator; `<g=1>` is the one `stageN2` generator not in it.)
* `forceLcs H 2 ≤ stageN3'` with `stageN3' = {a..i = 0, 4|j, 2|k, 2|l, 2|m}`. `stageN3` has
  `2 | j` where the truth is **`4 | j`**, and records **no condition on `k`** where the truth is
  `2 | k`. Certified by enumerating all `8192` elements of the lattice; `<j=2>` and `<k=1>` lie
  in `stageN3` and are not achievable.

**(P) Pointwise sharpness.** At a concrete marking the sharpest admissible target is the honest
lattice itself, because `le_of_gens_three` is exact (1.1). Measured:

| marking | k | `log2` lattice | `log2 N_out` | slack | hypothesis `H ≤ N_in`? |
|---|---|---|---|---|---|
| `stageWit h j stageX` (w60 binder) | 2 | 13 | 15 (`stageN3`) | `2^2` | yes |
| `liveBlkWit h j stageX` (w63 live) | 2 | 13 | 15 (`stageN3`) | `2^2` | yes |
| `fiveWit h j forceX` (w59/w60) | 3 | 7 | 7 (`forceN4`) | `2^0` | yes |
| `mixStageMark` (w61 strictness) | 2 | 8 | 15 | `2^7` | **no** (proved: `mixStage_not_le_stageN1`) |
| `orthFiveMark` (w59 strictness) | 3 | 6 | 7 | `2^1` | **no** (proved: `orthFive_not_le_forceN1`) |
| `halfFiveMark` (w59 half point) | 3 | 6 | 7 | `2^1` | **no** |
| `gapOneMark`, `gapOneMark'` | 2 | 10 | 14 (`gapKOne`) | `2^4` | no (odd `a`) |
| `gapTwoMark`, `gapTwoMark'` | 2 | 8 | 12 (`gapKTwo`) | `2^4` | no (odd `a`) |

At the two class-five binder points the honest lattice is `2^13`, i.e. **exactly** the uniform
`forceLcs stageN1 2`. So at those points the entire available sharpening is the uniform
sharpening above: `4 | j` and `2 | k`. Elsewhere the pointwise gap is larger.

**Is any of this used to conclude a possibility SURVIVES?** Checked, and the answer is no. The
tree's "survives"-shaped statements about lattices - `mixStage_forceLcs_not_le_stageN3`,
`orthFive_not_le_forceN4`, `halfFive`'s analogue - are all NEGATIVE containments proved by
exhibiting an explicit element of the lattice outside the target. Those are lower-bound
arguments and are sharp by construction; a weaker upper bound cannot corrupt them. The
non-sharp bounds are used only in the direction that proves exclusions, where a weaker bound can
fail to fire but cannot lie. **So the wave-55 failure mode is not present, and the sharpening is
an opportunity, not a correction.**

### 1.3 What the sharpening buys, and the honest limit

`gaTwoCenKill = <m = 3>` is excluded from the achievable stage-four lattice by `2 | m` alone, so
the sharper bound changes nothing about wave 63's or this wave's kills. Where it could matter is
anywhere the tree needs the class-three coordinates finer than mod 2: `stageN3_even` currently
hands out `2 | j`, `2 | l`, `2 | m` and could hand out `4 | j`, `2 | k`, `2 | l`, `2 | m`.

**Not done, and it is the obvious next step**: proving `forceLcs_two_le_stageN3'` in Lean. It
needs a `stageN3'` subgroup instance and the two `_of_commutator` coordinate lemmas, the same
shape as the committed ones, and is a self-contained wave-sized ticket.

---

## 2 Task B: the W63 cross-lane composite, RESOLVED - the answer is YES

**Question.** W63-LIVE5's witness reuses the committed `stageX` as its `x0` slot, which is the
slot W63-CENTRAL2's kill mechanism exploits. Does CENTRAL2's `gamma_2` kill apply at LIVE5's
point too?

**Answer: yes, in full, and the reason is that the two points share their `x0` slot.**

Proved in `GQ2/Dyadic/SqCore/GradedLiveGammaTwo.lean` (11 declarations, all std-3 pins):

* `gaTwoForces_liveBlkWit_false`, `gaTwoCentral_liveBlkWit_false`, `gaTwoOrth_liveBlkWit_false`:
  all three `gamma_2` lines FAIL at `liveBlkWit h j stageX`, at every handle count and every
  handle, with the very same killer `GradedGammaTwoCentral.gaTwoCenKill = <m = 3>`.
* `sqRelWord_liveBlkWit_cenKill`: the kill itself. `gaTwoShift_liveBlkWit_cenKill`: the shift is
  the central translation `liftO 7`, against the residue `liftO 1`.
* `liveCenKill_comm_form`: at the live point the killer is a **single** honest commutator of the
  point's own letters, `commP (liveBlkSig * stageX) (liveBlkV * liveBlkU⁻¹)`, where wave 63's
  point needed a product of two. `cenSigDress_liveCenKill_mem` turns that into membership of
  `forceLcs (liveBlkImage h j stageX) 1`.
* `liveCen_shared_x0`, `liveCen_knob`: the one-line reason.
  `stageWit h j stageX 1 = liveBlkWit h j stageX 1`, both `stageX`, so `cenKill_mechanism` is a
  statement about a slot the two points share.
* `liveCenKill_not_stageFour_achievable`: the boundary. The killer is not an achievable
  stage-four dressing, so `GradedFiveLive`'s stage-four and `gamma_3` exclusions stand.

**The modelling trap the orchestrator's spot-check fell into, avoided.** The BARE witness
`liveBlkWit h j 1` already kills the relator (`sqRelWord_liveBlkWit_triv`), so sweeping it for
kills is vacuous. The object is the DIAGONAL `a0 = a1` frame `liveBlkWit h j stageX`, whose
relator is `liftO 1`. `results/task_b.txt` section 0 records both.

**What this does and does not touch.** `GradedFiveLive` claims only the stage-four and `gamma_3`
exclusions at its point and never a `gamma_2` one, so nothing committed is contradicted. What is
removed is the hope that the new point is a fresh place for the class-five stack to stand one
filtration step wider. It is not.

**MEASURED** (`results/task_b.txt`, 56 named checks, 0 failures):

* the achievable `gamma_2` lattice at the live point is `2^26` and is exactly the **same box**
  `{gamma_2-shaped : f, g, h, j even}` wave 63 measured at its point;
* `forceLcs H 2` is `2^13` and does not contain `<m=3>`, so the killer sits strictly between the
  two lattices, as at wave 63's point;
* the exhaustive sigma-slot sweep: `1048576` dressings (exhaustive modulo the two coordinates
  `i`, `o` that the shift ignores), of which `16384` act centrally, `8192` of those move the
  class-five row oddly, and `2048` KILL - one eighth of the central ones, exactly what
  equidistribution over `ZMod 8` predicts;
* ⚠ **one genuine structural difference between the two points**: at wave 63's point the
  sigma-slot shift ignores the dressing's `i`, `j` and `o`; at the live point it ignores only `i`
  and `o` and **does** read `j`, because `liveBlkSig.d = 1` is odd where `fiveSigMark.d = 0`.
  The sweep was widened accordingly;
* ⚠ **the general mechanism, MEASURED and NOT proved**: at **every** five-tuple
  `fiveTuple R h j S X Y U V`, dressing the sigma slot by `<m = t>` multiplies the relator by
  `SqU6.liftO (t * X.e)`, with no hypothesis on `S, Y, U, V`, the handle count or the handle
  (3000 random tuples, 0 failures). If that were proved, both kills would be corollaries and the
  vulnerability would be visibly a property of the **witness standard** - which demands an odd
  `x0.e` (`D_gauge_x0_e_odd`) and an odd diagonal residue (`B_odd_residue`) - rather than of two
  particular points. This is the single highest-value proof target this lane found.

---

## 3 Task C: the legality audit, folded - one statement exists, no single column does

`scripts/w64_verify/task_c_legality.py`, output `results/task_c_legality.txt`, 7 named checks,
0 failures.

### 3.1 The one statement, and it covers all three points

The five abelian coordinates `a..e` of `SqU6` are group homomorphisms, so the abelian part of
`Phi g` depends only on the exponent vector `(a_s, a_0, a_1, a_U, a_V)` and equals `M . exponents`
for the point's `5 x 5` abelian column matrix `M`. **Legality is a condition on the exponents
alone and is the same condition at every point**:

```
lambda g = c a_s + a_0 + 2 a_1 = 0     (c = sqPivotExp, a unit; lambda kills every handle)
nu'    g = a_s = 0                     (at a fully cleared row)
```

so the legal exponent vectors form the **point-independent** lattice

```
L = { (0, -2t, t, u, v) : t, u, v in Z/8 },    |L mod 8| = 512.
```

**The single statement is `x0_ab not in M(L)`.** Verified exhaustively over all 512 legal
vectors at all three points:

| point | `|M(L)|` | `x0_ab` | reachable? |
|---|---|---|---|
| w60 `fiveFrameHom` | 64 | `(2,0,0,0,1)` | no |
| w61 `stageFrameHom` | 64 | `(2,0,0,0,5)` | no |
| w63 `liveBlkHom` | 128 | `(2,0,0,0,5)` | no |

This is the lemma the three lanes wanted: one hypothesis, one membership test, no per-point
column argument. Anyone moving the point again computes `M(L)` and checks one membership,
rather than inventing a fourth route.

### 3.2 The certified negative: no single column works everywhere

The hope that one abelian column suffices is **false**, exhaustively:

| column | mod 2 | mod 4 | mod 8 | works at all three? |
|---|---|---|---|---|
| `a` | no | w63 only | w63 only | no |
| `b` | no | no | no | no |
| `c` | no | no | no | no |
| `d` | no | no | no | no |
| `e` | w60 only | w60 only | w60 only | no |

No column at any modulus closes the door at all three. `x0.e` is unreachable at w60 and
reachable at both w61 and w63; `x0.a` is unreachable at w63 and reachable at both w60 and w61;
and **no single column works at w61 at all** - w61's route genuinely needs its two-step
`b`-then-`e` argument. So the three per-point routes are incomparable as a matter of fact, not
of presentation.

### 3.3 A free strengthening: `nu'`-triviality is not load-bearing

Dropping the `nu'` half entirely and keeping only `lambda g = 0` (with `a_s` free, and taking the
union over all four possible unit values of `sqPivotExp`, so the conclusion holds whatever
`sqPivotExp` is): `x0_ab` remains unreachable at **all three points**. So the legality obstruction
survives on the weaker hypothesis.

This matters because all three prose arguments use "`nu' g = a_s` at the cleared row", and `nu'`
is unconstrained on the `x1` slot and on handles other than the selected one - the step is the
weakest link in all three write-ups. It can be deleted: `lambda`-triviality alone suffices at
every point.

**Not done**: none of section 3 is formalised. Formalising it needs the abelianised exponent
vector of `D_sq h`, which the tree does not currently have as an object.

### 3.4 The fourth data point

`GradedBlockFrame` is not a fourth route; it is the observation that at statements quantifying
over the whole group or over an arbitrary relator-killing frame, there is no dressing class to be
legal in. The relator-killing hypothesis replaces legality, and `hu`/`hv` disappear with it. That
is consistent with 3.1: legality is exactly the condition that identifies a frame with a binder
POINT, and statements that never identify anything with a point never need it.

---

## 4 Task E: the bracket-convention audit

`scripts/w64_verify/task_e_bracket_convention.py`, output `results/task_e_bracket.txt`, 16 named
checks, 0 failures.

**The rule.** Lean and python agree: `commP x y = x⁻¹ y⁻¹ x y` (`GQ2/Words.lean:59`, and every
python library in `scripts/`). Mathlib's is `⁅x, y⁆ = x y x⁻¹ y⁻¹`, and
`⁅x, y⁆ = commP x⁻¹ y⁻¹` (`GradedFiveForce.commutatorElement_eq_commP`, re-verified here on 2000
random pairs). The two families are genuinely different: 1996 of 2000 random pairs differ. So a
python `commP` computation certifies a Lean statement written with `commP` **correctly**, and a
Lean statement written with `⁅.,.⁆` **incorrectly**.

**Scope of the gap in the tree.** The only Lean statements closed by `decide` that are written
with the mathlib bracket are `GradedStageFour`'s four `gap*Br` bracket censuses. The
`_of_commutator` lemmas in `GradedFiveForce`, `GradedFiveStageFour` and `GradedFiveNecessity` use
`⁅p, q⁆` but are proved by coordinate algebra, not by a script-certified `decide`. Every other
script-certified Lean statement in the tree is written with `commP`, including
`mixStage_breaker_mem`, `orthFive_quad_not_forceN4` and `gaTwoCenKill_comm_form`, so
`scripts/w61_sharp4/validate_sharp4.py` and the `find_*_point.py` searches match their targets.

**The one affected census, re-run in both conventions.** All four markings, `216` brackets each:

| marking | paper `commP` (what ran) | mathlib `⁅.,.⁆` (what the Lean says) |
|---|---|---|
| `gapOneA` | 0 violations of 216 | **0 violations of 216** |
| `gapOneB` | 0 violations of 216 | **0 violations of 216** |
| `gapTwoA` | 0 violations of 216 | **0 violations of 216** |
| `gapTwoB` | 0 violations of 216 | **0 violations of 216** |

**The conclusion survives at all four**, independently confirming `w64-psi4`. But the paper-run
was never a check of the `decide`'s input, and the sets really are different: at `gapOneA` the
paper convention gives 18 distinct brackets and mathlib 17, with an intersection of 10; at
`gapTwoA`, 12 and 12 with an intersection of 8.

**Convention IMMUNITY, and the good pattern.** A computation that takes the NORMAL CLOSURE over
the image cannot see the convention, because `H` is closed under inversion and
`⁅x,y⁆ = commP x⁻¹ y⁻¹`. Verified at four markings: the two normal closures agree exactly
(`2^13`, `2^13`, `2^10`, `2^8`). So

* every script that sifts a subgroup (`scripts/w63_central2/centrallib.py`'s `subgroup` and
  `derived_of`, and everything built on them) is **safe by construction**;
* only **raw bracket SETS** are at risk. In the tree those are `scripts/w61_sharp4/sharp4lib.py`
  lines 95-96 (`t3`, `t4`), `scripts/w62_separate/feasible2.py` lines 71-73 and the `find_*.py`
  searches. Each of those is a SEARCH producing a candidate point whose Lean statement is then
  written with `commP` and closed by `decide`, so a convention slip there costs a search, not a
  theorem - the `decide` is the ground truth in every case.

**Two patterns worth naming.** `centrallib.py` reads the `gamma_2` shift **off the relator**
rather than from an emitted closed form, so it is independent of every emitted form in
`GradedFiveGammaTwo`; and `scripts/w63_four/lean_match.py` re-checks the Lean letters coordinate
by coordinate rather than trusting a transcription. Both are the right shape. The missing third
member of that family is a convention assertion: **a certification script should state which
bracket its Lean target uses and compute that one.**

---

## 5 What is measured rather than proved

| claim | script | checks |
|---|---|---|
| the nine bounds' uniform sharpness and the two sharpened targets | `task_a_audit.py` | 60, 0 fail |
| the pointwise lattices at nine named markings | `task_a_audit.py` | in the same 60 |
| the exactness of the generator reduction, numerically | `task_a_audit.py` §3 | in the same 60 |
| the live point's `gamma_2` lattice, the sweep, the general shift identity | `task_b_live5_kill.py` | 56, 0 fail |
| the uniform legality criterion and the single-column negative | `task_c_legality.py` | 7, 0 fail |
| the bracket-convention audit and the re-run census | `task_e_bracket_convention.py` | 16, 0 fail |

Totals: **139 named checks, 0 failures**, in four scripts, all on the honest `6 x 6` matrices of
`scripts/w59_force5/u6mat.py` through the exact polycyclic sift of
`scripts/w63_central2/centrallib.py`. Nothing was rewritten that already existed.

---

## 6 What the next wave should do

1. **Prove the general sigma-shift identity** (2, last bullet). It subsumes two waves' kills and
   turns a per-point vulnerability into a property of the witness standard. Highest value.
2. **Prove `forceLcs_two_le_stageN3'`** with `stageN3' = {a..i = 0, 4|j, 2|k, 2|l, 2|m}`, and
   `forceLcs_one_le_stageN2'` with `2 | g` added (1.2). Self-contained, and it hands the whole
   class-five stack the class-three coordinates mod 4.
3. **Replace `GradedStageFour`'s copies** of `commLeft`/`commRight`/`commAll`/`le_of_gens_three`
   /`subset_normalizer_of_conj` by `LcsGens` and Mathlib's `le_set_normalizer_iff` (1.1).
4. **Apply the corrections of section 0.** They are docstring edits, not proof repairs, but two
   of them (0.1, 0.2) currently license inferences the proofs do not support.
5. **Formalise the uniform legality statement** (3.1), which needs the abelianised exponent
   vector of `D_sq h` as an object; and take the free strengthening of 3.3.
6. **Add a convention line to every certification script** (4), stating which bracket the Lean
   target uses.

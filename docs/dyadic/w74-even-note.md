# W74: the base's frame built, the climb's word replaced, the M row refuted

Lane W74-EVEN.  New module `GQ2/Dyadic/Instances/EvenStratumRowFrame.lean`; no edits to any
existing file.  Prefix `evenStratumRow` / `EvenStratumRow`.  49 declarations: 46 named public, 3
private.  All three tickets landed, plus wave 73's one untested prediction.

## 0.  Headline

Wave 73 left the surviving point with two blocked halves and one prediction.  All three moved.

> **The base's frame exists at the prescribed table.**
> `evenStratumRow_exists_adaptedFrame_vN_one`: at a third-stratum field of degree `2 + 2h` whose
> cyclotomic range attains `nUnit 1`, and given the EV-4a row lift supply at `vN 1`, there **is** a
> `StageGeneric.Frame` at the prescribed row table `vN 1` cup-adapted for the `alpha = 1` Gram.
> Wave 73's frame was at a table read off its own generators; this one is at the table
> `EvenStratumBaseN` names.
>
> **The climb's middle input is not merely repairable, it is gone.**
> `evenStratumRow_climb_defectReachable_one`: the `alpha = 1` stage climb runs on the residual
> supply and the deep row supply alone.  The third input of `evenClimb_defectReachable`, the
> crossed-derivation comparison `EvenSharpDbarShiftSupply` that wave 73 refuted at `alpha = 1`, is
> a **theorem** once the actual-defect supply is stated against the true `alpha = 1` word.
>
> **The M row fails at `alpha = 1` too, in mirror image.**
> `evenStratumRow_not_dbarShiftSupply_m_one`: the same committed `Prop` is false at the `M` word,
> at wave 73's cyclic group of order eight, with the correction moved from coordinate `0` to
> coordinate `2`.  N loses an atom; M gains one.

The classification at the surviving point is still **neither proved nor refuted**.  Nothing in
this lane asserts or denies `Nonempty (OrientedContinuousMulEquiv (chiN 1 h) chiCycKTwo)`.

## 1.  Ticket 1: the row-exact frame at `vN 1`

Wave 73's note called this "a bounded construction, not an open question about forms".  That is
right, and the construction is `evenFrame_of_adapted` with two substitutions.

### 1.1  The `alpha = 1` row of the bridge table (module §1)

`StageAbstractionEvenFrattiniFrameN.lean` §1 tabulates `nUnit alpha` mod 4, 8 and 16 for
`alpha >= 2` only.  The missing row is the opposite of every row present:

| `alpha` | `nUnit alpha` mod 16 | mod 8 | mod 4 | parity | `omega` |
|---|---|---|---|---|---|
| `1` | **`5`** | `5` | `1` | **`0`** | **`1`** |
| `2` | `3` | `3` | `3` | `1` | `1` |
| `3` | `7` | `7` | `3` | `1` | `0` |
| `>= 4` | `15` | `7` | `3` | `1` | `0` |

`evenStratumRow_nUnit_modFour/modEight/modSixteen`, from the committed `nUnit_mul` reduced in the
residue ring exactly as `evenBridgeN_nUnit_mul` does.  The two shadow tables of `vN 1` follow:
`evenStratumRow_parity_table` is **identically zero**, and `evenStratumRow_omega_table` is the
indicator of the letter `x1`.

Both flips are load-bearing, and they explain the `alpha = 1` case in one sentence: **the parity
column and the `omega` column exchange roles.**  At `alpha >= 2` the model forces the mod-four
class `kappa` onto the `x1` dual vector (the Gram is non-alternating, `kappa` is its Labute
vector), and the parity table is the `x1` indicator, so the match is free while the `omega` table
costs the hypothesis `EvenDegreeNModEightImage`.  On the third stratum `kappa = 0` (wave 71), the
Gram is alternating, nothing is forced, and it is the `omega` table that is the `x1` indicator.

### 1.2  Pinning the `omega` class (module §2, §3)

Because nothing is forced, the placement has to be done by hand.
`evenStratumRow_symplectic_pin` is `exists_symplectic_equiv` with its first hyperbolic pair
prescribed: for any nonzero `t`, some symplectic normal form has `phi t 0 = (0,1)` and `phi t` zero
on every other plane.  It is the outer step of `exists_symplectic_equiv_aux` run once with `t` in
the `v`-slot rather than the `w`-slot of `hypSplitEquiv`, which is what puts it in the *second*
coordinate; `t`'s own component in the complement is `t + t = 0`, which is why the pin is a single
plane.

`evenStratumRow_exists_gramOne_modelEquiv_pin` is then wave 73's
`evenStratum_exists_gramOne_modelEquiv` with that pin inserted, plane count fixed by the same
degree count.  Its one new hypothesis is `tau != 0`, and
`evenStratumRow_omegaClass_ne_zero` derives it: `nUnit 1 = 5 mod 8` and `omega(5) = 1`, so any
element with that cyclotomic value witnesses it.

### 1.3  The frame (module §4)

`evenStratumRow_frame_of_gramOne_adapted` is `evenFrame_of_adapted` verbatim with
`evenStratumGramOne` for `evenFrameGram` and wave 73's `evenStratum_levelTwoGen_of_realizers` for
the generation half; the row table stays a parameter, so the `M` row could consume it unchanged.
`evenStratumRow_exists_adaptedFrame_vN_one` instantiates at `vN 1`, discharging the two match
tables from §1: the parity table because **both sides vanish**, the `omega` table because §3 put
the class exactly where `nUnit 1 = 5 mod 8` demands.
`evenStratumRow_exists_adaptedFrame_of_rangeN_one` derives the row-value hypothesis from the
surviving point's own range identity through the committed `evenClimb_vN_mem_range`, which carries
no `2 <= alpha`.

**The binder ledger, against the committed `alpha >= 2` supply.**  Two binders go, one arrives:

* **gone**: the ramified-`i` binder `kappa != 0`.  It is not merely unavailable on the stratum,
  it is **false** there (wave 71).  The `alpha = 1` construction needs its negation instead.
* **gone**: `EvenDegreeNModEightImage`, whose only job at `alpha >= 2` is to pin `tau = c . kappa`.
  With `kappa = 0` that pin says nothing and is not used.
* **new**: `nUnit 1 ∈ im chi_cyc`, which is what makes `tau != 0` so that §2's pin has something to
  move.  Implied by the range identity.

Unchanged: the degree binder, and the EV-4a row lift supply `RowExactLevelFibreLiftSupply (vN 1)`,
carried exactly as the committed supply carries it.

### 1.4  What remains between this and `EvenStratumBaseN`

Wave 73 §5.3 named two obstacles.  **One is now discharged** (the row table).  The other is
untouched: the level-three relation `nRelWord 1 (levelMk 3 . generators) = 1`.  Cup-adaptedness for
`evenStratumGramOne h` is the statement that the relator's quadratic-initial form is realized on
the frame; converting that into the literal relation modulo `lambda_3` is the step
`StageAbstractionEvenLevelThree.lean` performs on the `alpha >= 2` side, and I did not run it.

## 2.  Ticket 2: the `alpha = 1` shift supply (module §5)

The queue asked for `EvenSharpDbarShiftSupply` rebuilt around `evenStratumShiftWordOne`.  The
answer is sharper than a rebuild: **there is nothing left to supply.**

The committed `Prop` exists because the comparison it asserts is not a theorem; wave 73's
`evenStratumShift_n_one` **is** the comparison at `alpha = 1`, at every profinite group and every
`k >= 3`, with no hypothesis.  So restating the machinery against the true word deletes the input:

* `evenStratumRow_wordOne_mem_zLayer`, `evenStratumRow_wordOne_one`,
  `evenStratumRow_coreOne_mul`, `evenStratumRow_wordOne_mul`: the `alpha = 1` word is a
  homomorphism on depth corrections.  The core proof is `evenRawCoreDbarWord_mul` minus its
  diagonal step, which was the only step using `evenRawSq_mul`.
* `EvenStratumRowActualDefectOne` and `EvenStratumRowActualDefectOne.toDefectReachable`: the
  actual-defect supply against the true word, and its passage to `Tuple.DefectReachable` with **no
  shift hypothesis**.
* `evenStratumRowResidualOne`, `EvenStratumRowResidualReachableOne`,
  `evenStratumRow_nonempty_actualDefectOne_iff_residual`: the residual and the reachability
  criterion, cloned by the torsor identity.
* `EvenStratumRowClimbResidualOne` and `evenStratumRow_climb_defectReachable_one`: the climb.

**The trade, stated so it is not over-read.**  The deep row supply is the committed `Prop`
verbatim.  The residual supply is **not** the committed `EvenClimbResidualSupply`: it is that `Prop`
with `evenRawDbarWord` replaced by `evenStratumShiftWordOne` in its two occurrences.  What is
genuinely deleted is the third input.  The climb is not easier; it is no longer blocked at a
**false** step, and the arithmetic it owes is the same arithmetic it always owed.

### 2.1  Wave 73's span prediction, tested (module §7)

Wave 73's queue item 2 ended with a prediction it marked as untested: the span "should come out
smaller, since the slot-zero square is gone, so `evenRawShiftSpan_eq_zLayer` may not clone."

**Correct, and this is its exact content.**

* `evenStratumRow_wordOne_zero_row`: the `alpha = 1` coordinate-`0` row is `[p, base 1]` alone,
  where the committed `evenRawDepthShiftHom_zero_apply` delivers `p^2 . [p, base 0] . [p, base 1]`.
* `evenStratumRow_wordOne_mem_bracketSpan`: **every** `alpha = 1` shift is a product of brackets
  `[p, base i]`.  The `alpha = 1` shift emits no square anywhere.
* `evenStratumRow_sq_mem_bracketSpan_of_isShift`: hence a pure square that is an `alpha = 1` shift
  is already a product of brackets.

So `evenRawShiftSpan_eq_zLayer_of_pureSquares` fails to clone not because a proof is missing but
because its `Hsq` input **cannot come from the `alpha = 1` rows at all**.  The compensation is real
and lies on the other side: at `alpha >= 2` the square and the bracket `[p, base 1]` sit in one
row, so neither is available without the other, which is why `evenRawBracket_base_mem_shiftSpan`
carries `Hsq`; at `alpha = 1` the bracket half is free.

I did **not** build the bundled span homomorphism or the six coordinate-row computations, so the
identity "the `alpha = 1` span equals the bracket subgroup" is proved in one direction only
(`<=`), together with the coordinate-`0` row in the other.  See §5 queue item 2.

## 3.  Ticket 3: the M twin (module §6)

Wave 73 predicted the `M` refutation and did not run it.  It is true.

`MarkedCore.mWord alpha a b c d = a^2 [a,b] c^(2^alpha) [c,d]`.  `evenRawMWord_mul_lambdaImage`
needs `2 <= alpha` because only then does `2^alpha = 2 . 2^(alpha-1)` have an **even** half, so
that `evenRawPow_of_even_half` kills the third letter's diagonal atom.  At `alpha = 1` the exponent
is `2 = 2 . 1` with an **odd** half, `evenRawPow_of_odd_half` applies, and the atom
`w2^2 . [w2, base 2]` survives.

* `evenStratumRow_mShift_one`: the true `M_1` shift is `evenStratumRowMWordOne`, which is
  `evenRawDbarWord` with the coordinate-`2` atom prefixed.
* `evenStratumRow_mShift_eq_atom_mul` measures the gap, and note the atom is on the **opposite
  side** of the equation from the `N` case: `N`'s `evenRawDbarWord = atom . trueShift`, `M`'s
  `trueShift = atom . evenRawDbarWord`.
* `evenStratumRow_not_dbarShiftSupply_m_one` refutes the committed `Prop` at
  `mStageWord 1 0`, at `EvenStratumShiftWitness` (wave 73's cyclic group of order eight), `k = 3`,
  trivial base, correction supported at coordinate `2` by `evenStratumShiftWitnessP`.
  `evenStratumRow_no_rawStageShift_m_one` is the same fact in `evenRawStageShift_m`'s own shape.

**Scope, exactly as wave 73 scoped the `N` side.**  What is refuted is the statement *quantified
over profinite groups*.  It does not decide
`EvenSharpDbarShiftSupply (mStageWord 1 h _) (maxProPQuotient 2 (GalK K)) k` at any particular
field; `evenStratumRow_mAtom_eq_one_of_rawShift` reduces that to whether the coordinate-`2` atom
vanishes there, and this lane says nothing about whether it does.

## 4.  Verification record

`scripts/mirror.sh sweep` once at lane start (5848 artifacts, cache at `608d3ded`), then
`scripts/mirror.sh check GQ2/Dyadic/Instances/EvenStratumRowFrame.lean` after every edit and
`scripts/mirror.sh gen GQ2.Dyadic.Instances.EvenStratumRowFrame` at each banking point.  Final run:
`OK`, no errors, no warnings.  No `lake` command was run at any point.  No `sorry`, no new axiom,
no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`, no `set_option`.

`#print axioms` is run on **all 46 named public declarations** (module §8), together with eight
comparison statements from waves 51, 72 and 73.  The three private helpers (two regrouping
identities and one shift assembler, re-declared because the originals are `private`) have no pins,
as in wave 73.  Measured:

| block | set |
| --- | --- |
| §1, §2, §5, §6, §7, §3's `omegaClass_ne_zero` and `coord_headSecond`, and the two local scalar instances (42 declarations) | std-3 |
| `evenStratumRow_exists_gramOne_modelEquiv_pin` | std-3 + `tateDualityAt` + `hilbertSymbol_normCriterion_finiteDyadic` + `absGalQ2_localEulerCharacteristic` |
| `evenStratumRow_frame_of_gramOne_adapted` | std-3 + `tateDualityAt` + `absGalQ2_isTopologicallyFinitelyGenerated` |
| the two `exists_adaptedFrame` headlines | the union of the previous two |

std-3 = `propext`, `Classical.choice`, `Quot.sound`.  Every pin is inside the even route's
committed sets, and the comparison is exact on both halves:

* the model-equivalence set is **identical** to wave 72's `evenStratum_no_cupAdaptedFrame`;
* the two headline sets are **identical** to the committed `alpha >= 2` supply
  `evenDegreeNCyclotomicFrattiniFrameSupply_holds` and to wave 73's
  `evenStratum_exists_gramOne_adaptedFrame`.

Tickets 2 and 3 and the span section are entirely arithmetic-free (std-3), matching
`evenClimb_defectReachable`, `evenSharpDbarShiftSupply_m` and
`evenRawShiftSpan_eq_zLayer_of_pureSquares`.

**[W76-HOUSE, sweep items 16, 17 and 18, three repairs to this verification block.**

*Item 16, the std-3 row.*  The 42 is right, but the blocks the row named summed to **40**:
§1 (10 pins), §2 (1), §5 (11), §6 (9), §7 (7) and the two scalar instances (2).  The two
missing are §3's `evenStratumRow_omegaClass_ne_zero` and `evenStratumRow_coord_headSecond`,
now named in the row above.  With them the table accounts for all 46: 42 + 1 + 1 + 2.

*Item 17, the comparison statements.*  Seven of the eight do date to waves 51, 72 and 73.
The eighth, `evenDegreeNCyclotomicFrattiniFrameSupply_holds`, is older: its declaration
landed at `61c51c9e`, **2026-08-07** ("land the even-degree N-row Frattini frame supply
(EV-3c1)"), before the wave-51 window; the name first appears two days earlier still, at
`de1b361f`, as a planned statement in the EV-3c skeleton.  Nothing about the axiom comparison
changes; only the provenance sentence does.

*Item 18, the private helpers.*  "Re-declared because the originals are `private`" is true of
`evenStratumRowRegroup` and `evenStratumRowShiftAssemble` and **false** of
`evenStratumRowAssembleM`, which is not a re-declaration of `evenRawAssembleM`
(`StageAbstractionEvenRawSpan.lean:558`): that one takes seven elements and two commutation
hypotheses and concludes `X*P*Y*Q*(A*B*C)`; this one takes **eight** elements and **three**
hypotheses and concludes `X*P*Y*Q*(Y₂*(A*B*C))`.  The extra slot `Y₂` is the coordinate-2
atom, which is the whole point of the `M` twin, so calling it a re-declaration hides the one
place the `M` shape shows up in the plumbing.  Round 11 §4.3(c) reported the same wording
defect one wave earlier at `EvenStratumShift.lean:75`, about a different pair.]**

Commits (branch `claude/w74-even`, based on `4fff1592`), all path-limited:

* `0adb30b6` record the alpha = 1 row of the even bridge table
* `7cdaec64` pin one nonzero vector in the symplectic normal form
* `db9b1d18` place the omega class at the x1 coordinate on the third stratum
* `e6fea078` build the cup-adapted frame at the prescribed row table vN 1
* `58857ee9` run the climb on the true alpha = 1 shift word
* `0068f1ab` refute the M row's committed shift comparison at alpha = 1
* `05e2f033` test wave 73's span prediction: the alpha = 1 shift is square-free
* `eb254082` remove em-dashes from the module prose

plus this docs-only commit.

## 5.  For the orchestrator

I edited nothing outside my own module and `docs/dyadic/w74-even-note.md`.

1. **`GQ2/Dyadic/Instances/EvenStratumRowFrame.lean` is unwired.**  Nothing imports it and it is
   not in `GQ2.lean`, exactly as `EvenStratumShift.lean` was left by wave 73.  Both are now
   unwired; the new module imports the old one, so registering them is one decision, not two.
2. **Wave 72's §3.1 first bullet should now be corrected a second time.**  Wave 73 already said the
   base is blocked by the *choice of Gram*, not the stratum.  With the repaired Gram the frame
   exists at the **prescribed** table too, so the base's remaining cost is the level-three
   relation and nothing else.
3. **`EvenUnramified.lean:70` and `:395`, and `StageAbstractionEvenRawSpan.lean`'s module
   docstring (lines 44-46 and 65)**, hedge the
   `alpha = 1` failure as attributed rather than proved.
   **[W75-HOUSE, round 11 §4.3(e): "§0" corrected.  That file's headers run §1 to §6 and it has
   no §0; the cited material is its module docstring.  Round 11 named five sites, all in waves
   72-73 prose, and this is a sixth, created by wave 74 one wave after the finding.  The label
   misdirects because the repo does use `§0` as a real heading elsewhere
   (`AdmissibleR.lean:77`, `OrientedTameBundle.lean:82`).]**  Wave 73 made the `N` half citable; the
   `M` half is now citable too (`evenStratumRow_no_rawStageShift_m_one`).  §4 of
   `StageAbstractionEvenRawSpan.lean` says both factorizations "need `2 <= alpha`"; both halves of
   that sentence are now theorems.
4. **The `alpha = 1` frame needs *fewer* arithmetic binders than the `alpha >= 2` one**, not more
   (§1.3).  Any status prose that prices the surviving point as strictly harder than `alpha >= 2`
   on the base side is wrong.

## 6.  Queue items this lane produces

1. **The level-three relation at `alpha = 1`.**  The only remaining gap between §4's frame and
   `EvenStratumBaseN`.  The `alpha >= 2` route runs from cup-adaptedness to
   `Frame.LevelThreeRelation` through `StageAbstractionEvenLevelThree.lean`; whether that passage
   is Gram-generic, and so applies to `evenStratumGramOne` unchanged, is the first thing to check.
   If it is, `EvenStratumBaseN` is discharged modulo the EV-4a row lift supply, and the surviving
   point reduces to the climb alone.
2. **The `alpha = 1` span, the other direction.**  §7 proves `span_1 <= bracketSpan` and computes
   the coordinate-`0` row.  The reverse containment needs the five other coordinate rows, which the
   committed file gets from `evenRawDepthShiftHom_*_apply` behind ~200 lines of index
   bookkeeping whose helper lemmas are `private`.  With it, `span_1 = bracketSpan` exactly, and the
   `alpha = 1` pure-square supply becomes a clean statement about a presented subgroup.
3. **`EvenRowDeepFibreLiftSupply 0`.**  Wave 73's queue item 4, still untouched:
   `evenClimb_deepRowSupply_n` carries `2 <= alpha`, and my §5.4 carries the depth-`s` supply
   as a binder without
   asking whether `s = 0` is free.  This is now the *only* undischarged input of the `alpha = 1`
   climb besides the residual supply.
4. **The `M` atom at the actual Galois quotient.**  Ticket 2's alternative, which I did not take:
   whether `c 2 ^ 2 . [c 2, base 2]` (or the `N` twin at coordinate `0`) vanishes at
   `maxProPQuotient 2 (GalK K)` for `K = Q_2(i)`.  Both reduce to whether `lambda_2` of that group
   has an element whose square escapes `lambda_4`, which is a question about the Demushkin
   structure of `G_K(2)` at `q = 4`, not an arithmetic congruence.  The mod-eight pattern of
   `evenStratumFrame_not_isSquare_neg_one` does not apply to it; I checked and it is a different
   kind of question.

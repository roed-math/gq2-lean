# W72: the cup-adapted frame refuted, and the surviving point unfolded

Lane W72-STRATUM.  New module `GQ2/Dyadic/Instances/EvenStratumFrame.lean`; no edits to existing
files.  Prefix `evenStratum` / `evenStratumFrame`.  23 declarations.  All three tickets landed.

## 0.  Headline

> **The two `q`s** (gloss added at W74-HOUSE, because this note runs on bare `q` for over a
> hundred lines).  Every bare `q` below is **`demushkinQ`**, the order of the torsion subgroup
> of the abelianization (`GQ2/Demushkin.lean:224`).  It is **not** `qOf K FF = 2^f`, the
> residue cardinality that the presentation relator `tau^sigma = tau^q` and `params.qK` use;
> that one is written `q_K` throughout the campaign.

Wave 71 refuted the *coordinate step* of the even frame producers on the third stratum.  This
lane refutes the object those producers deliver.

> **`evenStratum_no_cupAdaptedFrame`**: at a field whose cyclotomic range lies in
> `evenRangePrin 2` and whose degree is `2 + 2h`, and at **every** row table
> `v : Fin (coreRank h) -> Z_2^x`, there is **no** `StageGeneric.Frame` at `v` that is
> cup-adapted for the even quadratic-initial Gram `evenFrameGram h`.

That is what `evenFrame_of_adapted` assembles and what `EvenDegreeNCyclotomicFrattiniFrameSupply`
and its `M` twin conclude, so it is the frame step itself and not one implementation of it.
`evenStratum_no_cupAdaptedFrame_KNegOne` instantiates it at `Q_2(i)`.

The classification at the surviving point is still **neither proved nor refuted**.  §6 of the
module states an implication *into*
`Nonempty (OrientedContinuousMulEquiv (chiN 1 h) chiCycKTwo)` and names its two unproved
hypotheses; no declaration in this lane asserts or denies that `Prop`.  I held wave 71's line.

## 1.  Ticket 1: the frame, not only the model

The route wave 71 wrote down used nondegeneracy of the cup form.  It is not needed, and the
statement is cleaner without it.  What the proof actually uses:

1. **`evenStratumFrame_gram_diag`** (std-3).  `evenFrameGram h` contracted against a rank-one
   matrix `M i j = f i * f j` is `f 0`.  Every bracket of the head and of the `sigma`, `x_2`
   plane cancels in characteristic two, every handle plane cancels, and `f 0 * f 0 = f 0`.
   So `Frame.IsCupAdapted` forces `P c c = ` the value of `c` at the *zeroth generator*, for
   every continuous mod-two character `c`.
2. **`evenStratumFrame_eval_gen_zero`**.  `P c c` is the field cup form on the diagonal, which
   is `0` on this stratum by wave 71's `evenStratum_cup_self_eq_zero`.  Every degree-one class
   is a character class (`evenStratumFrame_exists_character`, the `hcz` step extracted from
   `frattiniFrameEval_eq_of_levelMk_eq`), so every class evaluates to `0` at `F.generators 0`.
3. **`evenStratumFrame_eq_zero_of_eval_gens`**.  Mod-two characters kill `lambda_2`, so
   `Frame.levelTwoGen` promotes vanishing on the generators to vanishing everywhere.  This is
   where nondegeneracy would have been used and is not: the frame's own generation field does
   the work, which is why the conclusion carries **no reciprocity bundle and no ramification
   binder**.
4. **Counting.**  The coordinate map `H^1 -> (Fin (coreRank h) -> F_2)` is therefore injective;
   both sides have `2 ^ (4 + 2h)` elements by `card_H1_zmodTwo_maxProTwoGalK` and the degree
   hypothesis, so it is a bijection, so some class has coordinate `1` at index `0`.  That
   contradicts step 2.

The degree hypothesis is the price of step 4 and is why the `Q_2(i)` corollary needs a degree
computation that wave 71's did not.  `-1` is not in the committed non-square list (the five rows
`+-2, 5, +-10` are all handled by the valuation criterion, and `-1` is a unit), so
`evenStratumFrame_not_isSquare_neg_one` redoes `not_isSquare_five`'s mod-eight count at `-1`;
`evenStratumFrame_finrank_KNegOne` is then `[Q_2(i) : Q_2] = 2 + 2*0`.

**On "the right frame":** wave 71 warned that a neighbour conflated `MarkedCore.NFrame` with
`StageGeneric.Frame`.  The object here is `StageGeneric.Frame` (`StageAbstraction.lean:793`) and
the predicate is `StageGeneric.Frame.IsCupAdapted` (`StageAbstraction.lean:815`), the one whose
`gram` and `P` parameters are instantiated at `evenFrameGram h` and `evenFramePairing` by
`StageAbstractionEvenFrattiniFrameN.lean:344`, `StageAbstractionEvenEndpoint.lean:349,870`, and
`evenFrame_of_adapted`.  `MarkedCore.NFrame` does not occur in the module.

## 2.  Why this is not a refutation of the classification

The Gram refuted is the `alpha >= 2` shape.  `evenFrameGramModel h` is non-alternating
(`evenFrameGramModel_self`), which is the `q = 2` shape and matches the even lane's standing
ramified-`i` binder `kappa != 0`.  On the third stratum `kappa = 0`, the field cup form is
alternating, and wave 70 computed `demushkinQ (D_N 1 h) = 4`.  So the two sides agree on the
invariant and disagree only about *which* Gram a frame should be adapted to.  A forward-generator
tuple at `alpha = 1` is not required to be cup-adapted for `evenFrameGram h`, and §6's reduction
is untouched by §4.

`evenStratum_baseN_frame_not_cupAdapted` is the seam, stated in Lean: on the stratum, the frame
witnessing a level-three base is *never* cup-adapted for `evenFrameGram h`.  The base is not
refuted; the committed route to it is.

## 3.  Ticket 2: the surviving point, unfolded

Wave 71 said the whole remaining price is "one `Prop`".  That `Prop` is a **structure with nine
fields**, so the phrase understates it.  Unfolded against the committed tree:

> **[W74-HOUSE, watch round 10.]  "ten" was wrong; `NForwardGeneratorData` has nine fields**
> (`generators`, `relation`, `topGen`, `x0`, `x1`, `sigma`, `x2`, `handleU`, `handleV`), and the
> breakdown below refutes the count on its own: six row fields plus three others is nine.
> Corrected here and at the two Lean sites in `EvenStratumFrame.lean`; the owner memo's copy was
> corrected at `f4a458a8`.  The substance is unaffected, the point being that "one `Prop`"
> understates the price.

* **Six row fields are free.**  `x0`, `x1`, `sigma`, `x2`, `handleU`, `handleV` are the `vN 1`
  table entry by entry, and `evenClimb_vN_mem_range` carries **no** `2 <= alpha`, so every value
  is attained once the range is `imChiN 1`.  Recorded as `evenStratum_vN_one_mem_range`.  The
  obstruction at `alpha = 1` is not in the values.
* **The other three interact.**  A tuple must have those values *and* generate *and* kill the
  relator.  The committed assembly of exactly that is
  `evenForwardGeneratorDataN_of_base_and_corrections`, whose own binder is `1 <= alpha`, so it
  applies here unchanged.  Its two inputs are a level-three stage tuple and defect reachability
  from level three up, and a level-three stage tuple is a `StageGeneric.Frame` whose relator dies
  modulo `lambda_3` (`Frame.toLevelThree`, which converts Frattini generation into topological
  generation).

So the deliverable is two named `Prop`s and one implication:

> **`EvenStratumBaseN K h`**: there is a `StageGeneric.Frame` at the `vN 1` row table whose
> relator dies modulo `lambda_3`.  Unfolded by `evenStratumBaseN_iff` into three explicit
> conditions on a tuple `g : Fin (coreRank h) -> G_K(2)`: exact cyclotomic values `vN 1`,
> Frattini generation, and `nRelWord 1 (levelMk 3 . g) = 1`.
>
> **`EvenStratumClimbN K h`**: `Tuple.DefectReachable` for every level-`k` stage tuple at the
> `N_1` word datum, `k >= 3`.
>
> **`evenStratum_orientedEquivN_one_of_base_and_climb`**: at degree `2 + 2h`, those two give
> `Nonempty (OrientedContinuousMulEquiv (chiN 1 h) chiCycKTwo)`.

Composed with wave 71's `evenStratum_orientedEquivN_one_of_forwardGeneratorData`, whose other
two inputs are already discharged at `alpha = 1` (the depth binder `1 <= 1`, and wave 70's
`evenAlphaOne_nModelDemushkin`).

### 3.1  Both halves have a *blocked* committed route, not merely an unproved one

This is the sharpest thing the lane learned about ticket 2, and it is recorded in the
`EvenStratumClimbN` docstring rather than as a theorem, because the second half is prose in
someone else's file.

* **The base.**  Blocked by §4 of this module: its frame can never be cup-adapted for
  `evenFrameGram h`, and cup-adaptation is the shared step of all three even frame producers.
* **The climb.**  `evenClimb_defectReachable` has three inputs, all supplied on the `N` row only
  under `2 <= alpha`: the residual supply at depth `alpha - 1`, the `d-bar` shift supply
  `evenSharpDbarShiftSupply_n`, and the deep row supply `evenClimb_deepRowSupply_n`.  The middle
  one is `evenRawStageShift_n`, and `StageAbstractionEvenRawSpan.lean`'s module docstring
  records **in prose**
  that the factorization's coordinate-`0` row is *false* at `alpha = 1`.  I did not verify that
  claim; I am reporting it as an attributed prose claim, and it agrees with wave 71 §1(b).

So a future lane attacking the surviving point has to replace two committed steps, not one, and
neither replacement is a matter of weakening a binder.

### 3.2  What I did **not** reduce

I did not reduce `EvenStratumClimbN` further, and I did not attempt to build either half.  The
natural next question, not attempted: at `alpha = 1` the residual supply's depth is
`alpha - 1 = 0`, and I do not know whether `EvenClimbResidualSupply 0` is degenerate, free, or
false.  That is one cheap lane's worth of reading.

The other natural next question, also not attempted: §2 says the alternating cup form on the
stratum is *compatible* with a frame adapted to the `alpha = 1` Gram.  Computing that Gram (the
quadratic-initial form of `nRelWord 1`, which is **not** `evenFrameGram h`, since the latter is
`alpha`-independent and built from `MarkedCore.nGram`) and asking whether an adapted frame exists
for **it** is the correct repair of the frame step at `alpha = 1`.  I state this as a queue item,
not as a claim that it works.

## 4.  Ticket 3: the `q >= 8` boundary, as theorems

Wave 69 queue item 4 and wave 71 queue item 4 both recorded this in prose.  Two statements now:

* **`evenStratum_two_add_two_pow_eq_two_pow`**: `2 + 2^a = 2^b` implies `a = 1` and `b = 2`.
  Restated at the campaign's named exponent as `evenStratum_pAlpha_eq_pow_two_iff`:
  `pAlpha a = 2^b <-> (a = 1 and b = 2)`.  `pAlpha alpha = 2 + 2^alpha` is the `x_0` exponent of
  the `N_alpha` core `x_0^{p_alpha}[x_0,x_1][sigma,x_2]`.
* **`evenStratum_demushkinQ_DN_le_four`**: `demushkinQ (D_N alpha h) <= 4` for every
  `alpha >= 1` and every handle count, composed from wave 70's `nFrame4_demushkinQ_DN_one`
  (`= 4` at `alpha = 1`) and the committed `nFrameExists_demushkinQ_DN` (`= 2` at `alpha >= 2`).
  Hence `evenStratum_demushkinQ_DN_ne_pow_two`: no member of the present `N` family has
  `q = 2^b` with `b >= 3`.

Both are **about the family, not about fields**.  `Q_2(zeta_8)` has `demushkinQ (G_K(2)) = 8`
(its residue cardinality `q_K` is `2`, the extension being totally ramified); the content is only
that it is not one of these cores, so reaching it needs a new core family.  Note also that the
second statement needs no arithmetic: the two committed computations already close the range.

## 5.  Verification record

`scripts/mirror.sh sweep` once at lane start (5813 artifacts, cache at `6db3ee88`), then
`scripts/mirror.sh check GQ2/Dyadic/Instances/EvenStratumFrame.lean` after every edit.  Final
run: `OK`, no errors, no warnings, no `sorry`.  No `lake` command was run.  No `sorry`, no new
axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.

`#print axioms` is run on all 23 declarations inside the module (§8), together with the three
statements §6 stands against.  **They are not three `alpha >= 2` analogues** (corrected at
W74-HOUSE): `evenForwardGeneratorDataN_of_base_and_corrections` carries `1 <= alpha`, only
`evenAlphaTwo_forwardGeneratorDataN_of_residual` carries `2 <= alpha`, and
`evenStratum_orientedEquivN_one_of_forwardGeneratorData` is wave 71's own statement fixed at
`alpha = 1`.  The same wrong phrase was in the Lean comment at `EvenStratumFrame.lean:585` and is
corrected there too.  Measured pins:

| block | set |
| --- | --- |
| §1, §2, §5's `not_isSquare`/`finrank`, §6's rows and `iff`, §7 all | std-3 |
| `evenStratumFrame_pairing_self` | std-3 + `tateDualityAt` |
| `evenStratumFrame_eval_gen_zero` | std-3 + `tateDualityAt` + `hilbertSymbol_normCriterion_finiteDyadic` |
| the three `no_cupAdaptedFrame` statements, `baseN_frame_not_cupAdapted` | the previous set + `Foundations.absGalQ2_localEulerCharacteristic` |
| `evenStratum_forwardGeneratorDataN_one_of_base_and_climb` | std-3 + `Foundations.absGalQ2_isTopologicallyFinitelyGenerated` |
| `evenStratum_orientedEquivN_one_of_base_and_climb` | std-3 + `tateDualityAt` + both `Foundations` axioms |

Per statement, against the three printed beside it (the blanket claim that stood here, "every one
of these is a subset", was **deleted at W74-HOUSE**: the next sentence refutes it, the composite
being a strict *superset*, and the fourth table row has no printed comparison at all).
`evenAlphaTwo_forwardGeneratorDataN_of_residual` pins exactly
`std-3 + Foundations.absGalQ2_isTopologicallyFinitelyGenerated`, the same as my
`forwardGeneratorDataN_one_of_base_and_climb`; and
`evenStratum_orientedEquivN_one_of_forwardGeneratorData` (wave 71) pins
`std-3 + tateDualityAt + Foundations.absGalQ2_localEulerCharacteristic`, so my composite adds
only the topological-finite-generation axiom, from
`LSquare.maxProTwoGalK_isTopologicallyFinGen`.

Commits (branch `claude/w72-stratum`, based on `e2e8917a`), all path-limited:

* `fbe09a18` refute the cup-adapted stage frame on the third stratum
* `311d1795` instantiate the frame refutation at the model field Q_2(i)
* `7fea99fe` unfold the surviving point into a base and a climb
* `743e4ffb` state the q >= 8 boundary as a theorem instead of prose
* `be513bec` record where the climb's committed route is blocked at alpha = 1

## 6.  Stale prose found, for the orchestrator

I edited nothing outside my own module.

1. ~~**Wave 71's `EvenForwardRouteSkeleton.lean:77-80` report stands** and is still
   unrepaired.~~  **[W74-HOUSE: false when written.]**  The orchestrator applied the repair at
   `e6d10612` (2026-08-12 12:53), **three hours and twelve minutes before this note was committed**
   (`60bfaab6`, 16:05), and `w72-house-note.md` §2.4b(d) marks it discharged.  Trunk therefore
   carried two contradicting notes on this item from wave 72 until now.  One residue does survive
   and is fixed this wave: the applied notice at `EvenForwardRouteSkeleton.lean:81` is headed
   "Corrected at wave 70", but `e6d10612` sits on `dyadic` after the two wave-71 merges and cites
   wave 70's landings as its *evidence*, so the correction was applied at **wave 71**.
2. **Wave 71 queue item 1 is discharged** by §4; item 4 is discharged by §7.  Item 2 (close the
   wave-69 `q`-parametrised frame as a non-item) and item 3 (the even route's status prose) are
   still open, and §4 sharpens what item 3 should say: not merely that the frame step is refuted
   on the stratum, but that no cup-adapted frame exists there at any row table, so the two
   remaining costs at the surviving point are a base and a climb, each with a blocked committed
   route.

## 7.  Queue items this lane produces

1. **Compute the `alpha = 1` quadratic-initial Gram of `nRelWord 1`** and ask whether a frame
   adapted to *it* exists on the stratum.  `evenFrameGram h` is `alpha`-independent (it is built
   from `MarkedCore.nGram` plus one hyperbolic plane per handle), so it cannot be the `alpha = 1`
   form; §2 above shows the alternating field cup form is compatible with a different Gram.  This
   is the correct repair of the frame step, and §4 says exactly why the current one cannot be
   repaired in place.
2. **Read `EvenClimbResidualSupply 0`.**  At `alpha = 1` the residual supply's depth collapses to
   `0`.  Half a lane of reading decides whether that half of `EvenStratumClimbN` is degenerate,
   free, or false, and it is the cheapest remaining question about the surviving point.
3. **Verify or refute the prose claim** that `evenRawStageShift_n`'s coordinate-`0` row is false
   at `alpha = 1` (`StageAbstractionEvenRawSpan.lean`, module docstring, lines 44-46 and 65).
   If it is false,
   `EvenStratumClimbN` is blocked at a *named* step and the surviving point's cost is two
   genuinely new constructions; if the prose is stale (this era's recurring trap), one of the two
   halves may be cheaper than advertised.
4. **The `M` twin of §4.**  `evenFrameGram h` is core-agnostic (`mGram_eq_nGram` is a `rfl`), and
   `evenFramePairing` is the same, so `evenStratum_no_cupAdaptedFrame` as stated already covers
   the `M` row's frame: it quantifies over every row table `v`, including `vM alpha`.  Worth one
   line in the status prose rather than a lane.

# W73: the prose verified, the Gram repaired, and depth zero read

Lane W73-STRATUM.  New module `GQ2/Dyadic/Instances/EvenStratumShift.lean`; no edits to existing
files.  Prefix `evenStratumShift` / `evenStratumGramOne` / `evenStratumResidual` / `evenStratum`.
55 declarations: 44 named public, 6 private, 5 anonymous instances on the witness group.  All
three tickets landed.

## 0.  Headline

Wave 72 left the surviving point with two blocked halves.  This lane settles the status of both
blocks, and they come out differently.

> **The climb's block is real.**  `evenStratum_not_dbarShiftSupply_one`: the committed
> `EvenSharpDbarShiftSupply` is **false** at `alpha = 1` at a named profinite group, so
> `evenRawStageShift_n`'s conclusion is false there and not merely unproved.  The prose in
> `StageAbstractionEvenRawSpan.lean` §0 is correct, and the failure is exactly one atom wide.
>
> **The base's block is an aiming error.**  `evenStratum_exists_gramOne_adaptedFrame`: on the
> third stratum, at degree `2 + 2h`, a `StageGeneric.Frame` cup-adapted for the `alpha = 1`
> quadratic-initial Gram **exists**.  Read against wave 72's `evenStratum_no_cupAdaptedFrame`,
> which says none exists for `evenFrameGram h` at any row table, the frame step fails on the
> stratum because it is aimed at the wrong Gram, not because frames are unavailable there.

The classification at the surviving point is still **neither proved nor refuted**.  Nothing in
this lane asserts or denies `Nonempty (OrientedContinuousMulEquiv (chiN 1 h) chiCycKTwo)`.  §5.3
of the module states in Lean's own prose what §5.2 does *not* deliver: a frame at the
**prescribed** row table `vN 1`, which is what `EvenStratumBaseN` needs.

## 1.  Ticket 1: the `alpha = 1` shift, verified and refuted

The campaign has been burned three times by relayed prose.  This one is true.

`MarkedCore.nWord 1 a b c d = a^4 [a,b][c,d]`, and `4 = 2 * 2` has an **even** half, so
`evenRawPow_of_even_half` applies exactly where `evenRawPow_of_odd_half` applies at `2 <= alpha`.
The diagonal atom `w0^2 * [w0, base 0]` never appears.

* **`evenStratumShift_n_one`** is the true literal factorization at `alpha = 1`, with no
  `2 <= alpha` anywhere: `stageShift (nStageWord 1 h _) base correction =
  evenStratumShiftWordOne base correction`, where `evenStratumShiftWordOne` is
  `evenRawDbarWord` with the diagonal atom deleted.  A future lane rebuilding the shift supply
  at `alpha = 1` has its factorization already available.
* **`evenStratumShift_dbarWord_eq_diagonalAtom_mul`** measures the gap exactly:
  `evenRawDbarWord base c = (c 0 ^ 2 * [c 0, base 0]) * stageShift (nStageWord 1 h _) base c`.
  So the `alpha >= 2` conclusion holds at `alpha = 1` for given data **iff** that atom is `1`.
* **`evenStratum_not_dbarShiftSupply_one`** refutes it, at the committed `Prop` itself:
  `EvenSharpDbarShiftSupply (nStageWord 1 0 _) EvenStratumShiftWitness 3` is false.  The witness
  is the smallest possible one: the cyclic group of order eight with its discrete topology,
  `k = 3`, `h = 0`, trivial base, and the correction supported at coordinate `0` by the image of
  the square of a generator.  That element lies in `lambdaImage G 2 4` by
  `sq_mem_twoCentralSeries_succ`, and its square is nontrivial in `Q_4` because `lambda_4 = bot`
  there.  `evenStratum_no_rawStageShift_one` is the same fact in the shape of
  `evenRawStageShift_n`'s own conclusion.

**Scope, stated so it is not over-read.**  What is refuted is the statement *quantified over
profinite groups*, which is the form both `evenRawStageShift_n` and `evenSharpDbarShiftSupply_n`
have.  It does **not** decide
`EvenSharpDbarShiftSupply (nStageWord 1 h _) (maxProPQuotient 2 (GalK K)) k` at any particular
field.  `evenStratumShift_diagonalAtom_eq_one_of_rawShift` reduces that question to whether the
diagonal atom vanishes there, and this lane says nothing about whether it does.

The tower computation is two reusable lemmas: `evenStratumShift_twoCentralSucc_le` (a discrete
abelian group's two-central step is contained in anything absorbing the squares of its input) and
`evenStratumShift_twoCentralSeries_le_pow` (`lambda_{k+1} <= A^{2^k}` for discrete abelian `A`).
Their hypotheses are satisfied by the witness, not merely general in the binders.

**Consequence for the tree.**  `evenSharpDbarShiftSupply_n` is `evenRawStageShift_n` verbatim, and
it is the middle input of `evenClimb_defectReachable` on the `N` row.  So the committed route to
`EvenStratumClimbN` is blocked at a **named** step whose general form is now known false, and the
surviving point's climb needs a genuinely new shift word, not a weakened binder.

## 2.  Ticket 2: wave 72's queue item 1 was half stale

**The `alpha = 1` Gram already existed.**  Wave 70's `EvenAlphaOne.evenAlphaOneNCupForm`
(`EvenAlphaOne.lean` §3) is the quadratic-initial form of `nRelWord 1`, *derived* from
`evenAlphaOne_nRelWord_fib` and identified with the relator obstruction by
`evenAlphaOne_obsH2_DN`.  Wave 72 asked for it to be computed; it was computed three waves
earlier.  What was genuinely missing is the bridge into the shape `Frame.IsCupAdapted` demands,
which takes the Gram as a function of the full matrix of character products.

* **`evenStratumGramOne`** is that bridge, and `evenStratumGramOne_alphaOneNCupForm` checks it
  against wave 70's form on the nose (`rfl`).  No Gram is invented.
* **`evenStratumGramOne_add_diag`**: `evenFrameGram h M = M 0 0 + evenStratumGramOne h M`.  One
  entry, and it is the frame shadow of ticket 1: the diagonal atom the `alpha = 1` parity kills is
  the same atom that produces the `(0,0)` entry.
* **`evenStratumGramOne_diag`**: contracting against a rank-one matrix gives `0`, where
  `evenStratumFrame_gram_diag` gives `f 0`.  This single line is why wave 72's refutation cannot
  be reproduced: the step that turned cup-adaptedness into a statement about one generator now
  produces `0 = 0`, and `0 = 0` is wave 71's `evenStratum_cup_self_eq_zero`.

Then the positive half, which is the actual answer:

* **`evenStratum_exists_gramOne_modelEquiv`**: on the stratum at degree `2 + 2h` there **is** a
  linear isomorphism `H^1(G_K(2), F_2) ~= evenFrameModel h` carrying the field cup form to
  `evenStratumGramOneModel h`.  This is the statement wave 71 refuted for
  `evenFrameGramModel h`, with the `alpha = 1` Gram in place of the `alpha >= 2` one and the
  degree pinned - the rank count needs it, where wave 71's refutation did not.  The proof
  applies the committed `FieldDataEven.exists_cupForm_normalForm_alternating` directly to
  `frattiniFrameCup` (whose `IsCupFormFp2`, `NondegFp2` and Labute facts are all committed), with
  Labute vector `0` by wave 71's `evenStratum_kappa_eq_zero`, and pins the plane count at `h + 2`
  by `card_H1_zmodTwo_maxProTwoGalK`.
* **`evenStratum_frame_of_gramOne_modelEquiv`** turns that into a frame, and
  **`evenStratum_exists_gramOne_adaptedFrame`** is the composite.
  `evenStratum_exists_gramOne_adaptedFrame_KNegOne` instantiates at `Q_2(i)`, at the same field
  and under the same standing profinite binders at which
  `evenStratum_no_cupAdaptedFrame_KNegOne` refutes one for `evenFrameGram 0`.

`evenStratum_levelTwoGen_of_realizers` is extracted from the middle of `evenFrame_of_adapted` as
reusable, Gram-free tooling: realizers of a coordinate system generate the Frattini quotient.  Its
hypotheses are discharged by the realizers of any linear isomorphism onto `evenFrameModel h`,
which is how §5.2 uses it.

### 2.1  What §5.2 does not give

`Frame v G chi` pins cyclotomic values **on the nose** and §5.2 reads `v` off its own generators
after the fact.  A level-three base needs the prescribed table `vN 1`.  Between §5.2 and
`EvenStratumBaseN` stand exactly two things, neither touched here:

1. row exactness at `vN 1` (`evenFrameExactLift`, which wants a `RowExactLevelFibreLiftSupply`);
2. the level-three relation `nRelWord 1 (levelMk 3 . generators) = 1`.

## 3.  Ticket 3: `EvenClimbResidualSupply 0` is open, and now for a sharper reason

`evenClimb_defectReachable` is generic in the depth `s`; the `alpha >= 2` route runs it at
`s = alpha - 1`, so the `alpha = 1` route would run it at `s = 0`.  Two facts, pointing opposite
ways.

* **The recorded obstruction is vacuous at depth zero.**
  `evenRouteAudit_residual_digit_necessary` extracts from reachability the character-digit
  condition `2^(k+1+s) | chi(r) - 1` on a representative of the residual, and
  `evenRouteAudit_residual_digit_automatic` records that the tree gives only `2^(k+alpha-1)` for
  free through `EvenSharpPmOne alpha`: at `alpha >= 2`, a one-digit gap.  But the **generic** tower
  bound `twoCentralSeries_units_le` gives `2^(k+1)` with no bound hypothesis at all, because the
  residual lies in `lambda_k`.  At `s = 0` that is exactly the demanded level.
  **`evenStratum_residual_digit_zero_automatic`**: the demand holds for every admissible
  correction, reachable or not.  At `s >= 1` it does not, since `k + 1 < k + 1 + s`.
* **Depth zero does not make the supply free.**  What depth zero hands over is
  **`evenStratumNeutralOfZLayer`**: at `s = 0` the neutrality demand *is* the tower's own bound, so
  the whole central layer `zLayer G k` qualifies as a neutral correction.  But
  **`evenStratum_dbarWord_eq_one_of_zLayer`** shows the literal shift word of a `zLayer`-valued
  correction is trivial - every bracket dies by centrality, the slot-zero square by `zLayer_sq` -
  so by **`evenStratum_zLayerNeutral_reaches_iff`** the free supply reaches the residual precisely
  when the residual is already `1`.

So the answer to "degenerate, free, or false" is **none of the three**.  Whatever discharges
`EvenClimbResidualSupply 0` has to produce a neutral correction with a coordinate *outside* the
central layer, which is the same demand as at every other depth.  The gain over `alpha >= 2` is
real but narrower than hoped: the one recorded obstruction is gone, and no new one replaces it.

## 4.  Verification record

`scripts/mirror.sh sweep` once at lane start (5833 artifacts, cache at `a515b437`), then
`scripts/mirror.sh check GQ2/Dyadic/Instances/EvenStratumShift.lean` after every edit, and
`scripts/mirror.sh gen GQ2.Dyadic.Instances.EvenStratumShift` at the end.  Final run: `OK`, no
errors, no warnings.  No `lake` command was run.  No `sorry`, no new axiom, no `native_decide`, no
`maxHeartbeats`, no `maxRecDepth`.

`#print axioms` is run on **all 44 named public declarations** inside the module (§7), together
with three comparison statements from waves 71 and 72.  The five anonymous instances on the
witness group (`TopologicalSpace`, `DiscreteTopology`, `ContinuousMul`, `ContinuousInv`,
`IsTopologicalGroup` on `Multiplicative (ZMod 8)`) have no user-written names and are not pinned;
they are `bot`, `rfl`, and `continuous_of_discreteTopology`.  Measured pins:

| block | set |
| --- | --- |
| §1, §2, §3 (all of ticket 1) | std-3 |
| §4 all (the Gram and its model) | std-3 |
| §6 all (ticket 3) | std-3 |
| `evenStratum_levelTwoGen_of_realizers` | std-3 + `absGalQ2_isTopologicallyFinitelyGenerated` |
| `evenStratum_exists_gramOne_modelEquiv` | std-3 + `tateDualityAt` + `hilbertSymbol_normCriterion_finiteDyadic` + `absGalQ2_localEulerCharacteristic` |
| `evenStratum_frame_of_gramOne_modelEquiv` | std-3 + `tateDualityAt` + `absGalQ2_isTopologicallyFinitelyGenerated` |
| the two `exists_gramOne_adaptedFrame` statements | the union of the previous two |

std-3 = `propext`, `Classical.choice`, `Quot.sound`; `evenStratumShiftWitness_pow_eight` prints
only `propext`, `Quot.sound`.

Every pin is inside the even route's committed sets.  The comparison is exact:
`evenStratum_no_cupAdaptedFrame` (wave 72) prints
std-3 + `tateDualityAt` + `hilbertSymbol_normCriterion_finiteDyadic` +
`absGalQ2_localEulerCharacteristic`, so my existence statement adds only
`absGalQ2_isTopologicallyFinitelyGenerated`, which is the same set wave 72's
`evenStratum_orientedEquivN_one_of_base_and_climb` prints.  Ticket 1 and ticket 3 are entirely
arithmetic-free.

Commits (branch `claude/w73-stratum`, based on `6a8fbc90`), all path-limited:

* `7716d263` verify the alpha = 1 shift prose and refute the coordinate-zero row
* `2f33a6b3` build the alpha = 1 Gram into the frame interface and produce an adapted frame
* `9d64637b` settle what depth zero buys for the even climb's residual supply
* `a4d7ad06` pin every named declaration and write the lane note
* (final) state the refutation at the committed supply and scope it

## 5.  For the orchestrator

I edited nothing outside my own module and `docs/dyadic/w73-stratum-note.md`.

1. **`GQ2/Dyadic/Instances/EvenStratumShift.lean` is unwired.**  Nothing imports it and it is not
   in `GQ2.lean`; the same state `NuSeeds.lean` was in before `a515b437`.
2. **`StageAbstractionEvenRawSpan.lean` §0 lines 44-46 and 65 are now backed by a theorem.**  The
   prose is correct and can cite `evenStratum_no_rawStageShift_one`.  Two downstream files hedge
   the same claim as attributed rather than proved and can be sharpened:
   `EvenUnramified.lean:70` ("documented false at `alpha = 1`") and `EvenUnramified.lean:395`
   ("recorded false at `alpha = 1`").
3. **Wave 72 queue item 1 was half stale.**  The Gram existed since wave 70.  Status prose that
   says the `alpha = 1` Gram is uncomputed should be corrected.
4. **Wave 72 §3.1's second bullet is confirmed and can be strengthened**: the climb's committed
   route is blocked because a named step's conclusion is false, not because a binder is unproved.
   Its first bullet (the base) should now say the opposite of what it says: the base's committed
   route is blocked only by the *choice of Gram*, and the repaired Gram admits a frame.

## 6.  Queue items this lane produces

1. **The row-exact frame at `vN 1`.**  §5.2 gives a cup-adapted frame for the `alpha = 1` Gram at
   *some* row table.  Getting one at `vN 1` needs `RowExactLevelFibreLiftSupply (vN 1)` plus the
   two match tables `hpar`/`homega` of `evenFrame_of_adapted`, computed against the `alpha = 1`
   Gram instead of the `alpha >= 2` one.  That is the whole distance from §5.2 to
   `EvenStratumBaseN`, and it is now a concrete, bounded construction rather than an open
   question about forms.
2. **The `alpha = 1` shift supply.**  Rebuild `EvenSharpDbarShiftSupply` around
   `evenStratumShiftWordOne` instead of `evenRawDbarWord`, and re-run the span calculus of
   `StageAbstractionEvenRawSpan.lean` §5 on it.  That file's own §0 says its §1 and §2 are
   `alpha`-free, and §1 of this module supplies the replacement for the one `alpha`-dependent
   row.  **Prediction, not a claim**: the span should come out *smaller*, since the slot-zero
   square is gone, so `evenRawShiftSpan_eq_zLayer` may not clone.  I did not test this.
3. **The `M` twin of ticket 1.**  `evenRawStageShift_m` needs `2 <= alpha` for the opposite
   reason - `M`'s third letter has exponent `2^alpha`, whose half is odd at `alpha = 1`, so the
   `M` word at `alpha = 1` gains an atom where `N` loses one (wave 70's
   `evenAlphaOne_diagCoeff_mSecond` and `evenAlphaOne_mWord_fib` are the Gram-level and fibre
   forms).  The same witness *group* should refute it with the correction moved to coordinate `2`
   instead of `0`; I did not run it.
4. **`EvenRowDeepFibreLiftSupply 0`.**  I read the residual supply at depth zero but not the
   *other* depth-`s` input of `evenClimb_defectReachable`.  `evenClimb_deepRowSupply_n` carries
   `2 <= alpha`, and whether the `s = 0` case is free is untested.

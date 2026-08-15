# W74-ENGINE: the uniform-in-class tower

**Lane W74-ENGINE, branch `claude/w74-engine`, base `4fff1592`.**  One new module,
`GQ2/Dyadic/SqCore/GradedUniformTower.lean` (prefix `gTower`), 94 declarations, every one
pinned to `[propext, Classical.choice, Quot.sound]`.  No edits to existing files.  Source:
Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), SS2 and SS4; the
campaign core is his `q = 2`, `n` odd case.

Commits: `7315032c` (T1 + T2), `cba40b5c` (level-free knobs), `6691f822` (reach subgroups +
engine step), `949c4699` (layer steps + tower induction), `ed6027d6` (conditional assembly).

## What landed, per ticket

### T1 - the row-kernel grading (his SS4 Lemma 1), COMPLETE and sharper than the paper

The campaign's admissibility is TWO logged rows (`lambda = nuLam`, `nu'`), not his one
character, and both targets are torsion-free, so his +-1-letter correction at low level never
arises.  The statement is uniform in `k >= 1` with complement of dimension exactly two:

* `gTower_row_dvd`: every `Z_2`-valued row of a `gamma_k`-element is `2^{k-1}`-divisible (the
  containment converse of the committed `bridge_row_image`).
* `gTower_decomp` (exact, not graded): every `g in gamma_k` factors as
  `g = d * x_0^{lambda(g)} * w^{nu'(g)}` with `d in gamma_k` exactly row-trivial, `w = sqPivot h`.
* `gTower_tower_row_trivial_iff`, `gTower_tower_mem_succ_dvd`: the two towers inject into
  every layer and are killed by no admissible combination; codimension exactly two, every level.
* `gTower_nu_x1`: `nu'(x_1) = 0` is FORCED at every selected marking (apply `nu'` to the
  relator; `Z_2` is a domain).  Hence `gTowerXOne = x_1 * x_0^{-2}` is exactly row-trivial
  (`gTower_xOne_nuLam`, `gTower_xOne_nu`): the x_1-scarcity is structural.  The x_1-letter sits
  on the ADMISSIBLE side of the grading; the complement letters are `x_0` and the pivot,
  uniformly in the level.

### T2 - the engine `delta o pi = pi o delta` (his one line, p. 125), COMPLETE

Pointwise, level-free, for `t in gamma_k`, `k >= 2`, read in `Q_{k+3}`:

* `gTower_engine_bracket`: `[t^2, g] == [t, g]^2 mod gamma_{k+3}` (all four bracket slots).
* `gTower_engine_bundle`: `(t^2)^2 * [t^2, g] == (t^2 * [t, g])^2 mod gamma_{k+3}` (the
  x_1-slot bundle).  So EVERY slot of the knob inventory commutes with squaring.
* Transport laws `gTower_sq_congr`, `gTower_sq_slack`, `gTower_comm_near_add`,
  `gTower_comm_near_slack` (his Prop 2(1)/(3) analogues).

**Marginal case, settled sharper than the brief expected.**  The Hall-Petrescu correction
`[[t,g],t]` lies in `[gamma_{k+1}, gamma_2] <= gamma_{k+3}` (committed
`cfive_commutator_lambdaTwo`), valid from `k = 2` on: the engine holds from relator class 5
upward with no marginal failure, and nothing deeper than the committed `[., gamma_2]` bound is
consumed anywhere in the module.

### Level-free knob inventory (enabler, ticket A)

`gTower_dress_zero/one/two/handleU/handleV`, `gTower_dress_core`, `gTower_kills`: the wave-71
class-five dress calculus restated in `Q_{k+2}` for corrections in `lambdaImage G k (k+2)`.
At `k = 2` these recover the class-four inventory, at `k = 3` the class-five one
(`cfiveKnob_dress_*`); from `k = 4` on they are new.  The five individual dress lemmas are
`k`-unconditional; only the composition carries `2 <= k`.

### T3 - the uniform generation (his SS4 Lemma 3), MACHINE COMPLETE, base left as one index

Definitions: `GTowerAdm` (his `X cap F_k`), `gTowerFar` (the x_1-free letter span),
`gTowerKnobSet` (brackets of admissible corrections against the far span + the x_1-slot
bundles; the bare x_1-bracket is deliberately NOT a generator - it is the waves-71-73 open
defect), `gTowerTowSet` (2^k-divisible powers of the cleared letters x-tilde_1, u-tilde, v-tilde),
`gTowerReach`, `gTowerTowXW` (the T1 complement towers), `gTowerFullReach`,
`GTowerLayerReach h nu' k` (the layer statement at correction depth `k`).

* `gTower_reach_step` (the crown): the subgroup-level engine step.  For `k >= 2`, an
  admissible `gamma_{k+1}`-element whose class lies in the depth-`k` reach has its square's
  class in the depth-`(k+1)` reach.  Closure induction; generator cases are exactly the three
  T2 identities.
* `gTower_comm_x1_split`: THE ENGINE MANUFACTURES THE x_1-DEFECT one level up:
  `[d, x_1] = (d^2 * [d, x_1]) * (d^2)^{-1}`, bundle knob times engine-step square.  This is
  the split no single class could commit; it costs one level of the tower, not a new idea per
  class.
* `gTower_comm_adm_step` / `gTower_comm_tower_step` / `gTower_sq_step` / `gTower_comm_step`
  (his Lemma 2): under the layer hypothesis one depth down, every square and bracket of a
  `gamma_{k+1}`-element lands in the depth-`(k+1)` full reach.  Tower brackets recurse through
  the engine at the half-exponent power (`gTower_zpow_half`), consuming the layer hypothesis
  at the bracket of the half - no auxiliary near-slot homomorphism needed.
* `gTower_full_layer_step`, `gTower_fullReach_realize`, `gTower_cut`: generation, realization,
  and the row cut back to the admissible reach.  (`gTower_cut` needs no membership hypothesis
  on the element: the realization plus the row arithmetic carries everything.)
* `gTower_layerReach_step`, `gTower_layerReach_of_base`: at a selected marking,
  **`GTowerLayerReach h nu' 2` implies `GTowerLayerReach h nu' k` for every `k >= 2`.**

The base index is depth 2 = the class-four layer `gamma_3/gamma_4`.  Assembling the base from
the committed class-four record (`cfourCmp_zLayer_le_gens`, `cfourKnob_sq_knob_pair`,
`gThreeFour_jacobi`, T1, with x-tilde_1 in the role of Labute's xi_1 and the self-bracket
trick for its tower) is W75 work; it was not reached this wave.

### T4 - the conditional assembly, COMPLETE

* `gTower_frame_row_nuLam` / `gTower_frame_row_nu`: the defect of every admissible frame is
  exactly row-trivial (`-4 * lambda(x_0-slot) + 2 * lambda(x_1-slot) = 0`, and the nu'-side
  uses the forced `nu'(x_1) = 0`).  So the defect NEVER has complement-tower coefficients.
* `gTower_defect_reach_of_base`: conditionally on the depth-2 base, the defect always lies in
  knob span + admissible towers; the only possible obstruction is the admissible-tower
  coefficients.
* `GTowerDefectVanishing h` (the FUNC-lane interface, his Lemma 4 target): the defect class
  lies in the knob span at every level `k >= 2`, every selected marking, every admissible
  frame with relator in `gamma_{k+1}`.
* `GTowerKnobRealizable h` (the extraction interface): a knob-span defect class is killed by
  an admissible depth-`k` correction tuple of the frame.
* `gTower_clear_step`, `gTower_supply_of_vanishing`: one clearing step per level, recursed
  from the committed class-three witness: the two interfaces give
  `SqClassClearingSupply h k` for EVERY `k`.
* `gTower_markTransitivity_of_vanishing`: **the two interfaces imply the full `h >= 1`
  residual `SqLamMarkTransitivity h`** through the committed compactness assembly.

## Dictionary verification (corrections to the briefing)

* **chi_sq values** (verified at `Cores.lean:494-515`): `chi(sigma) = S == 13 (16)`,
  `chi(x_0) = X == 5 (16)`, `chi(x_1) = Y = -X^2 == 7 (16)`.  So `Im chi = {+-1} x U^(2)`
  (`f = 2`) as the briefing guessed, but the letter attribution differs: BOTH `sigma` and
  `x_0` have infinite order at depth exactly `U^(2) \\ U^(3)`, and the +-1-role letter is
  `x_1` (via `Y = -X^2`), not `chi(x_1) = -1` literally.  None of the three letters lies in
  `ker chi`.
* **The admissibility is not `ker chi`**: it is `ker(nuLam) cap ker(nu')`, two logged rows.
  This makes T1 cleaner than the paper (no torsion adjustment, codimension exactly two at
  every level including level 1).
* **The pairing**: the knob table shows the sigma-slot brackets against `x_0` and the
  x_0-slot against `sigma`; in Labute's Theorem 3(2) coordinates the campaign letters are
  `(x_1, sigma, x_0) ~ (x_1, x_2, x_3)` up to the (harmless) transposition of the pair.
* **Prop 5(2) -> 5(3) transposition**: confirmed in the derived form.  The pi-slot letter
  (campaign `x_1`) is the excluded tower: its own tower is engine-reachable through the
  bundle (formalized: `gTower_comm_x1_split` + `gTower_reach_step`).

## Where wave 73's `h >= 2` flag actually lives

It does NOT bite the tower induction: for corrections exactly one layer down, all cross-slot
and cross-handle terms die (`[gamma_k, gamma_k] <= [gamma_k, gamma_2] <= gamma_{k+2}`), which
is why `gTower_dress_core` and the whole T3 machinery are `h`-uniform.  It bites only the
extraction `GTowerKnobRealizable`: converting a knob-SPAN membership into one correction
tuple at the CURRENT frame needs (i) the multi-slot composition across all `2h + 3` slots
(sequentially: cross terms die as above, so this is bookkeeping, not mathematics) and (ii)
the far-slot change of basis from the letters to the accumulated frame values.  For (ii) the
route is clear: the far slot of a knob kills `gamma_2`-images and squares (the layer has
exponent two), so only the MOD-2 classes of the far slots matter; the accumulated dressing
beyond the wave-68 bridge part is `gamma_3`-deep (invisible), and the bridge part
`bridgeDress = u^{nu'(v)} v^{nu'(u)} w^{-2nu'nu'}` is x_1-free with unipotent mod-2 letter
matrix, hence invertible over F_2.  This is a lane-sized job and was not formalized; the
interface isolates it exactly.

## What W75 needs

1. **The base** `GTowerLayerReach h nu' 2` (class-four layer = knobs + towers), from the
   committed class-four record.  With it, `gTower_defect_reach_of_base` is unconditional.
   **[W76-HOUSE, round 12 §4.3(b) and (c), two corrections to one item.**  (b) "Unconditional"
   means only "no longer conditional on the base hypothesis": the theorem still binds `hsigma`,
   `hx0`, `2 <= k`, the two row clauses and the relator clause, six binders in all.  (c) "From
   the committed class-four record" is a construction, not a citation.  The committed record
   `cfourCmp_zLayer_le_gens` quantifies its three families over **all** of `Q_4`, while
   `GTowerLayerReach` asks only about exactly row-trivial elements, so the reduction needs a
   row-restricted form that nothing in the tree states.  That restriction is not an
   inconvenience: it is precisely what keeps this item clear of wave 74's own refutation
   `gDelta_cfourCmp_span_hyp_false`, which kills the wave-73 route because that route quantified
   over all of `Q_4`.  This is the wave's largest open item.]**
2. **`GTowerKnobRealizable h`** by the mod-2 far-slot route above.
3. **`GTowerDefectVanishing h`** from the FUNC lane's delta-functionals (his Lemma 4:
   `Delta o delta = 0`, `Im delta = cap ker Delta`); note the FUNC file
   (`GradedDeltaFunctionals.lean`) was being written by a sibling lane this same wave.
   **[W76-HOUSE, round 12 §4.1(a), and it is the sharpest thing round 12 found.**  This item is
   **not obtainable from the delta-functionals**, and the obstruction is a theorem in the FUNC
   lane's own file.  `GTowerDefectVanishing` concludes membership in the **knob span alone**;
   since `gTower_defect_reach_of_base` already places the defect in
   `gTowerReach` = closure(knobs together with admissible towers), the Prop is exactly "the
   admissible tower coefficients vanish".  The admissible towers are those of
   `gTowerXLetters = {gTowerXOne} ∪ range (sqEichU) ∪ range (sqEichV)`, and `gTowerXOne` is the
   cleared `x_1` letter.  `gDelta_x1_tower_dvd` proves `2^{m+2} | gDelta h c (x_1^{2^m})` for
   every row `c`: **no functional sees the `x_1` tower.**  So the functionals can kill the two
   Eichler-tower coefficients and provably cannot kill the third.  Either
   `GTowerDefectVanishing` is weakened to allow an `x_1`-tower coefficient, with
   `GTowerKnobRealizable` extended to realize it (note that `gTowerKnobSet`'s second clause, the
   `x_1`-slot bundle, is the one knob that produces tower-type elements), or that coefficient is
   killed structurally rather than functionally.
   **W76-HOUSE round 13, and this settles it: wave 75 took the second option and it works.**
   `gJoin_xOne_tower_knob` (`GradedUniformJoin.lean` §6, landed `20cd4121`) proves that
   `x_1tilde^{2^k a}` lies in the knob span at every depth `k >= 1`: the `x_1`-slot bundle at
   `t = x_1tilde^{2^{k-1}a}` supplies `t^2 * [t, x_1]`, the bracket splits through the bracket
   homomorphism as `[t, x_1tilde] * [t, x_0^2]`, the first factor is trivial because `t` is a
   power of `x_1tilde`, and the second is a far-span knob.  So the one tower the functionals
   cannot see is precisely the one the moves manufacture, at no cost, and no weakening of the
   Prop was needed.  §7 of the same module then pins the residue exactly: the reach exceeds the
   knob span by exactly the `2h` handle towers, every one of them functional-visible.  This is
   Labute's division of labour made exact for the sq core.  The item that remains from this
   analysis is the `F_2`-independence bookkeeping `GJoinSeparationAll`, proved at `h = 0`
   only.]**

`gTower_markTransitivity_of_vanishing` then closes the residual.  No statement in the module
depends on the class; the one-class-per-wave ladder is replaced by (1) + (2) + (3).

## Verification of record

`scripts/mirror.sh sweep` at lane start (5848 artifacts); `gen GQ2.Dyadic.SqCore.GradedUniformTower`
green after every commit; zero warnings, zero sorries, no new axioms; `#print axioms` on all 94
declarations prints `[propext, Classical.choice, Quot.sound]`.  No dependents exist (new leaf
module; `GQ2.lean` untouched per protocol **as of this lane's last commit**).

**[W76-HOUSE, round 12 §4.2(a), and the convention that retires this finding.**  "`GQ2.lean`
untouched per protocol" is true of the lane and false of the tree within minutes: the
orchestrator registered this module at `1bf8c40a` (01:02:13), **7 min 5 s** after the lane's
last commit.  The lane-level and orchestrator-level behaviour is right; only the annotation was
missing, for the third wave running.  Convention, adopted here: a lane note's claim about
`GQ2.lean` or about a module being unwired is written **as of** the lane's last commit, since
that is the only tree the lane can speak for.]**

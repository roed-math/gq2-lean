# W79-DEPTH3: the depth-3 base REFUTED at every depth; the absorption transported; the residual re-cut onto the kill ladder

**Lane W79-DEPTH3, branch `claude/w79-depth3`, base `527adf51`.**  One new module,
`GQ2/Dyadic/SqCore/GradedDepthThree.lean` (prefix `gDeep`), 69 declarations, 69
`#print axioms`, every one `[propext, Classical.choice, Quot.sound]`.  No edits to existing
files, no `sorry`, no new axiom, no `native_decide`, no heartbeat or recursion-depth
options.  New leaf module, `GQ2.lean` untouched per protocol.

Commits: `a42b0cc2` (module opened), `74d01ee9` (the ladder refutation), `fbf7a168` (coker +
wide chain), `da0ed68e` (T1 + T2 at depth 3), `fce14874` (the kill-ladder re-cut and the
class-5 supply), `c597b157` (header).

Verification of record: `scripts/mirror.sh sweep` green at lane start, `gen
GQ2.Dyadic.SqCore.GradedDepthThree` green after every commit, `check` green; zero errors,
zero warnings, zero sorries.

## Headline

**`GDecideBaseThree h` is FALSE at every `h`, and so is the layer statement at EVERY depth:
the ticket's target does not exist.  But the absorption transports one level up exactly as
priced, the depth-3 coker is the two SQUARED classes and the functionals kill them on
corrected rows, and the route re-cuts onto the defect-restricted kill ladder, whose rungs
2 and 3 are now theorems.  Net effect on the residual: the class-5 supply joins class 4,
so the per-class residual starts at class 6.**

```
gDeep_not_layerReach       : ∀ k ν', ¬ GTowerLayerReach h ν' (k+2)          (⭐⭐⭐ every depth, every marking)
gDeep_not_baseThree        : ¬ GDecideBaseThree h                            (⭐⭐⭐ the W78 sole input, dead)
gDeep_leftover_decomp      : row-trivial γ₄ g  ⟶  g = p · (B²)^{e₁} · (C²)^{e₂},  mk₅ p ∈ reach₃   (T1₃)
gDeep_zero_reader_reach    : all readings zero ⟶ e₁ = e₂ = 0 ⟶ mk₅ g ∈ reach₃                      (T2₃)
GDeepKillAt h k            : the defect-restricted layer statement (rungs 2, 3 proved)
gDeep_markTransitivity_of_kills : (∀ k ≥ 2, GDeepKillAt h k) → GJoinSeparationAll h →
                                    GTowerKnobRealizable h → SqLamMarkTransitivity h
gDeep_supply_five          : GJoinSeparationAll h → GTowerKnobRealizable h → SqClassClearingSupply h 5
```

## 1. The refutation, exactly

The obstruction is wave 78's own coker class, iterated.  With `B = ⁅⁅x₁,σ⁆,x₁⁆`:

* `B^{2^k}` is exactly row-trivial (rows kill brackets, `map_pow`) and lies in `γ_{k+3}`
  (`gDeep_pow_two_pow_mem`).
* Its corrected-`σ`-row reading is EXACTLY `2^{k+2}·unit` (`gDeep_delta_B_pow_rowS`):
  `χ(B) = 1` collapses the norm sum, so each squaring doubles the reading and no bit is
  ever lost.
* The depth-`(k+2)` reach reads `2^{k+3}`-divisibly at that row
  (`gDeep_reach_le_layerDvd_rowS`, §2 of the module): knobs and bundles by wave 75's bounds
  at the general index (`gJoin_knob_dvd`, `gJoin_bundle_dvd` at `k`), Eichler towers read
  exactly zero (the corrected rows are depth-free), and the `x̃₁`-tower reads
  `2^{k+4}`-divisibly (`gDeep_xOne_pow_dvd`: one extra bit per squaring since `χ(x̃₁)` is
  an odd unit).

So `GTowerLayerReach h ν' k` fails for every `k ≥ 2`, every `h`, at EVERY marking, selected
or not; no finite witness group is involved.  Wave 77's `Q₁₆` silence at depth 3 was real
but immaterial: the functional obstruction climbs the tower with the class.  Consequences:

* `GDecideBaseThree h` is false (`gDeep_not_baseThree`), so wave 78's
  `gAbs_markTransitivity_of_baseThree`, `gAbs_supply_of_baseThree` and
  `gAbs_defectVanishing_of_baseThree` are vacuous (true, but with a false named input).
  They are superseded by this module's `_of_kills` versions; `GradedAbsorption.lean` is
  untouched per protocol.
* A depth-4 (or depth-K) re-seed of the SAME SHAPE is equally dead: the ticket's
  contingency question is answered in the strongest form.  The `gDecide_layerReach_of_baseAt`
  restart is engine-sound but will never be fed: no full-layer base exists at any depth.

## 2. The depth-3 coker inventory (the honest count)

Exactly TWO classes, `B²` and `C²`, i.e. the squares of the depth-2 coker: Labute's
`π^{j-1}ξ_i`-towers of the two excluded letters, at `j = 3`, exactly as the absorb note
predicted ("the classes `ξ⁅x₁,σ⁆²`-style one level up").  The count does NOT grow with the
layer dimension: all six families of the `γ₄/γ₅` generation record
(`cfiveSpan_zLayer_le_gens_dsq`, the level-5 record wave 78 priced as "the bulk"; it was
already in the tree from waves 72-73, so the port cost nothing) are absorbed by the two
classes alone (`gDeep_zLayer_le_wideFull`).  How each family lands:

* The four square families are instances of `gDeep_sq_rowTrivial`: a row-trivial
  `γ₃`-element `c` has wave-78 normal form `c = p·B^{e₁}C^{e₂}` (an exact group equation),
  and at level 5 the square splits as `mk₅(p²)·mk₅(B²)^{e₁}·mk₅(C²)^{e₂}` by
  `gTower_sq_congr` at `k = 3` (cross-terms in `γ₆`); `mk₅(p²)` rides the ENGINE STEP
  `gTower_reach_step` from `p`'s depth-2 reach membership.  This is the transport the
  absorb note called "the same absorption one level up": no new letter analysis, wave 78's
  T1 is consumed as a black box.
* The `x₁`-defect of a row-trivial `γ₃`-element follows by the bundle split
  (`gDeep_defect_rowTrivial`), and the two bracket families reduce over the letters by
  `gTower_commHom_span` at `k = 3`: far slots are depth-3 knobs, the `x₁`-slot is the
  defect (`gDeep_bracket_wide`).  The γ₃-analogues of the `gThreeFour` kit the ticket
  priced were NOT needed: `gTower_sq_congr`/`gTower_reach_step`/`gTower_commHom_span` are
  depth-general already, and the six-family record supplies the rest.
* Eighth powers and bracket fourth powers ride the depth-3 two-tower decomposition
  (`gDeep_pow_four_gammaTwo`: `gTower_decomp` at `k = 3`, tower exponents `8`-divisible
  into `gTowerTowXW h 3`).

The cut is verbatim wave 74's one index deeper (`gDeep_wideFull_realize`,
`gDeep_wide_cut`), giving T1₃ (`gDeep_leftover_decomp`).

## 3. The kill transports, one bit deeper

The corrected rows are depth-free, and the readings shift by exactly one bit:

| class | corrected `σ`-row | corrected `x₀`-row |
| --- | --- | --- |
| `B²`  | `2³·unit` (`gDeep_delta_B_sq_rowS`) | `0` (`gDeep_delta_B_sq_rowX`) |
| `C²`  | `0` (`gDeep_delta_C_sq_rowS`) | `2³·unit` (`gDeep_delta_C_sq_rowX`) |
| reach₃ | `2⁴ ∣` | `2⁴ ∣` |

A defect reads zero at every row, so both `𝔽₂`-exponents die (`gDeep_kill_mid`,
`gDeep_kill_last` at the bumped exponents) and the class reaches: T2₃
(`gDeep_zero_reader_reach`).  The ticket's contingency ("classes the functionals cannot
kill even on corrected rows") did NOT occur, so the word-shape pairing was not needed and
was not invoked.  `gDeep_B_sq_notMem_reach`/`gDeep_C_sq_notMem_reach` record the
refutation cores in wave 78's non-membership form.

## 4. The re-cut, and what the binders actually say

Auditing `gAbs_defectVanishing_of_baseThree` per the ticket: its `k ≥ 3` branch applies the
layer statement ONLY to the relator word, in a context where `gJoin_reading_zero` already
gives all readings zero.  So the route never needed the (false) full layer statement, only
its restriction to all-rows-zero elements.  That restriction is `GDeepKillAt h k`:

* rung 2 = wave 78's T2 (`gDeep_killAt_two`), rung 3 = this module's T2₃
  (`gDeep_killAt_three`);
* the full ladder + separation gives the vanishing interface
  (`gDeep_defectVanishing_of_kills`), hence the supply at every class and
  `SqLamMarkTransitivity h` (`gDeep_markTransitivity_of_kills`) with the extraction;
* the recursion seeded through the two proved rungs gives class 5 outright:
  `gDeep_vanishingThree_of_sep`, `gDeep_clear_step_three`, `gDeep_chiSupply_five`,
  `gDeep_supply_five`.  Answering the ticket's final question: a ladder rung at depth `k`
  feeds exactly the class-`(k+2)` step; rungs need no side witnesses (the class-4 witness
  wave 78 manufactured is subsumed: `gAbs_clear_step_two` consumes rung 2 via
  `gAbs_vanishingTwo_of_sep`, and this module's step consumes rung 3 the same way).  The
  ladder at ALL `k ≥ 2` gives ALL classes; nothing is left needing its own witness.
* `h = 0` carries no separation obligation (`gDeep_separationAll_handleFree`,
  `gDeep_supply_five_handleFree`).

## 5. What is open, stated exactly

1. **`GDeepKillAt h k` for `k ≥ 4`** (the ladder above the proved rungs).  The kill side
   transports verbatim (§2's reach kernel and the row readings are depth-general in this
   module already; only the two kill lemmas carry hardcoded exponents).  The cost of rung
   `k` is T1 at depth `k`, whose sole per-level input is the level-`(k+2)` generation
   record: level 4 has three families (`cfourCmp_zLayer_le_gens`), level 5 six
   (`cfiveSpan_zLayer_le_gens`), level 6 does not exist in the tree.  Everything else in
   the rung-3 proof (`gTower_decomp`, `gTower_sq_congr`, `gTower_reach_step`,
   `gTower_commHom_span`, the cut) is depth-general, and the T1 transport consumes the
   previous rung's T1 through the engine step, so the ladder is a genuine induction with
   one per-level graded input.  W80's fork: build the level-6 record and rung 4 (one more
   class, mechanical but sizable), or prove a UNIFORM generation record (Labute's Lemma 3
   is uniform in the weight; its graded shadow at every level is the real prize and would
   close the whole ladder at once).
2. **`GJoinSeparationAll h`** (wave 75 T3): unchanged, now consumed by both proved rungs;
   only depths 2 and 3 feed the class-5 endpoint.  Vacuous at `h = 0`.
3. **`GTowerKnobRealizable h`** (wave 75 T4): unchanged, the extraction interface.
4. The per-class residual `SqClassClearingSupply h k` for `k ≥ 6` and
   `limFinal_markTransitivity_iff` are untouched.

## What W80 needs

1. **The uniform generation record** (recommended over per-level ports): the graded basis
   statement for `γ_{k+1}/γ_{k+2}` at every `k`, Labute's Lemma 3 shadow.  With it, the
   T1/T2 induction in this module closes `GDeepKillAt h k` for all `k` and the odd route
   reduces to separation + extraction, full stop.
2. **Separation at depths 2 and 3** for `h ≥ 1`: on the critical path for the class-5
   endpoint and every rung; wave 75 §7 scoped it as ordered-product bookkeeping.
3. **The extraction** (`GTowerKnobRealizable`): the wave-73 multi-handle bookkeeping,
   unchanged.

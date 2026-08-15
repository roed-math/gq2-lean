# W80-UNIFORM: the level-free generation record, and the kill ladder closed

**Lane W80-UNIFORM, branch `claude/w80-uniform`, base `4f30776b`.**  One new module,
`GQ2/Dyadic/SqCore/GradedUniformGen.lean` (prefix `gGen`), 1040 lines, 56 declarations, 56
`#print axioms`, every one `[propext, Classical.choice, Quot.sound]`.  No edits to existing
files, no `sorry`, no new axiom, no `native_decide`, no heartbeat or recursion-depth
options.  New leaf module, `GQ2.lean` untouched per protocol.

Commits: `5f0ec1e1` (module opened), `80fc0f9a` (record stated, both committed instances),
`80aea266` (the record at every level), `d4dddfcc` (coker at every level, the four
supplies), `c0d42b4c` (T1 at every depth), `e59a5600` (T2, the ladder, the composite).

Verification of record: `scripts/mirror.sh sweep` green at lane start, `gen
GQ2.Dyadic.SqCore.GradedUniformGen` green after every commit, `check` green; zero errors,
zero warnings, zero sorries.

## Headline

**The uniform generation record holds at every level, so the whole kill ladder
`GDeepKillAt h k` is theorems and the graded side of the odd route is CLOSED.  What now
stands between the tree and `SqLamMarkTransitivity h` is exactly the two wave-75
interfaces: `GJoinSeparationAll h` (vacuous at `h = 0`) and `GTowerKnobRealizable h` (the
extraction).  At `h = 0` the residual is the extraction alone.**

```
GGenRecord h j            : the top layer of Q_{j+3} from three families      (TRUE, j >= 1)
gGen_record               : GGenRecord h j for every j >= 1                   (Labute Lemma 3 shadow)
gGen_t1                   : the leftover normal form at every depth           (T1, coker B^{2^m}, C^{2^m})
gGen_zero_reader_reach    : all readings zero -> reach, at every depth        (T2)
gGen_killAt               : GDeepKillAt h k for EVERY k >= 2                  (the ladder, closed)
gGen_markTransitivity     : GJoinSeparationAll h -> GTowerKnobRealizable h ->
                              SqLamMarkTransitivity h                         (the composite)
gGen_supply               : same inputs -> SqClassClearingSupply h k, ALL k   (per-class residual gone)
gGen_markTransitivity_handleFree : GTowerKnobRealizable 0 -> SqLamMarkTransitivity 0
```

## 1. The record, exactly

`GGenRecord h j`: a subgroup of `Q_{j+3}` containing

* `y^{2^j}` for every `y` in the `gamma_2`-image,
* `(commP w r)^2` for every `w` in the `gamma_j`-image and every `r`,
* `commP (commP w r) q` for the same `w` and every `r, q`,

contains the whole top layer `gamma_{j+2}/gamma_{j+3}`.  The near slots sit at `gamma_j`,
one below the natural `gamma_{j+1}`, because the step halves a power tower once before
reading it; this is exactly the calibration of both committed instances: `j = 1` is
`cfourCmp_zLayer_le_gens` re-indexed (the `2^1`-power family on the `gamma_2`-image covers
the fourth powers) and `j = 2` is `cfiveSpan_zLayer_le_dsq` verbatim.

**The step (`gGen_record_step`, `j >= 2`)** runs through the group itself.  The test
subgroup `gGenTest` holds the `gamma_{j+2}`-elements whose square and whose every bracket
land in the target at level `j+4`; it is a subgroup because squaring and the near bracket
slot are additive on `gamma_{j+2}` modulo `gamma_{j+4}` (`gTower_sq_congr`,
`gTower_comm_near_add`), and it swallows `gamma_{j+3}` outright, so membership only
depends on the class one level down.  The record one level down then covers the whole of
`gamma_{j+2}` by the test subgroup: the three family checks each peel one squaring through
the committed engine `gTower_engine_bracket` (his `delta_i pi = pi delta_{i-1}`), landing
squarely on the new families at the `gamma_{j+1}`-slots.  `gFourFive_zLayer_le_gen`
finishes.

**The standing degree-shift trap, resolved**: the Hall-Petrescu correction
`((t,g),t)` of the engine dies at EVERY step of this induction, because the near slot
climbs with the level: for `t` in `gamma_k` the correction lies in
`[gamma_{k+1}, gamma_2] <= gamma_{k+3}` (wave 70's `cfive_commutator_lambdaTwo` at free
`k`, packaged as `gTower_engine_corr_mem`).  The wave-76 third term is a LOW-slot
artifact: it survives only when the near slot stays at weight 2 while the level grows,
which is why the committed level-4/5 records carry triple-bracket families, and why the
uniform record's slot index must climb.  Formally nothing beyond the committed engine was
needed; no new Hall-Petrescu identity was proved.

## 2. T1 and T2 at every depth

The depth-`(m+2)` coker is `B^{2^m}, C^{2^m}` (`gGenCoker`; `gAbsCoker` is `m = 0`,
`gDeepCoker` is `m = 1`), Labute's `pi^{j-1} xi`-towers of the two excluded letters.
Centrality, normality, the involution law and the two-exponent form hold at every index
with wave 79's one-line proofs.

* **T1 (`gGen_t1`)**: every exactly row-trivial `gamma_{m+3}`-element is a
  depth-`(m+2)` reach element times `(B^{2^m})^{e_1} (C^{2^m})^{e_2}` with
  `F_2`-exponents.  Induction on `m`: wave 78's `gAbs_leftover_decomp` is the base, and
  the step is wave 79's depth-3 transport with the depth freed.  The four supplies
  (square, `x_1`-defect, bracket, `2^{m+2}`-power) consume the depth-`m` normal form
  through `gTower_reach_step`, `gTower_sq_congr`, `gTower_commHom_span` and
  `gTower_decomp`, all committed at free index; the record of Section 1 at index `m+2`
  then puts the whole next top layer inside the widened full reach, and the realize/cut
  pair (verbatim wave 79, one index free) gives the normal form.  `gGen_t1 1` reproves
  wave 79's `gDeep_leftover_decomp` independently.
* **T2 (`gGen_zero_reader_reach`)**: `B^{2^m}` reads `2^{m+2}*unit` at the corrected
  `sigma`-row (committed, `gDeep_delta_B_pow_rowS`) and `0` at the `x_0`-row, `C^{2^m}`
  conversely (`gGen_delta_C_rowX`, the one reading the tree lacked), while the reach reads
  `2^{m+3}`-divisibly (`gDeep_reach_le_layerDvd_*`, committed at free depth).  The kill
  lemmas are wave 79's with the exponents freed; both `F_2`-exponents die and the class
  reaches.

## 3. The ladder and the composite, with the binders read honestly

`gGen_killAt : forall k, 2 <= k -> GDeepKillAt h k` discharges wave 79's sole ladder
input.  Through the committed `gDeep_markTransitivity_of_kills` and
`gDeep_supply_of_kills`:

* `gGen_markTransitivity (hsep : GJoinSeparationAll h) (HR : GTowerKnobRealizable h) :
  SqLamMarkTransitivity h`.
* `gGen_supply` closes `SqClassClearingSupply h k` for EVERY `k` under the same two
  inputs, so the per-class residual (previously open from class 6) is gone, and by
  `limFinal_markTransitivity_iff` nothing else on the graded side remains.

The ticket asked whether the residual "is exactly the extraction".  Read off the actual
binders: at `h = 0` YES, exactly `GTowerKnobRealizable 0`
(`gGen_markTransitivity_handleFree`; the separation obligation is a theorem there,
`gDeep_separationAll_handleFree`).  At `h >= 1` the residual is the extraction PLUS
`GJoinSeparationAll h`, the wave-75 ordered-product bookkeeping (its Section 7 scoping);
both are pointwise interfaces already stated in the tree, and no layer statement, witness
group, or per-level generation input survives anywhere.

## 4. Honesty notes

* The record is stated at `D_sq h` (discrete level quotients), not at a general profinite
  `G`: the induction pushes subgroups forward along `levelMk`, and the image of a subgroup
  under a quotient map has no closedness for free.  The committed instances it consumes
  are the `_dsq` forms; the general-`G` statement was neither needed by the ladder nor
  claimed.
* `GGenRecord` at `j = 1` assumes strictly more than `cfourCmp_zLayer_le_gens` (the power
  family ranges over the whole `gamma_2`-image, not just the squares); the instance is
  derived FROM the committed record, so nothing is weakened.  At `j = 2` the match with
  `cfiveSpan_zLayer_le_dsq` is verbatim.
* Satisfiability at every level: the three families are consumed at
  `S := gGenWideFull h nu' (m+1)` for every `m` in the T1 induction, so the hypotheses
  are exercised, not vacuous; and the record's conclusion is applied to the top layer of
  every `Q_{m+5}`, which is nontrivial at every level (wave 79's refutation classes live
  there).  A per-class failure would have surfaced as an unprovable rung; none did.
* The unrestricted layer statement `GTowerLayerReach` stays FALSE at every depth (wave
  79); this lane closes only its defect-restricted form, which is all the route consumes.

## What W81 needs

1. **`GJoinSeparationAll h`** for `h >= 1`: the last graded-side interface, wave 75
   Section 7's ordered-product bookkeeping, now consumed at every depth `k >= 2` by the
   closed ladder.  Vacuous at `h = 0`.
2. **`GTowerKnobRealizable h`**: the extraction, the wave-73 multi-handle bookkeeping,
   unchanged, now THE residual at `h = 0`.
3. Nothing else: no level-6 record, no rung 4, no per-class witnesses; the ladder fork of
   wave 79 is resolved on the uniform branch.

### CORRECTION [W81-HOUSE, watch round 18, as of `6f2916f3`]

**Items 1 and 2 above are both wrong, and item 1 was wrong when it was written.**  This is
the wave-80 lesson repeating verbatim: a lane listed as open a theorem its own base carried.

**Item 1 is retracted.**  `GJoinSeparationAll h` was already a theorem in this lane's own
base.  `gExt_separationAll (h : Nat) : GJoinSeparationAll h` sits at
`GQ2/Dyadic/SqCore/GradedExtraction.lean:514` in commit `4f30776b`, which is the base this
note names in its own first line; wave 79 proved it unconditionally at every `h`, not just
at `h = 0`.  It was never "the last graded-side interface" and it was never something W81
needed.  Verified by `git show 4f30776b:GQ2/Dyadic/SqCore/GradedExtraction.lean`.

**Item 2 is retracted in its status, not in its content.**  `GTowerKnobRealizable h` is
indeed not proved, but it is not "THE residual" at `h = 0` or anywhere else, because the
route no longer passes through it.  Wave 79 found that the campaign's recursion does not
prove it AS QUANTIFIED (an admissible dressing may carry an `x_1`-component); wave 80's
sibling lane `GQ2/Dyadic/SqCore/GradedXFree.lean` responded by re-running the same
recursion with an `x_1`-freeness clause carried through the supply, on which the weakened
interface `GXfKnobRealizable h` IS a theorem (`gXf_knobRealizable`).  The extraction was
bypassed, not discharged.

**Item 3 stands, and understates the result.**  Nothing else was needed at all.
`SqLamMarkTransitivity h` is now a theorem at every `h` with no hypothesis of any kind:
`gOdd_markTransitivity` in `GQ2/Dyadic/SqCore/GradedOddClose.lean`, whose proof consumes
THIS LANE's `gGen_killAt` through `gXf_markTransitivity_of_residual`.  The headline of this
note (Section "Headline") is correspondingly stale in its second and third sentences; its
first sentence, that the ladder is closed at every rung, is correct and is what closed the
route.

The same two errors appear in this lane's module docstring at
`GQ2/Dyadic/SqCore/GradedUniformGen.lean` Section 7; annotated there in the same pass.

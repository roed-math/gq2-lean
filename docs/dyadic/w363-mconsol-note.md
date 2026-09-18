# W363-MCONSOL lane note

Lane: consolidation of the nine wave-362 M modules under an explicit, scoped
edit grant. Branch `claude/w363-mconsol`, base `69b9851c`, Lean 4.31.0-rc2.

No mathematics is added, removed or weakened by this lane. Every change is a
rename, a relocation of two already-proved statements, or a docstring
correction. No `sorry`, no `native_decide`, no new axiom, no `set_option` of
any kind, nothing over 100 columns, no em-dashes. `GQ2.lean` was not edited.

Scope of the grant, and what was touched inside it:

* the nine modules `GQ2/Dyadic/MarkedCore/{MHeadCleanup,
  MFullFrameCompactness, MFullFrameStages, MFrameMatrixLift, MInitialCupDepth,
  MFrameCupCoordinates, MBasisRowRefinement, MPlaneAmbientStage,
  MFullStabilizerLift}.lean` -- all nine edited;
* their lane notes `docs/dyadic/w362-*-note.md` -- all six edited, to record
  the rename and the move and to fold in two audit flags.

## T1. The public name

Before this lane, `GQ2.Dyadic.MarkedCore.mFullStabilizer_lift` named the
*composition shape* of `MFullFrameStages`, a theorem with five interface
hypotheses, while the landed unconditional theorem was called
`mFullStabilizer_lift_of_frame`. Anyone grepping the namespace hit the
conditional one first. The rename map:

| old | new | where |
| --- | --- | --- |
| `mFullStabilizer_lift` | `mFullStabilizer_lift_of_interfaces` | `MFullFrameStages.lean` |
| (new declaration) | `mFullStabilizer_lift` | `MFullStabilizerLift.lean` |
| `mFullStabilizer_lift_of_frame` | kept, now an alias of `mFullStabilizer_lift` | `MFullStabilizerLift.lean` |

Nothing else changed name. `mFullStabilizer_lift_of_initialLift`,
`MStageInitialLift`, `MStageStep`, `mFullStabilizer_lift_of_fixedHead`,
`mBasis_mFullStabilizer_lift_of_initialLift` and `mFullStabilizer_lift_iff` all
keep their spellings.

`mFullStabilizer_lift` in `MFullStabilizerLift.lean` carries the statement that
`mFullStabilizer_lift_of_frame` used to carry, verbatim, together with the
proof term that used to be under that name. `mFullStabilizer_lift_of_frame` is
retained in the same module as

```lean
theorem mFullStabilizer_lift_of_frame ... := mFullStabilizer_lift ha phi hchi hcup
```

with the identical statement, so the sibling Nielsen lane's new modules, which
import `MFullStabilizerLift` and refer to the earlier spelling, keep
elaborating unchanged. No `@[deprecated]` attribute was attached, so no new
warnings appear in any build. Both names are pinned.

Consumers updated. Only one was a code reference:
`mFullStabilizer_lift_of_initialLift`'s proof body in `MFullFrameStages.lean`.
`MFrameMatrixLift.mFullStabilizer_lift_of_fixedHead` and
`MPlaneAmbientStage.mBasis_mFullStabilizer_lift_of_initialLift` both go through
`mFullStabilizer_lift_of_initialLift`, whose name is unchanged, so only their
prose needed fixing. Docstring references were updated in `MFrameMatrixLift`
(2) and `MFrameCupCoordinates` (3).

The public pair of `MFullStabilizerLift.lean` is now
`mFullStabilizer_lift` / `mFullStabilizer_lift_iff`, the exact twins of
`NFullStabilizerLift`'s `nFullStabilizer_lift` / `nFullStabilizer_lift_iff`,
and the module docstring says so.

## T2. The head module's import cost

`MHeadCleanup.lean` carried two derivative-kernel re-exports,
`mHead_mRelWord_shift_eq_evenRawDbarWord` and
`mHead_mRelWord_shift_eq_nRelWord_shift`, whose only purpose was to package
`StageGeneric.evenRawStageShift_m` for the sibling kernel lane. They were the
sole reason the module imported `GQ2.Dyadic.Instances.StageAbstractionEvenRawSpan`.

Finding: **not literally duplicated in `MBasisRowRefinement.lean`, but strictly
implied by it.**

* `mHead_mRelWord_shift_eq_evenRawDbarWord` is `mBasis_mFiltered_mRelWord`
  followed by `mBasis_nFilteredDerivative_eq_evenRawDbarWord`, rearranged from
  product form into shift form. Same content, different arrangement.
* `mHead_mRelWord_shift_eq_nRelWord_shift` has no counterpart at all in
  `MBasisRowRefinement`; that file proves only the N half of it
  (`mBasis_nFilteredDerivative_eq_evenRawDbarWord`).

So both were **moved**, not deleted. They now sit in `MBasisRowRefinement.lean`
directly under the two adapters, and are now *proved from* those adapters
rather than from `evenRawStageShift_m` a second time (only the N leg still
calls `evenRawStageShift_n` directly). Their names are unchanged, deliberately:
nothing in the repository consumed them, so a rename was free, but keeping the
names costs nothing and cannot surprise an out-of-tree reference. The `mHead`
prefix now records where they were first stated rather than where they live,
and the destination's section docstring says so. If a later wave prefers
`mBasis_` spellings, that is a one-line change with no consumers to update.

`MHeadCleanup.lean` then loses the import outright. Measured transitive
`GQ2`-internal import closures, by parsing `^import GQ2...` over `GQ2/`
(so `Mathlib` and other package modules are leaves and are not counted):

| module | before | after |
| --- | ---: | ---: |
| `MHeadCleanup` | 459 | **10** |
| `MFullFrameStages` | 467 | **19** |
| `MFrameMatrixLift` | 469 | **21** |
| `MPlaneAmbientStage` | 713 | 713 |
| `MFullStabilizerLift` | 726 | 726 |

The ticket quoted "73 to 558"; those are not the numbers this lane measures,
and the figures above are what the import graph in the tree at this base
actually gives. The direction and the shape of the finding are the ticket's:
the head module was paying for a heavy import it did not use, and two modules
downstream of it were paying too. Nothing downstream broke: `MFullFrameStages`,
`MFrameMatrixLift`, `MPlaneAmbientStage` and `MFullStabilizerLift` all
re-elaborate with the lighter chain, which confirms that the heavy import was
reachable only through the moved section.

The three modules that still import `StageAbstractionEvenRawSpan` in the wave
are `MBasisRowRefinement` (directly, and it always did) and the two that import
it through `MBasisRowRefinement`.

## T3. Docstring accuracy after the wave

The nine module docstrings were written before the final theorem existed.
Corrections, by module:

* **`MHeadCleanup`** -- removed the paragraph describing the deleted
  coordination section; added where the two head results are actually consumed
  (`mHead_ordinary_row` by `MFullFrameStages`,
  `mHead_exists_freeTwo_characterZero_same_class` by `mStageStep_holds`), and
  a record of the T2 move.
* **`MFullFrameCompactness`** -- "Nonemptiness ... is assumed, not proved" now
  says it is a hypothesis of this file *and* names the downstream producers
  (`exists_mStageBasis_exact_stage` over `MStageStep`, and `mStageStep_holds`).
* **`MFullFrameStages`** -- title no longer says "conditional full-stabilizer
  shape"; the `MStageStep` entry says the interface is hypothetical *in this
  file* but proved downstream; the `alpha = 1` warning no longer says
  `MStageStep` "has no producer at all" (it has one, carrying `2 <= alpha`);
  the composition's own docstring lists, hypothesis by hypothesis, which
  sibling theorem discharges it, and points at the assembled statement.
* **`MFrameMatrixLift`** -- the MSTAGES interface section and
  `mFullStabilizer_lift_of_fixedHead`'s docstring now name the theorem that
  discharges the carried error, and state the scope honestly: the fixed-`T`
  lift and everything about it carry `2 <= alpha`, the orientation and
  projection material at the top of the file does not.
* **`MInitialCupDepth`** -- "no subsequent filtered correction, no frame
  automorphism lift, and no converse is asserted in this file" now says which
  file each of those three is.
* **`MFrameCupCoordinates`** -- added where both halves are consumed
  (`mCupStageError_of_frame` as the depth-three input of the lift,
  `mCupFrameCupIsometry_of_aut` as the cup half of the converse); two
  docstrings renamed their reference to the composition shape.
* **`MBasisRowRefinement`** -- the head-row nonclaim now names `MHeadCleanup`;
  added that this file is the row-refinement half of `mStageStep_holds`; new
  section docstring for the two moved re-exports.
* **`MPlaneAmbientStage`** -- "so the full-stabilizer lift of that module is
  conditional only on its initial-lift interface" was stale: that interface is
  discharged too. It now says the interface is *proved* here, names the two
  modules that discharge the remaining one, points at the assembled theorem,
  and records the Nielsen-list nonclaim. Same correction on
  `mBasis_mFullStabilizer_lift_of_initialLift`'s own docstring.
* **`MFullStabilizerLift`** -- the Contents list names
  `mFullStabilizer_lift` / `mFullStabilizer_lift_iff` as the public pair and
  the alias as an alias; both public statements now carry the `alpha >= 2` and
  arbitrary-`h` scope explicitly and disclaim both the finite Nielsen list and
  the rank-four packet; the N-reuse paragraph was rewritten (see FLAG-1 below).

What was deliberately **not** claimed anywhere: that the stabilizer has a
finite explicit Nielsen-generator presentation, that the rank-four packet is
certified, or that anything holds at `alpha <= 1`.

## Folding in W363-MAUDIT

The independent audit (`docs/dyadic/w363-m-full-stabilizer-independent-audit.md`
on `dyadic`) returned PROVED AS STATED with two comment-only flags in this
lane's T3 scope. Both are folded in.

**FLAG-1 (medium).** `MFullStabilizerLift.lean` and
`docs/dyadic/w362-massemble-note.md` both asserted "Nothing from the N theorem
is reused; only its shape is matched." False as written, and contradicted by
the other eight modules' own docstrings. Replaced, in both places, by a
paragraph that separates the M-specific mathematics (the coupled two-letter
row, the primitive relation vector `e_A + 2^(alpha-1) e_C` and the fixed head
`T = A * C^(2^(alpha-1))`, the square-head depth-three step, the M crossed
models, the parity-only `B` slot) from the shared infrastructure that really is
reused (`N.lean`'s `nFrameModel_map_t`, applicable because `MFrameModel h` and
`NFrameModel h` are the same Lean type; `NInitialCupDepth`'s commutator tail
`freeTail_eq_of_cup` / `freeTail_value` / `reducedRows`; `nPlaneCorrectionKernel`
with its closedness and `nBasisKernelWitness_mem` / `_row`;
`NPlaneAmbientStage.oneWord`; `NFrameCupCoordinates`). The standing and correct
disclaimer is kept: no N *relator conclusion* is used at the M word, and the M
defect is shifted by `evenRawStageShift_m`, never by the N identity.

**FLAG-2 (low).** The route attribution. The wording the flag describes is in
the lane notes, not in the `.lean` docstrings (greps for "step 5", "item 5",
"5 of 5" and "scaffold" over `MFullFrameStages.lean` and
`MFullStabilizerLift.lean` return nothing, before or after this lane). Fixed at
the source: `docs/dyadic/w362-massemble-note.md` no longer calls itself "step 5
of 5" and no longer cites "Route item 5", and says why. `w362-mstages-note.md`
is left alone: the audit is explicit that the scaffold's item 5 *is* the
stages/compactness step, which is that lane's.

FLAG-3 (the missing `MCupFrameCupIsometry` to `mCupIsometry` bridge) is an
interface observation about a consumer path, not a docstring defect, and is out
of this lane's grant. It is untouched and still open.

Two audit facts to keep true, and checked after the renames:

* `MFrameModel h = NFrameModel h` by `rfl`. Untouched: this lane changed no
  definition.
* Pin count. The audit measured 216, of which 215 print the standard three and
  `mStageOneLe` prints `[propext]` alone. This lane's arithmetic on that:
  `-2` from `MHeadCleanup`, `+2` to `MBasisRowRefinement` (the move), `+1` in
  `MFullStabilizerLift` (the new plain-named theorem), giving **217 pins, 216
  std-3, `mStageOneLe` still on `[propext]` alone**. Measured, not inferred.

## Verification of record

The mirror harness only. `lake` was never invoked, in any form, and
`scripts/check_dyadic.sh` was never run. The shared cache was never written to.

Final pass, in dependency order, from a clean sweep:

```text
scripts/mirror.sh sweep                  swept 10535 artifacts
gen GQ2.Dyadic.MarkedCore.MHeadCleanup             OK  pins   5 (std-3   5)
gen GQ2.Dyadic.MarkedCore.MFullFrameCompactness    OK  pins  25 (std-3  24)
gen GQ2.Dyadic.MarkedCore.MFullFrameStages         OK  pins  12 (std-3  12)
gen GQ2.Dyadic.MarkedCore.MInitialCupDepth         OK  pins   9 (std-3   9)
gen GQ2.Dyadic.MarkedCore.MFrameCupCoordinates     OK  pins  16 (std-3  16)
gen GQ2.Dyadic.MarkedCore.MBasisRowRefinement      OK  pins  11 (std-3  11)
gen GQ2.Dyadic.MarkedCore.MFrameMatrixLift         OK  pins 111 (std-3 111)
gen GQ2.Dyadic.MarkedCore.MPlaneAmbientStage       OK  pins  18 (std-3  18)
gen GQ2.Dyadic.MarkedCore.MFullStabilizerLift      OK  pins  10 (std-3  10)
                                       TOTAL pins 217, std-3 216, remainder 1
check GQ2.lean                                     OK: GQ2.lean
```

The single remainder is `mStageOneLe`, on `[propext]` alone, which is strictly
smaller than std-3 and is pre-existing.

Every module that imports a changed module was re-elaborated. Within the wave
those are exactly the nine above, which are regenerated in dependency order;
outside it, an exhaustive grep for `^import GQ2.Dyadic.MarkedCore.<one of the
nine>` over the tree returns only `GQ2.lean`, lines 1445-1453, which is the
`check` at the end. `MFullFrameCompactness` and `MInitialCupDepth` are in the
gen list because T3 touched them, not because they import anything changed.

Two mechanical audits were run over the nine at the end:

* pin-block completeness: every top-level `theorem` / `def` / `private theorem`
  in each of the nine has a `#print axioms` line, and no `#print axioms` line
  names a declaration that is not there. Nine files, 217 declarations, 217
  pins, zero missing, zero stale.
* hygiene: no em-dash, no `sorry`, no `native_decide`, no `set_option`, no bare
  `axiom`, and no line over 100 columns added anywhere by this lane.

One incidental catch worth recording for future docstring passes: a wrapped
prose line inside a docstring that happens to *begin* with the word `theorem`
or `def` is indistinguishable from a declaration to a line-based audit, and two
of this lane's own first-draft docstrings did exactly that. Both were rewrapped.

## Left for a later lane

* `MFullFrameStages.lean` has no copyright header, unlike its eight siblings.
  Noticed, not fixed: adding one is not a rename, a move or a docstring
  correction, and is outside the three tickets.
* The `mHead_` prefix on the two moved declarations (see T2). Free to change,
  zero consumers.
* Audit FLAG-3, the `MCupFrameCupIsometry` to `M.lean` `mCupIsometry` bridge.
  Out of grant; still open.

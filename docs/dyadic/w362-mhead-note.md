# W362-MHEAD lane note

Lane: `claude/w362-mhead`, base `6770a87e`. One new module,
`GQ2/Dyadic/MarkedCore/MHeadCleanup.lean`, namespace `GQ2.Dyadic.MarkedCore`,
declaration prefix `mHead`. No existing module and no `GQ2.lean` is touched.

Ticket: step 1 of 5 of the M full-stabilizer lifting task described in
`docs/dyadic/w361-m-next-general-scaffold.md`, section "Recommended first
bounded Claude task".

Verification of record: `bash scripts/w361_lean_runner.sh
GQ2/Dyadic/MarkedCore/MHeadCleanup.lean`, default limits, warning free.
All seven declarations pin `[propext, Classical.choice, Quot.sound]`.
No `sorry`, `admit`, `native_decide`, new axiom or resource option.

## Status

T1, T2 and T3 all landed.

## Relayed claims checked against the source

* `mRelWord_comm` / `mWord` (`Cores.lean`): the M word really is
  `A^2 [A,B] C^(2^alpha) [C,D]` times the handles, with `m 0 = A` and
  `m 2 = C`. Confirmed.
* `mPhiHom_A` (`MFrameExists.lean`) is literally
  `ofAdd (1, 0, -(2:Z_2)^(alpha-1), 0, 0)` and `mPhiHom_C` is
  `ofAdd (0, 0, 1, 0, 0)`. Confirmed, so the brief's `m = 2^(alpha-1)` is the
  source's exponent. Neither is used below; T1 to T3 are word-level, not
  frame-level.
* `evenRawStageShift_m` exists and is already proved (it is not a statement this
  lane had to supply); it carries three instance hypotheses the brief did not
  mention. See T3.

## Why M is not a text substitution for N here

`mRelWord_comm` (`Cores.lean`) gives
`mRelWord alpha m = m 0 ^ 2 * m 2 ^ (2 ^ alpha)`, so the ordinary row is
`2 f(A) + 2^alpha f(C)`: **coupled**. The `N` row is `(2 + 2^alpha) f(A)`,
which is two times a unit, so `NPlaneOrdinaryHead` can cancel it outright with
`nHeadExponent_two_unit`. There is no such unit on the M side, and the cleanup
must not manufacture one by setting the `C` row to zero.

## T1: the coupled ordinary-head cleanup

* `mHead_ordinary_row` -- the literal coupled row of `mRelWord`, every handle
  included, any topological group, any rank, any `alpha`.
* `mHead_correction_ordinary_row` -- the target-relative defect's row is the
  corrections' own coupled row, given only `f (mRelWord alpha y) = f target`.
  No relator equation is assumed on either `y` or the target.
* `mHead_dvd_of_coupled_row` -- the scalar step in `ZMod`-free `Z_2`: from
  `2^(d-1) | C` and `2^(d+1) | 2A + 2^alpha C` with `alpha >= 2` and `1 <= d`,
  conclude `2^d | A`. Explicit witness `b - 2^a c`; no unit is inverted.
* `mHead_correction_dvd` -- **T1**. For `alpha >= 2`, `1 <= d`, arbitrary
  marking `y`, corrections `t`, arbitrary `target` and any continuous `Z_2`
  character `f`: exact ordinary agreement `f (mRelWord alpha y) = f target`,
  `t 2 in twoCentralSeries G d` and the corrected defect in
  `twoCentralSeries G (d + 2)` give `2^d | toAdd (f (t 0))`.

The `C` row is **not** set to zero, no orientation premise is used, and `G` is
only a topological group (no compactness, pro-two or finite generation).
The ticket's `d >= 2` is the special case of `1 <= d`; `d = 0` is excluded only
because the conclusion would be vacuous, not because the argument needs it.

Note the filtration convention: `twoCentralSeries G 0 = twoCentralSeries G 1 =
top`, so `lambda_d` here is `twoCentralSeries G d` and a character sends
`lambda_(k+1)` into `2^k Z_2` (`twoCentralSeries_z2_character_dvd_succ`).

## T2: the same-class all-character-zero head representative

`mHead_exists_freeTwo_characterZero_same_class`: at arbitrary free rank `n`,
arbitrary handle count `h` and arbitrary target, the coupled defect supplies
every coordinate divisibility that
`exists_freeTwo_characterZero_same_twoCentralClass` needs, so the `A` column has
a representative `t0` in the same `lambda_d` class, with
`(t 0)^{-1} * t0` in `lambda_(d+1)` and `f t0 = 1` for every continuous `Z_2`
character.

Packaging: the conclusion is the exact triple that
`exists_freeTwo_nHead_characterZero_same_class` delivers on the `N` side and
that `NBasisRelativeRefinement`, `NPlaneRelativeRefinement` and
`NPlaneFullRelativeRefinement` consume via
`obtain <t0, ht0, hslack0, hzero0>` followed by `Function.update t 0 t0`. The M
consumer will call it the same way, except that it must pass **two** depth
facts, `ht 0` and `ht 2`, because the row is coupled.

## T3: the M derivative-kernel coordination statements

`evenRawStageShift_m` was **already proved** in
`GQ2/Dyadic/Instances/StageAbstractionEvenRawSpan.lean` (namespace
`GQ2.Dyadic.StageGeneric`). This lane adds no mathematics there; it re-exports
it in the shape the sibling MKERNEL lane asked for:

* `mHead_mRelWord_shift_eq_evenRawDbarWord` -- the literal shift
  `(mRelWord alpha base)^{-1} * mRelWord alpha (fun i => base i * correction i)`
  equals `evenRawDbarWord base correction`, for `alpha >= 2`, `k >= 3`,
  corrections of depth `k-1`. No `StageWord` datum to build, no separate
  `1 <= alpha` argument.
* `mHead_mRelWord_shift_eq_nRelWord_shift` -- the M and N shifts of the **same**
  base and correction are literally equal in `levelQuot G (k+1)`. This is the
  identification the scaffold's item 1 requires before any N kernel witness may
  be reused on the M side.

**Instance burden inherited from `evenRawStageShift_m`:** both T3 statements
need `[CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]` on `G`, unlike
T1 and T2. MKERNEL must supply those.

**Import cost, measured:** T3 is the only reason this module imports
`GQ2.Dyadic.Instances.StageAbstractionEvenRawSpan`. That single import takes the
module's transitive `GQ2` source closure from **73** modules to **558**. T1 and
T2 are foundational and every later M stage lemma will import them, so if the
orchestrator prefers the head cleanup to stay light, T3's two statements are the
natural thing to move into MKERNEL's own module; nothing in T1 or T2 uses
them.

## What this lane is NOT

It does not claim any M full-stabilizer lift, does not construct an M initial
free basis or a primitive relation-vector lift, does not assert the M analogue
of any N-relator conclusion (in particular not of
`exists_nBasis_allRows_same_kernelCoset`), and does not build the MKERNEL
adapter. `alpha >= 2` throughout; nothing here extrapolates to `alpha = 1`.

## What remains for step 1's consumers

1. The M analogue of `exists_nBasis_allRows_same_kernelCoset`: an M correction
   kernel and its arbitrary-basis diagonal row witnesses. T3 part 2 is the
   licence to try reusing the N witnesses, not a proof that they transfer.
2. The M relative-refinement wrapper (the analogue of
   `exists_nBasis_full_relative_correction`), which needs both an M
   `nRelWord_correction_defect_mem_iff` analogue and an M orientation clause.
   Checked against the source while writing this note: `mChiModel_ofAdd`
   (`M.lean`) gives `mChiModel alpha (ofAdd (eps,b,c,d)) = mSign b * u ^ d`, and
   `mChi_row_extract` (`alpha >= 2`) turns preservation into `mParityZ b = eps`
   and `d = w`. So the M orientation clause constrains B only through its
   **parity**, plus the integral D coordinate; it does not fix the integral B
   row the way the N clause does. The scaffold's further description of the
   orientation tuple on `(A,B,C,D)` was not checked by this lane.
3. The initial primitive relation-vector lift in the free basis
   `(T = A*C^m, B, C, D, handles)` with `m = 2^(alpha-1)`; a separately named
   task, deliberately not assumed anywhere above.

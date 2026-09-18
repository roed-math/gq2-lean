# W362-MHEAD lane note

Lane: `claude/w362-mhead`, base `6770a87e`. One new module,
`GQ2/Dyadic/MarkedCore/MHeadCleanup.lean`, namespace `GQ2.Dyadic.MarkedCore`,
declaration prefix `mHead`. No existing module and no `GQ2.lean` is touched.

Ticket: step 1 of 5 of the M full-stabilizer lifting task described in
`docs/dyadic/w361-m-next-general-scaffold.md`, section "Recommended first
bounded Claude task".

## Status

T1 landed. T2 in progress.

## T1: the coupled ordinary-head cleanup

The `M` relator's abelian collapse is `mRelWord_comm`,
`mRelWord alpha m = m 0 ^ 2 * m 2 ^ (2 ^ alpha)` (`Cores.lean`), so the ordinary
row is `2 f(A) + 2^alpha f(C)`: **coupled**, unlike the `N` row
`(2 + 2^alpha) f(A)`, which is a unit times two and cancels on its own.

Landed declarations, all pinned `[propext, Classical.choice, Quot.sound]`:

* `mHead_ordinary_row` -- the literal coupled row of `mRelWord`, all handles
  included, any topological group, any rank.
* `mHead_correction_ordinary_row` -- the target-relative defect's row is the
  corrections' own coupled row, given only `f (mRelWord alpha y) = f target`.
* `mHead_dvd_of_coupled_row` -- the scalar step, in `ZMod`-free `Z_2`: from
  `2^(d-1) | C` and `2^(d+1) | 2A + 2^alpha C` with `alpha >= 2`, `1 <= d`,
  conclude `2^d | A`. Witness `b - 2^a c`, no unit inversion.
* `mHead_correction_dvd` -- **T1**. For `alpha >= 2`, `1 <= d`, arbitrary
  marking `y`, corrections `t`, arbitrary `target` and continuous `Z_2`
  character `f`: exact ordinary agreement `f (mRelWord alpha y) = f target`,
  `t 2 in twoCentralSeries G d` and the corrected defect in
  `twoCentralSeries G (d + 2)` give `2^d | toAdd (f (t 0))`.

The `C` row is **not** set to zero and no orientation premise is used. `d >= 2`
of the ticket is the special case `1 <= d`; `d = 0` is excluded only because the
conclusion is then vacuous, not because the proof needs it.

## What this lane is NOT

It does not claim any M full-stabilizer lift, does not construct an M initial
free basis, and does not assert the M analogue of any N-relator conclusion.
`alpha >= 2` throughout; nothing here extrapolates to `alpha = 1`.

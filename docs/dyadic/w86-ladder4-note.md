# W86-LADDER4 lane note

Lane target: the row-move ladder at k >= 4. Extend `gRowSet h A B k` nonemptiness beyond the
wave-85 record (k <= 3 proved), aiming at `gLad_clearing (h) : SqNuOrientedClearAtUnitPivot h`
composed into the odd-degree classification, or the sharpest per-rung record with the first
obstruction in closed form. Module: `GQ2/Dyadic/SqCore/GradedRowLadder.lean` (prefix `gLad`).
No sorry, no new axiom, no native_decide.

## Status

IN PROGRESS. Skeleton banked; reading the wave-85 rung calculus and the M6 increment engine
(`mpcBld_incr_*`) next, then the class-4 defect of the class-3 solution in closed form.

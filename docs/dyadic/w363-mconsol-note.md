# W363-MCONSOL: consolidation of the wave-362 M modules

Lane branch `claude/w363-mconsol`, base `69b9851c`, Lean 4.31.0-rc2.

This lane holds an explicit, scoped edit grant over the nine wave-362 M modules
`GQ2/Dyadic/MarkedCore/{MHeadCleanup, MFullFrameCompactness, MFullFrameStages,
MFrameMatrixLift, MInitialCupDepth, MFrameCupCoordinates, MBasisRowRefinement,
MPlaneAmbientStage, MFullStabilizerLift}.lean` and their lane notes. Nothing
else is touched; in particular `GQ2.lean` is not edited.

Three tickets:

- T1 free the public name `mFullStabilizer_lift` for the unconditional theorem.
- T2 move (or drop) the head module's T3 re-exports so `MHeadCleanup.lean` can
  shed its heavy `StageAbstractionEvenRawSpan` import.
- T3 bring the nine module docstrings up to the landed state.

Status: in progress.

## Verification of record

The mirror harness, never `lake`: `scripts/mirror.sh sweep` once, then
`scripts/mirror.sh gen <Dotted.Module>` for every edited module in dependency
order, then `scripts/mirror.sh check <path>` for every importer of a changed
module.

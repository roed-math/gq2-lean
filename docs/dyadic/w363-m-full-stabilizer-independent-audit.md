# W363: independent audit of the full M stabilizer lift

Date: 2026-09-17. Audit lane: `w363-maudit`. No proof, umbrella, or script
changes are made by this lane; comment-only findings are FLAGGED here for the
orchestrator.

**VERDICT: (pending)**

## Verdict and exact scope

(pending)

## Critical proof checks

(pending)

## Verification performed

Every one of the nine wave-362 modules was read and separately re-elaborated by
this audit lane with `bash scripts/w361_lean_runner.sh <source>` (the pinned
`leanprover/lean4:v4.31.0-rc2` compiler against the shared dependency cache; no
`lake`, no cache mutation). All nine exited zero with no warnings, and every
printed pin is inside the standard three.

| Module, under `GQ2/Dyadic/MarkedCore/` | Public axiom pins | Source SHA-256 |
| --- | ---: | --- |
| `MHeadCleanup.lean` | 7 | `b632b27cbfbaa3e070a24b72a332a6eab00efdfbefc3239bf348831b0fa7f209` |
| `MFullFrameCompactness.lean` | 25 | `bfb1cebd28b74549a71a252e0dabf95bad5d20d82b5819f10e8f47f2d6bb9d05` |
| `MFullFrameStages.lean` | 12 | `0f5e55200f2ff423c96bc8e8e4601e09b268988f6378398f18a05000ca078238` |
| `MFrameMatrixLift.lean` | 111 | `7f918a6679b77fc1be00e64ebf3a1ceeda3fb8ca65ba423ec379359699c925a3` |
| `MInitialCupDepth.lean` | 9 | `d7c2eb53138d7c2a48fc93f714175429820df2169dbad0f01938ff2b33dcaae8` |
| `MFrameCupCoordinates.lean` | 16 | `0880b52342e6a658c492121323cccb18f508ce63d7400a8f97539b571aaed525` |
| `MBasisRowRefinement.lean` | 9 | `fa0b97b9950fedf4595fa5d92aacb4f9599d98949e1855b54e236103f044aceb` |
| `MPlaneAmbientStage.lean` | 18 | `5de574be85b686242a48287176fca24e9fef5ab5dc743302a6f6fc128ffff686` |
| `MFullStabilizerLift.lean` | 9 | `bac55a1a4268bdc1bac2e647a9c2c6b3c70d1dba8c3483421ea57e9ee36da783` |

216 pins in total. 215 print exactly

```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

and the remaining one is strictly smaller:
`'GQ2.Dyadic.MarkedCore.mStageOneLe' depends on axioms: [propext]`. The nine
pins of the endpoint module print, verbatim from the runner:

```text
'GQ2.Dyadic.MarkedCore.mFullStabilizer_liftEquiv_head' depends on axioms: [propext, Classical.choice, Quot.sound]
'GQ2.Dyadic.MarkedCore.mFullStabilizer_relError_of_cup' depends on axioms: [propext, Classical.choice, Quot.sound]
'GQ2.Dyadic.MarkedCore.mFullStabilizer_lift_of_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'GQ2.Dyadic.MarkedCore.mCupFrameOfDM_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'GQ2.Dyadic.MarkedCore.mFrameOrientation_cupFrameOfDM' depends on axioms: [propext, Classical.choice, Quot.sound]
'GQ2.Dyadic.MarkedCore.mFullStabilizer_orientation_of_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
'GQ2.Dyadic.MarkedCore.mFullStabilizer_cup_of_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
'GQ2.Dyadic.MarkedCore.mFullStabilizer_orientation_cup_of_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
'GQ2.Dyadic.MarkedCore.mFullStabilizer_lift_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Hygiene

`grep -nE "sorry|native_decide|set_option|^axiom |admit|#exit"` over all nine
sources returns exactly one line, and it is prose inside a docstring:

```text
GQ2/Dyadic/MarkedCore/MPlaneAmbientStage.lean:202:target-relative M defect lies in `lambda_k` admits a depth-`(k-1)` correction
```

No `sorry`, no `native_decide`, no `set_option` of any kind (so no raised
`maxHeartbeats`, no disabled linter), no bare `axiom`. All nine modules are
registered in `GQ2.lean` at lines 1445-1453, in dependency order:

```text
1445:import GQ2.Dyadic.MarkedCore.MHeadCleanup
1446:import GQ2.Dyadic.MarkedCore.MFullFrameCompactness
1447:import GQ2.Dyadic.MarkedCore.MFullFrameStages
1448:import GQ2.Dyadic.MarkedCore.MFrameMatrixLift
1449:import GQ2.Dyadic.MarkedCore.MInitialCupDepth
1450:import GQ2.Dyadic.MarkedCore.MFrameCupCoordinates
1451:import GQ2.Dyadic.MarkedCore.MBasisRowRefinement
1452:import GQ2.Dyadic.MarkedCore.MPlaneAmbientStage
1453:import GQ2.Dyadic.MarkedCore.MFullStabilizerLift
```

These are incremental source compilations against the shared dependency cache,
not a new source-only transitive clean build. They do not extend any historical
frozen whole-tree report; that remains a parent-owned step.

## Flagged items

(pending)

## Explicit nonclaims

(pending)

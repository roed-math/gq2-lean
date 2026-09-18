# W362-MSTAGES lane note

Lane: M full-stabilizer lifting, step 5 of 5 (exact all-depth stages, full-frame
stage transfer, compactness at M). Branch `claude/w362-mstages`, base `6770a87e`.

Verification of record: `bash scripts/w361_lean_runner.sh <file>` for the first
module, and `scripts/mirror.sh sweep` + `gen GQ2.Dyadic.MarkedCore.MFullFrameCompactness`
+ `check GQ2/Dyadic/MarkedCore/MFullFrameStages.lean` for the second. Default
limits throughout, `autoImplicit=false`, no warnings, no `sorry`, no new axioms.
Every declaration in both files carries `#print axioms`: 25 + 13 = 38 pins, all
exactly `[propext, Classical.choice, Quot.sound]`.

## New modules

### `GQ2/Dyadic/MarkedCore/MFullFrameCompactness.lean` (T1)

Free cover and orientation: `mStageProjection`, `mStageProjection_gen`,
`mStageProjection_surjective`, `mStageOrientation` (`chiM` pulled back along the
cover), `mStageOrientation_gen` (literal Labute values `(1, -1, 1, mUnit alpha)`
on the core and `1` on every handle letter).

Frattini and limit machinery in `D_M`: `MStageModTwoIndep`, `mStage_finsetGen`,
`mStage_iInf_twoCentralSeries`, `mStageLift_surjective`,
`mStageModTwoIndep_of_equiv`.

Full-frame compactness: `MStageFullFrameRealizes`, `mStageFullFrameStageSet`,
`mStageFullFrameStageSet_antitone`, `isClosed_mStageFullFrameStageSet`,
`mStageFullFrameStageSet_iInter_nonempty`,
`exists_mStageFullFrameRealizes_of_stages`, and the equivalence
`exists_mStageFullFrameRealizes_iff_stages`.

Full-frame stage transfer: `mStageProjection_ab_eq_of_coordinates`,
`mPhiHom_mStageProjection_eq_of_coordinates`, `mStageModTwoIndep_of_freeBasis`,
`mStageFullFrameStageSet_of_free_exact_stage`.

Torsion retention, checked in file rather than asserted:
`mStageFullFrameStageSet_abMk_eq` and `mStageFullFrameRealizes_abMk_eq` derive
equality of the literal `abMk` columns from the marking condition, using
`mPhiHom_injective`. The stage condition is therefore an equation in the actual
abelianization of `D_M`, not on a selected unramified marking; the first slot of
`MFrameModel h` is the class of `t = Abar + m Cbar`, `m = 2^(alpha-1)`
(`mPhiHom_t`).

Scope: this module needs only `1 <= alpha` (that is all `mPhiHom` needs). The
bridge `mStageOneLe : 2 <= alpha -> 1 <= alpha` is kept explicit so no statement
silently weakens.

### `GQ2/Dyadic/MarkedCore/MFullFrameStages.lean` (T2, T3)

The M row is **not** a text substitution of the N row. `mStageRelWord_ordinary_row`
records the literal two-letter row `2 f(y_0) + 2^alpha f(y_2)`. The primitive
relation word is therefore `mStageTorsionWord alpha y = y_0 * y_2^(2^(alpha-1))`,
and `mPhiHom_mStageTorsionWord` checks, via `mPhiHom_t`, that on the standard
marking this is exactly the frame's torsion generator, not `Abar`.
`mStageRelWord_row_of_torsionWord` converts fixation of that word into the exact
ordinary relator row; it uses `alpha >= 1` only through `2 * 2^(alpha-1) = 2^alpha`.

`MStageStep alpha h` is the named depth interface (MKERNEL's target); read with
`d = n + 2` it says: from a free basis with matching orientation and matching
ordinary relator row whose literal error lies in `lambda_(d+1)`, there is a
correction of depth `d` invisible to the orientation and to every ordinary
character (so the whole coordinate matrix survives) whose new error lies in
`lambda_(d+2)`. It is the exact M analogue of the composite of
`NAmbientStageSupply` with `exists_nBasis_full_relative_correction`.

`exists_mStageBasis_exact_stage` iterates that interface to every depth from one
initial depth-three basis, retaining every exact coordinate column. It carries no
`2 <= alpha` binder on purpose: the iteration is bookkeeping, and every
alpha-dependent fact lives in `MStageStep` and in the initial data. That is not a
claim of anything at `alpha = 1`, where `MStageStep` has no producer.

`mFullStabilizer_lift` is the composition shape, and is **conditional**. Its
hypotheses are exactly the three sibling interfaces: `(e0, hT, hchi0, hframe0)`
from MINIT, `herror0` from MCUP, `hstep : MStageStep alpha h` from MKERNEL. The
bundled variant `MStageInitialLift` + `mFullStabilizer_lift_of_initialLift`
reduces this to two hypotheses. No lift is proved here.

## What remains for the siblings

1. MKERNEL: produce `MStageStep alpha h` for `alpha >= 2`.
2. MINIT: produce the initial `e0` fixing `mStageTorsionWord alpha` (in the
   free basis `(T = A*C^m, B, C, D, handles)`), preserving `mStageOrientation`,
   and inducing `phi` on the full frame through `mStageProjection`.
3. MCUP: the depth-three error of that same `e0`.

With all three in hand the final theorem is one `exact mFullStabilizer_lift ...`.

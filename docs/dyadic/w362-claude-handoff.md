# W362-W364 handoff to the next session

**Drafted as a skeleton by the W362-HOUSE lane at the open of wave 362, against
base `6770a87e`; the mechanical sections filled by the W364-HOUSE lane at the
close of wave 364, against base `d2056503`.** Sections 2, 4, 6 and 7 are
complete. Section 3 was filled from the thirteen lane notes of waves 362 to 364.
Sections 1, 2, 5 and 8 were filled by the orchestrator at the session close (`3dab414f` and after); section 4's end-state verification record is the last thing written, after the final gate and fresh build. No placeholder remains.

Every number in the sections this lane filled was re-derived against the tree at
`d2056503`, not carried from a note. Where a note's own figure and the tree's
disagree, the disagreement is stated rather than silently resolved.

Structure follows `w361-claude-code-handoff.md` deliberately, so a reader who
has read that one can skip to the section they want.

Do not interpret this document as owner approval or a release. As of the base
commit, no owner decision listed in `w361-claude-code-handoff.md` section 6
item 4 has been taken.

---

## 1. Outcome and immediate orientation

**This session (waves 362 to 365, 2026-09-17, one eight-hour window) closed the
M full-stabilizer lifting and both section-14 finite Nielsen-family artifacts.**
`GQ2.Dyadic.MarkedCore.mFullStabilizer_lift` and `mFullStabilizer_lift_iff`
(`GQ2/Dyadic/MarkedCore/MFullStabilizerLift.lean`) are the exact twins of the N
theorems: for every `alpha >= 2` and every handle count, a continuous automorphism
of the actual M abelianization (torsion included) lifts to a continuous
`chiM`-preserving automorphism of `DM alpha h` with the full-frame square on every
element if and only if it preserves the transported original orientation and the
semantic full mod-two cup form; the torsion relation clause is discharged, not
assumed. Nine modules, 217 pins, all std-3, built in one wave by following
`w361-m-next-general-scaffold.md`'s five steps; independently audited PROVED AS
STATED (`w363-m-full-stabilizer-independent-audit.md`). Then
`mNielsenGen_finite_list` / `mNielsenGen_stabilizer_induced`
(`MNielsenGenerators.lean`) and `nNielsen_factorization` /
`nNielsenFac_finite_list` / `nNielsenFac_stabilizer_induced`
(`NNielsenFactorization.lean`, with `NNielsenGenerators.lean`) supply the packet's
finite-family lists at rank four for both cores, the composite lifts composed from
the members' lifts, and the Smith-Witt stabilizer quantifier closed literally;
independently audited WITH CAVEATS, all disclosed (`w364-nielsen-independent-audit.md`).

**Decisions taken by the owner on 2026-09-18, after this document was drafted:** Option A
(the compactness proof method accepted for both cores; W366 applies the amendment wording to
the packet and ledger), and the push (`488e7cf2..b9ad374f`, GitHub level with local). The
paragraph below predates them where it says otherwise.

**What it did NOT close.** The frozen M-word placement claim (a different
statement, false by the W341-W344 no-go results, untouched). Owner acceptance of
the uniform filtered-correction and compactness proof method, now for both cores
(`w364-proof-packet-amendment-mc.md` is the proposal; Option B, generator-level
lifts, has a work list read off the Lean and costs at least one axiom unless M3 is
rebuilt). The four Codex adoption items. The push. The publication packets remain
staged proposals (all ten ledger items for L, N0 and Npc now have exporters,
`w363-pub2-note.md`, with a five-kind binding taxonomy whose weakest kind is
statement identity, not proof identity).

**Counts changed.** Registered modules 1,552 to 1,564 (thirteen new `.lean` files
under `GQ2/`, twelve registered, the thirteenth an exporter driver that stays
outside `GQ2.lean` by convention; the W365 Gauss module, if it landed, is recorded
in section 4). Pins added: 397 for the MC work (217 + 70 + 16 + 94), every one std-3
except `mStageOneLe` on `[propext]` alone. Axiom census unchanged at eleven; the
general endpoint's footprint unchanged. Ledger at the wave-362 tree: 51,212 tracked
declarations, zero gaps; the end-state figure is in section 4.

Carried forward unchanged from W361, and true at base `6770a87e`:

- The full N stabilizer-lifting theorem is proved, not scaffolded, for every
  `alpha >= 2` and every handle count `h`. Public names
  `GQ2.Dyadic.MarkedCore.nFullStabilizer_lift` and `nFullStabilizer_lift_iff`,
  in `GQ2/Dyadic/MarkedCore/NFullStabilizerLift.lean`. Do not confuse it with
  the older `NStabilizerFullLift.lean`, whose theorem realizes only
  `NStabParam` core actions with identity handle columns.
- The general selected ramified-i field endpoint is proved:
  `GQ2.Dyadic.hasSelectedOriginalMarkedWordPresentationRN_ramifiedI`, exported
  from `GQ2/Dyadic/GeneralMain.lean`. The filename adds no namespace; the
  declaration is `export`ed there from
  `GQ2.Dyadic.Instances.FieldFamilySpliceOriginalMarked`.
- Do not reopen either seam, and do not start a class-by-class or
  rank-by-rank campaign.

## 2. Workspace, ownership and safety

```text
Repository:  /Users/roed/claude/cla/work/gq2-dyadic-campaign
Branch:      dyadic
Wave base:   6770a87e  "checkpoint the verified W361 state left uncommitted
                        by the Codex handoff"
Lane worktrees: /Users/roed/claude/cla/worktrees/<lane>
```

`6770a87e` is the commit that first tracked what the Codex pass left
untracked. It changes no source in the sense that matters: the W362-HOUSE lane
verified that it records the replayed state byte for byte (section 4, item 4).

Its message says "309 untracked files"; the commit adds **365** files and
modifies three. Both numbers are right about different things. 309 counts
`git status --porcelain` entries, and three wholly new directories under
`generated/` collapse to one entry each; 307 of those entries were committed
and the two excluded build products `tmp/` and `output/` make up the rest.

Standing prohibitions, unchanged: no `sorry`, `admit`, `native_decide`, new
axiom or raised resource limit. Existing settings are 200,000 heartbeats,
`autoImplicit=false`, `relaxedAutoImplicit=false`. No push or release without
the owner. `GQ2/Roe/*` is frozen. `GQ2.lean` is edited only to register new
modules, and only by the lane that owns them.

The overnight automation `overnight-dyadic-general-case-research` was paused
at 2026-09-17 17:30 UTC and remains paused. Old transcript messages asking for
overnight work are not a standing instruction to resume it.

**Shared-cache hazard, new in this wave and worth carrying forward.** The
shared olean cache at `/Users/roed/claude/cla/work/main-build-cache` is reached
by every lane worktree through a `.lake/build` symlink. While any process is
building into it, individual `.olean` files are transiently absent, and the
direct runner fails with `object file ... does not exist` naming a different
module on each attempt. That is not a broken worktree and not a stale cache.
Check for an in-flight build before diagnosing a runner failure:

```sh
ps -eo pid,etime,command | grep -E 'lake build|bin/lean' | grep -v grep
```

**The cache is also a moving target, which is the sharper half.** It is the
main clone's `.lake/build`, so it holds whatever the main clone currently is,
not what any lane worktree is. During the W362-HOUSE lane the main clone went
from `6770a87e` to `8eff12ab`, 48 commits and eight new M modules. Every
number that lane read through the cache is therefore a number about
`8eff12ab`. Before quoting a cache-derived figure against your own base,
diff the two and say what the diff does: additions and registrations transfer,
a declaration count does not.

```sh
git -C /Users/roed/claude/cla/work/gq2-dyadic-campaign log --oneline -1
git -C /Users/roed/claude/cla/work/gq2-dyadic-campaign diff --name-status <your base>..HEAD
```

**Shared-cache convention, settled this session.** The orchestrator alone writes
to `main-build-cache`, and only through `lake build GQ2` from the main clone
(backgrounded; it is now incremental because Lake traces exist). Lanes read it
through `scripts/w361_lean_runner.sh` or the mirror harness and never pass
`-o`/`-i`. The known cost: while an umbrella runs, a lane's runner can fail with a
different missing olean each time; the fix is to retry after the build, and the
orchestrator tells lanes when a build is in flight. A merged lane's modules enter
the cache only after the orchestrator wires them into `GQ2.lean` and rebuilds;
until then a sibling imports them by `git merge` of the lane branch plus mirror
`gen` in dependency order.

## 3. Proof architecture and reusable scaffolding

Carried forward unchanged: the eleven-module N architecture and its resolved
pitfalls are in `w361-claude-code-handoff.md` section 4. The W362-HOUSE lane
verified that table against the tree; see section 4 below.

The session added **twelve registered modules**, all under
`GQ2/Dyadic/MarkedCore/`, carrying **397 pins**, plus **one unregistered
exporter driver** under `scripts/`. Thirteen new `.lean` files in all: count the
driver and you get thirteen, count registered modules and you get twelve. The
pin counts below are this lane's own `#print axioms` census over the sources at
`d2056503`, and they agree with the lane notes everywhere except where a later
lane moved a declaration, which is said in the row.

Every one of the twelve is imported directly by `GQ2.lean`. No pre-existing
`.lean` file in the tree was modified by any lane of the session; the only
modified Lean file in `6770a87e..d2056503` is `GQ2.lean` itself, which gained
twelve import lines and nothing else.

### W362-MHEAD: the coupled ordinary-head cleanup

| Module | Reusable content | Public pins |
| --- | --- | ---: |
| `MHeadCleanup.lean` | see below | 5 |

- **`MHeadCleanup.lean`** `mHead_ordinary_row`, the literal coupled row `2 f(A) + 2^alpha f(C)`
  of `mRelWord`, every handle included, any topological group, any rank, any `alpha`.
  `mHead_dvd_of_coupled_row`, the scalar step in `Z_2` with an explicit witness `b - 2^a c` and
  no unit inverted. `mHead_correction_dvd` (T1), `2^d | toAdd (f (t 0))` for `alpha >= 2`, `1 <= d`,
  arbitrary marking, corrections and target.
  `mHead_exists_freeTwo_characterZero_same_class` (T2), the same-class all-character-zero head
  representative at arbitrary free rank and handle count.

Note the count. The note says seven, and seven is what the module carried at
its own close; W363-MCONSOL moved two declarations out of it (see MKERNEL
below), leaving five.

### W362-MSTAGES: full-frame compactness, stage transfer, the all-depth induction

| Module | Reusable content | Public pins |
| --- | --- | ---: |
| `MFullFrameCompactness.lean` | see below | 25 |
| `MFullFrameStages.lean` | see below | 12 |

- **`MFullFrameCompactness.lean`** The free cover `mStageProjection` and `mStageOrientation`
  (`chiM` pulled back, literal Labute values `(1, -1, 1, mUnit alpha)` on the core and `1` on
  every handle letter). The `D_M` Frattini and limit machinery. `MStageFullFrameRealizes` with
  closed antitone stage sets, nonempty intersection, and the equivalence
  `exists_mStageFullFrameRealizes_iff_stages`. Full-frame stage transfer. **Torsion retention
  checked, not asserted**: `mStageFullFrameStageSet_abMk_eq` and
  `mStageFullFrameRealizes_abMk_eq` derive equality of the literal `abMk` columns through
  `mPhiHom_injective`, so the stage condition is an equation in the actual abelianization of
  `D_M`. Needs only `1 <= alpha`; `mStageOneLe` is the explicit bridge from `2 <= alpha`.

- **`MFullFrameStages.lean`** `mStageTorsionWord alpha y = y 0 * y 2 ^ (2^(alpha-1))`, with
  `mPhiHom_mStageTorsionWord` checking it really is the frame's torsion generator on the
  standard marking, and `mStageRelWord_row_of_torsionWord` converting its fixation into the
  exact ordinary relator row. `MStageStep alpha h`, the named depth interface.
  `exists_mStageBasis_exact_stage`, the iteration to every depth from one initial depth-three
  basis, retaining every exact coordinate column. `mFullStabilizer_lift_of_interfaces`, the
  five-hypothesis composition shape, and the bundled `MStageInitialLift` /
  `mFullStabilizer_lift_of_initialLift`.


`mFullStabilizer_lift_of_interfaces` is the W363-MCONSOL spelling; the note was
written when it was called `mFullStabilizer_lift`, and every bare occurrence of
that name in a `w362-*-note.md` means this declaration, not the endpoint.

### W362-MINIT: the initial free lift with the primitive relation preserved

| Module | Reusable content | Public pins |
| --- | --- | ---: |
| `MFrameMatrixLift.lean` | see below | 111 |

- **`MFrameMatrixLift.lean`** `mFrameBasisChange` and the `(T, B, C, D, handles)` coordinate
  dictionary `mFrameHeadCoordinate_eq`; in T-coordinates the frame projection has the N shape.
  `exists_mFrame_freeBasis_lift` / `mFrameLiftEquiv` (T2): from orientation preservation alone,
  a free automorphism with literal fixed head `T = A * C^(2^(alpha-1))`, the exact relation
  vector `r = e_A + 2^(alpha-1) e_C`, the exact frame square on **every** element, orientation
  preserved on every element, and exact columns. `mFrameOrientation_preserved_iff`:
  preservation is `mParityZ` of the integral `B` slot plus the integral `D` slot, **not** the
  integral `B` row as on N. **The precise negative**: `mFrameNaiveLiftMatrix_relVec`
  (`N r = (1 + 2^(alpha-1) digit) r`), `mFrameNaiveLiftMatrix_relVec_iff`, and the explicit
  orientation-preserving involution `mFrameTorsionShear` for which independent sections do
  **not** fix `r`. The cup-side interface for MCUP (T3). The four MSTAGES shapes
  `mFrameLiftEquiv_torsionWord`, `_stageOrientation`, `_stageFrame`,
  `mStageInitialLift_of_fixedHead_error`, and `mFullStabilizer_lift_of_fixedHead`.


### W362-MCUP: the semantic full-frame cup predicate and the depth-three error

| Module | Reusable content | Public pins |
| --- | --- | ---: |
| `MInitialCupDepth.lean` | see below | 9 |
| `MFrameCupCoordinates.lean` | see below | 16 |

- **`MInitialCupDepth.lean`** The two M-specific facts, both needing `alpha >= 2`:
  `mCupPow_eq_one` (the actual `C^(2^alpha)` block dies in the class-two quotient) and
  `mCupSq_eq_of_zLayer` / `mCupSq_levelMk_eq_of_mem_two` (the surviving head is a **square**,
  so agreement modulo lambda-two suffices). `mCupPowHalf_mem_two` and
  `mCupHead_mem_two_of_fixed_T` **discharge** the MINIT hypothesis rather than assuming it.
  Deliverables at the actual `mRelWord`: `mCupRelWord_levelMk_eq_head_mul_tail`,
  `_level_three_eq`, `_error_mem_three`, `_error_mem_three_of_fixed_T`.

- **`MFrameCupCoordinates.lean`** `MCupFrameCupIsometry`, the semantic character-pair predicate
  over **every** continuous mod-two character of the actual full M frame, torsion coordinate
  included, assuming no group lift and no matrix. `mCupFrameCoordinate_head_relation`: all `4 + 2h`
  mod-two coordinates of the M frame genuinely are characters.
  `MCupFrameCupIsometry.reducedRows_of_projection` (T1). `mCupStageError_of_frame`, the MSTAGES
  seam, verbatim `herror0` and **without** the orientation hypothesis, so it is the stronger
  statement. `mCupFrameCupIsometry_of_aut` (T3), the converse ingredient, through `dmObs` and
  uniqueness of the one-dimensional degree-two obstruction.


### W362-MKERNEL: the M derivative-kernel interpolation at an arbitrary basis

| Module | Reusable content | Public pins |
| --- | --- | ---: |
| `MBasisRowRefinement.lean` | see below | 11 |
| `MPlaneAmbientStage.lean` | see below | 18 |

- **`MBasisRowRefinement.lean`** `mBasis_mFiltered_mRelWord` (T1),
  `mRelWord alpha (m*t) = mRelWord alpha m * nFilteredDerivative m t` in `Q_(k+1)`,
  from `evenRawStageShift_m`. Hence
  `mBasis_mem_nPlaneCorrectionKernel_iff_mError` characterizes the M defect by the **N**
  plane-correction kernel, with `_defect_mul_correctionKernel_iff` at an arbitrary target and
  top-layer slack invariance. `exists_mBasis_allRows_same_kernelCoset` (T2 interpolation). Plus
  the two `mHead_mRelWord_shift_eq_*` re-exports W363-MCONSOL moved in from `MHeadCleanup`,
  names unchanged, now proved from the adapters.

- **`MPlaneAmbientStage.lean`** `mBasis_exists_ambient_stage` and `mBasisAmbientStageSupply`,
  the M twin of `NAmbientStageSupply`. `exists_mBasis_full_relative_correction`, the
  relative-refinement half. **`mStageStep_holds : MStageStep alpha h`** (T3), for every `alpha >= 2`
  and every `h`, which discharges the interface the other four steps were stated against.
  `mBasis_mFullStabilizer_lift_of_initialLift`.


The note's per-module figures are 9 and 18; the 9 is now 11 because of the
W363-MCONSOL move, and the 18 is unchanged.

### W362-MASSEMBLE: the theorem and its converse

| Module | Reusable content | Public pins |
| --- | --- | ---: |
| `MFullStabilizerLift.lean` | see below | 10 |

- **`MFullStabilizerLift.lean`** **`mFullStabilizer_lift`** (sufficiency, unconditional) and
  **`mFullStabilizer_lift_iff`** (the image characterization), the exact twins of
  `nFullStabilizer_lift` / `_iff`. `mFullStabilizer_lift_of_frame`, the pre-W363 spelling, kept
  as an alias with the identical statement and no `@[deprecated]`.
  `mFullStabilizer_relError_of_cup`, the depth-three error from cup preservation **alone**,
  with no orientation input. The necessity halves `mFullStabilizer_orientation_of_lift` and
  `mFullStabilizer_cup_of_lift`, packaged as `mFullStabilizer_orientation_cup_of_lift`. The two
  new bridges `mFrameOrientation_cupFrameOfDM` and `mCupFrameOfDM_surjective`, and the
  torsion-word bridge `mFullStabilizer_liftEquiv_head`.


The note's deliverables table has nine rows because it was written before the
W363 rename added the plain-named theorem beside its alias; the module carries
ten declarations and ten pins.

### W363-NIELSEN: the packet's finite Nielsen-family list at M, and the N bridge

| Module | Reusable content | Public pins |
| --- | --- | ---: |
| `MNielsenGenerators.lean` | see below | 70 |
| `NNielsenGenerators.lean` | see below | 16 |

- **`MNielsenGenerators.lean`** `mNielsenGen_finite_list`, the explicit **seven**-member list
  of continuous automorphisms of `MFrameModel 0`, every member orientation-preserving, an
  `MCupFrameCupIsometry`, and lifting; the composite is the parameter's frame action and the
  composite lifts. `mNielsenGen_param_realized` and `mNielsenGen_stabilizer_induced`, the
  latter over every `IsMStabilizer` element, but at the canonical rank-four frame and for an
  orientation character with four pinned generator values, exactly as
  `mStabilizer_classification` is stated; its docstring's bare "every element" omits those
  binders, and section 5 flags that. The reusable half
  is the **cup producer**: `mNielsenGen_coord_zero` .. `_three`, `mNielsenGen_character_apply`
  and `mNielsenGen_cup_core` reduce the semantic predicate to a finite `F_2` matrix check,
  which is what the repo previously had no way to do except from an actual core automorphism.
  `mNielsenGen_nRed_eq_parity` bridges `N.lean`'s `nRed` and `M.lean`'s `mParityZ`.

- **`NNielsenGenerators.lean`** The same bridge at N, in N's own column convention:
  `nNielsenGen_coord_*`, `nNielsenGen_character_apply`, `nNielsenGenMat`,
  `nNielsenGen_cup_of_mat` (`A G A^T = G` gives `NFrameCupIsometry`), and
  `nNielsenGen_lift_of_mat` / `_of_rows`, the latter in `NRows.IsCupIsometry` vocabulary so a
  holder of `nStabilizer_classification`'s clause feeds it directly.


### W364-NFACTOR: the N factorization into six families, and the MC-N list

| Module | Reusable content | Public pins |
| --- | --- | ---: |
| `NNielsenFactorization.lean` | see below | 94 |

- **`NNielsenFactorization.lean`** `NStabParam.act`, the N twin of `MStabParam.act`, with
  `act_t` / `act_x1` / `act_sigma` / `act_x2` checking the four basis rows are `NRows.col` at
  `NStabParam.rows` on the nose. The six families `nFamN1` .. `nFamN6` as `NStabParam` values,
  with closed-form actions and admissibility. **`nNielsenFac_gl2_factor`**, the *bounded*
  `GL_2(Z_2)` factorization `g = F(w) diag(det g, 1) E(x) F(y) E(z)` with `w in {0,1}`
  (`N.lean`'s `nGL_factor` only gives submonoid membership, hence no slot count), reusable for
  the handle planes since it is `h`-free. **`nNielsen_factorization`**, the eight-slot
  factorization of any admissible parameter. `nNielsenFacEquiv`, the action on the actual
  frame; `nNielsenFac_orientation`; `nNielsenFac_mat` and `nNielsenFac_cupIsometry`.
  **`nNielsenFac_finite_list`**, the MC-N twin, length 8. `nNielsenFac_stabilizer_list` and
  `nNielsenFac_stabilizer_induced`, the quantifier closure over `IsNStab`.
  `nNielsenFacLifts_of_param_families`, the independent per-family route through
  `nStabParam_fullFrame_lift_general`.


### W362-PUB and W363-PUB2: the publication side

`scripts/w362_ln_fox_export.lean` is an exporter driver with a global `main`, so
it stays outside `GQ2.lean` like the five W361 export executables. It serializes
ledger items 4 and 5 for the seven existing L/N0/Npc `FoxCertificate` sectors and
carries **21 `rfl` signature theorems** proving that what it serialized is
definitionally the corresponding field of the actual record, plus 26 axiom pins,
all standard three or smaller. Because it has no olean, those 21 theorems are
checked only by the Fox replay, which recompiles the driver. W363-PUB2 added six
more such drivers on the same pattern, `scripts/w363_ln_*_export.lean` for
`specialization`, `input`, `stokes`, `hessian`, `coordinate` and `cover`.

### The key chain: the M full-stabilizer lift

```text
                       phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)
                         |                                   |
        orientation preserved                    MCupFrameCupIsometry ha phi
                         |                                   |
                         v                                   v
   MFrameMatrixLift                                 MFrameCupCoordinates
   mFrameLiftEquiv ha h phi                         mCupStageError_of_frame
   (fixed head T = A C^(2^(alpha-1)),               (uses NO orientation input)
    exact relation vector, exact                            |
    frame square on every element)                          |
        |          |            |                           |
      hT        hchi0        hframe0                      herror0
        |          |            |                           |
        +----------+------------+---------------------------+
                                |
                                v            MPlaneAmbientStage
              MFullFrameStages  |            mStageStep_holds ha : MStageStep alpha h
              mFullStabilizer_lift_of_interfaces  <----------+   (MHeadCleanup
                                |                                 mHead_exists_freeTwo_...
                                |                                 + MBasisRowRefinement
                                |                                 kernel interpolation)
                                v
              MFullFrameCompactness
              exists_mStageBasis_exact_stage  (all depths)
              exists_mStageFullFrameRealizes_of_stages  (compactness)
                                |
                                v
              MFullStabilizerLift
              mFullStabilizer_lift        (sufficiency)
              mFullStabilizer_lift_iff    (+ converse, through
                                           mCupFrameCupIsometry_of_aut and
                                           mFrameOrientation_cupFrameOfDM)
```

The forward proof is literally one composition:

```text
mFullStabilizer_lift_of_fixedHead ha phi hchi
  (mFullStabilizer_relError_of_cup ha phi hcup) (mStageStep_holds ha)
```

### The key chain: the two finite lists

Both lists are rank four (`h = 0`), because both rest on a rank-four
classification. The lifting halves underneath them are general in `h`.

```text
M side (W363-NIELSEN)                     N side (W364-NFACTOR)
---------------------                     ---------------------
M.lean                                    N.lean
  mStabilizer_classification                nStabilizer_classification (on NRows)
  mNielsen_factorization  (existed)         nNielsen_factorization  (DID NOT EXIST;
        |                                     W364 built it, 8 slots, from the
        |                                     bounded nNielsenFac_gl2_factor)
        v                                           v
MNielsenGenerators                        NNielsenFactorization
  mNielsenGenMap / M1..M7                   nNielsenFacMap / N1..N6
  cup producer: coord_* ->                  cup via W363's nNielsenGen_cup_of_mat
    character_apply -> cup_core               (NNielsenGenerators, the bridge
    (finite F_2 decide)                        W363 built for exactly this)
        |                                           |
        v                                           v
  mNielsenGen_finite_list (7)               nNielsenFac_finite_list (8)
  every member lifts by                     every member lifts by
    mFullStabilizer_lift                      nFullStabilizer_lift
        |                                           |
        v                                           v
  mNielsenGen_stabilizer_induced            nNielsenFac_stabilizer_induced
  (every IsMStabilizer element)             (every IsNStab element)
                                                    |
                                                    + second, independent route:
                                                      nNielsenFacLifts_of_param_families
                                                      through nStabParam_fullFrame_lift_general
```

### Pitfalls the notes recorded, and that later waves will hit again

These are the part later waves actually reuse. Each is a thing a lane got wrong
first, or nearly did.

1. **M is not a text substitution of N.** The M relator row is the *coupled*
   two-letter `2 f(A) + 2^alpha f(C)`; the N row is `(2 + 2^alpha) f(A)`, twice a
   unit, which `NPlaneOrdinaryHead` cancels outright. There is no such unit at M,
   and the cleanup must **not** manufacture one by setting the `C` row to zero.
   Every M consumer of the N head packaging must pass **two** depth facts,
   `ht 0` and `ht 2`.
2. **The lift fixes a composite word, not a letter.** `T = A * C^(2^(alpha-1))`,
   not `A`. `A^{-1} * e(A) = C^m * (e C)^{-m}` is only in lambda-two, so the M
   depth-three step turns on the surviving head being a **square**, where the N
   argument fixes a generator literally.
3. **Independent sections do not work at M.** Transcribing the N lift matrix
   column by column gives `N r = (1 + 2^(alpha-1) digit) r`, a unit multiple: the
   submodule `Z_2 r` survives but the vector does not. The explicit
   orientation-preserving involution `mFrameTorsionShear` realizes `digit = 1`, so
   this is a counterexample, not a gap. `mFrameLiftEquiv` exists precisely to
   avoid it.
4. **The M orientation is weaker than the N one.** It pins `mParityZ` of the
   integral `B` slot and the integral `D` slot, not the integral `B` row. A proof
   that assumes the N orientation clause at M is assuming something false.
5. **Variance.** `NInitialCupDepth.reducedRows` has columns = images and proves
   `Abar G Abar^T = G`; `M.lean` stores frame images in **rows** and writes the
   same condition as `Mbar^T G Mbar = G`. `MarkedCore/Variance.lean` is the
   dictionary. W363-NIELSEN sidestepped it by computing the column-convention
   matrix straight from the semantics, and the matrix that came out is the
   transpose of `mFrameMatrix_of_realizes`'s, exactly as the dictionary predicts.
6. **The two orientation formulations are not definitionally equal**, but the
   three frame projections **are**. `mFrameOrientation` lives on the frame and
   `mStageOrientation` on the free pro-two group; the bridge is
   `mStageOrientation_eq_freeOrientation` composed with
   `mFrameOrientation_projection`. By contrast `mFrameProjection`,
   `mCupFreeFrameProjection` and `mPhiHom o abMk o mStageProjection` are all
   `rfl`. Do not assume the pattern goes the same way twice.
7. **A public name can already be taken by a weaker theorem.**
   `mFullStabilizer_lift` named the five-hypothesis *conditional* composition
   shape for a whole wave, so a grep for the obvious name found the wrong theorem
   first. W363-MCONSOL freed it. A lane that may not edit existing modules cannot
   fix this itself; say so in the note and let a consolidation lane do it.
8. **A heavy import can hide in a re-export.** `MHeadCleanup` imported
   `StageAbstractionEvenRawSpan` for two packaging declarations it did not itself
   use, taking its `GQ2`-internal closure to 459 modules; moving them cut it to
   **10**, `MFullFrameStages` from 467 to 19 and `MFrameMatrixLift` from 469 to 21.
   Measure the closure before believing a prose figure: the wave-362 brief quoted
   "73 to 558" and those are not this graph's numbers.
9. **A line-based pin audit cannot tell a docstring from a declaration.** A
   wrapped prose line that happens to *begin* with the word `theorem` or `def`
   reads as a declaration. Two of W363-MCONSOL's own first-draft docstrings did
   exactly that. Rewrap, or audit after elaboration.
10. **`#print axioms` output wraps.** A long axiom list continues onto the next
    line in a build log, so a footprint of four axioms reads as one unless
    continuation lines are rejoined first.
11. **Citing a declaration by its file name does not give its Lean name.**
    `Instances/NpcCore.lean` declares in namespace `Instances.NProcyclicCore`, and
    `npcWUnit` lives in `Words.Npc` although its file is `SelectedEta.lean`. Both
    cost W362-PUB a probe iteration.
12. **Seven declarations in the field-selection layer are not standard three.**
    `FieldFamilyCampaignBoundary.hasSelectedRowResidualRN_l`, `_n0` and `_npc`
    each carry four documented standing inputs. Folding them into a
    standard-three count is exactly the error the readiness note warns about.
13. **Four slots are not enough for the `GL_2` block.** Any word with a single
    `F` has `(1,1)` entry `1` when its `(0,1)` entry vanishes, so `diag(1, u)`
    with `u != 1` needs the fifth. W364-NFACTOR records the argument; do not
    "simplify" the factorization to four.
14. **The N stabilizer is `alpha`-free.** `nNielsen_factorization` carries no
    `2 <= alpha` binder on purpose, and adding one would trip the unused-variable
    linter. Only the statements about the *actual frame* need `alpha >= 2`.

## 4. Verification record

**End-state record (orchestrator, session close).** Tree `d05976b6` (the last commit is the
memo note; the last Lean change is the registration of `GaussPhaseValues`, one commit
earlier). `lake build GQ2` from the main clone: **green, 5,187 jobs** (Mathlib and
dependencies accepted from the gq2-paper package store; the GQ2 tree fully traced since the
first umbrella of the session). Full ordinary gate with the ledger, through the dependency
wrapper now kept at `scripts/w361_run_with_deps.sh`:

```sh
bash scripts/w361_run_with_deps.sh env -u GQ2_LEDGER_FIXTURE GQ2_LEDGER_GATE=1 bash scripts/check_dyadic.sh
```

**all checks passed**: `check_axioms` all-pass, axiom census **11** (= expected), the five
capstones at the expected census set, the ledger at **51,436 tracked declarations** with **0**
`sorryAx` dependencies, **0** unknown non-standard axiom uses, **0** terminal violations.
(The wave-362 tree gated at 51,212; the difference is the W363 to W365 modules.)

**Fresh source-only build of this tree: PASS.** `scripts/w361_fresh_build.py --packages <gq2-paper
store> --lean <rc2> --jobs 6 --require-live-match`, snapshot
`/private/tmp/gq2-w361-fresh-fru2elbj` (1.3 GB; source snapshot taken 2026-09-18 03:28:06 UTC):
**1,565 / 1,565 local modules** compiled, `failed: []`, `unbuilt: []`, 2,080.2 seconds, no live
source drift, no live manifest drift, 3,727 output files inventoried. Durable copies of the
snapshot's own records are committed beside this document:
`w365-fresh-build-result.json` (SHA-256
`8c47b4aa93b17009db0715c1944f31194f357cb202380b5fe9f718ac64804920`) and
`w365-fresh-build-provenance.json` (SHA-256
`925e22635b17a44b2bbdcc2f064cce07bac611f5eb1ac5657a0fcd56c1b3d941`; pinned compiler
`1b370cfc...`, manifest `3c3d5e1a...`, driver `21b8f1d7...`). The verifier
(`scripts/w361_verify_fresh.py <snapshot> --replay`) was started on it at the close; its
outcome is the last line of this section if it finished, otherwise the next session runs it
(read-only) as its first act. Its content check already printed `FRESH_CONTENT_CHECK_PASS|1565`
(all 1,565 snapshot sources and outputs consistent) before the staged replay began.
**Verifier result: exit 0.** Its complete output was: `FRESH_CONTENT_CHECK_PASS|1565`, `FRESH_VERIFICATION_REPORT|/private/tmp/gq2-w361-fresh-verified-1416wqve/report.json`, `exit=0`. (The heavier multi-hour content-bound staged replay of W361's final record was not repeated; this is the reviewed verifier's own `--replay` run on the new snapshot, and it passed.) Its report is committed beside this document as `w365-fresh-verification-report.json` (SHA-256 `05e3e2c17bbcd3f7260cdf9f068783a5b097f37cf73d3aba71538a4753ea42cb`). Like W361's, this is content consistency with an observed

**W366 end state (after the owner's decisions), tree `fccda098`.** Two more modules registered
(`MNielsenHandles`, `NNielsenHandles`, 108 declarations, all std-3; 1,567 modules in the fresh
build's count). `lake build GQ2`: **green, 5,189 jobs**. Full gate with the ledger through
`scripts/w361_run_with_deps.sh`: **all checks passed**, census **11**, ledger **51,547 tracked
declarations**, 0 `sorryAx`, 0 unknown axioms, 0 terminal violations. A fresh source-only build
of this tree was started at 00:2x and its snapshot line follows this paragraph when it finished
in session; W366's other three lanes changed no Lean under `GQ2/` (the packet TeX, staged
overlays and docs only), so the W365 snapshot above remains a valid record of every module
except the two handles modules.

**Fresh source-only build of the W366 tree: PASS.** Snapshot `/private/tmp/gq2-w361-fresh-_i4abvuq`: **1,567 / 1,567 local modules**, `failed: []`, `unbuilt: []`, 1,974.5 seconds, no live source or manifest drift. Verifier (`w361_verify_fresh.py <snapshot> --replay`) output: `FRESH_CONTENT_CHECK_PASS|1567`, `FRESH_VERIFICATION_REPORT|/private/tmp/gq2-w361-fresh-verified-xi6wknax/report.json`, `exit=0`. Durable copies committed beside this document with SHA-256: 1856d758f5f1903efe4a1ed19f16bbefad374c2e6584f4666ab8e364c4abb4ef  w366-fresh-build-provenance.json; 6b5c00530ec1d8db078e0dde29d21727f561c876c32c707b40f98a917010eede  w366-fresh-build-result.json; 5a6e1a49bc32f034c39384da9e930b90b3d71e2415cc995a3d0c6cb6e89b82d0  w366-fresh-verification-report.json. This, not the W365 snapshot, is the binding record of the session's final tree; do not emit artifacts into either snapshot.
isolated build, not a signed attestation, and it reuses manifest-matching dependency artifacts.


### Verified in the W362-HOUSE lane against base `6770a87e`

These are re-derived facts, not carried claims. Each was checked against the
tree rather than against the W361 handoff.

1. The eleven N modules exist under `GQ2/Dyadic/MarkedCore/` and all eleven
   are directly imported by `GQ2.lean`.
2. They carry 118 `#print axioms` pins, distributed 19/6/1/2/7/4/4/30/30/9/6,
   matching the W361 section 4 table line for line. They contain exactly 118
   public declarations and 7 private ones, and the pin set is in one-to-one
   correspondence with the public set.
3. `docs/dyadic/w361-claude-code-verification-report.json` hashes to
   `aad5d041ec098c6f1d5dc0b8e24953322afdff2073a20a133a79e67e9f1a3711` and
   `docs/dyadic/w361-final-verification-report.json` to
   `bb20e9914dd86be093521808b0267f8ac0f6cd857fe6e13b8285d8213784abcb`,
   both as claimed.
4. The base commit carries no drift from the replayed state. Recomputing the
   verifier's own `local_source_set_sha256` over the `GQ2` import closure from
   the tree at `6770a87e` gives
   `34477d1c4c082aadda64e4a855ba66679765d486db8084fe931ed3b86e36e6dc`,
   identical to the W361 handoff's current verified source-set hash.
5. Registration is complete. Of 1,558 `.lean` files (root `GQ2.lean` plus
   1,557 under `GQ2/`), 1,552 are in the `GQ2` import closure. The six outside
   it are exactly `GQ2/AxiomLedger.lean` and the five exporter drivers under
   `GQ2/Dyadic/Word/`. Exporter drivers with a global `main` stay outside
   `GQ2.lean` intentionally.
6. The two theorem statements have exactly the shape the W361 handoff's
   section 3 describes, in every binder. Both are quoted in full in
   `docs/dyadic/w362-house-note.md` item 6. `{alpha h : ℕ}` with
   `ha : 2 ≤ alpha` and no constraint on `h`, so "every alpha >= 2 and every
   handle count h" is exact. `NFrameModel h` really is
   `Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2] × (Fin (2*h) → ℤ_[2]))`,
   `NFrameCupIsometry` really quantifies over every continuous F₂ character of
   the frame, and `nFrameOrientation_preserved_iff` really is the claimed
   equivalence with the integral b-coordinate.
7. All 118 pins print exactly `[propext, Classical.choice, Quot.sound]`,
   elaborated rather than grepped. All 118 are registered in the 691-name
   `scripts/w361_artifact_axiom_audit.lean` list.
8. The axiom census is eleven at source level: exactly eleven `axiom`
   declarations exist, all in `GQ2/Foundations/Axioms.lean`, and their names
   are set equal to `GQ2.AxiomLedger.bAxioms`. `scripts/check_axioms.sh:28`
   sets `EXPECTED_AXIOMS=11`.
9. There is no `sorry`, `admit` or `native_decide` outside comments anywhere
   in the tree, and none of the 223 `.lean` files `6770a87e` first tracked
   carries a `maxHeartbeats`, `maxRecDepth` or `synthInstance` option.
10. The four publication counts in W361 section 6 item 3 are all exact: four
    pair/mobile packets, six word-only L/N specimens (confirmed by file shape,
    not by prose), the 29-page PDF and its wrapper both hashing as the QA
    record claims, and forty TODO invocations.

11. All three audit drivers pass, run through the reviewed runner:
    `GENERAL_AXIOM_AUDIT_PASS|16` with the ramified-i endpoint at exactly
    twelve axioms (the standard three plus nine);
    `ARTIFACT_AXIOM_AUDIT_PASS|691`; and `GQ2/AxiomLedger.lean` reporting zero
    `sorryAx` dependencies, zero unknown nonstandard axiom uses and zero
    terminal violations, with every capstone at twelve census axioms and each
    Gamma_R capstone identical to its Gamma_A twin.
12. The census is eleven at the environment level, not only at source level.
    The completed umbrella build elaborated 12,964 pins over 12,814
    declarations; exactly eleven distinct nonstandard axioms appear and all
    eleven are `AxiomLedger.bAxioms`. No `sorryAx`, no `Lean.ofReduceBool`.

**Read items 11 and 12 with the caveat in section 2.** They were measured
through the shared cache, which had advanced to the wave's own HEAD by then,
so they are facts about that tree. They transfer back to `6770a87e` because
the intervening diff adds files and eight `GQ2.lean` import lines and modifies
no pre-existing `.lean`, but the ledger's declaration *count* does not
transfer and must not be recorded as a correction to W361's 50,991.

Full detail, with the method and the traps, is in
`docs/dyadic/w362-house-note.md`.

### Carried from W361, not re-run in this wave

The 1,552-module clean snapshot, the 691-pin artifact audit, the 50,991
declaration ledger and the complete content-bound staged replay were performed
by the Codex pass and are recorded in `w361-claude-code-handoff.md` section 5
and the durable JSON report. Item 4 above shows the source state they bound is
the state this wave starts from. It does not re-run them.

### This session: waves 362 to 364

**Pin census, re-derived by the W364-HOUSE lane over the sources at `d2056503`.**
This is a `#print axioms` count over the twelve new modules, cross-checked
against each lane's own runner output. Every pin in the session prints exactly
`[propext, Classical.choice, Quot.sound]` except one, `mStageOneLe`, which
prints the strictly smaller `[propext]`.

| Module, under `GQ2/Dyadic/MarkedCore/` | Pins | Lane | Runner record |
| --- | ---: | --- | --- |
| `MHeadCleanup.lean` | 5 | W362-MHEAD | direct runner, then the mirror harness |
| `MFullFrameCompactness.lean` | 25 | W362-MSTAGES | direct runner |
| `MFullFrameStages.lean` | 12 | W362-MSTAGES | mirror harness |
| `MFrameMatrixLift.lean` | 111 | W362-MINIT | mirror harness (see note) |
| `MInitialCupDepth.lean` | 9 | W362-MCUP | direct runner |
| `MFrameCupCoordinates.lean` | 16 | W362-MCUP | mirror harness |
| `MBasisRowRefinement.lean` | 11 | W362-MKERNEL (+2, W363) | direct runner |
| `MPlaneAmbientStage.lean` | 18 | W362-MKERNEL | mirror harness |
| `MFullStabilizerLift.lean` | 10 | W362-MASSEMBLE (+1, W363) | mirror harness |
| `MNielsenGenerators.lean` | 70 | W363-NIELSEN | direct runner |
| `NNielsenGenerators.lean` | 16 | W363-NIELSEN | direct runner |
| `NNielsenFactorization.lean` | 94 | W364-NFACTOR | direct runner and the mirror harness |
| **Total** | **397** | | |

`MFrameMatrixLift` was verified with the direct runner against the shared cache
before the MSTAGES rewire (commit `3b0a4254`) and with the mirror harness after
it. The two `+N, W363` rows are the W363-MCONSOL move and rename.

The first nine are the wave-362 M architecture; W363-MCONSOL re-elaborated all
nine in dependency order after its renames and recorded `217` pins, `216`
std-3, which is what this lane's independent count reproduces. `#print axioms`
coverage is exact and total: 397 declarations, 397 pins, no declaration
unpinned and no pin naming a declaration that is not there. Unlike the eleven N
modules, where the pin set matched the *public* declarations, here the 17
`private` declarations are pinned too.

Two figures in the lane notes are superseded rather than wrong, and both are
explained by the W363-MCONSOL move: `MHeadCleanup` was 7 at its own close and
is 5, and `MBasisRowRefinement` was 9 and is 11.

**Registration.** 1,569 `.lean` files under `GQ2/`, plus the root `GQ2.lean`.
1,564 are in the `GQ2` import closure. The six outside it are unchanged from
W361: `GQ2/AxiomLedger.lean` (it imports `GQ2`, so registering it would cycle)
and the five exporter drivers under `GQ2/Dyadic/Word/`. All twelve new modules
are imported directly by `GQ2.lean`. Verified twice, by independent routes: an
import-graph walk over the sources, and the scoreboard's own elaborated
registration scan, which printed `SCANNED|1569` and the same six `OUTSIDE`
lines.

**The machine scoreboard**, run from this lane's worktree at `d2056503`:

```sh
GQ2_MIR=/Users/roed/claude/cla/work/main-build-cache/lib/lean \
GQ2_PKG=/Users/roed/claude/gq2-paper/formalizations/gq2-claude/.lake/packages \
bash scripts/scoreboard.sh --raw
```

Exit 0. 1,084 `EXISTS` rows, 0 `MISSING`, 0 `STALE_UMBRELLA`, 2 `UNVERIFIED`
(both prose-level: the A6 review-round count, which is not in git, and the
per-item status of the owner docket). Run without `--raw` the board's OWNER
ITEMS section reads the memo and the newest house note and prints
**`memo and note AGREE 7`**.

**The full ordinary gate.** The dependency wrapper the Codex handoff described
as living in `/private/tmp` and warned might vanish is now in the tree, as
`scripts/w361_run_with_deps.sh` (commit `b87bfa06`). Its invocation is

```sh
bash scripts/w361_run_with_deps.sh \
  env -u GQ2_LEDGER_FIXTURE GQ2_LEDGER_GATE=1 bash scripts/check_dyadic.sh
```

**Read that invocation carefully before running it from a lane worktree.** The
wrapper ends with a hard-coded `cd /Users/roed/claude/cla/work/gq2-dyadic-campaign`
followed by `exec "$@"`, so it gates the **main clone**, whatever worktree you
launch it from, and it runs `lake` through `check_dyadic.sh`. It is the
orchestrator's tool at a merge, not a lane's.

Its last recorded output is the wave-362 close, recorded in section 198 of the
campaign log: `lake build GQ2` green at **5,183 jobs**, and the gate with the
ledger reporting **51,212 tracked declarations**, **0/0/0** (no `sorryAx`
dependency, no unknown nonstandard axiom, no terminal violation), **census
eleven**, and five capstones at the expected axiom set. That figure is
consistent with the W362-HOUSE ledger reading of 51,203 at `8eff12ab`: the
difference of nine is `MFullStabilizerLift`, registered between them.

**No clean-build or replay record exists for this session's end state.** The
last binding whole-tree replay is still the W361 22:53:05 UTC one, durable copy
`docs/dyadic/w361-claude-code-verification-report.json`. The wave-362 gate run
above is an ordinary gate against the shared cache, not a source-only
transitive clean build, and it predates waves 363 and 364 by three module
additions. `python3 scripts/w361_fresh_build.py --require-live-match` was in
flight at the close of wave 364; if it completed, its snapshot path and the
`w361_verify_fresh.py --replay` result belong here, and the orchestrator should
record them in section 1 as well.

**Every lane in this session verified with the direct runner or the mirror
harness, and none invoked `lake`.** W363-MCONSOL states explicitly that
`scripts/check_dyadic.sh` was never run in a lane and the shared cache was never
written to. Two mechanical audits were run over the nine wave-362 modules at the
consolidation: pin-block completeness (217 declarations, 217 pins, zero missing,
zero stale) and hygiene (no em-dash, `sorry`, `native_decide`, `set_option`,
bare `axiom` or over-100-column line added).

**Hygiene over the whole session**, re-measured by W364-HOUSE over every line
added in `6770a87e..d2056503`, `generated/` excluded: **zero em-dashes and zero
en-dashes added**, in any file. 144 added lines exceed 100 codepoints, of which
**two are in Lean sources** (`MFrameMatrixLift.lean:854` at 101 and
`MNielsenGenerators.lean:65` at 117, the latter a docstring line), four are in
scripts, and the remaining 138 are in Markdown tables and citation lines, 73 of
them in `w361-index.md` alone.

## 5. Remaining work

**Orchestrator's ordering** (rewritten 2026-09-18 by W366-HOUSE; the ordering below now
starts *after* Option A, and the push is off it). The owner took **Option A** on 2026-09-18
and authorized the push, so of the decisions this ordering used to put first, two are gone:
the proof-method acceptance is settled for both cores, and `488e7cf2..b9ad374f` is pushed.
Item 4 of `docs/dyadic/owner-items-2026-08-05.md` is the decision record. What is left, in
order:

(1) **Apply Option A**, which is a writing task, not a decision: the proposed wording of
`w364-proof-packet-amendment-mc.md` goes into the packet and the ledger, and the documents
that state the method as unaccepted get their annotations. W366's APPLY lane owns this.
(2) **The three remaining owner decisions**, which are the four Codex adoption items minus
the one Option A settled: the changed M pair/mobile words, the corrected RN interface, and
the symbolic display contract with the legacy L/N artifacts.
(3) **Publication adoption** of the staged L/N packets and the pair/mobile packets
(decisions 13 to 17 in `w363-pub2-note.md`); Route A of `w362-pub-note.md` (fill items 4
and 5 in the three L/N skeletons with the manifest untouched) is the
frozen-identifier-preserving first step.
(4) Only then the optional mathematics in the draft below (handles for the lists). Note that
**Option A removes the generator-level lift work entirely**: the M4/M5/M6/M7 and N4 residue
below was Option B's bill, and Option B was not taken.

The draft that follows is the W364-HOUSE lane's collection, and is accurate at **`2c4d0197`**,
its own base -- *not* at `e34315af`, as it said until 2026-09-18. `e34315af` is the commit
that repaired three of the four documentation items in it; see the strike-throughs below.

### Draft, assembled from the notes (W364-HOUSE)

**Mathematics.**

1. **Nothing is owed on either full-stabilizer lift.** `nFullStabilizer_lift_iff`
   and `mFullStabilizer_lift_iff` are both theorems, std-3, for every
   `alpha >= 2` and every handle count, with the converse. Do not reopen the
   starting-depth, arbitrary-basis, compactness or head-cleanup seams at either
   core, and do not start a class-by-class or rank-by-rank campaign.
2. **Handles, for the two finite lists.** Both lists are rank four because both
   rest on a rank-four classification (`mStabilizer_classification`,
   `nStabilizer_classification`). Extending them needs a classification of the
   *handle-mixing* stabilizer first: `GL` of the `2h` handle block plus the
   core-handle shears, on top of the core families. No such classification is in
   the repo. W363-NIELSEN records a weaker statement that is within easy reach and
   is deliberately not claimed: the core families extended by the identity on the
   handle tail still preserve orientation and cup at every `h`, hence still lift,
   and its coordinate and character machinery is already stated at general `h`.
   Only the final `evenCupForm` expansion is specialised to `h = 0`.
3. **Generator-level lifts, if the packet wording is read strictly.** At M:
   M1 is `mLambdaEquiv`, M2 is `dmTauDEquiv`, M3 is `MScaling` at handle level
   zero, and **M4, M5, M6, M7 have no group-level construction anywhere in the
   repo**. At N the per-family route exists
   (`nNielsenFacLifts_of_param_families`), but its **N4** ingredient
   `nPlaneScalingHypothesis_general` is itself an N-plane compactness limit. So
   the residue is four families at M and one at N. This is work only if the owner
   reads the packet sentence as demanding exhibited generators; see section 5's
   owner list.
4. **The minimality of eight slots is not proved.** W364-NFACTOR shows only that
   the `GL_2` *block* cannot be done in four slots of the `E, F, diag(k,1)`
   families uniformly. Eight overall is a bound for that slot list.
5. **The matrix-level entry point at M is not built** (W363-MAUDIT FLAG-3, still
   open). `MCupFrameCupIsometry` appears only in its defining module and the
   endpoint module; nothing relates it to `M.lean`'s `mCupIsometry` /
   `IsMStabilizer`, which is what `mStabilizer_classification` consumes. The
   semantic predicate is the safer public boundary and should not be replaced;
   the bridge should be added beside it, and that is where
   `MarkedCore/Variance.lean`'s row/column dictionary re-enters. W363-NIELSEN
   supplied the analogous bridge in the cup direction, which is the harder half.

**Publication.**

6. **Six exporters were named as missing by W362-PUB, and W363-PUB2 supplied
   them.** The W362-PUB note's T2.d table names
   `specializationTemplate`, `inputRowsTemplate`, `chainTemplate`,
   `hessianTemplate`, `coordinateTemplate` and `phaseCoverTemplate` as proposals
   for work not done; `scripts/w363_ln_*_export.lean` are the six drivers.
   Whoever finalizes this section must re-read that table rather than quote it:
   it was accurate when written and is not now.
7. **Five `generated/appendix/` skeletons still carry 40 `\dyadicAppendixTODO`
   invocations**, eight in each. A grep returns 45 because each file also carries
   the macro definition on a commented line.
8. **The twelve owner decisions in W362-PUB section T3.c** are the concrete form
   of the publication question: which of routes A, B or C the three frozen L/N
   rows take, whether a ten-item appendix may be published with items carried by
   checked declarations rather than displays, the manifest schema and
   `manifest_version` bump, gate 7's `_astHash` constants, how a
   `status: "STAGED"` artifact is promoted at all, and the two M skeletons that
   lane did not touch.

**Documentation repairs found by this session's housekeeping.** *(W366-HOUSE, 2026-09-18:
items 9, 11 and the disclosure half of 12 LANDED in this same session, in `e34315af` and
`eb3089cd`, after the list was written. Item 10 landed at M and stands at N. All four are
kept with their outcome marked, because the list is cited from section 7.)*

9. ~~`GQ2/Dyadic/MarkedCore/NNielsenGenerators.lean`'s module docstring says the
   MC-N artifact "cannot be produced yet" and that `nNielsen_factorization` and
   `nFamN1` to `nFamN6` exist nowhere under `GQ2/`. W364-NFACTOR landed all of
   them, in the same directory. Comment-only, and the highest-severity docstring
   defect in the session.~~ **DONE in `e34315af`**: the paragraph now carries a
   `[W364: OVERTAKEN the same session ...]` bracket naming
   `NNielsenFactorization.lean` and the three declarations, and is kept as the
   record of why that module stops where it does.
10. Several `MNielsenGenerators` and `NNielsenFactorization` docstrings say "for
    every parameter" where the statement quantifies over a *parameter together
    with a supplied inverse parameter*; no inverse structure on `MStabParam` or
    `NStabParam` exists in the tree. The headline theorems are unaffected
    (the seven and eight families each supply their own inverse), but the
    intermediate lemmas claim more than they state.
    **HALF DONE.** `e34315af` fixed the M half (`MNielsenGenerators.lean:27` now
    spells the supplied-inverse shape out). The **N half stands**:
    `NNielsenFactorization.lean:38-39` still reads "every parameter fixes the
    integral `x̄₁` coordinate, hence preserves `nFrameOrientation`
    (`nNielsenFac_orientation`); every admissible parameter is an
    `NFrameCupIsometry`", while `nNielsenFac_orientation` (`:504`) and
    `nNielsenFac_cupIsometry` (`:565`) both take `(P Q : NStabParam)` with two
    mutual-inverse hypotheses. Comment-only; that module was not in
    `e34315af`'s three.
11. ~~`MNielsenGenerators` refers to the endpoint seven times as
    `mFullStabilizer_lift_of_frame`, the retained alias, and never by the public
    name W363-MCONSOL freed for it. Its quantifier-closure docstring also claims
    "every element of the Smith-Witt stabilizer" where the statement fixes the
    canonical rank-four frame and pins four generator values of the orientation
    character; the N twin spells its clause out and the M one does not.~~
    **DONE in `e34315af`**: zero occurrences of the alias remain in that module,
    and the stabilizer claim now states its canonical-frame and pinned-`chi`
    scope. Re-elaborated at 70 pins, unchanged.
12. `docs/dyadic/w363-m-full-stabilizer-independent-audit.md` pins nine source
    SHA-256 with no as-of commit, and all nine are now stale because
    W363-MCONSOL edited all nine files later the same day. The audit's base is
    `69b9851c`; the verdict is unaffected.
    **DISCLOSED in `eb3089cd`/`e34315af`**: the document now opens with a dated
    W364 annotation naming `69b9851c` as its base, the rename, the diff-check
    result and the post-pass pin count. The nine hashes are still the old ones
    and are still not recomputed, which is the remaining half.

Carried forward from `w361-claude-code-handoff.md` section 6, in its order:

1. Read the scope audits before choosing new mathematics. N's full existence
   theorem is done. If the literal finite Nielsen-list method is still
   required, formulate its artifact separately; do not reopen the solved
   starting-depth, arbitrary-basis or compactness seams.
2. Audit and, if retained, tackle the larger M stabilizer assertion, starting
   from `docs/dyadic/w361-m-next-general-scaffold.md`. The first bounded task
   is coupled M-head divisibility and cleanup, not a new class sweep. Preserve
   the canonical-or-strict-handle alternative. Do not copy N's literal
   head/torsion argument without checking the different M relation.
3. Finish publication artifacts without silently changing authority. Four
   pair/mobile ten-item packets and the 29-page staged PDF exist and passed
   replay and visual QA. Six legacy L/N specimens are word-only. Five old
   appendix skeletons still carry 40 `\dyadicAppendixTODO` invocations, eight
   in each of the five files under `generated/appendix/` (a grep returns 45
   because each file also carries the macro definition on a commented line).
4. Owner and editorial decisions remain, and are listed in
   `w361-claude-code-handoff.md` section 6 item 4 (six of them) and in
   `w361-acceptance-readiness.md` under "Mathematical target decisions" (five,
   overlapping). None was taken at the base of this wave. G3 and release
   remain an owner gate.
   *(2026-09-18: one of the five, the MC proof-method reconciliation, has since
   been taken -- Option A. Both lists carry a dated annotation at that item.)*

   ~~**The owner's own memo does not reflect this.**
   `docs/dyadic/owner-items-2026-08-05.md` has its newest status block at wave
   89 (2026-08-16) reading "Zero items await you". That predates W360 and W361
   by a month, and nobody folded their docket back into it. The W362 house
   note carries the six forward plus one of its own, so
   `scripts/scoreboard.sh` now prints seven against the memo's zero. That
   disagreement is the board working as designed. Only the owner amends the
   memo; do not resolve the disagreement by editing either number.~~
   **OVERTAKEN in this session.** The docket was folded into the memo, which
   now opens with a "Status at wave 362 (2026-09-17)" block. The board reads
   the memo as AUTHORITY and the latest house note as the lane artifact, and
   the two no longer disagree: both read **five** after the owner decided item
   4 and closed item 5 on 2026-09-18. The standing instruction survives the
   rest: only the owner decides an item; a lane may correct the memo's *count*
   to match the owner's own recorded decisions, and W366-HOUSE did exactly that
   and no more.

Standing "do nots", unchanged: do not resurrect the false universal frozen-M
placement claim; do not claim an arbitrary external two-adic unit admits a
rational `NpcDisplayFor`; do not turn existential calibrated realization into
a pointwise arbitrary-fixed-realization theorem; do not generalize the
ramified-i hypothesis away.

## 6. Exact runtime and safe commands

Every path below was checked to exist from a lane worktree at base
`6770a87e`, and the paths are the ones the tools actually resolve, not the
ones a note says they use. Which commands this lane ran, and which it only
read, is stated at each one: `w361_fresh_build.py` and `w361_verify_fresh.py`
were **not** run here, since nothing in this lane changed a source.

```sh
GQ2_LEAN=/Users/roed/.elan/toolchains/leanprover--lean4---v4.31.0-rc2/bin/lean
GQ2_PACKAGES=/Users/roed/claude/gq2-paper/formalizations/gq2-claude/.lake/packages
GQ2_CACHE=/Users/roed/claude/cla/work/main-build-cache/lib/lean
```

Toolchain pin is `leanprover/lean4:v4.31.0-rc2` (`lean-toolchain`). In a lane
worktree, `.lake/build` is a symlink to `/Users/roed/claude/cla/work/main-build-cache`
and `.lake/packages` a symlink to the package store above, so the runner's own
defaults already resolve and the two environment variables are needed only when
pointing at an isolated snapshot instead.

Check a source against the shared cache, writing nothing:

```sh
bash scripts/w361_lean_runner.sh GQ2/Dyadic/MarkedCore/NFullStabilizerLift.lean
```

The runner refuses to start unless the Lean version matches the pin and
`lake-manifest.json` matches the package store's, and it rejects a dependency
package that carries local `GQ2` artifacts. It passes `-DautoImplicit=false
-DrelaxedAutoImplicit=false`. It never invokes `lake`.

The machine scoreboard, read-only, a few minutes:

```sh
GQ2_MIR="$GQ2_CACHE" GQ2_PKG="$GQ2_PACKAGES" bash scripts/scoreboard.sh --raw
```

Read the script's own header before believing a row: it re-derives every fact
by elaboration and prints `UNVERIFIED` where it cannot, and its OWNER ITEMS
section deliberately prints two independently asserted counts and whether they
agree. A disagreement is the product, not a failure.

The axiom census without `lake`, per `w361-claude-code-handoff.md` section 7:

```sh
bash scripts/w361_lean_runner.sh GQ2/AxiomLedger.lean
```

The additive general-endpoint footprint audit, which checks 16 declarations
against exact expected axiom lists and fails on an extra *or* a missing one:

```sh
bash scripts/w361_lean_runner.sh scripts/w361_general_axiom_audit.lean
```

Its expected footprints are the standard three for the structural lemmas, the
standard three plus six standing inputs for the generic supplied-bundle
endpoints, and the standard three plus nine for the canonical `K + RI`
endpoints. Those three lists are literal in the driver; read them there rather
than from prose.

For a new verified tree after edits, and its read-only replay:

```sh
python3 scripts/w361_fresh_build.py \
  --packages "$GQ2_PACKAGES" --lean "$GQ2_LEAN" --jobs 4 --require-live-match
python3 scripts/w361_verify_fresh.py <snapshot path it returns> \
  --packages "$GQ2_PACKAGES" --lean "$GQ2_LEAN" --replay
```

A snapshot is valid only for its frozen bytes. After any source change, build a
new one and use its returned path. Never emit artifacts into an existing fresh
snapshot. The builder wants 6 GiB free at start and 4 GiB during the build.

Two parsing traps, both of which have already produced wrong numbers:

- This tree uses Lean 4.31 module-system imports. 427 import lines are spelled
  `public import`. A scan matching only `^import ` misses 18 modules and
  reports 24 unregistered files where the truth is 6.
- Counting `dyadicAppendixTODO` by grep returns 45, not 40. See section 5
  item 3.
- A long `#print axioms` list wraps across lines in the build log. Rejoin
  continuation lines before matching, or wrapped entries read as truncated
  ones and a footprint of four axioms reads as one.

And one shell trap that cost this lane an hour: `pgrep -f 'lake build GQ2'`
matches your own diagnostic shells, because their command lines contain that
string. A wait loop built on it never exits. Wait on
`grep -q 'Build completed successfully' <log>` instead.

**A cheap source of evidence, worth knowing.** A Lean `#print axioms` emits an
`info:` line, so a full umbrella build's log already carries the axiom
footprint of every pin in the tree. Reading that log is free, cannot disagree
with the build, and does not race the cache the way a separate runner
invocation does. The W362-HOUSE lane closed its whole std-3 and census
question out of the orchestrator's own build log.

**Three commands this session added, listed here because section 4 is where
their output lives and this is where a reader looks for the invocation.**

The full ordinary gate, orchestrator only, because it runs `lake`:

```sh
bash scripts/w361_run_with_deps.sh \
  env -u GQ2_LEDGER_FIXTURE GQ2_LEDGER_GATE=1 bash scripts/check_dyadic.sh
```

`scripts/w361_run_with_deps.sh` is the tracked copy (commit `b87bfa06`) of the
`LEAN_PATH` wrapper the W361 handoff kept in `/private/tmp` and warned might
vanish. **It ends with a hard-coded `cd` into the main clone**, so it gates
`/Users/roed/claude/cla/work/gq2-dyadic-campaign` whatever worktree you launch
it from. That is correct for a merge and wrong for a lane.

The two staged publication checks, read-only, no `lake`:

```sh
bash scripts/w362_check_ln_staged.sh      # replays W361's check first, then W362's
bash scripts/w363_check_ln_staged.sh      # the six W363-PUB2 exporters
```

The second lands with the W363-PUB2 merge and is not in every lane worktree;
check it exists before invoking it.

`w362_check_ln_staged.sh` ends
`W362_LN_STAGED_CHECK_PASS (staged proposals only: not owner approval, not a
manifest entry, not a gate)`. Take that sentence literally; the artifacts it
passes all embed `status: "STAGED"` and every validator refuses any other
value.

## 7. Minimal reading list

1. This document, then `w361-claude-code-handoff.md` for anything it defers to.
2. `docs/dyadic/w361-index.md`, the one-line index of all 71 W360/W361
   documents, with four flags on headlines that outrun their bodies.
3. `GQ2/Dyadic/MarkedCore/NFullStabilizerLift.lean`.
4. `docs/dyadic/w361-n-full-stabilizer-independent-audit.md` and
   `docs/dyadic/w361-n-arbitrary-basis-refinement-audit.md`.
5. `docs/dyadic/w361-n-full-stabilizer-scope.md`, and
   `docs/dyadic/w361-m-next-general-scaffold.md` before any new M work.
6. `docs/dyadic/w361-completion-audit.md` and
   `docs/dyadic/w361-final-endpoint-scope-audit.md` for the campaign.
7. `docs/dyadic/w361-proof-packet-amendment.md` and
   `docs/dyadic/w361-acceptance-readiness.md` for what is proposed but not
   approved. *(2026-09-18: their MC proof-method item is now approved -- Option
   A -- and both carry a dated annotation saying so at the head and at the item.
   Everything else in them is still proposal.)*
8. `docs/dyadic/plan.md` and
   `docs/dyadic/refs/dyadic-presentations-formalization-proof.tex` when
   deciding what remains of M or the finite Nielsen-list artifact.
9. This session's own lane notes, in dependency order. Read the audits before
   the notes they judge, and read `w363-mconsol-note.md` before any
   `w362-*-note.md`, because it renamed a public theorem that all six of them
   were written against.

   *The M architecture, in the order the proof composes:*
   1. `docs/dyadic/w362-mhead-note.md` -- the coupled head cleanup (step 1).
   2. `docs/dyadic/w362-mkernel-note.md` -- the derivative-kernel interpolation
      and `mStageStep_holds` (step 2). Its per-module pin figures of 9 and 18
      are pre-`MCONSOL`; the first is now 11.
   3. `docs/dyadic/w362-minit-note.md` -- the initial free lift (step 3).
   4. `docs/dyadic/w362-mcup-note.md` -- the semantic cup predicate and the
      depth-three error (step 4).
   5. `docs/dyadic/w362-mstages-note.md` -- compactness, stage transfer and the
      conditional composition (step 5).
   6. `docs/dyadic/w362-massemble-note.md` -- the assembly, and the two landed
      theorems in full. Not one of the scaffold's five items; its header says so.

   *The audits of that architecture, both worth reading before any new M work:*
   7. `docs/dyadic/w363-m-full-stabilizer-independent-audit.md` -- the
      proof-level independent audit. **VERDICT: PROVED AS STATED**, with three
      flagged items, of which FLAG-3 is still open. Its nine source SHA-256 are
      as of `69b9851c`, before the consolidation renamed and edited all nine
      files. *(2026-09-18: the document does now say so; `eb3089cd` added a
      dated W364 annotation at its head naming that base. The hashes themselves
      are still the pre-consolidation ones.)*
   8. `docs/dyadic/w363-m-full-stabilizer-scope.md` -- the twin of
      `w361-n-full-stabilizer-scope.md`: what the M theorem does and does not
      settle in the governing packet, and six remaining campaign requirements.
      It cites the endpoint by its pre-rename spelling `mFullStabilizer_lift_of_frame`.

   *The consolidation, then the two Nielsen lanes:*
   9. `docs/dyadic/w363-mconsol-note.md` -- the rename map, the import-cost
      measurement, the nine docstring corrections and the folded audit flags.
      The one document that reconciles the six W362 notes with the tree.
   10. `docs/dyadic/w363-nielsen-note.md` -- the MC-M finite list and the N cup
       bridge. Its section "The N side" is **overtaken by W364-NFACTOR**: what it
       records as absent now exists.
   11. `docs/dyadic/w364-nfactor-note.md` -- the N factorization into six
       families, the bounded `GL_2` factorization, and the MC-N finite list.

   *The publication side and the housekeeping, readable independently:*
   12. `docs/dyadic/w362-pub-note.md` -- the ten-item inventory, the staged L/N
       packets, and twelve owner decisions. Its T2.d list of six missing
       exporters was supplied by W363-PUB2.
   13. `docs/dyadic/w363-pub2-note.md` -- the six exporters, staged, with the
       five-kind binding taxonomy.
   14. `docs/dyadic/w362-house-note.md` -- every Codex headline claim checked
       against the tree, and the shared-cache staleness lesson.
   15. `docs/dyadic/w364-house-note.md` -- this session's round, the index
       extension, and the scoreboard baseline for the next session.
   16. `docs/dyadic/w365-gauss-note.md` -- the Gauss sign and exponent of the
       wall-handle endpoints named as standalone theorems in every sector, with
       the item-8 cell map. It answers the narrow question of publication
       decision 16; the decision itself is untaken.

   *Wave 366, the first wave after the owner's decisions of 2026-09-18. Read
   `owner-items-2026-08-05.md` item 4 before any of them, because all four lanes
   are downstream of Option A:*
   17. `docs/dyadic/w366-apply-note.md` -- Option A applied: the amendment
       wording into the vendored packet and ledger, the MC-M and MC-N rows
       marked discharged in the completion audit, and the two W364 MC documents
       marked adopted for the applied parts. This is the lane that turns the
       decision into the record; read it before citing any MC row.
   18. `docs/dyadic/w366-gaussexport-note.md` -- the item-8 Gauss exporter
       driver and its staged artifacts, downstream of `w365-gauss-note.md`.
   19. `docs/dyadic/w366-handles-note.md` -- `MNielsenHandles`, the handle
       extension of the M finite list (section 5 item 2 above). Optional
       mathematics, not owed.
   20. `docs/dyadic/w366-house-note.md` -- watch 27, the decision's consequences
       across the docs corpus, this document's post-decision repairs, and the
       scoreboard baseline. Its "sites the APPLY lane must handle" list is the
       cross-check on item 17.

**One trap in that list.** Do not read `docs/dyadic/w361-final-verification.md`
as a current record. It opens "Final verified checkpoint, 2026-09-17 17:30
UTC" and states at line 141 that it is the current final snapshot; it is the
superseded 1,541-module / 573-pin one. The binding record is the 1,552-module
replay that finished at 22:53:05 UTC, durable copy
`docs/dyadic/w361-claude-code-verification-report.json`. Thirteen documents
link to the stale record and four of them do it in the words "current
verification status". `docs/dyadic/w361-index.md` flag 0 has the details.

## 8. Suggested first prompt to the next session

> Continue the dyadic campaign in `/Users/roed/claude/cla/work/gq2-dyadic-campaign`.
> Read `docs/dyadic/w362-claude-handoff.md` first, then its section 7 reading list.
> Read the memory file `codex-era-infra` before running any build: a plain
> `lake build` rebuilt Mathlib once this session and the fix is recorded there.
> The general selected ramified-i field endpoint, the full N and M stabilizer
> liftings (`nFullStabilizer_lift_iff`, `mFullStabilizer_lift_iff`) and both
> finite Nielsen-family lists are proved and independently audited; do not
> reopen those seams and do not start class-by-class or rank-by-rank work.
> The owner took **Option A** on 2026-09-18 -- the compactness proof method is
> accepted for both cores -- and authorized the push, so neither is open; wave
> 366 applied Option A to the packet, the ledger and the records. What remains
> is the memo's five items (the changed M words, the RN interface, the display
> contract, the untracked PDF, and G3/release), publication adoption (all L/N
> exporters are staged), and hygiene. No new axioms, placeholders, native
> decisions, resource-limit increases, frozen-word replacement, commit-message
> rewriting, or release without authorization.
> Keep verified facts, proposed scope amendments and owner decisions separate,
> and maintain a restartable handoff.

# W362-MASSEMBLE lane note

Lane: M full-stabilizer lifting, step 5 of 5 (the assembly: the final theorem
and its converse). Branch `claude/w362-massemble`, base `da50ba68`, with
`claude/w362-mkernel` merged in mid-lane.
Route item 5 of `docs/dyadic/w361-m-next-general-scaffold.md`.

One new module, `GQ2/Dyadic/MarkedCore/MFullStabilizerLift.lean`, 9
declarations. No existing module edited, `GQ2.lean` untouched. Default limits
(200000 heartbeats), `autoImplicit=false`, no `sorry`, no `admit`, no
`native_decide`, no new axiom, no resource option. Every declaration is std-3
(`propext`, `Classical.choice`, `Quot.sound`), pinned in file by
`#print axioms`.

Verification of record: `scripts/mirror.sh sweep`, then `gen
GQ2.Dyadic.MarkedCore.MBasisRowRefinement`, `gen
GQ2.Dyadic.MarkedCore.MPlaneAmbientStage` (the two MKERNEL modules, whose
oleans were not yet in the shared cache), then `check
GQ2/Dyadic/MarkedCore/MFullStabilizerLift.lean`. The six other M modules of the
wave came from the shared cache via the sweep. `lake` was never invoked. The
earlier conditional version of the module was additionally checked with `bash
scripts/w361_lean_runner.sh` directly against the shared cache.

No new mathematics about the M tower is proved here. The file reconciles the
dialects of the assembled halves and states the theorem.

## Status of record

**The M full-stabilizer lifting theorem is proved. It is not conditional.**

The lane was written against `MStageStep alpha h` as an open interface and then
rewritten when MKERNEL landed `mStageStep_holds` in
`GQ2/Dyadic/MarkedCore/MPlaneAmbientStage.lean` (std-3, every `alpha >= 2` and
every rank). `MStageStep` is now discharged, not assumed; this module consumes
`mStageStep_holds ha` and carries no interface hypothesis of any kind. Both
directions of the image characterization are unconditional.

`alpha >= 2` throughout. `MFrameMatrixLift`'s fixed-`T` lift needs it (the
torsion digit is killed by `2 ^ (alpha - 1)` only from `alpha = 2` on),
`MCupFrameCupIsometry` carries that binder, and so does `mStageStep_holds`.
Nothing here says anything about `alpha = 1`.

This is the M analogue of `NFullStabilizerLift`, not a copy of it. The M route
fixes the composite word `T = A * C^(2^(alpha-1))` rather than the single letter
`A`, its head row is the two-letter `2 f(A) + 2^alpha f(C)`, and its
orientation sees the `B` coordinate only through its parity. Nothing from the N
theorem is reused; only its shape is matched.

## A name that had to change

The ticket and the coordinator both asked for `mFullStabilizer_lift`.
That name is **already taken** in namespace `GQ2.Dyadic.MarkedCore`, by
`MFullFrameStages.mFullStabilizer_lift`, which is the *conditional composition
shape* with five interface hypotheses. The lane may not edit existing modules,
so the landed theorem is

```
mFullStabilizer_lift_of_frame
```

"of_frame" = from frame-level hypotheses (orientation and cup). The
characterization keeps the exact N-parallel name `mFullStabilizer_lift_iff`,
which was free. A later consolidation wave that is allowed to touch
`MFullFrameStages.lean` could rename the conditional shape (say to
`mStage_fullStabilizer_lift_of_interfaces`) and free the plain name.

## The two landed theorems

```
theorem mFullStabilizer_lift_of_frame {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (hchi : ∀ z, mFrameOrientation ha h (phi z) = mFrameOrientation ha h z)
    (hcup : MCupFrameCupIsometry ha phi) :
    ∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
      (∀ x, mPhiHom (mStageOneLe ha) h (abMk (Psi x)) =
        phi (mPhiHom (mStageOneLe ha) h (abMk x)))
```

```
theorem mFullStabilizer_lift_iff {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)) :
    (∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
      (∀ x, mPhiHom (mStageOneLe ha) h (abMk (Psi x)) =
        phi (mPhiHom (mStageOneLe ha) h (abMk x)))) ↔
    (∀ z, mFrameOrientation ha h (phi z) = mFrameOrientation ha h z) ∧
      MCupFrameCupIsometry ha phi
```

The second matches `nFullStabilizer_lift_iff` line for line with
`chiN / nPhiHom / nFrameOrientation / NFrameCupIsometry` replaced by
`chiM / mPhiHom / mFrameOrientation / MCupFrameCupIsometry`. Like its N twin it
asserts **no** finite explicit Nielsen-generator presentation of the
stabilizer: the condition is stated entirely on the full abelian frame. Handles
may mix arbitrarily; the commuting square is on all elements and includes the
torsion coordinate.

The forward proof is one composition,

```
mFullStabilizer_lift_of_fixedHead ha phi hchi
  (mFullStabilizer_relError_of_cup ha phi hcup) (mStageStep_holds ha)
```

so the assembly really is the whole of this ticket: MINIT had already
discharged the initial-basis obligations of `mFullStabilizer_lift` inside
`mFullStabilizer_lift_of_fixedHead`, and what was left was its `herror`
hypothesis and the stage step.

## Sufficiency: the error, with no orientation input

```
theorem mFullStabilizer_relError_of_cup {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (hcup : MCupFrameCupIsometry ha phi) :
    mRelWord alpha (fun i => mFrameLiftEquiv ha h phi (freeTwoRankGen (coreRank h) i)) *
      (mRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) 3
```

Worth recording: this uses **no orientation hypothesis**. MCUP's
`mCupStageError_of_frame` does not take one, so cup preservation by itself
already puts the actual M relator error in lambda-three. The orientation is
needed only later, by the stage iteration.

## Necessity, and the small bridge it needed

```
theorem mFullStabilizer_orientation_cup_of_lift {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type))
    (hchi : ∀ x, chiM alpha h (Psi x) = chiM alpha h x)
    (hframe : ∀ x, mPhiHom (mStageOneLe ha) h (abMk (Psi x)) =
      phi (mPhiHom (mStageOneLe ha) h (abMk x))) :
    (∀ z, mFrameOrientation ha h (phi z) = mFrameOrientation ha h z) ∧
      MCupFrameCupIsometry ha phi
```

Its two halves are `mFullStabilizer_orientation_of_lift` and
`mFullStabilizer_cup_of_lift`. The cup half is `mCupFrameCupIsometry_of_aut`
applied with `hphi i = (hframe (dmGen alpha h i)).symm`, which typechecks
because `mCupFrameCanonicalMark ha h i` unfolds to
`mPhiHom (mStageOneLe ha) h (abMk (dmGen alpha h i))`; it needs no `chiM`
hypothesis at all. The orientation half is the small bridge the ticket asked
for, and it is new here:

```
theorem mFrameOrientation_cupFrameOfDM {alpha h : ℕ} (ha : 2 ≤ alpha)
    (x : DM alpha h) :
    mFrameOrientation ha h (mCupFrameOfDM ha h x) = chiM alpha h x
```

proved by `ContinuousMulEquiv.symm_apply_apply` then `abLiftG_abMk`, the M twin
of `nFrameOrientation_canonicalFrameHom`, together with

```
theorem mCupFrameOfDM_surjective {alpha h : ℕ} (ha : 2 ≤ alpha) :
    Function.Surjective (mCupFrameOfDM ha h)
```

so that an arbitrary frame element can be written as the frame image of a core
element and `chiM`-preservation on `D_M` becomes orientation-preservation on
the frame.

## The two reconciliations the ticket asked about

Both dialect mismatches turned out to be already packaged upstream by MINIT, so
this lane restates neither; the note records which is which.

- **Orientation: not definitionally equal.** `mFrameOrientation hα h`
  (`MFrameMatrixLift`) is a `ContinuousMonoidHom (MFrameModel h) ℤ_[2]ˣ` on the
  frame; `mStageOrientation alpha h` (consumed by `MFullFrameStages`, and by
  `MStageStep` itself) lives on the free pro-two group. There is no
  definitional identity. The bridge is `mStageOrientation_eq_freeOrientation`
  composed with `mFrameOrientation_projection`, packaged as
  `mFrameLiftEquiv_stageOrientation`, which is what
  `mFullStabilizer_lift_of_fixedHead` consumes.
  `mFrameOrientation_eq_apiChiModel` further identifies `mFrameOrientation`
  with `MFrameApi`'s `mFrameApiChiModel` on the nose.
- **Projection: definitionally equal.** `mFrameProjection hα h`,
  `mCupFreeFrameProjection ha h` and `mPhiHom (mStageOneLe ha) h ∘ abMk ∘
  mStageProjection alpha h` are the same composite; `mFrameProjection_apply`,
  `mCupFreeFrameProjection_apply` and `mStageFrameHom_apply` are all `rfl`, and
  `mFrameFreeAbProjection_gen` closes the generator case. The packaging is
  `mFrameLiftEquiv_stageFrame`.

The one bridge genuinely missing upstream was the torsion word, where
`MFullFrameStages` writes `mStageTorsionWord` and `MFrameCupCoordinates` writes
the product out. It is the same term up to beta reduction, and this lane names
it so that the assembly never relies on that silently:

```
theorem mFullStabilizer_liftEquiv_head {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)) :
    mFrameLiftEquiv ha h phi (freeTwoRankGen (coreRank h) 0) *
        mFrameLiftEquiv ha h phi (freeTwoRankGen (coreRank h) 2) ^ 2 ^ (alpha - 1) =
      freeTwoRankGen (coreRank h) 0 *
        freeTwoRankGen (coreRank h) 2 ^ 2 ^ (alpha - 1)
```

proved by `mFrameLiftEquiv_torsionWord` alone.

## Deliverables

`GQ2/Dyadic/MarkedCore/MFullStabilizerLift.lean`, all std-3:

| declaration | role |
| --- | --- |
| `mFullStabilizer_liftEquiv_head` | torsion-word bridge |
| `mFullStabilizer_relError_of_cup` | depth-three error from cup alone |
| `mFullStabilizer_lift_of_frame` | **sufficiency, unconditional** |
| `mCupFrameOfDM_surjective` | frame quotient is onto |
| `mFrameOrientation_cupFrameOfDM` | `chiM` to frame orientation |
| `mFullStabilizer_orientation_of_lift` | necessity, orientation half |
| `mFullStabilizer_cup_of_lift` | necessity, cup half |
| `mFullStabilizer_orientation_cup_of_lift` | necessity, packaged |
| `mFullStabilizer_lift_iff` | **the image characterization** |

Registration in `GQ2.lean` is the orchestrator's, not this lane's; the module
imports `MFrameCupCoordinates`, `MFrameMatrixLift` and `MPlaneAmbientStage`.

## What remains

Nothing in this lane. Two things a later wave may want:

1. Free the name `mFullStabilizer_lift` by renaming the conditional composition
   shape in `MFullFrameStages.lean`, then rename `mFullStabilizer_lift_of_frame`
   onto it for exact N parity.
2. `MCupFrameCupIsometry` is the semantic predicate, quantified over every
   continuous mod-two frame character. MCUP's
   `MCupFrameCupIsometry.reducedRows_of_projection` already converts it to the
   reduced-coordinate system `Abar G Abar^T = G`; a lane wanting a *decidable*
   or matrix-level entry point to `mFullStabilizer_lift_iff` would package that
   direction and its converse as a standalone equivalence. That is a
   convenience, not a gap: the theorem above is complete as stated.

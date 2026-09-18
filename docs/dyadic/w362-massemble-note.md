# W362-MASSEMBLE lane note

Lane: M full-stabilizer lifting, step 5 of 5 (the assembly: the final theorem
and its converse). Branch `claude/w362-massemble`, base `da50ba68`.
Route item 5 of `docs/dyadic/w361-m-next-general-scaffold.md`.

One new module, `GQ2/Dyadic/MarkedCore/MFullStabilizerLift.lean`. No existing
module edited, `GQ2.lean` untouched. Verification of record: `bash
scripts/w361_lean_runner.sh GQ2/Dyadic/MarkedCore/MFullStabilizerLift.lean`
against the shared campaign cache, which already carried all six merged M
modules of this wave. Default limits (200000 heartbeats), `autoImplicit=false`,
no `sorry`, no `admit`, no `native_decide`, no new axiom, no resource option.
All nine declarations are std-3 (`propext`, `Classical.choice`, `Quot.sound`),
pinned in file by `#print axioms`. No new mathematics about the M tower is
proved here; the file reconciles three interfaces and records what is owed.

## Status of record

**The M full-stabilizer theorem is proved modulo `MStageStep`; the converse is
unconditional.**

`MStageStep alpha h` is the named depth-step interface defined in
`GQ2/Dyadic/MarkedCore/MFullFrameStages.lean`. Nothing in this repository
exhibits an `(alpha, h)` satisfying it. The forward theorem below is therefore
not a proved lifting theorem, and must not be relayed as one. Do not confuse it
with the N theorem `nFullStabilizer_lift_iff`
(`GQ2/Dyadic/MarkedCore/NFullStabilizerLift.lean`), which is unconditional; the
N file supplied the *shape* that was matched, not a result that was reused.

`alpha >= 2` throughout. `MFrameMatrixLift`'s fixed-`T` lift needs it (the
torsion digit is killed by `2 ^ (alpha - 1)` only from `alpha = 2` on), and
`MCupFrameCupIsometry` carries that binder. `MStageStep` itself is stated
without an `alpha` bound, but it has no producer anywhere, least of all at
`alpha = 1`.

## T1: the forward theorem

```
theorem mFullStabilizer_lift_of_step {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (hchi : ∀ z, mFrameOrientation ha h (phi z) = mFrameOrientation ha h z)
    (hcup : MCupFrameCupIsometry ha phi)
    (hstep : MStageStep alpha h) :
    ∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
      (∀ x, mPhiHom (mStageOneLe ha) h (abMk (Psi x)) =
        phi (mPhiHom (mStageOneLe ha) h (abMk x)))
```

`hstep` is the only conditional hypothesis: `hchi` and `hcup` are the actual
content of the statement, not interfaces. The proof is one composition,

```
mFullStabilizer_lift_of_fixedHead ha phi hchi
  (mFullStabilizer_relError_of_cup ha phi hcup) hstep
```

so the assembly is genuinely the whole of this ticket: MINIT already
discharged the initial-basis obligations of `mFullStabilizer_lift` inside
`mFullStabilizer_lift_of_fixedHead`, and what was left was its `herror`
hypothesis.

That is the second deliverable:

```
theorem mFullStabilizer_relError_of_cup {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (hcup : MCupFrameCupIsometry ha phi) :
    mRelWord alpha (fun i => mFrameLiftEquiv ha h phi (freeTwoRankGen (coreRank h) i)) *
      (mRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) 3
```

It is unconditional, and it carries **no orientation hypothesis**: MCUP's
`mCupStageError_of_frame` does not use one, so the depth-three relator error of
the fixed-`T` lift follows from the semantic full-frame cup predicate alone.

## The two reconciliations the ticket asked about

Both dialect mismatches turned out to be already packaged upstream by MINIT, so
this lane restates neither; the note records which is which.

- **Orientation: not definitionally equal.** `mFrameOrientation hα h`
  (`MFrameMatrixLift`) is a `ContinuousMonoidHom (MFrameModel h) ℤ_[2]ˣ` on the
  frame; `mStageOrientation alpha h` (consumed by `MFullFrameStages`) lives on
  the free pro-two group. There is no definitional identity. The bridge is
  `mStageOrientation_eq_freeOrientation` composed with
  `mFrameOrientation_projection`, packaged as
  `mFrameLiftEquiv_stageOrientation`, which is what `mFullStabilizer_lift_of_fixedHead`
  consumes. `mFrameOrientation_eq_apiChiModel` further identifies
  `mFrameOrientation` with `MFrameApi`'s `mFrameApiChiModel` on the nose.
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

## T2: the converse and the image characterization

```
theorem mFullStabilizer_lift_iff_of_step {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (hstep : MStageStep alpha h) :
    (∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
      (∀ x, mPhiHom (mStageOneLe ha) h (abMk (Psi x)) =
        phi (mPhiHom (mStageOneLe ha) h (abMk x)))) ↔
    (∀ z, mFrameOrientation ha h (phi z) = mFrameOrientation ha h z) ∧
      MCupFrameCupIsometry ha phi
```

This is the M twin of `nFullStabilizer_lift_iff` and matches its shape line for
line, with `chiN / nPhiHom / nFrameOrientation / NFrameCupIsometry` replaced by
`chiM / mPhiHom / mFrameOrientation / MCupFrameCupIsometry` and the extra
`hstep` binder. Like its N twin it asserts **no** finite explicit
Nielsen-generator presentation of the stabilizer: the condition is stated
entirely on the full abelian frame.

`hstep` is consumed by the right-to-left direction only. The left-to-right
direction is stated separately and is unconditional:

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

## T3: what a proof of `MStageStep alpha h` must look like to plug in

The interface is consumed verbatim, with no wrapper, so a producer must land
exactly this `Prop` from `MFullFrameStages.lean`:

```
def MStageStep (alpha h : ℕ) : Prop :=
  ∀ n : ℕ, ∀ e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type),
    (∀ i, mStageOrientation alpha h (e (freeTwoRankGen (coreRank h) i)) =
      mStageOrientation alpha h (freeTwoRankGen (coreRank h) i)) →
    (∀ f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
        (Multiplicative ℤ_[2]),
      f (mRelWord alpha (fun i => e (freeTwoRankGen (coreRank h) i))) =
        f (mRelWord alpha (freeTwoRankGen (coreRank h)))) →
    mRelWord alpha (fun i => e (freeTwoRankGen (coreRank h) i)) *
      (mRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n + 3) →
    ∃ s : Fin (coreRank h) → FreeTwoRank (coreRank h),
      (∀ i, s i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n + 2)) ∧
      (∀ i, mStageOrientation alpha h (s i) = 1) ∧
      (∀ i, ∀ f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
        (Multiplicative ℤ_[2]), f (s i) = 1) ∧
      mRelWord alpha (fun i => e (freeTwoRankGen (coreRank h) i) * s i) *
        (mRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
          twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n + 4)
```

Read with `d = n + 2`. What the producer owes, in the order the consumers use
it:

1. **Universally quantified over `n` and over `e`.** It is applied inside the
   induction of `exists_mStageBasis_exact_stage` at every depth, to a basis the
   induction itself produced, never to a fixed or constructed one. A statement
   proved only for the initial basis, or only for small `n`, does not plug in.
2. **`e` is an actual `ContinuousMulEquiv` of the free pro-two group**, not a
   marking, not a matrix, and not an automorphism of a graded or class-`c`
   quotient. There is no assumed derivative image and no diagonal restriction.
3. **The three premises are exactly as written.** The orientation premise is on
   generators and is `mStageOrientation`, the free-group orientation, not
   `mFrameOrientation`; the row premise is agreement under *every* continuous
   `Multiplicative ℤ_[2]` character; the error premise is literal membership in
   `twoCentralSeries _ (n + 3)`, at the level of group elements, not of any
   quotient.
4. **The correction `s` is a tuple of group elements, one per generator**, and
   all four conclusions are needed: depth `n + 2`, orientation-blind,
   invisible to every ordinary character (this is what keeps the integral
   coordinate matrix exactly fixed through
   `mStage_relator_row_transport`), and error pushed to `n + 4`.
5. **The correction must be a basis change.** The consumer immediately feeds
   `s` to `exists_freeTwoBasisCorrection`, which needs `s i ∈ twoCentralSeries
   _ 2`; the interface's `n + 2` gives that for every `n` by
   `twoCentralSeries_antitone`. A supply at depth `n + 1` would not.

Its N counterpart is the composite of `NAmbientStageSupply` with
`exists_nBasis_full_relative_correction`. A producer that lands the `Prop`
above, for a single `(alpha, h)` with `alpha >= 2`, immediately upgrades
`mFullStabilizer_lift_of_step` and `mFullStabilizer_lift_iff_of_step` at that
`(alpha, h)` with no edit to this file: `hstep` is a plain hypothesis in both.

The kernel lane owns that producer and `MBasisRowRefinement.lean`; nothing in
this lane touches either.

## Deliverables

`GQ2/Dyadic/MarkedCore/MFullStabilizerLift.lean`, 9 declarations, all std-3:

| declaration | conditional on `MStageStep`? |
| --- | --- |
| `mFullStabilizer_liftEquiv_head` | no |
| `mFullStabilizer_relError_of_cup` | no |
| `mFullStabilizer_lift_of_step` | **yes** |
| `mCupFrameOfDM_surjective` | no |
| `mFrameOrientation_cupFrameOfDM` | no |
| `mFullStabilizer_orientation_of_lift` | no |
| `mFullStabilizer_cup_of_lift` | no |
| `mFullStabilizer_orientation_cup_of_lift` | no |
| `mFullStabilizer_lift_iff_of_step` | **yes**, right-to-left only |

Registration in `GQ2.lean` is the orchestrator's, not this lane's.

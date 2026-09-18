/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.MarkedCore.MFrameCupCoordinates
import GQ2.Dyadic.MarkedCore.MFrameMatrixLift

/-!
# The full M-frame stabilizer, conditional on the stage step, and its converse

This file assembles the three merged halves of wave 362 into one statement and
its converse. It proves no new mathematics about the M tower; it reconciles the
three interfaces and records exactly what is still owed.

**What is conditional and what is not.** The forward direction carries the
hypothesis `MStageStep alpha h` of `MFullFrameStages`, and nothing in this
repository produces an instance of that hypothesis at any `(alpha, h)`. So the
forward theorem is *not* a proved lifting theorem: read it as "the M
full-stabilizer lift holds at `(alpha, h)` as soon as `MStageStep alpha h`
does". The converse direction carries no such hypothesis and is unconditional.

Do not read this file as the M copy of `NFullStabilizerLift`. The N theorem
`nFullStabilizer_lift` is unconditional; this one is not, and the M route also
fixes the composite word `T = A * C^(2^(alpha-1))` rather than the single letter
`A`. The N file is the shape that was matched, not a result that was reused.

Contents:

* `mFullStabilizer_relError_of_cup`: the MCUP obligation of
  `mFullStabilizer_lift_of_fixedHead`, discharged for the fixed-`T` lift out of
  the semantic full-frame cup predicate alone. Unconditional, and it does not
  use the orientation.
* `mFullStabilizer_lift_of_step`: the forward theorem, conditional on
  `MStageStep alpha h` and on nothing else.
* `mFrameOrientation_cupFrameOfDM`, `mFullStabilizer_orientation_of_lift`,
  `mFullStabilizer_cup_of_lift`, `mFullStabilizer_orientation_cup_of_lift`: the
  converse, unconditional.
* `mFullStabilizer_lift_iff_of_step`: the image characterization, the M twin of
  `nFullStabilizer_lift_iff`, conditional in one direction only.

`alpha >= 2` throughout: `MFrameMatrixLift`'s fixed-`T` lift needs it (the
torsion digit is killed by `2 ^ (alpha - 1)` only from `alpha = 2` on), and
`MCupFrameCupIsometry` is stated with that binder.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section

open GQ2 GQ2.SectionThree Multiplicative Roe.Labute
open scoped GQ2.SectionThree.TopAbInstances

/-! ## Bridging the three interfaces

The three merged halves speak three dialects of the same two notions.

* **Orientation.** `MFrameMatrixLift.mFrameOrientation` lives on the frame
  `MFrameModel h`; `MFullFrameStages` states its hypothesis with
  `mStageOrientation`, which lives on the free pro-two group. They are *not*
  the same function and there is no definitional identity between them: the
  bridge is `mStageOrientation_eq_freeOrientation` composed with
  `mFrameOrientation_projection`, and it is already packaged upstream as
  `mFrameLiftEquiv_stageOrientation`. That lemma is used below rather than
  restated.
* **Projection.** `mFrameProjection` and `mPhiHom _ h ∘ abMk ∘ mStageProjection`
  *are* definitionally equal (`mFrameProjection_apply` and
  `mFrameFreeAbProjection_gen` are both `rfl` on generators); the upstream
  packaging is `mFrameLiftEquiv_stageFrame`, again used rather than restated.
  `MCUP`'s `mCupFreeFrameProjection` is the same composite once more, and
  `mCupFreeFrameProjection_apply` is `rfl`.

The one bridge genuinely missing upstream is the torsion word, where
`MFullFrameStages` says `mStageTorsionWord` and `MFrameCupCoordinates` writes
the product out; that is `mFullStabilizer_liftEquiv_head` below. -/

/-- The fixed-`T` lift, written in the product form `MFrameCupCoordinates`
expects rather than the `mStageTorsionWord` form `MFullFrameStages` uses. The
two are the same term up to beta reduction; this lemma is the place that says
so, so that the assembly below never silently relies on it. -/
theorem mFullStabilizer_liftEquiv_head {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)) :
    mFrameLiftEquiv ha h phi (freeTwoRankGen (coreRank h) 0) *
        mFrameLiftEquiv ha h phi (freeTwoRankGen (coreRank h) 2) ^ 2 ^ (alpha - 1) =
      freeTwoRankGen (coreRank h) 0 *
        freeTwoRankGen (coreRank h) 2 ^ 2 ^ (alpha - 1) :=
  mFrameLiftEquiv_torsionWord ha h phi

/-! ## The forward theorem -/

/-- **The MCUP obligation of `mFullStabilizer_lift_of_fixedHead`, discharged.**
The literal depth-three relator error of the fixed-`T` lift follows from the
semantic full-frame cup predicate alone.

Unconditional: no `MStageStep`, and no orientation hypothesis either, since
`mCupStageError_of_frame` does not use one. -/
theorem mFullStabilizer_relError_of_cup {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (hcup : MCupFrameCupIsometry ha phi) :
    mRelWord alpha (fun i => mFrameLiftEquiv ha h phi (freeTwoRankGen (coreRank h) i)) *
      (mRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) 3 :=
  mCupStageError_of_frame ha (mFrameLiftEquiv ha h phi) hcup
    (mFullStabilizer_liftEquiv_head ha phi) (mFrameLiftEquiv_stageFrame ha h phi)

/-- **Full M-frame stabilizer sufficiency, conditional on the stage step.**
A continuous automorphism of the actual full M frame preserving the canonical
orientation and the full mod-two cup form is induced by a continuous
automorphism of `D_M` preserving `chiM`, *provided* `MStageStep alpha h` holds.

This is not a proved lift. `MStageStep alpha h` is the named depth-step
interface of `MFullFrameStages`, and no `(alpha, h)` is known to satisfy it;
the kernel lane owns its producer. Everything else is discharged:
`MFrameMatrixLift` supplies the initial fixed-`T` free basis with the exact
frame square and the preserved orientation, `MFrameCupCoordinates` supplies its
depth-three relator error, and `MFullFrameStages` supplies the iteration and
the torsion-sensitive compact limit.

Handles may mix arbitrarily and the conclusion is an all-element commuting
square for the full abelianization `mPhiHom`, torsion slot included. -/
theorem mFullStabilizer_lift_of_step {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (hchi : ∀ z, mFrameOrientation ha h (phi z) = mFrameOrientation ha h z)
    (hcup : MCupFrameCupIsometry ha phi)
    (hstep : MStageStep alpha h) :
    ∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
      (∀ x, mPhiHom (mStageOneLe ha) h (abMk (Psi x)) =
        phi (mPhiHom (mStageOneLe ha) h (abMk x))) :=
  mFullStabilizer_lift_of_fixedHead ha phi hchi
    (mFullStabilizer_relError_of_cup ha phi hcup) hstep

/-! ## The converse, unconditional -/

/-- The full frame quotient of `D_M` is surjective. -/
theorem mCupFrameOfDM_surjective {alpha h : ℕ} (ha : 2 ≤ alpha) :
    Function.Surjective (mCupFrameOfDM ha h) :=
  (mFrameExists_phiEquiv (mStageOneLe ha) h).surjective.comp abMk_surjective

/-- The transported orientation of the frame image of a core element is that
element's own `chiM`. This is the M twin of
`nFrameOrientation_canonicalFrameHom`, and it is what turns `chiM`-preservation
on `D_M` into orientation-preservation on the frame. -/
theorem mFrameOrientation_cupFrameOfDM {alpha h : ℕ} (ha : 2 ≤ alpha)
    (x : DM alpha h) :
    mFrameOrientation ha h (mCupFrameOfDM ha h x) = chiM alpha h x := by
  change abLiftG (chiM alpha h) ((mFrameExists_phiEquiv (mStageOneLe ha) h).symm
    (mFrameExists_phiEquiv (mStageOneLe ha) h (abMk x))) = _
  rw [ContinuousMulEquiv.symm_apply_apply, abLiftG_abMk]

/-- **Converse, orientation half.** If `phi` is induced on the full frame by a
`chiM`-preserving continuous automorphism of `D_M`, it preserves the canonical
orientation. Unconditional. -/
theorem mFullStabilizer_orientation_of_lift {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type))
    (hchi : ∀ x, chiM alpha h (Psi x) = chiM alpha h x)
    (hframe : ∀ x, mPhiHom (mStageOneLe ha) h (abMk (Psi x)) =
      phi (mPhiHom (mStageOneLe ha) h (abMk x)))
    (z : MFrameModel h) :
    mFrameOrientation ha h (phi z) = mFrameOrientation ha h z := by
  obtain ⟨x, rfl⟩ := mCupFrameOfDM_surjective ha z
  have hf : mCupFrameOfDM ha h (Psi x) = phi (mCupFrameOfDM ha h x) := hframe x
  rw [← hf, mFrameOrientation_cupFrameOfDM, mFrameOrientation_cupFrameOfDM, hchi]

/-- **Converse, cup half.** If `phi` is induced on the full frame by a
continuous automorphism of `D_M`, it is a full-frame cup isometry.
Unconditional, and it needs no `chiM` hypothesis. -/
theorem mFullStabilizer_cup_of_lift {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type))
    (hframe : ∀ x, mPhiHom (mStageOneLe ha) h (abMk (Psi x)) =
      phi (mPhiHom (mStageOneLe ha) h (abMk x))) :
    MCupFrameCupIsometry ha phi :=
  mCupFrameCupIsometry_of_aut ha Psi phi fun i => (hframe (dmGen alpha h i)).symm

/-- **The converse of the M full-stabilizer theorem, stated on its own.**
Everything induced on the full M frame by a `chiM`-preserving continuous
automorphism of `D_M` preserves the orientation and the full mod-two cup form.

This half is **unconditional**: it does not mention `MStageStep`, and it would
stand unchanged if that interface were refuted. -/
theorem mFullStabilizer_orientation_cup_of_lift {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type))
    (hchi : ∀ x, chiM alpha h (Psi x) = chiM alpha h x)
    (hframe : ∀ x, mPhiHom (mStageOneLe ha) h (abMk (Psi x)) =
      phi (mPhiHom (mStageOneLe ha) h (abMk x))) :
    (∀ z, mFrameOrientation ha h (phi z) = mFrameOrientation ha h z) ∧
      MCupFrameCupIsometry ha phi :=
  ⟨mFullStabilizer_orientation_of_lift ha phi Psi hchi hframe,
    mFullStabilizer_cup_of_lift ha phi Psi hframe⟩

/-! ## The image characterization -/

/-- **The exact image condition on the full M frame, the M twin of
`nFullStabilizer_lift_iff`.** A continuous frame automorphism is induced by a
`chiM`-preserving continuous automorphism of `D_M` exactly when it preserves the
canonical orientation and the full mod-two cup form.

**Conditional in one direction only.** The hypothesis `MStageStep alpha h` is
consumed by the right-to-left direction; the left-to-right direction is the
unconditional `mFullStabilizer_orientation_cup_of_lift` and does not use it.
So this is an iff modulo the stage step, not a proved characterization: nothing
in this repository exhibits an `(alpha, h)` with `MStageStep alpha h`.

Like its N twin, this asserts no finite explicit Nielsen-generator presentation
of the stabilizer; the condition is stated entirely on the full abelian
frame. -/
theorem mFullStabilizer_lift_iff_of_step {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (hstep : MStageStep alpha h) :
    (∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
      (∀ x, mPhiHom (mStageOneLe ha) h (abMk (Psi x)) =
        phi (mPhiHom (mStageOneLe ha) h (abMk x)))) ↔
    (∀ z, mFrameOrientation ha h (phi z) = mFrameOrientation ha h z) ∧
      MCupFrameCupIsometry ha phi := by
  constructor
  · rintro ⟨Psi, hchi, hframe⟩
    exact mFullStabilizer_orientation_cup_of_lift ha phi Psi hchi hframe
  · rintro ⟨hchi, hcup⟩
    exact mFullStabilizer_lift_of_step ha phi hchi hcup hstep

#print axioms mFullStabilizer_liftEquiv_head
#print axioms mFullStabilizer_relError_of_cup
#print axioms mFullStabilizer_lift_of_step
#print axioms mCupFrameOfDM_surjective
#print axioms mFrameOrientation_cupFrameOfDM
#print axioms mFullStabilizer_orientation_of_lift
#print axioms mFullStabilizer_cup_of_lift
#print axioms mFullStabilizer_orientation_cup_of_lift
#print axioms mFullStabilizer_lift_iff_of_step

end
end GQ2.Dyadic.MarkedCore

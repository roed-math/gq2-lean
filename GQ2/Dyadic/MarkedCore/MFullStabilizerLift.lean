/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.MarkedCore.MFrameCupCoordinates
import GQ2.Dyadic.MarkedCore.MFrameMatrixLift
import GQ2.Dyadic.MarkedCore.MPlaneAmbientStage

/-!
# Lifting the full M-frame orientation/cup stabilizer

Every continuous automorphism of the actual full M abelian frame preserving the
canonical orientation and the full mod-two cup form lifts to an actual
continuous automorphism of `D_M` preserving `chiM`. Handles may mix arbitrarily.
The conclusion is an all-element commuting square for the full abelianization
`mPhiHom`, torsion coordinate included, and the condition is exact: it is also
necessary.

**Unconditional.** No stage-supply, group-lift or matrix premise remains. The
`MStageStep` interface that `MFullFrameStages` states as a hypothesis is
discharged by `MPlaneAmbientStage.mStageStep_holds` for every `alpha >= 2` and
every rank, and this file consumes that theorem rather than carrying the
interface as a hypothesis.

This is the M analogue of `NFullStabilizerLift`, not a copy of it. The M route
is not a text substitution of the N proof: it fixes the composite word
`T = A * C^(2^(alpha-1))` rather than the single letter `A`, its head row is
the coupled two-letter `2 f(A) + 2^alpha f(C)`, its primitive relation vector
is `e_A + 2^(alpha-1) e_C`, its depth-three step turns on the surviving head
being a **square**, its crossed models are the M ones, and its orientation sees
the `B` coordinate only through its parity.

What the route does reuse from the N development is shared infrastructure,
never an N relator conclusion: `N.lean`'s `nFrameModel_map_t` (applied to M
frame automorphisms, `MFrameModel h` and `NFrameModel h` being the same Lean
type), the commutator tail of `NInitialCupDepth` (`freeTail_eq_of_cup`,
`freeTail_value`, `reducedRows`), the closed correction kernel
`nPlaneCorrectionKernel` with its closedness and the row witnesses
`nBasisKernelWitness_mem` / `_row`, `NPlaneAmbientStage.oneWord` as a tuple
container, and `NFrameCupCoordinates`. The M defect itself is shifted by the M
stage identity `evenRawStageShift_m`, never by the N one.

Contents:

* `mFullStabilizer_relError_of_cup`: the depth-three relator error of the
  fixed-`T` lift, from the semantic full-frame cup predicate alone. It uses no
  orientation hypothesis.
* `mFullStabilizer_lift`: sufficiency, and the public name. Together with
  `mFullStabilizer_lift_iff` it is the public pair of this module, the exact
  twin of the pair `nFullStabilizer_lift` / `nFullStabilizer_lift_iff` of
  `NFullStabilizerLift`.
* `mFullStabilizer_lift_of_frame`: the same statement under the earlier
  spelling, retained as an alias so that consumers written against that name
  keep elaborating. It is definitionally the theorem above, not a weaker one.
* `mFrameOrientation_cupFrameOfDM`, `mFullStabilizer_orientation_of_lift`,
  `mFullStabilizer_cup_of_lift`, `mFullStabilizer_orientation_cup_of_lift`:
  necessity.
* `mFullStabilizer_lift_iff`: the exact image characterization, the M twin of
  `nFullStabilizer_lift_iff`.

Neither `mFullStabilizer_lift` nor `mFullStabilizer_lift_iff` asserts a finite
explicit Nielsen-generator list for the stabilizer, and neither states the
rank-four packet: those are separate artifacts.

`alpha >= 2` throughout: `MFrameMatrixLift`'s fixed-`T` lift needs it (the
torsion digit is killed by `2 ^ (alpha - 1)` only from `alpha = 2` on),
`MCupFrameCupIsometry` carries that binder, and so does `mStageStep_holds`.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section

open GQ2 GQ2.SectionThree Multiplicative Roe.Labute
open scoped GQ2.SectionThree.TopAbInstances

/-! ## Bridging the assembled interfaces

The merged halves speak three dialects of the same two notions.

* **Orientation.** `MFrameMatrixLift.mFrameOrientation` lives on the frame
  `MFrameModel h`; `MFullFrameStages` states its hypotheses with
  `mStageOrientation`, which lives on the free pro-two group. They are *not*
  the same function and there is no definitional identity between them: the
  bridge is `mStageOrientation_eq_freeOrientation` composed with
  `mFrameOrientation_projection`, already packaged upstream as
  `mFrameLiftEquiv_stageOrientation`, which is used below rather than restated.
  `mFrameOrientation_eq_apiChiModel` further identifies `mFrameOrientation`
  with `MFrameApi`'s `mFrameApiChiModel` on the nose.
* **Projection.** `mFrameProjection`, `mCupFreeFrameProjection` and
  `mPhiHom _ h ∘ abMk ∘ mStageProjection` *are* definitionally equal:
  `mFrameProjection_apply`, `mCupFreeFrameProjection_apply` and
  `mStageFrameHom_apply` are all `rfl`, and `mFrameFreeAbProjection_gen` closes
  the generator case. The upstream packaging is `mFrameLiftEquiv_stageFrame`,
  again used rather than restated.

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

/-! ## Sufficiency -/

/-- The literal depth-three relator error of the fixed-`T` lift, from the
semantic full-frame cup predicate alone.

This carries **no orientation hypothesis**: `mCupStageError_of_frame` does not
use one, so cup preservation by itself already puts the actual M relator error
in lambda-three. -/
theorem mFullStabilizer_relError_of_cup {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (hcup : MCupFrameCupIsometry ha phi) :
    mRelWord alpha (fun i => mFrameLiftEquiv ha h phi (freeTwoRankGen (coreRank h) i)) *
      (mRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) 3 :=
  mCupStageError_of_frame ha (mFrameLiftEquiv ha h phi) hcup
    (mFullStabilizer_liftEquiv_head ha phi) (mFrameLiftEquiv_stageFrame ha h phi)

/-- **Full M-frame stabilizer sufficiency, with no identity-handle
restriction.** A continuous automorphism of the actual full M frame preserving
the canonical orientation and the full mod-two cup form is induced by a
continuous automorphism of `D_M` preserving `chiM`.

Unconditional, for every `alpha >= 2` and every handle count.
`MFrameMatrixLift` supplies the initial fixed-`T` free basis with the exact
frame square and the preserved orientation, `mFullStabilizer_relError_of_cup`
supplies its depth-three relator error, `MFullFrameStages` supplies the
iteration and the torsion-sensitive compact limit, and
`MPlaneAmbientStage.mStageStep_holds` discharges the depth-step interface that
iteration consumes.

This is the M twin of `nFullStabilizer_lift`. -/
theorem mFullStabilizer_lift {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (hchi : ∀ z, mFrameOrientation ha h (phi z) = mFrameOrientation ha h z)
    (hcup : MCupFrameCupIsometry ha phi) :
    ∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
      (∀ x, mPhiHom (mStageOneLe ha) h (abMk (Psi x)) =
        phi (mPhiHom (mStageOneLe ha) h (abMk x))) :=
  mFullStabilizer_lift_of_fixedHead ha phi hchi
    (mFullStabilizer_relError_of_cup ha phi hcup) (mStageStep_holds ha)

/-- The earlier spelling of `mFullStabilizer_lift`, retained as an alias. The
suffix recorded that `MFullFrameStages` then occupied the plain name with its
interface-level composition shape; that shape is now
`mFullStabilizer_lift_of_interfaces`, and the plain name is this module's. -/
theorem mFullStabilizer_lift_of_frame {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (hchi : ∀ z, mFrameOrientation ha h (phi z) = mFrameOrientation ha h z)
    (hcup : MCupFrameCupIsometry ha phi) :
    ∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
      (∀ x, mPhiHom (mStageOneLe ha) h (abMk (Psi x)) =
        phi (mPhiHom (mStageOneLe ha) h (abMk x))) :=
  mFullStabilizer_lift ha phi hchi hcup

/-! ## Necessity -/

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

/-- **Necessity, orientation half.** If `phi` is induced on the full frame by a
`chiM`-preserving continuous automorphism of `D_M`, it preserves the canonical
orientation. -/
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

/-- **Necessity, cup half.** If `phi` is induced on the full frame by a
continuous automorphism of `D_M`, it is a full-frame cup isometry. It needs no
`chiM` hypothesis. -/
theorem mFullStabilizer_cup_of_lift {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h))
    (Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type))
    (hframe : ∀ x, mPhiHom (mStageOneLe ha) h (abMk (Psi x)) =
      phi (mPhiHom (mStageOneLe ha) h (abMk x))) :
    MCupFrameCupIsometry ha phi :=
  mCupFrameCupIsometry_of_aut ha Psi phi fun i => (hframe (dmGen alpha h i)).symm

/-- **Necessity.** Everything induced on the full M frame by a
`chiM`-preserving continuous automorphism of `D_M` preserves the orientation and
the full mod-two cup form. -/
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

/-- **The exact image condition, stated entirely on the full M abelian frame.**
A continuous frame automorphism is induced by a `chiM`-preserving continuous
automorphism of `D_M` exactly when it preserves the canonical orientation and
the full mod-two cup form.

Unconditional in both directions, for every `alpha >= 2` and every handle
count. Like its N twin `nFullStabilizer_lift_iff` this does not assert a finite
explicit Nielsen-generator presentation of the stabilizer, and it says nothing
about the rank-four packet. -/
theorem mFullStabilizer_lift_iff {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)) :
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
    exact mFullStabilizer_lift ha phi hchi hcup

#print axioms mFullStabilizer_liftEquiv_head
#print axioms mFullStabilizer_relError_of_cup
#print axioms mFullStabilizer_lift
#print axioms mFullStabilizer_lift_of_frame
#print axioms mCupFrameOfDM_surjective
#print axioms mFrameOrientation_cupFrameOfDM
#print axioms mFullStabilizer_orientation_of_lift
#print axioms mFullStabilizer_cup_of_lift
#print axioms mFullStabilizer_orientation_cup_of_lift
#print axioms mFullStabilizer_lift_iff

end
end GQ2.Dyadic.MarkedCore

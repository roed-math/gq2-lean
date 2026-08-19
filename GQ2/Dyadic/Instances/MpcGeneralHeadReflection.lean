/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.MpcGeneralHeadSpan
import GQ2.Dyadic.Instances.M0C0PivotAutomorphism

/-!
# Uniform head reflection from the orientation row

For `alpha >= 2`, the compact-M orientation determines the full additive `D` coordinate:
the equation `chiM x = 1` forces that coordinate to vanish.  Consequently the secondary
head condition is automatic both for general stages and for exact-character corrections.

This closes head reflection uniformly in `alpha`, handle count, and stage.  The only remaining
finite-range problem is head completion, namely replacing the `C` correction by a deep-derived
one without changing the shift.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralHeadReflection

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.SectionThree
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.M0C0PivotAudit
open GQ2.Dyadic.Instances.M0C0PivotAutomorphism
open GQ2.Dyadic.Instances.MpcGeneralFiniteStages
open GQ2.Dyadic.Instances.MpcGeneralFiniteSpan
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcGeneralChiCorrection
open GQ2.Dyadic.Instances.MpcGeneralMarkedStages
open GQ2.Dyadic.Instances.MpcGeneralHeadSpan
open GQ2.Roe.Labute

/-- Exact triviality of the compact-M orientation forces the full additive `D` row to
vanish, at every handle count. -/
theorem mpcGeneralDeltaD_eq_one_of_chi_eq_one
    {alpha h : ℕ} (halpha : 2 ≤ alpha) {x : DM alpha h}
    (hx : chiM alpha h x = 1) : mpcGeneralDeltaD alpha h x = 1 := by
  let z := mPhiHom (by omega : 1 ≤ alpha) h (abMk x)
  have hzchi : mFrameApiChiModel alpha h z = 1 := by
    rw [← chiM_eq_mPhiHom (by omega : 1 ≤ alpha), hx]
  have hD : (toAdd z).2.2.2.1 = 0 :=
    chi_trivial_forces_d_zero halpha (toAdd z).2.1 (toAdd z).2.2.2.1 hzchi
  have hzD : (toAdd z).2.2.2.1 = toAdd (mDHom alpha h (abMk x)) := by
    rfl
  apply Multiplicative.toAdd.injective
  change toAdd (mDHom alpha h (abMk x)) = 0
  rw [← hzD]
  exact hD

/-- Every general stage already has the secondary head condition. -/
theorem mpcGeneralStage_headDelta {alpha h k : ℕ} (halpha : 2 ≤ alpha)
    {m : Fin (coreRank h) → (DM alpha h : Type)}
    (hm : m ∈ mpcGeneralStage alpha h k) :
    mpcGeneralDeltaD alpha h (m 0) = 1 := by
  apply mpcGeneralDeltaD_eq_one_of_chi_eq_one halpha
  rw [hm.2.1 0]
  exact chiM_dmA alpha h

/-- For `alpha >= 2`, the marked-stage state space is the original general-stage space. -/
theorem mpcGeneralMarkedStage_eq_stage {alpha h k : ℕ} (halpha : 2 ≤ alpha) :
    mpcGeneralMarkedStage alpha h k = mpcGeneralStage alpha h k := by
  ext m
  constructor
  · exact fun hm => hm.1
  · exact fun hm => ⟨hm, mpcGeneralStage_headDelta halpha hm⟩

/-- The head correction source is just the exact-character source: its extra `D` equation
is forced by `chiM = 1`. -/
theorem mpcGeneralHeadCorrectionSource_eq_chi
    {alpha h j : ℕ} (halpha : 2 ≤ alpha) (i : Fin (coreRank h)) :
    mpcGeneralHeadCorrectionSource alpha h j i =
      twoCentralSeries (DM alpha h : Type) j ⊓ mpcGeneralChiKer alpha h := by
  by_cases hi : i = 0
  · rw [mpcGeneralHeadCorrectionSource, if_pos hi]
    apply le_antisymm inf_le_left
    intro x hx
    refine ⟨hx, MonoidHom.mem_ker.mpr ?_⟩
    apply mpcGeneralDeltaD_eq_one_of_chi_eq_one halpha
    exact MonoidHom.mem_ker.mp hx.2
  · rw [mpcGeneralHeadCorrectionSource, if_neg hi]

/-- Hence the finite head image is the ordinary exact-character image. -/
theorem mpcGeneralHeadCorrectionImage_eq_chi
    {alpha h j n : ℕ} (halpha : 2 ≤ alpha) (i : Fin (coreRank h)) :
    mpcGeneralHeadCorrectionImage alpha h j n i =
      mpcGeneralChiCorrectionImage alpha h j n := by
  rw [mpcGeneralHeadCorrectionImage, mpcGeneralChiCorrectionImage,
    mpcGeneralHeadCorrectionSource_eq_chi halpha]

/-- Exact-character reachability therefore proves the uniform head-reflection supply. -/
theorem mpcGeneral_headReflectionSupply {alpha h : ℕ} (halpha : 2 ≤ alpha) :
    MpcGeneralHeadReflectionSupply alpha h := by
  intro k hk m hm
  obtain ⟨E⟩ := exists_mpcGeneralChiStageCorrection halpha m hm.1 hk
  let F : MpcGeneralHeadLevelCorrection alpha h k := fun i =>
    ⟨levelMk (DM alpha h) (k + 1) (E.factors i), by
      rw [mpcGeneralHeadCorrectionImage_eq_chi halpha]
      exact ⟨E.factors i, ⟨E.depth i, MonoidHom.mem_ker.mpr (E.chi i)⟩, rfl⟩⟩
  refine ⟨F, Subtype.ext ?_⟩
  have hdepthLevel : ∀ i,
      levelMk (DM alpha h) (k + 1) (E.factors i) ∈
        lambdaImage (DM alpha h) (k - 1) (k + 1) :=
    fun i => ⟨E.factors i, E.depth i, rfl⟩
  change evenRawDbarWord
      (fun i => levelMk (DM alpha h) (k + 1) (m i))
      (fun i => levelMk (DM alpha h) (k + 1) (E.factors i)) = _
  rw [← evenRawStageShift_m (G := DM alpha h) halpha (by omega)
    h k hk _ _ hdepthLevel]
  rw [mpcGeneralStageShift_eq (by omega)]
  have hnext : levelMk (DM alpha h) (k + 1)
      (mRelWord alpha (mpcGeneralModify m E.factors)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr E.nextRel
  change (levelMk (DM alpha h) (k + 1) (mRelWord alpha m))⁻¹ *
      levelMk (DM alpha h) (k + 1)
        (mRelWord alpha (mpcGeneralModify m E.factors)) =
    (levelMk (DM alpha h) (k + 1) (mRelWord alpha m))⁻¹
  rw [hnext, mul_one]

/-- After head reflection, general head completion alone proves the general pivot shift. -/
theorem mpcPivShiftH_of_generalHeadCompletion
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hcomplete : MpcGeneralHeadCompletionSupply alpha h) :
    MpcPivShiftH alpha h :=
  mpcPivShiftH_of_generalHeadReflectionCompletion halpha
    (mpcGeneral_headReflectionSupply halpha) hcomplete

end

end GQ2.Dyadic.Instances.MpcGeneralHeadReflection

section AxiomPins

open GQ2.Dyadic.Instances.MpcGeneralHeadReflection

#print axioms mpcGeneralDeltaD_eq_one_of_chi_eq_one
#print axioms mpcGeneralStage_headDelta
#print axioms mpcGeneralMarkedStage_eq_stage
#print axioms mpcGeneralHeadCorrectionSource_eq_chi
#print axioms mpcGeneralHeadCorrectionImage_eq_chi
#print axioms mpcGeneral_headReflectionSupply
#print axioms mpcPivShiftH_of_generalHeadCompletion

end AxiomPins

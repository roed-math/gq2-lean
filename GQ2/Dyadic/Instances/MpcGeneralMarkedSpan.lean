/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.MpcGeneralMarkedStages

/-!
# The uniform marked finite-range problem

This module adds the one secondary head constraint to the finite correction homomorphism.
The distinguished `C` source is already the deep derived subgroup; the head source is now
also required to have zero additive `D` coordinate.  All other coordinates remain the exact
`chiM` sources.

The resulting range theorem is precisely the successor statement needed on the marked state
space, uniformly in `alpha`, the handle count, and the filtration stage.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralMarkedSpan

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcGeneralFiniteStages
open GQ2.Dyadic.Instances.MpcGeneralFiniteSpan
open GQ2.Dyadic.Instances.MpcGeneralMarkedStages
open GQ2.Roe.Labute

/-- The exact marked source in one coordinate.  The original `C` restriction is retained,
and coordinate zero additionally preserves the secondary `D` invariant. -/
def mpcGeneralMarkedCorrectionSource (alpha h j : ℕ)
    (i : Fin (coreRank h)) : Subgroup (DM alpha h : Type) :=
  if i = 0 then
    mpcGeneralCorrectionSource alpha h j i ⊓
      (mpcGeneralDeltaD alpha h).toMonoidHom.ker
  else
    mpcGeneralCorrectionSource alpha h j i

/-- The finite image of one marked correction source. -/
def mpcGeneralMarkedCorrectionImage (alpha h j n : ℕ)
    (i : Fin (coreRank h)) : Subgroup (levelQuot (DM alpha h) n) :=
  (mpcGeneralMarkedCorrectionSource alpha h j i).map (levelMk (DM alpha h) n)

theorem mem_mpcGeneralMarkedCorrectionImage_iff_exists
    {alpha h j n : ℕ} {i : Fin (coreRank h)} (x : levelQuot (DM alpha h) n) :
    x ∈ mpcGeneralMarkedCorrectionImage alpha h j n i ↔
      ∃ e : DM alpha h,
        e ∈ twoCentralSeries (DM alpha h : Type) j ∧
        chiM alpha h e = 1 ∧
        (i = 2 → ∀ f : ContinuousMonoidHom
          (DM alpha h : Type) (Multiplicative ℤ_[2]), f e = 1) ∧
        (i = 0 → mpcGeneralDeltaD alpha h e = 1) ∧
        levelMk (DM alpha h) n e = x := by
  constructor
  · rintro ⟨e, he, rfl⟩
    have hold : e ∈ mpcGeneralCorrectionSource alpha h j i := by
      by_cases hi : i = 0
      · rw [mpcGeneralMarkedCorrectionSource, if_pos hi] at he
        exact he.1
      · rw [mpcGeneralMarkedCorrectionSource, if_neg hi] at he
        exact he
    have hdepth : e ∈ twoCentralSeries (DM alpha h : Type) j := by
      by_cases hi : i = 2
      · rw [mpcGeneralCorrectionSource, if_pos hi] at hold
        exact hold.1.1
      · rw [mpcGeneralCorrectionSource, if_neg hi] at hold
        exact hold.1
    have hchi : chiM alpha h e = 1 := by
      by_cases hi : i = 2
      · rw [mpcGeneralCorrectionSource, if_pos hi] at hold
        exact MonoidHom.mem_ker.mp hold.1.2
      · rw [mpcGeneralCorrectionSource, if_neg hi] at hold
        exact MonoidHom.mem_ker.mp hold.2
    have hrow : i = 2 → ∀ f : ContinuousMonoidHom
        (DM alpha h : Type) (Multiplicative ℤ_[2]), f e = 1 := by
      intro hi
      rw [mpcGeneralCorrectionSource, if_pos hi] at hold
      exact mem_mpcGeneralRowKer_iff.mp hold.2
    refine ⟨e, hdepth, hchi, hrow, ?_, rfl⟩
    intro hi
    rw [mpcGeneralMarkedCorrectionSource, if_pos hi] at he
    exact MonoidHom.mem_ker.mp he.2
  · rintro ⟨e, hdepth, hchi, hrow, hdelta, rfl⟩
    refine ⟨e, ?_, rfl⟩
    have hold : e ∈ mpcGeneralCorrectionSource alpha h j i := by
      by_cases hi : i = 2
      · rw [mpcGeneralCorrectionSource, if_pos hi]
        exact ⟨⟨hdepth, MonoidHom.mem_ker.mpr hchi⟩,
          mem_mpcGeneralRowKer_iff.mpr (hrow hi)⟩
      · rw [mpcGeneralCorrectionSource, if_neg hi]
        exact ⟨hdepth, MonoidHom.mem_ker.mpr hchi⟩
    by_cases hi : i = 0
    · rw [mpcGeneralMarkedCorrectionSource, if_pos hi]
      exact ⟨hold, MonoidHom.mem_ker.mpr (hdelta hi)⟩
    · rw [mpcGeneralMarkedCorrectionSource, if_neg hi]
      exact hold

/-- All marked coordinate choices at one finite stage. -/
abbrev MpcGeneralMarkedLevelCorrection (alpha h k : ℕ) :=
  ∀ i : Fin (coreRank h),
    mpcGeneralMarkedCorrectionImage alpha h (k - 1) (k + 1) i

/-- Forget the marked constraints and retain a raw depth correction. -/
def mpcGeneralMarkedLevelToRaw {alpha h k : ℕ}
    (E : MpcGeneralMarkedLevelCorrection alpha h k) :
    EvenRawDepthCorrection (DM alpha h) h k where
  correction i := (E i).1
  depth i := by
    obtain ⟨e, he, hlevel⟩ := (E i).2
    refine ⟨e, ?_, hlevel⟩
    by_cases hi : i = 0
    · rw [mpcGeneralMarkedCorrectionSource, if_pos hi] at he
      by_cases hi2 : i = 2
      · rw [mpcGeneralCorrectionSource, if_pos hi2] at he
        exact he.1.1.1
      · rw [mpcGeneralCorrectionSource, if_neg hi2] at he
        exact he.1.1
    · rw [mpcGeneralMarkedCorrectionSource, if_neg hi] at he
      by_cases hi2 : i = 2
      · rw [mpcGeneralCorrectionSource, if_pos hi2] at he
        exact he.1.1
      · rw [mpcGeneralCorrectionSource, if_neg hi2] at he
        exact he.1

/-- The marked forgetful map is a homomorphism. -/
noncomputable def mpcGeneralMarkedLevelToRawHom (alpha h k : ℕ) :
    MpcGeneralMarkedLevelCorrection alpha h k →*
      EvenRawDepthCorrection (DM alpha h) h k where
  toFun := mpcGeneralMarkedLevelToRaw
  map_one' := by ext i; rfl
  map_mul' _ _ := by ext i; rfl

/-- The marked finite shift homomorphism. -/
noncomputable def mpcGeneralMarkedLevelShiftHom {alpha h : ℕ}
    (m : Fin (coreRank h) → (DM alpha h : Type)) (k : ℕ) (hk : 3 ≤ k) :
    MpcGeneralMarkedLevelCorrection alpha h k →* zLayer (DM alpha h) k :=
  (evenRawDepthShiftHom
    (fun i => levelMk (DM alpha h) (k + 1) (m i)) hk).comp
      (mpcGeneralMarkedLevelToRawHom alpha h k)

/-- A group-level marked correction gives a finite marked correction. -/
def mpcGeneralMarkedCorrectionToLevel {alpha h k : ℕ}
    {m : Fin (coreRank h) → (DM alpha h : Type)}
    (E : MpcGeneralMarkedStageCorrection m k) :
    MpcGeneralMarkedLevelCorrection alpha h k := fun i =>
  ⟨levelMk (DM alpha h) (k + 1) (E.factors i),
    (mem_mpcGeneralMarkedCorrectionImage_iff_exists _).mpr
      ⟨E.factors i, E.depth i, E.chi i, fun hi => by
        subst hi
        exact E.row, fun hi => by
          subst hi
          exact E.headDelta, rfl⟩⟩

/-- Exact finite range criterion for one marked-stage correction. -/
theorem nonempty_mpcGeneralMarkedCorrection_iff_target_mem_range
    {alpha h k : ℕ} (halpha : 2 ≤ alpha)
    {m : Fin (coreRank h) → (DM alpha h : Type)}
    (hm : m ∈ mpcGeneralMarkedStage alpha h k) (hk : 3 ≤ k) :
    Nonempty (MpcGeneralMarkedStageCorrection m k) ↔
      mpcGeneralLevelTarget hm.1 ∈
        (mpcGeneralMarkedLevelShiftHom m k hk).range := by
  constructor
  · rintro ⟨E⟩
    refine ⟨mpcGeneralMarkedCorrectionToLevel E, Subtype.ext ?_⟩
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
  · rintro ⟨E, hE⟩
    have hex : ∀ i : Fin (coreRank h),
        ∃ e : DM alpha h,
          e ∈ twoCentralSeries (DM alpha h : Type) (k - 1) ∧
          chiM alpha h e = 1 ∧
          (i = 2 → ∀ f : ContinuousMonoidHom
            (DM alpha h : Type) (Multiplicative ℤ_[2]), f e = 1) ∧
          (i = 0 → mpcGeneralDeltaD alpha h e = 1) ∧
          levelMk (DM alpha h) (k + 1) e = (E i).1 :=
      fun i => (mem_mpcGeneralMarkedCorrectionImage_iff_exists (E i).1).mp (E i).2
    choose e hdepth hchi hrow hdelta hlevel using hex
    refine ⟨{
      factors := e
      depth := hdepth
      chi := hchi
      row := hrow 2 rfl
      headDelta := hdelta 0 rfl
      nextRel := ?_ }⟩
    apply (GQ2.Dyadic.SqCore.lim_mem_twoCentralSeries_iff_levelMk (k + 1) _).mpr
    have hmark : (fun i => (E i).1) =
        fun i => levelMk (DM alpha h) (k + 1) (e i) := by
      funext i
      exact (hlevel i).symm
    have hshift := congrArg Subtype.val hE
    change evenRawDbarWord
      (fun i => levelMk (DM alpha h) (k + 1) (m i))
      (fun i => (E i).1) = _ at hshift
    have hdepthLevel : ∀ i,
        levelMk (DM alpha h) (k + 1) (e i) ∈
          lambdaImage (DM alpha h) (k - 1) (k + 1) :=
      fun i => ⟨e i, hdepth i, rfl⟩
    rw [hmark, ← evenRawStageShift_m (G := DM alpha h) halpha (by omega)
      h k hk _ _ hdepthLevel, mpcGeneralStageShift_eq (by omega)] at hshift
    change (levelMk (DM alpha h) (k + 1) (mRelWord alpha m))⁻¹ *
        levelMk (DM alpha h) (k + 1)
          (mRelWord alpha (mpcGeneralModify m e)) =
      (levelMk (DM alpha h) (k + 1) (mRelWord alpha m))⁻¹ at hshift
    apply mul_left_cancel
      (a := (levelMk (DM alpha h) (k + 1) (mRelWord alpha m))⁻¹)
    simpa only [mul_one] using hshift

/-- The exact uniform finite-range theorem needed by the marked induction. -/
def MpcGeneralMarkedFiniteRangeSupply (alpha h : ℕ) : Prop :=
  ∀ k (hk : 3 ≤ k) m (hm : m ∈ mpcGeneralMarkedStage alpha h k),
    mpcGeneralLevelTarget hm.1 ∈ (mpcGeneralMarkedLevelShiftHom m k hk).range

/-- Marked finite-range supply gives marked-stage successors. -/
theorem mpcGeneralMarkedStageSuccessor_of_finiteRange {alpha h : ℕ}
    (halpha : 2 ≤ alpha) (H : MpcGeneralMarkedFiniteRangeSupply alpha h) :
    MpcGeneralMarkedStageSuccessorSupply alpha h := by
  intro k hk hstage
  obtain ⟨m, hm⟩ := hstage
  obtain ⟨E⟩ := (nonempty_mpcGeneralMarkedCorrection_iff_target_mem_range
    halpha hm hk).mpr (H k hk m hm)
  exact ⟨mpcGeneralModify m E.factors,
    mpcGeneralMarkedStage_succ_of_correction hm E hk⟩

/-- One parameterized marked range theorem proves the pivot shift in all degrees and ranks. -/
theorem mpcPivShiftH_of_generalMarkedFiniteRange {alpha h : ℕ}
    (halpha : 2 ≤ alpha) (H : MpcGeneralMarkedFiniteRangeSupply alpha h) :
    MpcPivShiftH alpha h :=
  mpcPivShiftH_of_generalMarkedStageSuccessor (by omega)
    (mpcGeneralMarkedStageSuccessor_of_finiteRange halpha H)

end

end GQ2.Dyadic.Instances.MpcGeneralMarkedSpan

section AxiomPins

open GQ2.Dyadic.Instances.MpcGeneralMarkedSpan

#print axioms mpcGeneralMarkedCorrectionSource
#print axioms mpcGeneralMarkedCorrectionImage
#print axioms MpcGeneralMarkedLevelCorrection
#print axioms mpcGeneralMarkedLevelShiftHom
#print axioms nonempty_mpcGeneralMarkedCorrection_iff_target_mem_range
#print axioms MpcGeneralMarkedFiniteRangeSupply
#print axioms mpcGeneralMarkedStageSuccessor_of_finiteRange
#print axioms mpcPivShiftH_of_generalMarkedFiniteRange

end AxiomPins

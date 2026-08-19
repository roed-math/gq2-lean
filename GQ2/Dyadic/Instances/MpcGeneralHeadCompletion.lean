/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.MpcGeneralHeadReflection

/-!
# Uniform head completion is one `C`-slot absorption theorem

After general head reflection, the head-marked and fully marked sources differ only in the
distinguished `C` slot.  This module splits every head-marked correction into its already
fully marked off-`C` part and a one-coordinate `C` correction.  Therefore head completion is
equivalent to absorption of those one-coordinate shifts into the full marked range.

This is a parameterized statement for all degrees, handle counts, stages, and current
markings.  It is the precise all-degree replacement for any class-by-class calculation.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralHeadCompletion

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralFiniteStages
open GQ2.Dyadic.Instances.MpcGeneralFiniteSpan
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcGeneralMarkedStages
open GQ2.Dyadic.Instances.MpcGeneralMarkedSpan
open GQ2.Dyadic.Instances.MpcGeneralHeadSpan
open GQ2.Dyadic.Instances.MpcGeneralHeadReflection
open GQ2.Roe.Labute

/-- Away from `C`, the head-marked and fully marked finite images coincide. -/
theorem mpcGeneralMarkedCorrectionImage_eq_head_of_ne
    {alpha h j n : ℕ} {i : Fin (coreRank h)} (hi : i ≠ 2) :
    mpcGeneralMarkedCorrectionImage alpha h j n i =
      mpcGeneralHeadCorrectionImage alpha h j n i := by
  ext x
  constructor
  · intro hx
    obtain ⟨e, hdepth, hchi, -, hdelta, hlevel⟩ :=
      (mem_mpcGeneralMarkedCorrectionImage_iff_exists x).mp hx
    exact (mem_mpcGeneralHeadCorrectionImage_iff_exists x).mpr
      ⟨e, hdepth, hchi, hdelta, hlevel⟩
  · intro hx
    obtain ⟨e, hdepth, hchi, hdelta, hlevel⟩ :=
      (mem_mpcGeneralHeadCorrectionImage_iff_exists x).mp hx
    exact (mem_mpcGeneralMarkedCorrectionImage_iff_exists x).mpr
      ⟨e, hdepth, hchi, fun htwo => (hi htwo).elim, hdelta, hlevel⟩

/-- Delete the `C` coordinate of a head-marked correction.  The result is fully marked. -/
def mpcGeneralHeadWithoutC {alpha h k : ℕ}
    (E : MpcGeneralHeadLevelCorrection alpha h k) :
    MpcGeneralMarkedLevelCorrection alpha h k := fun i => by
  classical
  by_cases hi : i = 2
  · exact ⟨1, Subgroup.one_mem _⟩
  · exact ⟨(E i).1, by
      rw [mpcGeneralMarkedCorrectionImage_eq_head_of_ne hi]
      exact (E i).2⟩

/-- Keep only the `C` coordinate of a head-marked correction. -/
def mpcGeneralHeadOnlyC {alpha h k : ℕ}
    (E : MpcGeneralHeadLevelCorrection alpha h k) :
    MpcGeneralHeadLevelCorrection alpha h k := fun i => by
  classical
  by_cases hi : i = 2
  · subst hi
    exact E 2
  · exact ⟨1, Subgroup.one_mem _⟩

/-- The off-`C` part followed by the `C`-only part is the original correction. -/
theorem mpcGeneralHead_split_C {alpha h k : ℕ}
    (E : MpcGeneralHeadLevelCorrection alpha h k) :
    mpcGeneralMarkedLevelToHead (mpcGeneralHeadWithoutC E) *
      mpcGeneralHeadOnlyC E = E := by
  classical
  funext i
  apply Subtype.ext
  by_cases hi : i = 2
  · subst hi
    simp [mpcGeneralHeadWithoutC, mpcGeneralHeadOnlyC,
      mpcGeneralMarkedLevelToHead]
  · simp [mpcGeneralHeadWithoutC, mpcGeneralHeadOnlyC,
      mpcGeneralMarkedLevelToHead, hi]

/-- Uniform `C` absorption: every one-coordinate head `C` shift is in the fully marked
range. -/
def MpcGeneralCAbsorptionSupply (alpha h : ℕ) : Prop :=
  ∀ k (hk : 3 ≤ k) (m : Fin (coreRank h) → (DM alpha h : Type))
    (E : MpcGeneralHeadLevelCorrection alpha h k),
    mpcGeneralHeadLevelShiftHom m k hk (mpcGeneralHeadOnlyC E) ∈
      (mpcGeneralMarkedLevelShiftHom m k hk).range

/-- `C` absorption implies full head completion. -/
theorem mpcGeneralHeadCompletionSupply_of_CAbsorption
    {alpha h : ℕ} (H : MpcGeneralCAbsorptionSupply alpha h) :
    MpcGeneralHeadCompletionSupply alpha h := by
  intro k hk m _ htarget
  obtain ⟨E, rfl⟩ := htarget
  obtain ⟨Q, hQ⟩ := H k hk m E
  refine ⟨mpcGeneralHeadWithoutC E * Q, ?_⟩
  rw [map_mul, ← mpcGeneralMarkedLevelToHead_shift]
  change mpcGeneralHeadLevelShiftHom m k hk
      (mpcGeneralMarkedLevelToHead (mpcGeneralHeadWithoutC E)) *
        mpcGeneralMarkedLevelShiftHom m k hk Q = _
  rw [hQ, ← map_mul, mpcGeneralHead_split_C]

/-- Conversely, head completion absorbs every `C`-only correction. -/
theorem mpcGeneralCAbsorptionSupply_of_headCompletion
    {alpha h : ℕ} (H : MpcGeneralHeadCompletionSupply alpha h) :
    MpcGeneralCAbsorptionSupply alpha h := by
  intro k hk m E
  apply H k hk m
  exact ⟨mpcGeneralHeadOnlyC E, rfl⟩

/-- Head completion is exactly the one-slot `C` absorption theorem. -/
theorem mpcGeneralHeadCompletionSupply_iff_CAbsorption {alpha h : ℕ} :
    MpcGeneralHeadCompletionSupply alpha h ↔
      MpcGeneralCAbsorptionSupply alpha h :=
  ⟨mpcGeneralCAbsorptionSupply_of_headCompletion,
    mpcGeneralHeadCompletionSupply_of_CAbsorption⟩

/-- The uniform `C` absorption theorem alone proves the general pivot shift. -/
theorem mpcPivShiftH_of_generalCAbsorption
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (H : MpcGeneralCAbsorptionSupply alpha h) :
    MpcPivShiftH alpha h :=
  mpcPivShiftH_of_generalHeadCompletion halpha
    (mpcGeneralHeadCompletionSupply_of_CAbsorption H)

end

end GQ2.Dyadic.Instances.MpcGeneralHeadCompletion

section AxiomPins

open GQ2.Dyadic.Instances.MpcGeneralHeadCompletion

#print axioms mpcGeneralMarkedCorrectionImage_eq_head_of_ne
#print axioms mpcGeneralHeadWithoutC
#print axioms mpcGeneralHeadOnlyC
#print axioms mpcGeneralHead_split_C
#print axioms mpcGeneralHeadCompletionSupply_of_CAbsorption
#print axioms mpcGeneralCAbsorptionSupply_of_headCompletion
#print axioms mpcGeneralHeadCompletionSupply_iff_CAbsorption
#print axioms mpcPivShiftH_of_generalCAbsorption

end AxiomPins

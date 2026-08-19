/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.MpcGeneralDerivedBoundary

/-!
# The uniform marked-stage invariant

The general finite-stage induction must retain one secondary invariant: the head has trivial
additive `D` coordinate.  This is the parameterized form of the invariant used by the
completed compact proof.  It is defined for every `alpha` and handle count.

The invariant is closed, holds for the universal bare seed, makes the current relator defect
`D`-neutral, and is preserved by a correction whose head factor is `D`-neutral.  Consequently
the general pivot shift follows from successors only on this marked state space; no successor
claim for arbitrary finite stages is required.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralMarkedStages

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcGeneralFiniteStages
open GQ2.Roe.Labute

/-- The additive `D` coordinate of the canonical general M-frame. -/
def mpcGeneralDeltaD (alpha h : ℕ) :
    ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]) :=
  (mDHom alpha h).comp (mAbMkHom alpha h)

@[simp] theorem mpcGeneralDeltaD_dmA (alpha h : ℕ) :
    mpcGeneralDeltaD alpha h (dmA alpha h) = 1 := by
  change mDHom alpha h (GQ2.SectionThree.abMk (dmGen alpha h 0)) = 1
  rw [mDHom, mCoordHom_gen, coreMark_zero]

@[simp] theorem mpcGeneralDeltaD_dmB (alpha h : ℕ) :
    mpcGeneralDeltaD alpha h (dmB alpha h) = 1 := by
  change mDHom alpha h (GQ2.SectionThree.abMk (dmGen alpha h 1)) = 1
  rw [mDHom, mCoordHom_gen, coreMark_one]

@[simp] theorem mpcGeneralDeltaD_dmC (alpha h : ℕ) :
    mpcGeneralDeltaD alpha h (dmC alpha h) = 1 := by
  change mDHom alpha h (GQ2.SectionThree.abMk (dmGen alpha h 2)) = 1
  rw [mDHom, mCoordHom_gen, coreMark_two]

@[simp] theorem mpcGeneralDeltaD_dmD (alpha h : ℕ) :
    mpcGeneralDeltaD alpha h (dmD alpha h) = ofAdd (1 : ℤ_[2]) := by
  change mDHom alpha h (GQ2.SectionThree.abMk (dmGen alpha h 3)) =
    ofAdd (1 : ℤ_[2])
  rw [mDHom, mCoordHom_gen, coreMark_three]

/-- General stages retaining the secondary head invariant. -/
def mpcGeneralMarkedStage (alpha h k : ℕ) :
    Set (Fin (coreRank h) → (DM alpha h : Type)) :=
  {m | m ∈ mpcGeneralStage alpha h k ∧ mpcGeneralDeltaD alpha h (m 0) = 1}

theorem mpcGeneralMarkedStage_antitone {alpha h k k' : ℕ} (hkk : k' ≤ k) :
    mpcGeneralMarkedStage alpha h k ⊆ mpcGeneralMarkedStage alpha h k' := by
  rintro m ⟨hm, hhead⟩
  exact ⟨mpcGeneralStage_antitone hkk hm, hhead⟩

theorem mpcGeneralMarkedStage_isClosed (alpha h k : ℕ) :
    IsClosed (mpcGeneralMarkedStage alpha h k) := by
  exact (mpcGeneralStage_isClosed alpha h k).inter
    (isClosed_eq
      ((mpcGeneralDeltaD alpha h).continuous_toFun.comp (continuous_apply 0))
      continuous_const)

/-- The universal bare seed retains the marked-head invariant. -/
theorem mpcGeneralMarkedStage_three_nonempty {alpha h : ℕ} (halpha : 1 ≤ alpha) :
    (mpcGeneralMarkedStage alpha h 3).Nonempty := by
  refine ⟨mpcBareShiftMark alpha h,
    ⟨mpcBareShiftMark_indep alpha h, mpcBareShiftMark_chi alpha h,
      mpcBareShiftMark_row alpha h, mpcBareShiftMark_rel_three halpha⟩, ?_⟩
  rw [mpcBareShiftMark_of_ne (show (0 : Fin (coreRank h)) ≠ 2 by
    intro H
    have := congrArg Fin.val H
    rw [coreVal_zero, coreVal_two] at this
    omega)]
  exact mpcGeneralDeltaD_dmA alpha h

/-- The universal `C + 2B` row forces the current `C` letter to have zero `D` coordinate. -/
theorem mpcGeneralStage_C_deltaD_eq_one {alpha h k : ℕ}
    {m : Fin (coreRank h) → (DM alpha h : Type)}
    (hm : m ∈ mpcGeneralStage alpha h k) :
    mpcGeneralDeltaD alpha h (m 2) = 1 := by
  have H := hm.2.2.1 (mpcGeneralDeltaD alpha h)
  apply Multiplicative.toAdd.injective
  simpa only [mpcGeneralDeltaD_dmC, mpcGeneralDeltaD_dmB, toAdd_one,
    mul_zero, add_zero] using H

/-- A marked general stage has a `D`-neutral relator defect. -/
theorem mpcGeneralMarkedStage_rel_deltaD_eq_one {alpha h k : ℕ}
    {m : Fin (coreRank h) → (DM alpha h : Type)}
    (hm : m ∈ mpcGeneralMarkedStage alpha h k) :
    mpcGeneralDeltaD alpha h (mRelWord alpha m) = 1 := by
  rw [map_mRelWord, mRelWord_comm, hm.2, mpcGeneralStage_C_deltaD_eq_one hm.1]
  simp

/-- A constrained correction which also preserves the secondary head invariant. -/
structure MpcGeneralMarkedStageCorrection {alpha h : ℕ}
    (m : Fin (coreRank h) → (DM alpha h : Type)) (k : ℕ)
    extends MpcGeneralStageCorrection m k where
  headDelta : mpcGeneralDeltaD alpha h (factors 0) = 1

/-- A marked correction advances a marked stage. -/
theorem mpcGeneralMarkedStage_succ_of_correction {alpha h k : ℕ}
    {m : Fin (coreRank h) → (DM alpha h : Type)}
    (hm : m ∈ mpcGeneralMarkedStage alpha h k)
    (E : MpcGeneralMarkedStageCorrection m k) (hk : 3 ≤ k) :
    mpcGeneralModify m E.factors ∈ mpcGeneralMarkedStage alpha h (k + 1) := by
  refine ⟨mpcGeneralStage_succ_of_correction hm.1 E.toMpcGeneralStageCorrection hk, ?_⟩
  rw [mpcGeneralModify, map_mul, hm.2, E.headDelta, one_mul]

/-- The honest uniform induction hypothesis: only marked finite stages need successors. -/
def MpcGeneralMarkedStageSuccessorSupply (alpha h : ℕ) : Prop :=
  ∀ k, 3 ≤ k → (mpcGeneralMarkedStage alpha h k).Nonempty →
    (mpcGeneralMarkedStage alpha h (k + 1)).Nonempty

/-- Marked successors produce marked stages at every finite depth. -/
theorem mpcGeneralMarkedStage_nonempty_all {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (H : MpcGeneralMarkedStageSuccessorSupply alpha h) :
    ∀ k, (mpcGeneralMarkedStage alpha h k).Nonempty := by
  intro k
  by_cases hk : k ≤ 3
  · exact (mpcGeneralMarkedStage_three_nonempty halpha).mono
      (mpcGeneralMarkedStage_antitone hk)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ k by omega)
    clear hk
    induction d with
    | zero => simpa using mpcGeneralMarkedStage_three_nonempty halpha
    | succ d ih => simpa [Nat.add_assoc] using H (3 + d) (by omega) ih

/-- A uniform marked-stage successor theorem proves the general pivot shift. -/
theorem mpcPivShiftH_of_generalMarkedStageSuccessor {alpha h : ℕ}
    (halpha : 1 ≤ alpha) (H : MpcGeneralMarkedStageSuccessorSupply alpha h) :
    MpcPivShiftH alpha h := by
  apply mpcPivShiftH_of_finiteStages
  intro k
  obtain ⟨m, hm⟩ := mpcGeneralMarkedStage_nonempty_all halpha H k
  exact ⟨m, hm.1⟩

end

end GQ2.Dyadic.Instances.MpcGeneralMarkedStages

section AxiomPins

open GQ2.Dyadic.Instances.MpcGeneralMarkedStages

#print axioms mpcGeneralDeltaD
#print axioms mpcGeneralMarkedStage
#print axioms mpcGeneralMarkedStage_isClosed
#print axioms mpcGeneralMarkedStage_three_nonempty
#print axioms mpcGeneralStage_C_deltaD_eq_one
#print axioms mpcGeneralMarkedStage_rel_deltaD_eq_one
#print axioms MpcGeneralMarkedStageCorrection
#print axioms mpcGeneralMarkedStage_succ_of_correction
#print axioms MpcGeneralMarkedStageSuccessorSupply
#print axioms mpcGeneralMarkedStage_nonempty_all
#print axioms mpcPivShiftH_of_generalMarkedStageSuccessor

end AxiomPins

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcGeneralHandleShiftRecipe

/-!
# Standard-handle stabilization of the Mpc odd shear

The canonical cross-h map kills every handle and retains the four core generators:

`dmForgetHandles alpha h : DM alpha h -> DM alpha 0`.

It is surjective and the orientation factors through it.  This is, however, the wrong direction
for stabilizing `MpcMk.mpcMk_pivShift`.  A map in the reverse direction which sends the four
rank-four generators to the standard core letters cannot exist by the presentation universal
property: the rank-four core word is trivial, while at positive handle count that same core word
is the inverse of the nontrivial handle block.

The exact missing input is therefore `MpcStandardHandleExtension`.  It asks for four lifts of a
compact shift witness whose core word equals the standard general-h core word, so adjoining the
unchanged handle generators kills the full relator.  It also records the two other properties
not supplied by mere lifts through the handle-forgetting quotient: topological generation and
the universal `C + 2 B` row.  Chi preservation follows automatically from handle-forgetting.

`mpcPivShiftH_of_standardHandleExtension` turns that datum into the full general-h shift via the
presentation recipe.  Thus the unconditional compact theorem reduces `MpcPivShiftH 2 h` to the
single standard-stabilization statement `MpcPivShiftStandardStabilization 2 h`.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcPiv
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcGeneralHandleShiftRecipe

/-- Kill all handles and retain the four core generators.  This is the canonical map available
between the stabilized and rank-four presentations; it goes from general h to h=0. -/
noncomputable def dmForgetHandles (alpha h : ℕ) :
    ContinuousMonoidHom (DM alpha h : Type) (DM alpha 0 : Type) :=
  mLiftHom alpha h (isProP_DM alpha 0)
    (coreMark (h := h) (dmA alpha 0) (dmB alpha 0) (dmC alpha 0) (dmD alpha 0)) (by
      rw [mRelWord_coreMark]
      have hr := dm_relation alpha 0
      rw [mRelWord, handleWord_zero, mul_one] at hr
      exact hr)

@[simp] theorem dmForgetHandles_dmA (alpha h : ℕ) :
    dmForgetHandles alpha h (dmA alpha h) = dmA alpha 0 := by
  change dmForgetHandles alpha h (dmGen alpha h 0) = dmA alpha 0
  rw [dmForgetHandles, mLiftHom_gen, coreMark_zero]

@[simp] theorem dmForgetHandles_dmB (alpha h : ℕ) :
    dmForgetHandles alpha h (dmB alpha h) = dmB alpha 0 := by
  change dmForgetHandles alpha h (dmGen alpha h 1) = dmB alpha 0
  rw [dmForgetHandles, mLiftHom_gen, coreMark_one]

@[simp] theorem dmForgetHandles_dmC (alpha h : ℕ) :
    dmForgetHandles alpha h (dmC alpha h) = dmC alpha 0 := by
  change dmForgetHandles alpha h (dmGen alpha h 2) = dmC alpha 0
  rw [dmForgetHandles, mLiftHom_gen, coreMark_two]

@[simp] theorem dmForgetHandles_dmD (alpha h : ℕ) :
    dmForgetHandles alpha h (dmD alpha h) = dmD alpha 0 := by
  change dmForgetHandles alpha h (dmGen alpha h 3) = dmD alpha 0
  rw [dmForgetHandles, mLiftHom_gen, coreMark_three]

@[simp] theorem dmForgetHandles_handleU (alpha h : ℕ) (j : Fin h) :
    dmForgetHandles alpha h (dmGen alpha h (handleIdxU j)) = 1 := by
  rw [dmForgetHandles, mLiftHom_gen, coreMark_handleU]

@[simp] theorem dmForgetHandles_handleV (alpha h : ℕ) (j : Fin h) :
    dmForgetHandles alpha h (dmGen alpha h (handleIdxV j)) = 1 := by
  rw [dmForgetHandles, mLiftHom_gen, coreMark_handleV]

/-- The orientation factors through handle-forgetting. -/
theorem chiM_dmForgetHandles (alpha h : ℕ) (x : DM alpha h) :
    chiM alpha 0 (dmForgetHandles alpha h x) = chiM alpha h x := by
  have heq : (chiM alpha 0).comp (dmForgetHandles alpha h) = chiM alpha h := by
    apply dm_hom_ext
    intro i
    rcases nCoreIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · change chiM alpha 0 (dmForgetHandles alpha h (dmA alpha h)) = chiM alpha h (dmA alpha h)
      rw [dmForgetHandles_dmA, chiM_dmA, chiM_dmA]
    · change chiM alpha 0 (dmForgetHandles alpha h (dmB alpha h)) = chiM alpha h (dmB alpha h)
      rw [dmForgetHandles_dmB, chiM_dmB, chiM_dmB]
    · change chiM alpha 0 (dmForgetHandles alpha h (dmC alpha h)) = chiM alpha h (dmC alpha h)
      rw [dmForgetHandles_dmC, chiM_dmC, chiM_dmC]
    · change chiM alpha 0 (dmForgetHandles alpha h (dmD alpha h)) = chiM alpha h (dmD alpha h)
      rw [dmForgetHandles_dmD, chiM_dmD, chiM_dmD]
    · change chiM alpha 0 (dmForgetHandles alpha h (dmGen alpha h (handleIdxU j))) = _
      rw [dmForgetHandles_handleU, map_one, chiM_handleU]
    · change chiM alpha 0 (dmForgetHandles alpha h (dmGen alpha h (handleIdxV j))) = _
      rw [dmForgetHandles_handleV, map_one, chiM_handleV]
  exact DFunLike.congr_fun heq x

/-- Handle-forgetting is onto; the unavailable direction is a section. -/
theorem dmForgetHandles_surjective (alpha h : ℕ) :
    Function.Surjective (dmForgetHandles alpha h) := by
  let q := dmForgetHandles alpha h
  have hclosed : IsClosed ((q.toMonoidHom.range : Subgroup (DM alpha 0 : Type)) :
      Set (DM alpha 0 : Type)) := by
    rw [MonoidHom.coe_range q.toMonoidHom]
    exact (isCompact_range q.continuous_toFun).isClosed
  have hsub : Subgroup.closure (Set.range (dmGen alpha 0)) ≤ q.toMonoidHom.range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨dmA alpha h, dmForgetHandles_dmA alpha h⟩
    · exact ⟨dmB alpha h, dmForgetHandles_dmB alpha h⟩
    · exact ⟨dmC alpha h, dmForgetHandles_dmC alpha h⟩
    · exact ⟨dmD alpha h, dmForgetHandles_dmD alpha h⟩
  have hle := Subgroup.topologicalClosure_minimal _ hsub hclosed
  rw [dm_topGen, top_le_iff] at hle
  intro y
  have : y ∈ q.toMonoidHom.range := by rw [hle]; trivial
  exact this

/-- The marking obtained by changing only the four core letters and adjoining the standard
handles. -/
def standardHandleMark {alpha h : ℕ} (a b c d : DM alpha h) :
    Fin (coreRank h) → DM alpha h :=
  fullMark a b c d
    (fun j => dmGen alpha h (handleIdxU j))
    (fun j => dmGen alpha h (handleIdxV j))

@[simp] theorem standardHandleMark_zero {alpha h : ℕ} (a b c d : DM alpha h) :
    standardHandleMark a b c d 0 = a := fullMark_zero _ _ _ _ _ _

@[simp] theorem standardHandleMark_one {alpha h : ℕ} (a b c d : DM alpha h) :
    standardHandleMark a b c d 1 = b := fullMark_one _ _ _ _ _ _

@[simp] theorem standardHandleMark_two {alpha h : ℕ} (a b c d : DM alpha h) :
    standardHandleMark a b c d 2 = c := fullMark_two _ _ _ _ _ _

@[simp] theorem standardHandleMark_three {alpha h : ℕ} (a b c d : DM alpha h) :
    standardHandleMark a b c d 3 = d := fullMark_three _ _ _ _ _ _

@[simp] theorem standardHandleMark_handleU {alpha h : ℕ} (a b c d : DM alpha h)
    (j : Fin h) :
    standardHandleMark a b c d (handleIdxU j) = dmGen alpha h (handleIdxU j) :=
  fullMark_handleU _ _ _ _ _ _ _

@[simp] theorem standardHandleMark_handleV {alpha h : ℕ} (a b c d : DM alpha h)
    (j : Fin h) :
    standardHandleMark a b c d (handleIdxV j) = dmGen alpha h (handleIdxV j) :=
  fullMark_handleV _ _ _ _ _ _ _

theorem mRelWord_standardHandleMark {alpha h : ℕ} (a b c d : DM alpha h) :
    mRelWord alpha (standardHandleMark a b c d) =
      mWord alpha a b c d *
        handleWord (fun j => dmGen alpha h (handleIdxU j))
          (fun j => dmGen alpha h (handleIdxV j)) := by
  rw [mRelWord, standardHandleMark_zero, standardHandleMark_one,
    standardHandleMark_two, standardHandleMark_three]
  congr 1
  simp_rw [standardHandleMark_handleU, standardHandleMark_handleV]

/-- The exact missing standard-handle extension of one compact shift witness. -/
def MpcStandardHandleExtension {alpha h : ℕ}
    (Psi0 : ContinuousMulEquiv (DM alpha 0 : Type) (DM alpha 0 : Type)) : Prop :=
  ∃ a b c d : (DM alpha h : Type),
    dmForgetHandles alpha h a = Psi0 (dmA alpha 0) ∧
    dmForgetHandles alpha h b = Psi0 (dmB alpha 0) ∧
    dmForgetHandles alpha h c = Psi0 (dmC alpha 0) ∧
    dmForgetHandles alpha h d = Psi0 (dmD alpha 0) ∧
    mWord alpha a b c d =
      mWord alpha (dmA alpha h) (dmB alpha h) (dmC alpha h) (dmD alpha h) ∧
    (Subgroup.closure (Set.range (standardHandleMark a b c d))).topologicalClosure = ⊤ ∧
    ∀ f : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]),
      toAdd (f c) = toAdd (f (dmC alpha h)) + 2 * toAdd (f (dmB alpha h))

/-- A compact witness with a standard-handle extension produces the actual general-h shift. -/
theorem mpcPivShiftH_of_standardHandleExtension {alpha h : ℕ}
    (Psi0 : ContinuousMulEquiv (DM alpha 0 : Type) (DM alpha 0 : Type))
    (hchi0 : ∀ x, chiM alpha 0 (Psi0 x) = chiM alpha 0 x)
    (hext : MpcStandardHandleExtension (h := h) Psi0) :
    MpcPivShiftH alpha h := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hcore, hgen, hrow⟩ := hext
  apply mpcPivShiftH_of_marking (standardHandleMark a b c d)
  · rw [mRelWord_standardHandleMark, hcore]
    exact dm_relation alpha h
  · exact hgen
  · intro i
    rcases nCoreIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · change chiM alpha h a = chiM alpha h (dmA alpha h)
      rw [← chiM_dmForgetHandles, ha, hchi0, chiM_dmA, chiM_dmA]
    · rw [standardHandleMark_one, show dmGen alpha h 1 = dmB alpha h from rfl]
      rw [← chiM_dmForgetHandles, hb, hchi0, chiM_dmB, chiM_dmB]
    · rw [standardHandleMark_two, show dmGen alpha h 2 = dmC alpha h from rfl]
      rw [← chiM_dmForgetHandles, hc, hchi0, chiM_dmC, chiM_dmC]
    · rw [standardHandleMark_three, show dmGen alpha h 3 = dmD alpha h from rfl]
      rw [← chiM_dmForgetHandles, hd, hchi0, chiM_dmD, chiM_dmD]
    · rw [standardHandleMark_handleU]
    · rw [standardHandleMark_handleV]
  · intro f
    rw [standardHandleMark_two]
    exact hrow f

/-- The smallest missing stabilization statement: every compact odd shear admits a lift whose
core relator is unchanged and whose adjoined handles are the standard ones. -/
def MpcPivShiftStandardStabilization (alpha h : ℕ) : Prop :=
  ∀ Psi0 : ContinuousMulEquiv (DM alpha 0 : Type) (DM alpha 0 : Type),
    (∀ x, chiM alpha 0 (Psi0 x) = chiM alpha 0 x) →
    (∀ f : ContinuousMonoidHom (DM alpha 0 : Type) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC alpha 0))) =
        toAdd (f (dmC alpha 0)) + 2 * toAdd (f (dmB alpha 0))) →
    MpcStandardHandleExtension (h := h) Psi0

/-- A compact shift plus the standard-handle stabilization theorem gives a general-h shift. -/
theorem mpcPivShiftH_of_standardStabilization {alpha h : ℕ}
    (hcompact : MpcPivShift alpha)
    (hstab : MpcPivShiftStandardStabilization alpha h) :
    MpcPivShiftH alpha h := by
  obtain ⟨Psi0, hchi0, hrow0⟩ := hcompact
  exact mpcPivShiftH_of_standardHandleExtension Psi0 hchi0 (hstab Psi0 hchi0 hrow0)

/-- For alpha two, only the standard-handle stabilization theorem remains. -/
theorem mpcPivShiftH_two_of_standardStabilization {h : ℕ}
    (hstab : MpcPivShiftStandardStabilization 2 h) :
    MpcPivShiftH 2 h :=
  mpcPivShiftH_of_standardStabilization MpcMk.mpcMk_pivShift hstab

#print axioms dmForgetHandles
#print axioms chiM_dmForgetHandles
#print axioms dmForgetHandles_surjective
#print axioms standardHandleMark
#print axioms mRelWord_standardHandleMark
#print axioms MpcStandardHandleExtension
#print axioms mpcPivShiftH_of_standardHandleExtension
#print axioms MpcPivShiftStandardStabilization
#print axioms mpcPivShiftH_of_standardStabilization
#print axioms mpcPivShiftH_two_of_standardStabilization

end
end GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization

/-!
# The nonabelian defect behind one-handle Mpc stabilization

For a lifted compact marking `(a,b,c,d)` at positive handle count, write

`w = mWord alpha a b c d`.

Changing only the `D`-letter from `d` to `z*d` changes the core word by the exact right factor

`conjP (commP c z) d`.

Thus a kernel element `z` absorbs the defect precisely when that factor is

`w⁻¹ * mWord alpha A B C D`.

`MpcStandardDDefectAbsorption` records this single nonabelian equation together with the lift,
generation, and universal `C + 2B` row conditions that are genuinely independent of it.
`mpcStandardHandleExtension_of_DDefectAbsorption` turns the datum into the standard extension
from `MpcGeneralHandleStandardStabilization`.

At one handle the canonical core word is exactly `[U₀,V₀]⁻¹`, so
`MpcOneHandleDDefectAbsorption` displays the first missing equation with no hidden relator
notation.  The compact M6 theorem then reduces `MpcPivShiftH 2 1` to that predicate.

This is not an abelian coordinate issue.  `mRelWord_mulEquiv_eq_one_iff` proves that applying
any same-group automorphism uniformly to a marking preserves whether its full relator defect is
trivial.  Consequently the existing same-h handle, Eichler, tau, and scaling automorphisms
cannot turn a nontrivial lifted defect into a relation; a new kernel commutator solution is the
missing input.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralHandleDefectAbsorption

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcPiv
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization

/-- A left correction of the `D`-letter contributes one explicit conjugated commutator to the
right of the core word. -/
theorem mWord_mul_left_D {G : Type*} [Group G] (alpha : ℕ) (a b c d z : G) :
    mWord alpha a b c (z * d) =
      mWord alpha a b c d * conjP (commP c z) d := by
  simp only [mWord, commP, conjP, mul_inv_rev]
  group

/-- A single handle block is its single standard commutator. -/
theorem handleWord_one {G : Type*} [Group G] (u v : Fin 1 → G) :
    handleWord u v = commP (u 0) (v 0) := by
  rw [handleWord, show List.finRange 1 = [(0 : Fin 1)] by decide]
  simp

/-- In the presented group the canonical core word is the inverse standard handle block. -/
theorem dmCoreWord_eq_handleWord_inv (alpha h : ℕ) :
    mWord alpha (dmA alpha h) (dmB alpha h) (dmC alpha h) (dmD alpha h) =
      (handleWord (fun j => dmGen alpha h (handleIdxU j))
        (fun j => dmGen alpha h (handleIdxV j)))⁻¹ := by
  have hrel := dm_relation alpha h
  change mWord alpha (dmA alpha h) (dmB alpha h) (dmC alpha h) (dmD alpha h) *
    handleWord (fun j => dmGen alpha h (handleIdxU j))
      (fun j => dmGen alpha h (handleIdxV j)) = 1 at hrel
  have h := congrArg
    (fun x => x * (handleWord (fun j => dmGen alpha h (handleIdxU j))
      (fun j => dmGen alpha h (handleIdxV j)))⁻¹) hrel
  simpa only [mul_assoc, mul_inv_cancel, mul_one, one_mul] using h

/-- At one handle the target core word is the inverse of `[U₀,V₀]`. -/
theorem dmCoreWord_one_eq_commP_inv (alpha : ℕ) :
    mWord alpha (dmA alpha 1) (dmB alpha 1) (dmC alpha 1) (dmD alpha 1) =
      (commP (dmGen alpha 1 (handleIdxU (0 : Fin 1)))
        (dmGen alpha 1 (handleIdxV (0 : Fin 1))))⁻¹ := by
  rw [dmCoreWord_eq_handleWord_inv, handleWord_one]

/-- The exact `D`-slot defect-absorption premise.  Besides four lifts of the compact marking it
asks for a kernel element solving the displayed nonabelian commutator equation.  The remaining
two clauses are precisely the generation and universal row data required by the presentation
recipe. -/
def MpcStandardDDefectAbsorption {alpha h : ℕ}
    (Psi0 : ContinuousMulEquiv (DM alpha 0 : Type) (DM alpha 0 : Type)) : Prop :=
  ∃ a b c d z : (DM alpha h : Type),
    dmForgetHandles alpha h a = Psi0 (dmA alpha 0) ∧
    dmForgetHandles alpha h b = Psi0 (dmB alpha 0) ∧
    dmForgetHandles alpha h c = Psi0 (dmC alpha 0) ∧
    dmForgetHandles alpha h d = Psi0 (dmD alpha 0) ∧
    dmForgetHandles alpha h z = 1 ∧
    conjP (commP c z) d =
      (mWord alpha a b c d)⁻¹ *
        mWord alpha (dmA alpha h) (dmB alpha h) (dmC alpha h) (dmD alpha h) ∧
    (Subgroup.closure (Set.range (standardHandleMark a b c (z * d)))).topologicalClosure = ⊤ ∧
    ∀ f : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]),
      toAdd (f c) = toAdd (f (dmC alpha h)) + 2 * toAdd (f (dmB alpha h))

/-- Solving the `D`-slot defect equation gives the standard-handle extension. -/
theorem mpcStandardHandleExtension_of_DDefectAbsorption {alpha h : ℕ}
    {Psi0 : ContinuousMulEquiv (DM alpha 0 : Type) (DM alpha 0 : Type)}
    (habs : MpcStandardDDefectAbsorption (h := h) Psi0) :
    MpcStandardHandleExtension (h := h) Psi0 := by
  obtain ⟨a, b, c, d, z, ha, hb, hc, hd, hz, hcorr, hgen, hrow⟩ := habs
  refine ⟨a, b, c, z * d, ha, hb, hc, ?_, ?_, hgen, hrow⟩
  · rw [map_mul, hz, one_mul, hd]
  · rw [mWord_mul_left_D, hcorr]
    group

/-- The first nontrivial case, with the target defect written explicitly as the inverse
standard handle commutator. -/
def MpcOneHandleDDefectAbsorption
    (Psi0 : ContinuousMulEquiv (DM 2 0 : Type) (DM 2 0 : Type)) : Prop :=
  ∃ a b c d z : (DM 2 1 : Type),
    dmForgetHandles 2 1 a = Psi0 (dmA 2 0) ∧
    dmForgetHandles 2 1 b = Psi0 (dmB 2 0) ∧
    dmForgetHandles 2 1 c = Psi0 (dmC 2 0) ∧
    dmForgetHandles 2 1 d = Psi0 (dmD 2 0) ∧
    dmForgetHandles 2 1 z = 1 ∧
    conjP (commP c z) d =
      (mWord 2 a b c d)⁻¹ *
        (commP (dmGen 2 1 (handleIdxU (0 : Fin 1)))
          (dmGen 2 1 (handleIdxV (0 : Fin 1))))⁻¹ ∧
    (Subgroup.closure (Set.range (standardHandleMark a b c (z * d)))).topologicalClosure = ⊤ ∧
    ∀ f : ContinuousMonoidHom (DM 2 1 : Type) (Multiplicative ℤ_[2]),
      toAdd (f c) = toAdd (f (dmC 2 1)) + 2 * toAdd (f (dmB 2 1))

/-- The explicit one-handle predicate is the general defect-absorption predicate at `(2,1)`. -/
theorem oneHandleDDefectAbsorption_iff
    (Psi0 : ContinuousMulEquiv (DM 2 0 : Type) (DM 2 0 : Type)) :
    MpcOneHandleDDefectAbsorption Psi0 ↔
      MpcStandardDDefectAbsorption (h := 1) Psi0 := by
  rw [MpcOneHandleDDefectAbsorption, MpcStandardDDefectAbsorption,
    dmCoreWord_one_eq_commP_inv]

/-- A solution of the explicit one-handle equation produces the actual one-handle odd shear. -/
theorem mpcPivShiftH_two_one_of_DDefectAbsorption
    (Psi0 : ContinuousMulEquiv (DM 2 0 : Type) (DM 2 0 : Type))
    (hchi0 : ∀ x, chiM 2 0 (Psi0 x) = chiM 2 0 x)
    (habs : MpcOneHandleDDefectAbsorption Psi0) :
    MpcPivShiftH 2 1 :=
  mpcPivShiftH_of_standardHandleExtension Psi0 hchi0
    (mpcStandardHandleExtension_of_DDefectAbsorption
      ((oneHandleDDefectAbsorption_iff Psi0).mp habs))

/-- The unconditional compact theorem leaves only defect absorption for its selected witness. -/
theorem mpcPivShiftH_two_one_of_compact_DDefectAbsorption
    (H : ∀ Psi0 : ContinuousMulEquiv (DM 2 0 : Type) (DM 2 0 : Type),
      (∀ x, chiM 2 0 (Psi0 x) = chiM 2 0 x) →
      (∀ f : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]),
        toAdd (f (Psi0 (dmC 2 0))) =
          toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0))) →
      MpcOneHandleDDefectAbsorption Psi0) :
    MpcPivShiftH 2 1 := by
  obtain ⟨Psi0, hchi0, hrow0⟩ := MpcMk.mpcMk_pivShift
  exact mpcPivShiftH_two_one_of_DDefectAbsorption Psi0 hchi0 (H Psi0 hchi0 hrow0)

/-- Uniformly applying a same-group automorphism cannot repair a nontrivial full relator
defect.  It sends the defect through an injective map, hence preserves exactly whether it is
one. -/
theorem mRelWord_mulEquiv_eq_one_iff {G : Type*} [Group G] {alpha h : ℕ}
    (Psi : G ≃* G) (m : Fin (coreRank h) → G) :
    mRelWord alpha (fun i => Psi (m i)) = 1 ↔ mRelWord alpha m = 1 := by
  rw [← map_mRelWord Psi]
  constructor
  · intro hzero
    apply Psi.injective
    simpa only [map_one] using hzero
  · intro hzero
    rw [hzero, map_one]

#print axioms mWord_mul_left_D
#print axioms handleWord_one
#print axioms dmCoreWord_eq_handleWord_inv
#print axioms dmCoreWord_one_eq_commP_inv
#print axioms MpcStandardDDefectAbsorption
#print axioms mpcStandardHandleExtension_of_DDefectAbsorption
#print axioms MpcOneHandleDDefectAbsorption
#print axioms oneHandleDDefectAbsorption_iff
#print axioms mpcPivShiftH_two_one_of_DDefectAbsorption
#print axioms mpcPivShiftH_two_one_of_compact_DDefectAbsorption
#print axioms mRelWord_mulEquiv_eq_one_iff

end
end GQ2.Dyadic.Instances.MpcGeneralHandleDefectAbsorption

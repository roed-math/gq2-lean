/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.MpcGeneralTowerAtoms

/-!
# Exact bracket boundary for the uniform Mpc tower families

A correction supported in the distinguished `C` slot contributes exactly the bracket with
the current `D` letter.  Applying this formula to each canonical M-frame tower atom identifies
the sole remaining general theorem as a parameterized bracket-absorption statement.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralTowerBracketBoundary

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralAbelianDecomposition
open GQ2.Dyadic.Instances.MpcGeneralFiniteSpan
open GQ2.Dyadic.Instances.MpcGeneralHeadSpan
open GQ2.Dyadic.Instances.MpcGeneralMarkedSpan
open GQ2.Dyadic.Instances.MpcGeneralTowerAtoms
open GQ2.Dyadic.Instances.MpcGeneralTowerReduction
open GQ2.Roe.Labute

/-- The raw correction underlying a singleton `C` correction is the generic coordinate-two
correction. -/
theorem mpcGeneralHeadSingleC_toRaw {alpha h k : ℕ}
    (x : DM alpha h)
    (hx : x ∈ twoCentralSeries (DM alpha h : Type) (k - 1))
    (hchi : chiM alpha h x = 1) :
    mpcGeneralHeadLevelToRaw (mpcGeneralHeadSingleC x hx hchi) =
      evenRawDepthCoordinateCorrection (G := DM alpha h) (h := h) (k := k) 2
        ⟨levelMk (DM alpha h) (k + 1) x, ⟨x, hx, rfl⟩⟩ := by
  classical
  apply EvenRawDepthCorrection.ext
  funext i
  by_cases hi : i = 2
  · subst hi
    simp [mpcGeneralHeadLevelToRaw, mpcGeneralHeadSingleC,
      evenRawDepthCoordinateCorrection_apply]
  · simp [mpcGeneralHeadLevelToRaw, mpcGeneralHeadSingleC,
      evenRawDepthCoordinateCorrection_apply, hi]

/-- Literal first variation of a singleton `C` correction. -/
theorem mpcGeneralHeadSingleC_shift_apply {alpha h k : ℕ}
    (m : Fin (coreRank h) → (DM alpha h : Type)) (hk : 3 ≤ k)
    (x : DM alpha h)
    (hx : x ∈ twoCentralSeries (DM alpha h : Type) (k - 1))
    (hchi : chiM alpha h x = 1) :
    (mpcGeneralHeadLevelShiftHom m k hk
      (mpcGeneralHeadSingleC x hx hchi)).1 =
      commP (levelMk (DM alpha h) (k + 1) x)
        (levelMk (DM alpha h) (k + 1) (m 3)) := by
  change ((evenRawDepthShiftHom
    (fun i => levelMk (DM alpha h) (k + 1) (m i)) hk)
      (mpcGeneralHeadLevelToRaw (mpcGeneralHeadSingleC x hx hchi))).1 = _
  rw [mpcGeneralHeadSingleC_toRaw]
  exact evenRawDepthShiftHom_two_apply
    (fun i => levelMk (DM alpha h) (k + 1) (m i)) hk
      ⟨levelMk (DM alpha h) (k + 1) x, ⟨x, hx, rfl⟩⟩

/-- The exact general boundary: every canonical `B`, `C`, or handle tower bracket with the
current `D` letter lies in the fully marked shift range.  The `A` and `D` atoms are trivial. -/
def MpcGeneralTowerAtomBracketSupply (alpha h : ℕ) : Prop :=
  ∀ (halpha : 2 ≤ alpha) k (hk : 3 ≤ k)
    (m : Fin (coreRank h) → (DM alpha h : Type))
    (x : DM alpha h) (hx : x ∈ twoCentralSeries (DM alpha h : Type) (k - 1))
    (hchi : chiM alpha h x = 1) (i : Fin (coreRank h)),
    let a := mpcGeneralTowerAtom (by omega : 1 ≤ alpha) x i
    let ha := (mpcGeneralTowerAtom_mem halpha hk hx hchi i).1
    (⟨commP (levelMk (DM alpha h) (k + 1) a)
        (levelMk (DM alpha h) (k + 1) (m 3)),
      commP_mem_zLayer k hk ⟨a, ha, rfl⟩ _⟩ : zLayer (DM alpha h) k) ∈
        (mpcGeneralMarkedLevelShiftHom m k hk).range

/-- Atomic shift absorption is equivalent to the explicit bracket boundary. -/
theorem mpcGeneralTowerAtomAbsorptionSupply_iff_brackets {alpha h : ℕ} :
    MpcGeneralTowerAtomAbsorptionSupply alpha h ↔
      MpcGeneralTowerAtomBracketSupply alpha h := by
  constructor
  · intro H halpha k hk m x hx hchi i
    dsimp only
    have Hi := H halpha k hk m x hx hchi i
    rw [show (⟨commP
          (levelMk (DM alpha h) (k + 1)
            (mpcGeneralTowerAtom (by omega) x i))
          (levelMk (DM alpha h) (k + 1) (m 3)), _⟩ : zLayer (DM alpha h) k) =
        mpcGeneralHeadLevelShiftHom m k hk
          (mpcGeneralHeadSingleCHom alpha h k
            ⟨mpcGeneralTowerAtom (by omega) x i,
              mpcGeneralTowerAtom_mem halpha hk hx hchi i⟩) by
      apply Subtype.ext
      symm
      exact mpcGeneralHeadSingleC_shift_apply m hk _
        (mpcGeneralTowerAtom_mem halpha hk hx hchi i).1
        (MonoidHom.mem_ker.mp
          (mpcGeneralTowerAtom_mem halpha hk hx hchi i).2)]
    exact Hi
  · intro H halpha k hk m x hx hchi i
    have Hi := H halpha k hk m x hx hchi i
    rw [show mpcGeneralHeadLevelShiftHom m k hk
          (mpcGeneralHeadSingleCHom alpha h k
            ⟨mpcGeneralTowerAtom (by omega) x i,
              mpcGeneralTowerAtom_mem halpha hk hx hchi i⟩) =
        (⟨commP
          (levelMk (DM alpha h) (k + 1)
            (mpcGeneralTowerAtom (by omega) x i))
          (levelMk (DM alpha h) (k + 1) (m 3)), _⟩ : zLayer (DM alpha h) k) by
      apply Subtype.ext
      exact mpcGeneralHeadSingleC_shift_apply m hk _
        (mpcGeneralTowerAtom_mem halpha hk hx hchi i).1
        (MonoidHom.mem_ker.mp
          (mpcGeneralTowerAtom_mem halpha hk hx hchi i).2)]
    exact Hi

/-- The explicit uniform bracket theorem proves the general pivot shift. -/
theorem mpcPivShiftH_of_generalTowerBrackets
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (H : MpcGeneralTowerAtomBracketSupply alpha h) :
    MpcGeneralHandlePivotBoundary.MpcPivShiftH alpha h :=
  mpcPivShiftH_of_generalTowerAtoms halpha
    ((mpcGeneralTowerAtomAbsorptionSupply_iff_brackets).mpr H)

end

end GQ2.Dyadic.Instances.MpcGeneralTowerBracketBoundary

section AxiomPins

open GQ2.Dyadic.Instances.MpcGeneralTowerBracketBoundary

#print axioms mpcGeneralHeadSingleC_toRaw
#print axioms mpcGeneralHeadSingleC_shift_apply
#print axioms MpcGeneralTowerAtomBracketSupply
#print axioms mpcGeneralTowerAtomAbsorptionSupply_iff_brackets
#print axioms mpcPivShiftH_of_generalTowerBrackets

end AxiomPins

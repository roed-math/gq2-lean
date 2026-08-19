/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.MpcGeneralTowerParityReduction

/-!
# Uniform induction boundary for the general Mpc tower

After parity reduction, the canonical atom at rung `k + 1` is the square of the atom at
rung `k`.  The generic Hall--Petrescu engine makes its bracket with `D` the graded square
of the preceding bracket.  This file separates the proof into exactly two parameterized
parts:

* one base-layer family in `Q_4`, indexed by the standard generator;
* one uniform square-preservation theorem for the marked shift range.

No nilpotency class appears in either interface.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralTowerInduction

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralMarkedSpan
open GQ2.Dyadic.Instances.MpcGeneralTowerParityReduction
open GQ2.Roe.Labute
open GQ2.Dyadic.SqCore

/-- The canonical atom at the next rung is the square of the current atom. -/
theorem mpcGeneralCanonicalTowerAtom_succ {alpha h k : ℕ}
    (hk : 3 ≤ k) (i : Fin (coreRank h)) :
    mpcGeneralCanonicalTowerAtom alpha h (k + 1) i =
      mpcGeneralCanonicalTowerAtom alpha h k i ^ 2 := by
  unfold mpcGeneralCanonicalTowerAtom
  rw [pow_two, ← zpowZtwo_add]
  congr 1
  have he : k + 1 - 2 = (k - 2) + 1 := by omega
  rw [he, pow_succ]
  ring

/-- The canonical bracket at the next rung is the graded square of the current bracket. -/
theorem mpcGeneralCanonicalTowerBracket_succ {alpha h k : ℕ}
    (hk : 3 ≤ k) (i : Fin (coreRank h)) :
    levelMk (DM alpha h) (k + 2)
        (commP (mpcGeneralCanonicalTowerAtom alpha h (k + 1) i)
          (dmD alpha h)) =
      levelMk (DM alpha h) (k + 2)
        (commP (mpcGeneralCanonicalTowerAtom alpha h k i) (dmD alpha h) ^ 2) := by
  rw [mpcGeneralCanonicalTowerAtom_succ hk i]
  have H := gTower_engine_bracket (G := DM alpha h) (k := k - 1)
    (by omega) (mpcGeneralCanonicalTowerAtom_mem hk i) (dmD alpha h)
  rwa [show k - 1 + 3 = k + 2 by omega] at H

/-- The base-layer canonical family.  This is a single generator-indexed statement in
`Q_4`, not a list of later nilpotency classes. -/
def MpcGeneralCanonicalTowerBracketBase (alpha h : ℕ) : Prop :=
  ∀ i : Fin (coreRank h), mpcGeneralTowerIndexActive i →
    (⟨commP
        (levelMk (DM alpha h) 4
          (mpcGeneralCanonicalTowerAtom alpha h 3 i))
        (levelMk (DM alpha h) 4 (dmD alpha h)),
      commP_mem_zLayer 3 (by omega)
        ⟨mpcGeneralCanonicalTowerAtom alpha h 3 i,
          mpcGeneralCanonicalTowerAtom_mem (by omega) i, rfl⟩ _⟩ :
      zLayer (DM alpha h) 3) ∈
        (mpcGeneralMarkedLevelShiftHom (dmGen alpha h) 3 (by omega)).range

/-- The uniform propagation statement: marked shift range is preserved along the one
canonical tower square. -/
def MpcGeneralCanonicalTowerBracketStep (alpha h : ℕ) : Prop :=
  ∀ k (hk : 3 ≤ k) (i : Fin (coreRank h)), mpcGeneralTowerIndexActive i →
    (⟨commP
        (levelMk (DM alpha h) (k + 1)
          (mpcGeneralCanonicalTowerAtom alpha h k i))
        (levelMk (DM alpha h) (k + 1) (dmD alpha h)),
      commP_mem_zLayer k hk
        ⟨mpcGeneralCanonicalTowerAtom alpha h k i,
          mpcGeneralCanonicalTowerAtom_mem hk i, rfl⟩ _⟩ :
      zLayer (DM alpha h) k) ∈
        (mpcGeneralMarkedLevelShiftHom (dmGen alpha h) k hk).range →
    (⟨commP
        (levelMk (DM alpha h) (k + 2)
          (mpcGeneralCanonicalTowerAtom alpha h (k + 1) i))
        (levelMk (DM alpha h) (k + 2) (dmD alpha h)),
      commP_mem_zLayer (k + 1) (by omega)
        ⟨mpcGeneralCanonicalTowerAtom alpha h (k + 1) i,
          mpcGeneralCanonicalTowerAtom_mem (by omega) i, rfl⟩ _⟩ :
      zLayer (DM alpha h) (k + 1)) ∈
        (mpcGeneralMarkedLevelShiftHom (dmGen alpha h) (k + 1) (by omega)).range

/-- Base absorption and uniform square propagation give every canonical rung. -/
theorem mpcGeneralCanonicalTowerBracketSupply_of_base_of_step
    {alpha h : ℕ} (Hbase : MpcGeneralCanonicalTowerBracketBase alpha h)
    (Hstep : MpcGeneralCanonicalTowerBracketStep alpha h) :
    MpcGeneralCanonicalTowerBracketSupply alpha h := by
  intro k hk i hi
  induction k, hk using Nat.le_induction with
  | base => simpa using Hbase i hi
  | succ k hk ih => exact Hstep k hk i hi ih

/-- The two uniform ingredients prove the general pivot shift. -/
theorem mpcPivShiftH_of_generalTowerBaseAndStep
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (Hbase : MpcGeneralCanonicalTowerBracketBase alpha h)
    (Hstep : MpcGeneralCanonicalTowerBracketStep alpha h) :
    GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary.MpcPivShiftH alpha h :=
  mpcPivShiftH_of_generalCanonicalTowerBrackets halpha
    (mpcGeneralCanonicalTowerBracketSupply_of_base_of_step Hbase Hstep)

end

end GQ2.Dyadic.Instances.MpcGeneralTowerInduction

section AxiomPins

open GQ2.Dyadic.Instances.MpcGeneralTowerInduction

#print axioms mpcGeneralCanonicalTowerAtom_succ
#print axioms mpcGeneralCanonicalTowerBracket_succ
#print axioms MpcGeneralCanonicalTowerBracketBase
#print axioms MpcGeneralCanonicalTowerBracketStep
#print axioms mpcGeneralCanonicalTowerBracketSupply_of_base_of_step
#print axioms mpcPivShiftH_of_generalTowerBaseAndStep

end AxiomPins

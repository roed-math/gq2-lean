/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.MpcGeneralTowerInduction
import GQ2.Dyadic.Instances.StageAbstractionEvenRawSpanStep

/-!
# Square propagation for the general marked Mpc range

The variable-rank identity `evenRawDbarWord_sq` already transports the complete even shift
word, handles included.  Here it is connected to the exact marked correction sources.
Squaring a marked correction preserves every character and row constraint, while raising
its depth by one.  Lift-independence of squares then transports any range witness to the
next canonical tower bracket.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralTowerStep

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralMarkedSpan
open GQ2.Dyadic.Instances.MpcGeneralMarkedStages
open GQ2.Dyadic.Instances.MpcGeneralTowerInduction
open GQ2.Dyadic.Instances.MpcGeneralTowerParityReduction
open GQ2.Roe.Labute

/-- A chosen group representative of one marked finite correction coordinate. -/
noncomputable def mpcGeneralMarkedLevelLift {alpha h k : ℕ}
    (E : MpcGeneralMarkedLevelCorrection alpha h k)
    (i : Fin (coreRank h)) : DM alpha h :=
  Classical.choose
    ((mem_mpcGeneralMarkedCorrectionImage_iff_exists (E i).1).mp (E i).2)

theorem mpcGeneralMarkedLevelLift_spec {alpha h k : ℕ}
    (E : MpcGeneralMarkedLevelCorrection alpha h k)
    (i : Fin (coreRank h)) :
    mpcGeneralMarkedLevelLift E i ∈
        twoCentralSeries (DM alpha h : Type) (k - 1) ∧
      chiM alpha h (mpcGeneralMarkedLevelLift E i) = 1 ∧
      (i = 2 → ∀ f : ContinuousMonoidHom
        (DM alpha h : Type) (Multiplicative ℤ_[2]),
          f (mpcGeneralMarkedLevelLift E i) = 1) ∧
      (i = 0 → mpcGeneralDeltaD alpha h (mpcGeneralMarkedLevelLift E i) = 1) ∧
      levelMk (DM alpha h) (k + 1) (mpcGeneralMarkedLevelLift E i) = (E i).1 :=
  Classical.choose_spec
    ((mem_mpcGeneralMarkedCorrectionImage_iff_exists (E i).1).mp (E i).2)

/-- Squaring every chosen representative gives a marked correction at the next rung. -/
noncomputable def mpcGeneralMarkedLevelSquare {alpha h k : ℕ}
    (hk : 3 ≤ k) (E : MpcGeneralMarkedLevelCorrection alpha h k) :
    MpcGeneralMarkedLevelCorrection alpha h (k + 1) := fun i =>
  ⟨levelMk (DM alpha h) (k + 2) (mpcGeneralMarkedLevelLift E i ^ 2),
    (mem_mpcGeneralMarkedCorrectionImage_iff_exists _).mpr
      ⟨mpcGeneralMarkedLevelLift E i ^ 2,
        by
          have H := (mpcGeneralMarkedLevelLift_spec E i).1
          have Hsq := sq_mem_twoCentralSeries_succ (DM alpha h : Type) H
          rwa [show k - 1 + 1 = (k + 1) - 1 by omega] at Hsq,
        by rw [map_pow, (mpcGeneralMarkedLevelLift_spec E i).2.1, one_pow],
        fun hi f => by
          rw [map_pow, (mpcGeneralMarkedLevelLift_spec E i).2.2.1 hi f, one_pow],
        fun hi => by
          rw [map_pow, (mpcGeneralMarkedLevelLift_spec E i).2.2.2.1 hi, one_pow],
        rfl⟩⟩

/-- The squared correction has the expected underlying quotient coordinate. -/
theorem mpcGeneralMarkedLevelSquare_apply {alpha h k : ℕ}
    (hk : 3 ≤ k) (E : MpcGeneralMarkedLevelCorrection alpha h k)
    (i : Fin (coreRank h)) :
    (mpcGeneralMarkedLevelSquare hk E i).1 =
      levelMk (DM alpha h) (k + 2) (mpcGeneralMarkedLevelLift E i) ^ 2 := by
  change levelMk (DM alpha h) (k + 2) (mpcGeneralMarkedLevelLift E i ^ 2) = _
  exact map_pow (levelMk (DM alpha h) (k + 2)) _ 2

/-- The marked range is preserved by the canonical tower square, uniformly in degree,
rank, and rung. -/
theorem mpcGeneralCanonicalTowerBracketStep (alpha h : ℕ) :
    MpcGeneralCanonicalTowerBracketStep alpha h := by
  intro k hk i _hi Hprev
  obtain ⟨E, hE⟩ := Hprev
  let corr : Fin (coreRank h) → levelQuot (DM alpha h) (k + 2) :=
    fun j => levelMk (DM alpha h) (k + 2) (mpcGeneralMarkedLevelLift E j)
  let base : Fin (coreRank h) → levelQuot (DM alpha h) (k + 2) :=
    fun j => levelMk (DM alpha h) (k + 2) (dmGen alpha h j)
  let W := evenRawDbarWord base corr
  let T := commP
    (levelMk (DM alpha h) (k + 2)
      (mpcGeneralCanonicalTowerAtom alpha h k i))
    (levelMk (DM alpha h) (k + 2) (dmD alpha h))
  have hcorrDepth : ∀ j, corr j ∈
      lambdaImage (DM alpha h) (k - 1) (k + 2) := fun j =>
    ⟨mpcGeneralMarkedLevelLift E j,
      (mpcGeneralMarkedLevelLift_spec E j).1, rfl⟩
  have hprojW : levelProj (DM alpha h) (k + 1) W =
      (mpcGeneralMarkedLevelShiftHom (dmGen alpha h) k hk E).1 := by
    change levelProj (DM alpha h) (k + 1)
        (evenRawDbarWord base corr) =
      evenRawDbarWord
        (fun j => levelMk (DM alpha h) (k + 1) (dmGen alpha h j))
        (mpcGeneralMarkedLevelToRaw E).correction
    rw [levelProj_evenRawDbarWord]
    congr 1
    funext j
    change levelMk (DM alpha h) (k + 1) (mpcGeneralMarkedLevelLift E j) =
      (E j).1
    exact (mpcGeneralMarkedLevelLift_spec E j).2.2.2.2
  have hprojT : levelProj (DM alpha h) (k + 1) T =
      commP
        (levelMk (DM alpha h) (k + 1)
          (mpcGeneralCanonicalTowerAtom alpha h k i))
        (levelMk (DM alpha h) (k + 1) (dmD alpha h)) := by
    rfl
  have hprevVal := congrArg Subtype.val hE
  have hsame : levelProj (DM alpha h) (k + 1) W =
      levelProj (DM alpha h) (k + 1) T := by
    rw [hprojW, hprojT, hprevVal]
  obtain ⟨z, hz, hW⟩ := exists_zLayer_mul hsame
  have hsqWT : W ^ 2 = T ^ 2 := by
    rw [hW, (zLayer_commute hz T).eq, sq_mul_zLayer (k + 1) hz]
  let E2 := mpcGeneralMarkedLevelSquare hk E
  refine ⟨E2, ?_⟩
  apply Subtype.ext
  change evenRawDbarWord base
      (fun j => (mpcGeneralMarkedLevelSquare hk E j).1) =
    commP
      (levelMk (DM alpha h) (k + 2)
        (mpcGeneralCanonicalTowerAtom alpha h (k + 1) i))
      (levelMk (DM alpha h) (k + 2) (dmD alpha h))
  have hsqShift := evenRawDbarWord_sq h (k + 1) (by omega)
    base corr hcorrDepth
  have hnext : evenRawDbarWord base
      (fun j => (mpcGeneralMarkedLevelSquare hk E j).1) = W ^ 2 := by
    rw [show (fun j => (mpcGeneralMarkedLevelSquare hk E j).1) =
        fun j => corr j ^ 2 by
      funext j
      exact mpcGeneralMarkedLevelSquare_apply hk E j]
    exact hsqShift.symm
  rw [hnext, hsqWT]
  exact (mpcGeneralCanonicalTowerBracket_succ hk i).symm

/-- The general Mpc tower now reduces solely to the uniform base-layer family. -/
theorem mpcPivShiftH_of_generalTowerBase {alpha h : ℕ}
    (halpha : 2 ≤ alpha)
    (Hbase : MpcGeneralCanonicalTowerBracketBase alpha h) :
    GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary.MpcPivShiftH alpha h :=
  mpcPivShiftH_of_generalTowerBaseAndStep halpha Hbase
    (mpcGeneralCanonicalTowerBracketStep alpha h)

end

end GQ2.Dyadic.Instances.MpcGeneralTowerStep

section AxiomPins

open GQ2.Dyadic.Instances.MpcGeneralTowerStep

#print axioms mpcGeneralMarkedLevelLift
#print axioms mpcGeneralMarkedLevelLift_spec
#print axioms mpcGeneralMarkedLevelSquare
#print axioms mpcGeneralMarkedLevelSquare_apply
#print axioms mpcGeneralCanonicalTowerBracketStep
#print axioms mpcPivShiftH_of_generalTowerBase

end AxiomPins

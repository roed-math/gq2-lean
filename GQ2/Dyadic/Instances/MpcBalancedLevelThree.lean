/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedBase
import GQ2.Dyadic.Instances.StageAbstractionEvenTransgression
import GQ2.Dyadic.Instances.EvenModelCupForm

/-!
# The balanced one-handle level-three cup boundary

W200 makes the balanced construction automatic through `λ₂`.  This module identifies the
first informative obstruction in `λ₂/λ₃` with the intrinsic even cup form.  A corrected
marking that preserves `evenCupForm` kills its full `M₂` relator modulo `λ₃` by the generic
level-three transgression theorem.  The balanced defect is exactly a conjugate of that full
relator, so it lies in `λ₃` as well.

Consequently a cup-adapted W199 seed inhabits `oneHandleBalancedSet Psi0 3`.  No existence of
such a cup-adapted seed is asserted here: constructing one is the next finite linear problem.
In particular, this module does not revive either false fixed-`C` bracket-surjectivity premise.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedLevelThree

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative ContCoh
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.EvenModel
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.StageGeneric.evenTransgression
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcGeneralHandleDefectAbsorption
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Roe.Labute

/-- The displayed even Gram in rank six. -/
def oneHandleEvenGram
    (κ : Fin (coreRank 1) → Fin (coreRank 1) → ZMod 2) : ZMod 2 :=
  κ 0 0 + (κ 0 1 + κ 1 0) + (κ 2 3 + κ 3 2) +
    ∑ j, (κ (handleIdxU j) (handleIdxV j) +
      κ (handleIdxV j) (handleIdxU j))

theorem oneHandleEvenGram_isEven : IsEvenGram oneHandleEvenGram := fun _ => rfl

theorem oneHandleEvenGram_rankOne
    (v w : Fin (coreRank 1) → ZMod 2) :
    oneHandleEvenGram (fun i j => v i * w j) = evenCupForm v w := rfl

/-- A marking is cup-adapted when pulling characters back along it preserves the intrinsic
even cup form. -/
def OneHandleCupAdapted (m : Fin (coreRank 1) → DM 2 1) : Prop :=
  ∀ c d : ContinuousMonoidHom (DM 2 1) (Multiplicative (ZMod 2)),
    evenCupForm (fun i => toAdd (c (m i))) (fun i => toAdd (d (m i))) =
      evenCupForm (fun i => toAdd (c (dmGen 2 1 i)))
        (fun i => toAdd (d (dmGen 2 1 i)))

/-- A W199 balanced seed whose corrected marking also preserves the intrinsic degree-two
cup form. -/
def OneHandleCupAdaptedSeed
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) : Prop :=
  ∃ p : OneHandleBalancedPoint,
    dmForgetHandles 2 1 (balancedA p) = Psi0 (dmA 2 0) ∧
    dmForgetHandles 2 1 (balancedB p) = Psi0 (dmB 2 0) ∧
    dmForgetHandles 2 1 (balancedC p) = Psi0 (dmC 2 0) ∧
    dmForgetHandles 2 1 (balancedD p) = Psi0 (dmD 2 0) ∧
    dmForgetHandles 2 1 (balancedZ p) = 1 ∧
    OneHandleModTwoIndep (balancedCorrectedMark p) ∧
    (∀ f : ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]),
      toAdd (f (balancedC p)) =
        toAdd (f (dmC 2 1)) + 2 * toAdd (f (dmB 2 1))) ∧
    OneHandleCupAdapted (balancedCorrectedMark p)

/-- A cup-adapted rank-six marking kills the full `M₂` relator modulo `λ₃`. -/
theorem mRelWord_mem_three_of_cupAdapted
    (m : Fin (coreRank 1) → DM 2 1) (hm : OneHandleCupAdapted m) :
    mRelWord 2 m ∈ twoCentralSeries (DM 2 1) 3 := by
  letI : DistribMulAction (DM 2 1) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul (DM 2 1) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  rw [lim_mem_twoCentralSeries_iff_levelMk]
  change (mStageWord 2 1 (by omega)).word
    (fun i => levelMk (DM 2 1) 3 (m i)) = 1
  apply levelThreeRelation_of_supplies (mStageWord 2 1 (by omega)) (DM 2 1)
    (dm_topologicallyFinGen 2 1) (isProP_DM 2 1) m
  · exact mRelWord_mem_twoCentralSeries_two (DM 2 1) (by omega) m
  · intro H _ m0 ζ hcentral hsquare
    exact mRelWord_mul_central (by omega) m0 ζ hcentral hsquare
  · intro c hc m0
    exact oneHandleEvenGram_isEven.mRelWord_fib hc (by omega) m0
  · intro c hc φ hbase
    apply gram_vanishes_aux (DM 2 1) (dm_topologicallyFinGen 2 1)
      (isProP_DM 2 1) oneHandleEvenGram_isEven.zero
      oneHandleEvenGram_isEven.add m c hc φ hbase (dmObs 2 1 (by omega))
    intro cG dG
    calc
      (dmObs 2 1 (by omega))
          (trivialCupPairing 2 (DM 2 1) (fun _ _ => rfl)
            (H1mk (DM 2 1) (ZMod 2) (Count.homEquivZ1 cG))
            (H1mk (DM 2 1) (ZMod 2) (Count.homEquivZ1 dG))) =
          evenCupForm (fun i => toAdd (cG (dmGen 2 1 i)))
            (fun i => toAdd (dG (dmGen 2 1 i))) := by
              simpa [evenModelCharacterClass] using
                dmFrattiniCupForm 2 1 (by omega) (by omega) cG dG
      _ = evenCupForm (fun i => toAdd (cG (m i)))
            (fun i => toAdd (dG (m i))) := (hm cG dG).symm
      _ = oneHandleEvenGram
            (fun i j => toAdd (cG (m i)) * toAdd (dG (m j))) :=
          (oneHandleEvenGram_rankOne _ _).symm

/-- The balanced defect is a conjugate of the corrected marking's full relator. -/
theorem oneHandleDDefect_eq_conj_relWord (p : OneHandleBalancedPoint) :
    oneHandleDDefect (balancedA p) (balancedB p) (balancedC p)
        (balancedD p) (balancedZ p) =
      (mWord 2 (balancedA p) (balancedB p) (balancedC p) (balancedD p))⁻¹ *
        mRelWord 2 (balancedCorrectedMark p) *
        mWord 2 (balancedA p) (balancedB p) (balancedC p) (balancedD p) := by
  rw [oneHandleDDefect, balancedCorrectedMark,
    mRelWord_standardHandleMark, handleWord_one,
    mWord_mul_left_D]
  group

theorem oneHandleDDefect_mem_three_of_cupAdapted
    (p : OneHandleBalancedPoint)
    (hp : OneHandleCupAdapted (balancedCorrectedMark p)) :
    oneHandleDDefect (balancedA p) (balancedB p) (balancedC p)
        (balancedD p) (balancedZ p) ∈ twoCentralSeries (DM 2 1) 3 := by
  rw [oneHandleDDefect_eq_conj_relWord]
  simpa only [inv_inv] using
    (twoCentralSeries_normal (DM 2 1) 3).conj_mem
      (mRelWord 2 (balancedCorrectedMark p))
      (mRelWord_mem_three_of_cupAdapted (balancedCorrectedMark p) hp)
      (mWord 2 (balancedA p) (balancedB p) (balancedC p) (balancedD p))⁻¹

/-- Cup adaptation is exactly the extra finite datum needed to upgrade a W199 seed through
the first informative balanced stage. -/
theorem oneHandleBalancedSet_three_nonempty_of_cupAdaptedSeed
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (H : OneHandleCupAdaptedSeed Psi0) :
    (oneHandleBalancedSet Psi0 3).Nonempty := by
  obtain ⟨p, ha, hb, hc, hd, hz, hind, hrow, hcup⟩ := H
  exact ⟨p, ha, hb, hc, hd, hz, hind, hrow,
    oneHandleDDefect_mem_three_of_cupAdapted p hcup⟩

#print axioms oneHandleEvenGram_isEven
#print axioms oneHandleEvenGram_rankOne
#print axioms OneHandleCupAdaptedSeed
#print axioms mRelWord_mem_three_of_cupAdapted
#print axioms oneHandleDDefect_eq_conj_relWord
#print axioms oneHandleDDefect_mem_three_of_cupAdapted
#print axioms oneHandleBalancedSet_three_nonempty_of_cupAdaptedSeed

end
end GQ2.Dyadic.Instances.MpcBalancedLevelThree

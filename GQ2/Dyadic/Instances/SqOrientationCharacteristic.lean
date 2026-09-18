import GQ2.Dyadic.OrientationMasterTransport
import GQ2.Dyadic.SqCore.GradedDeltaFunctionals

/-!
# The square-core orientation is characteristic in every rank

The full crossed-derivation masters already available for `DSq` and the generic transport
lemma recover the three unique Roe orientation values and all trivial handle values after
every automorphism. This closes the full orientation, not only the mod-two sign character.
-/

namespace GQ2.Dyadic.Instances.SqOrientationCharacteristic

open GQ2 GQ2.Roe GQ2.Roe.Labute FoxH Multiplicative
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.SqCore
open GQ2.Dyadic.OrientationMasterTransport
open GQ2.Dyadic.Instances.MOrientationCharacteristic

noncomputable section

attribute [local instance 2000] gDeltaTop gDeltaTopGroup gDeltaCompact gDeltaT2 gDeltaTotDisc

/-- The existing continuous square-core master family. -/
def sqDerivationBasis (h : ℕ) :
    DerivationBasis (sqGen h) (chiSq h).toMonoidHom where
  lift c := (gDeltaHom h c).toMonoidHom
  gen_u := gDelta_gen
  base := gDeltaHom_g
  continuous_u := gDelta_continuous

/-- Every continuous square-core automorphism preserves the full canonical orientation. -/
theorem sqCoreOrientationCharacteristic_all {h : ℕ}
    (e : ContinuousMulEquiv (DSq h : Type) (DSq h : Type)) (x : DSq h) :
    chiSq h (e x) = chiSq h x := by
  let χ := pullbackCharacter (chiSq h) e
  have hfull : ∀ b : Fin (sqRank h) → ℤ_[2],
      sqRelWord (fun i =>
        (⟨b i, χ (sqGen h i)⟩ : WordLift ℤ_[2] ℤ_[2]ˣ)) = 1 := by
    intro b
    obtain ⟨H, _, hH⟩ := (sqDerivationBasis h).exists_lift_of_aut (dsq_topGen h) e b
    have hword : sqRelWord (fun i => H (sqGen h i)) = 1 := by
      rw [← map_sqRelWord, dsq_relation, map_one]
    have hfun : (fun i => H (sqGen h i)) = fun i =>
        (⟨b i, χ (sqGen h i)⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) := by
      funext i
      rw [hH i]
      rfl
    rw [hfun] at hword
    exact hword
  have hdatum : IsLabuteOrientationDatum (χ (sqGen h 0)) (χ (sqGen h 1))
      (χ (sqGen h 2)) := by
    intro a b c
    let offset : Fin (sqRank h) → ℤ_[2] :=
      fun i => (sqMark (ofAdd a) (ofAdd b) (ofAdd c) i).toAdd
    have H := hfull offset
    simp only [sqRelWord, offset, sqMark_zero, sqMark_one, sqMark_two,
      sqMark_handleU, sqMark_handleV, toAdd_one, toAdd_ofAdd,
      handleWord_wordLift_formula, mul_zero, add_zero, Finset.sum_const_zero] at H
    change drWord _ _ _ * 1 = 1 at H
    simpa only [mul_one] using H
  have hhandles : ∀ b : Fin (sqRank h) → ℤ_[2],
      handleWord (fun j => (⟨b (sqHandleIdxU j), χ (sqGen h (sqHandleIdxU j))⟩ :
          WordLift ℤ_[2] ℤ_[2]ˣ))
        (fun j => ⟨b (sqHandleIdxV j), χ (sqGen h (sqHandleIdxV j))⟩) = 1 := by
    intro b
    have H := hfull b
    rw [sqRelWord, sqWord_eq_drWord, hdatum (b 0) (b 1) (b 2), one_mul] at H
    exact H
  obtain ⟨hU, hV⟩ := handle_characters_one_of_lift_relations
    sqHandleIdxU sqHandleIdxV sqHandleIdxU_injective sqHandleIdxV_injective
    sqHandleIdxU_ne_sqHandleIdxV (fun i => χ (sqGen h i)) hhandles
  obtain ⟨hσ, hx0, hx1⟩ := isLabuteOrientationDatum_unique
    (fun a b ha hb => Units.ext ((rootX_unique ha).trans (rootX_unique hb).symm))
    hdatum gDelta_datum
  exact chiSq_matching χ hσ hx0 hx1 hU hV x

#print axioms sqDerivationBasis
#print axioms sqCoreOrientationCharacteristic_all

end

end GQ2.Dyadic.Instances.SqOrientationCharacteristic

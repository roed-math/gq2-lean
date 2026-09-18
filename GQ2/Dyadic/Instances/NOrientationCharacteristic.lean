import GQ2.Dyadic.OrientationMasterTransport
import GQ2.Dyadic.SqCore.GradedDeltaFunctionals

/-!
# The N orientation is characteristic in every rank

The already-proved full N master family is transported by the group-independent master-matrix
theorem. Setting handle offsets to zero recognizes the four core values; then the independent
handle rows force every handle character to be trivial. This is uniform in alpha and rank.
-/

namespace GQ2.Dyadic.Instances.NOrientationCharacteristic

open GQ2 GQ2.SectionThree FoxH Multiplicative
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.SqCore
open GQ2.Dyadic.OrientationMasterTransport
open GQ2.Dyadic.Instances.MOrientationCharacteristic

noncomputable section

attribute [local instance 2000] gDeltaTop gDeltaTopGroup gDeltaCompact gDeltaT2 gDeltaTotDisc

/-- The existing N masters, with their continuity and generator coordinates bundled. -/
def nDerivationBasis {alpha h : ℕ} (halpha : 1 ≤ alpha) :
    DerivationBasis (dnGen alpha h) (chiN alpha h).toMonoidHom where
  lift c := (nLiftHom alpha h gDelta_isProP (nMasterMark alpha c)
    (nRelWord_nMasterMark halpha c)).toMonoidHom
  gen_u c i := by
    change (nLiftHom alpha h gDelta_isProP (nMasterMark alpha c)
      (nRelWord_nMasterMark halpha c) (dnGen alpha h i)).u = c i
    rw [nLiftHom_gen]
    rfl
  base c x := by
    let H := nLiftHom alpha h gDelta_isProP (nMasterMark alpha c)
      (nRelWord_nMasterMark halpha c)
    have heq : gDeltaBase.comp H = chiN alpha h := by
      apply dn_hom_ext
      intro i
      change (H (dnGen alpha h i)).g = chiN alpha h (dnGen alpha h i)
      rw [show H (dnGen alpha h i) = nMasterMark alpha c i from nLiftHom_gen ..]
      rw [chiN, nLiftHom_gen]
      rfl
    exact DFunLike.congr_fun heq x
  continuous_u c := gDelta_continuous_u.comp
    (nLiftHom alpha h gDelta_isProP (nMasterMark alpha c)
      (nRelWord_nMasterMark halpha c)).continuous_toFun

/-- Every automorphism preserves the canonical N cyclotomic orientation. -/
theorem nCoreOrientationCharacteristic_all {alpha h : ℕ} (halpha : 1 ≤ alpha)
    (e : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type)) (x : DN alpha h) :
    chiN alpha h (e x) = chiN alpha h x := by
  let χ := pullbackCharacter (chiN alpha h) e
  have hfull : ∀ b : Fin (coreRank h) → ℤ_[2],
      nRelWord alpha (fun i =>
        (⟨b i, χ (dnGen alpha h i)⟩ : WordLift ℤ_[2] ℤ_[2]ˣ)) = 1 := by
    intro b
    obtain ⟨H, _, hH⟩ := (nDerivationBasis (h := h) halpha).exists_lift_of_aut
      (dn_topGen alpha h) e b
    have hword : nRelWord alpha (fun i => H (dnGen alpha h i)) = 1 := by
      rw [← map_nRelWord, dn_relation, map_one]
    have hfun : (fun i => H (dnGen alpha h i)) = fun i =>
        (⟨b i, χ (dnGen alpha h i)⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) := by
      funext i
      rw [hH i]
      rfl
    rw [hfun] at hword
    exact hword
  have hdatum : IsLabuteOrientationDatumN alpha (χ (dnGen alpha h 0)) (χ (dnGen alpha h 1))
      (χ (dnGen alpha h 2)) (χ (dnGen alpha h 3)) := by
    intro a b c d
    let offset : Fin (coreRank h) → ℤ_[2] :=
      fun i => (coreMark (ofAdd a) (ofAdd b) (ofAdd c) (ofAdd d) i).toAdd
    have H := hfull offset
    simp only [nRelWord, offset, coreMark_zero, coreMark_one, coreMark_two, coreMark_three,
      coreMark_handleU, coreMark_handleV, toAdd_one, toAdd_ofAdd,
      handleWord_wordLift_formula, mul_zero, add_zero, Finset.sum_const_zero] at H
    change nWord alpha _ _ _ _ * 1 = 1 at H
    simpa only [mul_one] using H
  have hhandles : ∀ b : Fin (coreRank h) → ℤ_[2],
      handleWord (fun j => (⟨b (handleIdxU j), χ (dnGen alpha h (handleIdxU j))⟩ :
          WordLift ℤ_[2] ℤ_[2]ˣ))
        (fun j => ⟨b (handleIdxV j), χ (dnGen alpha h (handleIdxV j))⟩) = 1 := by
    intro b
    have H := hfull b
    rw [nRelWord, hdatum (b 0) (b 1) (b 2) (b 3), one_mul] at H
    exact H
  obtain ⟨hU, hV⟩ := handle_characters_one_of_lift_relations
    handleIdxU handleIdxV handleIdxU_injective handleIdxV_injective
    handleIdxU_ne_handleIdxV (fun i => χ (dnGen alpha h i)) hhandles
  exact chiN_matching halpha χ hdatum hU hV x

#print axioms nDerivationBasis
#print axioms nCoreOrientationCharacteristic_all

end

end GQ2.Dyadic.Instances.NOrientationCharacteristic

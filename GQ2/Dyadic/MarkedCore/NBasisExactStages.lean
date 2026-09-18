import GQ2.Dyadic.MarkedCore.NBasisRelativeRefinement
import GQ2.Dyadic.MarkedCore.NPlaneGeneralScaling

/-!
# Arbitrarily deep N stages preserving any initial free-coordinate matrix

Starting from a genuine orientation-compatible free basis with the required
ordinary relator row and an actual depth-three defect, the proved ambient
image theorem and arbitrary-basis relative refinement construct every deeper
stage. Every exact coordinate column of the initial basis is retained.

There is no supplied stage-image theorem or diagonal-matrix restriction.
Existence of the initial basis and its depth-three comparison are explicit
premises, not consequences of this iteration theorem. No compatible choice
of the separately quantified stage witnesses is asserted or needed here.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative Roe.Labute

/-- Exact coordinate equality determines every continuous ordinary character,
without assuming an abelianization isomorphism. -/
theorem freeTwo_character_eq_of_coordinate_values (N : ℕ)
    (x y : FreeTwoRank N)
    (hxy : ∀ j, toAdd (freeTwoCoordinate N j x) = toAdd (freeTwoCoordinate N j y))
    (f : ContinuousMonoidHom (FreeTwoRank N : Type) (Multiplicative ℤ_[2])) :
    f x = f y := by
  apply toAdd.injective
  rw [freeTwo_character_coordinates, freeTwo_character_coordinates]
  simp only [hxy]

private theorem nBasis_relator_row_transport {alpha h : ℕ}
    (e e0 : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (hcoords : ∀ j v,
      toAdd (freeTwoCoordinate (coreRank h) j (e (freeTwoRankGen (coreRank h) v))) =
        toAdd (freeTwoCoordinate (coreRank h) j (e0 (freeTwoRankGen (coreRank h) v))))
    (target : FreeTwoRank (coreRank h))
    (hrow0 : ∀ f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
        (Multiplicative ℤ_[2]),
      f (nRelWord alpha (fun i => e0 (freeTwoRankGen (coreRank h) i))) = f target)
    (f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) (Multiplicative ℤ_[2])) :
    f (nRelWord alpha (fun i => e (freeTwoRankGen (coreRank h) i))) = f target := by
  have hhead := freeTwo_character_eq_of_coordinate_values (coreRank h)
    (e (freeTwoRankGen (coreRank h) 0)) (e0 (freeTwoRankGen (coreRank h) 0))
    (fun j => hcoords j 0) f
  calc
    f (nRelWord alpha (fun i => e (freeTwoRankGen (coreRank h) i))) =
        f (nRelWord alpha (fun i => e0 (freeTwoRankGen (coreRank h) i))) := by
      apply toAdd.injective
      rw [nRelWord_ordinary_row, nRelWord_ordinary_row, hhead]
    _ = f target := hrow0 f

/-- Every depth has an actual free-basis stage with exactly the initial
coordinate matrix. The ambient correction supply is the proved general
theorem; the only initial-stage hypotheses are displayed explicitly. -/
theorem exists_nBasis_exact_stage {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (e0 : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (hchi0 : ∀ i, freeNOrientation alpha h (e0 (freeTwoRankGen (coreRank h) i)) =
      freeNOrientation alpha h (freeTwoRankGen (coreRank h) i))
    (hrow0 : ∀ f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
        (Multiplicative ℤ_[2]),
      f (nRelWord alpha (fun i => e0 (freeTwoRankGen (coreRank h) i))) =
        f (nRelWord alpha (freeTwoRankGen (coreRank h))))
    (herror0 : nRelWord alpha (fun i => e0 (freeTwoRankGen (coreRank h) i)) *
      (nRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) 3)
    (n : ℕ) :
    ∃ e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
        (FreeTwoRank (coreRank h) : Type),
      (∀ i, freeNOrientation alpha h (e (freeTwoRankGen (coreRank h) i)) =
        freeNOrientation alpha h (freeTwoRankGen (coreRank h) i)) ∧
      (∀ j v,
        toAdd (freeTwoCoordinate (coreRank h) j (e (freeTwoRankGen (coreRank h) v))) =
          toAdd (freeTwoCoordinate (coreRank h) j (e0 (freeTwoRankGen (coreRank h) v)))) ∧
      nRelWord alpha (fun i => e (freeTwoRankGen (coreRank h) i)) *
        (nRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
          twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+3) := by
  induction n with
  | zero => exact ⟨e0, hchi0, fun _ _ => rfl, herror0⟩
  | succ n ih =>
    obtain ⟨e, hechi, hecoords, heerror⟩ := ih
    obtain ⟨t, ht, hterror⟩ := nAmbientStageSupply halpha n e hechi heerror
    obtain ⟨s, hs, hschi, hsrow, hserror⟩ := exists_nBasis_full_relative_correction halpha n e t
      (nRelWord alpha (freeTwoRankGen (coreRank h)))
      (nBasis_relator_row_transport e e0 hecoords _ hrow0) ht hterror
    obtain ⟨e', he'⟩ := exists_freeTwoBasisCorrection (coreRank h) e s
      (fun i => twoCentralSeries_antitone (G := (FreeTwoRank (coreRank h) : Type))
        (by omega : 2 ≤ n+2) (hs i))
    refine ⟨e', ?_, ?_, ?_⟩
    · intro i
      rw [he', map_mul, hschi, mul_one, hechi]
    · intro j v
      rw [he', map_mul, hsrow, mul_one]
      exact hecoords j v
    · have htuple : (fun i => e' (freeTwoRankGen (coreRank h) i)) =
          (fun i => e (freeTwoRankGen (coreRank h) i)) * s := funext he'
      rw [htuple, show n+1+3=n+4 by omega]
      exact hserror

#print axioms freeTwo_character_eq_of_coordinate_values
#print axioms exists_nBasis_exact_stage

end
end GQ2.Dyadic.MarkedCore

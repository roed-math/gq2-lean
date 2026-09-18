import GQ2.Dyadic.MarkedCore.FreeProTwoCommutatorShear
import GQ2.Roe.Labute.TwoCentralTower

/-!
# Actual free bases survive corrections in lambda two

A right correction in the second lower two-central subgroup is invisible
in every index-two quotient. The corrected free endomorphism is therefore
surjective by the pro-two Frattini criterion, and is an automorphism by
profinite Hopficity. No ordinary-row or relator condition is assumed.
-/

namespace GQ2.Dyadic.MarkedCore

open Roe.Labute
open scoped commutatorElement

/-- Every open normal subgroup of index two contains lambda two. -/
theorem twoCentralSeries_two_le_indexTwo {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (M : OpenNormalSubgroup G)
    (hM : M.toSubgroup.index = 2) : twoCentralSeries G 2 ≤ M.toSubgroup := by
  letI : Finite (G ⧸ M.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have hc : Nat.card (G ⧸ M.toSubgroup) = 2 := by rwa [← Subgroup.index_eq_card]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsCyclic (G ⧸ M.toSubgroup) := isCyclic_of_prime_card hc
  letI : CommGroup (G ⧸ M.toSubgroup) := IsCyclic.commGroup
  rw [twoCentralSeries_succ G (by omega : 1 ≤ 1), twoCentralSeries_one, twoCentralSucc]
  refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) M.toOpenSubgroup.isClosed
  · rw [Subgroup.closure_le]
    rintro _ ⟨x, _, rfl⟩
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' M.toSubgroup (x ^ 2) = 1
    rw [map_pow, ← hc]
    exact pow_card_eq_one'
  · rw [Subgroup.commutator_le]
    intro x _ y _
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' M.toSubgroup ⁅x, y⁆ = 1
    rw [map_commutatorElement]
    simp [commutatorElement_def, mul_comm]

noncomputable section

def freeTwoBasisCorrectionHom (n : ℕ)
    (e : ContinuousMulEquiv (FreeTwoRank n : Type) (FreeTwoRank n : Type))
    (t : Fin n → FreeTwoRank n) :
    ContinuousMonoidHom (FreeTwoRank n : Type) (FreeTwoRank n : Type) :=
  presLiftHom 1 (isProP_presPro2 1)
    (fun i => e (freeTwoRankGen n i) * t i) (map_one _)

theorem freeTwoBasisCorrectionHom_gen (n : ℕ)
    (e : ContinuousMulEquiv (FreeTwoRank n : Type) (FreeTwoRank n : Type))
    (t : Fin n → FreeTwoRank n) (i : Fin n) :
    freeTwoBasisCorrectionHom n e t (freeTwoRankGen n i) =
      e (freeTwoRankGen n i) * t i := presLiftHom_gen _ _ _ _ _

theorem freeTwoBasisCorrectionHom_surjective (n : ℕ)
    (e : ContinuousMulEquiv (FreeTwoRank n : Type) (FreeTwoRank n : Type))
    (t : Fin n → FreeTwoRank n)
    (ht : ∀ i, t i ∈ twoCentralSeries (FreeTwoRank n : Type) 2) :
    Function.Surjective (freeTwoBasisCorrectionHom n e t) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine surjective_of_forall_index_p_quotient_surjective (isProP_presPro2 1) _ ?_
  intro M hM
  let q : ContinuousMonoidHom (FreeTwoRank n : Type)
      ((FreeTwoRank n : Type) ⧸ M.toSubgroup) :=
    ⟨QuotientGroup.mk' M.toSubgroup, continuous_quot_mk⟩
  have hqt (i : Fin n) : q (t i) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (twoCentralSeries_two_le_indexTwo M hM (ht i))
  have he : q.comp (freeTwoBasisCorrectionHom n e t) = q.comp (autHom e) := by
    apply presPro2_hom_ext
    intro i
    change q (freeTwoBasisCorrectionHom n e t (freeTwoRankGen n i)) = q (e (freeTwoRankGen n i))
    rw [freeTwoBasisCorrectionHom_gen, map_mul, hqt, mul_one]
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M.toSubgroup z
  refine ⟨e.symm x, ?_⟩
  have hh := congrArg (fun f : ContinuousMonoidHom _ _ => f (e.symm x)) he
  change q (freeTwoBasisCorrectionHom n e t (e.symm x)) = q (e (e.symm x)) at hh
  rw [e.apply_symm_apply] at hh
  exact hh

private theorem basisCorrection_topGen (n : ℕ) :
    ∃ s : Finset (FreeTwoRank n : Type),
      (Subgroup.closure (s : Set (FreeTwoRank n : Type))).topologicalClosure = ⊤ := by
  classical
  refine ⟨Finset.univ.image (freeTwoRankGen n), ?_⟩
  have hs : (↑(Finset.univ.image (freeTwoRankGen n)) : Set (FreeTwoRank n : Type)) =
      Set.range (freeTwoRankGen n) := by simp
  rw [hs]
  exact presPro2_topGen _

/-- The corrected marking is a genuine free basis, witnessed by an actual
continuous automorphism of the same free pro-two group. -/
def freeTwoBasisCorrectionEquiv (n : ℕ)
    (e : ContinuousMulEquiv (FreeTwoRank n : Type) (FreeTwoRank n : Type))
    (t : Fin n → FreeTwoRank n)
    (ht : ∀ i, t i ∈ twoCentralSeries (FreeTwoRank n : Type) 2) :
    ContinuousMulEquiv (FreeTwoRank n : Type) (FreeTwoRank n : Type) :=
  continuousMulEquivOfBijective (freeTwoBasisCorrectionHom n e t)
    ⟨profinite_hopfian (basisCorrection_topGen n) _ (freeTwoBasisCorrectionHom_surjective n e t ht),
      freeTwoBasisCorrectionHom_surjective n e t ht⟩

theorem freeTwoBasisCorrectionEquiv_gen (n : ℕ)
    (e : ContinuousMulEquiv (FreeTwoRank n : Type) (FreeTwoRank n : Type))
    (t : Fin n → FreeTwoRank n)
    (ht : ∀ i, t i ∈ twoCentralSeries (FreeTwoRank n : Type) 2) (i : Fin n) :
    freeTwoBasisCorrectionEquiv n e t ht (freeTwoRankGen n i) =
      e (freeTwoRankGen n i) * t i := freeTwoBasisCorrectionHom_gen n e t i

theorem exists_freeTwoBasisCorrection (n : ℕ)
    (e : ContinuousMulEquiv (FreeTwoRank n : Type) (FreeTwoRank n : Type))
    (t : Fin n → FreeTwoRank n)
    (ht : ∀ i, t i ∈ twoCentralSeries (FreeTwoRank n : Type) 2) :
    ∃ e' : ContinuousMulEquiv (FreeTwoRank n : Type) (FreeTwoRank n : Type),
      ∀ i, e' (freeTwoRankGen n i) = e (freeTwoRankGen n i) * t i :=
  ⟨freeTwoBasisCorrectionEquiv n e t ht, freeTwoBasisCorrectionEquiv_gen n e t ht⟩

#print axioms twoCentralSeries_two_le_indexTwo
#print axioms freeTwoBasisCorrectionHom
#print axioms freeTwoBasisCorrectionHom_gen
#print axioms freeTwoBasisCorrectionHom_surjective
#print axioms freeTwoBasisCorrectionEquiv
#print axioms freeTwoBasisCorrectionEquiv_gen
#print axioms exists_freeTwoBasisCorrection

end
end GQ2.Dyadic.MarkedCore

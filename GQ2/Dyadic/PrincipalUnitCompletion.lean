/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.PrincipalUnitTorsion
import GQ2.ProPAbelianization

/-!
# Residual 2-finiteness and the pro-2 completion of deep principal units

This file proves the strongest completion statement currently justified by the unit-filtration
API.  Every nontrivial element of `U^(i)`, for `i ≥ 1`, survives in a finite quotient
`U^(i) / U^(j)` of 2-power order.  Consequently the canonical map from the abstract group
`U^(i)` to its pro-2 completion is injective.

At depth `e + 1`, this combines with `isMulTorsionFree_depthUnits_succ_e`: the canonical image
contains no nontrivial torsion.  This is deliberately **not** a claim that the whole abstract
pro-2 completion is torsion-free.  Such a claim would require a cofinal power-subgroup theorem,
a logarithmic identification with an additive lattice, or another no-new-torsion theorem for
completion; none is used here.
-/

namespace GQ2

noncomputable section

/-! ## An abstract residual-`p` injectivity criterion -/

/-- An abstract group is residually a finite `p`-group if every nonidentity element is omitted
by a finite-index normal subgroup whose quotient is a `p`-group. -/
def IsResiduallyP (p : ℕ) (A : Type) [Group A] : Prop :=
  ∀ a : A, a ≠ 1 → ∃ N : FiniteIndexNormalSubgroup A,
    IsPGroup p (A ⧸ N.toSubgroup) ∧ a ∉ N

/-- Residual finite-`p` separation is exactly the extra input needed to keep the maximal
pro-`p` quotient from destroying injectivity of the profinite-completion map. -/
theorem proPCompletionMk_injective_of_isResiduallyP {p : ℕ} {A : Type} [Group A]
    (hA : IsResiduallyP p A) : Function.Injective (proPCompletionMk p A) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  by_contra hane
  obtain ⟨N, hNp, haN⟩ := hA a hane
  let Q := A ⧸ N.toSubgroup
  letI : TopologicalSpace Q := ⊥
  letI : DiscreteTopology Q := ⟨rfl⟩
  let f : A →* Q := QuotientGroup.mk' N.toSubgroup
  have hmap := congrArg (proPCompletionLift (isProP_of_isPGroup hNp) f) ha
  rw [proPCompletionLift_mk, map_one] at hmap
  exact haN ((QuotientGroup.eq_one_iff a).mp hmap)

namespace Dyadic

open scoped Classical

local notation "ℚbar2" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚbar2}

/-! ## The finite 2-group filtration quotients -/

/-- The relative index of two positive-depth unit groups is the product of the intervening
graded-piece cardinalities. -/
theorem depthUnits_relIndex_eq_two_pow (FF : DyadicUnitFiltration K)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    (depthUnits K FF.π j).relIndex (depthUnits K FF.π i) =
      2 ^ ((j - i) * FF.f) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
      have hji : depthUnits K FF.π j ≤ depthUnits K FF.π i :=
        depthUnits_antitone K FF.π FF.hπ_lt.le hij
      have hnext : depthUnits K FF.π (j + 1) ≤ depthUnits K FF.π j :=
        depthUnits_antitone K FF.π FF.hπ_lt.le (Nat.le_succ j)
      have hgrade :
          (depthUnits K FF.π (j + 1)).relIndex (depthUnits K FF.π j) = 2 ^ FF.f := by
        change ((depthUnits K FF.π (j + 1)).subgroupOf
          (depthUnits K FF.π j)).index = 2 ^ FF.f
        rw [Subgroup.index_eq_card]
        exact FF.card_gr j (hi.trans hij)
      calc
        (depthUnits K FF.π (j + 1)).relIndex (depthUnits K FF.π i) =
            (depthUnits K FF.π (j + 1)).relIndex (depthUnits K FF.π j) *
              (depthUnits K FF.π j).relIndex (depthUnits K FF.π i) :=
          (Subgroup.relIndex_mul_relIndex _ _ _ hnext hji).symm
        _ = 2 ^ FF.f * 2 ^ ((j - i) * FF.f) := by rw [hgrade, ih]
        _ = 2 ^ (((j + 1) - i) * FF.f) := by
          have hsub : (j + 1) - i = (j - i) + 1 := by omega
          rw [hsub, Nat.add_mul, one_mul, pow_add, mul_comm]

/-- Cardinality form of `depthUnits_relIndex_eq_two_pow`.  In particular every quotient between
positive depths is finite and has 2-power order. -/
theorem natCard_depthUnits_quotient_eq_two_pow (FF : DyadicUnitFiltration K)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    Nat.card (↥(depthUnits K FF.π i) ⧸
      (depthUnits K FF.π j).subgroupOf (depthUnits K FF.π i)) =
        2 ^ ((j - i) * FF.f) := by
  rw [← Subgroup.index_eq_card]
  exact depthUnits_relIndex_eq_two_pow FF hi hij

/-! ## Residual 2-finiteness and completion injectivity -/

/-- Every positive-depth principal-unit group is residually a finite 2-group.  The separating
quotient is another unit-filtration quotient; the fact that `‖π‖^j → 0` makes their kernels
intersect trivially. -/
theorem isResiduallyP_two_depthUnits (FF : DyadicUnitFiltration K)
    {i : ℕ} (hi : 1 ≤ i) : IsResiduallyP 2 ↥(depthUnits K FF.π i) := by
  intro u hu
  have hune : (((u.1 : (↥K)ˣ) : ↥K) : ℚbar2) - 1 ≠ 0 := by
    intro hzero
    apply hu
    apply Subtype.ext
    apply Units.ext
    apply Subtype.ext
    exact sub_eq_zero.mp hzero
  have hdistpos : 0 < ‖(((u.1 : (↥K)ˣ) : ↥K) : ℚbar2) - 1‖ :=
    norm_pos_iff.mpr hune
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hdistpos FF.hπ_lt
  let j := i + m
  have hij : i ≤ j := Nat.le_add_right i m
  have hπnonneg : 0 ≤ ‖FF.π‖ := norm_nonneg _
  have hpowi : ‖FF.π‖ ^ i ≤ 1 := pow_le_one₀ hπnonneg FF.hπ_lt.le
  have hjlt : ‖FF.π‖ ^ j < ‖(((u.1 : (↥K)ˣ) : ↥K) : ℚbar2) - 1‖ := by
    calc
      ‖FF.π‖ ^ j = ‖FF.π‖ ^ i * ‖FF.π‖ ^ m := by rw [show j = i + m from rfl, pow_add]
      _ ≤ 1 * ‖FF.π‖ ^ m := mul_le_mul_of_nonneg_right hpowi (pow_nonneg hπnonneg m)
      _ = ‖FF.π‖ ^ m := one_mul _
      _ < ‖(((u.1 : (↥K)ˣ) : ↥K) : ℚbar2) - 1‖ := hm
  let H : Subgroup ↥(depthUnits K FF.π i) :=
    (depthUnits K FF.π j).subgroupOf (depthUnits K FF.π i)
  have hcard : Nat.card (↥(depthUnits K FF.π i) ⧸ H) = 2 ^ ((j - i) * FF.f) := by
    simpa [H] using natCard_depthUnits_quotient_eq_two_pow FF hi hij
  letI : Finite (↥(depthUnits K FF.π i) ⧸ H) :=
    Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero ((j - i) * FF.f) two_ne_zero)
  letI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let N : FiniteIndexNormalSubgroup ↥(depthUnits K FF.π i) :=
    FiniteIndexNormalSubgroup.ofSubgroup H
  refine ⟨N, ?_, ?_⟩
  · exact IsPGroup.of_card hcard
  · change u ∉ H
    intro huH
    have huj : u.1 ∈ depthUnits K FF.π j := huH
    exact (not_le_of_gt hjlt) ((mem_depthUnits K FF.π j u.1).mp huj).2

/-- The canonical map of any positive-depth principal-unit group into its abstract pro-2
completion is injective. -/
theorem proTwoCompletionMk_depthUnits_injective (FF : DyadicUnitFiltration K)
    {i : ℕ} (hi : 1 ≤ i) :
    Function.Injective (proPCompletionMk 2 ↥(depthUnits K FF.π i)) :=
  proPCompletionMk_injective_of_isResiduallyP (isResiduallyP_two_depthUnits FF hi)

/-- The requested depth-`e+1` specialization. -/
theorem proTwoCompletionMk_depthUnits_succ_e_injective (FF : DyadicUnitFiltration K) :
    Function.Injective
      (proPCompletionMk 2 ↥(depthUnits K FF.π (FF.e + 1))) :=
  proTwoCompletionMk_depthUnits_injective FF (by omega)

/-- On the canonical image, completion creates no torsion: a deep unit whose image has finite
order was already finite-order, hence equals `1`.  This says nothing about completion points
outside the canonical image. -/
theorem depthUnit_eq_one_of_proTwoCompletionMk_isOfFinOrder
    (FF : DyadicUnitFiltration K) (u : ↥(depthUnits K FF.π (FF.e + 1)))
    (hu : IsOfFinOrder (proPCompletionMk 2 ↥(depthUnits K FF.π (FF.e + 1)) u)) :
    u = 1 := by
  apply depthUnit_eq_one_of_isOfFinOrder FF u
  exact (proTwoCompletionMk_depthUnits_succ_e_injective FF).isOfFinOrder_iff.mp hu

end Dyadic
end
end GQ2

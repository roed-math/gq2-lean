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

/-! ## When the abstract completion agrees with a compact topology -/

/-- Every finite `p`-group quotient of the underlying abstract group has open kernel in the
given topology.  This is the precise "no discontinuous finite `p`-quotients" condition needed
to compare the abstract pro-`p` completion with an already compact group topology. -/
def FinitePQuotientsAreOpen (p : ℕ) (A : Type) [Group A] [TopologicalSpace A] : Prop :=
  ∀ N : FiniteIndexNormalSubgroup A, IsPGroup p (A ⧸ N.toSubgroup) →
    IsOpen (N.toSubgroup : Set A)

/-- The canonical map to the abstract pro-`p` completion always has dense range. -/
theorem proPCompletionMk_denseRange {p : ℕ} {A : Type} [Group A] :
    DenseRange (proPCompletionMk p A) := by
  change DenseRange
    ((⇑(maxProPMk p (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of A)))) ∘
      ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of A))
  exact DenseRange.comp
    (Function.Surjective.denseRange (maxProPMk_surjective
      (p := p) (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of A))))
    (ProfiniteGrp.ProfiniteCompletion.denseRange _)
    (maxProPMk p
      (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of A))).continuous_toFun

/-- If all abstract finite `p`-group quotients are continuous, then so is the canonical map
from a topological group to its abstract pro-`p` completion. -/
theorem continuous_proPCompletionMk_of_finitePQuotientsAreOpen
    {p : ℕ} {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    (hopen : FinitePQuotientsAreOpen p A) : Continuous (proPCompletionMk p A) := by
  apply continuous_of_tendsto_nhds_one
  intro O hO
  rw [mem_nhds_iff] at hO
  obtain ⟨W, hWO, hWopen, h1W⟩ := hO
  obtain ⟨V, hVW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    hWopen h1W
  let f : A →* proPCompletion p A := proPCompletionMk p A
  let φ : A →* (proPCompletion p A ⧸ V.toSubgroup) :=
    (QuotientGroup.mk' V.toSubgroup).comp f
  letI : Finite φ.range := Finite.of_injective Subtype.val Subtype.val_injective
  let N : FiniteIndexNormalSubgroup A := FiniteIndexNormalSubgroup.ofSubgroup φ.ker
  have hNp : IsPGroup p (A ⧸ N.toSubgroup) := by
    change IsPGroup p (A ⧸ φ.ker)
    exact ((isProP_maxProPQuotient
      (p := p) (G := ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of A)) V).to_subgroup
        φ.range).of_equiv (QuotientGroup.quotientKerEquivRange φ).symm
  have hNopen : IsOpen (N.toSubgroup : Set A) := hopen N hNp
  have hker : (N.toSubgroup : Set A) = f ⁻¹' (V.toSubgroup : Set (proPCompletion p A)) := by
    ext a
    change a ∈ φ.ker ↔ f a ∈ V.toSubgroup
    simp only [MonoidHom.mem_ker, φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  refine Filter.mem_of_superset ?_ (fun a ha ↦ hWO (hVW ha))
  change (proPCompletionMk p A) ⁻¹' (V.toSubgroup : Set (proPCompletion p A)) ∈ nhds 1
  rw [← hker]
  exact hNopen.mem_nhds (N.toSubgroup.one_mem)

/-- A continuous canonical map from a compact group onto its abstract pro-`p` completion is
surjective: its range is simultaneously compact (hence closed) and dense. -/
theorem proPCompletionMk_surjective_of_continuous
    {p : ℕ} {A : Type} [Group A] [TopologicalSpace A] [CompactSpace A]
    (hcont : Continuous (proPCompletionMk p A)) :
    Function.Surjective (proPCompletionMk p A) := by
  have hclosed : IsClosed (Set.range (proPCompletionMk p A)) :=
    (isCompact_range hcont).isClosed
  rw [← Set.range_eq_univ, ← hclosed.closure_eq,
    (proPCompletionMk_denseRange (p := p) (A := A)).closure_eq]

/-- **Abstract completion reduction.**  A compact torsion-free group has torsion-free abstract
pro-`p` completion as soon as its finite `p`-group quotients are all continuous and the
canonical map is injective.  Thus the only arithmetic issue is openness of the abstract finite
`p`-quotient kernels; no assertion about completion points is smuggled in. -/
theorem isMulTorsionFree_proPCompletion_of_finitePQuotientsAreOpen
    {p : ℕ} {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [IsMulTorsionFree A]
    (hinj : Function.Injective (proPCompletionMk p A))
    (hopen : FinitePQuotientsAreOpen p A) : IsMulTorsionFree (proPCompletion p A) := by
  have hcont := continuous_proPCompletionMk_of_finitePQuotientsAreOpen hopen
  have hsurj := proPCompletionMk_surjective_of_continuous hcont
  constructor
  intro n hn x y hxy
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨b, rfl⟩ := hsurj y
  congr 1
  apply IsMulTorsionFree.pow_left_injective hn
  apply hinj
  simpa only [map_pow] using hxy

namespace Dyadic

open scoped Classical

local notation "ℚbar2" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚbar2}

/-! ## The exact depth-cofinality interface -/

/-- Each deeper unit subgroup is open in a fixed positive-depth unit group.  This is the
unconditional topological half of the cofinality problem. -/
theorem isOpen_depthUnits_subgroupOf (FF : DyadicUnitFiltration K) (i j : ℕ) :
    IsOpen (((depthUnits K FF.π j).subgroupOf (depthUnits K FF.π i) :
      Subgroup ↥(depthUnits K FF.π i)) : Set ↥(depthUnits K FF.π i)) := by
  let d : ↥(depthUnits K FF.π i) → ℚbar2 := fun u ↦
    (((u.1 : (↥K)ˣ) : ↥K) : ℚbar2) - 1
  have hd : Continuous d := by
    exact ((continuous_subtype_val.comp
      (Units.continuous_val.comp continuous_subtype_val)).sub continuous_const)
  have hset :
      (((depthUnits K FF.π j).subgroupOf (depthUnits K FF.π i) :
        Subgroup ↥(depthUnits K FF.π i)) : Set ↥(depthUnits K FF.π i)) =
        d ⁻¹' Metric.closedBall 0 (‖FF.π‖ ^ j) := by
    ext u
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    constructor
    · intro hu
      exact ((mem_depthUnits K FF.π j u.1).mp hu).2
    · intro hu
      exact (mem_depthUnits K FF.π j u.1).mpr ⟨u.2.1, hu⟩
  rw [hset]
  exact (IsUltrametricDist.isOpen_closedBall 0
    (ne_of_gt (pow_pos (norm_pos_iff.mpr FF.hπ_ne) j))).preimage hd

/-- The principal-unit depth filtration is cofinal among all finite-index normal subgroups
with finite `2`-group quotient.  Unlike residual `2`-finiteness, this quantifies over *every*
abstract finite `2`-quotient and therefore rules out discontinuous ones. -/
def DepthUnitsCofinalInFiniteTwoQuotients (FF : DyadicUnitFiltration K) (i : ℕ) : Prop :=
  ∀ N : FiniteIndexNormalSubgroup ↥(depthUnits K FF.π i),
    IsPGroup 2 (↥(depthUnits K FF.π i) ⧸ N.toSubgroup) →
      ∃ j : ℕ, i ≤ j ∧
        (depthUnits K FF.π j).subgroupOf (depthUnits K FF.π i) ≤ N.toSubgroup

/-- Depth cofinality implies that every abstract finite `2`-quotient is continuous. -/
theorem finitePQuotientsAreOpen_depthUnits_of_cofinal
    (FF : DyadicUnitFiltration K) (i : ℕ)
    (hcofinal : DepthUnitsCofinalInFiniteTwoQuotients FF i) :
    FinitePQuotientsAreOpen 2 ↥(depthUnits K FF.π i) := by
  intro N hN
  obtain ⟨j, _, hjN⟩ := hcofinal N hN
  exact Subgroup.isOpen_mono hjN (isOpen_depthUnits_subgroupOf FF i j)

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

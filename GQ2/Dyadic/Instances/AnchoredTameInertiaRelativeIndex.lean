/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.AnchoredTameInertiaNormIndex

/-!
# The visible index of the anchored tame-inertia field

For `U = GalKsub K`, the canonical tame-inertia field is fixed by the anchored image of
`rho ⁻¹(<t>)`.  This module computes its relative degree index exactly:

`[F₀ : K] = [rho.range : <t>]`.

The relative ramification index `e(F₀/K)` divides that visible quotient index.  This is the
strongest conclusion supplied by the fixed-field, subgroup-index, coset-norm, and tower APIs.
It does not make `e(F₀/K)` odd merely from oddness of `orderOf t`: the identity map of the
order-two group with `t = 1` has odd `orderOf t` and preimage index two.  Thus the tau-order
argument controls the complementary `L/F₀` leg, not this `F₀/K` leg.

`AnchoredTameInertiaOddRangeIndexAt` records the strongest direct group-index premise and gives
an honest producer for `AnchoredTameInertiaRelativeOddDataAt`.  It is sufficient, but stronger
than the arithmetic truth expected here: tame orientation should make `F₀/K` unramified, hence
`e(F₀/K) = 1`, even when its residue degree `[rho.range : <t>]` is even.  Proving that equality
still needs the absent relative unit/norm-reciprocity identification for this prescribed field;
it cannot follow from these subgroup cardinalities alone.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]
local notation "GalQ2" => Kummer.GaloisGroup ℚ_[2]

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C]

private theorem map_top_subtypeAnc_eq_fixingSubgroup
    (K : IntermediateField ℚ_[2] ℚ̄₂) :
    (⊤ : Subgroup ↑(GalKsub K)).map (subtypeAnc (GalKsub K)).toMonoidHom =
      K.fixingSubgroup := by
  ext g
  constructor
  · rintro ⟨x, -, rfl⟩
    exact x.2
  · intro hg
    exact ⟨⟨g, hg⟩, trivial, rfl⟩

/-- The relative field degree index is exactly the index of the tame-inertia preimage. -/
theorem anchoredTameInertiaField_fixing_index
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (rho : ContinuousMonoidHom ↑(GalKsub K) C) (t : C) :
    (((anchoredTameInertiaField (GalKsub K) rho t).fixingSubgroup).subgroupOf
      K.fixingSubgroup).index =
        ((Subgroup.zpowers t).comap rho.toMonoidHom).index := by
  rw [fixingSubgroup_anchoredTameInertiaField (GalKsub K)
    (isOpen_fixingSubgroup K) rho t, ← map_top_subtypeAnc_eq_fixingSubgroup K]
  change (((Subgroup.zpowers t).comap rho.toMonoidHom).map
      (subtypeAnc (GalKsub K)).toMonoidHom).relIndex
        ((⊤ : Subgroup ↑(GalKsub K)).map
          (subtypeAnc (GalKsub K)).toMonoidHom) = _
  rw [Subgroup.relIndex_map_map_of_injective _ _
    (subtypeAnc_injective (GalKsub K))]
  exact Subgroup.relIndex_top_right _

/-- Equivalently, the relative field degree index is the index of `<t>` inside `rho.range`. -/
theorem anchoredTameInertiaField_fixing_index_eq_relIndex_range
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (rho : ContinuousMonoidHom ↑(GalKsub K) C) (t : C) :
    (((anchoredTameInertiaField (GalKsub K) rho t).fixingSubgroup).subgroupOf
      K.fixingSubgroup).index =
        (Subgroup.zpowers t).relIndex rho.toMonoidHom.range := by
  rw [anchoredTameInertiaField_fixing_index K rho t,
    Subgroup.index_comap]

/-- The relative ramification index divides the exact finite quotient index visible from the
anchored subgroup. -/
theorem anchoredTameInertiaField_relE_dvd_relIndex_range
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (FK : DyadicUnitFiltration K) (rho : ContinuousMonoidHom ↑(GalKsub K) C) (t : C)
    (F₀F : DyadicUnitFiltration (anchoredTameInertiaField (GalKsub K) rho t)) :
    GaloisCosetNorm.relE FK F₀F
        (baseField_le_anchoredTameInertiaField K rho t) ∣
      ((Subgroup.zpowers t).relIndex rho.toMonoidHom.range : ℤ) := by
  let F₀ := anchoredTameInertiaField (GalKsub K) rho t
  letI : FiniteDimensional ℚ_[2] F₀ :=
    anchoredTameInertiaField_finiteDimensional (GalKsub K)
      (isOpen_fixingSubgroup K) rho t
  letI : CompactSpace ↑K.fixingSubgroup :=
    isCompact_iff_compactSpace.mp
      (IntermediateField.fixingSubgroup_isClosed K).isCompact
  have hopen : IsOpen
      ((((F₀.fixingSubgroup).subgroupOf K.fixingSubgroup) :
        Subgroup ↑K.fixingSubgroup) : Set ↑K.fixingSubgroup) := by
    change IsOpen ((fun x : ↑K.fixingSubgroup ↦ (x : GalQ2)) ⁻¹'
      (F₀.fixingSubgroup : Set GalQ2))
    exact (isOpen_fixingSubgroup F₀).preimage continuous_subtype_val
  letI : Finite (↑K.fixingSubgroup ⧸
      (F₀.fixingSubgroup).subgroupOf K.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hdiv := UnramifiedBridge.relE_dvd_of_index FK F₀F
    (baseField_le_anchoredTameInertiaField K rho t)
  rw [show Nat.card (↑K.fixingSubgroup ⧸
      (F₀.fixingSubgroup).subgroupOf K.fixingSubgroup) =
        (Subgroup.zpowers t).relIndex rho.toMonoidHom.range by
      exact anchoredTameInertiaField_fixing_index_eq_relIndex_range K rho t] at hdiv
  exact hdiv

/-- Pure subgroup arithmetic cannot turn odd `orderOf t` into an odd preimage index: for the
identity map of the order-two group and `t = 1`, the order of `t` is odd while the preimage of
`<t>` has index two. -/
theorem odd_order_even_tamePreimage_index_regression :
    Odd (orderOf (1 : Multiplicative (ZMod 2))) ∧
      Even (((Subgroup.zpowers (1 : Multiplicative (ZMod 2))).comap
        (MonoidHom.id (Multiplicative (ZMod 2)))).index) := by
  constructor
  · simp
  · rw [show (Subgroup.zpowers (1 : Multiplicative (ZMod 2))).comap
        (MonoidHom.id (Multiplicative (ZMod 2))) = ⊥ by simp,
      Subgroup.index_bot]
    change Even (Nat.card (ZMod 2))
    rw [Nat.card_zmod]
    exact even_two

/-- The strongest direct subgroup-index premise: in every compatible ramified use, the quotient
of `rho.range` by the cyclic tame-inertia image has odd index. -/
def AnchoredTameInertiaOddRangeIndexAt
    (P : FieldParameters) (K : IntermediateField ℚ_[2] ℚ̄₂)
    (tame : ContinuousMonoidHom ↑(GalKsub K) (Tq P.qK)) : Prop :=
  ∀ {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    (V : Type) [AddCommGroup V] [DistribMulAction D V]
    (c : ContinuousMonoidHom (Tq P.qK) D)
    (rho : ContinuousMonoidHom ↑(GalKsub K) D),
    (∀ g : ↑(GalKsub K), rho g = c (tame g)) →
      (∃ v : V, c (tqTau P.qK) • v ≠ v) →
        Odd ((Subgroup.zpowers (c (tqTau P.qK))).relIndex rho.toMonoidHom.range)

/-- Oddness of the exact visible subgroup quotient forces odd relative ramification. -/
theorem anchoredTameInertiaRelativeOddDataAt_of_oddRangeIndex
    (P : FieldParameters) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] (FK : DyadicUnitFiltration K)
    (tame : ContinuousMonoidHom ↑(GalKsub K) (Tq P.qK))
    (Hindex : AnchoredTameInertiaOddRangeIndexAt P K tame) :
    AnchoredTameInertiaRelativeOddDataAt P K FK tame := by
  intro D _ _ _ _ V _ _ c rho hfac hram
  let F₀ := anchoredTameInertiaField (GalKsub K) rho (c (tqTau P.qK))
  letI : FiniteDimensional ℚ_[2] F₀ :=
    anchoredTameInertiaField_finiteDimensional (GalKsub K)
      (isOpen_fixingSubgroup K) rho (c (tqTau P.qK))
  let F₀F : DyadicUnitFiltration F₀ := dyadicUnitFiltration F₀
  refine ⟨F₀F, ?_⟩
  have hdiv := anchoredTameInertiaField_relE_dvd_relIndex_range K FK rho
    (c (tqTau P.qK)) F₀F
  obtain ⟨a, ha⟩ := hdiv
  have hindexZ : Odd
      (((Subgroup.zpowers (c (tqTau P.qK))).relIndex rho.toMonoidHom.range : ℕ) : ℤ) := by
    exact_mod_cast Hindex V c rho hfac hram
  exact (Int.odd_mul.mp (ha ▸ hindexZ)).1

/-- The odd visible quotient-index premise feeds the full compatible involution norm theorem. -/
theorem anchoredInvolutionEqualNormValueGroupsAt_of_oddTameRangeIndex
    (P : FieldParameters) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] (FK : DyadicUnitFiltration K)
    (tame : ContinuousMonoidHom ↑(GalKsub K) (Tq P.qK))
    (htame : Function.Surjective tame) (hodd : Odd (Module.finrank ℚ_[2] K))
    (Hindex : AnchoredTameInertiaOddRangeIndexAt P K tame) :
    AnchoredInvolutionEqualNormValueGroupsAt P (GalKsub K) tame :=
  anchoredInvolutionEqualNormValueGroupsAt_of_relativeOddTameInertia P K FK tame
    htame hodd
    (anchoredTameInertiaRelativeOddDataAt_of_oddRangeIndex P K FK tame Hindex)

#print axioms anchoredTameInertiaField_fixing_index
#print axioms anchoredTameInertiaField_fixing_index_eq_relIndex_range
#print axioms anchoredTameInertiaField_relE_dvd_relIndex_range
#print axioms odd_order_even_tamePreimage_index_regression
#print axioms AnchoredTameInertiaOddRangeIndexAt
#print axioms anchoredTameInertiaRelativeOddDataAt_of_oddRangeIndex
#print axioms anchoredInvolutionEqualNormValueGroupsAt_of_oddTameRangeIndex

end
end GQ2.Dyadic

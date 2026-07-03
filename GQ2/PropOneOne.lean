import GQ2.Reciprocity
import GQ2.MaxProP

/-!
# Proposition 1.1 infrastructure: `ℤ₂` is pro-2, and `ν_ur` descends  (ticket P-10)

Proposition 1.1 (`GQ2.SectionThree.prop_1_1`) reads the unramified coordinates `ν_ur(a,s,y) =
(−2,1,0)` of the marked generators through arbitrary lifts to `G_{ℚ₂}`.  For that reading to be
well-defined the coordinate `ν_ur ∘ toAb : G_{ℚ₂} → ℤ₂` must be **constant on the fibres of the
maximal pro-2 quotient** `maxProPMk 2 G_{ℚ₂}` — i.e. it must factor through `G_{ℚ₂}(2)`.

This file supplies that descent.  Its engine is:

* `isProP_two_multPadicInt` : `IsProP 2 (Multiplicative ℤ₂)` — the target of `ν_ur` is a pro-2
  group.  Proof: every open subgroup of `ℤ₂` contains `2ⁿℤ₂ = span{2ⁿ}` for some `n` (the
  `span{2ⁿ}` are a `0`-neighbourhood basis, `PadicInt.norm_le_pow_iff_mem_span_pow`), so `2ⁿ`
  *uniformly* annihilates every finite quotient — a `2`-group.
* `nu_ur_descends` : `ν_ur ∘ toAb` factors through `maxProPMk 2 G_{ℚ₂}`, via the universal property
  of the maximal pro-2 quotient (`proPKernel_le_ker` for the pro-2 target above).

`docs/section3-extraction.md` §1.1 flags exactly this (`IsProP 2 (Multiplicative ℤ₂)` descent).
The remaining assembly of `prop_1_1` (compose B4's iso with Lemma 3.5's marked abelianization and
Prop. 3.8's automorphism lift) is **blocked** on P-07 (`lemma_3_5_marked_abelianization`, in
progress) and P-08 (`prop_3_8_*`, infrastructure-escalated — see the design note §Escalations 4);
this descent is the part of P-10 that is independent of them.
-/

open scoped Classical

namespace GQ2

namespace PropOneOne

/-- The `span{2ⁿ}` are a neighbourhood basis of `0` in `ℤ₂`: every open set containing `0` contains
`span{2ⁿ}` for some `n`. -/
lemma exists_span_pow_subset {S : Set ℤ_[2]} (hopen : IsOpen S) (hmem : (0 : ℤ_[2]) ∈ S) :
    ∃ n : ℕ, (Ideal.span {(2 : ℤ_[2]) ^ n} : Set ℤ_[2]) ⊆ S := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨n, fun x hx => hball ?_⟩
  have hx' : ‖x‖ ≤ (2 : ℝ) ^ (-n : ℤ) :=
    (PadicInt.norm_le_pow_iff_mem_span_pow x n).mpr hx
  rw [Metric.mem_ball, dist_eq_norm, sub_zero]
  calc ‖x‖ ≤ (2 : ℝ) ^ (-n : ℤ) := hx'
    _ = ((2 : ℝ)⁻¹) ^ n := by rw [zpow_neg, zpow_natCast, inv_pow]
    _ < ε := hn

/-- **`ℤ₂` is a pro-2 group** (multiplicatively): every finite continuous quotient of
`Multiplicative ℤ₂` is a `2`-group. -/
theorem isProP_two_multPadicInt : IsProP 2 (Multiplicative ℤ_[2]) := by
  intro U
  -- `S = {x : ℤ₂ | ofAdd x ∈ U}`, an open set containing `0`.
  set S : Set ℤ_[2] := Multiplicative.ofAdd ⁻¹' (U.toSubgroup : Set (Multiplicative ℤ_[2])) with hS
  have hopen : IsOpen S := U.isOpen'.preimage continuous_ofAdd
  have hmem : (0 : ℤ_[2]) ∈ S := by
    simp only [hS, Set.mem_preimage, SetLike.mem_coe]
    exact one_mem _
  obtain ⟨n, hspan⟩ := exists_span_pow_subset hopen hmem
  intro g
  refine ⟨n, ?_⟩
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective g
  show (QuotientGroup.mk' U.toSubgroup m) ^ (2 ^ n) = 1
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  -- `m ^ 2^n = ofAdd (2^n • toAdd m)`; and `2^n • toAdd m ∈ span{2^n} ⊆ S`, i.e. its `ofAdd` is in U.
  have hmem2 : (2 : ℤ_[2]) ^ n * Multiplicative.toAdd m ∈ S := by
    apply hspan
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hpow : m ^ (2 ^ n) = Multiplicative.ofAdd ((2 : ℤ_[2]) ^ n * Multiplicative.toAdd m) := by
    rw [← ofAdd_toAdd m, ← ofAdd_nsmul, toAdd_ofAdd, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [hpow]
  simpa only [hS, Set.mem_preimage, SetLike.mem_coe] using hmem2

/-! ## The `ν_ur`-descent through the maximal pro-2 quotient -/

section Descent

variable (R : LocalReciprocity)
variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- `ν_ur ∘ toAb : G_{ℚ₂} → ℤ₂` as a continuous homomorphism. -/
noncomputable def nuUrComp : ContinuousMonoidHom AbsGalQ2 (Multiplicative ℤ_[2]) where
  toFun g := R.nu_ur (toAb g)
  map_one' := by simp
  map_mul' a b := by simp [map_mul]
  continuous_toFun := R.continuous_nu_ur.comp continuous_quot_mk

/-- **`ν_ur` descends through the maximal pro-2 quotient.**  Since `ℤ₂` is pro-2
(`isProP_two_multPadicInt`), the continuous hom `ν_ur ∘ toAb : G_{ℚ₂} → ℤ₂` factors through
`G_{ℚ₂}(2) = maxProPQuotient 2 G_{ℚ₂}` (universal property `maxProPHomEquiv`): there is a continuous
`ν̄` with `ν̄ (maxProPMk g) = ν_ur (toAb g)`.  This is the well-definedness Prop. 1.1's `ν_ur`-rows
require (they read `ν_ur(toAb g)` off `maxProPMk g`). -/
noncomputable def nuUrBar :
    ContinuousMonoidHom (maxProPQuotient 2 AbsGalQ2) (Multiplicative ℤ_[2]) :=
  (maxProPHomEquiv isProP_two_multPadicInt).symm (nuUrComp R)

@[simp] lemma nuUrBar_maxProPMk (g : AbsGalQ2) :
    nuUrBar R (maxProPMk 2 AbsGalQ2 g) = R.nu_ur (toAb g) :=
  DFunLike.congr_fun ((maxProPHomEquiv isProP_two_multPadicInt).apply_symm_apply (nuUrComp R)) g

/-- **`ν_ur ∘ toAb` is constant on the fibres of `maxProPMk`** — the exact fact Prop. 1.1's
`ν_ur`-rows consume (all lifts `g` of a fixed `maxProP`-class have the same `ν_ur(toAb g)`). -/
lemma nu_ur_toAb_eq_of_maxProPMk_eq {g₁ g₂ : AbsGalQ2}
    (h : maxProPMk 2 AbsGalQ2 g₁ = maxProPMk 2 AbsGalQ2 g₂) :
    R.nu_ur (toAb g₁) = R.nu_ur (toAb g₂) := by
  rw [← nuUrBar_maxProPMk R g₁, ← nuUrBar_maxProPMk R g₂, h]

end Descent

end PropOneOne

end GQ2

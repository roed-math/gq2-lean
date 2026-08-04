/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.OrientedTameBundle

/-!
# Multiplicative decomposition of a finite dyadic field

The unit-filtration uniformizer gives the usual abstract group decomposition

`K× ≃ O_K× × ℤ`.

Here `O_K×` is the repository's spectral-norm subgroup `normUnits K`.  The integer coordinate
is constructed from value-group discreteness and is uniquely characterized by
`.‖x‖ = ‖π‖ ^ valuation`.  This exact multiplicative equivalence is the source-side packaging
needed to transfer the unit-filtration completion calculation to all of `K×`.
-/

namespace GQ2.Dyadic

noncomputable section

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂}

/-- The integer exponent of a nonzero field element relative to the filtration uniformizer. -/
noncomputable def dyadicValuation (FF : DyadicUnitFiltration K) (x : (↥K)ˣ) : ℤ :=
  Classical.choose (Aux.exists_norm_eq_zpow FF (x : ↥K).2 (by simp))

/-- Characterizing norm identity for `dyadicValuation`. -/
theorem norm_eq_zpow_dyadicValuation (FF : DyadicUnitFiltration K) (x : (↥K)ˣ) :
    ‖(((x : (↥K)ˣ) : ↥K) : ℚ̄₂)‖ = ‖FF.π‖ ^ dyadicValuation FF x :=
  Classical.choose_spec (Aux.exists_norm_eq_zpow FF (x : ↥K).2 (by simp))

/-- The norm exponent is unique because the uniformizer norm lies strictly between zero and
one. -/
theorem dyadicValuation_eq_of_norm_eq_zpow (FF : DyadicUnitFiltration K)
    (x : (↥K)ˣ) (n : ℤ)
    (hn : ‖(((x : (↥K)ˣ) : ↥K) : ℚ̄₂)‖ = ‖FF.π‖ ^ n) :
    dyadicValuation FF x = n := by
  apply zpow_right_injective₀ (norm_pos_iff.mpr FF.hπ_ne) (ne_of_lt FF.hπ_lt)
  change ‖FF.π‖ ^ dyadicValuation FF x = ‖FF.π‖ ^ n
  rw [← norm_eq_zpow_dyadicValuation FF x, hn]

theorem dyadicValuation_one (FF : DyadicUnitFiltration K) :
    dyadicValuation FF (1 : (↥K)ˣ) = 0 := by
  apply dyadicValuation_eq_of_norm_eq_zpow FF _ 0
  change ‖(1 : ℚ̄₂)‖ = ‖FF.π‖ ^ (0 : ℤ)
  rw [norm_one, zpow_zero]

theorem dyadicValuation_mul (FF : DyadicUnitFiltration K) (x y : (↥K)ˣ) :
    dyadicValuation FF (x * y) = dyadicValuation FF x + dyadicValuation FF y := by
  apply dyadicValuation_eq_of_norm_eq_zpow FF _ _
  change ‖(((x : ↥K) : ℚ̄₂) * ((y : ↥K) : ℚ̄₂))‖ = _
  rw [norm_mul, norm_eq_zpow_dyadicValuation FF x,
    norm_eq_zpow_dyadicValuation FF y, zpow_add₀ (norm_ne_zero_iff.mpr FF.hπ_ne)]

@[simp] theorem uniformizerK_val_zpow_coe (FF : DyadicUnitFiltration K) (n : ℤ) :
    ((((uniformizerK K FF : ↥K) ^ n : ↥K) : ℚ̄₂)) = FF.π ^ n := by
  exact (map_zpow₀ K.val _ _).trans
    (congrArg (fun z : ℚ̄₂ ↦ z ^ n) (uniformizerK_coe K FF))

/-- The integer valuation as a multiplicative homomorphism. -/
noncomputable def dyadicValuationHom (FF : DyadicUnitFiltration K) :
    (↥K)ˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (dyadicValuation FF x)
  map_one' := congrArg Multiplicative.ofAdd (dyadicValuation_one FF)
  map_mul' x y := congrArg Multiplicative.ofAdd (dyadicValuation_mul FF x y)

@[simp] theorem dyadicValuationHom_apply (FF : DyadicUnitFiltration K) (x : (↥K)ˣ) :
    (dyadicValuationHom FF x).toAdd = dyadicValuation FF x := rfl

/-- Remove the uniformizer power from `x`, leaving a norm-one unit. -/
noncomputable def normalizedUnit (FF : DyadicUnitFiltration K) (x : (↥K)ˣ) :
    ↥(normUnits K) :=
  ⟨x * uniformizerK K FF ^ (-dyadicValuation FF x), by
    rw [mem_normUnits]
    simp only [Units.val_mul]
    push_cast
    rw [uniformizerK_val_zpow_coe, norm_mul, norm_zpow, norm_eq_zpow_dyadicValuation FF x,
      ← zpow_add₀ (norm_ne_zero_iff.mpr FF.hπ_ne), add_neg_cancel, zpow_zero]⟩

/-- Recombining the normalized unit and valuation returns the original element. -/
theorem normalizedUnit_mul_uniformizer (FF : DyadicUnitFiltration K) (x : (↥K)ˣ) :
    (normalizedUnit FF x).1 * uniformizerK K FF ^ dyadicValuation FF x = x := by
  change (x * uniformizerK K FF ^ (-dyadicValuation FF x)) *
      uniformizerK K FF ^ dyadicValuation FF x = x
  rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]

/-- The standard `K× ≃ O_K× × ℤ` decomposition attached to a filtration uniformizer. -/
noncomputable def unitsEquivNormUnitsProdInt (FF : DyadicUnitFiltration K) :
    (↥K)ˣ ≃* (↥(normUnits K) × Multiplicative ℤ) where
  toFun x := (normalizedUnit FF x, Multiplicative.ofAdd (dyadicValuation FF x))
  invFun p := p.1.1 * uniformizerK K FF ^ p.2.toAdd
  left_inv x := normalizedUnit_mul_uniformizer FF x
  right_inv p := by
    have hnorm :
        ‖((((p.1.1 * uniformizerK K FF ^ p.2.toAdd : (↥K)ˣ) : ↥K) : ℚ̄₂))‖ =
          ‖FF.π‖ ^ p.2.toAdd := by
      simp only [Units.val_mul]
      push_cast
      rw [uniformizerK_val_zpow_coe, norm_mul, norm_zpow,
        (mem_normUnits K p.1.1).mp p.1.2, one_mul]
    have hval : dyadicValuation FF (p.1.1 * uniformizerK K FF ^ p.2.toAdd) = p.2.toAdd :=
      dyadicValuation_eq_of_norm_eq_zpow FF _ _ hnorm
    apply Prod.ext
    · apply Subtype.ext
      change (p.1.1 * uniformizerK K FF ^ p.2.toAdd) *
          uniformizerK K FF ^ (-dyadicValuation FF
            (p.1.1 * uniformizerK K FF ^ p.2.toAdd)) = p.1.1
      rw [hval, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
    · exact Multiplicative.toAdd.injective hval
  map_mul' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change (x * y) * uniformizerK K FF ^ (-dyadicValuation FF (x * y)) =
        (x * uniformizerK K FF ^ (-dyadicValuation FF x)) *
          (y * uniformizerK K FF ^ (-dyadicValuation FF y))
      rw [dyadicValuation_mul, neg_add_rev, zpow_add]
      ac_rfl
    · exact Multiplicative.toAdd.injective (dyadicValuation_mul FF x y)

#print axioms unitsEquivNormUnitsProdInt

end

end GQ2.Dyadic

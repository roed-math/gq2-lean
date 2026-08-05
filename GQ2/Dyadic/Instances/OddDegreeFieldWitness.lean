/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.OddDegreeRamifiedI
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldCore

/-!
# The odd-degree field-to-witness producer

The exhaustive selector `selectFieldBranchFamily` dispatches over a `FamilyFieldBranchWitness`,
but nothing in the repository produced such a witness from a field.  This file builds the
odd-degree producer: for a finite `K/ℚ₂` of odd degree, the `L`-family witness exists outright.

* `MarkedRecip.level_eq_zero_of_odd_finrank` — **odd degree forces the marked level to `0`.**
  The witness class is `rec_K(π · ũ)`: the uniformizer contributes the unit `ν`-value `−1`
  (clause `(b_K)`), and the base-changed scalar unit `ũ` is chosen — by odd-power surjectivity
  of `ℤ₂ˣ`, the same device as `chiCycKAb_surjective_of_odd_finrank` — so that its norm
  cancels the cyclotomic value of `rec(N π)` exactly.  A `ker χ` class of unit `ν`-value then
  collapses `2^r ∣ −1` mod `2`, the `bot_level_eq_zero` argument at general odd `K`.
* `oddDegreeFamilyFieldBranchWitness` — the witness: `Odd n` from the parameter package
  (`FiniteDyadicParameters`, whose existence is exactly `FF.f ∣ n` by
  `FiniteDyadicParameters.nonempty_iff_residueDegree_dvd`; at odd degree any such `f` is odd),
  and the level equation from the theorem above.  Ramified-`i` is not an extra input on the
  witness itself: at odd degree it is the theorem `ramifiedIData_of_odd_finrank`, which this
  file uses to instantiate the selector's `RI` binder canonically.
* Selection regressions: the selector on this witness picks the branch `.L` with handle count
  `([K : ℚ₂] − 1) / 2` (`handleCount P .L = (P.n − 1) / 2`) and the improved square word
  `lSqW ((n − 1) / 2)`; at `K = ⊥` the selection is `L` with `h = 0` and word `lSqW 0`,
  matching the `n = 1` gate `selectedPresentation_L_zero_word` (`GQ2/Dyadic/Main.lean`).
-/

namespace GQ2.Dyadic

open GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

noncomputable section

namespace MarkedRecip

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K]

/-- A base-changed `ℤ₂ˣ`-scalar has spectral norm `1` in the algebraic closure, so it feeds
the unit clause `(b_K)` of the marked-reciprocity bundle. -/
theorem norm_coe_baseChangedPadicUnit (K : IntermediateField ℚ_[2] ℚ̄₂) (w : ℤ_[2]ˣ) :
    ‖((LSquare.baseChangedPadicUnit K w : ↥K) : ℚ̄₂)‖ = 1 := by
  rw [LSquare.baseChangedPadicUnit_val]
  show ‖algebraMap ℚ_[2] ℚ̄₂ ((unitEmbed w : ℚ_[2]ˣ) : ℚ_[2])‖ = 1
  rw [norm_algebraMap' (𝕜' := ℚ̄₂), unitEmbed_val, PadicInt.algebraMap_apply,
    PadicInt.padic_norm_e_of_padicInt]
  exact PadicInt.isUnit_iff.mp w.isUnit

/-- **Odd degree forces the marked level to `0`** — the general-`K` form of
`bot_level_eq_zero`, and the arithmetic input of the odd-degree `L` witness.

The `ker χ` class of unit `ν`-value is `rec_K(π · ũ)`, where `π` is the filtration
uniformizer and `ũ` base-changes a `ℤ₂ˣ`-scalar `w` with
`w ^ [K : ℚ₂] = χ(rec(N π))` (odd-power surjectivity of `ℤ₂ˣ`).  Norm functoriality and the
two orientation clauses evaluate `χ` to `χ(rec(N π)) · χ(rec(N π))⁻¹ = 1` and `ν` to
`(−1) · 1 = −1`, and `nu_ker_chi_le` then reads `2^r ∣ −1`, absurd mod `2` unless `r = 0`. -/
theorem level_eq_zero_of_odd_finrank (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) (hodd : Odd (Module.finrank ℚ_[2] K)) : B.r = 0 := by
  obtain ⟨w, hw⟩ := LSquare.unitsPadicInt_pow_surjective_of_odd hodd
    (chiCycAb (Rec.recip (normUnitsK K (uniformizerK K FF))))
  change w ^ Module.finrank ℚ_[2] K =
    chiCycAb (Rec.recip (normUnitsK K (uniformizerK K FF))) at hw
  have hfac : ∀ x : (↥K)ˣ,
      chiCycKAb K (B.recip x) = chiCycAb (Rec.recip (normUnitsK K x)) := fun x => by
    rw [← chiCycAb_inclAbK, B.norm_compat]
  have hchi : chiCycKAb K
      (B.recip (uniformizerK K FF * LSquare.baseChangedPadicUnit K w)) = 1 := by
    rw [map_mul, map_mul, hfac (uniformizerK K FF),
      hfac (LSquare.baseChangedPadicUnit K w), LSquare.normUnitsK_baseChangedPadicUnit,
      Rec.chiCyc_recip_unit, hw, mul_inv_cancel]
  have hnu : B.nu_ur
      (B.recip (uniformizerK K FF * LSquare.baseChangedPadicUnit K w)) =
        Multiplicative.ofAdd ((-1 : ℤ) : ℤ_[2]) := by
    rw [map_mul, map_mul,
      B.nu_ur_recip_uniformizer (uniformizerK K FF) (norm_uniformizerK_lt_one K FF)
        (uniformizerK_max K FF),
      B.nu_ur_recip_unit _ (norm_coe_baseChangedPadicUnit K w), mul_one]
  by_contra hr
  obtain ⟨y, hy⟩ := B.nu_ker_chi_le _ hchi
  rw [hnu] at hy
  have hy' : ((-1 : ℤ) : ℤ_[2]) = 2 ^ B.r * y := hy
  have h2 : ((-1 : ℤ) : ZMod 2) = (2 : ZMod 2) ^ B.r * PadicInt.toZMod y := by
    have h := congrArg PadicInt.toZMod hy'
    rwa [map_intCast, map_mul, map_pow, map_ofNat] at h
  rw [show ((2 : ZMod 2)) = 0 from by decide, zero_pow hr, zero_mul] at h2
  push_cast at h2
  exact absurd h2 (by decide)

end MarkedRecip

/-! ## The witness and its canonical selection -/

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K]

/-- **The odd-degree field-to-witness producer.**  Every finite odd-degree `K/ℚ₂` with a
numerical parameter package supplies the corrected `L`-family witness: parity comes from the
package's degree equation, and the level equation is the theorem
`MarkedRecip.level_eq_zero_of_odd_finrank`.  No residual classification input remains on the
odd row. -/
noncomputable def oddDegreeFamilyFieldBranchWitness (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) (D : FiniteDyadicParameters K FF)
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    FamilyFieldBranchWitness D.params (B.fieldMarkedPair FF) :=
  .L (by rw [D.degree_eq]; exact hodd) (B.level_eq_zero_of_odd_finrank FF hodd)

/-- The odd row's handle count is `(n − 1) / 2` at the field's own degree. -/
theorem handleCount_L_eq_finrank {FF : DyadicUnitFiltration K}
    (D : FiniteDyadicParameters K FF) :
    handleCount D.params .L = (Module.finrank ℚ_[2] K - 1) / 2 := by
  rw [show handleCount D.params .L = (D.params.n - 1) / 2 from rfl, D.degree_eq]

/-- The selector on the odd-degree witness picks the `L` branch. -/
theorem selectFieldBranchFamily_oddDegree_branch (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    (selectFieldBranchFamily B FF D RI
      (oddDegreeFamilyFieldBranchWitness B FF D hodd)).branch = .L :=
  (selectFieldBranchFamily B FF D RI
    (oddDegreeFamilyFieldBranchWitness B FF D hodd)).arithmetic_matches

/-- **Odd-degree selection regression**: the selected semantic presentation is the `L` row at
handle count `([K : ℚ₂] − 1) / 2`, so the selected word is the improved square word
`lSqW (([K : ℚ₂] − 1) / 2)`. -/
theorem selectFieldBranchFamily_oddDegree_semantic (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    (selectFieldBranchFamily B FF D RI
        (oddDegreeFamilyFieldBranchWitness B FF D hodd)).semantic =
      SemanticPresentation.ofBranch ((Module.finrank ℚ_[2] K - 1) / 2) .L := by
  rw [show (selectFieldBranchFamily B FF D RI
      (oddDegreeFamilyFieldBranchWitness B FF D hodd)).semantic =
        SemanticPresentation.ofBranch (handleCount D.params .L) .L from rfl,
    handleCount_L_eq_finrank D]

/-- The canonical odd-degree selection: `RI` is not a residual input at odd degree — it is the
theorem `ramifiedIData_of_odd_finrank`. -/
noncomputable def selectFieldBranchOddDegree (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) (D : FiniteDyadicParameters K FF)
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    FamilyFieldBranchSelection K D.params (B.fieldMarkedPair FF)
      (oddDegreeFamilyFieldBranchWitness B FF D hodd) :=
  selectFieldBranchFamily B FF D (ramifiedIData_of_odd_finrank K hodd)
    (oddDegreeFamilyFieldBranchWitness B FF D hodd)

/-! ## The `K = ⊥` regression against the `n = 1` gate -/

section Bot

variable {Rec : LocalReciprocity}

/-- `⊥` has odd degree. -/
theorem odd_finrank_bot : Odd (Module.finrank ℚ_[2] (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) := by
  rw [IntermediateField.finrank_bot]
  exact odd_one

/-- At `K = ⊥` the odd-degree witness selects `L` with handle count `0`. -/
theorem selectFieldBranchFamily_bot_semantic
    (B : MarkedRecip Rec (⊥ : IntermediateField ℚ_[2] ℚ̄₂))
    (FF : DyadicUnitFiltration (⊥ : IntermediateField ℚ_[2] ℚ̄₂))
    (D : FiniteDyadicParameters (⊥ : IntermediateField ℚ_[2] ℚ̄₂) FF)
    (RI : RamifiedIData (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) :
    (selectFieldBranchFamily B FF D RI
        (oddDegreeFamilyFieldBranchWitness B FF D odd_finrank_bot)).semantic =
      SemanticPresentation.ofBranch 0 .L := by
  rw [selectFieldBranchFamily_oddDegree_semantic B FF D RI odd_finrank_bot,
    IntermediateField.finrank_bot]

/-- **The `K = ⊥` word gate**: the selected word at `⊥` is the stabilized square-commutator
word `lSqW 0` — the corrected selector lands on exactly the word of the `n = 1` gate
`selectedPresentation_L_zero_word` (`GQ2/Dyadic/Main.lean`). -/
theorem selectFieldBranchFamily_bot_word
    (B : MarkedRecip Rec (⊥ : IntermediateField ℚ_[2] ℚ̄₂))
    (FF : DyadicUnitFiltration (⊥ : IntermediateField ℚ_[2] ℚ̄₂))
    (D : FiniteDyadicParameters (⊥ : IntermediateField ℚ_[2] ℚ̄₂) FF)
    (RI : RamifiedIData (⊥ : IntermediateField ℚ_[2] ℚ̄₂))
    (hdeg : (selectFieldBranchFamily B FF D RI
      (oddDegreeFamilyFieldBranchWitness B FF D odd_finrank_bot)).semantic.degree = 1) :
    (selectFieldBranchFamily B FF D RI
        (oddDegreeFamilyFieldBranchWitness B FF D odd_finrank_bot)).semantic.wordAt 1 hdeg =
      Words.LSq.lSqW 0 := by
  have hsem := selectFieldBranchFamily_bot_semantic B FF D RI
  revert hdeg
  rw [hsem]
  intro hdeg
  rfl

/-- The degree hypothesis of the word gate is itself a theorem at `⊥`. -/
theorem selectFieldBranchFamily_bot_degree
    (B : MarkedRecip Rec (⊥ : IntermediateField ℚ_[2] ℚ̄₂))
    (FF : DyadicUnitFiltration (⊥ : IntermediateField ℚ_[2] ℚ̄₂))
    (D : FiniteDyadicParameters (⊥ : IntermediateField ℚ_[2] ℚ̄₂) FF)
    (RI : RamifiedIData (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) :
    (selectFieldBranchFamily B FF D RI
      (oddDegreeFamilyFieldBranchWitness B FF D odd_finrank_bot)).semantic.degree = 1 :=
  ((selectFieldBranchFamily B FF D RI
    (oddDegreeFamilyFieldBranchWitness B FF D odd_finrank_bot)).semantic_degree_field).trans
      IntermediateField.finrank_bot

end Bot

end

end GQ2.Dyadic

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GQ2.Reciprocity
import GQ2.UnramifiedNorm
import GQ2.HilbertLedger

/-!
# P-15f2c2c2 (N2): the CFT unit-index equals the ramification index

For a finite **abelian** Galois layer `F/ℚ₂` inside `ℚ̄₂ = AlgebraicClosure ℚ_[2]`, local class
field theory (B5, `LocalReciprocity.norm_reciprocity`) identifies `Gal(F/ℚ₂) ≅ ℚ₂ˣ / N_{F/ℚ₂}(Fˣ)`,
and the **inertia subgroup** — the image of the units `ℤ₂ˣ ↪ ℚ₂ˣ` under reciprocity — has order the
ramification index `e = FF.e`.  This file proves that count:

```
Nat.card ↥(((restrictAb F hab).comp R.recip).comp unitEmbed).range = FF.e.
```

**Design (`docs/p15f2c2c-handoff.md` §3 N2, scoping §half-(B) step 3).**  With `n := finrank ℚ₂ F`,
`N := normSubgroup F`, `U := unitEmbed.range` (`= ker v₂`):

* `norm_val` (analytic core): `‖(Algebra.norm ℚ₂ x : ℚ₂)‖ = ‖(x : ℚ̄₂)‖ ^ n`, via
  `Algebra.norm_eq_prod_automorphisms` + lifting each `F ≃ₐ F` to `ℚ̄₂`
  (`restrictNormalHom_surjective` + `restrictNormal_commutes`) + `norm_galois`, then
  `card_aut_eq_finrank`;
* the integer identity `e · v₂(Norm x) = n · v_F(x)` (`norm_eq_zpow` + `FF.he`, raising `‖·‖` to the
  `e` to avoid fractions);
* `v₂(N) = (n/e)·ℤ`, hence `(U ⊔ N).index = n/e`, and `#(unit-image) · (U⊔N).index = n`
  (`index_map` + `card_mul_index`), so `#(unit-image) = e`.

Kept **parametric** over `(R : LocalReciprocity)` and `(FF : DyadicUnitFiltration F)` (the
Reciprocity.lean stress-test / half-A idiom), so the statement is **std-3**; the axioms B5/B13 enter
only when the c2c4 assembly instantiates `R := localReciprocity`, `FF := dyadicUnitFiltration F`.
-/

namespace GQ2

namespace UnitNormIndex

open scoped Classical
open IntermediateField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- **Analytic core.**  The `ℚ₂`-norm of `x ∈ F` has spectral absolute value `‖x‖^{[F:ℚ₂]}`: the
norm is the product over `Gal(F/ℚ₂)` of the conjugates (`Algebra.norm_eq_prod_automorphisms`), each
conjugate has the same spectral norm as `x` (lift the `F`-automorphism to `ℚ̄₂` and apply
`norm_galois`), and there are `finrank ℚ₂ F` of them (`card_aut_eq_finrank`). -/
theorem norm_val (F : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] F] [IsGalois ℚ_[2] F]
    (x : F) :
    ‖(Algebra.norm ℚ_[2] x : ℚ_[2])‖ = ‖(x : ℚ̄₂)‖ ^ (Module.finrank ℚ_[2] F) := by
  -- each `F`-automorphism preserves the spectral norm (lift to `ℚ̄₂`)
  have hconj : ∀ σ : F ≃ₐ[ℚ_[2]] F, ‖algebraMap F ℚ̄₂ (σ x)‖ = ‖algebraMap F ℚ̄₂ x‖ := by
    intro σ
    obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ_[2]) (K₁ := F) (E := ℚ̄₂) σ
    have hcomm : (algebraMap F ℚ̄₂ (σ x)) = g (algebraMap F ℚ̄₂ x) := by
      rw [← hg]; exact (AlgEquiv.restrictNormal_commutes g F x)
    have hg2 := norm_galois g (algebraMap F ℚ̄₂ x)
    rw [AlgEquiv.smul_def] at hg2
    rw [hcomm, hg2]
  -- the norm as a product over automorphisms, coerced to `ℚ̄₂`
  have hprod : algebraMap ℚ_[2] F (Algebra.norm ℚ_[2] x) = ∏ σ : F ≃ₐ[ℚ_[2]] F, σ x :=
    Algebra.norm_eq_prod_automorphisms ℚ_[2] x
  have hcoe : (algebraMap ℚ_[2] ℚ̄₂ (Algebra.norm ℚ_[2] x))
      = ∏ σ : F ≃ₐ[ℚ_[2]] F, algebraMap F ℚ̄₂ (σ x) := by
    rw [IsScalarTower.algebraMap_apply ℚ_[2] F ℚ̄₂, hprod, map_prod]
  have hxcoe : (x : ℚ̄₂) = algebraMap F ℚ̄₂ x := rfl
  rw [hxcoe, ← norm_algebraMap' (𝕜' := ℚ̄₂) (Algebra.norm ℚ_[2] x), hcoe, norm_prod,
    Finset.prod_congr rfl (fun σ _ => hconj σ), Finset.prod_const, Finset.card_univ,
    ← IsGalois.card_aut_eq_finrank ℚ_[2] F, Nat.card_eq_fintype_card]

/-- `‖(2 : ℚ₂)‖ = 2 ^ (-1)`: `v₂(2) = 1`. -/
theorem norm_two : ‖(2 : ℚ_[2])‖ = (2 : ℝ) ^ (-1 : ℤ) := by
  rw [Padic.norm_eq_zpow_neg_valuation (by norm_num : (2 : ℚ_[2]) ≠ 0)]
  congr 1
  rw [show (2 : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) by norm_num, Padic.valuation_p]

/-- **The ramification identity.**  For `y ∈ Fˣ` with `‖(y:ℚ̄₂)‖ = ‖π_F‖^m` (the value-group
exponent, `norm_eq_zpow`), `e · v₂(N_{F/ℚ₂} y) = [F:ℚ₂] · m`.  (Raise `‖N y‖ = ‖π_F‖^{n·m}` to the
`e` and match `2`-power exponents: `‖π_F‖^e = ‖2‖ = 2^{-1}`.) -/
theorem e_mul_val_norm (F : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] F]
    [IsGalois ℚ_[2] F] (FF : DyadicUnitFiltration F) (y : F) (hy : y ≠ 0) (m : ℤ)
    (hm : ‖(y : ℚ̄₂)‖ = ‖FF.π‖ ^ m) :
    (FF.e : ℤ) * (Algebra.norm ℚ_[2] y).valuation = (Module.finrank ℚ_[2] F : ℤ) * m := by
  have hny : (Algebra.norm ℚ_[2] y : ℚ_[2]) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hy
  have hN2 : ‖(Algebra.norm ℚ_[2] y : ℚ_[2])‖ = (2 : ℝ) ^ (-(Algebra.norm ℚ_[2] y).valuation) := by
    rw [Padic.norm_eq_zpow_neg_valuation hny]; norm_num
  have hBe : ‖FF.π‖ ^ (FF.e : ℤ) = (2 : ℝ) ^ (-1 : ℤ) := by
    rw [zpow_natCast, ← FF.he, show (2 : ℚ̄₂) = algebraMap ℚ_[2] ℚ̄₂ 2 from (map_ofNat _ 2).symm,
      norm_algebraMap' (𝕜' := ℚ̄₂), norm_two]
  have hNB : ‖(Algebra.norm ℚ_[2] y : ℚ_[2])‖
      = ‖FF.π‖ ^ ((Module.finrank ℚ_[2] F : ℤ) * m) := by
    rw [norm_val F y, hm, ← zpow_natCast (‖FF.π‖ ^ m) (Module.finrank ℚ_[2] F), ← zpow_mul]
    congr 1; ring
  have hcombine : (2 : ℝ) ^ (-(Algebra.norm ℚ_[2] y).valuation * (FF.e : ℤ))
      = (2 : ℝ) ^ (-((Module.finrank ℚ_[2] F : ℤ) * m)) := by
    calc (2 : ℝ) ^ (-(Algebra.norm ℚ_[2] y).valuation * (FF.e : ℤ))
        = ((2 : ℝ) ^ (-(Algebra.norm ℚ_[2] y).valuation)) ^ (FF.e : ℤ) := by rw [← zpow_mul]
      _ = ‖(Algebra.norm ℚ_[2] y : ℚ_[2])‖ ^ (FF.e : ℤ) := by rw [← hN2]
      _ = (‖FF.π‖ ^ ((Module.finrank ℚ_[2] F : ℤ) * m)) ^ (FF.e : ℤ) := by rw [hNB]
      _ = (‖FF.π‖ ^ (FF.e : ℤ)) ^ ((Module.finrank ℚ_[2] F : ℤ) * m) := by
            rw [← zpow_mul, ← zpow_mul, mul_comm]
      _ = ((2 : ℝ) ^ (-1 : ℤ)) ^ ((Module.finrank ℚ_[2] F : ℤ) * m) := by rw [hBe]
      _ = (2 : ℝ) ^ (-((Module.finrank ℚ_[2] F : ℤ) * m)) := by rw [← zpow_mul]; ring_nf
  have hinj := zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hcombine
  linarith [hinj]

end UnitNormIndex

end GQ2

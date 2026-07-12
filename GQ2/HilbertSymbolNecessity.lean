import GQ2.HilbertSymbolDyadic

/-!
# B7′-3 — the necessity engine and the 11 `−1`-leaves

This file is the **B7′-3 deliverable** of the `hilbertSymbol_dyadic` axiom-discharge initiative
(board `docs/b7prime-tickets.md`, plan `docs/b7prime-proof-plan.md`, §4-B7′-3; coordination with the
parallel B7′-4 lane in `docs/b7prime-b34-coordination.md`).  It provides the machinery that proves a
dyadic Hilbert symbol is `−1` — i.e. a ternary form has **no** nontrivial `ℚ₂`-zero — from a finite
mod-`2^k` obstruction, and applies it to the eleven `−1` residue leaves.

* `exists_int_triple` — clear denominators: a nontrivial `ℚ₂`-solution scales (via a common
  denominator from `IsFractionRing ℤ_[2] ℚ_[2]`) to a nontrivial `ℤ_[2]`-solution.
* `exists_primitive_triple` — the 2-adic descent: if all three coordinates are non-units they are
  all divisible by `2`; halve and recurse on the `ℕ`-measure `Σ valuationᵢ` (`valuation 0 = 0`, so
  zeros are handled uniformly), which strictly decreases.  Terminates by `Nat.strong_induction_on`.
* `not_isHilbertSolvable_of_mod` — push a **primitive** `ℤ_[2]`-solution through the ring hom
  `PadicInt.toZModPow k` (`IsUnit.map` preserves the odd coordinate), contradicting a
  `decide`-checked non-solvability over `ZMod (2^k)`.
* the **11 `−1`-leaves**, each a `decide` at `k = 3` (`ZMod 8`, 512 triples, plain `decide`).

Necessity never touches the Hensel square criterion, so this file imports `GQ2.HilbertSymbolDyadic`
only (the shared coercion helpers `unit2_coe` / `unitCoe_coe` live there).
-/

namespace GQ2.HilbertSymbol

open scoped Classical
open PadicInt

/-! ## Integralization: a `ℚ₂`-solution scales into `ℤ_[2]` -/

/-- **Integralization.**  A nontrivial `ℚ₂`-zero of `A X² + B Y² − Z²` (with `A, B ∈ ℤ_[2]`) scales,
by a common denominator, to a nontrivial `ℤ_[2]`-zero. -/
theorem exists_int_triple {A B : ℤ_[2]} (h : IsHilbertSolvable (A : ℚ_[2]) (B : ℚ_[2])) :
    ∃ x y z : ℤ_[2], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ A * x ^ 2 + B * y ^ 2 = z ^ 2 := by
  obtain ⟨x, y, z, hne, heq⟩ := h
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ_[2])
      ({x, y, z} : Finset ℚ_[2]) id
  obtain ⟨x', hx'⟩ := hb x (by simp)
  obtain ⟨y', hy'⟩ := hb y (by simp)
  obtain ⟨z', hz'⟩ := hb z (by simp)
  simp only [id_eq, Algebra.smul_def] at hx' hy' hz'
  set c : ℚ_[2] := algebraMap ℤ_[2] ℚ_[2] (b : ℤ_[2]) with hc
  have hcne : c ≠ 0 := by
    rw [hc, ne_eq, map_eq_zero_iff _ (IsFractionRing.injective ℤ_[2] ℚ_[2])]
    exact nonZeroDivisors.coe_ne_zero b
  have key : ∀ (w : ℚ_[2]) (w' : ℤ_[2]), algebraMap ℤ_[2] ℚ_[2] w' = c * w → w ≠ 0 → w' ≠ 0 := by
    intro w w' hw hwne hw'0
    refine hwne ((mul_eq_zero.mp ?_).resolve_left hcne)
    rw [← hw, hw'0, map_zero]
  refine ⟨x', y', z', ?_, ?_⟩
  · exact hne.imp (key x x' hx') (Or.imp (key y y' hy') (key z z' hz'))
  · apply IsFractionRing.injective ℤ_[2] ℚ_[2]
    have heq' : algebraMap ℤ_[2] ℚ_[2] A * x ^ 2 + algebraMap ℤ_[2] ℚ_[2] B * y ^ 2 = z ^ 2 := heq
    rw [map_add, map_mul, map_mul, map_pow, map_pow, map_pow, hx', hy', hz']
    linear_combination c ^ 2 * heq'

/-! ## The 2-adic descent to a primitive solution -/

/-- **Primitivity descent.**  A nontrivial `ℤ_[2]`-solution has a **primitive** one — with some
coordinate a unit.  If none is a unit, all are divisible by `2`; halving strictly drops the measure
`Σ valuation`. -/
theorem exists_primitive_triple {A B : ℤ_[2]}
    (h : ∃ x y z : ℤ_[2], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ A * x ^ 2 + B * y ^ 2 = z ^ 2) :
    ∃ x y z : ℤ_[2], (IsUnit x ∨ IsUnit y ∨ IsUnit z) ∧ A * x ^ 2 + B * y ^ 2 = z ^ 2 := by
  obtain ⟨x₀, y₀, z₀, hne₀, heq₀⟩ := h
  have nonunit_two_dvd : ∀ c : ℤ_[2], ¬ IsUnit c → (2 : ℤ_[2]) ∣ c := by
    intro c hc
    have hlt : ‖c‖ < 1 :=
      lt_of_le_of_ne (PadicInt.norm_le_one c) (by rwa [PadicInt.isUnit_iff] at hc)
    simpa using (PadicInt.norm_lt_one_iff_dvd c).mp hlt
  have vstep : ∀ c : ℤ_[2], c ≠ 0 → (2 * c).valuation = c.valuation + 1 := by
    intro c hc
    have hh := PadicInt.valuation_p_pow_mul (p := 2) 1 c hc
    simp only [pow_one] at hh
    rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_num, hh]; omega
  have main : ∀ (n : ℕ) (x y z : ℤ_[2]), x.valuation + y.valuation + z.valuation = n →
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) → A * x ^ 2 + B * y ^ 2 = z ^ 2 →
      ∃ x' y' z' : ℤ_[2], (IsUnit x' ∨ IsUnit y' ∨ IsUnit z') ∧ A * x' ^ 2 + B * y' ^ 2 = z' ^ 2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x y z hM hne heq
      by_cases hprim : IsUnit x ∨ IsUnit y ∨ IsUnit z
      · exact ⟨x, y, z, hprim, heq⟩
      · rw [not_or, not_or] at hprim
        obtain ⟨hx, hy, hz⟩ := hprim
        obtain ⟨x₁, hx₁⟩ := nonunit_two_dvd x hx
        obtain ⟨y₁, hy₁⟩ := nonunit_two_dvd y hy
        obtain ⟨z₁, hz₁⟩ := nonunit_two_dvd z hz
        have heq₁ : A * x₁ ^ 2 + B * y₁ ^ 2 = z₁ ^ 2 := by
          have h4 : (4 : ℤ_[2]) * (A * x₁ ^ 2 + B * y₁ ^ 2) = 4 * z₁ ^ 2 := by
            rw [hx₁, hy₁, hz₁] at heq; linear_combination heq
          exact mul_left_cancel₀ (by norm_num : (4 : ℤ_[2]) ≠ 0) h4
        have hne₁ : x₁ ≠ 0 ∨ y₁ ≠ 0 ∨ z₁ ≠ 0 := by
          rcases hne with hh | hh | hh
          · exact Or.inl fun h0 => hh (by rw [hx₁, h0, mul_zero])
          · exact Or.inr <| Or.inl fun h0 => hh (by rw [hy₁, h0, mul_zero])
          · exact Or.inr <| Or.inr fun h0 => hh (by rw [hz₁, h0, mul_zero])
        have hlt : x₁.valuation + y₁.valuation + z₁.valuation < n := by
          rw [← hM, hx₁, hy₁, hz₁]
          have mono : ∀ c : ℤ_[2], c.valuation ≤ (2 * c).valuation := by
            intro c
            by_cases hc : c = 0
            · simp [hc, PadicInt.valuation_zero]
            · rw [vstep c hc]; omega
          have strict : ∀ c : ℤ_[2], c ≠ 0 → c.valuation < (2 * c).valuation := by
            intro c hc; rw [vstep c hc]; omega
          rcases hne₁ with hh | hh | hh
          · have := strict x₁ hh; have := mono y₁; have := mono z₁; omega
          · have := mono x₁; have := strict y₁ hh; have := mono z₁; omega
          · have := mono x₁; have := mono y₁; have := strict z₁ hh; omega
        exact ih _ hlt x₁ y₁ z₁ rfl hne₁ heq₁
  exact main _ x₀ y₀ z₀ rfl hne₀ heq₀

/-! ## The mod-`2^k` obstruction -/

/-- **Non-solvability from a finite obstruction.**  If `A X² + B Y² = Z²` has no primitive solution
over `ZMod (2^k)` (some coordinate a unit), it has no nontrivial `ℚ₂`-solution: integralize,
primitivize, and push through the ring hom `PadicInt.toZModPow k` (which sends the unit coordinate to
a unit by `IsUnit.map`). -/
theorem not_isHilbertSolvable_of_mod (A B : ℤ_[2]) (k : ℕ)
    (hk : ∀ x y z : ZMod (2 ^ k), (IsUnit x ∨ IsUnit y ∨ IsUnit z) →
      PadicInt.toZModPow k A * x ^ 2 + PadicInt.toZModPow k B * y ^ 2 ≠ z ^ 2) :
    ¬ IsHilbertSolvable (A : ℚ_[2]) (B : ℚ_[2]) := by
  intro hsolv
  obtain ⟨x, y, z, hprim, heq⟩ := exists_primitive_triple (exists_int_triple hsolv)
  refine hk (PadicInt.toZModPow k x) (PadicInt.toZModPow k y) (PadicInt.toZModPow k z) ?_ ?_
  · exact hprim.imp (·.map (PadicInt.toZModPow k))
      (Or.imp (·.map (PadicInt.toZModPow k)) (·.map (PadicInt.toZModPow k)))
  · simpa only [map_add, map_mul, map_pow] using congrArg (PadicInt.toZModPow k) heq

/-! ## The two `−1`-leaf families

Both reduce `hilbertSymbol … = -1` to a `decide`-checked non-solvability over `ZMod 8`, threading
the axiom's `unitCoe`/`unit2` wrappers through `unitCoe_coe`/`unit2_coe`.  The `decide` obligation is
passed as `hdec` so each concrete leaf below supplies it by `by decide` (512 triples, no
`native_decide`). -/

/-- Unit·unit `−1`-leaf: `(u, v)₂ = -1` at residues `(ru, rv)` for which `ru x² + rv y² = z²` has no
primitive `ZMod 8` solution. -/
theorem hilbertSymbol_uu_eq_neg_one {ru rv : ZMod 8}
    (hdec : ∀ x y z : ZMod 8, (IsUnit x ∨ IsUnit y ∨ IsUnit z) → ru * x ^ 2 + rv * y ^ 2 ≠ z ^ 2)
    (u v : ℤ_[2]ˣ) (hu : PadicInt.toZModPow 3 (u : ℤ_[2]) = ru)
    (hv : PadicInt.toZModPow 3 (v : ℤ_[2]) = rv) :
    hilbertSymbol (unitCoe u) (unitCoe v) = -1 := by
  have hns : ¬ IsHilbertSolvable ((unitCoe u : ℚ_[2]ˣ) : ℚ_[2]) ((unitCoe v : ℚ_[2]ˣ) : ℚ_[2]) := by
    rw [unitCoe_coe, unitCoe_coe]
    refine not_isHilbertSolvable_of_mod (u : ℤ_[2]) (v : ℤ_[2]) 3 ?_
    rw [hu, hv]; exact hdec
  rw [hilbertSymbol, if_neg hns]

/-- `(u, 2v)` `−1`-leaf: `(u, 2v)₂ = -1` at residues `(ru, rv)` for which `ru x² + 2 rv y² = z²` has
no primitive `ZMod 8` solution. -/
theorem hilbertSymbol_u2v_eq_neg_one {ru rv : ZMod 8}
    (hdec : ∀ x y z : ZMod 8, (IsUnit x ∨ IsUnit y ∨ IsUnit z) →
      ru * x ^ 2 + 2 * rv * y ^ 2 ≠ z ^ 2)
    (u v : ℤ_[2]ˣ) (hu : PadicInt.toZModPow 3 (u : ℤ_[2]) = ru)
    (hv : PadicInt.toZModPow 3 (v : ℤ_[2]) = rv) :
    hilbertSymbol (unitCoe u) (unit2 * unitCoe v) = -1 := by
  have hns : ¬ IsHilbertSolvable ((unitCoe u : ℚ_[2]ˣ) : ℚ_[2])
      ((unit2 * unitCoe v : ℚ_[2]ˣ) : ℚ_[2]) := by
    rw [unitCoe_coe,
      show ((unit2 * unitCoe v : ℚ_[2]ˣ) : ℚ_[2]) = ((2 * (v : ℤ_[2]) : ℤ_[2]) : ℚ_[2]) from by
        rw [Units.val_mul, unit2_coe, unitCoe_coe]; norm_cast]
    refine not_isHilbertSolvable_of_mod (u : ℤ_[2]) (2 * (v : ℤ_[2])) 3 ?_
    rw [map_mul, map_ofNat, hu, hv]; exact hdec
  rw [hilbertSymbol, if_neg hns]

/-! ## The 11 `−1`-leaves (plan §1 inventory; each `decide` at `ZMod 8`)

Unit·unit: `{3,3}, {3,7}, {7,7}`.  `(u, 2v)`: `u₀=3, v₀∈{1,5}`; `u₀=5, v₀∈{1,3,5,7}`;
`u₀=7, v₀∈{3,7}`.  The `by decide` on each certifies it is a genuine mod-8 `−1` leaf. -/

theorem leaf_uu_3_3 (u v : ℤ_[2]ˣ)
    (hu : PadicInt.toZModPow 3 (u : ℤ_[2]) = 3) (hv : PadicInt.toZModPow 3 (v : ℤ_[2]) = 3) :
    hilbertSymbol (unitCoe u) (unitCoe v) = -1 :=
  hilbertSymbol_uu_eq_neg_one (by decide) u v hu hv

theorem leaf_uu_3_7 (u v : ℤ_[2]ˣ)
    (hu : PadicInt.toZModPow 3 (u : ℤ_[2]) = 3) (hv : PadicInt.toZModPow 3 (v : ℤ_[2]) = 7) :
    hilbertSymbol (unitCoe u) (unitCoe v) = -1 :=
  hilbertSymbol_uu_eq_neg_one (by decide) u v hu hv

theorem leaf_uu_7_7 (u v : ℤ_[2]ˣ)
    (hu : PadicInt.toZModPow 3 (u : ℤ_[2]) = 7) (hv : PadicInt.toZModPow 3 (v : ℤ_[2]) = 7) :
    hilbertSymbol (unitCoe u) (unitCoe v) = -1 :=
  hilbertSymbol_uu_eq_neg_one (by decide) u v hu hv

theorem leaf_u2v_3_1 (u v : ℤ_[2]ˣ)
    (hu : PadicInt.toZModPow 3 (u : ℤ_[2]) = 3) (hv : PadicInt.toZModPow 3 (v : ℤ_[2]) = 1) :
    hilbertSymbol (unitCoe u) (unit2 * unitCoe v) = -1 :=
  hilbertSymbol_u2v_eq_neg_one (by decide) u v hu hv

theorem leaf_u2v_3_5 (u v : ℤ_[2]ˣ)
    (hu : PadicInt.toZModPow 3 (u : ℤ_[2]) = 3) (hv : PadicInt.toZModPow 3 (v : ℤ_[2]) = 5) :
    hilbertSymbol (unitCoe u) (unit2 * unitCoe v) = -1 :=
  hilbertSymbol_u2v_eq_neg_one (by decide) u v hu hv

theorem leaf_u2v_5_1 (u v : ℤ_[2]ˣ)
    (hu : PadicInt.toZModPow 3 (u : ℤ_[2]) = 5) (hv : PadicInt.toZModPow 3 (v : ℤ_[2]) = 1) :
    hilbertSymbol (unitCoe u) (unit2 * unitCoe v) = -1 :=
  hilbertSymbol_u2v_eq_neg_one (by decide) u v hu hv

theorem leaf_u2v_5_3 (u v : ℤ_[2]ˣ)
    (hu : PadicInt.toZModPow 3 (u : ℤ_[2]) = 5) (hv : PadicInt.toZModPow 3 (v : ℤ_[2]) = 3) :
    hilbertSymbol (unitCoe u) (unit2 * unitCoe v) = -1 :=
  hilbertSymbol_u2v_eq_neg_one (by decide) u v hu hv

theorem leaf_u2v_5_5 (u v : ℤ_[2]ˣ)
    (hu : PadicInt.toZModPow 3 (u : ℤ_[2]) = 5) (hv : PadicInt.toZModPow 3 (v : ℤ_[2]) = 5) :
    hilbertSymbol (unitCoe u) (unit2 * unitCoe v) = -1 :=
  hilbertSymbol_u2v_eq_neg_one (by decide) u v hu hv

theorem leaf_u2v_5_7 (u v : ℤ_[2]ˣ)
    (hu : PadicInt.toZModPow 3 (u : ℤ_[2]) = 5) (hv : PadicInt.toZModPow 3 (v : ℤ_[2]) = 7) :
    hilbertSymbol (unitCoe u) (unit2 * unitCoe v) = -1 :=
  hilbertSymbol_u2v_eq_neg_one (by decide) u v hu hv

theorem leaf_u2v_7_3 (u v : ℤ_[2]ˣ)
    (hu : PadicInt.toZModPow 3 (u : ℤ_[2]) = 7) (hv : PadicInt.toZModPow 3 (v : ℤ_[2]) = 3) :
    hilbertSymbol (unitCoe u) (unit2 * unitCoe v) = -1 :=
  hilbertSymbol_u2v_eq_neg_one (by decide) u v hu hv

theorem leaf_u2v_7_7 (u v : ℤ_[2]ˣ)
    (hu : PadicInt.toZModPow 3 (u : ℤ_[2]) = 7) (hv : PadicInt.toZModPow 3 (v : ℤ_[2]) = 7) :
    hilbertSymbol (unitCoe u) (unit2 * unitCoe v) = -1 :=
  hilbertSymbol_u2v_eq_neg_one (by decide) u v hu hv

end GQ2.HilbertSymbol

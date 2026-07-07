import GQ2.DeepCount
import GQ2.UnitFiltration

/-!
# P-15f2c2c (half A): the analytic `hunram` from equal value groups

The involution vanish route of P-15f2 (`SectionSix.lemma_6_17_vanish`) threads, through
`ShapiroDeepness.hvanish_involution` / `hvanish_involution_of_deepClass` and ultimately
`SectionSix.lemma_6_16` / `HilbertLedger.cup_unramified_unit`, the **analytic `hunram`**
hypothesis

```
∀ x : ℚ̄₂, x ≠ 0 → x ∈ L → ∃ y : ℚ̄₂, y ≠ 0 ∧ y ∈ k ∧ ‖x‖ = ‖y‖,
```

i.e. the value groups of the tower `k ≤ L` coincide (`‖L^×‖ = ‖k^×‖`) — the statement that
`L/k` is **unramified**, in the repo's spectral-norm vocabulary (no valuation ring / residue
field; see B13's convention).

This file is **half (A)** of P-15f2c2c (`docs/p15f2c2c-scoping.md`): given the B13
`DyadicUnitFiltration` data of `k` and `L` and the unramifiedness datum in norm vocabulary —
**equal uniformizer norm** `‖π_L‖ = ‖π_k‖` (equivalently equal absolute ramification index
`e_L = e_k`) — the analytic `hunram` holds.  The remaining **half (B)** — deriving
`‖π_L‖ = ‖π_k‖` from the group-level datum `ρ(ĝ) ∉ inertia` (c2b Step-0) — is the flagged leaf
decision (axiom-vs-derive, owner sign-off); it is **not** in this file.

The core is `exists_nat_val` (`GQ2/DeepCount.lean`): B13 discreteness (`hπ_max`) makes every
nonzero `k`-integral element's norm an exact power of `‖π‖`.  We lift it to a `ℤ`-power
(`norm_eq_zpow`, handling `‖x‖ > 1` via `x⁻¹`) and transport across the equal uniformizer norm.
-/

namespace GQ2

namespace UnramifiedNorm

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- **Value-group generation.**  With a B13 uniformizer `π` for `k` (discreteness `hπ_max`),
every nonzero `x ∈ k` has norm an integer power of `‖π‖`.  For `‖x‖ ≤ 1` this is
`exists_nat_val`; for `‖x‖ > 1` apply it to `x⁻¹ ∈ k` and negate the exponent. -/
theorem norm_eq_zpow {k : IntermediateField ℚ_[2] ℚ̄₂} (F : DyadicUnitFiltration k)
    {x : ℚ̄₂} (hx : x ∈ k) (hx0 : x ≠ 0) :
    ∃ n : ℤ, ‖x‖ = ‖F.π‖ ^ n := by
  rcases le_or_gt ‖x‖ 1 with h1 | h1
  · obtain ⟨m, hm⟩ :=
      exists_nat_val k F.π F.hπ_mem F.hπ_ne F.hπ_lt F.hπ_max hx hx0 h1
    exact ⟨(m : ℤ), by rw [hm, zpow_natCast]⟩
  · have hxinv : x⁻¹ ∈ k := k.inv_mem hx
    have hxinv0 : x⁻¹ ≠ 0 := inv_ne_zero hx0
    have hnorm : ‖x⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact le_of_lt (inv_lt_one_of_one_lt₀ h1)
    obtain ⟨m, hm⟩ :=
      exists_nat_val k F.π F.hπ_mem F.hπ_ne F.hπ_lt F.hπ_max hxinv hxinv0 hnorm
    refine ⟨-(m : ℤ), ?_⟩
    rw [norm_inv] at hm
    rw [zpow_neg, zpow_natCast, ← hm, inv_inv]

/-- **c2c-A: the analytic `hunram` from equal uniformizer norm.**  Given B13 filtration data for
`k` and `L` with `‖π_L‖ = ‖π_k‖` (the unramifiedness datum in norm vocabulary), every nonzero
`x ∈ L` has the same norm as some nonzero `y ∈ k` — namely `y = π_k^n` where `‖x‖ = ‖π_L‖^n`.
This is exactly the `hunram` hypothesis of `SectionSix.lemma_6_16` /
`ShapiroDeepness.hvanish_involution`. -/
theorem hunram_of_uniformizer_norm_eq {k L : IntermediateField ℚ_[2] ℚ̄₂}
    (Fk : DyadicUnitFiltration k) (FL : DyadicUnitFiltration L)
    (hπ : ‖FL.π‖ = ‖Fk.π‖) :
    ∀ x : ℚ̄₂, x ≠ 0 → x ∈ L → ∃ y : ℚ̄₂, y ≠ 0 ∧ y ∈ k ∧ ‖x‖ = ‖y‖ := by
  intro x hx0 hxL
  obtain ⟨n, hn⟩ := norm_eq_zpow FL hxL hx0
  refine ⟨Fk.π ^ n, zpow_ne_zero n Fk.hπ_ne, zpow_mem Fk.hπ_mem n, ?_⟩
  rw [hn, norm_zpow, hπ]

/-- **Equal absolute ramification index ⟹ equal uniformizer norm.**  Both uniformizers satisfy
`‖2‖ = ‖π‖^e` (`he`), so equal `e` forces equal `‖π‖` (positive `e`-th roots of the same
`‖2‖ ∈ (0,1)`).  Lets half (B) supply the unramifiedness datum in the conceptually-cleaner
`e_L = e_k` form. -/
theorem uniformizer_norm_eq_of_e_eq {k L : IntermediateField ℚ_[2] ℚ̄₂}
    (Fk : DyadicUnitFiltration k) (FL : DyadicUnitFiltration L) (he : FL.e = Fk.e) :
    ‖FL.π‖ = ‖Fk.π‖ := by
  have h2 : ‖FL.π‖ ^ FL.e = ‖Fk.π‖ ^ Fk.e := by rw [← FL.he, ← Fk.he]
  rw [he] at h2
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _)
    (Nat.one_le_iff_ne_zero.mp Fk.he_pos)).mp h2

/-- **c2c-A in the `e`-form.**  The analytic `hunram` from equal absolute ramification index. -/
theorem hunram_of_e_eq {k L : IntermediateField ℚ_[2] ℚ̄₂}
    (Fk : DyadicUnitFiltration k) (FL : DyadicUnitFiltration L) (he : FL.e = Fk.e) :
    ∀ x : ℚ̄₂, x ≠ 0 → x ∈ L → ∃ y : ℚ̄₂, y ≠ 0 ∧ y ∈ k ∧ ‖x‖ = ‖y‖ :=
  hunram_of_uniformizer_norm_eq Fk FL (uniformizer_norm_eq_of_e_eq Fk FL he)

end UnramifiedNorm

end GQ2

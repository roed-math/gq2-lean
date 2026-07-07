import GQ2.UnramifiedNorm
import GQ2.HilbertLedger

/-!
# P-15f2c2c1 (N1): the Galois coset-norm kit + the relative ramification index

Two axiom-free kits feeding the c2c4 assembly of the analytic `hunram` (`docs/p15f2c2c-handoff.md`).

**Part 1 — the coset norm.**  For `H ≤ K` closed subgroups of `Gal(ℚ̄₂/ℚ₂)` with finite index
`[K : H]`, the product `cosetNorm H K x = ∏_{c ∈ K ⧸ H} (out c) • x` of the `K`-cosets of `H`
applied to `x`:
* is `K`-invariant, hence lands in `fixedField K`, when `x ∈ fixedField H` (`cosetNorm_mem`);
* has spectral norm `‖cosetNorm H K x‖ = ‖x‖ ^ [K : H]` (`norm_cosetNorm`, from `norm_galois`).

So for a tower `k ≤ L` (`H = L.fixingSubgroup ≤ K = k.fixingSubgroup`) it realizes
`‖x‖ ^ [L : k] ∈ ‖k^×‖` for every `x ∈ L^×` — the input to Part 2's divisibility.

**Part 2 — the relative ramification index.**  Over B13 `DyadicUnitFiltration` data (kept as
hypotheses, half-A idiom, so statements stay axiom-free), for a tower `F ≤ L`: `relE` with
`‖π_F‖ = ‖π_L‖ ^ relE`, the tower formula `e_L = relE * e_F`, and the divisibility
`relE ∣ n` whenever `‖x‖ ^ n ∈ ‖F^×‖` for all `x ∈ L^×`.  c2c4 instantiates twice
(`[L : k] ⟹ relE ∣ 2`, `⟨t⟩-orbit ⟹ relE ∣ r`).

Axiom-free throughout (`Ax = ∅`, std-3).
-/

namespace GQ2

namespace GaloisCosetNorm

open IntermediateField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## Part 1 — the coset norm -/

section CosetNorm

variable {H K : Subgroup (Kummer.GaloisGroup ℚ_[2])} [Fintype (↥K ⧸ H.subgroupOf K)]

/-- The **coset norm**: the product over the `K`-cosets of `H` of the coset representatives
applied to `x`.  Uses `Quotient.out` representatives; the value is representative-independent on
`fixedField H` (`smul_eq_of_quot_eq`). -/
noncomputable def cosetNorm (H K : Subgroup (Kummer.GaloisGroup ℚ_[2]))
    [Fintype (↥K ⧸ H.subgroupOf K)] (x : ℚ̄₂) : ℚ̄₂ :=
  ∏ c : ↥K ⧸ H.subgroupOf K, (↑(Quotient.out c) : Kummer.GaloisGroup ℚ_[2]) • x

omit [Fintype (↥K ⧸ H.subgroupOf K)] in
/-- **Representative independence** (the well-definedness (i)): on `fixedField H`, two elements of
`K` in the same `H`-coset act identically. -/
theorem smul_eq_of_quot_eq {x : ℚ̄₂} (hx : x ∈ fixedField H) {g₁ g₂ : ↥K}
    (h : (QuotientGroup.mk g₁ : ↥K ⧸ H.subgroupOf K) = QuotientGroup.mk g₂) :
    (↑g₁ : Kummer.GaloisGroup ℚ_[2]) • x = (↑g₂ : Kummer.GaloisGroup ℚ_[2]) • x := by
  rw [QuotientGroup.eq] at h
  have hmem : (↑(g₁⁻¹ * g₂) : Kummer.GaloisGroup ℚ_[2]) ∈ H := (Subgroup.mem_subgroupOf).mp h
  have hfix : (↑(g₁⁻¹ * g₂) : Kummer.GaloisGroup ℚ_[2]) • x = x :=
    (mem_fixedField_iff H x).mp hx _ hmem
  have hcoe : (↑g₁ : Kummer.GaloisGroup ℚ_[2]) * ↑(g₁⁻¹ * g₂) = ↑g₂ := by
    rw [← Subgroup.coe_mul, mul_inv_cancel_left]
  have : (↑g₂ : Kummer.GaloisGroup ℚ_[2]) • x
      = (↑g₁ : Kummer.GaloisGroup ℚ_[2]) • ((↑(g₁⁻¹ * g₂) : Kummer.GaloisGroup ℚ_[2]) • x) := by
    rw [← mul_smul, hcoe]
  rw [this, hfix]

/-- Each factor is nonzero, so the coset norm of a nonzero element is nonzero. -/
theorem cosetNorm_ne_zero {x : ℚ̄₂} (hx : x ≠ 0) : cosetNorm H K x ≠ 0 := by
  rw [cosetNorm]
  refine Finset.prod_ne_zero_iff.mpr fun c _ => ?_
  rw [AlgEquiv.smul_def]
  exact (map_ne_zero _).mpr hx

/-- **(iii) the norm formula**: `‖cosetNorm‖ = ‖x‖ ^ [K : H]` (each factor is `‖x‖` by
`norm_galois`). -/
theorem norm_cosetNorm (x : ℚ̄₂) :
    ‖cosetNorm H K x‖ = ‖x‖ ^ Nat.card (↥K ⧸ H.subgroupOf K) := by
  rw [cosetNorm, norm_prod]
  simp only [norm_galois]
  rw [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]

/-- **(ii) `K`-invariance**: on `fixedField H` the coset norm lands in `fixedField K`
(left multiplication by `g ∈ K` permutes the cosets, and the finite product is reordered). -/
theorem cosetNorm_mem {x : ℚ̄₂} (hx : x ∈ fixedField H) :
    cosetNorm H K x ∈ fixedField K := by
  haveI hqa : MulAction.QuotientAction (↥K) (H.subgroupOf K) :=
    MulAction.left_quotientAction (H.subgroupOf K)
  letI : MulAction (↥K) (↥K ⧸ H.subgroupOf K) := MulAction.quotient (↥K) (H.subgroupOf K)
  rw [mem_fixedField_iff]
  intro g hg
  rw [cosetNorm, map_prod,
    ← Equiv.prod_comp (MulAction.toPerm (⟨g, hg⟩ : ↥K))
      (fun c : ↥K ⧸ H.subgroupOf K => (↑(Quotient.out c) : Kummer.GaloisGroup ℚ_[2]) • x)]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  -- `g (out c • x) = out (κ • c) • x`, both reps of the coset `κ • c`
  have hclass : (QuotientGroup.mk ((⟨g, hg⟩ : ↥K) * Quotient.out c) : ↥K ⧸ H.subgroupOf K)
      = QuotientGroup.mk (Quotient.out ((MulAction.toPerm (⟨g, hg⟩ : ↥K)) c)) := by
    rw [QuotientGroup.out_eq']
    show (QuotientGroup.mk ((⟨g, hg⟩ : ↥K) • Quotient.out c) : ↥K ⧸ H.subgroupOf K)
        = (⟨g, hg⟩ : ↥K) • c
    rw [MulAction.Quotient.mk_smul_out]
  have key := smul_eq_of_quot_eq hx hclass
  rw [Subgroup.coe_mul] at key
  rw [← key, ← AlgEquiv.smul_def, ← mul_smul]

/-- **c2c4-facing package**: for a nonzero `x ∈ fixedField H`, the power `‖x‖ ^ [K : H]` is the
spectral norm of a nonzero element of `fixedField K` (the coset norm).  This is the
`‖x‖ ^ n ∈ ‖(fixedField K)^×‖` input consumed by `relE_dvd`. -/
theorem exists_mem_fixedField_norm_pow {x : ℚ̄₂} (hx : x ∈ fixedField H) (hx0 : x ≠ 0) :
    ∃ y : ℚ̄₂, y ∈ fixedField K ∧ y ≠ 0 ∧ ‖x‖ ^ Nat.card (↥K ⧸ H.subgroupOf K) = ‖y‖ :=
  ⟨cosetNorm H K x, cosetNorm_mem hx, cosetNorm_ne_zero hx0, (norm_cosetNorm x).symm⟩

end CosetNorm

/-! ## Part 2 — the relative ramification index of a tower `F ≤ L` -/

section RelE

open UnramifiedNorm

variable {F L : IntermediateField ℚ_[2] ℚ̄₂}

/-- The **relative ramification index** `e(L/F)` of a tower `F ≤ L`, in norm vocabulary: the
integer `m` with `‖π_F‖ = ‖π_L‖ ^ m` (it exists by `norm_eq_zpow`, as `π_F ∈ F ≤ L`). -/
noncomputable def relE (FF : DyadicUnitFiltration F) (FL : DyadicUnitFiltration L) (hFL : F ≤ L) :
    ℤ :=
  (norm_eq_zpow FL (hFL FF.hπ_mem) FF.hπ_ne).choose

/-- Defining property of `relE`: `‖π_F‖ = ‖π_L‖ ^ e(L/F)`. -/
theorem relE_spec (FF : DyadicUnitFiltration F) (FL : DyadicUnitFiltration L) (hFL : F ≤ L) :
    ‖FF.π‖ = ‖FL.π‖ ^ relE FF FL hFL :=
  (norm_eq_zpow FL (hFL FF.hπ_mem) FF.hπ_ne).choose_spec

/-- **Tower multiplicativity of the absolute ramification index**: `e_L = e(L/F) · e_F` (both
uniformizers meet `‖2‖ = ‖π‖^e`, and `‖π_F‖ = ‖π_L‖^{e(L/F)}`; zpow-injectivity on `‖π_L‖ ∈ (0,1)`). -/
theorem e_eq_relE_mul (FF : DyadicUnitFiltration F) (FL : DyadicUnitFiltration L) (hFL : F ≤ L) :
    (FL.e : ℤ) = relE FF FL hFL * FF.e := by
  have hb0 : (0 : ℝ) < ‖FL.π‖ := norm_pos_iff.mpr FL.hπ_ne
  have hb1 : ‖FL.π‖ ≠ 1 := ne_of_lt FL.hπ_lt
  have hEq : ‖FL.π‖ ^ (FL.e : ℤ) = ‖FL.π‖ ^ (relE FF FL hFL * FF.e) := by
    rw [zpow_natCast, ← FL.he, FF.he, relE_spec FF FL hFL,
      ← zpow_natCast (‖FL.π‖ ^ relE FF FL hFL) FF.e, ← zpow_mul]
  exact zpow_right_injective₀ hb0 hb1 hEq

/-- `e(L/F) ≥ 1` (a genuine relative index): from tower multiplicativity and `e_L, e_F ≥ 1`. -/
theorem relE_pos (FF : DyadicUnitFiltration F) (FL : DyadicUnitFiltration L) (hFL : F ≤ L) :
    1 ≤ relE FF FL hFL := by
  have h := e_eq_relE_mul FF FL hFL
  have heL : 1 ≤ (FL.e : ℤ) := by exact_mod_cast FL.he_pos
  have heF : 1 ≤ (FF.e : ℤ) := by exact_mod_cast FF.he_pos
  by_contra hlt
  rw [not_le] at hlt
  nlinarith [h, heL, heF, mul_nonneg (by omega : (0 : ℤ) ≤ -relE FF FL hFL)
    (by omega : (0 : ℤ) ≤ (FF.e : ℤ))]

/-- **The divisibility feeding c2c4**: if `‖x‖ ^ n` lies in `‖(fixedField F)^×‖` for every
`x ∈ L^×`, then `e(L/F) ∣ n`.  (Test at `x = π_L`: `‖π_L‖^n = ‖π_F‖^a = ‖π_L‖^{e(L/F)·a}`.) -/
theorem relE_dvd (FF : DyadicUnitFiltration F) (FL : DyadicUnitFiltration L) (hFL : F ≤ L)
    {n : ℕ} (hn : ∀ x : ℚ̄₂, x ≠ 0 → x ∈ L → ∃ y : ℚ̄₂, y ≠ 0 ∧ y ∈ F ∧ ‖x‖ ^ n = ‖y‖) :
    relE FF FL hFL ∣ (n : ℤ) := by
  obtain ⟨y, hy0, hyF, hxy⟩ := hn FL.π FL.hπ_ne FL.hπ_mem
  obtain ⟨a, ha⟩ := norm_eq_zpow FF hyF hy0
  refine ⟨a, ?_⟩
  have hb0 : (0 : ℝ) < ‖FL.π‖ := norm_pos_iff.mpr FL.hπ_ne
  have hb1 : ‖FL.π‖ ≠ 1 := ne_of_lt FL.hπ_lt
  have hEq : ‖FL.π‖ ^ (n : ℤ) = ‖FL.π‖ ^ (relE FF FL hFL * a) := by
    rw [zpow_natCast, hxy, ha, relE_spec FF FL hFL, ← zpow_mul]
  exact zpow_right_injective₀ hb0 hb1 hEq

end RelE

end GaloisCosetNorm

end GQ2

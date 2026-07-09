import GQ2.UnitFiltration

/-!
# B13-1 + B13-2 — the topology layer and the uniformizer

This is the **B13-1 + B13-2 deliverable** (lane A) of the `dyadicUnitFiltration` axiom-discharge
initiative (board `docs/b13-tickets.md`, plan `docs/b13-proof-plan.md`).

**B13-1 (topology).**  The compact unit ball `O = {‖x‖ ≤ 1}` of a finite extension `k/ℚ₂` (a
bundled `OpenAddSubgroup` off `IsUltrametricDist.closedBall_openAddSubgroup`), the finite quotient
`O/2O` (`dyadicIndex k := #(O/2O)`), and the uniformizer **pigeonhole** `exists_pow_sub_dyadic`:
among `x⁰, …, x^M` two are congruent mod the radius-`‖2‖` ball.

**B13-2 (uniformizer).**  `norm_two_lt_one` (`‖2‖ < 1`, via the spectral norm extending the base
2-adic norm — `2` is a non-unit); the **gap lemma** `uniform_gap` (`‖x‖^M ≤ ‖2‖` for `‖x‖ < 1`, by
factoring `xⁱ(1 − xʲ⁻ⁱ)`); the **uniformizer** `exists_uniformizer` (a norm-maximal `π` with
`‖π‖ < 1`, attained on the compact ball `{‖y‖^M ≤ ‖2‖}` via `IsCompact.exists_isMaxOn`); the
**ramification index** `exists_ramificationIndex` (`‖2‖ = ‖π‖^e` exactly, `e ≥ 1`, via
`Nat.find` + the `2/π^e`-unit argument); and their package `exists_uniformizer_data` in the
`ℚ̄₂`-vocabulary the `DyadicUnitFiltration` structure consumes.

The residue field `O/𝔪` and the graded counts are B13-3/B13-4 (`UnitFiltrationCounts.lean`).
-/

namespace GQ2

open IsUltrametricDist Metric

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- `‖2‖ < 1` in `ℚ̄₂`: the spectral norm extends the 2-adic norm on the base, and `‖2‖ = 2⁻¹`
there — `2` is a non-unit.  The whole uniformizer theory rests on this. -/
theorem norm_two_lt_one : ‖(2 : ℚ̄₂)‖ < 1 := by
  have h2 : (2 : ℚ̄₂) = algebraMap ℚ_[2] ℚ̄₂ 2 := (map_ofNat (algebraMap ℚ_[2] ℚ̄₂) 2).symm
  rw [h2, NormedAlgebra.norm_eq_spectralNorm ℚ_[2], spectralNorm_extends]
  have h : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by
    have := Padic.norm_p (p := 2); rwa [Nat.cast_ofNat] at this
  rw [h]; norm_num

variable (k : IntermediateField ℚ_[2] ℚ̄₂)

/-- The closed **unit ball** `O = {x ∈ k : ‖x‖ ≤ 1}` of `k`, as a bundled open additive subgroup
(the ball is clopen in the ultrametric topology). -/
noncomputable def unitBall : OpenAddSubgroup ↥k := closedBall_openAddSubgroup ↥k (r := 1) one_pos

/-- The radius-`‖2‖` ball `2O = {x ∈ k : ‖x‖ ≤ ‖2‖}`, as a bundled open additive subgroup. -/
noncomputable def dyadicBall : OpenAddSubgroup ↥k :=
  closedBall_openAddSubgroup ↥k (r := ‖(2 : ℚ̄₂)‖) (norm_pos_iff.mpr two_ne_zero)

@[simp] theorem mem_unitBall {x : ↥k} : x ∈ (unitBall k).toAddSubgroup ↔ ‖x‖ ≤ 1 :=
  mem_closedBall_zero_iff

@[simp] theorem mem_dyadicBall {x : ↥k} :
    x ∈ (dyadicBall k).toAddSubgroup ↔ ‖x‖ ≤ ‖(2 : ℚ̄₂)‖ := mem_closedBall_zero_iff

/-- The `ℚ₂`-value `‖(2 : ↥k)‖` is `‖(2 : ℚ̄₂)‖` (the norm on `↥k` restricts `ℚ̄₂`'s). -/
theorem norm_two_k : ‖(2 : ↥k)‖ = ‖(2 : ℚ̄₂)‖ := rfl

/-- Powers of a norm-`≤ 1` element stay in the unit ball. -/
theorem unitBall_pow_mem {x : ↥k} (hx : ‖x‖ ≤ 1) (i : ℕ) : x ^ i ∈ (unitBall k).toAddSubgroup := by
  rw [mem_unitBall, norm_pow]; exact pow_le_one₀ (norm_nonneg x) hx

/-- **The ramification index `e` with `‖2‖ = ‖π‖^e`** for any uniformizer-like `π` (norm `< 1`,
norm-maximal below `1`, with `‖2‖ ≤ ‖π‖`).  `e` is least with `‖π‖^{e+1} < ‖2‖`; the exactness
`‖2‖ = ‖π‖^e` comes from applying the max property to `2/π^e`.  (Norm algebra only — no
finite-dimensionality needed.) -/
theorem exists_ramificationIndex {π : ↥k} (hlt : ‖π‖ < 1) (hge : ‖(2 : ℚ̄₂)‖ ≤ ‖π‖)
    (hmax : ∀ y : ↥k, ‖y‖ < 1 → ‖y‖ ≤ ‖π‖) :
    ∃ e : ℕ, 1 ≤ e ∧ ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e := by
  have h2pos : 0 < ‖(2 : ℚ̄₂)‖ := norm_pos_iff.mpr two_ne_zero
  have hπpos : 0 < ‖π‖ := lt_of_lt_of_le h2pos hge
  have hex : ∃ n : ℕ, ‖π‖ ^ (n + 1) < ‖(2 : ℚ̄₂)‖ := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one h2pos hlt
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h
      · rw [h0, pow_zero] at hm; exact absurd hm (not_lt.mpr (le_of_lt norm_two_lt_one))
      · exact h
    exact ⟨m - 1, by rwa [Nat.sub_add_cancel hm1]⟩
  refine ⟨Nat.find hex, ?_, ?_⟩
  · rw [Nat.one_le_iff_ne_zero]; intro he0
    have := Nat.find_spec hex; rw [he0, zero_add, pow_one] at this
    exact absurd this (not_lt.mpr hge)
  · set e := Nat.find hex with he
    have he_spec : ‖π‖ ^ (e + 1) < ‖(2 : ℚ̄₂)‖ := Nat.find_spec hex
    have he_lo : ‖(2 : ℚ̄₂)‖ ≤ ‖π‖ ^ e := by
      rcases Nat.eq_zero_or_pos e with h0 | hpos
      · rw [h0, pow_zero]; exact le_of_lt norm_two_lt_one
      · have := Nat.find_min hex (m := e - 1) (by omega); rw [Nat.sub_add_cancel hpos] at this
        exact not_lt.mp this
    by_contra hne
    have hlt2 : ‖(2 : ℚ̄₂)‖ < ‖π‖ ^ e := lt_of_le_of_ne he_lo hne
    have hxmem := hmax ((2 : ↥k) / π ^ e) (by
      rw [norm_div, norm_pow, norm_two_k, div_lt_one (pow_pos hπpos e)]; exact hlt2)
    rw [norm_div, norm_pow, norm_two_k, div_le_iff₀ (pow_pos hπpos e)] at hxmem
    have hfin : ‖(2 : ℚ̄₂)‖ ≤ ‖π‖ ^ (e + 1) := by rw [pow_succ, mul_comm]; exact hxmem
    linarith [he_spec]

variable [FiniteDimensional ℚ_[2] k]

/-- The unit ball is compact: a closed ball in the proper space `↥k` (finite-dimensional over the
locally compact `ℚ₂`). -/
instance : CompactSpace ↥(unitBall k).toAddSubgroup := by
  refine isCompact_iff_compactSpace.mp ?_
  have hp := FiniteDimensional.proper ℚ_[2] ↥k
  have hc : ((unitBall k).toAddSubgroup : Set ↥k) = closedBall 0 1 := rfl
  rw [hc]; exact isCompact_closedBall 0 1

/-- The quotient `O/2O` is finite: `2O` is an open subgroup of the compact group `O`. -/
instance : Finite (↥(unitBall k).toAddSubgroup ⧸
    (dyadicBall k).toAddSubgroup.addSubgroupOf (unitBall k).toAddSubgroup) :=
  AddSubgroup.quotient_finite_of_isOpen _
    (continuous_subtype_val.isOpen_preimage _ (dyadicBall k).isOpen)

/-- The index `M = #(O/2O)` — the length of the pigeonhole and the exponent of the value-group gap. -/
noncomputable def dyadicIndex : ℕ := Nat.card (↥(unitBall k).toAddSubgroup ⧸
  (dyadicBall k).toAddSubgroup.addSubgroupOf (unitBall k).toAddSubgroup)

theorem one_le_dyadicIndex : 1 ≤ dyadicIndex k := Nat.card_pos

/-- **The uniformizer pigeonhole.**  For `‖x‖ ≤ 1`, two of the powers `x⁰, …, x^M` (`M = dyadicIndex`)
are congruent modulo the radius-`‖2‖` ball: `‖xⁱ − xʲ‖ ≤ ‖2‖` with `i < j ≤ M`. -/
theorem exists_pow_sub_dyadic {x : ↥k} (hx : ‖x‖ ≤ 1) :
    ∃ i j : ℕ, i < j ∧ j ≤ dyadicIndex k ∧ ‖x ^ i - x ^ j‖ ≤ ‖(2 : ℚ̄₂)‖ := by
  classical
  haveI : Fintype (↥(unitBall k).toAddSubgroup ⧸
    (dyadicBall k).toAddSubgroup.addSubgroupOf (unitBall k).toAddSubgroup) := Fintype.ofFinite _
  let g : ℕ → ↥(unitBall k).toAddSubgroup := fun i => ⟨x ^ i, unitBall_pow_mem k hx i⟩
  let f : Fin (dyadicIndex k + 1) → (↥(unitBall k).toAddSubgroup ⧸
    (dyadicBall k).toAddSubgroup.addSubgroupOf (unitBall k).toAddSubgroup) :=
    fun i => QuotientAddGroup.mk (g i.val)
  have hcardQ : Fintype.card (↥(unitBall k).toAddSubgroup ⧸
      (dyadicBall k).toAddSubgroup.addSubgroupOf (unitBall k).toAddSubgroup) = dyadicIndex k :=
    (Nat.card_eq_fintype_card).symm
  have hlt : Fintype.card (↥(unitBall k).toAddSubgroup ⧸
      (dyadicBall k).toAddSubgroup.addSubgroupOf (unitBall k).toAddSubgroup)
      < Fintype.card (Fin (dyadicIndex k + 1)) := by
    rw [Fintype.card_fin, hcardQ]; exact Nat.lt_succ_self _
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt
  have hsub : g a.val - g b.val ∈
      (dyadicBall k).toAddSubgroup.addSubgroupOf (unitBall k).toAddSubgroup :=
    QuotientAddGroup.eq_iff_sub_mem.mp hfab
  rw [AddSubgroup.mem_addSubgroupOf] at hsub
  have hval : ((g a.val - g b.val : ↥(unitBall k).toAddSubgroup) : ↥k) = x ^ a.val - x ^ b.val := by
    simp [g]
  rw [hval, mem_dyadicBall] at hsub
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
  · exact ⟨a.val, b.val, h, (by have := b.isLt; omega), hsub⟩
  · exact ⟨b.val, a.val, h, (by have := a.isLt; omega), by rwa [norm_sub_rev] at hsub⟩

/-- **The value-group gap** (B13-2): for `‖x‖ < 1`, `‖x‖^M ≤ ‖2‖` (`M = dyadicIndex`).  Factor the
pigeonhole difference `xⁱ − xʲ = xⁱ(1 − xʲ⁻ⁱ)`: `‖1 − xʲ⁻ⁱ‖ = 1` (ultrametric, `‖x‖ < 1`), so
`‖x‖ⁱ ≤ ‖2‖`, and `‖x‖^M ≤ ‖x‖ⁱ` since `i ≤ M`. -/
theorem uniform_gap {x : ↥k} (hx : ‖x‖ < 1) : ‖x‖ ^ dyadicIndex k ≤ ‖(2 : ℚ̄₂)‖ := by
  obtain ⟨i, j, hij, hjM, hb⟩ := exists_pow_sub_dyadic k (le_of_lt hx)
  have hxji : ‖x ^ (j - i)‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg x) hx (by omega)
  have hone : ‖(1 : ↥k) - x ^ (j - i)‖ = 1 := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (by rw [norm_one, norm_neg]; exact ne_of_gt hxji),
      norm_one, norm_neg, max_eq_left (le_of_lt hxji)]
  have hfact : x ^ i - x ^ j = x ^ i * (1 - x ^ (j - i)) := by
    rw [mul_sub, mul_one, ← pow_add]; congr 2; omega
  have hi : ‖x‖ ^ i ≤ ‖(2 : ℚ̄₂)‖ := by
    rw [hfact, norm_mul, norm_pow, hone, mul_one] at hb; exact hb
  calc ‖x‖ ^ dyadicIndex k ≤ ‖x‖ ^ i :=
        pow_le_pow_of_le_one (norm_nonneg x) (le_of_lt hx) (by omega)
    _ ≤ ‖(2 : ℚ̄₂)‖ := hi

/-- **The uniformizer** (B13-2): a nonzero `π` with `‖π‖ < 1` that is **norm-maximal** below `1`.
Attained as the norm-maximizer on the compact ball `{‖y‖^M ≤ ‖2‖}` (which, by `uniform_gap`,
contains every element of norm `< 1`). -/
theorem exists_uniformizer :
    ∃ π : ↥k, π ≠ 0 ∧ ‖π‖ < 1 ∧ ∀ y : ↥k, ‖y‖ < 1 → ‖y‖ ≤ ‖π‖ := by
  haveI : ProperSpace ↥k := FiniteDimensional.proper ℚ_[2] ↥k
  set M := dyadicIndex k with hM
  have hM1 : 1 ≤ M := one_le_dyadicIndex k
  have h2lt : ‖(2 : ℚ̄₂)‖ < 1 := norm_two_lt_one
  have h2pos : 0 < ‖(2 : ℚ̄₂)‖ := norm_pos_iff.mpr two_ne_zero
  set B : Set ↥k := {y | ‖y‖ ^ M ≤ ‖(2 : ℚ̄₂)‖} with hB
  have hBsub : B ⊆ closedBall 0 1 := by
    intro y hy
    rw [mem_closedBall, dist_zero_right]
    by_contra hc; rw [not_le] at hc
    have h1 : (1 : ℝ) ≤ ‖y‖ ^ M := one_le_pow₀ (le_of_lt hc)
    have hy2 : ‖y‖ ^ M ≤ ‖(2 : ℚ̄₂)‖ := hy
    linarith
  have hBcompact : IsCompact B := Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (continuous_norm.pow M) continuous_const)
    (Metric.isBounded_closedBall.subset hBsub)
  have h2B : (2 : ↥k) ∈ B := by
    show ‖(2 : ↥k)‖ ^ M ≤ ‖(2 : ℚ̄₂)‖
    rw [norm_two_k]
    calc ‖(2 : ℚ̄₂)‖ ^ M ≤ ‖(2 : ℚ̄₂)‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt h2lt) hM1
      _ = ‖(2 : ℚ̄₂)‖ := pow_one _
  obtain ⟨π, hπB, hπmax⟩ := hBcompact.exists_isMaxOn ⟨2, h2B⟩ continuous_norm.continuousOn
  have hmax' := isMaxOn_iff.mp hπmax
  have hπge : ‖(2 : ℚ̄₂)‖ ≤ ‖π‖ := by have := hmax' _ h2B; rwa [norm_two_k] at this
  refine ⟨π, ?_, ?_, ?_⟩
  · intro h0; rw [h0, norm_zero] at hπge; linarith
  · have hπB' : ‖π‖ ^ M ≤ ‖(2 : ℚ̄₂)‖ := hπB
    by_contra hc; rw [not_lt] at hc
    have : (1 : ℝ) ≤ ‖π‖ ^ M := one_le_pow₀ hc
    linarith
  · intro y hy
    exact hmax' _ (show ‖y‖ ^ M ≤ ‖(2 : ℚ̄₂)‖ from uniform_gap k hy)

/-- **The uniformizer + ramification data** (B13-2's deliverable for the B13-5 capstone), in the
`ℚ̄₂`-vocabulary of the `DyadicUnitFiltration` structure: a `π ∈ k`, `π ≠ 0`, `‖π‖ < 1`,
norm-maximal below `1`, together with `e ≥ 1` and `‖2‖ = ‖π‖^e`. -/
theorem exists_uniformizer_data :
    ∃ (π : ℚ̄₂) (e : ℕ), π ∈ k ∧ π ≠ 0 ∧ ‖π‖ < 1
      ∧ (∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
      ∧ 1 ≤ e ∧ ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e := by
  obtain ⟨π, hne, hlt, hmax⟩ := exists_uniformizer k
  have hge : ‖(2 : ℚ̄₂)‖ ≤ ‖π‖ := by
    have h := hmax 2 (by rw [norm_two_k]; exact norm_two_lt_one); rwa [norm_two_k] at h
  obtain ⟨e, he1, he⟩ := exists_ramificationIndex k hlt hge hmax
  refine ⟨(π : ℚ̄₂), e, π.2, ?_, hlt, ?_, he1, he⟩
  · exact fun h => hne (by exact_mod_cast h)
  · intro x hxk hxlt; exact hmax ⟨x, hxk⟩ hxlt

end GQ2

import GQ2.UnitFiltrationTop

/-!
# B13-3 — the residue field of the unit ball

The **B13-3 deliverable** of the `dyadicUnitFiltration` axiom-discharge initiative (board
`docs/b13-tickets.md`, plan `docs/b13-proof-plan.md`, §1(R)).  For a finite extension `k/ℚ₂` it
builds the residue field `O/𝔪` of the valuation ring `O = {‖x‖ ≤ 1}` and records its cardinality:

* `Osub k : Subring ↥k` — the unit ball, and its `CompactSpace`;
* `maxIdeal k : Ideal ↥(Osub k)` — the maximal ideal `𝔪 = {‖x‖ < 1}` (**intrinsic, π-free** — so
  this file is independent of the B13-2 uniformizer lane);
* `ResidueField k := ↥(Osub k) ⧸ maxIdeal k` — **finite** (`𝔪` open in the compact `O`),
  an **integral domain** (norm multiplicativity), hence a **field**, of **characteristic 2**;
* `residue_card` — `#(O/𝔪) = 2^f` and `#(O/𝔪)ˣ = 2^f − 1` with `f ≥ 1`.

The graded isomorphisms and the two `Nat.card` counts against these (B13-4), and the capstone
(B13-5), append to this file.  Imports `GQ2.UnitFiltrationTop` (B13-1) + Mathlib.
-/

namespace GQ2.UnitFiltrationCounts

open IsUltrametricDist Metric

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- `‖(2 : ℚ̄₂)‖ < 1` — the dyadic uniformizer of the base has norm `2⁻¹`. -/
theorem norm_two_lt_one : ‖(2 : ℚ̄₂)‖ < 1 := by
  have h : (2 : ℚ̄₂) = algebraMap ℚ_[2] ℚ̄₂ 2 := by rw [map_ofNat]
  rw [h, norm_algebraMap' (𝕜' := ℚ̄₂)]
  have h2 : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by
    rw [show (2 : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) by norm_cast, Padic.norm_p]; norm_num
  rw [h2]; norm_num

variable (k : IntermediateField ℚ_[2] ℚ̄₂)

/-! ## The unit ball `O` as a subring, and its maximal ideal `𝔪` -/

/-- The **valuation ring** `O = {x ∈ k : ‖x‖ ≤ 1}`, as a subring (multiplicative structure the
counts need — B13-1's `unitBall` carries only the additive one). -/
noncomputable def Osub : Subring ↥k where
  carrier := {x | ‖x‖ ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' hx hy := le_trans (norm_add_le_max _ _) (max_le hx hy)
  mul_mem' hx hy := by rw [Set.mem_setOf_eq, norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy
  neg_mem' hx := by rwa [Set.mem_setOf_eq, norm_neg]

/-- The **maximal ideal** `𝔪 = {x ∈ O : ‖x‖ < 1}` (the non-units of `O`).  Intrinsic — no
uniformizer is used, so this file does not depend on the B13-2 lane. -/
noncomputable def maxIdeal : Ideal ↥(Osub k) where
  carrier := {x | ‖(x : ↥k)‖ < 1}
  zero_mem' := by simp
  add_mem' hx hy := lt_of_le_of_lt (norm_add_le_max _ _) (max_lt hx hy)
  smul_mem' c {x} hx := by
    rw [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, norm_mul]
    calc ‖(c : ↥k)‖ * ‖(x : ↥k)‖ ≤ 1 * ‖(x : ↥k)‖ := by gcongr; exact c.2
      _ = ‖(x : ↥k)‖ := one_mul _
      _ < 1 := hx

@[simp] theorem mem_maxIdeal {x : ↥(Osub k)} : x ∈ maxIdeal k ↔ ‖(x : ↥k)‖ < 1 := Iff.rfl

/-- `𝔪` is prime: `‖xy‖ = ‖x‖‖y‖ < 1` forces a factor `< 1`; `1 ∉ 𝔪`. -/
instance : (maxIdeal k).IsPrime where
  ne_top' h := by
    have h1 : (1 : ↥(Osub k)) ∈ maxIdeal k := h ▸ Submodule.mem_top
    rw [mem_maxIdeal] at h1; simp at h1
  mem_or_mem' {x y} hxy := by
    rw [mem_maxIdeal, Subring.coe_mul, norm_mul] at hxy
    rw [mem_maxIdeal, mem_maxIdeal]
    by_contra h
    rw [not_or, not_lt, not_lt] at h
    exact absurd hxy (not_lt.mpr (one_le_mul_of_one_le_of_one_le h.1 h.2))

variable [FiniteDimensional ℚ_[2] k]

/-- `O` is compact: the closed unit ball of the proper space `↥k`. -/
instance : CompactSpace ↥(Osub k) := by
  refine isCompact_iff_compactSpace.mp ?_
  have hp := FiniteDimensional.proper ℚ_[2] ↥k
  have hc : ((Osub k : Subring ↥k) : Set ↥k) = closedBall 0 1 := by
    ext x; simp [Osub]
  rw [hc]; exact isCompact_closedBall 0 1

/-- `O/𝔪` is finite: `𝔪` is an open subgroup of the compact `O`. -/
instance : Finite (↥(Osub k) ⧸ maxIdeal k) := by
  have hopen : IsOpen ((maxIdeal k).toAddSubgroup : Set ↥(Osub k)) :=
    continuous_subtype_val.isOpen_preimage {y : ↥k | ‖y‖ < 1}
      (isOpen_lt continuous_norm continuous_const)
  exact AddSubgroup.quotient_finite_of_isOpen (maxIdeal k).toAddSubgroup hopen

/-- **The residue field** `O/𝔪`. -/
abbrev ResidueField := ↥(Osub k) ⧸ maxIdeal k

/-- `O/𝔪` is a field: a finite integral domain. -/
noncomputable instance : Field (ResidueField k) := (Finite.isField_of_domain _).toField

omit [FiniteDimensional ℚ_[2] k] in
/-- `2 = 0` in the residue field (`‖2‖ < 1`, so `2 ∈ 𝔪`). -/
theorem two_eq_zero : (2 : ResidueField k) = 0 := by
  have h2mem : (2 : ↥(Osub k)) ∈ maxIdeal k := by
    rw [mem_maxIdeal]
    have e1 : ((2 : ↥(Osub k)) : ↥k) = (2 : ↥k) := by norm_cast
    rw [e1]; exact norm_two_lt_one
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr h2mem
  simpa only [map_ofNat] using h

/-- The residue field has characteristic `2`. -/
instance : CharP (ResidueField k) 2 := by
  obtain ⟨p, hp⟩ := CharP.exists (ResidueField k)
  haveI := hp
  haveI : Fintype (ResidueField k) := Fintype.ofFinite _
  have hpp : p.Prime := CharP.char_is_prime (ResidueField k) p
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ResidueField k) p 2).mp (by
    exact_mod_cast two_eq_zero k)
  rwa [(Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp hdvd] at hp

/-- **The residue-field cardinalities**: `#(O/𝔪) = 2^f` and `#(O/𝔪)ˣ = 2^f − 1` with `f ≥ 1`.
The `f` here is the residue degree; B13-4 feeds these into the graded counts. -/
theorem residue_card :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card (ResidueField k) = 2 ^ f ∧ Nat.card (ResidueField k)ˣ = 2 ^ f - 1 := by
  haveI : Fintype (ResidueField k) := Fintype.ofFinite _
  haveI : DecidableEq (ResidueField k) := Classical.decEq _
  obtain ⟨n, _, hcard⟩ := FiniteField.card (ResidueField k) 2
  exact ⟨n, n.2, by rw [Nat.card_eq_fintype_card, hcard],
    by rw [Nat.card_eq_fintype_card, Fintype.card_units, hcard]⟩

end GQ2.UnitFiltrationCounts

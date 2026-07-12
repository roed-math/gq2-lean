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
  rw [← map_ofNat (algebraMap ℚ_[2] ℚ̄₂) 2, norm_algebraMap' (𝕜' := ℚ̄₂)]
  exact_mod_cast Padic.norm_p_lt_one (p := 2)

variable (k : IntermediateField ℚ_[2] ℚ̄₂)

/-! ## The unit ball `O` as a subring, and its maximal ideal `𝔪` -/

/-- The **valuation ring** `O = {x ∈ k : ‖x‖ ≤ 1}`, as a subring (multiplicative structure the
counts need — B13-1's `unitBall` carries only the additive one). -/
noncomputable def Osub : Subring ↥k where
  carrier := {x | ‖x‖ ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' hx hy := (norm_add_le_max _ _).trans (max_le hx hy)
  mul_mem' hx hy := (norm_mul _ _).trans_le (mul_le_one₀ hx (norm_nonneg _) hy)
  neg_mem' hx := (norm_neg _).trans_le hx

/-- The **maximal ideal** `𝔪 = {x ∈ O : ‖x‖ < 1}` (the non-units of `O`).  Intrinsic — no
uniformizer is used, so this file does not depend on the B13-2 lane. -/
noncomputable def maxIdeal : Ideal ↥(Osub k) where
  carrier := {x | ‖(x : ↥k)‖ < 1}
  zero_mem' := by simp
  add_mem' hx hy := (norm_add_le_max _ _).trans_lt (max_lt hx hy)
  smul_mem' c {x} hx :=
    (norm_mul _ _).trans_lt ((mul_le_of_le_one_left (norm_nonneg _) c.2).trans_lt hx)

@[simp] theorem mem_maxIdeal {x : ↥(Osub k)} : x ∈ maxIdeal k ↔ ‖(x : ↥k)‖ < 1 := Iff.rfl

/-- `𝔪` is prime: `‖xy‖ = ‖x‖‖y‖ < 1` forces a factor `< 1`; `1 ∉ 𝔪`. -/
instance : (maxIdeal k).IsPrime where
  ne_top' h := by simpa using (h ▸ Submodule.mem_top : (1 : ↥(Osub k)) ∈ maxIdeal k)
  mem_or_mem' {x y} hxy := by
    rw [mem_maxIdeal, Subring.coe_mul, norm_mul] at hxy
    rw [mem_maxIdeal, mem_maxIdeal]
    by_contra! h
    exact absurd hxy (not_lt.mpr (one_le_mul_of_one_le_of_one_le h.1 h.2))

variable [FiniteDimensional ℚ_[2] k]

/-- `O` is compact: the closed unit ball of the proper space `↥k`. -/
instance : CompactSpace ↥(Osub k) := by
  have := FiniteDimensional.proper ℚ_[2] ↥k
  refine isCompact_iff_compactSpace.mp ?_
  rw [show ((Osub k : Subring ↥k) : Set ↥k) = closedBall 0 1 from Set.ext fun x ↦ by simp [Osub]]
  exact isCompact_closedBall 0 1

/-- `O/𝔪` is finite: `𝔪` is an open subgroup of the compact `O`. -/
instance : Finite (↥(Osub k) ⧸ maxIdeal k) :=
  AddSubgroup.quotient_finite_of_isOpen (maxIdeal k).toAddSubgroup
    (continuous_subtype_val.isOpen_preimage {y : ↥k | ‖y‖ < 1}
      (isOpen_lt continuous_norm continuous_const))

/-- **The residue field** `O/𝔪`. -/
abbrev ResidueField := ↥(Osub k) ⧸ maxIdeal k

/-- `O/𝔪` is a field: a finite integral domain. -/
noncomputable instance : Field (ResidueField k) := (Finite.isField_of_domain _).toField

omit [FiniteDimensional ℚ_[2] k] in
/-- `2 = 0` in the residue field (`‖2‖ < 1`, so `2 ∈ 𝔪`). -/
theorem two_eq_zero : (2 : ResidueField k) = 0 := by
  have h2mem : (2 : ↥(Osub k)) ∈ maxIdeal k := by
    rw [mem_maxIdeal, show ((2 : ↥(Osub k)) : ↥k) = (2 : ↥k) by norm_cast]
    exact norm_two_lt_one
  simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr h2mem

/-- The residue field has characteristic `2`. -/
instance : CharP (ResidueField k) 2 :=
  (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (mod_cast two_eq_zero k)

/-- **The residue-field cardinalities**: `#(O/𝔪) = 2^f` and `#(O/𝔪)ˣ = 2^f − 1` with `f ≥ 1`.
The `f` here is the residue degree; B13-4 feeds these into the graded counts. -/
theorem residue_card :
    ∃ f : ℕ,
      1 ≤ f ∧ Nat.card (ResidueField k) = 2 ^ f ∧ Nat.card (ResidueField k)ˣ = 2 ^ f - 1 := by
  have : Fintype (ResidueField k) := Fintype.ofFinite _
  obtain ⟨n, _, hcard⟩ := FiniteField.card (ResidueField k) 2
  exact ⟨n, n.2, by rw [Nat.card_eq_fintype_card, hcard],
    by rw [Nat.card_units, Nat.card_eq_fintype_card, hcard]⟩

/-! ## B13-4 — the graded isomorphisms and the two `Nat.card` counts

Two group homomorphisms cutting the unit filtration into residue-field data:
`U⁰ = normUnits → (O/𝔪)ˣ` (`u ↦ ū`) with kernel `U¹` and surjective, and for `i ≥ 1`
`U^{(i)} → Multiplicative (O/𝔪)` (`u ↦ (u−1)/πⁱ mod 𝔪`) with kernel `U^{(i+1)}` and surjective.
The isomorphism theorem then gives `#(U⁰/U¹) = #(O/𝔪)ˣ = 2^f − 1` and
`#(U^i/U^{i+1}) = #(O/𝔪) = 2^f`.
Everything is parameterized by a uniformizer `π : ↥k` (B13-2's `exists_uniformizer`). -/

omit [FiniteDimensional ℚ_[2] ↥k] in
theorem mem_Osub {x : ↥k} : x ∈ Osub k ↔ ‖x‖ ≤ 1 := Iff.rfl

omit [FiniteDimensional ℚ_[2] ↥k] in
/-- `‖↑x − 1‖ = ‖x − 1‖` bridging the `ℚ̄₂`-norm of the coercion and the `↥k`-norm. -/
theorem norm_sub_one_bridge (x : ↥k) : ‖((x : ↥k) : ℚ̄₂) - 1‖ = ‖x - 1‖ :=
  congrArg norm (show ((x : ↥k) : ℚ̄₂) - 1 = ((x - 1 : ↥k) : ℚ̄₂) by push_cast; ring)

omit [FiniteDimensional ℚ_[2] ↥k] in
/-- **The scaled exchange**: `‖x‖ < ‖π‖ⁱ ↔ ‖x‖ ≤ ‖π‖^{i+1}` (divide by `πⁱ` and apply `hπ_max`). -/
theorem scaled_exchange {π : ↥k} (hπne : π ≠ 0) (hπlt : ‖π‖ < 1)
    (hπmax : ∀ y : ↥k, ‖y‖ < 1 → ‖y‖ ≤ ‖π‖) (x : ↥k) (i : ℕ) :
    ‖x‖ < ‖π‖ ^ i ↔ ‖x‖ ≤ ‖π‖ ^ (i + 1) := by
  have hpi : 0 < ‖π‖ ^ i := pow_pos (norm_pos_iff.mpr hπne) i
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hle := hπmax (x / π ^ i) (by rwa [norm_div, norm_pow, div_lt_one hpi])
    rwa [norm_div, norm_pow, div_le_iff₀ hpi, ← pow_succ'] at hle
  · exact h.trans_lt (pow_lt_pow_right_of_lt_one₀ (norm_pos_iff.mpr hπne) hπlt i.lt_succ_self)

/-! ### Grade 0: `U⁰/U¹ ≃ (O/𝔪)ˣ` -/

omit [FiniteDimensional ℚ_[2] ↥k] in
/-- A norm-one unit of `k` as an element of the valuation ring `O`. -/
noncomputable def normUnitToOsub (u : ↥(normUnits k)) : ↥(Osub k) :=
  ⟨(u.1 : ↥k), ((mem_normUnits k u.1).mp u.2).le⟩

omit [FiniteDimensional ℚ_[2] ↥k] in
@[simp] theorem normUnitToOsub_coe (u : ↥(normUnits k)) : (normUnitToOsub k u : ↥k) = (u.1 : ↥k) :=
  rfl

omit [FiniteDimensional ℚ_[2] ↥k] in
theorem normUnitToOsub_one : normUnitToOsub k 1 = 1 := rfl

omit [FiniteDimensional ℚ_[2] ↥k] in
theorem normUnitToOsub_mul (a b : ↥(normUnits k)) :
    normUnitToOsub k (a * b) = normUnitToOsub k a * normUnitToOsub k b := rfl

omit [FiniteDimensional ℚ_[2] ↥k] in
/-- A norm-one unit of `k` as a unit of the valuation ring `O`. -/
noncomputable def normUnitToOsubUnit : ↥(normUnits k) →* (↥(Osub k))ˣ where
  toFun u :=
    { val := normUnitToOsub k u
      inv := ⟨((u.1⁻¹ : (↥k)ˣ) : ↥k), ((mem_normUnits k _).mp ((normUnits k).inv_mem u.2)).le⟩
      val_inv := Subtype.ext u.1.mul_inv
      inv_val := Subtype.ext u.1.inv_mul }
  map_one' := Units.ext (normUnitToOsub_one k)
  map_mul' a b := Units.ext (normUnitToOsub_mul k a b)

/-- **The grade-0 map** `U⁰ → (O/𝔪)ˣ`: a norm-one unit ↦ its residue. -/
noncomputable def gradeZeroHom : ↥(normUnits k) →* (ResidueField k)ˣ :=
  (Units.map (Ideal.Quotient.mk (maxIdeal k)).toMonoidHom).comp (normUnitToOsubUnit k)

omit [FiniteDimensional ℚ_[2] ↥k] in
theorem gradeZeroHom_val (u : ↥(normUnits k)) :
    ((gradeZeroHom k u : (ResidueField k)ˣ) : ResidueField k)
      = Ideal.Quotient.mk (maxIdeal k) (normUnitToOsub k u) := rfl

omit [FiniteDimensional ℚ_[2] ↥k] in
theorem coe_normUnitToOsub_sub_one (u : ↥(normUnits k)) :
    ((normUnitToOsub k u - 1 : ↥(Osub k)) : ↥k) = (u.1 : ↥k) - 1 := rfl

omit [FiniteDimensional ℚ_[2] ↥k] in
theorem gradeZeroHom_eq_one_iff (u : ↥(normUnits k)) :
    gradeZeroHom k u = 1 ↔ ‖(u.1 : ↥k) - 1‖ < 1 := by
  rw [← Units.val_eq_one, gradeZeroHom_val, Ideal.Quotient.mk_eq_one_iff_sub_mem, mem_maxIdeal,
    coe_normUnitToOsub_sub_one]

omit [FiniteDimensional ℚ_[2] ↥k] in
theorem gradeZeroHom_ker {π : ↥k} (hπlt : ‖π‖ < 1) (hπmax : ∀ y : ↥k, ‖y‖ < 1 → ‖y‖ ≤ ‖π‖) :
    (gradeZeroHom k).ker = (depthUnits k (π : ℚ̄₂) 1).subgroupOf (normUnits k) := by
  have hexch : ∀ x : ↥k, ‖x‖ < 1 ↔ ‖x‖ ≤ ‖(π : ℚ̄₂)‖ :=
    fun x ↦ ⟨hπmax x, fun h ↦ lt_of_le_of_lt h hπlt⟩
  ext u
  have hu1 : ‖((u.1 : ↥k) : ℚ̄₂)‖ = 1 := (mem_normUnits k u.1).mp u.2
  have hbridge : ‖((u.1 : ↥k) : ℚ̄₂) - 1‖ = ‖(u.1 : ↥k) - 1‖ := norm_sub_one_bridge k _
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_depthUnits, pow_one, hbridge]
  exact ⟨fun h ↦ ⟨hu1, (hexch _).mp ((gradeZeroHom_eq_one_iff k u).mp h)⟩,
    fun h ↦ (gradeZeroHom_eq_one_iff k u).mpr ((hexch _).mpr h.2)⟩

omit [FiniteDimensional ℚ_[2] ↥k] in
theorem gradeZeroHom_surjective : Function.Surjective (gradeZeroHom k) := by
  intro y
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (y : ResidueField k)
  have hane : ¬ ‖(a : ↥k)‖ < 1 := by
    rw [← mem_maxIdeal]; intro hmem
    exact y.ne_zero (by rw [← ha, Ideal.Quotient.eq_zero_iff_mem]; exact hmem)
  have hnorm : ‖(a : ↥k)‖ = 1 := le_antisymm ((mem_Osub k).mp a.2) (not_lt.mp hane)
  have haval : (a : ↥k) ≠ 0 := fun h ↦ one_ne_zero (by rw [← hnorm, h, norm_zero])
  refine ⟨⟨Units.mk0 (a : ↥k) haval, by rw [mem_normUnits]; exact hnorm⟩, Units.ext ?_⟩
  rw [gradeZeroHom_val, ← ha]; congr 1

omit [FiniteDimensional ℚ_[2] ↥k] in
theorem card_gradeZero {π : ↥k} (hπlt : ‖π‖ < 1) (hπmax : ∀ y : ↥k, ‖y‖ < 1 → ‖y‖ ≤ ‖π‖) :
    Nat.card (↥(normUnits k) ⧸ (depthUnits k (π : ℚ̄₂) 1).subgroupOf (normUnits k))
      = Nat.card (ResidueField k)ˣ := by
  rw [← gradeZeroHom_ker k hπlt hπmax]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (gradeZeroHom k)
    (gradeZeroHom_surjective k)).toEquiv

/-! ### Grade `i ≥ 1`: `U^{(i)}/U^{(i+1)} ≃ (O/𝔪, +)` -/

omit [FiniteDimensional ℚ_[2] ↥k] in
/-- `(u − 1)/πⁱ`, the value whose residue is the grade-`i` datum. -/
noncomputable def depthDiv {π : ↥k} (i : ℕ) (u : ↥(depthUnits k (π : ℚ̄₂) i)) : ↥k :=
  ((u.1 : ↥k) - 1) / π ^ i

omit [FiniteDimensional ℚ_[2] ↥k] in
theorem depthDiv_mem {π : ↥k} (hπne : π ≠ 0) (i : ℕ) (u : ↥(depthUnits k (π : ℚ̄₂) i)) :
    depthDiv k i u ∈ Osub k := by
  rw [mem_Osub, depthDiv, norm_div, norm_pow, div_le_one (pow_pos (norm_pos_iff.mpr hπne) i),
    ← norm_sub_one_bridge]
  exact ((mem_depthUnits k (π : ℚ̄₂) i u.1).mp u.2).2

/-- `(u − 1)/πⁱ` as an element of `O`. -/
noncomputable def depthToOsub {π : ↥k} (hπne : π ≠ 0) (i : ℕ) (u : ↥(depthUnits k (π : ℚ̄₂) i)) :
    ↥(Osub k) := ⟨depthDiv k i u, depthDiv_mem k hπne i u⟩

omit [FiniteDimensional ℚ_[2] ↥k] in
theorem depthToOsub_coe {π : ↥k} (hπne : π ≠ 0) (i : ℕ) (u : ↥(depthUnits k (π : ℚ̄₂) i)) :
    (depthToOsub k hπne i u : ↥k) = ((u.1 : ↥k) - 1) / π ^ i := rfl

omit [FiniteDimensional ℚ_[2] ↥k] in
theorem depthRes_eq_zero_iff {π : ↥k} (hπne : π ≠ 0) (i : ℕ) (u : ↥(depthUnits k (π : ℚ̄₂) i)) :
    Ideal.Quotient.mk (maxIdeal k) (depthToOsub k hπne i u) = 0 ↔ ‖(u.1 : ↥k) - 1‖ < ‖π‖ ^ i := by
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_maxIdeal, depthToOsub_coe, norm_div, norm_pow,
    div_lt_one (pow_pos (norm_pos_iff.mpr hπne) i)]

omit [FiniteDimensional ℚ_[2] ↥k] in
theorem depthRes_one {π : ↥k} (hπne : π ≠ 0) (i : ℕ) :
    Ideal.Quotient.mk (maxIdeal k)
      (depthToOsub k hπne i (1 : ↥(depthUnits k (π : ℚ̄₂) i))) = 0 := by
  rw [depthRes_eq_zero_iff]
  simp only [OneMemClass.coe_one, Units.val_one, sub_self, norm_zero]
  exact pow_pos (norm_pos_iff.mpr hπne) i

omit [FiniteDimensional ℚ_[2] ↥k] in
/-- **The grade-`i` additivity** (the cross-term `(u−1)(v−1)/πⁱ` has residue 0). -/
theorem depthRes_add {π : ↥k} (hπne : π ≠ 0) (hπlt : ‖π‖ < 1) {i : ℕ} (hi : 1 ≤ i)
    (u v : ↥(depthUnits k (π : ℚ̄₂) i)) :
    Ideal.Quotient.mk (maxIdeal k) (depthToOsub k hπne i (u * v))
      = Ideal.Quotient.mk (maxIdeal k) (depthToOsub k hπne i u)
        + Ideal.Quotient.mk (maxIdeal k) (depthToOsub k hπne i v) := by
  have hpi : (0 : ℝ) < ‖π‖ ^ i := pow_pos (norm_pos_iff.mpr hπne) i
  have hπine : (π : ↥k) ^ i ≠ 0 := pow_ne_zero i hπne
  rw [← (Ideal.Quotient.mk (maxIdeal k)).map_add, Ideal.Quotient.eq, mem_maxIdeal]
  have hval : ((depthToOsub k hπne i (u * v) - (depthToOsub k hπne i u + depthToOsub k hπne i v) :
      ↥(Osub k)) : ↥k) = ((u.1 : ↥k) - 1) * ((v.1 : ↥k) - 1) / π ^ i := by
    simp only [depthToOsub, depthDiv]
    push_cast [Subgroup.coe_mul, Units.val_mul]
    field_simp
    ring
  rw [hval, norm_div, norm_pow, div_lt_one hpi, norm_mul]
  have hbu : ‖(u.1 : ↥k) - 1‖ ≤ ‖π‖ ^ i := by
    rw [← norm_sub_one_bridge]; exact ((mem_depthUnits k (π : ℚ̄₂) i u.1).mp u.2).2
  have hbv : ‖(v.1 : ↥k) - 1‖ ≤ ‖π‖ ^ i := by
    rw [← norm_sub_one_bridge]; exact ((mem_depthUnits k (π : ℚ̄₂) i v.1).mp v.2).2
  have hpile : ‖π‖ ^ i ≤ ‖π‖ := by
    simpa using pow_le_pow_of_le_one (norm_nonneg _) hπlt.le hi
  calc ‖(u.1 : ↥k) - 1‖ * ‖(v.1 : ↥k) - 1‖
      ≤ ‖π‖ ^ i * ‖π‖ ^ i := mul_le_mul hbu hbv (norm_nonneg _) (le_of_lt hpi)
    _ ≤ ‖π‖ ^ i * ‖π‖ := mul_le_mul_of_nonneg_left hpile hpi.le
    _ < ‖π‖ ^ i * 1 := mul_lt_mul_of_pos_left hπlt hpi
    _ = ‖π‖ ^ i := mul_one _

omit [FiniteDimensional ℚ_[2] ↥k] in
/-- Surjectivity witness: `1 + a·πⁱ` is a norm-one unit in `U^{(i)}` with datum `a`. -/
theorem gradeI_surj_witness {π : ↥k} (hπne : π ≠ 0) (hπlt : ‖π‖ < 1) {i : ℕ} (hi : 1 ≤ i)
    (a : ↥(Osub k)) : ∃ u : ↥(depthUnits k (π : ℚ̄₂) i), depthToOsub k hπne i u = a := by
  have hpile : ‖π‖ ^ i ≤ ‖π‖ := by
    simpa using pow_le_pow_of_le_one (norm_nonneg _) hπlt.le hi
  have hsmall : ‖(a : ↥k) * π ^ i‖ ≤ ‖π‖ ^ i := by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) ((mem_Osub k).mp a.2)
  have hsmall1 : ‖(a : ↥k) * π ^ i‖ < 1 := lt_of_le_of_lt hsmall (lt_of_le_of_lt hpile hπlt)
  set w : ↥k := (1 : ↥k) + (a : ↥k) * π ^ i with hw
  have hval : ‖w‖ = 1 := by
    rw [hw, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (by rw [norm_one]; exact (ne_of_lt hsmall1).symm), norm_one, max_eq_left (le_of_lt hsmall1)]
  have hne0 : w ≠ 0 := fun h ↦ one_ne_zero (by rw [← hval, h, norm_zero])
  have hw1 : w - 1 = (a : ↥k) * π ^ i := by rw [hw]; ring
  have hmem : Units.mk0 w hne0 ∈ depthUnits k (π : ℚ̄₂) i := by
    rw [mem_depthUnits]
    refine ⟨hval, ?_⟩
    rw [norm_sub_one_bridge, show ((Units.mk0 w hne0 : (↥k)ˣ) : ↥k) = w from rfl, hw1]
    exact hsmall
  refine ⟨⟨Units.mk0 w hne0, hmem⟩, ?_⟩
  apply Subtype.ext
  rw [depthToOsub_coe]
  show (w - 1) / π ^ i = (a : ↥k)
  rw [hw1, mul_div_assoc, div_self (pow_ne_zero i hπne), mul_one]

/-- **The grade-`i` map** `U^{(i)} → Multiplicative (O/𝔪)`. -/
noncomputable def gradeIHom {π : ↥k} (hπne : π ≠ 0) (hπlt : ‖π‖ < 1) {i : ℕ} (hi : 1 ≤ i) :
    ↥(depthUnits k (π : ℚ̄₂) i) →* Multiplicative (ResidueField k) where
  toFun u := Multiplicative.ofAdd (Ideal.Quotient.mk (maxIdeal k) (depthToOsub k hπne i u))
  map_one' := by simp only [depthRes_one k hπne i, ofAdd_zero]
  map_mul' a b := congrArg Multiplicative.ofAdd (depthRes_add k hπne hπlt hi a b)

omit [FiniteDimensional ℚ_[2] ↥k] in
theorem gradeIHom_apply {π : ↥k} (hπne : π ≠ 0) (hπlt : ‖π‖ < 1) {i : ℕ} (hi : 1 ≤ i)
    (u : ↥(depthUnits k (π : ℚ̄₂) i)) :
    gradeIHom k hπne hπlt hi u
      = Multiplicative.ofAdd (Ideal.Quotient.mk (maxIdeal k) (depthToOsub k hπne i u)) := rfl

omit [FiniteDimensional ℚ_[2] ↥k] in
theorem gradeIHom_ker {π : ↥k} (hπne : π ≠ 0) (hπlt : ‖π‖ < 1)
    (hπmax : ∀ y : ↥k, ‖y‖ < 1 → ‖y‖ ≤ ‖π‖) {i : ℕ} (hi : 1 ≤ i) :
    (gradeIHom k hπne hπlt hi).ker
      = (depthUnits k (π : ℚ̄₂) (i + 1)).subgroupOf (depthUnits k (π : ℚ̄₂) i) := by
  ext u
  have hu1 : ‖((u.1 : ↥k) : ℚ̄₂)‖ = 1 := ((mem_depthUnits k (π : ℚ̄₂) i u.1).mp u.2).1
  have hkey : gradeIHom k hπne hπlt hi u = 1 ↔ ‖(u.1 : ↥k) - 1‖ < ‖π‖ ^ i := by
    rw [gradeIHom_apply, ← ofAdd_zero (α := ResidueField k),
      Multiplicative.ofAdd.apply_eq_iff_eq, depthRes_eq_zero_iff]
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_depthUnits, norm_sub_one_bridge, hkey]
  exact ⟨fun h ↦ ⟨hu1, (scaled_exchange k hπne hπlt hπmax _ i).mp h⟩,
    fun h ↦ (scaled_exchange k hπne hπlt hπmax _ i).mpr h.2⟩

omit [FiniteDimensional ℚ_[2] ↥k] in
theorem gradeIHom_surjective {π : ↥k} (hπne : π ≠ 0) (hπlt : ‖π‖ < 1) {i : ℕ} (hi : 1 ≤ i) :
    Function.Surjective (gradeIHom k hπne hπlt hi) := by
  intro y
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (Multiplicative.toAdd y)
  obtain ⟨u, hu⟩ := gradeI_surj_witness k hπne hπlt hi a
  refine ⟨u, ?_⟩
  rw [gradeIHom_apply, hu, ha]; rfl

omit [FiniteDimensional ℚ_[2] ↥k] in
theorem card_gradeI {π : ↥k} (hπne : π ≠ 0) (hπlt : ‖π‖ < 1)
    (hπmax : ∀ y : ↥k, ‖y‖ < 1 → ‖y‖ ≤ ‖π‖) {i : ℕ} (hi : 1 ≤ i) :
    Nat.card (↥(depthUnits k (π : ℚ̄₂) i) ⧸
        (depthUnits k (π : ℚ̄₂) (i + 1)).subgroupOf (depthUnits k (π : ℚ̄₂) i))
      = Nat.card (ResidueField k) := by
  rw [← gradeIHom_ker k hπne hπlt hπmax hi,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (gradeIHom k hπne hπlt hi)
      (gradeIHom_surjective k hπne hπlt hi)).toEquiv]
  rfl

/-- **B13-4 deliverable**: the graded counts `#(U⁰/U¹) = 2^f − 1` and `#(U^i/U^{i+1}) = 2^f`
(same `f`), at a uniformizer `π`.  Fed into the `DyadicUnitFiltration` structure by B13-5. -/
theorem exists_gradeCounts {π : ↥k} (hπne : π ≠ 0) (hπlt : ‖π‖ < 1)
    (hπmax : ∀ y : ↥k, ‖y‖ < 1 → ‖y‖ ≤ ‖π‖) :
    ∃ f : ℕ, 1 ≤ f ∧
      Nat.card (↥(normUnits k) ⧸ (depthUnits k (π : ℚ̄₂) 1).subgroupOf (normUnits k)) = 2 ^ f - 1 ∧
      ∀ i : ℕ, 1 ≤ i → Nat.card (↥(depthUnits k (π : ℚ̄₂) i) ⧸
        (depthUnits k (π : ℚ̄₂) (i + 1)).subgroupOf (depthUnits k (π : ℚ̄₂) i)) = 2 ^ f := by
  obtain ⟨f, hf1, hfc, hfu⟩ := residue_card k
  refine ⟨f, hf1, ?_, fun i hi ↦ ?_⟩
  · rw [card_gradeZero k hπlt hπmax]; exact hfu
  · rw [card_gradeI k hπne hπlt hπmax hi]; exact hfc

end GQ2.UnitFiltrationCounts

namespace GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- **The B13 capstone** (P-15f1 discharge, B13-5): every finite extension `k/ℚ₂` inside `ℚ̄₂`
carries a `DyadicUnitFiltration`.  Assembled from the uniformizer + ramification data
(`exists_uniformizer`, `exists_ramificationIndex` — `GQ2/UnitFiltrationTop.lean`, B13-1/2) and
the residue-graded counts (`UnitFiltrationCounts.exists_gradeCounts` — B13-3/4).  A **single**
uniformizer `π : ↥k` feeds every field, so the `he` normalization `‖2‖ = ‖π‖^e` and the graded
counts share the same `π` (the `↥k → ℚ̄₂` coercion is norm-preserving by `rfl`, so the `↥k`-form
hypotheses discharge the `ℚ̄₂`-form structure fields defeq).  `noncomputable` — the witnesses are
pulled from the existence lemmas by `Classical.choice`.  Discharges the axiom
`GQ2.dyadicUnitFiltration` (`GQ2/Foundations/Axioms.lean`). -/
noncomputable def dyadicUnitFiltration' (k : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] k] : DyadicUnitFiltration k :=
  let hu := exists_uniformizer k
  let π := hu.choose
  let hπne := hu.choose_spec.1
  let hπlt := hu.choose_spec.2.1
  let hmax := hu.choose_spec.2.2
  let hge : ‖(2 : ℚ̄₂)‖ ≤ ‖(π : ↥k)‖ := by
    have h := hmax 2 (by rw [norm_two_k]; exact norm_two_lt_one); rwa [norm_two_k] at h
  let hr := exists_ramificationIndex k hπlt hge hmax
  let hgc := UnitFiltrationCounts.exists_gradeCounts k hπne hπlt hmax
  { π := (π : ℚ̄₂)
    hπ_mem := π.2
    hπ_ne := fun h ↦ hπne (by exact_mod_cast h)
    hπ_lt := hπlt
    hπ_max := fun x hxk hxlt ↦ hmax ⟨x, hxk⟩ hxlt
    e := hr.choose
    he_pos := hr.choose_spec.1
    he := hr.choose_spec.2
    f := hgc.choose
    hf_pos := hgc.choose_spec.1
    card_gr_zero := hgc.choose_spec.2.1
    card_gr := hgc.choose_spec.2.2 }

end GQ2

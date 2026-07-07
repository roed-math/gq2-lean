import GQ2.HilbertLedger

/-!
# P-15f2c2a: the abstract Kummer presentation package

For a degree-2 extension `k ≤ L` of intermediate fields of `ℚ̄₂/ℚ_[2]` and a deep element
`A ∈ L` (`‖A − 1‖ < ‖2‖`), produce the concrete Kummer presentation that
`SectionSix.lemma_6_16` consumes (the paper's "write `L = k(√d)`, `a = u + v√d`", §6.3):

* a **generator** `(d : (↥k)ˣ, δ : ℚ̄₂)` with `δ² = d`, `δ ∈ L`, and the Galois identification
  `G_L = Stab(δ)` inside `G_k` (`fixingSubgroup_subgroupOf_eq_stabilizer`);
* **coordinates** `(u : (↥k)ˣ, v : ↥k)` with `A = u + v·δ` — the constant coordinate is a
  **unit** because `A` is deep: `u = 0` forces `σA = −A` for the conjugation `σ`, whence
  `‖2‖ = ‖(A−1) + (σA−1)‖ ≤ max(‖A−1‖, ‖σA−1‖) = ‖A−1‖ < ‖2‖` (ultrametric +
  `GQ2.norm_galois`).

The exported statement `exists_kummer_presentation` matches `lemma_6_16`'s hypothesis shapes
on the nose.  **Interface note (refinement over the board row)**: the deepness input is the
norm inequality `‖A − 1‖ < ‖2‖` — the consumer (P-15f2c2b) converts `IsDeepUnit` via the
banked `LocalKummer.norm_sub_one_lt_of_isDeepUnit`; this keeps the file free of `IsDeepUnit`
and §6 imports.

**The mathlib gap** is `fixingSubgroup_adjoin_simple`: the fixing subgroup of a simple adjoin
`F⟮δ⟯` is the stabilizer of `δ` — mathlib has the Galois connection `le_iff_le` but not this
equality.  Everything else is assembled from `IntermediateField`
(`extendScalars`/`adjoin`/`eq_of_le_of_finrank_le`), the infinite Galois correspondence
(`InfiniteGalois.fixedField_fixingSubgroup` at `⊥`, giving the conjugation `σδ = −δ` with no
power basis, no `liftNormal`, no minpoly identification — `(σδ)² = δ²` suffices), and
`Submodule.mem_span_pair` for the coordinates.

Paper: §6.3, around eq. (110).  Axioms: **∅** (std-3 target).
-/

namespace GQ2

namespace QuadraticAdjoin

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

open IntermediateField

/-! ## The √-adjoin fixing-subgroup lemma (the mathlib gap) -/

section AdjoinStabilizer

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- **The √-adjoin generator lemma** (not in mathlib): the fixing subgroup of a simple adjoin
`F⟮δ⟯` is exactly the stabilizer of the generator.  `⟹` is `δ ∈ F⟮δ⟯`; `⟸` runs the Galois
connection `IntermediateField.le_iff_le` on the cyclic subgroup `zpowers σ`. -/
theorem fixingSubgroup_adjoin_simple (δ : E) :
    (IntermediateField.adjoin F {δ}).fixingSubgroup
      = MulAction.stabilizer (E ≃ₐ[F] E) δ := by
  ext σ
  rw [IntermediateField.mem_fixingSubgroup_iff, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
  constructor
  · intro h
    exact h δ (IntermediateField.mem_adjoin_simple_self F δ)
  · intro hσ x hx
    have hst : Subgroup.zpowers σ ≤ MulAction.stabilizer (E ≃ₐ[F] E) δ :=
      Subgroup.zpowers_le.mpr
        (MulAction.mem_stabilizer_iff.mpr ((AlgEquiv.smul_def σ δ).trans hσ))
    have hle : IntermediateField.adjoin F {δ}
        ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
      intro f hf
      exact (AlgEquiv.smul_def f δ).symm.trans (MulAction.mem_stabilizer_iff.mp (hst hf))
    exact (IntermediateField.mem_fixedField_iff _ _).mp (hle hx) σ (Subgroup.mem_zpowers σ)

end AdjoinStabilizer

/-! ## The concrete tower `ℚ_[2] ≤ k ≤ L ≤ ℚ̄₂` -/

section Tower

variable (k L : IntermediateField ℚ_[2] ℚ̄₂)

/-- Membership in `⊥ : IntermediateField ↥k ℚ̄₂` is membership in `k` (the base-change of the
bottom element along the subtype algebra map). -/
theorem mem_bot_iff_mem (x : ℚ̄₂) : x ∈ (⊥ : IntermediateField ↥k ℚ̄₂) ↔ x ∈ k := by
  rw [IntermediateField.mem_bot]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

variable {k L}

/-- **Complete the square**: a degree-2 extension of intermediate fields of `ℚ̄₂/ℚ_[2]` has a
square-root generator: `δ ∈ L ∖ k` with `δ² = d ∈ kˣ` and `L = k⟮δ⟯`.  From a primitive
`θ ∈ L ∖ k` (degree 2 is prime) with monic quadratic minimal polynomial `X² + aX + b`, take
`δ := θ + a/2`, `d := a²/4 − b`. -/
theorem exists_sqrt_generator (hkL : k ≤ L)
    (hdeg : Module.finrank ↥k ↥(extendScalars hkL) = 2) :
    ∃ (d : (↥k)ˣ) (δ : ℚ̄₂), δ ^ 2 = ((d : ↥k) : ℚ̄₂) ∧ δ ∈ L ∧ δ ∉ k ∧
      IntermediateField.adjoin ↥k {δ} = extendScalars hkL := by
  haveI hfinL : FiniteDimensional ↥k ↥(extendScalars hkL) :=
    Module.finite_of_finrank_pos (by rw [hdeg]; norm_num)
  -- a primitive element θ ∈ L ∖ k
  have hne : extendScalars hkL ≠ ⊥ := by
    intro h
    rw [h, IntermediateField.finrank_bot] at hdeg
    exact absurd hdeg (by norm_num)
  obtain ⟨θ, hθmem, hθbot⟩ := SetLike.exists_of_lt hne.bot_lt
  have hθk : θ ∉ k := fun h => hθbot ((mem_bot_iff_mem k θ).mpr h)
  have hθL : θ ∈ L := hθmem
  have hθint : IsIntegral ↥k θ := (Algebra.IsAlgebraic.isAlgebraic θ).isIntegral
  haveI hfinθ : FiniteDimensional ↥k ↥(IntermediateField.adjoin ↥k {θ}) :=
    IntermediateField.adjoin.finiteDimensional hθint
  -- k⟮θ⟯ = L by finrank comparison (degree 2 is prime)
  have hle : IntermediateField.adjoin ↥k {θ} ≤ extendScalars hkL := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact hθmem
  have h2le : 2 ≤ Module.finrank ↥k ↥(IntermediateField.adjoin ↥k {θ}) := by
    have hpos : 0 < Module.finrank ↥k ↥(IntermediateField.adjoin ↥k {θ}) := Module.finrank_pos
    have hne1 : Module.finrank ↥k ↥(IntermediateField.adjoin ↥k {θ}) ≠ 1 := fun h1 =>
      hθbot (IntermediateField.finrank_adjoin_simple_eq_one_iff.mp h1)
    omega
  have heq : IntermediateField.adjoin ↥k {θ} = extendScalars hkL :=
    IntermediateField.eq_of_le_of_finrank_le hle (by rw [hdeg]; exact h2le)
  -- the minimal polynomial is a monic quadratic X² + aX + b
  have hpdeg : (minpoly ↥k θ).natDegree = 2 := by
    have hfr := IntermediateField.adjoin.finrank hθint
    rw [heq, hdeg] at hfr
    exact hfr.symm
  set a : ↥k := (minpoly ↥k θ).coeff 1 with ha
  set b : ↥k := (minpoly ↥k θ).coeff 0 with hb
  have hrel : θ ^ 2 + (a : ℚ̄₂) * θ + (b : ℚ̄₂) = 0 := by
    have haev := minpoly.aeval ↥k θ
    rw [Polynomial.aeval_eq_sum_range' (n := 3) (by rw [hpdeg]; norm_num) θ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at haev
    have hc2 : (minpoly ↥k θ).coeff 2 = 1 := by
      have hmc := (minpoly.monic hθint).coeff_natDegree
      rwa [hpdeg] at hmc
    rw [hc2, pow_zero, pow_one, one_smul, Algebra.smul_def, Algebra.smul_def, mul_one] at haev
    calc θ ^ 2 + (a : ℚ̄₂) * θ + (b : ℚ̄₂)
        = (b : ℚ̄₂) + (a : ℚ̄₂) * θ + θ ^ 2 := by ring
      _ = 0 := haev
  -- the discriminant generator δ := 2θ + a, δ² = a² − 4b
  set δ : ℚ̄₂ := 2 * θ + (a : ℚ̄₂) with hδdef
  set dd : ↥k := a ^ 2 - (b + b + b + b) with hdd
  have hδ2 : δ ^ 2 = ((dd : ↥k) : ℚ̄₂) := by
    have hcast : ((dd : ↥k) : ℚ̄₂)
        = (a : ℚ̄₂) ^ 2 - ((b : ℚ̄₂) + (b : ℚ̄₂) + (b : ℚ̄₂) + (b : ℚ̄₂)) := by
      rw [hdd]; push_cast; ring
    rw [hδdef, hcast]
    linear_combination (4 : ℚ̄₂) * hrel
  have h2k : (2 : ℚ̄₂) ∈ k := by simp
  have hθrec : θ = (δ - (a : ℚ̄₂)) * (2 : ℚ̄₂)⁻¹ := by
    rw [hδdef]
    field_simp
    ring
  have hδk : δ ∉ k := by
    intro hδmem
    refine hθk ?_
    rw [hθrec]
    exact k.mul_mem (k.sub_mem hδmem a.2) (k.inv_mem h2k)
  have hδL : δ ∈ L := by
    rw [hδdef]
    refine L.add_mem ?_ (hkL a.2)
    rw [two_mul]
    exact L.add_mem hθL hθL
  have hdd0 : dd ≠ 0 := by
    intro h0
    refine hδk ?_
    have hz : δ ^ 2 = 0 := by rw [hδ2, h0]; simp
    have hδ0 : δ = 0 := (pow_eq_zero_iff two_ne_zero).mp hz
    rw [hδ0]
    exact k.zero_mem
  have hadj : IntermediateField.adjoin ↥k {δ} = IntermediateField.adjoin ↥k {θ} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff, hδdef]
      refine add_mem ?_ ((IntermediateField.adjoin ↥k {θ}).algebraMap_mem a)
      rw [two_mul]
      exact add_mem (IntermediateField.mem_adjoin_simple_self ↥k θ)
        (IntermediateField.mem_adjoin_simple_self ↥k θ)
    · rw [IntermediateField.adjoin_simple_le_iff, hθrec]
      refine mul_mem (sub_mem (IntermediateField.mem_adjoin_simple_self ↥k δ)
        ((IntermediateField.adjoin ↥k {δ}).algebraMap_mem a)) (inv_mem ?_)
      simp
  exact ⟨Units.mk0 dd hdd0, δ, hδ2, hδL, hδk, hadj.trans heq⟩

/-- **Coordinates** in the `{1, δ}` basis: every element of `L = k⟮δ⟯` is `u + v·δ` with
`u, v ∈ k` (the span of the independent pair `{1, δ}` fills the 2-dimensional `L` by
finrank comparison; extract with `Submodule.mem_span_pair`). -/
theorem exists_coords (hkL : k ≤ L)
    (hdeg : Module.finrank ↥k ↥(extendScalars hkL) = 2)
    {δ : ℚ̄₂} (hadj : IntermediateField.adjoin ↥k {δ} = extendScalars hkL)
    {A : ℚ̄₂} (hAL : A ∈ L) :
    ∃ u v : ↥k, A = ((u : ↥k) : ℚ̄₂) + ((v : ↥k) : ℚ̄₂) * δ := by
  have hδint : IsIntegral ↥k δ := (Algebra.IsAlgebraic.isAlgebraic δ).isIntegral
  -- the minimal polynomial of δ is a monic quadratic
  have hqdeg : (minpoly ↥k δ).natDegree = 2 := by
    have hfr := IntermediateField.adjoin.finrank hδint
    rw [hadj, hdeg] at hfr
    exact hfr.symm
  have hqmonic : (minpoly ↥k δ).Monic := minpoly.monic hδint
  have hq1 : minpoly ↥k δ ≠ 1 := by
    intro h1
    rw [h1, Polynomial.natDegree_one] at hqdeg
    exact absurd hqdeg (by norm_num)
  -- A is a polynomial in δ
  have hA' : A ∈ IntermediateField.adjoin ↥k {δ} := by rw [hadj]; exact hAL
  have hAalg : A ∈ Algebra.adjoin ↥k ({δ} : Set ℚ̄₂) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic (R := ↥k) δ)]
    exact hA'
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hAalg
  obtain ⟨p, hp⟩ := hAalg
  -- reduce mod the minimal polynomial: the remainder is linear
  set r := p %ₘ minpoly ↥k δ with hr
  have hAr : (Polynomial.aeval δ) r = A := by
    have hsplit : r + minpoly ↥k δ * (p /ₘ minpoly ↥k δ) = p :=
      Polynomial.modByMonic_add_div p (minpoly ↥k δ)
    calc (Polynomial.aeval δ) r
        = (Polynomial.aeval δ) r
          + (Polynomial.aeval δ) (minpoly ↥k δ) * (Polynomial.aeval δ) (p /ₘ minpoly ↥k δ) := by
          rw [minpoly.aeval, zero_mul, add_zero]
      _ = (Polynomial.aeval δ) p := by rw [← map_mul, ← map_add, hsplit]
      _ = A := hp
  have hrdeg : r.natDegree < 2 := by
    have hlt := Polynomial.natDegree_modByMonic_lt p hqmonic hq1
    rwa [hqdeg] at hlt
  -- expand the linear remainder
  refine ⟨r.coeff 0, r.coeff 1, ?_⟩
  have hexp := Polynomial.aeval_eq_sum_range' hrdeg δ
  rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one,
    Algebra.smul_def, Algebra.smul_def, mul_one] at hexp
  calc A = (Polynomial.aeval δ) r := hAr.symm
    _ = ((r.coeff 0 : ↥k) : ℚ̄₂) + ((r.coeff 1 : ↥k) : ℚ̄₂) * δ := hexp

/-- **The conjugation**: some `↥k`-automorphism of `ℚ̄₂` negates `δ`.  Since `δ ∉ k`, the
infinite Galois correspondence over `↥k` (at `⊥`, via `fixingSubgroup_bot`) produces a `σ`
moving `δ`; then `(σδ)² = σ(δ²) = d = δ²` forces `σδ = −δ` — no minimal polynomial needed. -/
theorem exists_conj {δ : ℚ̄₂} {d : ↥k} (hδ2 : δ ^ 2 = (d : ℚ̄₂)) (hδk : δ ∉ k) :
    ∃ σ : ℚ̄₂ ≃ₐ[↥k] ℚ̄₂, σ δ = -δ := by
  have hbot : δ ∉ (⊥ : IntermediateField ↥k ℚ̄₂) := fun h => hδk ((mem_bot_iff_mem k δ).mp h)
  have htop : IntermediateField.fixedField (⊤ : Subgroup (ℚ̄₂ ≃ₐ[↥k] ℚ̄₂)) = ⊥ := by
    rw [← IntermediateField.fixingSubgroup_bot (F := ↥k) (E := ℚ̄₂)]
    exact InfiniteGalois.fixedField_fixingSubgroup ⊥
  have hmove : ∃ σ : ℚ̄₂ ≃ₐ[↥k] ℚ̄₂, σ δ ≠ δ := by
    by_contra hall
    rw [not_exists] at hall
    refine hbot (htop ▸ (IntermediateField.mem_fixedField_iff _ _).mpr ?_)
    intro f _
    exact not_not.mp (hall f)
  obtain ⟨σ, hσδ⟩ := hmove
  refine ⟨σ, ?_⟩
  have hsq : (σ δ + δ) * (σ δ - δ) = 0 := by
    have hcomm : σ (δ ^ 2) = δ ^ 2 := by
      rw [hδ2]; exact σ.commutes d
    have hz : σ δ ^ 2 - δ ^ 2 = 0 := by rw [← map_pow, hcomm, sub_self]
    calc (σ δ + δ) * (σ δ - δ) = σ δ ^ 2 - δ ^ 2 := by ring
      _ = 0 := hz
  rcases mul_eq_zero.mp hsq with h | h
  · exact eq_neg_of_add_eq_zero_left h
  · exact absurd (sub_eq_zero.mp h) hσδ

/-- **Unit coordinate**: if `A = u + v·δ` is deep (`‖A − 1‖ < ‖2‖`) then `u ≠ 0` — otherwise
the conjugation gives `σA = −A`, so `(A−1) + (σA−1) = −2` while both summands have norm
`< ‖2‖` (Galois invariance `GQ2.norm_galois` + ultrametric inequality): contradiction.
Uniform in `v` (the `v = 0` sub-case is `A = 0`, killed by the same norms). -/
theorem coord_unit {δ : ℚ̄₂} (σ : ℚ̄₂ ≃ₐ[↥k] ℚ̄₂) (hσ : σ δ = -δ)
    {A : ℚ̄₂} (hA1 : ‖A - 1‖ < ‖(2 : ℚ̄₂)‖)
    {u v : ↥k} (hAuv : A = ((u : ↥k) : ℚ̄₂) + ((v : ↥k) : ℚ̄₂) * δ) :
    u ≠ 0 := by
  rintro rfl
  have hA : A = ((v : ↥k) : ℚ̄₂) * δ := by rw [hAuv, ZeroMemClass.coe_zero, zero_add]
  have hσA : σ A = -A := by
    have hσv : σ ((v : ↥k) : ℚ̄₂) = ((v : ↥k) : ℚ̄₂) := σ.commutes v
    rw [hA, map_mul, hσ, hσv]
    ring
  have hnorm : ‖σ A - 1‖ = ‖A - 1‖ := by
    have h1 : σ A - 1 = (AlgEquiv.restrictScalars ℚ_[2] σ) • (A - 1) := by
      rw [AlgEquiv.smul_def]
      show σ A - 1 = σ (A - 1)
      rw [map_sub, map_one]
    rw [h1, norm_galois]
  have hle : ‖(2 : ℚ̄₂)‖ ≤ max ‖A - 1‖ ‖σ A - 1‖ := by
    calc ‖(2 : ℚ̄₂)‖ = ‖(A - 1) + (σ A - 1)‖ := by
          rw [hσA]; rw [show (A - 1) + (-A - 1) = -2 by ring, norm_neg]
      _ ≤ max ‖A - 1‖ ‖σ A - 1‖ := IsUltrametricDist.norm_add_le_max _ _
  rw [hnorm, max_self] at hle
  exact absurd (lt_of_le_of_lt hle hA1) (lt_irrefl _)

/-- The `subgroupOf`-packaged form of `fixingSubgroup_adjoin_simple` at the tower
`ℚ_[2] ≤ k ≤ L ≤ ℚ̄₂`: inside `G_k`, fixing `L` pointwise is stabilizing `δ`.  Elements of
`k.fixingSubgroup` upgrade to `↥k`-automorphisms along `IntermediateField.fixingSubgroupEquiv`
(same underlying function), `L`-membership transports along `mem_extendScalars` (`Iff.rfl`)
and `hadj`. -/
theorem fixingSubgroup_subgroupOf_eq_stabilizer (hkL : k ≤ L) {δ : ℚ̄₂}
    (hadj : IntermediateField.adjoin ↥k {δ} = extendScalars hkL) :
    (L.fixingSubgroup).subgroupOf (k.fixingSubgroup)
      = (MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf (k.fixingSubgroup) := by
  have key := fixingSubgroup_adjoin_simple (F := ↥k) (E := ℚ̄₂) δ
  rw [hadj] at key
  ext g
  have hmem := SetLike.ext_iff.mp key (IntermediateField.fixingSubgroupEquiv k g)
  simp only [IntermediateField.mem_fixingSubgroup_iff, MulAction.mem_stabilizer_iff,
    AlgEquiv.smul_def] at hmem
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    IntermediateField.mem_fixingSubgroup_iff, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
  exact hmem

end Tower

/-! ## The exported package -/

section Export

variable {k L : IntermediateField ℚ_[2] ℚ̄₂}

/-- **The abstract Kummer presentation package** (P-15f2c2a, exported interface): a degree-2
extension `k ≤ L` inside `ℚ̄₂/ℚ_[2]` together with a deep element `A ∈ L` yields the full
generator-and-coordinates data of `SectionSix.lemma_6_16`: `d, δ` with `δ² = d`, `δ ∈ L`,
the fixing-subgroup/stabilizer identification, and `A = u + v·δ` with `u` a **unit**.

Consumer (P-15f2c2b) supplies `hdeg` from the index-2 hypothesis (fixing-index → degree
bridge) and `hA1` from `IsDeepUnit` via `LocalKummer.norm_sub_one_lt_of_isDeepUnit`. -/
theorem exists_kummer_presentation (hkL : k ≤ L)
    (hdeg : Module.finrank ↥k ↥(extendScalars hkL) = 2)
    {A : ℚ̄₂} (hAL : A ∈ L) (hA1 : ‖A - 1‖ < ‖(2 : ℚ̄₂)‖) :
    ∃ (d : (↥k)ˣ) (δ : ℚ̄₂) (u : (↥k)ˣ) (v : ↥k),
      δ ^ 2 = ((d : ↥k) : ℚ̄₂) ∧ δ ∈ L ∧
      (L.fixingSubgroup).subgroupOf (k.fixingSubgroup)
        = (MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf (k.fixingSubgroup) ∧
      A = ((u : ↥k) : ℚ̄₂) + ((v : ↥k) : ℚ̄₂) * δ := by
  obtain ⟨d, δ, hδ2, hδL, hδk, hadj⟩ := exists_sqrt_generator hkL hdeg
  obtain ⟨u₀, v, hAuv⟩ := exists_coords hkL hdeg hadj hAL
  obtain ⟨σ, hσ⟩ := exists_conj (d := (d : ↥k)) hδ2 hδk
  have hu : u₀ ≠ 0 := coord_unit σ hσ hA1 hAuv
  exact ⟨d, δ, Units.mk0 u₀ hu, v, hδ2, hδL,
    fixingSubgroup_subgroupOf_eq_stabilizer hkL hadj, hAuv⟩

end Export

end QuadraticAdjoin

end GQ2

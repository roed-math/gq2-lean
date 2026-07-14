import Mathlib
import GQ2.TeichmullerLift
import GQ2.UnitFiltrationCounts

/-!
# B11b-1 — the quadratic layer · B11b-2 — the residue layer

Discharges axiom **B11b** (`unramifiedQuadratic_units_are_norms`) in-repo (landed 2026-07-09,
census 11 → 10; archived board + plan at `docs/orchestration/b11b-tickets.md` /
`b11b-proof-plan.md`).  This file is the **quadratic layer**
(lane B, §1(Q)+(D)): the conjugation `σ`, `k`-coordinates on `k⟮δa⟯`, the norm/trace forms, and
the degenerate `δa ∈ k` case.  Imports Mathlib only (the B13 filtration and the σ-free
Teichmüller bricks of `GQ2.TeichmullerLift` enter later, at the engine B11b-3).

For `k ≤ ℚ̄₂` finite and `δa ∈ ℚ̄₂` with `δa² = a ∈ kˣ`, `δa ∉ k`:

* `exists_conj` — a global `↥k`-algebra involution `σ : ℚ̄₂ ≃ₐ[↥k] ℚ̄₂` with `σδa = −δa`
  (infinite Galois correspondence; the B11b-0 route, `QuadraticAdjoin.exists_conj` re-ported);
* `norm_galois`/`norm_conj_eq` — `σ` preserves the spectral norm;
* `conj_apply`, `norm_coord`, `trace_coord` — `σ(x + yδa) = x − yδa`, `N(x+yδa) = x² − ay²`,
  `s(x+yδa) = 2x` (`x, y ∈ k`);
* `exists_coords` — every `z ∈ ↥k⟮δa⟯` is `x + yδa` (`modByMonic` remainder);
* `conj_fixed_iff` — on `↥k⟮δa⟯`, `σz = z ↔ z ∈ k`;
* `norm_form_of_mem` — the degenerate case: if `δa ∈ k` every `u ∈ ↥k` is `x² − ay²`.

**B11b-2 (lane B closure, plan §1(R)3 + board "s̄ surjective")** — the residue layer, appended
below over the quadratic layer + the σ-free bricks of `GQ2.TeichmullerLift`:

* `le_of_conj_residue_trivial` — **the crux** `σ̄ = id ⟹ L ≤ k`, entirely in norm vocabulary
  (`σ̄ = id` ⟺ `∀ z ∈ O_L, ‖σz − z‖ < 1`): a norm-one `z` has a Teichmüller representative
  `ω` (`ω^{q−1} = 1`, `ω ≡ z`); `σω` is a root of unity of the same **odd** order in the same
  residue class, so odd-root separation forces `σω = ω`, i.e. `ω ∈ k` — every residue of `L`
  lies in `k`, and successive approximation closes `L ≤ k`.
* `exists_conj_unit` — contrapositive at `δa ∈ L ∖ k`: some `z₁ ∈ O_L` has `‖σz₁ − z₁‖ = 1`
  ("`σ̄ ≠ id`").
* `trace_covers` — **the engine deliverable** (consumed by the B11b-3 increments): the trace
  `s(z) = z + σz` covers the integral elements of `k` *exactly* (not just mod `𝔪`): writing
  `z₁ = x + yδa`, the unit trace value `t := s(z₁) = 2x ∈ k` has `‖t‖ = 1` (char-2 shift:
  `s(z₁)` and `σz₁ − z₁` differ by `2z₁`), and `k`-linearity of `s` scales it to any target —
  no residue-field or `l^σ̄`-linear-algebra interface is needed.

The residue-field inputs of the crux stay **hypothesis-abstracted** (`q`, `hqn`, `hqodd`,
`hlag` — Lagrange `‖z^q − z‖ < 1` at `L`; `π`, `hπmax` — the shared uniformizer): B11b-3
discharges them from the B13 filtration at `L` (`q := 2^F`, `q − 1` odd).
-/

namespace GQ2.UnramifiedQuadraticNorms

open IntermediateField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## Galois invariance of the spectral norm -/

/-- **Galois invariance of the spectral norm on `ℚ̄₂`** (re-port of `HilbertLedger.norm_galois`,
which is downstream of the axiom file).  The extension norm on an algebraic extension of a
complete field is unique, so it is invariant under every `ℚ₂`-algebra automorphism. -/
theorem norm_galois (g : ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂) (x : ℚ̄₂) : ‖g x‖ = ‖x‖ := by
  rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[2], NormedAlgebra.norm_eq_spectralNorm ℚ_[2]]
  exact (spectralNorm_eq_of_equiv g x).symm

variable (k : IntermediateField ℚ_[2] ℚ̄₂)

/-- `σ` preserves the spectral norm (`σ` is `↥k`-linear, a fortiori `ℚ₂`-linear). -/
theorem norm_conj_eq (σ : ℚ̄₂ ≃ₐ[↥k] ℚ̄₂) (x : ℚ̄₂) : ‖σ x‖ = ‖x‖ :=
  norm_galois (σ.restrictScalars ℚ_[2]) x

/-! ## The `⊥`-membership port and the conjugation -/

/-- Membership in `⊥ : IntermediateField ↥k ℚ̄₂` is membership in `k` (re-port of
`QuadraticAdjoin.mem_bot_iff_mem`). -/
theorem mem_bot_iff_mem (x : ℚ̄₂) : x ∈ (⊥ : IntermediateField ↥k ℚ̄₂) ↔ x ∈ k := by
  rw [IntermediateField.mem_bot]
  constructor
  · rintro ⟨y, rfl⟩; exact y.2
  · intro hx; exact ⟨⟨x, hx⟩, rfl⟩

variable {k}

/-- **The conjugation** `σ : ℚ̄₂ ≃ₐ[↥k] ℚ̄₂` with `σδa = −δa` (re-port of
`QuadraticAdjoin.exists_conj`): built from the infinite Galois correspondence
(`fixedField ⊤ = ⊥`), with `(σδa)² = δa²` forcing the sign. -/
theorem exists_conj {δa : ℚ̄₂} {d : ↥k} (hδ2 : δa ^ 2 = (d : ℚ̄₂)) (hδk : δa ∉ k) :
    ∃ σ : ℚ̄₂ ≃ₐ[↥k] ℚ̄₂, σ δa = -δa := by
  have hbot : δa ∉ (⊥ : IntermediateField ↥k ℚ̄₂) := fun h => hδk ((mem_bot_iff_mem k δa).mp h)
  have htop : IntermediateField.fixedField
      (⊤ : Subgroup (ℚ̄₂ ≃ₐ[↥k] ℚ̄₂)) = ⊥ := by
    rw [← IntermediateField.fixingSubgroup_bot (F := ↥k) (E := ℚ̄₂)]
    exact InfiniteGalois.fixedField_fixingSubgroup ⊥
  have hmove : ∃ σ : ℚ̄₂ ≃ₐ[↥k] ℚ̄₂, σ δa ≠ δa := by
    by_contra hall
    rw [not_exists] at hall
    refine hbot (htop ▸ (IntermediateField.mem_fixedField_iff _ _).mpr ?_)
    intro f _
    exact not_not.mp (hall f)
  obtain ⟨σ, hσδ⟩ := hmove
  refine ⟨σ, ?_⟩
  have hsq : (σ δa + δa) * (σ δa - δa) = 0 := by
    have hc : σ δa ^ 2 = δa ^ 2 := by rw [← map_pow, hδ2]; exact σ.commutes d
    linear_combination hc
  rcases mul_eq_zero.mp hsq with h | h
  · exact eq_neg_of_add_eq_zero_left h
  · exact absurd (sub_eq_zero.mp h) hσδ

/-! ## Coordinate action, norm, and trace -/

/-- `σ` fixes the base: `σ (x : ℚ̄₂) = x` for `x ∈ ↥k`. -/
theorem conj_base (σ : ℚ̄₂ ≃ₐ[↥k] ℚ̄₂) (x : ↥k) : σ (x : ℚ̄₂) = (x : ℚ̄₂) := σ.commutes x

/-- The conjugation on `k`-coordinates: `σ(x + yδa) = x − yδa`. -/
theorem conj_apply {δa : ℚ̄₂} {σ : ℚ̄₂ ≃ₐ[↥k] ℚ̄₂} (hσ : σ δa = -δa) (x y : ↥k) :
    σ ((x : ℚ̄₂) + (y : ℚ̄₂) * δa) = (x : ℚ̄₂) - (y : ℚ̄₂) * δa := by
  rw [map_add, map_mul, conj_base, conj_base, hσ]; ring

/-- The **norm form**: `(x + yδa)(x − yδa) = x² − a y²` in `↥k` (with `δa² = a`). -/
theorem norm_coord {δa : ℚ̄₂} {a : (↥k)ˣ} (hδa : δa ^ 2 = ((a : ↥k) : ℚ̄₂)) (x y : ↥k) :
    ((x : ℚ̄₂) + (y : ℚ̄₂) * δa) * ((x : ℚ̄₂) - (y : ℚ̄₂) * δa)
      = ((x ^ 2 - (a : ↥k) * y ^ 2 : ↥k) : ℚ̄₂) := by
  push_cast
  linear_combination (- (y : ℚ̄₂) ^ 2) * hδa

/-- The **trace form**: `(x + yδa) + (x − yδa) = x + x` (`= 2x ∈ k`). -/
theorem trace_coord {δa : ℚ̄₂} (x y : ↥k) :
    ((x : ℚ̄₂) + (y : ℚ̄₂) * δa) + ((x : ℚ̄₂) - (y : ℚ̄₂) * δa) = ((x + x : ↥k) : ℚ̄₂) := by
  push_cast; ring

/-! ## Coordinates exist on the adjoin -/

/-- The `↥k`-minimal polynomial of `δa` (with `δa² = d`, `δa ∉ k`) has degree `2`. -/
theorem minpoly_natDegree_eq_two {δa : ℚ̄₂} {d : ↥k} (hδ2 : δa ^ 2 = (d : ℚ̄₂)) (hδk : δa ∉ k) :
    (minpoly ↥k δa).natDegree = 2 := by
  have hδint : IsIntegral ↥k δa := (Algebra.IsAlgebraic.isAlgebraic δa).isIntegral
  -- minpoly divides X² − C d, so natDegree ≤ 2
  have hdvd : minpoly ↥k δa ∣ Polynomial.X ^ 2 - Polynomial.C d := by
    apply minpoly.dvd
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hδ2]
    simp
  have hle : (minpoly ↥k δa).natDegree ≤ 2 := by
    have hmonic : (Polynomial.X ^ 2 - Polynomial.C d).Monic := by
      apply Polynomial.monic_X_pow_sub_C
      norm_num
    have := Polynomial.natDegree_le_of_dvd hdvd hmonic.ne_zero
    simpa using this
  -- natDegree ≠ 1 (else δa ∈ k) and ≠ 0 (minpoly nonconstant)
  have hne1 : (minpoly ↥k δa).natDegree ≠ 1 := by
    intro h1
    apply hδk
    apply (mem_bot_iff_mem k δa).mp
    apply IntermediateField.finrank_adjoin_simple_eq_one_iff.mp
    rw [IntermediateField.adjoin.finrank hδint]
    exact h1
  have hne0 : (minpoly ↥k δa).natDegree ≠ 0 := by
    intro h0
    have := minpoly.natDegree_pos hδint
    omega
  omega

/-- **Coordinates**: every `z ∈ ↥k⟮δa⟯` is `x + yδa` for unique `x, y ∈ k`
(re-port of `QuadraticAdjoin.exists_coords`, `p %ₘ minpoly` remainder). -/
theorem exists_coords {δa : ℚ̄₂} {d : ↥k} (hδ2 : δa ^ 2 = (d : ℚ̄₂)) (hδk : δa ∉ k)
    {z : ℚ̄₂} (hz : z ∈ IntermediateField.adjoin ↥k {δa}) :
    ∃ x y : ↥k, z = (x : ℚ̄₂) + (y : ℚ̄₂) * δa := by
  have hδint : IsIntegral ↥k δa := (Algebra.IsAlgebraic.isAlgebraic δa).isIntegral
  have hqdeg : (minpoly ↥k δa).natDegree = 2 := minpoly_natDegree_eq_two hδ2 hδk
  have hzalg : z ∈ Algebra.adjoin ↥k ({δa} : Set ℚ̄₂) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic (R := ↥k) δa)]
    exact hz
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hzalg
  obtain ⟨p, hp⟩ := hzalg
  have hmne1 : minpoly ↥k δa ≠ 1 := by
    intro h; rw [h, Polynomial.natDegree_one] at hqdeg; exact absurd hqdeg (by norm_num)
  set r := p %ₘ minpoly ↥k δa with hr
  have hzr : (Polynomial.aeval δa) r = z := by
    have hsplit : r + minpoly ↥k δa * (p /ₘ minpoly ↥k δa) = p :=
      Polynomial.modByMonic_add_div p (minpoly ↥k δa)
    calc (Polynomial.aeval δa) r
        = (Polynomial.aeval δa) r
          + (Polynomial.aeval δa) (minpoly ↥k δa) * (Polynomial.aeval δa) (p /ₘ minpoly ↥k δa) := by
          rw [minpoly.aeval, zero_mul, add_zero]
      _ = (Polynomial.aeval δa) p := by rw [← map_mul, ← map_add, hsplit]
      _ = z := hp
  have hrdeg : r.natDegree ≤ 1 := by
    have hlt : r.natDegree < (minpoly ↥k δa).natDegree :=
      Polynomial.natDegree_modByMonic_lt p (minpoly.monic hδint) hmne1
    omega
  refine ⟨r.coeff 0, r.coeff 1, ?_⟩
  rw [← hzr, Polynomial.aeval_eq_sum_range' (n := 2) (by omega) δa,
    Finset.sum_range_succ, Finset.sum_range_one]
  simp [Algebra.smul_def]

/-- On `↥k⟮δa⟯`, `σ` fixes exactly `k`: `σz = z ↔ z ∈ k`. -/
theorem conj_fixed_iff {δa : ℚ̄₂} {d : ↥k} (hδ2 : δa ^ 2 = (d : ℚ̄₂)) (hδk : δa ∉ k)
    {σ : ℚ̄₂ ≃ₐ[↥k] ℚ̄₂} (hσ : σ δa = -δa) {z : ℚ̄₂} (hz : z ∈ IntermediateField.adjoin ↥k {δa}) :
    σ z = z ↔ z ∈ k := by
  have hδa0 : δa ≠ 0 := fun h => hδk (h ▸ k.zero_mem)
  constructor
  · intro h
    obtain ⟨x, y, rfl⟩ := exists_coords hδ2 hδk hz
    rw [conj_apply hσ] at h
    have hy : (y : ℚ̄₂) = 0 := by
      have h2 : (2 : ℚ̄₂) * ((y : ℚ̄₂) * δa) = 0 := by linear_combination -h
      rcases mul_eq_zero.mp h2 with h' | h'
      · exact absurd h' (by norm_num)
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact h''
        · exact absurd h'' hδa0
    rw [hy, zero_mul, add_zero]
    exact x.2
  · intro hzk
    exact conj_base σ ⟨z, hzk⟩

/-! ## The degenerate case `δa ∈ k` -/

/-- **Degenerate case**: if `δa ∈ k` (so `a` is already a square in `k`), every `u ∈ ↥k` is a
norm `x² − a y²` — solve `(x − δ'y)(x + δ'y) = u` with `x = (1+u)/2`, `y = (u−1)/(2δ')`. -/
theorem norm_form_of_mem {a : (↥k)ˣ} {δa : ℚ̄₂} (hδa : δa ^ 2 = ((a : ↥k) : ℚ̄₂))
    (hmem : δa ∈ k) (u : ↥k) :
    ∃ x y : ↥k, (u : ↥k) = x ^ 2 - (a : ↥k) * y ^ 2 := by
  set δ' : ↥k := ⟨δa, hmem⟩ with hδ'
  have hδ'2 : δ' ^ 2 = (a : ↥k) := by
    have : ((δ' ^ 2 : ↥k) : ℚ̄₂) = ((a : ↥k) : ℚ̄₂) := by push_cast [hδ']; exact hδa
    exact_mod_cast this
  have hδ'0 : δ' ≠ 0 := by
    intro h
    apply a.ne_zero
    rw [← hδ'2, h, zero_pow]; norm_num
  refine ⟨(1 + u) / 2, (u - 1) / (2 * δ'), ?_⟩
  have h20 : (2 : ↥k) ≠ 0 := by norm_num
  field_simp
  linear_combination (-(u - 1) ^ 2) * hδ'2

/-! ## The residue layer (B11b-2, lane B closure) -/

section ResidueLayer

open TeichmullerLift

/-- `‖2‖ < 1` in `ℚ̄₂` (the spectral norm extends the 2-adic norm). -/
lemma norm_two_lt_one : ‖(2 : ℚ̄₂)‖ < 1 := by
  have h : (2 : ℚ̄₂) = algebraMap ℚ_[2] ℚ̄₂ 2 := (map_ofNat _ 2).symm
  rw [h, norm_algebraMap' (𝕜' := ℚ̄₂) (2 : ℚ_[2])]
  exact Padic.norm_p_lt_one

variable {k L : IntermediateField ℚ_[2] ℚ̄₂}

/-- **The residue crux** (plan §1(R)3, "`σ̄ = id ⟹ L = k`"), in pure norm vocabulary.  If the
conjugation is trivial on residues — `‖σz − z‖ < 1` for every integral `z ∈ L` — then `L ≤ k`:
a norm-one `z ∈ L` has a Teichmüller representative `ω` (`exists_teichmuller`, using the
Lagrange input `hlag`), whose conjugate `σω` is a root of unity of the same odd order `q − 1`
in the same residue class, so odd-root separation (`norm_sub_eq_one_of_pow_eq_one`) forces
`σω = ω`, i.e. `ω ∈ k` (`conj_fixed_iff`); thus every residue of `L` lies in `k`, and
successive approximation (`le_of_shared_uniformizer`) closes `L ≤ k`.

The residue-field inputs are hypothesis-abstracted (B11b-3 supplies them from the B13
filtration at `L`): `q` with `‖q‖ < 1` and `q − 1` odd (`q = 2^F`), Lagrange `hlag`, and the
shared uniformizer `π`. -/
theorem le_of_conj_residue_trivial [FiniteDimensional ℚ_[2] k] [FiniteDimensional ℚ_[2] L]
    (hkL : k ≤ L)
    {δa : ℚ̄₂} {d : ↥k} (hδ2 : δa ^ 2 = (d : ℚ̄₂)) (hδk : δa ∉ k)
    {σ : ℚ̄₂ ≃ₐ[↥k] ℚ̄₂} (hσ : σ δa = -δa)
    (hLadj : ∀ z ∈ L, z ∈ IntermediateField.adjoin ↥k {δa})
    {π : ℚ̄₂} (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ z ∈ L, ‖z‖ < 1 → ‖z‖ ≤ ‖π‖)
    {q : ℕ} (hqn : ‖(q : ℚ̄₂)‖ < 1) (hqodd : Odd (q - 1))
    (hlag : ∀ z ∈ L, ‖z‖ ≤ 1 → ‖z ^ q - z‖ < 1)
    (hσid : ∀ z ∈ L, ‖z‖ ≤ 1 → ‖σ z - z‖ < 1) :
    L ≤ k := by
  refine le_of_shared_uniformizer k L hkL hπk hπ0 hπ1 hπmax ?_
  intro z hzL hz1
  rcases lt_or_eq_of_le hz1 with hzlt | hzeq
  · exact ⟨0, k.zero_mem, by simpa using hzlt⟩
  -- `‖z‖ = 1`: take the Teichmüller representative
  obtain ⟨ω, hωL, hωfix, hω1, hωz⟩ := exists_teichmuller L hqn hzL hzeq (hlag z hzL hz1)
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h, norm_zero] at hω1
    exact zero_ne_one hω1
  have hωq1 : ω ^ (q - 1) = 1 := by
    have h : ω ^ (q - 1) * ω = 1 * ω := by
      rw [one_mul, ← pow_succ, show q - 1 + 1 = q by
        have := hqodd.pos
        omega]
      exact hωfix
    exact mul_right_cancel₀ hω0 h
  have hσωq1 : (σ ω) ^ (q - 1) = 1 := by rw [← map_pow, hωq1, map_one]
  -- `σω` lies in the same residue class as `ω`
  have hωclose : ‖σ ω - ω‖ < 1 := by
    have hdecomp : σ ω - ω = σ (ω - z) + (σ z - z) + (z - ω) := by
      rw [map_sub]; ring
    have h1 : ‖σ (ω - z)‖ < 1 := by rw [norm_conj_eq]; exact hωz
    have h2 : ‖σ z - z‖ < 1 := hσid z hzL hz1
    have h3 : ‖z - ω‖ < 1 := by rw [norm_sub_rev]; exact hωz
    calc ‖σ ω - ω‖ = ‖σ (ω - z) + (σ z - z) + (z - ω)‖ := by rw [hdecomp]
      _ ≤ max (max ‖σ (ω - z)‖ ‖σ z - z‖) ‖z - ω‖ :=
          le_trans (IsUltrametricDist.norm_add_le_max _ _)
            (max_le_max (IsUltrametricDist.norm_add_le_max _ _) le_rfl)
      _ < 1 := by
          rw [max_lt_iff, max_lt_iff]
          exact ⟨⟨h1, h2⟩, h3⟩
  -- odd-root separation forces `σω = ω`, hence `ω ∈ k`
  have hσω : σ ω = ω := by
    by_contra hne
    have hsep := norm_sub_eq_one_of_pow_eq_one hqodd hσωq1 hωq1 hne
    rw [hsep] at hωclose
    exact lt_irrefl _ hωclose
  have hωk : ω ∈ k := (conj_fixed_iff hδ2 hδk hσ (hLadj ω hωL)).mp hσω
  exact ⟨ω, hωk, by rwa [norm_sub_rev]⟩

/-- **`σ̄ ≠ id`** (the board's B11b-2 lane-B item, contrapositive form): with `δa ∈ L ∖ k`
witnessing `¬(L ≤ k)`, some integral `z₁ ∈ L` has `‖σz₁ − z₁‖ = 1` — the conjugation moves a
residue. -/
theorem exists_conj_unit [FiniteDimensional ℚ_[2] k] [FiniteDimensional ℚ_[2] L]
    (hkL : k ≤ L)
    {δa : ℚ̄₂} {d : ↥k} (hδ2 : δa ^ 2 = (d : ℚ̄₂)) (hδk : δa ∉ k) (hδaL : δa ∈ L)
    {σ : ℚ̄₂ ≃ₐ[↥k] ℚ̄₂} (hσ : σ δa = -δa)
    (hLadj : ∀ z ∈ L, z ∈ IntermediateField.adjoin ↥k {δa})
    {π : ℚ̄₂} (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ z ∈ L, ‖z‖ < 1 → ‖z‖ ≤ ‖π‖)
    {q : ℕ} (hqn : ‖(q : ℚ̄₂)‖ < 1) (hqodd : Odd (q - 1))
    (hlag : ∀ z ∈ L, ‖z‖ ≤ 1 → ‖z ^ q - z‖ < 1) :
    ∃ z₁, z₁ ∈ L ∧ ‖z₁‖ ≤ 1 ∧ ‖σ z₁ - z₁‖ = 1 := by
  by_contra hnone
  push Not at hnone
  have hσid : ∀ z ∈ L, ‖z‖ ≤ 1 → ‖σ z - z‖ < 1 := by
    intro z hzL hz1
    have hle : ‖σ z - z‖ ≤ 1 := by
      rw [sub_eq_add_neg]
      refine le_trans (IsUltrametricDist.norm_add_le_max _ _) ?_
      rw [norm_neg, norm_conj_eq]
      exact max_le hz1 hz1
    exact lt_of_le_of_ne hle (hnone z hzL hz1)
  exact hδk (le_of_conj_residue_trivial hkL hδ2 hδk hσ hLadj hπk hπ0 hπ1 hπmax hqn hqodd
    hlag hσid hδaL)

/-- **Trace coverage** (the engine deliverable, board "`s̄` surjective onto `⊇ k̄`" —
strengthened to an *exact* statement).  The trace `s(z) = z + σz` hits every integral element
of `k` from an integral element of `L`: the witness `z₁` of `σ̄ ≠ id` has unit trace value
`t := s(z₁) = 2x ∈ k` (`z₁ = x + yδa`; `s(z₁)` differs from `σz₁ − z₁` by `2z₁`, of norm
`< 1`), and `s` is `k`-linear, so `z := (c/t)·z₁` does it.  No residue-field interface and no
`mod 𝔪` bookkeeping: the covering is on the nose. -/
theorem trace_covers [FiniteDimensional ℚ_[2] k] [FiniteDimensional ℚ_[2] L]
    (hkL : k ≤ L)
    {δa : ℚ̄₂} {d : ↥k} (hδ2 : δa ^ 2 = (d : ℚ̄₂)) (hδk : δa ∉ k) (hδaL : δa ∈ L)
    {σ : ℚ̄₂ ≃ₐ[↥k] ℚ̄₂} (hσ : σ δa = -δa)
    (hLadj : ∀ z ∈ L, z ∈ IntermediateField.adjoin ↥k {δa})
    {π : ℚ̄₂} (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ z ∈ L, ‖z‖ < 1 → ‖z‖ ≤ ‖π‖)
    {q : ℕ} (hqn : ‖(q : ℚ̄₂)‖ < 1) (hqodd : Odd (q - 1))
    (hlag : ∀ z ∈ L, ‖z‖ ≤ 1 → ‖z ^ q - z‖ < 1) :
    ∀ c : ℚ̄₂, c ∈ k → ‖c‖ ≤ 1 → ∃ z, z ∈ L ∧ ‖z‖ ≤ 1 ∧ z + σ z = c := by
  obtain ⟨z₁, hz₁L, hz₁1, hz₁σ⟩ := exists_conj_unit hkL hδ2 hδk hδaL hσ hLadj hπk hπ0 hπ1
    hπmax hqn hqodd hlag
  obtain ⟨x, y, hxy⟩ := exists_coords hδ2 hδk (hLadj z₁ hz₁L)
  -- the trace value is `2x ∈ k`, of norm `1`
  have ht : z₁ + σ z₁ = ((x + x : ↥k) : ℚ̄₂) := by
    rw [hxy, conj_apply hσ]
    exact trace_coord x y
  have h2z : ‖(2 : ℚ̄₂) * z₁‖ < 1 := by
    rw [norm_mul]
    calc ‖(2 : ℚ̄₂)‖ * ‖z₁‖ ≤ ‖(2 : ℚ̄₂)‖ * 1 :=
          mul_le_mul_of_nonneg_left hz₁1 (norm_nonneg _)
      _ = ‖(2 : ℚ̄₂)‖ := mul_one _
      _ < 1 := norm_two_lt_one
  have htnorm : ‖z₁ + σ z₁‖ = 1 := by
    have hdecomp : z₁ + σ z₁ = (σ z₁ - z₁) + (2 : ℚ̄₂) * z₁ := by ring
    have hne : ‖σ z₁ - z₁‖ ≠ ‖(2 : ℚ̄₂) * z₁‖ := by
      rw [hz₁σ]
      exact ne_of_gt h2z
    rw [hdecomp, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, hz₁σ]
    exact max_eq_left h2z.le
  have htk : z₁ + σ z₁ ∈ k := ht ▸ (x + x).2
  have ht0 : z₁ + σ z₁ ≠ 0 := by
    intro h
    rw [h, norm_zero] at htnorm
    exact zero_ne_one htnorm
  intro c hck hc1
  refine ⟨c / (z₁ + σ z₁) * z₁, L.mul_mem (hkL (k.div_mem hck htk)) hz₁L, ?_, ?_⟩
  · rw [norm_mul, norm_div, htnorm, div_one]
    calc ‖c‖ * ‖z₁‖ ≤ 1 * 1 := mul_le_mul hc1 hz₁1 (norm_nonneg _) zero_le_one
      _ = 1 := mul_one 1
  · have hfixdiv : σ (c / (z₁ + σ z₁)) = c / (z₁ + σ z₁) := by
      have h := conj_base σ ⟨c / (z₁ + σ z₁), k.div_mem hck htk⟩
      simpa using h
    rw [map_mul, hfixdiv, ← mul_add]
    exact div_mul_cancel₀ c ht0

end ResidueLayer

/-! ## The approximation engine (B11b-3) — filtration helpers -/

section Engine

/-- `‖1 + x‖ = 1` when `‖x‖ < 1` (ultrametric: the unit dominates). -/
lemma norm_one_add {x : ℚ̄₂} (hx : ‖x‖ < 1) : ‖(1 : ℚ̄₂) + x‖ = 1 := by
  have hne : ‖(1 : ℚ̄₂)‖ ≠ ‖x‖ := by rw [norm_one]; exact (ne_of_lt hx).symm
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one, max_eq_left hx.le]

/-- The `(↥K)ˣ → ↥K → ℚ̄₂` coercion commutes with powers. -/
lemma coe_units_pow {K : IntermediateField ℚ_[2] ℚ̄₂} (v : (↥K)ˣ) (n : ℕ) :
    (((v ^ n : (↥K)ˣ) : ↥K) : ℚ̄₂) = ((v : ↥K) : ℚ̄₂) ^ n := by
  rw [Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow]

/-- **Lagrange in `U⁰/U¹`** — the single group-theoretic input behind both residue facts.  The
graded piece `U⁰_K/U¹_K` is a finite group of order `2^f − 1` (`card_gr_zero`), so every
norm-one unit `u` satisfies `u^{2^f − 1} ∈ U¹_K`. -/
lemma pow_card_sub_one_mem (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (fil : DyadicUnitFiltration K) {u : (↥K)ˣ} (hu : u ∈ normUnits K) :
    u ^ (2 ^ fil.f - 1) ∈ depthUnits K fil.π 1 := by
  set H := (depthUnits K fil.π 1).subgroupOf (normUnits K) with hH
  have : H.Normal := inferInstance
  have hcard : Nat.card (↥(normUnits K) ⧸ H) = 2 ^ fil.f - 1 := fil.card_gr_zero
  have hgpow : (QuotientGroup.mk' H ⟨u, hu⟩) ^ Nat.card (↥(normUnits K) ⧸ H) = 1 :=
    pow_card_eq_one'
  rw [hcard, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hH,
    Subgroup.mem_subgroupOf, SubmonoidClass.coe_pow] at hgpow
  exact hgpow

/-- **Depth-1 start** (the square residue layer, via Lagrange with `x := u^{2^{f−1}}`): a norm-one
unit is a square modulo `U¹`.  Since `2·2^{f−1} = 2^f`, `x² = u^{2^f}` and
`u^{2^f} − u = u(u^{2^f−1} − 1)` with `u^{2^f−1} ∈ U¹`. -/
lemma exists_sq_approx (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (fil : DyadicUnitFiltration K) {u : (↥K)ˣ} (hu : u ∈ normUnits K) :
    ∃ x : (↥K)ˣ, x ∈ normUnits K ∧
      ‖((u : ↥K) : ℚ̄₂) - ((x : ↥K) : ℚ̄₂) ^ 2‖ ≤ ‖fil.π‖ := by
  have hu1 : ‖((u : ↥K) : ℚ̄₂)‖ = 1 := hu
  have hf1 : 1 ≤ fil.f := fil.hf_pos
  have h2f1 : 1 ≤ 2 ^ fil.f := Nat.one_le_two_pow
  refine ⟨u ^ (2 ^ (fil.f - 1)), (normUnits K).pow_mem hu _, ?_⟩
  set U : ℚ̄₂ := ((u : ↥K) : ℚ̄₂) with hUdef
  have hmem := pow_card_sub_one_mem K fil hu
  rw [mem_depthUnits, pow_one, coe_units_pow u] at hmem
  have hexp : 2 ^ (fil.f - 1) * 2 = 2 ^ fil.f := by
    have hff : fil.f - 1 + 1 = fil.f := by omega
    calc 2 ^ (fil.f - 1) * 2 = 2 ^ (fil.f - 1) * 2 ^ 1 := by rw [pow_one]
      _ = 2 ^ (fil.f - 1 + 1) := (pow_add 2 _ 1).symm
      _ = 2 ^ fil.f := by rw [hff]
  rw [coe_units_pow u, ← pow_mul, hexp]
  have hfac : U - U ^ (2 ^ fil.f) = U * (1 - U ^ (2 ^ fil.f - 1)) := by
    have hff : 2 ^ fil.f - 1 + 1 = 2 ^ fil.f := by omega
    have h2f : U ^ (2 ^ fil.f) = U ^ (2 ^ fil.f - 1) * U := by rw [← pow_succ, hff]
    rw [h2f]; ring
  rw [hfac, norm_mul, hu1, one_mul, norm_sub_rev]
  exact hmem.2

/-- **The Lagrange input `hlag`** for `trace_covers` at `L`: with `q := 2^F` (`F` the residue
degree of `L`), `‖z^q − z‖ < 1` for every integral `z ∈ L`.  Unit case: Lagrange
(`z^{q−1} ∈ U¹_L`); non-unit case: ultrametric on `‖z‖ < 1`. -/
lemma lagrange_pow_sub (L : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] L]
    (fil : DyadicUnitFiltration L) {z : ℚ̄₂} (hzL : z ∈ L) (hz1 : ‖z‖ ≤ 1) :
    ‖z ^ (2 ^ fil.f) - z‖ < 1 := by
  have h2f1 : 1 ≤ 2 ^ fil.f := Nat.one_le_two_pow
  rcases lt_or_eq_of_le hz1 with hzlt | hzeq
  · -- non-unit: both terms have norm < 1
    have hzq : ‖z ^ (2 ^ fil.f)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hzlt (pow_ne_zero fil.f two_ne_zero)
    calc ‖z ^ (2 ^ fil.f) - z‖ ≤ max ‖z ^ (2 ^ fil.f)‖ ‖z‖ := by
          rw [sub_eq_add_neg]
          refine le_trans (IsUltrametricDist.norm_add_le_max _ _) ?_
          rw [norm_neg]
      _ < 1 := max_lt hzq hzlt
  · -- unit: z is a unit of ↥L, Lagrange in U⁰/U¹
    have hz0 : z ≠ 0 := by intro h; rw [h] at hzeq; simp at hzeq
    have hzL0 : (⟨z, hzL⟩ : ↥L) ≠ 0 := by
      intro h; exact hz0 (by simpa using congrArg Subtype.val h)
    let u : (↥L)ˣ := Units.mk0 ⟨z, hzL⟩ hzL0
    have huz : ((u : ↥L) : ℚ̄₂) = z := rfl
    have hunorm : u ∈ normUnits L := by rw [mem_normUnits, huz]; exact hzeq
    have hmem := pow_card_sub_one_mem L fil hunorm
    rw [mem_depthUnits, pow_one, coe_units_pow u, huz] at hmem
    have hfac : z ^ (2 ^ fil.f) - z = z * (z ^ (2 ^ fil.f - 1) - 1) := by
      have hff : 2 ^ fil.f - 1 + 1 = 2 ^ fil.f := by omega
      have h2f : z ^ (2 ^ fil.f) = z ^ (2 ^ fil.f - 1) * z := by rw [← pow_succ, hff]
      rw [h2f]; ring
    rw [hfac, norm_mul, hzeq, one_mul]
    exact lt_of_le_of_lt hmem.2 fil.hπ_lt

/-- **The quadratic extension `L = k(δa)`.**  Packages `k⟮δa⟯`, viewed as an intermediate field
over `ℚ₂` via `restrictScalars`, together with the facts the engine needs: it is finite over
`ℚ₂`, contains `k` and `δa`, and its elements are exactly the elements of the `↥k`-adjunction
(so `exists_coords` applies). -/
private lemma exists_quadraticExt (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
    {δa : ℚ̄₂} :
    ∃ L : IntermediateField ℚ_[2] ℚ̄₂, FiniteDimensional ℚ_[2] L ∧ k ≤ L ∧ δa ∈ L ∧
      ∀ z ∈ L, z ∈ IntermediateField.adjoin ↥k {δa} := by
  have hδaint : IsIntegral ↥k δa := (Algebra.IsAlgebraic.isAlgebraic δa).isIntegral
  have hSfin : FiniteDimensional ↥k ↥(IntermediateField.adjoin ↥k {δa}) :=
    IntermediateField.adjoin.finiteDimensional hδaint
  refine ⟨(IntermediateField.adjoin ↥k {δa}).restrictScalars ℚ_[2],
    FiniteDimensional.trans ℚ_[2] ↥k ↥(IntermediateField.adjoin ↥k {δa}), ?_, ?_, fun z hz => hz⟩
  · intro x hx
    simpa using (IntermediateField.adjoin ↥k {δa}).algebraMap_mem ⟨x, hx⟩
  · exact IntermediateField.mem_adjoin_simple_self ↥k δa

/-- **`π`-transfer: the uniformizer is `L`-maximal.**  Given the spectral hypothesis `hunram`
(every nonzero `z ∈ L` has the norm of some nonzero `w ∈ k`), the `k`-maximal uniformizer
`filk.π` also attains the maximal norm `< 1` on all of `L`. -/
private lemma norm_le_uniformizer (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
    {a : (↥k)ˣ} {δa : ℚ̄₂} (hδ2 : δa ^ 2 = ((a : ↥k) : ℚ̄₂)) (hδk : δa ∉ k)
    {L : IntermediateField ℚ_[2] ℚ̄₂}
    (hLadj : ∀ z ∈ L, z ∈ IntermediateField.adjoin ↥k {δa})
    (hunram : ∀ z : ℚ̄₂, z ≠ 0 →
      (∃ x y : ↥k, z = (x : ℚ̄₂) + (y : ℚ̄₂) * δa) →
      ∃ w : ↥k, w ≠ 0 ∧ ‖z‖ = ‖(w : ℚ̄₂)‖)
    (filk : DyadicUnitFiltration k) :
    ∀ z ∈ L, ‖z‖ < 1 → ‖z‖ ≤ ‖filk.π‖ := by
  intro z hzL hzlt
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [norm_zero]; positivity
  · obtain ⟨x, y, hxy⟩ := exists_coords hδ2 hδk (hLadj z hzL)
    obtain ⟨w, _hw0, hwnorm⟩ := hunram z hz0 ⟨x, y, hxy⟩
    rw [hwnorm]
    exact filk.hπ_max (w : ℚ̄₂) w.2 (hwnorm ▸ hzlt)

/-- **One successive-approximation step.**  From a norm-one `w ∈ L` approximating the target norm
`U` to depth `n + 1` (`‖U − w·σw‖ ≤ ‖π‖^{n+1}`) and a trace witness `z₀` for the quotient
`(U − w·σw)/(w·σw·π^{n+1})`, the update `w' = w·(1 + π^{n+1}·z₀)` is again a norm-one element of
`L` whose norm-form value approximates `U` to depth `n + 2`.  The gain is quadratic in `z₀`
(char-2 telescoping: `U − w'·σw' = −(w·σw·π^{2(n+1)}·z₀·σz₀)`). -/
private lemma approx_step (k : IntermediateField ℚ_[2] ℚ̄₂) {L : IntermediateField ℚ_[2] ℚ̄₂}
    {σ : ℚ̄₂ ≃ₐ[↥k] ℚ̄₂} {π U : ℚ̄₂} (hπL : π ∈ L) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1) (hσπ : σ π = π)
    (hNnorm : ∀ z : ℚ̄₂, ‖z‖ = 1 → ‖z * σ z‖ = 1) {n : ℕ} {w z₀ : ℚ̄₂} (hwL : w ∈ L)
    (hwnorm : ‖w‖ = 1) (hz₀L : z₀ ∈ L) (hz₀norm : ‖z₀‖ ≤ 1)
    (hz₀s : z₀ + σ z₀ = (U - w * σ w) / (w * σ w * π ^ (n + 1))) :
    w * (1 + π ^ (n + 1) * z₀) ∈ L ∧ ‖w * (1 + π ^ (n + 1) * z₀)‖ = 1 ∧
      ‖U - w * (1 + π ^ (n + 1) * z₀) * σ (w * (1 + π ^ (n + 1) * z₀))‖ ≤ ‖π‖ ^ (n + 1 + 1) := by
  have hπpos : (0 : ℝ) < ‖π‖ := norm_pos_iff.mpr hπ0
  have hNwnorm : ‖w * σ w‖ = 1 := hNnorm w hwnorm
  have hNw0 : w * σ w ≠ 0 := fun h => by
    rw [h, norm_zero] at hNwnorm; exact one_ne_zero hNwnorm.symm
  set P : ℚ̄₂ := π ^ (n + 1) with hPdef
  have hP0 : P ≠ 0 := pow_ne_zero _ hπ0
  have hPnorm : ‖P‖ = ‖π‖ ^ (n + 1) := norm_pow _ _
  have hPz0 : ‖P * z₀‖ < 1 := by
    rw [norm_mul, hPnorm]
    calc ‖π‖ ^ (n + 1) * ‖z₀‖ ≤ ‖π‖ ^ (n + 1) * 1 :=
          mul_le_mul_of_nonneg_left hz₀norm (by positivity)
      _ = ‖π‖ ^ (n + 1) := mul_one _
      _ < 1 := pow_lt_one₀ hπpos.le hπ1 (by omega)
  refine ⟨L.mul_mem hwL (L.add_mem L.one_mem (L.mul_mem (pow_mem hπL _) hz₀L)), ?_, ?_⟩
  · rw [norm_mul, norm_one_add hPz0, hwnorm, one_mul]
  · have hσw' : σ (w * (1 + P * z₀)) = σ w * (1 + P * σ z₀) := by
      rw [map_mul, map_add, map_one, map_mul, hPdef, map_pow, hσπ, ← hPdef]
    have hrel2 : (z₀ + σ z₀) * (w * σ w * P) = U - w * σ w := by
      rw [hz₀s, hPdef]; exact div_mul_cancel₀ _ (mul_ne_zero hNw0 hP0)
    have hz₀σz₀ : ‖z₀ * σ z₀‖ ≤ 1 := by
      rw [norm_mul, norm_conj_eq]; exact mul_le_one₀ hz₀norm (norm_nonneg _) hz₀norm
    have hkey : U - w * (1 + P * z₀) * σ (w * (1 + P * z₀))
        = -(w * σ w * P ^ 2 * (z₀ * σ z₀)) := by
      rw [hσw']; linear_combination -hrel2
    rw [hkey, norm_neg]
    have hb : ‖w * σ w * P ^ 2 * (z₀ * σ z₀)‖ ≤ ‖π‖ ^ ((n + 1) * 2) := by
      rw [norm_mul, norm_mul, hNwnorm, one_mul, norm_pow, hPnorm, ← pow_mul]
      calc ‖π‖ ^ ((n + 1) * 2) * ‖z₀ * σ z₀‖ ≤ ‖π‖ ^ ((n + 1) * 2) * 1 :=
            mul_le_mul_of_nonneg_left hz₀σz₀ (by positivity)
        _ = ‖π‖ ^ ((n + 1) * 2) := mul_one _
    exact le_trans hb (pow_le_pow_of_le_one hπpos.le hπ1.le (by omega))

/-- **The engine (non-degenerate case).**  For `δa ∉ k`, every norm-one unit of `k` is a value
of the norm form `x² − a y²`.  Sets up `L = k(δa)`, the conjugation `σ`, the shared uniformizer
`π` (via `hunram`), and the residue data at `L`, then runs the successive-approximation engine
against `trace_covers`.

`hunram` is `IsUnramifiedQuadraticSpectral k δa` written **unfolded** — that predicate is a plain
`def` in the (downstream) axiom file, so it cannot be named here; the B11b flip supplies it
definitionally. -/
theorem units_are_norms_nondegen (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
    {a : (↥k)ˣ} {δa : ℚ̄₂} (hδ2 : δa ^ 2 = ((a : ↥k) : ℚ̄₂)) (hδk : δa ∉ k)
    (hunram : ∀ z : ℚ̄₂, z ≠ 0 →
      (∃ x y : ↥k, z = (x : ℚ̄₂) + (y : ℚ̄₂) * δa) →
      ∃ w : ↥k, w ≠ 0 ∧ ‖z‖ = ‖(w : ℚ̄₂)‖) :
    ∀ u : (↥k)ˣ, ‖((u : ↥k) : ℚ̄₂)‖ = 1 → ∃ x y : ↥k, (u : ↥k) = x ^ 2 - (a : ↥k) * y ^ 2 := by
  -- The quadratic extension `L = k(δa)`
  obtain ⟨L, hLfin, hkL, hδaL, hLadj⟩ := exists_quadraticExt k (δa := δa)
  haveI := hLfin
  -- the conjugation `σ δa = −δa`
  obtain ⟨σ, hσ⟩ := exists_conj (d := (a : ↥k)) hδ2 hδk
  -- filtrations at `k` and `L`; the shared uniformizer `π ∈ k`
  set filk := dyadicUnitFiltration' k with hfilk
  set filL := dyadicUnitFiltration' L with hfilL
  set π : ℚ̄₂ := filk.π with hπ
  have hπk : π ∈ k := filk.hπ_mem
  have hπ0 : π ≠ 0 := filk.hπ_ne
  have hπ1 : ‖π‖ < 1 := filk.hπ_lt
  have hπL : π ∈ L := hkL hπk
  -- π-transfer: `π` is `L`-maximal too (via `hunram` + `k`-maximality)
  have hπmax : ∀ z ∈ L, ‖z‖ < 1 → ‖z‖ ≤ ‖π‖ :=
    norm_le_uniformizer k hδ2 hδk hLadj hunram filk
  -- the residue exponent `q = 2^F` and the trace-covering hypotheses
  set q : ℕ := 2 ^ filL.f with hq
  have hqn : ‖((q : ℕ) : ℚ̄₂)‖ < 1 := by
    rw [hq, Nat.cast_pow, Nat.cast_ofNat, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) norm_two_lt_one (Nat.one_le_iff_ne_zero.mp filL.hf_pos)
  have hqodd : Odd (q - 1) := by
    rw [hq]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Nat.even_pow.mpr ⟨even_two, Nat.one_le_iff_ne_zero.mp filL.hf_pos⟩) odd_one
  have hlag : ∀ z ∈ L, ‖z‖ ≤ 1 → ‖z ^ q - z‖ < 1 := fun z hzL hz1 =>
    lagrange_pow_sub L filL hzL hz1
  -- exact trace coverage: `s(z) = z + σz` hits every integral `c ∈ k`
  have hcov := trace_covers hkL hδ2 hδk hδaL hσ hLadj hπk hπ0 hπ1 hπmax hqn hqodd hlag
  -- ambient facts for the engine
  have : CompleteSpace ↥L := FiniteDimensional.complete ℚ_[2] ↥L
  have hσπ : σ π = π := conj_base σ ⟨π, hπk⟩
  have hπpos : (0 : ℝ) < ‖π‖ := norm_pos_iff.mpr hπ0
  have hσcont : Continuous (σ : ℚ̄₂ → ℚ̄₂) :=
    (Isometry.of_dist_eq (fun x y => by rw [dist_eq_norm, dist_eq_norm, ← map_sub,
      norm_conj_eq])).continuous
  -- `N z := z·σz` is `k`-valued on `L` (norm form) and norm-preserving
  have hNk : ∀ z ∈ L, z * σ z ∈ k := by
    intro z hz
    obtain ⟨x, y, rfl⟩ := exists_coords hδ2 hδk (hLadj z hz)
    rw [conj_apply hσ, norm_coord hδ2]
    exact SetLike.coe_mem _
  have hNnorm : ∀ z : ℚ̄₂, ‖z‖ = 1 → ‖z * σ z‖ = 1 := by
    intro z hz; rw [norm_mul, norm_conj_eq, hz, mul_one]
  -- now fix a norm-one unit `u`
  intro u hunorm
  set U : ℚ̄₂ := ((u : ↥k) : ℚ̄₂) with hUdef
  have hUk : U ∈ k := SetLike.coe_mem _
  -- depth-1 start `w₀`
  obtain ⟨x₀, hx₀norm, hx₀approx⟩ := exists_sq_approx k filk hunorm
  set w₀ : ℚ̄₂ := ((x₀ : ↥k) : ℚ̄₂) with hw₀def
  have hw₀L : w₀ ∈ L := hkL (SetLike.coe_mem _)
  have hw₀norm : ‖w₀‖ = 1 := hx₀norm
  have hσw₀ : σ w₀ = w₀ := conj_base σ x₀
  have hInv0 : w₀ ∈ L ∧ ‖w₀‖ = 1 ∧ ‖U - w₀ * σ w₀‖ ≤ ‖π‖ ^ (0 + 1) := by
    refine ⟨hw₀L, hw₀norm, ?_⟩
    rw [hσw₀, pow_one, ← sq]
    exact hx₀approx
  classical
  -- the per-step target quotient `c` and the chosen increment `zc` (junk `0` off-domain)
  set cval : ℕ → ℚ̄₂ → ℚ̄₂ := fun n w => (U - w * σ w) / (w * σ w * π ^ (n + 1)) with hcval
  set zc : ℕ → ℚ̄₂ → ℚ̄₂ := fun n w =>
    if h : cval n w ∈ k ∧ ‖cval n w‖ ≤ 1 then (hcov (cval n w) h.1 h.2).choose else 0 with hzc
  set wseq : ℕ → ℚ̄₂ := fun n => Nat.rec w₀ (fun m wm => wm * (1 + π ^ (m + 1) * zc m wm)) n
    with hwseq
  have hwseqS : ∀ n, wseq (n + 1) = wseq n * (1 + π ^ (n + 1) * zc n (wseq n)) := fun _ => rfl
  -- integrality of `cval` from the invariant (used in the induction and the jump bound)
  have hcval_ok : ∀ n w, w ∈ L → ‖w‖ = 1 → ‖U - w * σ w‖ ≤ ‖π‖ ^ (n + 1) →
      cval n w ∈ k ∧ ‖cval n w‖ ≤ 1 := by
    intro n w hwL hwnorm hwapprox
    have hNwk : w * σ w ∈ k := hNk w hwL
    have hNwnorm : ‖w * σ w‖ = 1 := hNnorm w hwnorm
    refine ⟨?_, ?_⟩
    · simp only [hcval]
      exact k.div_mem (k.sub_mem hUk hNwk) (k.mul_mem hNwk (pow_mem hπk _))
    · simp only [hcval, norm_div, norm_mul, hNwnorm, one_mul, norm_pow]
      rw [div_le_one (by positivity)]
      exact hwapprox
  -- `zc` computes to the chosen witness on the invariant's domain
  have hzc_spec : ∀ n w, (h : cval n w ∈ k ∧ ‖cval n w‖ ≤ 1) →
      zc n w ∈ L ∧ ‖zc n w‖ ≤ 1 ∧ zc n w + σ (zc n w) = cval n w := by
    intro n w h
    have hval : zc n w = (hcov (cval n w) h.1 h.2).choose := by rw [hzc]; exact dif_pos h
    rw [hval]; exact (hcov (cval n w) h.1 h.2).choose_spec
  -- the invariant, by induction
  have hInv : ∀ n, wseq n ∈ L ∧ ‖wseq n‖ = 1 ∧ ‖U - wseq n * σ (wseq n)‖ ≤ ‖π‖ ^ (n + 1) := by
    intro n
    induction n with
    | zero => exact hInv0
    | succ n ih =>
      obtain ⟨hwL, hwnorm, hwapprox⟩ := ih
      obtain ⟨hz₀L, hz₀norm, hz₀s⟩ := hzc_spec n (wseq n) (hcval_ok n _ hwL hwnorm hwapprox)
      simp only [hcval] at hz₀s
      rw [hwseqS n]
      exact approx_step k hπL hπ0 hπ1 hσπ hNnorm hwL hwnorm hz₀L hz₀norm hz₀s
  -- the sequence lives in the complete `↥L`; extract the limit
  set wseqL : ℕ → ↥L := fun n => ⟨wseq n, (hInv n).1⟩ with hwseqL
  have hjump : ∀ n, dist (wseqL n) (wseqL (n + 1)) ≤ ‖π‖ * ‖π‖ ^ n := by
    intro n
    have hz1 : ‖zc n (wseq n)‖ ≤ 1 :=
      (hzc_spec n (wseq n) (hcval_ok n _ (hInv n).1 (hInv n).2.1 (hInv n).2.2)).2.1
    rw [dist_eq_norm]
    change ‖(wseq n : ℚ̄₂) - (wseq (n + 1) : ℚ̄₂)‖ ≤ ‖π‖ * ‖π‖ ^ n
    rw [hwseqS n, show wseq n - wseq n * (1 + π ^ (n + 1) * zc n (wseq n))
        = -(wseq n * (π ^ (n + 1) * zc n (wseq n))) by ring, norm_neg, norm_mul, norm_mul,
      (hInv n).2.1, one_mul, norm_pow]
    calc ‖π‖ ^ (n + 1) * ‖zc n (wseq n)‖ ≤ ‖π‖ ^ (n + 1) * 1 :=
          mul_le_mul_of_nonneg_left hz1 (by positivity)
      _ = ‖π‖ * ‖π‖ ^ n := by rw [mul_one, pow_succ']
  have hcauchy : CauchySeq wseqL := cauchySeq_of_le_geometric ‖π‖ ‖π‖ hπ1 hjump
  obtain ⟨wLimL, hwLimL⟩ := cauchySeq_tendsto_of_complete hcauchy
  set wLim : ℚ̄₂ := (wLimL : ℚ̄₂) with hwLimdef
  have hwLimL' : wLim ∈ L := wLimL.2
  have hwtend : Filter.Tendsto wseq Filter.atTop (nhds wLim) :=
    (continuous_subtype_val.tendsto wLimL).comp hwLimL
  -- `N wseq → N wLim` and `N wseq → U`, hence `N wLim = U`
  have hNtend1 : Filter.Tendsto (fun n => wseq n * σ (wseq n)) Filter.atTop
      (nhds (wLim * σ wLim)) :=
    ((continuous_id.mul hσcont).tendsto wLim).comp hwtend
  have hNtend2 : Filter.Tendsto (fun n => wseq n * σ (wseq n)) Filter.atTop (nhds U) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hg : Filter.Tendsto (fun n : ℕ => ‖π‖ ^ (n + 1)) Filter.atTop (nhds 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hπpos.le hπ1).const_mul ‖π‖
      rw [mul_zero] at h
      simpa only [pow_succ'] using h
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => by rw [norm_sub_rev]; exact (hInv n).2.2) hg
  have hNeq : wLim * σ wLim = U := tendsto_nhds_unique hNtend1 hNtend2
  -- extract coordinates of the limit
  obtain ⟨x, y, hxy⟩ := exists_coords hδ2 hδk (hLadj wLim hwLimL')
  have hfinal : U = ((x ^ 2 - (a : ↥k) * y ^ 2 : ↥k) : ℚ̄₂) := by
    rw [← hNeq, hxy, conj_apply hσ, norm_coord hδ2]
  refine ⟨x, y, ?_⟩
  have hf2 : ((u : ↥k) : ℚ̄₂) = ((x ^ 2 - (a : ↥k) * y ^ 2 : ↥k) : ℚ̄₂) := hfinal
  exact_mod_cast hf2

/-- **The B11b capstone** (B11b-4): units of an unramified quadratic extension `k(√a)/k` are
norms — every norm-one `u ∈ k` is `x² − a y²`.  Dispatches the degenerate case `δa ∈ k`
(`norm_form_of_mem`, the norm form is then universal) against the engine
`units_are_norms_nondegen`.

The statement is the axiom `GQ2.unramifiedQuadratic_units_are_norms`
(`GQ2/Foundations/Axioms.lean`) **with `IsUnramifiedQuadraticSpectral k δa` written unfolded** —
that predicate is a plain `def` downstream of this file, so it cannot be named here; the B11b-5
census flip supplies it definitionally (`:= unramifiedQuadratic_units_are_norms' k a δa hδa
hunram`, zero consumer churn — the B11a/`dyadicNormCriterion` precedent). -/
theorem unramifiedQuadratic_units_are_norms' (k : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] k] (a : (↥k)ˣ) (δa : ℚ̄₂)
    (hδa : δa ^ 2 = ((a : ↥k) : ℚ̄₂))
    (hunram : ∀ z : ℚ̄₂, z ≠ 0 →
      (∃ x y : ↥k, z = (x : ℚ̄₂) + (y : ℚ̄₂) * δa) →
      ∃ w : ↥k, w ≠ 0 ∧ ‖z‖ = ‖(w : ℚ̄₂)‖) :
    ∀ u : (↥k)ˣ, ‖((u : ↥k) : ℚ̄₂)‖ = 1 →
      ∃ x y : ↥k, (u : ↥k) = x ^ 2 - (a : ↥k) * y ^ 2 := by
  by_cases hδk : δa ∈ k
  · exact fun u _ => norm_form_of_mem hδa hδk (u : ↥k)
  · exact units_are_norms_nondegen k hδa hδk hunram

end Engine

end GQ2.UnramifiedQuadraticNorms

import Mathlib
import GQ2.TeichmullerLift

/-!
# B11b-1 — the quadratic layer · B11b-2 — the residue layer

Groundwork toward discharging axiom **B11b** (`unramifiedQuadratic_units_are_norms`) in-repo —
see `docs/b11b-tickets.md` / `docs/b11b-proof-plan.md`.  This file is the **quadratic layer**
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
    have hcomm : σ (δa ^ 2) = δa ^ 2 := by rw [hδ2]; exact σ.commutes d
    calc (σ δa + δa) * (σ δa - δa) = σ δa ^ 2 - δa ^ 2 := by ring
      _ = 0 := by rw [← map_pow, hcomm, sub_self]
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

end GQ2.UnramifiedQuadraticNorms

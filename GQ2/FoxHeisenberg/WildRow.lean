import GQ2.FoxHeisenberg.Traced

/-!
# Lemma 5.4/5.5: the finite Fox derivatives of the wild aux words (tame case)

Split off from `GQ2.FoxHeisenberg`, building on `GQ2.FoxHeisenberg.Traced`.  At a tame lower map
(the wild inertia `x₀, x₁` and, in the split case, `σ₂` acting trivially) the `ω₂`-powers in the
auxiliary words collapse to their offsets, so the first Fox derivatives become plain
`𝔽₂`-combinations of the lift offsets, mirroring the paper's Lemma 5.4 ledger.

See `GQ2.FoxHeisenberg` for the umbrella module docstring.
-/

namespace GQ2

namespace FoxH

/-! ## Lemma 5.4/5.5: the finite Fox derivatives of the wild aux words (tame case)

At a tame lower map (the wild inertia `x₀, x₁` and, in the split case, `σ₂` acting trivially), the
`ω₂`-powers in the auxiliary words collapse to their offsets via `WordLift.powOmega2_u_of_trivial`,
so the first Fox derivatives `D(·)` become plain `𝔽₂`-combinations of the lift offsets `x`.  These
mirror the paper's Lemma 5.4 ledger `D(uᵢ) = P(Dxᵢ + Dτ)`, `D(d₀) = Pb + (P+1)c` at `P = 1`. -/

section WildRow

variable {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]
  [Finite V]

/-- **`D(u₀) = x₂ + x₁`** (tame case): with `x₀, τ` acting trivially the `ω₂`-power in
`u₀ = (x₀τ)^{ω₂}` collapses (odd exponent, char 2), leaving the plain product offset. -/
theorem liftMarking_u0_u (t : Marking C) (x : Fin 4 → V) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) :
    (liftMarking t x).u0.u = x 2 + x 1 := by
  have hbase : ∀ v : V, ((liftMarking t x).x₀ * (liftMarking t x).τ).g • v = v := by
    intro v
    show (t.x₀ * t.τ) • v = v
    rw [mul_smul, htau, hx0]
  have hu0 : (liftMarking t x).u0 = powOmega2 ((liftMarking t x).x₀ * (liftMarking t x).τ) := rfl
  rw [hu0, WordLift.powOmega2_u_of_trivial hV₂ _ hbase]
  show x 2 + t.x₀ • x 1 = x 2 + x 1
  rw [hx0]

/-- **`D(u₁) = x₃ + x₁`** (tame case), the `x₁`-analogue of `liftMarking_u0_u`. -/
theorem liftMarking_u1_u (t : Marking C) (x : Fin 4 → V) (hV₂ : ∀ v : V, v + v = 0)
    (hx1 : ∀ v : V, t.x₁ • v = v) (htau : ∀ v : V, t.τ • v = v) :
    (liftMarking t x).u1.u = x 3 + x 1 := by
  have hbase : ∀ v : V, ((liftMarking t x).x₁ * (liftMarking t x).τ).g • v = v := by
    intro v
    show (t.x₁ * t.τ) • v = v
    rw [mul_smul, htau, hx1]
  have hu1 : (liftMarking t x).u1 = powOmega2 ((liftMarking t x).x₁ * (liftMarking t x).τ) := rfl
  rw [hu1, WordLift.powOmega2_u_of_trivial hV₂ _ hbase]
  show x 3 + t.x₁ • x 1 = x 3 + x 1
  rw [hx1]

/-! ### Ramified (`V^T = 0`) aux-word offsets (P-13b)

In the ramified case `τ` acts non-trivially, but its 2-primary part is trivial (`hTodd`), so the
ω₂-power bases `u0 = (x₀τ)^{ω₂}`, `u1 = (x₁τ)^{ω₂}` still act *trivially* on `V` (their base is the
2-part of the `τ`-action) while their offsets *vanish* (`powOmega2_u_of_oddFixedPointFree`).  Thus
every wild aux word remains trivially-based (so the split `.u`-additivity toolkit applies), only the
`u0`/`u1` offsets change to `0`. -/

/-- Ramified base-`g` triviality: `u0`'s base acts trivially on `V` (it is `powOmega2 (t.x₀ t.τ)`,
whose action is `τ`'s 2-part, killed by `hTodd`). -/
theorem liftMarking_u0_g_ramified (t : Marking C) (x : Fin 4 → V) (hx0 : ∀ v : V, t.x₀ • v = v)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (v : V) : (liftMarking t x).u0.g • v = v := by
  have hg : ((liftMarking t x).x₀ * (liftMarking t x).τ).g = t.x₀ * t.τ := rfl
  have hgeq : (liftMarking t x).u0.g = powOmega2 (t.x₀ * t.τ) := by
    show (powOmega2 ((liftMarking t x).x₀ * (liftMarking t x).τ)).g = powOmega2 (t.x₀ * t.τ)
    rw [powOmega2, WordLift.pow_g, hg]
    exact powOmega2_pow_eq (t.x₀ * t.τ)
      (orderOf_dvd_of_pow_eq_one (by rw [← hg, ← WordLift.pow_g, pow_orderOf_eq_one]; rfl))
      (orderOf_pos _).ne'
  rw [hgeq]; exact WordLift.powOmega2_smul_of_trivial_mul t.x₀ t.τ hx0 hTodd v

/-- Ramified base-`g` triviality: `u1`'s base acts trivially on `V`. -/
theorem liftMarking_u1_g_ramified (t : Marking C) (x : Fin 4 → V) (hx1 : ∀ v : V, t.x₁ • v = v)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (v : V) : (liftMarking t x).u1.g • v = v := by
  have hg : ((liftMarking t x).x₁ * (liftMarking t x).τ).g = t.x₁ * t.τ := rfl
  have hgeq : (liftMarking t x).u1.g = powOmega2 (t.x₁ * t.τ) := by
    show (powOmega2 ((liftMarking t x).x₁ * (liftMarking t x).τ)).g = powOmega2 (t.x₁ * t.τ)
    rw [powOmega2, WordLift.pow_g, hg]
    exact powOmega2_pow_eq (t.x₁ * t.τ)
      (orderOf_dvd_of_pow_eq_one (by rw [← hg, ← WordLift.pow_g, pow_orderOf_eq_one]; rfl))
      (orderOf_pos _).ne'
  rw [hgeq]; exact WordLift.powOmega2_smul_of_trivial_mul t.x₁ t.τ hx1 hTodd v

/-- Ramified `D(u₀) = 0` (the ω₂-norm of the fixed-point-free `τ`-base vanishes). -/
theorem liftMarking_u0_u_ramified (t : Marking C) (x : Fin 4 → V) (hx0 : ∀ v : V, t.x₀ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    (liftMarking t x).u0.u = 0 := by
  show (powOmega2 ((liftMarking t x).x₀ * (liftMarking t x).τ)).u = 0
  refine WordLift.powOmega2_u_of_oddFixedPointFree _ (fun v hv => htau _ ?_)
    (fun v => WordLift.powOmega2_smul_of_trivial_mul t.x₀ t.τ hx0 hTodd v)
  have hact : ((liftMarking t x).x₀ * (liftMarking t x).τ).g • v = t.τ • v := by
    show (t.x₀ * t.τ) • v = t.τ • v; rw [mul_smul, hx0]
  rw [← hact]; exact hv

/-- Ramified `D(u₁) = 0`. -/
theorem liftMarking_u1_u_ramified (t : Marking C) (x : Fin 4 → V) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    (liftMarking t x).u1.u = 0 := by
  show (powOmega2 ((liftMarking t x).x₁ * (liftMarking t x).τ)).u = 0
  refine WordLift.powOmega2_u_of_oddFixedPointFree _ (fun v hv => htau _ ?_)
    (fun v => WordLift.powOmega2_smul_of_trivial_mul t.x₁ t.τ hx1 hTodd v)
  have hact : ((liftMarking t x).x₁ * (liftMarking t x).τ).g • v = t.τ • v := by
    show (t.x₁ * t.τ) • v = t.τ • v; rw [mul_smul, hx1]
  rw [← hact]; exact hv

/-- **`D(d₀) = x₁`** (tame case, `P = 1`): from `d₀ = u₀·x₀⁻¹`, `D(d₀) = D(u₀) − x₂ = (x₂+x₁) − x₂ =
x₁`.  This is the paper's `Dd₀ = Pb + (P+1)c = b` at the split value `P = 1` (`c`-terms cancel). -/
theorem liftMarking_d0_u (t : Marking C) (x : Fin 4 → V) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) :
    (liftMarking t x).d0.u = x 1 := by
  have hbase : ∀ v : V, ((liftMarking t x).x₀ * (liftMarking t x).τ).g • v = v := by
    intro v
    show (t.x₀ * t.τ) • v = v
    rw [mul_smul, htau, hx0]
  have hx0inv : ∀ v : V, t.x₀⁻¹ • v = v := fun v => inv_smul_eq_iff.mpr (hx0 v).symm
  have hu0g : ∀ v : V, (liftMarking t x).u0.g • v = v := fun v =>
    WordLift.powOmega2_g_smul_of_trivial _ hbase v
  have hd0 : (liftMarking t x).d0 = (liftMarking t x).u0 * (liftMarking t x).x₀⁻¹ := rfl
  rw [hd0, WordLift.mul_u, liftMarking_u0_u t x hV₂ hx0 htau, WordLift.inv_u]
  show x 2 + x 1 + (liftMarking t x).u0.g • -(t.x₀⁻¹ • x 2) = x 1
  rw [hx0inv, hu0g]
  abel

/-- **`σ₂`'s base is exactly `t.sigma2`** — the `ω₂`-exponent taken in `WordLift V C` agrees
with the one in `C` (Lemma 5.1, finite-exponent independence): `orderOf t.σ ∣ orderOf σ_WL`, so
`powOmega2_pow_eq` identifies the two representatives.  Hence the σ-tameness `hU` (stated on
`t.sigma2`) transfers to the wild-row evaluation — `hU v` gives `(liftMarking t x).sigma2.g • v = v`
after `rw [liftMarking_sigma2_g]`. -/
theorem liftMarking_sigma2_g (t : Marking C) (x : Fin 4 → V) :
    (liftMarking t x).sigma2.g = t.sigma2 := by
  have hg : (liftMarking t x).σ.g = t.σ := rfl
  have hdvd : orderOf t.σ ∣ orderOf (liftMarking t x).σ := by
    apply orderOf_dvd_of_pow_eq_one
    have h1 : ((liftMarking t x).σ ^ orderOf (liftMarking t x).σ).g = (1 : WordLift V C).g :=
      congrArg WordLift.g (pow_orderOf_eq_one _)
    rwa [WordLift.pow_g, hg, WordLift.one_g] at h1
  have hN : orderOf (liftMarking t x).σ ≠ 0 := (orderOf_pos _).ne'
  rw [show (liftMarking t x).sigma2 =
      (liftMarking t x).σ ^ omega2Exp (orderOf (liftMarking t x).σ) from rfl,
    WordLift.pow_g, hg]
  exact powOmega2_pow_eq t.σ hdvd hN

omit [Finite V] [Finite C] in
/-- **`D(x₁^σ) = S⁻¹·x₃`** (tame case): conjugating by `σ` shifts the `x₁`-offset by `t.σ⁻¹`, and
the `x₀`-offsets contributed by the two `σ`'s cancel.  This is the sole surviving `S⁻¹` in the wild
row
(the paper's `xσ₁` ledger row `0 0 0 S⁻¹`). -/
theorem liftMarking_conjP_x1_sigma_u (t : Marking C) (x : Fin 4 → V)
    (hx1 : ∀ v : V, t.x₁ • v = v) :
    (conjP (liftMarking t x).x₁ (liftMarking t x).σ).u = t.σ⁻¹ • x 3 := by
  show -(t.σ⁻¹ • x 0) + t.σ⁻¹ • x 3 + (t.σ⁻¹ * t.x₁) • x 0 = t.σ⁻¹ • x 3
  rw [mul_smul, hx1]; abel

/-! ### Base-triviality of the wild aux words (tame case)

Each aux word evaluates to a trivially-based element, so `.u`-additivity (`mul_u_of_trivial` etc.)
applies.  `g₀ = σ₂²` and `z₀ = x₀^{σ₂}` use σ-tameness `hU`; the rest use the wild-core
triviality. -/

theorem liftMarking_g0_g_smul (t : Marking C) (x : Fin 4 → V) (hU : ∀ v : V, t.sigma2 • v = v)
    (v : V) : (liftMarking t x).g0.g • v = v := by
  show ((liftMarking t x).sigma2 ^ 2).g • v = v
  rw [WordLift.pow_g, pow_two, mul_smul, liftMarking_sigma2_g, hU, hU]

omit [Finite C] [Finite V] in
theorem liftMarking_u0_g_smul (t : Marking C) (x : Fin 4 → V) (hx0 : ∀ v : V, t.x₀ • v = v)
    (htau : ∀ v : V, t.τ • v = v) (v : V) : (liftMarking t x).u0.g • v = v := by
  apply WordLift.powOmega2_g_smul_of_trivial
  intro a; show (t.x₀ * t.τ) • a = a; rw [mul_smul, htau, hx0]

omit [Finite C] [Finite V] in
theorem liftMarking_u1_g_smul (t : Marking C) (x : Fin 4 → V) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v) (v : V) : (liftMarking t x).u1.g • v = v := by
  apply WordLift.powOmega2_g_smul_of_trivial
  intro a; show (t.x₁ * t.τ) • a = a; rw [mul_smul, htau, hx1]

omit [Finite C] [Finite V] in
theorem liftMarking_d0_g_smul (t : Marking C) (x : Fin 4 → V) (hx0 : ∀ v : V, t.x₀ • v = v)
    (htau : ∀ v : V, t.τ • v = v) (v : V) : (liftMarking t x).d0.g • v = v := by
  show ((liftMarking t x).u0 * (liftMarking t x).x₀⁻¹).g • v = v
  exact WordLift.mul_g_trivial _ _ (liftMarking_u0_g_smul t x hx0 htau)
    (WordLift.inv_g_trivial (liftMarking t x).x₀ hx0) v

omit [Finite C] [Finite V] in
theorem liftMarking_z0_g_smul (t : Marking C) (x : Fin 4 → V) (hx0 : ∀ v : V, t.x₀ • v = v)
    (v : V) : (liftMarking t x).z0.g • v = v := by
  show (conjP (liftMarking t x).x₀ (liftMarking t x).sigma2).g • v = v
  exact WordLift.conjP_g_trivial _ _ hx0 v

omit [Finite C] [Finite V] in
theorem liftMarking_h0_g_smul (t : Marking C) (x : Fin 4 → V) (hx0 : ∀ v : V, t.x₀ • v = v)
    (htau : ∀ v : V, t.τ • v = v) (_ : ∀ v : V, t.sigma2 • v = v) (v : V) :
    (liftMarking t x).h0.g • v = v := by
  have hd0g := liftMarking_d0_g_smul t x hx0 htau
  have hP1g : ∀ w : V, (conjP (liftMarking t x).x₀ (liftMarking t x).g0).g • w = w := fun w =>
    WordLift.conjP_g_trivial _ _ hx0 w
  have hdgg : ∀ w : V, (liftMarking t x).dg.g • w = w := fun w =>
    WordLift.conjP_g_trivial (liftMarking t x).d0 (liftMarking t x).g0 hd0g w
  have hhcg : ∀ w : V, (liftMarking t x).hc.g • w = w := fun w =>
    WordLift.commP_g_trivial _ _ hdgg hd0g w
  have hd02g : ∀ w : V, ((liftMarking t x).d0 ^ 2).g • w = w := fun w => by
    rw [WordLift.pow_g, pow_two, mul_smul, hd0g, hd0g]
  have hq1 := fun w => WordLift.mul_g_trivial _ (liftMarking t x).x₀ hP1g hx0 w
  have hq2 := fun w => WordLift.mul_g_trivial _ _ hq1 hdgg w
  have hq3 := fun w => WordLift.mul_g_trivial _ _ hq2 hd0g w
  have hq4 := fun w => WordLift.mul_g_trivial _ _ hq3 hd02g w
  show (conjP (liftMarking t x).x₀ (liftMarking t x).g0 * (liftMarking t x).x₀ *
    (liftMarking t x).dg * (liftMarking t x).d0 * (liftMarking t x).d0 ^ 2 *
    (liftMarking t x).hc).g • v = v
  exact WordLift.mul_g_trivial _ _ hq4 hhcg v

/-- **`D(h₀) = 0`** (tame case): the paper's `h₀`-shadow (Lemma 5.3(i)).  With every base acting
trivially, `.u` is additive, so `D(h₀) = D(x₀^{g₀}) + D(x₀) + D(d_g) + D(d₀) + D(d₀²) + D([d_g,d₀])
= x₂ + x₂ + x₁ + x₁ + 0 + 0 = 0` (conjugates keep the offset, `d₀²` and the commutator vanish). -/
theorem liftMarking_h0_u (t : Marking C) (x : Fin 4 → V) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) (hU : ∀ v : V, t.sigma2 • v = v) :
    (liftMarking t x).h0.u = 0 := by
  have hd0g := liftMarking_d0_g_smul t x hx0 htau
  have hg0g := liftMarking_g0_g_smul t x hU
  have hd0u := liftMarking_d0_u t x hV₂ hx0 htau
  have hP1g : ∀ w : V, (conjP (liftMarking t x).x₀ (liftMarking t x).g0).g • w = w := fun w =>
    WordLift.conjP_g_trivial _ _ hx0 w
  have hdgg : ∀ w : V, (liftMarking t x).dg.g • w = w := fun w =>
    WordLift.conjP_g_trivial (liftMarking t x).d0 (liftMarking t x).g0 hd0g w
  have hq1 := fun w => WordLift.mul_g_trivial _ (liftMarking t x).x₀ hP1g hx0 w
  have hq2 := fun w => WordLift.mul_g_trivial _ _ hq1 hdgg w
  have hq3 := fun w => WordLift.mul_g_trivial _ _ hq2 hd0g w
  have hd02g : ∀ w : V, ((liftMarking t x).d0 ^ 2).g • w = w := fun w => by
    rw [WordLift.pow_g, pow_two, mul_smul, hd0g, hd0g]
  have hq4 := fun w => WordLift.mul_g_trivial _ _ hq3 hd02g w
  have hP1u : (conjP (liftMarking t x).x₀ (liftMarking t x).g0).u = x 2 :=
    WordLift.conjP_u_of_trivial _ _ hx0 hg0g
  have hdgu : (liftMarking t x).dg.u = x 1 := by
    show (conjP (liftMarking t x).d0 (liftMarking t x).g0).u = x 1
    rw [WordLift.conjP_u_of_trivial _ _ hd0g hg0g, hd0u]
  have hhcu : (liftMarking t x).hc.u = 0 := by
    show (commP (liftMarking t x).dg (liftMarking t x).d0).u = 0
    exact WordLift.commP_u_of_trivial _ _ hdgg hd0g
  have hd02u : ((liftMarking t x).d0 ^ 2).u = 0 := by
    rw [pow_two, WordLift.mul_u_of_trivial _ _ hd0g, hd0u]; exact hV₂ (x 1)
  show (conjP (liftMarking t x).x₀ (liftMarking t x).g0 * (liftMarking t x).x₀ *
    (liftMarking t x).dg * (liftMarking t x).d0 * (liftMarking t x).d0 ^ 2 *
    (liftMarking t x).hc).u = 0
  rw [WordLift.mul_u_of_trivial _ _ hq4, WordLift.mul_u_of_trivial _ _ hq3,
    WordLift.mul_u_of_trivial _ _ hq2, WordLift.mul_u_of_trivial _ _ hq1,
    WordLift.mul_u_of_trivial _ _ hP1g, hP1u, hhcu, hd02u, hdgu, hd0u]
  show x 2 + x 2 + x 1 + x 1 + 0 + 0 = 0
  rw [add_zero, add_zero, hV₂ (x 2), zero_add, hV₂ (x 1)]

omit [Finite C] [Finite V] in
/-- **`D(c₀) = 0`** (tame case): `c₀ = [d₀,z₀]` is a commutator of trivially-based elements. -/
theorem liftMarking_c0_u (t : Marking C) (x : Fin 4 → V) (hx0 : ∀ v : V, t.x₀ • v = v)
    (htau : ∀ v : V, t.τ • v = v) (_ : ∀ v : V, t.sigma2 • v = v) :
    (liftMarking t x).c0.u = 0 := by
  show (commP (liftMarking t x).d0 (liftMarking t x).z0).u = 0
  exact WordLift.commP_u_of_trivial _ _ (liftMarking_d0_g_smul t x hx0 htau)
    (liftMarking_z0_g_smul t x hx0)

/-- **The split wild row (Lemma 5.5)**: `L_w = D(h₀) + D(u₁⁻¹) + D(x₁^σ) + D(c₀) =
0 + (x₃+x₁) + S⁻¹·x₃ + 0 = x₁ + (1 + S⁻¹)·x₃`.  This is `(d1Fun t x).2` at a split (`T = 1`) simple
tame module — the wild half of `lemma_5_13_split`'s `Z¹` characterisation. -/
theorem liftMarking_wildValue_u (t : Marking C) (x : Fin 4 → V) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v) (htau : ∀ v : V, t.τ • v = v)
    (hU : ∀ v : V, t.sigma2 • v = v) :
    (liftMarking t x).wildValue.u = x 1 + x 3 + t.σ⁻¹ • x 3 := by
  have hh0g := liftMarking_h0_g_smul t x hx0 htau hU
  have hu1g := liftMarking_u1_g_smul t x hx1 htau
  have hx1sg : ∀ w : V, (conjP (liftMarking t x).x₁ (liftMarking t x).σ).g • w = w := fun w =>
    WordLift.conjP_g_trivial _ _ hx1 w
  have hu1invg : ∀ w : V, (liftMarking t x).u1⁻¹.g • w = w := fun w =>
    WordLift.inv_g_trivial _ hu1g w
  have hq2 := fun w => WordLift.mul_g_trivial _ _ hh0g hu1invg w
  have hq3 := fun w => WordLift.mul_g_trivial _ _ hq2 hx1sg w
  show ((liftMarking t x).h0 * (liftMarking t x).u1⁻¹ *
    conjP (liftMarking t x).x₁ (liftMarking t x).σ * (liftMarking t x).c0).u =
    x 1 + x 3 + t.σ⁻¹ • x 3
  rw [WordLift.mul_u_of_trivial _ _ hq3, WordLift.mul_u_of_trivial _ _ hq2,
    WordLift.mul_u_of_trivial _ _ hh0g, liftMarking_h0_u t x hV₂ hx0 htau hU,
    WordLift.inv_u_of_trivial _ hu1g, liftMarking_u1_u t x hV₂ hx1 htau,
    liftMarking_conjP_x1_sigma_u t x hx1, liftMarking_c0_u t x hx0 htau hU,
    show -(x 3 + x 1) = x 3 + x 1 from neg_eq_of_add_eq_zero_left (hV₂ (x 3 + x 1))]
  abel

/-! ### Ramified wild row (P-13b): `L_w = S⁻¹·d`

With `u0.u = u1.u = 0` (collapse) and every aux base trivial, the ramified aux offsets are
`d0.u = x₂` (vs `x₁` split), `h0.u = 0`, `c0.u = 0`, and `conjP(x₁,σ).u = S⁻¹·x₃` (the split lemma,
`τ`-free).  So the wild value collapses to `S⁻¹·x₃` — the display (53) wild row. -/

/-- Ramified `d0.g` acts trivially (via the `hTodd` `u0.g`-triviality). -/
theorem liftMarking_d0_g_ramified (t : Marking C) (x : Fin 4 → V) (hx0 : ∀ v : V, t.x₀ • v = v)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (v : V) : (liftMarking t x).d0.g • v = v :=
  WordLift.mul_g_trivial _ _ (liftMarking_u0_g_ramified t x hx0 hTodd)
    (WordLift.inv_g_trivial _ hx0) v

/-- Ramified `D(d₀) = x₂` (`= Pb + (P+1)c = c` at `P = 0`; `c`-term survives, `b`-term dies). -/
theorem liftMarking_d0_u_ramified (t : Marking C) (x : Fin 4 → V) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v → v = 0)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) : (liftMarking t x).d0.u = x 2 := by
  have hx0inv : ∀ v : V, t.x₀⁻¹ • v = v := fun v => inv_smul_eq_iff.mpr (hx0 v).symm
  show ((liftMarking t x).u0 * (liftMarking t x).x₀⁻¹).u = x 2
  rw [WordLift.mul_u, liftMarking_u0_u_ramified t x hx0 htau hTodd, WordLift.inv_u]
  show 0 + (liftMarking t x).u0.g • -(t.x₀⁻¹ • x 2) = x 2
  rw [hx0inv, liftMarking_u0_g_ramified t x hx0 hTodd, zero_add]
  exact neg_eq_of_add_eq_zero_left (hV₂ (x 2))

/-- Ramified `D(c₀) = 0` (`c₀ = [d₀,z₀]`, both trivially-based; `z0.g` reuses the split lemma). -/
theorem liftMarking_c0_u_ramified (t : Marking C) (x : Fin 4 → V) (hx0 : ∀ v : V, t.x₀ • v = v)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) : (liftMarking t x).c0.u = 0 :=
  WordLift.commP_u_of_trivial _ _ (liftMarking_d0_g_ramified t x hx0 hTodd)
    (liftMarking_z0_g_smul t x hx0)

/-- Ramified `h₀.g` acts trivially (all sub-word bases trivial; only `hd0g` differs from split). -/
theorem liftMarking_h0_g_ramified (t : Marking C) (x : Fin 4 → V) (hx0 : ∀ v : V, t.x₀ • v = v)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (v : V) : (liftMarking t x).h0.g • v = v := by
  have hd0g := liftMarking_d0_g_ramified t x hx0 hTodd
  have hP1g : ∀ w : V, (conjP (liftMarking t x).x₀ (liftMarking t x).g0).g • w = w := fun w =>
    WordLift.conjP_g_trivial _ _ hx0 w
  have hdgg : ∀ w : V, (liftMarking t x).dg.g • w = w := fun w =>
    WordLift.conjP_g_trivial (liftMarking t x).d0 (liftMarking t x).g0 hd0g w
  have hhcg : ∀ w : V, (liftMarking t x).hc.g • w = w := fun w =>
    WordLift.commP_g_trivial _ _ hdgg hd0g w
  have hd02g : ∀ w : V, ((liftMarking t x).d0 ^ 2).g • w = w := fun w => by
    rw [WordLift.pow_g, pow_two, mul_smul, hd0g, hd0g]
  have hq1 := fun w => WordLift.mul_g_trivial _ (liftMarking t x).x₀ hP1g hx0 w
  have hq2 := fun w => WordLift.mul_g_trivial _ _ hq1 hdgg w
  have hq3 := fun w => WordLift.mul_g_trivial _ _ hq2 hd0g w
  have hq4 := fun w => WordLift.mul_g_trivial _ _ hq3 hd02g w
  show (conjP (liftMarking t x).x₀ (liftMarking t x).g0 * (liftMarking t x).x₀ *
    (liftMarking t x).dg * (liftMarking t x).d0 * (liftMarking t x).d0 ^ 2 *
    (liftMarking t x).hc).g • v = v
  exact WordLift.mul_g_trivial _ _ hq4 hhcg v

/-- Ramified `D(h₀) = 0` — **`hU`-free** (de-`hU`'d 2026-07-05): the cancellation happens in
`g₀`-conjugate *pairs*, `(g₀⁻¹•x₂ + x₂) + (g₀⁻¹•x₂ + x₂) = 0`, via `conjP_u_of_base_trivial` —
the `x₀^{g₀}`/`dg` terms carry the same `g₀⁻¹` prefix as each other, so no triviality of `g₀`'s
action is needed.  (`hU` is *not* derivable from admissibility: `S₃` on its 2-dimensional simple
module, marking `x₀=x₁=1`, is admissible with `σ₂ = σ` acting nontrivially.) -/
theorem liftMarking_h0_u_ramified (t : Marking C) (x : Fin 4 → V) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v → v = 0)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    (liftMarking t x).h0.u = 0 := by
  have hd0g := liftMarking_d0_g_ramified t x hx0 hTodd
  have hd0u := liftMarking_d0_u_ramified t x hV₂ hx0 htau hTodd
  have hP1g : ∀ w : V, (conjP (liftMarking t x).x₀ (liftMarking t x).g0).g • w = w := fun w =>
    WordLift.conjP_g_trivial _ _ hx0 w
  have hdgg : ∀ w : V, (liftMarking t x).dg.g • w = w := fun w =>
    WordLift.conjP_g_trivial (liftMarking t x).d0 (liftMarking t x).g0 hd0g w
  have hq1 := fun w => WordLift.mul_g_trivial _ (liftMarking t x).x₀ hP1g hx0 w
  have hq2 := fun w => WordLift.mul_g_trivial _ _ hq1 hdgg w
  have hq3 := fun w => WordLift.mul_g_trivial _ _ hq2 hd0g w
  have hd02g : ∀ w : V, ((liftMarking t x).d0 ^ 2).g • w = w := fun w => by
    rw [WordLift.pow_g, pow_two, mul_smul, hd0g, hd0g]
  have hq4 := fun w => WordLift.mul_g_trivial _ _ hq3 hd02g w
  have hP1u : (conjP (liftMarking t x).x₀ (liftMarking t x).g0).u
      = (liftMarking t x).g0.g⁻¹ • x 2 :=
    WordLift.conjP_u_of_base_trivial _ _ hx0
  have hdgu : (liftMarking t x).dg.u = (liftMarking t x).g0.g⁻¹ • x 2 := by
    show (conjP (liftMarking t x).d0 (liftMarking t x).g0).u = _
    rw [WordLift.conjP_u_of_base_trivial _ _ hd0g, hd0u]
  have hhcu : (liftMarking t x).hc.u = 0 := by
    show (commP (liftMarking t x).dg (liftMarking t x).d0).u = 0
    exact WordLift.commP_u_of_trivial _ _ hdgg hd0g
  have hd02u : ((liftMarking t x).d0 ^ 2).u = 0 := by
    rw [pow_two, WordLift.mul_u_of_trivial _ _ hd0g, hd0u]; exact hV₂ (x 2)
  show (conjP (liftMarking t x).x₀ (liftMarking t x).g0 * (liftMarking t x).x₀ *
    (liftMarking t x).dg * (liftMarking t x).d0 * (liftMarking t x).d0 ^ 2 *
    (liftMarking t x).hc).u = 0
  rw [WordLift.mul_u_of_trivial _ _ hq4, WordLift.mul_u_of_trivial _ _ hq3,
    WordLift.mul_u_of_trivial _ _ hq2, WordLift.mul_u_of_trivial _ _ hq1,
    WordLift.mul_u_of_trivial _ _ hP1g, hP1u, hhcu, hd02u, hdgu, hd0u]
  show (liftMarking t x).g0.g⁻¹ • x 2 + x 2 + (liftMarking t x).g0.g⁻¹ • x 2 + x 2 + 0 + 0 = 0
  rw [add_zero, add_zero,
    show (liftMarking t x).g0.g⁻¹ • x 2 + x 2 + (liftMarking t x).g0.g⁻¹ • x 2 + x 2
      = ((liftMarking t x).g0.g⁻¹ • x 2 + (liftMarking t x).g0.g⁻¹ • x 2) + (x 2 + x 2) from by
        abel,
    hV₂, hV₂, add_zero]

/-- **The ramified wild row (Lemma 5.5, `V^T = 0`)**: `L_w = D(h₀) + D(u₁⁻¹) + D(x₁^σ) + D(c₀) =
0 + 0 + S⁻¹·x₃ + 0 = S⁻¹·x₃`.  This is `(d1Fun t x).2` at a ramified simple module — the wild half
forcing `d = x₃ = 0` in the normal form. -/
theorem liftMarking_wildValue_u_ramified (t : Marking C) (x : Fin 4 → V) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    (liftMarking t x).wildValue.u = t.σ⁻¹ • x 3 := by
  have hh0g := liftMarking_h0_g_ramified t x hx0 hTodd
  have hu1g := liftMarking_u1_g_ramified t x hx1 hTodd
  have hx1sg : ∀ w : V, (conjP (liftMarking t x).x₁ (liftMarking t x).σ).g • w = w := fun w =>
    WordLift.conjP_g_trivial _ _ hx1 w
  have hu1invg : ∀ w : V, (liftMarking t x).u1⁻¹.g • w = w := fun w =>
    WordLift.inv_g_trivial _ hu1g w
  have hq2 := fun w => WordLift.mul_g_trivial _ _ hh0g hu1invg w
  have hq3 := fun w => WordLift.mul_g_trivial _ _ hq2 hx1sg w
  show ((liftMarking t x).h0 * (liftMarking t x).u1⁻¹ *
    conjP (liftMarking t x).x₁ (liftMarking t x).σ * (liftMarking t x).c0).u = t.σ⁻¹ • x 3
  rw [WordLift.mul_u_of_trivial _ _ hq3, WordLift.mul_u_of_trivial _ _ hq2,
    WordLift.mul_u_of_trivial _ _ hh0g, liftMarking_h0_u_ramified t x hV₂ hx0 htau hTodd,
    WordLift.inv_u_of_trivial _ hu1g, liftMarking_u1_u_ramified t x hx1 htau hTodd,
    liftMarking_conjP_x1_sigma_u t x hx1, liftMarking_c0_u_ramified t x hx0 hTodd]
  show 0 + -(0 : V) + t.σ⁻¹ • x 3 + 0 = t.σ⁻¹ • x 3
  abel

end WildRow

end FoxH

end GQ2

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.FoxBasic
public import GQ2.FoxHeisenberg.WildRow

@[expose] public section

/-!
# Proposition 4.1: the evaluated wild Fox row of the Roe relator  (⟦prop:jacobian⟧)

The `Γ_R` counterpart of `GQ2.FoxHeisenberg.WildRow`: at a tame lower map (the wild inertia
`x₀, x₁` acting trivially on the coefficient module `V`) the first Fox derivatives of the four
factors of

  `r_R = (x₀^σ)⁻¹ · a · x₁² · c`,   `a = (x₀⁻³τ)^{ω₂}`,   `c = [x₁, x₁^{σ₂}]`

collapse to plain `𝔽₂`-combinations of the lift offsets `x` (indices `0,1,2,3 = σ,τ,x₀,x₁`;
the note's lift variables `(a, b, c, d)`), giving the wild row of the note's display
⟦eq:jacobian⟧

  `d¹_{R,ρ,V} = [ S⁻¹(1+T)  S⁻¹+1+T  0  0 ;  0  P  P+S⁻¹  0 ]`.

Per-factor ledger (the note's proof of ⟦prop:jacobian⟧, quoted):

* "`D((x₀^σ)⁻¹) = S⁻¹c`" — `liftMarking_conjP_x0_sigma_u` (+ the char-2 sign flip in the
  assembled rows);
* "For `g = x₀⁻³τ`, one has `Dg = (−3)c + b = c + b` in characteristic 2, and `g` acts on `V`
  as `T`.  The profinite power/norm rule used in [RT Lemma 5.5] gives `D(g^{ω₂}) = P(c+b)`" —
  `liftMarking_aR_u` (split, `T = 1`, `P = 1`) and `liftMarking_aR_u_ramified` (`V^T = 0`,
  `P = 0`), via `WordLift.powOmega2_u_of_trivial` / `powOmega2_u_of_oddFixedPointFree`;
* "`D(x₁²) = (1+1)d = 0`" — `liftMarking_x1_sq_u`;
* "both entries of `[x₁, x₁^{σ₂}]` act trivially, so its first derivative is zero" —
  `liftMarking_cR_u` (`WordLift.commP_u_of_trivial`; no `σ₂`-hypothesis — `σ₂` is only a
  conjugator in `r_R`).

Assembled rows: **split** `L_w = b + (1 + S⁻¹)c` (`liftMarking_wildValueR_u`); **ramified**
`L_w = S⁻¹c` (`liftMarking_wildValueR_u_ramified`) — the note's `L_w = Pb + (P + S⁻¹)c` at
`P = 1` resp. `P = 0`.  The note's "Thus it is exactly the matrix in [RT (5.4)] after
interchanging the two wild columns" is mechanised by the stress tests
`liftMarking_wildValueR_u_eq_swap(_ramified)`.

Also here, the first half of Lemma 4.3 ⟦lem:trivial⟧: "For `V = 𝔽₂` with trivial action,
`d¹_R(a,b,c,d) = (b,b)`" (`d1FunR_of_trivial`/`d1R_of_trivial` — set `S = T = P = 1` in
⟦eq:jacobian⟧); the Gram second half ⟦eq:scalarform⟧ is ticket R25.

Organisation mirrors `GQ2/FoxHeisenberg/WildRow.lean` 1:1 (per-factor `u`-ledger and
base-triviality lemmas, then the assembled rows), so the `Γ_A` ↔ `Γ_R` correspondence is
line-readable; this file is far shorter — `r_R` has no class-two `h₀`-word, and two of its four
factors have zero first derivative outright.
-/

namespace GQ2

namespace FoxH

section WildRowR

variable {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]
  [Finite V]

omit [Finite C] [Finite V] in
/-- **`D(x₀^σ) = S⁻¹·x₂`** (tame case): conjugating by `σ` shifts the `x₀`-offset by `t.σ⁻¹`,
and the `σ`-offsets contributed by the two `σ`'s cancel — the `x₀`-analogue of
`liftMarking_conjP_x1_sigma_u`.  (The relator's first factor is the *inverse*; the char-2 sign
flip happens in the assembled rows.) -/
theorem liftMarking_conjP_x0_sigma_u (t : Marking C) (x : Fin 4 → V)
    (hx0 : ∀ v : V, t.x₀ • v = v) :
    (conjP (liftMarking t x).x₀ (liftMarking t x).σ).u = t.σ⁻¹ • x 2 := by
  show -(t.σ⁻¹ • x 0) + t.σ⁻¹ • x 2 + (t.σ⁻¹ * t.x₀) • x 0 = t.σ⁻¹ • x 2
  rw [mul_smul, hx0]; abel

/-! ### The `a = (x₀⁻³τ)^{ω₂}`-ledger

The base word `x₀⁻³τ` acts as `T` on `V` (the `x₀`-part is trivial), so the `ω₂`-power collapses
by `powOmega2_u_of_trivial` in the split case and is annihilated by
`powOmega2_u_of_oddFixedPointFree` in the ramified case — the note's `D(g^{ω₂}) = P(c+b)`. -/

omit [Finite C] [Finite V] in
/-- The base of `x₀³` acts trivially when `x₀` does (the `−3`-exponent leg of the `a`-word). -/
private theorem liftMarking_x0_pow3_g_smul (t : Marking C) (x : Fin 4 → V)
    (hx0 : ∀ v : V, t.x₀ • v = v) (v : V) : ((liftMarking t x).x₀ ^ 3).g • v = v := by
  rw [WordLift.pow_g]
  exact (MulAction.stabilizer C v).pow_mem (hx0 v) 3

omit [Finite C] [Finite V] in
/-- The base of the `a`-subword `x₀⁻³τ` acts trivially in the split case (`x₀, τ` trivial). -/
private theorem liftMarking_aR_base_g_smul (t : Marking C) (x : Fin 4 → V)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) (v : V) :
    ((((liftMarking t x).x₀ ^ 3)⁻¹ * (liftMarking t x).τ).g) • v = v :=
  WordLift.mul_g_trivial _ _
    (WordLift.inv_g_trivial _ (liftMarking_x0_pow3_g_smul t x hx0)) htau v

omit [Finite C] [Finite V] in
/-- **Split base-triviality of `a`**: any `ω₂`-power of a trivially-acting base acts
trivially. -/
theorem liftMarking_aR_g_smul (t : Marking C) (x : Fin 4 → V) (hx0 : ∀ v : V, t.x₀ • v = v)
    (htau : ∀ v : V, t.τ • v = v) (v : V) : (liftMarking t x).aR.g • v = v :=
  WordLift.powOmega2_g_smul_of_trivial _ (liftMarking_aR_base_g_smul t x hx0 htau) v

/-- **`D(a) = x₂ + x₁`** (split case) — the note's "`Dg = (−3)c + b = c + b` in characteristic
2" followed by "`D(g^{ω₂}) = P(c+b)`" at `P = 1`: with `x₀, τ` acting trivially the `ω₂`-power
in `a = (x₀⁻³τ)^{ω₂}` collapses (odd exponent, char 2) to its base-word offset
`D(x₀⁻³τ) = −3·x₂ + x₁ = x₂ + x₁`. -/
theorem liftMarking_aR_u (t : Marking C) (x : Fin 4 → V) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) :
    (liftMarking t x).aR.u = x 2 + x 1 := by
  have hq3g := liftMarking_x0_pow3_g_smul t x hx0
  have hq3u : ((liftMarking t x).x₀ ^ 3).u = x 2 := by
    rw [WordLift.pow_u]
    have hc : ∀ i : ℕ, (liftMarking t x).x₀.g ^ i • (liftMarking t x).x₀.u = x 2 := fun i =>
      (MulAction.stabilizer C (x 2)).pow_mem (hx0 (x 2)) i
    simp only [hc, Finset.sum_const, Finset.card_range]
    show (2 + 1) • x 2 = x 2
    rw [add_nsmul, two_nsmul, hV₂, zero_add, one_nsmul]
  have haR : (liftMarking t x).aR
      = powOmega2 (((liftMarking t x).x₀ ^ 3)⁻¹ * (liftMarking t x).τ) := rfl
  rw [haR, WordLift.powOmega2_u_of_trivial hV₂ _ (liftMarking_aR_base_g_smul t x hx0 htau),
    WordLift.mul_u_of_trivial _ _ (WordLift.inv_g_trivial _ hq3g),
    WordLift.inv_u_of_trivial _ hq3g, hq3u]
  show -(x 2) + x 1 = x 2 + x 1
  rw [neg_eq_of_add_eq_zero_left (hV₂ (x 2))]

/-- **Ramified base-triviality of `a`**: with `τ` acting with odd order (trivial 2-part,
`hTodd`), the base of `a = (x₀⁻³τ)^{ω₂}` still acts *trivially* on `V` — its action is the
2-part of the `τ`-action.  Mirrors `liftMarking_u0_g_ramified` (finite-exponent independence
`powOmega2_pow_eq` + `powOmega2_smul_of_trivial_mul`). -/
theorem liftMarking_aR_g_ramified (t : Marking C) (x : Fin 4 → V)
    (hx0 : ∀ v : V, t.x₀ • v = v) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (v : V) :
    (liftMarking t x).aR.g • v = v := by
  have hx03 : ∀ w : V, t.x₀ ^ 3 • w = w := fun w => (MulAction.stabilizer C w).pow_mem (hx0 w) 3
  have hx03inv : ∀ w : V, (t.x₀ ^ 3)⁻¹ • w = w := fun w => inv_smul_eq_iff.mpr (hx03 w).symm
  have hg : ((((liftMarking t x).x₀ ^ 3)⁻¹ * (liftMarking t x).τ).g) = (t.x₀ ^ 3)⁻¹ * t.τ := by
    rw [WordLift.mul_g, WordLift.inv_g, WordLift.pow_g]; rfl
  have hgeq : (liftMarking t x).aR.g = powOmega2 ((t.x₀ ^ 3)⁻¹ * t.τ) := by
    show (powOmega2 (((liftMarking t x).x₀ ^ 3)⁻¹ * (liftMarking t x).τ)).g = _
    rw [powOmega2, WordLift.pow_g, hg]
    exact powOmega2_pow_eq ((t.x₀ ^ 3)⁻¹ * t.τ)
      (orderOf_dvd_of_pow_eq_one (by rw [← hg, ← WordLift.pow_g, pow_orderOf_eq_one]; rfl))
      (orderOf_pos _).ne'
  rw [hgeq]
  exact WordLift.powOmega2_smul_of_trivial_mul _ t.τ hx03inv hTodd v

/-- **Ramified `D(a) = 0`** — the note's `D(g^{ω₂}) = P(c+b)` at `P = 0`: the `ω₂`-norm over
the fixed-point-free odd-order `τ`-base vanishes (`powOmega2_u_of_oddFixedPointFree`). -/
theorem liftMarking_aR_u_ramified (t : Marking C) (x : Fin 4 → V)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v → v = 0)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    (liftMarking t x).aR.u = 0 := by
  have hx03 : ∀ w : V, t.x₀ ^ 3 • w = w := fun w => (MulAction.stabilizer C w).pow_mem (hx0 w) 3
  have hx03inv : ∀ w : V, (t.x₀ ^ 3)⁻¹ • w = w := fun w => inv_smul_eq_iff.mpr (hx03 w).symm
  have hg : ((((liftMarking t x).x₀ ^ 3)⁻¹ * (liftMarking t x).τ).g) = (t.x₀ ^ 3)⁻¹ * t.τ := by
    rw [WordLift.mul_g, WordLift.inv_g, WordLift.pow_g]; rfl
  show (powOmega2 (((liftMarking t x).x₀ ^ 3)⁻¹ * (liftMarking t x).τ)).u = 0
  refine WordLift.powOmega2_u_of_oddFixedPointFree _ (fun v hv => htau v ?_) (fun v => ?_)
  · rw [← hx03inv (t.τ • v), ← mul_smul, ← hg]
    exact hv
  · rw [hg]
    exact WordLift.powOmega2_smul_of_trivial_mul _ t.τ hx03inv hTodd v

/-! ### The `x₁²`- and `c = [x₁, y₁]`-ledgers

Both die at the first derivative: `x₁²` by char 2, the commutator because both entries are
trivially-based (`x₁` by wild-core triviality, `y₁ = x₁^{σ₂}` as a *conjugate* of `x₁` — for any
conjugator, so no `σ₂`-tameness hypothesis enters, unlike the `Γ_A` aux-word ledger). -/

omit [Finite C] [Finite V] in
/-- Base-triviality of `x₁²`. -/
theorem liftMarking_x1_sq_g_smul (t : Marking C) (x : Fin 4 → V)
    (hx1 : ∀ v : V, t.x₁ • v = v) (v : V) : ((liftMarking t x).x₁ ^ 2).g • v = v := by
  rw [WordLift.pow_g]
  show t.x₁ ^ 2 • v = v
  rw [pow_two, mul_smul, hx1, hx1]

omit [Finite C] [Finite V] in
/-- **`D(x₁²) = 0`** — the note's "`D(x₁²) = (1+1)d = 0`" (char 2). -/
theorem liftMarking_x1_sq_u (t : Marking C) (x : Fin 4 → V) (hV₂ : ∀ v : V, v + v = 0)
    (hx1 : ∀ v : V, t.x₁ • v = v) : ((liftMarking t x).x₁ ^ 2).u = 0 := by
  rw [pow_two, WordLift.mul_u]
  show x 3 + t.x₁ • x 3 = 0
  rw [hx1]
  exact hV₂ (x 3)

omit [Finite C] [Finite V] in
/-- Base-triviality of `y₁ = x₁^{σ₂}`: a conjugate of the trivially-acting `x₁` acts trivially,
for *any* conjugator — no hypothesis on the `σ₂`-action is needed. -/
theorem liftMarking_y1R_g_smul (t : Marking C) (x : Fin 4 → V)
    (hx1 : ∀ v : V, t.x₁ • v = v) (v : V) : (liftMarking t x).y1R.g • v = v := by
  show (conjP (liftMarking t x).x₁ (liftMarking t x).sigma2).g • v = v
  exact WordLift.conjP_g_trivial _ _ hx1 v

omit [Finite C] [Finite V] in
/-- Base-triviality of `c = [x₁, y₁]`. -/
theorem liftMarking_cR_g_smul (t : Marking C) (x : Fin 4 → V)
    (hx1 : ∀ v : V, t.x₁ • v = v) (v : V) : (liftMarking t x).cR.g • v = v := by
  show (commP (liftMarking t x).x₁ (liftMarking t x).y1R).g • v = v
  exact WordLift.commP_g_trivial _ _ hx1 (liftMarking_y1R_g_smul t x hx1) v

omit [Finite C] [Finite V] in
/-- **`D(c) = 0`** — the note's "both entries of `[x₁, x₁^{σ₂}]` act trivially, so its first
derivative is zero" (`commP_u_of_trivial`).  Holds in the split *and* ramified cases alike. -/
theorem liftMarking_cR_u (t : Marking C) (x : Fin 4 → V)
    (hx1 : ∀ v : V, t.x₁ • v = v) : (liftMarking t x).cR.u = 0 := by
  show (commP (liftMarking t x).x₁ (liftMarking t x).y1R).u = 0
  exact WordLift.commP_u_of_trivial _ _ hx1 (liftMarking_y1R_g_smul t x hx1)

/-! ### The assembled wild rows (⟦prop:jacobian⟧, display ⟦eq:jacobian⟧) -/

/-- **The split wild row** (⟦prop:jacobian⟧, `T = 1`, `P = 1`):
`L_w = D((x₀^σ)⁻¹) + D(a) + D(x₁²) + D(c) = S⁻¹·x₂ + (x₂ + x₁) + 0 + 0 = x₁ + (1 + S⁻¹)·x₂` —
the note's `L_w = Pb + (P + S⁻¹)c` at `P = 1`.  This is `(d1FunR t x).2` at a split simple tame
module: `Γ_A`'s row with the two wild columns interchanged
(`liftMarking_wildValueR_u_eq_swap`).  Note **no `σ₂`-tameness hypothesis `hU`**, unlike
`liftMarking_wildValue_u` — `σ₂` enters `r_R` only as a conjugator. -/
theorem liftMarking_wildValueR_u (t : Marking C) (x : Fin 4 → V) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v) :
    (liftMarking t x).wildValueR.u = x 1 + x 2 + t.σ⁻¹ • x 2 := by
  have hconjg : ∀ w : V, (conjP (liftMarking t x).x₀ (liftMarking t x).σ).g • w = w := fun w =>
    WordLift.conjP_g_trivial _ _ hx0 w
  have hf1g : ∀ w : V, ((conjP (liftMarking t x).x₀ (liftMarking t x).σ)⁻¹).g • w = w :=
    fun w => WordLift.inv_g_trivial _ hconjg w
  have haRg := liftMarking_aR_g_smul t x hx0 htau
  have hsqg := liftMarking_x1_sq_g_smul t x hx1
  have hq2 := fun w => WordLift.mul_g_trivial _ _ hf1g haRg w
  have hq3 := fun w => WordLift.mul_g_trivial _ _ hq2 hsqg w
  show ((conjP (liftMarking t x).x₀ (liftMarking t x).σ)⁻¹ * (liftMarking t x).aR *
      (liftMarking t x).x₁ ^ 2 * (liftMarking t x).cR).u = x 1 + x 2 + t.σ⁻¹ • x 2
  rw [WordLift.mul_u_of_trivial _ _ hq3, WordLift.mul_u_of_trivial _ _ hq2,
    WordLift.mul_u_of_trivial _ _ hf1g, WordLift.inv_u_of_trivial _ hconjg,
    liftMarking_conjP_x0_sigma_u t x hx0, liftMarking_aR_u t x hV₂ hx0 htau,
    liftMarking_x1_sq_u t x hV₂ hx1, liftMarking_cR_u t x hx1,
    show -(t.σ⁻¹ • x 2) = t.σ⁻¹ • x 2 from neg_eq_of_add_eq_zero_left (hV₂ _)]
  abel

/-- **The ramified wild row** (⟦prop:jacobian⟧, `V^T = 0`, `P = 0`):
`L_w = D((x₀^σ)⁻¹) + D(a) + D(x₁²) + D(c) = S⁻¹·x₂ + 0 + 0 + 0 = S⁻¹·x₂` — the note's
`L_w = Pb + (P + S⁻¹)c` at `P = 0`.  This is `(d1FunR t x).2` at a ramified simple module —
the wild half forcing `c = x₂ = 0` in the normal form (ticket R22). -/
theorem liftMarking_wildValueR_u_ramified (t : Marking C) (x : Fin 4 → V)
    (hV₂ : ∀ v : V, v + v = 0) (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    (liftMarking t x).wildValueR.u = t.σ⁻¹ • x 2 := by
  have hconjg : ∀ w : V, (conjP (liftMarking t x).x₀ (liftMarking t x).σ).g • w = w := fun w =>
    WordLift.conjP_g_trivial _ _ hx0 w
  have hf1g : ∀ w : V, ((conjP (liftMarking t x).x₀ (liftMarking t x).σ)⁻¹).g • w = w :=
    fun w => WordLift.inv_g_trivial _ hconjg w
  have haRg := liftMarking_aR_g_ramified t x hx0 hTodd
  have hsqg := liftMarking_x1_sq_g_smul t x hx1
  have hq2 := fun w => WordLift.mul_g_trivial _ _ hf1g haRg w
  have hq3 := fun w => WordLift.mul_g_trivial _ _ hq2 hsqg w
  show ((conjP (liftMarking t x).x₀ (liftMarking t x).σ)⁻¹ * (liftMarking t x).aR *
      (liftMarking t x).x₁ ^ 2 * (liftMarking t x).cR).u = t.σ⁻¹ • x 2
  rw [WordLift.mul_u_of_trivial _ _ hq3, WordLift.mul_u_of_trivial _ _ hq2,
    WordLift.mul_u_of_trivial _ _ hf1g, WordLift.inv_u_of_trivial _ hconjg,
    liftMarking_conjP_x0_sigma_u t x hx0, liftMarking_aR_u_ramified t x hx0 htau hTodd,
    liftMarking_x1_sq_u t x hV₂ hx1, liftMarking_cR_u t x hx1,
    show -(t.σ⁻¹ • x 2) = t.σ⁻¹ • x 2 from neg_eq_of_add_eq_zero_left (hV₂ _)]
  abel

/-! ### Stress tests: the column swap and the trivial module -/

/-- **Stress test (the column swap, split)**: the note's "Thus it is exactly the matrix in
[RT (5.4)] after interchanging the two wild columns" — the split `Γ_R` wild row at offsets `x`
equals the `Γ_A` wild row at the offsets with the two wild coordinates `x₂ ↔ x₃`
interchanged. -/
theorem liftMarking_wildValueR_u_eq_swap (t : Marking C) (x : Fin 4 → V)
    (hV₂ : ∀ v : V, v + v = 0) (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v) (hU : ∀ v : V, t.sigma2 • v = v) :
    (liftMarking t x).wildValueR.u = (liftMarking t ![x 0, x 1, x 3, x 2]).wildValue.u := by
  rw [liftMarking_wildValueR_u t x hV₂ hx0 hx1 htau,
    liftMarking_wildValue_u t ![x 0, x 1, x 3, x 2] hV₂ hx0 hx1 htau hU]
  rfl

/-- **Stress test (the column swap, ramified)**: both ramified wild rows see only the
`S⁻¹`-column, which the swap moves from `x₃` (`Γ_A`) to `x₂` (`Γ_R`). -/
theorem liftMarking_wildValueR_u_ramified_eq_swap (t : Marking C) (x : Fin 4 → V)
    (hV₂ : ∀ v : V, v + v = 0) (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    (liftMarking t x).wildValueR.u = (liftMarking t ![x 0, x 1, x 3, x 2]).wildValue.u := by
  rw [liftMarking_wildValueR_u_ramified t x hV₂ hx0 hx1 htau hTodd,
    liftMarking_wildValue_u_ramified t ![x 0, x 1, x 3, x 2] hV₂ hx0 hx1 htau hTodd]
  rfl

/-- **Lemma 4.3 ⟦lem:trivial⟧, first half**: on the trivial module `d¹_R` collapses to the
diagonal `x ↦ (x₁, x₁)` — the note's "For `V = 𝔽₂` with trivial action, `d¹_R(a,b,c,d) =
(b,b)`" (set `S = T = P = 1` in ⟦eq:jacobian⟧).  Tame row: `Γ_A`'s, via `d1FunR_tame`, giving
`x₁`; wild row: `x₁ + x₂ + x₂ = x₁` (char 2).  Mirrors `d1Fun_of_trivial`
(`GQ2/TrivialSelfDual.lean`); R25's `trivialSelfDual_R` consumes this together with the Gram
⟦eq:scalarform⟧. -/
theorem d1FunR_of_trivial (t : Marking C) (ht : t.TameRel) (_ : t.WildRelR)
    (htriv : ∀ (c : C) (a : V), c • a = a) (hV₂ : ∀ v : V, v + v = 0) (x : Fin 4 → V) :
    d1FunR t x = (x 1, x 1) := by
  have h1 : (d1FunR t x).1 = x 1 := by
    rw [d1FunR_tame t ht x]
    simp only [htriv]
    rw [hV₂ (x 1)]
    abel
  have h2 : (d1FunR t x).2 = x 1 := by
    show (liftMarking t x).wildValueR.u = x 1
    rw [liftMarking_wildValueR_u t x hV₂ (htriv t.x₀) (htriv t.x₁) (htriv t.τ),
      htriv t.σ⁻¹ (x 2), add_assoc, hV₂ (x 2), add_zero]
  exact Prod.ext h1 h2

/-- `d¹_R` bundled, on the trivial module: `d1R t x = (x 1, x 1)` — the note's
`d¹_R(a,b,c,d) = (b,b)`. -/
theorem d1R_of_trivial (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (htriv : ∀ (c : C) (a : V), c • a = a) (hV₂ : ∀ v : V, v + v = 0) (x : Fin 4 → V) :
    d1R t x = (x 1, x 1) :=
  d1FunR_of_trivial t ht hw htriv hV₂ x

end WildRowR

end FoxH

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * Proposition 4.1 (Evaluated Jacobian) = ⟦prop:jacobian⟧ — the per-factor ledger
    (`liftMarking_conjP_x0_sigma_u`, `liftMarking_aR_u(_ramified)`, `liftMarking_x1_sq_u`,
    `liftMarking_cR_u`) and the assembled rows `liftMarking_wildValueR_u(_ramified)`;
    display ⟦eq:jacobian⟧.
  * "the matrix in [RT (5.4)] after interchanging the two wild columns" =
    `liftMarking_wildValueR_u_eq_swap(_ramified)`.
  * Lemma 4.3 (Trivial coefficient) = ⟦lem:trivial⟧, first half —
    `d1FunR_of_trivial`/`d1R_of_trivial` (`d¹_R(a,b,c,d) = (b,b)`); the scalar Gram
    ⟦eq:scalarform⟧ second half is ticket R25.
-/

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Certificates.N0Fox
import GQ2.Dyadic.Word.Stokes
import GQ2.Dyadic.Word.Hessian

/-!
# Dyadic campaign, ticket WN0-c: Stokes, scalar, Hessian and phase certificates for compact `N_α`

The closing file of the pilot lane (packet Def. 9.1 items (5)–(6) for row 2 of the R5
selection freeze), on top of WN0-a's word (`GQ2/Dyadic/Words/N0.lean`), WN0-b's Fox
certificate (`GQ2/Dyadic/Certificates/N0Fox.lean`), WW3's second-order layer
(`GQ2/Dyadic/Word/Stokes.lean`) and WW4's Hessian/phase interface
(`GQ2/Dyadic/Word/{Hessian,Phase}.lean`).

```
R_{N,α,0} = x₀^{2+2^α} [x₀,x₁] · x₂^{-σ} (x₂τ)^{ω₂} · H_h,      α ≥ 2
```

## 1. The Stokes certificate (second order via WW3's `heisEvalZ`)

`heisZ_nCompact_unram` evaluates the word's central (Stokes) coordinate at the Heisenberg
lift of any simple-tame-module marking (`hwild` + `hτ`, the unramified class of WN0-b's
rows), at an arbitrary resolver value `E ω₂ = e`.  The value decomposes as

* the **`x₀`-diagonal** `y₀(a₀)` — the binomial coefficient `C(2+2^α, 2)` is odd exactly
  for `α ≥ 2` (`choose_two_add_two_pow_odd`), which is the freeze's "α ≥ 2 is a Hessian
  condition" at the Stokes level (WN0-b measured that first order sees only `α ≥ 1`);
* the **`(x₀,x₁)` hyperbolic cross** `y₀(a₁) + y₁(a₀)` from `[x₀,x₁]`;
* the **boundary block** on `(σ,τ,x₂)`, whose clean form (`heisZ_nCompact_res_one`, at
  the honest resolver class `e ≡ 1 mod 4`) is `y_σ(a₂) + y₂(a_σ + (1+S)(a₂+a_τ))` — the
  second-order shadow of WN0-b's invertible `1 − S⁻¹` unramified Fox block
  (`isUnit_onePlusSEnd_iff` ties `1 + S` to `isUnit_oneSubSInvEnd_iff` by composition);
* the **`h` identity-operator hyperbolic planes**
  `Σ_j (y_{u_j}(a_{v_j}) + y_{v_j}(a_{u_j}))` (`heisZ_handlesW`) — no `S`/`T` operator
  touches the handle block, at any handle count.

This is the S2.1/S2.6 Sage-side block structure ("rank-3 core atoms ⊕ `h` hyperbolic
planes", certificates `N-compact-alpha{2,3,4}-h{0,1}-v001`, battery `regressed-F-G`) in
Lean: the three core atoms are the `(x₀,x₁)`-plane (unimodular over every module,
`coreBlockEquiv`), the `x₀`-diagonal, and the `(1+S)`-atom on `x₂`
(`heisZ_nCompact_wild_block`), invertible exactly on `V^S = 0` — WN0-b's dichotomy.

The **resolver dependence is exact**: the general form carries `e•` and `C(e,2)•`
coefficients, and `C(e,2)` depends on `e mod 4` — the Stokes-level trace of ticket
S1.T's "the lift level is 4, not 2" (`kappa0_pow_eq_one_of_snd_pow`).  The honest `ω₂`
representative for a finite 2-group target satisfies `e ≡ 1 (mod 2^k)` (WW1's engine;
`GQ2.omega2Exp` on a `2`-power is literally `1`), so `heisZ_nCompact_res_one` is the
certificate form; the `e ≡ 3` twin is pinned at the scalar Gram
(`sqrtNegTwo_scalarGram_three`) to keep the sensitivity visible.

**The duality payload**: `nCompact_stokesDuality` instantiates WW3's packet-Lem-5.1
engine `stokesDuality_of_simple` at the resolved two-relator family `nCompactFam`
(tame `τ^σ(τ^q)⁻¹` first, wild second — WW2's Jacobian row order), with `hr` discharged
through `lift_heisToFree_eq_one_iff` from Gate-level `evalZ = 1` facts and `hend`
discharged by `nCompact_isStokesEndpoint` — proved for **all** `α, h` and all even `q`,
odd `e` (the per-instance `decide` route of the WW3 stress pin is subsumed;
`sqrtNegTwo_isStokesEndpoint` pins the `(2,0,2,3)` instance).  Per-simple-module duality
stays a hypothesis slot: discharging it per coefficient module is gate-F/AS-lane work,
exactly as in the frozen `ℚ₂` chain.

## 2. The scalar certificate (cup–Bockstein / `stokesGram`, Gram-by-`decide`)

`sqrtNegTwo_scalarGram` pins the traced Stokes Gram matrix of the `√−2` family on the
scalar module (`A = 𝔽₂`, trivial action) at the standard letter basis, in the packet
column order `σ, τ, x₀, x₁, x₂` — the `GQ2/Roe/TrivialSelfDual.lean` `scalarGramR`
comparison shape.  Diagonal entries (the Bockstein squares) sit at `τ` (from the tame
relator, `C(q,2)` odd at `q = 2`) and `x₀` (from `C(6,2) = 15` odd); the off-diagonal
(cup) blocks are the `(x₀,x₁)`- and `(σ,x₂)`-, `(σ,τ)`-pairings.  The `e = 3` twin
`sqrtNegTwo_scalarGram_three` differs in exactly the `{τ,x₂}²`-block — the Bockstein
diagonal migrating with the resolver class, `class2.py`'s "the polarization alone cannot
see the Bockstein diagonal" as a kernel-checked matrix pair.  The field-side (Hilbert
symbol) comparison column is AS2's: it needs `K = ℚ₂(√−2)` data that no word ticket owns.

## 3. The Hessian certificate (the word connected to WW4's endpoint)

WW4's `compactN_certificate` already certifies the frozen endpoint
`Q = q(c₀) + b_q(c₀,c₁) = plusFormD q q` (identity CoV, `diag := fun v ↦ dat.f v v`).
What WN0-c adds is the **word-side equation**: `hessRelZ_nCompact` evaluates the word
through WW4's extraspecial route (`hessRelZ`/`hessEvalZ` at the κ⁰-cocycle
`kappa0Cocycle dat hdat` on `V ⋊ C`) at the graph-type marking `hessMark` (σ, τ on the
κ-free `C`-line; wild letters on the Heisenberg slice; **`x₂` carries no primal letter**
— the ratified boundary convention) and proves the fibre is

```
q(c₀) + b_q(c₀, c₁) + Σ_j b_q(d_j, e_j)
```

for **every** resolver pair `(E, E₂)` — the boundary block `x₂^{-σ}(x₂τ)^{ω₂}` dies on
the `C`-line for every exponent, so the twist-immunity of freeze row 2 extends to
resolver-immunity, and the honest-`ω₂` instance needs no per-word exponent pin (it is
`sqrtNegTwo_hess_eval`, through F2's genuine profinite `Marking.eval` and the
`eval_eq_evalNat_exponent` bridge, with **no** hypotheses on the boundary letters).
At `h = 0` the value is `plusFormD q q (c₀, c₁)` on the nose
(`hessRelZ_nCompact_plusForm`) — the `Q`-parameter of `compactN_certificate` — and
`nCompact_word_gaussSum` closes the loop by computing the Gauss sum of the *word's*
evaluated Hessian through the certificate's `affinePhase.G0`.

κ⁰-normalization bookkeeping (deviation-grade note): the endpoint values consume `hdat`
only through `f_diag`/`f_polar`, like WW4's worked rows; the evaluation *calculus*
additionally uses the normalization clauses `f_zero_left/right`, `m_one`, the derived
`m_zero` (`factorSet_m_zero`) and — in the slice commutator only — `f_cocycle`.  All of
these are `q`-blind, so the twist-immunity claim is untouched; they are the clauses that
make `κ⁰` a cocycle at all, and the NC lane's slice calculus uses the same set.

## 4. The phase consumables (`c₁`-Lagrangian ⇒ Gauss `2^{nd/2}`)

At `Φ := (compactN_certificate …).affinePhase` (WW4's `plusFormPhaseCover`, `baseSign
= 1` by the `c₁`-Lagrangian computation `gaussSum_plusFormD`): `nCompact_G0` pins
`Φ.G0 = 2^d`; `nCompact_gauss_translate` instantiates packet Lem 6.1's shifted-sum
output at raw shift vectors; `nCompact_gauss_pow` is the `SN`-valued degree-`n`
magnitude `2^{n·d}` via `gaussSum_pi_of_baseSign_one` — with `dim(V×V) = 2d` this *is*
the `c₁`-Lagrangian ⇒ Gauss `2^{nd/2}` statement in `standardNumerics` shape
(`SN.gaussRam`, positive sign), and `sqrtNegTwo_gauss_degree_two` pins the `n = 2`
instance of the `ℚ₂(√−2)` row.

## 5. The `√−2` instance and the handle story

The `(α, q, h, n) = (2, 2, 0, 2)` instance is pinned end-to-end: the Stokes endpoint
condition (`sqrtNegTwo_isStokesEndpoint`), the duality wrapper (`nCompact_stokesDuality`
applies verbatim), both scalar Grams, the honest Hessian evaluation
(`sqrtNegTwo_hess_eval`) and the degree-2 Gauss magnitude.

**Handles at general `h`.**  Provable here and proved: the handle tail contributes the
`h` identity-operator hyperbolic planes to the Stokes pairing (`heisZ_handlesW`) and the
`Σ_j b_q(d_j, e_j)` tail to the evaluated Hessian (`hessRelZ_nCompact`), is jet-zero
(so it never shifts the affine phase — WW4's `heisJetZero_mul_right_jet` applies), and
the full `h`-handle endpoint keeps `ε = +1`: its Gauss sum is `2^{d(h+1)}`
(`nCompact_handle_form_gaussSum`).  On a rank-one (scalar-type) coefficient module the
polar form vanishes identically (`polar_zmod2_eq_zero`), so the planes are invisible
there — the Lean-side shard of F5's Sage measurement that **permutation-module targets
are blind to `h`** (the frozen row's `(S₃, D₈, A₄)` epimorphism vector is `h`-independent
on such gates), while the **`C₄`-centre extraspecial witness sees them**: at the
hyperbolic-plane datum the `h = 1` word evaluates to fibre `1` with all core offsets
zero (`stress_handle_visible`); the corresponding Sage-side count separation is recorded
in the certificate battery and cited here only.

## Implementation notes

Not `module`-style, and forced: `GQ2.Dyadic.Certificates.N0Fox` is plain-import (the
WN0-a ruling that `Words/` and `Certificates/` are plain-import layers); the
`module`-style imports (`Stokes`, `Hessian`) are fine in this direction.  No new
axioms; kernel `decide` only (the Gram pins and stress pins); no `Marking.eval` outside
the finite-discrete instances WW5/WN0-a already use.

Axiom prints are recorded in the section docstrings the way WN0-b did; every headline
prints a subset of the standard three (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GQ2.Dyadic.Certificates

open GQ2.FoxH GQ2.Dyadic.Words

/-! ## `𝔽₂` parity helpers

The two cast lemmas that make every parity step below uniform, plus the two binomial
parities of the row: `C(2+2^α, 2)` is odd for `α ≥ 2` (the Hessian condition of freeze
row 2, at the Stokes level), and `C(e, 2)` is even on the honest resolver class
`e ≡ 1 (mod 4)` (ticket S1.T's modulus). -/

section Parity

theorem natCast_zmod2_even {n : ℕ} (hn : Even n) : (n : ZMod 2) = 0 := by
  obtain ⟨m, rfl⟩ := hn
  push_cast
  ring_nf
  simp [CharTwo.two_eq_zero]

theorem natCast_zmod2_odd {n : ℕ} (hn : Odd n) : (n : ZMod 2) = 1 := by
  obtain ⟨m, rfl⟩ := hn
  push_cast
  simp [CharTwo.two_eq_zero]

theorem nsmul_zmod2_even {n : ℕ} (hn : Even n) (z : ZMod 2) : n • z = 0 := by
  rw [nsmul_eq_mul, natCast_zmod2_even hn, zero_mul]

theorem nsmul_zmod2_odd {n : ℕ} (hn : Odd n) (z : ZMod 2) : n • z = z := by
  rw [nsmul_eq_mul, natCast_zmod2_odd hn, one_mul]

/-- `C(2+2^α, 2)` is odd exactly on the branch condition `α ≥ 2`: with
`2 + 2^α = 2m`, `C(2m, 2) = m(2m−1)` and `m = 1 + 2^{α−1}` is odd iff `α ≥ 2`
(`Words.odd_one_add_two_pow`).  This is where the freeze's "`α ≥ 2` is a Hessian
condition" lives: WN0-b's first-order rows see only the parity of `2 + 2^α`. -/
theorem choose_two_add_two_pow_odd {α : ℕ} (hα : 2 ≤ α) : Odd ((2 + 2 ^ α).choose 2) := by
  have hm : 2 + 2 ^ α = 2 * (1 + 2 ^ (α - 1)) := Words.two_add_two_pow α (by omega)
  set m := 1 + 2 ^ (α - 1) with hm_def
  have hchoose : (2 * m).choose 2 = m * (2 * m - 1) := by
    rw [Nat.choose_two_right, show 2 * m * (2 * m - 1) = m * (2 * m - 1) * 2 by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  rw [hm, hchoose]
  have hm1 : 1 ≤ m := Nat.le_add_right 1 _
  exact (Words.odd_one_add_two_pow hα).mul ⟨m - 1, by omega⟩

/-- `C(e, 2)` is even on the resolver class `e ≡ 1 (mod 4)` — the class the honest `ω₂`
representative for a `2`-group target lives in (`omega2Exp` of a `2`-power is `1`).
On `e ≡ 3 (mod 4)` it is odd; the pair of scalar Gram pins below keeps the difference
visible (ticket S1.T: the lift level is `4`, not `2`). -/
theorem choose_two_even_of_mod_four {e : ℕ} (he : e % 4 = 1) : Even (e.choose 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, e = 4 * k + 1 := ⟨e / 4, by omega⟩
  rw [Nat.choose_two_right, show 4 * k + 1 - 1 = 4 * k by omega,
    show (4 * k + 1) * (4 * k) = (4 * k + 1) * k * 2 * 2 by ring,
    Nat.mul_div_cancel _ (by norm_num)]
  exact ⟨(4 * k + 1) * k, by ring⟩

theorem odd_of_mod_four_eq_one {e : ℕ} (he : e % 4 = 1) : Odd e := by
  obtain ⟨k, rfl⟩ : ∃ k, e = 4 * k + 1 := ⟨e / 4, by omega⟩
  exact ⟨2 * k, by ring⟩

end Parity

/-! ## The Heisenberg toolkit: powers, commutators and conjugates of trivial-base lifts

Three closed forms for `HeisLift`-values whose base acts trivially — the per-factor
engine of the second-order row, mirroring WN0-b's `trivAct` toolkit one degree up.
The commutator form needs **no** 2-torsion (the offsets cancel exactly); only the power
form's simplifications do. -/

section HeisToolkit

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- A trivially-acting base acts trivially on the elementary dual as well
(the contragredient of the identity). -/
theorem smul_elemDual_of_trivial {g : C} (hg : ∀ a : A, g • a = a) (lam : ElemDual A) :
    g • lam = lam := by
  refine ElemDual.ext fun a => ?_
  rw [ElemDual.smul_apply]
  exact congrArg lam (inv_smul_eq_iff.mpr (hg a).symm)

private theorem elemDual_nsmul_apply (k : ℕ) (f : ElemDual A) (a : A) :
    (k • f) a = k • f a := by
  induction k with
  | zero => rfl
  | succ k ih => rw [succ_nsmul, succ_nsmul, ElemDual.add_apply, ih]

/-- **The power law for a trivial-base Heisenberg lift**:
`p^n = (n·a, n·λ, n·z + C(n,2)·λ(a); gⁿ)`.  The binomial coefficient is the whole
second-order content of a power — the `q(c₀)`-production mechanism of the leading
`x₀^{2+2^α}`. -/
theorem heisPow_of_trivial (p : HeisLift A C) (hp : ∀ a : A, p.g • a = a) (n : ℕ) :
    p ^ n = ⟨n • p.a, n • p.l, n • p.z + (n.choose 2) • p.l p.a, p.g ^ n⟩ := by
  induction n with
  | zero =>
      refine HeisLift.ext ?_ ?_ ?_ ?_ <;> simp
  | succ n ih =>
      have hgn : ∀ a : A, (p.g ^ n) • a = a := fun a =>
        mem_trivAct.mp (pow_mem (mem_trivAct (V := A).mpr hp) n) a
      rw [pow_succ, ih]
      refine HeisLift.ext ?_ ?_ ?_ ?_
      · show n • p.a + (p.g ^ n) • p.a = (n + 1) • p.a
        rw [hgn, succ_nsmul]
      · show n • p.l + (p.g ^ n) • p.l = (n + 1) • p.l
        rw [smul_elemDual_of_trivial hgn, succ_nsmul]
      · show n • p.z + (n.choose 2) • p.l p.a + p.z + (n • p.l) ((p.g ^ n) • p.a)
          = (n + 1) • p.z + ((n + 1).choose 2) • p.l p.a
        rw [hgn, elemDual_nsmul_apply, Nat.choose_succ_succ n 1, Nat.choose_one_right]
        simp only [add_nsmul, succ_nsmul]
        abel
      · show p.g ^ n * p.g = p.g ^ (n + 1)
        rw [pow_succ]

/-- **The commutator of two trivial-base Heisenberg lifts is jet-zero central** with
value the mixed pairing `λ_p(a_q) + λ_q(a_p)` — an identity-operator hyperbolic plane.
No 2-torsion hypothesis: the offsets cancel exactly, only the `ZMod 2` centre folds
signs.  This is each handle pair's entire second-order content. -/
theorem heisCommR_of_trivial (p r : HeisLift A C) (hp : ∀ a : A, p.g • a = a)
    (hr : ∀ a : A, r.g • a = a) :
    commR p r = ⟨0, 0, p.l r.a + r.l p.a, commR p.g r.g⟩ := by
  have hpi : ∀ a : A, p.g⁻¹ • a = a := fun a => inv_smul_eq_iff.mpr (hp a).symm
  have hri : ∀ a : A, r.g⁻¹ • a = a := fun a => inv_smul_eq_iff.mpr (hr a).symm
  rw [commR]
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · simp only [HeisLift.mul_a, HeisLift.inv_a, HeisLift.mul_g, HeisLift.inv_g, mul_smul,
      hp, hpi, hri]
    abel
  · simp only [HeisLift.mul_l, HeisLift.inv_l, HeisLift.mul_g, HeisLift.inv_g, mul_smul,
      smul_elemDual_of_trivial hp, smul_elemDual_of_trivial hpi, smul_elemDual_of_trivial hri]
    abel
  · simp only [HeisLift.mul_z, HeisLift.mul_l, HeisLift.inv_z,
      HeisLift.inv_a, HeisLift.inv_l, HeisLift.mul_g, HeisLift.inv_g, mul_smul,
      hp, hpi, hri, smul_elemDual_of_trivial hpi, smul_elemDual_of_trivial hri]
    simp only [ElemDual.add_apply, ElemDual.neg_apply, map_neg]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, zero_add, add_zero]
    rw [sub_eq_add_neg, CharTwo.neg_eq]
  · simp only [HeisLift.mul_g, HeisLift.inv_g]
    rfl

/-- **The conjugate of a trivial-base lift by an arbitrary lift**:
`p^s = (s⁻¹·a_p, s⁻¹·λ_p, z_p + λ_s(a_p) + λ_p(a_s); p.g^{s.g})`.  Both `s`-offsets
survive only through the symmetric mixed pairing; the base operator `s.g⁻¹` twists the
jet — the second-order source of the `S`-operators in the boundary block. -/
theorem heisConjR_of_trivial (p s : HeisLift A C) (hp : ∀ a : A, p.g • a = a) :
    conjR p s = ⟨s.g⁻¹ • p.a, s.g⁻¹ • p.l, p.z + s.l p.a + p.l s.a, conjR p.g s.g⟩ := by
  rw [conjR]
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · simp only [HeisLift.mul_a, HeisLift.inv_a, HeisLift.mul_g, HeisLift.inv_g, mul_smul, hp]
    abel
  · simp only [HeisLift.mul_l, HeisLift.inv_l, HeisLift.mul_g, HeisLift.inv_g, mul_smul,
      smul_elemDual_of_trivial hp]
    abel
  · simp only [HeisLift.mul_z, HeisLift.mul_l, HeisLift.inv_z,
      HeisLift.inv_l, HeisLift.mul_g, HeisLift.inv_g, mul_smul, hp]
    simp only [ElemDual.add_apply, ElemDual.neg_apply, ElemDual.smul_apply,
      inv_inv, smul_inv_smul]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, zero_add]
    rw [sub_eq_add_neg, CharTwo.neg_eq]
  · simp only [HeisLift.mul_g, HeisLift.inv_g]
    rfl

end HeisToolkit

/-! ### `heisEvalZ` constructor rules

WW3 exports `heisEvalZ_gen/mul/inv`; the remaining constructor rules are the same
definitional facts, recorded here so the factor computations below stay `rw`-driven. -/

section HeisEvalRules

variable {X : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]
variable (μ : X → C) (x : X → A) (y : X → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

theorem heisEvalZ_one : heisEvalZ μ x y E E₂ .one = 1 := rfl

theorem heisEvalZ_conj (u g : PWord X) :
    heisEvalZ μ x y E E₂ (.conj u g)
      = conjR (heisEvalZ μ x y E E₂ u) (heisEvalZ μ x y E E₂ g) := rfl

theorem heisEvalZ_comm (u v : PWord X) :
    heisEvalZ μ x y E E₂ (.comm u v)
      = commR (heisEvalZ μ x y E E₂ u) (heisEvalZ μ x y E E₂ v) := rfl

theorem heisEvalZ_zpow (u : PWord X) (k : ℤ) :
    heisEvalZ μ x y E E₂ (.zpow u k) = heisEvalZ μ x y E E₂ u ^ k := rfl

theorem heisEvalZ_profPow (u : PWord X) (γ : Zhat) :
    heisEvalZ μ x y E E₂ (.profPow u γ) = heisEvalZ μ x y E E₂ u ^ E γ := rfl

theorem heisEvalZ_prodList (l : List (PWord X)) :
    heisEvalZ μ x y E E₂ (PWord.prodList l) = (l.map (heisEvalZ μ x y E E₂)).prod :=
  PWord.evalZ_prodList _ _ _ l

/-- Products of jet-zero denotations are jet-zero with **additive** central coordinate —
the "⊕" of the block structure, at the list level. -/
theorem heisEvalZ_prodList_jetZero {l : List (PWord X)}
    (hl : ∀ w ∈ l, heisEvalZ μ x y E E₂ w ∈ heisJetZero A C) :
    heisEvalZ μ x y E E₂ (PWord.prodList l) ∈ heisJetZero A C ∧
      (heisEvalZ μ x y E E₂ (PWord.prodList l)).z
        = (l.map fun w => (heisEvalZ μ x y E E₂ w).z).sum := by
  induction l with
  | nil => exact ⟨one_mem _, rfl⟩
  | cons w ws ih =>
      have hw := hl w List.mem_cons_self
      have ihs := ih fun u hu => hl u (List.mem_cons_of_mem _ hu)
      rw [PWord.prodList_cons]
      refine ⟨mul_mem hw ihs.1, ?_⟩
      rw [heisEvalZ_mul, heisJetZero_mul_z hw, ihs.2, List.map_cons, List.sum_cons]

end HeisEvalRules

/-! ## The second-order (Stokes) forms of the compact-`N` word

The five factors of `R_{N,α,0}` evaluated in the Heisenberg lift at a simple-tame-module
marking — the standing setting of WN0-b's first-order rows, one degree up.  The class
hypotheses are the unramified ones (`hwild` + `hτ`); the ramified second order is not a
certificate item (the freeze's plus form lives on the unramified/split side, where the
one-op normal form leaves the wild generator paired). -/

section StokesRows

variable {h α : ℕ} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]
  (t : Marking (2 + 2 * h) C) (x : Generator (2 + 2 * h) → A)
  (y : Generator (2 + 2 * h) → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **Factor 1** — `x₀^{2+2^α}` is jet-zero central with value the diagonal `y₀(a₀)`:
the binomial `C(2+2^α, 2)` is odd for `α ≥ 2` (`choose_two_add_two_pow_odd`) while the
even exponent kills both first-order jets.  The `q(c₀)`-production mechanism. -/
theorem heisF_leadingPow (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) (hα : 2 ≤ α) :
    heisEvalZ ⇑t x y E E₂ (.zpow (.gen (coreLetter h 0)) (2 + 2 ^ α))
      = ⟨0, 0, y (coreLetter h 0) (x (coreLetter h 0)),
          t (coreLetter h 0) ^ (2 + 2 ^ α : ℕ)⟩ := by
  have h0 := mem_trivAct.mp (trivAct_coreLetter t hwild 0)
  rw [heisEvalZ_zpow, heisEvalZ_gen,
    show ((2 : ℤ) + 2 ^ α) = ((2 + 2 ^ α : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
    heisPow_of_trivial _ h0]
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · exact even_nsmul_eq_zero hA₂ (even_two_add_two_pow (by omega)) _
  · exact even_nsmul_eq_zero ElemDual.add_self_eq_zero (even_two_add_two_pow (by omega)) _
  · show (2 + 2 ^ α) • (0 : ZMod 2) + ((2 + 2 ^ α).choose 2) • _ = _
    rw [smul_zero, zero_add, nsmul_zmod2_odd (choose_two_add_two_pow_odd hα)]
  · rfl

/-- **Factor 2** — `[x₀,x₁]` is jet-zero central with value the hyperbolic cross
`y₀(a₁) + y₁(a₀)` — the `b_q(c₀,c₁)`-production mechanism. -/
theorem heisF_leadingComm (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) :
    heisEvalZ ⇑t x y E E₂ (.comm (.gen (coreLetter h 0)) (.gen (coreLetter h 1)))
      = ⟨0, 0, y (coreLetter h 0) (x (coreLetter h 1)) + y (coreLetter h 1) (x (coreLetter h 0)),
          commR (t (coreLetter h 0)) (t (coreLetter h 1))⟩ := by
  rw [heisEvalZ_comm, heisEvalZ_gen, heisEvalZ_gen,
    heisCommR_of_trivial _ _ (mem_trivAct.mp (trivAct_coreLetter t hwild 0))
      (mem_trivAct.mp (trivAct_coreLetter t hwild 1))]

/-- **Factor 3** — `(x₂^σ)⁻¹` carries the `S⁻¹`-twisted jet `(−S⁻¹a₂, −S⁻¹y₂)` and central
value `y_σ(a₂) + y₂(a_σ) + y₂(a₂)`; the diagonal `y₂(a₂)` is the `β(u⁻¹)`-rule's Bockstein
term (`heisEvalZ_inv_z`), the seam the κ⁰-normalization pins on the Hessian side. -/
theorem heisF_invConjX2 (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) :
    heisEvalZ ⇑t x y E E₂ (.inv (.conj (.gen (coreLetter h 2)) (.gen .sigma)))
      = ⟨-(t.σ⁻¹ • x (coreLetter h 2)), -(t.σ⁻¹ • y (coreLetter h 2)),
          y .sigma (x (coreLetter h 2)) + y (coreLetter h 2) (x .sigma)
            + y (coreLetter h 2) (x (coreLetter h 2)),
          (conjR (t (coreLetter h 2)) t.σ)⁻¹⟩ := by
  have h2 := mem_trivAct.mp (trivAct_coreLetter t hwild 2)
  rw [heisEvalZ_inv, heisEvalZ_conj, heisEvalZ_gen, heisEvalZ_gen,
    heisConjR_of_trivial _ _ h2]
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · show -((conjR (t (coreLetter h 2)) t.σ)⁻¹ • t.σ⁻¹ • x (coreLetter h 2)) = _
    rw [mem_trivAct.mp (inv_mem (trivAct_conjR (trivAct_coreLetter t hwild 2) t.σ))]
  · show -((conjR (t (coreLetter h 2)) t.σ)⁻¹ • t.σ⁻¹ • y (coreLetter h 2)) = _
    rw [smul_elemDual_of_trivial
      (mem_trivAct.mp (inv_mem (trivAct_conjR (trivAct_coreLetter t hwild 2) t.σ)))]
  · show (0 : ZMod 2) + y .sigma (x (coreLetter h 2)) + y (coreLetter h 2) (x .sigma)
        + (t.σ⁻¹ • y (coreLetter h 2)) (t.σ⁻¹ • x (coreLetter h 2)) = _
    rw [ElemDual.smul_apply, inv_inv, smul_inv_smul, zero_add]
  · rfl

/-- The `δ₂`-block's inner word `x₂τ` (in the certificate's `prodList` spelling). -/
theorem heisF_deltaInner (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) :
    heisEvalZ ⇑t x y E E₂ (PWord.prodList [.gen (coreLetter h 2), .gen .tau])
      = ⟨x (coreLetter h 2) + x .tau, y (coreLetter h 2) + y .tau,
          y (coreLetter h 2) (x .tau), t (coreLetter h 2) * t.τ⟩ := by
  have h2 := mem_trivAct.mp (trivAct_coreLetter t hwild 2)
  rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, heisEvalZ_mul,
    heisEvalZ_mul, heisEvalZ_gen, heisEvalZ_gen, heisEvalZ_one, mul_one]
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · show x (coreLetter h 2) + t (coreLetter h 2) • x .tau = _
    rw [h2]
  · show y (coreLetter h 2) + t (coreLetter h 2) • y .tau = _
    rw [smul_elemDual_of_trivial h2]
  · show (0 : ZMod 2) + 0 + y (coreLetter h 2) (t (coreLetter h 2) • x .tau) = _
    rw [h2, zero_add, zero_add]
  · rfl

/-- **Factor 4** — `(x₂τ)^{ω₂}` at a resolver value `E ω₂ = e` (unramified class): the
`e`-th power of the inner word, by the trivial-base power law.  The `C(e,2)`-term is the
resolver-class sensitivity: it dies exactly on `e ≡ 0, 1 (mod 4)` — ticket S1.T's
"the lift level is 4, not 2", at the `ZMod 2`-centre Heisenberg level. -/
theorem heisF_deltaBlock (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hτ : ∀ v : A, t.τ • v = v) {e : ℕ} (hE : E omega2 = (e : ℤ)) :
    heisEvalZ ⇑t x y E E₂
        (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau]))
      = ⟨e • (x (coreLetter h 2) + x .tau), e • (y (coreLetter h 2) + y .tau),
          e • y (coreLetter h 2) (x .tau)
            + (e.choose 2) • ((y (coreLetter h 2) + y .tau) (x (coreLetter h 2) + x .tau)),
          (t (coreLetter h 2) * t.τ) ^ e⟩ := by
  have h2 := mem_trivAct.mp (trivAct_coreLetter t hwild 2)
  have hbase : ∀ v : A, (t (coreLetter h 2) * t.τ) • v = v := fun v => by
    rw [mul_smul, hτ, h2]
  rw [PWord.omega2Pow, heisEvalZ_profPow, heisF_deltaInner t x y E E₂ hwild, hE,
    zpow_natCast, heisPow_of_trivial _ hbase]

/-- **Factor 5, membership** — the handle block is jet-zero at every handle count. -/
theorem heisF_handlesW_mem (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) :
    heisEvalZ ⇑t x y E E₂ (handlesW h) ∈ heisJetZero A C := by
  rw [handlesW]
  refine (heisEvalZ_prodList_jetZero ⇑t x y E E₂ ?_).1
  intro w hw
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw
  rw [heisEvalZ_comm, heisEvalZ_gen, heisEvalZ_gen,
    heisCommR_of_trivial _ _ (mem_trivAct.mp (trivAct_handleU t hwild j))
      (mem_trivAct.mp (trivAct_handleV t hwild j))]
  exact ⟨rfl, rfl⟩

/-- **Factor 5, value** — `H_h` contributes exactly the `h` **identity-operator hyperbolic
planes** `Σ_j (y_{u_j}(a_{v_j}) + y_{v_j}(a_{u_j}))`: no `S`- or `T`-operator enters, at
any handle count.  This is the "⊕ h hyperbolic planes" half of the S2.1/S2.6 block
structure. -/
theorem heisF_handlesW_z (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) :
    (heisEvalZ ⇑t x y E E₂ (handlesW h)).z
      = ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  rw [handlesW]
  have hmem : ∀ w ∈ (List.finRange h).map fun j =>
      (PWord.comm (.gen (handleU j)) (.gen (handleV j)) : PWord (Generator (2 + 2 * h))),
      heisEvalZ ⇑t x y E E₂ w ∈ heisJetZero A C := by
    intro w hw
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw
    rw [heisEvalZ_comm, heisEvalZ_gen, heisEvalZ_gen,
      heisCommR_of_trivial _ _ (mem_trivAct.mp (trivAct_handleU t hwild j))
        (mem_trivAct.mp (trivAct_handleV t hwild j))]
    exact ⟨rfl, rfl⟩
  rw [(heisEvalZ_prodList_jetZero ⇑t x y E E₂ hmem).2, List.map_map, Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  show (heisEvalZ ⇑t x y E E₂ (.comm (.gen (handleU j)) (.gen (handleV j)))).z = _
  rw [heisEvalZ_comm, heisEvalZ_gen, heisEvalZ_gen,
    heisCommR_of_trivial _ _ (mem_trivAct.mp (trivAct_handleU t hwild j))
      (mem_trivAct.mp (trivAct_handleV t hwild j))]

/-- **The compact-`N` second-order (Stokes) row, unramified class, exact in the
resolver**: the central coordinate of the word's `heisEvalZ`-denotation at any marking
whose wild letters and `τ` act trivially, with `E ω₂ = e`.

Block reading: `x₀`-diagonal ⊕ `(x₀,x₁)`-cross ⊕ boundary block on `(σ,τ,x₂)` (with the
`e`- and `C(e,2)`-sensitivities displayed) ⊕ the `h` identity-operator hyperbolic planes.
The Sage-side measurement of this decomposition is certificate battery `regressed-F-G`
(S2.1/S2.6); the clean certificate form at the honest resolver class is
`heisZ_nCompact_res_one`. -/
theorem heisZ_nCompact_unram (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) (hτ : ∀ v : A, t.τ • v = v)
    (hα : 2 ≤ α) {e : ℕ} (hE : E omega2 = (e : ℤ)) :
    (heisEvalZ ⇑t x y E E₂ (nCompactW α h)).z
      = y (coreLetter h 0) (x (coreLetter h 0))
        + (y (coreLetter h 0) (x (coreLetter h 1)) + y (coreLetter h 1) (x (coreLetter h 0)))
        + (y .sigma (x (coreLetter h 2)) + y (coreLetter h 2) (x .sigma)
            + y (coreLetter h 2) (x (coreLetter h 2)))
        + (e • y (coreLetter h 2) (x .tau)
            + (e.choose 2) • ((y (coreLetter h 2) + y .tau) (x (coreLetter h 2) + x .tau))
            + e • y (coreLetter h 2) (t.σ • (x (coreLetter h 2) + x .tau)))
        + ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  have h5mem := heisF_handlesW_mem t x y E E₂ hwild
  have h5z := heisF_handlesW_z t x y E E₂ hwild
  rw [nCompactW, heisEvalZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  set P1 := heisEvalZ ⇑t x y E E₂
    (.zpow (.gen (coreLetter h 0)) (2 + 2 ^ α)) with hP1
  set P2 := heisEvalZ ⇑t x y E E₂
    (.comm (.gen (coreLetter h 0)) (.gen (coreLetter h 1))) with hP2
  set P3 := heisEvalZ ⇑t x y E E₂
    (.inv (.conj (.gen (coreLetter h 2)) (.gen .sigma))) with hP3
  set P4 := heisEvalZ ⇑t x y E E₂
    (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau])) with hP4
  set P5 := heisEvalZ ⇑t x y E E₂ (handlesW h) with hP5
  have e1 := heisF_leadingPow t x y E E₂ hA₂ hwild hα
  have e2 := heisF_leadingComm t x y E E₂ hwild
  have e3 := heisF_invConjX2 t x y E E₂ hwild
  have e4 := heisF_deltaBlock t x y E E₂ hwild hτ hE
  have h1jz : P1 ∈ heisJetZero A C := by rw [hP1, e1]; exact ⟨rfl, rfl⟩
  have h2jz : P2 ∈ heisJetZero A C := by rw [hP2, e2]; exact ⟨rfl, rfl⟩
  have h45z : (P4 * P5).z = P4.z + P5.z := heisMul_z_of_a_eq_zero _ _ h5mem.1
  have h45a : (P4 * P5).a = P4.a := by rw [HeisLift.mul_a, h5mem.1, smul_zero, add_zero]
  have h3g : ∀ v : A, P3.g • v = v := by
    rw [hP3, e3]
    exact fun v =>
      mem_trivAct.mp (inv_mem (trivAct_conjR (trivAct_coreLetter t hwild 2) t.σ)) v
  have h345 : (P3 * (P4 * P5)).z = P3.z + (P4.z + P5.z) + P3.l P4.a := by
    rw [HeisLift.mul_z, h45z, h45a, h3g]
  rw [heisJetZero_mul_z h1jz, heisJetZero_mul_z h2jz, h345, hP1, hP2, hP3, hP4, e1, e2, e3,
    e4, h5z]
  dsimp only
  rw [map_nsmul, ElemDual.neg_apply, ElemDual.smul_apply, inv_inv, CharTwo.neg_eq, map_add]
  simp only [smul_add, map_add]
  abel

/-- **The certificate form at the honest resolver class** `e ≡ 1 (mod 4)` (the class the
genuine `ω₂` inhabits on every finite `2`-group target): the boundary block collapses to
`y_σ(a₂) + y₂(a_σ + (1+S)(a₂ + a_τ))` — the second-order shadow of WN0-b's `1 − S⁻¹`
unramified Fox block (`1 + S = (1 − S⁻¹)·S` in characteristic 2). -/
theorem heisZ_nCompact_res_one (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) (hτ : ∀ v : A, t.τ • v = v)
    (hα : 2 ≤ α) {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    (heisEvalZ ⇑t x y E E₂ (nCompactW α h)).z
      = y (coreLetter h 0) (x (coreLetter h 0))
        + (y (coreLetter h 0) (x (coreLetter h 1)) + y (coreLetter h 1) (x (coreLetter h 0)))
        + y .sigma (x (coreLetter h 2))
        + y (coreLetter h 2)
            (x .sigma + ((x (coreLetter h 2) + x .tau)
              + t.σ • (x (coreLetter h 2) + x .tau)))
        + ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  rw [heisZ_nCompact_unram t x y E E₂ hA₂ hwild hτ hα hE,
    nsmul_zmod2_odd (odd_of_mod_four_eq_one he), nsmul_zmod2_odd (odd_of_mod_four_eq_one he),
    nsmul_zmod2_even (choose_two_even_of_mod_four he)]
  simp only [map_add]
  abel

/-- **The scalar (split) collapse**: with `σ` also acting trivially the `(1+S)`-block
dies and the wild word's second order is the two diagonals plus the two crosses — the
wild half of the scalar Gram matrix below. -/
theorem heisZ_nCompact_scalar (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) (hτ : ∀ v : A, t.τ • v = v)
    (hσ : ∀ v : A, t.σ • v = v) (hα : 2 ≤ α) {e : ℕ} (hE : E omega2 = (e : ℤ))
    (he : e % 4 = 1) :
    (heisEvalZ ⇑t x y E E₂ (nCompactW α h)).z
      = y (coreLetter h 0) (x (coreLetter h 0))
        + (y (coreLetter h 0) (x (coreLetter h 1)) + y (coreLetter h 1) (x (coreLetter h 0)))
        + y .sigma (x (coreLetter h 2)) + y (coreLetter h 2) (x .sigma)
        + ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  rw [heisZ_nCompact_res_one t x y E E₂ hA₂ hwild hτ hα hE he]
  have hzero : (x (coreLetter h 2) + x .tau) + t.σ • (x (coreLetter h 2) + x .tau) = 0 := by
    rw [hσ (x (coreLetter h 2) + x .tau)]
    exact hA₂ _
  rw [hzero, add_zero]

/-- **The rank-3 wild core**: at offsets supported on the wild letters, the second-order
row is the `(x₀,x₁)` unimodular plane plus the `x₂`-atom `y₂((1+S)a₂)`.  The three core
atoms of the S2.1 decomposition; the third is invertible exactly on `V^S = 0`
(`isUnit_onePlusSEnd_iff`), matching WN0-b's first-order dichotomy. -/
theorem heisZ_nCompact_wild_block (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) (hτ : ∀ v : A, t.τ • v = v)
    (hα : 2 ≤ α) {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1)
    (hxσ : x .sigma = 0) (hxτ : x .tau = 0) (hyσ : y .sigma = 0) :
    (heisEvalZ ⇑t x y E E₂ (nCompactW α h)).z
      = y (coreLetter h 0) (x (coreLetter h 0))
        + (y (coreLetter h 0) (x (coreLetter h 1)) + y (coreLetter h 1) (x (coreLetter h 0)))
        + y (coreLetter h 2) (x (coreLetter h 2) + t.σ • x (coreLetter h 2))
        + ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  rw [heisZ_nCompact_res_one t x y E E₂ hA₂ hwild hτ hα hE he, hxσ, hxτ, hyσ]
  simp only [ElemDual.zero_apply, add_zero, zero_add]

end StokesRows

/-! ### The `1 + S` atom and WN0-b's block

`1 + S = (1 − S⁻¹)·S` over an elementary module, so the second-order `x₂`-atom is
invertible exactly when WN0-b's first-order `1 − S⁻¹` block is: on `V^S = 0`, i.e. on
every nontrivial simple unramified module and no scalar one. -/

section OnePlusS

variable {n : ℕ} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- The second-order `x₂`-atom `1 + S` as an operator. -/
noncomputable def onePlusSEnd (t : Marking n C) : AddMonoid.End A :=
  1 + DistribMulAction.toAddMonoidEnd C A t.σ

@[simp] theorem onePlusSEnd_apply (t : Marking n C) (v : A) :
    onePlusSEnd t v = v + t.σ • v := rfl

/-- `1 + S = (1 − S⁻¹) ∘ S` over an elementary module. -/
theorem onePlusSEnd_eq_comp (t : Marking n C) (hA₂ : ∀ a : A, a + a = 0) :
    onePlusSEnd t (A := A) = oneSubSInvEnd t * DistribMulAction.toAddMonoidEnd C A t.σ := by
  refine DFunLike.ext _ _ fun v => ?_
  show v + t.σ • v = t.σ • v - t.σ⁻¹ • t.σ • v
  rw [inv_smul_smul, sub_eq_add_neg, neg_eq_self hA₂, add_comm]

/-- **The rank-3 completion of the wild core**: the `x₂`-atom `1 + S` is invertible iff
`V^S = 0` — by composition with WN0-b's `isUnit_oneSubSInvEnd_iff`.  On a nontrivial
simple unramified module all three core atoms are invertible; on a scalar module the
third dies, exactly as at first order. -/
theorem isUnit_onePlusSEnd_iff [Finite A] (t : Marking n C) (hA₂ : ∀ a : A, a + a = 0) :
    IsUnit (onePlusSEnd t (A := A)) ↔ ∀ v : A, t.σ • v = v → v = 0 := by
  have hS : IsUnit (DistribMulAction.toAddMonoidEnd C A t.σ) := by
    refine isUnit_iff_exists.mpr ⟨DistribMulAction.toAddMonoidEnd C A t.σ⁻¹, ?_, ?_⟩
    · exact DFunLike.ext _ _ fun v => smul_inv_smul _ _
    · exact DFunLike.ext _ _ fun v => inv_smul_smul _ _
  have hSinv : IsUnit (DistribMulAction.toAddMonoidEnd C A t.σ⁻¹) := by
    refine isUnit_iff_exists.mpr ⟨DistribMulAction.toAddMonoidEnd C A t.σ, ?_, ?_⟩
    · exact DFunLike.ext _ _ fun v => inv_smul_smul _ _
    · exact DFunLike.ext _ _ fun v => smul_inv_smul _ _
  rw [← isUnit_oneSubSInvEnd_iff t, onePlusSEnd_eq_comp t hA₂]
  constructor
  · intro hu
    have h2 : oneSubSInvEnd t (V := A)
        = oneSubSInvEnd t * DistribMulAction.toAddMonoidEnd C A t.σ
            * DistribMulAction.toAddMonoidEnd C A t.σ⁻¹ := by
      refine DFunLike.ext _ _ fun v => ?_
      show oneSubSInvEnd t v = oneSubSInvEnd t (t.σ • t.σ⁻¹ • v)
      rw [smul_inv_smul]
    rw [h2]
    exact hu.mul hSinv
  · intro hu
    exact hu.mul hS

end OnePlusS

/-! ### The tame relator's second-order row -/

section TameStokes

variable {n q : ℕ} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]
  (t : Marking n C) (x : Generator n → A) (y : Generator n → ElemDual A)
  (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **The tame row at second order, split/unramified class** (`T = 1` on `A`, `q` even):
the `(σ,τ)` hyperbolic cross plus the `τ`-diagonal with coefficient `C(q,2)` — odd at
`q ≡ 2 (mod 4)`, in particular at the `√−2` row's `q = 2`.  The τ-Bockstein diagonal of
the scalar Gram. -/
theorem heisZ_tameRelW_unram (hA₂ : ∀ a : A, a + a = 0) (hτ : ∀ v : A, t.τ • v = v)
    (hq : Even q) :
    (heisEvalZ ⇑t x y E E₂ (tameRelW n q)).z
      = y .sigma (x .tau) + y .tau (x .sigma) + (q.choose 2) • y .tau (x .tau) := by
  have hτm : ∀ a : A, t Generator.tau • a = a := hτ
  have e1 : heisEvalZ ⇑t x y E E₂ (.conj (.gen .tau) (.gen .sigma))
      = ⟨t.σ⁻¹ • x .tau, t.σ⁻¹ • y .tau,
          y .sigma (x .tau) + y .tau (x .sigma), conjR (t .tau) t.σ⟩ := by
    rw [heisEvalZ_conj, heisEvalZ_gen, heisEvalZ_gen, heisConjR_of_trivial _ _ hτm]
    refine HeisLift.ext rfl rfl ?_ rfl
    show (0 : ZMod 2) + y .sigma (x .tau) + y .tau (x .sigma) = _
    rw [zero_add]
  have e2 : heisEvalZ ⇑t x y E E₂ (.inv (.zpow (.gen .tau) (q : ℤ)))
      = ⟨0, 0, (q.choose 2) • y .tau (x .tau), (t .tau ^ q)⁻¹⟩ := by
    have hqa : q • x .tau = 0 := even_nsmul_eq_zero hA₂ hq _
    have hql : q • y .tau = (0 : ElemDual A) :=
      even_nsmul_eq_zero ElemDual.add_self_eq_zero hq _
    rw [heisEvalZ_inv, heisEvalZ_zpow, heisEvalZ_gen, zpow_natCast,
      heisPow_of_trivial _ hτm]
    refine HeisLift.ext ?_ ?_ ?_ rfl
    · show -((t .tau ^ q)⁻¹ • q • x .tau) = 0
      rw [hqa, smul_zero, neg_zero]
    · show -((t .tau ^ q)⁻¹ • q • y .tau) = 0
      rw [hql, smul_zero, neg_zero]
    · show q • (0 : ZMod 2) + (q.choose 2) • y .tau (x .tau) + (q • y .tau) (q • x .tau)
        = (q.choose 2) • y .tau (x .tau)
      rw [smul_zero, zero_add, hql, ElemDual.zero_apply, add_zero]
  rw [tameRelW, heisEvalZ_mul, e1, e2, HeisLift.mul_z]
  show y .sigma (x .tau) + y .tau (x .sigma) + (q.choose 2) • y .tau (x .tau)
      + (t.σ⁻¹ • y .tau) (conjR (t .tau) t.σ • (0 : A)) = _
  rw [smul_zero, map_zero, add_zero]

end TameStokes

/-! ## The resolved relator family and the endpoint condition

The two-relator family of the presentation `⟨σ, τ, x₀, …, x_{2h+2} ∣ τ^σ(τ^q)⁻¹, R_{N,α,0}⟩`
resolved at the constant integer representative `e` of `ω₂` — WW2's Jacobian row order
(tame first, wild second).  `nCompact_isStokesEndpoint` proves display (40)'s endpoint
condition for **all** `α ≥ 1, h` and every even `q`, odd `e`: the traced mod-2 exponent
vector vanishes because every per-letter coefficient — `1−q+e` on `τ`, `2+2^α` on `x₀`,
`e−1` on `x₂` — is even; no case analysis on the letter is needed. -/

section Family

/-- Collapse of `conjR` in a commutative group. -/
theorem conjR_eq_self_of_comm {H : Type*} [CommGroup H] (x g : H) : conjR x g = x := by
  rw [conjR, mul_comm g⁻¹ x, mul_assoc, inv_mul_cancel, mul_one]

/-- `commR` maps to `commR` under any group hom. -/
theorem map_commR' {G H : Type*} [Group G] [Group H] (f : G →* H) (a b : G) :
    f (commR a b) = commR (f a) (f b) := by
  rw [commR, commR, map_mul, map_mul, map_mul, map_inv, map_inv]

/-- Commutators die under any hom into a commutative group. -/
theorem monoidHom_commR_eq_one {G H : Type*} [Group G] [CommGroup H] (f : G →* H)
    (a b : G) : f (commR a b) = 1 := by
  rw [map_commR', commR_eq_one_iff]
  exact Commute.all _ _

variable {α h q e : ℕ}

/-- **The resolved compact-`N` relator family**: the tame relator and the frozen branch
word, `heisToFree`-resolved at the constant representative `e` — the `ρ = Fin 2` family
the WW3 machinery consumes, in the Jacobian row order of WN0-b's `foxJacobian`. -/
noncomputable def nCompactFam (α h q e : ℕ) : Fin 2 → FreeGroup (Generator (2 + 2 * h)) :=
  ![heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 + 2 * h) q),
    heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (nCompactW α h)]

@[simp] theorem nCompactFam_zero :
    nCompactFam α h q e 0
      = heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 + 2 * h) q) := rfl

@[simp] theorem nCompactFam_one :
    nCompactFam α h q e 1
      = heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (nCompactW α h) := rfl

/-- `heisEps` on a letter is the indicator. -/
theorem heisEps_of {ι : Type*} [DecidableEq ι] (i j : ι) :
    heisEps i (FreeGroup.of j) = Multiplicative.ofAdd (if j = i then (1 : ZMod 2) else 0) := by
  rw [heisEps]
  exact FreeGroup.lift_apply_of

/-- An even natural `ℤ`-scalar kills every `ZMod 2` value. -/
theorem zsmul_natCast_zmod2_even {n : ℕ} (hn : Even n) (z : ZMod 2) : (n : ℤ) • z = 0 := by
  rw [zsmul_eq_mul, Int.cast_natCast, natCast_zmod2_even hn, zero_mul]

/-- An odd natural `ℤ`-scalar is the identity on `ZMod 2` values. -/
theorem zsmul_natCast_zmod2_odd {n : ℕ} (hn : Odd n) (z : ZMod 2) : (n : ℤ) • z = z := by
  rw [zsmul_eq_mul, Int.cast_natCast, natCast_zmod2_odd hn, one_mul]

/-- The handle block's resolved word has trivial mod-2 exponent vector (commutators). -/
theorem heisEps_handlesW (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (i : Generator (2 + 2 * h)) :
    heisEps i (PWord.evalZ FreeGroup.of E E₂ (handlesW h)) = 1 := by
  rw [handlesW, PWord.evalZ_prodList, map_list_prod]
  refine List.prod_eq_one ?_
  intro m hm
  simp only [List.map_map, List.mem_map] at hm
  obtain ⟨j, -, rfl⟩ := hm
  show heisEps i (PWord.evalZ FreeGroup.of _ _
    (.comm (.gen (handleU j)) (.gen (handleV j)))) = 1
  rw [PWord.evalZ_comm]
  exact monoidHom_commR_eq_one _ _ _

/-- **The endpoint condition holds at every compact-`N` instance** (`α ≥ 1`, any `h`,
`q` even, `e` odd): the traced per-letter exponents are `1−q+e` (τ), `2+2^α` (x₀),
`e−1` (x₂), `0` elsewhere — all even.  This is what WW3's chain conditions consume;
the per-word `decide` route of `stress_endpoint_gammaA` is subsumed. -/
theorem nCompact_isStokesEndpoint (hα : 1 ≤ α) (hq : Even q) (he : Odd e) :
    IsStokesEndpoint (nCompactFam α h q e) := by
  intro i
  rw [Fin.sum_univ_two, nCompactFam_zero, nCompactFam_one]
  have htame : heisEps i (heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ))
      (tameRelW (2 + 2 * h) q))
      = heisEps i (FreeGroup.of Generator.tau)
        * (heisEps i (FreeGroup.of Generator.tau) ^ (q : ℤ))⁻¹ := by
    rw [tameRelW, heisToFree, PWord.evalZ_mul, PWord.evalZ_conj, PWord.evalZ_inv,
      PWord.evalZ_zpow, PWord.evalZ_gen, PWord.evalZ_gen, map_mul, map_conjR,
      conjR_eq_self_of_comm, map_inv, map_zpow]
  have hwild : heisEps i (heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (nCompactW α h))
      = heisEps i (FreeGroup.of (coreLetter h 0)) ^ ((2 : ℤ) + 2 ^ α)
        * ((heisEps i (FreeGroup.of (coreLetter h 2)))⁻¹
            * (heisEps i (FreeGroup.of (coreLetter h 2))
                * heisEps i (FreeGroup.of Generator.tau)) ^ (e : ℤ)) := by
    rw [nCompactW, heisToFree, PWord.evalZ_prodList]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [map_mul, map_mul, map_mul, map_mul, PWord.evalZ_zpow, PWord.evalZ_gen, map_zpow,
      PWord.evalZ_comm, monoidHom_commR_eq_one, PWord.evalZ_inv, PWord.evalZ_conj,
      PWord.evalZ_gen, PWord.evalZ_gen, map_inv, map_conjR, conjR_eq_self_of_comm,
      PWord.omega2Pow, PWord.evalZ_profPow, map_zpow, PWord.prodList_cons,
      PWord.prodList_cons, PWord.prodList_nil, PWord.evalZ_mul, PWord.evalZ_mul,
      PWord.evalZ_gen, PWord.evalZ_gen, PWord.evalZ_one, mul_one, map_mul, one_mul,
      heisEps_handlesW, mul_one]
  rw [htame, hwild]
  simp only [heisEps_of, toAdd_mul, toAdd_inv, toAdd_zpow, toAdd_ofAdd]
  rw [zsmul_natCast_zmod2_even hq, zsmul_natCast_zmod2_odd he,
    show ((2 : ℤ) + 2 ^ α) • (if coreLetter h 0 = i then (1 : ZMod 2) else 0) = 0 by
      rw [show ((2 : ℤ) + 2 ^ α) = ((2 + 2 ^ α : ℕ) : ℤ) by push_cast; ring]
      exact zsmul_natCast_zmod2_even (even_two_add_two_pow hα) _]
  rw [CharTwo.neg_eq, CharTwo.neg_eq]
  abel_nf
  simp [CharTwo.two_eq_zero]

/-- The `√−2` instance pin: `(α, h, q, e) = (2, 0, 2, 3)` satisfies the endpoint
condition — the odd representative `e = 3` matching the frozen `Γ_A` stress pin. -/
theorem sqrtNegTwo_isStokesEndpoint : IsStokesEndpoint (nCompactFam 2 0 2 3) :=
  nCompact_isStokesEndpoint (by norm_num) (by decide) (by decide)

end Family

/-! ## The Stokes duality payload

WW3's packet-Lem-5.1 engine, instantiated at the compact-`N` family.  The relator
hypotheses are Gate-level `evalZ = 1` facts, converted through
`lift_heisToFree_eq_one_iff`; the endpoint condition is discharged by the theorem above;
per-simple-module duality remains the hypothesis slot it is in the frozen `ℚ₂` chain
(gate-F / AS-lane discharge).  Downstream, WW3b's `stokesChi1_bijective` turns the
conclusion into the perfect pairing on `H¹` with no further row-specific input. -/

section Duality

universe u

variable {C : Type*} [Group C]

theorem nCompact_stokesDuality {α h q e : ℕ} [Finite C] (t : Marking (2 + 2 * h) C)
    (hα : 1 ≤ α) (hq : Even q) (he : Odd e)
    (hrt : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 + 2 * h) q) = 1)
    (hrw : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (nCompactW α h) = 1)
    (hsimp : ∀ (V : Type u) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V →
        StokesDuality ⇑t (nCompactFam α h q e) V)
    (A : Type u) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) : StokesDuality ⇑t (nCompactFam α h q e) A := by
  refine stokesDuality_of_simple ⇑t (nCompactFam α h q e) ?_
    (nCompact_isStokesEndpoint hα hq he) hsimp A hA₂
  intro k
  fin_cases k
  · exact (lift_heisToFree_eq_one_iff ⇑t _ _ _).mpr hrt
  · exact (lift_heisToFree_eq_one_iff ⇑t _ _ _).mpr hrw

/-- **The traced Stokes pairing of the family** is the sum of the two second-order
values computed above — the bridge between `heisEta1`/`stokesGram` entries and the
per-word closed forms `heisZ_tameRelW_unram`/`heisZ_nCompact_unram`. -/
theorem heisEta1_nCompactFam_apply {α h q e : ℕ} {A : Type*} [AddCommGroup A]
    [DistribMulAction C A] (t : Marking (2 + 2 * h) C) (x : Generator (2 + 2 * h) → A)
    (y : Generator (2 + 2 * h) → ElemDual A) :
    heisEta1 ⇑t (nCompactFam α h q e) x y
      = (heisEvalZ ⇑t x y (fun _ => (e : ℤ)) (fun _ => (e : ℤ))
          (tameRelW (2 + 2 * h) q)).z
        + (heisEvalZ ⇑t x y (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (nCompactW α h)).z := by
  rw [heisEta1_apply, Fin.sum_univ_two, nCompactFam_zero, nCompactFam_one,
    ← heisEvalZ_eq_lift, ← heisEvalZ_eq_lift]

end Duality

/-! ## The scalar certificate: the `√−2` Gram matrices, by kernel `decide`

The cup–Bockstein comparison matrix (`stokesGram`) of the `√−2` family on the scalar
module `A = 𝔽₂` (trivial action — the split class of WN0-b's rows), at the standard
letter basis in the packet column order `σ, τ, x₀, x₁, x₂`; rows index the primal basis
vector, columns the dual one.  This is the `GQ2/Roe/TrivialSelfDual.lean` `scalarGramR`
comparison shape; the field-side (Hilbert-symbol) column of the comparison is AS2's.

Two pins, differing **only** in the resolver class of `ω₂`:

* `e = 1` — the honest class for a 2-group target (`GQ2.omega2Exp` of a 2-power is `1`,
  and the evaluation target here is the 16-element Heisenberg group of exponent 4, so
  honest `ω₂`-evaluation is `evalNat` at an exponent `≡ 1 (mod 4)`).  Diagonal (Bockstein)
  entries at `τ` (tame, `C(2,2)` odd) and `x₀` (wild, `C(6,2) = 15` odd); cup blocks
  `(x₀,x₁)`, `(σ,τ)`, `(σ,x₂)`.  The matrix is symmetric of rank 5 over `𝔽₂`.
* `e = 3` — the other odd class: exactly the `{τ,x₂}²`-block moves (the `C(e,2)`-block of
  `heisZ_nCompact_unram` switches on).  The pair makes ticket S1.T's "the lift level is
  4, not 2" a kernel-checked matrix statement, and is why the certificate form
  `heisZ_nCompact_res_one` pins the class `e ≡ 1 (mod 4)` — `class2.py`'s "the
  polarization alone cannot see the Bockstein diagonal", Gram-side.

Every entry agrees with the closed forms `heisZ_tameRelW_unram` +
`heisZ_nCompact_scalar`/`heisZ_nCompact_unram` (the `decide` recomputes what the
theorems prove; the matrices were derived from the theorems, not vice versa). -/

section ScalarGram

/-- The trivial action for the scalar pins (WW3's `local instance` idiom — not
exported). -/
local instance : DistribMulAction (Multiplicative (ZMod 2)) (ZMod 2) where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- The all-trivial (scalar/split) marking of the `√−2` alphabet. -/
def scalarMark : Marking 2 (Multiplicative (ZMod 2)) := Marking.ofLetters 1 1 ![1, 1, 1]

/-- The packet column order `σ, τ, x₀, x₁, x₂`. -/
def scalarLetter : Fin 5 → Generator 2 := ![.sigma, .tau, .wild 0, .wild 1, .wild 2]

/-- The standard primal basis: a unit offset on one letter. -/
def scalarX (p : Fin 5) : Generator 2 → ZMod 2 :=
  fun g => if g = scalarLetter p then 1 else 0

/-- The standard dual basis: the identity functional on one letter. -/
noncomputable def scalarY (p : Fin 5) : Generator 2 → ElemDual (ZMod 2) :=
  fun g => if g = scalarLetter p then (AddMonoidHom.id (ZMod 2) : ElemDual (ZMod 2)) else 0

/-- **The `√−2` scalar Gram at the honest resolver class** (`e = 1`): Bockstein
diagonals at `τ` and `x₀`, cup blocks `(σ,τ)`, `(σ,x₂)`, `(x₀,x₁)`. -/
theorem sqrtNegTwo_scalarGram :
    stokesGram ⇑scalarMark (nCompactFam 2 0 2 1) scalarX scalarY
      = !![0,1,0,0,1; 1,1,0,0,0; 0,0,1,1,0; 0,0,1,0,0; 1,0,0,0,0] := by
  decide +kernel

/-- **The `e = 3` twin**: the `{τ,x₂}²`-block moves with the resolver class — the
mod-4 (ℤ/4-lift-level) sensitivity, kernel-checked. -/
theorem sqrtNegTwo_scalarGram_three :
    stokesGram ⇑scalarMark (nCompactFam 2 0 2 3) scalarX scalarY
      = !![0,1,0,0,1; 1,0,0,0,1; 0,0,1,1,0; 0,0,1,0,0; 1,1,0,0,1] := by
  decide +kernel

end ScalarGram

/-! ## The Hessian certificate: the word connected to WW4's endpoint

WW4's `compactN_certificate` certifies the frozen endpoint `plusFormD q q` (identity
CoV, `diag := fun v ↦ dat.f v v`).  This section supplies the missing word-side
equation, through WW4's own evaluation route: `hessRelZ` at the κ⁰-cocycle
`kappa0Cocycle dat hdat` on `V ⋊ C`, at the graph-type marking `hessMark` (σ, τ on the
κ-free `C`-line, wild letters on the Heisenberg slice, **`x₂` with no primal letter** —
the ratified boundary convention).  The slice calculus below is the module-side twin of
the NC lane's (`GQ2/Dyadic/NpcJet/Defs.lean` §2, stated against the non-`module`
`WordCoh2.CentExt`); the module rule forces the third copy, per MC-OB's ratified
discipline.

κ⁰-consumption ledger: the endpoint values use `f_diag` (the slice square law, via WW4's
`hessSq_of_fibre`) and `f_polar` (the slice commutator law) — exactly WW4's twist-immune
budget; the *calculus* additionally uses the `q`-blind normalization clauses
`f_zero_left/right`, `m_one`, the derived `m_zero` (`factorSet_m_zero`) and, inside the
commutator law only, `f_cocycle`. -/

section Hessian

open GQ2.SectionSix

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

open GQ2.QuadraticFp2

include hdat in
/-- `m_c(0) = 0` — derived from `m_quad` at `(c, 0, 0)`; the module-side twin of
`GQ2.SectionEight.AffineTLift.IsEquivariantFactorSet.m_zero`. -/
theorem factorSet_m_zero (c : C) : dat.m c 0 = 0 := by
  have h := hdat.m_quad c 0 0
  simp only [add_zero, smul_zero, hdat.f_zero_left] at h
  rw [CharTwo.add_self_eq_zero, zero_add] at h
  exact h

/-- Central inclusions multiply additively, in any `CentExt`. -/
theorem centExt_incl_mul {L : Type} [Group L] {c : WordCoh.TwoCocycle L} (z z' : ZMod 2) :
    WordCoh.CentExt.incl c z * WordCoh.CentExt.incl c z'
      = WordCoh.CentExt.incl c (z + z') := by
  refine WordCoh.CentExt.ext ?_ ?_
  · exact one_mul 1
  · show z + z' + c.κ 1 1 = z + z'
    rw [c.norm, add_zero]

/-- Central inclusions power by `ℕ`-scalars. -/
theorem centExt_incl_pow {L : Type} [Group L] {c : WordCoh.TwoCocycle L} (z : ZMod 2)
    (n : ℕ) : WordCoh.CentExt.incl c z ^ n = WordCoh.CentExt.incl c (n • z) := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; rfl
  | succ n ih => rw [pow_succ, ih, centExt_incl_mul, succ_nsmul]

/-- Products of central inclusions sum the fibres. -/
theorem centExt_incl_list_prod {L : Type} [Group L] {c : WordCoh.TwoCocycle L}
    (l : List (ZMod 2)) :
    (l.map (WordCoh.CentExt.incl c)).prod = WordCoh.CentExt.incl c l.sum := by
  induction l with
  | nil => rw [List.map_nil, List.prod_nil, List.sum_nil]; rfl
  | cons z zs ih =>
      rw [List.map_cons, List.prod_cons, ih, centExt_incl_mul, List.sum_cons]

/-- **Heisenberg-slice elements** `((v,1),z)` of the κ⁰-extension. -/
def hessSlice (v : V) (z : ZMod 2) : WordCoh.CentExt (kappa0Cocycle dat hdat) :=
  ((v, (1 : C)), z)

/-- **κ-free `C`-line elements** `((0,c),0)`. -/
def hessLine (c : C) : WordCoh.CentExt (kappa0Cocycle dat hdat) := (((0 : V), c), 0)

@[simp] theorem hessSlice_fib (v : V) (z : ZMod 2) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat) (hessSlice dat hdat v z) = z := rfl

@[simp] theorem hessLine_fib (c : C) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat) (hessLine dat hdat c) = 0 := rfl

theorem hessSlice_zero_zero : hessSlice dat hdat 0 0 = 1 := rfl

/-- The slice product law: the κ-correction degenerates to `f(v,w)`. -/
theorem hessSlice_mul (v w : V) (z z' : ZMod 2) :
    hessSlice dat hdat v z * hessSlice dat hdat w z'
      = hessSlice dat hdat (v + w) (z + z' + dat.f v w) := by
  refine WordCoh.CentExt.ext (Prod.ext ?_ ?_) ?_
  · show v + (1 : C) • w = v + w
    rw [one_smul]
  · exact one_mul 1
  · show z + z' + (dat.f v ((1 : C) • w) + dat.m 1 w) = z + z' + dat.f v w
    rw [one_smul, hdat.m_one, add_zero]

/-- The slice inversion law: the `q`-charge of inversion (char 2). -/
theorem hessSlice_inv (hV2 : ∀ v : V, v + v = 0) (v : V) (z : ZMod 2) :
    (hessSlice dat hdat v z)⁻¹ = hessSlice dat hdat v (z + q v) := by
  have hneg : ∀ w : V, -w = w := fun w => neg_eq_self hV2 w
  refine WordCoh.CentExt.ext (Prod.ext ?_ ?_) ?_
  · show -((1 : C)⁻¹ • v) = v
    rw [inv_one, one_smul, hneg]
  · exact inv_one
  · show z + (kappa0Cocycle dat hdat).κ (v, (1 : C)) (-((1 : C)⁻¹ • v), (1 : C)⁻¹)
      = z + q v
    rw [inv_one, one_smul, hneg, kappa0Cocycle_κ, one_smul, hdat.m_one, add_zero, hdat.f_diag]

/-- **The slice commutator law** — the cross-term mechanism, charge-independent:
`[((d,1),ζ), ((w,1),ξ)]` is central with fibre `b_q(d,w)`.  Module-side port of the NC
lane's `sliceElt_comm`. -/
theorem hessSlice_commR (hV2 : ∀ v : V, v + v = 0) (d w : V) (ζ ξ : ZMod 2) :
    commR (hessSlice dat hdat d ζ) (hessSlice dat hdat w ξ)
      = WordCoh.CentExt.incl _ (polar q d w) := by
  have hcross : dat.f d (d + w) = q d + dat.f d w := by
    have hc := hdat.f_cocycle d d w
    rw [hV2, hdat.f_zero_left, hdat.f_diag, zero_add] at hc
    rw [hc, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hkey : dat.f (d + w) d = q d + dat.f w d := by
    have hc := hdat.f_cocycle d w d
    rw [add_comm w d, hcross] at hc
    linear_combination hc
  have hV2' : d + w + d = w := by
    rw [add_comm d w, add_assoc, hV2, add_zero]
  rw [commR, hessSlice_inv dat hdat hV2, hessSlice_inv dat hdat hV2,
    hessSlice_mul dat hdat, hessSlice_mul dat hdat, hessSlice_mul dat hdat, hV2', hV2,
    hkey, hdat.f_diag]
  show hessSlice dat hdat 0 _ = _
  rw [show WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (polar q d w)
      = hessSlice dat hdat 0 (polar q d w) from rfl]
  congr 1
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hdat.f_polar d w

/-- The `C`-line product law: the κ-corrections vanish on it. -/
theorem hessLine_mul (c d : C) :
    hessLine dat hdat c * hessLine dat hdat d = hessLine dat hdat (c * d) := by
  refine WordCoh.CentExt.ext (Prod.ext ?_ ?_) ?_
  · show (0 : V) + c • (0 : V) = 0
    rw [smul_zero, add_zero]
  · rfl
  · show (0 : ZMod 2) + 0 + (dat.f 0 (c • (0 : V)) + dat.m c 0) = 0
    rw [smul_zero, hdat.f_zero_left, factorSet_m_zero dat hdat]
    simp only [add_zero]

/-- The `C`-line as a hom — what pushes arbitrary `ω₂`-resolver powers along it. -/
noncomputable def hessLineHom : C →* WordCoh.CentExt (kappa0Cocycle dat hdat) where
  toFun := hessLine dat hdat
  map_one' := rfl
  map_mul' c d := (hessLine_mul dat hdat c d).symm

@[simp] theorem hessLineHom_apply (c : C) : hessLineHom dat hdat c = hessLine dat hdat c :=
  rfl

/-- **The leading-power law**: `((v,1),0)^{2+2^α} = ι(q v)` for `α ≥ 2` — WW4's
extraspecial square law `hessSq_of_fibre` iterated through the spelling discipline
`2 + 2^α = 2(1 + 2^{α−1})`, with `1 + 2^{α−1}` odd exactly on the branch condition. -/
theorem hessSlice_pow_leading (hV2 : ∀ v : V, v + v = 0) {α : ℕ} (hα : 2 ≤ α) (v : V) :
    hessSlice dat hdat v 0 ^ (2 + 2 ^ α)
      = WordCoh.CentExt.incl _ (q v) := by
  rw [Words.two_add_two_pow α (by omega), pow_mul,
    show hessSlice dat hdat v 0 ^ 2 = WordCoh.CentExt.incl _ (q v) by
      rw [sq]
      exact hessSq_of_fibre dat hdat hV2 (hessSlice dat hdat v 0) rfl,
    centExt_incl_pow, nsmul_zmod2_odd (Words.odd_one_add_two_pow hα)]

/-! ### The graph-type marking and the word-side equation -/

/-- The wild-letter slots `x₀`, `x₁` of the compact-`N` alphabet (`x2Idx` is WN0-b's). -/
def x0Idx (h : ℕ) : Fin (2 + 2 * h + 1) := ⟨0, by omega⟩

@[inherit_doc x0Idx]
def x1Idx (h : ℕ) : Fin (2 + 2 * h + 1) := ⟨1, by omega⟩

/-- The handle-letter slots, matching `handleU`/`handleV`. -/
def hIdxU {h : ℕ} (j : Fin h) : Fin (2 + 2 * h + 1) := ⟨3 + 2 * (j : ℕ), by omega⟩

@[inherit_doc hIdxU]
def hIdxV {h : ℕ} (j : Fin h) : Fin (2 + 2 * h + 1) := ⟨4 + 2 * (j : ℕ), by omega⟩

/-- **The graph-type κ⁰-marking of the compact-`N` alphabet**: `σ ↦ ((0,s))`,
`τ ↦ ((0,u))` on the `C`-line, wild letter `x_i` on the Heisenberg slice at offset
`v i`.  The endpoint hypothesis `v (x2Idx h) = 0` (the boundary generator carries no
primal letter) is taken at the theorems, not baked into the marking. -/
def hessMark {h : ℕ} (s u : C) (v : Fin (2 + 2 * h + 1) → V) :
    Generator (2 + 2 * h) → SemiProd C V
  | .sigma => ((0 : V), s)
  | .tau => ((0 : V), u)
  | .wild i => (v i, (1 : C))

/-- The handle tail evaluates to the central inclusion of the hyperbolic sum
`Σ_j b_q(d_j, e_j)` — the Hessian-side twin of `heisF_handlesW_z`. -/
theorem hess_handlesW_eval {h : ℕ} (hV2 : ∀ v : V, v + v = 0) (s u : C)
    (v : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    PWord.evalZ (WordCoh.lift (hessMark s u v) (kappa0Cocycle dat hdat)) E E₂
        (handlesW h)
      = WordCoh.CentExt.incl _ (∑ j, polar q (v (hIdxU j)) (v (hIdxV j))) := by
  rw [handlesW, PWord.evalZ_prodList, List.map_map]
  have hcong : (List.finRange h).map
        (PWord.evalZ (WordCoh.lift (hessMark s u v) (kappa0Cocycle dat hdat)) E E₂
          ∘ fun j => PWord.comm (.gen (handleU j)) (.gen (handleV j)))
      = (List.finRange h).map fun j =>
          WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
            (polar q (v (hIdxU j)) (v (hIdxV j))) := by
    refine List.map_congr_left fun j _ => ?_
    show PWord.evalZ (WordCoh.lift (hessMark s u v) (kappa0Cocycle dat hdat)) E E₂
        (.comm (.gen (handleU j)) (.gen (handleV j))) = _
    rw [PWord.evalZ_comm, PWord.evalZ_gen, PWord.evalZ_gen,
      show WordCoh.lift (hessMark s u v) (kappa0Cocycle dat hdat) (handleU j)
        = hessSlice dat hdat (v (hIdxU j)) 0 from rfl,
      show WordCoh.lift (hessMark s u v) (kappa0Cocycle dat hdat) (handleV j)
        = hessSlice dat hdat (v (hIdxV j)) 0 from rfl,
      hessSlice_commR dat hdat hV2]
  rw [hcong,
    show ((List.finRange h).map fun j => WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
        (polar q (v (hIdxU j)) (v (hIdxV j))))
      = ((List.finRange h).map fun j => polar q (v (hIdxU j)) (v (hIdxV j))).map
          (WordCoh.CentExt.incl (kappa0Cocycle dat hdat)) from List.map_map.symm,
    centExt_incl_list_prod, ← Fin.sum_univ_def]

/-- **The word-side Hessian equation, general `h`, every resolver** (packet Def. 9.1(5)
at freeze row 2): the evaluated class-two value of the frozen compact-`N` word at the
graph-type κ⁰-marking with `x₂`-slot zero is

```
q(c₀) + b_q(c₀, c₁) + Σ_j b_q(d_j, e_j).
```

Resolver-immunity is exact, not approximate: at this marking the boundary block
`x₂^{-σ}(x₂τ)^{ω₂}` evaluates on the κ-free `C`-line for **every** value of `E ω₂`, so
no `ω₂`-representative pin is needed — the honest profinite instance is
`sqrtNegTwo_hess_eval`.  The `α ≥ 2` hypothesis enters exactly once, through
`hessSlice_pow_leading`. -/
theorem hessRelZ_nCompact {h α : ℕ} (hV2 : ∀ v : V, v + v = 0) (hα : 2 ≤ α) (s u : C)
    (v : Fin (2 + 2 * h + 1) → V) (hv2 : v (x2Idx h) = 0) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    hessRelZ (hessMark s u v) (kappa0Cocycle dat hdat) E E₂ (nCompactW α h)
      = q (v (x0Idx h)) + polar q (v (x0Idx h)) (v (x1Idx h))
        + ∑ j, polar q (v (hIdxU j)) (v (hIdxV j)) := by
  have hx2 : WordCoh.lift (hessMark s u v) (kappa0Cocycle dat hdat)
      (coreLetter h 2) = 1 := by
    show hessSlice dat hdat (v (x2Idx h)) 0 = 1
    rw [hv2]
    rfl
  rw [hessRelZ, hessEvalZ, nCompactW, PWord.evalZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have e1 : PWord.evalZ (WordCoh.lift (hessMark s u v) (kappa0Cocycle dat hdat))
      E E₂ (.zpow (.gen (coreLetter h 0)) (2 + 2 ^ α))
      = WordCoh.CentExt.incl _ (q (v (x0Idx h))) := by
    rw [PWord.evalZ_zpow, PWord.evalZ_gen,
      show WordCoh.lift (hessMark s u v) (kappa0Cocycle dat hdat) (coreLetter h 0)
        = hessSlice dat hdat (v (x0Idx h)) 0 from rfl,
      show ((2 : ℤ) + 2 ^ α) = ((2 + 2 ^ α : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
      hessSlice_pow_leading dat hdat hV2 hα]
  have e2 : PWord.evalZ (WordCoh.lift (hessMark s u v) (kappa0Cocycle dat hdat))
      E E₂ (.comm (.gen (coreLetter h 0)) (.gen (coreLetter h 1)))
      = WordCoh.CentExt.incl _ (polar q (v (x0Idx h)) (v (x1Idx h))) := by
    rw [PWord.evalZ_comm, PWord.evalZ_gen, PWord.evalZ_gen,
      show WordCoh.lift (hessMark s u v) (kappa0Cocycle dat hdat) (coreLetter h 0)
        = hessSlice dat hdat (v (x0Idx h)) 0 from rfl,
      show WordCoh.lift (hessMark s u v) (kappa0Cocycle dat hdat) (coreLetter h 1)
        = hessSlice dat hdat (v (x1Idx h)) 0 from rfl,
      hessSlice_commR dat hdat hV2]
  have e3 : PWord.evalZ (WordCoh.lift (hessMark s u v) (kappa0Cocycle dat hdat))
      E E₂ (.inv (.conj (.gen (coreLetter h 2)) (.gen .sigma))) = 1 := by
    rw [PWord.evalZ_inv, PWord.evalZ_conj, PWord.evalZ_gen, PWord.evalZ_gen, hx2, one_conjR,
      inv_one]
  have e4 : PWord.evalZ (WordCoh.lift (hessMark s u v) (kappa0Cocycle dat hdat))
      E E₂ (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau]))
      = hessLine dat hdat (u ^ E omega2) := by
    rw [PWord.omega2Pow, PWord.evalZ_profPow, PWord.prodList_cons, PWord.prodList_cons,
      PWord.prodList_nil, PWord.evalZ_mul, PWord.evalZ_mul, PWord.evalZ_gen,
      PWord.evalZ_gen, PWord.evalZ_one, mul_one, hx2, one_mul,
      show WordCoh.lift (hessMark s u v) (kappa0Cocycle dat hdat) Generator.tau
        = hessLineHom dat hdat u from rfl,
      ← map_zpow]
    rfl
  rw [e1, e2, e3, e4, hess_handlesW_eval dat hdat hV2 s u v E E₂, one_mul,
    WordCoh.CentExt.incl_mul_fib, WordCoh.CentExt.incl_mul_fib, WordCoh.CentExt.mul_fib,
    hessLine_fib, WordCoh.CentExt.incl_fib,
    show (kappa0Cocycle dat hdat).κ
        (WordCoh.CentExt.base (hessLine dat hdat (u ^ E omega2)))
        (WordCoh.CentExt.base (WordCoh.CentExt.incl _
          (∑ j, polar q (v (hIdxU j)) (v (hIdxV j))))) = 0 from
      (kappa0Cocycle dat hdat).κ_one_right _,
    zero_add, add_zero, add_assoc]

end Hessian

end GQ2.Dyadic.Certificates

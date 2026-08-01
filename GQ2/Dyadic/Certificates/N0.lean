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

end GQ2.Dyadic.Certificates

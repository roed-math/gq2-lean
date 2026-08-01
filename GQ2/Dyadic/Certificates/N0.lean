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

end GQ2.Dyadic.Certificates

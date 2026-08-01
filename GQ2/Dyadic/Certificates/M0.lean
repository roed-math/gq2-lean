/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Certificates.M0Fox
import GQ2.Dyadic.Certificates.N0
import GQ2.Dyadic.Word.Stokes
import GQ2.Dyadic.Word.Hessian

/-!
# Dyadic campaign, ticket WM0-c: Stokes, scalar, Hessian and phase certificates for compact `M_α`

The closing file of the compact-`M` lane (packet Def. 9.1 items (5)–(6) for **row 4** of the R5
selection freeze), on top of WM0-a's word (`GQ2/Dyadic/Words/M0.lean`), WM0-b's Fox certificate
(`GQ2/Dyadic/Certificates/M0Fox.lean`), WW3's second-order layer
(`GQ2/Dyadic/Word/Stokes.lean`) and WW4's Hessian/phase interface
(`GQ2/Dyadic/Word/{Hessian,Phase}.lean`).

```
R_{M,0} = A₀² [A₀,x₁] σ₂^{2m} · J₂ · E_m^rev · H_h,
A₀ = x₀⁻¹σ₂⁻ᵐ,  J₂ = x₂^{-σ}(x₂τ)^{ω₂},  E_m^rev = δ₁^{σ₂^{2m}}δ₁^{σ₂^m}δ₀^{σ₂^m}δ₀,  m = 2^{α−1}
```

## 1. The Stokes certificate

`heisZ_mCompact_unram` evaluates the word's central (Stokes) coordinate at the Heisenberg lift
of a simple-tame-module marking, exact in the resolver value `E ω₂ = e`.  The decomposition is
the same **rank-3 core atoms ⊕ `h` hyperbolic planes** shape as the pilot's, reached by a
different mechanism in the first two atoms:

* the **`x₀`-diagonal** `y₀(a₀)` — from `A₀²`, whose exponent is the literal `2`, so
  `C(2,2) = 1` and **no `α`-hypothesis is consumed** (contrast the pilot's `x₀^{2+2^α}`, which
  needs `α ≥ 2` for `choose_two_add_two_pow_odd`).  The `σ₂^{−m}` half of `A₀` contributes only
  a central charge, and `2 •` kills it;
* the **`(A₀,x₁)` hyperbolic cross** `y₀(a₁) + y₁(a₀)` from `[A₀,x₁]`;
* the **boundary block** `J₂` on `(σ,τ,x₂)`, which is the pilot's third-and-fourth factor
  verbatim (`heisF_j2W`), hence the same `(1+S)`-atom and the same
  `isUnit_onePlusSEnd_iff` dichotomy;
* the **`h` identity-operator hyperbolic planes** from `H_h`;
* and — the compact-`M` addition — the **`𝓔`-correction block**, which is *central* at the
  unramified class (`heisZ_eRevW_P1`), so it enters the row as a scalar and not as an atom.

**`σ₂^{2m}` contributes nothing at second order** (`heisZ_sigma2Pow_two_mul_eq_zero`): its jet
dies because `2m` is even, and its central charge `C(2m,2) • Σ.λ(Σ.a)` dies because
`C(2m,2) = m(2m−1)` with `m = 2^{α−1}` even.  This is the second-order twin of WM0-b's finding
that **the `σ`-column cancels over `ℤ`** — there it was the differentiated power balance
`−2·2^{α−1} + 2^α = 0`; here it is the same balance one degree up, and the opaque atom `D(σ₂)`
(`𝒢_m`, the Sage engine's `G[S;ω₂]`) is again **never computed**: `sigma2Z` stays a formal
`HeisLift` throughout.

The `hS₂` discipline is WM0-b's, one degree up: the unramified-simple certificates carry
`hS₂ : ∀ v, sigma2Z.g • v = v`.  The pilot never met this hypothesis — the compact-`N` word has
no `σ₂`-letter at all.

**Resolver dependence is exact**: the general form carries `e •` and `C(e,2) •` coefficients,
and `C(e,2)` depends on `e mod 4` — ticket S1.T's "the lift level is 4, not 2".  The honest
`ω₂` representative on a finite 2-group target satisfies `e ≡ 1 (mod 4)`, so
`heisZ_mCompact_res_one` is the certificate form; the `e ≡ 3` twin is kept visible at the
scalar Gram (`sqrtTwo_scalarGram_three`).

`IsStokesEndpoint` is proved **generally** (`mCompact_isStokesEndpoint`: all `α ≥ 1`, all `h`,
every even `q` and odd `e`), as in the pilot; duality rides `stokesDuality_of_simple`.

## 2. The scalar certificate

`sqrtTwo_scalarGram` / `sqrtTwo_scalarGram_three` pin the traced Stokes Gram of the `√2`
family on the scalar module at the packet column order `σ, τ, x₀, x₁, x₂`, by kernel `decide`
— the `e = 1` / `e = 3` twins that make S1.T's mod-4 sensitivity a matrix pair, exactly as
`sqrtNegTwo_scalarGram{,_three}` does for the pilot.

## 3. The Hessian certificate: **both projector normal forms**

The lane's two-branch obligation, connected word-side to WW4's two endpoints.  At the graph-type
κ⁰-marking (`hessMarkM`: `σ`, `τ` on the κ-free `C`-line, wild letters on the Heisenberg slice,
`x₂` carrying no primal letter) the δ-letter's jet is the freeze's `d_i = (1 + P) c_i`, and the
two branches are exactly the two values of the `ω₂`-norm projector `P = N_T`:

* **`P = 1`** (`hessRelZ_mCompact_P1`, hypothesis `hP1`: the `ω₂`-block `(x_iτ)^{ω₂}` is the
  slice element `x_i` again — the unramified reading, where `τ` sits on the trivial line): every
  `d_i = 0`, the correction block is **trivial**, and the word-side value is
  `q(c₀) + b_q(c₀,c₁) + Σ_j b_q(d_j,e_j)`.  At `h = 0` this is `plusFormD q q` on the nose —
  the endpoint of WW4's `compactM_P1_certificate`, with the **identity** CoV.  WM0-b proved the
  `P = 1` case *is* the compact-`N` construction at first order; `hessRelZ_mCompact_P1_eq_nCompact`
  makes that a second-order theorem too (the two words have equal evaluated Hessians).
* **`P = 0`** (`hessRelZ_mCompact_P0`, hypothesis `hP0`: the `ω₂`-block is trivial — the ramified
  reading, WM0-b's `hTodd`/`hτfpf` class): `d_i = c_i`, the correction block contributes exactly
  `q(c₀) + q(c₁)`, and the word-side value becomes `q(c₁) + b_q(c₀,c₁) + Σ_j b_q(d_j,e_j)` —
  the endpoint of WW4's `compactM_P0_certificate`, reached by the **`(c₀,c₁)` block-swap** CoV
  (`LinearEquiv.prodComm`).  The block's `q(c₀) + q(c₁)` is *not* an interpolation: it is the
  six-pair κ-sum of the four δ-factors, `q(c₁) + q(c₀) + 4·f(c₁,c₀)`, with the four self-charges
  cancelling in pairs.

Both branches are proved at **general `h` and every resolver**; the projector branch is the only
hypothesis that separates them.  (Freeze row 4's ⚠ open input — the compact-`M` *marked* change
of variables, errata item 3 — is untouched here: these are the gate-E CoVs, which the freeze
does display.)

## 4. The order-rejection certificate (the lane's headline)

WM0-a built the forward-order mutant `mFwdW`; WM0-b proved first-order equality as a theorem
chain and correctly left the rejection here.  What this file proves is S4.1 §9.4's **difference
formula**, in the class-two algebra:

```
Q(fwd) + Q(rev) = b_q(W d₀, d₀) + b_q(W d₁, d₁) + b_q((1 + W²) d₁, d₀),
d_i = (1 + P) c_i,   W = the σ₂^m-action,   P = N_T
```

(`hessRelZ_mFwdW_add_mCompactW`).  The route is three steps, and each is a separate headline:

1. **The whole-word difference is the block difference** (`hessRelZ_mWordWith_add`): the two
   words share their other four factors and their handle tail, and the two correction blocks
   have *equal total jets* (a product's jet is order-independent), so every prefix/suffix cross
   term is common and cancels.  This is where WM0-a's block-agnostic `mWordWith` pays for
   itself.
2. **Reversal adds the full polarization** (`centExt_rev4_fib`): for four elements of a
   class-two group, `fib(p₁p₂p₃p₄) + fib(p₄p₃p₂p₁) = Σ_{i<j} b(bᵢ,bⱼ)`, because the ordered
   product's fibre is `Σ fib(pᵢ) + Σ_{i<j} κ(bᵢ,bⱼ)` and reversal transposes κ, whose
   symmetrization is the polar form.  The self-charges never enter.
3. **Six pairs collapse to three** (`polarSum_rev4_collapse`): with `b(Wx,Wy) = b(x,y)` the pairs
   `(1,3)` and `(2,4)` become equal and cancel in characteristic 2, `(2,3)` merges with `(1,4)`
   into `b((1+W²)d₁,d₀)`, and `(1,2)`, `(3,4)` are the two diagonal terms.

The formula's two structural corollaries are proved, not asserted:
`mFwdW_second_order_eq_of_P1` (at `P = 1` every `dᵢ = 0`, so the orders agree at second order
too — the second-order continuation of WM0-b's order-invisibility chain) and
`mFwdW_second_order_eq_of_trivial_W` (at `W = 1` the difference dies because `b` is alternating
and `1 + W² = 0`).  Together they are the freeze's **visibility criterion**
`(1 + P) ≠ 0 ∧ σ₂^m ≠ 1`, in Lean.

**The negative pin.**  `fifthRoot_separates` exhibits the archive's `F16-fifth-root` orbit — the
`(α, q_K) = (2,2)` separating orbit of the S4.1 battery — as a concrete `𝔽₂`-module on which the
difference is `1 ≠ 0`, by kernel `decide`: `V = 𝔽₁₆ = 𝔽₂[g]/(g⁴+g+1)` carried as
`ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2`, `T` = multiplication by the primitive fifth root `g³`,
`W = σ₂^m` = the squared Frobenius `x ↦ x⁴` (order 2, so `1 + W² = 0` and the difference is the
archive's *linear* shape), and `q x = Tr_{𝔽₁₆/𝔽₂}(g·x⁵)`, the `T`-invariant nonsingular form.
All four facts a genuine instance owes are kernel-checked: `q` is quadratic and nonsingular,
`q` is `T`- and `W`-invariant, `P = 1 + T + T² + T³ + T⁴ = 0` (hence `dᵢ = cᵢ`), and the
difference at `c₀ = g³`, `c₁ = 0` is `1`.

⚠ **Honest size wall.**  This pin does *not* cover the two **displayed** instances.  Per errata
item 6 the fifth-root orbit separates the orders only at `(α, q_K) = (2,2)`, and √2 is `(3,2)`
while √5 is `(2,4)`; both need the `F256-seventeenth-root` orbit, i.e. `dim_{𝔽₂} V = 8`, 256
module elements.  The obstruction is not the difference evaluation (one vector — trivial) but
the *quadraticity* side condition `IsQuadraticFp2 q`, which is a three-variable identity and so
`256³ ≈ 1.7 × 10⁷` kernel evaluations; the `T`/`W`-invariance checks are only 256 each and would
be fine.  The instantiation route is therefore: supply `IsQuadraticFp2` for the dim-8 form by a
*structural* lemma (any `Σ_{i≤j} U_ij x_i x_j` is quadratic — the Sage side's `QuadraticForm`
invariant) rather than by `decide`, at which point the seventeenth-root pin costs the same as
this one.  That structural lemma is a `GQ2/QuadraticFp2.lean` API item, not a word-lane item,
so it is recorded here and not built here.  The proved general bound (a separating orbit needs
`dim ≥ 2^α`) is why no cheaper orbit exists.

## 5. The phase consumables

Taken from WW4's certificates at **both** projector branches: `mCompact_P1_G0` / `mCompact_P0_G0`
(`G0 = 2^d`), the packet-Lem-6.1 translated sums, and the degree-`n` magnitudes `2^{n·d}` in
`SN` shape.  `sqrtTwo_gauss_degree_two` / `sqrtFive_gauss_degree_two` pin the `√2` (`m = 4`,
`α = 3`) and `√5` (`m = 2`, `α = 2`) instances end to end.

## Implementation notes

Not `module`-style, and forced: `GQ2.Dyadic.Certificates.M0Fox` is plain-import.  No new
axioms; kernel `decide` only.  The `deltaC` → `deltaCert` rename is WM0-b's (the peripheral
`GQ2.deltaC` wins the resolution race); it is repeated here for the same reason.
-/

namespace GQ2.Dyadic.Certificates.MCompact

open GQ2.FoxH GQ2.Dyadic.Words.MCompact

open GQ2.Dyadic.Words.MCompact renaming deltaC → deltaCert

/-! ## Generic second-order rules the compact-`M` row needs

The pilot could read every factor off the trivial-base closed forms, because every one of its
factors acts trivially.  The compact-`M` row cannot: `A₀` and `σ₂^{2m}` act through the
balancing powers `S₂^{∓m}`.  These three rules are what replace it — and they are what makes
the opaque atom `D(σ₂)` stay opaque. -/

section GenericHeis

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- The base of a `ℤ`-power is the power of the base (`HeisLift.gHom` is a `MonoidHom`). -/
theorem heisZpow_g (p : HeisLift A C) (k : ℤ) : (p ^ k).g = p.g ^ k :=
  map_zpow HeisLift.gHom p k

/-- `n • a = a` for odd `n` on a 2-torsion module — the companion of `even_nsmul_eq_zero`, and
the rule by which an odd resolver value collapses an `ω₂`-block's jet onto its base offset. -/
theorem nsmul_self_of_odd {M : Type*} [AddCommGroup M] (h2 : ∀ a : M, a + a = 0) {n : ℕ}
    (hn : Odd n) (a : M) : n • a = a := by
  obtain ⟨k, rfl⟩ := hn
  rw [add_nsmul, one_nsmul, even_nsmul_eq_zero h2 ⟨k, by ring⟩, zero_add]

/-- **The second-order trivial lifts**: jet-zero *and* zero central charge.  Strictly stronger
than `heisJetZero` membership, and exactly what the compact-`M` correction block satisfies at
the `P = 1` class — which is why the block can be dismissed rather than merely commuted past. -/
def heisTrivial (A C : Type*) [Group C] [AddCommGroup A] [DistribMulAction C A] :
    Subgroup (HeisLift A C) where
  carrier := {p | p.a = 0 ∧ p.l = 0 ∧ p.z = 0}
  one_mem' := ⟨rfl, rfl, rfl⟩
  mul_mem' := fun {p r} hp hr =>
    ⟨by rw [HeisLift.mul_a, hp.1, hr.1, smul_zero, add_zero],
     by rw [HeisLift.mul_l, hp.2.1, hr.2.1, smul_zero, add_zero],
     by rw [HeisLift.mul_z, hp.2.2, hr.2.2, hp.2.1, hr.1, smul_zero, ElemDual.zero_apply,
       add_zero, add_zero]⟩
  inv_mem' := fun {p} hp =>
    ⟨by rw [HeisLift.inv_a, hp.1, smul_zero, neg_zero],
     by rw [HeisLift.inv_l, hp.2.1, smul_zero, neg_zero],
     by rw [HeisLift.inv_z, hp.2.2, hp.2.1, ElemDual.zero_apply, add_zero]⟩

theorem mem_heisTrivial {p : HeisLift A C} :
    p ∈ heisTrivial A C ↔ p.a = 0 ∧ p.l = 0 ∧ p.z = 0 := Iff.rfl

/-- Second-order triviality survives conjugation by an **arbitrary** lift, provided the
conjugand's base acts trivially: both `s`-offsets enter `heisConjR_of_trivial` only through the
mixed pairing, and that pairing has a zero slot on each side. -/
theorem heisConjR_mem_heisTrivial {p s : HeisLift A C} (hp : ∀ a : A, p.g • a = a)
    (hmem : p ∈ heisTrivial A C) : conjR p s ∈ heisTrivial A C := by
  obtain ⟨ha, hl, hz⟩ := hmem
  rw [heisConjR_of_trivial p s hp]
  exact ⟨by show s.g⁻¹ • p.a = 0; rw [ha, smul_zero],
    by show s.g⁻¹ • p.l = 0; rw [hl, smul_zero],
    by show p.z + s.l p.a + p.l s.a = 0; rw [ha, hl, hz, map_zero, ElemDual.zero_apply,
      add_zero, add_zero]⟩

/-- **A trivial-base lift raised to an even natural power is jet-zero** on a 2-torsion module.
The mechanism by which every `σ₂`-power in the word loses its first jet. -/
theorem heisPow_jetZero_of_even (p : HeisLift A C) (hp : ∀ a : A, p.g • a = a)
    (hA₂ : ∀ a : A, a + a = 0) {n : ℕ} (hn : Even n) : p ^ n ∈ heisJetZero A C := by
  rw [heisPow_of_trivial p hp n]
  exact ⟨even_nsmul_eq_zero hA₂ hn _, even_nsmul_eq_zero ElemDual.add_self_eq_zero hn _⟩

/-- The central charge of an even trivial-base power is the binomial term alone: `n • p.z` dies
in the `ZMod 2` centre. -/
theorem heisPow_z_of_even (p : HeisLift A C) (hp : ∀ a : A, p.g • a = a) {n : ℕ} (hn : Even n) :
    (p ^ n).z = (n.choose 2) • p.l p.a := by
  rw [heisPow_of_trivial p hp n, nsmul_zmod2_even hn]
  exact zero_add _

/-- **The `σ₂`-power law**: an even power of a trivially-acting atom, and its inverse, are both
jet-zero with the *same* central charge `C(n,2) • λ(a)`.  Stated for `ℤ`-powers because the word
spells `σ₂^{−m}` and `σ₂^{2m}`. -/
theorem heisZpow_of_even (p : HeisLift A C) (hp : ∀ a : A, p.g • a = a)
    (hA₂ : ∀ a : A, a + a = 0) {n : ℕ} (hn : Even n) :
    p ^ (n : ℤ) ∈ heisJetZero A C ∧ p ^ (-(n : ℤ)) ∈ heisJetZero A C := by
  have hmem : p ^ (n : ℤ) ∈ heisJetZero A C := by
    rw [zpow_natCast]
    exact heisPow_jetZero_of_even p hp hA₂ hn
  exact ⟨hmem, by rw [zpow_neg]; exact inv_mem hmem⟩

end GenericHeis

/-! ## The second-order (Stokes) rows of the compact-`M` word

The six factors of `R_{M,0}` evaluated in the Heisenberg lift at a simple-tame-module marking:
`hwild` (every wild letter acts trivially), `hτ` (the unramified `τ`-class) and — new in this
lane — `hS₂`, WM0-b's `σ₂`-triviality discipline one degree up. -/

section StokesRows

variable {h α : ℕ} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]
  (t : Marking (2 + 2 * h) C) (x : Generator (2 + 2 * h) → A)
  (y : Generator (2 + 2 * h) → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **The opaque `σ₂`-atom** `Σ = σ^{ω₂}` in the Heisenberg lift.  Like WM0-b's `𝒢_m`
(`G[S;ω₂]` on the Sage side) this is never computed: every statement below consumes it only
through `hS₂` and the parity of the exponent. -/
noncomputable def sigma2Z : HeisLift A C := heisEvalZ ⇑t x y E E₂ sigma2W

@[simp] theorem sigma2Z_def : heisEvalZ ⇑t x y E E₂ sigma2W = sigma2Z t x y E E₂ := rfl

/-- The `σ₂`-atom's base is the resolved `2`-primary part of the `σ`-letter. -/
theorem sigma2Z_g : (sigma2Z t x y E E₂).g = t.σ ^ E omega2 := by
  rw [sigma2Z, sigma2W, PWord.omega2Pow, heisEvalZ_profPow, heisZpow_g, heisEvalZ_gen]
  rfl

/-- **`σ₂^{k}` is jet-zero for every even `k`**, under the `hS₂` discipline: the jets carry the
factor `k` and the module is 2-torsion. -/
theorem heisZ_sigma2Pow_jetZero (hA₂ : ∀ a : A, a + a = 0)
    (hS₂ : ∀ v : A, (sigma2Z t x y E E₂).g • v = v) {n : ℕ} (hn : Even n) :
    heisEvalZ ⇑t x y E E₂ (.zpow sigma2W (n : ℤ)) ∈ heisJetZero A C ∧
      heisEvalZ ⇑t x y E E₂ (.zpow sigma2W (-(n : ℤ))) ∈ heisJetZero A C := by
  rw [heisEvalZ_zpow, heisEvalZ_zpow]
  exact heisZpow_of_even _ hS₂ hA₂ hn

/-- **Factor 3 — `σ₂^{2m}` is invisible at second order.**  Its jet dies because `2m` is even;
its central charge `C(2m,2) • λ(a)` dies because `C(2m,2) = m(2m−1)` and `m = 2^{α−1}` is even
for `α ≥ 2`.  This is WM0-b's "the `σ`-column cancels over `ℤ`" one degree up: the packet's
power balance `−2·2^{α−1} + 2^α = 0`, differentiated twice. -/
theorem heisZ_sigma2Pow_two_mul (hA₂ : ∀ a : A, a + a = 0)
    (hS₂ : ∀ v : A, (sigma2Z t x y E E₂).g • v = v) (hα : 2 ≤ α) :
    heisEvalZ ⇑t x y E E₂ (.zpow sigma2W (2 * (mOf α : ℤ)))
      = ⟨0, 0, 0, ((sigma2Z t x y E E₂).g) ^ (2 * mOf α)⟩ := by
  have hev : Even (2 * mOf α) := even_two_mul _
  have hchoose : Even ((2 * mOf α).choose 2) := by
    have hm : Even (mOf α) := even_mOf hα
    rw [Nat.choose_two_right,
      show 2 * mOf α * (2 * mOf α - 1) = mOf α * (2 * mOf α - 1) * 2 by ring,
      Nat.mul_div_cancel _ (by norm_num)]
    exact hm.mul_right _
  rw [heisEvalZ_zpow, show (2 * (mOf α : ℤ)) = ((2 * mOf α : ℕ) : ℤ) by push_cast; ring,
    zpow_natCast, sigma2Z_def, heisPow_of_trivial _ hS₂]
  refine HeisLift.ext ?_ ?_ ?_ rfl
  · exact even_nsmul_eq_zero hA₂ hev _
  · exact even_nsmul_eq_zero ElemDual.add_self_eq_zero hev _
  · rw [nsmul_zmod2_even hev, nsmul_zmod2_even hchoose, add_zero]

/-- The Labute letter `A₀ = x₀⁻¹σ₂^{−m}` has the jet of `x₀⁻¹` alone: the `σ₂`-half is jet-zero
(`m = 2^{α−1}` is even for `α ≥ 2`), so it can only add a central charge. -/
theorem heisF_a0W (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hS₂ : ∀ v : A, (sigma2Z t x y E E₂).g • v = v) (hα : 2 ≤ α) :
    (heisEvalZ ⇑t x y E E₂ (a0W α h)).a = -x (coreLetter h 0) ∧
      (heisEvalZ ⇑t x y E E₂ (a0W α h)).l = -y (coreLetter h 0) ∧
      (∀ v : A, (heisEvalZ ⇑t x y E E₂ (a0W α h)).g • v = v) := by
  have hjz := (heisZ_sigma2Pow_jetZero t x y E E₂ hA₂ hS₂ (even_mOf hα)).2
  have h0 := mem_trivAct.mp (trivAct_coreLetter t hwild 0)
  have hev : heisEvalZ ⇑t x y E E₂ (a0W α h)
      = heisEvalZ ⇑t x y E E₂ (.inv (.gen (coreLetter h 0)))
        * heisEvalZ ⇑t x y E E₂ (.zpow sigma2W (-(mOf α : ℤ))) := by
    rw [a0W, PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, heisEvalZ_mul,
      heisEvalZ_mul, heisEvalZ_one, mul_one]
  have hinv : heisEvalZ ⇑t x y E E₂ (.inv (.gen (coreLetter h 0)))
      = ⟨-x (coreLetter h 0), -y (coreLetter h 0),
          y (coreLetter h 0) (x (coreLetter h 0)), (t (coreLetter h 0))⁻¹⟩ := by
    rw [heisEvalZ_inv, heisEvalZ_gen]
    refine HeisLift.ext ?_ ?_ ?_ rfl
    · show -((t (coreLetter h 0))⁻¹ • x (coreLetter h 0)) = _
      rw [mem_trivAct.mp (inv_mem (trivAct_coreLetter t hwild 0))]
    · show -((t (coreLetter h 0))⁻¹ • y (coreLetter h 0)) = _
      rw [smul_elemDual_of_trivial (mem_trivAct.mp (inv_mem (trivAct_coreLetter t hwild 0)))]
    · show (0 : ZMod 2) + y (coreLetter h 0) (x (coreLetter h 0)) = _
      rw [zero_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [hev, HeisLift.mul_a, hinv, hjz.1, smul_zero, add_zero]
  · rw [hev, HeisLift.mul_l, hinv, hjz.2, smul_zero, add_zero]
  · intro v
    rw [hev, HeisLift.mul_g, hinv, mul_smul,
      mem_trivAct.mp (inv_mem (trivAct_coreLetter t hwild 0))]
    rw [heisEvalZ_zpow, sigma2Z_def, heisZpow_g]
    exact mem_trivAct.mp (zpow_mem (mem_trivAct.mpr hS₂) _) v

/-- **Factor 1 — `A₀²` is jet-zero central with value the diagonal `y₀(a₀)`.**

The exponent is the *literal* `2`, so `C(2,2) = 1` carries the diagonal with **no parity
side-condition on `α`** — the compact-`M` row's cheapest deviation from the pilot, whose
`x₀^{2+2^α}` needs `choose_two_add_two_pow_odd`.  The `σ₂^{−m}` charge inside `A₀` is killed by
the `2 •` in front of `A₀.z`, which is why the opaque atom never surfaces. -/
theorem heisF_leadingSquare (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hS₂ : ∀ v : A, (sigma2Z t x y E E₂).g • v = v) (hα : 2 ≤ α) :
    heisEvalZ ⇑t x y E E₂ (.zpow (a0W α h) 2)
      = ⟨0, 0, y (coreLetter h 0) (x (coreLetter h 0)),
          (heisEvalZ ⇑t x y E E₂ (a0W α h)).g ^ 2⟩ := by
  obtain ⟨ha, hl, hg⟩ := heisF_a0W t x y E E₂ hA₂ hwild hS₂ hα
  rw [heisEvalZ_zpow, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast,
    heisPow_of_trivial _ hg]
  refine HeisLift.ext ?_ ?_ ?_ rfl
  · exact even_nsmul_eq_zero hA₂ (by decide) _
  · exact even_nsmul_eq_zero ElemDual.add_self_eq_zero (by decide) _
  · rw [nsmul_zmod2_even (by decide), zero_add, ha, hl, Nat.choose_self, one_nsmul,
      ElemDual.neg_apply, map_neg, neg_neg]

/-- **Factor 2 — `[A₀,x₁]` is jet-zero central with the hyperbolic cross `y₀(a₁) + y₁(a₀)`.**
The `σ₂`-half of `A₀` is invisible here for the same reason it is invisible to the Fox row: the
two `D(A₀)` copies of a commutator cancel. -/
theorem heisF_leadingComm (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hS₂ : ∀ v : A, (sigma2Z t x y E E₂).g • v = v) (hα : 2 ≤ α) :
    heisEvalZ ⇑t x y E E₂ (.comm (a0W α h) (.gen (coreLetter h 1)))
      = ⟨0, 0, y (coreLetter h 0) (x (coreLetter h 1)) + y (coreLetter h 1) (x (coreLetter h 0)),
          commR (heisEvalZ ⇑t x y E E₂ (a0W α h)).g (t (coreLetter h 1))⟩ := by
  obtain ⟨ha, hl, hg⟩ := heisF_a0W t x y E E₂ hA₂ hwild hS₂ hα
  rw [heisEvalZ_comm, heisEvalZ_gen,
    heisCommR_of_trivial _ _ hg (mem_trivAct.mp (trivAct_coreLetter t hwild 1))]
  refine HeisLift.ext rfl rfl ?_ rfl
  show (heisEvalZ ⇑t x y E E₂ (a0W α h)).l (x (coreLetter h 1))
      + y (coreLetter h 1) (heisEvalZ ⇑t x y E E₂ (a0W α h)).a = _
  rw [ha, hl, ElemDual.neg_apply, map_neg, CharTwo.neg_eq, CharTwo.neg_eq]

/-! ### Factors 4–6: the boundary block, the correction block, the handles

`J₂` and `H_h` are the pilot's own factors, so they are **used, not re-derived**: the two
compact-`N` rows `heisF_invConjX2`/`heisF_deltaBlock` and `heisF_handlesW_z` transport across
`coreLetter_eq`/`handleU_eq`/`handleV_eq`, which are all `rfl`.  This is the second-order
continuation of WM0-b's "the `x₂`-block **is** the compact-`N` block". -/

/-- `MCompact`'s handle block is WN0-a's, on the nose. -/
theorem handlesW_eq (h : ℕ) : handlesW h = Words.handlesW h := rfl

/-- The handle **tail** (empty at `h = 0`, per WM0-a deviation 1) has the handle block's
value at every `h`. -/
theorem heisEvalZ_handleTailW (t : Marking (2 + 2 * h) C) (x : Generator (2 + 2 * h) → A)
    (y : Generator (2 + 2 * h) → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    (((handleTailW h).map (heisEvalZ ⇑t x y E E₂)).prod) = heisEvalZ ⇑t x y E E₂ (handlesW h) := by
  cases h with
  | zero => rw [handleTailW, handlesW_eq]; rfl
  | succ n => rw [handleTailW]; simp only [List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]

/-- **Factor 4 — the boundary block `J₂ = x₂^{-σ}(x₂τ)^{ω₂}`**, exact in the resolver: the
product of the pilot's third and fourth factors, transported verbatim. -/
theorem heisF_j2W (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hτ : ∀ v : A, t.τ • v = v) {e : ℕ} (hE : E omega2 = (e : ℤ)) :
    (heisEvalZ ⇑t x y E E₂ (j2W h)).z
      = (y .sigma (x (coreLetter h 2)) + y (coreLetter h 2) (x .sigma)
          + y (coreLetter h 2) (x (coreLetter h 2)))
        + (e • y (coreLetter h 2) (x .tau)
            + (e.choose 2) • ((y (coreLetter h 2) + y .tau) (x (coreLetter h 2) + x .tau)))
        + e • y (coreLetter h 2) (t.σ • (x (coreLetter h 2) + x .tau)) := by
  have e3 := Certificates.heisF_invConjX2 t x y E E₂ hwild
  have e4 := Certificates.heisF_deltaBlock t x y E E₂ hwild hτ hE
  simp only [coreLetter_eq]
  rw [show j2W h = PWord.mul (.inv (.conj (.gen (coreLetter h 2)) (.gen .sigma)))
      (PWord.mul (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau]))
        PWord.one) from rfl,
    heisEvalZ_mul, heisEvalZ_mul, heisEvalZ_one, mul_one]
  simp only [coreLetter_eq] at e3 e4 ⊢
  rw [HeisLift.mul_z, e3, e4]
  dsimp only
  rw [mem_trivAct.mp
      (inv_mem (trivAct_conjR (Certificates.trivAct_coreLetter t hwild 2) t.σ)),
    map_nsmul, ElemDual.neg_apply, ElemDual.smul_apply, inv_inv, CharTwo.neg_eq, map_add,
    smul_add]

/-- **Factor 6, membership** — the handle block is jet-zero at every handle count. -/
theorem heisF_handlesW_mem (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) :
    heisEvalZ ⇑t x y E E₂ (handlesW h) ∈ heisJetZero A C := by
  rw [handlesW_eq]
  exact Certificates.heisF_handlesW_mem t x y E E₂ hwild

/-- **Factor 6, value** — the `h` identity-operator hyperbolic planes. -/
theorem heisF_handlesW_z (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) :
    (heisEvalZ ⇑t x y E E₂ (handlesW h)).z
      = ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  rw [handlesW_eq]
  exact Certificates.heisF_handlesW_z t x y E E₂ hwild

/-! ### The correction block at the `P = 1` (unramified) class

On the **wild block** — the boundary convention `x τ = 0`, `y τ = 0`, matching the pilot's
`heisZ_nCompact_wild_block` and the Hessian marking's "`τ` carries no primal letter" — the
`δ`-letter is *trivial* at second order, not merely jet-zero: its jet is `a_i − a_i = 0` and its
two central charges `y_i(a_i)` cancel.  Hence the whole `𝓔`-block is trivial, and the
compact-`M` row **is** the compact-`N` row.  This is S4.1's module finding (i), "the correction
is invisible exactly when the projector is 1", at second order. -/

/-- The inner word `x_iτ` of the `δ`-letter, at an **arbitrary** wild index.

⚠ Re-derived, not reused: the pilot's `heisF_deltaInner`/`heisF_deltaBlock` are hardwired at
`coreLetter h 2` (compact-`N` has exactly one `δ`-letter), while the compact-`M` correction
block carries `δ₀` and `δ₁`.  An index-generic restatement belongs in the WW toolkit — see the
report's API findings. -/
theorem heisF_deltaInnerAt (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (i : Fin 3) :
    heisEvalZ ⇑t x y E E₂ (PWord.prodList [.gen (coreLetter h i), .gen .tau])
      = ⟨x (coreLetter h i) + x .tau, y (coreLetter h i) + y .tau,
          y (coreLetter h i) (x .tau), t (coreLetter h i) * t.τ⟩ := by
  have hi := mem_trivAct.mp (trivAct_coreLetter t hwild i)
  rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, heisEvalZ_mul,
    heisEvalZ_mul, heisEvalZ_gen, heisEvalZ_gen, heisEvalZ_one, mul_one]
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · show x (coreLetter h i) + t (coreLetter h i) • x .tau = _
    rw [hi]
  · show y (coreLetter h i) + t (coreLetter h i) • y .tau = _
    rw [smul_elemDual_of_trivial hi]
  · show (0 : ZMod 2) + 0 + y (coreLetter h i) (t (coreLetter h i) • x .tau) = _
    rw [hi, zero_add, zero_add]
  · rfl

@[inherit_doc heisF_deltaInnerAt]
theorem heisF_deltaBlockAt (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hτ : ∀ v : A, t.τ • v = v) {e : ℕ} (hE : E omega2 = (e : ℤ)) (i : Fin 3) :
    heisEvalZ ⇑t x y E E₂
        (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau]))
      = ⟨e • (x (coreLetter h i) + x .tau), e • (y (coreLetter h i) + y .tau),
          e • y (coreLetter h i) (x .tau)
            + (e.choose 2) • ((y (coreLetter h i) + y .tau)
                (x (coreLetter h i) + x .tau)),
          (t (coreLetter h i) * t.τ) ^ e⟩ := by
  have hi := mem_trivAct.mp (trivAct_coreLetter t hwild i)
  have hbase : ∀ v : A, (t (coreLetter h i) * t.τ) • v = v := fun v => by
    rw [mul_smul, hτ, hi]
  rw [PWord.omega2Pow, heisEvalZ_profPow, heisF_deltaInnerAt t x y E E₂ hwild i, hE,
    zpow_natCast, heisPow_of_trivial _ hbase]

/-- **The `δ`-letter is trivial at second order** on the wild block at the honest resolver
class.  `e ≡ 1 (mod 4)` is consumed exactly twice: `e` odd collapses the `ω₂`-block's jet onto
`a_i`, and `C(e,2)` even kills its own charge; the two surviving `y_i(a_i)` charges then cancel
in the `ZMod 2` centre.  Jet **and** value vanish — the block is not merely jet-zero. -/
theorem heisF_deltaCert_trivial (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) (hτ : ∀ v : A, t.τ • v = v)
    (hxτ : x .tau = 0) (hyτ : y .tau = 0) {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1)
    (i : Fin 3) : heisEvalZ ⇑t x y E E₂ (deltaCert h i) ∈ heisTrivial A C := by
  have hi := mem_trivAct.mp (trivAct_coreLetter t hwild i)
  have hodd := odd_of_mod_four_eq_one he
  have hbase : ∀ v : A, ((t (coreLetter h i) * t.τ) ^ e) • v = v := fun v =>
    mem_trivAct.mp (pow_mem (mem_trivAct.mpr (fun w => by rw [mul_smul, hτ, hi])) e) v
  have hblk : heisEvalZ ⇑t x y E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau]))
      = ⟨x (coreLetter h i), y (coreLetter h i), 0, (t (coreLetter h i) * t.τ) ^ e⟩ := by
    rw [heisF_deltaBlockAt t x y E E₂ hwild hτ hE i]
    refine HeisLift.ext ?_ ?_ ?_ rfl
    · show e • (x (coreLetter h i) + x .tau) = _
      rw [hxτ, add_zero]
      exact nsmul_self_of_odd hA₂ hodd _
    · show e • (y (coreLetter h i) + y .tau) = _
      rw [hyτ, add_zero]
      exact nsmul_self_of_odd ElemDual.add_self_eq_zero hodd _
    · show e • y (coreLetter h i) (x .tau)
          + (e.choose 2) • ((y (coreLetter h i) + y .tau)
              (x (coreLetter h i) + x .tau)) = _
      rw [hxτ, hyτ, map_zero, smul_zero, zero_add,
        nsmul_zmod2_even (choose_two_even_of_mod_four he)]
  have hinv : heisEvalZ ⇑t x y E E₂ (.inv (.gen (coreLetter h i)))
      = ⟨-x (coreLetter h i), -y (coreLetter h i),
          y (coreLetter h i) (x (coreLetter h i)), (t (coreLetter h i))⁻¹⟩ := by
    rw [heisEvalZ_inv, heisEvalZ_gen]
    refine HeisLift.ext ?_ ?_ ?_ rfl
    · show -((t (coreLetter h i))⁻¹ • x (coreLetter h i)) = _
      rw [mem_trivAct.mp (inv_mem (trivAct_coreLetter t hwild i))]
    · show -((t (coreLetter h i))⁻¹ • y (coreLetter h i)) = _
      rw [smul_elemDual_of_trivial (mem_trivAct.mp (inv_mem (trivAct_coreLetter t hwild i)))]
    · show (0 : ZMod 2) + y (coreLetter h i) (x (coreLetter h i)) = _
      rw [zero_add]
  rw [show deltaCert h i
      = PWord.mul (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau]))
          (PWord.mul (.inv (.gen (coreLetter h i))) PWord.one) from rfl,
    heisEvalZ_mul, heisEvalZ_mul, heisEvalZ_one, mul_one, hblk, hinv]
  refine ⟨?_, ?_, ?_⟩
  · show x (coreLetter h i) + ((t (coreLetter h i) * t.τ) ^ e) • (-x (coreLetter h i)) = 0
    rw [hbase, add_neg_cancel]
  · show y (coreLetter h i) + ((t (coreLetter h i) * t.τ) ^ e) • (-y (coreLetter h i)) = 0
    rw [smul_elemDual_of_trivial hbase, add_neg_cancel]
  · show (0 : ZMod 2) + y (coreLetter h i) (x (coreLetter h i))
        + y (coreLetter h i) (((t (coreLetter h i) * t.τ) ^ e) • (-x (coreLetter h i))) = 0
    rw [hbase, map_neg, CharTwo.neg_eq, zero_add, CharTwo.add_self_eq_zero]

/-- The `δ`-letter's base acts trivially, at every class — the hypothesis
`heisConjR_mem_heisTrivial` needs to dismiss the *conjugated* factors. -/
theorem heisF_deltaCert_trivAct (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hτ : ∀ v : A, t.τ • v = v) (i : Fin 3) (v : A) :
    (heisEvalZ ⇑t x y E E₂ (deltaCert h i)).g • v = v := by
  have hi := mem_trivAct.mp (trivAct_coreLetter t hwild i)
  rw [show deltaCert h i
      = PWord.mul (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau]))
          (PWord.mul (.inv (.gen (coreLetter h i))) PWord.one) from rfl,
    heisEvalZ_mul, heisEvalZ_mul, heisEvalZ_one, mul_one, HeisLift.mul_g]
  refine mem_trivAct.mp (mul_mem ?_ ?_) v
  · rw [PWord.omega2Pow, heisEvalZ_profPow, heisF_deltaInnerAt t x y E E₂ hwild i, heisZpow_g]
    refine zpow_mem (mem_trivAct.mpr fun w => ?_) _
    show (t (coreLetter h i) * t.τ) • w = w
    rw [mul_smul, hτ, hi]
  · rw [heisEvalZ_inv, HeisLift.inv_g, heisEvalZ_gen]
    exact inv_mem (trivAct_coreLetter t hwild i)

/-- **The `𝓔`-correction block is trivial at second order on the wild block** — every one of
its four conjugated `δ`-factors is (`heisConjR_mem_heisTrivial`).  S4.1's finding (i) in Lean:
at `P = 1` the correction is invisible, so the compact-`M` Stokes row *is* the compact-`N`
row. -/
theorem heisF_eRevW_trivial (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) (hτ : ∀ v : A, t.τ • v = v)
    (hxτ : x .tau = 0) (hyτ : y .tau = 0) {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    heisEvalZ ⇑t x y E E₂ (eRevW α h) ∈ heisTrivial A C := by
  have hδ : ∀ i : Fin 3, heisEvalZ ⇑t x y E E₂ (deltaCert h i) ∈ heisTrivial A C :=
    heisF_deltaCert_trivial t x y E E₂ hA₂ hwild hτ hxτ hyτ hE he
  have hfac : ∀ (i : Fin 3) (k : ℤ),
      heisEvalZ ⇑t x y E E₂ (.conj (deltaCert h i) (.zpow sigma2W k)) ∈ heisTrivial A C := by
    intro i k
    rw [heisEvalZ_conj]
    exact heisConjR_mem_heisTrivial (heisF_deltaCert_trivAct t x y E E₂ hwild hτ i) (hδ i)
  rw [show eRevW α h
      = PWord.mul (.conj (deltaCert h 1) (.zpow sigma2W (2 * (mOf α : ℤ))))
          (PWord.mul (.conj (deltaCert h 1) (.zpow sigma2W (mOf α : ℤ)))
            (PWord.mul (.conj (deltaCert h 0) (.zpow sigma2W (mOf α : ℤ)))
              (PWord.mul (deltaCert h 0) PWord.one))) from rfl,
    heisEvalZ_mul, heisEvalZ_mul, heisEvalZ_mul, heisEvalZ_mul, heisEvalZ_one, mul_one]
  exact mul_mem (hfac 1 _) (mul_mem (hfac 1 _) (mul_mem (hfac 0 _) (hδ 0)))

end StokesRows

end GQ2.Dyadic.Certificates.MCompact

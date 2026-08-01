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

## 3. The Hessian layer: both projector normal forms

WW4's `compactM_P1_certificate` and `compactM_P0_certificate` already certify the two frozen
**endpoints** (`q(c₀)+b_q(c₀,c₁)` with the identity CoV; `q(c₁)+b_q(c₀,c₁)` with the `(c₀,c₁)`
block-swap CoV).  What this file adds on the word side is the κ⁰ **slice calculus for this row**
and the projector mechanism itself:

* `hessSlice_sq`, `hessSlice_odd_pow`, `hessSlice_mul_incl` — the extension arithmetic the
  compact-`M` letters need (the pilot needed none of it: its boundary block sat entirely on the
  `C`-line);
* `factorSet_m_zpow_even` — **no `m`-charge survives**, and for a structural reason.  Commuting
  a slice past `σ₂^k` costs the correction `m_{σ₂^k}`; under `hS₂` eq. (60) gives
  `m_{g·g}(w) = m_g(g·w) + m_g(w) = 2·m_g(w) = 0`, so every **even** σ₂-power is `m`-free — and
  every σ₂-power in `R_{M,0}` is even, because `m = 2^{α−1}` with `α ≥ 2`.  No untwisted-
  refinement hypothesis is needed: the same evenness that kills the σ₂-jets at Stokes level
  kills the σ₂-charges here;
* `hessLine_slice_comm` / `hessM_line_comm` — the resulting gate-E commutation, which is what
  lets the C-line factors cancel by the power balance `−2·2^{α−1} + 2^α = 0` without disturbing
  the slice letters;
* **the two projector branches of the `δ`-letter**, which is where `d_i = (1 + P) c_i` actually
  lives.  `P` is the `ω₂`-norm projector `N_T`, and the branches are stated exactly where WM0-b
  states them — as a hypothesis on the evaluated `ω₂`-block.  `hessDeltaCert_P1`: the block
  returns the slice letter, so `δ_i = x_i x_i⁻¹ = 1` and `d_i = 0` — S4.1's finding (i), "the
  correction is invisible exactly when the projector is 1", and the reason
  `compactM_P1_certificate` *is* `compactN_certificate`.  `hessDeltaCert_P0`: the block is
  trivial, so `δ_i = x_i⁻¹` and `d_i = c_i` — the ramified reading (WM0-b's `hTodd`/`hτfpf`
  class).  `hessDeltaBlock_P1` **discharges** the `P = 1` hypothesis at `u = 1` and the honest
  class `e ≡ 1 (mod 4)`, so the branch is not vacuous.

⚠ **Residual, stated plainly.**  The final *assembly* — a single `hessRelZ_mCompact_P{0,1}`
equating the whole word's evaluated fibre to `q(c₀)+b_q(c₀,c₁)+Σ_j b_q(dⱼ,eⱼ)` resp.
`q(c₁)+b_q(c₀,c₁)+Σ_j b_q(dⱼ,eⱼ)` — is **not** in this file.  Every ingredient is (factor by
factor: `A₀² = ι(q c₀)·σ₂^{−2m}` from `hessSlice_sq`; `[A₀,x₁] = ι(b_q(c₀,c₁))` from
`hessSlice_commR` once the central `σ₂`-half is transported out; `σ₂^{2m}` cancelling the
former's C-line by the balance; `J₂` dying on the `C`-line at `v(x₂) = 0` exactly as in the
pilot; the `𝓔`-block trivial at `P = 1` and `ι(q c₀ + q c₁)` at `P = 0` by two applications of
`hessSlice_sq`; the handle tail via the pilot's `hess_handlesW_eval`), and the arithmetic is
checked on paper — at `P = 0` the block contributes `q(c₀)+q(c₁)`, which turns the core's
`q(c₀)+b_q(c₀,c₁)` into `q(c₁)+b_q(c₀,c₁)`, i.e. **the block swap is what the correction block
performs**.  What is missing is one transport lemma, `commR (a·L) b = commR a b` for `L`
commuting with `a` and `b`, and the bookkeeping that chains the six factors.  It is a
half-day's work on top of what is here, and it is the first thing a follow-on should do.

Note also that this whole layer is stated at the `hS₂` class (`W = 1` on `V`).  At general `W`
the endpoint needs the compact-`M` **marked** change of variables, which freeze row 4 flags as
an open input (errata item 3, "missing from the packet/drafts") — so it stays an explicit-datum
binder here, exactly as the lane spec mandates.  The order-rejection of §4 below is
deliberately *not* subject to that restriction: it is proved at general `W`, and must be, since
`W = 1` is precisely the blind case.

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

**Reused from the pilot, not re-derived** (the file imports `GQ2.Dyadic.Certificates.N0`
deliberately, as WM0-b imports `N0Fox`): the boundary block's two factors
(`Certificates.heisF_invConjX2`, `Certificates.heisF_deltaBlock`), the handle rows
(`heisF_handlesW_mem/_z`), `heisEps_handlesW`, `heisEps_of`, the `(1+S)`-atom dichotomy
`isUnit_onePlusSEnd_iff`, the graph-type marking `hessMark`, and the WWH toolkit in
`Word/Stokes.lean`.  ⚠ **One WW API finding**: the pilot's `heisF_deltaInner`/`heisF_deltaBlock`
are hardwired at `coreLetter h 2` — compact `N` has a single `δ`-letter — so the compact-`M`
correction block, which carries `δ₀` and `δ₁`, forced index-generic restatements
(`heisF_deltaInnerAt`, `heisF_deltaBlockAt`).  Those two belong in the WW toolkit; every later
`-c` lane with more than one `δ`-letter (WNP-c, WMP-c) will need them.

## Axiom state (audited; `#print axioms` run in a scratch file, not committed)

Zero `sorryAx`, zero `native_decide`, and **no `GQ2.AbsGalQ2` B-axiom leaks** through either
import chain.  All twenty headlines — `heisZ_mCompact_res_one`, `heisZ_mCompact_wild_block`,
`mCompact_isStokesEndpoint`, `mCompact_stokesDuality`, `sqrtTwo_scalarGram`,
`sqrtTwo_scalarGram_three`, `sqrtFive_scalarGram`, `heisF_eRevW_trivial`, `hessDeltaBlock_P1`,
`hessDeltaCert_P1`, `hessDeltaCert_P0`, `factorSet_m_zpow_even`, `hessSlice_rev4_fib`,
`swapDifference_formula`, `swapDifference_zero_of_P1`, `swapDifference_zero_of_trivial_W`,
`fifthRoot_separates`, `fifthRoot_orders_differ`, `mCompact_gauss_pow` and
`mCompact_P0_endpoint_gaussSum` — print exactly the standard three
`[propext, Classical.choice, Quot.sound]`.  The census stays at eleven.
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

/-! ### The assembled compact-`M` second-order row -/

/-- **The compact-`M` second-order (Stokes) row at the honest resolver class.**

```
y₀(a₀) ⊕ (y₀(a₁) + y₁(a₀)) ⊕ (y_σ(a₂) + y₂(a_σ) + y₂((1+S)a₂)) ⊕ Σ_j planes
```

Reading, block by block: the `x₀`-diagonal from `A₀²`, the `(A₀,x₁)` cross, the boundary block
`J₂` — the pilot's, verbatim, with the same `(1+S)`-atom — and the `h` identity-operator
hyperbolic planes.  `σ₂^{2m}` and `E_m^rev` are both **absent**, for two different reasons: the
first is killed by the doubled power balance (`heisZ_sigma2Pow_two_mul`), the second by the
`P = 1` projector (`heisF_eRevW_trivial`).

⚠ Deviation from the pilot: the assembled row is stated at `e ≡ 1 (mod 4)`, not exact in `e`.
Exactness in the resolver survives one level down, in `heisF_j2W`; it cannot survive assembly,
because the correction block is only trivial at the honest class (at a general odd `e` it
carries the charge `C(e,2)•y_i(a_i)` per `δ`-letter).  The compact-`N` row had no correction
block and so stayed exact after assembly. -/
theorem heisZ_mCompact_res_one (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) (hτ : ∀ v : A, t.τ • v = v)
    (hS₂ : ∀ v : A, (sigma2Z t x y E E₂).g • v = v) (hα : 2 ≤ α)
    (hxτ : x .tau = 0) (hyτ : y .tau = 0) {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    (heisEvalZ ⇑t x y E E₂ (mCompactW α h)).z
      = y (coreLetter h 0) (x (coreLetter h 0))
        + (y (coreLetter h 0) (x (coreLetter h 1)) + y (coreLetter h 1) (x (coreLetter h 0)))
        + (y .sigma (x (coreLetter h 2)) + y (coreLetter h 2) (x .sigma)
            + y (coreLetter h 2) (x (coreLetter h 2) + t.σ • x (coreLetter h 2)))
        + ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  have e1 := heisF_leadingSquare t x y E E₂ hA₂ hwild hS₂ hα
  have e2 := heisF_leadingComm t x y E E₂ hA₂ hwild hS₂ hα
  have e3 := heisZ_sigma2Pow_two_mul t x y E E₂ hA₂ hS₂ hα
  have e4 := heisF_j2W t x y E E₂ hwild hτ hE
  have e5 := heisF_eRevW_trivial (α := α) t x y E E₂ hA₂ hwild hτ hxτ hyτ hE he
  have e6mem := heisF_handlesW_mem t x y E E₂ hwild
  have e6z := heisF_handlesW_z t x y E E₂ hwild
  have h1jz : heisEvalZ ⇑t x y E E₂ (.zpow (a0W α h) 2) ∈ heisJetZero A C := by
    rw [e1]; exact ⟨rfl, rfl⟩
  have h2jz : heisEvalZ ⇑t x y E E₂ (.comm (a0W α h) (.gen (coreLetter h 1)))
      ∈ heisJetZero A C := by rw [e2]; exact ⟨rfl, rfl⟩
  have h3jz : heisEvalZ ⇑t x y E E₂ (.zpow sigma2W (2 * (mOf α : ℤ))) ∈ heisJetZero A C := by
    rw [e3]; exact ⟨rfl, rfl⟩
  rw [mCompactW, heisEvalZ_prodList, List.map_append, List.prod_append,
    heisEvalZ_handleTailW t x y E E₂]
  simp only [mFactors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [heisMul_z_of_a_eq_zero _ _ e6mem.1, heisJetZero_mul_z h1jz, heisJetZero_mul_z h2jz,
    heisJetZero_mul_z h3jz, heisMul_z_of_a_eq_zero _ _ e5.1, e5.2.2, add_zero, e1, e2, e3, e4,
    e6z]
  dsimp only
  simp only [hxτ, hyτ, add_zero, map_zero, zero_add,
    nsmul_zmod2_even (choose_two_even_of_mod_four he),
    nsmul_zmod2_odd (odd_of_mod_four_eq_one he), map_add]
  abel

/-- **The rank-3 wild core** of the compact-`M` row: on offsets supported in the wild letters,
the `(x₀,x₁)` unimodular plane plus the `x₂`-atom `y₂((1+S)a₂)` — the *same* three core atoms as
the pilot's, with the third invertible exactly on `V^S = 0` (`isUnit_onePlusSEnd_iff`, which the
compact-`M` lane inherits rather than restates). -/
theorem heisZ_mCompact_wild_block (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) (hτ : ∀ v : A, t.τ • v = v)
    (hS₂ : ∀ v : A, (sigma2Z t x y E E₂).g • v = v) (hα : 2 ≤ α)
    (hxσ : x .sigma = 0) (hxτ : x .tau = 0) (hyσ : y .sigma = 0) (hyτ : y .tau = 0)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    (heisEvalZ ⇑t x y E E₂ (mCompactW α h)).z
      = y (coreLetter h 0) (x (coreLetter h 0))
        + (y (coreLetter h 0) (x (coreLetter h 1)) + y (coreLetter h 1) (x (coreLetter h 0)))
        + y (coreLetter h 2) (x (coreLetter h 2) + t.σ • x (coreLetter h 2))
        + ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  rw [heisZ_mCompact_res_one t x y E E₂ hA₂ hwild hτ hS₂ hα hxτ hyτ hE he, hxσ, hyσ]
  simp only [ElemDual.zero_apply, map_zero, add_zero, zero_add]

end StokesRows

/-! ## The resolved relator family and the endpoint condition

The two-relator family `⟨σ, τ, x₀, …, x_{2h+2} ∣ τ^σ(τ^q)⁻¹, R_{M,0}⟩` resolved at the constant
representative `e`, in WM0-b's Jacobian row order.

The endpoint proof is **cheaper than the pilot's**, and structurally so: on the abelianized
mod-2 exponent vector every compact-`M` factor except `J₂` dies for a *syntactic* reason —
`A₀²` is a square, `[A₀,x₁]` a commutator, `σ₂^{2m}` an even power, `H_h` a product of
commutators, and `E_m^rev` carries each `δ`-letter exactly **twice** (conjugation is invisible
in an abelian target).  So the traced vector of the compact-`M` word *is* the traced vector of
the compact-`N` word's boundary block, and the endpoint condition reduces to the pilot's
`τ`/`x₂` bookkeeping with no `α`- or `m`-dependence at all. -/

section Family

variable {α h q e : ℕ}

/-- **The resolved compact-`M` relator family** — tame relator first, branch word second. -/
noncomputable def mCompactFam (α h q e : ℕ) : Fin 2 → FreeGroup (Generator (2 + 2 * h)) :=
  ![heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 + 2 * h) q),
    heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (mCompactW α h)]

@[simp] theorem mCompactFam_zero :
    mCompactFam α h q e 0
      = heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 + 2 * h) q) := rfl

@[simp] theorem mCompactFam_one :
    mCompactFam α h q e 1
      = heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (mCompactW α h) := rfl

/-- Every element of the traced target `Multiplicative (ZMod 2)` is an involution. -/
theorem mult_zmod2_sq (u : Multiplicative (ZMod 2)) : u * u = 1 := by
  revert u; decide

/-- Squares are invisible to the traced mod-2 exponent vector. -/
theorem heisEps_sq {ι : Type*} [DecidableEq ι] (i : ι) (g : FreeGroup ι) :
    heisEps i (g ^ (2 : ℤ)) = 1 := by
  rw [map_zpow, zpow_two, mult_zmod2_sq]

/-- So are even powers. -/
theorem heisEps_even_zpow {ι : Type*} [DecidableEq ι] (i : ι) (g : FreeGroup ι) (k : ℤ) :
    heisEps i (g ^ (2 * k)) = 1 := by
  rw [mul_comm, zpow_mul, heisEps_sq]

/-- The `𝓔`-block is invisible to the traced vector: each `δ`-letter occurs **twice**, and
conjugation is invisible in an abelian target. -/
theorem heisEps_eRevW (E' : Zhat → ℤ) (E₂' : ℤ_[2] → ℤ) (i : Generator (2 + 2 * h)) :
    heisEps i (PWord.evalZ FreeGroup.of E' E₂' (eRevW α h)) = 1 := by
  have hconj : ∀ (j : Fin 3) (k : ℤ),
      heisEps i (PWord.evalZ FreeGroup.of E' E₂' (.conj (deltaCert h j) (.zpow sigma2W k)))
        = heisEps i (PWord.evalZ FreeGroup.of E' E₂' (deltaCert h j)) := by
    intro j k
    rw [PWord.evalZ_conj, map_conjR, conjR_eq_self_of_comm]
  rw [show eRevW α h
      = PWord.mul (.conj (deltaCert h 1) (.zpow sigma2W (2 * (mOf α : ℤ))))
          (PWord.mul (.conj (deltaCert h 1) (.zpow sigma2W (mOf α : ℤ)))
            (PWord.mul (.conj (deltaCert h 0) (.zpow sigma2W (mOf α : ℤ)))
              (PWord.mul (deltaCert h 0) PWord.one))) from rfl]
  simp only [PWord.evalZ_mul, PWord.evalZ_one, map_mul, mul_one, hconj]
  rw [show ∀ u v : Multiplicative (ZMod 2), u * (u * (v * v)) = (u * u) * (v * v) from
      fun u v => by rw [mul_assoc], mult_zmod2_sq, mult_zmod2_sq, one_mul]

/-- **The endpoint condition holds at every compact-`M` instance** (`α ≥ 1`, any `h`, `q` even,
`e` odd).  Only `J₂` and the tame relator reach the traced vector; the per-letter coefficients
are the pilot's `1−q+e` on `τ` and `e−1` on `x₂`, both even. -/
theorem mCompact_isStokesEndpoint (hq : Even q) (he : Odd e) :
    IsStokesEndpoint (mCompactFam α h q e) := by
  intro i
  rw [Fin.sum_univ_two, mCompactFam_zero, mCompactFam_one]
  have htame : heisEps i (heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ))
      (tameRelW (2 + 2 * h) q))
      = heisEps i (FreeGroup.of Generator.tau)
        * (heisEps i (FreeGroup.of Generator.tau) ^ (q : ℤ))⁻¹ := by
    rw [tameRelW, heisToFree, PWord.evalZ_mul, PWord.evalZ_conj, PWord.evalZ_inv,
      PWord.evalZ_zpow, PWord.evalZ_gen, PWord.evalZ_gen, map_mul, map_conjR,
      conjR_eq_self_of_comm, map_inv, map_zpow]
  have hwild : heisEps i (heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (mCompactW α h))
      = (heisEps i (FreeGroup.of (coreLetter h 2)))⁻¹
        * (heisEps i (FreeGroup.of (coreLetter h 2))
            * heisEps i (FreeGroup.of Generator.tau)) ^ (e : ℤ) := by
    rw [mCompactW, heisToFree, PWord.evalZ_prodList, List.map_append, List.prod_append]
    simp only [mFactors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      map_mul]
    rw [PWord.evalZ_zpow, heisEps_sq, PWord.evalZ_comm, monoidHom_commR_eq_one,
      PWord.evalZ_zpow, heisEps_even_zpow, heisEps_eRevW,
      show ((handleTailW h).map (PWord.evalZ FreeGroup.of
          (fun _ => (e : ℤ)) (fun _ => (e : ℤ)))).prod
        = PWord.evalZ FreeGroup.of (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (handlesW h) by
        cases h with
        | zero => rfl
        | succ n => simp only [handleTailW, List.map_cons, List.map_nil, List.prod_cons,
            List.prod_nil, mul_one],
      handlesW_eq, Certificates.heisEps_handlesW]
    simp only [one_mul, mul_one]
    rw [show j2W h = PWord.mul (.inv (.conj (.gen (coreLetter h 2)) (.gen .sigma)))
        (PWord.mul (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau]))
          PWord.one) from rfl]
    rw [PWord.evalZ_mul, PWord.evalZ_mul, PWord.evalZ_one, mul_one, map_mul,
      PWord.evalZ_inv, PWord.evalZ_conj, PWord.evalZ_gen, PWord.evalZ_gen, map_inv,
      map_conjR, conjR_eq_self_of_comm, PWord.omega2Pow, PWord.evalZ_profPow, map_zpow,
      PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, PWord.evalZ_mul,
      PWord.evalZ_mul, PWord.evalZ_gen, PWord.evalZ_gen, PWord.evalZ_one, mul_one, map_mul]
  rw [htame, hwild]
  simp only [Certificates.heisEps_of, toAdd_mul, toAdd_inv, toAdd_zpow, toAdd_ofAdd]
  rw [zsmul_natCast_zmod2_even hq, zsmul_natCast_zmod2_odd he, CharTwo.neg_eq, CharTwo.neg_eq]
  abel_nf
  simp [CharTwo.two_eq_zero]

/-- The `√2` instance pin: `(α, h, q, e) = (3, 0, 2, 3)`. -/
theorem sqrtTwo_isStokesEndpoint : IsStokesEndpoint (mCompactFam 3 0 2 3) :=
  mCompact_isStokesEndpoint (by decide) (by decide)

/-- The `√5` instance pin: `(α, h, q, e) = (2, 0, 4, 3)` — the unramified quadratic extension,
so `q_K = 4`. -/
theorem sqrtFive_isStokesEndpoint : IsStokesEndpoint (mCompactFam 2 0 4 3) :=
  mCompact_isStokesEndpoint (by decide) (by decide)

end Family

/-! ## The Stokes duality payload -/

section Duality

universe u

variable {C : Type*} [Group C]

/-- WW3's packet-Lem-5.1 engine at the compact-`M` family; per-simple-module duality stays the
hypothesis slot it is in the frozen `ℚ₂` chain. -/
theorem mCompact_stokesDuality {α h q e : ℕ} [Finite C] (t : Marking (2 + 2 * h) C)
    (hq : Even q) (he : Odd e)
    (hrt : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 + 2 * h) q) = 1)
    (hrw : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (mCompactW α h) = 1)
    (hsimp : ∀ (V : Type u) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V →
        StokesDuality ⇑t (mCompactFam α h q e) V)
    (A : Type u) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) : StokesDuality ⇑t (mCompactFam α h q e) A := by
  refine stokesDuality_of_simple ⇑t (mCompactFam α h q e) ?_
    (mCompact_isStokesEndpoint hq he) hsimp A hA₂
  intro k
  fin_cases k
  · exact (lift_heisToFree_eq_one_iff ⇑t _ _ _).mpr hrt
  · exact (lift_heisToFree_eq_one_iff ⇑t _ _ _).mpr hrw

end Duality

/-! ## The scalar certificate: the `√2` Gram matrices, by kernel `decide`

The cup–Bockstein comparison matrix (`stokesGram`) of the `√2` family (`α = 3`, `m = 4`,
`q_K = 2`) on the scalar module, at the packet column order `σ, τ, x₀, x₁, x₂`.  Two pins
differing **only** in the resolver class, as in the pilot: `e = 1` (the honest class for a
2-group target) and its `e = 3` twin, which makes ticket S1.T's mod-4 sensitivity a
kernel-checked matrix pair.  The `√5` twin (`α = 2`, `q_K = 4`) is pinned alongside — the two
displayed instances of freeze row 4. -/

section ScalarGram

/-- The trivial action for the scalar pins (WW3's `local instance` idiom — not exported). -/
local instance : DistribMulAction (Multiplicative (ZMod 2)) (ZMod 2) where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- The all-trivial (scalar/split) marking of the compact-`M` alphabet at `h = 0`. -/
def scalarMarkM : Marking 2 (Multiplicative (ZMod 2)) := Marking.ofLetters 1 1 ![1, 1, 1]

/-- The packet column order `σ, τ, x₀, x₁, x₂`. -/
def scalarLetterM : Fin 5 → Generator 2 := ![.sigma, .tau, .wild 0, .wild 1, .wild 2]

/-- The standard primal basis: a unit offset on one letter. -/
def scalarXM (p : Fin 5) : Generator 2 → ZMod 2 :=
  fun g => if g = scalarLetterM p then 1 else 0

/-- The standard dual basis: the identity functional on one letter. -/
noncomputable def scalarYM (p : Fin 5) : Generator 2 → ElemDual (ZMod 2) :=
  fun g => if g = scalarLetterM p then (AddMonoidHom.id (ZMod 2) : ElemDual (ZMod 2)) else 0

/-- **The `√2` scalar Gram at the honest resolver class** (`α = 3`, `q_K = 2`, `e = 1`):
Bockstein diagonals at `τ` and `x₀`, cup blocks `(σ,τ)`, `(σ,x₂)`, `(x₀,x₁)`.

⚠ **Finding — this is the pilot's matrix, entry for entry** (`sqrtNegTwo_scalarGram`).  The
scalar module is blind to everything that distinguishes compact `M` from compact `N`: the
`σ₂`-powers act trivially *and carry no jet* (`m` is even), so the `𝓔`-block's four factors are
four equal lifts whose six pair terms cancel, and `A₀²` produces the same `y₀(a₀)` that
`x₀^{2+2^α}` does.  The Gram-level twin of WM0-b's "the normal forms are literally the pilot's",
and the Lean shard of the archive's gate-G blindness row. -/
theorem sqrtTwo_scalarGram :
    stokesGram ⇑scalarMarkM (mCompactFam 3 0 2 1) scalarXM scalarYM
      = !![0,1,0,0,1; 1,1,0,0,0; 0,0,1,1,0; 0,0,1,0,0; 1,0,0,0,0] := by
  decide +kernel

/-- **The `e = 3` twin**: exactly the `{τ,x₂}²`-block moves with the resolver class — S1.T's
"the lift level is 4, not 2" as a kernel-checked matrix pair, and the reason the certificate
form `heisZ_mCompact_res_one` pins `e ≡ 1 (mod 4)`. -/
theorem sqrtTwo_scalarGram_three :
    stokesGram ⇑scalarMarkM (mCompactFam 3 0 2 3) scalarXM scalarYM
      = !![0,1,0,0,1; 1,0,0,0,1; 0,0,1,1,0; 0,0,1,0,0; 1,1,0,0,1] := by
  decide +kernel

/-- **The `√5` scalar Gram** (`α = 2`, `q_K = 4`, `e = 1`).  The `τ`-Bockstein diagonal is
**absent** here — `C(4,2) = 6` is even where the `√2` row's `C(2,2) = 1` is odd.  That single
entry is the entire `q_K`-sensitivity of the scalar comparison, and it lives in the *tame*
relator, not in the branch word: WM0-a's `astHash_q2_eq_q4` says `q_K` never reaches the word,
and this is that theorem's Gram-level shadow. -/
theorem sqrtFive_scalarGram :
    stokesGram ⇑scalarMarkM (mCompactFam 2 0 4 1) scalarXM scalarYM
      = !![0,1,0,0,1; 1,0,0,0,0; 0,0,1,1,0; 0,0,1,0,0; 1,0,0,0,0] := by
  decide +kernel

end ScalarGram

/-! ## The Hessian certificate: both projector normal forms

WW4's `compactM_P1_certificate` and `compactM_P0_certificate` already certify the two frozen
**endpoints**.  What this section supplies is the **word side**: the evaluated class-two value
of `R_{M,0}` at the graph-type κ⁰-marking, in each projector branch, landing on those endpoints
with the changes of variables the freeze mandates.

The marking is the pilot's `hessMark` (reused, not restated): `σ ↦ ((0,s))`, `τ ↦ ((0,u))` on
the κ-free `C`-line, wild letters on the Heisenberg slice, `x₂` carrying no primal letter.

**Why no `m`-charge survives** — the lane's cleanest structural gift.  Commuting a slice past
the `C`-line element `σ₂^k` costs the factor-set correction `m_{σ₂^k}`.  Under `hS₂` (σ₂ acts
trivially on `V`) eq. (60) gives `m_{g·g}(w) = m_g(g·w) + m_g(w) = 2·m_g(w) = 0`, so **every
even** σ₂-power is `m`-free; and every σ₂-power occurring in the word — `σ₂^{−m}` inside `A₀`
and `σ₂^{2m}` — is even, because `m = 2^{α−1}` with `α ≥ 2`.  So no untwisted-refinement
hypothesis is needed here: the same evenness that killed the σ₂-jets at Stokes level kills the
σ₂-charges at Hessian level, and the C-line factors then cancel by the packet's power balance
`−2·2^{α−1} + 2^α = 0`. -/

section Hessian

open GQ2.SectionSix GQ2.QuadraticFp2

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

include hdat in
/-- **Even σ₂-powers carry no factor-set correction**, given that σ₂ acts trivially: eq. (60)
at `g^j · g^j` folds to `2 · m_{g^j}` — zero in `ZMod 2`.  Stated for `ℤ`-powers because the
word spells `σ₂^{−m}` as well as `σ₂^{2m}`. -/
theorem factorSet_m_zpow_even {g : C} (hg : ∀ w : V, g • w = w) {k : ℤ} (hk : Even k)
    (w : V) : dat.m (g ^ k) w = 0 := by
  obtain ⟨j, rfl⟩ := hk
  have hj : ∀ w : V, (g ^ j) • w = w := fun w =>
    mem_trivAct.mp (zpow_mem (mem_trivAct.mpr hg) j) w
  rw [zpow_add g j j, hdat.m_mul, hj, CharTwo.add_self_eq_zero]

/-- **The `C`-line element of a trivially-acting, `m`-free base is central against the
slice.**  This is the gate-E commutation the compact-`M` word needs and the compact-`N` word
never did. -/
theorem hessLine_slice_comm {g : C} (hg : ∀ w : V, g • w = w) (hm : ∀ w : V, dat.m g w = 0)
    (v : V) (z : ZMod 2) :
    hessLine dat hdat g * hessSlice dat hdat v z
      = hessSlice dat hdat v z * hessLine dat hdat g := by
  refine WordCoh.CentExt.ext (Prod.ext ?_ ?_) ?_
  · show (0 : V) + g • v = v + (1 : C) • (0 : V)
    rw [hg, smul_zero, add_zero, zero_add]
  · show g * (1 : C) = (1 : C) * g
    rw [mul_one, one_mul]
  · show (0 : ZMod 2) + z + (dat.f 0 (g • v) + dat.m g v)
      = z + 0 + (dat.f v ((1 : C) • (0 : V)) + dat.m 1 (0 : V))
    rw [hdat.f_zero_left, hm, smul_zero, hdat.f_zero_right, hdat.m_one]
    simp only [add_zero, zero_add]

/-- A central factor just adds its charge to a slice. -/
theorem hessSlice_mul_incl (v : V) (z c : ZMod 2) :
    hessSlice dat hdat v z * WordCoh.CentExt.incl (kappa0Cocycle dat hdat) c
      = hessSlice dat hdat v (z + c) := by
  rw [show WordCoh.CentExt.incl (kappa0Cocycle dat hdat) c = hessSlice dat hdat 0 c from rfl,
    hessSlice_mul dat hdat, add_zero, hdat.f_zero_right, add_zero]

/-- **The slice square law**, charge-independent: `((v,1),z)² = ι(q v)`. -/
theorem hessSlice_sq (hV2 : ∀ v : V, v + v = 0) (v : V) (z : ZMod 2) :
    hessSlice dat hdat v z * hessSlice dat hdat v z
      = WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (q v) := by
  rw [hessSlice_mul dat hdat, hV2, hdat.f_diag]
  show hessSlice dat hdat 0 (z + z + q v) = _
  rw [CharTwo.add_self_eq_zero, zero_add]
  rfl

/-- **The odd slice power law**: `s^{2k+1} = ((v,1), z + k·q v)` — the `ω₂`-resolver form.
The `C(e,2)`-parity of the pilot's `heisF_deltaBlock`, in the κ⁰-extension. -/
theorem hessSlice_odd_pow (hV2 : ∀ v : V, v + v = 0) (v : V) (z : ZMod 2) (k : ℕ) :
    hessSlice dat hdat v z ^ (2 * k + 1) = hessSlice dat hdat v (z + k • q v) := by
  induction k with
  | zero => rw [Nat.mul_zero, Nat.zero_add, pow_one, zero_nsmul, add_zero]
  | succ j ih =>
      rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 by ring, pow_succ, pow_succ, ih,
        mul_assoc, hessSlice_sq dat hdat hV2, hessSlice_mul_incl dat hdat, succ_nsmul,
        ← add_assoc]

/-! ### The `δ`-letter in each projector branch

`P` is the `ω₂`-norm projector `N_T`, and the two branches are exactly its two values, stated
where WM0-b states them — as a hypothesis on the evaluated `ω₂`-block:

* `P = 1`: the block returns the slice letter, so `δ_i = x_i x_i⁻¹ = 1` and `d_i = 0`;
* `P = 0`: the block is trivial, so `δ_i = x_i⁻¹` and `d_i = c_i`.

Together these are the freeze's `d_i = (1 + P) c_i`, branch by branch.  `hessDeltaBlock_P1`
shows the `P = 1` hypothesis is *satisfied* (at `u = 1` and the honest class `e ≡ 1 (mod 4)`),
so the branch is not vacuous. -/

variable {h : ℕ}

/-- The `ω₂`-block of the `δ`-letter **returns the letter** when `τ` sits on the trivial line
and the resolver is in the honest class — the `P = 1` hypothesis, discharged. -/
theorem hessDeltaBlock_P1 (hV2 : ∀ v : V, v + v = 0) (s : C)
    (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) (i : Fin 3) :
    PWord.evalZ (WordCoh.lift (Certificates.hessMark s (1 : C) vv) (kappa0Cocycle dat hdat))
        E E₂ (PWord.omega2Pow (PWord.prodList [.gen (Words.coreLetter h i), .gen .tau]))
      = hessSlice dat hdat (vv (xIdx h i)) 0 := by
  obtain ⟨t, ht⟩ : ∃ t, e = 4 * t + 1 := ⟨e / 4, by omega⟩
  have hinner : PWord.evalZ (WordCoh.lift (Certificates.hessMark s (1 : C) vv)
      (kappa0Cocycle dat hdat)) E E₂ (PWord.prodList [.gen (Words.coreLetter h i), .gen .tau])
      = hessSlice dat hdat (vv (xIdx h i)) 0 := by
    rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, PWord.evalZ_mul,
      PWord.evalZ_mul, PWord.evalZ_gen, PWord.evalZ_gen, PWord.evalZ_one, mul_one,
      show WordCoh.lift (Certificates.hessMark s (1 : C) vv) (kappa0Cocycle dat hdat)
        Generator.tau = hessLine dat hdat 1 from rfl,
      show hessLine dat hdat (1 : C) = 1 from rfl, mul_one]
    rfl
  rw [PWord.omega2Pow, PWord.evalZ_profPow, hinner, hE, zpow_natCast, ht,
    show 4 * t + 1 = 2 * (2 * t) + 1 by ring, hessSlice_odd_pow dat hdat hV2,
    even_nsmul_eq_zero (fun a : ZMod 2 => CharTwo.add_self_eq_zero a) ⟨t, by ring⟩, add_zero]

/-- **`P = 1` ⇒ the `δ`-letter is trivial**: `d_i = (1 + P) c_i = 0`. -/
theorem hessDeltaCert_P1 (s u : C) (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) (i : Fin 3)
    (hP1 : PWord.evalZ (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat))
      E E₂ (PWord.omega2Pow (PWord.prodList [.gen (Words.coreLetter h i), .gen .tau]))
      = hessSlice dat hdat (vv (xIdx h i)) 0) :
    PWord.evalZ (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)) E E₂
        (deltaCert h i) = 1 := by
  rw [show deltaCert h i
      = PWord.mul (PWord.omega2Pow (PWord.prodList [.gen (Words.coreLetter h i), .gen .tau]))
          (PWord.mul (.inv (.gen (Words.coreLetter h i))) PWord.one) from rfl,
    PWord.evalZ_mul, PWord.evalZ_mul, PWord.evalZ_one, mul_one, hP1, PWord.evalZ_inv,
    PWord.evalZ_gen,
    show WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)
      (Words.coreLetter h i) = hessSlice dat hdat (vv (xIdx h i)) 0 from rfl,
    mul_inv_cancel]

/-- **`P = 0` ⇒ the `δ`-letter is the inverse slice letter**: `d_i = (1 + P) c_i = c_i`, with
the `q`-charge of inversion. -/
theorem hessDeltaCert_P0 (hV2 : ∀ v : V, v + v = 0) (s u : C)
    (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (i : Fin 3)
    (hP0 : PWord.evalZ (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat))
      E E₂ (PWord.omega2Pow (PWord.prodList [.gen (Words.coreLetter h i), .gen .tau])) = 1) :
    PWord.evalZ (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)) E E₂
        (deltaCert h i) = hessSlice dat hdat (vv (xIdx h i)) (q (vv (xIdx h i))) := by
  rw [show deltaCert h i
      = PWord.mul (PWord.omega2Pow (PWord.prodList [.gen (Words.coreLetter h i), .gen .tau]))
          (PWord.mul (.inv (.gen (Words.coreLetter h i))) PWord.one) from rfl,
    PWord.evalZ_mul, PWord.evalZ_mul, PWord.evalZ_one, mul_one, hP0, one_mul, PWord.evalZ_inv,
    PWord.evalZ_gen,
    show WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)
      (Words.coreLetter h i) = hessSlice dat hdat (vv (xIdx h i)) 0 from rfl,
    hessSlice_inv dat hdat hV2, zero_add]

end Hessian

/-! ## The order-rejection certificate (S4.1 §9.4)

The lane's headline.  WM0-a built the forward-order mutant `mFwdW`; WM0-b proved that the two
orders agree at first order, at both boundaries and on every finite 2-group target, and left
the rejection here — correctly, because the phenomenon is **second-order**.

What is proved: the frozen and forward words differ, in the class-two algebra, by exactly

```
Q(fwd) + Q(rev) = b_q(W d₀, d₀) + b_q(W d₁, d₁) + b_q((1 + W²) d₁, d₀)
```

with `W` = the `σ₂^m`-action and `d_i = (1 + P) c_i`.  Everything is 2-torsion, so the `+` on
the left *is* the difference — there are no signs in the identity.

**Bilinearity of the factor set** is assumed (`hbil`, additivity of `f` in the first slot;
second-slot additivity is then derived through `f_cocycle`).  This is not a restriction of
substance: the repo's own `f_cocycle` docstring records that *all* of the paper's concrete
factor sets — eqs. (75), (76), (73), (95) — are bilinear in the coordinates, and the archive's
own `swap_difference_form` computes with the polar **matrix**, i.e. bilinearly.  It is stated
rather than assumed silently because the identity genuinely uses it. -/

section OrderRejection

open GQ2.QuadraticFp2

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
  (hbil : ∀ v w x : V, dat.f (v + w) x = dat.f v x + dat.f w x)

include hdat hbil in
/-- Second-slot additivity, from first-slot additivity and the cocycle identity. -/
theorem factorSet_f_add_right (v w x : V) :
    dat.f v (w + x) = dat.f v w + dat.f v x := by
  have hc := hdat.f_cocycle v w x
  rw [hbil v w x] at hc
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hc

include hdat hbil in
/-- **Reversal adds the full polarization.**  For four Heisenberg-slice factors,

```
fib(p₁p₂p₃p₄) + fib(p₄p₃p₂p₁) = Σ_{i<j} b_q(bᵢ, bⱼ),
```

and the right-hand side is **charge-independent** — the four `z`'s and the four self-terms
cancel in pairs, so only the `κ`-symmetrization survives.  That is why the *difference* between
the two orders is proof-grade where neither individual value is: it never sees the bilinear
refinement, the class-two lift, or the choice of `κ_q⁰`. -/
theorem hessSlice_rev4_fib (b₁ b₂ b₃ b₄ : V) (z₁ z₂ z₃ z₄ : ZMod 2) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        (hessSlice dat hdat b₁ z₁ * (hessSlice dat hdat b₂ z₂ *
          (hessSlice dat hdat b₃ z₃ * hessSlice dat hdat b₄ z₄)))
      + WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        (hessSlice dat hdat b₄ z₄ * (hessSlice dat hdat b₃ z₃ *
          (hessSlice dat hdat b₂ z₂ * hessSlice dat hdat b₁ z₁)))
      = polar q b₁ b₂ + polar q b₁ b₃ + polar q b₁ b₄
        + polar q b₂ b₃ + polar q b₂ b₄ + polar q b₃ b₄ := by
  simp only [hessSlice_mul dat hdat, hessSlice_fib]
  rw [factorSet_f_add_right dat hdat hbil, factorSet_f_add_right dat hdat hbil,
    factorSet_f_add_right dat hdat hbil, factorSet_f_add_right dat hdat hbil,
    factorSet_f_add_right dat hdat hbil, factorSet_f_add_right dat hdat hbil]
  have p12 := hdat.f_polar b₁ b₂
  have p13 := hdat.f_polar b₁ b₃
  have p14 := hdat.f_polar b₁ b₄
  have p23 := hdat.f_polar b₂ b₃
  have p24 := hdat.f_polar b₂ b₄
  have p34 := hdat.f_polar b₃ b₄
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
    p12 + p13 + p14 + p23 + p24 + p34

include hdat hbil in
/-- **THE DIFFERENCE FORMULA** (packet S4.1 §9.4, freeze row 4's rejection of record), in the
class-two algebra:

```
Q(fwd) + Q(rev) = b_q(W d₀, d₀) + b_q(W d₁, d₁) + b_q((1 + W²) d₁, d₀).
```

The six pairs of `hessSlice_rev4_fib` collapse to three: `W`-invariance of `b_q` makes the
`(1,3)` and `(2,4)` pairs equal — they cancel in characteristic 2 — and merges `(2,3)` with the
surviving `(1,4)` into `b_q((1+W²)d₁, d₀)`, leaving `(1,2)` and `(3,4)` as the two diagonal
terms.  Charges are irrelevant throughout, which is the whole reason this is proof-grade. -/
theorem swapDifference_formula (hq : IsQuadraticFp2 q) (W : V → V)
    (hW : ∀ v w : V, polar q (W v) (W w) = polar q v w) (d₀ d₁ : V)
    (z₁ z₂ z₃ z₄ : ZMod 2) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        (hessSlice dat hdat (W (W d₁)) z₁ * (hessSlice dat hdat (W d₁) z₂ *
          (hessSlice dat hdat (W d₀) z₃ * hessSlice dat hdat d₀ z₄)))
      + WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        (hessSlice dat hdat d₀ z₄ * (hessSlice dat hdat (W d₀) z₃ *
          (hessSlice dat hdat (W d₁) z₂ * hessSlice dat hdat (W (W d₁)) z₁)))
      = polar q (W d₀) d₀ + polar q (W d₁) d₁ + polar q (d₁ + W (W d₁)) d₀ := by
  rw [hessSlice_rev4_fib dat hdat hbil, hW (W d₁) d₁, hW (W d₁) d₀, hW d₁ d₀,
    hq.polar_add_left]
  ring_nf
  simp [CharTwo.two_eq_zero]

include hdat hbil in
/-- **Corollary — `P = 1` is order-blind at second order.**  Every `d_i = (1 + P) c_i` is zero,
so the difference vanishes identically: the second-order continuation of WM0-b's
order-invisibility theorem chain, and the first half of the freeze's visibility criterion. -/
theorem swapDifference_zero_of_P1 (hq : IsQuadraticFp2 q) (W : V → V) (hW0 : W 0 = 0)
    (hW : ∀ v w : V, polar q (W v) (W w) = polar q v w) (z₁ z₂ z₃ z₄ : ZMod 2) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        (hessSlice dat hdat (W (W 0)) z₁ * (hessSlice dat hdat (W 0) z₂ *
          (hessSlice dat hdat (W 0) z₃ * hessSlice dat hdat 0 z₄)))
      + WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        (hessSlice dat hdat 0 z₄ * (hessSlice dat hdat (W 0) z₃ *
          (hessSlice dat hdat (W 0) z₂ * hessSlice dat hdat (W (W 0)) z₁)))
      = 0 := by
  rw [swapDifference_formula dat hdat hbil hq W hW 0 0, hW0, hW0, add_zero]
  simp [polar_zero_left q hq]

include hdat hbil in
/-- **Corollary — `W = 1` is order-blind too.**  The two diagonal terms die because `b_q` is
alternating, and the third dies because `1 + W² = 0`.  This is the second half of the freeze's
visibility criterion `(1 + P) ≠ 0 ∧ σ₂^m ≠ 1`, and it is why the `hS₂` class — where `σ₂` acts
trivially — can never separate the orders.  It is also why the fifth-root orbit is blind at
`α ≥ 3`: there `ord(σ₂) ∣ m`, so `W = 1`. -/
theorem swapDifference_zero_of_trivial_W (hq : IsQuadraticFp2 q)
    (hV2 : ∀ v : V, v + v = 0) (d₀ d₁ : V) (z₁ z₂ z₃ z₄ : ZMod 2) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        (hessSlice dat hdat d₁ z₁ * (hessSlice dat hdat d₁ z₂ *
          (hessSlice dat hdat d₀ z₃ * hessSlice dat hdat d₀ z₄)))
      + WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        (hessSlice dat hdat d₀ z₄ * (hessSlice dat hdat d₀ z₃ *
          (hessSlice dat hdat d₁ z₂ * hessSlice dat hdat d₁ z₁)))
      = 0 := by
  rw [hessSlice_rev4_fib dat hdat hbil, polar_self q hq hV2, polar_self q hq hV2]
  simp [CharTwo.add_self_eq_zero]

end OrderRejection

/-! ## The negative pin: the `F16` fifth-root orbit

The archive's `F16-fifth-root` orbit — the `(α, q_K) = (2, 2)` separating orbit of the S4.1
battery — carried into Lean and checked by kernel `decide`.

`V = 𝔽₁₆ = 𝔽₂[g]/(g⁴+g+1)` in the basis `(1, g, g², g³)`, so `(a,b,c,d) ↦ a + bg + cg² + dg³`:

* `T` = multiplication by the primitive fifth root `g³` — order 5, and
  `P = N_T = 1 + T + T² + T³ + T⁴ = 0`, so `d_i = (1+P) c_i = c_i` (the ramified reading);
* `W = σ₂^m` = the **squared Frobenius** `x ↦ x⁴` (`m = 2^{α−1} = 2`, `ord σ₂ = 4`), of order 2
  — so `1 + W² = 0` and the difference has the archive's *linear* shape;
* `q x = Tr_{𝔽₁₆/𝔽₂}(g · x⁵)`, the nonsingular `T`-invariant form; its zero set is `{0} ∪ μ₅`.

Everything a genuine instance owes is checked: `q` is quadratic and nonsingular, `q` is `T`- and
`W`-invariant, `T` has order 5, `P = 0`, and the factor set is a bilinear equivariant datum for
`q`.  `fifthRoot_orders_differ` is the **Lean-side rejection of the forward order**.

⚠ **The size wall, stated honestly.**  This orbit does **not** cover the two *displayed*
instances.  Per errata item 6 the fifth-root orbit separates only at `(α, q_K) = (2,2)`, while
√2 is `(3,2)` and √5 is `(2,4)`; at `α = 3` one has `ord(σ₂) = 4 ∣ m = 4`, so `W = 1` and
`swapDifference_zero_of_trivial_W` applies — the orbit is *provably* blind there, not merely
unchecked.  Both displayed instances need the `F256-seventeenth-root` orbit,
`dim_{𝔽₂} V = 8`.  The obstruction is **not** the difference evaluation (one vector) nor the
invariance checks (256 each), but `IsEquivariantFactorSet.f_cocycle` and
`IsQuadraticFp2.polar_add_*`, which are three-variable identities: `256³ ≈ 1.7 × 10⁷` kernel
evaluations apiece, against the `16³ = 4096` that makes this 4-dimensional pin affordable.  The
route is to replace those `decide`s with a **structural** lemma — every
`f v w = Σ_{i ≤ j} U_ij v_i w_j` is a bilinear equivariant factor set for its own diagonal, and
every such diagonal is quadratic — after which the dim-8 pin costs what this one costs.  That
lemma is a `GQ2/QuadraticFp2.lean` API item, not a word-lane item; it is recorded, not built,
here.  The proved general bound (a separating orbit needs `dim ≥ 2^α`) is why no cheaper orbit
exists. -/

section FifthRoot

open GQ2.QuadraticFp2

/-- `𝔽₁₆` as an `𝔽₂`-module, in the basis `(1, g, g², g³)`. -/
abbrev V16 : Type := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2

/-- `q x = Tr_{𝔽₁₆/𝔽₂}(g·x⁵)`, in coordinates.  Zero set `{0} ∪ μ₅`. -/
def q16 : V16 → ZMod 2 :=
  fun v => v.2.1 + v.2.2.1 + v.1 * v.2.2.2 + v.2.1 * v.2.2.1 + v.2.1 * v.2.2.2
    + v.2.2.1 * v.2.2.2

/-- `W = σ₂^m`: the squared Frobenius `x ↦ x⁴`, of order 2. -/
def W16 : V16 → V16 :=
  fun v => (v.1 + v.2.1 + v.2.2.1 + v.2.2.2, v.2.1 + v.2.2.2, v.2.2.1 + v.2.2.2, v.2.2.2)

/-- `T`: multiplication by the primitive fifth root of unity `g³`. -/
def T16 : V16 → V16 :=
  fun v => (v.2.1, v.2.1 + v.2.2.1, v.2.2.1 + v.2.2.2, v.1 + v.2.2.2)

/-- The upper-triangular bilinear refinement of `q16` (`f v v = q16 v` over `𝔽₂`). -/
def f16 : V16 → V16 → ZMod 2 :=
  fun v w => v.2.1 * w.2.1 + v.2.2.1 * w.2.2.1 + v.1 * w.2.2.2 + v.2.1 * w.2.2.1
    + v.2.1 * w.2.2.2 + v.2.2.1 * w.2.2.2

/-- The trivial `C`-action carrying the pin: `W` and `T` enter as plain operators (the
difference formula never touches the action), so the factor set may be taken untwisted. -/
local instance : DistribMulAction (Multiplicative (ZMod 2)) V16 where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- The equivariant factor-set datum of the pin: `f16` with no central correction. -/
def dat16 : FactorSet (Multiplicative (ZMod 2)) V16 where
  f := f16
  m _ _ := 0

theorem hdat16 : IsEquivariantFactorSet q16 dat16 := by
  constructor <;> decide

theorem hbil16 : ∀ v w x : V16, dat16.f (v + w) x = dat16.f v x + dat16.f w x := by decide

theorem hq16 : IsQuadraticFp2 q16 := by constructor <;> decide

theorem hns16 : Nonsingular q16 := by
  show ∀ v : V16, v ≠ 0 → ∃ w : V16, polar q16 v w ≠ 0
  decide

theorem hV2_16 : ∀ v : V16, v + v = 0 := by decide

/-- `q` is `W`-invariant, so `b_q` is — the hypothesis the difference formula consumes. -/
theorem hW16_invariant : ∀ v w : V16, polar q16 (W16 v) (W16 w) = polar q16 v w := by decide

/-- `W` has order 2: `1 + W² = 0`, which is why the archive records this orbit's difference as
a **linear** form. -/
theorem hW16_sq : ∀ v : V16, W16 (W16 v) = v := by decide

/-- `T` has order 5 — the primitive fifth root. -/
theorem hT16_order_five : ∀ v : V16, T16 (T16 (T16 (T16 (T16 v)))) = v := by decide

/-- `q` is `T`-invariant: a legal invariant form for the orbit. -/
theorem hT16_invariant : ∀ v : V16, q16 (T16 v) = q16 v := by decide

/-- **`P = N_T = 0`** on the whole orbit, so `d_i = (1 + P) c_i = c_i` — the projector half of
the freeze's visibility criterion, discharged. -/
theorem hP16_zero : ∀ v : V16, v + T16 v + T16 (T16 v) + T16 (T16 (T16 v))
    + T16 (T16 (T16 (T16 v))) = 0 := by decide

/-- The separating vector `c₀ = g³`. -/
def c16 : V16 := (0, 0, 0, 1)

/-- **The difference formula's right-hand side is nonzero on this orbit** — the negative pin,
at `d₀ = g³`, `d₁ = 0`.  Since `1 + W² = 0` here only the first diagonal term survives, and it
is `b_q(W g³, g³) = q(g¹⁰) = 1`. -/
theorem fifthRoot_separates :
    polar q16 (W16 c16) c16 + polar q16 (W16 0) 0 + polar q16 (0 + W16 (W16 0)) c16 = 1 := by
  decide

/-- **THE LEAN-SIDE REJECTION OF THE FORWARD ORDER.**  On the `F16` fifth-root orbit the two
orders of the `𝓔`-block give **different** class-two values, at every choice of the four
charges.

This is what WM0-a could not promise and WM0-b correctly deferred: gates A–E and G are blind to
the order, structurally, and so is the first Fox order — but the second order is not, and here
is the witness. -/
theorem fifthRoot_orders_differ (z₁ z₂ z₃ z₄ : ZMod 2) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat16 hdat16)
        (hessSlice dat16 hdat16 (W16 (W16 0)) z₁ * (hessSlice dat16 hdat16 (W16 0) z₂ *
          (hessSlice dat16 hdat16 (W16 c16) z₃ * hessSlice dat16 hdat16 c16 z₄)))
      ≠ WordCoh.CentExt.fib (c := kappa0Cocycle dat16 hdat16)
        (hessSlice dat16 hdat16 c16 z₄ * (hessSlice dat16 hdat16 (W16 c16) z₃ *
          (hessSlice dat16 hdat16 (W16 0) z₂ * hessSlice dat16 hdat16 (W16 (W16 0)) z₁))) := by
  intro hcon
  have hdiff := swapDifference_formula dat16 hdat16 hbil16 hq16 W16 hW16_invariant c16 0
    z₁ z₂ z₃ z₄
  rw [hcon, CharTwo.add_self_eq_zero, fifthRoot_separates] at hdiff
  exact absurd hdiff (by decide)

end FifthRoot

/-! ## The phase consumables, at **both** projector branches

WW4's `affinePhase` is `plusFormPhaseCover` on both compact-`M` rows — the two certificates
differ in their endpoint `Q` and in the change of variables, never in the phase cover, because
the `(c₀,c₁)` block swap is an isometry.  So the record leaves are the same four `SN`-valued
shapes on each branch: `G0 = 2^d`, packet Lem 6.1's translated sum, and the degree-`n`
magnitude `2^{n·d} = 2^{n·dim(V×V)/2}` — `standardNumerics n |>.gaussRam d`, positive sign,
which is the Lagrangian clause of the lane spec.  `n = 2` is the degree of both `ℚ₂(√2)` and
`ℚ₂(√5)`. -/

section Phase

open GQ2.SectionSix GQ2.QuadraticFp2

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  [Module (ZMod 2) V] [Fintype V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
  (hq : IsQuadraticFp2 q) (hns : Nonsingular q) {d : ℕ}
  (hcard : Fintype.card V = 2 ^ d)

/-- The `P = 1` branch's Gauss residue slot: `G0 = ε·2^m = 2^d` (`ε = +1`). -/
theorem mCompact_P1_G0 :
    (compactM_P1_certificate dat hdat hq hns hcard).affinePhase.G0 = 2 ^ d :=
  one_mul _

/-- The `P = 0` branch's Gauss residue slot — the **same** `G0`, because the block swap is an
isometry and the phase cover is shared. -/
theorem mCompact_P0_G0 :
    (compactM_P0_certificate dat hdat hq hns hcard).affinePhase.G0 = 2 ^ d :=
  one_mul _

include dat hdat hq hns hcard in
/-- **Packet Lem 6.1's output at the `P = 1` row**: a raw shift vector contributes exactly its
affine phase against `G0 = 2^d`. -/
theorem mCompact_P1_gauss_translate (y : V × V) :
    gaussSum (fun x => plusFormD q q x + polar (plusFormD q q) x y)
      = sign (plusFormD q q y) * 2 ^ d := by
  have h := (compactM_P1_certificate dat hdat hq hns hcard).affinePhase.gauss_translate y
  rw [mCompact_P1_G0 dat hdat hq hns hcard] at h
  exact h

include dat hdat hq hns hcard in
/-- **The degree-`n` Gauss magnitude in `SN`-shape**, `2^{n·d}` — with `dim_{𝔽₂}(V × V) = 2d`
this is `2^{n·dim/2}`, i.e. `standardNumerics n |>.gaussRam d` with positive sign. -/
theorem mCompact_gauss_pow (n : ℕ) :
    gaussSum (fun x : Fin n → V × V => ∑ i, plusFormD q q (x i)) = 2 ^ (n * d) :=
  (compactM_P1_certificate dat hdat hq hns hcard).affinePhase.gaussSum_pi_of_baseSign_one rfl n

include dat hdat hq hns hcard in
/-- The `ℚ₂(√2)` instance of the magnitude (`α = 3`, `m = 4`): `n = 2`. -/
theorem sqrtTwo_gauss_degree_two :
    gaussSum (fun x : Fin 2 → V × V => ∑ i, plusFormD q q (x i)) = 2 ^ (2 * d) :=
  mCompact_gauss_pow dat hdat hq hns hcard 2

include dat hdat hq hns hcard in
/-- The `ℚ₂(√5)` instance (`α = 2`, `m = 2`, `q_K = 4`): the same magnitude — the `q_K`
sensitivity of this row lives in the tame relator, not in the phase. -/
theorem sqrtFive_gauss_degree_two :
    gaussSum (fun x : Fin 2 → V × V => ∑ i, plusFormD q q (x i)) = 2 ^ (2 * d) :=
  mCompact_gauss_pow dat hdat hq hns hcard 2

include dat hdat hq hns hcard in
/-- **The `P = 0` endpoint has the same Gauss residue as the `P = 1` endpoint** — the block-swap
change of variables made numerical.  Freeze row 4's "the two rows are one plus form in two
coordinate systems", at the Gauss level. -/
theorem mCompact_P0_endpoint_gaussSum :
    gaussSum (fun p : V × V => q p.2 + polar q p.1 p.2) = 2 ^ d := by
  have h := (compactM_P0_certificate dat hdat hq hns hcard).endpoint_gaussSum
  rw [mCompact_P0_G0 dat hdat hq hns hcard] at h
  exact h

end Phase

/-! ## The word-side Hessian equations: landing on WW4's two endpoints -/

section HessianWord

open GQ2.SectionSix GQ2.QuadraticFp2

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
  {h α : ℕ} (s u : C) (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- Abbreviation for the evaluated marking. -/
private noncomputable abbrev mk :=
  WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)

/-- `σ₂` evaluates onto the `C`-line at the resolved 2-primary part of `σ`. -/
theorem hessM_sigma2W :
    PWord.evalZ (mk dat hdat s u vv) E E₂ sigma2W = hessLine dat hdat (s ^ E omega2) := by
  rw [sigma2W, PWord.omega2Pow, PWord.evalZ_profPow, PWord.evalZ_gen,
    show mk dat hdat s u vv Generator.sigma = hessLineHom dat hdat s from rfl, ← map_zpow]
  rfl

@[inherit_doc hessM_sigma2W]
theorem hessM_sigma2Pow (k : ℤ) :
    PWord.evalZ (mk dat hdat s u vv) E E₂ (.zpow sigma2W k)
      = hessLine dat hdat ((s ^ E omega2) ^ k) := by
  rw [PWord.evalZ_zpow, hessM_sigma2W,
    show hessLine dat hdat (s ^ E omega2) = hessLineHom dat hdat (s ^ E omega2) from rfl,
    ← map_zpow]
  rfl

variable (hS₂ : ∀ w : V, (s ^ E omega2) • w = w)

include hdat hS₂ in
/-- **The `σ₂`-line commutes with every slice, at every even power.**  Two facts meet here: the
`hS₂`-action is trivial, and `factorSet_m_zpow_even` kills the factor-set correction because the
power is even.  Every `σ₂`-power occurring in `R_{M,0}` — `σ₂^{−m}` inside `A₀` and `σ₂^{2m}` —
is even, since `m = 2^{α−1}` with `α ≥ 2`.

This is the gate-E commutation the compact-`M` word needs and the compact-`N` word never did,
and it is the step that lets the C-line factors cancel by the packet's power balance
`−2·2^{α−1} + 2^α = 0` without disturbing the slice letters. -/
theorem hessM_line_comm {k : ℤ} (hk : Even k) (w : V) (z : ZMod 2) :
    hessLine dat hdat ((s ^ E omega2) ^ k) * hessSlice dat hdat w z
      = hessSlice dat hdat w z * hessLine dat hdat ((s ^ E omega2) ^ k) :=
  hessLine_slice_comm dat hdat
    (fun v => mem_trivAct.mp (zpow_mem (mem_trivAct.mpr hS₂) k) v)
    (fun v => factorSet_m_zpow_even dat hdat hS₂ hk v) w z

end HessianWord

end GQ2.Dyadic.Certificates.MCompact

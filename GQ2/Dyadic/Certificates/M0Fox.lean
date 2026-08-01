/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Words.M0
import GQ2.Dyadic.Certificates.N0Fox

/-!
# Dyadic campaign, ticket WM0-b: the Fox certificate of the compact `M_α` branch word

Packet Def. 9.1 items (3)–(4) for **row 4 of the R5 selection freeze**, the compact-`M` relator
with the *reversed* `𝓔`-correction

```
A₀ = x₀⁻¹σ₂⁻ᵐ,  J₂ = x₂^{-σ}(x₂τ)^{ω₂},  E_m^rev = 𝓔(σ₂^m,σ₂^m;δ₀,δ₁),  m = 2^{α−1}
R_{M,0} = A₀² [A₀,x₁] σ₂^{2m} · J₂ · E_m^rev · H_h
```

sitting on WM0-a's word (`GQ2/Dyadic/Words/M0.lean`), WW1's Fox evaluator
(`GQ2/Dyadic/Word/Fox.lean`), WW2's certificate grammar (`GQ2/Dyadic/Word/FoxCert.lean`) and —
deliberately — the *pilot lane's* certificate file `GQ2/Dyadic/Certificates/N0Fox.lean`, because
the `x₂`-block of this word **is** the compact-`N` block (see "Shared with WC-N0" below).

## The rows

Notation: `S = σ`, `T = τ`, `S₂ = σ₂ = σ^{ω₂}` (WW2's `TameSym.sigma2` atoms), `P` = the
`ω₂`-norm projector (`TameSym.proj`), column order `σ, τ, x₀, x₁, x₂, handles`.

| relator | `σ` | `τ` | `x₀` | `x₁` | `x₂` | handles |
|---|---|---|---|---|---|---|
| tame `τ^σ(τ^q)⁻¹` | `S⁻¹(T−1)` | `S⁻¹ − N_q(T)` | `0` | `0` | `0` | `0` |
| wild `R_{M,0}` | `0` | `P·S₂^{−2m}` | `P·S₂^{−m} + P` | `P·S₂^{−m} + P·S₂^{−2m}` | `S⁻¹ + P` | `0` |

The wild row is `mCompactWildRow`, reproduced **entry for entry** from the frozen certificates
`M-compact-alpha{2,3,4}-h{0,1}-q{2,4}-v001` (whose printed `rows.wild.entries` at `α = 2` are
`sigma: 0`, `tau: P[T]S2^-4`, `x0: P[T]S2^-2 + P[T]`, `x1: P[T]S2^-2 + P[T]S2^-4`,
`x2: S^-1 + P[T]`), including the *print order* of the two-term entries.  The tame row is
literally the compact-`N` lane's (`Certificates.tameRow`): same tame relator, same `q_K`.

The three published specializations, and what each needs:

| class | assignment | wild row | Lean |
|---|---|---|---|
| unramified (general) | `P ↦ 1`, `T = 1` | `(0, S₂^{−2m}, S₂^{−m}+1, S₂^{−m}+S₂^{−2m}, S⁻¹+1)` | `foxD_mCompact_unram` |
| unramified **simple** | … and `S₂ = 1` | `(0, 1, 0, 0, S⁻¹+1)` | `foxD_mCompact_unram_simple` |
| ramified | `P ↦ 0`, `V^T = 0` | `(0, 0, 0, 0, −S⁻¹)` | `foxD_mCompact_ram` |
| split/scalar | `P ↦ 1`, `T = S = 1` | `(0, 1, 0, 0, 0)` | `foxD_mCompact_split` |

⚠ **`S₂ = 1` is a hypothesis, not an interpretation** (WW2's binding rule: "whether `S` (or
`S₂`) additionally acts trivially is a hypothesis of the instantiating theorem, not part of the
interpretation").  It is the Sage side's `specialize_unramified(simple=True)` clause, whose
justification is the *simple*-module lemma — inertia acts trivially, so the action factors
through the cyclic `⟨S⟩` of order `2^a·m'`; its Sylow `2`-subgroup acts on a nonzero
`𝔽₂`-space, hence has nonzero fixed points, which are `⟨S⟩`-stable, so simplicity forces the
`2`-part to act trivially — and `S₂ = S^{ω₂}` *is* that `2`-part.  `simple = False` keeps `S₂`,
which is exactly the general row above.  The compact-`N` row never met this because it carries
no `σ₂`-letter at all; this row carries four.

## Where each entry comes from (the frozen derivation, mechanised)

The word is a `prodList` of **five factors plus the handle tail**, and those factors do *not*
all act trivially — `A₀²` acts as
`S₂^{−2m}` and `σ₂^{2m}` as `S₂^{2m}` — so the compact-`N` shortcut
`foxD_prodList_of_trivial` is unavailable and each factor enters weighted by the **lower value
of its prefix** (`D(uv) = D(u) + ū·D(v)`, iterated).  That weighting is the whole story:

* **`A₀² `** (prefix `1`): the leading power contributes the operator **`1 + S₂^{−m}`** — the
  compact-`M` shape of a leading factor `2`, and literally `2` once `S₂ = 1`.  That is where
  the row's balanced pairs come from: `x₀` reads `P·(1 + S₂^{−m})` and `x₁` reads the twisted
  twin `P·(S₂^{−m} + S₂^{−2m})`.  In full,
  `−(1 + S₂^{−m})·a(x₀) − (1 + S₂^{−m})S₂^{−m}·𝒢_m` where
  `𝒢_k = (1 + S₂ + ⋯ + S₂^{k−1})·D(σ₂)` (`foxD_leadingSquare`).  `D(σ₂)` is **never computed**:
  it is the Sage engine's opaque atom `G[S;ω₂]` (`omega_proj`'s last branch — `σ` is
  unramified, so its `ω₂`-power is *not* a projector), and it cancels before the row is reached.
* **`[A₀,x₁]`** (prefix `S₂^{−2m}`): locally `(1 − S₂^{m})·a(x₁)`
  (`foxD_comm_of_trivial_right`), weighted to `S₂^{−2m}·a(x₁) − S₂^{−m}·a(x₁)`.  No `x₀`, no
  `σ`: the two `D(A₀)` copies of the commutator cancel.
* **`σ₂^{2m}`** (prefix `S₂^{−2m}`): `S₂^{−2m}·𝒢_{2m}`.  **This is the `σ`-column cancellation**
  (inside `foxD_mWordWith_core`): `𝒢_{2m} = 𝒢_m + S₂^m·𝒢_m` (`sigmaGeom_two_mul`), so the
  weighted contribution is `(S₂^{−2m} + S₂^{−m})·𝒢_m`, *identical* to the `A₀²` contribution —
  and it cancels **over `ℤ`**, without any characteristic-`2` hypothesis.  Mathematically this
  is the packet's power balance `−2·2^{α−1} + 2^α = 0` differentiated once.
* **`J₂`** (prefix `S₂^{−2m}·S₂^{2m} = 1`): `−S⁻¹·a(x₂) + P·(a(x₂) + a(τ))` — *the compact-`N`
  factors verbatim*: `foxD_j2W_unram`/`_ram` are proved by rewriting with WN0-b's own
  `foxD_invConjX2` and `foxD_deltaBlock_unram`/`_ram`, across the `coreLetter_eq` bridge.
* **`E_m^rev`** (prefix `1`): all four conjugated `δ`-letters act trivially, so
  `D(E_m^rev) = (S₂^{−2m}+S₂^{−m})·D(δ₁) + (S₂^{−m}+1)·D(δ₀)` with
  `D(δ_i) = (P+1)·a(x_i) + P·a(τ)` (`foxD_deltaC_unram`, `foxD_deltaC_ram`).
* **`H_h`** (prefix `1`): `0`, at every `h` — commutators of trivially-acting letters
  (`foxD_comm_of_trivial`, hoisted by WWH).  ⚠ At `h = 0` there is **no handle factor at all**
  (WM0-a deviation 1), so `foxD_handleTailW` is proved by cases and the `h ≥ 1` branch is the
  only one with content.

The `x₀`- and `x₁`-entries are then **pure `P`-multiples** because the `1`-part of the
`E_m^rev` coefficient `(P+1)` reproduces the `A₀²[A₀,x₁]` contribution exactly and
`X + (1+P)X = P·X` over `𝔽₂`; the `τ`-entry is `P·S₂^{−2m}` because `J₂`'s `P` cancels the `+P`
of the block's `P(S₂^{−2m}+1)`.  Those two steps — and only those — need `hV₂`.

## `E_m^rev` at first order: what is true

Stated honestly, because three different things are easy to conflate.

1. **The block is *not* zero at first order.**  `foxD_eRevW_unram` is `(S₂^{−2m}+1)·a(τ)`
   (nonzero as formal data) and `foxD_eRevW_ram` is
   `−(S₂^{−2m}+S₂^{−m})·a(x₁) − (S₂^{−m}+1)·a(x₀)`.  Deleting the block changes the row.
2. **It is invisible in each published specialization, for two *different* reasons.**  At
   `P = 1` its primal (`x₀`,`x₁`) offsets carry the factor `P+1 = 0` and its `τ`-contribution
   `(S₂^{−2m}+1)·a(τ)` dies on a *simple* unramified module (`S₂ = 1`); at `P = 0` its primal
   offsets survive but cancel the `A₀²[A₀,x₁]` contribution over `𝔽₂`.  That is the frozen
   certificate's note "the delta offsets carry the factor `(1 + P)` … invisible at first order
   in BOTH projector cases", made precise.
3. **The block *order* is first-order invisible** — `foxD_eFwdW_eq_eRevW`, hence
   `foxD_mFwdW_eq_mCompact` and equality of the evaluated row as a homomorphism
   (`foxDHom_mFwdW_eq_mCompact`): the four factors all act trivially, so the product rule
   degenerates to a plain sum and reordering is `add_comm`.  This is a **theorem**, not a
   docstring claim, and it is the Lean shard of S4.1's order-invisibility.  Per the dated
   2026-07-31 correction to the WM0 spec: the rejection of the forward order is **second
   order** (S4.1 §9.4's proof-grade difference formula in `(q, b_q, P, W)`, `W` = the action of
   `σ₂^m`), it is *not* a rank drop, and it is **not** finite-target detectable (F5 row C2 is
   pinned NOT-SEPARATED).  The Lean-side rejection is **WM0-c's**, not this file's; nothing
   below claims it.

## Shared with WC-N0 (the frozen note, mechanised)

The frozen certificate says *"the `x_2` block is the compact-N boundary factor `J_2`, so its
`1 − S^{-1}` term and its two one-operation normal forms are shared with packet row WC-N0"*.
This file proves that rather than restating it: it **imports** `Certificates.N0Fox` and

* proves `foxD_j2W_unram`/`_ram` by `exact`-ing `foxD_invConjX2` and
  `foxD_deltaBlock_unram`/`_ram` (the alphabets are the same and `MCompact.coreLetter` is `rfl`
  to `Words.coreLetter`, `mCompactWildRow_x2_eq_nCompactWildRow_x2`);
* reuses the tame relator `tameRelW`, its two rows and `tameRowCertUnram` unchanged;
* reuses the *normal forms* themselves — `mCompactUnramNormalForm = nCompactUnramNormalForm`
  and `mCompactRamNormalForm = nCompactRamNormalForm` are `rfl` — and with them
  `oneSubSInv`, `isUnit_oneSubSInvEnd_iff` (the `1 − S⁻¹` block is invertible iff `V^S = 0`),
  `neg_eq_self`, `sigmaAtom_mul`.

Consequently the **two one-op normal forms are the same two operations** as the pilot's, which
is what the frozen `operations` block records: `add_row(source 0, target 1, factor S)` in the
unramified branch and `scale_col(x2, unit S)` in the ramified one.

## The instances

`ℚ₂(√2)` is `(α, q_K) = (3, 2)` (`m = 4`), `ℚ₂(√5)` is `(α, q_K) = (2, 4)` (`m = 2`), and
`(α, h, q_K) = (2, 0, 2)` is the canonical engine instance whose digest
`7c9005f50f9e1d5d…` the freeze quotes for row 4.  All three are `h = 0`; the `α = 2, h = 1`
certificate is covered by the general-`h` theorems (nothing below is `h`-specific).

⚠ **No `α`-hypothesis is needed anywhere in this file.**  The compact-`N` row needed `1 ≤ α` to
know that `p_α = 2 + 2^α` is even; here the leading exponent is the literal `2`, and `α` enters
only through the *symbolic* `σ₂`-exponents `m = mOf α` and `2m`.  WM0-a's `1 ≤ α` is a Gate-C
hypothesis (`2m = 2^α`), not a first-order one; `even_mOf` (`2 ≤ α`) is Hessian data for WM0-c.
This is the compact-`M` analogue of WN0-b's "α ≥ 1 suffices at first order" finding, one step
stronger.

## Axiom state (recorded per WM0-b instructions; `#print axioms` run in a scratch file, not
committed)

**Audited 2026-08-01, all 96 named declarations of this file**: every one depends on a subset
of the standard axioms `[propext, Classical.choice, Quot.sound]` — 75 print exactly std-3, 16
print `[propext, Quot.sound]`, 4 print `[propext]`, and `tameRow_two_ne_four` (a kernel
`decide`) depends on **no axiom at all**.  Zero `sorryAx`, zero `Lean.ofReduceBool` (no
`native_decide`), and no `B`-axiom of the dyadic census leaks through the
`Words.M0 → TameBoundary → MarkedCore` import chain.  The census stays at **eleven**.

All 28 headlines print exactly std-3: `foxD_mWordWith_core`, `foxD_mCompact_core`,
`foxD_mCompact_unram`, `foxD_mCompact_unram_simple`, `foxD_mCompact_ram`,
`foxD_mCompact_split`, `foxD_mCompact_eq_nCompact_unram_simple`, `foxD_eRevW`,
`foxD_eRevW_unram`, `foxD_eRevW_ram`, `foxD_eFwdW_eq_eRevW`, `foxD_mFwdW_eq_mCompact`,
`foxDHom_mFwdW_eq_mCompact`, `foxDHom_mCompact_handleU_column`,
`foxDHom_mCompact_handleV_column`, `mCompactWildRow_toHom_apply`, the four published-row
certificates, the two Jacobian certificates and all six instance certificates.

## Implementation notes

**Not `module`-style, and forced**: `GQ2.Dyadic.Words.M0` is not `module`-style (it imports
F3's `TameBoundary`), and a `module` file may not import a non-`module` one — the WN0-a ruling
that `Words/` and `Certificates/` are plain-import layers.  `Certificates.N0Fox` is likewise
plain, so importing it is fine in this direction.

**Nested namespace `GQ2.Dyadic.Certificates.MCompact`**, following WM0-a's deviation 2: this
file and `N0Fox.lean` share the enclosing namespace and would otherwise collide on
`foxD_leadingComm`, `x2Idx`, and the row/normal-form names.  The real fix is the WAH alphabet
hoist; nesting is the minimal fix inside this ticket's one owned file.

**Hoist candidates for the cleanup queue** (lane-generic, introduced here, wanted by
WNP-b/WMP-b/WL-b which all have non-trivially-acting prefixes):
`foxD_comm_of_trivial_right`, `foxD_conj_of_trivial`, `foxD_prodList_pair`,
`evalFin_prodList_pair`, `trivAct_commR_right`, `geom_pow_smul_two_mul`, and the four-support
alphabet sum `sum_generator_quad`.  All of them belong beside WWH's
`foxD_prodList_of_trivial` in `GQ2/Dyadic/Word/Fox.lean`.
-/

namespace GQ2.Dyadic.Certificates.MCompact

open GQ2.FoxH GQ2.Dyadic.Words GQ2.Dyadic.Words.MCompact

/-! WM0-a's certificate `δ`-letter is renamed to `deltaCert` here, because the enclosing `GQ2`
namespace already declares a *peripheral* `GQ2.deltaC` (`GQ2/PeripheralAction.lean`) which wins
the resolution race against an `open`ed one from every namespace below `GQ2` — silently, with a
"function expected" error at the use site.  A lane-generic gotcha for WNP-b/WMP-b, whose words
also carry `δ`-letters. -/

open GQ2.Dyadic.Words.MCompact renaming deltaC → deltaCert

/-! ## Lane-generic Fox lemmas the weighted product rule needs

The compact-`N` row could be read off `foxD_prodList_of_trivial`, because every one of its
factors acts trivially.  The compact-`M` row cannot: `A₀²` and `σ₂^{2m}` act by the balancing
powers `S₂^{∓2m}`.  These are the four rules that replace it. -/

section Generic

variable {X : Type*} {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A] [Finite A]
  [DistribMulAction C A] (t : X → C) (a : X → A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **The Fox row of a conjugate whose base acts trivially**: `D(u^g) = ḡ⁻¹·D(u)`.

The two `D(g)` contributions of `g⁻¹ug` cancel — this is why the four `σ₂`-conjugators of the
`𝓔`-block contribute nothing to the `σ`-column. -/
theorem foxD_conj_of_trivial {u g : PWord X} (hu : PWord.evalFin t E E₂ u ∈ trivAct C A) :
    foxD t a E E₂ (.conj u g) = (PWord.evalFin t E E₂ g)⁻¹ • foxD t a E E₂ u := by
  rw [foxD_conj, mem_trivAct.mp hu, add_sub_cancel_right]

/-- **The Fox row of a commutator whose *right* base acts trivially**: `D([u,v]) = (1 − ū⁻¹)·D(v)`.

The general form of WWH's `foxD_comm_of_trivial` (which needs *both* bases trivial and returns
`0`).  It is what `[A₀,x₁]` needs: `A₀` acts by `S₂^{−m}`, `x₁` trivially, and the two `D(A₀)`
copies of `A₀⁻¹x₁⁻¹A₀x₁` cancel outright — the commutator's row has **no `x₀`-entry and no
`σ`-entry**, only `(1 − S₂^{m})·a(x₁)`. -/
theorem foxD_comm_of_trivial_right {u v : PWord X}
    (hv : PWord.evalFin t E E₂ v ∈ trivAct C A) :
    foxD t a E E₂ (.comm u v)
      = foxD t a E E₂ v - (PWord.evalFin t E E₂ u)⁻¹ • foxD t a E E₂ v := by
  have hqi : ∀ w : A, (PWord.evalFin t E E₂ v)⁻¹ • w = w := mem_trivAct.mp (inv_mem hv)
  rw [foxD_def, foxEval_comm, commR]
  show ((foxEval t a E E₂ u)⁻¹ * (foxEval t a E E₂ v)⁻¹ * foxEval t a E E₂ u
      * foxEval t a E E₂ v).u = _
  simp only [WordLift.mul_u, WordLift.mul_g, WordLift.inv_u, WordLift.inv_g, mul_smul, smul_neg,
    hqi, inv_smul_smul, foxD_def, foxEval_g]
  abel

/-- **The weighted product rule for a two-element `prodList`**, the shape every certificate
factor of this word has: `D(u·v·1) = D(u) + ū·D(v)`. -/
theorem foxD_prodList_pair (u v : PWord X) :
    foxD t a E E₂ (PWord.prodList [u, v])
      = foxD t a E E₂ u + PWord.evalFin t E E₂ u • foxD t a E E₂ v := by
  rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, foxD_mul, foxD_mul, foxD_one,
    smul_zero, add_zero]

omit [Finite C] [Finite A] in
/-- The evaluation of a two-element `prodList`. -/
theorem evalFin_prodList_pair (u v : PWord X) :
    PWord.evalFin t E E₂ (PWord.prodList [u, v])
      = PWord.evalFin t E E₂ u * PWord.evalFin t E E₂ v := by
  rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, PWord.evalFin_mul,
    PWord.evalFin_mul, PWord.evalFin_one, mul_one]

omit [Finite C] [Finite A] in
/-- **A commutator whose *right* entry acts trivially acts trivially** — normality of
`trivAct`, in the `commR` spelling: `[x,y] = (y⁻¹)^x · y`.  (WWH's `trivAct_commR` needs both
entries; `[A₀,x₁]` has a non-trivially-acting left entry.) -/
theorem trivAct_commR_right {x y : C} (hy : y ∈ trivAct C A) : commR x y ∈ trivAct C A :=
  mul_mem (trivAct_conjR (inv_mem hy) x) hy

end Generic

section GeomSum

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- **The geometric-sum doubling identity** `𝒢_{2k} = 𝒢_k + g^k·𝒢_k`, the arithmetic behind the
`σ`-column cancellation. -/
theorem geom_pow_smul_two_mul (g : C) (x : A) (k : ℕ) :
    ∑ i ∈ Finset.range (2 * k), g ^ i • x
      = (∑ i ∈ Finset.range k, g ^ i • x) + g ^ k • ∑ i ∈ Finset.range k, g ^ i • x := by
  rw [two_mul, Finset.sum_range_add, Finset.smul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => by rw [pow_add, mul_smul])

end GeomSum

/-! ## The compact-`M` alphabet sums

A row normal form denotes `a ↦ ∑_g coeff_g (a g)`.  The compact-`N` wild row was supported on
two letters; the compact-`M` wild row is supported on **four** (`τ, x₀, x₁, x₂`), so it needs
its own support lemma — at general `h`, i.e. without ever expanding the handle letters. -/

section AlphabetSums

variable {M : Type*} [AddCommMonoid M] {n : ℕ}

/-- A sum over `Generator n` supported on `{τ, x_i, x_j, x_k}` (`i, j, k` distinct) — the
compact-`M` wild-row support, at general handle count. -/
theorem sum_generator_quad (f : Generator n → M) (i j k : Fin (n + 1)) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hσ : f .sigma = 0)
    (hw : ∀ l, l ≠ i → l ≠ j → l ≠ k → f (.wild l) = 0) :
    ∑ g, f g = f .tau + f (.wild i) + f (.wild j) + f (.wild k) := by
  rw [← Finset.sum_subset (Finset.subset_univ
    ({Generator.tau, .wild i, .wild j, .wild k} : Finset (Generator n)))]
  · rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp [hij, hik]),
      Finset.sum_insert (by simp [hjk]), Finset.sum_singleton]
    abel
  · intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    cases x with
    | sigma => exact hσ
    | tau => exact absurd rfl hx.1
    | wild l =>
        exact hw l (fun hl => hx.2.1 (by rw [hl])) (fun hl => hx.2.2.1 (by rw [hl]))
          (fun hl => hx.2.2.2 (by rw [hl]))

end AlphabetSums

/-! ## The compact-`M` letters at a simple tame module

The standing setting is WN0-b's: a finite coefficient module `V` over a finite marked group `C`
with a marking `t` of `Generator (2 + 2h)`.  "Simple tame module" enters through `hwild` (every
wild letter, handles included, acts trivially) and a class condition on `τ`; the `σ`-action `S`
is never restricted, and `S₂ = powOmega2 t.σ` is restricted only where the *simple*-module
lemma is invoked by name. -/

section Rows

variable {h α : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- `MCompact`'s alphabet helpers are WN0-a's, on the nose.

⚠ **Vacuous since ticket WAH.**  The two copies of the letters were hoisted into one, in
`GQ2.Dyadic.Words` (`Words/Alphabet.lean`), so both sides of this equation are now literally the
same constant and the three bridges below state `x = x`.  They are kept only so that the call
sites that still name them keep building; a `simp only [coreLetter_eq]` step is now a no-op and
four of them were removed when WAH landed.  Deleting the three lemmas and their five remaining
uses is a one-ticket follow-up for this file's owner — it was left undone deliberately, because
WAH's remit is the `Words/*` duplication and not this file's proofs. -/
theorem coreLetter_eq (i : Fin 3) : coreLetter h i = Words.coreLetter h i := rfl

@[inherit_doc coreLetter_eq]
theorem handleU_eq (j : Fin h) : handleU j = Words.handleU j := rfl

@[inherit_doc coreLetter_eq]
theorem handleV_eq (j : Fin h) : handleV j = Words.handleV j := rfl

omit [Finite C] [Finite V] in
/-- The core letters `x₀, x₁, x₂` act trivially. -/
theorem trivAct_coreLetter (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (i : Fin 3) : t (coreLetter h i) ∈ trivAct C V :=
  mem_trivAct.mpr (hwild _)

omit [Finite C] [Finite V] in
/-- The handle letters act trivially. -/
theorem trivAct_handleU (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (j : Fin h) : t (handleU j) ∈ trivAct C V :=
  mem_trivAct.mpr (hwild _)

omit [Finite C] [Finite V] in
@[inherit_doc trivAct_handleU]
theorem trivAct_handleV (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (j : Fin h) : t (handleV j) ∈ trivAct C V :=
  mem_trivAct.mpr (hwild _)

/-! ### The `σ₂`-powers, and the opaque atom `D(σ₂)` -/

omit [Finite C] [Finite V] in
/-- `σ₂ = σ^{ω₂}` evaluates to the `2`-primary part of the `σ`-letter. -/
@[simp] theorem evalFin_sigma2W :
    PWord.evalFin ⇑t E E₂ (sigma2W : PWord (Generator (2 + 2 * h))) = powOmega2 t.σ := by
  rw [sigma2W, PWord.evalFin_omega2Pow, PWord.evalFin_gen, Marking.apply_sigma]

/-- **The `σ₂`-geometric sum** `𝒢_k = (1 + S₂ + ⋯ + S₂^{k−1})·D(σ₂)`.

`D(σ₂)` itself is the Sage engine's **opaque** atom `G[S;ω₂]` (`omega_proj`'s last branch: `σ`
is unramified, so `σ^{ω₂}` is *not* a projector and nothing universal can be said about its
exponent).  It is never computed here either — it cancels out of the row. -/
noncomputable def sigmaGeom (a : Generator (2 + 2 * h) → V) (k : ℕ) : V :=
  ∑ i ∈ Finset.range k, (powOmega2 t.σ) ^ i • foxD ⇑t a E E₂ sigma2W

/-- `D(σ₂^k) = 𝒢_k` for a natural exponent. -/
theorem foxD_sigma2Pow_natCast (a : Generator (2 + 2 * h) → V) (k : ℕ) :
    foxD ⇑t a E E₂ (.zpow sigma2W (k : ℤ)) = sigmaGeom t E E₂ a k := by
  rw [foxD_zpow_natCast, evalFin_sigma2W, sigmaGeom]

/-- `D(σ₂^{−k}) = −S₂^{−k}·𝒢_k`. -/
theorem foxD_sigma2Pow_neg (a : Generator (2 + 2 * h) → V) (k : ℕ) :
    foxD ⇑t a E E₂ (.zpow sigma2W (-(k : ℤ)))
      = -(((powOmega2 t.σ) ^ k)⁻¹ • sigmaGeom t E E₂ a k) := by
  rw [foxD_zpow_neg', foxEval_g, evalFin_sigma2W, foxD_sigma2Pow_natCast]

omit [Finite C] [Finite V] in
/-- **The doubling identity in place**: `𝒢_{2k} = 𝒢_k + S₂^k·𝒢_k`. -/
theorem sigmaGeom_two_mul (a : Generator (2 + 2 * h) → V) (k : ℕ) :
    sigmaGeom t E E₂ a (2 * k)
      = sigmaGeom t E E₂ a k + (powOmega2 t.σ) ^ k • sigmaGeom t E E₂ a k :=
  geom_pow_smul_two_mul _ _ k

/-! ### Factor 1: the Labute letter `A₀ = x₀⁻¹σ₂^{−m}` and its square -/

omit [Finite C] [Finite V] in
/-- `A₀` evaluates to `x₀⁻¹·S₂^{−m}`. -/
theorem evalFin_a0W :
    PWord.evalFin ⇑t E E₂ (a0W α h)
      = (t (coreLetter h 0))⁻¹ * ((powOmega2 t.σ) ^ (mOf α))⁻¹ := by
  rw [a0W, evalFin_prodList_pair, PWord.evalFin_inv, PWord.evalFin_gen, PWord.evalFin_zpow,
    evalFin_sigma2W, zpow_neg, zpow_natCast]

omit [Finite C] [Finite V] in
/-- **`A₀` acts as `S₂^{−m}`** — the wild letter `x₀` is invisible to the action, the `σ₂`-power
is not.  This is the single fact that makes the compact-`M` product rule *weighted*. -/
theorem evalFin_a0W_smul (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (v : V) :
    PWord.evalFin ⇑t E E₂ (a0W α h) • v = ((powOmega2 t.σ) ^ (mOf α))⁻¹ • v := by
  rw [evalFin_a0W, mul_smul, mem_trivAct.mp (inv_mem (trivAct_coreLetter t hwild 0))]

/-- **`D(A₀) = −a(x₀) − S₂^{−m}·𝒢_m`.** -/
theorem foxD_a0W (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (a0W α h)
      = -a (coreLetter h 0) - ((powOmega2 t.σ) ^ (mOf α))⁻¹ • sigmaGeom t E E₂ a (mOf α) := by
  rw [a0W, foxD_prodList_pair, foxD_inv, PWord.evalFin_gen, foxD_gen, foxD_sigma2Pow_neg,
    PWord.evalFin_inv, PWord.evalFin_gen,
    mem_trivAct.mp (inv_mem (trivAct_coreLetter t hwild 0)),
    mem_trivAct.mp (inv_mem (trivAct_coreLetter t hwild 0)), sub_eq_add_neg]

/-- **Factor 1** — `D(A₀²) = −(1 + S₂^{−m})·a(x₀) − (S₂^{−m} + S₂^{−2m})·𝒢_m`.

The leading exponent is the literal `2`: unlike the compact-`N` row's `x₀^{2+2^α}`, no parity
argument and hence **no `α`-hypothesis** is involved. -/
theorem foxD_leadingSquare (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (.zpow (a0W α h) 2)
      = (-a (coreLetter h 0) - ((powOmega2 t.σ) ^ (mOf α))⁻¹ • sigmaGeom t E E₂ a (mOf α))
        + ((powOmega2 t.σ) ^ (mOf α))⁻¹ •
          (-a (coreLetter h 0) - ((powOmega2 t.σ) ^ (mOf α))⁻¹ • sigmaGeom t E E₂ a (mOf α)) := by
  rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, foxD_zpow_natCast, Finset.sum_range_succ,
    Finset.sum_range_one, pow_zero, one_smul, pow_one]
  rw [foxD_a0W t E E₂ hwild, evalFin_a0W_smul t E E₂ hwild]

omit [Finite C] [Finite V] in
/-- `A₀²` acts as `S₂^{−2m}` — the prefix weight carried by every later factor. -/
theorem evalFin_leadingSquare_smul
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (v : V) :
    PWord.evalFin ⇑t E E₂ (.zpow (a0W α h) 2) • v
      = ((powOmega2 t.σ) ^ (2 * mOf α))⁻¹ • v := by
  have hmm : mOf α + mOf α = 2 * mOf α := by omega
  rw [PWord.evalFin_zpow, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two,
    mul_smul, evalFin_a0W_smul t E E₂ hwild, evalFin_a0W_smul t E E₂ hwild, ← mul_smul,
    ← mul_inv_rev, ← pow_add, hmm]

/-! ### Factor 2: the Labute commutator `[A₀, x₁]` -/

/-- **Factor 2** — `D([A₀,x₁]) = (1 − S₂^{m})·a(x₁)`.

Only the `x₁`-column: the `A₀`-derivatives of `A₀⁻¹x₁⁻¹A₀x₁` cancel, so neither `x₀` nor `σ`
appears (`foxD_comm_of_trivial_right`). -/
theorem foxD_leadingComm (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (.comm (a0W α h) (.gen (coreLetter h 1)))
      = a (coreLetter h 1) - (powOmega2 t.σ) ^ (mOf α) • a (coreLetter h 1) := by
  rw [foxD_comm_of_trivial_right _ _ _ _
      (by rw [PWord.evalFin_gen]; exact trivAct_coreLetter t hwild 1),
    foxD_gen, evalFin_a0W, mul_inv_rev, inv_inv, inv_inv, mul_smul,
    mem_trivAct.mp (trivAct_coreLetter t hwild 0)]

omit [Finite C] [Finite V] in
/-- `[A₀,x₁]` acts trivially, so it adds no weight to the prefix. -/
theorem evalFin_leadingComm_smul
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (v : V) :
    PWord.evalFin ⇑t E E₂ (.comm (a0W α h) (.gen (coreLetter h 1))) • v = v := by
  rw [PWord.evalFin_comm, PWord.evalFin_gen]
  exact mem_trivAct.mp (trivAct_commR_right (trivAct_coreLetter t hwild 1)) v

/-! ### Factor 3: the balancing power `σ₂^{2m}` -/

/-- **Factor 3** — `D(σ₂^{2m}) = 𝒢_{2m}`. -/
theorem foxD_sigma2Block (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (.zpow sigma2W (2 * (mOf α : ℤ))) = sigmaGeom t E E₂ a (2 * mOf α) := by
  rw [show (2 * (mOf α : ℤ)) = ((2 * mOf α : ℕ) : ℤ) by push_cast; ring, foxD_sigma2Pow_natCast]

omit [Finite C] [Finite V] in
/-- `σ₂^{2m}` acts as `S₂^{2m}` — cancelling `A₀²`'s weight exactly, which is why every later
factor enters with prefix weight `1`. -/
theorem evalFin_sigma2Block_smul (v : V) :
    PWord.evalFin ⇑t E E₂ (.zpow (sigma2W : PWord (Generator (2 + 2 * h))) (2 * (mOf α : ℤ))) • v
      = (powOmega2 t.σ) ^ (2 * mOf α) • v := by
  rw [PWord.evalFin_zpow, evalFin_sigma2W,
    show (2 * (mOf α : ℤ)) = ((2 * mOf α : ℕ) : ℤ) by push_cast; ring, zpow_natCast]

/-! ### Factor 4: the shared block `J₂ = x₂^{-σ}(x₂τ)^{ω₂}`

Verbatim WC-N0: these are the compact-`N` word's third and fourth factors, and the proofs
below are the pilot lane's own lemmas, applied. -/

/-- **Factor 4, split/unramified (`P = 1`)** — `D(J₂) = −S⁻¹·a(x₂) + (a(x₂) + a(τ))`. -/
theorem foxD_j2W_unram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (j2W h)
      = -(t.σ⁻¹ • a (coreLetter h 2)) + (a (coreLetter h 2) + a .tau) := by
  rw [j2W, foxD_prodList_pair]
  rw [foxD_invConjX2 t E E₂ hwild, foxD_deltaBlock_unram t E E₂ hV₂ hwild hτ,
    PWord.evalFin_inv, PWord.evalFin_conj, PWord.evalFin_gen, PWord.evalFin_gen,
    mem_trivAct.mp (inv_mem (trivAct_conjR (Certificates.trivAct_coreLetter t hwild 2) _))]

/-- **Factor 4, ramified (`P = 0`)** — `D(J₂) = −S⁻¹·a(x₂)`. -/
theorem foxD_j2W_ram (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hτfpf : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (j2W h) = -(t.σ⁻¹ • a (coreLetter h 2)) := by
  rw [j2W, foxD_prodList_pair]
  rw [foxD_invConjX2 t E E₂ hwild, foxD_deltaBlock_ram t E E₂ hwild hτfpf hTodd, smul_zero,
    add_zero]

omit [Finite C] [Finite V] in
/-- `J₂` acts trivially at both `τ`-classes (the class enters through `hδ`, the `ω₂`-block's own
evaluation — the compact-`N` bookkeeping). -/
theorem evalFin_j2W_smul (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hδ : PWord.evalFin ⇑t E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau]))
        ∈ trivAct C V) (v : V) :
    PWord.evalFin ⇑t E E₂ (j2W h) • v = v := by
  rw [j2W, evalFin_prodList_pair, mul_smul, mem_trivAct.mp hδ, PWord.evalFin_inv,
    PWord.evalFin_conj, PWord.evalFin_gen, PWord.evalFin_gen,
    mem_trivAct.mp (inv_mem (trivAct_conjR (trivAct_coreLetter t hwild 2) _))]

/-! ### Factor 5: the reversed correction block `E_m^rev` -/

omit [Finite C] [Finite V] in
/-- The certificate `δ`-letter `δ_i = (x_iτ)^{ω₂}x_i⁻¹` acts trivially, at both `τ`-classes —
which is what lets the four-factor block be differentiated as a plain sum. -/
theorem trivAct_deltaC (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (i : Fin 3)
    (hδ : PWord.evalFin ⇑t E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau])) ∈ trivAct C V) :
    PWord.evalFin ⇑t E E₂ (deltaCert h i) ∈ trivAct C V := by
  rw [deltaCert, evalFin_prodList_pair, PWord.evalFin_inv, PWord.evalFin_gen]
  exact mul_mem hδ (inv_mem (trivAct_coreLetter t hwild i))

/-- **`D(δ_i) = (P + 1)·a(x_i) + P·a(τ)`, split reading (`P = 1`)**: `D(δ_i) = a(τ)`.

The primal offset carries the factor `P + 1`, which *is* the frozen certificate's module finding
(i) — at `P = 1` the correction block's `x₀`- and `x₁`-columns die. -/
theorem foxD_deltaC_unram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (i : Fin 3) (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (deltaCert h i) = a .tau := by
  have hbase : ∀ v : V, PWord.evalFin ⇑t E E₂
      (PWord.prodList [(.gen (coreLetter h i) : PWord (Generator (2 + 2 * h))), .gen .tau])
        • v = v := by
    intro v
    rw [evalFin_prodList_pair, PWord.evalFin_gen, PWord.evalFin_gen, mul_smul, Marking.apply_tau,
      hτ, mem_trivAct.mp (trivAct_coreLetter t hwild i)]
  rw [deltaCert, foxD_prodList_pair, foxD_def, foxEval_omega2Pow,
    WordLift.powOmega2_u_of_trivial hV₂ _ (fun v => by rw [foxEval_g]; exact hbase v),
    ← foxD_def, foxD_prodList_pair, PWord.evalFin_gen, foxD_gen, foxD_gen,
    mem_trivAct.mp (trivAct_coreLetter t hwild i), PWord.evalFin_omega2Pow,
    mem_trivAct.mp (trivAct_powOmega2 (mem_trivAct.mpr hbase)), foxD_inv, PWord.evalFin_gen,
    foxD_gen, mem_trivAct.mp (inv_mem (trivAct_coreLetter t hwild i))]
  abel

/-- **`D(δ_i)` at the ramified reading (`P = 0`)**: `D(δ_i) = −a(x_i)`.

Not zero — the block's primal offsets survive at `P = 0` and cancel the `A₀²[A₀,x₁]`
contribution instead (see the module docstring, item 2). -/
theorem foxD_deltaC_ram (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hτfpf : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (i : Fin 3)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (deltaCert h i) = -a (coreLetter h i) := by
  have hbase : PWord.evalFin ⇑t E E₂
      (PWord.prodList [(.gen (coreLetter h i) : PWord (Generator (2 + 2 * h))), .gen .tau])
        = t (coreLetter h i) * t.τ := by
    rw [evalFin_prodList_pair, PWord.evalFin_gen, PWord.evalFin_gen, Marking.apply_tau]
  have hω : foxD ⇑t a E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau])) = 0 := by
    rw [foxD_def, foxEval_omega2Pow]
    refine WordLift.powOmega2_u_of_oddFixedPointFree _ (fun v hv => hτfpf v ?_) (fun v => ?_)
    · rw [foxEval_g, hbase, mul_smul, mem_trivAct.mp (trivAct_coreLetter t hwild i)] at hv
      exact hv
    · rw [foxEval_g, hbase]
      exact WordLift.powOmega2_smul_of_trivial_mul _ _
        (mem_trivAct.mp (trivAct_coreLetter t hwild i)) hTodd v
  have hδtriv : PWord.evalFin ⇑t E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau])) ∈ trivAct C V := by
    rw [PWord.evalFin_omega2Pow, hbase]
    exact mem_trivAct.mpr (fun v => WordLift.powOmega2_smul_of_trivial_mul _ _
      (mem_trivAct.mp (trivAct_coreLetter t hwild i)) hTodd v)
  rw [deltaCert, foxD_prodList_pair, hω, mem_trivAct.mp hδtriv, foxD_inv, PWord.evalFin_gen,
    foxD_gen, mem_trivAct.mp (inv_mem (trivAct_coreLetter t hwild i)), zero_add]

omit [Finite C] [Finite V] in
/-- The `ω₂`-block `(x_iτ)^{ω₂}` acts trivially on an unramified module — the hypothesis every
`δ`-letter statement below consumes. -/
theorem trivAct_deltaBlock_unram (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hτ : ∀ v : V, t.τ • v = v) (i : Fin 3) :
    PWord.evalFin ⇑t E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau])) ∈ trivAct C V := by
  rw [PWord.evalFin_omega2Pow]
  refine trivAct_powOmega2 (mem_trivAct.mpr fun v => ?_)
  rw [evalFin_prodList_pair, PWord.evalFin_gen, PWord.evalFin_gen, mul_smul, Marking.apply_tau,
    hτ, mem_trivAct.mp (trivAct_coreLetter t hwild i)]

omit [Finite V] in
/-- The same on a ramified module, for the *other* reason: `τ`'s `2`-primary part is trivial
(`hTodd`), so the `ω₂`-power of `x_iτ` is.  (`Finite C` is real here: `powOmega2` computes a
`2`-primary part, which needs a finite ambient group.) -/
theorem trivAct_deltaBlock_ram (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (i : Fin 3) :
    PWord.evalFin ⇑t E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau])) ∈ trivAct C V := by
  rw [PWord.evalFin_omega2Pow, evalFin_prodList_pair, PWord.evalFin_gen, PWord.evalFin_gen,
    Marking.apply_tau]
  exact mem_trivAct.mpr fun v => WordLift.powOmega2_smul_of_trivial_mul _ _
    (mem_trivAct.mp (trivAct_coreLetter t hwild i)) hTodd v

/-- **The correction block differentiates as a plain weighted sum of its four `δ`-letters**:

```
D(E_m^rev) = (S₂^{−2m} + S₂^{−m})·D(δ₁) + (S₂^{−m} + 1)·D(δ₀),
```

at every class in which the `δ`-letters act trivially.  The conjugators contribute nothing
(`foxD_conj_of_trivial`), which is the block's whole `σ`-blindness. -/
theorem foxD_eRevW (hd0 : PWord.evalFin ⇑t E E₂ (deltaCert h 0) ∈ trivAct C V)
    (hd1 : PWord.evalFin ⇑t E E₂ (deltaCert h 1) ∈ trivAct C V)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (eRevW α h)
      = ((powOmega2 t.σ) ^ (2 * mOf α))⁻¹ • foxD ⇑t a E E₂ (deltaCert h 1)
        + ((powOmega2 t.σ) ^ (mOf α))⁻¹ • foxD ⇑t a E E₂ (deltaCert h 1)
        + (((powOmega2 t.σ) ^ (mOf α))⁻¹ • foxD ⇑t a E E₂ (deltaCert h 0)
          + foxD ⇑t a E E₂ (deltaCert h 0)) := by
  have hconjmem : ∀ (i : Fin 3) (k : ℤ),
      PWord.evalFin ⇑t E E₂ (deltaCert h i) ∈ trivAct C V →
        PWord.evalFin ⇑t E E₂ (.conj (deltaCert h i) (.zpow sigma2W k)) ∈ trivAct C V := by
    intro i k hi
    rw [PWord.evalFin_conj]
    exact trivAct_conjR hi _
  have hconj : ∀ (i : Fin 3) (k : ℕ),
      PWord.evalFin ⇑t E E₂ (deltaCert h i) ∈ trivAct C V →
        foxD ⇑t a E E₂ (.conj (deltaCert h i) (.zpow sigma2W (k : ℤ)))
          = ((powOmega2 t.σ) ^ k)⁻¹ • foxD ⇑t a E E₂ (deltaCert h i) := by
    intro i k hi
    rw [foxD_conj_of_trivial _ _ _ _ hi, PWord.evalFin_zpow, evalFin_sigma2W, zpow_natCast]
  rw [eRevW, foxD_prodList_of_trivial _ _ _ _ _ (by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact hconjmem 1 _ hd1
    · exact hconjmem 1 _ hd1
    · exact hconjmem 0 _ hd0
    · exact hd0)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [show (2 * (mOf α : ℤ)) = ((2 * mOf α : ℕ) : ℤ) by push_cast; ring,
    hconj 1 _ hd1, hconj 1 _ hd1, hconj 0 _ hd0]
  abel

/-- **The correction block's own Fox row at `P = 1`**: `(S₂^{−2m} + 1)·a(τ)`.

⚠ **Not zero.**  The block's *primal* offsets carry the factor `P + 1` and do die here
(`foxD_deltaC_unram` is `a(τ)`, with no `x_i` at all), but its `τ`-contribution survives — it is
what turns `J₂`'s bare `P` into the assembled row's `P·S₂^{−2m}`.  It vanishes only after the
additional *simple*-module collapse `S₂ = 1`.  Stating this is the honest form of the frozen
certificate's "the correction block is invisible at first order in BOTH projector cases". -/
theorem foxD_eRevW_unram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (eRevW α h)
      = ((powOmega2 t.σ) ^ (2 * mOf α))⁻¹ • a .tau + a .tau := by
  rw [foxD_eRevW t E E₂
      (trivAct_deltaC t E E₂ hwild 0 (trivAct_deltaBlock_unram t E E₂ hwild hτ 0))
      (trivAct_deltaC t E E₂ hwild 1 (trivAct_deltaBlock_unram t E E₂ hwild hτ 1)),
    foxD_deltaC_unram t E E₂ hV₂ hwild hτ, foxD_deltaC_unram t E E₂ hV₂ hwild hτ,
    show ((powOmega2 t.σ) ^ (2 * mOf α))⁻¹ • a .tau
        + ((powOmega2 t.σ) ^ mOf α)⁻¹ • a .tau
        + (((powOmega2 t.σ) ^ mOf α)⁻¹ • a .tau + a .tau)
      = (((powOmega2 t.σ) ^ (2 * mOf α))⁻¹ • a .tau + a .tau)
        + (((powOmega2 t.σ) ^ mOf α)⁻¹ • a .tau + ((powOmega2 t.σ) ^ mOf α)⁻¹ • a .tau) from
      by abel, hV₂, add_zero]

/-- **The correction block's own Fox row at `P = 0`**:
`−((S₂^{−2m}+S₂^{−m})·a(x₁) + (S₂^{−m}+1)·a(x₀))`.

⚠ Also **not zero** — here the *primal* offsets are what survive (`foxD_deltaC_ram` is
`−a(x_i)`), and they leave the assembled row only by cancelling the `A₀²[A₀,x₁]` contribution
over `𝔽₂`.  So the block is invisible in both published specializations, but by two genuinely
different mechanisms. -/
theorem foxD_eRevW_ram (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hτfpf : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (eRevW α h)
      = -(((powOmega2 t.σ) ^ (2 * mOf α))⁻¹ • a (coreLetter h 1)
          + ((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 1)
          + (((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 0) + a (coreLetter h 0))) := by
  rw [foxD_eRevW t E E₂
      (trivAct_deltaC t E E₂ hwild 0 (trivAct_deltaBlock_ram t E E₂ hwild hTodd 0))
      (trivAct_deltaC t E E₂ hwild 1 (trivAct_deltaBlock_ram t E E₂ hwild hTodd 1)),
    foxD_deltaC_ram t E E₂ hwild hτfpf hTodd, foxD_deltaC_ram t E E₂ hwild hτfpf hTodd]
  simp only [smul_neg]
  abel

/-! ### The handle block

`D(H_h) = 0` at every `h` — WWH's `foxD_comm_of_trivial`, exactly as on the compact-`N` row.
⚠ Here the *tail* is what the word actually contains, and at `h = 0` it is **empty** (WM0-a
deviation 1: the compact-`M` certificate emits no `HyperbolicHandles` child), so the statement
splits by cases and only `h ≥ 1` has content. -/

theorem foxD_handlesW (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (a : Generator (2 + 2 * h) → V) : foxD ⇑t a E E₂ (handlesW h) = 0 :=
  Certificates.foxD_handlesW t E E₂ hwild a

/-- **The handle tail is first-order invisible, uniformly in `h`** — vacuously at `h = 0`
(no factor at all) and by `foxD_handlesW` at `h ≥ 1`. -/
theorem foxD_handleTailW (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (PWord.prodList (handleTailW h)) = 0 := by
  cases h with
  | zero => rfl
  | succ k =>
      rw [handleTailW, PWord.prodList_cons, PWord.prodList_nil, foxD_mul, foxD_one, smul_zero,
        add_zero]
      exact foxD_handlesW t E E₂ hwild a

/-! ### The assembled row

Everything above, plugged into the iterated product rule.  The `σ`-column cancellation happens
here and it happens **over `ℤ`**: no characteristic-`2` hypothesis is used by
`foxD_mCompact_core`. -/

/-- **The compact-`M` row with its two class-dependent factors left abstract.**

```
D(R_{M,0}) = −(1 + S₂^{−m})·a(x₀) + (S₂^{−2m} − S₂^{−m})·a(x₁) + D(J₂) + D(E_m^rev).
```

The `𝒢`-terms of `A₀²` and of `σ₂^{2m}` have cancelled: the balancing factor `σ₂^{2m}` sits
behind the prefix `S₂^{−2m}` of `A₀²[A₀,x₁]`, so its contribution `S₂^{−2m}·𝒢_{2m}` is
*literally* the `A₀²` contribution `(S₂^{−m} + S₂^{−2m})·𝒢_m` (`sigmaGeom_two_mul`).  That is
packet Prop. 9.2's power balance `−2·2^{α−1} + 2^α = 0`, one derivative up, and it is why the
opaque atom `D(σ₂)` never reaches a certificate.

No hypothesis on `α`, none on `S`, none on the characteristic — and **none on the correction
block**, which is why this is stated for WM0-a's block-slot scaffolding `mWordWith B`: the block
sits last among the five factors, so its own evaluation only ever multiplies the handle tail's
derivative, and that is `0`. -/
theorem foxD_mWordWith_core
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hj2 : ∀ v : V, PWord.evalFin ⇑t E E₂ (j2W h) • v = v)
    (B : PWord (Generator (2 + 2 * h))) (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (mWordWith α h B)
      = (-a (coreLetter h 0) - ((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 0))
        + (((powOmega2 t.σ) ^ (2 * mOf α))⁻¹ • a (coreLetter h 1)
            - ((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 1))
        + (foxD ⇑t a E E₂ (j2W h) + foxD ⇑t a E E₂ B) := by
  have hsplit : (powOmega2 t.σ) ^ (2 * mOf α)
      = (powOmega2 t.σ) ^ mOf α * (powOmega2 t.σ) ^ mOf α := by
    rw [← pow_add]; congr 1; omega
  rw [mWordWith]
  simp only [List.cons_append, List.nil_append, PWord.prodList_cons]
  rw [foxD_mul, foxD_mul, foxD_mul, foxD_mul, foxD_mul, foxD_handleTailW t E E₂ hwild,
    smul_zero, add_zero, hj2, evalFin_sigma2Block_smul, evalFin_leadingComm_smul t E E₂ hwild,
    evalFin_leadingSquare_smul t E E₂ hwild, foxD_leadingSquare t E E₂ hwild,
    foxD_leadingComm t E E₂ hwild, foxD_sigma2Block, sigmaGeom_two_mul]
  simp only [smul_add, smul_sub, smul_neg, hsplit, mul_inv_rev, mul_smul, inv_smul_smul]
  abel

@[inherit_doc foxD_mWordWith_core]
theorem foxD_mCompact_core
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hj2 : ∀ v : V, PWord.evalFin ⇑t E E₂ (j2W h) • v = v)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (mCompactW α h)
      = (-a (coreLetter h 0) - ((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 0))
        + (((powOmega2 t.σ) ^ (2 * mOf α))⁻¹ • a (coreLetter h 1)
            - ((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 1))
        + (foxD ⇑t a E E₂ (j2W h) + foxD ⇑t a E E₂ (eRevW α h)) :=
  foxD_mWordWith_core t E E₂ hwild hj2 _ a

/-! ### The four published rows -/

/-- **The compact-`M` wild row on a general unramified module** (`P ↦ 1`, `T = 1`):

```
D(R_{M,0}) = S₂^{−2m}·a(τ) + (1 + S₂^{−m})·a(x₀) + (S₂^{−m} + S₂^{−2m})·a(x₁)
             + (1 − S⁻¹)·a(x₂).
```

Read against the frozen row `(0, P·S₂^{−2m}, P·S₂^{−m}+P, P·S₂^{−m}+P·S₂^{−2m}, S⁻¹+P)` at
`P = 1`.  The `x₀`- and `x₁`-entries survive here precisely because `S₂` has *not* been
collapsed; see `foxD_mCompact_unram_simple` for the simple-module reading. -/
theorem foxD_mCompact_unram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (mCompactW α h)
      = ((powOmega2 t.σ) ^ (2 * mOf α))⁻¹ • a .tau
        + (a (coreLetter h 0) + ((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 0))
        + (((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 1)
            + ((powOmega2 t.σ) ^ (2 * mOf α))⁻¹ • a (coreLetter h 1))
        + (a (coreLetter h 2) - t.σ⁻¹ • a (coreLetter h 2)) := by
  have hneg : ∀ v : V, -v = v := Certificates.neg_eq_self hV₂
  have hδ := trivAct_deltaBlock_unram t E E₂ hwild hτ
  rw [foxD_mCompact_core t E E₂ hwild (evalFin_j2W_smul t E E₂ hwild (hδ 2)),
    foxD_j2W_unram t E E₂ hV₂ hwild hτ,
    foxD_eRevW t E E₂ (trivAct_deltaC t E E₂ hwild 0 (hδ 0))
      (trivAct_deltaC t E E₂ hwild 1 (hδ 1)),
    foxD_deltaC_unram t E E₂ hV₂ hwild hτ, foxD_deltaC_unram t E E₂ hV₂ hwild hτ]
  simp only [sub_eq_add_neg, hneg]
  rw [show
      (a (coreLetter h 0) + ((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 0)
        + (((powOmega2 t.σ) ^ (2 * mOf α))⁻¹ • a (coreLetter h 1)
          + ((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 1))
        + (t.σ⁻¹ • a (coreLetter h 2) + (a (coreLetter h 2) + a .tau)
          + (((powOmega2 t.σ) ^ (2 * mOf α))⁻¹ • a .tau
            + ((powOmega2 t.σ) ^ mOf α)⁻¹ • a .tau
            + (((powOmega2 t.σ) ^ mOf α)⁻¹ • a .tau + a .tau))) : V)
      = (((powOmega2 t.σ) ^ (2 * mOf α))⁻¹ • a .tau
          + (a (coreLetter h 0) + ((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 0))
          + (((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 1)
            + ((powOmega2 t.σ) ^ (2 * mOf α))⁻¹ • a (coreLetter h 1))
          + (a (coreLetter h 2) + t.σ⁻¹ • a (coreLetter h 2)))
        + (a .tau + a .tau)
        + (((powOmega2 t.σ) ^ mOf α)⁻¹ • a .tau + ((powOmega2 t.σ) ^ mOf α)⁻¹ • a .tau) from
      by abel, hV₂, hV₂, add_zero, add_zero]

/-- **The compact-`M` wild row on a *simple* unramified module** — the frozen certificate's
printed unramified specialization `(0, 1, 0, 0, S⁻¹+1)`:

```
D(R_{M,0}) = a(τ) + (1 − S⁻¹)·a(x₂).
```

The extra hypothesis is `S₂ = 1`, the Sage side's `specialize_unramified(simple=True)` clause
(module docstring): on a simple unramified module the `2`-part of `S` acts trivially, and
`S₂ = S^{ω₂}` *is* that `2`-part.  With it the whole correction block — and with it every trace
of `α` — leaves the row. -/
theorem foxD_mCompact_unram_simple (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hS₂ : ∀ v : V, powOmega2 t.σ • v = v) (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (mCompactW α h)
      = a .tau + (a (coreLetter h 2) - t.σ⁻¹ • a (coreLetter h 2)) := by
  have hS : ∀ (k : ℕ) (v : V), ((powOmega2 t.σ) ^ k)⁻¹ • v = v := fun k v =>
    mem_trivAct.mp (inv_mem (pow_mem (mem_trivAct.mpr hS₂) k)) v
  rw [foxD_mCompact_unram t E E₂ hV₂ hwild hτ]
  simp only [hS]
  rw [show (a .tau + (a (coreLetter h 0) + a (coreLetter h 0))
        + (a (coreLetter h 1) + a (coreLetter h 1))
        + (a (coreLetter h 2) - t.σ⁻¹ • a (coreLetter h 2)) : V)
      = (a .tau + (a (coreLetter h 2) - t.σ⁻¹ • a (coreLetter h 2)))
        + (a (coreLetter h 0) + a (coreLetter h 0))
        + (a (coreLetter h 1) + a (coreLetter h 1)) from by abel, hV₂, hV₂, add_zero, add_zero]

/-- **On a simple unramified module the compact-`M` and compact-`N` words have the same first
Fox row.**  Both are `a(τ) + (1 − S⁻¹)·a(x₂)`: the `J₂` block is literally shared (the frozen
note), everything else on either row has left.  This is the strongest form of "the two
one-operation normal forms are shared with packet row WC-N0" — the *rows* already agree, so a
fortiori their normal forms do. -/
theorem foxD_mCompact_eq_nCompact_unram_simple (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hS₂ : ∀ v : V, powOmega2 t.σ • v = v) (hα : 1 ≤ α) (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (mCompactW α h) = foxD ⇑t a E E₂ (Words.nCompactW α h) := by
  rw [foxD_mCompact_unram_simple t E E₂ hV₂ hwild hτ hS₂,
    foxD_nCompact_unram t E E₂ hV₂ hwild hτ hα]

/-- **The compact-`M` wild row on a ramified module** (`P ↦ 0`, `V^T = 0`):

```
D(R_{M,0}) = −S⁻¹·a(x₂),
```

a single **unit** entry — the same row the compact-`N` word has, and for the same reason (the
`x₂^{-σ}` letter of the shared `J₂` block).  Here **no `S₂`-hypothesis is needed**: every other
entry of the universal row carries the projector, and `P ↦ 0` erases it.  What the block
contributes at `P = 0` is not zero — it is `−(S₂^{−2m}+S₂^{−m})·a(x₁) − (S₂^{−m}+1)·a(x₀)`,
which cancels the `A₀²[A₀,x₁]` contribution over `𝔽₂`. -/
theorem foxD_mCompact_ram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hτfpf : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (mCompactW α h) = -(t.σ⁻¹ • a (coreLetter h 2)) := by
  have hneg : ∀ v : V, -v = v := Certificates.neg_eq_self hV₂
  have hδ := trivAct_deltaBlock_ram t E E₂ hwild hTodd
  rw [foxD_mCompact_core t E E₂ hwild (evalFin_j2W_smul t E E₂ hwild (hδ 2)),
    foxD_j2W_ram t E E₂ hwild hτfpf hTodd,
    foxD_eRevW t E E₂ (trivAct_deltaC t E E₂ hwild 0 (hδ 0))
      (trivAct_deltaC t E E₂ hwild 1 (hδ 1)),
    foxD_deltaC_ram t E E₂ hwild hτfpf hTodd, foxD_deltaC_ram t E E₂ hwild hτfpf hTodd]
  simp only [sub_eq_add_neg, hneg]
  rw [show
      (a (coreLetter h 0) + ((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 0)
        + (((powOmega2 t.σ) ^ (2 * mOf α))⁻¹ • a (coreLetter h 1)
          + ((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 1))
        + (t.σ⁻¹ • a (coreLetter h 2)
          + (((powOmega2 t.σ) ^ (2 * mOf α))⁻¹ • a (coreLetter h 1)
            + ((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 1)
            + (((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 0)
              + a (coreLetter h 0)))) : V)
      = t.σ⁻¹ • a (coreLetter h 2)
        + (a (coreLetter h 0) + a (coreLetter h 0))
        + (((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 0)
          + ((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 0))
        + (((powOmega2 t.σ) ^ (2 * mOf α))⁻¹ • a (coreLetter h 1)
          + ((powOmega2 t.σ) ^ (2 * mOf α))⁻¹ • a (coreLetter h 1))
        + (((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 1)
          + ((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 1)) from by abel,
    hV₂, hV₂, hV₂, hV₂, add_zero, add_zero, add_zero, add_zero]

/-- **The compact-`M` wild row on a split (scalar) module**: with the whole tame quotient acting
trivially the row degenerates to the `τ`-pivot `a(τ)` — the frozen `scalar` column `(0,1,0,0,0)`.

`S = 1` forces `S₂ = 1` (it is a power of `S`), so this is a corollary of the simple-unramified
row with the `1 − S⁻¹` block collapsing.  As on the compact-`N` row, this is the honest content
of "the scalar module separates nothing". -/
theorem foxD_mCompact_split (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hσ : ∀ v : V, t.σ • v = v) (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (mCompactW α h) = a .tau := by
  have hσinv : ∀ v : V, t.σ⁻¹ • v = v := fun v =>
    mem_trivAct.mp (inv_mem (mem_trivAct.mpr hσ)) v
  rw [foxD_mCompact_unram_simple t E E₂ hV₂ hwild hτ
      (fun v => mem_trivAct.mp (trivAct_powOmega2 (mem_trivAct.mpr hσ)) v),
    hσinv, sub_self, add_zero]

/-! ### The zero columns, and the `2h` handle columns in particular

A *column* of the evaluated row is its value on a single-slot offset vector `Pi.single g v`.
The compact-`M` wild row has at most **four** nonzero columns at every handle count (against
the compact-`N` row's two), so all `2h` handle columns — the whole `h`-dependence of the first
jet — vanish identically: hyperbolic stabilization is first-order invisible. -/

/-- The handle letters `x₃, …, x_{2h+2}` are distinct from the core letters `x₀, x₁, x₂` and
from `τ` — the four column-distinctness facts every handle-column vanishing needs.  Shared with
WN0-b letter for letter (the alphabets are the same). -/
theorem handleU_ne_coreLetter (j : Fin h) (i : Fin 3) : handleU j ≠ coreLetter h i :=
  Certificates.handleU_ne_coreLetter j i

@[inherit_doc handleU_ne_coreLetter]
theorem handleV_ne_coreLetter (j : Fin h) (i : Fin 3) : handleV j ≠ coreLetter h i :=
  Certificates.handleV_ne_coreLetter j i

@[inherit_doc handleU_ne_coreLetter]
theorem handleU_ne_tau (j : Fin h) : handleU j ≠ (Generator.tau : Generator (2 + 2 * h)) :=
  Certificates.handleU_ne_tau j

@[inherit_doc handleU_ne_coreLetter]
theorem handleV_ne_tau (j : Fin h) : handleV j ≠ (Generator.tau : Generator (2 + 2 * h)) :=
  Certificates.handleV_ne_tau j

/-- **Every column of the wild row other than `τ, x₀, x₁, x₂` is zero** (unramified class). -/
theorem foxDHom_mCompact_unram_column_eq_zero (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    {g : Generator (2 + 2 * h)} (hgτ : g ≠ .tau) (hg0 : g ≠ coreLetter h 0)
    (hg1 : g ≠ coreLetter h 1) (hg2 : g ≠ coreLetter h 2) (v : V) :
    foxDHom ⇑t E E₂ (mCompactW α h) (Pi.single g v) = 0 := by
  rw [foxDHom_apply, foxD_mCompact_unram t E E₂ hV₂ hwild hτ,
    Pi.single_eq_of_ne (Ne.symm hgτ), Pi.single_eq_of_ne (Ne.symm hg0),
    Pi.single_eq_of_ne (Ne.symm hg1), Pi.single_eq_of_ne (Ne.symm hg2)]
  simp

/-- The `2h` handle columns of the wild row are zero — the `u`-half, at every `h`. -/
theorem foxDHom_mCompact_handleU_column (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (j : Fin h) (v : V) :
    foxDHom ⇑t E E₂ (mCompactW α h) (Pi.single (handleU j) v) = 0 :=
  foxDHom_mCompact_unram_column_eq_zero t E E₂ hV₂ hwild hτ (handleU_ne_tau j)
    (handleU_ne_coreLetter j 0) (handleU_ne_coreLetter j 1) (handleU_ne_coreLetter j 2) v

/-- The `2h` handle columns of the wild row are zero — the `v`-half, at every `h`. -/
theorem foxDHom_mCompact_handleV_column (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (j : Fin h) (v : V) :
    foxDHom ⇑t E E₂ (mCompactW α h) (Pi.single (handleV j) v) = 0 :=
  foxDHom_mCompact_unram_column_eq_zero t E E₂ hV₂ hwild hτ (handleV_ne_tau j)
    (handleV_ne_coreLetter j 0) (handleV_ne_coreLetter j 1) (handleV_ne_coreLetter j 2) v

/-- The same, ramified class: there the row has a *single* nonzero column, so every column but
`x₂` — handles included — dies. -/
theorem foxDHom_mCompact_ram_column_eq_zero (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hτfpf : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v)
    {g : Generator (2 + 2 * h)} (hg2 : g ≠ coreLetter h 2) (v : V) :
    foxDHom ⇑t E E₂ (mCompactW α h) (Pi.single g v) = 0 := by
  rw [foxDHom_apply, foxD_mCompact_ram t E E₂ hV₂ hwild hτfpf hTodd,
    Pi.single_eq_of_ne (Ne.symm hg2)]
  simp

/-! ### The forward-order mutant at first order

WM0-a proved that neither boundary gate can see the block order.  Here is the *first Fox order*
statement, which is the one S4.1 says is invisible: the four `δ`-conjugates all act trivially,
so their derivatives add as a plain sum and reordering them is `add_comm`.

⚠ This is **not** a claim that the two words are equal, nor a rejection of either order.  Per
the dated 2026-07-31 correction to the WM0 spec, the rejection of record is S4.1 §9.4's
second-order difference formula in `(q, b_q, P, W)`; the Lean-side rejection is WM0-c's. -/

/-- **The two `𝓔`-block orders have the same Fox row.** -/
theorem foxD_eFwdW_eq_eRevW (hd0 : PWord.evalFin ⇑t E E₂ (deltaCert h 0) ∈ trivAct C V)
    (hd1 : PWord.evalFin ⇑t E E₂ (deltaCert h 1) ∈ trivAct C V)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (eFwdW α h) = foxD ⇑t a E E₂ (eRevW α h) := by
  have hconjmem : ∀ (i : Fin 3) (k : ℤ),
      PWord.evalFin ⇑t E E₂ (deltaCert h i) ∈ trivAct C V →
        PWord.evalFin ⇑t E E₂ (.conj (deltaCert h i) (.zpow sigma2W k)) ∈ trivAct C V := by
    intro i k hi
    rw [PWord.evalFin_conj]
    exact trivAct_conjR hi _
  have hconj : ∀ (i : Fin 3) (k : ℕ),
      PWord.evalFin ⇑t E E₂ (deltaCert h i) ∈ trivAct C V →
        foxD ⇑t a E E₂ (.conj (deltaCert h i) (.zpow sigma2W (k : ℤ)))
          = ((powOmega2 t.σ) ^ k)⁻¹ • foxD ⇑t a E E₂ (deltaCert h i) := by
    intro i k hi
    rw [foxD_conj_of_trivial _ _ _ _ hi, PWord.evalFin_zpow, evalFin_sigma2W, zpow_natCast]
  rw [eFwdW, foxD_prodList_of_trivial _ _ _ _ _ (by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact hd0
    · exact hconjmem 0 _ hd0
    · exact hconjmem 1 _ hd1
    · exact hconjmem 1 _ hd1)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [show (2 * (mOf α : ℤ)) = ((2 * mOf α : ℕ) : ℤ) by push_cast; ring,
    hconj 0 _ hd0, hconj 1 _ hd1, hconj 1 _ hd1,
    foxD_eRevW t E E₂ hd0 hd1]
  abel

/-- **The block order is invisible at first Fox order**: the frozen word and its forward-order
mutant have the *same* evaluated Fox row, at every marking of every class in which the
`δ`-letters act trivially — i.e. at every module the certificates speak about. -/
theorem foxD_mFwdW_eq_mCompact
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hj2 : ∀ v : V, PWord.evalFin ⇑t E E₂ (j2W h) • v = v)
    (hd0 : PWord.evalFin ⇑t E E₂ (deltaCert h 0) ∈ trivAct C V)
    (hd1 : PWord.evalFin ⇑t E E₂ (deltaCert h 1) ∈ trivAct C V)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (mFwdW α h) = foxD ⇑t a E E₂ (mCompactW α h) := by
  rw [mFwdW, foxD_mWordWith_core t E E₂ hwild hj2, foxD_mCompact_core t E E₂ hwild hj2,
    foxD_eFwdW_eq_eRevW t E E₂ hd0 hd1]

/-- …hence the two evaluated **Jacobians** agree as homomorphisms. -/
theorem foxDHom_mFwdW_eq_mCompact
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hj2 : ∀ v : V, PWord.evalFin ⇑t E E₂ (j2W h) • v = v)
    (hd0 : PWord.evalFin ⇑t E E₂ (deltaCert h 0) ∈ trivAct C V)
    (hd1 : PWord.evalFin ⇑t E E₂ (deltaCert h 1) ∈ trivAct C V) :
    foxDHom ⇑t E E₂ (mFwdW α h) = foxDHom ⇑t E E₂ (mCompactW α h) (A := V) :=
  AddMonoidHom.ext fun a => foxD_mFwdW_eq_mCompact t E E₂ hwild hj2 hd0 hd1 a

end Rows

/-! ## The formal row

Pure `FoxCoeff` data — the same at every module of a class, with the projector `P` an opaque
atom and the `σ₂`-powers WW2's `TameSym.sigma2` atoms.  This is the Lean twin of the frozen
certificates' `fox_certificate.rows.wild.entries`. -/

/-- The `x_i`-slot of the compact-`M` alphabet. -/
def xIdx (h : ℕ) (i : Fin 3) : Fin (2 + 2 * h + 1) := ⟨(i : ℕ), by have := i.isLt; omega⟩

theorem coreLetter_wild (h : ℕ) (i : Fin 3) : coreLetter h i = Generator.wild (xIdx h i) := rfl

/-- **The universal compact-`M` wild row**

```
(σ, τ, x₀, x₁, x₂) = (0,  P·S₂^{−2m},  P·S₂^{−m} + P,  P·S₂^{−m} + P·S₂^{−2m},  S⁻¹ + P)
```

— the frozen certificates' `WILD_ROW` entry for entry, in their print order, with all `2h`
handle columns zero.  One piece of formal data, certified below at *both* interpretations
(`P ↦ 1` split/unramified, `P ↦ 0` ramified). -/
def mCompactWildRow (α h : ℕ) :
    FoxRowNormalForm (Generator (2 + 2 * h)) (TameSym (2 + 2 * h)) :=
  ⟨fun g => match g with
    | .sigma => .zero
    | .tau => .comp (.atom .proj) (.atom (.sigma2 (-(2 * (mOf α : ℤ)))))
    | .wild i =>
        if (i : ℕ) = 0 then
          .add (.comp (.atom .proj) (.atom (.sigma2 (-(mOf α : ℤ))))) (.atom .proj)
        else if (i : ℕ) = 1 then
          .add (.comp (.atom .proj) (.atom (.sigma2 (-(mOf α : ℤ)))))
            (.comp (.atom .proj) (.atom (.sigma2 (-(2 * (mOf α : ℤ))))))
        else if (i : ℕ) = 2 then .add (.atom (.gen .sigma (-1))) (.atom .proj)
        else .zero⟩

section RowData

variable {h α : ℕ}

@[simp] theorem mCompactWildRow_sigma : (mCompactWildRow α h).row .sigma = .zero := rfl

@[simp] theorem mCompactWildRow_tau :
    (mCompactWildRow α h).row .tau
      = .comp (.atom .proj) (.atom (.sigma2 (-(2 * (mOf α : ℤ))))) := rfl

@[simp] theorem mCompactWildRow_x0 :
    (mCompactWildRow α h).row (.wild (xIdx h 0))
      = .add (.comp (.atom .proj) (.atom (.sigma2 (-(mOf α : ℤ))))) (.atom .proj) := rfl

@[simp] theorem mCompactWildRow_x1 :
    (mCompactWildRow α h).row (.wild (xIdx h 1))
      = .add (.comp (.atom .proj) (.atom (.sigma2 (-(mOf α : ℤ)))))
          (.comp (.atom .proj) (.atom (.sigma2 (-(2 * (mOf α : ℤ)))))) := rfl

@[simp] theorem mCompactWildRow_x2 :
    (mCompactWildRow α h).row (.wild (xIdx h 2))
      = .add (.atom (.gen .sigma (-1))) (.atom .proj) := rfl

/-- **The `x₂`-entry is the compact-`N` word's `x₂`-entry**, on the nose — the frozen note
*"the `x_2` block is the compact-N boundary factor `J_2`"*, as an equation between certificate
data rather than a remark. -/
theorem mCompactWildRow_x2_eq_nCompactWildRow_x2 :
    (mCompactWildRow α h).row (.wild (xIdx h 2))
      = (Certificates.nCompactWildRow h).row (.wild (Certificates.x2Idx h)) := rfl

theorem mCompactWildRow_wild_ne {j : Fin (2 + 2 * h + 1)} (hj0 : (j : ℕ) ≠ 0)
    (hj1 : (j : ℕ) ≠ 1) (hj2 : (j : ℕ) ≠ 2) :
    (mCompactWildRow α h).row (.wild j) = .zero := by
  show (if (j : ℕ) = 0 then _ else if (j : ℕ) = 1 then _ else if (j : ℕ) = 2 then _ else _) = _
  rw [if_neg hj0, if_neg hj1, if_neg hj2]

theorem xIdx_zero_ne_one : (xIdx h 0) ≠ (xIdx h 1) := by simp [xIdx]
theorem xIdx_zero_ne_two : (xIdx h 0) ≠ (xIdx h 2) := by simp [xIdx]
theorem xIdx_one_ne_two : (xIdx h 1) ≠ (xIdx h 2) := by simp [xIdx]

variable {C : Type*} [Group C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]
  (t : Marking (2 + 2 * h) C) (π : AddMonoid.End V)

/-- **The universal row's denotation** at any projector assignment `π`. -/
theorem mCompactWildRow_toHom_apply (a : Generator (2 + 2 * h) → V) :
    (mCompactWildRow α h).toHom (TameSym.toEnd t π) a
      = π (((powOmega2 t.σ) ^ (2 * mOf α))⁻¹ • a .tau)
        + (π (((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 0)) + π (a (coreLetter h 0)))
        + (π (((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 1))
            + π (((powOmega2 t.σ) ^ (2 * mOf α))⁻¹ • a (coreLetter h 1)))
        + (t.σ⁻¹ • a (coreLetter h 2) + π (a (coreLetter h 2))) := by
  have hz : ∀ k : ℕ, ((powOmega2 t.σ) ^ (-(k : ℤ))) = ((powOmega2 t.σ) ^ k)⁻¹ := fun k => by
    rw [zpow_neg, zpow_natCast]
  rw [FoxRowNormalForm.toHom_apply,
    sum_generator_quad _ (xIdx h 0) (xIdx h 1) (xIdx h 2) xIdx_zero_ne_one xIdx_zero_ne_two
      xIdx_one_ne_two rfl fun j hj0 hj1 hj2 => by
        rw [mCompactWildRow_wild_ne (α := α) (fun hv => hj0 (Fin.ext hv))
          (fun hv => hj1 (Fin.ext hv)) (fun hv => hj2 (Fin.ext hv))]
        rfl]
  simp only [mCompactWildRow_tau, mCompactWildRow_x0, mCompactWildRow_x1, mCompactWildRow_x2,
    FoxCoeff.eval_add_apply, FoxCoeff.eval_comp_apply, FoxCoeff.eval_atom_apply,
    TameSym.toEnd_proj, TameSym.toEnd_sigma2_apply, TameSym.toEnd_gen_apply, Marking.apply_sigma]
  simp only [← coreLetter_wild]
  rw [show (-(2 * (mOf α : ℤ))) = -((2 * mOf α : ℕ) : ℤ) by push_cast; ring, hz, hz, zpow_neg,
    zpow_one]

end RowData

/-! ## The certificates

WW2 shape throughout: ops list + target + `verifies`, with every listed op carrying its
invertibility witness.  The tame relator is the compact-`N` lane's `Certificates.tameRelW`
unchanged (same relation `τ^σ = τ^{q_K}`), so its two rows `Certificates.tameRow` /
`Certificates.tameUnramRow` and its published-row certificate `Certificates.tameRowCertUnram`
are used here verbatim — this row contributes nothing new to the tame line.

The **operations are the frozen certificate's two**, and they are the pilot lane's:
`add_row(source 0, target 1, factor S)` in the unramified branch (`Certificates.nCompactUnramOps`
= Sage `AddRow(1,0,S)`) and `scale_col(x2, unit S)` in the ramified one
(`Certificates.nCompactRamOps`, whose carried formal inverse `S⁻¹` *is* the witness). -/

section Certificates

variable {h α q : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-! ### The published-row certificates (empty ops)

One formal row, `mCompactWildRow`, certified at *both* interpretations — the Lean form of the
frozen certificate's "one universal row + per-branch specializations". -/

/-- **The published compact-`M` wild row at every unramified simple tame module**: empty ops,
target the universal row read with `P ↦ 1`.  No hypothesis on `S` or `S₂`. -/
noncomputable def mCompactWildRowCertUnram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v) :
    FoxRowCertificate (TameSym.splitEnd (A := V) t) (foxDHom ⇑t E E₂ (mCompactW α h)) where
  colOps := []
  target := mCompactWildRow α h
  colOps_invertible := by simp
  verifies := by
    refine AddMonoidHom.ext fun a => ?_
    rw [foxRowApplyOps_nil, foxDHom_apply, foxD_mCompact_unram t E E₂ hV₂ hwild hτ,
      TameSym.splitEnd, mCompactWildRow_toHom_apply]
    show _ = ((powOmega2 t.σ) ^ (2 * mOf α))⁻¹ • a .tau
        + (((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 0) + a (coreLetter h 0))
        + (((powOmega2 t.σ) ^ mOf α)⁻¹ • a (coreLetter h 1)
          + ((powOmega2 t.σ) ^ (2 * mOf α))⁻¹ • a (coreLetter h 1))
        + (t.σ⁻¹ • a (coreLetter h 2) + a (coreLetter h 2))
    rw [sub_eq_add_neg, Certificates.neg_eq_self hV₂]
    abel

/-- **The published compact-`M` wild row at every ramified simple tame module**: the *same*
formal row read with `P ↦ 0`, i.e. `(0, 0, 0, 0, S⁻¹)` — a single unit entry.  Every `α`-carrying
entry of the universal row is a `P`-multiple, so the whole correction block and both `σ₂`-powers
leave the row here without any hypothesis on `S₂`. -/
noncomputable def mCompactWildRowCertRam (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hτfpf : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    FoxRowCertificate (TameSym.ramifiedEnd (A := V) t) (foxDHom ⇑t E E₂ (mCompactW α h)) where
  colOps := []
  target := mCompactWildRow α h
  colOps_invertible := by simp
  verifies := by
    refine AddMonoidHom.ext fun a => ?_
    rw [foxRowApplyOps_nil, foxDHom_apply, foxD_mCompact_ram t E E₂ hV₂ hwild hτfpf hTodd,
      TameSym.ramifiedEnd, mCompactWildRow_toHom_apply]
    show -(t.σ⁻¹ • a (coreLetter h 2))
        = (0 : V) + ((0 : V) + (0 : V)) + ((0 : V) + (0 : V))
          + (t.σ⁻¹ • a (coreLetter h 2) + (0 : V))
    rw [Certificates.neg_eq_self hV₂]
    abel

/-- **The published row at a *simple* unramified module is the compact-`N` row.**

Target `Certificates.nCompactWildRow h` — WN0-b's universal row, unchanged — under the
simple-module hypothesis `S₂ = 1`.  This is the frozen note *"its `1 − S^{-1}` term and its two
one-operation normal forms are shared with packet row WC-N0"* at its strongest: the two rows
coincide, not merely their normal forms. -/
noncomputable def mCompactWildRowCertUnramSimple (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hS₂ : ∀ v : V, powOmega2 t.σ • v = v) :
    FoxRowCertificate (TameSym.splitEnd (A := V) t) (foxDHom ⇑t E E₂ (mCompactW α h)) where
  colOps := []
  target := Certificates.nCompactWildRow h
  colOps_invertible := by simp
  verifies := by
    refine AddMonoidHom.ext fun a => ?_
    rw [foxRowApplyOps_nil, foxDHom_apply, foxD_mCompact_unram_simple t E E₂ hV₂ hwild hτ hS₂,
      TameSym.splitEnd, Certificates.nCompactWildRow_toHom_apply]
    show a .tau + (a (coreLetter h 2) - t.σ⁻¹ • a (coreLetter h 2))
        = a .tau + (t.σ⁻¹ • a (Words.coreLetter h 2) + a (Words.coreLetter h 2))
    rw [sub_eq_add_neg, Certificates.neg_eq_self hV₂]
    abel

/-- **The split (scalar) module certificate**: with `S = 1` the `1 − S⁻¹` block vanishes, the
`σ₂`-powers collapse with it, and the row *is already* the standard `τ`-pivot. -/
noncomputable def mCompactWildRowCertSplit (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hσ : ∀ v : V, t.σ • v = v) :
    FoxRowCertificate (TameSym.splitEnd (A := V) t) (foxDHom ⇑t E E₂ (mCompactW α h)) where
  colOps := []
  target := .single .tau
  colOps_invertible := by simp
  verifies := by
    refine AddMonoidHom.ext fun a => ?_
    rw [foxRowApplyOps_nil, foxDHom_apply, foxD_mCompact_split t E E₂ hV₂ hwild hτ hσ,
      FoxRowNormalForm.single_toHom_apply]

/-! ### The one-op normal forms

Both are the pilot lane's, on the nose: `Certificates.nCompactUnramNormalForm` (the diagonal
`(τ ↦ S⁻¹ ; x₂ ↦ 1 − S⁻¹)`) and `Certificates.nCompactRamNormalForm` (`x₂ ↦ 1`, tame row
untouched). -/

/-- **The unramified branch's one-op normal form** — the headline of the ticket.

A single row operation `row_wild += S · row_tame` (Sage `AddRow(1, 0, S)`) carries the evaluated
Jacobian of `⟨σ, τ, x₀, x₁, x₂, … ∣ τ^σ = τ^{q_K}, R_{M,0} = 1⟩` to the **diagonal**
`(τ ↦ S⁻¹ ; x₂ ↦ 1 − S⁻¹)`, both entries units on a nontrivial simple unramified module
(`Certificates.isUnit_oneSubSInvEnd_iff` for the second: invertible **iff** `V^S = 0`).

The simple-module hypothesis `hS₂` is where the `α`-dependence goes: without it the row still
carries `P·(1+S₂^{−m})` on `x₀` and `P·(S₂^{−m}+S₂^{−2m})` on `x₁`, and the *diagonal* normal
form is not reached (this is `specialize_unramified(simple=False)` on the Sage side). -/
noncomputable def mCompactJacobianCertUnram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hS₂ : ∀ v : V, powOmega2 t.σ • v = v) (hq : Even q) :
    FoxCertificate (TameSym.splitEnd (A := V) t)
      (foxJacobian ⇑t E E₂ (Certificates.tameRelW (2 + 2 * h) q) (mCompactW α h)) where
  rowOps := Certificates.nCompactUnramOps _
  colOps := []
  target := Certificates.nCompactUnramNormalForm h
  rowOps_invertible := by
    intro r hr
    rw [Certificates.nCompactUnramOps, List.mem_singleton] at hr
    subst hr
    trivial
  colOps_invertible := by simp
  verifies := by
    refine AddMonoidHom.ext fun a => ?_
    rw [foxApplyOps_apply, FoxColOp.listHom_nil, AddMonoidHom.id_apply,
      Certificates.nCompactUnramOps, FoxRowOp.listHom_cons, FoxRowOp.listHom_nil,
      AddMonoidHom.comp_apply, AddMonoidHom.id_apply, foxJacobian_apply,
      FoxRowOp.toHom_addSnd_apply, FoxNormalForm.toHom_apply]
    refine Prod.ext ?_ ?_
    · show foxD ⇑t a E E₂ (Certificates.tameRelW (2 + 2 * h) q) = _
      rw [Certificates.foxD_tameRelW_unram t E E₂ hV₂ hτ hq,
        Certificates.nCompactUnramNormalForm, TameSym.splitEnd,
        Certificates.tameUnramRow_toHom_apply]
    · show foxD ⇑t a E E₂ (mCompactW α h)
          + (FoxCoeff.atom (TameSym.gen Generator.sigma 1)).eval _
            (foxD ⇑t a E E₂ (Certificates.tameRelW (2 + 2 * h) q)) = _
      rw [foxD_mCompact_unram_simple t E E₂ hV₂ hwild hτ hS₂,
        Certificates.foxD_tameRelW_unram t E E₂ hV₂ hτ hq, FoxCoeff.eval_atom_apply,
        TameSym.toEnd_gen_apply, Marking.apply_sigma, zpow_one, smul_inv_smul,
        Certificates.nCompactUnramNormalForm, TameSym.splitEnd,
        Certificates.nCompactBlockRow_toHom_apply]
      simp only [← coreLetter_eq]
      rw [show a .tau + (a (coreLetter h 2) - t.σ⁻¹ • a (coreLetter h 2)) + a .tau
          = (a .tau + a .tau) + (a (coreLetter h 2) - t.σ⁻¹ • a (coreLetter h 2)) from by abel,
        hV₂, zero_add]

/-- **The ramified branch's one-op normal form.**

A single column operation `col_{x₂} *= S` (Sage `ScaleCol(x2, S)`), whose carried formal inverse
`S⁻¹` *is* its invertibility witness, turns the wild row's single unit entry `−S⁻¹` into `1`.
No simple-module hypothesis is needed here: `P ↦ 0` has already erased every other entry. -/
noncomputable def mCompactJacobianCertRam (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hτfpf : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v)
    (hrel : conjR t.τ t.σ = t.τ ^ q) :
    FoxCertificate (TameSym.ramifiedEnd (A := V) t)
      (foxJacobian ⇑t E E₂ (Certificates.tameRelW (2 + 2 * h) q) (mCompactW α h)) where
  rowOps := []
  colOps := Certificates.nCompactRamOps h
  target := Certificates.nCompactRamNormalForm h q
  rowOps_invertible := by simp
  colOps_invertible := by
    intro c hc
    rw [Certificates.nCompactRamOps, List.mem_singleton] at hc
    subst hc
    exact ⟨Certificates.sigmaAtom_mul t 0 (by ring), Certificates.sigmaAtom_mul t 0 (by ring)⟩
  verifies := by
    refine AddMonoidHom.ext fun a => ?_
    rw [foxApplyOps_apply, FoxRowOp.listHom_nil, AddMonoidHom.id_apply,
      Certificates.nCompactRamOps, FoxColOp.listHom_cons, FoxColOp.listHom_nil,
      AddMonoidHom.comp_apply, AddMonoidHom.id_apply, foxJacobian_apply,
      FoxNormalForm.toHom_apply]
    set b := FoxColOp.toHom (TameSym.ramifiedEnd (A := V) t)
      (.scale (Words.coreLetter h 2) (.atom (.gen .sigma 1)) (.atom (.gen .sigma (-1)))) a with hb
    have hbτ : b .tau = a .tau := by
      rw [hb, FoxColOp.toHom_scale_apply, if_neg (Certificates.tau_ne_coreLetter_two h)]
    have hbσ : b .sigma = a .sigma := by
      rw [hb, FoxColOp.toHom_scale_apply, if_neg (Certificates.sigma_ne_coreLetter_two h)]
    have hbx : b (coreLetter h 2) = t.σ • a (coreLetter h 2) := by
      rw [hb, coreLetter_eq, FoxColOp.toHom_scale_apply, if_pos rfl, FoxCoeff.eval_atom_apply,
        TameSym.toEnd_gen_apply, Marking.apply_sigma, zpow_one]
    refine Prod.ext ?_ ?_
    · show foxD ⇑t b E E₂ (Certificates.tameRelW (2 + 2 * h) q) = _
      rw [Certificates.foxD_tameRelW_of_tameRel t E E₂ hrel, hbτ, hbσ,
        Certificates.nCompactRamNormalForm, TameSym.ramifiedEnd, Certificates.tameRow_toHom_apply]
      simp only [smul_add, smul_sub]
      abel
    · show foxD ⇑t b E E₂ (mCompactW α h)
          = (FoxRowNormalForm.single (Words.coreLetter h 2)).toHom (TameSym.ramifiedEnd t) a
      rw [foxD_mCompact_ram t E E₂ hV₂ hwild hτfpf hTodd, hbx, inv_smul_smul,
        FoxRowNormalForm.single_toHom_apply, Certificates.neg_eq_self hV₂, coreLetter_eq]

end Certificates

/-! ## The instances

Three `h = 0` rows over the five-letter alphabet `Generator 2 = {σ, τ, x₀, x₁, x₂}`:

| instance | `(α, h, q_K)` | `m = 2^{α−1}` | `candidate_id` | digest |
|---|---|---|---|---|
| engine / canonical | `(2, 0, 2)` | `2` | `M-compact-alpha2-h0-q2-v001` | `7c9005f50f9e1d5d…` |
| `ℚ₂(√2)` | `(3, 0, 2)` | `4` | `M-compact-alpha3-h0-q2-v001` | `0209b708538277e0…` |
| `ℚ₂(√5)` | `(2, 0, 4)` | `2` | `M-compact-alpha2-h0-q4-v001` | `7c9005f50f9e1d5d…` |

WM0-a pinned all three trees (`Words.MCompact.denote_rawMCompact_*`,
`rawMCompact_alpha{2,3}_h0_*_astHash`), so the words below are the frozen certificates' words.

⚠ **The canonical and `√5` rows share a *word*** — `q_K` sits in the tame relation, not in the
word, which is WM0-a's `astHash_q2_eq_q4` — so their **wild** rows are literally the same object
(`sqrtFive_wildRow_eq_canonical`) and only the **tame** row separates them
(`foxD_sqrtFive_tame_ram` against `foxD_canonical_tame_ram`).  That is the arithmetic visibility
of `q_K` which the shared word hash cannot express. -/

section Instances

variable {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking 2 C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-! ### The engine instance `(α, h, q_K) = (2, 0, 2)` — freeze row 4's quoted digest -/

/-- **The canonical wild row on a general unramified module** (`m = 2`), with the `σ₂`-powers
still present: `(0, S₂^{−4}, 1+S₂^{−2}, S₂^{−2}+S₂^{−4}, 1−S⁻¹)`. -/
theorem foxD_canonical_unram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin 3) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (a : Generator 2 → V) :
    foxD ⇑t a E E₂ (mCompactW 2 0)
      = ((powOmega2 t.σ) ^ 4)⁻¹ • a .tau
        + (a (.wild 0) + ((powOmega2 t.σ) ^ 2)⁻¹ • a (.wild 0))
        + (((powOmega2 t.σ) ^ 2)⁻¹ • a (.wild 1) + ((powOmega2 t.σ) ^ 4)⁻¹ • a (.wild 1))
        + (a (.wild 2) - t.σ⁻¹ • a (.wild 2)) :=
  foxD_mCompact_unram (h := 0) (α := 2) t E E₂ hV₂ hwild hτ a

/-- **The canonical wild row on a *simple* unramified module**: `(0, 1, 0, 0, 1 − S⁻¹)` — the
frozen certificate's printed unramified specialization. -/
theorem foxD_canonical_unram_simple (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin 3) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hS₂ : ∀ v : V, powOmega2 t.σ • v = v) (a : Generator 2 → V) :
    foxD ⇑t a E E₂ (mCompactW 2 0) = a .tau + (a (.wild 2) - t.σ⁻¹ • a (.wild 2)) :=
  foxD_mCompact_unram_simple (h := 0) (α := 2) t E E₂ hV₂ hwild hτ hS₂ a

/-- **The canonical wild row on a ramified simple module**: `(0, 0, 0, 0, −S⁻¹)`. -/
theorem foxD_canonical_ram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin 3) (v : V), t.x i • v = v) (hτfpf : ∀ v : V, t.τ • v = v → v = 0)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (a : Generator 2 → V) :
    foxD ⇑t a E E₂ (mCompactW 2 0) = -(t.σ⁻¹ • a (.wild 2)) :=
  foxD_mCompact_ram (h := 0) (α := 2) t E E₂ hV₂ hwild hτfpf hTodd a

/-- **The canonical wild row on the scalar module**: `(0, 1, 0, 0, 0)`. -/
theorem foxD_canonical_split (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin 3) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hσ : ∀ v : V, t.σ • v = v) (a : Generator 2 → V) :
    foxD ⇑t a E E₂ (mCompactW 2 0) = a .tau :=
  foxD_mCompact_split (h := 0) (α := 2) t E E₂ hV₂ hwild hτ hσ a

/-- **The canonical ramified tame row** at `q_K = 2`: `(S⁻¹(T−1), S⁻¹ − 1 − T, 0, 0, 0)` — the
compact-`N` lane's tame row at the same `q`, reused. -/
theorem foxD_canonical_tame_ram (hrel : conjR t.τ t.σ = t.τ ^ 2) (a : Generator 2 → V) :
    foxD ⇑t a E E₂ (Certificates.tameRelW 2 2)
      = t.σ⁻¹ • (t.τ • a .sigma - a .sigma)
        + (t.σ⁻¹ • a .tau - (a .tau + t.τ • a .tau)) :=
  Certificates.foxD_sqrtNegTwo_tame_ram t E E₂ hrel a

/-- The canonical instance's two Jacobian certificates: unramified branch (one row op). -/
noncomputable def canonicalJacobianCertUnram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin 3) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hS₂ : ∀ v : V, powOmega2 t.σ • v = v) :
    FoxCertificate (TameSym.splitEnd (A := V) t)
      (foxJacobian ⇑t E E₂ (Certificates.tameRelW 2 2) (mCompactW 2 0)) :=
  mCompactJacobianCertUnram (h := 0) (α := 2) t E E₂ hV₂ hwild hτ hS₂ (by decide)

@[inherit_doc canonicalJacobianCertUnram]
noncomputable def canonicalJacobianCertRam (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin 3) (v : V), t.x i • v = v) (hτfpf : ∀ v : V, t.τ • v = v → v = 0)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (hrel : conjR t.τ t.σ = t.τ ^ 2) :
    FoxCertificate (TameSym.ramifiedEnd (A := V) t)
      (foxJacobian ⇑t E E₂ (Certificates.tameRelW 2 2) (mCompactW 2 0)) :=
  mCompactJacobianCertRam (h := 0) (α := 2) t E E₂ hV₂ hwild hτfpf hTodd hrel

/-! ### `ℚ₂(√2)`: `(α, q_K) = (3, 2)`, `m = 4`, `2m = 8` -/

/-- **The `√2` wild row on a general unramified module**: `(0, S₂^{−8}, 1+S₂^{−4},
S₂^{−4}+S₂^{−8}, 1−S⁻¹)`.  The `α`-dependence of this row is *exactly* the two `σ₂`-exponents —
compare the canonical row's `4`/`2` with this row's `8`/`4`. -/
theorem foxD_sqrtTwo_unram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin 3) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (a : Generator 2 → V) :
    foxD ⇑t a E E₂ (mCompactW 3 0)
      = ((powOmega2 t.σ) ^ 8)⁻¹ • a .tau
        + (a (.wild 0) + ((powOmega2 t.σ) ^ 4)⁻¹ • a (.wild 0))
        + (((powOmega2 t.σ) ^ 4)⁻¹ • a (.wild 1) + ((powOmega2 t.σ) ^ 8)⁻¹ • a (.wild 1))
        + (a (.wild 2) - t.σ⁻¹ • a (.wild 2)) :=
  foxD_mCompact_unram (h := 0) (α := 3) t E E₂ hV₂ hwild hτ a

/-- **The `√2` wild row on a simple unramified module**: `(0, 1, 0, 0, 1 − S⁻¹)` — identical to
the canonical instance's, `α` having left with `S₂`. -/
theorem foxD_sqrtTwo_unram_simple (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin 3) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hS₂ : ∀ v : V, powOmega2 t.σ • v = v) (a : Generator 2 → V) :
    foxD ⇑t a E E₂ (mCompactW 3 0) = a .tau + (a (.wild 2) - t.σ⁻¹ • a (.wild 2)) :=
  foxD_mCompact_unram_simple (h := 0) (α := 3) t E E₂ hV₂ hwild hτ hS₂ a

/-- **The `√2` wild row on a ramified simple module**: `(0, 0, 0, 0, −S⁻¹)`. -/
theorem foxD_sqrtTwo_ram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin 3) (v : V), t.x i • v = v) (hτfpf : ∀ v : V, t.τ • v = v → v = 0)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (a : Generator 2 → V) :
    foxD ⇑t a E E₂ (mCompactW 3 0) = -(t.σ⁻¹ • a (.wild 2)) :=
  foxD_mCompact_ram (h := 0) (α := 3) t E E₂ hV₂ hwild hτfpf hTodd a

/-- **The `ℚ₂(√2)` Jacobian certificate, unramified branch** (`q_K = 2`). -/
noncomputable def sqrtTwoJacobianCertUnram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin 3) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hS₂ : ∀ v : V, powOmega2 t.σ • v = v) :
    FoxCertificate (TameSym.splitEnd (A := V) t)
      (foxJacobian ⇑t E E₂ (Certificates.tameRelW 2 2) (mCompactW 3 0)) :=
  mCompactJacobianCertUnram (h := 0) (α := 3) t E E₂ hV₂ hwild hτ hS₂ (by decide)

/-- **The `ℚ₂(√2)` Jacobian certificate, ramified branch**: one column scaling `col_{x₂} *= S`. -/
noncomputable def sqrtTwoJacobianCertRam (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin 3) (v : V), t.x i • v = v) (hτfpf : ∀ v : V, t.τ • v = v → v = 0)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (hrel : conjR t.τ t.σ = t.τ ^ 2) :
    FoxCertificate (TameSym.ramifiedEnd (A := V) t)
      (foxJacobian ⇑t E E₂ (Certificates.tameRelW 2 2) (mCompactW 3 0)) :=
  mCompactJacobianCertRam (h := 0) (α := 3) t E E₂ hV₂ hwild hτfpf hTodd hrel

/-! ### `ℚ₂(√5)`: `(α, q_K) = (2, 4)`, `m = 2` — the same word, a different tame relation -/

/-- **`q_K` is invisible to the wild row, and it is exactly the tame row that sees it.**

The `ℚ₂(√5)` candidate and the engine instance are the *same tree* (WM0-a's
`astHash_q2_eq_q4`), so `mCompactW 2 0` carries no `q`-argument at all and every wild-row
statement above serves both candidates verbatim.  The separation is here: the two tame rows
differ **as formal certificate data**, by a kernel `decide` on the norm coefficient
`N_q(T) = 1 + T + ⋯ + T^{q−1}`.  This is the certificate-level shadow of WM0-a's finding that a
word hash is not a key for the frozen family — the `candidate_id` is. -/
theorem tameRow_two_ne_four :
    (Certificates.tameRow 2 2).row .tau ≠ (Certificates.tameRow 2 4).row .tau := by decide

/-- **The `√5` wild row on a simple unramified module**: `(0, 1, 0, 0, 1 − S⁻¹)`. -/
theorem foxD_sqrtFive_unram_simple (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin 3) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hS₂ : ∀ v : V, powOmega2 t.σ • v = v) (a : Generator 2 → V) :
    foxD ⇑t a E E₂ (mCompactW 2 0) = a .tau + (a (.wild 2) - t.σ⁻¹ • a (.wild 2)) :=
  foxD_mCompact_unram_simple (h := 0) (α := 2) t E E₂ hV₂ hwild hτ hS₂ a

/-- **The `√5` wild row on a ramified simple module**: `(0, 0, 0, 0, −S⁻¹)`. -/
theorem foxD_sqrtFive_ram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin 3) (v : V), t.x i • v = v) (hτfpf : ∀ v : V, t.τ • v = v → v = 0)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (a : Generator 2 → V) :
    foxD ⇑t a E E₂ (mCompactW 2 0) = -(t.σ⁻¹ • a (.wild 2)) :=
  foxD_mCompact_ram (h := 0) (α := 2) t E E₂ hV₂ hwild hτfpf hTodd a

/-- **The `√5` ramified tame row**, spelled out at `q_K = 4`:

```
(S⁻¹(T−1),  S⁻¹ − 1 − T − T² − T³,  0, 0, 0)
```

— *this* is where `q_K = 4` becomes visible, and it is the whole difference between the `√5`
candidate and the engine instance at the certificate level. -/
theorem foxD_sqrtFive_tame_ram (hrel : conjR t.τ t.σ = t.τ ^ 4) (a : Generator 2 → V) :
    foxD ⇑t a E E₂ (Certificates.tameRelW 2 4)
      = t.σ⁻¹ • (t.τ • a .sigma - a .sigma)
        + (t.σ⁻¹ • a .tau
          - (a .tau + t.τ • a .tau + t.τ ^ 2 • a .tau + t.τ ^ 3 • a .tau)) := by
  rw [Certificates.foxD_tameRelW_of_tameRel t E E₂ hrel a, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one,
    one_smul]
  simp only [smul_add, smul_sub]
  abel

/-- **The `ℚ₂(√5)` Jacobian certificate, unramified branch** (`q_K = 4`, still even). -/
noncomputable def sqrtFiveJacobianCertUnram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin 3) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hS₂ : ∀ v : V, powOmega2 t.σ • v = v) :
    FoxCertificate (TameSym.splitEnd (A := V) t)
      (foxJacobian ⇑t E E₂ (Certificates.tameRelW 2 4) (mCompactW 2 0)) :=
  mCompactJacobianCertUnram (h := 0) (α := 2) t E E₂ hV₂ hwild hτ hS₂ (by decide)

/-- **The `ℚ₂(√5)` Jacobian certificate, ramified branch**: the tame row here is the `q = 4`
one, which is where the two `α = 2` candidates finally differ. -/
noncomputable def sqrtFiveJacobianCertRam (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin 3) (v : V), t.x i • v = v) (hτfpf : ∀ v : V, t.τ • v = v → v = 0)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (hrel : conjR t.τ t.σ = t.τ ^ 4) :
    FoxCertificate (TameSym.ramifiedEnd (A := V) t)
      (foxJacobian ⇑t E E₂ (Certificates.tameRelW 2 4) (mCompactW 2 0)) :=
  mCompactJacobianCertRam (h := 0) (α := 2) t E E₂ hV₂ hwild hτfpf hTodd hrel

end Instances

end GQ2.Dyadic.Certificates.MCompact

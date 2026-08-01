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

The word is a **six-factor `prodList`** whose factors do *not* all act trivially — `A₀²` acts as
`S₂^{−2m}` and `σ₂^{2m}` as `S₂^{2m}` — so the compact-`N` shortcut
`foxD_prodList_of_trivial` is unavailable and each factor enters weighted by the **lower value
of its prefix** (`D(uv) = D(u) + ū·D(v)`, iterated).  That weighting is the whole story:

* **`A₀² `** (prefix `1`): `−(1 + S₂^{−m})·a(x₀) − (1 + S₂^{−m})S₂^{−m}·𝒢_m` where
  `𝒢_k = (1 + S₂ + ⋯ + S₂^{k−1})·D(σ₂)` (`foxD_leadingSquare`).  `D(σ₂)` is **never computed**:
  it is the Sage engine's opaque atom `G[S;ω₂]` (`omega_proj`'s last branch — `σ` is
  unramified, so its `ω₂`-power is *not* a projector), and it cancels before the row is reached.
* **`[A₀,x₁]`** (prefix `S₂^{−2m}`): locally `(1 − S₂^{m})·a(x₁)`
  (`foxD_comm_of_trivial_right`), weighted to `S₂^{−2m}·a(x₁) − S₂^{−m}·a(x₁)`.  No `x₀`, no
  `σ`: the two `D(A₀)` copies of the commutator cancel.
* **`σ₂^{2m}`** (prefix `S₂^{−2m}`): `S₂^{−2m}·𝒢_{2m}`.  **This is the `σ`-column cancellation**
  (`foxD_mCompact_sigma_column`): `𝒢_{2m} = 𝒢_m + S₂^m·𝒢_m` (`sigmaGeom_two_mul`), so the
  weighted contribution is `(S₂^{−2m} + S₂^{−m})·𝒢_m`, *identical* to the `A₀²` contribution —
  and it cancels **over `ℤ`**, without any characteristic-`2` hypothesis.  Mathematically this
  is the packet's power balance `−2·2^{α−1} + 2^α = 0` differentiated once.
* **`J₂`** (prefix `S₂^{−2m}·S₂^{2m} = 1`): `−S⁻¹·a(x₂) + P·(a(x₂) + a(τ))` — *the compact-`N`
  factors verbatim* (`foxD_j2W_unram`/`_ram` are proved by `exact`-ing WN0-b's own lemmas).
* **`E_m^rev`** (prefix `1`): all four conjugated `δ`-letters act trivially, so
  `D(E_m^rev) = (S₂^{−2m}+S₂^{−m})·D(δ₁) + (S₂^{−m}+1)·D(δ₀)` with
  `D(δ_i) = (P+1)·a(x_i) + P·a(τ)` (`foxD_deltaC`).
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
   `foxD_mFwdW_eq_mCompact` and equality of the whole evaluated Jacobian
   (`foxJacobian_mFwdW_eq_mCompact`): the four factors all act trivially, so the product rule
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

**Audited 2026-07-31, all named declarations of this file**: every one depends on a subset of
the standard axioms `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, no
`Lean.ofReduceBool` (no `native_decide`), and no `B`-axiom of the dyadic census leaks through
the `Words.M0 → TameBoundary → MarkedCore` import chain.  The census stays at **eleven**.

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
`foxD_comm_of_trivial_right`, `foxD_conj_of_trivial`, `foxD_prodList_weighted`,
`geom_pow_smul_two_mul`, and the four-support alphabet sum `sum_generator_quad`.  All four
belong beside WWH's `foxD_prodList_of_trivial` in `GQ2/Dyadic/Word/Fox.lean`.
-/

namespace GQ2.Dyadic.Certificates.MCompact

open GQ2.FoxH GQ2.Dyadic.Words.MCompact

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

/-- `MCompact`'s alphabet helpers are WN0-a's, on the nose — the two `Words` namespaces exist
only because the letters would otherwise be declared twice (WM0-a deviation 2, ticket WAH). -/
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
  simp only [coreLetter_eq]
  rw [foxD_invConjX2 t E E₂ hwild, foxD_deltaBlock_unram t E E₂ hV₂ hwild hτ,
    PWord.evalFin_inv, PWord.evalFin_conj, PWord.evalFin_gen, PWord.evalFin_gen,
    mem_trivAct.mp (inv_mem (trivAct_conjR (Certificates.trivAct_coreLetter t hwild 2) _))]

/-- **Factor 4, ramified (`P = 0`)** — `D(J₂) = −S⁻¹·a(x₂)`. -/
theorem foxD_j2W_ram (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hτfpf : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (j2W h) = -(t.σ⁻¹ • a (coreLetter h 2)) := by
  rw [j2W, foxD_prodList_pair]
  simp only [coreLetter_eq]
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

end Rows

end GQ2.Dyadic.Certificates.MCompact

# Eichler-reduction note (lane SQ, P2 residue) — 2026-08-05

Companion to `GQ2/Dyadic/SqCore/EichlerReduction.lean` (compiles clean at HEAD 0119687b,
all prints std-3).  Status: `SqHandleEichler h c` is **reduced**, not discharged.  What
remains is one word-level seed per `(j, k odd)`, and it is a machine-search problem.

## What is proved (Lean, banked)

1. `sqEichlerMoveAt_add` — Eichler moves at one handle **compose additively in `k`**
   (pivot row and `v_j`-hypothesis both transport).  Hence
   `sqHandleEichler_of_unit_moves`: the unit slice `k ∈ ℤ₂ˣ` generates everything
   (`k = 1 + (k−1)`).  This *replaces* the M/N lane's `θ_w`-conjugation / `SL₂ = E₂`
   rescaling machinery at this seam.
2. `sq_absorb` + `sqRelWord_sqEichlerSub_eq_one` — the relator dies as soon as the core
   defect of the four-slot substitution is the `handlePrefix`-conjugate of one
   `[v_j, ρ]^{u_j}`-commutator.
3. `SqEichlerSeed` + `sqEichlerMoveAt_of_seed` + `sqHandleEichler_of_seeds` +
   `sqHandleMixFixesCore_of_seeds` — the full assembly from seeds on the unit slice.
4. `sqWord_tau_sigma_defect` — the excluded transvection `σ ↦ x₁^k·σ` has defect exactly
   `[x₁^k, x₀]^σ` (one conjugated commutator).

## The class-two balance (do not re-derive)

Sites/suffix-classes of `C_sq·[u,v]` give, for `σ ↦ σβ₁`, `x₀ ↦ x₀β₀`, `x₁ ↦ x₁β₂`,
`u ↦ ρu` with `β̄ᵢ = aᵢ·v̄`, `ρ̄ = k(σ̄ − c x̄₀) + a_u v̄`:

```
Δ₂ = [a₁v̄, x̄₀] − [a₀v̄, σ̄ − 10x̄₀ + 8x̄₁] + [a₂v̄, x̄₁] + [ρ̄, v̄]   (mod cross-terms)
```

Relations available in gr₂: the relator's quadratic form (no `[v̄,σ̄]`-part) and
`2[t̄, ḡ] ≡ 0`, `t̄ = x̄₁ − 2x̄₀` (no `[v̄,σ̄]`-part either).  Forced first-order solution:

```
a₀ = −k ,   a₂ = 2a₀ = −2k (degree-1) ,   m = 3k (coefficient of 2[t̄,v̄]) ,
a₁ = −10a₀ − kc − 4m = −k(2+c) ,   a_v = 0 (v-slot never moves).
```

Consequences: (i) the two-slot (σ, u) scaffold is unsatisfiable for every odd `k` — the
first version of the Lean file had that scaffold and was rewritten; (ii) the necessity of
the `v_j`-row hypothesis re-derives (without it the `x₀`-row moves by `−k·ν'(v_j)`);
(iii) at even `k` all coefficients are even — consistent with the cup-form parity lore.

## Basis-independent walls (why no HM2-shape decomposition exists)

* Evenness: relator abelianization `2t̄` ⇒ every letter-degree even in every basis ⇒ no
  once-occurring moved letter.
* Syllable counts: the reduced core has 6 σ-syllables (4 cyclically), 4 `x₁`, 2 `x₀` but
  with degree −4; the `(w, x, t)`-basis (`σ = w·x₀^c`, `x₁ = t·x₀²`) fixes all degrees but
  has 9 `x₀`-syllables from trapped `x₀^{±c}`-dressings.  HM2's form needs exactly 2.

## The residual search (recommendation)

Search for the seed words at `k = 1` (unit slice suffices; general odd `k` should follow
the same shape with `zpowZtwo`-exponents).  Ansatz space, in the harness's letters
(`~/claude/general_2adic/dyadic_search`, `fg.py`-style, extended by a commuting formal
power `X = x₀^c`): words of bounded length in conjugates of `v_j`, `u_j`, `w = σX⁻¹`,
`ζ_j`-dressings, with the leading classes above imposed.  Target identity (h = 1, j = 0
first; `P = 1`):

```
sqWord(σβ₁, x₀β₀, x₁β₂) · [ρu, v] = sqWord(σ, x₀, x₁) · [u, v]     (free, or mod ⟨⟨R⟩⟩)
```

plus Nielsen invertibility of the image tuple.  The Lean interface accepts a defect that
holds only in `D_sq` (mod the relator), which is strictly easier than the free identity
the M/N lane proved.  On success, fill one `SqEichlerSeed` per `(j, k)` and the chain
`sqHandleEichler_of_seeds → sqHandleMixFixesCore_of_seeds → certificate` closes P2 with
no new axiom.

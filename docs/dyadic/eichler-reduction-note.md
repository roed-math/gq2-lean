# Eichler-reduction note (lane SQ, P2 residue) — 2026-08-05

Companion to `GQ2/Dyadic/SqCore/EichlerReduction.lean` (compiles clean at HEAD 0119687b,
all prints std-3).  Status: `SqHandleEichler h c` is **reduced**, not discharged.

> ⚠ **Updated 2026-08-07.**  Sections 1–3 stand.  The *search target* has moved: the word-level
> `SqEichlerSeed` per `(j, k odd)` this note originally recommended is refuted, along with every
> family that dresses the moved slots by words in the two cleared letters.  The live target is
> `SqArbRelWord h`, equivalently `SqClearingStep h`, equivalently `SqLamMarkTransitivity h`.  See
> the rewritten final section, and read the index warning in "The class-two balance" before
> quoting any `aᵢ` from here.

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

> ⚠ **Index convention — read this before quoting `a₀`/`a₁` anywhere else (W46).**  The
> substitution below is written `σ ↦ σβ₁`, `x₀ ↦ x₀β₀`, so the *subscript on `a` is the letter's
> subscript, not the slot's position*:
>
> | weight | dresses the slot | slot position in `sqArbFrame` |
> | --- | --- | --- |
> | `a₀` | `x₀` | 1 |
> | `a₁` | `σ` | 0 |
> | `a₂` | `x₁` | 2 |
> | `a_u` | `u_j` | 3 |
>
> A naive read inverts the forcing's slot.  The balance's forced value `a₀ = −k` is the
> **`x₀`-slot** dressing — which is exactly `SqCore/CommFrames.lean`'s and
> `SqCore/GradedTwo.lean`'s `sqArbFrame_x0_dressing_forced`, whose forced weight is written
> `ā₁` there because `ArbFrames` indexes dressings by *slot position*.  Same statement, opposite
> subscript.

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

## The residual search (rewritten 2026-08-07 — the old target is refuted)

> ⚠ **What this section used to say is dead.**  It recommended searching an ansatz space of
> *words in the moved letters* — bounded-length words in conjugates of `v_j`, `u_j`,
> `w = σ·x₀^{−c}` — for a `SqEichlerSeed`, and it posed the identity on the two-slot `(σ, u)`
> scaffold.  Every family of that shape is now closed:
>
> * the two-slot scaffold is unsatisfiable for every odd `k` — consequence (i) of the balance
>   above, and the reason the first version of `EichlerReduction.lean` was rewritten;
> * `SqCore/EichRefutation.lean` §3 refutes the `V`-dressed family `sqEichFrame`, the `U`-dressed
>   `sqEichFrameT`, and their disjunction `SqEichRelWordMix`, **at every weight triple** — not
>   at the class-two-forced parameters only, so none is a near miss with a correction term.  The
>   witness is a homomorphism to `D₄ ≅ Heis(𝔽₂)` that kills one of the two moved letters; the
>   dressings die with it and the bare core word is the inverse of a nontrivial commutator;
> * `SqCore/UVFrames.lean`'s two-letter widening `sqEichFrameUV` — each moved slot dressed by
>   `U^k V^l`, containing both families above as slices — dies too, by a *different* mechanism:
>   `EichRefutation` §7's collapse lemma (identify the two cleared letters onto an involution)
>   and its `D₈` instance `not_sqEichRelWordUV`, at the single marking `nuSel h j 1 1`.
>
> So no search over words in `U` and `V` can succeed, and the `SqEichlerSeed` →
> `sqHandleEichler_of_seeds` → `sqHandleMixFixesCore_of_seeds` chain has no reachable input.
> The *idea* survives; the letter alphabet does not.

**The live target.**  Dress the moved slots by **arbitrary** `λ`-trivial, `ν'`-trivial elements
instead of by words in the cleared letters.  That family is `sqArbFrame`
(`SqCore/ArbFrames.lean` §4), and its word equation `SqArbRelWord h` is the whole residual:

```text
sqArbRelWord_iff_clearingStep         : SqArbRelWord h ↔ SqClearingStep h   (ArbFrames §6)
sqClearingStep_iff                    : SqClearingStep h ↔ SqLamMarkTransitivity h  (CommFrames §1)
sqArbRelWord_iff_lamMarkTransitivity  : SqArbRelWord h ↔ SqLamMarkTransitivity h    (CommFrames §1)
```

all at **every** `h`.  Two consequences worth stating plainly.  First, the family cannot be
widened further inside the one-handle scheme — it already *is* the scheme, because
`sqArbRelWord_of_clearingStep` reads the dressings straight off a clearing automorphism.  Second,
no homomorphism-based probe can refute it without refuting `SqLamMarkTransitivity` itself, which
is why the two mechanisms that killed the word families provably cannot reach it.

**The explicit five-word normal form.**  With `base = (σ, x₀, x₁, U, V, …)` — the `j`-th handle
letters cleared, everything else standing — the target is: exhibit

```text
a : Fin (sqRank h) → D_sq h ,   a i ∈ ker λ ∩ ker ν' ,   m i = base i · a i
```

with `sqRelWord (sqArbFrame h ν' j a) = 1`.  Only five slots are moved, so it is five words.
Everything else is discharged: the `λ`- and `ν'`-rows transpose verbatim from `LamFrames` §2a
(they use only that the dressing is `λ`- and `ν'`-trivial), surjectivity is the mod-2 Frattini
criterion `SqModTwoIndep` (`ArbFrames` §1–§2 — the slots span `H₁` over `𝔽₂`; no strip-off, no
`d = d' = 0` restriction), and the composition into the handle stratum is
`sqHandleMixFixesCore_of_arbRelWord`.

**What the balance above now contributes** — guidance, not a scaffold.  Run it for the general
dressed frame.  The undressed class-two defect is `Δ₀ = −s·(Ū ∧ w̄) + t·(V̄ ∧ w̄)` in `K ⊗ P`
(`t = ν'(u_j)`, `s = ν'(v_j)`, `w̄ = σ̄ − c₀x̄₀`, `K = ker λ ∩ ker ν'`, `P = ⟨w̄, x̄₀⟩`), and the
only dressing reaching the `w̄`-column is the one on the **`x₀`-slot** — this note's `a₀`, see
the index warning above.  Balancing forces

```text
a₀ = −s·Ū + t·V̄        (in the `x₁ = x₀²` gauge; `sqArbFrame_x0_dressing_forced`)
```

which is this note's `a₀ = −k` at the corresponding row.  ⚠ Note *what* is forced: the `x₀`-slot
must be dressed by the **handle** letters, not the handles by the core.  One dressing fixed,
three free — so the balance under-determines the answer rather than closing it, and it is a
filter on candidates, not a solution.

Two further pins to search against.  (i) The core **must** move: for a frame fixing the core the
relator identity collapses to an exact `iff`, `sqRelWord (sqCommFrame h j p q) = 1 ↔ ⁅p, q⁆ =
⁅u_j, v_j⁆` (`CommFrames` §3), and the same class-two computation shows that equation forces
`s = t = 0` — the handle was already clear.  So `SqHandleComm h` is false for `h ≥ 1`.  (ii) The
basis-independent walls above (evenness, syllable counts) still apply and still rule out any
HM2-shape decomposition, in any basis.

**Offline status.**  A sweep over 27 groups of order 8, 16 and 32 (all five of order 8
exhaustively; 20000 sampled markings each at order 16, 5000 at order 32; every pivot exponent
`c₀` mod 8 and every handle row pair `(t, s)`) finds no probe refuting the arbitrary-dressing
shape, while the same sweep restricted to `U`/`V`-word dressings does reproduce the `D₈`
refutation — so the sweep has discriminating power, and the arbitrary family survives exactly
where the two-letter family dies.  That is the numerical shadow of the equivalence above.

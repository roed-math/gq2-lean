# P-15f2 option-1 scoping: closing `lemma_6_17_vanish` via orbit decomposition

**Date**: 2026-07-07 (Opus).  **Goal**: remove the `lemma_6_17_vanish` sorry
(`Q⁰_loc∣X₊ = 0`) by building the §6.2 orbit decomposition on top of the banked
`KappaNormalForm` scaffolding — the user-selected "option 1".

This doc records the **critical path** and, crucially, a prerequisite discovered during scoping —
**general `Q⁰_loc` datum-independence** (Lemma 6.1/6.4) — with its own reduction (landed) and a
subtlety analysis so the next session does not repeat the derivation.

## Architecture (paper §6.3, p. 34)

`lemma_6_17_vanish` gives an arbitrary equivariant factor set `dat` for the invariant nonsingular
`q` on the simple `𝔽₂[C]`-module `V`.  The paper's route:

1. **Regular embedding** (`lemma_6_11`, ✓ std-3 in `RegularSummand`): `V ↪ W = 𝔽₂[C]^N` as a
   `C`-equivariant split summand (`ι`, `r`, `r∘ι = id`).
2. **Transport** (`lemma_6_14`, ✓ in `RepIndependence`): `Q⁰_loc (datW.comap ι) ρ x = Q⁰_loc datW ρ (ι_*x)`
   for a datum `datW` on `W`.
3. **Orbit-sum datum on `W`**: `datW = sumDatum (orbit datums ext-by-0)` (`squareOrbitDatum` /
   `freeOrbitDatum` / `invOrbitDatum` from `OrbitData`, equivariance for the involution case banked
   in `InvolutionDatum.isEquivariantFactorSet_invOrbitDatum`).  Then `Q⁰_loc datW ρ (ι_*x)` is the
   orbit sum (via `graphPullback_sumDatum` + `Q0loc_vanish_of_datum_decomp`, both ✓ landed).
4. **Per-orbit corestriction** (`lemma_6_15` (103)/(104)/(105), ✓ banked in `ShapiroLedger`): each
   `graphPullback (orbit datum) ρ (Shapiro α_r)` is a `cor2Fun` of a scalar cup / Evens norm.
5. **Deep vanishing** (`cup_deepClasses` (94) / `lemma_6_16`, ✓ banked): for a deep class every
   scalar coordinate `α_r ∈ U_{e+1}(K)`, so each `inner` vanishes in the subgroup's `H²`.

The cohomological assembly of 3–5 is **already built** (P-15f2 increments 1–4,
`GQ2/OrbitVanish.lean`): `Q0loc_vanish_of_datum_decomp` consumes `datW = sumDatum s datf`,
per-orbit banked 6.15 `hcoh`, and per-orbit `hvanish`.

## The critical-path prerequisites (what is NOT yet built)

| # | Prerequisite | Status |
|---|---|---|
| **P0** | **`Q⁰_loc` datum-independence** (swap the given `dat` for `datW.comap ι`) | ⚠ **reduced to DI-core**, landed 2026-07-07 (below); DI-core itself open |
| P1 | **Isometric** regular embedding: `ι` with `Q_W ∘ ι = q` (`Q_W` = orbit-sum form) — upgrades `lemma_6_11`'s split embedding to an isometry | open |
| P2 | Orbit decomposition `datW = sumDatum (orbit datums)` at the datum level | ~trivial once `datW` is *defined* as the sum; the content is P1 (isometry) + P3 |
| P3 | **Shapiro-coordinate identification**: `(Quotient.out (ι_*x))` block coords = `shapiroFun (ker ρ) α_r` for scalar Kummer coordinates `α_r` | open |
| P4 | Per-orbit `hcoh`/`hvanish` matching to banked 6.15/6.16/(94) | small, on banked lemmas |

**Banked scaffolding** (`KappaNormalForm`, P-17e5, std-3): `PermW`, `permBas`,
`permBas_support_decomp`, `quadratic_eq_double_sum` (the monomial expansion
`Q F = ∑_{p,p'} F_p F_{p'} f₀(p,p')`), `exists_biadditive_refinement'`, `datum_add`/`datum_comap`/
`datum_of_split`, `exists_datum_of_invariant_quadratic`.  ⚠ It took a **non-orbit-decomposed**
"single β-refinement" route (for `kappa0_exists`), so it does not hand P2 the orbit-sum datum
directly — but P1/P3 sit on exactly this machinery.

## P0 — `Q⁰_loc` datum-independence (the discovered prerequisite)

Because `lemma_6_17_vanish` quantifies over **arbitrary** `dat`, step 2 cannot apply unless the given
`dat` equals `datW.comap ι` (impossible in general — `dat` is gauge-free) **or** `Q⁰_loc` is
independent of the datum for a fixed form.  Only a *special isometry case* is banked
(`UnramifiedModel.graphPullback_comap_smul_sub_mem_B2`).

**Reduction landed 2026-07-07** (`GQ2/OrbitVanish.lean`, `section DatumIndependence`, all std-3):
- `diffDatum dat1 dat2` — the pointwise 𝔽₂-sum (= char-2 difference).
- `graphPullback_diffDatum` — `graphPullback` is 𝔽₂-linear along it.
- `isEquivariantFactorSet_diffDatum` — the difference of two equivariant factor sets for the same
  `q` is an equivariant factor set for the **zero form**.
- `Q0loc_datum_indep_of_core` — datum-independence, **parametric on DI-core**.

**DI-core** (the isolated remaining input): *the graph pullback of a zero-form equivariant factor
set is a `2`-coboundary* (`∈ B²`).  Equivalently: the class `[κ⁰]` of a zero-form factor set on
`V ⋊ C` is trivial, so its `(b,ρ)`-pullback splits over `G_ℚ₂`.

### DI-core analysis (why it needs the paper, not a one-liner)

Candidate coboundary `Λ(g) := Δφ(b g)` for a quadratic refinement `Δφ : V → 𝔽₂` of the difference
datum.  With `polar Δφ = Δf` and the cocycle identity for `b`, a direct computation gives
`δ¹Λ(g,h) = Δf(b g, ρg·b h) + [Δφ(b h) + Δφ(ρg·b h)]`, which matches
`graphPullback (Δdat) ρ b (g,h) = Δf(b g, ρg·b h) + Δm(ρg)(b h)` **iff**
`Δφ(v) + Δφ(c·v) = Δm c v`.  That compatibility is **consistent** with the factor-set identities
(checked: `m_quad`, `m_mul`, `m_one` all follow from `polar Δφ = Δf`), so the obstruction is purely
the **existence of `Δφ`** with `polar Δφ = Δf`.

But a zero-form factor set's `Δf` is a symmetric normalized `2`-cocycle with zero diagonal, whose
**bilinear part** need not be a coboundary of a function `Δφ` (e.g. a nonzero alternating form / cup
product `x_i ∪ x_j` is a nontrivial class in `H²(V; 𝔽₂)`).  So the naive `Λ = Δφ(b·)` can fail.

The genuine proof is the paper's **Lemma 6.1/6.4**: any two equivariant lifts of the same `q` give
**cohomologous** central cocycles on `V ⋊ C` (the extension of `V ⋊ C` classified by a zero-form
factor set is split), and pullback preserves coboundaries.  Formalizing this is the P0 build — a
self-contained cohomological lemma (`~150–300` ln), reusable (f3's `UnramifiedModel` built only the
special isometry instance).  **This is the recommended next brick** — it unblocks the entire route
and does not touch the orbit combinatorics.

## Recommended order

1. **P0 / DI-core** — general datum-independence (Lemma 6.1/6.4).  Self-contained; the interface is
   already fixed by `Q0loc_datum_indep_of_core`.
2. **P1** — isometric regular embedding (on `KappaNormalForm`'s `PermW` + `exists_biadditive_refinement'`).
3. **P3** — Shapiro-coordinate identification (on `permBas_support_decomp` + `shapiroFun`).
4. **P2/P4** — assemble via the landed `Q0loc_vanish_of_datum_decomp`.

Each of P0/P1/P3 is a substantial, mostly-independent lemma; option 1 is a multi-session build.  The
**alternative** (reroute the vanishing through `KappaNormalForm`'s single β-datum, bypassing orbit
decomposition — still needs P0) remains on the table and may be shorter; weigh before P1.

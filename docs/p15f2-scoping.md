# P-15f2 scoping: `lemma_6_17_vanish` (`Q⁰_loc|X₊ = 0`)

**Date**: 2026-07-06 (Opus, autonomous).  **Target**: `SectionSix.lemma_6_17_vanish` — the base
connecting map `Q⁰_loc` vanishes on the deep half `X₊`.

## Paper proof (§6.3, p. 34)

> "By lemma 6.14, compute the base connecting map after an `H_V`-split embedding into a regular
> module, and apply lemma 6.15 to the complete invariant monomial expansion of `q ∘ p`.  For a
> class in `X₊` every scalar coordinate `α_r` lies in `U_{e+1}(K)`.  Free orbits vanish by (94).
> Square orbits vanish because `α_r² = α_r ⌣ (−1)` and `−1 ∈ U_e`.  For an involution orbit, tame
> inertia has odd order, so `K/K₀` in (105) is unramified quadratic … lemma 6.16 makes the Evens
> norm vanish before corestriction.  Every orbit contribution is therefore zero."

## Dependency map

| Input | Repo status |
|---|---|
| `H_V`-split embedding into a regular module | **`GQ2.lemma_6_11`** — SORRIED node (P-15f4); **shared with f1** |
| Lemma 6.14 (regular-module realization) | `RepIndependence.lemma_6_14` — **banked, std-3** |
| Lemma 6.15 orbit classes (103)/(104)/(105) | `ShapiroLedger` — free case `lemma_6_15_free_aux` **banked std-3**; involution-case cochain identities banked (`phi_inv_eq`, `orbit_equiv`, `mk_invLift`, …) |
| Lemma 6.16 (deep-unit Evens norm = 0) | `SectionSix.lemma_6_16` — **banked** (Ax B9, B11) |
| (94) `U_{e+1} ⟂ U_{e+1}`, `−1 ∈ U_e` | **the shared hard gap** (cup = Hilbert symbol on deep Kummer classes); *same piece as f1's isotropy* |
| the monomial expansion `q ∘ p = Σ orbit terms` | **UNBUILT** — the combinatorial layer |

## The two genuine gaps

1. **(94) / cup = Hilbert-symbol** — free orbits (`α_r ⌣ g α_s`, both deep ⟹ 0) and square
   orbits (`α_r² = α_r ⌣ (−1)`, deep ⌣ `U_e` ⟹ 0).  This is **identical to f1's isotropy** gap
   (`card_deepPart_sq_le_of_isotropic`'s `hiso`): the polar/cup of two deep classes vanishes.
   Do it once, both consume it.  Route: relate the B6 cup on `H¹` to the local Hilbert symbol on
   Kummer classes (`polar_Q0loc` + the (93)-cochain layer, both banked), then `U_{e+1} ⊆
   U_{e+1}^⊥ = U_e` from eq. (94).  Candidate no-new-axiom via `B11a` + a conductor bound (see
   `docs/p15f1-axiom-proposal.md` §4.3); else a small L3 leaf (Serre LF XIV §§2–3 /
   Fesenko–Vostokov — not in any current `references/` PDF).

2. **The monomial-expansion layer** — express `q ∘ p` (the quadratic form pulled back along the
   regular embedding `p = i∗`) as the sum of the three orbit-class types, so 6.15's evaluations
   apply.  This is self-contained combinatorics over the regular module `𝔽₂[H_V]^N` (indexed by
   `H_V`-orbits on the coordinate pairs), gated only on the `lemma_6_11` embedding.  UNBUILT;
   ~200–400 lines.  The involution case then closes via 6.16 (banked), the free/square via gap 1.

## Suggested structure (when built)

State an intermediate `Q0loc_vanish_of_orbit_data` taking (a) the regular embedding (from
`lemma_6_11`), (b) the three per-orbit vanishing facts as hypotheses — mirroring f1's
`card_deepPart_sq_le_of_isotropic` (hypothesis-isolated, verified).  Then discharge (b) from
6.15/6.16 + gap 1.  This keeps the verified reduction separate from the hard analytic inputs.

## Status

Not started in Lean (no clean self-contained brick that isn't gated on gap 1 or the unbuilt
expansion).  **Recommendation**: land gap 1 (the cup = Hilbert / (94) orthogonality) *first* —
it unblocks both f1's upper bound and f2's free/square orbits — then build the expansion layer.

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
| (94) `U_{e+1} ⟂ U_{e+1}`, `−1 ∈ U_e` | ✅ **BANKED 2026-07-06** — `cup_deep_deep`/`cup_deep_self`/`cup_deep_neg_one` (HilbertLedger Tier 5, std-3∪{B11a}, no new axiom) |
| the monomial expansion `q ∘ p = Σ orbit terms` | **UNBUILT** — the combinatorial layer |

## The two genuine gaps

1. **(94) / cup = Hilbert-symbol** — ✅ **CLOSED 2026-07-06, as theorems, NO new axiom**
   (`GQ2/HilbertLedger.lean` Tier 5).  The scalar leaves are banked: free orbits =
   `cup_deep_deep`, square orbits = `cup_deep_self` / `cup_deep_neg_one` (all
   std-3 ∪ {B11a}); underlying `normForm_of_deep` / `normForm_neg_one_of_deep` are std-3
   sorry-free (Brahmagupta descent + `sq_of_near_one`; the general (94) is only an
   *exercise* in FV Ch. VII §4 — Ex. 4c/5b — hence proved, not leafed, per the 2026-07-06
   user directive).  **Now also lifted into `deepClasses` vocabulary**:
   `LocalKummer.cup_deepClasses` (std-3 ∪ {B11a}) — two deep classes in `H¹(G_k,𝔽₂)` cup to 0 —
   via the std-3 bridge `deepClass_eq_kummerClassK` (a deepClass over `k.fixingSubgroup` **is**
   `kummerClassK k a` for a genuine deep `a∈kˣ`; Galois correspondence + `kummerCocycleFun_neg`).
   Consumer bridge `norm_sub_one_lt_of_isDeepUnit` (LocalKummer).
   What still stands between these scalar leaves and `hiso`/the orbit terms is only the
   **monomial-expansion bridge** (gap 2) + the consumer transport `ker ρ = (fixedField (ker ρ))ᶠⁱˣ`.

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

**Gap 1 landed 2026-07-06** (Tier-5 scalar leaves, see above) — the recommendation was
executed, with theorems instead of a leaf.  Remaining: gap 2 (the monomial-expansion layer,
gated on `lemma_6_11` = P-15f4) + the per-orbit assembly (6.15/6.16, banked).

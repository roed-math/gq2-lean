# P-15f2b — COMPLETE (orbit route, I0–I4 landed, std-3)

**Date**: 2026-07-07 (Opus).  Status: after the foundation pause, the user chose the **orbit
route**; increments **I0–I4 are landed sorry-free (std-3)**.  **P-15f2b's full interface is now
delivered**: `regular_isometric_embedding_orbit` — the `C`-equivariant (through `e : C ≃* G⧸N`)
isometric split embedding into `Fin K → RegRep N` carrying the **§6.2 orbit-sum datum** `sumDatum
(orbitIndexSet Q_W) orbitDatum` for `Q_W := q∘r`, *definitionally* the orbit sum.  The remaining
inputs to closing `lemma_6_17_vanish` are f2a (datum-independence, its full proof paper-verified in
`p15f2-option1-scoping.md`), f2c (Shapiro coords), and f2d (assembly + the `C ≅ AbsGalQ2⧸ker ρ`
instantiation of `e`).

## Orbit route — landed increments (all std-3)

| Inc | Commit | Content |
|---|---|---|
| **I0** | `4a3ca0c` | de-privatize `KappaNormalForm`'s generic quadratic/datum layer (`quadratic_expansion`, `datum_*`, `polar_*`, `isQuadraticFp2_*`) — visibility-only, clash-free |
| **I1** | `6d3c3cc` | `GQ2/OrbitDecomp.lean` carrier: `blockBas` basis + support decomp, `blockDiag`/`blockPolar` coordinates + invariance reductions, `posSwap`/`IsFreePos` + the `freeReps` orientation transversal |
| **I2** | `cbf4700` | the three block summands (`{square,free,inv}BlockDatum` = `FactorSet.comap` of the literal `OrbitData` datums) + equivariance + quadraticity + basis diagonal/polar evaluations (incl. the involution `Quotient.out` bookkeeping) |
| **I3** | `677ae4a` | **`isEquivariantFactorSet_orbitSumDatum`** — a `(G/N)`-invariant `𝔽₂`-quadratic `Q` on `Fin K → RegRep N` **is** the square map of `sumDatum (orbitIndexSet N Q) (orbitDatum N)`.  Via `isEquivariantFactorSet_sumDatum` (generic) + `quadratic_ext` (basis extensionality through `quadratic_expansion`) + the diagonal/polar matching (`orbitSum_blockBas` / `orbitSum_polar_blockBas`, the combinatorial heart). |

`isEquivariantFactorSet_orbitSumDatum` is Galois-free over abstract `(G, N)` with `[Finite (G⧸N)]`
— exactly the `dat = sumDatum s datf` shape `OrbitVanish.Q0loc_vanish_of_datum_decomp` consumes.

| **I4** | `GQ2/RegularIsometry.lean` | **`regular_isometric_embedding_orbit`** — composes the foundation `regular_isometric_embedding` with a block-reindexing intertwiner `reBlock` along `e : C ≃* G⧸N`, transports `ι`/`r`/`Q_W := q∘r` onto `Fin K → RegRep N`, and applies `isEquivariantFactorSet_orbitSumDatum` to conclude the full f2b interface with `datW` **definitionally** the orbit sum. |

## I4 — the reindex capstone (landed)

`regular_isometric_embedding_orbit` (`GQ2/RegularIsometry.lean`): the transport bricks are
* `reSummand e : (C → ZMod 2) ≃+ RegRep N`, `f ↦ (fun h => f (e.symm h))`; blockwise
  `reBlock := AddEquiv.piCongrRight`;
* action compat `reBlock (c • F) = e c • reBlock F` / `reBlock.symm (d • Y) = e.symm d • reBlock.symm Y`
  (both left-regular; `e.symm` a hom);
* `ι := reBlock ∘ ι₀`, `r := r₀ ∘ reBlock.symm`, `Q_W := q ∘ r`; invariance (through `reBlock.symm`
  + `hinv`) / quadraticity of `Q_W`, isometry `Q_W (ι v) = q v` through `r∘ι = id`, and
  equivariance `ι (a • v) = e a • ι v`.

The conclusion's datum is *literally* `sumDatum (orbitIndexSet N Q_W) (orbitDatum N)` — no bridging
for f2c's per-orbit `hcoh`.  `e` is kept abstract; f2d instantiates it at `C ≅ AbsGalQ2⧸ker ρ`.

---

## Foundation (I earlier) — `regular_isometric_embedding` (commit `cfbbe96`, std-3)

## What landed (`GQ2/RegularIsometry.lean`, commit `cfbbe96`)

`regular_isometric_embedding` — the `C`-equivariant isometric split embedding of a ramified
simple faithful quadratic `𝔽₂[C]`-module `(V, q)` into the regular module `W = PermW C N`:

```
∃ (N : ℕ) (ι : V →+ PermW C N) (r : PermW C N →+ V) (datW : FactorSet C (PermW C N)),
  IsEquivariantFactorSet (fun F => q (r F)) datW ∧          -- (1) equivariant datum for Q_W
  (∀ v, q (r (ι v)) = q v) ∧                                -- (3) isometry  Q_W ∘ ι = q
  (∀ (h : C) (v : V), ι (h • v) = h • ι v) ∧                -- (4) ι equivariant (PermW smul)
  (∀ (h : C) (F : PermW C N), r (h • F) = h • r F) ∧        -- (4) r equivariant (PermW smul)
  (∀ v, r (ι v) = v)                                        -- (5) retraction
```

`#print axioms = {propext, Classical.choice, Quot.sound}` (std-3, **no new axioms**, census
unchanged).  Own-file build green.  Committed as `cfbbe96` (leaf file only; the `GQ2.lean` import
line is added in the working tree, uncommitted, per the shared-import convention).

Hypotheses mirror `RegularSummand.lemma_6_11` (`c`, `hgen`, `hV2`, `hfaith`, `hsimple`, `hram`)
plus the form data (`q`, `hq : IsQuadraticFp2 q`, `hinv : IsInvariant C q`) — exactly the shapes
already present in `SectionSix.lemma_6_17_vanish`, so it slots straight in there.

## The scoping finding (reframes the ticket)

The board framed f2b as **P1 = the isometry** (hard) + **P2 = `datW = sumDatum` (~free)**.  The
code says the opposite:

- **The isometry is FREE.**  Take `Q_W := q ∘ r` (pull back along the retraction).  Then
  `Q_W (ι v) = q (r (ι v)) = q v` from `r ∘ ι = id`; `Q_W` is invariant/quadratic because `r` is
  equivariant/additive.  This is *exactly* what `KappaNormalForm.kappa0_exists_tame`'s ramified
  branch already does internally (lines 1219–1240) — `regular_isometric_embedding` just **exposes**
  `ι`/`r`/`datW`/isometry instead of collapsing to `∃ dat, IsEquivariantFactorSet q dat` on `V`.
- **`datW = sumDatum(orbit datums)` is the real remainder.**  The banked normal form
  `exists_datum_of_invariant_quadratic` deliberately took the **single invariant-biadditive
  `β`-refinement** route (`docs/p17e-kappa0-scoping.md`), *not* the orbit sum.  So it produces
  `datW` but not its orbit-sum form.  Recovering the orbit sum is the §6.2 decomposition of `Q_W`
  into square/free/involution orbit polynomials — the single largest combinatorial effort left for
  `lemma_6_17_vanish`, and it includes reconciling the involution-orientation datum `invOrbitDatum`
  (the gnarliest object in the §6 layer).

The per-orbit **equivariance** lemmas are banked and ready to reuse:
`isEquivariantFactorSet_squareOrbitDatum`, `isEquivariantFactorSet_freeOrbitDatum`
(`GQ2/SectionNine.lean:1286,1305`), `isEquivariantFactorSet_invOrbitDatum`
(`GQ2/InvolutionDatum.lean:191`) — all on `RegRep N`; transporting them into the `N` blocks of
`PermW C N'` is the `exists_invBlock_datum`/`comap` pattern (`KappaNormalForm.lean:469–495`).

## Route fork (open — decide before the big build)

1. **Orbit route (literal f2b remainder).**  Build `datW = sumDatum(orbit datums)` on `PermW`:
   expand `Q_W = q∘r` via `quadratic_eq_double_sum`, group coordinate-pair orbits by relative
   position `x⁻¹y ∈ C` (`= 1` → square, involution → involution, else → free), identify each with
   the banked orbit datum, and match diagonals.  Then f2c (banked 6.15/6.16 per orbit) + f2d
   (`Q0loc_vanish_of_datum_decomp` + `lemma_6_14`).  Board-aligned; reuses the most machinery;
   **large** (multi-session).

2. **β-route (flagged in `docs/p15f2-subtickets.md`).**  Skip the orbit decomposition: use
   datum-independence (f2a, `Q0loc_datum_indep_of_core`) to swap `dat` for the already-built
   `kappa0_exists_tame`/β-datum, then prove `Q0loc = 0` **directly** from the β-datum on deep
   classes.  Could collapse f2b+f2c+f2d — but the direct-vanishing step is **unbuilt** (the banked
   6.15/6.16 vanish per *orbit* datum), so viability is uncertain and it needs its own argument.

Both routes still need **f2a** (datum-independence), which is independent and can proceed either way.

## Consumers of the foundation

Either route consumes `regular_isometric_embedding`: it supplies the equivariant `ι` (for
`lemma_6_14`'s `mapCoeff1` transport), the retraction, and an equivariant `Q_W`-datum on `W`.  The
orbit route additionally needs the orbit-sum refinement of `datW`; the β-route uses the exposed
`datW` (or `kappa0_exists_tame`'s datum) directly.

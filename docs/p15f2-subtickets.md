# P-15f2 subticket decomposition (parallelizable)

**Date**: 2026-07-07 (Opus).  Breaks `lemma_6_17_vanish` (option 1, orbit decomposition) into four
subtickets that parallelize, because the **landed cohomological backbone** makes every remaining
piece hypothesis-isolated behind a crisp interface:

- `Q0loc_vanish_of_datum_decomp` (increment 4) — consumes `datW = sumDatum s datf` + per-orbit 6.15
  `hcoh` + deep-class `hvanish`.
- `Q0loc_datum_indep_of_core` + `isEquivariantFactorSet_diffDatum` (increment 5) — reduce datum
  choice to **DI-core**.

Each subticket **provides** a named lemma whose statement is already fixed, and **consumes** only
other subtickets' provided lemmas (or banked results).  So they can be built against each other's
signatures without waiting.

```
        f2a (datum-indep)          f2b (isometric embedding)
             │  provides                 │  provides
             │  Q0loc_datum_indep        │  ⟨N, ι, r, datW, hiso, hdatW,
             │                           │   datW = sumDatum orbit datums⟩
             │                           │
             │                           ▼
             │                     f2c (Shapiro coords + deepness)
             │                           │  provides per-orbit hcoh, hvanish
             ▼                           ▼
        ┌────────────────── f2d (assembly + SectionSix splice) ──────────────────┐
        │  Q0loc dat ρ x  =[f2a]  Q0loc datW.comap ι ρ x  =[6.14]  Q0loc datW ρ ι∗x │
        │                 =[f2b,f2c → Q0loc_vanish_of_datum_decomp]  0             │
        └──────────────────────────────────────────────────────────────────────────┘
```

**Immediately parallel: f2a and f2b** (both fully independent, start now).  f2c develops against
f2b's fixed interface; f2d is the capstone (skeleton now, splice when a/b/c land).

---

## Board-ready rows (splice into `docs/tickets.md` when free)

| P-15f2a | B: **`Q⁰loc` datum-independence** — DI-core (Lemma 6.1/6.4): the graph pullback of a zero-form equivariant factor set is a `2`-coboundary, hence any two equivariant factor sets for the same `q` give equal `Q⁰loc`. | ⭐⭐⭐ | — | P-15f2 backbone ✓ | ∅ (pure cohomology/𝔽₂ linear algebra; a2 parametric on `(I ◁ C, odd, V^I=0)` — producers banked) | ◐ **CLAIMED (Opus→Fable 2026-07-07); INCREMENT 1 LANDED (8b18bf8, std-3)**: cochain heart `graphPullback_mem_B2_of_refinement` + `Q0loc_datum_indep_of_refinement`. **★ PLAN RESOLVED (Fable, on-paper proof verified — scoping doc §P0)**: (a1) `Δφ₀` exists C-independently (`Δf` symmetric + zero-diagonal ⟹ twisted extension `V ×_Δf 𝔽₂` elementary abelian ⟹ linear section over `ZMod 2`; needs `hV2`; `splitting_of_global_cocycle` probed — NOT reusable); (a2) equivariance correction by the **banked f1 averaging pattern** (`L₀ = Σ_{i∈I} D i` kills the defect on odd `I`; normality ⟹ corrected defect `I`-invariant; `Σ_{i∈I} i•v ∈ V^I = 0` kills it globally — NO general `H¹(C,V*)` theory); (a3) wire through the landed increment-1, parametric on `(I, hIn, hodd, hVI)` + `hV2` (tame instantiation stays with f2d). **Option-2 amendment (fix canonical datum in 6.17) REJECTED**: consumers get datums existentially (`kappa0_exists`), so it relocates the requirement to the 6.18→§8 boundary, doesn't remove it. Increments A/B/C ≈ 150–200/150/40 ln, all in `OrbitVanish` §DatumIndependence (no new file — `GQ2.lean` parallel-dirty). **Interface FIXED** by `OrbitVanish.Q0loc_datum_indep_of_core` (hyp `hcore`); provide `Q0loc_datum_indep`. Sub-bricks: **(a1)** quadratic refinement `Δφ` of `Δf` — 𝔽₂ `Module` lemma, `KappaNormalForm.exists_biadditive_refinement'` is the template; `Δf` IS a symmetric coboundary (two data share diagonal+polar, so `[Δf]=0` in `H²(V;𝔽₂)`). **(a2)** correct `Δφ` by an additive `L : V→𝔽₂` killing the C-equivariance defect `Δφ(v)+Δφ(cv) = Δm c v` (an `H¹(C,V*)` vanishing — leverage odd-inertia/involution structure), then `Λ(g)=Δφ(bg)`, verify `δ¹Λ = graphPullback Δdat`. Analysis: `docs/p15f2-option1-scoping.md` §P0. FULLY INDEPENDENT (no arithmetic); reusable (f3/Unramified\-Model has only the special isometry case). Own file or extend `OrbitVanish`. ~200–400 ln. |
| P-15f2b | B: **isometric regular embedding** — the `C`-equivariant split embedding `ι : V →+ W = PermW C N` into the regular module carrying the **orbit-sum form** `Q_W`, with `Q_W ∘ ι = q` (isometric) and retraction `r`. Upgrades `lemma_6_11` to an isometry vs. the orbit-sum form. | ⭐⭐⭐ | — | `lemma_6_11` ✓, KappaNormalForm ✓ | ∅ (finite rep theory) | ☐ OPEN. Provide `∃ N (ι : V →+ PermW C N) (r) (datW), IsEquivariantFactorSet Q_W datW ∧ datW = sumDatum orbit-datums ∧ (∀ v, Q_W (ι v) = q v) ∧ equivariance ∧ r∘ι = id`. Sits on **banked scaffolding** `KappaNormalForm` (`PermW`, `permBas_support_decomp`, `quadratic_eq_double_sum`, `exists_datum_of_invariant_quadratic`, `datum_of_split`) + `InvolutionDatum.isEquivariantFactorSet_invOrbitDatum` + `RegularSummand.lemma_6_11`. This is **P1**; **P2** (`datW = sumDatum`) is ~free once `datW` is defined as the orbit sum. FULLY INDEPENDENT, start now. Own file `GQ2/RegularIsometry.lean`. ~200–400 ln. |
| P-15f2c | B: **Shapiro coordinates + scalar deepness** — for `x ∈ deepPart ρ`, the transported cocycle `out(ι∗x)`'s block coordinates are (cohomologous to) `shapiroFun (ker ρ) α_r` for scalar Kummer coordinates `α_r`, and each `α_r` is a deep unit. | ⭐⭐⭐ | — | P-15f2b interface, `lemma_6_15` ✓, `lemma_6_16` ✓, `cup_deepClasses` ✓ | B9, B11a (via 6.16/(94)) | ☐ OPEN. Produce the two per-orbit hypotheses of `Q0loc_vanish_of_datum_decomp`: **`hcoh`** (each `graphPullback (orbit datum) ρ (out ι∗x) ~ cor2Fun` — match to banked `lemma_6_15_square/free/involution`) and **`hvanish`** (each inner cocycle `= 0` in the subgroup `H²` — scalar `α_r ∈ U_{e+1}` ⟹ `cup_deepClasses`(94)/`lemma_6_16`). This is **P3 + P4**. SEMI-INDEPENDENT: develop against f2b's fixed embedding interface (hypothesize `ι`/`W`), instantiate when f2b lands. On `permBas_support_decomp` + `shapiroFun` + `deepPart`/`deepClasses`. ~200–300 ln. |
| P-15f2d | B: **final assembly + SectionSix splice** — compose f2a (swap `dat → datW.comap ι`) + `lemma_6_14` transport + f2b (`datW = sumDatum`) + f2c (`hcoh`/`hvanish`) through `Q0loc_vanish_of_datum_decomp`, then remove the `lemma_6_17_vanish` sorry. | ⭐⭐⭐ | — | P-15f2a, P-15f2b, P-15f2c | (inherits B9/B11a/B6/B7) | ☐ OPEN (capstone). Skeleton can be built NOW against a/b/c signatures. ⚠ **co-owns the frozen 6.17 signatures + the shared SectionSix exit with P-15f1/P-15f8** — use the statement-move pattern (6.18ram/P-15d) and cross-flag. Wiring only. ~100–200 ln. |

## Notes for claimants

- **f2a and f2b are the two independent starting tracks** — assign first.
- All interfaces are `FactorSet`/`Q0loc`/`sumDatum`-shaped and already compile in `OrbitVanish.lean`
  / `OrbitData.lean`; no signature is speculative.
- Keep each subticket in its **own file** (f2a → `OrbitVanish` or new; f2b → `RegularIsometry`;
  f2c → new or `LocalKummer`) to avoid parallel-edit collisions; f2d does the single SectionSix
  splice under coordination with f1/f8.
- The **alt β-route** (bypass orbit decomposition via `KappaNormalForm`'s single β-datum) still needs
  f2a but could replace f2b+f2c+f2d with one shorter ticket — weigh before committing f2b/f2c.

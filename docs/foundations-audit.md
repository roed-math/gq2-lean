# Mathlib foundation audit for the $G_{\mathbf Q_2}$ presentation

Audited against **Mathlib `v4.31.0`** (the pinned revision), plus a survey of the
**open PR queue** of `leanprover-community/mathlib4` (as of 2026-07-01, via `gh`).
The question: what does the paper's statement and proof need, and how much of it
exists or is in flight?

This document is intentionally date-stamped. Names and merged-PR status describe the pinned
environment used by the formalization and should not be read as a claim about current Mathlib
`main`.

## Legend
- ✅ **in Mathlib** — usable today.
- 🟡 **partial / open PR** — exists but incomplete, or only in an unmerged PR.
- ❌ **absent** — not in Mathlib and not in the open PR queue.

## A. Foundations needed to even *state* Theorem 1.2

| Ingredient | Status | Where / notes |
|---|---|---|
| Absolute Galois group of a field | ✅ | `Field.absoluteGaloisGroup K := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K` in `Mathlib/FieldTheory/AbsoluteGaloisGroup.lean`, with `Group`, `TopologicalSpace` (Krull), `IsTopologicalGroup` instances. For char-0 `K` (our `ℚ₂`), algebraic closure = separable closure, so this is genuinely $G_{\mathbf Q_2}$. |
| ↳ *fix to separable closure + more instances* | 🟡 PR **#19616** | `adamtopaz`, open since 2024. Changes the def to the separable closure and adds instances. Explicitly notes **"Still missing is compactness, but that seems like a bigger project."** Does not affect us (char 0) except for the compactness gap below. |
| $\mathbf Q_2 = $ `ℚ_[2]` | ✅ | `Padic 2`, `Mathlib/Data/Padics/PadicNumbers.lean`. |
| Krull topology on `Gal` | ✅ | `Mathlib/FieldTheory/KrullTopology.lean`. |
| ↳ *uniform group structure on `Gal`* | 🟡 PR **#36239** | `plp127`, `feat(FieldTheory/KrullTopology): define uniform group structure on galois group`. Useful for completeness/compactness arguments. |
| Profinite groups as a category | ✅ | `ProfiniteGrp` in `Mathlib/Topology/Algebra/Category/ProfiniteGrp/{Basic,Limits,Completion}.lean`. |
| `Gal(K/F)` **is** profinite (compact) for Galois `K/F` | ✅ | `Mathlib/FieldTheory/Galois/{Infinite,Profinite}.lean` (infinite Galois correspondence; profinite structure). This is the route to the missing compactness instance on `absoluteGaloisGroup ℚ₂`: `AlgebraicClosure ℚ₂ / ℚ₂` is Galois (char 0 ⇒ perfect), so the general profinite structure applies — but wiring it onto the `absoluteGaloisGroup` def is not yet done in Mathlib. |
| `IsGaloisGroup` predicate + finite Galois API | ✅ | `Mathlib/FieldTheory/Galois/IsGaloisGroup.lean` (several open follow-up PRs: #41208, #40866, #41051 by `tb65536`/`xroblot`). |
| Free profinite group on a set | ❌ Mathlib / ✅ **built here** | `FreeProfiniteGroup`: **0 hits** in Mathlib, no open PR. **Now constructed in this repo** (`GQ2/FreeProfinite.lean`) as `profiniteCompletion (FreeGroup X)`, with universal property `(FreeProfiniteGroup X ⟶ P) ≃ (X → P)` — using Mathlib's new `ProfiniteGrp.profiniteCompletion` adjunction (A. Topaz). Mathlib-contribution-worthy. |
| Profinite presentation (quotient by closed normal closure of relators) | 🟡 / ✅ **quotient built here** | Mathlib has no presentation API. **`GQ2/ProfiniteQuotient.lean` supplies the key missing piece**: for `G` profinite and `N` a *closed* normal subgroup, `G ⧸ N` is profinite (`instTotallyDisconnectedSpace_quotient` — the one instance Mathlib lacked, proved via a clopen topological basis inherited from `G`'s open-normal-subgroup basis — plus `profiniteQuotient : ProfiniteGrp`). With `FreeProfiniteGroup` + `homEquiv_apply`, defining `Γ_A` as the `profiniteQuotient` by the closed normal closure of the relators is now unblocked. Mathlib-contribution-worthy. |
| $\widehat{\mathbf Z}$ and $\omega_2$ idempotent; $\widehat{\mathbf Z}$-exponentiation | ❌ | `ZHat`: **0 hits**, no open PR. Needed for the auxiliary words $x^{\omega_2}$. *Mitigation:* on any finite quotient, $\omega_2$ reduces to an ordinary integer via CRT (paper App. A/B), so the finite/surjection-count form avoids $\widehat{\mathbf Z}$ entirely. |

**Conclusion for the statement.** The surjection-count form is statable *today* (it needs
only `absoluteGaloisGroup ℚ₂` + finite-group tuple counting). The *literal* presentation
form needs `FreeProfiniteGroup` + `ZHat`, both absent from Mathlib and its PR queue; this
repo scaffolds minimal versions and flags them.

## B. Foundations needed for the *proof*

| Ingredient (paper section) | Status | Notes |
|---|---|---|
| Schur–Zassenhaus (Lemma 9.2) | ✅ | `Mathlib/GroupTheory/SchurZassenhaus.lean`. |
| Finite group theory: normal closure, `IsPGroup`, subdirect/fibre products (Lemmas 2.1, 9.1) | ✅ | `Subgroup.normalClosure`, `IsPGroup`, `MonoidHom`/`Subgroup.prod` API. |
| 2-core $O_2(G)$ (Lemmas 3.3, 10.1) | 🟡 | No dedicated `O_2`/`Fitting`-style API found; expressible as "the largest normal 2-subgroup" or handled via `IsPGroup` on normal closures. Minor build-out. |
| Hopfian property of f.g. profinite groups (Lemma 2.5) | 🟡 | Mathlib has `Hopfian` for modules/general; the *profinite* statement ("surjective endomorphism of a topologically f.g. profinite group is injective") needs assembling from `ProfiniteGrp` + finiteness of `Sur(P, Pₙ)`. Not packaged. |
| Group cohomology $H^1,H^2$; **Tate cohomology**, Herbrand quotient, corestriction/inflation-restriction | 🟡 ✅ **imported** | Mathlib has discrete low-degree cohomology; **`ClassFieldTheory` (imported, see below) adds `tateCohomology`, Herbrand quotient, `Corestriction`/`Inflation`/`InflationRestriction`, trivial-cohomology criteria** — the machinery §§5–8 need. Continuous/profinite cohomology + cup products still to assemble. |
| Non-archimedean local fields; valuation, ramification/inertia, unramified extensions | ✅ **imported** | `ClassFieldTheory.IsNonarchimedeanLocalField.*` — the `IsNonarchimedeanLocalField` class (with a `ℚ_[p]` instance, currently upstream-`sorry`'d), `RamificationInertia`, `Unramified`, `UnramifiedCohomology`, `ValuationExactSequence`, Teichmüller lifts. Mathlib itself now also has `NumberTheory/LocalField/Basic`. |
| Local Tate duality; Euler characteristic | 🟡 | Not directly; but the `ClassFieldTheory` cohomology stack (`LocalInv`, unramified cohomology) is the substrate to build it on. |
| Local class field theory / reciprocity map (Lemma 3.5) | 🟡 **imported (in progress)** | **`kbuzzard/ClassFieldTheory` is now a dependency of this repo** (2025 Oxford CMI summer-school project; `LocalCFT/` is early — `Continuity`, `Teichmuller` — the Artin/reciprocity map is not yet complete upstream). Provides the local-field + cohomology foundation to build Lemma 3.5 on. |
| Demushkin groups; Labute's classification (Prop. 1.1, Lemmas 3.4–3.8) | ❌ | `Demushkin`: **0 hits**, no open PR. This is the structural heart of §3.1. |
| Dyadic Hilbert symbol / quadratic-form invariants over $\mathbf Q_2$ (§6) | 🟡/❌ | Mathlib has quadratic forms, Witt groups, and some Hilbert-symbol material over general fields, but not the explicit dyadic formulas used. |
| Stiefel–Whitney / Evens classes, Fourier–Gauss sums over $\mathbf F_2[C]$ (§§5–8) | ❌ | Not present. |
| Tame/étale fundamental group of $\mathbf P^1\setminus\{0,1,\infty\}$; outer Galois action (Lemma 3.6) | ❌ | Not present. |

## C. Open PRs that are genuinely useful as a foundation

Ranked by relevance to *this* project:

1. **#19616** — `fix: fix the definition of the absolute Galois group of a field` (`adamtopaz`).
   Directly the object we name. Adopt its instances once merged; track the compactness follow-up.
2. **#36239** — `feat(FieldTheory/KrullTopology): uniform group structure on galois group` (`plp127`).
   Supports completeness/compactness of $G_{\mathbf Q_2}$, i.e. the profinite instance we need.
3. **#40955** — `feat(NumberTheory/NumberField/ExistsRamified): galois groups are generated by
   inertia subgroups` (`tb65536`). Ramification-theoretic; adjacent to the tame/wild split (§3),
   though it is a global-field statement.
4. **#41208 / #40866 / #41051** — `IsGaloisGroup` refactors/additions (`tb65536`, `xroblot`).
   General Galois-group ergonomics used throughout.

**No open Mathlib PR** provides free profinite groups, profinite presentations, $\widehat{\mathbf Z}$,
or Demushkin groups. Local fields, Tate cohomology, and (partial) local class field theory are now
available via the **`ClassFieldTheory` dependency** (§E), though the reciprocity map itself is not
yet complete there.

## E. The `ClassFieldTheory` dependency (added 2026-07-01)

[`kbuzzard/ClassFieldTheory`](https://github.com/kbuzzard/ClassFieldTheory) — the 2025 Clay/CMI
Oxford summer-school project formalizing local & global class field theory — is now a git
dependency of this repo (`lakefile.toml`). This required realigning our toolchain to
`leanprover/lean4:v4.31.0-rc2` and pinning Mathlib to CFT's commit `23b0068d` (near-complete Azure
cache hit: 8546/8550 oleans). **All of our own proofs still build** against this Mathlib.

What it gives us (see §B rows): the `IsNonarchimedeanLocalField` class with a `ℚ_[p]` instance,
ramification/inertia, unramified extensions and their cohomology, Teichmüller lifts, and a full
Tate-cohomology / Herbrand-quotient / corestriction stack — the substrate for the paper's §3 and
§§5–8. `GQ2/CFTTest.lean` is a smoke test (`IsNonarchimedeanLocalField ℚ_[2]` resolves).

**Caveats.** (1) Several CFT declarations — *including* the `ℚ_[p]`-is-a-local-field instance — are
`sorry`'d **upstream**, so importing gives the *API to build on*, not finished theorems; anything we
prove *through* those must be re-audited when CFT fills them in. (2) Our build is now coupled to a
fast-moving research repo pinned to a specific Mathlib commit; if that commit's cache expires or CFT
moves, a re-pin may be needed. Our **core lib does not import CFT** (only `CFTTest.lean` does), so
`lake build GQ2` stays independent of it.

## D. Reproduce this audit

```sh
R=leanprover-community/mathlib4
# existing code:
gh api -X GET search/code -f q="absoluteGaloisGroup repo:$R" --jq '.items[].path'
gh api -X GET search/code -f q="ProfiniteGrp repo:$R"        --jq '.items[].path'
gh api -X GET search/code -f q="FreeProfiniteGroup repo:$R"  --jq '.total_count'   # 0
gh api -X GET search/code -f q="ZHat repo:$R"                --jq '.total_count'   # 0
gh api -X GET search/code -f q="Demushkin repo:$R"           --jq '.total_count'   # 0
# open PRs:
gh pr list --repo $R --state open --search "absolute Galois" --limit 20
gh pr list --repo $R --state open --search "profinite"       --limit 20
```

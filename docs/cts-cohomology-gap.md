# The homogeneous ↔ inhomogeneous gap in continuous cohomology

This is a dated API survey explaining why the formalization uses the explicit low-degree model in
`GQ2/Cohomology.lean` rather than silently identifying it with Mathlib's abstract homogeneous
continuous cohomology.  First written against the pinned Mathlib revision (`ec410d2`,
2026-06-12); **rewritten 2026-07-24** because the upstream API changed out from under the pin.

## What the pinned Mathlib has (`ec410d2`, 2026-06-12)

`Mathlib.Algebra.Category.ContinuousCohomology.Basic` (215 lines; upstreamed from
`rmhi/ctsToDiscrete`) defines continuous cohomology of a topological group with
topological-module coefficients:

- `continuousCohomology (n : ℕ) : Action (TopModuleCat R) G ⥤ TopModuleCat R`
  `:= homogeneousCochains R G ⋙ HomologicalComplex.homologyFunctor _ _ n`.
- Cochains are **homogeneous**: `G`-invariants of the nested-coinduction complex
  `M → C(G,M) → C(G,C(G,M)) → ⋯`.
- **Degree 0 is its only computed degree**: `continuousCohomologyZeroIso :
  continuousCohomology R G 0 ≅ invariants R G`.

## What upstream looks like now (master, checked 2026-07-24)

The pin is stale here; do **not** take the section above as a description of current Mathlib.

- **Redefined and moved** (PR #41144, merged 2026-07-02, Hill–Yang–Xie): continuous cohomology
  now lives at `Mathlib/RepresentationTheory/Homological/ContCohomology/Basic.lean`, built over
  `TopRep k G` via a recursive coinduced resolution (`TopRep.resolution`,
  `TopRep.homogeneousCochains`, `continuousCohomology n A`).  The pin's
  `Algebra.Category.ContinuousCohomology` names (`continuousCohomologyZeroIso`,
  `kerHomogeneousCochainsZeroEquiv`, …) **no longer exist upstream**; the degree-0 iso is now
  `ContCohomology.zeroIso` in `ContCohomology/LowDegree.lean` (still the only computed degree).
- **Functoriality landed** (PR #41309, 2026-07-03): `ContCohomology/Functoriality.lean` gives
  `cochainsMap`/`cocyclesMap`/`map` in both the group and the coefficients — the abstract
  counterpart of our `ContCoh.H0/H1/H2comap`.
- **In flight right now**: #41539 (functoriality refactor via `continuousCohomologyFunctor` +
  `resNatTrans`; active the week of 2026-07-20) and #41545 (inflation maps, stacked on #41539).
  The API surface is still moving — which is exactly why we are **not bumping Mathlib now**
  (owner decision, 2026-07-24).
- **Cup products exist sorry-free in the FLT staging tree**, not in Mathlib:
  `FLT/Mathlib/RepresentationTheory/Homological/ContCohomology/CupProduct.lean` (Edison Xie, 582
  lines) — all degrees `(m, n)` on the homogeneous model, from an intertwining pairing with
  jointly continuous uncurry (automatic for discrete coefficients), with the Leibniz rule and
  cocycle/coboundary descent; its companion staging `Basic.lean` adds `cohomologyIsoQuot`
  (a kernel-mod-coboundary model).  Not yet PR'd to Mathlib.
- The discrete-group comparison with `groupCohomology` is reported sorry-free in the staging repo
  `rmhi/ctsToDiscrete` (commits of 2026-07-10), also not yet PR'd.
- Still absent **everywhere** upstream (Mathlib, FLT staging, ctsToDiscrete): the concrete
  *inhomogeneous* low-degree description (explicit 1-/2-cocycle identities), corestriction /
  transfer / the Evens norm, and long exact sequences (the module TODO is unchanged).

## The precise missing isomorphism

The classical homogeneous ↔ inhomogeneous cochain iso, continuous version, in low degree:

- **Degree 1.**  Inhomogeneous continuous `1`-cochains `c : C(G, M)` with cocycle condition
  `c(g·h) = c(g) + g • c(h)` correspond to homogeneous `1`-cochains `f : G² → M` (a `G`-invariant
  element of `C(G, C(G, M))`) via
  `f(g₀, g₁) = g₀ • c(g₀⁻¹ g₁)`,  inverse  `c(g) = f(1, g)`.
- **Degree 2.**  `c : C(G², M)` with the `2`-cocycle identity corresponds to homogeneous
  `f : G³ → M` via `f(g₀,g₁,g₂) = g₀ • c(g₀⁻¹g₁, g₁⁻¹g₂)`.

One must check these are mutually inverse **continuous** maps and commute with the differentials
(a chain isomorphism), which then gives the homology iso `Hⁿ_inhom ≅ continuousCohomology n` for
`n ≤ 2`.  This remains a genuine formalization task, not a mechanical port; the FLT staging
`cohomologyIsoQuot` (cohomology ≅ ker d / im d on homogeneous cochains) does the
quotient-presentation half of the work on the abstract side.

## What the formalization uses

- `GQ2/Cohomology.lean` — explicit **inhomogeneous** continuous cochains `H⁰/H¹/H²` over the
  elementary `[DistribMulAction G M] [ContinuousSMul G M]` interface (Serre GC I §2.2
  conventions).  This *is* the concrete low-degree model Mathlib's TODO asks for.
- `GQ2/CupProduct.lean` — cup products `(1,1),(0,2),(2,0)` on that model (with
  graded-commutativity in char 2 in `GQ2/CupSymmetry.lean`), and degree-1/2 corestriction and the
  Evens norm in `GQ2/EvensKahn.lean` / `GQ2/Corestriction.lean` — none of which exist upstream
  in any form.

The earlier experimental `CtsCohBridge.lean` adapter was removed during cleanup because no theorem
in the final proof consumed it.  The absence of that file is deliberate: the formalization does not
claim a proved equivalence between its explicit `ContCoh.H¹/H²` and Mathlib's abstract functor.

## What would close the gap

1. Wait for the upstream stack to stabilize (#41539, #41545, the FLT cup product reaching
   Mathlib), then bump.
2. Build the degree-1 and degree-2 continuous homogeneous↔inhomogeneous chain isos above against
   the **new** `TopRep` API.
3. Obtain `ContCoh.H1 ≅ continuousCohomology 1 (TopRep.of _)` and likewise `H2`.
4. Transport the `CupProduct.lean` cups onto `ContinuousCohomology.cup` along these isomorphisms
   (compatibility statement), and upstream the inhomogeneous layer + corestriction/Evens norm —
   coordinating with the stack's authors (Richard Hill, Edison Xie, Andrew Yang).

Until then, the B-axiom statements that need continuous cohomology are phrased against our
explicit `ContCoh.Hⁱ`.  The classical comparison is part of the intended mathematical
interpretation, but it is not represented as a theorem in the present repository.  Planning
context: `docs/angdinata-review-plan.md` §2.

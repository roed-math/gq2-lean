# The homogeneous ↔ inhomogeneous gap in continuous cohomology

Status note (2026-07-03).  Records exactly what is and isn't available for continuous group
cohomology, so we don't rediscover it.  Companion to `GQ2/CtsCohBridge.lean`.

## What Mathlib has (as of mathlib `ec410d2`, 2026-06-12)

`Mathlib.Algebra.Category.ContinuousCohomology.Basic` (Richard Hill's `rmhi/ctsToDiscrete`,
upstreamed) defines continuous cohomology of a topological group with topological-module
coefficients:

- `continuousCohomology (n : ℕ) : Action (TopModuleCat R) G ⥤ TopModuleCat R`
  `:= homogeneousCochains R G ⋙ HomologicalComplex.homologyFunctor _ _ n`.
- Coefficients live in `Action (TopModuleCat R) G` (equivalently `TopRep R G` via
  `TopRepEquivActionTop`), i.e. a topological `R`-module with a continuous `R`-linear `G`-action.
- Cochains are **homogeneous**: `homogeneousCochains` is the `G`-invariants of the complex
  `M → C(G,M) → C(G,C(G,M)) → ⋯` (nested continuous-function coinduction `I`), a
  `CochainComplex (TopModuleCat R) ℕ`.
- **Degree 0 is fully done**: `ContinuousCohomology.continuousCohomologyZeroIso :
  continuousCohomology R G 0 ≅ invariants R G`, and `kerHomogeneousCochainsZeroEquiv`.

Mathlib's version is **more complete than the standalone `ctsToDiscrete` repo**, which `#exit`s and
`sorry`s the degree-0 iso; the repo also *redefines* the now-upstreamed core, so it is **not
co-importable** with Mathlib (double-declared `ContinuousCohomology.MultiInd.d`).  We therefore
build on the Mathlib object and have **removed** the `ctsToDiscrete` dependency.

## What Mathlib does NOT have (its own stated TODO)

From the module docstring, verbatim TODO:
> - Show that it coincides with `groupCohomology` for discrete groups.
> - Give the usual description of cochains in terms of `n`-ary functions for locally compact groups.
> - Show that short exact sequences induce long exact sequences in certain scenarios.

The **second** item is our gap: there is no concrete *inhomogeneous* (`n`-ary) description of the
continuous cochains in low degree, hence no ready `Hⁿ = {cocycles}/{coboundaries}` for `n = 1, 2`.

## The precise missing isomorphism

The classical homogeneous ↔ inhomogeneous cochain iso, continuous version, in low degree:

- **Degree 1.**  Inhomogeneous continuous `1`-cochains `c : C(G, M)` with cocycle condition
  `c(g·h) = c(g) + g • c(h)` correspond to homogeneous `1`-cochains `f : G² → M` (a `G`-invariant
  element of `C(G, C(G, M))`) via
  `f(g₀, g₁) = g₀ • c(g₀⁻¹ g₁)`,  inverse  `c(g) = f(1, g)`.
- **Degree 2.**  `c : C(G², M)` with the `2`-cocycle identity corresponds to homogeneous
  `f : G³ → M` via `f(g₀,g₁,g₂) = g₀ • c(g₀⁻¹g₁, g₁⁻¹g₂)`.

One must check these are mutually inverse **continuous** maps and commute with the differentials
(a chain isomorphism), which then gives the homology iso `Hⁿ_inhom ≅ continuousCohomology R G n`
for `n ≤ 2`.  Scale: Mathlib's *abstract* analogue over `Rep R G`
(`inhomogeneousCochainsFunctor` and the iso to `groupCohomology`; in `ctsToDiscrete`
`FinHomogeneousToMathlib.lean`) is a multi-hundred-line development — this is a genuine
formalization task, not a mechanical port, and the natural place to coordinate with Hill / the
Mathlib effort.

## What we have built (and where it connects)

- `GQ2/Cohomology.lean` — explicit **inhomogeneous** continuous cochains `H⁰/H¹/H²` over the
  elementary `[DistribMulAction G M] [ContinuousSMul G M]` interface (Serre GC I §2.2 conventions).
  This *is* the concrete low-degree model Mathlib's TODO asks for.
- `GQ2/CupProduct.lean` — cup products `(1,1),(0,2),(2,0)` on that model.
- `GQ2/CtsCohBridge.lean` — the seam:
  - **coefficient bridge** `toContRep`/`toTopRep`/`toAction` (a `[DistribMulAction]` discrete
    module as `Action (TopModuleCat ℤ) G`);
  - **degree-0 bridge** `H0Equiv : (continuousCohomology ℤ G 0).obj (toAction M) ≃+ H0 G M`
    (done, via `continuousCohomologyZeroIso`).

## Plan to close the gap (deferred)

1. Build the degree-1 and degree-2 continuous homogeneous↔inhomogeneous chain isos above.
2. Obtain `ContCoh.H1 ≅ (continuousCohomology ℤ G 1).obj (toAction M)` and likewise `H2`.
3. Transport the `CupProduct.lean` cups onto `continuousCohomology` along these isos.

Until then, the B-axiom statements that need continuous cohomology are phrased against our explicit
`ContCoh.Hⁱ`, with `H0Equiv` certifying agreement in degree 0 and the above as the pending
certification in degrees 1–2.

# Response plan — David Angdinata's review (received 2026-07-24)

David Angdinata reviewed the axiom layer (eyeballed B1, B5, B6, B7, B10, B11a; passed the rest
to "Sol" for semantic checking) and raised four points.  This document records the evidence-backed
assessment of each point and the work plan.  All mathlib claims below were verified against the
pinned checkout (`ec410d2`, 2026-06-12) **and** against `master` as of 2026-07-24 (GitHub API +
loogle/leansearch); repo claims cite file:line.

## Verdict summary

| # | Criticism | Verdict | Cost to address |
|---|---|---|---|
| 1 | use `TopologicalAbelianization`, not `GQ2.commClosure` | **misreading** — we already build on it; `commClosure` names its defining subgroup because mathlib has no projection/lift API | hours (clarity), small mathlib PR (optional) |
| 2 | use mathlib's continuous cohomology; "cup products are there" | **wrong for mathlib proper** (H⁰-only there), but sorry-free all-degree cups exist in **FLT's mathlib-staging tree** (likely David's referent); the inhomogeneous/cochain-formula layer the axioms consume exists nowhere upstream; migration impossible today; readability complaint is fair | notation pass now; bridge to the Hill–Xie stack as it lands |
| 3 | doc mismatches: B8, B4-vs-B3c, 4 errors in formalization.yaml | **confirmed** (yaml + B4); B8 specifics still needed from Sol | hours |
| 4 | `IsUnramifiedQuadraticSpectral` is bad; use mathlib ramification | **overstated** — it is a `def` consumed and supplied only by *proved* theorems; no mathlib notion applies at these types today | rename/doc now; bridge when mathlib matures |

---

## Decisions (owner, 2026-07-24)

* **No mathlib bump now** — wait for the upstream `ContCohomology` stack to stabilize
  (#41539/#41545 and the FLT cup product landing).
* **No mathlib PRs for now** — A2 (`TopologicalAbelianization.of`/`lift`) and the C3 upstream
  coordination are deferred; C2 (finite-group bridge) waits for the post-stabilization bump.
* **Proceed**: W0 fixes, A1 docstrings, U1 rename (→ `HasEqualNormValueGroups`), C1 cup
  notation, and **B9-A** — scoped in `docs/orchestration/b9a-proof-plan.md` +
  `b9a-tickets.md`; Fable/Opus subagent tickets on branch `b9a` in worktree `~/claude/gq2-b9a`.

Execution log: W0 + A1 + U1 + C1(axiom-surface) applied 2026-07-24 on `master`; B9-A T0/T1
dispatched the same day (see the ticket board for live status).

---

## 1. `TopologicalAbelianization` vs `GQ2.commClosure`

**Facts.**
- Mathlib's entire API (pin *and* master) is 59 lines
  (`Mathlib/Topology/Algebra/Group/TopologicalAbelianization.lean`):
  `abbrev TopologicalAbelianization G := G ⧸ (commutator G).topologicalClosure`, the normality
  instance, and a `CommGroup` instance.  There is **no** projection hom, no universal property,
  no kernel lemma, no continuity lemma.
- The repo *already* builds on it: `AbsGalQ2ab := Field.absoluteGaloisGroupAbelianization ℚ_[2]`
  (`GQ2/Reciprocity.lean:109`), which is mathlib's
  `TopologicalAbelianization (Field.absoluteGaloisGroup ℚ_[2])` by `abbrev` unfolding.
- `commClosure` (`Reciprocity.lean:113`) is an `abbrev` for `(commutator AbsGalQ2).topologicalClosure`
  — literally the subgroup mathlib's `abbrev` quotients by.  It exists so that
  `toAb := QuotientGroup.mk' commClosure`, `QuotientGroup.lift commClosure …` (`chiCycAb`,
  `restrictAb`) and the kernel lemmas can be stated; mathlib offers none of these.

**Verdict.**  The criticism reads as "you defined a rival abelianization"; we did not.  What we
defined is the *missing API* over mathlib's definition.

**Actions.**
- (A1, hours) Make the reuse impossible to miss: extend the docstrings of `AbsGalQ2ab`,
  `commClosure`, `toAb` to state "this *is* mathlib's `TopologicalAbelianization`; `commClosure`
  is its defining subgroup, named only because mathlib exports no projection/lift API".  Optionally
  drop the `commClosure` abbrev and inline the term (mechanical, ~15 call sites across
  `Reciprocity`/`SectionThree`/`BoundaryMapsWitness`/`UnramifiedBridge`/`TameQuotient`).
- (A2, small upstream PR, optional) Contribute `TopologicalAbelianization.of : G →* G_ab`
  (continuous, surjective), `lift`, `ker_of = (commutator G).topologicalClosure`, and the
  `IsTopologicalGroup` instance on the quotient — then delete our local versions on the next bump.
  This is the constructive answer to the review.

## 2. Continuous cohomology: ours vs mathlib

**The mathematical constraint.**  The B-axioms take cohomology of the *profinite* `G_ℚ₂` and its
open subgroups with finite discrete coefficients (`H1 AbsGalQ2 M` in B7, `H¹/H²(G_k, 𝔽₂)` in
B6/B9/B11a).  The faithful object is **continuous-cochain** cohomology (Serre, *Galois
Cohomology* I §2.2).  Mathlib's main `groupCohomology` is for **abstract** `Rep k G` — no
topology.  For profinite groups abstract and continuous cohomology differ (already at `H¹` the
comparison for finite coefficients needs Nikolov–Segal-grade input; at `H²` they genuinely
diverge), so `groupCohomology` is not a drop-in and using it would be a *faithfulness bug*, not a
refactor.

**What mathlib actually has** (verified in the pin and on master, 2026-07-24):

| capability | `GQ2.ContCoh` (repo, axiom-free) | mathlib pin `ec410d2` | mathlib master today |
|---|---|---|---|
| framework | explicit inhomogeneous continuous cochains; coefficients = `DistribMulAction` + `ContinuousSMul` | homogeneous nested `C(G,·)` functor over `Action (TopModuleCat R) G` (`Algebra/Category/ContinuousCohomology/Basic.lean`, 215 lines) | **redefined & moved** (#41144, 2026-07-02): over `TopRep k G` via a recursive coinduced resolution, at `RepresentationTheory/Homological/ContCohomology/`; the pin's API no longer exists upstream |
| `H⁰` | invariants subgroup | `continuousCohomologyZeroIso` (its **only** computed degree) | still the only computed degree (`LowDegree.lean` is H⁰-only) |
| concrete `H¹`, `H²` (cocycles/coboundaries, cocycle-identity lemmas) | ✓ `Cohomology.lean` | ✗ — its own module TODO | ✗ |
| functoriality in `(G, M)` (restriction, inflation, coefficient maps) | ✓ `H0/H1/H2comap` + `res`/`inf`/`mapCoeff` | ✗ | ✓ `Functoriality.lean` (#41309); refactor in flight (#41539), inflation maps queued behind it (#41545) |
| cup products | ✓ `(1,1)`, `(0,2)`, `(2,0)` w.r.t. any equivariant pairing, bilinear by construction; graded-commutativity in char 2 (`CupProduct.lean`, `CupSymmetry.lean`) | ✗ — no cup products in mathlib, incl. abstract `groupCohomology` | ✗ in mathlib and its PR queue; **✓ sorry-free in FLT's staging tree** (pipeline note below) |
| corestriction / Evens norm | ✓ degree-1 index-2 (`EvensKahn.lean`) + transversal degree-2 (`Corestriction.lean`); Evens-norm two-point cocycle | ✗ for cohomology (group *homology* has corestriction) | ✗ |
| LES fragments | the pieces the paper needs, proved in `GQ2/Devissage/` (`LESCore`/`LESExact`/`LESMaster`) | ✗ (TODO) | ✗ |
| comparison with abstract `groupCohomology` (finite/discrete `G`) | deliberately deferred (`Cohomology.lean` closing note) | TODO | TODO |

The only latent "cup-like" structure in mathlib is `groupCohomologyIsoExt`
(`Hⁿ(G,A) ≅ Extⁿ(k,A)`) plus Yoneda composition — abstract-only, no topology, no cocycle
formulas.  The axioms *consume cochain formulas* (the Hilbert-symbol ledger, the two-point Evens
cocycle (98), Kummer cocycles), which a purely categorical `H²` cannot even state.

**The wider pipeline (found 2026-07-24; changes the forecast, not today's facts).**  The pin is
genuinely stale here.  Mathlib **redefined** continuous cohomology on 2026-07-02 (#41144,
Hill–Yang–Xie), three weeks after our pin: it now lives at
`RepresentationTheory/Homological/ContCohomology/` over `TopRep k G`, and the pin's
`Algebra.Category.ContinuousCohomology` API (which `docs/cts-cohomology-gap.md` describes) was
deleted upstream.  Functoriality followed on 2026-07-03 (#41309); open right now are #41539
(functoriality refactor, active this week) and #41545 (inflation maps, stacked on #41539) — both
by Richard Hill (@rmhi).  Beyond mathlib, the **FLT project's staging tree** carries
`FLT/Mathlib/RepresentationTheory/Homological/ContCohomology/CupProduct.lean` (Edison Xie, 582
lines, **sorry-free**): cup products in *all* degrees `(m, n)` on the homogeneous model, taking an
intertwining pairing with jointly continuous uncurry (automatic for discrete coefficients — our
setting), with the Leibniz rule and full cocycle/coboundary descent; its companion `Basic.lean`
adds `cohomologyIsoQuot` (a kernel-mod-coboundary model of the cohomology).  Not yet PR'd to
mathlib.  Hill's staging repo `rmhi/ctsToDiscrete` also reports the discrete-group comparison
with `groupCohomology` sorry-free as of 2026-07-10.  FLT has **no** corestriction/transfer
(searched).

**Verdict.**  For mathlib proper the claim is still false today — no cup products at the pin, on
master, or in the PR queue, including for abstract `groupCohomology` — but it has a real
referent: the Hill–Xie continuous-cohomology stack, whose cup products exist sorry-free in FLT's
mathlib-staging tree and are clearly mathlib-bound.  What that stack still lacks, everywhere
upstream, is exactly what the B-axiom statements consume: the concrete **inhomogeneous
low-degree** description (explicit cocycle formulas — Kummer cocycles, the Hilbert ledger, the
two-point Evens cocycle (98)) and **corestriction / the Evens norm**.  Our `ContCoh` layer is
precisely that missing middle layer, per mathlib's own module TODO.  What *is* fair in David's
critique: the cup products are hard to read at consumer sites
(`trivialCupPairing 2 k.fixingSubgroup htriv (kummerClassK k a) (kummerClassK k b)` rather than
`[a] ⌣ [b]`), and with the upstream stack converging, the comparison bridge is now a when-not-if
question — but building it against an API that is being refactored this week would be wasted
motion.

**Actions.**
- (C1, 1–2 days) **Readability pass**, no statement changes at the `Prop` level beyond notation:
  scoped notation `a ⌣[μ] b` for `cup11` and a dyadic-specialized `a ⌣₂ b` for
  `trivialCupPairing`; abbreviations for the ubiquitous `H¹(G_k, 𝔽₂)` pattern; a short
  "reviewer's dictionary" section in `docs/` mapping each def to the Serre GC / paper formula.
  (Also consider renaming `ContCoh.B1/B2` (coboundaries) → `B1cob/B2cob` or similar: they collide
  with the *axiom* labels B1/B2 in review conversations.)
- (C2, ~1 week, after C1) Build the deferred **finite/discrete-group bridge** to
  `groupCohomology` (the `Cohomology.lean` closing-note plan): for discrete `G`, `ContCoh.H1/H2 ≃`
  mathlib's `H1/H2` via the cocycle-level match with `cocycles₁/₂`.  This directly answers "why
  not mathlib" with a theorem: *on the overlap, they agree*.
- (C3, upstream-facing, weeks) Coordinate with the stack's authors — Richard Hill (@rmhi), Edison
  Xie (@Whysoserioushah), Andrew Yang — *before* writing bridge code: their functoriality is being
  refactored right now (#41539), inflation (#41545) and the FLT cup product are queued behind it,
  so a comparison written against today's API would churn.  Once it settles and we bump: build the
  degree-≤2 homogeneous↔inhomogeneous chain isos against the **new** `TopRep` API (FLT's
  `cohomologyIsoQuot` already exposes the kernel-mod-coboundary model, which is half the work),
  obtain `ContCoh.H1/H2 ≅ continuousCohomology 1/2`, and prove our `cup11` matches their `cup`
  under the iso.  The upstreamable gap that stays ours to fill: the inhomogeneous low-degree layer
  itself plus degree-1/2 corestriction and the Evens norm (nowhere upstream, FLT included).
- (C4, immediate, zero code) Rewrite `docs/cts-cohomology-gap.md`: the API it describes was
  **deleted upstream** on 2026-07-02 (#41144 redefined continuous cohomology over `TopRep k G` at
  `RepresentationTheory/Homological/ContCohomology/`).  Record the new decl names
  (`TopRep.homogeneousCochains`, `continuousCohomology n A`, `ContCohomology.zeroIso`), the open
  PRs (#41539, #41545), the FLT staging cup product, and the ctsToDiscrete comparison status, so
  the next bump isn't a surprise.

## 3. Documentation mismatches

**(a) `formalization.yaml` — confirmed, exactly four mislabels, in two places.**
The comments at lines 38–41 label `absGalQ2_localEulerCharacteristic` as B3c, `dyadicOrientation`
as B5, `localReciprocity` as B6, `tateDualityAt` as B7.  Per the compile-checked ledger
(`GQ2/AxiomLedger.lean:42`): Euler char = **B7**, orientation = **B3c**, reciprocity = **B5**,
Tate duality = **B6**.  The same four errors repeat in `literature_dependencies` (lines 65–74).
Sol's count ("four mistakes") is exactly right.

**(b) "in some places your B4 is B3c" — confirmed; stale docstrings post-dating the B4 deletion.**
Axiom B4 (standalone `G_ℚ₂(2) ≅ D₀`) was deleted 2026-07-10 as unused (B3c subsumes a marked B4;
`docs/literature-axioms.md` §B4).  Stale references that still assert B4 *is a live axiom*:
- `GQ2/DyadicPresentation.lean:20` ("isomorphism … **is** axiom B4 in `GQ2/Foundations/Axioms.lean`"),
  `:52`, `:57` — the worst offenders (they name the axiom file).
- `GQ2/Demushkin.lean:196` ("the classification instance the paper uses **is** axiom B4").
- Softer/confusing: `GQ2/MaxProP.lean:21`, `GQ2/TameQuotient.lean:23` ("on a par with B1/B4"),
  `GQ2/SectionEight/ScalarCount.lean:336` ("B4/B5-content" — audit which numbering it means).
Fix: sweep to "(the B4 interface, subsumed into `dyadicOrientation` (B3c) since 2026-07-10)".

**(c) "B8 is wrongly documented" — not yet reproduced; two candidates.**
A line-by-line check of `peripheralCyclotomicAction` (`Foundations/Axioms.lean:251` vs the bundle
in `GQ2/PeripheralAction.lean`) found the fields and docstrings consistent.  Candidates for what
Sol saw: (i) **paper renumbering drift** — the docstrings cite "Lemma 3.6" but the current tex has
it as Lemma 3.7 (the paperforge footer in `PeripheralAction.lean` records "= lemma 3.7 in current
tex"); a semantic checker reading the current writeup would flag every 3.6 citation; (ii) the
module-docstring phrase "each `u ∈ ℤ₂ˣ` in the image of the cyclotomic character" (redundant since
the local cyclotomic character is surjective onto `ℤ₂ˣ` — which is *why* the all-units form needs
the B5 input, as the composite-leaf note explains).  **Ask David for Sol's transcript** before
changing anything.

**(d) Global docstring check — do it with tooling, not eyeballs.**
- Single source of truth for labels = `AxiomLedger.bAxioms`.  Extend `scripts/check_axioms.sh` (or
  a new `scripts/check_labels.py`) to grep every `# B\d` / "B\d" tag in `formalization.yaml`,
  `docs/literature-axioms*.md`, and axiom-file docstrings against the ledger, and to whitelist
  historical labels (B2, B4, B7′, B11b, B12, B13) only when accompanied by
  "deleted/subsumed/discharged" language.
- Paper-numbering sync: the paperforge `⟦tag⟧` ledgers already map old↔new numbering; add a pass
  that flags bare "Lemma m.n" citations whose tag says the number moved.
- Then a one-shot agent audit: per axiom, docstring ↔ Lean statement ↔ bundle-field docs ↔
  `literature-axioms.md` row, reporting drift.  (This is the systematic version of what Sol did.)

## 4. `IsUnramifiedQuadraticSpectral`

**Facts.**
- It is a `def`, not an axiom (`Foundations/Axioms.lean:408`), and *nothing assumes it*: it is a
  hypothesis of the **proved** theorem `unramifiedQuadratic_units_are_norms` (the B11b flip,
  proved in `GQ2/UnramifiedQuadraticNorms.lean` + `TeichmullerLift.lean`), and where the §6 layer
  *uses* that theorem the hypothesis is **discharged in-repo** for the extensions that occur
  (`GQ2/Shapiro/Deepness.lean:185` — "`hunram` HOLDS for every …; c2c discharges `hunram` in
  spectral-norm vocabulary").  So the predicate is soundness-neutral: axioms neither state nor
  consume it.  Our own adversarial review already isolated it as the "riskiest piece" and forced
  it into a named, documented `def` (rec 2).
- Mathematically it says the quadratic extension has equal norm value groups, i.e. `e = 1`, which
  *is* unramifiedness for finite extensions of complete discretely-valued fields — the standard
  characterization, just phrased in spectral-norm vocabulary because the repo carries norms, not
  valuation rings.
- Mathlib survey (pin *and* master): `IsNonarchimedeanLocalField`
  (`NumberTheory/LocalField/Basic.lean`, Andrew Yang) exists but has **zero instances** (not even
  `ℚ_[p]`) and **no extension/ramification theory**; `Ideal.ramificationIdx`/RamificationInertia
  is Dedekind-ideal-theoretic and would need `𝒪`-structures our `IntermediateField ℚ_[2] ℚ̄₂`
  types don't carry; `Algebra.FormallyUnramified` is the wrong notion for this (for field
  extensions it is separability); the NumberField completion-ramification files are
  number-field-specific.  **There is no mathlib unramifiedness notion usable at our types today.**

**Verdict.**  "Bad" overstates it; "not a mathlib notion" is exactly what our docs already say.
The actionable content is naming/bridging, and the bridge is blocked on mathlib, not on us.

**Actions.**
- (U1, hours) Rename to what it *is* — e.g. `HasEqualNormValueGroups` (keeping
  `IsUnramifiedQuadraticSpectral` as a deprecated alias for one release of the repo) — or keep the
  name and lead the docstring with "= `e(k(δa)/k) = 1`, the standard unramifiedness criterion
  (Serre LF I §4), in spectral-norm vocabulary".  Add a negative stress test (`k = ℚ₂`,
  `δa = √2` fails the predicate) next to the existing positive suppliers.
- (U2, watch + bridge) Track Andrew Yang's `LocalField` development; when e/f for finite
  extensions of nonarchimedean local fields lands, prove
  `IsUnramifiedQuadraticSpectral k δa ↔ (mathlib unramifiedness)` and cite it from the docstring.
  Upstreaming e/f ourselves is a possible but larger contribution (needs `ValuativeRel`
  instances on our intermediate fields first).

## 5. Bonus: B9 restructure (Sol's "relative Stiefel–Whitney identity" suggestion)

Sol suggests axiomatizing a cleaner "relative SW identity" and *deriving* the current
`evensKahn_dyadic` from it.  Assessment: the current B9 is confessedly composite (fixed Lemma-6.16
diagonalizations; SW classes only notational; Delzant well-definedness absorbed into scoping —
all flagged in the docstring).  Restructure options, not mutually exclusive:

- **(B9-A, Sol's proposal, ~1–2 weeks swarm)**  New axiom stated at the quadratic-form level:
  for `L/k` quadratic (char ≠ 2), `a ∈ Lˣ`,
  `w(Tr_{L/k}⟨a⟩) = w(Tr_{L/k}⟨1⟩)·(1 + cor_{L/k}[a] + N^{Ev}_{L/k}[a])` in degrees ≤ 2, with
  `w₁/w₂` *defined on isometry classes* (Delzant well-definedness **proved**, via the Steinberg
  relation — over dyadic bases derivable from B11a, which keeps the axiom's base dyadic as now).
  Then **prove** today's `evensKahn_dyadic` from it by formalizing Lemma 6.16's trace-form
  diagonalizations `Tr⟨a⟩ ≃ ⟨2u, 2dn/u⟩`, `Tr⟨1⟩ ≃ ⟨2, 2d⟩` (elementary Gram computation the
  paper does).  Net effect: the axiom becomes checkable against Kahn Théorème 2 nearly verbatim;
  census stays at 9.  Mathlib prerequisites exist (`QuadraticForm.Equivalent`, diagonalization
  over fields of char ≠ 2).
  *(Postscript, 2026-07-24: **B9-A was executed and landed** — B9 is now
  `relativeStiefelWhitney_dyadic` (SW classes `swOne`/`swTwo` with Delzant well-definedness proved),
  the former composite statement is the byte-identical derived theorem `evensKahn_dyadic`, census
  stays at 9; board `docs/orchestration/b9a-tickets.md`, write-up `docs/literature-axioms.md` §B9.)*
- **(B9-B, days, do regardless)**  Discharge B9's **degree-1 component** in-repo: it is classical
  `cor[a] = [N_{L/k}a]` compatibility, and with our *explicit* `corFun = b₁ + b_s` and Kummer
  cocycles it reduces to a cocycle computation (`κ_β(g) + κ_{s⁻¹·}(g)` against `κ_{β·sβ}`).
  Needs a short feasibility ticket first; if it goes through, B9 shrinks to the degree-2 identity.
- **(B9-C, hours)**  Promote the docstring's convention anchor (`G = C₄ ⊇ C₂`, fibre `D₈`,
  Lemma 6.13) from prose to a Lean `example` stress-testing `evensNormH2` on a finite model.

## Work plan

| wave | items | effort | risk | status (2026-07-24) |
|---|---|---|---|---|
| W0 mechanical | yaml 4×2 label fixes; B4 stale-docstring sweep; gap-doc rewrite (C4) | ~1 h | none | **done** |
| W1 audit | label lint vs `AxiomLedger.bAxioms`; paper-numbering drift pass; per-axiom docstring↔statement agent audit; ask David for Sol's B8 transcript | ~1 day | none | open (owner: the B8 ask) |
| W2 readability | cup/`⌣` notation (C1); `commClosure` docs (A1); rename to `HasEqualNormValueGroups` (U1) | 1–2 days | statement-preserving only | **done** at the axiom surface; broad ⌣ sweep = ticket W2c, negative test = ticket W2n (b9a board) |
| W3 axiom quality | **B9-A landed 2026-07-24** (board `docs/orchestration/b9a-tickets.md`; census-neutral 9→9, B9 ↦ `relativeStiefelWhitney_dyadic`, `evensKahn_dyadic` now a byte-identical derived theorem); B9-B/B9-C folded into that board | 1–2 weeks | axiom statement change was gated on owner sign-off (T5 gate, cleared) | **done 2026-07-24** |
| W4 bridges | finite-group bridge to `groupCohomology` (C2); upstream `TopologicalAbelianization.of/lift` (A2) | ~1 week + review latency | none to repo | **deferred** (owner: no mathlib PRs now) |
| W5 upstream | bridge to the Hill–Xie `ContCohomology` stack after it stabilizes (C3); local-field unramifiedness bridge when available (U2) | weeks, elapsed | external dependencies | watching (no bump now) |

Owner-gated decisions: B9-A (changes an axiom statement), any renaming of public axiom-adjacent
defs (U1), and whether to pursue A2/C3 upstream PRs under the repo's authorship conventions.

## Questions to send back to David

1. Please share Sol's B8 finding verbatim — our line-by-line check of
   `peripheralCyclotomicAction` against `PeripheralAction.lean` found the docs consistent; the
   likeliest culprit is the paper's Lemma 3.6→3.7 renumbering, which we'll fix globally either way.
2. On cup products: mathlib proper still has none (pin, master 2026-07-24, and the PR queue) — but
   we found `FLT/Mathlib/RepresentationTheory/Homological/ContCohomology/CupProduct.lean`
   (Edison Xie; sorry-free, all degrees, homogeneous model).  Is that what you meant?  If so, we
   agree it is the right convergence target; note it exposes no inhomogeneous/cochain-formula
   access, which is what the axiom statements consume, so our plan is to bridge to it (and
   upstream the inhomogeneous low-degree layer plus corestriction/Evens norm, which exist nowhere
   upstream) once #41539/#41545 land and the cup product reaches mathlib.  Do you know whether
   Xie/Hill plan the inhomogeneous description themselves?
3. Would you review a small mathlib PR adding `TopologicalAbelianization.of`/`lift`?  That is the
   missing API that forced `commClosure`/`toAb` to exist locally.

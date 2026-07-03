# What Mathlib and ClassFieldTheory currently provide (survey)

Ticket T-00, done 2026-07-03 against **mathlib `ec410d2`** (2026-06-12) and **ClassFieldTheory
`3565c752`**.  Purpose: a current map of what already exists, so we stop being surprised by
Mathlib/CFT content (this has bitten us twice — continuous cohomology and the local-field class
were both already upstreamed).  Organized by the infrastructure our nine literature leaves (B1–B9,
see `docs/literature-axioms.md`) and tickets need.  Each entry: **EXISTS**(name · file) or
**ABSENT**, with a one-line note.

> Convention: mathlib paths are under `.lake/packages/mathlib/Mathlib/`; CFT under
> `.lake/packages/ClassFieldTheory/ClassFieldTheory/`.

## Headline "we didn't know Mathlib had this"

- **Continuous group cohomology is in Mathlib** — `Mathlib.Algebra.Category.ContinuousCohomology`
  (`continuousCohomology (n) : Action (TopModuleCat R) G ⥤ TopModuleCat R`), degree-0 iso proved.
  See `docs/cts-cohomology-gap.md`.  (`ctsToDiscrete`, upstreamed.)
- **`IsNonarchimedeanLocalField` is a Mathlib class** — `NumberTheory/LocalField/Basic.lean`
  (via `ValuativeRel` + `LocallyCompactSpace`).  The **`ℚ_[p]` instance is in CFT**
  (`IsNonarchimedeanLocalField/Basic.lean`, which now `import`s the Mathlib class).
- **`CompactSpace Gal(K/k)`** for `[IsGalois k K]` and `profiniteGalGrp : ProfiniteGrp`
  (`FieldTheory/Galois/Profinite.lean`).  Does **not** yet fire for
  `Field.absoluteGaloisGroup ℚ_[2]` (instance synth fails) — see B1 below.

## B1 — `G_ℚ₂` is topologically finitely generated / profinite

- **EXISTS** `Field.absoluteGaloisGroup K := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K`,
  `deriving Group, TopologicalSpace (Krull), IsTopologicalGroup`
  (`FieldTheory/AbsoluteGaloisGroup.lean`).
- **EXISTS** `CompactSpace Gal(K/k)` (`[IsGalois k K]`), `InfiniteGalois.profiniteGalGrp`
  (`FieldTheory/Galois/Profinite.lean`) — the profinite structure of a Galois group as a limit of
  finite quotients.
- **GAP** `CompactSpace (absoluteGaloisGroup ℚ_[2])` does **not** resolve by `inferInstance`
  (checked).  It should be derivable — `AlgebraicClosure ℚ₂ / ℚ₂` is Galois in char 0 — but needs
  glue (`IsGalois ℚ_[2] (AlgebraicClosure ℚ_[2])` + matching the `Gal`-instance to
  `absoluteGaloisGroup`'s def).  ⇒ **actionable**: our `main_presentation` still needs its
  `[CompactSpace AbsGalQ2]` hypothesis, but wiring this up (a small lemma) may discharge it.
- **ABSENT** topological finite generation of `G_ℚ₂` itself — remains axiom **B1**
  (`GQ2/Foundations.lean`).
- Our own foundations on top of `ProfiniteGrp`/`profiniteCompletion`/`OpenNormalSubgroup`:
  `FreeProfiniteGroup`, `profiniteQuotient`, `profinitePresentation`, `Zhat`/`omega2`
  (`GQ2/{FreeProfinite,ProfiniteQuotient,ProfinitePresentation,Zhat}.lean`).

## B2 — 2-adic cyclotomic character is surjective

- **EXISTS** `cyclotomicCharacter (p) [Fact p.Prime] : (L ≃+* L) →* ℤ_[p]ˣ`
  (`NumberTheory/Cyclotomic/CyclotomicCharacter.lean`).  Our axiom **B2**
  (`GQ2/Foundations.lean`) asserts surjectivity for `p = 2`; the character itself is Mathlib's.

## B3 — Demushkin classification / cup nondegeneracy · B4 — `G_ℚ₂(2) ≅ D₀`

**Discrete group cohomology (Mathlib, `RepresentationTheory/Homological/GroupCohomology/`):**
- **EXISTS** `groupCohomology.H0/H1/H2` + `H0Iso/H1Iso/H2Iso`; explicit
  `cocycles₁/₂`, `coboundaries₁/₂`, `IsCocycle₁ f : f(g·h) = g•f h + f g`,
  `IsCocycle₂ f : f(gh,j)+f(g,h) = g•f(h,j)+f(g,hj)` (`LowDegree.lean`) — **these conventions match
  our `ContCoh.mem_Z1_iff`/`mem_Z2_iff` exactly**.  `H1IsoOfIsTrivial : H1 ≅ Hom(G,A)` (trivial
  action).  All over `Rep k G` (`k`-linear).
- **EXISTS** `tateCohomology` + `TateCohomology.isoGroupCohomology (n>0)` + LES
  (`TateCohomology/Basic.lean`).
- **EXISTS** `groupCohomology.map`/`cocyclesMap` (functoriality along a group hom + module map),
  `H1InfRes` (low-degree inflation–restriction short complex, proved) (`Functoriality.lean`).
- **EXISTS** `Rep.ofDistribMulAction` / `Representation.ofDistribMulAction` (needs
  `[SMulCommClass G k A]`), `Rep.of` — the *discrete* coefficient bridge (analogue of our
  `toContRep` on the continuous side).
- **ABSENT — cup products.**  Mathlib has **no** cup product on `groupCohomology`/`Rep`
  (`Hᵖ × Hᵍ → H^{p+q}`), nor on continuous cohomology.  ⇒ our `GQ2/CupProduct.lean` is genuinely
  novel, not a duplicate.
- **ABSENT — Demushkin / pro-`p` groups.**  No `Demushkin`, no `maximalProP`/`proPCompletion`.
  `IsPGroup` (finite) and `ProfiniteGrp`/`profiniteCompletion`/`OpenNormalSubgroup` exist.
  ⇒ **T-05 (max pro-`p` quotient) is build-from-scratch** (confirmed), on top of `profiniteQuotient`.
- **ABSENT** any Demushkin classification ⇒ **B3** stays an axiom (stated via `IsDemushkin`,
  `ContCoh` H¹/H² + cup, per `docs/formalization-plan.md`).

## B5 — local reciprocity · B6 — local Tate duality · B9 — Evens/corestriction

**ClassFieldTheory (`3565c752`) — substantial local-CFT machinery, but the reciprocity map itself
is not there yet.**

- **Local field API** (`IsNonarchimedeanLocalField/`): ramification `e`, inertia `f`,
  `e_mul_f_eq_n`, `IsUnramified`, `FiniteDimensional K L` — **proved**.  The `IsNonarchimedeanLocalField ℚ_[p]`
  instance is present but **carries `sorry`s** (⇒ using the CFT local-field API for ℚ₂ rigorously is
  not yet free).  `valuationShortComplex : 0 → 𝒪[L]ˣ → Lˣ → ℤ → 0` **proved**.
- **Cohomology** (`Cohomology/`, all over `Rep ℤ G`, **finite** `G`): `tateCohomology` (+ `zeroIso`,
  `negOneIso`) proved; **`Corestriction`** with `cores₀/cores₁/cores_obj` and the key
  `cores_res : rest ≫ cores = |S|·id` **proved** (⇒ directly usable for **B9**'s corestriction);
  `restriction`, `inflation` proved; **`inflationRestriction` exactness — `sorry`**; Herbrand
  quotient (SES multiplicativity proved; `h(Lˣ)=[L:K]` proved; `h(𝒪ˣ)=1` `sorry`);
  **`localInv : H²(ℤ/nℤ, ℤ) ≅ ZMod n`** proved (Brauer-map seed).
- **LocalCFT** (`LocalCFT/`): `Continuity` (`continuous_algebraMap`, `ContinuousSMul K L`) and
  `Teichmuller` proved.  **No Artin/reciprocity map `Kˣ → Gal(Kᵃᵇ/K)`, no fundamental class**
  (blueprint plans them via the unramified case; `UnramifiedCohomology` vanishing is `sorry`).
- **Mathlib**: `Hilbert90` (`H¹(Gal(L/K), Lˣ)=0`) proved.  **Local Tate duality — ABSENT**
  (no perfect pairing / Pontryagin dual).  **Local Euler characteristic — ABSENT**.  Brauer group
  `Algebra.BrauerGroup` (CSA quotient) exists but **no `localInvariant : H²(k,Gₘ) ≅ ℚ/ℤ`**.
- ⇒ **B5** (reciprocity) and **B6** (Tate duality) stay axioms; CFT gives the surrounding tower
  (Herbrand, Tate, corestriction, valuation SES) but not the maps themselves.  **B9**'s
  corestriction *is* available in CFT (`cores_res`), over finite `G`.

## B7 — local Euler characteristic · B7′ — dyadic Hilbert symbol

- **Hilbert symbol — ABSENT.**  No `HilbertSymbol`/`hilbertSymbol`, local or global, anywhere.
  ⇒ **T-07 builds it from scratch.**
- **Quadratic forms — EXISTS (char ≠ 2).**  `QuadraticForm`/`QuadraticMap`, `.discr`, `Isometry`,
  `IsometryEquiv`, `Equivalent`, `Anisotropic`, and diagonalization
  `exists_orthogonal_basis` — **but the latter needs `[Invertible (2 : K)]`, so it does NOT apply
  over `𝔽₂`** (relevant to B9's characteristic-2 forms).  **ABSENT**: Witt ring/group of a field
  (only `WittVector`, unrelated), Witt cancellation, **Arf invariant**, any char-2 quadratic-form
  theory, **Stiefel–Whitney classes**.
- **`ℚ₂`/`ℤ₂` units — EXISTS partially.**  `PadicInt` (`ℤ_[p]`), `Padic`, `padicValNat/Int/Rat`,
  `PadicInt.unitCoeff : x ≠ 0 → ℤ_[p]ˣ`, `PadicInt.valuation`, `ZMod.unitsEquivCoprime`.
  **ABSENT**: the decomposition `ℤ₂ˣ ≅ {±1} × (1+2ℤ₂)`, and the maps `ε(u)=(u−1)/2 mod 2`,
  `ω(u)=(u²−1)/8 mod 2`.
- **Local Euler characteristic — ABSENT** (Galois version; only unrelated `eulerChar`s).  ⇒ **B7**
  stays an axiom.
- ⇒ **T-07**: define `hilbertSymbol a b` (via solvability of `z²=ax²+by²` — the quadratic-form API
  supports this in char ≠ 2), plus `ε`, `ω` and the `ℤ₂ˣ` decomposition, then the **B7′** axiom
  (Serre CiA III §1.2 Thm 1).  Plan unchanged.

## B8 — Galois action on `π₁(ℙ¹∖{0,1,∞})`

- **ABSENT** (expected) étale fundamental group / `π₁`.  Stated as the group-theoretic conclusion
  (Lemma 3.6); see `docs/formalization-plan.md` B8.

## B9 detail — Kummer theory, Stiefel–Whitney, Evens norm

- **Kummer theory**: **EXISTS** `FieldTheory.KummerExtension` — `autEquivRootsOfUnity`,
  `autEquivZmod`, `X_pow_sub_C_splits_of_isPrimitiveRoot`, explicit factorization
  (polynomial/extension level).  **ABSENT** the cohomological `H¹(k, μ_n) ≅ kˣ/(kˣ)ⁿ` and the
  Kummer class cocycle `a ↦ [g ↦ g(ⁿ√a)/ⁿ√a]`.  ⇒ **T-13 (Kummer class)**: build the cocycle
  ourselves (in `ContCoh`), reusing the extension-level facts.
- **Evens norm / Stiefel–Whitney**: **Stiefel–Whitney classes of quadratic forms — ABSENT** in
  Mathlib, as is any char-2 / Arf theory (see B7′).  The Evens norm and the low-degree SW classes
  are transcribed from the paper's explicit cocycles (per `docs/formalization-plan.md` B9); CFT's
  `cores` (`cores_res` proved) supplies corestriction.

## Ticket implications

- **T-05 (max pro-`p` quotient)** — **build from scratch**; nothing in Mathlib
  (`maximalProP`/`proPCompletion` absent).  Foundation available: `ProfiniteGrp`,
  `profiniteCompletion`, `OpenNormalSubgroup`, `IsPGroup`, and our `profiniteQuotient`.  Plan
  unchanged (`docs/formalization-plan.md` I4).
- **T-13 (Kummer class)** — **build the cocycle** in `ContCoh`; reuse `FieldTheory.KummerExtension`
  (`autEquivRootsOfUnity`, splitting) for the field-theoretic input.  No cohomological Kummer iso
  in Mathlib.
- **T-15 (μ_n as a discrete `G`-module)** — **build**: `rootsOfUnity`, `IsPrimitiveRoot`,
  `cyclotomicCharacter`/`modularCyclotomicCharacter : (L≃+*L) →* (ZMod n)ˣ` exist, but the
  `DistribMulAction`/continuity of the Galois action on `rootsOfUnity` (needed as a `ContCoh`
  coefficient) is **absent** — assemble it from the Galois action + Krull-open stabilizers.
- **Cohomology coefficient bridges** — the *discrete* analogue of our `toContRep` already exists
  (`Rep.ofDistribMulAction`); keep our `CtsCohBridge.toContRep` for the *continuous* side.
- **Cup products** — Mathlib has none anywhere; `GQ2/CupProduct.lean` is the only cup product in
  scope.  (If ever upstreaming, both continuous and discrete `groupCohomology` would want it.)
- **T-07 (Hilbert symbol + B7′)** — **build**: no Hilbert symbol in Mathlib.  Reuse the (char ≠ 2)
  `QuadraticForm` API for the `z²=ax²+by²` solvability definition; build `ε`, `ω`, the
  `ℤ₂ˣ ≅ {±1}×(1+2ℤ₂)` decomposition from `PadicInt.unitCoeff`/`padicVal*`.  No shared deps ⇒ can
  start immediately.
- **B9 char-2 caveat** — Mathlib's quadratic-form diagonalization requires `Invertible 2`, so it is
  unavailable over `𝔽₂`; B9's SW/Evens content must use the paper's explicit diagonal
  representatives, not a Mathlib diagonalization.

## Cross-cutting notes

- **Compactness of `AbsGalQ2`**: actionable follow-up — `CompactSpace Gal(K/k)` (`[IsGalois k K]`)
  + `IsGalois ℚ_[2] (AlgebraicClosure ℚ_[2])` (char 0) should discharge the `[CompactSpace AbsGalQ2]`
  hypotheses in `main_presentation`; needs a small def-compatibility lemma.
- **CFT's `ℚ_[p]` local-field instance is `sorry`-carrying** — don't treat CFT's local-field API for
  ℚ₂ as axiom-clean yet.
- **Naming**: our `ContCoh` inhomogeneous conventions equal Mathlib's discrete `IsCocycle₁/₂`, so a
  future "our `Hⁱ` = Mathlib discrete `groupCohomology`" comparison (for finite quotients) is
  convention-compatible.

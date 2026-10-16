# Tau Ceti discharge campaign: plan

Goal: prove the nine literature inputs (B1, B3c, B5, B6, B7, B8, B9, B10, B11a) from the
[Tau Ceti](https://github.com/TauCetiProject/TauCeti) library, so that the presentation theorems
for `Γ_A` and `Γ_R` print exactly `propext`, `Classical.choice`, `Quot.sound`, with no
`LiteratureInputs` hypothesis and no `axiom` declaration anywhere in the repository.

Board: [`tauceti-tickets.md`](tauceti-tickets.md). Written 2026-10-16.

## 1. Starting point

- The proof graph already takes the nine inputs as the typeclass `GQ2.LiteratureInputs`
  (`GQ2/Foundations/LiteratureInputs.lean`). The generic capstones
  `GQ2.main_presentation_literal_of_inputs` and
  `GQ2.main_presentation_literal_roe_unconditional_of_inputs` are sorry-free at the standard three
  axioms. The only axiom-backed object is the instance in `GQ2/Foundations/AxiomInstance.lean`,
  assembled from the nine `axiom`s in `GQ2/Foundations/Axioms.lean`.
- So the campaign is: build a second `LiteratureInputs` term from Tau Ceti theorems, instantiate
  the generic capstones with it, then delete the axiom file. No consumer of the nine inputs
  changes.
- Tau Ceti's own fleet tracked this exact goal in
  `~/claude/tauceti-fleet/targets/gq2_axiom_targets.md`: 346 roadmap milestones, 345 landed, the
  one open item (`cyclotomic-conductor`) serves no GQ2 axiom. The list's closing "Gaps" paragraph
  names the gq2-side adapters; §3 below is that paragraph expanded against the current sources.
- Tau Ceti main at `706344c35` (2026-10-16), toolchain `v4.35.0`, Mathlib `cfc55fc58`. A
  source-only checkout is at `~/claude/tauceti-main` (a `git worktree` of
  `~/claude/tauceti-site`, no `.lake`). gq2-lean is at `v4.31.0-rc2`, Mathlib `ec410d23d`
  (2026-06-12).

## 2. Platform decisions

**Pin.** `lean-toolchain` → `leanprover/lean4:v4.35.0`; `require TauCeti` at `706344c35`; Mathlib
pinned to Tau Ceti's manifest revision `cfc55fc58714a59dc06e6e79edc6d1d95140d3c2` so the two
manifests agree. If a later Tau Ceti revision is needed, both pins move together.

**Worktree.** All building happens in a new worktree `~/claude/gq2-tauceti` on branch `tauceti`
(the main checkout has no `.lake` build and stays on `master`). Caches:

```bash
lake exe cache get                                        # Mathlib oleans
LAKE_CACHE_DIR=.lake/cache lake cache get --package=TauCeti --service=tauceti-public  # Tau Ceti oleans
```

The second line needs a `[[cache.service]]` entry named `tauceti-public` with
`artifactEndpoint = https://cache.taucetiproject.org/artifacts` and
`revisionEndpoint = https://cache.taucetiproject.org/revisions`, passed through `LAKE_CONFIG`
(copy the step from `~/claude/tauceti-lgg-tate-module/.github/workflows/ci.yml`, lines 56-110).
Tau Ceti's cache is `platformIndependent`, so a hit is expected on arm64 macOS. A miss is not
fatal: `lake build GQ2` compiles only the imported closure of Tau Ceti, not all 15,394 files.
No sibling in `~/claude` has `v4.35.0` + `cfc55fc`, so `bin/lake-restore` cannot clone; budget
roughly 8-10 GB against the 67 GB free.

**Module system.** Every Tau Ceti file is `module` + `public import`, as is GQ2, so adapter files
are ordinary `module` files. The capstone file that instantiates `main_presentation_literal_of_inputs`
imports the §2/§8 stack and must therefore be plain-import style (see `roe-tickets.md`,
2026-07-25 pitfall).

**Namespaces.** Both libraries define `IsProP`, `D0`/`d0A`/`d0S`/`d0Y`, `kummerClass`,
`H0`/`H1`/`H2`, `Zhat`/`zHat`. Adapter files never `open TauCeti` at top level; Tau Ceti names
are written qualified.

**Owner gates.**
- G0 (before T0): the trust base changes from "nine cited theorems, stated in this repository"
  to "Tau Ceti's proofs of them". Tau Ceti enforces zero sorries and an axiom allowlist in CI,
  but is machine-written. The owner accepts this trade.
- G1 (before C2): deleting `GQ2/Foundations/Axioms.lean` is the census flip 9 → 0; it waits for
  owner sign-off like the B9-A T5 gate.
- G2 (at C3): whether to keep the legacy Comparator pair `Challenge.lean`/`Solution.lean`
  once it, too, prints the standard three.

## 3. Axiom-by-axiom map

Each row gives the gq2 field type (verbatim in `LiteratureInputs`), the Tau Ceti source, and the
translation the adapter must do. File paths are relative to `~/claude/tauceti-main/TauCeti/` and
line numbers are at `706344c35`.

### Shared dictionaries

**A1, Galois groups.** `GQ2.AbsGalQ2` is `Field.absoluteGaloisGroup ℚ_[2]`, the same group Tau
Ceti's local theory is stated on, so no transport is needed at the base. Tau Ceti's cohomological
layer is stated on `AbsoluteGaloisGroup K` (over `SeparableClosure K`); the bridge is
`absoluteGaloisGroupRestrictEquiv K : Field.absoluteGaloisGroup K ≃ₜ* AbsoluteGaloisGroup K`
(`FieldTheory/Galois/AbsoluteGaloisGroup/Basic.lean:325`). For a finite
`k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])` the gq2 statements use `k.fixingSubgroup`;
Tau Ceti uses `Field.absoluteGaloisGroup k` with the local-field instances
`finiteIntermediateFieldValuativeRel`, `finiteIntermediateFieldTopology` (as in
`ClassFieldTheory/Local/EulerCharacteristic/Theorem.lean:45-60`) and `galoisSubgroup K L σ`
(`FieldTheory/Galois/AbsoluteGaloisGroup/FiniteExtension.lean:138`) with
`absoluteGaloisGroupExtend` (`:201`). A1 provides
`k.fixingSubgroup ≃ₜ* Field.absoluteGaloisGroup k` and the instance package on `k`, and
identifies `GQ2.chiCyc` with `localCyclotomicCharacter 2 ℚ_[2]`
(`FieldTheory/Galois/AbsoluteGaloisGroup/Cyclotomic/Character.lean:33`).

**A2, cohomology.** `GQ2.ContCoh.H0/H1/H2` (`GQ2/Cohomology.lean`) and
`TauCeti.ContCohomology.H0/H1/H2` (`RepresentationTheory/Homological/ContCohomology/LowDegree.lean`)
are both the explicit inhomogeneous complex with `Z1 = C1 ⊓ ker d1`, `B2 = d1(C1)`; the expected
outcome is an `AddEquiv` by unfolding. From there
`explicitH1AddEquivContinuousCohomology` / `explicitH2AddEquivContinuousCohomology`
(`ContCohomology/CohomologyComparison.lean:134, :232`) reach `continuousCohomology i A`, which is
what the arithmetic theorems are stated on. Cup products: gq2 `cup11/cup02/cup20`
(`GQ2/CupProduct.lean`) and `trivialCupPairing` (`GQ2/Demushkin.lean:95`) against
`(trivialF2TopPairing G).cup i j` (`ContCohomology/Cup/TrivialF2/Basic.lean:66`). Kummer classes:
`GQ2.kummerClassK k a` (`GQ2/EvensKahn.lean:437`) against
`TauCeti.kummerClass a : continuousCohomology 1 (trivialF2 (AbsoluteGaloisGroup k))`
(`FieldTheory/GaloisCohomology/MuTwo/Basic.lean:355`); both are the class of the cocycle
`g ↦ g√a/√a`. Restriction `res1/res2` against `explicitRes1/2`.

**P1, pro-p and presentations.** `GQ2.IsProP` (`GQ2/MaxProP.lean:61`) and `TauCeti.IsProP`
(`Topology/Algebra/Group/Profinite/ProP/Basic.lean:68`) are the same predicate word for word.
`GQ2.maxProPQuotient p G` (`MaxProP.lean:152`) and `TauCeti.maximalProPQuotient p G`
(`Profinite/MaximalProP.lean:105`) are both `G ⧸ proPKernel p G`; show the two kernels coincide.
`GQ2.FreeProfiniteGroup X` (`GQ2/FreeProfinite.lean:38`) and `TauCeti.freeProfiniteGroup X`
(`Profinite/Free/Basic.lean:60`): both profinite completions of `FreeGroup X`, possibly
definitionally equal. `GQ2.profinitePresentation rels` against `presentedProfiniteGroup X rels`
(`Profinite/Presentation/Basic.lean:99`) and `presentedProP p X rels` (`:490`);
`freeProP p X = maximalProPQuotient p (freeProfiniteGroup X)` (`Free/ProP.lean:72`).
`GQ2.Zhat` (`GQ2/Zhat.lean:119`, completion of `Multiplicative ℤ`) against `TauCeti.zHat`
(`Profinite/ZHat/Basic.lean:66`), with `GQ2.zhatProjTwo` against the `ℤ₂` component of
`ZHat/Decomposition.lean`. `GQ2.zpowZtwo` (`GQ2/ZtwoPowering.lean:351`) against
`IsProP.padicPow` (`ProP/PadicPow.lean:135`): both are characterized by their images in every
finite quotient, so uniqueness on either side gives the identity.

### B1, topological finite generation

- gq2: `∃ s : Finset AbsGalQ2, (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤`.
- Tau Ceti: `isTopologicallyFinitelyGenerated_absoluteGaloisGroup p K`
  (`NumberTheory/LocalField/Generation/AbsoluteGaloisGroup.lean:67`), for
  `[IsNonarchimedeanLocalField K] [Algebra ℚ_[p] K] [Module.Finite ℚ_[p] K] [ValuativeExtension ℚ_[p] K]`.
- Translation: instances at `K = ℚ_[2]` from `NumberTheory/LocalField/Padic.lean`; unfold
  `TauCeti.IsTopologicallyFinitelyGenerated` (`Topology/Algebra/Group/Generation.lean:73`) to
  the `Finset` form. Easy.

### B7, local Euler characteristic

- gq2: for finite discrete `M : Type` with continuous `AbsGalQ2`-action,
  `Finite H0 ∧ Finite H1 ∧ Finite H2 ∧ #H1 = #H0 * #H2 * 2 ^ padicValNat 2 (#M)`.
- Tau Ceti: `eulerCharacteristic_mixed p n hn A hA`
  (`ClassFieldTheory/Local/EulerCharacteristic/Theorem.lean:98`):
  `#H¹(A) = #H⁰(A) * #H²(A) * p ^ (finrank ℚ_[p] F * padicValNat p (#A.V))` for
  `A : GalRep n F`, `[Finite A.V]`, `[Fact (IsSmoothDiscrete (ZMod n) A)]`; finiteness from
  `finite_H` (used at `Formula.lean:57`).
- Translation: package `M` as `A : GalRep (Nat.card M) ℚ_[2]` (`M` is `#M`-torsion, so a
  `ZMod (#M)`-module; a finite discrete module with continuous action has open stabilizers, which
  is `IsSmoothDiscrete`); `finrank ℚ_[2] ℚ_[2] = 1`; transport cardinalities through A2. Medium.

### B6, local Tate duality at every finite `k/ℚ₂`

- gq2: `tateDualityAt G n hloc : TateDualityG G n` for `hloc : IsLocalDualizingGroup G n`
  (`G` open-embeds in `AbsGalQ2` with finite index, compatibly with `MuN n`); the bundle is
  `inv : H2 G (MuN n) ≃+ ZMod n` plus bijectivity of `x ↦ inv ∘ (x ∪ ·)` onto the Pontryagin
  dual in degree pairs `(0,2)`, `(1,1)`, `(2,0)` (`GQ2/TateDuality.lean:208-244`).
- Tau Ceti: `tateDualityPairing_perfect_mixed F n hn A tr hA i j hij`
  (`ClassFieldTheory/Local/Duality/Perfect.lean:280`): both-sided nondegeneracy of
  `tateDualityPairing A tr i j` (`Duality/Basic.lean:385`) for finite smooth-discrete
  `A : GalRep n F`, with `tr` supplied by `h2MuEquivZMod_mixed`
  (`ClassFieldTheory/Brauer/RootsOfUnity.lean:145`); `tateDual A` (`Duality/Basic.lean:88`),
  `muNRep n F` (`ClassFieldTheory/MuNRep.lean:137`), `muNRepToTateDual`
  (`Duality/RootsOfUnity.lean:61`).
- Translation: (i) from `hloc` produce the finite `K := fixedField ι.range` and
  `G ≃ₜ* Field.absoluteGaloisGroup K` (open finite-index subgroup ⇒ fixing subgroup of a finite
  extension; `absoluteGaloisGroupExtend` and the `range_absoluteGaloisGroupExtend_*` lemmas in
  `Local/EulerCharacteristic/Shapiro.lean:114-160` show the pattern); (ii) `MuN n ≅ (muNRep n K).V`
  equivariantly and `MuDual n M ≅ (tateDual A).V`; (iii) bijectivity from two-sided
  nondegeneracy plus finiteness of both sides (a counting argument, unless `Perfect.lean:220-242`
  already gives the bijective form; check first). Hard; the largest adapter.

### B11a, the Hilbert-symbol norm criterion

- gq2: `kummerClassK k a ⌣[htriv] kummerClassK k b = 0 ↔ ∃ x y : k, b = x ^ 2 - a * y ^ 2`.
- Tau Ceti: `cup_kummerClass_eq_zero_iff a b` (`FieldTheory/GaloisCohomology/MuTwo/CupNorm.lean:100`),
  over any field of characteristic not 2; no local hypothesis.
- Translation: entirely A1 + A2 (fixing subgroup, explicit `H1`/`H2`, cup, Kummer class). Medium,
  and the best first consumer of the dictionaries.

### B9, the relative Stiefel-Whitney identity

- gq2: the two-component identity on `swOne`/`swTwo` (`GQ2/StiefelWhitney.lean:413, :423`) of
  `traceFormTwisted k δ a` and `traceFormOne k δ` (`GQ2/TraceForm.lean:142, :153`), with
  `corH1` and `evensNormH2` (`GQ2/EvensKahn.lean:261, :332`) of the Kummer cocycle `α` of `β`.
- Tau Ceti: `sw1Class_formClass_traceTransfer_smul_sq`
  (`FieldTheory/QuadraticForm/StiefelWhitney/Transfer.lean:91`) and
  `sw2Class_formClass_traceTransfer_smul_sq` (`StiefelWhitney/QuadraticExtension.lean:209`):
  `sw2Class (Tr⟨a⟩) = sw2Class (Tr⟨1⟩) + galoisEvens K L σ hfin (kummerClass a) + cup (sw1Class (Tr⟨1⟩)) (galoisCor K L σ 1 (kummerClass a))`,
  over any field of characteristic not 2. Supporting: `sw1Class`/`sw2Class`
  (`StiefelWhitney/Class.lean:99, :190`), `QuadraticMap.traceTransfer`
  (`LinearAlgebra/QuadraticForm/Transfer/Basic.lean:139`), `galoisCor`
  (`GaloisCohomology/Corestriction/Basic.lean:75`), `galoisEvens`
  (`GaloisCohomology/EvensNorm.lean:84`), `evensNormIndexTwo_homClass`
  (`ContCohomology/Evens/IndexTwoNorm.lean:89`) and `graphClass` (`Evens/Class.lean:258`).
- Translation: `swOne/swTwo` of a `QuadraticForm k V` against `sw1Class/sw2Class` of its
  `RegularFormClass`; `traceFormTwisted k δ a` is `((a • sq).traceTransfer k)` on
  `L = quadExt k δ`; `corH1 … α …` against `galoisCor k L σ 1 (kummerClass a)`; gq2's
  `evensNormH2` is the graph class of a homomorphism, so compare with `graphClass` at
  `galoisSubgroup k L σ` through `evensNormIndexTwo_homClass`; the stabilizer of `δ` in
  `k.fixingSubgroup` against `galoisSubgroup`. Hard, all dictionary.

### B5, local reciprocity

- gq2: `LocalReciprocity` (`GQ2/Reciprocity.lean:225`): `recip : ℚ_[2]ˣ →* AbsGalQ2ab`
  continuous with dense range; `nu_ur : AbsGalQ2ab →* Multiplicative ℤ_[2]` continuous
  surjective; `norm_reciprocity` on every finite abelian `L/ℚ₂` (surjective onto `Gal(L/ℚ₂)` with
  kernel `normSubgroup L`); `nu_ur_recip : nu_ur (recip x) = ofAdd (-(v₂ x))`;
  `chiCyc_recip_unit : chiCycAb (recip u) = u⁻¹`; `chiCyc_recip_uniformizer : chiCycAb (recip 2) = 1`.
- Tau Ceti: `artinMap ℚ_[2] : ℚ_[2]ˣ →* Field.absoluteGaloisGroupAbelianization ℚ_[2]`
  (`ClassFieldTheory/Local/ArtinMap.lean:114`), the same target as `AbsGalQ2ab`;
  `continuous_artinMap` (`:248`), `denseRange_artinMap` (`:188`), `injective_artinMap`
  (`LocalExistence/ArtinMap.lean:113`); `unramifiedCoordinate K : G^ab →ₜ* zHat`
  (`NumberTheory/LocalField/Unramified/Coordinate.lean:77`) with
  `unramifiedCoordinate_artinMap x = zHat.ofInt (normalizedValuation K x)`
  (`Local/Unramified.lean:407`); finite reciprocity `localArtinEquiv` and the kernel description
  (`Local/Reciprocity.lean`, `Formation/ArtinMap.lean:159`); `localCyclotomicCharacter_artinMap_unit`
  (`Local/ExplicitCyclotomicSymbol/ArtinMap.lean:311`, gives `(norm u)⁻¹`, and `norm = id` at
  `K = ℚ_[2]`); `localCyclotomicCharacter_artinMap_padic_uniformizer` (`Local/Cyclotomic.lean:364`,
  value `1` at the uniformizer `Units.mk0 (p : ℚ_[p])`, which is gq2's `uniformizer`).
- Translation: `recip := artinMap ℚ_[2]` (arithmetic on both sides);
  `nu_ur := inverse ∘ ℤ₂-reduction ∘ unramifiedCoordinate` (Tau Ceti's coordinate is arithmetic,
  gq2's `ν_ur` geometric, hence the sign in `nu_ur_recip`); `norm_reciprocity` needs
  `restrictAb L hab` against the finite layer's Artin map and gq2's `normSubgroup L` against
  `normGroup`. Hard, mostly for the `norm_reciprocity` field.

### B10, the oriented tame quotient

- gq2: `OrientedTameQuotient R` (`GQ2/TameQuotient.lean:70-117`): closed normal pro-2
  `W ≤ AbsGalQ2`, `equiv : AbsGalQ2 ⧸ W ≃ₜ* Ttame` with
  `Ttame = profinitePresentation {tameWord}` (geometric Frobenius: `σ⁻¹τσ = τ²`,
  `GQ2/BoundaryFrame.lean:124-185`), `nuT : Ttame →ₜ* Ztwo`, and the two clauses
  `nuT_recip_unit` (units ↦ `1`) and `nuT_recip_uniformizer` (`rec 2` ↦ `ztwoOne⁻¹`).
- Tau Ceti: `wildInertiaSubgroup ℚ_[2]` (`NumberTheory/LocalField/WildInertia.lean:245`),
  `isClosed_wildInertiaSubgroup`, `isProP_wildInertiaSubgroup` (`:473`);
  `tameQuotient K = G_K ⧸ wildInertiaSubgroup K` (`LocalField/Tame/Quotient.lean:144`);
  `tameQuotientGeometricEquiv hσ τ hτ : tameQuotient K ≃ₜ* IwasawaGroupGeometric K`
  (`Tame/Geometric.lean:194`) where `IwasawaGroupGeometric K = presentedProfiniteGroup (ULift (Fin 2)) {γ⁻¹ τ γ τ⁻ᵠ}`
  with `q = Nat.card 𝓀[K]`, and `natCard_residueField : Nat.card 𝓀[ℚ_[p]] = p`
  (`LocalField/Padic.lean:155`); `iwasawaCoordinateGeometric` (`Tame/Geometric.lean:167`);
  `tameQuotientGeometricEquiv_toTameQuotient_frobenius` (`:199`, arithmetic Frobenius ↦
  `iwasawaSigmaGeometric⁻¹`); the inputs `hσ : IsArithFrobeniusLift K σ` and a tame generator
  `τ` with `hτ` from `exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top`
  (`Tame/Quotient.lean:160`).
- Translation: `Ttame ≃ₜ* IwasawaGroupGeometric ℚ_[2]` through P1 (same relator once `q = 2`);
  `nuT` against the `ℤ₂`-reduction of `iwasawaCoordinateGeometric`; `ztwoOne` against the
  reduction of `zHat.gen`; the orientation clauses from `unramifiedCoordinate_artinMap` (units
  have coordinate `1`, the uniformizer has coordinate `gen`) composed with B5's `recip`. Depends on
  B5. Medium-hard.

### B3c, the dyadic orientation

- gq2: `DyadicOrientation` (`GQ2/Orientation.lean:73`): `equiv : maxProPQuotient 2 AbsGalQ2 ≃ₜ* D0`
  with `D0 = maxProPQuotient 2 (profinitePresentation {A²S⁴[S,Y]})`
  (`GQ2/DyadicPresentation.lean:45-93`); `chiTwo` continuous, descending `chiCyc`, surjective,
  with values `(-1, 1, (-3)⁻¹)` at `equiv.symm d0A/d0S/d0Y`.
- Tau Ceti: `absoluteGaloisGroupProP_two_ratPadic_marked`
  (`NumberTheory/LocalField/ProP/RatPadic.lean:91`):
  `∃ e : absoluteGaloisGroupProP 2 ℚ_[2] ≃ₜ* demushkinD0, standardD0Orientation.comp e = cyclotomicOrientation 2 ℚ_[2] _ ∧ Surjective (cyclotomicOrientation …)`;
  `absoluteGaloisGroupProP p K = maximalProPQuotient p (Field.absoluteGaloisGroup K)`
  (`FieldTheory/Galois/AbsoluteGaloisGroup/ProP.lean:28`); `cyclotomicOrientation` is the
  `quotientLift` of `continuousLocalCyclotomicCharacter`
  (`AbsoluteGaloisGroup/Cyclotomic/Orientation.lean:82`), which is the descent clause;
  `demushkinD0 = presentedProP 2 (Fin 3) {d0Relator}` with `d0A/d0S/d0Y`
  (`Topology/Algebra/Group/Profinite/Demushkin/D0/Basic.lean:77-110`) and the values of
  `standardD0Orientation` on them (`Demushkin/D0/Invariants.lean`).
- Translation: `GQ2.D0 ≃ₜ* demushkinD0` carrying generators to generators (P1: presentation of a
  max-pro-2 quotient against `presentedProP`; check `d0Relator` on both sides is `A²S⁴[S,Y]` in
  the same commutator convention); `GQ2.maxProPQuotient 2 AbsGalQ2 ≃ₜ* absoluteGaloisGroupProP 2 ℚ_[2]`
  (P1); `chiTwo := cyclotomicOrientation ∘ (that equiv)`, descent from A1's
  `chiCyc = localCyclotomicCharacter`; the three values from `standardD0Orientation`'s value
  theorems. Hard, mostly P1.

### B8, the peripheral cyclotomic action

- gq2: `PeripheralCyclotomicAction` (`GQ2/PeripheralAction.lean:92`): an exponent embedding
  `ι : ℤ_[2]ˣ → Zhat` (continuous, `ι 1 = omega2`, `zhatProjTwo (ι u) = ofAdd u`) and for each
  `u` an automorphism of `Delta = maxProPQuotient 2 (FreeProfiniteGroup (Fin 2))` sending
  `deltaP/deltaT/deltaC` to conjugates of `x ^ᶻ ι u`.
- Tau Ceti: `exists_peripheralPowerAutomorphism_two hF e u`
  (`Topology/Algebra/Group/Profinite/Free/Peripheral/Dyadic.lean:124`): for pro-2 `F` with
  `e : F ≃ₜ* freeProP 2 (Fin 2)`, an automorphism with `φ P = cP⁻¹ (P^u) cP` etc., `cP = 1`,
  powers `hF.padicPow`; `periphP/T/C` (`:70-78`), with `C = (PT)⁻¹` as in gq2.
- Translation: `Delta ≃ₜ* freeProP 2 (Fin 2)` (P1, since
  `freeProP 2 X = maximalProPQuotient 2 (freeProfiniteGroup X)`); `x ^ᶻ ι u = zpowZtwo x u`
  (gq2's `zpowHat_eq_zpowZtwo`) against `padicPow` (P1); construct `ι` in gq2 as the element of
  `Zhat` with `2`-component `u` and trivial odd part, through the `zHat` decomposition
  (`Profinite/ZHat/Decomposition.lean`) and P1's `Zhat ≃ zHat`. Medium.

## 4. Assembly and census flip

- `GQ2/TauCeti/Instance.lean`: `noncomputable def tauCetiInputs : LiteratureInputs` from the
  nine adapters.
- `GQ2/TauCeti/Main.lean` (plain-import style): the four unconditional capstones
  `main_presentation_literal_tauceti`, `main_presentation_literal_roe_tauceti`,
  `main_surjection_count_tauceti`, `main_surjection_count_R_tauceti`, each by `haveI := tauCetiInputs`
  on the `_of_inputs` theorem. `#print axioms` must be exactly the standard three.
- `GQ2/TauCetiAxiomAudit.lean` alongside `PalomarAxiomAudit.lean`; `scripts/check_axioms.sh`
  gains the four names in a new audit block with expected set = standard three; CI gets the Tau
  Ceti cache step.
- Census flip (after G1): delete `GQ2/Foundations/Axioms.lean` and `AxiomInstance.lean`; the
  nine public names (`GQ2.localReciprocity`, `GQ2.tateDualityAt`, …) become same-name
  theorems/defs backed by the adapters, so the existing consumers, `Challenge.lean`,
  `Solution.lean` and the Palomar pair are untouched; `EXPECTED_AXIOMS=0`,
  `AUDIT_EXPECTED_AXIOMS` = standard three; `AxiomLedger.bAxioms` emptied or retargeted.
- Docs: `formalization.yaml` (axiom lists, `status.scope`, divergence (i), review notes),
  `README.md`, `docs/literature-axioms.md` and the one-page summary (each leaf: "proved via
  Tau Ceti `…`"), `comparator-config*.json`, `docs/README.md`.

## 5. Risks

- **Mathlib bump volume.** Four months of Mathlib over 121k lines in 310 files. Statements are
  byte-identical by rule; only proofs and names move. Run `/bump-mathlib` file by file, commit per
  green batch. This is the long pole and gates everything else.
- **Cache miss on macOS.** Then Tau Ceti's import closure builds from source in the worktree; the
  roadmap checkouts in `~/claude` show this closure built in about 1.6 GB.
- **Convention mismatches** are known and listed above: arithmetic vs geometric Frobenius
  (`ν_ur`, `nuT`, `ztwoOne⁻¹`), commutator convention in `d0Relator`, `Additive` vs
  `Multiplicative` targets (`MuN n`, `Multiplicative ℤ_[2]`, `Multiplicative (ZMod 2)` in
  `graphClass`), ULift in Tau Ceti's presentations.
- **Universes.** Tau Ceti states `continuousCohomology.{0,u,u}` on `GalRep n F : Type (u+1)`;
  gq2's bundle quantifies modules over `Type`. The B7 field already uses `M : Type` for this reason.
- **B6 is the open-ended piece**: the bijective form of perfectness and the `IsLocalDualizingGroup`
  ⇒ `fixedField` reconstruction may need lemmas that are not on Tau Ceti main. If so, they are
  proved in gq2 first and offered upstream afterwards.

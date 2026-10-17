# Dyadic Tau Ceti discharge: T2 recon memo (B5-K, B10-K)

Ticket T2 of [`tauceti-discharge-tickets.md`](tauceti-discharge-tickets.md), against plan
[`tauceti-discharge-plan.md`](tauceti-discharge-plan.md) §3. Written 2026-10-17 at Tau Ceti
`706344c35`, Mathlib `cfc55fc58`, Lean `v4.35.0`, on branch `dyadic-tauceti` after T1. The format
follows the ℚ₂ campaign's memo [`../orchestration/tauceti-t2-recon.md`](../orchestration/tauceti-t2-recon.md);
its cross-cutting findings 1–7 (Tau Ceti definitions are not exposed, instance-search timeouts
under heavy imports, two topologies on a finite `↥k`, …) all still hold and are not repeated here.

**Result.** Both `K`-level inputs are **closed in scratch**. These two terms elaborate with no
`sorry`, and `#print axioms` gives exactly `propext, Classical.choice, Quot.sound`:

- `GQ2.TauCetiBridge.markedRecipAt_tauceti K : Dyadic.MarkedRecip localReciprocity_tauceti K`,
  with all twelve fields;
- `GQ2.TauCetiBridge.orientedTameQuotientAt_tauceti K FF : Dyadic.OrientedTameQuotientK (markedRecipAt_tauceti K) FF`,
  with all seven fields.

They are in `tauceti-t2-evidence/full/b5k_b10k.lean` (963 lines). **No Tau Ceti lemma is
missing.** Every gap between gq2's statements and Tau Ceti's is a gq2-side lemma, proved in the
prototypes: the norm ↔ valuation bridge, the topology comparison, the residue count, a
closed-subgroup lemma for `ℤ₂`, unramified ⇒ equal norm value groups, and `IwasawaGroupGeometric ≃ Tq q`.

**Smoke file.** [`GQ2/TauCeti/SmokeK.lean`](../../GQ2/TauCeti/SmokeK.lean) has 409 lines. It is a
`module` in `namespace GQ2.TauCetiBridge` and imports 29 Tau Ceti modules, 3 Mathlib modules and 9
gq2 modules: the adapters `GaloisDict`, `B5`, `B10` and `ProPDict`, the two bundles,
`UnitFiltrationCounts`, `TraceForm` and `Foundations.TauCetiInstance`.

- Section `Signatures` `#check`s 108 declarations by full name. The verbatim output is
  [`tauceti-t2-evidence/smokeK-check-output.txt`](tauceti-t2-evidence/smokeK-check-output.txt),
  and every signature quoted below comes from it.
- Section `AtK` fixes `K : IntermediateField ℚ_[2] ℚ̄₂` with `[FiniteDimensional ℚ_[2] K]`.
  Through a local macro `pkgK K t`, which is A1's `letI valuativeRel / letI localTopology / haveI
  isNonarchimedeanLocalField`, it instantiates every source at `↥K` in 32 `example`s.
- Seven of those examples use `fail_if_success` to pin an instance that does **not** synthesize,
  or a `rfl` that fails.

`tools.sh chk GQ2/TauCeti/SmokeK.lean` prints `OK` in about 25 s. The file is not imported by the
library, so the build loop does not build it.

**Scratch evidence.** The prototypes are in [`tauceti-t2-evidence/`](tauceti-t2-evidence/README.md),
one subdirectory per lane, outside every `lean_lib`. Each file elaborates with `tools.sh chk` and
contains no `sorry`, and each `#print axioms` gives the standard three. The files cannot import one
another, so each repeats what it needs from the files before it. Paths below are relative to that
directory.

| lane | scratch status | prototype |
|---|---|---|
| A1-K bridge, topology, Q3 | **complete**: norm ↔ valuation bridge, `localTopology_eq`, `#𝓀[↥K] = 2 ^ FF.f` | `bridge/bridge.lean` (light imports) |
| B5-K `recip`, `continuous_recip`, `denseRange_recip` | **complete** | `recipK/b5k.lean` |
| B5-K `nu_ur`, `continuous_nu_ur`, `nu_ur_recip_unit`, `nu_ur_recip_uniformizer` | **complete** | `recipK/b5k.lean` |
| B5-K `norm_compat` | **complete** (`artinMap_norm` at `(ℚ₂, ↥K)`) | `recipK/b5k.lean` |
| B5-K `r`, `nu_ker_chi_le`, `nu_ker_chi_ge` (Q1) | **complete**; no ramification fact about `ℚ₂(μ_{2^∞})` is needed | `recipK/b5k.lean` |
| B5-K `ki_unramified` (Q2) | **complete** | `kiunram/ki.lean` |
| B5-K assembled | **complete term** `markedRecipAt_tauceti K` | `kiunram/ki.lean`, `full/b5k_b10k.lean` |
| B10-K `W`, `normal`, `isClosed`, `isProP` | **complete** | `tameK/b10k.lean` |
| B10-K `equiv` (Q3) | **complete**: generic `IwasawaGroupGeometric L ≃ₜ* Tq q` for `#𝓀[L] = q` | `tameK/b10k.lean` |
| B10-K `nuT_recip_unit`, `nuT_recip_uniformizer` | **complete** (one lemma for any lift) | `tameK/b10k.lean` |
| B10-K assembled | **complete term** `orientedTameQuotientAt_tauceti K FF` | `full/b5k_b10k.lean` |

## Answers to the three recon questions

### Q1: `ν_ur(ker χ_K) = 2^r ℤ₂`

**Answer: easy. Neither the finiteness of the unramified part of `K(μ_{2^∞})/K` nor any ramification
fact about `ℚ₂(μ_{2^∞})` is needed.** The proof is in `recipK/b5k.lean`, about 100 lines.

1. **The witness `rec_K(2)`.** Let `d = [K : ℚ₂]` and `e = v_K(2)`.
   - **Its cyclotomic value.** `χ_K(rec_K 2) = χ(rec_{ℚ₂}(N_{K/ℚ₂} 2))` by `norm_compat` and gq2's
     `chiCycAb_inclAbK`. Then `χ(rec_{ℚ₂}(N 2)) = χ(rec_{ℚ₂}(2))^d = 1`, using B5's clause
     `chiCyc_recip_uniformizer` and `Algebra.norm_algebraMap`. These are `normUnitsK_two` and
     `chiCycKAb_recipK_two`.
   - **Its unramified value.** `ν_ur(rec_K 2) = ofAdd (−v_K(2))` is `nuUrK_recipK`.
     `v_K(2) ≠ 0` because `‖2‖ < 1` and the bridge applies; this is `normalizedValuation_two_ne_one`.
   - So `rec_K(2) ∈ ker χ_K` has `ν`-value `−e ≠ 0`. As a by-product, `r ≤ v₂(e_K)`.
2. **Closed subgroups of `ℤ_[2]`.** `exists_level` is generic. Let `A` be a compact group, and
   let `χ : A →* ℤ₂ˣ` and `ν : A →* Multiplicative ℤ₂` be continuous.
   - `ker χ` is closed, hence compact, so `S = ν(ker χ)` is compact, hence closed in `ℤ₂`.
   - A closed additive subgroup of `ℤ₂` is an ideal. This is `mul_mem_of_isClosed`, 10 lines from
     Mathlib's `PadicInt.denseRange_intCast`.
   - A nonzero ideal is `2^r ℤ₂` by Mathlib's `PadicInt.ideal_eq_span_pow_p`. The two clauses are
     the two inclusions.
   - `CompactSpace (GalKab K)` comes from A1's `compactSpace_fixingSubgroup` through
     `Quotient.compactSpace`. It has to be **passed explicitly**; see the instance table.
   - Neither Mathlib nor Tau Ceti has "a closed subgroup of `ℤ_[p]` is an ideal". Tau Ceti's
     `closedSubgroupSubmoduleOrderIso` (`Topology/Algebra/Group/Profinite/ProP/ClosedSubmodule.lean:39`)
     is the pro-`p` version, phrased with `padicPow` scalars, and is not needed.
3. **What Tau Ceti has, for the record.** None of it is used.
   - **Ramification of `ℚ₂(μ_{2^∞})`.** There is no general theorem that `ℚ_p(μ_{p^∞})/ℚ_p` is
     totally ramified. Tau Ceti has two worked examples:
     - `TauCeti.DyadicCyclotomicEight.isTotallyRamified : TauCeti.IsTotallyRamified ℚ_[2] TauCeti.DyadicCyclotomicEight`
       (`NumberTheory/LocalField/WorkedExamples/CyclotomicEight/Basic.lean:146`), with `e = 4`
       (`ramificationIndex_eq_four`, `:142`);
     - `TauCeti.DyadicSqrtNegOne.ramificationIndex_eq_two`
       (`WorkedExamples/DyadicSqrt/NegOne/Ramification.lean:109`).
   - **2-power roots of unity.** An unramified extension of `ℚ₂` has only `±1` as 2-power roots of
     unity: `TauCeti.localRootOfUnityOrder_two_of_isUnramified`
     (`NumberTheory/LocalField/RootsOfUnity/Unramified.lean:45`).
   - **The abelianized cyclotomic character.**
     - `abelianizedLocalCyclotomicCharacter` (`FieldTheory/Galois/AbsoluteGaloisGroup/Cyclotomic/Character.lean:66`)
       and `_mk` (`:73`).
     - `ClassFieldTheory.abelianizedLocalCyclotomicCharacter_artinMap`
       (`NumberTheory/ClassFieldTheory/Local/Cyclotomic.lean:226`). It needs `↑u = ↑(Nat.card 𝓀[K])`
       with `u : ℤ_[p]ˣ`, so **`p` must differ from the residue characteristic**. It is unusable
       at `p = 2` over a dyadic `K`.
     - `ClassFieldTheory.abelianizedLocalCyclotomicCharacter_artinMap_norm` (`:271`): `χ_L(Art_L x) = χ_K(Art_K(N x))`.
       It is the Tau Ceti twin of the argument in step 1. gq2 does not need it, because its `χ_K`
       is defined as the restriction of `chiCyc` (`chiCycKAb_eq_comp`) and `norm_compat` already
       gives the identity.
     - `localCyclotomicCharacter_absoluteGaloisGroupExtend` (`…/Cyclotomic/FiniteExtension.lean:91`).

### Q2: `ki_unramified`

**Answer: proved in about 170 lines** (`kiunram/ki.lean`, `isUnramified_layerE` and
`hasEqualNormValueGroups_of_isUnramified`).

- **Inertia in Tau Ceti.**
  - `TauCeti.inertiaSubgroup K := (maximalUnramifiedExtension K (AlgebraicClosure K)).fixingSubgroup`
    (`NumberTheory/LocalField/Unramified/Inertia/Basic.lean:110`).
  - Fixed-field criterion, algebraic-closure model: `inertiaSubgroup_le_fixingSubgroup_iff` (`:274`).
    It needs `Algebra.IsSeparable K E`.
  - Fixed-field criterion, separable-closure model, **the one used**:
    `map_inertiaSubgroup_le_fixingSubgroup_iff` (`Unramified/Inertia/SeparableClosure.lean:99`).
    It needs only Tau Ceti's package on `↥E`.
  - The maximal unramified extension is `maximalUnramifiedExtension` (`Unramified/Maximal.lean:95`).
- **`ker ν_ur` versus the image of inertia.** The plan's equation "`ker ν_ur` = image of inertia
  in `G_K^ab`" is **false**.
  - Tau Ceti's `ker_unramifiedCoordinate` (`Unramified/Coordinate.lean:159`) is about the
    `ℤ̂`-valued coordinate. gq2's `ν_ur` is its `ℤ₂`-component, so `ker ν_ur` also contains the
    prime-to-2 part `∏_{ℓ odd} ℤ_ℓ` of the unramified quotient.
  - Only `inertia ⊆ ker ν_ur` is needed. It is `unramifiedCoordinate_mk_eq_one_iff` (`:148`) and
    takes three lines (`nuUrK_toAbK_of_mem_inertia`).
  - So the clause's hypothesis, which quantifies over `ker ν_ur`, is *stronger* than "inertia acts
    trivially on `μ₄`". This makes the axiom weaker than the classical statement and the proof easier.
- **Why `μ₄` gives `K(i)` unramified.** The proof has three steps.
  1. `χ(g) ≡ 1 (mod 4)` forces `g(δi) = δi`. This is Mathlib's `cyclotomicCharacter.spec`
     (`Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean:324`) at `δi^{2^2} = 1`, the
     pattern of gq2's `GQ2/Dyadic/CyclotomicKummerBridge.lean`. The prototype is
     `fixes_of_chiCyc_mod_four`.
  2. Take `E := (layerEmb K (quadExt K δi)).fieldRange`, an intermediate field of `↥K`'s separable
     closure. A1's B9 lemma `fixingEquivAbsGal_mem_galoisSubgroup_quadExt_iff`
     (`GQ2/TauCeti/GaloisDict.lean:357`) and Tau Ceti's `galoisSubgroup_toSubgroup`
     (`FieldTheory/Galois/AbsoluteGaloisGroup/FiniteExtension.lean:146`) turn step 1 into
     `(inertiaSubgroup ↥K).map restrictEquiv ≤ E.fixingSubgroup`. The bridge is
     `fixingEquivAbsGal K (absGalEquivFixing K τ) = restrictEquiv τ`, by `fixingEquivAbsGal_apply`.
  3. `map_inertiaSubgroup_le_fixingSubgroup_iff E` gives `TauCeti.IsUnramified ↥K ↥E`.
- **`IsUnramified` and equal norm value groups.** Only `IsUnramified ⇒ HasEqualNormValueGroups`
  is needed.
  - It uses `isUnramified_iff_normalizedValuation_comp_unitsMap_surjective`
    (`Unramified/Basic.lean:134`): every `z ∈ Eˣ` has the normalized valuation of some `w ∈ Kˣ`.
    Equal normalized valuations give equal valuations (`toAdd_normalizedValuation_le_iff_valuation_le`),
    and then the **bridge at `↥E`** gives equal spectral norms.
  - The bridge at `↥E` is the generic `vle_iff_of_isEquiv` over the base `↥K`. Its `w` is gq2's
    norm through `sepClosureEquiv K`, and its `IsEquiv` hypothesis is the `K`-level bridge. So it
    costs about 15 lines.
  - The plan's `isUnramified_iff_normalizedValuation_algebraMap` and
    `isUnramified_iff_ramificationIndex_eq_one` are not the convenient forms.
  - The converse direction is never needed.
- Tau Ceti's `localCyclotomicCharacter_eq_one_of_mem_inertiaSubgroup`
  (`Unramified/Inertia/Cyclotomic.lean:47`) needs `p.Coprime (ringChar 𝓀[K])`, so it does not
  apply at `p = 2`. This is the reason the argument runs through `ker ν_ur` instead.

### Q3: `Nat.card 𝓀[↥K] = 2 ^ FF.f`

**Answer: yes, without any private lemma** (`bridge/bridge.lean`, `natCard_residueField_eq_two_pow`,
about 45 lines).

- **gq2's ball is Tau Ceti's ring of integers.** gq2's unit ball `UnitFiltrationCounts.Osub K =
  {‖x‖ ≤ 1}` *is* Tau Ceti's `𝒪[↥K] = (valuation ↥K).integer`, as subrings of `↥K`. This is
  `osub_eq_integer`, by the bridge.
- **The residue fields have the same size.** The residue map `Osub K → 𝓀[↥K]` is surjective, and its
  kernel is gq2's `maxIdeal K = {‖x‖ < 1}` (by Mathlib's `Valuation.Integer.not_isUnit_iff_valuation_lt_one`).
  So `#𝓀[↥K] = #(UnitFiltrationCounts.ResidueField K)`.
- **gq2 already counts its own residue field.** gq2's `UnitFiltrationCounts.residueField_card_eq_pow_f`
  (`GQ2/UnitFiltrationCounts.lean:366`, **public**) gives `#(O/𝔪) = 2 ^ FF.f`.
- **D2 is moot.** Neither `card_gradeZero` (public, `:217`) nor `card_gradeI` is needed directly.
- Tau Ceti's `inertiaDegree` and `ramificationIndex` are not needed.

## Findings the orchestrator must know

1. **No missing Tau Ceti lemma.** Both bundles are closed by existing Tau Ceti declarations plus
   six gq2-side lemma groups, all prototyped:
   - the norm ↔ valuation bridge, about 60 lines;
   - `localTopology_eq`, about 25 lines;
   - the residue count, about 45 lines;
   - closed subgroups of `ℤ₂` and the level, about 70 lines;
   - unramified ⇒ equal norm value groups, about 60 lines;
   - `IwasawaGroupGeometric L ≃ₜ* Tq q`, about 130 lines.

   The plan's "hard" clauses (`r`, `ki_unramified`) are each a few dozen lines of composition.
2. **The plan's Q1 and Q2 routes are replaced.**
   - The finiteness of the unramified part of `K(μ_{2^∞})/K` is never needed. The witness
     `rec_K(2)` suffices (Q1).
   - "`ker ν_ur` = image of inertia" is false as an equation, and only `⊇` is used (Q2).
   - The A1-K item "`chiCycKAb K` against `abelianizedLocalCyclotomicCharacter 2 ↥K`" is
     **unnecessary**. No clause needs Tau Ceti's cyclotomic character at `↥K`.
3. **The two topologies on `↥K` must be proved equal.** The ℚ₂ memo recorded them as "equal but not
   definitionally". Nobody had proved equality, and `continuous_recip` needs it because gq2's
   statement uses the subspace topology on `(↥K)ˣ`.
   - `localTopology_eq` is proved by showing the subspace topology is an `IsValuativeTopology` for
     Tau Ceti's relation. It uses `IsValuativeTopology.of_mem_nhds_zero_iff_vle` with gq2's
     `NormedField.valuation`, then compares neighbourhoods with `IsValuativeTopology.mem_nhds_iff`.
   - Even with the equation, `Continuous.comp` must be applied with **explicit `@` instances**.
     Instance-implicit arguments are re-synthesized and then compared, giving "synthesized type
     class instance is not definitionally equal".
4. **`GQ2.localReciprocity` is not exposed outside `GQ2/Foundations/TauCetiInstance.lean`.** So
   `MarkedRecip localReciprocity_tauceti K` cannot be used where `MarkedRecip localReciprocity K`
   is expected in any other module; this is pinned by a `fail_if_success rfl` in `SmokeK.lean`.
   - The C1' same-name `noncomputable def`s `markedRecipAt` and `orientedTameQuotientAt` must
     therefore live **in `TauCetiInstance.lean` itself**. That is where the plan puts them, and
     where `tameQuotient := tameQuotient_tauceti` already relies on the same unfolding.
   - The alternative is for that file to export `localReciprocity_eq : localReciprocity =
     localReciprocity_tauceti := rfl` for a cast.
   - B5K/B10K must be stated at `localReciprocity_tauceti`, as the plan says.
5. **Instances.** Two need care.
   - `ValuativeExtension ℚ₂ ↥K` is **not** produced by the three-`letI` package. It must be
     `haveI`'d from A1's `valuativeExtension K`, and that is what makes `FinitePadicExtension ↥K 2`
     and `artinMap_norm` work. Plan §3 assumed `FinitePadicExtension ↥K 2` "is found after A1's
     `letI` package". It is found only with this fourth `haveI`.
   - `CharP 𝓀[↥K] 2` must be supplied as `charP_residueField K 2`, as at ℚ₂.
   - The full table is below.

## Instance table (all tested in `SmokeK.lean`, section `AtK`, and in the prototypes)

The package `pkgK K` is `letI := valuativeRel K; letI := localTopology K; haveI := isNonarchimedeanLocalField K`.

| instance at `↥K` | after `pkgK K` | supplied by |
|---|---|---|
| `ValuativeRel ↥K`, `TopologicalSpace ↥K` (local), `IsNonarchimedeanLocalField ↥K` | the package itself | A1 `valuativeRel K`, `localTopology K`, `isNonarchimedeanLocalField K` |
| local topology beats the global subspace topology | yes (`(inferInstance : TopologicalSpace K) = localTopology K := rfl` under the package) | — |
| `Algebra.IsAlgebraic ℚ_[2] ↥K` | **synthesizes** | — |
| `ValuativeExtension ℚ_[2] ↥K` | **no** (`fail_if_success`) | `haveI := valuativeExtension K` (A1) |
| `TauCeti.FinitePadicExtension ↥K 2` | synthesizes once `valuativeExtension K` is in context (`ofInstances`) | — |
| `CharP 𝓀[↥K] 2` | **no** (`fail_if_success`) | `TauCeti.charP_residueField K 2` |
| `(TauCeti.wildInertiaSubgroup ↥K).Normal` | **synthesizes** | — |
| `localTopology K = instTopologicalSpaceSubtype` | **not `rfl`** (`fail_if_success`) | A1-K `localTopology_eq` (prototype) |
| `CompactSpace (Dyadic.GalK K)` | **no** (`fail_if_success`); A1's instance is on the `Kummer.GaloisGroup` path | `compactSpace_fixingSubgroup K` (the same term) |
| `CompactSpace (Dyadic.GalKab K)` | `Quotient.compactSpace` works once `CompactSpace (GalK K)` is `haveI`'d (smoke); **but** as the instance argument of `exists_level` it was not found even with `haveI := compactSpace_galKab K` in context | pass `compactSpace_galKab K` explicitly: `@exists_level (GalKab K) _ _ (compactSpace_galKab K) …` |
| `GalK K ≃ₜ* ↥(K.fixingSubgroup : Subgroup (Kummer.GaloisGroup ℚ₂))` | `ContinuousMulEquiv.refl _` typechecks | `galKEquiv` (prototype) |
| `FiniteDimensional ↥K ↥(quadExt K δi)` | **no** (`fail_if_success`) | `finiteDimensional_quadExt K (-1) _` (`GQ2/TraceForm.lean:79`) |
| `FiniteDimensional ↥K ↥E`, `E = (layerEmb K (quadExt K δi)).fieldRange` | no | `(AlgHom.equivFieldRange _).toLinearEquiv.finiteDimensional` |
| package on `↥E` | — | `TauCeti.finiteIntermediateFieldValuativeRel/Topology ↥K (SeparableClosure ↥K) E`, `finiteIntermediateField_isNonarchimedeanLocalField`, `finiteIntermediateField_valuativeExtension` |
| `Algebra.IsAlgebraic ↥K ↥E` | not tried | `Algebra.IsAlgebraic.of_finite K _` |

**Pathology met.** Under the heavy B5 imports, one `simpa using hπ.le` (a goal about
`‖(1 : ↥K) : ℚ̄₂‖`) timed out at `DiscreteTopology ℚ̄₂` (20000 heartbeats). The bridge file, on
light imports, ran the same `simpa` fine. So A1-K's bridge belongs in a light file
(`GaloisDictK.lean`), and heavy files should use explicit `rw [OneMemClass.coe_one, norm_one]`.
No `Module.IsTorsionFree` or `IsAlgClosure` timeout was met: no prototype searches for Galois
instances at `ℚ̄₂/ℚ₂`.

## A1-K: dictionary additions

Prototype: `bridge/bridge.lean` (light imports: `GaloisDict`, `LocalField.NormalizedValuation`,
`LocalField.Padic`, `LocalField.AlgebraicExtension.Basic`, Mathlib `ValuativeTopology`,
`GQ2.UnitFiltrationCounts`). The `G_K^{ab}` part is in `recipK/b5k.lean`. Status: **complete**.

### gq2 side
- `GalKsub K : Subgroup AbsGalQ2 := K.fixingSubgroup` (`GQ2/Dyadic/MarkedRecipBundle.lean:138`).
  - `GalK K := ↥(GalKsub K)` (`:141`).
  - `GalKab K := TopologicalAbelianization (GalK K)` (`:151`).
  - `toAbK` (`:154`), `chiCycK` (`:162`), `chiCycKAb` (`:177`), `inclAbK` (`:206`) with
    `inclAbK_toAbK` (`:210`, `rfl`), `chiCycAb_inclAbK` (`:223`), `normUnitsK` (`:227`).
- The spectral norm `‖·‖` of `ℚ̄₂` (Mathlib's `PadicAlgCl`, `= spectralNorm ℚ_[2] ℚ̄₂`).
  `‖(x : ↥K)‖ = ‖(x : ℚ̄₂)‖` holds by `rfl`.
- `UnitFiltrationCounts.Osub`, `maxIdeal`, `ResidueField`, `residueField_card_eq_pow_f`
  (`GQ2/UnitFiltrationCounts.lean:47, :57, :91, :366`).

### Tau Ceti sources
Paths are relative to `.lake/packages/TauCeti/TauCeti/`.
- `TauCeti.finiteIntermediateFieldValuativeRel` (`NumberTheory/LocalField/FiniteExtension/IntermediateField.lean:69`).
  `…Topology` is at `:75`, `…_valuativeExtension` at `:81`, `…_isValuativeTopology` at `:89`,
  `…_isNonarchimedeanLocalField` at `:97`.
  ```lean
  TauCeti.finiteIntermediateField_isValuativeTopology : ∀ (K : Type u_1) [inst : Field K] [inst_1 : ValuativeRel K]
    [inst_2 : TopologicalSpace K] [inst_3 : IsNonarchimedeanLocalField K] (Ω : Type u_2) [inst_4 : Field Ω]
    [inst_5 : Algebra K Ω] (M : IntermediateField K Ω) [inst_6 : Module.Finite K ↥M], IsValuativeTopology ↥M
  ```
  The relation is `algebraicExtensionValuativeRel K M`, the spectral norm of `M/K` with respect to
  `K`'s *normalized* absolute value. It is **not exposed**, so go through the two uniqueness
  theorems below, never through its body.
- `TauCeti.vle_iff_algebraicExtensionNormedField_norm_le` (`NumberTheory/LocalField/AlgebraicExtension/Basic.lean:266`):
  ```lean
  ∀ (K : Type u_1) [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K]
    [inst_3 : IsNonarchimedeanLocalField K] {M : Type u_2} [inst_4 : Field M] [inst_5 : Algebra K M]
    [inst_6 : Algebra.IsAlgebraic K M] [inst_7 : ValuativeRel M] [ValuativeExtension K M] (x y : M),
    x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖
  ```
  Here `‖·‖` is `algebraicExtensionNormedField K M`.
- `TauCeti.algebraicExtensionNormedField_norm_le_norm_iff` (same file, `:241`):
  ```lean
  ∀ {K : Type u_1} … {M : Type u_2} [inst_4 : Field M] [inst_5 : Algebra K M] [inst_6 : Algebra.IsAlgebraic K M]
    {Γ : Type u_3} [inst_7 : LinearOrderedCommGroupWithZero Γ] {w : Valuation M Γ},
    (Valuation.comap (algebraMap K M) w).IsEquiv (valuation K) → ∀ (x y : M), ‖x‖ ≤ ‖y‖ ↔ w x ≤ w y
  ```
- `Padic.normalizedAbsoluteValue_eq_nnnorm` (`NumberTheory/LocalField/Padic.lean:164`):
  `∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (x : ℚ_[p]), ↑((TauCeti.normalizedAbsoluteValue ℚ_[p]) x) = ‖x‖₊`.
  It is used together with `TauCeti.normalizedAbsoluteValue_le_normalizedAbsoluteValue_iff`
  (`NumberTheory/LocalField/NormalizedValuation.lean:493`):
  `(TauCeti.normalizedAbsoluteValue K) x ≤ (TauCeti.normalizedAbsoluteValue K) y ↔ (valuation K) x ≤ (valuation K) y`.
- `TauCeti.normalizedValuation : (K : Type u_1) → … → Kˣ →* Multiplicative ℤ` (`NormalizedValuation.lean:114`).
  - `normalizedValuation_eq_one_iff` (`:232`): `(TauCeti.normalizedValuation K) x = 1 ↔ (valuation K) ↑x = 1`.
  - `toAdd_normalizedValuation_le_iff_valuation_le` (`:258`):
    `Multiplicative.toAdd ((TauCeti.normalizedValuation K) x) ≤ Multiplicative.toAdd ((TauCeti.normalizedValuation K) y) ↔ (valuation K) ↑y ≤ (valuation K) ↑x`.
  - `normalizedValuation_surjective` (`:327`).
- `IsValuativeTopology.of_mem_nhds_zero_iff_vle` (Mathlib, `Topology/Algebra/ValuativeRel/ValuativeTopology.lean:116`):
  ```lean
  ∀ {R : Type u_1} [inst : Ring R] [inst_1 : ValuativeRel R] {Γ₀ : Type u_2} [inst_2 : LinearOrderedCommGroupWithZero Γ₀]
    [inst_3 : TopologicalSpace R] (v : Valuation R Γ₀) [v.Compatible] [IsTopologicalAddGroup R],
    (∀ {s : Set R}, s ∈ nhds 0 ↔ ∃ γ, {z | v.restrict z < ↑γ} ⊆ s) → IsValuativeTopology R
  ```
  Also `IsValuativeTopology.mem_nhds_iff` (same file, `:171`).
- `ContinuousMulEquiv.topologicalAbelianizationCongr` (`Topology/Algebra/Group/TopologicalAbelianization.lean:208`),
  `G ≃ₜ* H → TopologicalAbelianization G ≃ₜ* TopologicalAbelianization H`, with `_mk` (`:214`):
  `e.topologicalAbelianizationCongr ↑x = ↑(e x)`.
- `Valuation.Integer.not_isUnit_iff_valuation_lt_one` (Mathlib, `RingTheory/Valuation/Integers.lean:288`):
  `¬IsUnit x ↔ v ↑x < 1`.
- From A1: `absGalEquivFixing` (`GQ2/TauCeti/GaloisDict.lean:194`), `coe_absGalEquivFixing_apply`
  (`:199`), `compactSpace_fixingSubgroup` (`:107`).

### Translation (all tested)
- **The bridge: one line from Tau Ceti.**
  ```lean
  theorem vle_iff_of_isEquiv … (hw : (w.comap (algebraMap F M)).IsEquiv (valuation F)) (x y : M) :
      x ≤ᵥ y ↔ w x ≤ w y :=
    (TauCeti.vle_iff_algebraicExtensionNormedField_norm_le F x y).trans
      (TauCeti.algebraicExtensionNormedField_norm_le_norm_iff hw x y)
  ```
  - At `F = ℚ₂` and `M = ↥K`, take `w = normValuation K := NormedField.valuation.comap K.val`.
    Its `IsEquiv` hypothesis (`isEquiv_normValuation`) is `norm_algebraMap'` plus
    `Padic.normalizedAbsoluteValue_eq_nnnorm`.
  - Result: **`vle_iff_norm_le K x y : x ≤ᵥ y ↔ ‖(x : ℚ̄₂)‖ ≤ ‖(y : ℚ̄₂)‖`** and
    `valuation_le_iff_norm_le`.
  - No unfolding of a Tau Ceti definition is involved, so it survives Tau Ceti's lack of `@[expose]`.
- **Normalized valuations** (each about 10 to 40 lines):
  - `normalizedValuation_eq_one_of_norm_eq_one`: `‖u‖ = 1 → v_K(u) = 1`;
  - `normalizedValuation_eq_ofAdd_one_of_norm`: gq2's spectral uniformizer has `v_K = ofAdd 1`;
  - `normalizedValuation_two_ne_one`.
- **`localTopology_eq`.** First `isValuativeTopology_subtype`. The `Compatible` instance for gq2's
  `NormedField.valuation` on `↥K` is the bridge, and the neighbourhood description is
  `NormedField.toValued.is_topological_valuation`; the subspace topology *is* the normed-field
  topology of `SubfieldClass.toNormedField` by `rfl`. Then `TopologicalSpace.ext_nhds` with
  `IsValuativeTopology.mem_nhds_iff` on both sides.
- **`abEquivK K := ((galKEquiv K).trans (absGalEquivFixing K).symm).topologicalAbelianizationCongr`.**
  - `galKEquiv := ContinuousMulEquiv.refl _` bridges gq2's `AbsGalQ2`-path `GalK K` and A1's
    `Kummer.GaloisGroup`-path `↥K.fixingSubgroup` (bundle memo R6).
  - Value lemmas: `abEquivK_toAbK`, and `abEquivK_symm_mk : abEquivK.symm ↑τ = toAbK (galKEquiv.symm (absGalEquivFixing K τ))`.
  - The plan wanted `inclAbK` "matched to the abelianization of `absoluteGaloisGroupExtend`". That
    is not needed: `inclAbK_toAbK` (`rfl`) plus `coe_absGalEquivFixing_apply` work pointwise.
- **Q3** is as described in the answer above.

### Missing lemmas
None in Tau Ceti. The gq2-side lemmas are listed under the proposed A1-K list at the end.

## B5-K: `markedRecipAt_tauceti K : MarkedRecip localReciprocity_tauceti K`

Result: **closed in scratch** (`kiunram/ki.lean:607`, standard three axioms).

### gq2 side
`structure MarkedRecip (R : LocalReciprocity) (K) [FiniteDimensional ℚ_[2] K]`
(`GQ2/Dyadic/MarkedRecipBundle.lean:571`), with these fields, verbatim:
```lean
recip : (↥K)ˣ →* GalKab K
continuous_recip : Continuous recip
denseRange_recip : DenseRange recip
nu_ur : GalKab K →* Multiplicative ℤ_[2]
continuous_nu_ur : Continuous nu_ur
norm_compat : ∀ x : (↥K)ˣ, inclAbK K (recip x) = R.recip (normUnitsK K x)
nu_ur_recip_unit : ∀ u : (↥K)ˣ, ‖((u : ↥K) : AlgebraicClosure ℚ_[2])‖ = 1 →
    nu_ur (recip u) = 1
nu_ur_recip_uniformizer : ∀ π : (↥K)ˣ,
    ‖((π : ↥K) : AlgebraicClosure ℚ_[2])‖ < 1 →
    (∀ z : ↥K, z ≠ 0 → ‖(z : AlgebraicClosure ℚ_[2])‖ < 1 →
      ‖(z : AlgebraicClosure ℚ_[2])‖ ≤ ‖((π : ↥K) : AlgebraicClosure ℚ_[2])‖) →
    nu_ur (recip π) = Multiplicative.ofAdd ((-1 : ℤ) : ℤ_[2])
r : ℕ
nu_ker_chi_le : ∀ g : GalKab K, chiCycKAb K g = 1 →
    ∃ y : ℤ_[2], (nu_ur g).toAdd = 2 ^ r * y
nu_ker_chi_ge : ∀ y : ℤ_[2], ∃ g : GalKab K,
    chiCycKAb K g = 1 ∧ (nu_ur g).toAdd = 2 ^ r * y
ki_unramified : (∀ g : GalKab K, nu_ur g = 1 →
      (PadicInt.toZModPow 2 ((chiCycKAb K g : ℤ_[2]ˣ) : ℤ_[2])) = 1) →
    ∀ δi : AlgebraicClosure ℚ_[2], δi ^ 2 = -1 → HasEqualNormValueGroups K δi
```
`HasEqualNormValueGroups K δa` (`:105`) says: every nonzero `z = x + y·δa` with `x, y ∈ ↥K` has
`‖z‖ = ‖w‖` for some nonzero `w ∈ ↥K`.

### Field by field

Each field is listed with its Tau Ceti source, its instances, its translation, its status and any
missing lemma.

#### 1. `recip`

- **Source.** `TauCeti.ClassFieldTheory.artinMap` (`NumberTheory/ClassFieldTheory/Local/ArtinMap.lean:114`):
  ```lean
  (K : Type) → [inst : Field K] → [inst_1 : ValuativeRel K] → [inst_2 : TopologicalSpace K] →
    [IsNonarchimedeanLocalField K] → Kˣ →* Field.absoluteGaloisGroupAbelianization K
  ```
- **At `↥K`.** `pkgK K (TauCeti.ClassFieldTheory.artinMap K) : pkgK K (Kˣ →* Field.absoluteGaloisGroupAbelianization K)` (smoke).
- **Instances.** The package suffices.
- **Translation.** `recipK K := (abEquivK K).symm ∘ artinMap ↥K`. Both are arithmetic.
- **Status.** Done (`b5k.lean:208`).

#### 2. `continuous_recip`

- **Source.** `continuous_artinMap` (`:248`): `Continuous ⇑(TauCeti.ClassFieldTheory.artinMap K)`.
- **Instances.** The package. **But** the statement's topology on `(↥K)ˣ` is the global one.
- **Translation.** Use `localTopology_eq` (A1-K), then `@Continuous.comp` with the Units topology
  of `localTopology K` written explicitly.
- **Status.** Done (`b5k.lean:228`).

#### 3. `denseRange_recip`

- **Source.** `denseRange_artinMap` (`:188`).
- **Instances.** The package.
- **Translation.** `(abEquivK K).symm.surjective.denseRange.comp (denseRange_artinMap K) (abEquivK K).symm.continuous`.
  No topology on `↥K` is involved.
- **Status.** Done (`:221`).

#### 4. `nu_ur`

- **Source.** `TauCeti.unramifiedCoordinate` (`NumberTheory/LocalField/Unramified/Coordinate.lean:77`),
  `… → Field.absoluteGaloisGroupAbelianization K →ₜ* ↑TauCeti.zHat.toProfinite.toTop`, together
  with `TauCeti.zHat.lift` (`Topology/Algebra/Group/Profinite/ZHat/Basic.lean:140`).
- **Instances.** The package.
- **Translation.** `nuUrK K := (zHat.lift (ofAdd 1) ∘ unramifiedCoordinate ↥K ∘ abEquivK K)⁻¹`.
  This is B5's `nuUr`, with the inversion between geometric and arithmetic normalization.
- **Status.** Done (`:246`).

#### 5. `continuous_nu_ur`

- **Source.** The same continuous homs.
- **Translation.** `continuous_inv.comp …`.
- **Status.** Done (`:261`).

#### 6. `norm_compat`

- **Source.** `TauCeti.ClassFieldTheory.artinMap_norm` (`ArtinMap.lean:345`):
  ```lean
  ∀ {K : Type} [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K]
    [inst_3 : IsNonarchimedeanLocalField K] (L : Type) [inst_4 : Field L] [inst_5 : Algebra K L]
    [inst_6 : FiniteDimensional K L] (iota : L →ₐ[K] SeparableClosure K) [inst_7 : ValuativeRel L]
    [inst_8 : TopologicalSpace L] [inst_9 : IsNonarchimedeanLocalField L] [ValuativeExtension K L] (x : Lˣ)
    (τ : Field.absoluteGaloisGroup L),
    ↑τ = (TauCeti.ClassFieldTheory.artinMap L) x →
      ↑((TauCeti.absoluteGaloisGroupExtend K L iota) τ) =
        (TauCeti.ClassFieldTheory.artinMap K) ((TauCeti.Algebra.normUnits K) x)
  ```
  Also `TauCeti.Algebra.normUnits` (`RingTheory/Norm/Units.lean:49`), which is
  `Units.map (Algebra.norm R)`, and `TauCeti.Algebra.coe_normUnits` (`:54`).
- **At `(ℚ₂, ↥K)`.** `iota = sepEmb K`.
- **Instances.** The package **plus `haveI := valuativeExtension K`**.
- **Translation.**
  - Lift `artinMap ↥K x` to `τ`. Then `recipK x = toAbK (galKEquiv.symm (absGalEquivFixing K τ))`.
  - `inclAbK_toAbK` and `coe_absGalEquivFixing_apply` turn this into `↑(absoluteGaloisGroupExtend ℚ₂ ↥K (sepEmb K) τ)`.
  - `normUnitsK K x = Algebra.normUnits ℚ₂ x` by `Units.ext` and `coe_normUnits`. It is **not**
    `rfl`, because `normUnits` is not exposed.
  - The right side is `localReciprocity_tauceti.recip = artinMap ℚ₂` (`rfl`, B5).
- **Status.** Done (`:298`, about 20 lines).

#### 7. `nu_ur_recip_unit`

- **Source.** `ClassFieldTheory.unramifiedCoordinate_artinMap` (`NumberTheory/ClassFieldTheory/Local/Unramified.lean:407`):
  ```lean
  ∀ (K : Type) [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K]
    [inst_3 : IsNonarchimedeanLocalField K] (x : Kˣ),
    (TauCeti.unramifiedCoordinate K) ((TauCeti.ClassFieldTheory.artinMap K) x) =
      TauCeti.zHat.ofInt ((TauCeti.normalizedValuation K) x)
  ```
  Also `zHat.lift_ofInt` (`ZHat/Basic.lean:146`):
  `(TauCeti.zHat.lift a) (TauCeti.zHat.ofInt z) = a ^ Multiplicative.toAdd z`.
- **Instances.** The package.
- **Translation.** `nuUrK_recipK : ν(rec x) = ofAdd (−v_K(x))`, then the bridge
  (`normalizedValuation_eq_one_of_norm_eq_one`).
- **Status.** Done (`:269`, `:282`).

#### 8. `nu_ur_recip_uniformizer`

- **Source.** Same as field 7.
- **Translation.** `nuUrK_recipK` with `normalizedValuation_eq_ofAdd_one_of_norm`. gq2's spectral
  "maximal norm `< 1`" spec gives `v_K(π) = 1`, proved through `normalizedValuation_surjective`
  and the bridge.
- **Status.** Done (`:286`).

#### 9. `r`, `nu_ker_chi_le`, `nu_ker_chi_ge`

- **Source.** Field 7's chain, plus B5's `chiCyc_recip_uniformizer`, Mathlib's
  `PadicInt.ideal_eq_span_pow_p` (`NumberTheory/Padics/PadicIntegers.lean:545`):
  `s ≠ ⊥ → ∃ n, s = Ideal.span {↑p ^ n}`, and Mathlib's `PadicInt.denseRange_intCast`
  (`NumberTheory/Padics/RingHoms.lean:513`).
- **Instances.** `CompactSpace (GalKab K)`, passed explicitly.
- **Translation.** Q1 above. `r := (exists_levelK K).choose`.
- **Status.** Done (`:334`, `:408`, about 100 lines).

#### 10. `ki_unramified`

- **Source.** `unramifiedCoordinate_mk_eq_one_iff`, `map_inertiaSubgroup_le_fixingSubgroup_iff`,
  `galoisSubgroup_toSubgroup`, `isUnramified_iff_normalizedValuation_comp_unitsMap_surjective`,
  and the uniqueness theorems of A1-K (signatures below).
- **Instances.** The package on `↥K`, the package on `↥E` (from `finiteIntermediateField*` over
  `↥K`), `FiniteDimensional ↥K ↥(quadExt K δi)` and `FiniteDimensional ↥K ↥E`.
- **Translation.** Q2 above.
- **Status.** Done (`ki.lean:429–605`, about 170 lines).

### Tau Ceti sources for Q2 (verbatim)
- `@TauCeti.unramifiedCoordinate_mk_eq_one_iff` (`Unramified/Coordinate.lean:148`):
  ```lean
  ∀ {K : Type u_1} [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K]
    [inst_3 : IsNonarchimedeanLocalField K] (σ : Field.absoluteGaloisGroup K),
    (TauCeti.unramifiedCoordinate K) ↑σ = 1 ↔ σ ∈ TauCeti.inertiaSubgroup K
  ```
- `@TauCeti.map_inertiaSubgroup_le_fixingSubgroup_iff` (`Unramified/Inertia/SeparableClosure.lean:99`):
  ```lean
  ∀ {K : Type u_1} [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K]
    [inst_3 : IsNonarchimedeanLocalField K] (E : IntermediateField K (SeparableClosure K))
    [inst_4 : ValuativeRel ↥E] [inst_5 : TopologicalSpace ↥E] [inst_6 : IsNonarchimedeanLocalField ↥E]
    [inst_7 : ValuativeExtension K ↥E],
    Subgroup.map (TauCeti.absoluteGaloisGroupRestrictEquiv K).toMonoidHom (TauCeti.inertiaSubgroup K) ≤ E.fixingSubgroup ↔
      TauCeti.IsUnramified K ↥E
  ```
- `TauCeti.galoisSubgroup_toSubgroup` (`FieldTheory/Galois/AbsoluteGaloisGroup/FiniteExtension.lean:146`):
  `↑(TauCeti.galoisSubgroup K L σ) = σ.fieldRange.fixingSubgroup`.
- `TauCeti.isUnramified_iff_normalizedValuation_comp_unitsMap_surjective` (`Unramified/Basic.lean:134`):
  ```lean
  ∀ (K : Type u_1) (L : Type u_2) [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K]
    [inst_3 : IsNonarchimedeanLocalField K] [inst_4 : Field L] [inst_5 : ValuativeRel L] [inst_6 : TopologicalSpace L]
    [inst_7 : IsNonarchimedeanLocalField L] [inst_8 : Algebra K L] [inst_9 : ValuativeExtension K L],
    TauCeti.IsUnramified K L ↔ Function.Surjective ⇑((TauCeti.normalizedValuation L).comp (Units.map ↑(algebraMap K L)))
  ```
  Its siblings `isUnramified_iff_ramificationIndex_eq_one` (`:125`) and
  `isUnramified_iff_normalizedValuation_algebraMap` (`:143`) are not used.
  The class `TauCeti.IsUnramified` is at `Unramified/Basic.lean:113`.
- A1 (gq2):
  - `fixingEquivAbsGal_mem_galoisSubgroup_quadExt_iff` (`GQ2/TauCeti/GaloisDict.lean:357`):
    `(fixingEquivAbsGal k) g ∈ TauCeti.galoisSubgroup (↥k) (↥(quadExt k δ)) (layerEmb k (quadExt k δ)) ↔ ↑g • δ = δ`,
    under `[FiniteDimensional ↥k ↥(quadExt k δ)]`;
  - `fixingEquivAbsGal_apply` (`:268`);
  - `sepClosureEquiv_algebraMap` (`:251`);
  - `sepClosureEquiv_layerEmb` (`:303`).
- Mathlib `cyclotomicCharacter.spec` (`NumberTheory/Cyclotomic/CyclotomicCharacter.lean:324`):
  ```lean
  ∀ {L : Type u_1} [inst : CommRing L] [inst_1 : IsDomain L] (p : ℕ) [inst_2 : Fact (Nat.Prime p)] {n : ℕ}
    [∀ (i : ℕ), HasEnoughRootsOfUnity L (p ^ i)] (g : L ≃+* L) (t : L),
    t ^ p ^ n = 1 → g t = t ^ ((PadicInt.toZModPow n) ↑((cyclotomicCharacter L p) g)).val
  ```
  `(cyclotomicCharacter ℚ̄₂ 2) gr = chiCycKAb K (toAbK K g)` holds by `rfl` (gq2 definitions are exposed).

### Answers
1. *Is any Tau Ceti lemma missing for B5-K?* **No.**
2. *Different hypotheses between Tau Ceti and the bundle field.*
   - `artinMap_norm` needs `ValuativeExtension ℚ₂ ↥K`, which the package does not give.
   - `continuous_artinMap` is for Tau Ceti's topology, not gq2's subspace topology, so
     `localTopology_eq` is needed.
   - `ki_unramified` quantifies over `ker ν_ur`, which is larger than inertia, so the field is
     *easier* than its classical reading.
   - Tau Ceti's inertia criterion lives on `↥K`'s own separable closure, not on `ℚ̄₂`. A1's
     `layerEmb` and `fixingEquivAbsGal` intertwining bridge the two.
3. *Cross-module visibility.* `B10K` needs `(markedRecipAt_tauceti K).recip x = recipK K x`.
   Either `B5K.lean` keeps gq2's `@[expose] public section`, as `B5.lean` does, or it exports
   that equation proved by `rfl`. The B10-K prototype takes it as the hypothesis `hB`.

## B10-K: `orientedTameQuotientAt_tauceti K FF : OrientedTameQuotientK (markedRecipAt_tauceti K) FF`

Result: **closed in scratch** (`full/b5k_b10k.lean`; the B10 part is `tameK/b10k.lean`, standard
three axioms).

### gq2 side
`structure OrientedTameQuotientK {K} [FiniteDimensional ℚ_[2] K] {R} (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)`
(`GQ2/Dyadic/OrientedTameBundle.lean:275`), with these fields, verbatim:
```lean
W : Subgroup (GalK K)
[normal : W.Normal]
isClosed : IsClosed (W : Set (GalK K))
isProP : IsProP 2 W
equiv : ContinuousMulEquiv (GalK K ⧸ W) (Tq (qOf K FF))
nuT_recip_unit : ∀ (u : (↥K)ˣ) (g : GalK K),
    ‖((u : ↥K) : ℚ̄₂)‖ = 1 →
    toAbK K g = B.recip u →
    nuTq (qOf K FF) (equiv (QuotientGroup.mk g)) = 1
nuT_recip_uniformizer : ∀ g : GalK K,
    toAbK K g = B.recip (uniformizerK K FF) →
    nuTq (qOf K FF) (equiv (QuotientGroup.mk g)) = ztwoOne⁻¹
```
The other definitions involved:

- `qOf K FF := 2 ^ FF.f` (`:178`) and `uniformizerK K FF` (`:202`), with
  `norm_uniformizerK_lt_one` (`:208`) and `uniformizerK_max` (`:215`).
- `Tq q := profinitePresentation {tameWordQ q}` (`GQ2/Dyadic/TameQuotientK.lean:257`), with
  `tqSigma`, `tqTau` and `tame_relation_q` (`:276`):
  `((Dyadic.tqTau q) ^c Dyadic.tqSigma q) = Dyadic.tqTau q ^ q`.
- `nuTq q : Tq q →ₜ* Ztwo` (`:413`), with `nuTq_tqSigma = ztwoOne` and `nuTq_tqTau = 1`.

### Field by field

Here `phiK K := (absGalEquivFixing K).trans (galKEquiv K).symm : G_{↥K} ≃ₜ* GalK K`.

#### 1. `W`

- **Source.** `TauCeti.wildInertiaSubgroup` (`NumberTheory/LocalField/WildInertia.lean:245`),
  `… → Subgroup (Field.absoluteGaloisGroup K)`.
- **Instances.** The package.
- **Translation.** `wildK K := (wildInertiaSubgroup ↥K).map (phiK K)`.
- **Status.** Done (`b10k.lean:395`).

#### 2. `normal`

- **Source.** `wildInertiaSubgroup_normal` (`:284`), an instance.
- **Instances.** It synthesizes under the package.
- **Translation.** `Subgroup.Normal.map _ _ (phiK K).surjective`.
- **Status.** Done (`:407`).

#### 3. `isClosed`

- **Source.** `isClosed_wildInertiaSubgroup` (`:279`).
- **Instances.** The package.
- **Translation.** `(phiK K).toHomeomorph.isClosedMap`.
- **Status.** Done (`:413`).

#### 4. `isProP`

- **Source.** `isProP_wildInertiaSubgroup` (`:473`):
  `∀ (K : Type u_1) [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K] [inst_3 : IsNonarchimedeanLocalField K] (p : ℕ) [CharP 𝓀[K] p], TauCeti.IsProP p ↥(TauCeti.wildInertiaSubgroup K)`.
  Also `TauCeti.IsProP.of_surjective` (`Topology/Algebra/Group/Profinite/ProP/Basic.lean:146`) and
  `TauCeti.isProP_iff` (`:75`).
- **Instances.** The package, **plus `valuativeExtension K` and `CharP 𝓀[↥K] 2 := charP_residueField K 2`**
  (`AbsoluteRamificationIndex.lean:173`).
- **Translation.**
  - Map onto `W` by `(phiK K).toMonoidHom.subgroupMap`, which is continuous by
    `continuous_induced_rng` and surjective by `subgroupMap_surjective`.
  - Land in gq2's predicate with `TauCeti.isProP_iff.mp`. P1's `isProP_iff_tauCeti` is equivalent
    but not needed.
- **Status.** Done (`:420`).

#### 5. `equiv` (Q3)

- **Source.**
  - `ContinuousMulEquiv.quotientCongr` (`Topology/Algebra/Group/ClosedSubgroup.lean:153`) and
    `quotientCongr_symm_mk` (`:174`);
  - `tameQuotientGeometricEquiv` (`Tame/Geometric.lean:194`);
  - `exists_isArithFrobeniusLift` (`Unramified/Inertia/Basic.lean:384`);
  - `exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top` (`Tame/Quotient.lean:186`);
  - `iwasawaRelatorGeometric_def` (`Tame/Geometric.lean:53`);
  - `inv_iwasawaSigmaGeometric_mul_iwasawaTauGeometric_mul` (`:160`);
  - `presentedProfiniteGroup.lift`, `.lift_of` and `.hom_ext_of` (`Profinite/Presentation/Basic.lean:166, :195, :214`);
  - `freeProfiniteGroup.lift` and `.lift_of` (`Profinite/Free/Basic.lean:124, :129`).
- **Instances.** The package. Both existence theorems elaborate at `↥K` with automatic instances
  (smoke).
- **Translation.** `tameEquivK K FF := (phiK K).quotientCongr wild W h |>.symm ≫ tameQuotientGeometricEquiv hσ τ hτ ≫ iwasawaGeometricEquivTq ↥K (qOf K FF) hq`.
  - Here `hq := natCard_residueField_eq_two_pow K FF |>.trans (qOf_eq K FF).symm` (Q3).
  - The generic `iwasawaGeometricEquivTq L q hq` is B10's construction, with
    `Padic.natCard_residueField` replaced by `hq` and `Ttame`/`tameWord` by `Tq q`/`tameWordQ q`.
  - The equation `h : map = wildK` must be a **named lemma** (`map_wild_eq_wildK`). An inline `rfl`
    makes later `rw`s fail with "not type-correct under the implicit transparency".
- **Status.** Done (`:253–381`, `:433`).

#### 6. `nuT_recip_unit`

- **Source.**
  - `iwasawaCoordinateGeometric_tameQuotientGeometricEquiv` (`Tame/Geometric.lean:231`);
  - `tameQuotientToZHat_toTameQuotient` (`Tame/Quotient.lean:404`);
  - `toTameQuotient_apply` (`:164`);
  - `unramifiedCoordinate_mk` (`Coordinate.lean:88`);
  - `unramifiedCoordinate_artinMap`;
  - `zHat.lift_ofInt`;
  - `iwasawaCoordinateGeometric_iwasawaSigmaGeometric` (`= zHat.gen⁻¹`, `:178`) and
    `_iwasawaTauGeometric` (`= 1`, `:184`).
- **Instances.** The package.
- **Translation.** One lemma for any lift `g` of `rec_K x`:
  `nuTq_tameEquivK_mk : nuTq q (tameEquivK (mk g)) = ztwoOne⁻¹ ^ v_K(x)`. It uses the sign
  `nuTq ∘ iwToTq = zHat.lift ztwoOne⁻¹ ∘ iwasawaCoordinateGeometric` (`nuTq_iwasawaGeometricToTq`,
  by `hom_ext_of`). For units, `v_K(u) = 0` by the bridge.
- **Status.** Done (`:448`, `:473`).

#### 7. `nuT_recip_uniformizer`

- **Source.** The same.
- **Translation.** `v_K(uniformizerK K FF) = 1` by `normalizedValuation_eq_ofAdd_one_of_norm`
  with `norm_uniformizerK_lt_one` and `uniformizerK_max`.
- **Status.** Done.

### Verbatim signatures
- `@TauCeti.tameQuotientGeometricEquiv` (`Tame/Geometric.lean:194`):
  ```lean
  {K : Type u_1} → [inst : Field K] → [inst_1 : ValuativeRel K] → [inst_2 : TopologicalSpace K] →
    [inst_3 : IsNonarchimedeanLocalField K] → {σ : Field.absoluteGaloisGroup K} → TauCeti.IsArithFrobeniusLift K σ →
      (τ : ↥(TauCeti.inertiaSubgroup K)) → (Subgroup.zpowers ((TauCeti.inertiaTameCharacter K) τ)).topologicalClosure = ⊤ →
        TauCeti.tameQuotient K ≃ₜ* TauCeti.IwasawaGroupGeometric K
  ```
- `TauCeti.iwasawaRelatorGeometric_def` (`:53`):
  ```lean
  TauCeti.iwasawaRelatorGeometric K =
    (TauCeti.freeProfiniteGroup.of { down := 0 })⁻¹ * TauCeti.freeProfiniteGroup.of { down := 1 } *
        TauCeti.freeProfiniteGroup.of { down := 0 } *
      (TauCeti.freeProfiniteGroup.of { down := 1 } ^ Nat.card 𝓀[K])⁻¹
  ```
  At `↥K`, `K : Type 0`, so `ULift.{0} (Fin 2)`, exactly as at ℚ₂.
- `TauCeti.inv_iwasawaSigmaGeometric_mul_iwasawaTauGeometric_mul` (`:160`):
  `(TauCeti.iwasawaSigmaGeometric K)⁻¹ * TauCeti.iwasawaTauGeometric K * TauCeti.iwasawaSigmaGeometric K = TauCeti.iwasawaTauGeometric K ^ Nat.card 𝓀[K]`.
- `@ContinuousMulEquiv.quotientCongr` (`Topology/Algebra/Group/ClosedSubgroup.lean:153`):
  `(e : G ≃ₜ* H) → (N : Subgroup G) → (M : Subgroup H) → [inst_4 : N.Normal] → [inst_5 : M.Normal] → Subgroup.map e.toMonoidHom N = M → G ⧸ N ≃ₜ* H ⧸ M`.
- `TauCeti.charP_residueField` (`NumberTheory/LocalField/AbsoluteRamificationIndex.lean:173`):
  `∀ (K : Type u_1) … (p : ℕ) [inst_4 : Fact (Nat.Prime p)] [TauCeti.FinitePadicExtension K p], CharP 𝓀[K] p`.

### Answers
1. *Is any Tau Ceti lemma missing for B10-K?* **No.**
2. *Different hypotheses between Tau Ceti and the bundle field.*
   - `isProP_wildInertiaSubgroup` needs `CharP 𝓀[↥K] 2`, as at ℚ₂.
   - Tau Ceti's relator is at `Nat.card 𝓀[↥K]` while gq2's is at `qOf K FF`. They are bridged by Q3
     through the hypothesis `hq` of the generic equivalence, with no cast on `Tq`.
3. *Dependencies.* B10-K needs B5-K's `recipK` (the equation `B.recip = recipK K`) and A1-K's
   bridge and Q3. It does **not** need P1 (correction to plan §3).

## Corrections to the plan (§3) and board

- **A1-K.** Drop the `chiCycKAb ↔ abelianizedLocalCyclotomicCharacter 2 ↥K` item: no clause uses
  it. Add the following:
  - `localTopology_eq`, which is not in the plan but is needed for `continuous_recip`;
  - the generic `vle_iff_of_isEquiv`;
  - the residue count (Q3), whose ingredients are public, so D2 is moot;
  - `galKEquiv` (R6 path bridge).
- **B5-K `norm_compat`.** The plan said "`normUnitsK` is Tau Ceti's `Algebra.normUnits ℚ_[2]`".
  This holds only propositionally (`Units.ext` with `coe_normUnits`), since `normUnits` is not
  exposed. `artinMap_norm` needs `ValuativeExtension ℚ₂ ↥K`, which must be `haveI`'d.
- **B5-K Q1.** "Hard" becomes **easy**. Use the witness `rec_K(2)` and closed subgroups of `ℤ₂`.
  No ramification of `ℚ₂(μ_{2^∞})` and no finiteness of the unramified part of `K(μ_{2^∞})/K` is
  needed.
- **B5-K Q2.** "`ker ν_ur` in `G_K^ab` is the image of inertia" is false; use only `inertia ⊆ ker ν_ur`
  (`unramifiedCoordinate_mk_eq_one_iff`). The plan's suggested `localArtinMap_unit_of_unramified`
  and `mem_inertiaSubgroup_of_mk_eq_artinMap` pattern is not needed.
  - Use `map_inertiaSubgroup_le_fixingSubgroup_iff`, the separable-closure model, with A1's
    `layerEmb`. The algebraic-closure version would need a second embedding.
  - Use `isUnramified_iff_normalizedValuation_comp_unitsMap_surjective`, in the direction ⇒ only.
- **B10-K.** Drop the P1 dependency. The `ULift` and `fin_cases` pattern of B10 carries over
  verbatim to `Tq q`.
- **C1'.** The two legacy same-name `def`s must be in `TauCetiInstance.lean` (finding 4). The plan
  already says so, but it is now a hard constraint, not a choice.
- **Prototype names to avoid when landing:** `normValuation`, `exists_level`, `layerE`, `phiK`,
  `wildK`, `KiClause`. Check them against `GQ2.TauCetiBridge` and the dyadic tree.

## Difficulty ranking (after recon)

1. **`ki_unramified` (Q2):** medium. About 170 lines, prototyped. The fiddly parts are the
   package on `↥E` and the order of `letI`s in a statement.
2. **B10-K `equiv`:** medium. About 180 lines, almost all a parametrized copy of B10.
3. **A1-K bridge, `localTopology_eq` and Q3:** easy to medium. About 200 lines, prototyped on
   light imports.
4. **`r`, `nu_ker_chi_le`, `nu_ker_chi_ge` (Q1):** easy. About 100 lines.
5. **`norm_compat`:** easy. About 20 lines.
6. **`recip`, `continuous_recip`, `denseRange_recip`, `nu_ur`, the unit and uniformizer clauses,
   and B10-K's `W`, `normal`, `isClosed`, `isProP` and both orientation clauses:** easy. 5 to 30
   lines each.

Estimated landed sizes: `GaloisDictK.lean` about 230 lines, `B5K.lean` about 400, `B10K.lean`
about 260.

## Proposed A1-K lemma list (`GQ2/TauCeti/GaloisDictK.lean`, light imports)

Every lemma uses the variables `(K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]`.
Statements are written under the package, as in the prototypes. Dependencies are in brackets.

| name | statement | depends on |
|---|---|---|
| `vle_iff_of_isEquiv` | generic: `[ValuativeRel M] [ValuativeExtension F M]`, `(w.comap (algebraMap F M)).IsEquiv (valuation F) → (x ≤ᵥ y ↔ w x ≤ w y)` | Tau Ceti uniqueness (AlgebraicExtension/Basic) |
| `normValuation K` | `Valuation ↥K ℝ≥0 := NormedField.valuation.comap K.val`; `normValuation_apply : … = ‖(x : ℚ̄₂)‖₊` (`rfl`) | — |
| `isEquiv_normValuation` | `((normValuation K).comap (algebraMap ℚ₂ ↥K)).IsEquiv (valuation ℚ₂)` | `Padic.normalizedAbsoluteValue_eq_nnnorm` |
| `vle_iff_norm_le` | `letI := valuativeRel K; x ≤ᵥ y ↔ ‖(x : ℚ̄₂)‖ ≤ ‖(y : ℚ̄₂)‖` | the two above, A1 package |
| `valuation_le_iff_norm_le`, `valuation_eq_iff_norm_eq` | the same through `valuation ↥K` | `Valuation.Compatible.vle_iff_le` |
| `normalizedValuation_eq_one_of_norm_eq_one` | `‖(u : ℚ̄₂)‖ = 1 → normalizedValuation ↥K u = 1` | bridge |
| `normalizedValuation_eq_ofAdd_one_of_norm` | gq2's spectral uniformizer spec → `normalizedValuation ↥K π = ofAdd 1` | bridge, `normalizedValuation_surjective` |
| `normalizedValuation_two_ne_one` | `normalizedValuation ↥K (Units.mk0 2 _) ≠ 1` | bridge |
| `isValuativeTopology_subtype`, `localTopology_eq` | the subspace topology is valuative; `localTopology K = instTopologicalSpaceSubtype` | bridge, Mathlib `IsValuativeTopology.of_mem_nhds_zero_iff_vle` |
| `osub_eq_integer`, `osubToResidue`, `ker_osubToResidue`, `natCard_residueField_eq`, `natCard_residueField_eq_two_pow` | `Osub K = 𝒪[↥K]`; `Nat.card 𝓀[↥K] = 2 ^ FF.f` | bridge, `UnitFiltrationCounts.residueField_card_eq_pow_f` |
| `galKEquiv`, `abEquivK`, `abEquivK_toAbK`, `abEquivK_symm_mk`, `coe_galKEquiv_symm_absGalEquivFixing` | `GalKab K ≃ₜ* Field.absoluteGaloisGroupAbelianization ↥K` and its values | A1 `absGalEquivFixing`, Tau Ceti `topologicalAbelianizationCongr` |
| `compactSpace_galK`, `compactSpace_galKab` (theorems, not instances) | compactness on gq2's instance path | A1 `compactSpace_fixingSubgroup` |

The `↥E`-level bridge (`normValuationE`, `isEquiv_normValuationE`) is specific to `ki_unramified`
and can stay in `B5K.lean`.

## Recommended order for B5-K's clauses

1. A1-K first (above). Every clause uses the bridge or `abEquivK`.
2. `recip`, `denseRange_recip`, `nu_ur`, `continuous_nu_ur`, and `nuUrK_recipK` (`ν(rec x) = −v_K(x)`).
3. `nu_ur_recip_unit`, `nu_ur_recip_uniformizer` (bridge corollaries).
4. `continuous_recip` (needs `localTopology_eq`).
5. `norm_compat` (`artinMap_norm`).
6. `r`, `nu_ker_chi_le`, `nu_ker_chi_ge`. The witness needs `norm_compat` and step 2.
7. `ki_unramified`, last and independent of steps 5 and 6. It needs only `nuUrK`, `abEquivK`, the
   bridge and A1's B9 layer lemmas.

After that comes B10-K. It uses `recipK` (with the exported equation `markedRecipAt_tauceti_recip`),
the bridge and Q3. Then C1' writes the two same-name `def`s in `TauCetiInstance.lean`.

# EV-4b — the stage machinery abstracted over (word, rank, rows)

W50-EVSTAGE deliverable. Status: **implemented and pinned** — the generic layer compiles
sorry-free at std-3, and the committed odd-degree endpoints are re-derived through it with
byte-identical statements and *equal* axiom prints.

New files:

* `GQ2/Dyadic/Instances/StageAbstraction.lean` — the generic layer
  (namespace `GQ2.Dyadic.StageGeneric`).
* `GQ2/Dyadic/Instances/StageAbstractionLSq.lean` — the L instantiation and the
  definitional pins.

Neither file is (or needs to be) imported by any committed file; the committed L route is
untouched. Wiring for the root is two lines (§6).

## 1. The survey: what the L stage chain consumes, declaration by declaration

The forward chain, in dependency order (all under `GQ2/Dyadic/Instances/`):

| station | file | endpoint |
|---|---|---|
| core/word | `../SqCore/Cores.lean` | `sqWord`, `sqRelWord`, `map_sqRelWord`, `DSq`, `sqGen` |
| model + tables | `GammaLSylowPreimageFieldCore.lean` | `SqCyclotomicForwardGeneratorData`, `OddDegreeGalKSqCyclotomicCoreTable`, `dsqFinsetTopGen` |
| finite levels | `GammaLSylowPreimageFieldLabuteFinite.lean` | `SqCyclotomicFiniteLevelEpiData`, `finiteLevelEpiDataOfTuple`, `forwardGeneratorData_of_finiteLevel` |
| stage machinery | `GammaLSylowPreimageFieldLabuteStage.lean` | `SqCyclotomicStageTuple`, defect calculus, corrections, `toNext`, `stage_nonempty_all_levels`, `finiteLevelEpiData_nonempty_of_base_and_corrections` |
| seed | `GammaLSylowPreimageFieldLabuteLevelThreeSeed.lean` | `SqCyclotomicFrattiniFrame`, `IsCupAdapted`, `toLevelThree`, the two finite supplies |
| frame supply | `GammaLSylowPreimageFieldLabuteFrattiniFrame.lean` | `oddDegreeSqCyclotomicFrattiniFrameSupply_holds` |
| transgression | `GammaLSylowPreimageFieldLabuteLevelThreeTransgression.lean` | `oddDegreeSqLevelThreeRelationRealization` (`gram_vanishes`) |
| level-3 base | `GammaLSylowPreimageFieldLabuteLevelThreeBase.lean` | `oddDegree_sqCyclotomicStageTuple_levelThree` |
| stage climb | `…VariableStageTwo/KernelAdaptedSupply/RawSpan(Step)/BracketSpan/StageHandles/StageRankOne.lean` | `SqKernelAdaptedDefectSupply` ⟹ per-stage `DefectReachable` |
| rigidity | `GammaLSylowPreimageFieldRigidity.lean`, `…VariableCoreRigidity.lean` | `nonempty_orientedEquiv_oddDegree_of_stageBase_and_primitiveResidualVanishing`, `OddDegreeGalKSqForwardGeneratorSupply` |

**Headline of the survey.** Of the stage machinery proper
(`LabuteStage.lean`, 1297 lines + the seed's structural half, 213 lines), everything is
word-generic except exactly three kinds of appearance of the L data:

1. **the word itself** — every occurrence of `SqCore.sqRelWord` enters only through
   (a) evaluation, (b) naturality `map_sqRelWord`, and (c) central exponent-two shift
   invariance `sqRelWord_zLayer_shift`. No other property of the word is consumed —
   in particular the stage layer never inspects the exponents or the commutator pattern;
2. **the rank/row structure** — `Fin (SqCore.sqRank h)` indexing plus the five fibre
   fields (`sigma`/`x0`/`x1` pinned at `SvalUnit`/`rootXUnit`/`YvalUnit`, `handleU`/`handleV`
   in `ker χ`). These five fields are exactly a value table
   `Fin (sqRank h) → ℤ₂ˣ` (kernel rows = value `1`); the committed
   `frattiniFrameTarget h` (FrattiniFrame.lean:673) *is* that table;
3. **the arithmetic instantiations** — `oddDegreeGalKSq_sharpCharacterFiltrationExact` and
   `oddDegreeGalKSq_sharpExactLevelFibreLiftSupply` consume `chiCycKTwo` **surjectivity**
   (odd degree only); the seed's `IsCupAdapted` consumes the word's **quadratic-initial
   Gram** `sqRelatorQuadraticInitialGram h`; the frame supply consumes the mod-4/mod-8/mod-16
   cyclotomic bridge tables.

Already word-generic in the committed file, reused rather than re-proved:
`handleWord_central_shift`, `mem_lambdaImage_succ_of_levelProj_mem`, the whole
`sharpChiLevel` calculus (`sharpChiLevel`, `sharpChiLevel_cast_eq_chiLevel`,
`sharpChiLevel_levelProj_eq_chiLevel_succ`, `SharpUnitsFiltrationExact` and
`sharpUnitsFiltrationExact`, `SharpCharacterFiltrationExact`,
`SharpExactLevelFibreLiftSupply`, the fresh-digit regressions), and the entire Labute tower
(`levelQuot`/`levelMk`/`levelProj`/`canonLift`/`zLayer`/`lambdaImage`,
`eq_top_of_map_levelProj_eq_top`, `closure_range_mul_eq_top_of_mem_lambdaImage_two`,
`exists_twoCentralSeries_le`, `discreteTopology_levelQuot`).

Word-specific and **left in place** (not abstracted, correctly so):
`stageShift_zero_eq_dbarWordR2` (the rank-3 crossed-derivation comparison used to reuse
`stageSL1R2`), the `ofCoreTable` constructors, the `OddDegreeGalKSqCyclotomicCoreTable`
witnesses, and everything in the frame-supply/transgression/climb stations below the two
finite supplies.

## 2. The abstraction, as implemented

`StageAbstraction.lean`, namespace `GQ2.Dyadic.StageGeneric`. Ambient data throughout:
an arbitrary `G : Type` (topological group; compact/T2/totally-disconnected where descent
needs it) with `chi : ContinuousMonoidHom G ℤ_[2]ˣ` — **no `GalK` anywhere**, so the layer
serves the field side and the model side alike.

* `StageWord n` — the word datum: `word` (rank-`n` shape in any group), `map_word`
  (naturality), `zshift` (central exponent-two shift invariance).
  `zshift_of_core_handles` derives `zshift` for any word of the campaign's
  core-plus-handles shape from the core case alone (handles die by the committed
  `handleWord_central_shift`), so an even ticket proves only a four-letter computation.
* Defect calculus: `stageZero`, `stageZero_levelProj`, `stageDefect`,
  `stageDefect_eq_of_lift`, `stageDefect_mem_zLayer`, `stageZero_defect_mem_zLayer`,
  `stageDefect_eq_one_iff_lift_relation`, `stageModified`, `stageShift`,
  `word_stageModified`, `rawDefectReachable`.
* `Tuple W v G chi k` — the `SqCyclotomicStageTuple` clone with the five fibre fields
  replaced by one uniform row field over the table `v : Fin n → ℤ₂ˣ`; `levelProj`,
  `generators_mem_stageZero`.
* Open-quotient descent: `openMap` (+`_levelMk`, `_surjective`), `OpenTuple` (the
  model-independent content of `SqCyclotomicFiniteLevelEpiData`), `Tuple.toOpenTuple`
  (+ relation/rows regressions).
* Corrections: `AdmissibleCorrection`, `TruncatedAdmissibleCorrection`,
  `SharpAdmissibleCorrection` (+`toTruncated`, `toAdmissible`),
  `FreshDigitStrictificationSupply`, `DefectReachable`, `TruncatedDefectReachable`
  (+`toDefectReachable`), `DefectReachable.toRaw`, `ExactFibreStrictification`
  (+`of_raw_of_exactFibreStrictification`), `ActualDefectSpanSupply`,
  `CorrectionSurjective`, `CrossedDerivationSpanSupply` (+ all committed adapters),
  `DefectKillingCorrection` (+`toNext`), `DefectReachable.toNext`,
  `CorrectionSurjective.toNext`.
* Induction/endgame: `stage_nonempty_all_levels`,
  `openTuple_nonempty_of_base_and_corrections`.
* Model transport (regression seam): `ofModel`, `ofModel_defectReachable` — the
  `ofOrientedEquiv` clones over an abstract marked model `(D, gen, relation, topGen,
  IsTopologicallyFinGen D, chiD, rows, e : D ≃ G, chi∘e = chiD)`.
* Seed: `Frame` (the `SqCyclotomicFrattiniFrame` clone), `Frame.LevelThreeRelation`,
  `Frame.IsCupAdapted`, `Frame.toLevelThree` (+ regressions).

### 2.1 Two deviations from the standing (word, rank, rows) recommendation

Both were forced by the survey; the recommendation is otherwise validated.

**(a) The seed layer also consumes the word's quadratic-initial Gram.** The committed
`IsCupAdapted` contracts `FieldData.cupFormK` against `sqRelatorQuadraticInitialGram h`.
The Gram is data *of the word* (its degree-two initial form), not of the rows, so
`Frame.IsCupAdapted` takes a `gram : (Fin n → Fin n → ZMod 2) → ZMod 2` parameter and an
abstract character pairing `P` (for L: the cup form through `characterClass`; pinned
`Iff.rfl` in the LSq file). The even instantiation must supply the even Gram — see the
EV-3c/d cruxes.

**(b) Sharp exact lifting must be row-target-relative.** The committed
`SharpExactLevelFibreLiftSupply G chi` demands an exact lift at **every** target of
`ℤ₂ˣ`. That is provable only when `chi` is surjective (`…of_surjective` +
`sharpUnitsFiltrationExact`) — true at odd degree, **false at even degree**, where
`im(chiCycKTwo)` is a proper subgroup. The survey shows the machinery only ever lifts at
the row values, so the abstraction demands only `RowExactLevelFibreLiftSupply v G chi`
(lifting at the `v i`); `rowSupply_of_sharpSupply` recovers the odd-degree situation, and
EV-4a's image-relative filtration produces the even row supply directly. Without this
weakening the even lane could not instantiate the correction-upgrade seam at all.

The same surjectivity choke point recurs one station higher:
`stageResidual_exists_primitiveVanishing_of_kernelAdaptedSupply`
(VariableStageTwo.lean:87) consumes `Function.Surjective chiCycKTwo` for the sharp
core-row upgrade. That station is *not* part of EV-4b's layer; its even clone must be
row-relative in the same way (flagged in EV-3f).

### 2.2 Definitional recovery of the L instance (the pins)

`StageAbstractionLSq.lean`. The word datum `lSqWord h` has the committed constants as its
field *values* (`word := sqRelWord`, `map_word := map_sqRelWord`,
`zshift := sqRelWord_zLayer_shift`), which makes the generic definitions specialise
definitionally:

* `rfl` pins: `sqStageZero = stageZero (lSqWord h) G k`, `sqStageDefect = stageDefect …`,
  `stageModified`, `stageShift`, `sqRawDefectReachable`; `LevelThreeRelation` and
  `IsCupAdapted` are `Iff.rfl` through `frameOfSq`.
* Converters (generators/relation/topGen transfer **unchanged**; only the five fibre
  fields are re-indexed through `sqIndex_cases` + the `frattiniFrameTarget` simp lemmas):
  `ofSq`/`toSq` (tuples), `admissibleOfSq` + `defectReachable_ofSq` (the correction
  interface), `openTupleToEpiData` (through the committed `finiteLevelEpiDataOfTuple`),
  `frameOfSq` (frames).
* Endpoint pins, statements byte-identical to the committed theorems, axiom prints
  **equal** to the committed originals (verified side-by-side in the file's output):

| pin | committed original | print |
|---|---|---|
| `pin_stage_nonempty_all_levels` | `SqCyclotomicStageTuple.stage_nonempty_all_levels` | std-3 = std-3 |
| `pin_finiteLevelEpiData_nonempty_of_base_and_corrections` | `…finiteLevelEpiData_nonempty_of_base_and_corrections` | std-3 = std-3 |
| `pin_oddDegree_sqCyclotomicStageTuple_levelThree_of_finiteRealization` | `oddDegree_sqCyclotomicStageTuple_levelThree_of_finiteRealization` | std-3 + {`tateDualityAt`, `absGalQ2_isTopologicallyFinitelyGenerated`} = same |
| `pin_oddDegree_sqCyclotomicStageTuple_levelThree` | `oddDegree_sqCyclotomicStageTuple_levelThree` | std-3 + {`hilbertSymbol_normCriterion_finiteDyadic`, `tateDualityAt`, `absGalQ2_isTopologicallyFinitelyGenerated`, `absGalQ2_localEulerCharacteristic`} = same |

The L pin set deliberately stops at the `DefectReachable` seam: the committed
truncated/sharp L machinery keeps its own instances (converting the *quantified* L
supplies through the abstraction would buy nothing), while the even lane uses the generic
truncated/sharp layer directly. `DefectReachable` is the narrow waist through which the
induction consumes all correction arithmetic, and that seam is pinned.

A regression example re-derives the committed `sqRelWord_zLayer_shift` through
`zshift_of_core_handles` at the L core, confirming the even route through the four-letter
core case is the same mechanism.

## 3. What the even clone still needs (input inventory)

With EV-4b in place, an even-core forward route needs, per core (`nRelWord α`/DN and
`mRelWord α`/DM), exactly:

1. a `StageWord (coreRank h)` instance (mechanical; §4 EV-3a);
2. a row table `Fin (coreRank h) → ℤ₂ˣ` matching the frozen constructor tables of
   `chiN`/`chiM` — N: `(x₀,x₁,σ,x₂) ↦ (1, nUnit α, 1, 1)`, M: `(A,B,C₀,D) ↦
   (1, −1, 1, mUnit α)`, handles `1` (`MarkedCore/Cores.lean:1072–1105`,
   `EvenForwardRouteSkeleton.lean:104/128`) (§4 EV-3b);
3. the even frame supply and transgression realization (the two finite supplies; §4
   EV-3c/d) feeding `Frame.toLevelThree` (§4 EV-3e);
4. per-stage `DefectReachable` at `k ≥ 3` (the climb; §4 EV-3f, with EV-4a as input);
5. the model-side compactness/limit station from `OpenTuple` to
   `EvenDegreeGalK{N,M}ForwardGeneratorSupply` (§4 EV-3g);

after which `EvenForwardRouteSkeleton.lean` already carries the rigidity endgame
(`orientedEquivN_of_supplies`/`orientedEquivM_of_supplies`, no `demushkinQ`, no image
identification, orientation free).

## 4. EV-3 decomposed into Opus-sized tickets

Sizes are relative to the committed L templates (line counts given). Dependencies:
a → b means b consumes a. `EV-3a → EV-3b → {EV-3c,d,f,g}`, `EV-3c,d → EV-3e`,
`EV-4a → EV-3f`, `EV-3e,f,g → EV-3h`.

**EV-3a — even word data.** New file `Instances/StageAbstractionEvenWords.lean`.
`nStageWord α h, mStageWord α h : StageWord (MarkedCore.coreRank h)` with
`word := nRelWord α / mRelWord α`, `map_word := map_nRelWord/map_mRelWord`
(`MarkedCore/Cores.lean:203/208`), and `zshift` through
`StageGeneric.zshift_of_core_handles` at `c = 4` — the only proof obligation is the core
case `nWord α (z·m…) = nWord α (m…)` for `z ∈ Z_k` (and mWord's), which is
`commP`-central-kill plus `z^even = 1` (`zLayer_inv_self`); **requires `1 ≤ α`** so all
core exponents are even (the even lane assumes `α ≥ 2` anyway). Template: `lSqWord` +
the `zshift_of_core_handles` regression example in `StageAbstractionLSq.lean`. Size: S
(≤ 150 lines).

**EV-3b — even row tables, index eliminator, model data.** Same or adjacent file.
`vN α : Fin (coreRank h) → ℤ₂ˣ` and `vM α` per §3.2; `evenIndex_cases` (clone of
`sqIndex_cases`; needs the `coreRank` alphabet equiv — clone `sqInitialAlphabetEquiv`
from `Count/H3SqRowInitialForms.lean:42` at 4 core letters, or index arithmetic);
`Tuple.ofModel` instances for DN/DM from `dn_relation`/`dm_relation`, `dnGen` topological
generation (clone `dsqFinsetTopGen`, `FieldCore.lean:99`), and the `chiN`/`chiM` row
lemmas (`chiN_dnX0…chiN_handleV`, all committed simp lemmas). Deliverable: for any
oriented equivalence `e : DN α h ≃ G` with `chi∘e = chiN`, generic stages at every level
with reachable defects (`ofModel_defectReachable`) — the even h=0-style regression seam.
Size: M (≈ 250 lines).

**EV-3c — even Frattini frame supply (the arithmetic head).** Clone of
`FrattiniFrame.lean` (1068 lines) producing
`Frame (vN α) (maxProPQuotient 2 (GalK K)) chiCycKTwo` (and M-analogue) plus
`IsCupAdapted` at the even Gram, for `[K:ℚ₂] = 2 + 2h` with `K(i)/K` ramified. **Marked
cruxes**: (i) the even head `[[1,1],[1,0]]` has no dual-basis *permutation* — its inverse
Gram is `[[0,1],[1,1]]`, so the odd `sqInitialPartner : Equiv.Perm` must become a
dual-*vector* map (recorded in `EvenForwardRouteSkeleton.lean:48–51`); (ii) the
S≡13, X≡5, Y≡7 mod 16 table matching `(−1,−1)_K = −1, (2,−1)_K = 1` is the odd-word
table — the even-word analogue (values `1, nUnit α, 1, 1` resp. `1, −1, 1, mUnit α`)
needs its own mod-16 bridge table, a real mathematical checkpoint, not plumbing;
(iii) rows must lie in `im(chiCycKTwo)` — for M the `−1` row is exactly the
`−1 ∈ im χ` branch condition. Likely split c1 (N-row) / c2 (M-row). Size: XL — this and
EV-3f are the mathematical content of EV-3.

**EV-3d — even transgression realization.** Clone of `LevelThreeTransgression.lean`
(662 lines): cup-adapted even frame ⟹ `Frame.LevelThreeRelation (nStageWord α h)`.
`handleWord_mul_central` and the `gram_zero/add/sum` scaffolding transfer; the
word-specific pieces are `nWord/mWord_mul_central` (clone `sqWord_mul_central`, :98) and
`nRelWord_mem_twoCentralSeries_two` (clone :162 — uses `2 | exponents`, needs `α ≥ 1`),
then `gram_vanishes` against the even Gram. Size: L.

**EV-3e — even level-three base.** Compose EV-3c + EV-3d through
`Frame.toLevelThree` (hfg := the even-degree `maxProTwoGalK` fin-gen, hpro :=
`isProP_maxProPQuotient`): `Nonempty (Tuple (nStageWord α h) (vN α) … 3)` for every even
`K` at `h = ([K:ℚ₂] − 2)/2`. Mirror of `LevelThreeSeed` supplies + `LevelThreeBase`
(47 lines). Size: S. Statement shape (final): the even analogues of
`OddDegreeSqCyclotomicFrattiniFrameSupply` / `…RelationRealization`, quantified over
`Module.finrank ℚ_[2] K = 2 + 2*h` and carrying the caller's `MarkedRecip` bundle binder
exactly as the odd ones do (no axiom growth at endpoints).

**EV-3f — even stage climb (`DefectReachable` at every `k ≥ 3`).** Clone of the
RawSpan/RawSpanStep/BracketSpan/StageHandles/StageRankOne/KernelAdaptedSupply/
VariableStageTwo chain (≈ 4100 lines — the largest station; split per file). Produces
`∀ k ≥ 3, ∀ T : Tuple (nStageWord α h) …, Tuple.DefectReachable T`. **Marked cruxes**:
(i) the SL1 crossed-derivation calculus at the 4-letter core — the even analogue of
`stageShift_zero_eq_dbarWordR2` needs its own `dbarWord` comparison (the even relator's
linearisation differs: `ρ_N = (2+2^α)x̄₀`, `ρ_M = 2Ā + 2^αC̄₀`); (ii) the sharp core-row
upgrade must be **row-relative** (§2.1(b)) — clone
`stageResidual_exists_primitiveVanishing_of_kernelAdaptedSupply` replacing
`Function.Surjective chiCycKTwo` by the EV-4a row supply; (iii) the generic
truncated/sharp correction layer of `StageAbstraction.lean` is used *directly* (no even
re-derivation). Size: XL, decompose further at execution time (per L template file).

**EV-3g — even finite-level compactness + forward supply.** Clone of
`LabuteFinite.lean`'s model half (678–830 for the `OpenTuple → EpiData` adapter via
`nLiftHom`/`mLiftHom`, then 276–430 for the inverse-limit argument): even
`FiniteLevelEpiData` structures on `DN/DM`, cofiltered functor + `Finite` instances,
`evenForwardGeneratorData_of_finiteLevel` concluding
`Nonempty (NForwardGeneratorData α h chiCycKTwo)` — i.e.
`EvenDegreeGalKNForwardGeneratorSupply α` (`EvenForwardRouteSkeleton.lean:415`), and the
M twin. Note the two `mem_closed*_of_finiteQuotient_approximations` helpers are
`private` in the committed file and must be restated (identical proofs). Size: L,
mechanical.

**EV-4a — image-relative sharp filtration (input to EV-3f, separate lane).** The
even-degree replacement for `oddDegreeGalKSq_sharpCharacterFiltrationExact`: identify
`χ(λ_n(G_K(2)))` relative to `im χ` (the committed `SharpCharacterFiltrationExact` is
false verbatim — `EvenForwardRouteSkeleton.lean:63–65` already records "NOT via
`of_surjective`"), and produce `RowExactLevelFibreLiftSupply (vN α)` /
`…(vM α)` — lifting is only needed at the four core values and `1`, all in `im χ` by
construction. The abstraction consumes nothing stronger (§2.1(b)). Size: L, genuinely
arithmetic.

**EV-3h — assembly.** `EvenDegreeGalK{N,M}ForwardGeneratorSupply α` from e+f+g, then the
committed `orientedEquiv{N,M}_of_supplies` close the route (their remaining model-side
premise `NModelDemushkin`/`MModelDemushkin` is EV-1e, a *different* lane). Size: S.

**Standing notes for all tickets.**

* **Parallel dependency**: `demushkinQ (DM α h) = 2` at general `h` is being built by the
  w50-mframe agent from the N-side template. It is **not** on the EV-3 critical path (the
  forward route consumes no `demushkinQ` — skeleton header, lines 20–28); it feeds the
  model-side Demushkin package (EV-1e). Cite it as an assumed input where it appears; do
  not rebuild it.
* **α = 1 is out of scope**: at `α = 1` the N relator exponent `2 + 2 = 4` kills the
  mod-2 quadratic initial form and the core is not Demushkin; the even lane assumes
  `α ≥ 2`. (EV-3a/d only need `α ≥ 1`, but state them at the lane's `α ≥ 2` if that
  simplifies.)
* **q = 4 Arf sign**: confined to the even *determinant* residues
  (`owner-items-2026-08-05.md` §1, narrowed 2026-08-06) — not in the forward lane; no
  EV-3 ticket touches it.
* The frozen word hashes are untouched: the abstraction never redefines a word — the even
  instances' `word` fields are the committed `nRelWord α`/`mRelWord α` constants, exactly
  as `lSqWord` wraps `sqRelWord`.

## 5. Verification record

* `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true`
  green on both files; the LSq file checked against a full symlink mirror of the shared
  olean tree with the new `StageAbstraction.olean` swapped in.
* All 28 printed generic declarations at std-3 (`[propext, Classical.choice, Quot.sound]`).
* All 8 LSq converters at std-3; all 4 endpoint pins with prints **equal** to their
  committed originals (§2.2 table).
* Collision test: scratch `import GQ2` + both new modules, `#check` on all 80+ new public
  names — clean.

## 6. Wiring for the orchestrator

Append to `GQ2.lean` (after the `GammaLSylowPreimageFieldLabuteDegreeThree` import, order
immaterial — both files import only committed modules):

```
import GQ2.Dyadic.Instances.StageAbstraction
import GQ2.Dyadic.Instances.StageAbstractionLSq
```

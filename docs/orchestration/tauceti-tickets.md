# Tau Ceti discharge ticket board

Plan: [`tauceti-proof-plan.md`](tauceti-proof-plan.md). Branch `tauceti`, worktree
`~/claude/gq2-tauceti` (recon tickets run read-only against the main checkout and
`~/claude/tauceti-main`). Model column = subagent tier (fable = design/hard seams, opus =
well-specified fills). One ticket = one agent dispatch; each commits on green with
`tauceti <id>: <summary>`.

**Board protocol (from `roe-tickets.md`): workers never edit this file.** The orchestrator alone
updates rows. Workers end with a report: files, commit hash, sorry/axiom state, deviations, and
discoveries affecting later tickets. Every adapter file is `module`-style, never `open TauCeti`
at top level, and declares the gq2 field with its type byte-identical to the corresponding field
of `GQ2.LiteratureInputs`.

Acceptance for every B-ticket: `GQ2/TauCeti/<id>.lean` builds with zero sorries, imports
nothing from `GQ2/Foundations/Axioms.lean` or `AxiomInstance.lean`, and
`#print axioms` of its main declaration is the standard three.

## Wave 0: platform (sequential)

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| G0 | owner gate: accept Tau Ceti in the trust base, approve the pin | owner | — | — | approved 2026-10-16 |
| T0 | worktree, pins, caches | opus | `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `.github/workflows/ci.yml` | G0 | done `90bea281` |
| T1 | Mathlib bump `ec410d23d` → `cfc55fc58` (`v4.31.0-rc2` → `v4.35.0`) | fable | all of `GQ2/`, `Challenge*.lean`, `Solution*.lean`, `GQ2.lean` | T0 | done `d40bfb1f`…`84e08795` |
| T2 | Tau Ceti smoke import and dictionary recon memo | opus | `GQ2/TauCeti/Smoke.lean`, `docs/orchestration/tauceti-t2-recon.md` | T1 | done `79bca060` |

## Wave 1: shared dictionaries (parallel)

The T2 memo ([`tauceti-t2-recon.md`](tauceti-t2-recon.md), "Corrections to the plan and board")
revises the Wave 2 dependencies: B1 and B5 need no dictionary, B10 needs only B5, B3c is
self-contained, B9 does not need B11a. Prototypes for most lanes are in
[`tauceti-t2-evidence/`](tauceti-t2-evidence/README.md). The dependency column below is unchanged
until the orchestrator re-plans Wave 2.

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| A1 | Galois-group dictionary | fable | `GQ2/TauCeti/GaloisDict.lean` | T2 | done `90c2284c` |
| A2 | cohomology, cup and Kummer dictionary | fable | `GQ2/TauCeti/CohomologyDict.lean` | T2 | in progress |
| P1 | pro-p, free, presentation, `ℤ̂` dictionary | fable | `GQ2/TauCeti/ProPDict.lean` | T2 | done `3b488710` |

## Wave 2: the nine inputs (parallel within the dependency order)

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| B1 | topological finite generation | opus | `GQ2/TauCeti/B1.lean` | A1 | done `a5ccd575` |
| B11a | Hilbert-symbol norm criterion | opus | `GQ2/TauCeti/B11a.lean` | A1, A2 | open |
| B7 | local Euler characteristic | fable | `GQ2/TauCeti/B7.lean` | A2 | open |
| B5 | local reciprocity bundle | fable | `GQ2/TauCeti/B5.lean` | A1 | done `a395ed6b`, `8a6d969b` |
| B8 | peripheral cyclotomic action | fable | `GQ2/TauCeti/B8.lean` | P1 | done `6f68cfe3` |
| B9 | relative Stiefel-Whitney identity | fable | `GQ2/TauCeti/B9.lean`, `GQ2/TauCeti/StiefelWhitneyDict.lean` | A1, A2 | open |
| B6 | local Tate duality at finite `k/ℚ₂` | fable | `GQ2/TauCeti/B6.lean`, `GQ2/TauCeti/DualizingGroup.lean` | A1, A2 | open |
| B10 | oriented tame quotient | fable | `GQ2/TauCeti/B10.lean` | B5, P1 | done `a2c2b6ea` |
| B3c | dyadic orientation | fable | `GQ2/TauCeti/B3c.lean` | P1, A1 | done `b80367b3` (private copies of P1 pieces; dedupe after Wave 2) |

## Wave 3: assembly, flip, docs (sequential)

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| C1 | instance, four capstones, audit, CI | opus | `GQ2/TauCeti/Instance.lean`, `GQ2/TauCeti/Main.lean`, `GQ2/TauCetiAxiomAudit.lean`, `scripts/check_axioms.sh`, `.github/workflows/ci.yml`, `GQ2.lean` | all B | open |
| G1 | owner gate: census flip 9 → 0 | owner | — | C1 | open |
| C2 | delete the axiom file; same-name wrappers | fable | `GQ2/Foundations/Axioms.lean` (delete), `GQ2/Foundations/AxiomInstance.lean` (delete), `GQ2/Foundations/Interfaces.lean`, `GQ2/AxiomLedger.lean`, `scripts/check_axioms.sh`, `comparator-config*.json` | G1 | open |
| C3 | docs sweep | opus | `formalization.yaml`, `README.md`, `docs/literature-axioms.md`, `docs/literature-axioms-onepage.md`, `docs/README.md`, `docs/orchestration/README.md` | C2 | open |
| G2 | owner gate: keep or retire the legacy `Challenge`/`Solution` pair | owner | — | C3 | open |

## Ticket briefs

**T0 (opus).** Create `~/claude/gq2-tauceti` with `git worktree add -b tauceti`. Set
`lean-toolchain` to `leanprover/lean4:v4.35.0`. In `lakefile.toml` add
`[[require]] name = "TauCeti" git = "https://github.com/TauCetiProject/TauCeti" rev = "706344c354…"`
(full SHA) before the Mathlib require, and pin Mathlib's `rev` to
`cfc55fc58714a59dc06e6e79edc6d1d95140d3c2`. Check whether the `lean-atlas` dev dependency has a
commit building under `v4.35.0`; if not, drop the require and note it (it is not imported by
`GQ2`). `lake update`, then `lake exe cache get`, then the Tau Ceti cache fetch of plan §2 (write
the `LAKE_CONFIG` toml into the worktree's `.lake/`, not the repository). Report free disk before
and after. Add the Tau Ceti cache step to `ci.yml` after the Mathlib cache step, copied from
`~/claude/tauceti-lgg-tate-module/.github/workflows/ci.yml` lines 56-110 with the public
endpoints hard-coded. Do not attempt to build `GQ2` yet.

**T1 (fable).** Run `/bump-mathlib` in the worktree. Rules: every theorem statement in `GQ2/`
byte-identical (the Γ_A/Γ_R twin audit and the Comparator pairs depend on it); fix proofs and
renamed Mathlib declarations only; commit per green batch of files, path-limited. Done when
`lake build GQ2 Challenge Solution ChallengePalomar SolutionPalomar` is green,
`scripts/check_axioms.sh` passes at census 9, and `lake env lean GQ2/AxiomLedger.lean` and
`lake env lean GQ2/PalomarAxiomAudit.lean` pass. Report the list of Mathlib renames met, for
later tickets.

**T2 (opus, read-only except the two owned files).** Write `GQ2/TauCeti/Smoke.lean` importing the
modules that hold every declaration named in plan §3 and `#check`ing each by its full name
(this pins the names at the chosen revision). For each lane, record in
`tauceti-t2-recon.md`: the exact signature of each Tau Ceti source, the instance arguments it
needs at `K = ℚ_[2]` or at a finite `k`, and the gq2 field it must become. Specifically answer:
(1) is `GQ2.FreeProfiniteGroup X` definitionally `TauCeti.freeProfiniteGroup X`; (2) do the two
`proPKernel` definitions agree; (3) does `Perfect.lean` state bijectivity, or only two-sided
nondegeneracy; (4) which lemma turns an open finite-index subgroup of `Field.absoluteGaloisGroup K`
into `K'.fixingSubgroup` for a finite `K'`; (5) which `D0/Invariants.lean` theorems give the
values of `standardD0Orientation` on `d0A`, `d0S`, `d0Y`; (6) which `ZHat/Decomposition.lean`
declaration is the `ℤ₂`-component and its section.

**A1 (fable).** In `GaloisDict.lean`: for a finite `k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])`
provide the local-field instance package on `↥k` (`finiteIntermediateFieldValuativeRel`,
`finiteIntermediateFieldTopology`, `IsNonarchimedeanLocalField`, `FinitePadicExtension`), a
`ContinuousMulEquiv` `k.fixingSubgroup ≃ₜ* Field.absoluteGaloisGroup ↥k` and its composite with
`absoluteGaloisGroupRestrictEquiv`, and `chiCyc_eq_localCyclotomicCharacter : GQ2.chiCyc g = localCyclotomicCharacter 2 ℚ_[2] g`
(both are the cyclotomic character of `ℚ̄₂ ≃ₐ[ℚ₂] ℚ̄₂`; Tau Ceti's goes through the separable
closure). Also the stabilizer of `δ` against `galoisSubgroup k (quadExt k δ) σ` for the B9 lane.

**A2 (fable).** In `CohomologyDict.lean`: `AddEquiv`s `GQ2.ContCoh.Hi G M ≃+ TauCeti.ContCohomology.Hi G M`
for `i = 0, 1, 2` (expected by unfolding), composed with
`explicitH{1,2}AddEquivContinuousCohomology` to `continuousCohomology i A` for the `TopRep`
built from `M`; naturality for restriction (`res1/res2` vs `explicitRes1/2`) and coefficient maps;
cup compatibility `cup11/cup02/cup20` and `trivialCupPairing` against `(trivialF2TopPairing G).cup`;
`kummerClassK k a ↦ TauCeti.kummerClass a` under the A1 equivalence. State each as a `simp`-usable
equation.

**P1 (fable).** In `ProPDict.lean`: `GQ2.IsProP p G ↔ TauCeti.IsProP p G` (`Iff.rfl` if the
definitions match); `GQ2.maxProPQuotient p G ≃ₜ* TauCeti.maximalProPQuotient p G` commuting with
the two `mk`s; `GQ2.FreeProfiniteGroup X ≃ₜ* TauCeti.freeProfiniteGroup X` carrying `of` to
`of`; `GQ2.profinitePresentation rels ≃ₜ* presentedProfiniteGroup X rels'` and the pro-p
variant against `presentedProP`; `GQ2.Zhat ≃ₜ* TauCeti.zHat` carrying `Zhat.ofInt` to
`zHat.ofInt`, with `zhatProjTwo` against the `ℤ₂`-component; `zpowZtwo hP x u = (P1-transported hP).padicPow x u`
by the finite-quotient characterization on both sides. These feed B3c, B8, B10.

**B1 (opus).** `theorem absGalQ2_isTopologicallyFinitelyGenerated_tauceti : ∃ s : Finset AbsGalQ2, (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤`
from `TauCeti.isTopologicallyFinitelyGenerated_absoluteGaloisGroup 2 ℚ_[2]`.

**B11a (opus).** `theorem hilbertSymbol_normCriterion_finiteDyadic_tauceti` with the B11a field
type, from `TauCeti.cup_kummerClass_eq_zero_iff` over `↥k`, through A1 and A2. This ticket is the
first full exercise of the dictionaries; report any A1/A2 lemma that is missing or wrongly shaped
so the orchestrator can reopen those tickets before B9 and B6 start.

**B7 (fable).** `theorem absGalQ2_localEulerCharacteristic_tauceti (M : Type) … : Finite (H0 …) ∧ … = … * 2 ^ padicValNat 2 (Nat.card M)`
from `TauCeti.ClassFieldTheory.eulerCharacteristic_mixed 2 (Nat.card M) _ A _` with
`A : GalRep (Nat.card M) ℚ_[2]` built from `M` (torsion by Lagrange, `IsSmoothDiscrete` from
open stabilizers), `Module.finrank ℚ_[2] ℚ_[2] = 1`, finiteness from `finite_H`, cardinalities
transported by A2.

**B5 (fable).** `noncomputable def localReciprocity_tauceti : LocalReciprocity` with
`recip := TauCeti.ClassFieldTheory.artinMap ℚ_[2]`, continuity and density from
`continuous_artinMap`, `denseRange_artinMap`; `nu_ur` the inverse of the `ℤ₂`-reduction of
`unramifiedCoordinate ℚ_[2]` (use P1's `zHat` component), `nu_ur_recip` from
`unramifiedCoordinate_artinMap` and `normalizedValuation` vs `GQ2.v2`; `chiCyc_recip_unit` from
`localCyclotomicCharacter_artinMap_unit` at `K = ℚ_[2]` with A1's character identification and
`Algebra.norm ℚ_[2] = id`; `chiCyc_recip_uniformizer` from
`localCyclotomicCharacter_artinMap_padic_uniformizer`; `norm_reciprocity` from the finite local
reciprocity `localArtinEquiv` and the formation's `ker_artinMap`, with gq2's `restrictAb L hab`
and `normSubgroup L` matched to Tau Ceti's layer restriction and `normGroup`. Do
`norm_reciprocity` last and report its seam if it does not close.

**B8 (fable).** `noncomputable def peripheralCyclotomicAction_tauceti : PeripheralCyclotomicAction`.
Build `e : Delta ≃ₜ* freeProP 2 (Fin 2)` from P1 and apply
`TauCeti.exists_peripheralPowerAutomorphism_two` for each `u`; `aut u` is the chosen `φ`
transported back; `cP u := 1`. Construct `ι u` as the element of `Zhat` with `ℤ₂`-component `u`
and trivial odd part, prove `hι_cont`, `hι_one`, `hι_proj`; then `x ^ᶻ ι u = zpowZtwo x u`
(`zpowHat_eq_zpowZtwo`) and P1's `zpowZtwo = padicPow` close `hP`, `hT`, `hC`.

**B9 (fable).** `theorem relativeStiefelWhitney_dyadic_tauceti` with the B9 field type. In
`StiefelWhitneyDict.lean`: `swOne k Q = sw1Class (formClass Q _)` and
`swTwo k htriv Q = sw2Class (formClass Q _)` (gq2's classes are defined on diagonalizations with
Delzant well-definedness proved; Tau Ceti's through `RegularFormClass.liftDiagonal`);
`traceFormTwisted k δ a = ((a • sq).traceTransfer k)` and `traceFormOne k δ = (sq.traceTransfer k)`
up to the module identification `↥(quadExt k δ) = L`; `corH1 … α … = galoisCor k L σ 1 (kummerClass a)`;
`evensNormH2 … = galoisEvens k L σ hdeg (kummerClass a)` via `evensNormIndexTwo_homClass` and
`graphClass`. Then `B9.lean` is `sw1Class_formClass_traceTransfer_smul_sq` and
`sw2Class_formClass_traceTransfer_smul_sq` rewritten through the dictionary; commutativity of
the cup in degree `(1,1)` over `𝔽₂` is `trivialF2TopPairing_cup_comm` if the summand order
differs.

**B6 (fable).** `noncomputable def tateDualityAt_tauceti (G …) (n) … (hloc) : TateDualityG G n`.
In `DualizingGroup.lean`: from `hloc` obtain a finite `K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])`
with `ι.range = K.fixingSubgroup` and `G ≃ₜ* Field.absoluteGaloisGroup ↥K` compatible with the
`MuN n` action (T2 item 4 names the lemma, or prove it from Mathlib's Galois correspondence for
open subgroups). Then `MuN n ≅ (muNRep n K).V` and `MuDual n M ≅ (tateDual A).V` for the `GalRep`
built from `M`; `inv := tr` from `h2MuEquivZMod_mixed`; `perfect02/11/20` from
`tateDualityPairing_perfect_mixed` plus finiteness (if T2 item 3 reports nondegeneracy only,
prove bijectivity by cardinality: an injective homomorphism between finite groups of equal order).
Report any lemma proved here that belongs upstream.

**B10 (fable).** `noncomputable def tameQuotient_tauceti : OrientedTameQuotient localReciprocity_tauceti`.
`W := wildInertiaSubgroup ℚ_[2]` with closedness, normality, `isProP_wildInertiaSubgroup` through
P1's `IsProP` identification; choose `σ` an arithmetic Frobenius lift and `τ` a tame generator
(`exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top`); `equiv` is
`tameQuotientGeometricEquiv hσ τ hτ` composed with P1's `IwasawaGroupGeometric ℚ_[2] ≃ₜ* Ttame`
(the relator matches once `Nat.card 𝓀[ℚ_[2]] = 2` is rewritten with `natCard_residueField`);
`nuT` against the `ℤ₂`-reduction of `iwasawaCoordinateGeometric` and `ztwoOne` against the
reduction of `zHat.gen`; the two orientation clauses from `unramifiedCoordinate_artinMap` and
`tameQuotientGeometricEquiv_toTameQuotient_frobenius`. Watch the direction: gq2's `tameSigma` is
geometric Frobenius and `rec 2` is arithmetic, which is why the uniformizer clause reads
`ztwoOne⁻¹`.

**B3c (fable).** `noncomputable def dyadicOrientation_tauceti [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] : DyadicOrientation`.
Obtain `e` from `TauCeti.absoluteGaloisGroupProP_two_ratPadic_marked`; `equiv` is P1's
`maxProPQuotient 2 AbsGalQ2 ≃ₜ* absoluteGaloisGroupProP 2 ℚ_[2]` followed by `e` and P1's
`demushkinD0 ≃ₜ* GQ2.D0` (generators to generators; check the commutator convention in the two
`d0Relator`s and insert the inverse if they differ); `chiTwo := cyclotomicOrientation 2 ℚ_[2] _`
transported, `chiTwo_factors` from `cyclotomicOrientation_mk` and A1's character identification,
`surjective_chiTwo` from the theorem's second conjunct, `chi_A/chi_S/chi_Y` from
`standardD0Orientation`'s values (T2 item 5) through the first conjunct.

**C1 (opus).** `Instance.lean`: `noncomputable def tauCetiInputs : LiteratureInputs := { … }`
from the nine adapters. `Main.lean` (plain imports): the four capstones listed in plan §4.
`GQ2/TauCetiAxiomAudit.lean` modelled on `PalomarAxiomAudit.lean`: imports only
`GQ2.TauCeti.Main`, asserts each capstone's axioms are exactly the standard three.
`check_axioms.sh`: a check 7 running that file, and the four names added to a new
`AUDIT_STD3_DECLS` list in check 5. `ci.yml`: build `GQ2.TauCeti.Main` and run the new audit.
Add the import lines to `GQ2.lean`. Census stays 9 in this ticket.

**C2 (fable, after G1).** Single atomic commit on `tauceti`, following the B9-A T5 checklist:
delete `GQ2/Foundations/Axioms.lean` and `AxiomInstance.lean`; in `Interfaces.lean` (or a new
`GQ2/Foundations/TauCetiInstance.lean`) define the nine legacy public names as same-name
theorems/defs equal to the adapters, with the statements byte-identical to the deleted axioms
(B7 keeps `M : Type*` by restating the adapter universe-polymorphically if the proof allows,
otherwise document the restriction); `instance : LiteratureInputs := tauCetiInputs`;
`EXPECTED_AXIOMS=0`, `AUDIT_EXPECTED_AXIOMS` = standard three, every `AUDIT_DECLS` entry and twin
pair now at the standard three; `AxiomLedger.lean` certificate empty; `comparator-config*.json`
axiom lists updated. Gates before merge: full build green, zero sorries, `check_axioms.sh`,
`AxiomLedger`, `PalomarAxiomAudit`, `TauCetiAxiomAudit` all pass.

**C3 (opus).** `formalization.yaml`: `status.scope` and `axioms`, `main_results` (the
unconditional capstones become the main entries, `literature_dependencies` → proved via Tau Ceti,
`fidelity.divergences` (i) rewritten, `acknowledgements` add Tau Ceti with its revision);
`README.md` result section; `docs/literature-axioms.md` and the one-page: each B-leaf gets its
Tau Ceti source declaration and the gq2 adapter file; `docs/README.md` and
`docs/orchestration/README.md`: this board and plan become archival once G2 is recorded.

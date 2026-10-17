# Dyadic Tau Ceti discharge: ticket board

Plan: [`tauceti-discharge-plan.md`](tauceti-discharge-plan.md). Branch `dyadic-tauceti`, worktree
`/scratch/claudeM/gq2-dyadic` (mimir). Protocol as the `tauceti` board
([`../orchestration/tauceti-tickets.md`](../orchestration/tauceti-tickets.md)): one ticket = one
agent dispatch; workers never edit this file; each commits on green with
`dyadic-tauceti <id>: <summary>`; adapters are `module` files in `namespace GQ2.TauCetiBridge`, never
`open TauCeti` at top level, no duplicate public names, statements byte-identical to the bundle
fields they fill. Per-file gate for workers: `lake build GQ2.<Module>` (not `lake env lean`, which
ignores the lakefile's `leanOptions`).

Acceptance for every adapter: builds with zero sorries, imports nothing reaching
`GQ2/Foundations/Axioms.lean`, `#print axioms` of its main declaration is the standard three.

## Wave 0: platform (sequential)

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| G0' | owner gate: approve the plan and decisions D1–D4 | owner | — | — | done 2026-10-17 (D1 `dyadic-tauceti`, D2 public, D3 keep the 17 rows, D4 gates = `check_axioms.sh`, `check_dyadic.sh`, ledger, audits, full build) |
| D0 | worktree `/scratch/claudeM/gq2-dyadic`, branch `dyadic-tauceti` off `origin/dyadic` | orchestrator | — | — | done 2026-10-17 |
| T0 | merge `tauceti` into `dyadic-tauceti`; census 11 → 2 (TauCetiInstance for the nine, `Axioms.lean` reduced to B5-K/B10-K); cache toml; pins | orchestrator | the 11 conflicted files (plan §1) | G0' | done ffb225d8 (tag `dyadic-tauceti-T0`); D2 a90262d2 |
| T1 | Mathlib bump `ec410d23d` → `cfc55fc58` of the dyadic tree, statements byte-identical | fable workers | `GQ2/Dyadic/**`, every dyadic-only file; ℚ₂ files already bumped on `tauceti` | T0 | done 2026-10-17: full build green (7627 jobs), `check_axioms.sh` (census 2, 17 `AUDIT_DYADIC` rows at std-3, Tau Ceti audit), `check_dyadic.sh` D-checks, `AxiomLedger`, `PalomarAxiomAudit`, `TauCetiAxiomAudit` all pass; 53 commits dyadic-tauceti-T0..98057ce0, 186 files, +783/−474 |
| T2 | recon memo for B5-K and B10-K: `docs/dyadic/tauceti-discharge-recon.md`, smoke additions | opus | the memo, `GQ2/TauCeti/SmokeK.lean` | T1 | done 2026-10-17: memo, `SmokeK.lean` (108 `#check`s, 32 `example`s, chk OK), and complete sorry-free prototypes of both inputs at the standard three (`docs/dyadic/tauceti-t2-evidence/full/b5k_b10k.lean`, re-elaborated by the orchestrator) |

## Wave 1: dictionary

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| A1-K | `abEquivK`, the norm ↔ valuation bridge on `↥K`, `localTopology_eq`, the residue-degree bridge `Nat.card 𝓀[↥K] = 2 ^ FF.f` (the `chiCycKAb` item is not needed by any clause; D2 is moot — `residueField_card_eq_pow_f` was public) | opus | `GQ2/TauCeti/GaloisDictK.lean` | T2 | landing from the T2 prototype `tauceti-t2-evidence/bridge/` |

## Wave 2: the two inputs

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| B5-K | `markedRecipAt_tauceti K : Dyadic.MarkedRecip localReciprocity_tauceti K` | opus | `GQ2/TauCeti/B5K.lean` | A1-K | landing from `tauceti-t2-evidence/{recipK,kiunram}/` |
| B10-K | `orientedTameQuotientAt_tauceti K FF : Dyadic.OrientedTameQuotientK (markedRecipAt_tauceti K) FF` | opus | `GQ2/TauCeti/B10K.lean` | B5-K, A1-K (not P1) | landing from `tauceti-t2-evidence/tameK/` |

## Wave 3: flip and docs

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| G1' | owner gate: census flip 2 → 0 | owner | — | B5-K, B10-K | open |
| C1' | legacy names as defs; delete `Axioms.lean`; census 0; check 5b at std-3 with the W361 endpoint; ledger; audits | orchestrator | `GQ2/Foundations/TauCetiInstance.lean`, `GQ2/Foundations/Axioms.lean` (delete), `scripts/check_axioms.sh`, `GQ2/AxiomLedger.lean`, `GQ2/TauCetiAxiomAudit.lean` | G1' | open |
| C2' | docs sweep: `literature-axioms-dyadic.md`, `plan.md` status, owner items, `README.md`, `formalization.yaml` | opus | those files | C1' | open |
| G2' | owner gate: fast-forward `dyadic` to `dyadic-tauceti`, push | owner | — | C2' | open |

## Ticket briefs

**T0 (orchestrator).** `git merge tauceti`. Resolutions: `GQ2/Foundations/TauCetiInstance.lean` =
`tauceti`'s file; `GQ2/Foundations/Axioms.lean` re-created from `dyadic`'s version keeping only the
B5-K and B10-K sections (docstring updated: the nine are now theorems in `TauCetiInstance.lean`);
`GQ2.lean` = union of imports; `Foundations.lean` imports both; `check_axioms.sh` = `tauceti`'s
version plus `dyadic`'s check-5b block with every frozen set reduced to the standard three and
`AXIOMS_FILE`/`EXPECTED_AXIOMS=2` restored; `AxiomLedger.lean` = `tauceti`'s with `bAxioms` = the
two `K`-axioms; `comparator-config.json` = `tauceti`'s; docs = `tauceti`'s with `dyadic`'s additions
kept; `Partition.lean` and `SectionTenSources.lean` take `tauceti`'s code and `dyadic`'s docstrings.
Copy `.lake/tauceti-lake-cache.toml`; `lake update` is **not** run (the manifest comes from
`tauceti`); `lake exe cache get`; check that `lake build TauCeti.NumberTheory.LocalField.Padic`
unpacks rather than compiles. Commit `dyadic-tauceti T0: merge tauceti (census 11 → 2)`.

**T1 environment leak (orchestrator, 2026-10-17).** After T0 every GQ2 file reached
`GQ2.Foundations.TauCetiInstance` (`Interfaces → Axioms → TauCetiInstance → public import
GQ2.TauCeti.Instance`), which put the Tau Ceti library and its Mathlib closure (instances such as
`Pi.instCharP`, `TauCeti.IsTopologicalAddGroup.nonarchimedeanAddGroup_of_compactSpace`) into the
environment of ℚ₂ files that are byte-identical to `tauceti`'s and build there (`GQ2/WordCoh2R.lean`,
`GQ2/Shapiro/Read.lean` failed from changed `simp`/instance paths). Fix: `TauCetiInstance.lean`
imports the adapters privately (`import GQ2.TauCeti.Instance`, `public section` without
`@[expose]`, the `LiteratureInputs` instance built field-by-field from the legacy names);
`Interfaces.lean` no longer re-exports `Axioms.lean`; the files that use a legacy input name
import `TauCetiInstance`/`Axioms` directly. Non-`module` files (1379 of 1596) still load private
imports transitively, so the ~1000 transitive importers of those files keep the heavier
environment; divergences there are fixed per file and recorded in the worker brief. The same
restructuring of `TauCetiInstance.lean` is a candidate for `tauceti` (owner item).

**T1 statement exceptions (orchestrator-approved, for the owner's review at G1').** (i) The four
ℚ₂-model pins `example : @prop_6_18_(un)ramified_K_q2 = @<ℚ₂ model> := rfl` in
`GQ2/Dyadic/LocalGauss/{Unramified,Ramified,Main}.lean` take a `[LiteratureInputs]` binder because
the ℚ₂ theorems gained one in the merged refactor. (ii) `GQ2/Dyadic/LocalGauss/ReadPerOrbitK.lean`:
nine `omit` lists drop `[Finite (RegRep N)]`; in the Tau Ceti environment the
`IsTopologicalAddGroup (Fin K → RegRep N)` instance is found through a Tau Ceti instance needing
`Finite`, so the elaborated statements gain that hypothesis (the only caller has it). (iii) Mathlib made `MonoidAlgebra` a structure
without a function coercion: `GQ2/Dyadic/Count/CompletedRankOneFox.lean` `regularUnitGroupAlgebraEquiv_apply`
and `regularModTwoComponent_apply` read `(… c).coeff q = c (q, _)` instead of `… c q = c (q, _)` (the
same translation is applied wherever a group-algebra element is applied to a point). (iv) `Set` is a
structure: `Set`-valued defs whose bodies mention noncomputable constants are marked `noncomputable`
(`GQ2/Dyadic/Count/Wild.lean` `wildLetters`). (v) Mathlib swapped the names `Ideal.ramificationIdx`/`ramificationIdx'` and
`inertiaDeg'`/`inertiaDeg` without a meaning-preserving alias: the four statements of
`GQ2/Dyadic/RamificationInertiaBridge.lean` that use them are renamed accordingly (same underlying
definitions). Everything
else in T1 is proof/import-only; the dyadic files that call ℚ₂ declarations carrying a
`[LiteratureInputs]` binder import `GQ2.Foundations.TauCetiInstance` for the instance.

**T1 (fable workers, orchestrated).** The `tauceti` T1 procedure: a keep-going full build, one
subagent per failing file with the pattern brief, the statement checker on every changed file
(dyadic files against `origin/dyadic`, ℚ₂ files against `master`), commit per green batch,
path-limited, `dyadic-tauceti T1: <files>`. Report the renames met beyond T1's list.

**T2 findings that change the plan (memo §"Corrections", 2026-10-17).** No Tau Ceti lemma is
missing; the gaps are six gq2-side lemma groups, all proved in the prototypes. Q1 is easy:
`rec_K(2) ∈ ker χ_K` with unramified coordinate `−v_K(2) ≠ 0` (no ramification of `ℚ₂(μ_{2^∞})`
needed). Q2: "`ker ν_ur` = image of inertia" is false (the odd part of `ℤ̂` is also in the kernel);
only inertia ⊆ `ker ν_ur` is needed, via `map_inertiaSubgroup_le_fixingSubgroup_iff` and A1's
`layerEmb`. A1's three-`letI` package must be extended with `haveI := valuativeExtension K` before
`FinitePadicExtension ↥K 2`, `artinMap_norm`, `charP_residueField` work; `CharP 𝓀[↥K] 2`,
`CompactSpace (GalKab K)`, `FiniteDimensional ↥K (quadExt K δi)` are supplied by hand. The C1'
same-name defs must live inside `GQ2/Foundations/TauCetiInstance.lean` (`localReciprocity` is
opaque elsewhere since the environment containment), and `B5K` must export
`(markedRecipAt_tauceti K).recip = recipK K` for B10-K.

**T2 (opus, read-only except the two owned files).** For B5-K and B10-K: the exact Tau Ceti
signatures at `↥K` (after A1's `letI` package), which instances synthesize and which must be
supplied, and scratch prototypes for each bundle field; answer Q1 (`ν_ur(ker χ_K) = 2^r ℤ₂`: closed
subgroups of `ℤ_[2]` and the finiteness of the unramified part of `K(μ_{2^∞})/K` in Tau Ceti),
Q2 (inertia, its fixed field, `IsUnramified` ↔ equal norm value groups), Q3 (`Nat.card 𝓀[↥K]` from
`FF.f`). Record every Tau Ceti lemma missing for a clause.

**A1-K, B5-K, B10-K (fable).** As plan §3; start from the T2 prototypes; import
`GQ2.TauCeti.GaloisDict`, `B5`, `B10`, `ProPDict` as needed; heavy Tau Ceti imports only in the
adapters, never in `GaloisDictK.lean`.

**C1' (orchestrator, after G1').** The C2 checklist of the `tauceti` campaign at census 2 → 0, plus
the dyadic gates: check 5b (`AUDIT_DYADIC` rows at the standard three, the W361 endpoint
`GQ2.Dyadic.exists_certifiedFullyMarkedFlexiblePresentation_ramifiedI` added), `check_dyadic.sh`
D1–D6, `TauCetiAxiomAudit.lean` extended with the dyadic endpoints. Gates: full build, zero sorries,
all audits.

**C2' (opus).** `docs/dyadic/literature-axioms-dyadic.md` (§B census rows for B5-K/B10-K → proved via
Tau Ceti with sources and adapters; §W361 trust base: standard three + Tau Ceti `706344c35`),
`docs/dyadic/plan.md` and `owner-items-*.md` status notes, `README.md`'s result section on this
branch, `formalization.yaml` where the branch differs from `tauceti`'s copy.

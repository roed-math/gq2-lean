# Dyadic Tau Ceti discharge: plan

Goal: the `dyadic` branch (the general ramified-`i` campaign) at the standard three axioms. Delete
every `axiom` (census 11 → 0) so that the general endpoint
`GQ2.Dyadic.Instances.FieldFamilySpliceMarkedCanonical.exists_certifiedFullyMarkedFlexiblePresentation_ramifiedI` (`GQ2/Dyadic/GeneralMain.lean`),
`GQ2.Dyadic.ramifiedI_candidate_equiv_galK` (`GQ2/Dyadic/Main.lean`), the seventeen frozen rows of
`scripts/check_axioms.sh` check 5b and the ℚ₂ capstones all print exactly `propext`,
`Classical.choice`, `Quot.sound`, with the literature inputs proved from
[Tau Ceti](https://github.com/TauCetiProject/TauCeti).

Board: [`tauceti-discharge-tickets.md`](tauceti-discharge-tickets.md). Written 2026-10-17 by the
orchestrator of the `tauceti` campaign, whose plan and board
([`../orchestration/tauceti-proof-plan.md`](../orchestration/tauceti-proof-plan.md),
[`../orchestration/tauceti-tickets.md`](../orchestration/tauceti-tickets.md)), recon memo
([`../orchestration/tauceti-t2-recon.md`](../orchestration/tauceti-t2-recon.md)) and adapters
(`GQ2/TauCeti/`) this campaign reuses. Conventions not restated here (module style, no top-level
`open TauCeti`, namespace `GQ2.TauCetiBridge`, no duplicate public names, statements byte-identical,
commit per green batch, workers never edit the board) are those of the `tauceti` board.

## 1. Starting point (measured 2026-10-17 at `origin/dyadic` = `c5438820`, W366)

- Toolchain `leanprover/lean4:v4.31.0-rc2`, Mathlib `ec410d23d` (2026-06-12): the state `master` was
  in before the `tauceti` campaign. 1,572 Lean files and 769k lines under `GQ2/` (`master`: 310 and
  121k); 188 of them `module` files; `GQ2.lean` has 1,451 imports. Many files set
  `maxHeartbeats` up to 3,200,000.
- **Census 11** (`GQ2/Foundations/Axioms.lean`, `EXPECTED_AXIOMS=11`): the nine ℚ₂ inputs, with
  statements **byte-identical** to `master`'s (checked per axiom), plus two `K`-level inputs:
  - **B5-K** `GQ2.markedRecipAt (K) [FiniteDimensional ℚ_[2] K] : Dyadic.MarkedRecip localReciprocity K`
    (bundle in `GQ2/Dyadic/MarkedRecipBundle.lean`; gate G-AX 2026-07-29, `ax3-proposal.md`);
  - **B10-K** `GQ2.orientedTameQuotientAt (K) [FiniteDimensional ℚ_[2] K] (FF : DyadicUnitFiltration K) : Dyadic.OrientedTameQuotientK (markedRecipAt K) FF`
    (bundle in `GQ2/Dyadic/OrientedTameBundle.lean`; `ax4-proposal.md`).

  46 files consume the two; the W361 general endpoint consumes both; none of the seventeen check-5b
  rows does (they print subsets of the nine).
- Merge base with `master` and `tauceti`: `d0714a7c`. `dyadic` lacks `master`'s eight later commits
  (the explicit-literature-inputs refactor, PR #5: `LiteratureInputs`, the `_of_inputs` capstones,
  the Palomar Comparator pair), so merging `tauceti` brings those too.
- Trial merge (`git merge-tree tauceti origin/dyadic`): **11 conflicted files, all glue**:
  `GQ2.lean`, `GQ2/AxiomLedger.lean`, `GQ2/Foundations.lean`,
  `GQ2/Foundations/TauCetiInstance.lean` (the rename of `Axioms.lean` against `dyadic`'s two added
  axioms), `GQ2/SectionTenSources.lean` (docstring), `GQ2/SectionEight/Partition.lean` (one hunk: a
  `[LiteratureInputs]` binder against a docstring path), `comparator-config.json`,
  `scripts/check_axioms.sh`, `formalization.yaml`, `docs/README.md`, `docs/literature-axioms.md`.
  The 53 T1 proof-fix files auto-merge.
- Gates on `dyadic`: `scripts/check_axioms.sh` with check 5b (`AUDIT_DYADIC`, seventeen capstones at
  frozen per-declaration axiom sets, and `AUDIT_DYADIC_PAIRS`); `scripts/check_dyadic.sh` D1–D6 (D2
  obligation guard, D4 one-tree hash of the generated word TeX against Lean `_astHash` constants, D6
  ledger opt-in); `GQ2/AxiomLedger.lean`; CI builds `GQ2 Challenge Solution`.
- Policy (plan A6): the ℚ₂ tree is frozen; in-place edits need approval. The Mathlib bump is such an
  approval, under T1's rule: proofs, imports and renamed identifiers only, statements byte-identical.

## 2. Platform decisions

**Branch.** Work on `dyadic-tauceti` (worktree `/scratch/claudeM/gq2-dyadic`, created from
`origin/dyadic`); fast-forward into `dyadic` and push at the final owner gate. Nothing is pushed
before that.

**Pins.** They arrive with the `tauceti` merge: `v4.35.0`, Mathlib `cfc55fc58`, TauCeti `706344c35`,
the Tau Ceti cache step in CI. Locally, the cache toml of plan §2 of the `tauceti` plan is copied to
the new worktree's `.lake/`, and `LAKE_CACHE_DIR` may point at `/scratch/claudeM/gq2-tauceti/.lake/cache`
to reuse the 15,395 unpacked artifacts.

**Intermediate census 2.** At the merge, the nine ℚ₂ inputs become theorems through
`GQ2/Foundations/TauCetiInstance.lean` exactly as on `tauceti`; `GQ2/Foundations/Axioms.lean` is
re-created holding **only** the two `K`-level axioms, `EXPECTED_AXIOMS=2`, `AXIOMS_FILE` restored, and
every check-5b row's frozen set loses the nine names (all seventeen become the standard three; the
rows stay, so growth still fails the gate). The two `K`-axioms stay axioms until their adapters land.

**Adapters.** Module files in `GQ2/TauCeti/` (`GaloisDictK.lean`, `B5K.lean`, `B10K.lean`), namespace
`GQ2.TauCetiBridge`, importing the landed dictionaries. `MarkedRecipBundle.lean` and
`OrientedTameBundle.lean` are `module` files, so the adapters can import them; the final instance
file keeps the two legacy names as same-name `noncomputable def`s (the C2 pattern).

**Builds.** The dyadic tree is five times `master`; a full build is long and the keep-going build loop
of T1 is kept but with fewer, larger rounds. The dyadic board's trap applies: `lake env lean` does
**not** apply the lakefile's `leanOptions` (`autoImplicit false`), so the per-file gate for workers
is `lake build GQ2.<Module>`, never `lake env lean` alone.

**Owner gates.** G0' this plan (branch, census-2 interim, the decisions of §6). G1' the census flip
2 → 0. G2' fast-forward into `dyadic` and push.

## 3. The two new inputs, mapped to Tau Ceti

The nine ℚ₂ inputs need no new work: the `tauceti` adapters apply verbatim because the statements
are byte-identical. Everything below is about B5-K and B10-K. `K` is a finite
`IntermediateField ℚ_[2] ℚ̄₂`; gq2's `GalK K = ↥K.fixingSubgroup`, `GalKab K = TopologicalAbelianization (GalK K)`,
`toAbK`, `inclAbK : GalKab K →* AbsGalQ2ab`, `normUnitsK = Units.map (Algebra.norm ℚ_[2])`,
`chiCycKAb` (all `GQ2/Dyadic/MarkedRecipBundle.lean`); `Tq q = profinitePresentation {tameWordQ q}`
with `Tq 2 = Ttame` by `rfl`, `nuTq q : Tq q →ₜ* Ztwo` (`GQ2/Dyadic/TameQuotientK.lean`);
`qOf K FF = 2 ^ FF.f`, `uniformizerK K FF` (`GQ2/Dyadic/OrientedTameBundle.lean`).

### A1-K: the dictionary additions

Tau Ceti states local class field theory on `Field.absoluteGaloisGroup ↥K` for any
`IsNonarchimedeanLocalField ↥K`; A1 already gives `absGalEquivFixing K : Field.absoluteGaloisGroup ↥K ≃ₜ* ↥K.fixingSubgroup`
and the local-field package on `↥K` (`valuativeRel`, `localTopology`, `isNonarchimedeanLocalField`,
`valuativeExtension`, for `letI`). New:

- `abEquivK K : GalKab K ≃ₜ* Field.absoluteGaloisGroupAbelianization ↥K`, sending `toAbK K g` to the
  class of `(absGalEquivFixing K).symm g`, with `inclAbK` matched to the abelianization of
  `absoluteGaloisGroupExtend ℚ_[2] ↥K (sepEmb K)` (A1's `absoluteGaloisGroupExtend_absGalEquivFixing_symm`:
  extend ∘ e⁻¹ is the inclusion `GalK K → AbsGalQ2`).
- **The norm ↔ valuation bridge on `↥K`.** gq2 states units and uniformizers through the spectral
  norm `‖·‖` of `ℚ̄₂` (`PadicAlgCl`) restricted to `K`; Tau Ceti through `normalizedValuation ↥K`
  and `ValuativeRel ↥K` (A1 found the two topologies equal but not definitionally). Needed:
  `‖(x : ℚ̄₂)‖ = 1 ↔ normalizedValuation x = 1`, and "`‖π‖ < 1` maximal among the `‖z‖ < 1`"
  ↔ `normalizedValuation π = ofAdd (-1)`; equal norm value groups (gq2's `HasEqualNormValueGroups`)
  ↔ Tau Ceti's `IsUnramified` (`isUnramified_iff_normalizedValuation_algebraMap`,
  `isUnramified_iff_ramificationIndex_eq_one`). This bridge is used by every clause of both bundles.
- **Residue degree.** `Nat.card 𝓀[↥K] = qOf K FF = 2 ^ FF.f`: gq2's filtration residue degree
  against Tau Ceti's residue field. gq2's `card_gradeZero`/`card_gradeI`
  (`GQ2/UnitFiltrationCounts.lean`) are `private`; the dyadic board (AS-F) already asked for them to
  be exposed: owner decision D2 of §6.
- `chiCycKAb K` against `abelianizedLocalCyclotomicCharacter 2 ↥K` through `abEquivK`, from A1's
  `chiCyc_eq` and Tau Ceti's `localCyclotomicCharacter_absoluteGaloisGroupExtend`.

### B5-K `markedRecipAt K : MarkedRecip localReciprocity K`

| field | Tau Ceti source | translation |
|---|---|---|
| `recip : (↥K)ˣ →* GalKab K` | `ClassFieldTheory.artinMap ↥K` | transported along `abEquivK` |
| `continuous_recip`, `denseRange_recip` | `continuous_artinMap`, `denseRange_artinMap` | through the homeomorphism |
| `nu_ur : GalKab K →* Multiplicative ℤ_[2]`, continuity | `unramifiedCoordinate ↥K`, `zHat.lift (ofAdd 1)` | B5's `nuUr` pattern (inverse: arithmetic vs geometric), at `↥K` |
| `norm_compat : inclAbK (recip x) = R.recip (normUnitsK K x)` | `artinMap_norm` (`Local/ArtinMap.lean:345`): `Art_K (N_{L/K} x) = extend (Art_L x)` | exactly this clause at `(ℚ_[2], ↥K)`; `normUnitsK` is Tau Ceti's `Algebra.normUnits ℚ_[2]`; `inclAbK` via `abEquivK` and A1 |
| `nu_ur_recip_unit` (‖u‖ = 1) | `unramifiedCoordinate_artinMap`, `normalizedValuation` of a unit | norm ↔ valuation bridge |
| `nu_ur_recip_uniformizer` (norm-maximal ‖π‖ < 1 ⇒ `ofAdd (-1)`) | same, `normalizedValuation π = ofAdd 1` (arithmetic) | bridge + inversion |
| `r`, `nu_ker_chi_le`, `nu_ker_chi_ge` (`ν_ur(ker χ_K) = 2^r ℤ₂`) | no single theorem; `abelianizedLocalCyclotomicCharacter`, `unramifiedCoordinate`, closed subgroups of `ℤ_[2]`, the ramification of `ℚ_[2](μ_{2^∞})` | Recon question Q1: the image of the compact `ker χ_K` under continuous `ν` is a closed subgroup of `ℤ₂`, so `0` or `2^r ℤ₂`; it is nonzero because the unramified part of `K(μ_{2^∞})/K` is finite (`ℚ_[2](μ_{2^∞})/ℚ_[2]` totally ramified). Hard. |
| `ki_unramified` (inertia trivial on `μ₄` ⇒ `HasEqualNormValueGroups K δi`) | `inertiaSubgroup`, its fixed field as the maximal unramified extension, `IsUnramified` criteria | Recon question Q2: `ker ν_ur` in `G_K^ab` is the image of inertia (`localArtinMap_unit_of_unramified`, `mem_inertiaSubgroup_of_mk_eq_artinMap` pattern), inertia acting trivially on `μ₄ = {±1, ±i}` makes `K(i)` fixed by inertia hence unramified, then the bridge to equal norm value groups. Hardest clause. |

Dependencies: A1, A1-K; none of A2/P1.

### B10-K `orientedTameQuotientAt K FF : OrientedTameQuotientK (markedRecipAt K) FF`

| field | Tau Ceti source | translation |
|---|---|---|
| `W`, `normal`, `isClosed`, `isProP` | `wildInertiaSubgroup ↥K`, `wildInertiaSubgroup_normal`, `isClosed_wildInertiaSubgroup`, `isProP_wildInertiaSubgroup` (needs `CharP 𝓀[↥K] 2`, from `charP_residueField ↥K 2` once `FinitePadicExtension ↥K 2` is found after A1's `letI` package) | transported along `absGalEquivFixing K` to `GalK K`; P1's `isProP_iff_tauCeti` |
| `equiv : GalK K ⧸ W ≃ₜ* Tq (qOf K FF)` | `tameQuotientGeometricEquiv` at `↥K` (`IwasawaGroupGeometric ↥K`, relator with `Nat.card 𝓀[↥K]`), `exists_isArithFrobeniusLift`, `exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top` | B10's `iwasawaGeometricEquivTtame` generalized to `Tq q` (same relator `γ⁻¹τγ(τ^q)⁻¹`, `ULift` by `fin_cases`), then `q = Nat.card 𝓀[↥K] = qOf K FF` by the residue-degree bridge. Recon question Q3: is `Nat.card 𝓀[↥K]` computable from `FF.f` without the private lemmas? |
| `nuT_recip_unit`, `nuT_recip_uniformizer` | `iwasawaCoordinateGeometric_tameQuotientGeometricEquiv`, `unramifiedCoordinate_artinMap`, `normalizedValuation` | B10's single lemma at general `q`: `nuTq q (equiv (mk g)) = ztwoOne⁻¹ ^ v_K(x)` whenever `toAbK K g = markedRecipAt.recip x`, with `nuTq q ∘ e = zHat.lift ztwoOne⁻¹ ∘ iwasawaCoordinateGeometric`; `uniformizerK K FF` has valuation `1` by the bridge |

Dependencies: B5-K (its type mentions `markedRecipAt K`), A1-K, P1.

## 4. Steps

- **T0, merge.** `git merge tauceti` into `dyadic-tauceti`; resolve the 11 files as in §2 (census 2).
  The result does not build (toolchain changed); like `tauceti`'s T0 it is the start state of T1.
  Copy the cache toml; `lake exe cache get`; verify Tau Ceti unpacks from cache.
- **T1, Mathlib bump** of the dyadic tree (`ec410d23d` → `cfc55fc58`, `v4.31.0-rc2` → `v4.35.0`).
  Same rules and tooling as `tauceti` T1: statements byte-identical (the statement checker, extended
  with `git diff` against `origin/dyadic` for the dyadic files and against `master` for the ℚ₂
  files), the pattern brief (now with the eleven T1 patterns pre-loaded: transparency, lost imports,
  `@[to_fun]`, `PadicInt.ext`, `Equiv.setCongr`, `FreeGroup.induction_on`'s `one`, def-synonym
  products, …), subagents per failing file, the build loop, commit per green batch. Done when
  `lake build GQ2 Challenge Solution ChallengePalomar SolutionPalomar` is green, `check_axioms.sh`
  passes at census 2, `check_dyadic.sh` passes, `AxiomLedger`, `PalomarAxiomAudit` and
  `TauCetiAxiomAudit` pass. The long pole.
- **T2, recon** for the two `K`-lanes, in the format of `tauceti-t2-recon.md`: verbatim Tau Ceti
  signatures at `↥K`, instance needs after A1's package, answers to Q1–Q3 of §3, scratch prototypes.
- **A1-K** (`GQ2/TauCeti/GaloisDictK.lean`): the §3 dictionary additions.
- **B5-K** (`GQ2/TauCeti/B5K.lean`): `markedRecipAt_tauceti K : Dyadic.MarkedRecip localReciprocity_tauceti K`;
  note the bundle is parametrized by the reciprocity datum, so it is stated at B5's adapter and
  reaches the legacy name through `localReciprocity = localReciprocity_tauceti` (`rfl`, as B10 did).
- **B10-K** (`GQ2/TauCeti/B10K.lean`): `orientedTameQuotientAt_tauceti K FF : Dyadic.OrientedTameQuotientK (markedRecipAt_tauceti K) FF`.
- **C1', assembly and flip** (one atomic commit after G1'): `GQ2/Foundations/TauCetiInstance.lean`
  gains the two legacy names as same-name `noncomputable def`s; `Axioms.lean` deleted again;
  `EXPECTED_AXIOMS=0`; check 5b rows at the standard three with the W361 endpoint added;
  `AxiomLedger.bAxioms` empty; `TauCetiAxiomAudit` extended with the dyadic endpoints;
  `comparator-config.json` already at the standard three from the merge.
- **C2', docs**: `docs/dyadic/literature-axioms-dyadic.md` (census rows B5-K/B10-K → proved via Tau
  Ceti; the W361 section's trust base), `docs/dyadic/plan.md` status note, `docs/dyadic/owner-items-*.md`,
  `README.md` (dyadic flavour), `formalization.yaml` if the branch's copy diverges.
- **G2'**: fast-forward `dyadic` to `dyadic-tauceti`, push.

## 5. Risks

- **Volume of T1.** ~1,260 files not covered by the `tauceti` bump. T1 fixed 53 of 310 files (17%);
  expect 150–250 dyadic files needing edits, dominated by the same patterns, plus the heavy-heartbeat
  files, where the v4.35 transparency check may push elaboration over budget. Rounds of the build
  loop take tens of minutes instead of seconds. Mitigation: the pre-loaded pattern brief, more
  parallel subagents, batching by directory.
- **B5-K's `r` and `ki_unramified` clauses** have no Tau Ceti theorem matching them; they are
  compositions (Q1, Q2). If a piece is missing from Tau Ceti main, it is proved in gq2 first (the
  `tauceti` plan's rule for B6).
- **The norm ↔ valuation bridge** touches the two-topologies diamond on `↥K` (memo cross-cutting 3);
  it must be stated with explicit `@` instance arguments.
- **Instance-search timeouts** at `↥K` under Tau Ceti's class-field-theory imports (memo cross-cutting
  2; A1 found the trigger is already `AbsoluteRamificationIndex`). A1-K must stay on light imports
  and export named facts; B5-K/B10-K `haveI` them.
- **The merge brings the `LiteratureInputs` refactor** into the dyadic tree: dyadic consumers of ℚ₂
  theorems now meet `[LiteratureInputs]` binders, filled by the global instance
  `tauCetiLiteratureInputs`; a few call sites may need `haveI`/explicit instances (Partition.lean's
  conflict is the visible case).
- **Frozen-tree policy and D4.** The bump edits proofs in frozen files (approved here); D4 hashes
  generated TeX against Lean data constants and is untouched by proof edits.
- **CI time**: the dyadic build plus Tau Ceti's closure; the 120-minute limit set in C1 may need
  raising once CI actually runs (it has not run for either branch).

## 6. Decisions for the owner (G0')

- **D1** Working branch `dyadic-tauceti`, fast-forwarded into `dyadic` at G2' (recommended), versus
  committing on `dyadic` directly.
- **D2** Expose `card_gradeZero`/`card_gradeI` in `GQ2/UnitFiltrationCounts.lean` (a one-word change
  in a frozen ℚ₂ file, as the dyadic board requested at AS-F), versus re-proving the residue-degree
  count inside A1-K.
- **D3** Check 5b: keep the seventeen frozen rows, all at the standard three (recommended: growth
  still fails the gate), versus retiring the block in favour of check 5's `AUDIT_STD3_DECLS`.
- **D4** Which of the Codex-era verification scripts (`scripts/w361_*`, `scripts/mirror.sh`) are
  gates for this campaign. Proposed: `check_axioms.sh`, `check_dyadic.sh`, `AxiomLedger.lean`,
  the three audit files and the full build; the W361 fresh-build/staged scripts are not run.

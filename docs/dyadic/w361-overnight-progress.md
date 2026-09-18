# W361 overnight general-case campaign

Start: 2026-09-17 09:10 UTC. Requested minimum horizon: 2026-09-17 17:10 UTC
(13:10 America/New_York). This is a continuation of W360, not a restart.

Heartbeat `overnight-dyadic-general-case-research` is active every 30 minutes in the
current task. At the first safe checkpoint after the horizon, verify, summarize, and
pause it. Do not claim eight hours have elapsed before checking the clock.

## Guardrails and environment

Read `w360-restart-handoff.md` for exact mathematical and build state. Preserve the
92-commit local lead and all uncommitted W360 work. No commit, push, reset, new axiom,
proof placeholder, native_decide, or heartbeat override. General arguments only;
finite examples serve solely as diagnostics or counterexamples.

Repository: `/Users/roed/claude/cla/work/gq2-dyadic-campaign`.
Raw Lean helper: `/private/tmp/gq2-w360-lean.sh`.
Durable pinned runner (preferred): `scripts/w361_lean_runner.sh`, with
`GQ2_W361_PACKAGES=/Users/roed/claude/gq2-paper/formalizations/gq2-claude/.lake/packages`.
Transitive rebuild: `/private/tmp/gq2-rebuild-campaign.py`.
Parent coordinates umbrella/full builds; agents may compile their distinct modules.

## Active lanes (09:18 UTC)

- Root: generic tame-correction invariance of first-order and Heisenberg normal
  pairings, then integration and next general analytic steps.
- `raw_pairing`: actual sheared hyperbolic Fox row and normal forms, owning new
  `EvenMHeadHandleHyperbolicShearedFox.lean`.
- `source_audit`: independent finite-action diagnostics of the corrected source's
  ramified pairing with the true powers-of-sigma action profile.
- `odd_front_audit`: uniform positive-level epsilon-false Mpc mixed-head structural
  route; unit-head U-minus-C is not a unit at positive level.

Inspect agent state before reassigning; do not duplicate an active lane.

## Verification update

The previously running full W360 scoreboard completed successfully (terminal 31954,
exit 0), generated 2026-09-17 02:41 local, log
`/private/tmp/gq2-w360-scoreboard.log`. All six W360 rows are EXISTS / std-3.
Historical MISSING rows remain for three structure-name lookups (flexible certificate
leaves, boundary-compatible equivalence, Nielsen pair); this is not a failed compile
and does not assert missing certificate producers have been supplied. W360's full
1,351-module umbrella and default dyadic gate were already checked separately.

## Results and revised general route (09:35 UTC)

- `TameCorrectionStokes.lean` is checked at default limits: arbitrary tame correction
  preserves d1 and eta on tau-normalized cochains. If tau acts trivially and the resolved
  correction exponent is divisible by four, the entire Stokes ladder is unchanged, on all
  cochains. Public audits use only the standard three logical axioms.
- `StokesJetZero.lean` is checked: a word at zero-jet generator lifts has zero first jets,
  and its central charge is the mod-two exponent character of the generator charges.
- The naive sheared hyperbolic source has a real finite-action defect. The reproducible
  `scripts/w361_hyperbolic_action_diagnostic.py --self-test` checks GF4 examples with odd B
  or D row: full H1 pairing has radical dimension two. Prime-to-two correction exponent
  16 satisfies the parity and finite-action constraints. Strict abstract handle rows do
  not exclude these cases, but realizability by a specific selected field's nu has NOT
  been proved. Do not claim a field counterexample.
- `raw_pairing` has checked generic D-clearing in new
  `EvenMHeadHandleHyperbolicPreNormalize.lean`. This preserves chi/U/C and restores V=0;
  it cannot by itself remove the B-only defect.
- `odd_front_audit` has checked the structural positive-level route in scratch: use the
  actual unit nu(D) as the arbitrary-unit Mpc parameter, normalize sigma to one, then
  apply the simultaneous wild shear. No unit U or distinguished-C premise is needed.

### Tame averaging splice: the new priority

Define a substitution P by

    P(sigma) = sigma, P(tau) = 1,
    P(wild_i) = (wild_i * tau)^omega2 * (tau^omega2)^(-1).

Write Shadow(R) for substitution by P and define

    Splice(R, H) = Shadow(R) * H * Shadow(H)^(-1).

Here R supplies the correctly normalized pro-2 core, and H supplies a known good ramified
template. On pro-2 evaluations with tau=1, Shadow is the identity, so Splice has the core R.
On ramified cochains with sigma offsets zero, every shadow generator has zero jets. Only
wild central charges can remain, and the even wild exponents of a relator cancel them.
On unramified cochains with tau offsets zero, Shadow preserves Heisenberg coordinates and
base action, so H and its shadow cancel. This is a proposed general gluing mechanism,
not yet a completed source certificate.

The diagnostic splice exactly recovers the good raw Fox columns and normal Gram in all
tested GF4 profiles and a difficult GF16 profile. Finite tests are evidence only.
The template H can probably be original compact M (same alphabet, all handle ranks),
not necessarily the W360 hyperbolic template, which needs a chosen handle.

Current ownership supersedes the initial lanes:

- Root: `Instances/TameShadowRamified.lean`, generic ramified shadow vanishing and later
  Stokes transfer. Initial single-lift jet lemmas are being checked.
- `raw_pairing`: `GQ2/Dyadic/TameShadowWord.lean`, namespace GQ2.Dyadic,
  `tameShadowSubst`, `tameShadow`, `tameSplice`; pro-2/core transport, endpoint, pure-sigma
  base evaluation and tame specialization.
- `source_audit`: `GQ2/Dyadic/HeisActionCongruence.lean` and a dedicated
  `TameShadowUnramified.lean`, action-congruence and unramified shadow comparison.
- `odd_front_audit`: banking positive-level normalized Mpc core, then unramified Stokes
  transport for that source. Analytic/certificate closure is not claimed from core alone.

### Checked ramified gluing milestone (09:50 UTC)

`Instances/TameShadowRamified.lean` is now green, all eight public audits std-3 and no
warnings/default limits. The result is stronger than the initial normal-form plan:

- At actual wild base one (as in a faithful simple action image), every shadow wild
  generator is CENTRAL on arbitrary cochains, including arbitrary sigma/tau offsets.
- Endpoint gives even wild exponents. Tame specialization, via `tqClassify` and a valid
  Heisenberg resolver, kills the remaining pure-sigma evaluation.
- `heisEvalZ_tameSplice_ramified` proves full equality with the template's Heisenberg
  evaluation, for every cochain. `stokesDuality_tameSplice_ramified_iff` transfers the
  full Stokes ladder with NO normal-form/separation hypothesis.
- Inputs are explicit: finite group/coefficient, wild base one, tau odd fixed-point-free
  action, both tame specializations and endpoints, and resolvers. No theorem asserts that
  these structural/resolver premises have magically been supplied for every selected field.

`StokesWordComparison.lean` is also checked: equal a/l/z coordinates identify full Stokes
ladders, using the l-coordinate for the dual differential (no extra bidual resolver).

Other banked modules now available:

- `GQ2/Dyadic/TameShadowWord.lean`: 16 checked structural declarations, including complete
  CorePresentation.ofTameSplice, tame specialization, pure-sigma semantic/resolved
  evaluation, and endpoint transport.
- `GQ2/Dyadic/HeisActionCongruence.lean`: generic coordinate/action congruence under words.
- `GQ2/Dyadic/TameShadowUnramified.lean`: shadow/splice agree with R on tau-normalized
  unramified cochains, with arbitrary sigma offsets/action (checked by source_audit).
- `Instances/MpcMobileNuSource.lean`: positive-level normalized core and tame correction.
- `Instances/OmegaPinnedLevelResolver.lean`: coefficient-independent level resolver, with
  E(omega2) exactly the nonnegative omega2Exp N and E2 linked to E(padicOmega2 z).

Next ownership:

- Root: uniform resolver wrapper and compact-M ramified template integration, then assembly.
- source_audit: generic unramified Stokes transfer from tau-normal comparisons. Do NOT
  assert full d1 equality in general; it is false off the tau-zero subspace.
- odd_front_audit: semantic arbitrary-unit Mpc unramified sigma-FPF and scalar supply,
  using resolver-dependent literal displays, not a nonexistent global rational display.
- raw_pairing: normalized pair-source unramified/scalar supply for unit-handle M0 branch.

No W361 umbrella/full gate has been run yet. Parent owns integration and full rebuild.

### Complete analytic-core milestone (10:10 UTC)

The preceding "no W361 umbrella" line is now superseded. The first W361 umbrella rebuild
completed successfully: 1,376 modules, 26 newly compiled. All newly compiled source modules
passed their default-limit checks. The ordinary dyadic gate also passed after supplying the
recovered pinned package path through LEAN_PATH. An initial invocation without that path
failed to find Mathlib; that was an environment failure, not a proof failure. Corrected gate
log: `/private/tmp/gq2-w361-gate.log`. Optional D6 remains off. Diagnostic self-test and
`git diff --check` pass.

The mathematically important improvement is that BOTH changed-source families now have full
finite-coefficient Stokes supply, not just ramified normal-pairing calculations:

- `EvenMHeadHandlePairSplice.lean` and `EvenMHeadHandlePairSpliceSupply.lean`: corrected,
  normalized head-handle pair word spliced with compact M, arbitrary positive handle rank,
  alpha >= 2. No analytic residual hypothesis; the exact unit-U equation is needed only for
  its normalized pro-2 core, not the analytic theorem.
- `MpcMobileSpliceSupply.lean`: normalized actual-unit Mpc word, prime-to-two corrected and
  spliced with compact M, arbitrary unit, level, p, and handle rank (including zero), alpha >= 2.
  Again no analytic residual. Its normalized core retains the exact actual nu(D)=eta premise.
- `TameSpliceRamifiedSupply.lean` discharges all finite resolver and compact-template inputs.
  `TameSpliceActionImage.lean` connects ramified gluing and normalized cores to the preexisting
  word-generic devissage in `NpcActionImageDevissage.lean`.
- `StokesKernelTransport`, `TameNormalStokes`, and `TameSpliceUnramifiedStokes` supply the
  unramified comparison. Scalar transfer uses the endpoint/chain-square diagonal-d1 argument;
  fixed-point-free transfer uses kernels, ranges and cycle pairing, not false full-d1 equality.

The common downstream certificate pipeline is now checked, without branch hypotheses:

- `GammaRUniformStokesSupply.lean`: `UniformStokesSupply`, scalar character count, scalar H2
  cardinality two, complete scalar certificate, and half-torsor identity. The nonzero variation
  datum is supplied by the tame sigma map to the fixed order-two quotient, not a core pivot.
- `GammaRUniformExactLifting.lean`: complete `ExactLiftingSemanticsRN`.
- `GammaRUniformAnalyticCore.lean`: all four Stokes-certificate clauses and a genuine
  `SourceAnalyticCoreRN` constructor. `certificateLeaves` now leaves ONLY the affine determinant
  as an analytic premise, along with the explicitly supplied normalized core and tamespec.
- `TameSpliceAnalyticSources.lean`: concrete `headHandlePairSplice_analyticCore` and
  `mpcMobileSplice_analyticCore` producers, both checked std-3/default limits.

All these new public audits are standard three only. No new axiom, placeholder, option,
commit, or push. Later banking after the first umbrella build needs a new umbrella rebuild.

Current bounded lanes:

- Root: general boundary-head projection plumbing, integration, verification and documentation.
- source_audit: extraspecial central-extension shadow comparison for the affine phase. Ordinary
  Heisenberg Stokes comparison alone does not determine the diagonal/factor-set Gauss value.
- odd_front_audit: generic scalar-H2 trace orientation and QZero-to-hessRelZ seam, using the new
  UniformStokesSupply rather than a hardcoded compact-M carrier.
- raw_pairing: selected-field coverage package. Strict M0 at level zero forces unit U after
  pulled-back-nu transport; positive Mpc supplies actual unit D by its existing residue theorem.
  The old frozen-word HasSelectedRowResidualRN is NOT being asserted for the new source.

Still open: affine determinant for the new words, completed flexible selected dispatcher, and
the separate shared reciprocity/field-arithmetic inputs described in W360. The eight-hour
horizon is still 17:10 UTC; only about one hour has elapsed at this milestone.

### Quadratic comparison milestone (10:40 UTC)

The second umbrella rebuild passed: 1,386 modules, including the general determinant
assembler, selected structural coverage, and initial extraspecial shadow comparisons.
Further imports were added after that build and need rebuilding.

- `GammaRUniformDeterminant`: an arbitrary even-degree uniformly Stokes source gets its
  determinant and complete flexible leaves from its actual `wPhBranchFreeSupply`. No
  hardcoded compact-M carrier remains in the assembler.
- `GammaRUniformWordTrace`, `GammaRUniformWordPhaseSeam`, and
  `GammaRUniformProjectedPhaseSeam`: scalar H2 orientation, arbitrary-word QZero trace,
  and exact projected factor-set comparison, all on the actual source.
- `TameShadowHessian`/`Ramified`, `HessianPinnedResolverTransport`, and
  `TameHessianNormalization`: the full extraspecial extension is controlled, including
  quadratic factor-set terms that ordinary Heisenberg Stokes does not determine.
- `TameSpliceRamifiedComparison.phaseComparison_tameSplice_mCompact_ramified` is checked:
  arbitrary structural word, all handle ranks, complete normal-form existence/uniqueness
  and phase comparison. It leaves only genuine boundary hypotheses and the supplied
  uniform Stokes, endpoint, and tame specialization, all available for both new families.
- Both actual unramified sources now have QZero equal to the compact wall-handle phase:
  `MpcMobileProjectedPhase` and `EvenMHeadHandlePairProjectedPhase`.
- `WordPhaseRawUnramifiedNormal` supplies the raw pair and semantic-Mpc normal forms with
  NO raw-relator-death assumption. The old row normal-form theorem's unused death binder
  was removed in a fresh proof, which also compiles at default limits.
- `SigmaNormalKernelTransport` and `SigmaNormalSpliceTransport` identify actual source
  kernels using comparison only on sigma=tau=0. The raw side needs only d1-d0 square zero,
  not false relator death in the possibly nonfaithful original coefficient group.
- `EvenMHeadHandlePairSpliceNormal` and `EvenMHeadHandlePairUnramifiedComparison` are checked
  and cached. The latter is a genuine complete source-to-phase comparison, not merely a
  formula on assumed normal coordinates.
- `WordPhaseBoundaryMarking` and `WordPhaseHeadProfiles` derive the actual projected base
  entries and action profiles. In particular, faithful-head powOmega2(sigma)=1 is an
  actual group equality in the unramified branch; this is not inferred merely from a
  trivially acting element before passage to the faithful quotient.

All new public audits remain std-3/default limits. No new axiom, placeholder, option,
commit, or push. Last diff check passed.

Current ownership:

- Root: integration and verification; audit the independent field-reciprocity frontier.
- source_audit: concrete pair-splice boundary phase supply and affine determinant.
- odd_front_audit: complete actual Mpc unramified comparison, then boundary supply and
  affine determinant (using the completed common ramified comparison).
- raw_pairing: complete selected changed-source residual/dispatcher, waiting on the two
  concrete determinant producers; keep ordinary orientation explicit and stop the std-3
  layer before the known axiom-bearing final field identification.

No completed concrete determinant is claimed at this timestamp. The eight-hour horizon
remains 17:10 UTC; approximately 90 minutes have elapsed.

### General even-M source closure (10:50 UTC)

The preceding determinant caveat is now superseded. BOTH concrete determinant producers and
the complete selected changed-source dispatcher are checked at default limits/std-3:

- `EvenMHeadHandlePairSpliceBoundary`: actual boundary comparison, branch-free phase supply,
  affine determinant, complete flexible leaves and full corrected word certificate. Inputs
  are alpha>=2 and the structural exact unit-U row; no residual phase, normal form, pairing,
  Stokes, or determinant premise.
- `MpcMobileUnramifiedComparison` and `MpcMobileSpliceBoundary`: actual unramified comparison,
  both boundary branches, branch-free supply, determinant and complete flexible leaves.
  Arbitrary r,p,h and unit eta; exact actual nu(D)=eta is the structural input. Positive
  selected Mpc supplies this by taking eta to be the field's actual D-value.
- `EvenMSelectedSpliceComplete` (12 std-3 audits): complete field-tied changed-source data,
  full corrected residual, strict M0 and selected positive Mpc producers, and
  `hasSelectedFlexibleRowResidualRN_of_evenMInputs`. This retains the ordinary Mpc field
  orientation, M0 canonical-or-strict structural boundary, and inherited canonical residual
  producer as explicit inputs. It does not assert a residual at the old frozen obstructed
  word. Rank-zero M0 goes through the canonical branch; both positive Mpc signs and all
  handle counts are covered.

The third umbrella build passed with 1,403 modules before these last four imports. A fourth
build is being run after their registration. Full scoreboard session 58724 was started at
10:46 UTC using a fresh private mirror; it may reflect the preceding import snapshot, so
check completion and freshness rather than assuming it certifies the latest four imports.
Diagnostic self-test and diff check pass. No commits/pushes or new axioms/options/placeholders.

The explanatory proof note is `w361-tame-splice-mechanism.md`.

New research lanes after source closure:

- Root: integration/verification and the precise content of the base LocalReciprocity
  normalization. Its norm-kernel law alone should not be confused with the full signed
  Frobenius law; examine prime-to-two normalization rather than adding an assumption.
- odd_front_audit: direct actual tame-inertia versus absolute-residue inertia comparison,
  using existing finite odd-root lifting and group structure if possible.
- source_audit: compatible anchored norm-value equality; determine whether special layers
  permit a proof weaker than full relative finite-abelian CFT. Do not redo W300 unit counting.
- raw_pairing: independent read-only adversarial audit of the new complete source/selected
  statements, recording exact hypotheses and remaining field frontier in a dedicated note.

Final field identifications still require the shared compatible ramified-data input and
inherit established field-theoretic axioms. The new std-3 source producers do not hide or
discharge those axioms. Minimum overnight horizon is still 17:10 UTC (about six hours left).

### Arithmetic restart and independent audit (11:08 UTC)

The fourth umbrella rebuild passed: **1,407 modules**, including the complete pair/Mpc
source certificates and selected changed-word dispatcher. The ordinary dyadic gate was rerun
at that state and passed (`/private/tmp/gq2-w361-gate.log`; optional lake ledger off).
The independent adversarial audit is in `w361-independent-audit.md`: no source-closure defect
found, exact remaining field inputs and inherited axioms recorded, rank-zero Mpc probed.

The scoreboard attempt 58724 returned an **UNVERIFIED** board (probe did not elaborate),
not a passing census. The running script was modified when the last five source rows were
added, plausibly causing its shell parse error. Rerun a stable script and inspect raw errors;
do not cite this attempt as a verified board. Its log is `/private/tmp/gq2-w361-scoreboard.log`.

New arithmetic/general group results have compiled with only the standard three axioms:

- `RamifiedCertificateOddCyclotomicRamification`: actual finite residue action is faithful
  on an odd-root generated extension, hence its filtration ramification index is one.
- `RamifiedCertificateInertiaFixedField`: actual absolute inertia fixes exactly the
  odd-cyclotomic compositum; every relative inertia-fixed element lies in a finite
  `K` compositum with a primitive odd root field.
- `RamifiedCertificateResidueUnitReciprocity` (agent-owned, expanding): base reciprocity
  units fix every odd root and lie in actual inertia, by the finite norm law and `e=1`.
- `ProfiniteOddReflection` and `LocalReciprocityOddReflection`: the natural odd-primary
  inversion / pro-two identity automorphism preserves **all** clauses of the current
  LocalReciprocity bundle, not merely its pro-two coordinate. This is a normalization audit,
  not an assertion that the weaker kernel comparison is unprovable.
- `ProfiniteTwoPrimary`: on every abelian profinite group, the omega-two fixed part is
  detected by the maximal pro-two quotient.
- `ZhatTorsion`: full profinite integers are torsion-free (kernel-checked); the finite-index
  endomorphism injectivity extension is being completed in the same file.

The three agents now have disjoint positive arithmetic tasks: odd_front transports
unit-inertia to the marked character and proves forward tame-inertia containment;
source_audit converts actual-inertia fixed fields into odd-cyclotomic finite containment and
anchored norm values; raw_pairing proves relative odd-cyclotomic ramification one over
arbitrary finite `K`, then equal norm values. Root supplies pure `Zhat` quotient facts and
integration. The hoped-for mechanism is **kernel equality without any signed full Frobenius
normalization**, then the special unramified-field norm argument rather than all relative CFT.
These final consequences are still research targets, not yet claimed theorems.

### General field and presentation closure (11:27 UTC)

The preceding arithmetic frontier is now superseded: the shared field packet and final
all-degree selected flexible assembly have compiled at default limits. The original scope
was checked against `plan.md`: **every finite K/Q2 with K(i)/K ramified**. The restriction
is not new debt. The excluded unramified-i theorem of Diekert is not a Lean target here.

The positive mechanism is kernel equality, not a signed full Frobenius normalization:

1. Base reciprocity units fix odd roots by the existing finite norm law and odd-cyclotomic
   ramification index one. Norm compatibility transports this to the relative marked
   character. Density gives factorization of the actual pro-two residue character by nu.
2. This kills the oriented wild subgroup in actual residue. The tame relation forces tau
   to vanish under any Zhat character by torsion-freeness. A nonzero integer in the image
   of the resulting Zhat endomorphism makes it injective. Thus the actual and full tame
   inertia subgroups agree exactly, with no additional normalization premise.
3. Inertia-fixed elements lie in odd-cyclotomic composita. These have relative ramification
   index one over **arbitrary** finite K. The anchored finite fields therefore have e=1;
   the relative odd-degree tower argument discharges involution norm values in all degrees.
4. `compatibleRamifiedDataAt_of_norm_reciprocity` combines the actual residue lift and
   involution data. It retains the caller's MuN 2 action and has only std3 plus the existing
   `tateDualityAt` dependency. No Hbase, Htame, Hrel, absolute odd-degree or Galois-K premise.

`FieldFamilySpliceSourceComplete` dispatches the completed pair/mobile splice certificates
and inherited L/N/canonical producers to every range-matching selected family. Its final
`HasSelectedFlexibleAssemblyRN` retains the actual source word, full corrected certificate,
marked pro-two core realization, and equivalence for that exact candidate.

`FieldFamilySpliceFinal.hasSelectedFlexibleAssemblyRN_fieldSelectionFromRange B FF T D RI`
is the checked general endpoint. It has **no extra analytic, determinant, phase, mobile-pivot,
or field-packet premise**. In addition to std3 its inherited axioms are exactly:

- `hilbertSymbol_normCriterion_finiteDyadic`
- `peripheralCyclotomicAction`
- `relativeStiefelWhitney_dyadic`
- `tateDualityAt`
- `Foundations.absGalQ2_isTopologicallyFinitelyGenerated`
- `Foundations.absGalQ2_localEulerCharacteristic`

This is not an axiom-free formalization of all local-field theory. B and T remain supplied
standing field bundles in this generic theorem; canonical specialization will use the existing
`localReciprocity`, `markedRecipAt`, and `orientedTameQuotientAt` axioms. The FF/D and topology
inputs are proved constructions, not further axioms. No old frozen M-word claim is made.

`LocalReciprocityNormalizationAudit` also proves, with std3, that a bundle and its odd-reflected
bundle cannot both satisfy the signed full residue law. This explains why the stronger W300
route was blocked while the weaker kernel route succeeds; no new axiom was added.

Independent arithmetic audit is `w361-arithmetic-assembly-audit.md` (being extended to the final
capstone). Latest completed umbrella build is 1,414 modules; the newly registered arithmetic
chain and final capstone still require the next whole-umbrella rebuild. Raw scoreboard rerun
75285 passed without stale umbrella but found four resolver false-missing entries; exact-name
resolution was fixed and must be rechecked. Do not mistake the earlier UNVERIFIED run for a pass.

Minimum overnight horizon remains **17:10 UTC**. Continue audits, integration, documentation,
and useful general-case consolidation; only about 2h17m have elapsed.

### Scope audit and next general target (11:28 UTC)

`FieldFamilySpliceCanonical` is checked and cached. The bare existence theorem takes only a
finite intermediate dyadic field and `RI : RamifiedIData K`, retaining its exact degree, actual
word, corrected certificate, and candidate/Galois continuous group isomorphism. Its footprint
is std3 plus the nine established inputs described above (six generic plus three canonical
bundle constructors). The odd-degree corollary discharges RI by an existing proved theorem.

**Do not yet call the full original marked presentation target complete.** A fresh audit of
`plan.md` §1 against the reconstruction endpoint found a real statement-strength distinction:
`ThmFourTwoRN.nonempty_continuousMulEquiv_of_sourcesRN` first sums fixed-frame counts into
unframed surjection counts and calls plain reconstruction. Its output is an abstract continuous
group isomorphism, with no compatibility equations on that same isomorphism. The carried
source/core/nu data do not by themselves prove that the chosen isomorphism preserves them.
The general certificate and abstract presentation closure above stand; simultaneous preservation
of tame quotient, maximal pro-two marking, orientation and nu is the next audit/proof target.

odd_front_audit owns the reconstruction API search/relative reconstruction extension; root
will investigate the fixed-frame count side. No class-by-class work is planned.

### Tame-marked reconstruction and scalar refinement (11:44 UTC)

The full 1,429-module umbrella rebuild passed, and both the ordinary dyadic gate and the
stable raw scoreboard passed at that state. The scoreboard reports `SCANNED|1429`, no MISSING
or STALE_UMBRELLA entries, and only the intentionally separate AxiomLedger outside the umbrella.
The exact-name resolver fix is therefore verified. Logs:
`/private/tmp/gq2-w361-gate-final.log`, `/private/tmp/gq2-w361-scoreboard-final-raw.log`.

The marking audit led to a genuine strengthening, now kernel-checked at default limits:

- `MarkedReconstruction`: general allowed-subset finite-quotient compactness, exact relative
  surjection assembly, and relative Hopfian reconstruction. Three std3 audits. Independent
  recheck confirms no unjustified surjectivity of transition maps or boundary maps is used.
- `TameMarkedFiniteLifts`: use the **actual wild image** in each finite quotient, rather than
  summing away the induced tame frame. A positive exact-image count produces a quotient map
  with simultaneous representatives for the finite image and exact tame coordinate.
- `TameMarkedReconstruction`: one reconstructed isomorphism preserves the actual tame map
  and therefore the full Ztwo unramified character. Both theorems std3.
- `FieldFamilySpliceTameFinal` and `FieldFamilySpliceTameCanonical`: the actual all-degree
  selected and bare finite-K+RI field endpoints now retain these exact equations on the SAME
  equivalence. The inherited axiom baseline is unchanged. The source word/certificate remain
  explicit and changed M words are not identified with the frozen ones.
- `ScalarMarkedFiniteLifts` / `ScalarMarkedReconstruction`: a finite elementary core decoration
  is retained at the same time as tame. Refine a target quotient by the scalar kernel first.
- `ElementaryMarkedReconstruction`: finite generation makes the set of F2-valued core
  characters finite, so their joint evaluation retains ALL elementary characters on ONE
  equivalence. This still does not fix higher Frattini coordinates.
- `SourceBoundaryMarkingRN` and `FieldFamilyFlexibleMarkedBoundary`: the induced common-core
  automorphism is explicit. Tame compatibility makes it nu-preserving. Equality of the
  prescribed core maps is equivalent to that automorphism being identity; this is not assumed.

Still separate: the prescribed full pro-two boundary square and cyclotomic compatibility.
The fixed-frame record contains elementary scalar decoration, not arbitrary nonabelian
pro-two decoration. The raw-pairing lane has proved a promising general structural lemma:
`MinimalBlock.le_ker_of_isPGroup` and `le_proPKernel` show every nonscalar minimal wild block
is killed by every map to a two-group. It is developing refined decorated recursion; aggregate
count equality alone is NOT being treated as equality of individual refined fibers.

Orientation audit found an existing all-rank M characteristic-orientation theorem, superseding
the older boundary-only warning. The source-audit lane is generalizing the master crossed-
derivation argument to the N and L structural families. This is a uniform family proof, not a
return to nilpotency-class-by-class arguments. No full cyclotomic conclusion is claimed yet.

Newly registered marked modules require the next umbrella build. No new axiom, placeholder,
option, commit, or push. Minimum horizon remains 17:10 UTC (about 5h26m remain).

### Fully marked general existence and public entry point (12:08 UTC)

The marking gap identified at 11:28 is now closed for the actual existential field theorem.
The generic relative reconstruction remains unchanged; the new argument calibrates only the
existential core realization and proves that full cyclotomic orientation survives calibration.

- `FieldFamilySpliceAlignedFinal` keeps the word, core, nu and certificate definitionally
  fixed, replacing only the realization by that induced by the tame/nu-compatible equivalence.
  This yields the literal pro-two and maximal-pro-two squares. It does NOT preserve an
  arbitrary previously fixed realization pointwise.
- `CharacteristicCharacter` and `OrientationMasterTransport` package the uniform master
  derivation argument. New `NOrientationCharacteristic` and `SqOrientationCharacteristic`,
  together with the existing all-rank M theorem, prove characteristic orientation on every
  selected core. `FieldCyclotomicCharacteristic` transports it to the actual field group.
- `FieldFamilySpliceMarkedFinal.AlignedMarkedFieldEquiv` includes all equations on ONE
  equivalence and explicitly retains the ORIGINAL core character chosen before reconstruction.
  The cyclotomic conclusion is not merely a post-hoc definition by pulling back along e.
- `FieldFamilySpliceMarkedCanonical.exists_certifiedFullyMarkedFlexiblePresentation_ramifiedI`
  takes only finite K and RI, and returns an actual certified source at EXACT field degree,
  the new existential realization, and tame/pro-two/maximal-pro-two/cyclotomic/full-nu equations.
  It has std3 plus the same nine inherited arithmetic/foundation axioms (12 total), not new
  assumptions. The supplied-bundle endpoint has std3 plus six (9 total).
- `GQ2/Dyadic/GeneralMain.lean` is the new public entry point, exporting these canonical
  theorems while leaving historical frozen-table `Main.lean` untouched. It compiles at default
  limits and its axiom prints match those above.

Independent final packaging probes pass. See `w361-aligned-marking-audit.md`. The generic
reconstruction was re-audited: finite allowed subsets at every open normal quotient, closed
fiber compactness and mutual Hopfian surjections suffice; no surjectivity of transition maps
or boundary maps was silently assumed.

Latest completed shared-cache umbrella: **1,448 modules**, before the final two modules and
GeneralMain. A new umbrella build is running (session 37105). The prior 1,429-module gate and
scoreboard passes remain valid for their recorded snapshot, not yet the new public endpoint.

A **source-only fresh build** began at 11:52 UTC using the durable
`scripts/w361_fresh_build.py`: 1,448 local modules, ZERO pre-existing GQ2 artifacts reused,
exact matching dependency manifest and default Lean options. Snapshot and provenance:
`/private/tmp/gq2-w361-fresh-dl5f62fk`; log `/private/tmp/gq2-w361-fresh-build.log`;
session 52617. It is still running (over 400 modules checked). Do not claim its completion or
coverage of later modules until explicitly verified.

Remaining consolidation is real, not a hidden proof premise: (1) expose exact selected-word
constructor information currently forgotten by existential packaging; (2) stage a symbolic
one-tree export for arbitrary Ztwo parameters without modifying frozen S1.1 fixtures;
(3) refresh current trust-boundary and completion documentation; (4) complete clean build,
gate and scoreboard verification. Agent odd owns (1), raw owns (2), source owns (3), root (4).
The old hash gate covers only the five old fixtures; it does NOT certify the new splice words.
Full arbitrary MC-N stabilizer lifting remains a stronger historical conditional lemma, not
a premise of the now-proved presentation. No owner sign-off or selection-freeze migration is
being manufactured. Minimum overnight horizon remains **17:10 UTC**.

### Exact word provenance and explicit acceptance artifacts (12:40 UTC)

The selected-word information is now retained in the final fully marked record:
`SelectedWordProfile` distinguishes the exact canonical, pair-splice, and arbitrary-unit
mobile constructors, and `SelectedWordMarkedFieldData` carries that profile with its
certificate and every marking equation. The mobile profile includes its actual unit and
the congruence to the selected eta. Calibration keeps the literal word, core, and nu fixed.
`GeneralMain` exports the bare K+RI endpoint with this stronger record. The exact-footprint
audit `scripts/w361_general_axiom_audit.lean` passes all 12 pins, with unchanged nine-total
generic and twelve-total canonical footprints.

Completed shared-cache umbrella before the artifact integration: **1,453 modules**.
The full gate including axiom ledger passed at the preceding 1,451-module state, recording
49,450 declarations, zero sorryAx, zero UNKNOWN axioms, and zero terminal violations
(`/private/tmp/gq2-w361-gate-1451-ledger.log`). The raw scoreboard also passed at that state;
the two newer selected-word modules were then outside its snapshot and are now registered.
These snapshot distinctions are intentional, not a claim that an older gate covers new code.

The checked additive artifact work now includes:

- Four ordinary `GeneralTemplate*` library leaves: typed symbolic exponents, exact actual-word
  denotation bridges, and integer/finite evaluation agreement for every valid pinned level.
  The separate export driver has `main` and is intentionally not imported by the umbrella.
- Four staged JSON/TeX/provenance artifacts. Root independently repeated all **37** tooling
  tests and strong fresh-Lean replay of all four artifacts. The template hash does not bind
  q, nu, eta, shear coefficients or correction values; formal binding bridges remain essential.
  No frozen exporter, five-fixture manifest or word table was changed.
- `SigmaNormalFoxElimination`, `SigmaNormalFoxRows`, `SigmaNormalSpliceFox`, and
  `TameSpliceFoxNormal`: explicit invertible triangular row operations and actual pair/mobile
  all-cochain identities with identity pivots at tau and x2. The actual changed word supplies
  its own tau column. No raw-relator-death premise or kernel-to-matrix shortcut is introduced.
- `WordPhasePolarNormal`: the literal block-diagonal polar matrix of the common phase,
  with explicit inverse and a proof that it represents the actual polarization, in every rank.

All mathematical artifact pins use at most std3 and default limits. The 1,462-module umbrella
integration is running. A separate ramified Fox column/row elimination is in progress.
Independent endpoint and matrix audits have been assigned without shared code edits.

The source audit verified AX3/AX4 against the actual Serre and NSW texts. Root additionally
visually checked the norm/inclusion diagrams, unit-to-inertia corollary, uniformizer formula,
and tame relation pages. Reciprocity remains arithmetic; sigma is its inverse Frobenius
convention. The old AX3 proposal's uniform `1+8 Z2` inertia claim is too strong in general;
it is not an axiom field or a dependency of the new theorem. The staged proof-packet amendment
records the correction and does not alter owner-approved artifacts or discharge inherited axioms.

The source-only **1,448-module build PASSED**, taking 2,914.7 seconds (48.6 minutes), with
zero failed or unbuilt modules. Its frozen snapshot predates the final marked/profile/artifact
leaves. The shared-cache 1,462-module integration also passed. A fresh latest-source verification
must follow. Minimum overnight horizon remains **17:10 UTC**; about 4h30m remain.

### Literal original markings and all coefficient sectors (13:17 UTC)

`FieldFamilySpliceOriginalMarked` and `GeneralMain` now retain the ORIGINAL selected
branch, its exact word profile, the certificate, and the aligned field equivalence in one
statement. This is stronger bookkeeping than retaining only the newly calibrated branch's
character. The bare K+RI theorem has the same twelve-total axiom footprint; the supplied
compatible bundle theorem has nine total. The 16-pin exact-footprint audit passed.

Every changed-source Fox sector is explicit: scalar `(x_tau,x_tau)`, unramified
`(S^-1 x_tau, x_tau+(1-S^-1)x2)`, and the projected ramified tame row together with
`-S^-1 x2`. The actual-splice tau-column theorem closes the previous opaque-column seam.
Finite action-polynomial inverse formulas are proved for both nonscalar pivots, with
operator order retained in the noncommuting ramified case. Actual pair/mobile phase
comparisons are proved additive, so the common full-rank polar matrix and inverse now
apply to the original source coordinates, not just a set-theoretic comparison.

`TameSpliceFoxCertificates` additionally packages all six pair/mobile sector results in
the ORIGINAL `FoxCertificate` API, with literal words, markings, and pinned resolvers.
These records use the old fixed formal operation lists and targets. The stronger full
identity-pivot operations remain separate checked lemmas. All **59** artifact audit pins
passed with at most standard three axioms. Shared-cache **1,473-module umbrella PASS**.

Full gate including ledger passed at the preceding 1,465-module state: **49,772 tracked
declarations**, zero sorryAx/UNKNOWN/terminal violations. This does not yet cover later
modules. Latest source-only build is still running on a frozen **1,472-module** snapshot
(`/private/tmp/gq2-w361-fresh-1472.log`, session 41078). It predates the original Fox-record
leaf and the corresponding umbrella import. Do not call it a live-worktree clean build.

Independent tooling audit first verified all 1,448 imports in the earlier clean build
against Lean's actual dependency parser. It then found valid header syntaxes the original
custom parser could miss; the durable driver now uses Lean `--deps` and only manifest-declared
dependency roots. Negative tests covered parser syntax, missing imports, compile errors,
cycles, contamination, bad manifests, and live drift. A further fake-executable test showed
why compiler success alone was insufficient: the driver now checks the pinned version,
records the executable hash, and demands nonempty .olean/.ilean outputs. The revised
real-Lean smoke build passes with zero drift. The full in-flight build used the actual
pinned Lean but predates this last defensive driver change; final full verification must
use the hardened revision.

Publication work is not being confused with mathematical proof: all five OLD generated
appendices contain eight placeholder invocations each (40 total). The new parametric
pair/mobile ten-item appendix is hand-authored, not a synchronized generated artifact or
owner-approved format. Original Hessian-record packaging and generic legacy L/N tree
bridges are active bounded tasks. L's existing wild-row certificate also lacks a named
full two-row wrapper; that wrapper is being added separately. No new nilpotency-class
casework is planned. The requested minimum horizon remains **17:10 UTC**.

### Original certificate records and actual N diagonals (13:44 UTC)

Shared-cache **1,484-module umbrella PASS**; the **134-pin artifact audit PASS** uses
only standard logical axioms. This snapshot includes full original Fox records with
identity pivots, literal finite polynomials in the unchanged coefficient grammar, all-rank
L two-row Fox certificates, and general denotation bridges for legacy L/N0/Npc trees.
No frozen word factory or hash manifest was changed.

Original `HessianCertificate`/`PhaseCoverCertificate` records now exist for actual pair/mobile
sources in both nonscalar sectors. The very same source comparison is proved additive and
then F2-linear; its cardinality is derived internally. The entire quadratic phase survives,
not just its polarization. Generic arbitrary-diagonal wall records similarly retain d0.

For procyclic N the new `NpcPhaseAdditiveNormal`, `NpcPhaseAdditiveHead`, and
`NpcHessianCertificates` modules prove additivity and original records at the actual
projected heads, with the original full-offset diagonal and lift-level resolver. Independent
fresh compilation and all eight public axiom checks passed. No inverse-Lc or x2=0 slice
was substituted. A branch-free boundary-record adapter is in progress; the original final
affine determinant theorem was already branch-free and is unchanged.

Two further modules are checked/cached after the 1,484 build: `CompactNHessianCertificates`
has both actual compact-N original records and same-map additivity, all ranks, four std3
pins; `WordPhaseWallHandlePolarInverse` has the canonical arbitrary-diagonal polar operator,
its explicit inverse, and both literal head-matrix products, 23 pins at most std3. Its diagonal
adjoint is derived from finite nonsingular duality, not introduced as an extra hypothesis.
Their imports and audit pins are registered; combined verification is pending.

The weaker `NScalingHypothesis` is now proved directly from the existing SL2 move, uniformly.
The stronger historical simultaneous plane-scaling claim remains distinct and conditional.
The naive B8 handle-scaling candidate violates fixed character rows when kappa is not one;
that candidate obstruction does not refute all possible simultaneous automorphisms. Neither
scaling binder is needed by the completed selected presentation.

The 1,472-module isolated build is still progressing (over 1,170 modules checked). Its
snapshot predates these newest leaves. Active work: original odd-head L records, branch-free
Npc record packaging, updated ten-item parametric appendix, and final hardened fresh-source
verification. The minimum overnight horizon remains **17:10 UTC**, not yet reached.

### All original boundary records and typed certificate exports (14:25 UTC)

The original Hessian/phase-cover packaging is now complete at every relevant actual
boundary for L, N0, Npc, pair, and mobile sources. L retains q=2^f with odd f and
the exact negative/unramified and positive/ramified signs. Npc retains its actual
full-offset diagonal; the old inverse-Lc slice is not substituted. These additions
package the existing uniform proofs, not new nilpotency-class casework.

Shared-cache **1,499-module umbrella PASS** and **279-pin artifact axiom audit PASS**.
The latter permits only Lean's standard three logical axioms. The full 1,492-state
gate with ledger passed with **50,072 tracked declarations**, zero sorryAx/UNKNOWN
or terminal violations, and unchanged Q2 capstone footprints. Its raw scoreboard
also passed; a latest-tree repetition is still required. The source-only 1,472 build
passed in 48.2 minutes with zero failed/unbuilt modules; only GQ2 drifted afterward.
The fully hardened 1,492 snapshot build is still running, now past 1,190 modules.
None of these earlier snapshots is being relabelled as the final moving worktree.

New typed Lean trees export the full Fox input rows, ordered operations, carried
inverse polynomials and targets; the complete quadratic phase/polar matrices;
and the original cover's embeddings, diagonal, base dimension and sign. Six exact
input-binding lemmas identify the Fox input with each actual source Jacobian.
Uniform bridges identify the exported data with the original certificate records.
The phase-cover tree is cross-bound to the exact phase hash and tree.

Four **STAGED ten-item composite packets now generate** in
`generated/general-certificate-staged/`. Independent runtime mutation audit passed
32 checks, including strong-replay rejection of coherently rehashed forged word,
Fox, phase and cover trees and forged declaration transcripts. The four helpers
passed 37/81/44/51 self-tests; an additional durable packet suite passes 29 tests.
Two prose-scope clarifications are fixed. PDF QA found four overflowing expanded
word lines; exact bounded subtree abbreviations are being added without changing
the word AST or its hash. No final PDF quality or accepted publication status is
claimed yet. The five old appendix skeletons and their 40 TODO invocations remain
unchanged. The new packet is not their silent replacement or a release gate.

The general N-plane investigation has a new exact central-defect absorption lemma:
the torsion-head letter can absorb every odd plane determinant when the selected
commutator is central, invisibly to all characters. This is NOT a full DN
automorphism or a proof of `NPlaneScalingHypothesis`. A twisted Alexander-module
interpolation route is being investigated with the group-lifting gap explicit.
The completed changed-word presentation does not require this stronger theorem.

The overnight minimum remains **17:10 UTC**. Work continues on synchronized
publication, independent scope review, general scaling research, and final-source
verification. No owner approval, commit, push, census or release action has occurred.

### Hardened build and printable exact words (14:35 UTC)

The hardened source-only **1,492-module build PASSED**, 2,396.4 seconds
(39.9 minutes), zero failed/unbuilt modules, zero reused local artifacts.
Snapshot: `/private/tmp/gq2-w361-fresh-5pyyouae`; metadata records pinned compiler
version/hash, source and output hashes, and actual Lean dependency parsing.
The only subsequent source drift in its closure is `GQ2`; the manifest matches.
This proves that frozen collection, not newer unimported leaves or an atomic
filesystem snapshot. Manifest-matching external dependency artifacts are reused.

The shared latest **1,501-module umbrella** and **300-pin artifact audit** also
pass. The additional 21 standard-three pins construct the central N correction
and a concrete two-evaluation integral skew-pairing isometry fixing all handles.
The latter is NOT yet identified with the DN Alexander module or lifted to a
group automorphism. The stronger N-plane question remains open.

The word renderer now constructs a strictly backward-reference abbreviation DAG.
Every displayed definition has at most 11 visible AST/reference nodes; exact
expansion is checked against the hashed tree. All **142** renderer tests and
fresh Lean replay of all four unchanged word hashes pass. The staged review PDF
now compiles to 29 pages with no overfull/underfull boxes; root has visually
checked pages 1–14 and the independent reviewer is checking 15–29. Final PDF
delivery status awaits that inspection. A read-only, opt-in
`scripts/w361_check_staged.sh` consolidates tests, audits and strong replay; it
does not alter the existing release gate.

### General N intermediates and complete local output inventory (14:58 UTC)

The latest shared umbrella is **1,504 modules, PASS**; the selected artifact
audit is **335 pins, PASS**, all at most standard-three. `NPlanePowerSeries`
constructs an actual continuous involution on Z2[[X]] and an all-rank skew-unitary
linear automorphism with the desired constant-term plane scale and every handle
fixed. `NPlaneRelativeBoundary` isolates the exact nonlinear relation that an
actual group lift must preserve. Neither asserts an Alexander-module/pairing
identification or a DN automorphism. Deck/orientation inversion conventions must
be retained when making any such future identification.

An independent primary-source audit found no directly applicable simultaneous
integral-row lifting theorem: the checked classification results leave those rows
uncontrolled, and the closest peripheral scaling result assumes odd p. Raw and
the independent reviewer now agree on a uniform mixed-Lie correction-kernel
formula that could remove ordinary row changes from Labute's corrections.
This is a general algebraic route, not a nilpotency-class search. A bounded
abstract Lean identity and a free-pro-2 IA shear lemma are in progress; filtered
representatives and convergence are still genuine obligations for the strong
N statement. The completed changed-source presentation remains unaffected.

L/N word synchronization now has a separate staged exporter. Eight new canonical
denotation bridges retain the exact original semantic words after the unchanged
S1.1 rational canonicalization. Six durable L/N examples, including 3/9 and -3/9,
pass strong replay; helper39 self-tests and52 independent checks pass. This closes
the word-tree/hash seam, not the remaining full L/N ten-item appendix contract.

The full1,501-state gate+ledger passed with **50,530 tracked declarations** and
no sorryAx/unknown/terminal violations. The1,504-state staged suite (word142,
Fox81,phase44,cover51,LN39,packet29, exact footprint16, artifact335, strong replays)
has passed; fresh-verifier unit coverage is now38 tests, separately checked.

Independent provenance audit found that Lean's module system also loads
`.olean.private`, `.olean.server` and `.ir` companions. The fresh builder now hashes
all local outputs immediately per module, then rechecks their complete final
inventory; the verifier also binds every index/companion byte before and after
replay. Earlier source-only builds remain valid observed build results, but their
recorded output hashes cover primary .olean files only. They are not retroactively
called complete-inventory attestations. Real legacy and module-system smoke builds
pass the new contract. The verifier also pins the exact runner compiler, requires
the current reviewed producer hash, and forbids report output inside checked trees.
Final full-source verification will use this strengthened, independently tested
revision. Minimum overnight horizon remains **17:10 UTC**.
## 15:12 UTC — exact-row N compactness and correction interfaces

Added and checked `NPlaneCompactness.lean`: the strong N-plane hypothesis is
now proved equivalent to nonemptiness of explicit exact-row upstairs stage
sets at every depth. Nested closed-set compactness, filtration separation,
Frattini generation, and Hopfian promotion give the actual DN automorphism.
All twelve pins are standard-three and default-limit. This closes the
conditional limit step, not the uniform stage supply.

Integrated the stable free-pro-two commutator shear (9 pins), exact coordinate
removal (10), abstract mixed-Lie kernel vector (10), and generic additive
character filtration arithmetic (5). The coordinate theorem really removes
all ordinary character rows at once while preserving the selected filtration
class, given the stated extra divisibility. Its commutative-target corollary
also preserves orientation. The mixed-Lie module retains the exceptional
degree-one square term and allows coincident slots, but its concrete filtered
group instantiation is still open: true mixed squaring is not globally additive
on degree one. No implicit substitution of that operation for a global additive
endomorphism is licensed.

The agents are now attempting bounded general group-level bridges: initial
unit-power substitution, concrete mixed-power congruences, and exact head-row
divisibility under a relator correction. No class-by-class sweep is underway.
The final source-only rebuild has not yet started; the added leaves are being
integrated and audited first.

## 15:46 UTC — actual arbitrary-rank correction kernel and finite rows

The earlier abstract mixed-Lie obstacle now has a concrete group-level route:
`MixedPowerCongruence`, `NPlaneMixedGroupKernel`, and
`NPlaneKernelTupleDerivative` prove the uniform mixed-power identity and actual
five-factor cancellation in the lower two-central quotient. No globally additive
degree-one square operation is assumed. The explicit kernel tuples preserve the
literal full N relator at the required next depth, including arbitrary handles
and coincident correction slots.

`NPlaneCorrectionKernel` packages the actual derivative kernel as a closed
subgroup of the tuple group and proves right multiplication preserves any current
next-level defect. `NPlaneKernelDiagonal` retains the current marking's diagonal
unit weights instead of substituting literal-generator coordinates. The finite
interpolation in `ProTwoRowCorrection` permits zero scales for excluded rows and
constructs its enumeration for any finite row family. These additions have
independent default-limit, warning-free checks with standard-three footprints.
Shared umbrella1,524 and artifact audit482 pass. The newly proved pro-p product
helper and final relative-row adapter are being integrated next.

The actual crossed defect already vanishes for every canonical-orientation
crossed derivation; this is proved, not an extra assumption. The major remaining
mathematical problem is arbitrary-rank unrestricted orientation-kernel stage
reachability. Existing rank-three L span results are not an instantiation of it.
Kernel flexibility cannot establish nonemptiness of an arbitrary derivative
fiber. The completed selected field theorem remains independent of strong N
scaling, with its exact ramified-i scope and baseline footprint unchanged.

The staged29-page certificate PDF is fully visually checked. Six legacy L/N
word displays also have canonicalization/denotation and strong replay; they do
not constitute full L/N ten-item packets. Publication notes now distinguish
the new synchronized pair/mobile packet from the historical word-only export.
Final fixed-tree source compilation and content-inventory replay remain pending.

## 16:20 UTC — unconditional arbitrary-rank strong N scaling

The earlier image-gap diagnosis was based on an incomplete inventory. The older
`evenDeriv_mem_rawShiftSpan_of_forall_derivKer` is genuinely arbitrary-rank and
accepts an independently supplied central class. A constant-one auxiliary word
packages the actual free basis without assuming its N relator is one. Explicit
finite crossed coordinate maps on that moving basis kill both actual relators,
so the target-relative error lies in the actual derivative image. This gives
ambient corrections at every depth, with no row or orientation premise on them.

The kernel tuple now includes v=b: its two additional commutator factors are
exactly trivial in that case. Full-row interpolation therefore removes every
ordinary coordinate, restoring orientation as a consequence. The head's extra
digit comes from the actual improved error, and the literal target is preserved.
Free-basis persistence, quotient transport and nested compactness complete the
induction. `nPlaneScalingHypothesis_general` has only `2 <= alpha`, with arbitrary
handle rank. Its GL2 and admissible stabilizer corollaries have no supply premise.

All five new modules/26 pins passed independent, isolated scratch compilation
and full proof review. Production-name copies also compile, standard-three only.
They are deliberately not yet banked: the frozen 1,531-module build is still
running, and its content-inventory replay must finish before source integration.
The next source snapshot will be separately labelled; the older 504-pin result
cannot certify these new declarations. No new axiom or option was introduced.

Exact scope still matters: the new `nStabParam_lift_general` controls every
ordinary Z2-character frame, not the torsion-sensitive `P.rows` components.
The original packet's full abelianization lift is stronger. The completed
selected field theorem needs only the already-supplied marked consumer, so this
distinction is not a missing premise of that endpoint. Read the new independent
`w361-n-general-scaling-audit.md` and the updated stage-gap/sanity notes.

## 16:50 UTC — full torsion-sensitive N core lift and final source freeze

The remaining core torsion entries are now proved, not merely planned.
`DNAutomorphismCup` transports the actual N presentation through any continuous
automorphism and compares the injective H2-to-F2 obstruction maps. This proves
cup invariance uniformly in alpha >= 2 and all handle ranks, with no orientation
premise. `NStabilizerFullRows` uses actual torsion and ordinary characters to
recover the torsion head, both coupled plane entries and every handle torsion
entry. Exact N1 precomposition then adjusts the one free entry without changing
the other images or any ordinary row.

`nStabParam_fullFrame_lift_general` returns one chi-preserving continuous DN
automorphism with every prescribed literal canonical abelianization coordinate,
including torsion and identity handle columns. It has no remaining stage,
scaling, cup, matrix or torsion premise beyond alpha >= 2 and P.Admissible.
This closes the distinguished core-parameter family, not every arbitrary
handle-mixing stabilizer in the original specification. The independent full
proof and production-source comparison are in
`w361-n-full-row-independent-audit.md`.

Ten new modules/69 standard-three pins are integrated. Shared umbrella1,541,
artifact audit573, ordinary gate+ledger50,854 declarations and the corrected
raw scoreboard all PASS. The earlier isolated1,531-module build also completed
and passed its full content-bound staged replay before any new source was banked.
The final zero-local-reuse1,541-module build began at16:45UTC with sources frozen.
Its exact provenance, pending replay and assurance limits are recorded in
`w361-final-verification.md`. Do not call it finished until it actually completes.

The eight-hour minimum remains17:10UTC; verification may safely extend beyond it.
No commit, push, source-word replacement under an old identifier, owner acceptance,
new axiom, proof placeholder or resource-option change has occurred.

## 17:07 UTC — frozen verification and next-general-case handoff

The final isolated build is past halfway with no reported failure. The source
freeze is intact. Independent review of six principal handoff/scope documents
found no stronger RI, frozen-M, fixed-realization or arbitrary handle-mixing
claim. Historical exporter/PDF status statements and one log-path typo were
corrected; current and historical build evidence remain explicitly separated.

A bounded read-only assessment of the broader handle-mixing question produced
a concrete PROPOSED continuation in `w361-n-plane-unrestricted-stage-gap.md`.
Actual inverse free-basis coordinates give A B = I; finite ordered powers of
the known closed-kernel witnesses should therefore remove the diagonal-unit
restriction on row interpolation. The remaining packages are an arbitrary
integral matrix's free-basis/initial-depth realization, that row-refinement
generalization, and full-coordinate compactness/transfer. None is asserted as
an implemented theorem in this snapshot.

Independent review confirmed the important variance convention: with generator
images as columns, cup preservation is A G A-transpose = G, not the reversed
formula. The actual N1 shear gives a concrete counterexample to the reversed
convention. Exact orientation, rather than preservation of its image alone,
is required; no extra condition fixing nu should be imposed. This route seeks
one uniform degree-two calculation followed by all-depth induction, not a new
nilpotency-class enumeration. All agents have completed their bounded lanes;
root continues through the eight-hour horizon and the final clean replay.

## 17:30 UTC — verified overnight checkpoint; heartbeat paused

The requested window began at 09:10 UTC and the eight-hour minimum was reached
at 17:10 UTC. Work continued through the final isolated build and replay.
The complete 1,541-module build passed in 2,414.159 seconds, with zero local
artifact reuse, 3,679 inventoried outputs, no failures/unbuilt modules, and no
source/manifest/output drift. Snapshot: `/private/tmp/gq2-w361-fresh-egoma1il`.

The full source-bound replay passed from 17:26:09 to 17:29:11 UTC: 16 headline
pins, 573 artifact pins, all component tests and all strong staged certificate
replays. The direct fresh-root ledger passed with 50,854 tracked declarations
and zero sorry dependencies, unknown nonstandard axioms or terminal violations.
An independent reviewer rehashed all sources and outputs after replay, compared
the entire report state, and verified all 21 replay-source files and 62 staged
files against current bytes. No mismatch was found.

The exact report is retained in `w361-final-verification-report.json`, SHA-256
`bb20e9914dd86be093521808b0267f8ac0f6cd857fe6e13b8285d8213784abcb`.
See `w361-final-verification.md` for hashes, logs and precise assurance limits,
and `w361-restart-handoff.md` for the proved endpoints and remaining work.
This final report includes the ten new strong-N/full-core modules, unlike the
historical 1,531-module conditional snapshot.

Heartbeat `overnight-dyadic-general-case-research` was paused through the app
tool at 17:30 UTC, preserving its other fields. Every proof/audit lane and
build is complete. The 29-page staged PDF is visually checked and byte-stable.
No commit, push, deletion, new axiom, proof placeholder, option override, frozen
word replacement or owner acceptance occurred. The branch/HEAD are unchanged.
The general field endpoint and full torsion-sensitive N core-family lift are
proved at their stated scope; broader handle-mixing stabilizers and publication
adoption remain distinct unfinished work. No class-by-class campaign is the
next step.

## Later user-requested hard-scaffolding / Claude Code handoff pass

The user reported 26% remaining usage and requested the hardest scaffolding
followed by a Claude Code handoff. This superseded further autonomous overnight
research; the heartbeat remained paused.

The proposed arbitrary-handle N continuation was fully implemented: eleven
new modules, 118 new public standard-three pins, culminating in
`GQ2.Dyadic.MarkedCore.nFullStabilizer_lift_iff`. It gives the exact image of
orientation-preserving DN automorphisms on the full abelian frame: precisely
the actual orientation/cup-preserving frame automorphisms. Every torsion and
handle coordinate is retained, with an all-element commuting square. Initial
free-basis construction, actual lambda-three error, arbitrary-basis kernel
interpolation, all-depth exact rows and full-frame compactness are supplied.
The mathematical full N lifting obligation is closed; the prescribed finite
Nielsen-list proof method remains distinct. M is not claimed closed.

All new proofs were independently reviewed and recompiled at default limits.
The clean 1,552-module build passed with zero local artifact reuse and 3,701
inventoried outputs. Complete staged replay passed at 22:53:05 UTC, including
16 headline and 691 artifact pins, all component tests and strong Lean replays.
The isolated ledger passed: 50,991 tracked declarations, no sorry dependencies,
unknown nonstandard axioms or terminal violations. No source/manifest/output
drift occurred. The old 1,541-module report was preserved as historical evidence.

Current instructions and exact verification record:
`w361-claude-code-handoff.md` and
`w361-claude-code-verification-report.json`. A precise next general M task is
mapped in `w361-m-next-general-scaffold.md`, including coupled head cleanup
and the primitive torsion-basis issue. No proof placeholder, new axiom,
resource override, commit, push, release, frozen-word replacement or owner
acceptance was introduced. Last usage reading: 20% remaining.

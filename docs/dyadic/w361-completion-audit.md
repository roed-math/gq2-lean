# W361 completion audit: mathematical endpoint versus campaign acceptance

Snapshot: 2026-09-17, 12:00 UTC, with the subsequent additive trust-boundary refresh
noted below. Read-only audit of the implementation and the campaign specification;
this note is the only file created by this audit. The parent separately authorized
the additive update to `literature-axioms-dyadic.md`. Neither change amends an owner
ruling, the frozen word table, or the proof packet.

**15:44 UTC additive status refresh:** the preferred exact-source endpoint is
`GQ2.Dyadic.hasSelectedOriginalMarkedWordPresentationRN_ramifiedI`; its canonical
footprint is standard three plus nine standing inputs, unchanged by the optional
strong N research. Four synchronized staged ten-item pair/mobile packets and a
fully visually checked 29-page PDF now exist. Six legacy L/N word-only specimens
also pass strong replay. Neither artifact set is owner-approved. Earlier build
counts and skipped-ledger statements below are historical: later gates have run
with the ledger enabled; a final hardened source-only build/replay will be recorded
in the restart handoff. Do not mistake any older snapshot for the final live tree.

**16:47 UTC mathematical update:** strong N-plane scaling and GL2 lifting are
now proved uniformly. `nStabParam_fullFrame_lift_general` also realizes all
prescribed core stabilizer coordinates, including torsion, with identity handle
columns, at every alpha >= 2 and handle rank. No supply/scaling/torsion premise
remains. See `w361-n-general-scaling-audit.md` and
`w361-n-full-row-independent-audit.md`. Arbitrary handle-mixing stabilizers are
still a broader original-specification obligation; the field endpoint does not
depend on them. The final1,541-module source-bound verification is tracked in
`w361-final-verification.md`, separately from all earlier snapshots.

## 1. Verdict and exact scope

**Final successor verification:** the new full-N increment is included in the
clean 1,552-module / 691-artifact-pin checkpoint, with complete staged replay
PASS at 22:53:05 UTC and an isolated 50,991-declaration ledger with zero gaps
or unknown axioms. See `w361-claude-code-handoff.md` and its separate report.
This does not alter the historical 1,541-module verification record.

**18:55 UTC mathematical update:** the full arbitrary-handle N stabilizer
assertion is now proved by `nFullStabilizer_lift` and its converse
`nFullStabilizer_lift_iff`. They lift every actual continuous full-frame
automorphism preserving the actual orientation and full mod-two cup form,
with an all-element torsion-sensitive abelianization square. The proof is
uniform in rank and uses only the standard three logical axioms. It does not
exhibit the finite Nielsen-generator list prescribed as a proof method in the
old packet. [W366 2026-09-18: that last sentence is now superseded twice over.
The rank-four finite Nielsen-family lists exist for **both** cores
(`mNielsenGen_finite_list`, `mNielsenGen_stabilizer_induced`,
`nNielsen_factorization`, `nNielsenFac_finite_list`,
`nNielsenFac_stabilizer_induced`), and on 2026-09-18 the owner accepted Option A
of `w364-proof-packet-amendment-mc.md`: the uniform filtered-correction and
compactness method satisfies the packet's completion criterion for MC-M and
MC-N, and the lists satisfy the section-14 sentence in the families reading.
**Both MC rows of the packet are amended to "Discharged"**, with the two scope
statements carried into the rows: the lists are rank four (`h = 0`) while the
lifting halves are general in `h`, and "finite list" means finitely many
parameterized families, not a finite generating set, which does not exist. This
closes the MC half of the acceptance gap only; the WC, publication and release
items below are untouched by it.] Read `w361-n-full-stabilizer-scope.md`; current integration evidence
is kept separately in `w361-claude-code-handoff.md`. Earlier statements that
arbitrary N handle mixing remained unproved describe the earlier checkpoint.

The general **existential, fully marked presentation theorem for finite dyadic
fields in the ramified-`i` scope is now proved for the actual carried source
words**, relative to the established field-theoretic axiom baseline. The new
source construction is uniform in rank and parameters. No additional analytic,
phase, determinant, pivot-placement, shared-field-packet, or marking hypothesis
is left in the bare field endpoint.

This does **not** prove the original frozen M-word claim. [W362: the M full stabilizer lifting IS now proved, `mFullStabilizer_lift_iff`, std-3, alpha >= 2, all h; the frozen M-WORD placement claim remains false and is a different statement; see the section 3 MC-M row annotation.] It also does not yet
satisfy every publication/merge acceptance item in
[plan §§0–7](plan.md), the
[proof packet](refs/dyadic-presentations-formalization-proof.tex), and the
[acceptance ledger](refs/dyadic-presentations-formalization-ledger.md). The
specification must distinguish the corrected source interface and changed words;
the new words now have staged synchronized ten-item packets, but their display
contract and publication adoption remain unapproved, and complete L/N publication
treatment remains outstanding. The stronger full stabilizer-lifting statements
must not be certified merely because the actual marking-correction consumers close.

The scope is exactly the original campaign scope: finite `K/ℚ₂` with
`RI : RamifiedIData K`, expressing the ramified quadratic `K(i)/K` situation.
It is **not** a theorem for every finite dyadic field without this hypothesis.
Fields containing `i`, and fields for which `K(i)/K` is unramified, are outside
this campaign's stated target. The odd-degree corollary supplies `RI` by an
existing theorem; it does not impose an odd-degree restriction on the main result.

## 2. Current mathematical endpoints

The most direct field-facing statement is
`FieldFamilySpliceMarkedCanonical.exists_certifiedFullyMarkedFlexiblePresentation_ramifiedI`
in [FieldFamilySpliceMarkedCanonical.lean](../../GQ2/Dyadic/Instances/FieldFamilySpliceMarkedCanonical.lean).
Its only explicit field input beyond finite-dimensional `K` is `RI`. It supplies:

- a `GenAsmFlexibleBranch` at degree exactly `[K : ℚ₂]`;
- a complete `GenAsmFlexibleRowResidualRN`, hence the actual `WordCertificateRN`;
- an actual `ContinuousMulEquiv` from `GammaR` of that same carried word to `GalK K`;
- tame, pro-two, canonical maximal-pro-two, cyclotomic, and full `Ztwo`-valued
  unramified compatibility equations for that same equivalence.

The auxiliary filtration, numerical parameters, topology instances, reciprocity,
and tame quotient are supplied in the canonical wrapper. The generic bundled
version is
`FieldFamilySpliceMarkedFinal.hasSelectedFullyMarkedFlexibleAssemblyRN_fieldSelectionFromRange`
in [FieldFamilySpliceMarkedFinal.lean](../../GQ2/Dyadic/Instances/FieldFamilySpliceMarkedFinal.lean).
Both modules are green at default Lean limits and warning-free. This audit also
rechecked both marked modules directly; the canonical endpoint's printed
axiom set is recorded in §6 below. The additive public entry point is now
[GeneralMain.lean](../../GQ2/Dyadic/GeneralMain.lean).

### What the marking proof actually establishes

[TameMarkedReconstruction.lean](../../GQ2/Dyadic/TameMarkedReconstruction.lean)
proves `nonempty_tameMarkedEquiv_of_sourcesRN` and
`exists_tameNuCompatible_equiv_of_sourcesRN`: reconstruction retains the actual
tame map, and therefore the full unramified character, not merely its reduction
modulo two.

[FieldFamilySpliceAlignedFinal.lean](../../GQ2/Dyadic/Instances/FieldFamilySpliceAlignedFinal.lean)
then replaces **only the existential branch's realization of its pro-two core**
by the one induced by this equivalence. The word, core, degree, `nuP`, and
certificate are retained definitionally. The two literal pro-two squares are
`alignedRealization_pro2` and `alignedRealization_maxPro2`.

This is not a post hoc definition of the cyclotomic character. The record
`AlignedMarkedFieldEquiv` in `FieldFamilySpliceMarkedFinal` fixes the character
using the **original** supplied realization before reconstruction.
`alignedRealization_chi_eq_original` proves that calibration leaves it unchanged.
Its input is discharged by
`FieldCyclotomicCharacteristic.chiCycKTwo_characteristic_ramifiedI`
([source](../../GQ2/Dyadic/Instances/FieldCyclotomicCharacteristic.lean)), using the
existing M-characteristic theorem and the new uniform N and square-core
characteristic theorems. Thus all the marking equations coexist on one equivalence.

What is **not** proved is that reconstruction respects an arbitrary previously
fixed pro-two realization pointwise. Existing fixed-frame counts test an
elementary-abelian-two quotient of the core, not every prescribed finite pro-two
quotient; see [the fixed-core audit](w361-full-core-marking-audit.md). That stronger
fixed-realization theorem remains separate. It is unnecessary for the existential
endpoint because calibration is allowed there, and the original character survives.
The proof packet should state this quantifier order explicitly.

### Coverage and actual source identity

[FieldFamilySpliceSourceComplete.lean](../../GQ2/Dyadic/Instances/FieldFamilySpliceSourceComplete.lean),
`hasSelectedFlexibleRowResidualRN_of_matchesRange`, exhausts all five selected
families. Its branches are:

| Selected family | Actual certified source used |
| --- | --- |
| L | Existing all-odd-degree L source and certificate |
| N0 | Existing range-matched compact-N source and certificate |
| Npc | Existing range-matched procyclic-N source and certificate |
| M0 | Existing canonical source when its pivot condition holds; otherwise the uniform promoted-handle pair splice |
| Mpc | Uniform mobile, normalized, tame-corrected splice for both epsilon values and every handle count |

The concrete changed words are
`EvenMHeadHandlePairSpliceSupply.headHandlePairSpliceW` and
`tameSplice (mpcMobileTameCorrectedW ...) (Words.MCompact.mCompactW alpha h)`.
Their complete analytic and affine-phase leaves are constructed, not assumed, by
`headHandlePairSplice_flexibleCertificateLeaves` and
`mpcMobileTameSplice_flexibleCertificateLeaves` in
[the pair boundary module](../../GQ2/Dyadic/Instances/EvenMHeadHandlePairSpliceBoundary.lean)
and [the mobile boundary module](../../GQ2/Dyadic/Instances/MpcMobileSpliceBoundary.lean).
Both concrete source constructions print standard-three axioms only. The mobile
construction includes `h = 0`; the pair construction uses a genuine selected
handle, and the M0 dispatcher supplies the canonical alternative when no such
handle can occur.

The subsequent selected-word strengthening now exposes the constructor in the
theorem conclusion. `SelectedWordProfile` in
[FieldFamilySpliceSelectedWord.lean](../../GQ2/Dyadic/Instances/FieldFamilySpliceSelectedWord.lean)
retains actual `HEq` word equality, alphabet degree and core equality, and the
splice marking. `SelectedWordMarkedFieldData` in
[FieldFamilySpliceSelectedWordFinal.lean](../../GQ2/Dyadic/Instances/FieldFamilySpliceSelectedWordFinal.lean)
retains this profile under realization calibration together with the certificate
and all marking equations. Its bare producer is
`nonempty_selectedWordMarkedFieldData_ramifiedI K RI`. On Mpc, the actual mobile
unit `etaD` is retained with its congruence to the selected display unit modulo
`2^r`, not falsely equated to that representative. Thus theorem-level source
explicitness is now supplied, not merely a family tag. Publication/export
acceptance remains separate; see [the selected-word audit](w361-selected-word-audit.md).

[TameShadowWord.lean](../../GQ2/Dyadic/TameShadowWord.lean) defines the splice as
`shadow(R) * H * shadow(H)⁻¹` and proves its specialization properties, including
`eval_pro2_tameSplice` and `CorePresentation.ofTameSplice`. The construction is not
an asserted tame-compatible equivalence with the old M candidate. Such a shortcut
is ruled out in the obstructed cases by the
[W341](w341-even-m-adapted-boundary-nogo-note.md),
[W343](w343-even-m-flexible-model-nogo-note.md), and
[W344](w344-even-m-flexible-selector-nogo-note.md) no-go results. Those results
remain valid; the new endpoint concerns a genuinely changed source.

## 3. The original nine obligations: functional discharge and literal statements

The packet's §14 table and plan §2 prescribe stronger intermediate formulations
in some places than the final theorem needs. The following is a dependency audit,
not an owner-approved relabelling of those historical obligations.

| ID | Current proof status relevant to the general endpoint | Qualification against the original wording |
| --- | --- | --- |
| MC-M | Required oriented core matching and marking corrections are supplied. General M scaling/mixing consumers are in `MarkedCore/MScalingHandles.lean`; range-selected field orientations and the canonical-or-strict handle dichotomy feed the source dispatcher. | Do not infer unrestricted transitivity of all `Ztwo` markings, or universal canonical-C placement. The strict-handle alternative is essential. Nor does correction of a particular marking by itself prove every originally proposed pure Nielsen-family lift. [W362: the original mathematical M stabilizer-lifting assertion is now CLOSED by `mFullStabilizer_lift_iff` (every full-frame automorphism preserving the actual orientation and full mod-two cup form lifts, torsion-sensitive, all h, alpha >= 2, std-3); the finite Nielsen-list artifact is separate, as for N.] [W366 2026-09-18: **MC-M is discharged and the packet row now says so.** The owner accepted Option A of `w364-proof-packet-amendment-mc.md`, so the uniform filtered-correction and compactness method satisfies the row, and the finite Nielsen-family list artifact now exists at rank four: `mNielsenGen_finite_list` and `mNielsenGen_stabilizer_induced` (`GQ2/Dyadic/MarkedCore/MNielsenGenerators.lean:694,856`), a literal seven-member list drawn from the seven Nielsen families, every member orientation-preserving, a full mod-two cup isometry and lifting, quantified over every element of `IsMStabilizer`. Two scopes stay apart: the list is rank four (`h = 0`), the lifting half `mFullStabilizer_lift_iff` is general in `h` at every `alpha >= 2`. "Finite list" is the families reading: finitely many parameterized families, one member of each slot per stabilizer element; no finite generating set exists and no finite-word decomposition of the limiting automorphism is produced. The individual generators are lifted by the uniform theorem, not by seven closed-form group constructions. Std-3.] |
| MC-N | Required primitive correction, strong plane scaling and core lifting remain proved. The new `nFullStabilizer_lift_iff` additionally characterizes the entire orientation/cup-preserving full-frame image, allowing arbitrary handle mixing and retaining torsion, uniformly in rank. | The original mathematical stabilizer-lifting assertion is closed. The old packet's prescribed finite Nielsen-generator list is not supplied by the filtered/compactness proof; either that presentation artifact or acceptance of the alternative proof method remains. No weakening to primitive correction is needed. [W366 2026-09-18: **both of those alternatives have now happened, and MC-N is discharged.** The artifact exists at rank four (`nNielsen_factorization`, `nNielsenFac_finite_list`, `nNielsenFac_stabilizer_induced`, `GQ2/Dyadic/MarkedCore/NNielsenFactorization.lean:357,758,911`), an eight-slot list drawn from six Nielsen families with the completeness half supplied by W364; and the owner accepted the alternative proof method on 2026-09-18 as Option A of `w364-proof-packet-amendment-mc.md`. The packet row now reads discharged. At N the list members carry a second, independent lift assembled from the families' own constructions (`nNielsenFacLifts_of_param_families`), whose `N4` ingredient is itself a compactness limit. The same two scope statements as MC-M apply: rank four for the list, general `h` for `nFullStabilizer_lift_iff`, and the families reading of "finite list". Std-3.] |
| WC-L | Complete source/certificate at every required odd degree: `wordCertificateRN_lSq_qOf` in `GammaLOddDegreeGrandAssembly.lean`, consumed by `hasSelectedRowResidualRN_l`. | The general source, not only the old `n = 1` fixture, is the proof input. New release documentation must link its uniform certificate. |
| WC-N0 | `hasSelectedRowResidualRN_n0` in `FieldFamilyCampaignBoundary.lean` consumes the complete range-matched compact-N certificate at the selected degree. | The source has no residual Fox/Stokes/Hessian assumption; acceptance should cite its actual normal-form lemmas, not merely the old illustrative matrix. |
| WC-Npc | `hasSelectedRowResidualRN_npc` supplies the complete selected procyclic-N source with general parameters. | No restriction to the manifest's `(alpha,r,eta,h) = (2,1,1,0)` fixture is used. Retain the exact semantic parameter conventions when updating the appendix. |
| WC-M0 | Both canonical-pivot and strict-handle cases have complete certificates; the latter is `headHandlePairSplice_flexibleCertificateLeaves`. | General coverage is at the changed pair-splice word when necessary. It does not complete the false universal frozen-word placement assertion. |
| WC-Mpc | `mpcMobileTameSplice_flexibleCertificateLeaves` supplies all analytic clauses and the actual affine determinant, uniformly in the semantic unit and parameters. | The word is the mobile normalized/tame-corrected splice, not an identification with the frozen self-replicating display. The full extraspecial factor-set charge is retained; bilinear Stokes alone was not substituted for phase. |
| LG-K | `compatibleRamifiedDataAt_of_norm_reciprocity` in `RamifiedCertificateCanonicalFieldData.lean` supplies the shared packet for arbitrary finite K. The new relative-inertia/norm argument removes the formerly carried signed-Frobenius, relative-norm, and odd-degree premises. | No new relative-CFT or field-presentation axiom was introduced. `RamifiedIData K` remains the standing presentation-scope hypothesis, not a universally constructed bundle. |
| SD-n | `thm_4_2_of_sourcesRN` in `ThmFourTwoRN.lean` and its reconstruction consumers are degree-generic and two-sided; W361 adds tame-marked reconstruction and existentially aligned full marking. | This uses `SourceDataRN` / `WordCertificateRN` and the corrected `zRN` coefficient, not the unchanged frozen R-stage clause. The packet's “induction unchanged” wording must account for this correction and the marked reconstruction argument. |

Exact source anchors for the historical lifting distinction are
[Certificate.lean, “hypothesis surface”](../../GQ2/Dyadic/MarkedCore/Certificate.lean),
[N.lean, `nStabParam_lift`](../../GQ2/Dyadic/MarkedCore/N.lean),
[ClearWide.lean, `nStabParam_lift_of_scaling`](../../GQ2/Dyadic/MarkedCore/ClearWide.lean),
and [MScalingHandles.lean](../../GQ2/Dyadic/MarkedCore/MScalingHandles.lean).
The all-family consumer is the short case split in `FieldFamilySpliceSourceComplete`;
it has no residual proposition corresponding to any of these historical binders.

Consequently it is accurate to say **the mathematical roles of all nine lanes are
supplied for the revised general endpoint**. It is not accurate to say **all nine
original intermediate statements, with the old words and unchanged source record,
have now been proved verbatim**.

## 4. One-tree TeX/hash and certificate acceptance: a concrete remaining gap

I reran `python3 scripts/dyadic_word_tex.py check`: it prints
`one-tree hash check passed (merge gate 7)`. This checks only the declared entries
in [generated/hash-manifest.json](../../generated/hash-manifest.json):

`rawLsq_n1`, `rawMCompact_alpha2_h0_q2`, `rawMpcSqrtNeg10`,
`rawNCompact_alpha2_h0`, and `rawNpc_a2_r1_eta1_1_h0`.

There is **no pair-splice or mobile-splice entry**. Therefore the passing existing
hash check does not certify that the newly proved words match any published TeX
display. Also, for example,
[rawMpcSqrtNeg10's generated appendix](../../generated/appendix/rawMpcSqrtNeg10.tex)
still has explicit `dyadicAppendixTODO` slots for items 2–9: specializations, Fox
Jacobian, invertible operations, reduced matrix, Stokes identity, extraspecial
Hessian, quadratic normal form, and affine phase certificate.

This is a publication/interface gap, not a missing Lean phase proof. The concrete
new boundary modules construct the affine supplies and determinant certificates;
`UniformStokesSupply.determinant_of_branchFree` is consumed with proved branch-free
supplies. The newer `generated/general-certificate-staged/` packets now expose
the pair/mobile word, Fox, phase and cover trees with source-certificate
references, declaration transcripts and ten-section TeX. They are separate
staged artifacts, not additions to the old manifest or owner-approved
fulfillment of its acceptance contract. Their 29-page PDF has passed visual QA;
the final source-bound replay is tracked in `w361-final-verification.md`.

For the new words the release contract must cover the following. The staged
implementation now supplies the expression trees, Lean bridges, synchronized
TeX/hashes and regression checks; adoption and the precise semantic/display
scope remain decisions, not automatic consequences of implementation:

1. A single authoritative expression-tree/export representation of the actual
   promoted-pair/mobile normalization, tame correction, and `tameSplice` operation,
   together with a checked bridge to the `PWord` used by the certificates.
2. Generated TeX and hashes tied to that representation, covering the uniform
   parameterized construction rather than presenting a few fixed fixtures as a
   proof of the general family. The representation of semantic two-adic parameters
   must be explicit.
3. Completed certificate appendices, or an explicitly owner-approved equivalent
   presentation of their compositional proofs, containing all ten ledger items.
4. Regression coverage that actually includes these new entries.

The old interchange constructor named `RawWord.shadow` in
[Word/Export.lean](../../GQ2/Dyadic/Word/Export.lean) must not be confused with
W361's semantic `tameShadow` substitution. In that old exporter `.shadow` has no
general `PWord` denotation. Matching names are not a word-identity proof.

## 5. Statement and editorial reconciliation

The following changes require explicit reconciliation of the authoritative packet,
not just a claim that the old prose is “now green”:

- Replace universal use of the frozen M representatives by the actual flexible
  source-selection theorem; state its uniform word-construction rules and retain
  the established no-go qualifications. Keep L/N and the old regression table intact.
- Expose the actual construction/certificate equality in the public explicit-word
  statement, so the published construction is not linked to the existential word
  only by inspecting its proof. The public selected-source endpoint and staged
  symbolic export now share this semantic target; the publication contract must
  retain it and state the limits of symbolic two-adic parameter binding.
- State the corrected RN source equation and its relation to the degree-one frozen
  interface. `SourceDataRN` contains the corrected coefficient and checked
  degree-one bridges; it is not definitionally the old general-degree contract.
- State marked existence with its quantifier order: the realization is existentially
  calibrated, the original cyclotomic character is preserved, and one equivalence
  satisfies all the displayed marking equations. Do not claim the old abstract
  count theorem already preserved an arbitrary fixed boundary map.
- Keep MC-M's stronger literal stabilizer claim separate from its proved marking
  consumers. MC-N's full mathematical assertion is now proved; reconcile only
  its prescribed finite Nielsen-list proof method with the new uniform proof.
- Refresh the completion summary around the new additive entry point
  `GQ2/Dyadic/GeneralMain.lean`. The old `Main.lean` still advertises the older
  frozen-quadratic assembly and does not itself express the W361 general endpoint.
  Historical residual inventories and early W361 notes should be dated or
  cross-linked, not read as the current binder list.

In particular, the packet's certificate-main theorem fixes a standard word/core
before claiming all compatibilities, whereas its old proof only invokes abstract
finite-quotient reconstruction. The new marked result repairs that proof gap for
the revised existential source statement; it does not retroactively establish an
arbitrary-fixed-realization version.

## 6. Axiom and citation posture

The new bare fully marked canonical endpoint prints exactly standard-three
(`propext`, `Classical.choice`, `Quot.sound`) plus these **nine existing** inputs:

- `GQ2.hilbertSymbol_normCriterion_finiteDyadic`
- `GQ2.localReciprocity`
- `GQ2.markedRecipAt`
- `GQ2.orientedTameQuotientAt`
- `GQ2.peripheralCyclotomicAction`
- `GQ2.relativeStiefelWhitney_dyadic`
- `GQ2.tateDualityAt`
- `GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated`
- `GQ2.Foundations.absGalQ2_localEulerCharacteristic`

This is a twelve-name endpoint print, **not nine newly introduced axioms**. The
repository's foundational declaration census remains eleven; an individual endpoint
need not use every declaration. The new source, tame-marked reconstruction, and
abstract characteristic arguments are standard-three; the canonical field endpoint
inherits its arithmetic baseline through the existing producers.

The historical sections of
[literature-axioms-dyadic.md](literature-axioms-dyadic.md) are an older measured
snapshot. Its new additive §W361 now records the current endpoint and qualifies
the old claims about `markedRecipAt`/`orientedTameQuotientAt` as historical. This
refresh changes the current interpretation, not the old measured theorem prints.

The same document records the historical owner-approved citation-status
discipline: the two K-side axiom citation **targets** were approved without a PDF
detail-check. A subsequent W361
[clause-level source audit](w361-axiom-source-verification.md) now checks the
principal primary-source pages, distinguishes direct support from the composite
finite-r/K(i) arguments, and identifies a historical proposal prose overclaim.
It is not a blanket axiom-encoding verification or a change of owner approval.
The theorem remains foundationally conditional. No new axiom, additional
field-presentation assumption, or external publication is proposed here.

## 7. Verification and owner release gates

The earlier full integration snapshot recorded in
[w361-overnight-progress.md](w361-overnight-progress.md) built 1429 modules and passed
the ordinary dyadic gate and raw scoreboard. The gate report at
`/private/tmp/gq2-w361-gate-final.log` records:

- census eleven, empty sorry allowlist, no `native_decide`, and no obligation axiom;
- unchanged frozen Q2 and seventeen older dyadic capstone axiom checks;
- the existing manifest's hash check and sanity harness passing;
- **axiom-ledger gate skipped**, because that optional `lake` check belongs to the
  orchestrator's merge run.

That earlier integration run predates the final marked modules. The individual
new marked endpoints are green, including this audit's direct fresh checks; this
audit did not launch a competing shared full build. Before release, the orchestrator
must record a fresh full import-closure/build and gates at one fixed final tree,
including the new headline axiom sets and the enabled ledger gate. Existing frozen
Q2 names/prints and the `sqrt(-10)` procyclic `(r,epsilon,eta) = (1,1,1)` regression
must remain intact. Passing finite diagnostic examples is not part of the proof.

The plan's owner gates are not erased by mathematical completion:

- **G-1 / word selection:** the old freeze release does not approve replacing its
  M displays. The owner must accept the revised word-selection/statement artifact.
- **G-Lab:** the actual core consumers are supplied by proved routes; there is no
  new classification-axiom request. Record that discharge, including the distinction
  between required corrections and stronger unused historical lifting claims.
- **G-AX:** no census flip is requested. Carry forward the approved baseline and
  its citation qualifications; update the measured new endpoint surface.
- **G3:** final census/sign-off and whether/when to merge remain owner decisions.
  This audit does not authorize or perform a commit, merge, or publication.

## 8. Practical completion checklist

1. Freeze and independently verify the new general fully marked endpoint and its
   exact carried words at one integration tree.
2. Obtain/record approval of the revised M-word, RN-source, and existential-marking
   statements; resolve the literal nine-obligation wording as described above.
3. Adopt the checked staged pair/mobile TeX/hash and ten-item packet format,
   resolve its remaining editorial/display boundary, and complete or explicitly
   supersede the L/N publication appendices. The staged artifacts already exist.
4. Refresh the public entrypoint, binder/axiom ledger, proof-packet narrative, and
   current handoff; retain historical snapshots and no-go results accurately.
5. Run the final full build, fresh headline axiom audits, enabled ledger check,
   original regressions, and owner G3 review.

No further nilpotency-class casework is indicated by these endpoints. For the
revised existential ramified-i theorem, the remaining items above are acceptance,
statement, documentation, and release work. Proving the stronger unused full
stabilizer-lifting or arbitrary-fixed-realization statements would be additional
mathematics, not a hidden premise of the proved endpoint.

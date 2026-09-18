# W361 — handoff to Claude Code

Prepared 2026-09-17 for the user's request to spend the remaining Codex budget
on the hardest scaffolding and then hand the campaign over. This is the current
starting document; `w361-restart-handoff.md` records the earlier overnight
checkpoint. Do not interpret either handoff as owner approval or a release.

**Verified handoff:** clean build, complete staged replay and isolated ledger
all PASS. The complete replay finished at 22:53:05 UTC; final documentation
was assembled afterward without changing the frozen proof/source tree.
An independent post-replay consistency recheck also passed. All build and
agent lanes are finished; no running job is being handed over. The overnight
automation remains paused. No commit, push or release was performed.

## 1. Outcome and immediate orientation

**The full N stabilizer-lifting theorem is now proved, not merely scaffolded.**
For every alpha >= 2 and every handle count h, any continuous automorphism of
the actual N abelian frame preserving its actual orientation and full mod-two
cup form lifts to a continuous automorphism of DN. The conclusion preserves
the entire abelianization, including torsion and arbitrary handle mixing, on
every group element. The converse is also proved.

Public names, both in namespace `GQ2.Dyadic.MarkedCore`:

```lean
nFullStabilizer_lift
nFullStabilizer_lift_iff
```

File: `GQ2/Dyadic/MarkedCore/NFullStabilizerLift.lean`.
Do not confuse it with the older `NStabilizerFullLift.lean`, whose theorem
realizes only `NStabParam` core actions with identity handle columns.
All eleven new modules are integrated into `GQ2.lean`; their 118 public pins
are registered in the 691-pin artifact audit. Default-limit compilation and
independent proof reviews pass. No new axiom, proof placeholder, native
decision or resource option was introduced.

The earlier general ramified-i field presentation endpoint was already
proved and remains unchanged. This pass closes an additional, previously
unproved, original N mathematical obligation. It does **not** prove the
analogous unrestricted M assertion, restore the obstructed frozen M word
claim, or finish publication/owner acceptance.

## 2. Workspace, ownership and safety

```text
Repository: /Users/roed/claude/cla/work/gq2-dyadic-campaign
Branch:     dyadic
HEAD:       2bf856c94ee3cf2ac89ca41a689f1275cd84ae25
```

This is a heavily dirty research checkout: many earlier W360/W361 files are
untracked. They are user work, not disposable scratch. Preserve all of it.
No commit, push, reset, merge, release, census amendment or authoritative
packet adoption has been authorized. No cleanup was performed in this pass.

Keep the general-case focus. Do not start another class-seven or rank-by-rank
campaign. Do not reintroduce `sorry`, `admit`, `native_decide`, new axioms or
extra resource settings. Existing default settings are 200,000 heartbeats,
`autoImplicit=false`, and `relaxedAutoImplicit=false`.

The prior eight-hour request was fulfilled (09:10–17:34 UTC). The overnight
automation `overnight-dyadic-general-case-research` was **paused** at 17:30 UTC
and remains paused. Do not resume it merely because old transcript messages
asked for overnight work. This later pass is explicitly a bounded handoff.

## 3. What the new theorem actually says

Let `phi : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)`, where the
canonical frame is the actual topological abelianization in coordinates
`Z/2 × Z₂³ × Z₂^(2h)`. Assume:

1. `∀ z, nFrameOrientation ha h (phi z) = nFrameOrientation ha h z`;
2. `NFrameCupIsometry ha phi`.

Then there is an actual continuous automorphism `Psi` of `DN alpha h` with

```text
∀ x, chiN alpha h (Psi x) = chiN alpha h x
∀ x, nPhiHom ha h (abMk (Psi x)) = phi (nPhiHom ha h (abMk x)).
```

The cup condition is intrinsic to the full frame: it quantifies over every
continuous F₂ character, including the torsion character. It does not assume
a group lift, a matrix realization, a finite-stage supply or an initial-error
bound. Every frame automorphism automatically fixes the unique nonzero
order-two element. Orientation is the transported original `chiN`, not one
chosen after finding the lift. Its preservation is equivalent to preserving
the integral b-coordinate (`nFrameOrientation_preserved_iff`).

The final lift is not claimed to fix the nonabelian head generator literally.
Literal fixation is used for the **initial free lift**; subsequent correction
retains its full abelian coordinates. Nor is nu fixed: these automorphisms
are precisely available for changing unramified markings.

Original packet §7, lines 732–735, asks for this full invariant-triple lifting.
That mathematical N assertion is now closed. Packet §14, lines 1077–1082,
also prescribes a finite list of orientation-preserving Nielsen generators.
This proof uses uniform filtered correction and compactness, not a finite
decomposition certificate. Accepting this proof method is distinct from
weakening the mathematical target. Do not call the finite-list artifact done.

## 4. Proof architecture and hard reusable scaffolding

All files below live in `GQ2/Dyadic/MarkedCore/`. Except `NInitialCupDepth`,
they add no namespace beyond `GQ2.Dyadic.MarkedCore`.

| Module | Reusable content | Public pins |
| --- | --- | ---: |
| `FreeProTwoMatrixBasis` | Coordinate-word maps, actual free bases from right-invertible integral matrices, exact coordinate rows and literal fixed columns; equality in every commutative pro-two target | 19 |
| `NBasisRowRefinement` | Inverse-basis coordinate identity and closed derivative-kernel interpolation for an arbitrary basis; kills every ordinary row | 6 |
| `NBasisRelativeRefinement` | Exact row/orientation correction retaining the improved literal target-relative relator error | 1 |
| `NBasisExactStages` | Uniform all-depth induction retaining the entire initial coordinate matrix | 2 |
| `NFullFrameCompactness` | Closed stage sets retain full torsion-sensitive frame marking, orientation and Frattini generation; actual automorphism at the limit | 7 |
| `NFullFrameStageTransfer` | Exact free coordinates transfer to actual DN abelianization, including torsion; transports finite stages | 4 |
| `NBasisFullFrameLift` | All higher stages and compact limit from one initial depth-three basis | 4 |
| `NFrameMatrixLift` | Any actual full-frame automorphism has an actual free-basis lift, literal fixed head, exact frame square and orientation | 30 |
| `NInitialCupDepth` | Uniform actual commutator calculation in lambda₂/lambda₃; full cup preservation plus fixed head implies actual relator error in lambda₃ | 30 |
| `NFrameCupCoordinates` | Semantic full-frame cup condition implies the exact reduced-coordinate equations required by the initial-depth lemma | 9 |
| `NFullStabilizerLift` | Composes all seams; all-element full-frame sufficiency and exact image iff | 6 |

Key chain:

```text
actual full-frame automorphism + orientation + full cup
  -> actual free basis, literal head fixed
  -> genuine initial relator error in lambda₃
  -> arbitrary-basis kernel interpolation at each depth
  -> all-depth exact full-coordinate stages
  -> torsion-sensitive compact limit, actual DN automorphism
  -> all-element full-frame square and converse
```

Important pitfalls already resolved:

- With generator images as matrix columns, the cup equation is
  `Abar G Abarᵀ = G`, **not** `Abarᵀ G Abar = G`. The latter even rejects the
  known N1 automorphism. The proof checks the semantic-to-coordinate variance.
- Integral inverse matrices do not give inverse nonabelian coordinate-word
  maps. Surjectivity is proved through index-two quotients and Frattini, then
  Hopficity gives an actual automorphism. The row correction uses coordinates
  of the actual inverse basis; it does not fake a group inverse.
- Z₂ characters on DN alone miss torsion. Exact **free** coordinates determine
  every commutative pro-two image, including the actual torsion-sensitive
  abelianization. The compact stage sets retain literal full frame values.
- The extra head divisibility digit follows from the literal improved relator
  equation; it is not an extra hidden input. The kernel includes the b row.
- The initial cup lemma proves actual quotient equality / error membership,
  not merely membership in a formal bracket span. Literal fixed head cancels
  the entire `(2+2^alpha)` power; symmetric off-diagonal coefficients contract
  to zero against the actual alternating bracket, uniformly over all handles.
- `NUnrestrictedStageSupply` from an older proposed approach is unnecessary.
  The existing proved ambient-stage theorem supplies every stage in this route.
- No compatible sequence is assumed: closed nested stages and compactness
  yield one actual marked lift. Frattini generation survives the limit.

## 5. Verification record for this handoff

New source snapshot: 2026-09-17 18:55:00–18:55:01 UTC, after integration.

Already complete:

- All eleven modules: default-limit, warning-free compile; 118 standard-three
  pins, with independent reviews of every hard seam and the final theorem.
- Shared-cache umbrella PASS, log `/private/tmp/gq2-w361-claude-umbrella.log`.
- Artifact audit PASS, **691** pins, log
  `/private/tmp/gq2-w361-claude-artifact-audit.log`.
- `git diff --check` PASS at integration.

Final clean verification **PASS**:

- Full ordinary gate with ledger **PASS**, 50,991 tracked declarations,
  zero sorry dependencies, unknown nonstandard axioms and terminal violations;
  global axiom census remains eleven:
  `/private/tmp/gq2-w361-claude-gate-ledger.log`.
- Raw scoreboard **PASS**, 1,557 files under `GQ2/` scanned: 1,551 imported
  source modules, the separate `AxiomLedger` driver, and five exporter drivers.
  The clean closure additionally counts root `GQ2.lean`, giving 1,552 modules.
  The scoreboard used the correct explicit roots:
  `/private/tmp/gq2-w361-claude-scoreboard.log`.
- New clean snapshot **PASS**: `/private/tmp/gq2-w361-fresh-slpe4r0g`,
  **1,552/1,552 local modules**, zero local artifact reuse, 3,701 inventoried
  output files, recorded build time 2,517.610 seconds. No failed/unbuilt
  modules and no live source, manifest or output-file drift. Log:
  `/private/tmp/gq2-w361-claude-handoff-fresh.log`.
- Complete content-bound staged replay **PASS**, recorded from
  20:32:58 to 22:53:05 UTC: all 16 exact headline-footprint pins, all 691
  artifact pins, component tests and all strong staged Lean replays. Every
  source/output byte, all 21 replay-source files and all 62 staged-content
  files matched before and after. Original report:
  `/private/tmp/gq2-w361-fresh-verified-pb3zz3w7/report.json`.
- Exact durable report copy:
  [`w361-claude-code-verification-report.json`](w361-claude-code-verification-report.json).
  Its SHA-256, independently compared with the original bytes, is
  `aad5d041ec098c6f1d5dc0b8e24953322afdff2073a20a133a79e67e9f1a3711`.
- Direct isolated-root ledger **PASS**, 50,991 tracked declarations, zero
  sorry dependencies, unknown nonstandard axiom uses and terminal violations.
  Log `/private/tmp/gq2-w361-claude-fresh-ledger.log`, SHA-256
  `027a89089476fe8e8ee2177fef6f6598ee941a1ec905dc6d2496f46215459e15`.

Current verified source-set SHA-256:
`34477d1c4c082aadda64e4a855ba66679765d486db8084fe931ed3b86e36e6dc`.
Complete local-output-file-set SHA-256 (all 3,701 files):
`388d0fdf8b91278a5ca95f8dd8731be2a5a68936e8e1676ab1e714e534b4908a`.
Staged replay log SHA-256:
`bfda64077395d30826d7dd351b0233e6bb9b7e4b4f72c3cfab3c94e039ecb5e3`.
After replay, an independent reviewer rechecked all 1,552 current/snapshot
sources and 3,701 outputs, all 21 replay-source and 62 staged-content hashes,
the replay-log hash, the byte-identical durable report, the 691/16 audit
counts and the zero-gap 50,991-declaration ledger. Everything matched; that
read-only recheck introduced no new artifact and is not an additional replay.
The reviewed builder and verifier were unchanged; their hashes and full
verification contract remain in `w361-final-verification.md`. The new report,
not the old report below, binds this 1,552-module source state.

The prior **1,541-module / 573-pin** checkpoint remains historical:
`/private/tmp/gq2-w361-fresh-egoma1il`, durable report
`docs/dyadic/w361-final-verification-report.json`, report SHA-256
`bb20e9914dd86be093521808b0267f8ac0f6cd857fe6e13b8285d8213784abcb`.
It passed at 17:29 UTC but does **not** cover the new modules or changed audit
script. Do not overwrite its files or relabel its report as current evidence.

Fresh verification reuses manifest-matching external dependency artifacts;
it does not rebuild or independently byte-attest those dependencies. It checks
the entire local import closure, all local olean/ilean/private/server/IR files,
the exact compiler/manifest, 21 replay-source files and 62 staged-content files
before/after replay. This is content consistency with an observed isolated
build, not an atomic/signed attestation or proof of editorial prose.

## 6. Existing field endpoint and remaining campaign work

Preferred field entrypoint:
`GQ2.Dyadic.hasSelectedOriginalMarkedWordPresentationRN_ramifiedI`, exported
by `GQ2/Dyadic/GeneralMain.lean` (again, the filename adds no namespace).

It proves the selected fully marked RN presentation for finite K/Q₂ with
explicit `RI : RamifiedIData K`. The selected original source and calibrated
realization are existential. One aligned equivalence retains the original
cyclotomic character, full Z₂ unramified character, exact constructor profile
and complete carried RN certificate. Both changed even-M families use the
uniform tame-shadow splice. General Stokes, affine determinant and the full
quadratic phase are composed, not merely separately available.

Trust boundary is unchanged: the generic supplied-bundle endpoint uses the
standard three plus six standing inputs; the canonical K+RI endpoint uses
the standard three plus nine. Global nonstandard axiom declarations remain
eleven. New N lifting has only the standard three. Do not infer elimination
of field axioms or coverage of fields outside the RI scope.

Recommended next work, in order:

1. **Read the scope audits before choosing new mathematics.** N's full
   existence theorem is done. If the literal finite Nielsen-list method is
   still required, formulate its precise artifact separately; do not reopen
   the solved starting-depth, arbitrary-basis or compactness seams.
2. **Audit and, if retained, tackle the larger M stabilizer assertion.**
   Start with the precise next-task map in
   `docs/dyadic/w361-m-next-general-scaffold.md`: the shared high-depth
   derivative is already proved; the first bounded task is coupled M-head
   divisibility/cleanup, not a new class sweep or a generic reachability axiom.
   Existing `MarkedCore/MScalingHandles.lean` and marking consumers suffice
   for the selected field theorem. They do not automatically prove every
   original invariant-triple automorphism lifts. Preserve the essential
   canonical-or-strict-handle alternative; do not assume unrestricted
   transitivity to a canonical C pivot. Transfer new general free-basis
   infrastructure where it genuinely applies, but do not copy N's literal
   head/torsion argument without checking the different M relation.
3. **Finish publication artifacts without silently changing authority.**
   Four pair/mobile ten-item packets and the 29-page staged PDF exist and
   have passed strong replay/visual QA. Six legacy L/N specimens are word-only,
   not full ten-item appendices. Five old appendix skeletons still contain
   40 recorded TODO invocations. Complete the missing general L/N certificate
   presentation or propose a clearly equivalent accepted format; retain
   frozen identifiers and hashes. Source bindings/transcripts do not prove
   editorial completeness or serialize every continuous parameter choice.
4. **Owner/editorial decisions remain.** Adoption of changed M pair/mobile
   words, corrected RN interface, existential realization/calibration
   quantifiers, symbolic display contract, treatment of legacy L/N artifacts,
   and acceptance of N's alternative proof method are not approved. Update
   proposals and implementation notes, not authoritative acceptance/release
   records without permission. G3/release remains an owner gate.

Do not resurrect the false universal frozen-M placement claim. Do not claim
an arbitrary external two-adic unit admits a rational `NpcDisplayFor`. Do not
turn existential calibrated realization into a pointwise arbitrary-fixed-
realization theorem. Do not generalize the ramified-i hypothesis away.

## 7. Exact runtime and safe commands

```sh
cd /Users/roed/claude/cla/work/gq2-dyadic-campaign
GQ2_HANDOFF_LEAN=/Users/roed/.elan/toolchains/leanprover--lean4---v4.31.0-rc2/bin/lean
GQ2_HANDOFF_PACKAGES=/Users/roed/claude/gq2-paper/formalizations/gq2-claude/.lake/packages
GQ2_HANDOFF_CACHE=/Users/roed/claude/cla/work/main-build-cache/lib/lean
```

Lean is pinned to **4.31.0-rc2**. The package checkout's manifest must match.
Compile/check a source against the shared cache with the reviewed runner:

```sh
GQ2_W361_ARTIFACTS="$GQ2_HANDOFF_CACHE" \
GQ2_W361_PACKAGES="$GQ2_HANDOFF_PACKAGES" \
bash scripts/w361_lean_runner.sh GQ2/Dyadic/MarkedCore/NFullStabilizerLift.lean
```

When changing a module, emit its `.olean` and `.ilean` explicitly under the
shared cache and rebuild dependents. Example:

```sh
GQ2_W361_ARTIFACTS="$GQ2_HANDOFF_CACHE" \
GQ2_W361_PACKAGES="$GQ2_HANDOFF_PACKAGES" \
bash scripts/w361_lean_runner.sh \
  -o "$GQ2_HANDOFF_CACHE/GQ2/Dyadic/MarkedCore/NFullStabilizerLift.olean" \
  -i "$GQ2_HANDOFF_CACHE/GQ2/Dyadic/MarkedCore/NFullStabilizerLift.ilean" \
  GQ2/Dyadic/MarkedCore/NFullStabilizerLift.lean
```

For a new verified tree after edits:

```sh
python3 scripts/w361_fresh_build.py \
  --packages "$GQ2_HANDOFF_PACKAGES" --lean "$GQ2_HANDOFF_LEAN" \
  --jobs 4 --require-live-match
```

Use the exact snapshot path it returns in a read-only replay:

```sh
python3 scripts/w361_verify_fresh.py /private/tmp/gq2-w361-fresh-slpe4r0g \
  --packages "$GQ2_HANDOFF_PACKAGES" --lean "$GQ2_HANDOFF_LEAN" --replay

GQ2_W361_ARTIFACTS=/private/tmp/gq2-w361-fresh-slpe4r0g/lib/lean \
GQ2_W361_PACKAGES="$GQ2_HANDOFF_PACKAGES" \
bash scripts/w361_lean_runner.sh GQ2/AxiomLedger.lean

GQ2_MIR="$GQ2_HANDOFF_CACHE" GQ2_PKG="$GQ2_HANDOFF_PACKAGES" \
bash scripts/scoreboard.sh --raw
```

The example snapshot is valid only for its frozen bytes; after any source
change, build a **new** snapshot and use its returned path. Never emit artifacts
into an existing fresh snapshot. Do not substitute an arbitrary Lake invocation
whose shared artifact root may take precedence. Do not use `mirror.sh sweep`
on the shared cache. Exporter drivers with global `main` intentionally stay
outside `GQ2.lean`. The builder requires 6 GiB free at start and 4 GiB during
build; approximately 84 GiB was free at the start of this pass's verification.

For the full ordinary gate, the existing temporary wrapper is:

```sh
bash /private/tmp/gq2-w361-run-with-deps.sh \
  env -u GQ2_LEDGER_FIXTURE GQ2_LEDGER_GATE=1 bash scripts/check_dyadic.sh
```

If that temporary wrapper has gone, reconstruct its environment from the
runtime paths above: `LEAN_PATH` must begin with the shared local artifact root,
then all manifest package `.lake/build/lib/lean` roots, then the pinned compiler
`lib/lean`. Do not silently skip the ledger or use a fixture.
The current `.lake/build` is a symlink to
`/Users/roed/claude/cla/work/main-build-cache`; this is why the ordinary
gate's internal Lake invocation selects the checked artifacts here. After
relocating the checkout, check that mapping explicitly. Prefer the direct
reviewed runner for the independent isolated-root ledger and artifact audits.

## 8. Minimal reading list

1. This document and its final verification record.
2. `GQ2/Dyadic/MarkedCore/NFullStabilizerLift.lean`.
3. `docs/dyadic/w361-n-full-stabilizer-independent-audit.md`.
4. `docs/dyadic/w361-n-arbitrary-basis-refinement-audit.md`.
5. `docs/dyadic/w361-n-full-stabilizer-scope.md`.
   For the first new mathematical task also read
   `docs/dyadic/w361-m-next-general-scaffold.md`.
6. `docs/dyadic/w361-completion-audit.md` and
   `docs/dyadic/w361-final-endpoint-scope-audit.md` for the overall campaign.
7. `docs/dyadic/w361-proof-packet-amendment.md` and
   `docs/dyadic/w361-acceptance-readiness.md` for proposed, not approved, adoption.
8. The exact original target in `docs/dyadic/plan.md` and
   `docs/dyadic/refs/dyadic-presentations-formalization-proof.tex` when deciding
   what remains of M or the finite Nielsen-list artifact.

## 9. Suggested first prompt to Claude Code

> Continue the dyadic campaign in `/Users/roed/claude/cla/work/gq2-dyadic-campaign`.
> Read `docs/dyadic/w361-claude-code-handoff.md` and its referenced current
> verification/audits first. Preserve the dirty research checkout. The general
> selected ramified-i field endpoint and full arbitrary-handle N stabilizer
> lifting are proved; do not reopen those seams or return to class-by-class
> work. Take stock of the remaining original M stabilizer requirement and
> publication/acceptance distinctions, then make general-case progress with
> independently checked subagents if available. No new axioms, placeholders,
> native decisions, resource-limit increases, frozen-word replacement, commit,
> push or release without authorization. Keep verified facts, proposed scope
> amendments and owner decisions separate, and maintain a restartable handoff.

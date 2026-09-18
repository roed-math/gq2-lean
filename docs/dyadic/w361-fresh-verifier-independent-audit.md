# W361 independent audit of fresh-content verification

Status: engineering review of the additive, opt-in verifier. This is **not**
owner approval, a new release gate, a mathematical axiom audit, a signed build
attestation, or evidence that the current complete campaign has already passed
the final fresh-build-and-replay command. The latter needs its own actual report.

All three in-contract issues found below are fixed and independently retested.
Audited final script SHA-256 values:

```text
w361_verify_fresh.py      1b204d792fd744f0faf4122e7a76ebb632921b0a6bd092569a6e8ddd97a628b3
w361_fresh_build.py       21b8f1d72e013abac2e142048a61c0c8253e3c539b12c5f145c217c555bcd5be
w361_verify_fresh_test.py 8e60430ce008fb013bfe32b9838a6ddc37a8d8c8588a824c9fffa37cb3d7ed02
```

## Scope and method

Reviewed `scripts/w361_verify_fresh.py`, the output-recording portion of
`scripts/w361_fresh_build.py`, the explicit Lean runner, and the staged check
driver. The parent owns those scripts; this auditor did not edit them. Reported
fixes were applied by the parent and independently retested.

All mutation tests used isolated temporary fixtures or copies of a newly
compiled two-module test project. They did **not** alter the real historical
snapshot, shared campaign cache, dependency cache, or live Lean source. The
temporary harnesses are under `/private/tmp/w361-fresh-verifier-audit.QjHSuU/`.
Mocked replay tests exercise the verifier's post-run logic, not the mathematical
contents of the full staged suite.

The actual historical snapshot `/private/tmp/gq2-w361-fresh-5pyyouae` was tested
read-only. The initial verifier rejected it with `live source differs from
build: GQ2`. The strengthened verifier rejects it even earlier because it
predates the complete companion-file inventory. It has not been retroactively
upgraded or relabelled as a verification of the current tree.

## Issues found and correction evidence

### 1. Lean companion files and index bytes were initially unbound — fixed

The initial verifier checked `.olean` digests, required nonempty `.ilean`
files, and ignored `.olean.private`, `.olean.server`, and `.ir`. These are not
irrelevant cache debris. The installed pinned Lean sources
`Lean/Environment.lean` (`findOLeanParts`, `loadData`, `loadIR?`) load those
parts, and `Lean/Compiler/IR/CompilerM.lean` explains the separate runtime IR
storage. The real historical build contains module-system leaves with all
three companions.

The independent initial harness demonstrated that changed index bytes,
changed/deleted private parts, and added server/IR parts could survive both
pre- and post-replay checks.

The corrected producer now records mandatory `.olean`/`.ilean` plus the complete
private/server/IR trio when present, immediately after each successful module
compile. It requires nonempty outputs, compares the final **entire** local file
inventory to those recorded bytes, and fails on missing, additional, or changed
files. The provenance marker is `all-local-output-files-v1`.

The corrected verifier requires that contract, validates each relative output
path against the recorded local module names, cross-checks the old primary
`.olean` map, requires a complete companion trio, and rehashes the full inventory
before and after replay. The report separately records the primary-output
digest and the complete output-file-set digest. All reproduced companion/index
mutations are now rejected.

A genuine pinned-Lean smoke project with one legacy umbrella and one
module-system leaf built successfully as `/private/tmp/gq2-w361-fresh-r2h93ld6`.
It has exactly two local modules and seven recorded files. Seventeen tests on
isolated copies checked the baseline, deletion and corruption of each of the
seven files, an extra file, and deletion of the entire companion trio. All
behaved as expected. This is a producer-format test, **not** a fresh build of
the complete campaign.

### 2. Selected compiler and replay compiler could differ — fixed

The verifier initially accepted any explicitly supplied executable filename,
while the runner reconstructs `TOOLCHAIN/bin/lean`. Selecting `bin/lean-copy`
could therefore bind one executable's digest while replaying another.

The verifier now requires the resolved selected executable to be the exact
`bin/lean` used by the runner. The isolated alias test is rejected before any
compiler process is invoked. The current producer's SHA-256 is also required
to match the recorded `driver_sha256`, and the producer source is included in
the before/after replay-source hashes. A wrong producer digest, changed producer
source, or producer drift during replay is rejected. This narrows producer
identity; it does not authenticate a freely editable JSON record.

### 3. Custom report directory could self-contaminate a snapshot — fixed

An isolated no-replay invocation with a new report directory inside
`snapshot/lib/lean` passed its checks, wrote `report.json` into that inventory,
and emitted a successful report. An immediate subsequent check correctly
rejected the now-extra file. Replay mode detects this self-contamination after
the replay, but the promised read-only use of the snapshot has already been
violated. The default new `/private/tmp` directory is safe.

The corrected verifier resolves and rejects custom report destinations inside
the snapshot, checkout, dependency packages, or toolchain **before checking the
snapshot or creating anything**. Independent end-to-end tests cover all four
protected roots and a symlink leading into the snapshot. Every prohibited
destination is rejected without being created; the snapshot still passes its
unchanged baseline check. Separate new report directories remain accepted.

## Checked failure modes

The final revised isolated suite has 64 passing characterization tests,
and the parent's separate durable record suite has 38 passing tests. The suite
includes deliberate acceptance tests for the explicitly excluded assurances
below; it is not a claim that every scenario must fail.

Checked rejection includes:

- changed or missing recorded live/snapshot sources; malformed module paths;
- changed, missing, empty, or additional local outputs; complete companion and
  index-byte checks; unsafe/unknown output-inventory paths;
- partial/failed builds, count/type errors, claimed local reuse, invalid
  inventory contracts, malformed digests, duplicate JSON keys, and nonfinite
  JSON constants;
- compiler executable/version/pin mismatches, producer mismatches,
  snapshot/live/dependency manifest mismatch, dependency-root availability
  changes, and local `GQ2` artifacts injected into a declared dependency root;
- missing staged directories, PDF, or directly bound replay source;
- replay failure or missing exact completion marker; source, record, manifest,
  pin, producer, staged-file, PDF, and local-output drift during replay;
- pre-existing report directories, which are not overwritten.

Metadata does not supply an executable command: the compiler is explicitly
selected by the caller, scripts are fixed local paths, and module/output paths
are validated before use. The runner replaces `LEAN_PATH` with the isolated
local output root, declared dependency roots, and pinned toolchain library.
The updated staged driver also checks the new L/N export helper and its six
durable examples, rather than merely hashing those artifacts.

## Exact trust boundary and residual obligations

The appropriate interpretation of a successful **replayed** report is:

> The observed builder record, recorded local source/output bytes, currently
> selected compiler and manifests, direct replay sources, and staged contents
> agreed at the verifier's checks; the staged subprocess succeeded; the bound
> values still agreed after it returned.

It does not establish any of the following:

- **Hostile-record authenticity.** A coherently forged record and fake outputs
  can pass structural consistency checks. The verifier does not rederive the
  complete import graph or replay every compilation. It relies on the observed
  run of the bound producer for those facts. A test that coherently removes a
  dependency from both maps and inventories deliberately illustrates this
  boundary; it is not an acceptable way to create a real report.
- **External artifact bytes.** Package manifests and root lists are matched,
  but external compiled artifacts and the whole toolchain library are neither
  rebuilt nor byte-attested. The executable itself is hashed. A changed
  non-`GQ2` dependency artifact remains outside this promise.
- **Atomicity or continuous monitoring.** Checks read multiple files over time.
  A mutation restored between checks, a race within a hash pass, or later edits
  are not excluded. Filesystem symlinks are resolved/read as ordinary paths;
  this is not a hostile-filesystem sandbox or signed supply-chain mechanism.
- **Proof that PDF/prose is correct.** The PDF and TeX bytes are bound; that
  alone does not prove they agree visually or that editorial claims are true.
- **Automatic release acceptance.** Without `--replay`, a report records
  content consistency only, not suite execution. An actual final complete
  fresh build, current-tree replay report, and the separate owner/editorial
  approval decisions remain required for the stronger campaign milestones.

No further mathematical premise or Lean axiom is introduced by this tooling.

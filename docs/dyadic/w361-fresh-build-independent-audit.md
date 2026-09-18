# W361: independent audit of fresh-build isolation and tau-column semantics

Date: 2026-09-17. Read-only audit of the two build scripts and the new tau-column proof.
No script or Lean proof was changed during this audit.

Version scope: the script findings below describe the **pre-hardening implementation read
for this audit**, which used `local_imports` and an unrestricted package-directory glob.
The parent began implementing the recommendations afterward. These findings and line
references are historical; they do not assert that a later hardened script still has each flaw.
The separately identified first-run snapshot/provenance remains unchanged.

## Conclusion for the first successful run

The recorded run `/private/tmp/gq2-w361-fresh-dl5f62fk` is supported as a successful
fresh **local GQ2-source** build of its frozen 1,448-module import closure, using existing
external dependency artifacts. It is not a from-source rebuild of Mathlib, not a cryptographic
attestation of all dependency artifacts, and not a build of later additions to the live umbrella.
I found no evidence that this run accidentally reused a local GQ2 artifact.

Independently checked evidence:

- `result.json` reports 1,448 completed out of 1,448, no failed or unbuilt modules, and
  2,914.728 seconds. `/private/tmp/gq2-w361-fresh-build.log` ends with the matching result
  and `FRESH BUILD COMPLETE`.
- All 1,448 snapshotted source files reproduce their recorded SHA-256 hashes. Every
  expected local `.olean` exists in this run's private output tree.
- **All 1,448 module headers were independently parsed with the recorded Lean executable's
  `--deps` mode.** The resulting local dependency sets agree exactly with the script's
  scanner: zero errors and zero missing or extra edges. The recursive local closure is thus
  checked with Lean's parser, not merely by repeating the Python scanner.
- The external artifact roots currently contain no `GQ2.olean` or `GQ2/` artifact namespace.
  The run's private output root is first in `LEAN_PATH`; the shared campaign cache is absent.
- The recorded Lean version is `4.31.0-rc2`, commit
  `5e44d5f905127c78a2da7a015fe7a47840c95eb1`, matching the current toolchain pin. The
  recorded manifest SHA-256 is
  `3c3d5e1a78af7992672c437d36d7440c14c63249a840ef2c042e09649e51fae5`; current workspace,
  snapshot, and external package-workspace manifest agree.
- A scan of the saved module logs found no `sorryAx`, declaration-uses-sorry warning, or
  Lean error diagnostic. This complements, but does not replace, the separate declaration
  axiom audit.
- At audit time, the only changed live file among the 1,448 recorded source paths was
  `GQ2.lean`. This is expected umbrella growth. New modules absent from that snapshot are
  not certified by its success marker; later builds need their own recorded coverage.

Diagnostics were isolated under `/private/tmp/gq2-fresh-audit.7dErWX`. They read the frozen
tree and dependency artifacts; no source or artifact there was changed.

## Assurance supplied by the fresh-build script

`scripts/w361_fresh_build.py` creates a new temporary source and output tree, copies the
recursively discovered local `.lean` inputs, hashes the copied bytes, and compiles from that
source tree. It does not put the workspace or the shared GQ2 build cache on `LEAN_PATH`.
The dependency scheduler waits for each discovered local import to finish successfully.
There is no incremental freshness test: every discovered local module is submitted to Lean.

The three explicit Lean options match the current `lakefile.toml` exactly:
`autoImplicit=false`, `relaxedAutoImplicit=false`, and `pp.unicode.fun=true`. There is no
script-level heartbeat, recursion-depth, or proof-trust override. The `-o` and `-i` paths are
inside the fresh output tree.

On a compiler failure, the module is recorded as failed and no new jobs are launched; already
running jobs are drained. A blocked/cyclic graph leaves unbuilt modules and exits nonzero.
Low disk space also yields a failed build. An exception from a worker propagates nonzero
rather than producing a success marker, although it can prevent `result.json` from being
written. No failure-to-success bug was found in this control flow.

## Real limitations and hardening recommendations

### 1. The import scanner is not a complete Lean lexer

At lines 22–39, block comments are removed before line comments, line breaks are treated as
command boundaries, and removed comments are not replaced with whitespace. Three isolated
files, each accepted by Lean `--deps` with dependency `GQ2.Sanity`, all returned an empty
dependency list from `local_imports`:

```lean
-- A line comment containing /-
import GQ2.Sanity
```

```lean
import
  GQ2.Sanity
```

```lean
import/- ordinary separator -/GQ2.Sanity
```

Other Lean import modifiers or unusual names also are not generally covered. The script
deliberately supports only the `GQ2` namespace and ASCII module components.

A missed dependency normally makes the clean build fail because its artifact is absent;
it does **not** automatically create a false success. However, if a dependency artifact root
contains the missing local namespace, the unrestricted search path can supply a stale artifact
and the hard-coded `local_artifacts_reused: 0` would be unjustified. If the same module was
discovered elsewhere, scheduling may also be incorrect even though all its artifacts are fresh.

Recommendation: use Lean's header/dependency parser as the authoritative graph, or compare
against it before building; also reject local GQ2 namespaces in every external search root.
The full parser comparison above establishes that this flaw did not affect the recorded run.
An additional isolated test confirmed that `lean --deps` works with the source root on
`LEAN_PATH`: it returns the corresponding expected `.olean` path even when that artifact
does not exist. Thus dependency discovery need not reuse old GQ2 artifacts. Keep this source
search path confined to the parse phase; use only the fresh output root for local build imports.

### 2. Manifest equality does not authenticate dependency artifacts

The scripts compare lockfile bytes, but do not check package checkout revisions, dirty package
sources, artifact hashes, or whether artifacts were built from those sources. Their glob includes
**every** `*/.lake/build/lib/lean`, not just packages named in the manifest. The current list
actually includes an undeclared `ClassFieldTheory` build directory. It contains its own
namespace, and no use of that extra directory was found in the recorded closure, but its
presence demonstrates the mismatch between lockfile validation and search-path restriction.

Recommendation: derive the package roots from the manifest, record/verify checked-out
revisions and relevant artifact identities, and keep the claim explicitly “fresh local build
against prebuilt dependencies” unless dependencies themselves are rebuilt and audited.

### 3. Toolchain selection is recorded, not enforced by both entry points

The fresh-build script accepts an arbitrary `--lean` file and records its `--version`; it does
not compare that version with `lean-toolchain`, authenticate the executable, or verify each
expected output file before declaring success. A wrongly supplied executable that ignores
arguments and exits zero would pass the control flow. This is not what happened in the
recorded run: its genuine Lean binary and all expected outputs were checked independently.

The shell runner defaults to the pinned Elan directory, but a `GQ2_W361_TOOLCHAIN` override
is not checked against the pin. Lean artifact-version checks help reject incompatible binaries,
but are not an exact toolchain attestation.

Recommendation: validate the selected Lean version/identity against the intended pin and
record it with the executable hash; verify output existence before accepting a successful job.

### 4. A frozen source set is not an atomic workspace snapshot

Files are read sequentially during recursive traversal. Once copied, compilation is insulated
from later live edits, but concurrent edits during traversal can produce a mixed-time source
set. The source hashes faithfully identify that set; the script does not claim or prove that it
was one Git tree or one atomic filesystem state. It also does not compare live hashes after
the build. Dependency artifacts remain live throughout compilation.

Recommendation: freeze a Git/filesystem snapshot, or explicitly verify stable source hashes
around snapshot creation and report later drift. Record the exact immutable input set as the
object verified. Do not silently extend the first success marker to subsequent umbrella edits.

### 5. Provenance is useful but incomplete for independent replay

The provenance records source hashes, manifest hash, Lean path/version, target and job count.
It does not record the build-script hash, exact command-line options, package search paths,
dependency artifact hashes, `lakefile.toml`/`lean-toolchain` contents, or relevant environment.
`local_artifacts_reused: 0` is an assertion from the configured search path, not a measured
artifact-load trace. The independent checks above substantiate it for this run under the
observed filesystem, but the JSON alone does not establish it.

Recommendation: make those identities explicit in a future replay manifest. This audit did
not mutate either script to do so.

## The shell runner's narrower contract

`scripts/w361_lean_runner.sh` is a direct Lean invocation helper, **not** a fresh-build verifier.
It checks directories, an executable, and manifest equality, then uses a supplied local artifact
root (or the workspace cache by default). It does not check that imported artifacts correspond
to the current source files, discover/rebuild an import closure, or validate a fresh-run provenance
file. A caller checking a new source against an old artifact root can therefore check against old
imports. Supplying a fresh tree is necessary but not sufficient to establish live-source identity.

`set -euo pipefail` and the final `exec` correctly preserve Lean's exit status. The three leading
options match current project defaults, but caller arguments are forwarded unchanged and can
override options or include `-o`/`-i`. Consequently the header's “nor mutates a cache” describes
the ordinary no-output-argument usage, not a guarantee enforced by the script. A proof build
returning zero also is not, by itself, a no-sorry or approved-axioms check.

## Separate semantic audit: `TameShadowTauColumn.lean`

The new module independently compiles with default settings. Its three printed axiom sets
are exactly `propext`, `Classical.choice`, and `Quot.sound`.

The statements are correctly scoped:

- The primal cochain is `Pi.single tau a`; the dual cochain is zero.
- Coefficients have exponent two; tau and all wild bases act trivially. Sigma's action is
  unrestricted. The resolver's omega value is a natural integer congruent to one modulo four.
- A shadow generator has zero first jets and central charge, and its base has the original
  generator's **action**. It is not claimed to have the original generator's literal base element.
- `HeisActionEq.evalZ` propagates exactly that action-level relation through every word
  constructor, including resolved integer, two-adic, and profinite powers.
- In `splice = shadow(R) * H * shadow(H)⁻¹`, write these lift factors as `p,b,c`.
  Shadow vanishing gives `p.a = c.a = 0`; action congruence gives `act(c)=act(b)`.
  The sole relator-death premise is the **actual changed word**:
  `evalZ(splice)=1`. It implies `act(p)=1`, and therefore the splice's primal tau jet is
  `p.a + act(p)b.a + act(pb)(c⁻¹.a) = b.a`.

No raw-R death, raw-H death, fixed-point-freeness, faithful action, finite-group assumption,
or sigma-two-primary triviality is smuggled into this argument. In particular it does not use
kernel equality to infer a row identity. It proves the literal primal tau-column equality.
The proof is valid; no correction to the root-owned module is requested by this audit.

## Independent retest of the hardened revision

The following is a separate audit of the subsequently hardened scripts, held unchanged by
the parent during these tests. Exact audited SHA-256 identities:

```
w361_fresh_build.py
44c53c42ec62bf9c61c8925e555fcef833df94bc4d669e6848b860850e9f168e
w361_lean_runner.sh
a91afda065314e3344fc7942a0c47bb6a05e3802365c48c38e642a3b16aa4c70
```

This revision replaces the custom scanner with Lean `--deps`, snapshots all local source
bytes before discovering the selected closure, uses only manifest-listed dependency roots,
rejects a `GQ2` artifact namespace inside those declared dependency roots, records the actual
dependency roots and missing declared artifact roots, identifies its driver hash, and records
snapshot start/end times with `snapshot_atomic: false`. Live source/manifest drift is reported
after compilation; `--require-live-match` converts observed drift to exit code 2.

The parent's smoke run `/private/tmp/gq2-w361-fresh-l_pen1h8`, logged in
`/private/tmp/gq2-w361-fresh-hardened-smoke.log`, successfully rebuilt `GQ2.Sanity`.
Its provenance matches the driver hash above, excludes the undeclared ClassFieldTheory root,
and explicitly reports the missing unused Cli artifact root. The smoke alone covers one module,
not the complete campaign.

### Isolated diagnostic results

Test fixtures, copied script implementations, and a diagnostic driver were placed under
`/private/tmp/gq2-hardened-audit.cSBDxT`. Only these isolated fixture sources/manifests were
modified to exercise drift. No campaign source, cache, or script was changed by the audit.

| Case | Observed behavior |
| --- | --- |
| All three former valid-import counterexamples | Four-module closure correctly discovered and compiled; four oleans produced, exit 0. |
| Undeclared Rogue dependency containing `GQ2.olean` | Excluded from both scripts' paths; successful build provenance has no dependency roots. |
| Real Lean type error | Fresh build records the failed module and exits 1; shell runner also exits 1. |
| Missing local import | Compiler dependency parsing reports the missing source; fresh build exits 1. |
| Cyclic local imports | No module is built; both cycle members are reported unbuilt; exit 1. |
| Zero jobs / missing Lean executable | Fresh build rejects each before compilation, exit 2. |
| Manifest mismatch | Both entry points reject it, exit 2. |
| Declared dependency containing local GQ2 artifact namespace | Fresh build rejects with exit 2; shell runner's Python guard rejects with exit 1. |
| Missing shell-runner artifact root | Rejected with exit 2. |
| Live source edit during successful compilation | Reported in `live_source_drift`; frozen-source success retained, exit 0 by default. |
| Live source and manifest edits with `--require-live-match` | Both reported; frozen-source compilation succeeds, final exit 2. |

The successful parser test is `/private/tmp/gq2-w361-fresh-esmyvcp2`. The non-strict drift
test is `/private/tmp/gq2-w361-fresh-eftqcci_`; the strict source-plus-manifest drift test is
`/private/tmp/gq2-w361-fresh-mamsylb3`. In the latter, the success marker is followed by the
drift warning and exit 2. Consumers must use the exit code and result fields, not grep only for
`FRESH BUILD COMPLETE`. This is coherent with successful verification of frozen bytes plus
a failed requirement that those bytes still match the live workspace.

### Remaining reproduced false-clean configuration

The audited hardened revision still accepts `--lean /usr/bin/true`. In the isolated fixture it
recorded one completed module, emitted `FRESH BUILD COMPLETE`, and exited 0 with **zero
olean files**. The result is `/private/tmp/gq2-w361-fresh-kn11wpti`; its recorded Lean version
is empty. This is an explicit wrong-tool configuration, not evidence against the genuine-Lean
smoke or historical full build, but it demonstrates that “pinned Lean” is still a label rather
than a validated precondition in this revision.

The next hardening step should validate the intended Lean version/toolchain and require each
expected `.olean` (and requested `.ilean`) to exist before accepting a zero subprocess status.
The parent has been notified. This audit does not claim a later revision retains this flaw.

The previous scope limitations still apply: manifest equality does not authenticate external
artifact contents; the frozen collection is intentionally not an atomic live filesystem epoch;
the shell helper is not a source/artifact freshness verifier and forwards caller options/output
arguments; and build success is not a replacement for the declaration-level axiom audit. The
new driver provenance and explicit drift fields make these boundaries substantially clearer.

### Second hardening retest: compiler version and output validation

A further bounded independent retest covered these exact revised identities:

```
w361_fresh_build.py
09c3205fc69df40f05694c727f52c9770408add44f1800c72544e615b2aee0c2
w361_lean_runner.sh
4366f47bec06cac743dee81002b06890cc5c15a90fbb093887ee089ef92e745c
```

The former `/usr/bin/true` false-clean configuration is now rejected before discovery with
exit 2 because its reported version does not match the pin. A separate isolated fake executable
reported the expected version prefix but produced no files: the driver now rejected its
zero subprocess status, recorded `GQ2` as failed, and exited 1. The diagnostic log explicitly
names both missing/nonempty-output requirements (`.olean` and `.ilean`); see
`/private/tmp/gq2-w361-fresh-_5wfnkb5`. The shell runner likewise rejects an empty-version
fake toolchain with exit 2. No success marker was emitted by either driver failure test.

The genuine pinned compiler still passes the four-module import-regression build, at
`/private/tmp/gq2-w361-fresh-ab_rqv2h`. This revision records the compiler executable hash
and each successful local olean hash. A self-reported version plus recorded executable hash
is useful identity/provenance data, not authentication of an arbitrary malicious binary that
could spoof version strings and manufacture files; the selected toolchain remains a trusted
input. The tested accidental wrong-tool/no-output false-clean configurations are closed.

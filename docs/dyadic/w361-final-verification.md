# W361 source-bound verification record

Final verified checkpoint, 2026-09-17 17:30 UTC. This is not owner acceptance
or a release certificate. Work continued from 09:10 UTC through the requested
eight-hour minimum at 17:10 UTC and the successful final replay at 17:29 UTC.
The overnight heartbeat was paused at 17:30 UTC after verification.

## Verification contract

- Pinned compiler: Lean `4.31.0-rc2`, exact executable byte hash recorded.
- Manifest-matching external package artifacts are reused. They are not rebuilt
  or independently byte-attested by this local-source check.
- The entire local `GQ2` import closure is snapshotted and built from source,
  using zero local prebuilt artifacts and the compiler's own dependency parser.
- All local `.olean`, `.ilean`, and present private/server/IR companion files
  are inventoried and hashed. Missing, extra or changed local outputs fail.
- Live source, manifest, artifact and staged-content bytes must match before
  and after replay. The builder/verifier explicitly do not claim an atomic
  snapshot, signed build attestation, or proof of editorial prose.
- The full read-only staged suite rechecks the precise headline and artifact
  axiom pins, component tests, symbolic trees, declaration transcripts and
  strong Lean replay against that exact isolated local artifact root.

Reviewed driver SHA-256:
`21b8f1d72e013abac2e142048a61c0c8253e3c539b12c5f145c217c555bcd5be`.
Reviewed verifier SHA-256:
`1b204d792fd744f0faf4122e7a76ebb632921b0a6bd092569a6e8ddd97a628b3`.
Independent checks comprise 38 durable tests, 64 fixture tests and 17 mutations
of an actual two-module build; see `w361-fresh-verifier-independent-audit.md`.

## Earlier conditional checkpoint: 1,531 local modules

Source freeze: 15:54 UTC. Snapshot:
`/private/tmp/gq2-w361-fresh-q_r3y2zv`.
Log: `/private/tmp/gq2-w361-fresh-final.log`.

This source state has the complete relative correction, basis and compactness
adapters, but only the conditional strong N implication. Its shared-cache
umbrella, 504 distinct standard-three artifact pins, 16 exact headline-footprint
pins, ordinary dyadic gate and ledger passed. The ledger scanned 50,777
declarations with zero gaps, unknown axioms or terminal violations. Global
nonstandard axiom declarations remain eleven.

The hardened isolated build **passed** at 16:34 UTC: 1,531/1,531 modules,
2,353.926 seconds, no failed or unbuilt modules, no live source/manifest drift,
and no local output-file drift. The complete inventory contains 3,659 files.
The complete content-inventory replay **passed**, 16:34:23–16:36:58 UTC,
including 16 headline pins, 504 artifact pins, all component tests and all staged Lean
replays. Report:
`/private/tmp/gq2-w361-fresh-verified-atoihjgo/report.json`.
The direct isolated-root ledger independently reports 50,777 tracked declarations,
zero sorry dependencies, zero unknown nonstandard axioms and zero terminal
violations (`/private/tmp/gq2-w361-fresh-1531-ledger.log`).

Recorded source-set SHA-256:
`9c2b9d1825f44ad6ae0de5e9d41eb88764f6f5b3ac0a156a97bd6cca8b1eda78`.
Complete local-output-set SHA-256:
`e0e919b0fa9c090b22a02e582eabe39b82fe3b2aa35c83e674eba0ae42f387ea`.
Replay-log SHA-256:
`37ea75888149af21e235cccf0c1a86eda05ba8a3bf309e847897ee5c911dbebc`.
Sources were integrated only AFTER this replay completed. This is therefore
a valid historical checkpoint, not the current live-source claim.

## New unconditional N checkpoint

Five independently audited production-name modules are now banked and compile:
`NPlaneKernelAllRows`, `NPlaneFullRowRefinement`,
`NPlaneFullRelativeRefinement`, `NPlaneAmbientStage`, `NPlaneGeneralScaling`.
All 26 new pins use only the standard three logical axioms. Exact staged hashes
and proof review are in `w361-n-general-scaling-audit.md`.

Also banked/default-green are `DNAutomorphismCup` (8 pins), `NTorsionAdjust`
(7 pins), and `FreeProTwoModTwoCharacters` (3 pins). The banked strong-N
sources match their independently audited production hashes exactly. Root
independently read and recompiled all three additional modules; no placeholders,
axioms, native decisions or option changes occur in the eight new files.

The full torsion-row bridge and final existence theorem are now integrated:
`NStabilizerFullRows` adds 24 pins and `NStabilizerFullLift` adds one. Their
independent proof/scope and production-byte audit is
`w361-n-full-row-independent-audit.md`. This realizes every prescribed core
`NStabParam` coordinate, including torsion, with identity handle columns.
It does not assert arbitrary handle-mixing stabilizer lifting.

All ten increment modules compile at default limits; their 69 new pins have
only standard-three axioms. Shared umbrella 1,541 PASS and artifact audit 573
PASS. Static cross-check confirms 573 distinct names and 79 audit imports, all
inside the 1,541-module snapshot. Logs:
`/private/tmp/gq2-w361-umbrella-1541.log` and
`/private/tmp/gq2-w361-artifact-audit-573.log`.

Full ordinary gate WITH ledger PASS, scanning 50,854 declarations, no sorry
dependencies, unknown nonstandard axioms or terminal violations; global
declaration census 11 and all frozen regressions remain unchanged. Log:
`/private/tmp/gq2-w361-gate-final-1541-ledger.log`.
Corrected raw scoreboard PASS, scanning 1,546 source modules (the 1,541 closure
plus five intended exporter drivers outside):
`/private/tmp/gq2-w361-scoreboard-1541-corrected.log`.
An initial scoreboard invocation selected an absent default mirror and failed
to resolve GQ2. Supplying the actual shared artifact and matching package roots
fixed that environment error; no source or assertion was weakened.

**Final source freeze: 16:45 UTC.** Complete isolated build PASS at 17:25 UTC:
`/private/tmp/gq2-w361-fresh-egoma1il`, all 1,541 modules in 2,414.159 seconds,
zero local artifact reuse, and 3,679 inventoried output files. There are no
failed or unbuilt modules and no live source, manifest or output-file drift.
Log: `/private/tmp/gq2-w361-fresh-unconditional-final.log`.
The current build's complete content-bound replay **PASS**, from
17:26:09 to 17:29:11 UTC. It rechecked 16 headline and 573 artifact axiom pins,
all component tests, four word specimens, six L/N word specimens, two Fox
specimens, the phase and cover specimens, and all four combined ten-item
packets. Sources, compiler, manifest, all local outputs, 21 replay-source files
and 62 staged-content files matched before and after the suite.

Original report:
`/private/tmp/gq2-w361-fresh-verified-mw059e4v/report.json`.
An exact byte-for-byte durable copy is
[`w361-final-verification-report.json`](w361-final-verification-report.json).
Report SHA-256:
`bb20e9914dd86be093521808b0267f8ac0f6cd857fe6e13b8285d8213784abcb`.
Current local source-set SHA-256:
`285d59846224c7de5fc2d5ad356698103c6999541ed6ab8823f24327770d01d1`.
Complete local output-file-set SHA-256:
`f8796aef65256aadb074e5d5809cb73d4c753d3f173a361a0b0d4db606278eff`.
Replay-log SHA-256:
`d476543de4c693b3c395ec4261e59f9781cc729287b482a34fb4cc130c0f8be6`.
The durable report also retains primary-olean, compiler, manifest, provenance,
result, replay-source and staged-content hashes.

The direct fresh-root ledger independently **PASS**: 50,854 tracked
declarations, zero `sorryAx` dependencies, zero unknown nonstandard axioms,
zero terminal violations. Log:
`/private/tmp/gq2-w361-fresh-1541-ledger.log`, SHA-256
`805c498c26d42d5e7860c3f2066434d783353babe26b98b88f70b2931084cac1`.

An independent reviewer repeated the complete read-only snapshot check AFTER
the replay, rehashing all 1,541 live/snapshot sources and all 3,679 output files,
and compared every returned field with the report. The reviewer separately
confirmed every replay-source/staged-content hash, all ten new modules' audited
production hashes, the replay log and the ledger. No mismatch was found.
This is the current final snapshot, not the historical 1,531-module result.

## Stable staged publication artifacts

The four pair/mobile packets, six legacy L/N word displays and reviewed PDF
are unchanged during verification. The PDF has 29 pages, all visually checked,
with zero TeX overfull/underfull box diagnostics. Its SHA-256 is
`3cec56dc3adde9ad9982225cbc376904a9284224f23ba0c1a07c72f17a4b71bb`.
See `w361-staged-pdf-qa.md` for output, source and page-QA details.

These are staged review artifacts, not adopted replacements for the original
packet or five old appendices. No commit, push, release, frozen-word change,
new axiom, proof placeholder, or option override is authorized by this record.

## Final checkpoint

All required final source checks have exited successfully. The requested
minimum window was exceeded by approximately twenty minutes at the verified
checkpoint. Heartbeat `overnight-dyadic-general-case-research` is **PAUSED**;
its prompt, schedule, task target and other fields were preserved.

Branch and HEAD remain `dyadic` at
`2bf856c94ee3cf2ac89ca41a689f1275cd84ae25`. No commit, push, deletion, new axiom,
proof placeholder, resource override or frozen-word replacement occurred.
All previous dirty work is preserved. The latest `git diff --check` passes.

Any subsequent source, manifest, compiler, audit-script or staged-artifact
change requires fresh corresponding verification. Do not edit the archived
report to imply that this build checked a different source state. Broader
handle-mixing stabilizers, owner adoption and publication work remain explicitly
separate in `w361-restart-handoff.md`.

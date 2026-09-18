# W364 acceptance readiness: the MC-M and MC-N rows

**STATUS 2026-09-18: the target decision is TAKEN (Option A) and the rows it
scores are ADOPTED; the four documentation repairs remain PROPOSED.** The owner
accepted Option A on 2026-09-18 ([owner memo item 4](owner-items-2026-08-05.md)),
and lane W366-APPLY applied the amendment's sections 3 and 4 to the packet, with
the corresponding status in the ledger and in
[the W361 completion audit](w361-completion-audit.md). In the checklist at the
foot of this note, the owner's decision and the adoption of the rows are done,
including the two scope statements, which were carried into the packet rows
themselves. **Still open and not done by W366:** the four documentation repairs
(packet citation / `refs/README.md`, ledger pointer, M family inventory
docstring, stale W363 audit hashes), the final acceptance record, and the
whole-tree build and axiom gate. See [the W366 lane note](w366-apply-note.md).

The original header follows.

**PROPOSAL and readiness review for the owner. Not acceptance, not approval, not
a migration or release record.** 2026-09-17, lane W364-PACKET, base `d2056503`,
toolchain `leanprover/lean4:v4.31.0-rc2`. The authoritative standards remain
[plan A1 and section 7](plan.md),
[ledger sections 7 and 10](refs/dyadic-presentations-formalization-ledger.md),
and the proof packet's own acceptance criteria. This note changes none of them,
and records no owner decision. It is the MC companion of
[the W361 checklist](w361-acceptance-readiness.md) and uses its shape; the
proposed wording it scores is in
[the W364 amendment](w364-proof-packet-amendment-mc.md).

## Bottom line

Both MC rows now have a **finite-list artifact at rank four**, which is what
W361 recorded as missing at N and W363 recorded as missing at both. The
mathematical lifting assertion was already closed at N (W361, Codex) and at M
(W362), as an equivalence, torsion included, at every handle count. What
remains on these two rows is **not mathematics**: it is one editorial decision
about the proof method, two scope statements that must survive into the
acceptance text, and four documentation repairs.

Nothing here touches the field endpoint, its inherited local axioms, the word
certificates, the generated appendix, the hash manifest or the release gate.
No `generated/` artifact exists for MC-M or MC-N, and none is required by the
packet rows: unlike the WC rows, these obligations are discharged by Lean
statements, so the one-tree hash check and the D4 gate do not cover them and
their passing says nothing about these rows either way.

## The two rows

"Verified" means measured by this lane in this worktree, or quoted verbatim
from the Lean at this base. "Proposed" means offered in the amendment and not
adopted. "Decision needed" means an owner call that no amount of further Lean
work removes.

### MC-M

| | Content |
| --- | --- |
| **Verified** | `mFullStabilizer_lift` and `mFullStabilizer_lift_iff` (`MarkedCore/MFullStabilizerLift.lean:144,238`): the full-frame orientation/cup condition is exactly the image of the `chiM`-preserving group-level stabilizer, at every `alpha >= 2` and every handle count, torsion coordinate included, with an all-element commuting square on `abMk`. `mNielsenGen_finite_list` (`MNielsenGenerators.lean:685`): a literal seven-member list drawn from the seven Nielsen families, every member orientation-preserving, a full mod-two cup isometry and lifting, composite equal to the parameter's frame action, composite of the lifts lifting it. `mNielsenGen_stabilizer_induced` (`:845`): the same over every element of the Smith-Witt stabilizer `IsMStabilizer`, concluding `abMk (Psi x) = xi (abMk x)`. 80 axiom pins over the two modules, all `[propext, Classical.choice, Quot.sound]`, both modules elaborating clean at default limits. |
| **Proposed** | The replacement per-core assertion and the replacement MC-M row, [amendment sections 3 and 4](w364-proof-packet-amendment-mc.md). The row as proposed states the discharge and names the qualification (generators lifted by the uniform theorem, not by seven closed-form constructions) inside the row itself rather than in a footnote. |
| **Decision needed** | (1) Accept the uniform filtered-correction and compactness proof method for the generators' lifts, or require generator-level closed-form lifts. Under the second option the outstanding M work is families **M4**, **M6**, **M7** (no construction in the tree), family **M3** (only `MScaling.lean`'s, which consumes axiom **B8** `peripheralCyclotomicAction`), family **M5** (`mMixFamily_coreMix` exists but is stated on `ℤ₂`-valued characters, so it does not pin the full frame's torsion coordinate), and an assembly theorem, which at M does not exist. (2) Accept that the list is rank four (`h = 0`) while the lifting half is general in `h`. (3) Accept that `chi` in the stabilizer quantifier is an abstract character with four pinned generator values, not a descended `chiMab`. |

### MC-N

| | Content |
| --- | --- |
| **Verified** | `nFullStabilizer_lift_iff` (`MarkedCore/NFullStabilizerLift.lean:80`), the N twin of the above. `nNielsen_factorization` (`NNielsenFactorization.lean:357`): every admissible stabilizer parameter factors through the fixed eight-slot list drawn from the six Nielsen families, with the bounded `GL_2(ℤ₂)` factorization and the two admissibility couplings consumed exactly once. `nNielsenFac_finite_list` (`:758`) and `nNielsenFac_stabilizer_induced` (`:911`), the N twins of the M list theorems, with the stabilizer clause `IsNStab` on the rows read in the canonical frame. A second, independent per-family lift route exists at N (`nNielsenFacLifts_of_param_families`). 100 axiom pins over the two modules, all standard three, both elaborating clean. |
| **Proposed** | The replacement per-core assertion and the replacement MC-N row, [amendment sections 3 and 4](w364-proof-packet-amendment-mc.md). |
| **Decision needed** | (1) The same proof-method decision. Under the second option the outstanding N work is family **N4** alone, whose ingredient `nPlaneScalingHypothesis_general` is itself a compactness limit; N1, N2, N3, N5, N6 have their own constructions and the assembly exists. (2) The same rank-four scope statement. (3) Whether W361 amendment section 4 and W361 readiness item 4, which say the MC-N finite-list method "remains distinct" and that the artifact or an acceptance of the alternative is needed, are superseded by the artifact now existing, or retained as the record of their date. [W366, 2026-09-18: ANSWERED. Both W361 records carry dated annotations (W366-HOUSE): superseded on the proof-method point, retained as dated records; and decision (1) is DECIDED, Option A.] |

## Concrete artifact inventory

The MC obligations are Lean-only. At review time the artifacts are these five
modules, at these source SHA-256 values, all registered in `GQ2.lean` at lines
1444 and 1453 to 1456.

```text
MarkedCore/MFullStabilizerLift.lean    cf6c7bbd928d8f31f23fa6b9dfe140e2b0d9325ac06ca8b5498779d0a45aebf3
MarkedCore/NFullStabilizerLift.lean    4e53faea073017932b26665557bf332aaa5b36520bb9c2a5b6641be6d838438d
MarkedCore/MNielsenGenerators.lean     5950dbde9faa560d39132cc851bc547a0db603bf09a83210d0547aa47c752321
MarkedCore/NNielsenGenerators.lean     dd11b0e0c08a598a9afc916e8a6cb24d9dbbe4a49b78ff1310f98ed6bcb4c2c1
MarkedCore/NNielsenFactorization.lean  87a949561474def8d60fb63ec32ea50ba9a45e898b518bd718086d89069b0000
```

Two supporting M modules that the W363 audit pinned separately:

```text
MarkedCore/MFrameCupCoordinates.lean   bc2183b237fb0d103af76d528fb9abef9d52544ee25f61c39ea316e54ff026ca
MarkedCore/MFrameMatrixLift.lean       d1325c69272ec2574d357bd992b8a70a1282eb99ecd1a3270ad5c93e9b24fe42
```

**The W363 audit hashes are stale, and this is a documentation repair, not a
finding against the audit.** `w363-m-full-stabilizer-scope.md` and
`w363-m-full-stabilizer-independent-audit.md` pin
`bac55a1a...`, `0880b523...` and `7f918a66...` for these three M modules. Two
commits have touched them since: `acffa057`, which frees the public name
`mFullStabilizer_lift` for the unconditional theorem and retains
`mFullStabilizer_lift_of_frame` (the audits' subject) as a definitional alias,
and `492fe22e`, docstrings, including the repair of that audit's FLAG-1. This
lane checked the diffs: `MFrameCupCoordinates.lean` and `MFrameMatrixLift.lean`
have **zero** changed declaration lines since the audited hash, and
`MFullStabilizerLift.lean`'s only declaration-level change is the rename plus
the alias. The audits' verdicts stand at the new hashes; their hash lines and
theorem name need a dated update.

## Verification basis and snapshot limits

This lane re-elaborated four modules with
`bash scripts/w361_lean_runner.sh <source>` at the pinned toolchain against the
shared dependency cache. `lake` was not invoked, `scripts/check_dyadic.sh` was
not run, and nothing was written.

| Module | pins | result | exit |
| --- | --- | --- | --- |
| `MFullStabilizerLift.lean` | 10 | all standard three | 0 |
| `NFullStabilizerLift.lean` | 6 | all standard three | 0 |
| `MNielsenGenerators.lean` | 70 | all standard three | 0 |
| `NNielsenFactorization.lean` | 94 | all standard three | 0 |

180 pins, no exceptions, no errors, no warnings. `NNielsenGenerators.lean` (16
declarations, W363) was not re-elaborated by this lane; its pins are the W363
lane note's, and it is an import of `NNielsenFactorization.lean`, which was.

**Limits.** This is an incremental re-elaboration against a shared cache, not a
source-only transitive clean build, not a whole-tree gate run, and not an axiom
census. It is evidence for these four modules at these hashes and for nothing
else. No earlier whole-tree record is extended by it, and the 1,541-module
report referenced in the W361 documents predates all five modules above.

## Owner decisions this raises

Cross-referenced to the wave-362 block of
[`owner-items-2026-08-05.md`](owner-items-2026-08-05.md). **This lane does not
edit that memo.** What follows is what the orchestrator should add, as text the
owner can act on.

### Against memo item 4, "Acceptance of the uniform filtered-correction and compactness proof method"

Item 4 currently reads, in part, that "the packet's section 14 finite
Nielsen-generator list is a separate artifact; W363-NIELSEN is attempting it as
a corollary of the full lifts plus the existing rank-four frame factorizations,
which would let you accept the packet wording literally."

Proposed replacement for that sentence:

> The packet's section 14 finite Nielsen-generator list now **exists at rank
> four for both cores**: `mNielsenGen_finite_list` and
> `mNielsenGen_stabilizer_induced` (W363), `nNielsen_factorization`,
> `nNielsenFac_finite_list` and `nNielsenFac_stabilizer_induced` (W364), all
> std-3. So the decision is no longer whether to accept a method in place of a
> missing artifact; it is whether the delivered artifact satisfies the row,
> given that the individual generators are lifted by the uniform theorem rather
> than by closed-form group constructions. Accepting it discharges both rows
> today. Declining it leaves a named work list: M4, M6, M7 with no construction
> at all, M3 constructible only through axiom B8, M5 constructible only on the
> `ℤ₂` coordinates, an M assembly theorem that does not exist, and N4, whose
> ingredient is itself a compactness limit. See
> `docs/dyadic/w364-proof-packet-amendment-mc.md` sections 4 and 5.

### New items the orchestrator should open

1. **Scope statements that must survive into the acceptance text.** The finite
   lists are rank four (`h = 0`); the lifting halves are general in `h`. And
   "finite list" means finitely many families, one member of each per
   stabilizer element; a finite generating set is impossible. Neither is a
   caveat that can be dropped for brevity, since both are exactly what a reader
   would otherwise over-read.
2. **Packet citation repair.** The per-core assertion is Section 8 of the
   compiled packet (Definition 8.1, Proposition 8.2), not section 7;
   `docs/dyadic/refs/README.md:19` says 7.1 and 7.2. Cite by label or line
   range.
3. **Ledger pointer repair.** The MC-M and MC-N rows are not in the ledger at
   all; they are in the packet TeX section 14. The ledger's corresponding
   content is section 5.1 (`MarkedCoreCertificate`), section 9 item 6, section
   10 and section 11. Several briefs and notes cite the ledger for these rows.
4. **The M family inventory in the module docstring is wrong at M5, and silent
   about B8 at M3.** `MNielsenGenerators.lean`'s docstring says families M3
   through M7 have no independent group-level lift;
   `docs/dyadic/w363-nielsen-note.md` says M4 through M7. The Lean has
   `mMixFamily_coreMix` for the pure M5 move at every parameter and every `h`,
   and `MScaling.lean`'s M3 route consumes B8. No proof depends on these
   sentences, but the Option B work list is read straight off them. Comment-only
   repair, in the shape of W363's FLAG-1.
5. **Stale hashes in the two W363 M audits**, as recorded above. Comment-only.

### Not raised by this lane

The push, the untracked PDF, the changed-M word adoption, the RN interface, the
symbolic display contract, the generated appendix skeletons, G3 and release are
untouched by this wave and keep their existing memo items.

## Checklist after the target decision

- [x] The mathematical lifting assertion, both cores, torsion-sensitive, every
      handle count, as an equivalence. Measured std-3 by this lane.
- [x] A literal finite list at rank four, both cores, with every member
      orientation-preserving, cup-preserving and lifting, and with the literal
      Smith-Witt stabilizer quantifier closed at both.
- [x] The owner's proof-method decision on the two rows (memo item 4 as
      amended above). **Taken 2026-09-18: Option A, the method is accepted.**
- [x] If the method is accepted: adopt the amendment's rows, and carry the two
      scope statements into the acceptance text verbatim. **Done by lane
      W366-APPLY: the packet's section 14 MC-M and MC-N rows now read
      "Discharged", and both scope statements (rank four for the lists, general
      handle count for the lifting halves; the families reading of "finite
      list", with no finite generating set and no finite-word decomposition of
      the limiting automorphism) are inside the rows, not in a footnote.**
- [x] If it is not: commission the Option B work list, and decide separately
      whether a B8-carrying M3 construction is acceptable inside an artifact
      whose entire point is a standard-three footprint. **Moot: Option A was
      chosen, so the Option B work list is not commissioned.**
- [ ] The four documentation repairs above (packet citation, ledger pointer, M
      family inventory, stale audit hashes). All comment-only; none blocks the
      decision.
- [ ] Register the MC rows' evidence in whatever final acceptance record the
      owner chooses, noting that no `generated/` artifact or hash-manifest
      entry exists or is required for them.
- [ ] A whole-tree build and axiom gate at the final release base. This lane's
      four-module incremental run is not that, and does not extend any earlier
      whole-tree record.

Source verification of these modules is not elimination of the general
endpoint's inherited literature axioms, and no new arithmetic axiom or
finite-target proof is needed to finish any item above.

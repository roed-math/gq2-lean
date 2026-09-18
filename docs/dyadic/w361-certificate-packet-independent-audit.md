# W361 independent audit: staged certificate packet

## Scope

This audit concerns the additive ten-item publication pipeline in
`scripts/w361_certificate_packet.py`, the exported word/Fox/phase templates it
combines, and the new compact-N original-record boundary adapter. It does not
approve replacement of the frozen fixture gate or historical appendices.

## Initial mathematical and interface review

The packet correctly distinguishes the corrected pair/mobile splice sources
from the frozen M word. The word environment binds the full two-adic shear
coefficients, actual mobile unit, and chosen profinite correction exponent.
Those values remain symbolic in the displayed template; arbitrary assignments
are not asserted to satisfy the core or source certificate. The structural
parameters and exact environment/denotation declaration names are bound in the
word payload. Pair indices must lie in the actual handle range, and the combined
packet requires `alpha >= 2`.

The three finite-action Fox profiles retain distinct premises. In particular,
the unramified all-cochain formula retains actual changed-word death, while the
ramified formula uses the compatible finite surjective head projection and
actual tame relation; it does not insert raw-word death or commutativity of
sigma and tau. The half-period in a polynomial inverse is the actual coefficient
action half-period, not the handle count or an assumed ambient group order.

The phase template denotes the complete compact quadratic expression, not only
its polar form. Its coefficient matrices are relative to `polar(q)`, not a claim
that this coefficient pairing has identity Gram matrix. The actual boundary
Hessian producers retain the existing source quotient and full-phase linear
coordinate equivalence. The compact even-phase sign is positive in both
sectors; the separate odd L sign distinction is not silently imported into these
pair/mobile appendices.

The original probe checks existence and axiom closure of the named declarations
and prints their inferred types. It does not independently assert expected
theorem types or prove the editorial prose. The actual input-matrix connection
initially used the combination of the concrete source row theorems with the
typed profile's input evaluation theorem; operations and reduced targets have
literal signature-equality bridges to the original Fox records.

The bounded audit follow-up now supplies
`Instances/TameSpliceFoxTemplateInputBinding.lean`. Its six public
`GeneralFoxTemplate.{scalar,unramified,ramified}_{pair,mobile}_input` theorems
state equality of additive homomorphisms from the complete exported input
matrix to the actual pinned `foxJacobian`, not merely equality on cycles or
after row reduction. All original source/action hypotheses remain explicit.
The concrete ramified wrappers discharge specialization and endpoint internally;
no public supplied row identity is introduced. The actual coefficient-action
half-period is retained in the nonscalar profile denotation. All six compiled
with default options, no warnings, and exactly the standard three axioms.

## Assurance boundaries

* Artifact-only validation is not Lean synchronization. A schema-valid AST with
  recomputed hashes is not established to be the named factory output by hash
  checking alone; strong replay compares against Lean's actual output.
* Provenance is an explicit selected list of direct source files. It is not a
  transitive import closure, compiler-artifact provenance, or clean-build record.
* Reading current source hashes does not establish that those bytes produced the
  imported `.olean` files. Nor does it assert a simultaneous live-filesystem
  snapshot. A separately frozen source-only build is the relevant stronger
  attestation.
* Proof-transcript equality can detect a change in displayed signatures, but
  remains distinct from a separately authored typed semantic contract.
* The packet is conditional, parameterized documentation. It does not construct
  a new finite field or instantiate the continuous source parameters.

## Initial issue reported to the owner

Python equality identifies `True` with `1`. In the initial revision, comparing
the section list directly with the generated list admitted a rehashed boolean
in place of section number 1. This is a schema/heading issue, not a Lean proof
issue. The suggested repair is strict integer checking or canonical-JSON
comparison. Test outcomes and the final inspected revision are recorded below
once the complete helper pipeline is available.

A second issue was found when the Fox helper arrived: its fragment functions
return bare `pmatrix`/`aligned` environments, whereas the initial combined
renderer inserted them outside math mode. The owner was notified to wrap those
fragments in display-math delimiters. This is a document-generation issue, not
an error in the matrix identities.

Both repairs are present in the tested revision: section comparison uses
canonical JSON, and each Fox fragment is wrapped in display math. The same
revision adds exact comparison of the stored declaration-type/axiom transcript
against fresh replay. Item 9 now consumes a typed Lean-exported phase-cover
payload with the literal embeddings, diagonal, sign and symbolic dimension;
the packet checks its exact phase hash, tree and handle rank against item 7.

## Isolated runtime checks

The inspected script revision has SHA-256
`0a64428fdcd382e38939f227e8783056350988ec776ec609bc36738258388e21`.
The isolated run is under
`/private/tmp/gq2-w361-packet-audit-ZHbN7g`, separate from generated publication
artifacts. It builds mobile alpha=2/r=1/p=0/h=0 and pair alpha=2/h=1/j=0 packets.
Both passed artifact-only checking and actual Lean replay, including 29 cited
declaration probes per family. The word/Fox/phase/cover helpers independently
passed their existing tests (word 37, Fox 81, phase 44, cover 51).

Deliberately forged but schema-valid word, Fox, phase and cover data were
rehashed, including a forged phase with coherently updated cover tree/hash.
Artifact-only checks accepted these only in their explicitly limited mode;
actual Lean replay rejected each at the relevant factory comparison. Strict
section booleans, alpha below the analytic bound, mismatched ranks, changed
direct-source provenance, unsafe binding names, boolean matrix/sign entries,
wrong cover phase bindings, opaque Fox inverses, extra fields, duplicate JSON
keys, empty directories, out-of-scope output paths and a failing runner were
also rejected.

The full isolated harness ended with `INDEPENDENT_PACKET_AUDIT_PASS|32` and exit
zero. Its final cases confirm that a forged proof transcript with a coherently
updated manifest is rejected by exact strong replay, while direct TeX/probe
drift, changed file bytes, and manifest path traversal are rejected by the
corresponding artifact checks.

The private harness and log retain the exact bounded mutations. They do not
change the repository scripts or Lean sources. This check is independent of the
owner's separate four-packet build and later frozen-source build.

## Remaining editorial/layout review at this revision

Two small mathematical-scope clarifications were reported to the owner:

1. The mobile factory quantifies arbitrary eta and r/p. The sentence that the
   unit *is* congruent to a selected representative requires a field-selector
   context not supplied by this generic packet. It should be conditional on
   such selection, or omitted in favor of the exact actual-unit equation.
2. Item 3 should state finite C and finite exponent-two A as common hypotheses
   of all three Fox profiles, not only mention them in the unramified sentence.
   The printed theorem types already retain them.

No input path for LaTeX command injection was found: declaration/binding names
are fixed identities, structural numbers are strict integers, and symbolic
identifiers are validated and escaped. This does not by itself establish page
layout. In particular the shared-subtree word renderer can leave the final
mobile root expression as a single enormous line; this was flagged for the
owner's PDF compile/render review. Scaling that line to page width alone would
not make it a legible publication display. A size-based exact abbreviation or
multiline decomposition can improve layout without changing the AST or proof.

The owner subsequently assigned this display repair as a separate task. The
revised exact subtree-DAG renderer, its 142 tests and unchanged Lean-replayed
template hashes are documented in `w361-word-display-layout.md`. The packet
owner handles regeneration of combined packets and physical PDF verification;
the 32-check runtime record above remains tied to its stated earlier revision.

## Independent compact-N boundary check

`CompactNBoundaryHessianCertificates.compactNBoundaryHessian` was independently
recompiled from its current source with the durable Lean runner and pinned
toolchain, without writing any new cache artifact. Its dependencies came from
the shared campaign cache; this is a fresh module check, not a transitive clean
build. It completed with no warnings and exactly `propext`, `Classical.choice`,
and `Quot.sound`.

The theorem's conclusion is the original `SourceCompactHessian` at the actual
boundary descent `rhoPrimeK`, uniformly in all handle ranks including zero. The
normal-coordinate map and full quadratic identity are inherited from the actual
compact-N source comparison. Its explicit mathematical inputs remain the finite
marked target/minimal block, exponent-two scalar target, nonzero even q,
`alpha >= 2`, compatible tame/pro-two boundary maps with prescribed generator
values, nontrivial block action, nonzero radical functional, and actual boundary
lift. No head-sector, fixed-point-free, phase, inverse, dimension or cardinality
premise is added. The two sector branches construct their head hypotheses from
the public boundary marking/profile theorems.

# Index of the W360/W361 document corpus

Compiled by the W362-HOUSE lane against the tree at `6770a87e`, which is the
commit that first tracked all 71 of these files. Every entry below was read at
that hash; nothing here is carried over from an earlier note.

The corpus is 69 Markdown documents and 2 JSON verification reports, all
matching `docs/dyadic/w36*`. Six classes are used:

- **verified record** -- states what a checked artifact proves or what a run
  observed. Cite these.
- **audit** -- an independent read-only review reaching a verdict.
- **scope note** -- delimits what a result does and does not say, or maps the
  next task. Carries no new theorem.
- **proposal (not adopted)** -- proposes a statement, format or migration that
  needs an owner decision. None of these is approved.
- **handoff** -- wave-boundary state transfer.
- **template** -- describes a staged export format and its Lean bindings.

A document's class is what it *is*, not what it covers: an audit of a template
is an audit.

## Start here

`w361-claude-code-handoff.md` is the current entry point, and
`w361-claude-code-verification-report.json` is the evidence it binds.
Everything else is reachable from those two.

---

## Handoffs (3)

| Document | One line |
| --- | --- |
| `w360-restart-handoff.md` | W360 resumption state: the general even-M source and odd-L arithmetic, at local tip `2bf856c9`. Superseded. |
| `w361-restart-handoff.md` | The 17:30 UTC overnight checkpoint, 1,541 modules / 573 pins. Its own header sends readers to the Claude handoff instead. Superseded. |
| `w361-claude-code-handoff.md` | **Current.** The Codex-to-Claude transfer: full N stabilizer lifting proved, 1,552 modules, 691 pins, census eleven, remaining work and runtime commands. |

## Verified records (24)

| Document | One line |
| --- | --- |
| `w361-claude-code-verification-report.json` | The durable replay report binding the 1,552-module state; SHA-256 `aad5d041...`, verified in place. |
| `w361-final-verification-report.json` | The historical 1,541-module report; SHA-256 `bb20e991...`, verified in place. Does not cover the eleven N modules. |
| `w361-final-verification.md` | The 17:30 UTC source-bound verification contract and record. Historical relative to the Claude handoff. |
| `w361-overnight-progress.md` | The 978-line running log of the 09:10-17:34 UTC pass. See flag 1: a forward-written log, not a current-state record. |
| `w361-compact-n-boundary-hessian-record.md` | Branch-free original compact-N Hessian record at every actual boundary lift. |
| `w361-npc-boundary-hessian-record.md` | Branch-free original Npc Hessian record at every actual boundary lift of the displayed source. |
| `w361-l-boundary-hessian-records.md` | Original L Hessian records at the actual boundary lifts, uniformly in the handle count. |
| `w361-l-hessian-records.md` | Original L phase-cover and Hessian records for `GammaL`, uniformly in `h`; records that the odd head is not the even compact head. |
| `w361-pair-mobile-boundary-hessian-records.md` | `pairBoundaryHessian` and `mobileBoundaryHessian` at the original radical-cover boundary lift. The shortest document in the corpus (23 lines). |
| `w361-hessian-phase-records.md` | Original Hessian and phase-cover records at arbitrary handle rank for the corrected/spliced M words. |
| `w361-polar-normal-certificate.md` | Basis-independent polar normal certificate for the common even phase. |
| `w361-wall-polar-inverse.md` | Arbitrary-diagonal wall polar inverse, uniform in the handle count. |
| `w361-l-polar-polynomial-inverse.md` | Finite polynomial inverse for the odd L head, uniform in action period and handle rank; closes a limitation recorded in `w361-l-hessian-records.md`. |
| `w361-fox-polynomial-inverse.md` | Closed finite-sum inverse of the unramified Fox pivot under a fixed-point-free odd-period action. |
| `w361-ramified-fox-polynomial-inverse.md` | The ramified Fox inverse as a finite polynomial in the sigma and tau actions. |
| `w361-ramified-fox-normal-certificate.md` | The actual ramified differential of the compact-template splice and its explicit invertible row operations. |
| `w361-scalar-fox-normal.md` | The literal scalar Fox matrix for the actual changed pair and mobile sources. |
| `w361-polynomial-fox-certificates.md` | Literal polynomial inverses inside the original `FoxCertificate` records. |
| `w361-original-certificate-record-bridge.md` | Which original certificate records the actual changed words now instantiate, sector by sector. |
| `w361-fox-input-template-binding.md` | Six full input-matrix identities binding the exported Fox templates to the actual inputs. |
| `w361-general-ln-denotation.md` | Exact denotation of the existing raw L/N factories at arbitrary rank and parameters. |
| `w361-n-plane-actual-mixed-congruence.md` | Checked arithmetic-free mixed-power and relative correction congruences in an arbitrary topological group. |
| `w361-n-plane-compactness.md` | The general-rank exact-row compactness reduction as an iff. See flag 2. |
| `w361-word-display-layout.md` | The four overfull word-display lines and the display-plan-only fix; no word, AST, schema or hash changed. |

## Audits (29)

| Document | One line |
| --- | --- |
| `w361-completion-audit.md` | The campaign-level audit: mathematical endpoint versus acceptance, with an in-place 15:44 UTC status refresh. See flag 4. |
| `w361-final-endpoint-scope-audit.md` | Fresh re-elaboration of the public capstone; confirms the standard three plus nine for the original-marked endpoint. |
| `w361-independent-audit.md` | Interface and claim audit of the pair-splice and mobile-Mpc `FlexibleCertificateLeavesRN` closure. |
| `w361-marked-endpoint-independent-audit.md` | No loophole or circular marking in the five marked-endpoint modules; conclusion is existence with an existentially calibrated realization. |
| `w361-aligned-marking-audit.md` | No circularity or dropped source data in the aligned endpoint; calibration replaces only an existentially carried core realization. |
| `w361-arithmetic-assembly-audit.md` | No defect in the inertia / odd-cyclotomic / relative-norm chain or the canonical field data. |
| `w361-axiom-source-verification.md` | Clause-level primary-source verification for the AX3 and AX4 citation targets. Not an axiom change. |
| `w361-selected-word-audit.md` | Finds that the earlier existential theorem dropped the source constructor, and records the checked strengthening. |
| `w361-full-core-marking-audit.md` | What full marked reconstruction still requires; the fixed-frame exact-image theorem does not by itself give it. |
| `w361-n-full-stabilizer-independent-audit.md` | PASS on `nFullStabilizer_lift_iff`, with the exact equivalence spelled out. |
| `w361-n-arbitrary-basis-refinement-audit.md` | PASS on the three `NBasis*` modules plus `FreeProTwoMatrixBasis` and `NFrameMatrixLift`; all 58 pins read. |
| `w361-n-full-row-independent-audit.md` | Torsion-sensitive N core-row lifting verified, with a 17:30 UTC final-status addendum. |
| `w361-n-general-scaling-audit.md` | Uniform strong N-plane scaling; the reviewed scratch modules are now integrated under production names. |
| `w361-n-plane-scaling-audit.md` | What B8 scaling does and does not prove for N; the stronger statement is not needed by the completed endpoint. |
| `w361-n-plane-primary-source-audit.md` | None of the primary results examined supplies the exact simultaneous integral character action `NPlaneScalingHypothesis` wants. |
| `w361-n-plane-filtered-bridge-audit.md` | The filtered-group results do not by themselves discharge `NPlaneScalingHypothesis`; a header records that later work did. |
| `w361-n-plane-completed-ring-independent-audit.md` | Read-only audit and recompilation of the completed-ring and relative-boundary modules. |
| `w361-n-unrestricted-supply-sanity.md` | Sanity check of the uniform N-stage supply; sections 1-6 are the earlier snapshot, 7 and 8 the later results. |
| `w361-n-boundary-record-independent-audit.md` | PASS on the N-family boundary Hessian records; all five pins print exactly the standard three. |
| `w361-npc-hessian-independent-audit.md` | PASS on the full-offset Npc Hessian records; no source, resolver, coordinate or interface defect. |
| `w361-explicit-matrix-independent-audit.md` | The all-cochain unramified Fox and common-phase polar matrix identities are genuine and do not infer differentials from kernels. |
| `w361-ramified-inverse-independent-audit.md` | No defect in the polynomial inverse and Fox-matrix modules; conclusions are conditional matrix identities, not field-hypothesis discharge. |
| `w361-word-template-audit.md` | The staged templates denote the actual splice constructors, with literal `PWord` equality rather than evaluation equality. |
| `w361-certificate-packet-independent-audit.md` | Audit of the ten-item packet pipeline and the compact-N boundary adapter. Approves no fixture-gate replacement. |
| `w361-phase-renderer-boundary-independent-audit.md` | STAGED audit of the phase renderer; passed after two renderer-side parser fixes, no schema or hash change. |
| `w361-fresh-build-independent-audit.md` | Audit of fresh-build isolation and tau-column semantics. Its findings describe the pre-hardening scripts and are explicitly historical. |
| `w361-fresh-verifier-independent-audit.md` | Audit of the opt-in fresh-content verifier; three in-contract issues found, fixed and retested. Not a release gate. |
| `w361-staged-pdf-qa.md` | Review of the 29-page staged certificate PDF, with wrapper and output hashes. |
| `w361-l-n-certificate-readiness.md` | Family-level readiness audit of the L/N certificate producers against the ledger's ten-item standard. |

## Scope notes (8)

| Document | One line |
| --- | --- |
| `w361-n-full-stabilizer-scope.md` | What the full N stabilizer theorem does and does not settle against the original specification. |
| `w361-m-next-general-scaffold.md` | The next general M lifting task: coupled M-head divisibility and cleanup first, not a new class sweep. Research tasks, not hypotheses. |
| `w361-acceptance-readiness.md` | Readiness review separating proofs, artifacts and owner decisions. Explicitly not acceptance. See flag 4. |
| `w361-n-plane-unrestricted-stage-gap.md` | The N-stage gap and the ambient-stage route that closed it. See flag 3. |
| `w361-n-plane-strong-scaling-research.md` | Historical research checkpoint: six rank-uniform intermediate modules from when strong N-plane scaling was open. |
| `w361-tame-splice-mechanism.md` | Why a new source word was necessary and what the rank-uniform construction is. |
| `w361-compositional-certificate-map.md` | Connects the actual word constructors and checked transformations to the ledger's publication requirements. |
| `w361-general-ln-export.md` | The staged all-parameter L/N export and replay, and the explicit statement that it does not finish the ten-item appendix. |

## Proposals, not adopted (5)

| Document | One line |
| --- | --- |
| `w361-proof-packet-amendment.md` | Proposed replacement statements for the packet's main theorem, marked-matching requirement, source interface and reconstruction proof. |
| `w361-pair-mobile-certificate-appendix.md` | STAGED parametric appendix giving all ten ledger items for the pair and mobile constructors. Not generated TeX, not an approved format. |
| `w361-word-template-proposal.md` | STAGED symbolic word templates: why no finite rational display represents the new two-adic coefficients. |
| `w361-n-plane-relative-graded-correction.md` | A proposed uniform relative mixed-Lie correction identity. Explicitly not a Lean theorem and not an assumed premise. |
| `w361-general-phase-cover-template.md` | STAGED typed phase-cover export format, with no owner approval or migration status. |

## Templates (2, plus 2 cross-references)

| Document | One line |
| --- | --- |
| `w361-general-phase-template.md` | The staged typed quadratic-phase export: syntax, bindings and hashes. |
| `w361-symbolic-fox-template.md` | The staged symbolic Fox-operation template: typed rows, carried inverse coefficients, finite-sum templates. |
| `w361-word-template-audit.md` | (listed under Audits; the template it audits is described in `w361-word-template-proposal.md`.) |
| `w361-fox-input-template-binding.md` | (listed under Verified records; the binding it records belongs to the Fox template.) |

Counting each document once by its own class: 3 handoffs, 24 verified records,
29 audits, 8 scope notes, 5 proposals and 2 templates. That is 71. The two
parenthesised rows in the Templates section are cross-references to documents
already counted under Audits and Verified records, and are not recounted.

---

## Flags: where a headline outruns its body

The docstring-outruns-statement rule applied to prose. The corpus is unusually
disciplined -- almost every document states its own limits in its first
paragraph, and every `GQ2/*.lean` and `scripts/*` path cited anywhere in the
corpus resolves in the tree at `6770a87e`. Four items still deserve a marker.

**Flag 1 (medium) -- `w361-overnight-progress.md` is a log, not a record.**
978 lines, the longest document here, with a title that reads like a campaign
record. It was written forward in time during the 09:10-17:34 UTC pass, so
earlier sections assert states that later sections and the handoff overturn:
the body contains ten "corrected", nine "historical", four "superseded", one
"stale" and four "conditional". It also names about nineteen `.lean` modules
by their then-current scratch names. Do not cite it as evidence for a current
fact; cite `w361-claude-code-handoff.md` section 5 and the JSON report.

**Flag 2 (low-medium) -- `w361-n-plane-compactness.md` has a completion title
over a conditional body.** The title is the bare assertion "the exact-row N
limit is checked". The body says three separate times what is not proved:
"not by itself a construction of its stage inputs"; "The hard remaining input
is **uniform nonemptiness** of these exact-row upstairs sets"; and "It does
not prove ... `NPlaneScalingHypothesis` itself." A later-added preamble
rescues the title by naming the modules that since supplied the inputs, so
the title is true today, but it was not a description of this module's own
content when written. A retitle would fix it; the body needs no change.

**Flag 3 (low) -- `w361-n-plane-unrestricted-stage-gap.md` has the opposite
problem.** 568 lines under a title that names a gap, whose own first line says
the gap is closed and points at `nFullStabilizer_lift_iff`. A reader scanning
titles for open problems lands on the longest resolved-obstacle document in
the corpus. The fix is a title marker, not an edit to the analysis.

**Flag 4 (low) -- two documents carry two vintages in one body.**
`w361-acceptance-readiness.md` and `w361-completion-audit.md` were both edited
in place with timestamped successor paragraphs at the head ("18:55 UTC
successor update", "15:44 UTC additive status refresh"). Their heads are
current and their lower sections are not, and both say so. The hazard is
partial reading, not a false claim.

**Not a flag, recorded to save the next reader the check.** The handoff's
"five old appendix skeletons still contain 40 recorded TODO invocations" is
exact. A grep for `dyadicAppendixTODO` under `generated/appendix/` returns 45,
because each of the five files also carries the macro's definition on a
commented-out line. Eight real invocations per file, five files, 40.

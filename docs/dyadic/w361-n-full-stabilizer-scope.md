# W361 full N stabilizer: original-specification scope

2026-09-17, 18:54 UTC. Independent read-only proof/interface review and fresh
default-limit elaboration; this note does not approve a release or amend the
authoritative packet. It supersedes the earlier *remaining arbitrary N
handle-mixing* assessment, not the historical verification reports.

**Later integration addendum:** the full 1,552-module clean build and complete
691-pin staged replay have now passed. The current checkpoint is documented in
`w361-claude-code-handoff.md` and its separate durable verification report;
the integration task below records what remained at this audit's 18:54 review.

## The mathematical N lifting assertion is now proved

In `GQ2/Dyadic/MarkedCore/NFullStabilizerLift.lean`,
`GQ2.Dyadic.MarkedCore.nFullStabilizer_lift` proves, for every `alpha >= 2`
and every `h`, that every continuous automorphism `phi` of

```text
NFrameModel h = Z/2 × Z₂³ × Z₂^(2h)
```

preserving the transported **actual** orientation `nFrameOrientation` and
the full `NFrameCupIsometry` has an actual continuous lift `Psi : DN ≃ DN`
such that, simultaneously for **every group element** `x`,

```text
chiN (Psi x) = chiN x
nPhiHom (abMk (Psi x)) = phi (nPhiHom (abMk x)).
```

`nFullStabilizer_lift_iff` proves the converse as well. No identity-handle
restriction, diagonal-matrix restriction, `NStabParam` classification,
finite-stage supply, initial-error assumption, or hypothetical group lift is
an input. The torsion coordinate and all handle coordinates are retained.
The canonical `nFrameExists_phiEquiv` is a proved equivalence with the actual
topological abelianization, so this is not a theorem about an unrelated
coordinate model. Transport along that equivalence gives the corresponding
statement on the actual abelianization itself.

The orientation is not chosen after finding a lift:
`nFrameOrientation` transports `abLiftG (chiN ...)` through the canonical
frame. The cup predicate quantifies over **all continuous F₂ characters** of
that frame, including its torsion coordinate. `nFrameModel_map_t` in `N.lean`
shows that every frame automorphism fixes the unique nontrivial order-two
element; the N torsion-relation clause is therefore automatic, not omitted.

Checked proof anchors:

- `NFrameMatrixLift`: actual full-frame automorphism → actual free pro-two
  basis, literal fixed head, exact all-element frame projection, actual
  orientation preservation.
- `NFrameCupCoordinates`: all-element coordinate-character pullback and
  semantic full-frame cup isometry → reduced row-cup equality.
- `NInitialCupDepth`: exact class-two commutator expansion, symmetric-matrix
  contraction, complete ordered handle product and actual relator error in
  lambda-three. The column-image variance is `Abar G Abarᵀ = G`.
- `NBasisRelativeRefinement`, `NBasisExactStages`, `NBasisFullFrameLift`:
  actual arbitrary-basis corrections and all higher stages retain the entire
  initial ordinary-coordinate matrix; the initial head equality supplies the
  exact ordinary relator row.
- `NFullFrameStageTransfer`, `NFullFrameCompactness`: torsion-sensitive
  stage projection and compact limit give one actual DN automorphism;
  `NFullStabilizerLift` extends generator equations to the all-element square.

This is a uniform proof, not a rank/class sweep or finite-target test.

## What this settles in the governing packet

The authoritative proof packet
`refs/dyadic-presentations-formalization-proof.tex:732–735` asks that every
orientation/relation/cup-preserving automorphism of the abelianization lift.
The new theorem supplies that mathematical sufficiency for N, including
arbitrary handle mixing, and gives an exact image characterization. The
rank-four case is `h=0`; no further handle decomposition is needed to prove
surjectivity for larger `h`.

However, packet lines 1077–1082 and plan §2/A3 also prescribe a **finite list
of orientation-preserving Nielsen generators** whose lifts and compositions
realize the stabilizer. The new proof does not exhibit such a finite list or
a finite-word decomposition of every final automorphism. Its initial basis
uses explicit coordinate words, but its corrected limit is obtained by
filtered refinement and compactness. These are different assertions.

Thus there is no longer a missing mathematical N stabilizer-surjectivity
theorem. There remains either a literal finite-family/decomposition artifact
to construct, or an owner/editorial decision to accept this proved general
lifting theorem as the replacement proof method for §14. Such acceptance
need not weaken the mathematical target. Do not describe the proof already
present as a finite Nielsen-list certificate, or infer an algorithm producing
a finite expression for its compact-limit witness.

The earlier proposed amendment replacing MC-N by only a primitive-row
correction is now unnecessarily weak as a description of the available N
theorem. Historical notes saying arbitrary N handle mixing remains unproved
refer to the earlier 1,541-module checkpoint and need a dated update, not a
retroactive change of what that snapshot verified.

## Remaining campaign requirements for the next agent

1. **Integration/verification of this increment.** This new proof is outside
   the archived 1,541-module/573-pin report. Preserve that immutable snapshot.
   Register the reviewed new modules/pins and rerun the appropriate whole-tree
   and axiom gates before claiming a newly integrated verified endpoint.
2. **M is separate.** N's full lifting theorem does not prove the analogous
   unrestricted M stabilizer claim. Existing M marking consumers and the
   canonical-or-strict-handle alternative already suffice for the selected
   field theorem; this does not identify them with every originally requested
   pure Nielsen-family lift. Audit or prove that larger M statement separately
   if retaining the literal original MC-M criterion.
3. **Changed words remain changed.** The proved general field endpoint uses
   the selected pair/mobile M splices when required. It does not resurrect
   the obstructed universal frozen-M placement claim or establish a
   tame-compatible identification with that old candidate. Adoption of the
   revised source profile, semantic-unit congruence and corrected RN interface
   remains a substantive paper/owner decision.
4. **Field scope is unchanged.** The preferred
   `hasSelectedOriginalMarkedWordPresentationRN_ramifiedI` retains explicit
   `RamifiedIData K`, an existential selected source and calibrated realization,
   complete RN certificate, original cyclotomic character and full Z₂
   unramified character. It does not preserve every externally prescribed
   pro-two realization. The new N theorem adds no non-RI field coverage and
   eliminates none of the field endpoint's inherited local axioms.
5. **Publication/release work remains.** Adopt the staged ten-item display
   contract; complete or explicitly supersede the L/N appendix skeletons;
   decide which frozen M artifacts remain regression-only; bind the intended
   release tree through strong replay and the accepted checker. Typed
   word/Fox/phase/cover payloads do not independently serialize the entire
   source quotient coordinate map or prove completeness of editorial prose.
   The five old appendix skeletons still have their previously recorded 40
   TODO invocations; passing their old word-hash gate is not appendix completion.
   Authoritative packet/freeze/census/release updates require owner authority.

The mathematical roles of the nine lanes are already supplied for the
revised selected ramified-i field theorem. The new result additionally closes
the stronger original N lifting assertion; it does not by itself certify
every unchanged original intermediate statement or publication requirement.

## Independent check evidence

Fresh default elaboration of `NFullStabilizerLift.lean` exited zero, without
warnings; all six public pins use exactly `propext`, `Classical.choice`, and
`Quot.sound`. Log: `/private/tmp/gq2-w361-n-full-stabilizer-independent.log`.
Source SHA-256:

```text
4e53faea073017932b26665557bf332aaa5b36520bb9c2a5b6641be6d838438d
```

`NFrameCupCoordinates.lean` was independently read and re-elaborated, all nine
pins standard-three and no warnings, log
`/private/tmp/gq2-w361-n-frame-cup-independent.log`, source SHA-256
`1a27fcca678f3fe84742e34d08f74ef664e270e00f355e607066d432e2d0c568`.
`NInitialCupDepth.lean` additionally has an independent sibling read/compile
audit of all 30 standard-three pins. These are incremental checks using the
pinned compiler and dependency cache, not a new complete clean-build report.

# W361: independent audit of the full N stabilizer lift

Date: 2026-09-17. Audit lane: `odd_front_audit`. No proof, umbrella, or
script changes were made during this audit.

## Verdict and exact scope

**PASS.** `MarkedCore.nFullStabilizer_lift_iff`, in
`GQ2/Dyadic/MarkedCore/NFullStabilizerLift.lean`, proves the following for
every `alpha >= 2` and every handle count `h`.

For an actual continuous automorphism `phi` of `NFrameModel h`, the
following are equivalent:

1. There is an actual continuous automorphism `Psi` of `DN alpha h`
   preserving `chiN`, with
   `nPhiHom (abMk (Psi x)) = phi (nPhiHom (abMk x))` **for every element** `x`.
2. `phi` preserves the canonical orientation and `NFrameCupIsometry`.

The frame is the full topological abelianization model, including the
`ZMod 2` torsion coordinate and all integral handle coordinates. There is
no identity-handle, plane-block, diagonal-matrix, initial-basis,
initial-depth, derivative-image, or stage-supply premise in the final
theorem. The torsion generator is automatically fixed by any frame
automorphism because it is the unique nontrivial element of order two.

This closes the **general, torsion-sensitive N stabilizer lifting
existence statement**, including arbitrary allowed handle mixing. It is
stronger than the earlier `NStabParam` core-plus-identity-handles endpoint.
It is not an assertion that every arbitrary matrix lifts: the actual
frame automorphism must preserve the displayed invariants.

## Critical proof checks

- **Actual frame to actual free basis.** `NFrameMatrixLift` constructs the
  canonical zero/one torsion-coordinate lift of the full frame columns.
  Every index-two character factors through the actual N frame; frame
  invertibility therefore gives Frattini surjectivity and Hopficity.
  No invertible integral lift is assumed. The initial free automorphism
  fixes generator zero literally. Its orientation is the transported
  actual `chiN`, proved equal to `nUnit alpha` raised to the integral
  b-coordinate.
- **Semantic cup condition.** `NFrameCupCoordinates` quantifies over all
  actual continuous F2 characters of the frame. Its coordinate zero is
  the torsion character. Pullback to the free group is the reduced
  ordinary coordinate on every element, not merely on generators. No
  DN group lift is used to prove the sufficient cup condition.
- **Correct variance and literal initial depth.** `NInitialCupDepth`
  uses generator-image columns and the row pairing `Abar G Abar^T`.
  The symmetric difference of the tail coefficient matrices contracts
  to zero against the symmetric, alternating actual bracket in
  lambda-two/lambda-three. Matching head columns removes the diagonal
  cup term; literal head fixation makes the entire head power equal.
  The conclusion is an actual quotient equality and membership of the
  relative relator error in lambda-three, not a span membership claim.
  Every handle block occurs, uniformly in `h`.
- **Arbitrary-basis refinement.** `NBasisRowRefinement` obtains inverse
  coordinates from the genuine inverse automorphism. Closed-kernel
  powers and a finite ordered product give exact diagonal row witnesses.
  After separately justified head cleanup, all rows, including the
  b-coordinate, are cleared. `NBasisExactStages` retains every entry of
  the initial integral coordinate matrix; no diagonal restriction
  reappears in the induction.
- **Torsion-sensitive compactness.** Exact free coordinates determine
  every commutative pro-two map, so `NFullFrameStageTransfer` preserves
  the full abelianization, not merely its torsion-free quotient. Exact
  marking, orientation, and finite Frattini generation are closed
  conditions. Nested compact stages give a limit without any assumed
  compatible choice of witnesses.
- **All-element square and necessity.** The final generator equations
  are upgraded using `dn_hom_ext` for continuous homomorphisms; the
  conclusion genuinely quantifies over every `x`. In the reverse
  implication, surjectivity of the canonical frame quotient transports
  orientation preservation. The previously checked actual
  `DNAutomorphismCup.evenCupForm_comp_dn_aut` supplies cup necessity.

## Verification performed

Each of these files was read and separately recompiled by this audit
lane with `bash /private/tmp/gq2-w360-lean.sh <source>`:

| Module, under `GQ2/Dyadic/MarkedCore/` | Public axiom pins |
| --- | ---: |
| `NBasisRowRefinement.lean` | 6 |
| `NBasisRelativeRefinement.lean` | 1 |
| `NBasisExactStages.lean` | 2 |
| `NInitialCupDepth.lean` | 30 |
| `NFrameCupCoordinates.lean` | 9 |
| `NFullFrameCompactness.lean` | 7 |
| `NFullFrameStageTransfer.lean` | 4 |
| `NBasisFullFrameLift.lean` | 4 |
| `NFullStabilizerLift.lean` | 6 |

All passed at default limits without warnings. All 69 listed pins print
exactly `propext`, `Classical.choice`, and `Quot.sound`. The audit lane
authored `FreeProTwoMatrixBasis` and `NFrameMatrixLift`, so its own checks
of those two files are not counted here as independent authorship review.

Final source SHA-256 values for the critical new boundaries:

- `NFrameCupCoordinates.lean`:
  `1a27fcca678f3fe84742e34d08f74ef664e270e00f355e607066d432e2d0c568`.
- `NInitialCupDepth.lean`:
  `1ba5a73c92740584da6505d659a76327bae94fb2366fe884e64f01448eecd2df`.
- `NFullStabilizerLift.lean`:
  `4e53faea073017932b26665557bf332aaa5b36520bb9c2a5b6641be6d838438d`.

These are default **incremental source compilations against the shared
dependency cache**, not a new source-only transitive build. They do not
extend the historical frozen 1541-module clean-build report. Final
source-only integration verification is a separate parent-owned step.

## Explicit nonclaims

- The final lift is obtained through compactness; no finite explicit
  Nielsen-generator list or algorithm for its generator words is
  produced. The separate presentation/artifact requirement in
  `plan.md` sections MC-N/A3 is not certified merely by this theorem.
- Literal head fixation is a property of the **initial free lift**.
  The final `Psi` is asserted to have the prescribed full abelianization,
  not to fix the group generator itself literally.
- The theorem is for `alpha >= 2`. It does not assert the same N-frame
  statement at alpha zero or one.
- This is an N-core result. It neither establishes the analogous full M
  stabilizer result nor declares the entire campaign or owner acceptance
  ledger complete.

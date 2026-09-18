# W361: actual changed words in the original certificate records

## Fox: concrete original records produced

`GQ2/Dyadic/Instances/TameSpliceFoxCertificates.lean` constructs the original
`FoxCertificate` record for both actual changed source families, in each of the
scalar, nontrivial unramified, and ramified coefficient sectors:

```text
pairSplice_FoxCertificate_scalar
pairSplice_FoxCertificate_unramified
pairSplice_FoxCertificate_ramified
mobileSplice_FoxCertificate_scalar
mobileSplice_FoxCertificate_unramified
mobileSplice_FoxCertificate_ramified
```

Every result type pins the actual normalized, prime-corrected splice `PWord`,
the marking, and the two pinned resolvers at `4 * exponent C`, inside the
original evaluated `foxJacobian`. The bridge does not substitute a kernel
description or certify only the old compact word.

There is no grammar obstruction: `FoxCertificate` is generic in its atom
alphabet and evaluated Jacobian. The pinned first-jet/`foxJacobian` bridge is
proved at the lift level. In the two nonscalar sectors the actual differential
equals the compact-M differential, so the original compact-M certificate can
be transported while retaining its fixed formal operation list and target.
All matrix equalities in the concrete producers are discharged by proved
source identities, not supplied as extra assumptions.

| Sector | Original-record operations and target |
| --- | --- |
| Scalar | One row operation `addSnd(-1)`; target literally tau / zero. |
| Nontrivial unramified | Original `nCompactUnramOps`: add S times tame row to wild row; target diagonal tau coefficient S⁻¹ and x₂ coefficient 1−S⁻¹. |
| Ramified | Original `nCompactRamOps`: scale x₂ column by S, with inverse S⁻¹; tame row retained and wild target the unit x₂ row. |

The original-record targets are intentionally the existing compact-M targets,
not a claim that these one-operation records themselves contain every further
pivot scaling. The fully identity-pivot reductions and their explicit inverse
operators are separate checked artifacts in the `Sigma*Fox*` modules.

Hypotheses are preserved. Nontrivial unramified producers require actual
changed-word death, not raw-word death. Ramified producers require a
surjective action-compatible projected head with actual projected wild bases
one, tame relation, tau fixed-point-freeness and trivial two-primary tau
action; they require no relator-death premise. Scalar producers use direct
trivial-action exponent calculations and require no relator-death premise.
All use finite C/A and exponent-two A. Concrete structural parameters are
`1 <= alpha`, nonzero even q, supplied `nuP`, and either a pair index or an
arbitrary mobile unit/levels/charge/handle rank. No selected unit pivot is
silently added to these first-order statements.

All nine public declarations compiled with default limits, warning-free, and
have exactly the standard three axioms. The new module was cached. No original
record, original word constructor, old operation list or frozen export fixture
was modified.

## Hessian: compatible interface, separate packaging seam

The original `HessianCertificate dat diag Q Qnf j0 j1` is generic in its two
finite F₂ vector spaces, not tied to a frozen word grammar. It records a linear
change of variables, exact quadratic equality, quadraticity/nonsingularity,
and an original `PhaseCoverCertificate`. It has **no word parameter**, so an
actual word-to-endpoint equation must be retained explicitly in any concrete
producer or accompanying theorem; a bare normal-form record cannot replace
that connection.

For the common arbitrary-handle endpoint
`Q(c0,c1,(u,v)) = q(c0) + B(c0,c1) + sum B(u,v)`, the natural old-format phase
record uses `j0(v)=((v,0),0)`, `j1(v)=((0,v),0)`, diagonal `dat.f(v,v)`, sign +1,
and `baseDim=(h+1)*d` when `#V=2^d`. The cardinality, Gauss, polar and diagonal
identities follow from already proved common-phase facts. The normal endpoint
has an identity linear change of variables; existing actual pair/mobile
Hessian identities can supply the concrete word-facing quadratic equality.

At this inspection, that arbitrary-handle original `PhaseCoverCertificate` /
`HessianCertificate` packaging was not present as a named record producer.
The newer actual-source `SourceWordPhaseComparison` and determinant pipeline
are already proved, including their affine-shift interface. Thus this seam is
record packaging, not a newly assumed phase or missing determinant argument.
Hessian implementation is not part of this Fox bridge.

This closes the original **Fox record-production** question. It does not by
itself approve a revised appendix presentation, symbolic export grammar, or
release contract.

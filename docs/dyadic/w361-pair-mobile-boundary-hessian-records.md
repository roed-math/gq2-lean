# W361 — original pair/mobile Hessian records at actual boundary lifts

2026-09-17. Checked additive record packaging, not an owner amendment.

`Instances/TameSpliceBoundaryHessianCertificates.lean` provides
`pairBoundaryHessian` and `mobileBoundaryHessian`. Both return
`Nonempty (SourceCompactHessian DD rhoM ... h)` at the original radical-cover
boundary lift, uniformly in every source parameter and handle rank. The pair
requires a genuine selected handle; mobile permits zero handles.

The proofs retain the existing boundary descent, projected marking, semidirect
surjectivity and head-profile argument from the completed determinant modules.
Only the final head-level consumers change: they now keep the original Hessian
record instead of forgetting it to a set equivalence. The exact source word,
`sourceBoundaryMapK`, `rhoPrimeK`, and full QZeroBar phase remain in the result.
There is no extra normal-form, sector, fixed-point-free, matrix, cardinality or
Gauss hypothesis. The existing nonzero/nontrivial boundary hypotheses remain.

Each record includes the same proved F2-linear source coordinates, full compact
wall-handle phase, nonsingularity, and the original phase-cover fields. These are
stronger artifact outputs, not new mathematical premises for the previously
completed field theorem. Both declarations compile without warnings at default
limits and print exactly the standard three logical axioms.

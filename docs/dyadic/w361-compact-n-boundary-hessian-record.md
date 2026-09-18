# W361: branch-free original compact-N Hessian record

`Instances/CompactNBoundaryHessianCertificates.lean` exports
`CompactNBoundaryHessianCertificates.compactNBoundaryHessian`.

For each actual boundary lift of
`NCompact.gamma alpha h q = GammaR (2+2*h) q (nCompactW alpha h)`, the theorem
returns `Nonempty (SourceCompactHessian DD rhoM (scalarActionZmodTwo_triv _) h)`.
The descent datum `DD` and induced map `rhoM` are the actual `descData` and
`rhoPrimeK` associated to that boundary lift and nonzero radical.

`SourceCompactHessian` is the original `HessianCertificate`: the source form is
`QZeroBar DD rhoM`, the target is the complete compact wall/handle form, and the
diagonal is the literal coefficient quadratic `DD.qbar`. Its linear equivalence
with inverse is the same source comparison already used by the compact-N phase
proof. The record also supplies the exact phase identity, quadraticity,
nonsingularity, and original affine-phase record. There is no replacement source,
abstract equicardinality argument, or weakened record type.

## Scope and proof

The assumptions are the existing finite marked target/minimal-block data, elementary
boundary quotient, nonzero even `q`, `alpha≥2`, canonical tame generator equations,
tame/pro-2 ν-compatibility, a nonzero radical, and nontrivial coefficient action.
The theorem is uniform in every handle rank, including zero.

No head-sector choice, fixed-point-free action, odd-order statement, phase identity,
Gauss value, dimension, or cardinality equation is supplied by the caller. All head
facts follow from `projectedHead_marking`, `head_cyclic_of_unramified`,
`head_sigma_fixedPointFree`, and `head_tau_ramified_profile`. The actual original
records are then supplied by `compactNUnramifiedHessian` or
`compactNRamifiedHessian`.

The old boundary comparison's separate simplicity and nonzero-coefficient premises
are unnecessary here: the public head profiles consume the minimal-block structural
simplicity directly, and the retained nontrivial-action premise suffices for the
unramified fixed-point-free conclusion. This weakens, rather than strengthens, the
old boundary input requirements.

The sole split is the uniform dichotomy between trivial and nontrivial tau action.
It is not a field-class or handle-rank enumeration. Both branches retain the same
compact source and target, so unlike procyclic Npc no existentially varying head
diagonal is needed.

## Verification

Fresh default-limit compile passed, warning-free. The public axiom audit is exactly
`propext`, `Classical.choice`, and `Quot.sound`. No old proof module, API, frozen
fixture, or publication acceptance rule was edited.

# W361: original L Hessian records at actual boundary lifts

## Checked endpoint

`GQ2/Dyadic/Instances/LBoundaryHessianCertificates.lean` exports
`LBoundaryHessianCertificates.lBoundaryHessian`. It produces an original
`HessianCertificate` for the actual scalar phase `QZeroBar` of each boundary lift
of `gamma h q`, uniformly in the handle count `h`.

The record uses the same literal projected graph operator as the completed L
phase comparison:

```
U = action((pi(rho0(rho)(sigma)) ^ omega2Exp(4 * exponent(SemiProd C0 V)))^-1).
```

Its normal phase remains `qDouble qbar U + sum_j polar qbar(u_j,v_j)`.
The source-to-normal map is the additive/linear upgrade of the actual full-phase
comparison, not an independently chosen polar isometry.

Both signs are exposed for the same returned certificate:

* `baseSign = -1` if and only if the tame inertia generator acts trivially on
  the actual block module;
* `baseSign = 1` if and only if that action is nontrivial.

Thus the unramified Arf-one branch is not assigned the ramified positive sign.

## Exact scope and premises

The endpoint retains the existing L boundary scope:

* a finite marked target and minimal block, with the usual quotient normality
  instances and exponent-two scalar target;
* a boundary frame and actual tame/pro-two maps compatible with `nu`, whose
  values on sigma, tau and the wild generators are the prescribed ones;
* `q != 0`, `Even q`, and `q = 2^f` with `Odd f`;
* the existing simple, nonzero and nontrivial block-action hypotheses;
* the existing dimension parameter `m >= 1` and `#V = 2^(2*m)`;
* a nonzero radical functional and an actual boundary lift.

There is no supplied sector, matrix, inverse, Arf value, Gauss sum, head model,
normal form, phase comparison or `LRamifiedSourceArfData` premise.
The public head-profile theorems construct the appropriate head model.
`lRamifiedSourceArf_blockK` supplies the ramified source-Arf datum internally.
`LHessianCertificates` then packages the completed phase comparison into the
original record.

## Relation to the explicit inverse

The literal odd-head polar operator is `J = 1 + U + U^-1`. The separate checked
`WordPhaseOddPolynomialInverse` module identifies its inverse with the finite
sum `sum_{i < 2^k} (U + U^-1)^i` whenever `U^(2^k) = 1`; the existing two-power
period supplies such a `k`. This is an exact operator identity, not a rank or
nilpotency-class enumeration. See `w361-l-polar-polynomial-inverse.md`.

## Verification and acceptance boundary

The module compiles with the default Lean options. Its public theorem has the
standard three axioms only: `propext`, `Classical.choice`, and `Quot.sound`.
No existing source certificate is weakened and no old source file is changed.

This closes the original-record boundary adapter in the stated L scope. It is
a staged compositional publication artifact, not an assertion that the owner
has approved replacement of the historical certificate ledger appendices.

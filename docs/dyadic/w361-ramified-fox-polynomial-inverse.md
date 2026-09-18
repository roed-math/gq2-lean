# W361: the ramified Fox inverse as a finite polynomial

Date: 2026-09-17. Staged compositional certificate artifact, not approval of a ledger migration.

`GQ2/Dyadic/SigmaRamifiedFoxPolynomialInverse.lean` completes the displayed inverse of the
ramified row's sigma pivot. For `S` the sigma action and `T` the tau action,

```
U = S⁻¹(T-1),
U⁻¹ = (1-T⁻¹)⁻¹ T⁻¹ S
    = sum (j < m/2) T^(-(2j+2)) S,
```

where `m` is any odd period of the tau action. The order of composition matters: each
summand first applies `S`, then the indicated inverse power of `T`. No commutation of
sigma and tau, tame relation, or restriction on sigma is assumed.

The factorization `T-1 = T(1-T⁻¹)` is proved as equality of the existing additive
equivalences, without any exponent-two assumption. The exponent-two hypothesis is used
only when applying the previously checked odd inverse-power polynomial for `1-T⁻¹`.

The canonical endpoint `sigmaPivot_symm_eq_actionPolynomial` uses

```
m = orderOf (MulAction.toPermHom C A tau).
```

Its hypotheses are finite `C` and `A`, exponent-two coefficients, tau fixed-point-freeness,
and trivial action of `powOmega2 tau`. The latter proves this actual action order is odd;
the element tau itself is not required to have odd order in the ambient group. The separate
arbitrary-odd-period endpoint needs no finiteness of `C`.

The conclusion is literal equality with
`SigmaRamifiedFoxElimination.sigmaPivot.symm`, so it describes the inverse operation already
used in the ramified column shear and diagonal row scaling. The other ramified pivot's inverse
was already the explicit `-S`. Original Fox modules and their hypotheses remain unchanged.

Verification: default Lean, warning-free, all six displayed axiom pins exactly
`propext`, `Classical.choice`, `Quot.sound`. The module is cached in the shared campaign
artifact tree. The identity is uniform in rank and finite action period; it is not a list of
finite-case tests and does not assert a single bounded-degree polynomial for all periods.

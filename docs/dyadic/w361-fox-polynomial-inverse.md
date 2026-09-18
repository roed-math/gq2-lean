# W361: explicit finite-sum inverse of the unramified Fox pivot

Date: 2026-09-17. Additive, staged certificate artifact; this does not record owner approval
of replacing the old ledger appendices.

## Closed formula

Let `A` be an additive commutative group of exponent two, and let `S` denote the action of
sigma. Assume `S` has no nonzero fixed vectors and `S^(2k+1) = 1`. The inverse of the
unramified Fox pivot `D = 1 - S⁻¹` is

```
P = S⁻¹ + S⁻³ + ... + S⁻(2k-1)
  = sum (j < k) S^(-(2j+1)).
```

The sum has `k` terms. This also covers `k = 0`: period one and fixed-point-freeness then
force the coefficient group to be trivial. No positive-dimension assumption is hidden.

`GQ2/Dyadic/SigmaNormalFoxPolynomialInverse.lean` defines this finite sum as an additive
homomorphism `oddInversePolynomial`. The checked proof has two steps:

1. Pair adjacent powers to obtain
   `N = 1 + P + S⁻¹ P`, where `N = sum (i < 2k+1) S⁻i`.
2. The norm image is fixed by `S⁻¹`, hence is zero by fixed-point-freeness. Since `A` has
   exponent two, `P - S⁻¹ P = 1`. The polynomial commutes with `S⁻¹`, so `P D = D P = 1`.

The period-based construction does not require `A` or the acting group to be finite.
`polynomialPivotEquiv` has `D` as its literal forward function and `P` as its literal inverse.
Both inverse identities are proved, rather than inferred from a finite counting argument.

## Canonical period under the existing Fox hypotheses

For finite `C` and `A`, put

```
m = orderOf (MulAction.toPermHom C A sigma).
```

This is the order of the actual sigma action, not its possibly larger order in `C`.
The hypothesis `∀ a, powOmega2 sigma • a = a` implies that `m` is odd. Naturality sends
the two-primary projection into the permutation group; if an element there had even order,
its order would divide its omega exponent while that exponent is odd, a contradiction.
Thus `m` is an action period and `k = m / 2` is a canonical valid summation bound.

The endpoint `oneSubInvAction_symm_eq_actionPolynomial` states exactly

```
(oneSubInvAction sigma hfpf).symm a
  = sum (j < orderOf (MulAction.toPermHom C A sigma) / 2)
      (sigma⁻¹)^(2*j+1) • a.
```

Its hypotheses are precisely finite `C`, finite `A`, exponent two, sigma
fixed-point-freeness, and trivial action of sigma's two-primary part. No odd-order
assumption on sigma in the ambient group is inserted. The period is independent of a
choice of basis. The generic odd-period theorem also accepts any supplied odd action period.

## Compatibility and scope

`oneSubInvAction_eq_polynomialPivotEquiv` identifies the new explicit equivalence with the
existing `SigmaNormalFoxElimination.oneSubInvAction`. Consequently the old row certificate
and its inverse operations are unchanged; the new result supplies the closed expression for
the previously choice-constructed inverse. No original Fox module is edited.

This is a uniform finite-action identity, not a check of finitely many ranks, groups, or
nilpotency classes. The sum's length depends on the actual finite action period, as expected
for a finite-action formula. It does not assert one fixed polynomial valid at all periods.

## Verification

The new module compiles under the campaign's default Lean settings, with no warnings,
new axioms, placeholders, or option changes. All thirteen displayed axiom pins have exactly
`propext`, `Classical.choice`, and `Quot.sound`. The canonical formula depends on none of the
field, local reciprocity, or duality foundation axioms. Its olean is placed in the shared
campaign cache after a second clean module compile.

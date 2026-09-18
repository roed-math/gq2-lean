# W361: explicit finite polynomial inverse for the odd L head

`Instances/WordPhaseOddPolynomialInverse.lean` closes the inverse-display
limitation recorded in `w361-l-hessian-records.md`. It is uniform in the action
period and handle rank, and does not enumerate nilpotency classes or fixtures.

Let `U : V ≃+ V`, with `v+v=0` for all `v`, and suppose `U^[2^k]=id`. In the
ring of additive endomorphisms (multiplication is composition), put

```
K = U + U^-1,
J = 1 + K,
P = J^(2^k-1),
S = sum_{i=0}^{2^k-1} K^i.
```

The checked identities are

```
K^(2^k)=0,       J^(2^k)=1,
J P=P J=1,      J S=S J=1,      P=S.
```

Commuting Frobenius powers give `K^(2^k)=1+1=0`; the finite geometric-sum
identities then give both inverse products. No finiteness assumption on `V`,
quadratic form, nonsingularity assumption, basis or chosen bijection is needed
for these polynomial identities. They include `k=0`.

`inverseSumPolynomial_apply` displays the vector-level operations explicitly:

```
S(v) = sum_{i<2^k} (w ↦ U(w)+U^-1(w))^[i](v).
```

`polynomialWallEquiv` has literal forward map `v ↦ v+Uv+U^-1v` and this sum as
its specified inverse, even without finite `V`. For the existing finite
certificate, `wallPolarEquiv_symm_eq_sum` and `wallPolarEquiv_symm_eq_power`
identify its inverse with `S` and `P`. The existing existential two-power
hypothesis suffices directly via `wallPolarEquiv_symm_eq_chosen_sum`; no
additional period premise is required when using that endpoint.

`oddCross_eq_polynomial` identifies the original phase-cover edge map literally
as `(S(v),0)`. Thus the displayed operations are tied to the original record,
not to some newly chosen isometry. The original phase and its negative
unramified/positive ramified signs are unchanged.

The module compiles with default Lean options, no warnings, no placeholders and
no new axioms. All 13 printed public pins use exactly `propext`,
`Classical.choice`, and `Quot.sound`. Parent-owned fresh source-only integration
and owner approval of the compositional acceptance format remain separate
checks; this result makes no claim about either one.

# W96: honest ramified compact-M Hessian

Date: 2026-08-16

## Result

`GQ2/Dyadic/Certificates/M0Ramified.lean` proves the handle-free ramified compact-M Hessian
formula directly on the kappa-zero central extension:

```text
hessRelZ(mCompactW alpha 0; c0, c1) = q(c1) + polar(q)(c0, c1).
```

The theorem assumes exponent two on the additive module, odd order and fixed-point-freeness
for the tame `tau` action, and correctness of the resolver.  It does not assume that the
two-primary part of `sigma` acts trivially, and it does not assume that individual lifted
`(x_i tau)` blocks vanish.

## Construction

The proof evaluates the full word at `evalFin`.  Each charged delta slice is split into a
zero-charge slice and a central inclusion.  The eight zero-charge slices form a moving-line
octagon whose product is `polar q c0 c1`.  All opaque power charges, factor-set moving-line
charges, and the two boundary charges occur twice and cancel in characteristic two.

The shared `J2` block is trivial because its `x2` coordinate is zero.  The remaining head,
commutator, correction, and reverse blocks combine to contribute `q c1` plus the octagon
polar term.  Resolver correctness then transports the finite evaluation to `hessRelZ`.

## Correction to the old assembler

The earlier generic P0 assembler remains a theorem for its stated hypotheses, but those
hypotheses do not describe the honest ramified boundary.  In particular, per-letter
omega-two triviality is false in a finite fixed-point-free example.  This wave replaces that
route with whole-word cancellation instead of weakening or hiding the failed premise.

## Verification surface

All twelve declarations use only `propext`, `Classical.choice`, and `Quot.sound`.  The module
introduces no axiom, `sorry`, `native_decide`, or option override.

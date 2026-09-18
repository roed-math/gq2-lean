# W361: literal scalar Fox matrix for the changed sources

The checked source is `GQ2/Dyadic/Instances/TameSpliceScalarFoxNormal.lean`,
namespace `GQ2.Dyadic.Instances.TameSpliceScalarFoxNormal`.

## Exact matrix and row operation

For an additive coefficient group `A` of exponent two, assume every generator
of the finite acting group marking acts trivially on `A`. Order the columns as
sigma, tau, then all wild generators. For each of the **actual** normalized,
prime-corrected pair and mobile tame-splice sources, the pinned resolved Fox map
is, on every cochain,

```text
D = [ 0  Id  0 ... 0 ]       D(x) = (x_tau, x_tau).
    [ 0  Id  0 ... 0 ]

L = [ Id   0 ]              L^-1 = [ Id  0 ]
    [-Id  Id ]                     [ Id Id ]

LD = [ 0  Id  0 ... 0 ]     (LD)(x) = (x_tau, 0).
     [ 0   0  0 ... 0 ]
```

`scalarRowElimination` is the additive equivalence implementing `L`, with its
inverse proved explicitly. No column operation is needed. In particular the
sigma column is zero as an operator, not merely zero on a previously identified
kernel.

## Why this is an all-cochain calculation

The proof first evaluates arbitrary free words: under trivial action their first
jets are additive exponent evaluations. Applying an elementary dual character
reduces this directly to the literal total mod-two exponent condition in
`IsStokesEndpoint`. Thus the sum of the two first-jet rows is zero. The tame row
is computed independently and is exactly `x_tau` when `q` is even; exponent two
then identifies the second row with the same coordinate.

This argument does **not** infer a column from `d1 ∘ d0 = 0`, a Stokes pairing,
or equality of kernels. It does not assume the relators die in the acting group.
The concrete pair/mobile endpoint producers prove the required syntactic input
for the actual changed words; it is not an extra matrix or analytic premise in
the concrete theorems.

## Public interfaces and scope

- `sum_scalarFox_eq_zero_of_endpoint`: the general direct first-jet/exponent
  identity for a finite relator family.
- `scalarFox_rows_of_endpoint`: the two rows of `gammaFam` are both tau for an
  arbitrary resolved endpoint word.
- `scalarRowElimination` and `scalarRowElimination_diagonal`: explicit invertible
  row subtraction.
- `pairSplice_scalar_rows` / `pairSplice_scalar_reducedFox`: actual
  `headHandlePairSpliceW`, with its normalization, prime correction and splice.
- `mobileSplice_scalar_rows` / `mobileSplice_scalar_reducedFox`: actual
  `tameSplice (mpcMobileTameCorrectedW ...) (MCompact.mCompactW ...)`.

The concrete hypotheses are `1 ≤ alpha`, `q ≠ 0`, `Even q`, finite acting group
`C`, exponent-two `A`, and trivial action of every marked generator. Pair
parameters include `j : Fin h`; mobile parameters allow arbitrary `r`, `p`,
unit `eta : ℤ_[2]ˣ`, and `h`, including `h = 0`. Both allow an arbitrary supplied
`nuP : ContinuousMonoidHom (DM alpha h) Ztwo`. The resolver level is exactly
`4 * Monoid.exponent C`. There is no finite-`A` premise, selected-field pivot
premise, prescribed unit-value condition on `nuP`, raw relation-death premise,
or additional analytic hypothesis.

All eight public declarations were compiled with the default limits and have
only `propext`, `Classical.choice`, and `Quot.sound` in their axiom audit.
The finite two-row case split concerns the fixed relator index, not a
field-class or handle-rank enumeration.

## Acceptance boundary

This is a rank-uniform, basis-independent Fox matrix and invertible row-operation
artifact for the scalar sector. It complements the separate nonscalar and
ramified artifacts. It neither changes frozen S1.1 syntax/hash fixtures nor
claims owner approval for replacing the ledger's complete appendix format.
Selection, field hypotheses, certificates and the remaining appendix objects
are supplied elsewhere and are not silently identified with this matrix alone.

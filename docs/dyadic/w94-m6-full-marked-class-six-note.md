# W94: exact full-marked class-six certificate

Date: 2026-08-16

## Result

The full four-slot marked move from W92 kills the actual M6 class-six defect in the exact
maximal exponent-2 quotient through class five.  The old two-slot specialization does not.

This is an exact finite-group computation, not a sampled Magnus ansatz.  The scripts construct

`Q = <A,B,C,D | A^2 [A,B] C^4 [C,D]> / lambda_6`

with Magma's `pQuotient`, use the actual subgroup intersections for the correction carriers,
evaluate the exact increment map, and solve membership in the fifth lower exponent-2 layer.

## Dimensions and membership

The quotient has order `2^322` and lower-layer dimensions

`[4, 9, 25, 70, 214]`.

At layer four, the marked carrier has dimension `68` and the derived pivot carrier has
dimension `67`.  The four slot images have ranks `[68, 67, 67, 68]`; their cumulative image
has rank `209` in the 214-dimensional target.

The W5 defect is nonzero.  It is not in the old `T + N` image, whose rank is `134`, but it is
in the full `S + T + M + N` image.  The reconstructed correction is checked by exact equality
in `Q`.

## Reproducibility

`scripts/w94_m6_full_marked/full_marked.m` performs the unrestricted subgroup-intersection
calculation and asserts the rank, nonmembership, membership, and killing results.

`scripts/w94_m6_full_marked/full_marked_natural.m` independently generates complete natural
commutator-and-square bases for the same carriers, checks that their dimensions equal the
honest subgroup intersections, finds a sparse solution, and asserts the killing equality.

## Route correction

The full marked image has corank five, not corank one.  Consequently it cannot contain an
arbitrary codimension-one chi-twisted Fox kernel.  The remaining uniform theorem must prove
that the specific M6 defect family lands in this rank-209 image, or enlarge the correction
carriers.  W92's suggested blanket Fox-kernel containment is therefore too strong.

The finite certificate is strong evidence for the four-slot design and a precise target for
formalization.  It is not itself a Lean proof: the tree does not yet have a class-six normal
form or a reflection theorem for this finite quotient, so translating the killing equality
would require a substantial new collection argument.

# W329: syntactic Nielsen pairs

W328 descends a continuous free-profinite equivalence once its relator and wild-core behavior
is known.  W329 supplies the syntax-level producer needed for an actual change of normal form.

A `PWordNielsenPair` is a pair of substitutions on the dyadic alphabet whose two composites
evaluate to the identity on the free profinite generators.  The universal property of the free
profinite group turns the substitutions into mutually inverse continuous homomorphisms, giving
`PWordNielsenPair.freeEquiv`.

`AdmissiblePWordNielsenEquiv` makes the remaining proof obligations finite and explicit: the
tame and word relators die in both directions, and every substituted wild generator lies in the
normal closure of the wild alphabet.  Its `toWildPreserving` constructor feeds W328, and
`gammaEquiv` is the resulting equivalence of corrected candidate groups.

This is uniform in degree, tame modulus, and word.  It replaces a future quotient-level
isomorphism proof by concrete word substitution identities; combined with W327--W328, only the
two tame/pro-2 generator tables then remain before the complete corrected certificate and the
general-K equivalence transport automatically.

All public declarations print exactly the standard trust base
`[propext, Classical.choice, Quot.sound]`.

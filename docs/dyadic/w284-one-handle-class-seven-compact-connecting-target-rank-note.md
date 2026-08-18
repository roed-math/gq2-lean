# W284: rank jump for the compact connecting target

W283 produced an exact finite kernel criterion for membership of the class-seven reference
obstruction in the compact connecting image.  W284 expresses the same condition as a finite
F2-rank computation.

`oneHandleCompactConnectingImageTransposeRank` is the rank of character evaluation on the
connecting image.  `oneHandleCompactConnectingTargetAugmentedTransposeRank E` appends the
reference-obstruction evaluation.  Their range cardinalities are powers of two with these
exponents, and `ordinaryRelativeSolvable_iff_connectingTarget_finrank_eq` proves that equality
of the two ranks is exactly ordinary relative solvability.

The augmented rank can only be the image rank or the image rank plus one.  The latter case is
equivalent to failure and to `OneHandleCompactConnectingTargetDetected E`, an explicit
separating-character certificate.  Thus the ordinary class-seven frontier is now a single
finite one-bit rank decision.  The separate neutral-C condition remains outside this module.

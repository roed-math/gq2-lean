# W222: the torsion row in the neutral source

W222 replaces the quantified character condition in the neutral relative `C` source by an
explicit abelian condition.  On `DM 2 1`, membership in `oneHandleRowKer` is equivalent to the
square of the abelianization class being trivial.  Continuous `Z_2`-valued rows see every
coordinate except the distinguished order-two torsion class, so this is the sharp global
statement.

The handle-forgetting kernel removes that last torsion class.  Therefore
`mem_oneHandleRowKer_iff_abMk_eq_one_of_forget` identifies row-neutrality there with trivial
abelianization, and `oneHandleNeutralRelativeLambdaImage_eq_abMkKernel` rewrites the finite
neutral layer as the image of an exact relative abelianization kernel.

This is a structural reduction, not a dimension assertion.  The next step is to identify the
ordinary relative source modulo this kernel using the two handle coordinates; the expected
`(ZMod 4)^2` model remains to be proved rather than assumed.

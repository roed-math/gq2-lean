# W223: the finite handle-coordinate range

W223 identifies the quotient left by W222 without assuming its size.  The first `U`- and
`V`-handle coordinates descend modulo `2^k` to the `(k+1)`-st two-central quotient.  Their
restriction `oneHandleRelativeUVLevel` to the ordinary relative source has kernel exactly
the image of the genuinely row-neutral relative source:

`ker(oneHandleRelativeUVLevel) = range(oneHandleNeutralRelativeInclusion)`.

The reverse inclusion is constructive.  A class with vanishing finite handle digits admits
an exact relative representative whose two handle coordinates are divisible by `2^k`.
Multiplying by the corresponding deep `Z_2`-powers of the standard handle generators clears
both coordinates without changing the `(k+1)`-level class.  Handle-forgetting and all four
core abelian coordinates are preserved, so W222 makes the corrected representative exactly
row-neutral.

The first isomorphism theorem then gives
`oneHandleRelativeCModuloNeutralEquivUVRange`, a canonical equivalence from the relative
`C` source modulo neutral representatives to the intrinsic range of the two handle digits.
This is deliberately the first of two coordinate stages: W223 proves neither that the range
is the whole ambient product nor that it has cardinality sixteen.  The expected
`(ZMod 4)^2` identification remains the next finite calculation.

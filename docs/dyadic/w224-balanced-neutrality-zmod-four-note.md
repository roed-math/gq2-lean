# W224: the neutral quotient is `(ZMod 4)^2`

W223 reduced the one-handle relative source modulo exact row-neutral representatives to the
intrinsic range of its two finite handle coordinates.  W224 computes that range exactly.

For every `k ≥ 3`, a representative from `lambda_(k-1)` has both handle coordinates divisible
by `2^(k-2)` modulo `2^k`.  Conversely, pure powers of the standard `U` and `V` handle
generators realize those two depth digits independently.  Multiplication by `2^(k-2)` gives
an injective copy of `ZMod 4` in each coordinate, and the two copies fill the intrinsic range.

The public equivalence
`oneHandleRelativeCModuloNeutralEquivZModFourSq` identifies the relative `C` source modulo
neutral representatives with `(Multiplicative (ZMod 4))^2`.  The companion theorem
`natCard_oneHandleRelativeCModuloNeutral` records its cardinality as `16`.  This is an exact
range computation, not a claim that the map fills the ambient `ZMod (2^k)^2` product.

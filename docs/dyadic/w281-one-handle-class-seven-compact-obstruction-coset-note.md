# W281: the class-seven compact obstruction coset

W278 isolated the compact connecting homomorphism, W279 reduced its vanishing to finite range
coverage, and W280 dualized that condition to an exact finite transpose-rank equality.  W281
separates a second issue: whether every value in the connecting image is actually realized by
the difference between two legal compact lifts.

For any reference lift `E`, `compactConnectingObstructionCoset E` is the translate of the
inverse connecting image by the obstruction of `E`.  Every attained packet obstruction lies
in this coset.  The new predicate `OneHandleCompactConnectingRealizedAt E` says that every
connecting-image value is attained by a legal difference from `E`, and
`compactPacketObstructionValues_eq_connectingCoset_iff` proves that this is exactly equivalent
to equality between the finite packet-obstruction set and the whole coset.

No realization or vanishing theorem is asserted.  The remaining class-seven problem now has
two independent finite faces: compute whether the connecting image is zero (the W280 rank
test), and determine whether its values are all realized by legal compact lifts (the W281
criterion).  The cocycle theorem guarantees that no packet obstruction lies outside the stated
coset.

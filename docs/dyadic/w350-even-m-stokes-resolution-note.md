# W350: uniform finite resolution and Stokes endpoint for even M

W350 advances the changed-word route of W349 without introducing a class or degree split.
The unrestricted tame correction from W349 is refined to a prime-to-two correction: every
finite tame-inertia image has odd order, so its correcting exponent may be chosen with trivial
maximal pro-`2` component.  This keeps both the pro-`2` core presentation and the mod-two
Stokes trace unchanged.

The second general ingredient is a target-dependent finite resolver.  Density of the ordinary
integers in `Zhat` supplies, for every finite group `Q`, one integer resolver which computes
every profinite power on every element of `Q`; the same construction resolves `Ztwo` powers.
Taking the product with the multiplicative group of `ZMod 2` records parity at the same time,
so resolution and the endpoint condition use one matched family rather than unrelated choices.

Finally, the normalized even-`M` source is obtained from compact `M` by two substitutions which
fix `tau`.  An arbitrary substitution acts linearly on the total mod-two exponent vector, while
fixing `tau` leaves the tame row's trace unchanged.  Therefore the compact endpoint transports
to every normalized head-handle source and survives the prime-to-two correction.

The headline theorem `resolvesAt_and_endpoint_headHandlePairPrime` gives, for every finite
target and every rank and handle count, a resolved two-relator family satisfying
`IsStokesEndpoint`.  The same corrected word also has honest tame specialization and complete
`FlexibleCoreLeavesRN`.  The remaining campaign seam is analytic: exact lifting, Hessian/
Stokes duality, scalar evaluation, and determinant supply for this uniform changed word.

All public theorem pins in this wave use exactly `propext`, `Classical.choice`, and
`Quot.sound`.

# W354: the pure head-handle pair source has a uniform Stokes radical

W354 closes the second-order audit of the pure head-handle pair exchange with a negative,
rank-uniform result.  Suppose the original `sigma` acts trivially on a nonzero finite
coefficient module.  In the ramified pair normal form, put a nonzero value in the free slot
that is represented simultaneously by `x₂` and the selected handle coordinate.  After the pair
exchange, every compact core factor has zero primal offset.  The only nonzero primal handle
coordinate is paired with the original dual `sigma` coordinate, which every ramified normal
dual cocycle forces to zero.

The full traced pairing therefore vanishes against every dual cocycle.  The tame relator
vanishes because both head offsets are zero; the wild relator vanishes by a recursive
primal-pure evaluation theorem and the explicit handle formula.  The special primal cocycle is
not a coboundary, since its `x₂` coordinate is nonzero while wild letters act trivially.
`StokesDuality.pairing_vanish_left` then gives a contradiction.

This is not a class-seven or finite-row computation.  The theorem holds for every `alpha`,
every handle rank, and every selected handle.  It invalidates the pure pair exchange as the
general source in the sigma-trivial ramified branch.  The next general construction must retain
a second-order partner for the displaced `x₂` coordinate, most likely through a mixed shear or
triangular source rather than a literal exchange of both pairs.

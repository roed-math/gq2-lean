# W117: exact unramified procyclic-M Hessian

The h=0 unramified procyclic-M Hessian is now evaluated directly in the kappa-zero central
extension.

For general `pp`, the exact quadratic value is

`q c0 + polar q c0 c1 + dat.m ((s ^ E omega2)^pp) c0`.

The final summand is the linear quadratic refinement that the previously known bilinear pairing
could not detect.  It is retained explicitly rather than inferred away.

For `pp = 0`, the head power is one and equivariance gives `dat.m 1 c0 = 0`.  The formula then
becomes exactly `plusFormD q q (c0,c1)`, which is the √10 phase target.  A graph-QZero wrapper
connects this calculation to the scalar word-phase seam with the honest resolver and scalar
cohomology premises.

All three public theorems compile with exactly `propext`, `Classical.choice`, and `Quot.sound`.
The `pp = 1` case deliberately retains the factor-set charge.

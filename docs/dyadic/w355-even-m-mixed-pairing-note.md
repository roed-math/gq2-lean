# W355 — the general mixed source repairs the pair radical

W354 proved that the literal head-handle pair exchange cannot satisfy Stokes duality whenever
the original `sigma` action is trivial: the displaced `x₂` coordinate pairs to zero against
every dual cocycle.  This wave replaces that failed source uniformly in the handle count.

`EvenMHeadHandleMixedNielsen` composes the pair exchange with one finite Nielsen shear.  On the
backward substitution the promoted handle becomes `sigma * x₀`; the other relevant letters
retain the pair-exchange images.  The construction is finite, invertible, and independent of
the ramification class.

`EvenMHeadHandleMixedPairing` evaluates the complete two-relator source on the coordinate that
generated the W354 radical.  The tame contribution is zero, while the general compact
ramified Hessian formula reduces the wild contribution to the single handle-plane term
`lam v`.  Thus the repaired source supplies exactly the missing dual partner.

All public declarations use only `propext`, `Classical.choice`, and `Quot.sound`.  This is not
yet the full Stokes theorem for the mixed source: the next step is to compute its complete
normal pairing matrix and prove separation.  It does, however, settle the first necessary
test for any general replacement and rules out a return to class-by-class sources.

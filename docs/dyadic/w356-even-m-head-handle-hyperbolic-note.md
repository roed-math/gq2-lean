# W356 — the promoted handle is uniformly hyperbolic

W355 showed how a mixed Nielsen shear restores a partner for the displaced `V` coordinate.
The general source must restore both directions of the promoted handle simultaneously.  W356
does so by shearing the promoted compact `U` letter by compact `sigma` before applying the pair
exchange.  Backward substitution sends it to `sigma * U`.

`EvenMHeadHandleHyperbolicPairing` proves both exact two-relator identities:

* primal promoted `V` against dual promoted `U` is `lam v`;
* primal promoted `U` against dual promoted `V` is `lam v`.

In each calculation the non-handle factors are one-sided pure, so their central charge is zero.
The selected handle commutator is the sole surviving term.  The proof is uniform in `alpha`,
the handle count, the selected handle, the tame exponent, and both exponent resolvers.  It uses
only triviality of the original `sigma` and wild actions; no ramification-class or `tau` input
appears.

All public declarations pin to `propext`, `Classical.choice`, and `Quot.sound`.  The remaining
analytic step is to combine this hyperbolic plane with the unchanged compact core and the other
handle planes into the complete normal pairing and separation theorem.

# W358 — full Nielsen transport removes the new Hessian seam

W356–W357 changed only the compact branch word and then analyzed the resulting first- and
second-order rows.  There is a stronger general construction: apply the same finite Nielsen
transformation to both relators.  Stokes duality is invariant under such a change of free
generators, so no new sigma-offset Hessian formula is needed.

`EvenMHeadHandleHyperbolicStokes` proves the two resolved inverse identities for the composed
pair-exchange/right-shear transformation at arbitrary integer exponent resolvers.  It defines
`headHandleHyperbolicFullFamily` by substituting the inverse Nielsen map into the complete
compact-M relator family, and proves
`stokesDuality_headHandleHyperbolicFullFamily_iff`:

* the transformed family at the original marking is Stokes-dual exactly when
* the compact-M family is Stokes-dual at the induced substituted marking.

This statement is uniform in `alpha`, `q`, the handle count, the selected handle, the finite
coefficient module, and both resolvers.  It does not split by ramification class.  All public
declarations pin to `propext`, `Classical.choice`, and `Quot.sound`.

The next step is integration rather than a new analytic calculation: instantiate the right
side with the landed compact-M Stokes theorems, then transport the resulting full relator
family through the flexible presentation/certificate APIs.  The branch-word-only source from
W356 remains useful for its explicit rows, but it is no longer the shortest route to general
Stokes duality.

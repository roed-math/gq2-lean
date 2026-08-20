# W342: transport the analytic core before installing a boundary

W341 proves that changing only the tame/pro-2 boundary at the standard compact-M or Mpc word
cannot alter the distinguished-pivot invariant.  W342 supplies the general API needed to test
whether changing the presentation word/source group and the boundary together fares better.

`SourceAnalyticCoreRN.transportGamma` now transports the entire boundary-independent corrected
core across an arbitrary continuous source-group equivalence.  It carries finite generation,
corrected exact lifting, Stokes duality, and the scalar/Hilbert counts, while deliberately
leaving the boundary and affine determinant unspecified.  The construction is the general
boundary-free part of `SourceDataRN.transport` and has no even-M or class parameter.

`FlexibleModelSourceRN.ofTransportedAnalyticBoundary` installs a new boundary on that
transported core and returns the presentation-independent model consumed by corrected general
assembly.  Both declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

The remaining even-M question is consequently precise and uniform: whether such a transported
model can survive after its boundary is pulled back along the source equivalence.  W342 makes
that comparison formalizable; it does not assert that a rewritten presentation evades W341.
If pullback preserves the obstruction, the selector must change the actual candidate group or
branch rather than merely choose another word for an equivalent source.

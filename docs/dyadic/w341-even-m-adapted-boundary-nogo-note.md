# W341: adapted even-M boundaries preserve the pivot obstruction

W340 separated the corrected source into a boundary-independent analytic core and a movable
tame/pro-2 boundary.  W341 proves that this flexibility does not remove the outstanding even-M
placement issue.

`EvenMAdaptedBoundaryNoGo` gives the uniform reason.  Every surjective tame coordinate on the
same `GammaR` whose kernel is pro-2 has exactly the canonical wild kernel.  Every corrected
pro-2 coordinate has the canonical maximal pro-2 kernel.  The quotient construction therefore
puts any adapted boundary in the canonical boundary's orbit, up to automorphisms of `Tq`, the
pro-2 core, and `Ztwo`.  The last automorphism is multiplication by a 2-adic unit, so it cannot
change unitness or the exact valuation of any marking row.

The two field-facing consequences are:

* `mCompact_mobileBoundary_forces_cPivot`: an adapted compact-M boundary still forces the
  distinguished `C` row to be a unit;
* `mpc_mobileBoundary_forces_cPivot`: an adapted arbitrary-display, arbitrary-handle Mpc
  boundary still forces the distinguished `C` row to have exact level `r`.

Both theorems require only the honest pro-2 tame-kernel condition and one oriented M-core/field
equivalence.  Their axiom sets are exactly `propext`, `Classical.choice`, and `Quot.sound`.

This closes the mobile-boundary route negatively in complete generality.  It also supersedes
the idea that another determinant, Hessian, or nilpotency-class calculation could repair the
remaining fields.  Those analytic pieces are already uniform.  The live even-M task is now a
selector/presentation-normal-form correction: fields whose intrinsic marking lacks the
canonical `C` placement must be assigned a genuinely different candidate presentation or
branch, not the same presentation with a different boundary map.

The other general campaign front remains the odd-L arithmetic packet: the absolute residue
Frobenius/exact-sequence comparison and the anchored relative norm-value statement.  That work
is likewise field-theoretic rather than class-by-class.

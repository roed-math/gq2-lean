# W309: the general M mobile pivot is canonical or handle-supported

W309 identifies the placement defect without splitting by nilpotency class.  For every
`alpha >= 2`, every handle count, and every continuous `Ztwo` marking on `DM alpha h`, a unit
value somewhere on `ker chiM` forces one of exactly two outcomes:

1. the distinguished `C` row is a unit; or
2. a standard handle `U_j` or `V_j` row is a unit.

The proof is the full general-h abelian calculation.  A chi-trivial word has even `B`
coefficient and zero `D` coefficient.  The relator makes the `A` contribution even.  Hence a
unit value cannot be assembled unless the `C` contribution or a handle contribution is odd.

The field-side predicate `MFieldHandlePivotAtLevel` records the second outcome.  At level zero,
`mFieldCPivot_or_handlePivotAtLevel_zero` turns the intrinsic kernel unit into the exact
canonical-or-handle dichotomy.  The selected theorem
`m0_cPivot_or_handlePivot_of_familySelection` applies it uniformly to every M0 row selected
from the actual cyclotomic range.

This sharpens the general campaign boundary.  When the current canonical M normal form fails,
the missing pivot is not arbitrary: it is supported on a hyperbolic handle.  The next general
task is therefore a handle-pivot M normal form (and its positive-level divided analogue), not
another class-specific pivot calculation.

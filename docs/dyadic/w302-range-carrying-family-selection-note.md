# W302: range-carrying family selection

W301 constructed the corrected family witness from the actual cyclotomic range.  W302 carries
that identity through selection and removes the duplicated range premises from downstream
consumers.

`FamilyFieldBranchWitness.MatchesCyclotomicRange` records the actual `imChiM alpha` or
`imChiN alpha` identity on an even witness.  The canonical W301 witness satisfies it by
construction.  For any range-matching selection, the selected M and N orientations now follow
directly from the range identity and degree equation.

The canonical all-degree selection consequently has corrected RN residuals on the following
branches from the branch equality alone:

* N0: `n0RowResidualRN_of_fieldSelectionFromRange`;
* Npc: `npcRowResidualRN_of_fieldSelectionFromRange`;
* epsilon-true Mpc: `mpcRowResidualRN_of_fieldSelectionFromRange_true`.

There is no repeated `-1` exclusion, adjacent-depth sharpness test, oriented-equivalence, pivot,
or determinant premise in these three endpoints.  The argument remains uniform in degree,
level, and handle count.  M0 orientation is automatic as well, but its intrinsic field pivot is
still a genuine arithmetic input.  The other even residue is the epsilon-false positive-level
Mpc divided-C digit.  These are now downstream branch boundaries rather than gaps in family
classification or range transport.

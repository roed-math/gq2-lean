# W303: the all-degree corrected family boundary

W303 replaces the branch-by-branch status surface with one all-degree corrected-family
dispatcher.  It starts from W301/W302's canonical selection built from the field's actual
cyclotomic range and returns a displayed `GenAsmBranch` together with its corrected
`GenAsmRowResidualRN`.

The odd L row is now included in this record-level statement without a reciprocity-law premise:
the uniform graded construction supplies its marked pro-2 realization, and the odd-residue
word certificate supplies the corrected candidate record.  The local-reciprocity laws remain
necessary only for the later direct identification of the full `GammaR` with `G_K`, not for the
selected corrected row itself.

On the even side, N0 and Npc close from the carried N range.  Epsilon-true Mpc closes from the
uniform all-degree, all-handle pivot tower.  The two remaining canonical M normal forms are
therefore expressed by a single predicate:

`MFieldCPivotAtLevel B alpha r h`

It says that some oriented M presentation places an exact `unit * 2^r` value on the
distinguished `C` coordinate.  At `r = 0` this is exactly `M0FieldPivotUnit`; at positive
epsilon-false level it is the divided-C placement problem.  `EvenCanonicalMarkingBoundary` is
this predicate on precisely those two constructors and is `True` on every other family row.

The headline
`hasSelectedRowResidualRN_of_fieldSelectionFromRange_of_boundary` consequently covers every
degree, level, unit, and handle count.  This is not a class-seven reduction.  It gives a single
interface for the remaining general normalization problem: either prove a mobile-pivot
normalization, or introduce the alternate M normal form needed when the minimal unramified
value lies in a handle direction rather than on `C`.

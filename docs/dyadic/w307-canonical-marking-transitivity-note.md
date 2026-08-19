# W307: transitivity is sufficient, but oriented transitivity is false

W307 packages W306's full marking-orbit boundary as one uniform sufficient condition.
`MZtwoMarkingTransitivity alpha h` says that every two surjective continuous `Ztwo` markings
on `DM alpha h` differ by a topological automorphism.  The arithmetic marking pulled back
through any core equivalence is surjective, so this condition constructs both the compact-M
and procyclic-M canonical marked-core realizations.  The resulting theorem
`hasSelectedRowResidualRN_of_fieldSelectionFromRange_of_markingTransitivity` feeds the
all-degree dispatcher and covers the two remaining even rows together.

The natural stronger guess is not available.  `not_mOrientedZtwoMarkingTransitivity` proves
that orientation-preserving transitivity is false whenever a handle exists.  A handle
coordinate is a surjective marking that vanishes on the distinguished `C` generator, while
the compact-M canonical marking is a unit at `C`; the oriented pivot obstruction prevents an
orientation-preserving automorphism from joining those markings.

Thus the next general problem is not another nilpotency class and not unrestricted oriented
transitivity.  It is to characterize the invariant strata of the full automorphism action on
surjective `Ztwo` markings, uniformly in `alpha` and `h`, and to place the transported
arithmetic marking in the canonical stratum required by the two M families.

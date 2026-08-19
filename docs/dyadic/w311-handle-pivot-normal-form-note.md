# W311: the general M handle pivot has one normal form

W309 and W310 showed uniformly that the two unresolved M selector families have either the
canonical distinguished C pivot or an exact pivot on a standard hyperbolic handle.  W311 puts
the handle alternative into one normal form, for every alpha, level, and handle count.

If the exact pivot is on a handle U row, lifted `theta` and `tauV` moves scale it to exactly
`2^r` and kill the paired V row.  If the pivot starts on V, a lifted handle swap first moves it
to U and the same correction applies.  These automorphisms preserve `chiM` and fix the C row.

The field theorem `mFieldNormalizedHandlePivotAtLevel_of_handlePivot` transports the correction
through any oriented field realization.  Consequently the remaining M work is no longer pivot
existence or a collection of degree classes: it is one uniform alternate certificate problem
for a marking with a chosen handle U row equal to `2^r` and its paired V row equal to zero.

# W310: the positive-level M pivot is canonical or handle-supported

W310 extends W309 to exact positive levels.  Suppose an M marking has level at most `r` on
`ker chiM`, attains the value `2^r` there, and its B row is itself divisible by `2^r`.  Then the
divided unit at level `r` occurs either on the distinguished C row or on a standard handle row.

The proof is again uniform in alpha, r, and the handle count.  Write the exact kernel element
in the full M abelian frame and divide every contribution by `2^r`.  The A quotient is even by
the relator, the B quotient is killed by the even B coefficient forced by chi-triviality, and
the D coefficient is zero.  If every C and handle quotient were nonunits, the total divided
value could not be one.

For a family-selected epsilon-false Mpc row, the selector's lambda(-1) equation says exactly
that the B row is divisible by `2^r`.  Thus
`mpcFalse_cPivot_or_handlePivot_of_familySelection` gives the same canonical-or-handle
dichotomy already obtained for M0 in W309.

The two remaining M selector branches are therefore no longer separate arithmetic mysteries.
Both reduce uniformly to one alternate-normal-form problem: consume an exact pivot supported
on a hyperbolic handle when the distinguished C pivot is absent.

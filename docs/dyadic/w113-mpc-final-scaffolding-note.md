# W113: determinant-only procyclic-M final endpoints

The corrected procyclic-M record now feeds the general assembly and the two canonical quadratic
field branches with determinant data as its only analytic input.

`mpc_candidate_equiv_galKRN_of_tied_determinant` is the generic field-facing wrapper.  For
`sqrt(10)`, the unconditional canonical selector supplies the tied branch, so both the corrected
row residual and the candidate/Galois equivalence require only an
`AffineDeterminantCertificate`.

For `sqrt(-10)`, the same determinant-only analytic route is available after
`MpcPivShift 2`.  This shift is exactly the additional selector premise needed to identify the
chosen marking with the canonical `mpcNu` marking.  The older unconditional selector lands on
the transported `mpcPiv_nuZtwo` marking and cannot honestly feed the corrected canonical
residual.

All five declarations are axiom-pinned to their established field-selection and general
assembly sets, with no `sorryAx`.

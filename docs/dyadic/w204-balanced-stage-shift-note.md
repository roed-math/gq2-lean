# W204: the balanced finite-quotient stage shift

W203 isolates the honest five-variable correction boundary, but its `nextDefect` field is
nonlinear. W204 rewrites that field as the exact finite-quotient equation consumed by the
generic even-stage machinery.

For raw balanced factors `(e_a,e_b,e_c,e_d,e_z)`, the correction of the corrected marking
has core rows

`(e_a, e_b, e_c, d^-1 * e_z * d * e_d)`

and trivial handle rows. The theorem `balancedCorrectedMark_modify_eq_mul` proves this
identity before passing to a quotient. `correctionMark_mem_twoCentralSeries` and
`correctionMark_mem_lambdaImage` then verify that every induced row has the corrected W203
depth `lambda_(k-1)`.

`oneHandleBalancedRelatorShift_eq` identifies the generic stage shift with the old relator
inverse times the modified relator. The two constructors between
`OneHandleBalancedShiftCorrection` and `OneHandleBalancedCorrection` prove the exact
equivalence `nonempty_shiftCorrection_iff_correction`: killing the old relator in
`DM 2 1 / lambda_(k+1)` is equivalent to pushing the conjugate balanced defect into
`lambda_(k+1)`.

Finally, `oneHandleBalancedRelatorShift_eq_evenRawDbarWord` identifies this shift with the
existing `evenRawDbarWord`. Thus the remaining all-rung boundary is no longer an opaque
nonlinear condition: `OneHandleBalancedShiftSupply` asks whether the five constrained rows
reach the inverse current relator through the established even crossed-derivation word.
`balancedShiftSupply_iff_climbSupply` proves that this reformulation loses no information,
and `mpcPivShiftH_two_one_of_balancedShift` remains the final conditional consumer.

Every declaration has exactly the standard axiom set `propext`, `Classical.choice`, and
`Quot.sound`. No reachability or span assertion is assumed.

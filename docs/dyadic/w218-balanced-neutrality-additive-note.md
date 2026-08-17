# W218: the additive CABD defect row

W218 packages W217's literal multiplicative equation as one finite homomorphism.  On four
ordinary relative rows, ordered `C,A,B,D`, the defect is

`C(y) * (A(a) * B(b) * D(d))⁻¹`.

The theorem `balancedCABD_eq_iff_defect_eq_one` identifies its kernel with the literal CABD
equation.  Applying the multiplicative-to-additive type tag gives
`oneHandleBalancedCABDAddRow`; `balancedCABD_eq_iff_addRow_eq_zero` identifies its zero
fiber, and `oneHandleBalancedCABDAddKernel` records the exact additive solution subgroup.

This is the finite additive row intended for the next restricted-Lie calculation.  It does
not assert that the row has a prescribed rank or that the remaining neutrality obstruction
vanishes.  Every public declaration has exactly the standard axiom set `propext`,
`Classical.choice`, and `Quot.sound`.

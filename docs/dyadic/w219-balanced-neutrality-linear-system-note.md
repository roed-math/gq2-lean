# W219: the finite CABD system

W219 adds the inhomogeneous class condition to W218's homogeneous defect row.  The combined
homomorphism records:

- the CABD defect in the relative central layer; and
- the `C` coordinate modulo genuinely character-neutral corrections.

`mem_oneHandleBalancedCABDSystem_range_iff` identifies membership of the target
`(1, [x])` with the existence of four ordinary relative corrections satisfying both the
prescribed-class condition and the literal CABD equation.  Its additive tag is
`oneHandleBalancedCABDAddSystem`.

The target-specific theorem
`neutralityObstruction_eq_one_iff_mem_CABDAddSystem_range` says that the remaining
neutrality obstruction vanishes exactly when the corresponding explicit additive target is
in this finite system's range.  This is now a genuine finite image/rank problem; no range or
rank result is asserted here.  Every public declaration has exactly the standard axiom set
`propext`, `Classical.choice`, and `Quot.sound`.

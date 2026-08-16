# Wave 105: exact marked-successor reduction

Wave 105 isolates the one-order-higher input needed to propagate the full-marked M6 ladder.
It does not assert a false generic surjectivity theorem.

`mpcMkAdvance` applies a four-slot cost-domain witness to a word-set point.
`mpcMk_advance_mem` proves that an exact cost/defect equality makes this explicit point solve
the next quotient problem.

At the following layer, `mpcMk_cost_succ_base_indep` proves that the cost map is unchanged by
the visible base shifts introduced in the preceding move.  The proof uses graded vanishing of
commutators between the successor correction layer and the depth-j shift; it removes moving
base points from the propagation problem.

`mpcMk_good_succ_of_advance_range` then reduces the successor to one honest statement: the
secondary defect of the advanced point belongs to the fixed next cost range based at the old
point.  The missing mathematics is a one-order-higher collection formula modulo the next
filtration level and a deeper marked correction for that secondary term.

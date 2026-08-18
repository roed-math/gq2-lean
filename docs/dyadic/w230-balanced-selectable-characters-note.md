# W230: one good point per rung is exactly enough

Earlier one-handle supplies asked every balanced point at a rung to cover the constrained
coordinate target. W230 removes that excess uniformity. For each `k ≥ 3`, stage `k + 1` is
nonempty exactly when some point at stage `k` has its relative target in the constrained
coordinate span. The reverse implication is especially sharp: a point already at stage
`k + 1` has stage-`k` target equal to one.

At a selected point, ordinary-relative coverage and the three parity-character rows from W229
imply full coordinate coverage. Selecting such a point at every nonempty stage therefore
constructs all finite stages and feeds the existing compactness theorem to obtain
`MpcPivShiftH 2 1`.

This wave does not assert that a suitable point exists. It identifies the exact quantifier and
removes the stronger uniform requirement. The remaining one-handle front is now: at each
nonempty rung, select one balanced point whose relative target is covered and whose first,
second, and diagonal scalar characters are all nontrivial.

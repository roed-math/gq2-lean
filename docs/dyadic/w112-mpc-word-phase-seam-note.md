# W112: procyclic-M word-phase seam

The scalar word-trace and graph-Hessian seam is now complete for every displayed procyclic-M
word.  The module supplies the resolved scalar row, the one-dimensional `WordH2` trace, the
flexible resolver system, and the comparison between `QZero` and the tame-plus-wild Hessian
trace.

The flexible orientation is proved from the existing scalar `H2` cardinality and does not
freeze a choice of quotient action.  `wPmpc_QZero_eq_graphHessianTrace` then identifies the
cohomological scalar obstruction with the two word Hessians through an explicit graph resolver.

All ten exported declarations compile with exactly `propext`, `Classical.choice`, and
`Quot.sound`.

This removes the word-trace plumbing from the determinant frontier.  The remaining analytic
calculation is specifically the unramified Mpc quadratic diagonal.  Existing unramified
pairing results determine its bilinear Gram form, but do not rule out a linear quadratic
refinement.  The branch selector is not involved in this gap.

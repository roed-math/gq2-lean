# W206: exact relative lifts in the two-central tower

W205 leaves four correction rows in `lambda_(k-1)`, each required to vanish exactly under
the one-handle forgetting map. W206 proves that these two group-level conditions are exactly
one finite-level subgroup condition.

For a continuous epimorphism `f : P -> Q` and `j <= n`,
`exactRelativeImage_eq_inf_ker` identifies the image of

`lambda_j(P) intersect ker(f)`

inside `P / lambda_n(P)` with the intersection of `lambdaImage P j n` and the kernel of the
induced level map. The reverse inclusion is exact: an error in `lambda_n(Q)` is lifted through
`lambda_n(P)` and removed without changing the level-`n` class.

The specialization `oneHandleRelativeLambdaImage` uses `dmForgetHandles 2 1`.
`mem_oneHandleRelativeLambdaImage_iff_exists_exact` therefore supplies representatives that
simultaneously have the required depth, vanish under handle-forgetting in the original group,
and realize the prescribed finite class.

The `C`-row condition involving every continuous `Z_2`-valued character is intentionally not
declared quotient-determined. It remains an extra representative constraint for the next
finite four-row packaging step.

Every declaration has exactly the standard axiom set `propext`, `Classical.choice`, and
`Quot.sound`.

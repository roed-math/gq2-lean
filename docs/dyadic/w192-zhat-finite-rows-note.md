# W192: exact finite rows for the missing Frobenius normalization

W191 exhibits two distinct lifts of AX4's known geometric pro-`2` value. W192 identifies the
complete additional datum needed to distinguish such lifts.

`ZhatNonProTwoRows gamma delta` says that `gamma` and `delta` agree in every finite quotient of
`Zhat` which is not a `2`-group. The theorem
`zhat_eq_iff_maxProTwo_and_nonProTwoRows` proves that equality in `Zhat` is equivalent to:

- equality in the maximal pro-`2` quotient; and
- these non-pro-`2` finite rows.

The proof is intrinsic: the pro-`2` kernel lies in every open normal subgroup with a finite
`2`-group quotient, the row hypothesis handles every other open normal subgroup, and their total
intersection is trivial.

AX4 already supplies the first condition for the abstract geometric uniformizer coordinate.
Therefore `abstractTameUniformizerNormalization_iff_nonProTwoRows` reduces the full
`Zhat.ofInt (-1)` normalization exactly to `AbstractTameUniformizerNonProTwoRows`. W191's two
explicit lifts provably fail one of these remaining finite rows.

All six public declarations in `RamifiedCertificateZhatFiniteRows.lean` depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

Verification passes the 4,539-job build, fresh 1,127-module scoreboard, and full ledger gate over
45,226 tracked declarations, with zero `sorryAx` dependencies, zero unknown non-standard axiom
uses, and zero terminal violations.

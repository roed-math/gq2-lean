# W216: the literal C-versus-ABD equation

W216 expands W215's interaction-source membership into one explicit finite row equation. An
ordinary relative class `y` belongs to the source precisely when there are ordinary relative
classes `a`, `b`, and `d` such that

`C_relaxed(y) = A(a) * B(b) * D(d)`.

For any chosen relaxed-`C` representative `x` of the target neutrality class,
`neutralityObstruction_eq_one_iff_CABD` says that the obstruction vanishes exactly when the
class of `x` modulo genuinely character-neutral representatives has a representative `y`
satisfying this equation.

This is the current exact finite boundary. It separates the two required calculations:
changing `x` by a neutral class, and solving the resulting three-row `ABD` relation. The
module does not assert a solution.

Both public theorems have exactly the standard axiom set `propext`, `Classical.choice`, and
`Quot.sound`.

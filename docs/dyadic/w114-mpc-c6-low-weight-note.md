# W114: eliminate the low-weight M6 trace factors

The checked class-six trace now continues from the 51-factor prefix to a 47-factor endpoint in
which every factor has depth exactly five.

The new module uses only the existing trusted checker rules.  It kills the restricted-square
triple `[D,B]^2 * [[D,B],B] * [B^2,D]`, removes `[B,B^4]`, and combines the remaining
`[C,B^2]` power pair.  No new collection identity was added to the checker.

The replay is stored as 25 checked chunks over 246 shared word nodes, totaling 1,108 derivation
nodes.  The chunk check, endpoint length, and depth audit are axiom-free.  The evaluation
theorems use exactly `propext`, `Classical.choice`, and `Quot.sound`.

This exhausts the inverse/orientation and low-weight Hall-Petrescu cleanup.  The remaining
47-factor equality is a pure class-five restricted-Lie/Jacobi normalization problem, and the
defining one-relator class is genuinely required.

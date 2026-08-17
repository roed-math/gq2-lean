# W202: the unconditional cup-adapted seed

W201 reduced balanced depth three to the finite condition `OneHandleCupAdaptedSeed`.  W202
constructs that seed from every compact M6 row satisfying the universal `C + 2B` equation.

`MpcCupAdaptedSeed.exists_oneHandleCupAdaptedSeed` lifts the four compact letters to the
one-handle group and clears the two handle coordinates modulo two.  The universal row equation
makes the remaining `C`-handle coordinates even.  The resulting rank-six marking therefore
pulls each mod-two character back through the compact automorphism.  Invariance of the compact
even cup form then proves that this marking is cup-adapted.

Consequently `MpcCupAdaptedSeed.oneHandleBalancedSet_three_nonempty` unconditionally inhabits
`oneHandleBalancedSet Psi0 3`.  Both public declarations use exactly `propext`,
`Classical.choice`, and `Quot.sound`.

This closes the finite W201 boundary.  It does not assume either disproved fixed-`C`
surjectivity statement.  The next honest problem is propagation from depth three to higher
rungs, where residual-specific graded reachability—not full relative-kernel surjectivity—is
required.

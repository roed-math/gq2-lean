# W306: canonical M realization is a full marking orbit

W306 identifies W305's field-facing boundary with one general automorphism problem.  For any
presented pro-2 core `P`, any base equivalence `e : P ≃ G_K(2)`, and any target marking `nuP`,

`Nonempty (MarkedCoreRealization P nuP)`

is equivalent to the existence of a core automorphism `Psi` such that, at every `x`,

`ztwoIota (nuP x) = nuUrKTwo B (e (Psi x))`.

The theorem is `markedCoreRealization_iff_markingOrbitAt`; both directions are formal.  A
realization differs from the chosen base equivalence by a core automorphism, and an orbit
witness composes with the base equivalence to form the realization.

Specializing gives exact orbit characterizations of both
`M0CanonicalMarkedCoreRealization` and `MpcCanonicalMarkedCoreRealization`.  These are full
marking equalities, not distinguished-coordinate conditions.  Therefore the remaining general
M-family theorem is now unambiguous: establish automorphism transitivity on the relevant
surjective `Ztwo` markings of `DM alpha h`, uniformly in `alpha` and `h`.  Such a theorem closes
M0 and epsilon-false Mpc together; no nilpotency-class split is involved.

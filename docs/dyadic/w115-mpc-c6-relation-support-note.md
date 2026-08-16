# W115: checked degree-five Mpc relator support

The class-six checker now verifies the six degree-five consequences of the defining Mpc
relator that are needed by the sparse certificate.

Four exact unit cleanup rules were added: `[1,x] = 1`, `[x,1] = 1`, `1^2 = 1`, and
`1^-1 = 1`.  Each is proved directly from group laws.

`MpcC6WeightedRelationSupport.lean` constructs and checks the six named relator consequences,
then expands them to 18 depth-five factors.  Combining those factors with the 47-factor low
endpoint yields an explicit 65-factor endpoint.  The module proves that the original
certificate word and this endpoint have the same evaluation.

All Boolean and depth audits are axiom-free, while the semantic evaluation theorems use exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The remaining theorem is stated but not assumed: the 65-factor endpoint must be killed by
universal class-five Hall-Witt/Jacobi and restricted-square identities.  The conditional helper
`certificateKill_of_jacobiEndpoint` keeps that final input visible.

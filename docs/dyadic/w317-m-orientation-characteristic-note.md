# W317: characteristic orientation of the general M core

W317 proves the general theorem
`MOrientationCharacteristic.mCoreOrientationCharacteristic_all`:
for every `1 ≤ alpha` and every handle count `h`, every continuous automorphism of
`DM alpha h` preserves the canonical character `chiM alpha h`.

The proof is uniform in `alpha` and `h`.  It evaluates the arbitrary-rank master
crossed derivations on an automorphic generating tuple, proves the resulting matrix
invertible modulo two, and contracts its inverse to obtain every Fox row.  The four
core rows give the Labute descent datum; singleton handle rows force both characters
in each handle pair to equal one.  The existing uniqueness theorem then identifies
the pulled-back character with `chiM`.

This closes the orientation-naturality boundary isolated in W316.  In particular,
there is no class-seven or rank-by-rank orientation premise left in the M/Mpc lane.
The theorem and its supporting public declarations use exactly the standard axiom
set `[propext, Classical.choice, Quot.sound]`.

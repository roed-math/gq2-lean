# W110: full procyclic-M Stokes certificate

The full four-clause `StokesDualityCertificate` is now available for every honest
procyclic-M display.  The proof reuses the uniform Heisenberg resolver and the existing generic
counting theorems; it introduces no new analytic premise.

The clauses are supplied by `tcocycle_cardN`, `hsep_field_goal_marking`, the right-separation
and partial-count route through uniform self-duality, and `hZcardN`.  The assembled theorem
needs only a display package, `2 ≤ alpha`, `1 ≤ r`, and `Even q`.  In particular, it does not
need `q ≠ 0`.

`mpcCand_stokes_one` matches the degree-two carrier used by the corrected procyclic-M record.
Consequently `mpcWordCertificateRN_of_determinant` and
`mpcRowResidualRN_of_tied_determinant` now discharge exact lifting, scalar, and Stokes data
internally.  The affine determinant is the only remaining analytic input to the corrected
record and tied row residual.

Every new Stokes and integration declaration compiles with exactly `propext`,
`Classical.choice`, and `Quot.sound`.

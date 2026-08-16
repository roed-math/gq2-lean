# W108: procyclic-M scalar certificate

The corrected procyclic-M record now has an unconditional scalar certificate for every valid
display package.  The construction combines the uniform pushed Heisenberg count with the
existing field-cardinality theorem, then packages both scalar clauses as a
`ScalarHilbertCertificate`.

The three new public declarations are:

- `mpcCandidate_homCard_of_uniformPushed`, the scalar-character count;
- `mpcCandidate_scalar_of_uniformPushed`, the generic pushed scalar certificate;
- `mpcCandidate_scalar`, the display-level certificate with standard numerics.

All three compile using exactly `propext`, `Classical.choice`, and `Quot.sound`.

This closes the scalar field of `WordCertificateRN`.  Corrected exact lifting was already
available as `recBl_mpc_exactLiftingRN`, so the remaining record inputs are the full four-clause
Stokes certificate and the affine determinant certificate.  The M6 selector is not an input to
the word certificate itself; it is needed later for the canonical `sqrt(-10)` branch marking.

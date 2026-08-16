# W109: tied selectors and procyclic-M corrected-record scaffolding

Two reusable interfaces now preserve the data needed by the corrected row assembly.

`FieldBranchIdentificationTied.lean` adds field-facing even-N and even-M selectors that retain
the heterogeneous equality between the selected marking and the canonical marking.  The old
selectors remain available for compatibility, but no longer force downstream corrected-record
proofs to reconstruct information that selection had discarded.

`MpcCandidateRN.lean` packages a corrected procyclic-M `WordCertificateRN` once the full Stokes
and affine determinant certificates are supplied.  Its exact-lifting and scalar fields are
discharged by existing theorems.  A tied residual wrapper then transports the certificate to a
field branch whose marking is identified with the canonical Mpc marking.

The four public declarations are:

- `fieldId_genAsmBranch_of_orientedN_tied`;
- `fieldId_genAsmBranch_of_orientedM_tied`;
- `mpcWordCertificateRN_of_stokes_determinant`;
- `mpcRowResidualRN_of_tied`.

The N selector and both corrected-record declarations use exactly the standard three axioms.
The M selector additionally inherits the existing `peripheralCyclotomicAction` premise through
`mMixHypothesis`.

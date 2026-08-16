# Wave 104: general corrected compact-N integration

Wave 104 exposes the already uniform compact-N certificate through a generic tied-branch
interface.  The earlier final module connected it only to the frozen `N0 2 0` row, although
the determinant supply and `WordCertificateRN` were general in both alpha and the handle
count.

`wPcN_rowResidualRN_of_tied` takes any general-assembly branch identified with `N0 alpha h`
and the canonical `nNuZtwo alpha h` marking.  It constructs the corrected row residual from
`wPcNWordCertificateRN` with no additional analytic hypothesis.

`wPcN_candidate_equiv_galKRN_of_tied` feeds that residual directly to corrected general
assembly.  The binder-free `sqrt(-2)` endpoint is the specialization `alpha = 2`, `h = 0`;
the new declarations make the same closed route available to every future tied compact-N
branch.

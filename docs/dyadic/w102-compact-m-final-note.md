# Wave 102: corrected compact-M final endpoints

Wave 102 instantiates the branch-free compact-M supply at the two canonical handle-free M0
rows and feeds them to corrected general assembly.

For `sqrt(5)`, `canRec_branch_sqrtFive` identifies the branch with `M0 2 0` and its canonical
compact-M marking.  `wPcM_rowResidualRN_sqrtFive` combines that identification with
`wPcM_branchFreeSupply` and the supply-parameterized record from wave 99.  The corresponding
`wPcM_candidate_equiv_galKRN_sqrtFive` invokes corrected general assembly directly.

The `sqrt(2)` pair is identical with `M0 3 0` and alpha equal to three.  The canonical `HEq`
marking witnesses pass directly through the generic tied-row wrapper; no dependent transport
or extra analytic premise is required.

All four statements are binder-free with respect to coefficient-stage vanishing.  Together
with the corrected compact-N endpoint, this closes the tied handle-free even rows through the
active `WordCertificateRN` API.

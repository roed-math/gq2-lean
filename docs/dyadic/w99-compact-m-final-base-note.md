# Wave 99: corrected compact-M record base

Wave 99 packages the corrected compact-M record layer independently of the unfinished
boundary comparison.  Its only analytic input is an abstract `wPhBranchFreeSupply`.

`wPcM_affineDeterminantCertificate_of_supply` converts that supply through the compact-M
word-phase determinant theorem and the standard record-block congruence.  The resulting
determinant is combined with the unconditional corrected lifting, Stokes, and scalar leaves
in `wPcMWordCertificateRN_of_supply`.

Two generic tied-branch wrappers expose the integration seam.  Given a branch identified
with `M0 alpha h`, its canonical marking, and the same branch-free supply,
`wPcM_rowResidualRN_of_tied` constructs `GenAsmRowResidualRN`, and
`wPcM_candidate_equiv_galKRN_of_tied` feeds it to corrected general assembly.

The module deliberately does not import a concrete compact-M boundary theorem.  Once the
ramified and unramified comparisons are joined, the final tied rows need only instantiate
the supply argument; no coefficient-stage vanishing hypothesis returns.

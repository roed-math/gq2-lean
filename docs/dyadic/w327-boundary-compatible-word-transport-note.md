# W327: boundary-compatible word transport

W327 closes the analytic transport problem for a new, table-free candidate word.  A
`BoundaryCompatibleWordEquivRN` consists of a continuous equivalence from the new candidate
group to a certified reference candidate together with the two boundary squares that actually
matter: compatibility with the tame quotient and with the presented pro-2 core.

From this packet, `FlexibleCertificateLeavesRN.ofTransport` transports the complete corrected
source record supplied by W326.  Exact lifting (including the corrected `zRN` stage), Stokes
duality, scalar counts, and both determinant branches therefore move together.  W325 then
reassembles the transported leaves into a `WordCertificateRN`, and W324 supplies the direct
general-K consumer.

This is a general presentation result, not another frozen-row argument.  The remaining
mobile-pivot problem has been narrowed to one algebraic construction: produce a tame-compatible
Nielsen equivalence between the adapted word and a certified reference word, and prove its tame
and pro-2 generator identities.  No analytic branch needs to be recomputed.

All five public declarations print only the standard trust base
`[propext, Classical.choice, Quot.sound]`, except the terminal field-equivalence consumer, which
inherits exactly the already-audited general-assembly field axioms.

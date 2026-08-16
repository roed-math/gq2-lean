# W156: general-h compact-N realization at level zero

Level zero now produces the compact-N marked-core realization at every handle count.

An exact ker-chi element need not be primitive in the original sigma/x2 plane when handles are
present.  `marked_matching_certificate_KTwoN_of_level_zero_general` applies the W154
chi-preserving Eichler correction to move a primitive handle coordinate into x2, then invokes the
existing arbitrary-h compact-N marked certificate.

`markedCoreRealizationN_of_level_zero_general` adapts that certificate to
`MarkedCoreRealization (DN alpha h) (nNuZtwo alpha h)`.  Its only field-side input beyond level
zero and `2 <= alpha` is the ordinary oriented equivalence.  No primitive-pair, handle-frame, or
analytic premise remains.

Both declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The immediate follow-on is the family-facing wrapper: combine the selector's N0 branch equality
with this realization and the already-uniform compact-N corrected certificate.

# W326: corrected source transport

The frozen source record already transported across a continuous group equivalence, but the
general-degree campaign uses the corrected `SourceDataRN`.  W326 supplies its missing generic
transport theorem.

`SourceDataRN.transport` precomposes both boundary legs and transports every corrected source
clause: exact lifting (including the `zRN` R-stage), Stokes duality, scalar Hom and H2 counts,
and the ramified and unramified affine determinant formulas.  The proof is completely generic
in the degree, word, source group, core, orientation, and numerics.

`sourceBoundaryMapK_congr_pair` and `affineDeterminantCertificate_congr` isolate the dependent
proof-term issue that occurs when both boundary homomorphisms change.  Equality of the tame and
pro-2 maps is enough; the compatibility witnesses are propositions and introduce no additional
condition.

All three declarations have exactly the standard three axioms.  Together with W325, this means
all five non-routine certificate leaves can be transported at once after constructing a
boundary-compatible equivalence between the adapted candidate word and a certified reference
word.  The remaining substantive work is therefore the tame-compatible Nielsen equivalence,
not a repetition of the analytic branch proofs.

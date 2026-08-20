# W338 — flexible corrected model sources

W337 proves that a tame-compatible presentation change cannot solve the obstructed even-M
family: transporting such a packet back to the standard compact-M or Mpc word gives a
realized canonical word certificate, and characteristic orientation forces the false
distinguished-C pivot.

W338 moves the abstraction boundary to the input actually consumed by corrected
reconstruction.  `FlexibleModelSourceRN` packages:

- an arbitrary corrected `SourceDataRN` over the required pro-2 boundary slot;
- a continuous equivalence from the desired candidate group to the source carrier;
- surjectivity of its tame map; and
- the pro-2 property of its wild kernel.

The source's tame and pro-2 maps need not be the canonical maps derived from `tameOfSpec` and
a fixed `CorePresentation`.  `candidate_equiv_galK_of_modelSourceRN` reconstructs the candidate
against any arithmetic source over the same slot, and
`genAsmFlexible_candidate_equiv_galKRN_compatible_ofModelSource` is the general-K field
consumer.  Ordinary `WordCertificateRN` records embed through
`FlexibleModelSourceRN.ofWordCertificate`, so the new interface preserves every landed row.

This is the honest general mobile-pivot boundary.  What remains is not another nilpotency
class and not another equivalent-word transport: it is one corrected source model whose
boundary maps are adapted to the intrinsic mobile M pivot.  The analytic and reconstruction
clauses remain exactly the existing `SourceDataRN` clauses.

All new structural and generic reconstruction declarations use only the standard axioms
`[propext, Classical.choice, Quot.sound]`.  The field assembler inherits only the already
recorded general arithmetic dependencies.

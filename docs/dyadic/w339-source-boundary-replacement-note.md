# W339 — corrected source boundary replacement

W338 shows that corrected reconstruction consumes a `SourceDataRN` model rather than
intrinsically requiring the canonical tame specialization in `WordCertificateRN`.  W339
separates the boundary-dependent part of that model from its remaining analytic core.

`SourceAnalyticCoreRN` contains the source carrier, finite generation, exact lifting, Stokes,
and scalar clauses over one fixed marked pro-2 slot.  `SourceAnalyticBoundaryRN` adds exactly
the boundary pair, its structural facts, and its affine determinant.  Their `toSource`
constructor is the exact decomposition of `SourceDataRN`.

`BoundaryReplacementRN S` contains exactly:

- an adapted tame map and pro-2 map on `S.Γ`;
- their compatibility and joint surjectivity;
- the maximal-pro-2 kernel identity; and
- the affine determinant for the adapted boundary.

When a source over the same marked slot is already known, `SourceDataRN.replaceBoundary`
reuses its finite generation, exact lifting, Stokes, and scalar clauses.
`FlexibleModelSourceRN.transportedWordSourceRN` first transports those boundary-independent
clauses across an arbitrary candidate-group equivalence.
`FlexibleModelSourceRN.ofWordEquivBoundaryReplacement` then installs the adapted boundary.
Unlike the W334 transport, it assumes no equality between that tame map and the canonical
`tameOfSpec` map.

The end-to-end theorem
`genAsmFlexible_candidate_equiv_galKRN_compatible_ofBoundaryReplacement` therefore states the
replacement route in one signature: over a known analytic core on the mobile marked slot,
construct an abstract candidate-group equivalence, an adapted jointly-surjective boundary,
its pro-2 wild kernel, and its affine determinant.  If no landed source is marking-equivalent
to that slot, the boundary-independent `SourceAnalyticCoreRN` remains an explicit obligation;
W339 does not hide it behind canonical transport.

Every new structural declaration uses only `[propext, Classical.choice, Quot.sound]`; the
field endpoint inherits the existing general arithmetic dependencies and adds none.

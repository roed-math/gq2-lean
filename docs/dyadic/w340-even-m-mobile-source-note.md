# W340 — even-M mobile corrected source cores

W339 separates a corrected source into its analytic core and its tame/pro-2 boundary.  W340
applies that separation to both even-M families at the field's intrinsic mobile marking.

The compact-M and displayed-Mpc exact-lifting, Stokes, scalar, and finite-generation theorems
are already polymorphic in the marked pro-2 slot.  Consequently
`mCompactAnalyticCoreRN` and `mpcAnalyticCoreRN` construct the complete boundary-independent
analytic core directly over `maxProPQuotient 2 (GalK K)` with marking `fieldCoreNuZtwo B`.
No canonical-C placement, marking-compatible core equivalence, or new analytic computation is
required.

`mCompactFieldModelSourceRN` and `mpcFieldModelSourceRN` then show that the exact remaining
input is a `SourceAnalyticBoundaryRN` on that intrinsic field marking, together with the
pro-2 property of the adapted tame kernel.  The resulting field endpoints are
`mCompactField_candidate_equiv_galKRN_of_mobileBoundary` and
`mpcField_candidate_equiv_galKRN_of_mobileBoundary`.

The adapted tame map is deliberately not required to equal the canonical `tameOfSpec` map.
W337 proves that retaining canonical tame compatibility would force the original pivot
placement and therefore cannot repair the odd-residue compact-M case.  W340 leaves only the
honest full-boundary construction: an adapted tame map, compatible pro-2 map, joint
surjectivity, maximal-pro-2 kernel identity, affine determinant, and pro-2 wild kernel.

Every structural declaration in this wave uses only
`[propext, Classical.choice, Quot.sound]`; the two field endpoints inherit the existing
general arithmetic packet and add no campaign axiom.

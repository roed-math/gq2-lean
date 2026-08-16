# W93: corrected compact-N final endpoint

Date: 2026-08-16

## Result

The compact-N route now reaches the active corrected general assembly theorem at
`Q2(sqrt(-2))`.  The final endpoint has no `askCStageVanishing` binders.

Earlier compact-N work closed the determinant phase in both tame-action branches, but its
compatibility endpoint still used the frozen `WordCertificate` surface.  The corrected
`WordCertificateRN` surface makes exact lifting unconditional at this compact row and lets the
branch realization supply the field-side arithmetic source directly.

## Construction

`GQ2/Dyadic/Instances/WordPhaseCompactNFinal.lean` packages the existing leaves:

* corrected exact lifting from `rowCl_nCand_exactLiftingRN`;
* the compact-N Stokes and scalar certificates;
* the branch-free determinant supply from `wPcN_branchFreeSupply`;
* the standard compact-N core relation, pro-2 quotient, marking compatibility, and wild/tame
  structure.

These fields form `wPcNWordCertificateRN`.  The canonical tied sqrt(-2) branch is then
repackaged as `GenAsmRowResidualRN`, and `genAsm_candidate_equiv_galKRN` gives the final
candidate equivalence.

The new declarations are:

* `wPcN_affineDeterminantCertificate`;
* `wPcNWordCertificateRN`;
* `wPcN_rowResidualRN_sqrtNegTwo`;
* `wPcN_candidate_equiv_galKRN_sqrtNegTwo`.

The first two are standard-three.  The residual and final theorem carry exactly the standing
finite-dyadic classification axioms, with the final theorem adding the frozen relative
Stiefel-Whitney input.  There is no new axiom, `sorry`, `native_decide`, or option override.

## Campaign effect

Compact N is now closed on the corrected public route, not merely at the determinant seam.
The remaining record-row obstruction is confined to honest ramified compact M.  The M6
selector remains a separate group-theoretic front.

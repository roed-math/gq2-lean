# W322: the exact general selected-family assembly

W322 moves the W321 placement theorem through a corrected compatibility-aware general
assembly.  For the canonical range selection, and with `GenAsmCompatibleFieldInputs` fixed,
it proves

`HasSelectedAssemblyRN B FF S ↔ ¬ CanonicalPivotPlacementDefectBoundary B S`.

`HasSelectedAssemblyRN` contains the selected `GenAsmBranch`, its corrected RN residual, and
the final candidate/Galois equivalence.  Consequently this is the exact candidate-side
endpoint for every degree and all five families, not another class computation.

The new field packet contains only the tame quotient, degree/modulus parameters, and
`CompatibleRamifiedDataAt` for that quotient.  The corrected assembler
`genAsm_candidate_equiv_galKRN_compatible` therefore removes the legacy universal
quantification over unrelated actions and the unused all-square-roots ramified-i premise.

The remaining compatible ramified packet is an independent field-arithmetic boundary.  The
odd-L work has reduced its production to full unramified reciprocity normalization and relative
norm/unit reciprocity; those laws are not consequences of, and should not be conflated with,
the even-family pivot placement defect.

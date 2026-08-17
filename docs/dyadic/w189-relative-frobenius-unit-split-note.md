# W189: splitting unit inertia from uniformizer normalization

W188 reduced the signed relative Frobenius comparison to its norm-one unit rows and one chosen
uniformizer row. W189 separates the two kinds of arithmetic information.

Assume `TameUnitInertiaRefinement`, the existing statement that the abstract full tame coordinate
kills reciprocity units. Then the abstract side of every unit row is one. The W188 unit rows are
therefore equivalent to `AbsoluteResidueUnitInertia`: every lift of a norm-one reciprocity class
lies in the kernel of the canonical absolute residue action. The exact-kernel theorem for
`absoluteResidueCoordinateK` proves the equivalent coordinate formulation
`AbsoluteResidueUnitReciprocity`.

The other residual is `RelativeFrobeniusUniformizerRow`, the signed equality on the filtration's
chosen uniformizer. Consequently
`orientedAbsoluteResidueFrobeniusCompatibility_iff_unit_uniformizer` identifies the full global
comparison exactly with:

1. actual residue triviality on norm-one reciprocity units;
2. the geometric-versus-arithmetic Frobenius normalization at one uniformizer.

All seven public declarations in
`RamifiedCertificateRelativeFrobeniusUnitSplit.lean` depend only on `propext`,
`Classical.choice`, and `Quot.sound`. The current reciprocity interfaces still supply neither the
full prime-to-`2` unit-inertia theorem nor the signed uniformizer normalization.

Verification passes the 4,536-job build, fresh 1,124-module scoreboard, and full ledger gate over
45,204 tracked declarations, with zero `sorryAx` dependencies, zero unknown non-standard axiom
uses, and zero terminal violations.

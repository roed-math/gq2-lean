# W188: relative Frobenius reciprocity rows

W187 reduced compatible ramified residue lifting to one signed equality between the actual
absolute residue coordinate and the abstract full tame coordinate on `GalK K`. W188 descends
both continuous `Zhat` coordinates to `GalKab K` and uses the dense local reciprocity image.

The global comparison is equivalent to `RelativeFrobeniusReciprocityRows`, consisting of exactly
two rows:

1. the signed coordinate equality on every norm-one unit of `K`;
2. the signed coordinate equality on the chosen filtration uniformizer.

The proof uses `exists_unit_zpow_decomp` to write every nonzero field element as a norm-one unit
times an integral power of that uniformizer. Density of `MarkedRecip.recip` then promotes the
reciprocity equality to all of `GalK K`. Thus
`orientedAbsoluteResidueFrobeniusCompatibility_iff_rows` is an exact equivalence, not merely a
sufficient criterion.

All nine public declarations in
`RamifiedCertificateRelativeFrobeniusRows.lean` depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

The residue-side frontier is now sharply local-class-field-theoretic. Existing interfaces identify
only the maximal pro-`2` projection of these rows; they do not determine the prime-to-`2`
coordinates of the full `Zhat` equality. The next useful split is to isolate the unit row from the
uniformizer normalization and compare each with the corresponding anchored norm/refinement
interfaces.

Verification passes the 4,535-job build, fresh 1,123-module scoreboard, and full ledger gate over
45,196 tracked declarations, with zero `sorryAx` dependencies, zero unknown non-standard axiom
uses, and zero terminal violations.

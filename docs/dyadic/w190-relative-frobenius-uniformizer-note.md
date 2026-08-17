# W190: the remaining Frobenius uniformizer normalization

W189 separated actual residue triviality on reciprocity units from the signed uniformizer row.
W190 connects that split to the existing full-inertia boundary.

If reciprocity units land in abstract full tame inertia and abstract full tame inertia lies in
canonical absolute inertia, the actual unit-inertia condition is automatic. Under those two
inputs, `orientedAbsoluteResidueFrobeniusCompatibility_iff_uniformizer` proves that the entire
global signed comparison is equivalent to one row at the chosen filtration uniformizer.

That row follows from the expected pair of full `Zhat` normalizations:

- `AbsoluteResidueUniformizerNormalization`: the actual coordinate is `Zhat.ofInt f`, arithmetic
  `2^f`-Frobenius;
- `AbstractTameUniformizerNormalization`: the abstract coordinate is `Zhat.ofInt (-1)`, geometric
  Frobenius.

The exponent `-f` in the relative comparison converts the second value exactly into the first.
AX4 already proves
`maxProPMk_orientedTameQurCoordinateKAb_recip_uniformizer`, the maximal pro-`2` shadow of the
abstract normalization. It does not determine the prime-to-`2` coordinates, and the current
local-reciprocity packet does not state the actual full normalization.

All seven public declarations in
`RamifiedCertificateRelativeFrobeniusUniformizer.lean` depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

Verification passes the 4,537-job build, fresh 1,125-module scoreboard, and full ledger gate over
45,212 tracked declarations, with zero `sorryAx` dependencies, zero unknown non-standard axiom
uses, and zero terminal violations.

# W191: the pro-two Frobenius value does not determine the full value

W190 observed that AX4 fixes only the maximal pro-`2` shadow of the abstract geometric
uniformizer coordinate. W191 makes that insufficiency formal.

The new module `RamifiedCertificateZhatProTwoAmbiguity.lean` proves that `omega2` and
`Zhat.ofInt 1` have the same image in the maximal pro-`2` quotient of `Zhat`, but are distinct.
Their difference is detected by the odd quotient `Multiplicative (ZMod 3)`: `omega2` acts there
by the zeroth power, while the integer exponent `1` acts by the first power.

Taking inverses gives the form used by the geometric uniformizer row:

- `omega2⁻¹ ≠ Zhat.ofInt (-1)`;
- both elements map to `ztwoOne⁻¹` under `maxProPMk 2 Zhat`;
- consequently `maxProPMk 2 Zhat` is not injective, and `ztwoOne⁻¹` has two explicit
  distinct lifts.

Therefore the AX4 theorem
`maxProPMk_orientedTameQurCoordinateKAb_recip_uniformizer` cannot imply
`AbstractTameUniformizerNormalization` without genuinely odd-primary Frobenius/reciprocity
information. This is a mathematical obstruction, not a missing rewriting lemma.

All eight public declarations in `RamifiedCertificateZhatProTwoAmbiguity.lean` depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

Verification passes the 4,538-job build, fresh 1,126-module scoreboard, and full ledger gate over
45,220 tracked declarations, with zero `sorryAx` dependencies, zero unknown non-standard axiom
uses, and zero terminal violations.

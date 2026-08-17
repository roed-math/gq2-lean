# W193: the geometric uniformizer row in the tame quotient

W192 describes the missing abstract uniformizer normalization through finite non-pro-`2` rows in
`Zhat`. W193 translates that residual back to the natural abstract tame quotient.

`AbstractTameUniformizerQurRow T` says that every `g : GalK K` lifting the reciprocity class of
the chosen filtration uniformizer satisfies

```text
qMkQ (T.tameFK g) = qSigmaQ⁻¹.
```

This statement is independent of the lift because the `QurQ` coordinate descends through
abelianization. The normalized equivalence `qurQEquivZhat`, which sends `qSigmaQ` to
`Zhat.ofInt 1`, proves
`abstractTameUniformizerNormalization_iff_qurRow`. Combining this with W192 also proves that the
single quotient row is equivalent to all of the missing non-pro-`2` finite rows.

Thus the abstract side of the remaining odd ramified-data seam now has a field-native statement:
AX4 must be strengthened from the maximal pro-`2` uniformizer value to the full geometric
Frobenius value in `QurQ`. No choice of Galois lift remains in the premise.

All three public declarations in `RamifiedCertificateTameUniformizerQurRow.lean` depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

Verification on 2026-08-17:

- `lake build GQ2`: 4,540 jobs completed successfully;
- `GQ2_LEDGER_GATE=1 bash scripts/check_dyadic.sh`: 45,230 tracked declarations, no `sorryAx`
  dependencies, no unknown non-standard axioms, and no terminal-certificate violations;
- `bash scripts/scoreboard.sh --raw`: 1,128 imported modules and no stale umbrella imports.

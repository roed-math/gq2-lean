# W194: natural Frobenius rows at the uniformizer

W193 expresses the abstract uniformizer normalization directly in the full tame quotient:
every lift of the reciprocity uniformizer maps to the inverse distinguished generator in `QurQ`.
W194 gives the matching field-side statement.

`AbsoluteResidueUniformizerFrobeniusRow B FF` says that every such Galois lift acts on the
absolute residue field by `absoluteResidueFrobenius ^ FF.f`.  The square-Frobenius-normalized
equivalence with `Zhat` proves
`absoluteResidueUniformizerNormalization_iff_frobeniusRow`, so no information is lost in passing
from the coordinate equation to the natural action equation.

The theorem `orientedAbsoluteResidueFrobeniusCompatibility_of_uniformizerRows` combines this
field-action row with W193's `AbstractTameUniformizerQurRow`.  Under the already isolated unit and
full-inertia hypotheses, the two rows imply the signed relative Frobenius comparison and hence
feed the compatible odd ramified-data lane.

The remaining arithmetic issue is now stated without coordinate artifacts: prove geometric
Frobenius in the abstract `QurQ` quotient and arithmetic Frobenius on the actual absolute residue
field for the same reciprocity uniformizer.  The current AX4/marked-reciprocity interface exposes
only their maximal pro-`2` shadows.

All three public declarations in `RamifiedCertificateUniformizerFrobeniusRows.lean` depend only
on `propext`, `Classical.choice`, and `Quot.sound`.

Verification on 2026-08-17:

- `lake build GQ2`: 4,541 jobs completed successfully;
- `GQ2_LEDGER_GATE=1 bash scripts/check_dyadic.sh`: 45,234 tracked declarations, no `sorryAx`
  dependencies, no unknown non-standard axioms, and no terminal-certificate violations;
- `bash scripts/scoreboard.sh --raw`: 1,129 imported modules and no stale umbrella imports.

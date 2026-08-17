# W198: the fixed-C neutral-bracket obstruction

W180 replaced the false unrestricted fixed-`C` bracket-surjectivity premise by a seemingly
sharper condition restricted to relative, abelian-neutral residuals.  W198 proves that this
repair is still impossible.

`not_fixedCRelativeNeutralBracketSurjective` states that
`FixedCRelativeNeutralBracketSurjective c` is false for every `c : DM 2 1`.  The proof chooses
two orthogonal mod-two covectors from the handle and core hyperbolic planes.  Their Heisenberg
marking kills both `c` and the even relator Gram, while a mixed relative commutator has nonzero
central image.  Because the test Heisenberg group has trivial third two-central-series term,
fixed-`C` surjectivity would force that central image to vanish.

This rules out both fixed-`C` one-slot routes:

- unrestricted relative bracket surjectivity fails by the handle-square obstruction;
- abelian-neutral relative bracket surjectivity fails uniformly by the Heisenberg detector.

The remaining honest one-handle route is therefore the balanced multi-slot finite-class
nonemptiness interface from `MpcOneHandleBalancedLimit`.  Any successful proof must choose the
lift tuple jointly (or prove a correspondingly restricted multi-slot graded spanning theorem);
it cannot keep `C` fixed and solve every residual with one adjoint.

The public theorem depends exactly on `propext`, `Classical.choice`, and `Quot.sound`.

Verification on 2026-08-17:

- `lake build GQ2`: 4,545 jobs completed successfully;
- `GQ2_LEDGER_GATE=1 bash scripts/check_dyadic.sh`: 45,318 tracked declarations, no `sorryAx`
  dependencies, no unknown nonstandard axioms, and no terminal-certificate violations;
- `bash scripts/scoreboard.sh --raw`: 1,133 imported modules and no stale umbrella imports.

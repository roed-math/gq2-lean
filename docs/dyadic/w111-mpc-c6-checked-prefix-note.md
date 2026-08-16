# W111: kernel-checked M6 class-six trace prefix

The external class-six collector now emits a compact derivation that Lean replays through the
trusted Boolean checker at default limits.  The generator remains untrusted: the exported
theorem follows only from `Deriv.check = true` and `Deriv.sound`.

Six exact group-law cleanup rules were added to the checker: inverse commutators in each slot,
self-commutator, inverse square, inverse commutator orientation, and repeated-factor squaring.
Each rule is proved directly by the group tactic and adds no axiom.

`MpcC6WeightedTracePrefix.lean` stores 92 separately checked chunks over a shared 826-node word
DAG.  The combined replay has 8,864 derivation nodes and reduces `certificateWord` to a product
of 51 graded factors.  Exactly three endpoint factors have depth three:

`[D,B]^2`, `[[D,B],B]`, and `[B^2,D]`.

The other endpoint factors have depth four or five.  The main evaluation theorem uses exactly
`propext`, `Classical.choice`, and `Quot.sound`; the list checks and exact depth-three
identification are axiom-free.

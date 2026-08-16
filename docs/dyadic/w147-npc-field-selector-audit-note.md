# W147: the exact field-side Npc selector boundary

The corrected family selector determines the positive-level Npc presentation, display, degree,
canonical marking, and core-side structural maps.  It does not construct the field-side marked
core realization needed by `GenAsmBranch`.

`GQ2.Dyadic.Instances.NpcFieldSelectorAudit` records this boundary without inventing a frozen Npc
row.  Its conditional constructors package a tied Npc branch from exactly

```lean
MarkedCoreRealization (DN alpha h) (npcNu alpha r h eta)
```

and add no classification or orientation assumptions.

The compact-N adapter cannot fill this gap.  It requires pointwise agreement with `nuN`, while
`not_npcNu_matches_nuN` proves that `npcNu` already differs at `dnX1`: the positive-level Npc
marking records the unit `eta`, whereas `nuN` is zero there.  The existing primitive-pair route
also collapses the Npc level to zero and therefore cannot certify a genuinely positive-level
branch.

The remaining field-side task is consequently precise: construct an Npc-specific positive-level
marked-core certificate whose `nu_equiv` identifies `npcNu` with the field orientation, then adapt
it to `MarkedCoreRealization`.  The analytic determinant and corrected RN consumers are separate
from this selector problem.

All four public declarations compile with only `propext`, `Classical.choice`, and `Quot.sound`.

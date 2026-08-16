# W152: Npc level certificate from the family selector

The positive-level Npc realization now derives its level, eta residue, and handle clearing from
the selected field data.  Its only remaining coordinate premise is a primitive quotient condition
on the chosen `(sigma, x2)` plane.

`NpcCertificateLevel` adds a divisible-pivot handle clearer.  Unlike the older unit-pivot clearer,
it works when every handle coordinate is a multiple of the level pivot `2^r`.  The new DN lift
clears all handle rows while preserving the plane and `x1` coordinates.

The module defines three reduced inputs:

- `NpcChiKerLevel`, derived from `B.nu_ker_chi_le` and the selector equation `B.r = r`;
- `NpcX1Residue`, derived from `FamilyFieldBranchSelection.arithmetic_matches` and `IsEtaFor`; and
- `NpcPlanePrimitiveAtLevel`, the primitive quotient pair after dividing sigma and `x2` by `2^r`.

`npcMarkedCoreRealization_of_familySelection` discharges the first two automatically, invokes the
positive-level normalization, and returns the exact field-side `MarkedCoreRealization`.  The sole
surviving premise is `NpcPlanePrimitiveAtLevel` for the selected oriented equivalence.

All thirteen public declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
No transported-coordinate fact is attributed to `SemanticSelectedCoreLeavesRN.ofNpc`; that API
describes the canonical target leaves, not an arbitrary field frame.

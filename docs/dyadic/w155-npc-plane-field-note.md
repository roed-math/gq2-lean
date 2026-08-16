# W155: premise-free selected Npc field row

Exact positive level now removes the final primitive-plane premise from the family-selected Npc
lane.

`exists_orientedEquiv_npcPlanePrimitive` applies the exact-level primitive-frame theorem to the
transported field marking.  It precomposes the oriented `DN` equivalence by the chi-preserving
Eichler correction and returns an oriented equivalence whose divided sigma/x2 row is primitive.

`npcMarkedCoreRealization_of_familySelection_exactLevel` feeds that corrected equivalence to the
positive-level Npc certificate.  The resulting realization has the exact canonical marking
`npcNu`.  No plane-coordinate or handle-clearing premise remains.

The final two endpoints package the selected field branch and its corrected RN residual:

- `npcGenAsmBranch_of_familySelection_tied_exactLevel`
- `npcRowResidualRN_of_familySelection_exactLevel`

Both retain the ordinary oriented field equivalence input, but no Npc-specific campaign residual.
All four declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The next highest-leverage selector front is the general-h compact-N level-zero realization.

# W153: Npc family-selection RN endpoint

The selected positive-level Npc branch now reaches the corrected RN row with exactly one explicit
field-coordinate premise, `NpcPlanePrimitiveAtLevel`.

`npcGenAsmBranch_of_familySelection_tied` composes the W152 realization with the W147 tied branch
constructor.  It transports the selector's dependent display and returns a `GenAsmBranch` whose
presentation and marking are tied to the selected Npc data.

`npcRowResidualRN_of_familySelection` then supplies the unconditional W148 Npc determinant and
corrected word certificate.  Its result is a selected tied branch together with
`Nonempty (GenAsmRowResidualRN G)`.

Both declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.  No candidate
equivalence wrapper is duplicated: once the residual exists, `genAsm_candidate_equiv_galKRN` is
the generic continuation.

This module does not hide the remaining frame choice.  Both public endpoints retain exactly
`NpcPlanePrimitiveAtLevel` for the transported sigma/x2 plane.

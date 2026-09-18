# W361: uniform legacy L/N denotation bridges

The additive module `GQ2/Dyadic/Word/GeneralTemplateLN.lean`, namespace
`GQ2.Dyadic.GeneralTemplateLN`, proves exact denotation of the **existing** raw
factories at arbitrary rank and parameters:

```text
denote_rawLsq h
  : Export.denote (LSq.denoteCtx h) (LSq.rawLsq h)
      = some (LSq.lSqW h)

denote_rawNCompact alpha h
  : Export.denote (Words.denoteCtx h) (Words.rawNCompact alpha h)
      = some (Words.nCompactW alpha h)

denote_rawNpc alpha r h num den
  : Export.denote (Words.denoteCtx h) (Npc.rawNpc alpha r h num den)
      = some (Npc.npcW alpha r h ⟨num,den⟩)

denote_rawNpc_display alpha r h d
  : Export.denote (Words.denoteCtx h)
      (Npc.rawNpc alpha r h d.data.num d.data.den)
      = some (Npc.npcWUnit alpha r h eta)
```

The last theorem takes `d : NpcDisplayFor eta`, including exact representation
of the supplied unit. `wf_rawNpc_display` also proves this same tree passes
the existing well-formedness test. A merely congruent rational number is not
silently substituted for eta. The unrestricted raw numerator/denominator
theorem is a literal syntax/denotation statement, not a claim that malformed
or even-denominator trees satisfy the old exporter validity rules.

The proof uses the existing `Export.handleFactors` interpreter unchanged. A
generic theorem rewrites its ordered `List.range h` traversal to
`List.finRange h`, proves that the supplied handle-generator lookups succeed,
and obtains the exact semantic commutator list. Separate even/odd alphabet
instantiations discharge all index bounds. The L zero/successor split follows
its original syntax convention: no handle node at h=0. It is not a finite
rank enumeration. N0/Npc retain their count-zero node at h=0.

Thus the fixture-only denotation comments in `Words/L.lean`, `Words/N0.lean`
and `Words/Npc.lean` describe the previous proof frontier, not an inherent
semantic obstruction. No old source comment or factory was edited. No new
tree factory, handle-node encoding, association convention, fixture, hash,
manifest, original exporter or gate was changed. The new module imports the
old definitions and proves stronger theorems about exactly those definitions.

All ten public declarations pass default Lean checks, warning-free, with only
`propext`, `Classical.choice`, and `Quot.sound`. These general denotation proofs
close the mathematical tree-to-word seam for the selected L/N words; they do
not generate or approve a new publication fixture catalog, a universal finite
display for every external two-adic unit, or a revised release/appendix format.

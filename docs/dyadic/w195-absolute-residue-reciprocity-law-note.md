# W195: the absolute-residue local reciprocity law

W194 isolates the action of a reciprocity uniformizer on the absolute residue field.  W195
combines that row with the unit row into the canonical field statement.

`AbsoluteResidueLocalReciprocityLaw B FF` says that if `x : K×` has filtration valuation `n`,
then every Galois lift of `rec_K(x)` acts on the absolute residue field by
`absoluteResidueFrobenius ^ (FF.f * n)`.  The theorem
`absoluteResidueLocalReciprocityLaw_iff_rows` proves that this is exactly the conjunction of:

- reciprocity units acting trivially on the absolute residue field; and
- the chosen uniformizer acting by the `FF.f`-th power of square Frobenius.

The decomposition `K× = O_K× · π^ℤ` proves the reverse implication.  Consequently
`orientedAbsoluteResidueFrobeniusCompatibility_of_localReciprocityLaw` combines the single
field law with W193's geometric `QurQ` row and the abstract unit refinement.  Unlike the W194
two-row consumer, it needs no separate full-inertia containment: that containment follows from
the resulting signed relative Frobenius comparison.

This is the sharp classical field-side residual missing from the current `MarkedRecip` packet.
Its existing `nu_ur` clauses record only the maximal pro-`2` unramified coordinate and do not
identify local reciprocity with the canonical action on the full absolute residue field.

All five public declarations in `RamifiedCertificateAbsoluteResidueReciprocityLaw.lean` depend
only on `propext`, `Classical.choice`, and `Quot.sound`.

Verification on 2026-08-17:

- `lake build GQ2`: 4,542 jobs completed successfully;
- `GQ2_LEDGER_GATE=1 bash scripts/check_dyadic.sh`: 45,240 tracked declarations, no `sorryAx`
  dependencies, no unknown non-standard axioms, and no terminal-certificate violations;
- `bash scripts/scoreboard.sh --raw`: 1,130 imported modules and no stale umbrella imports.

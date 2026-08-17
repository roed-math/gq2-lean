# W196: the abstract tame local reciprocity law

W195 packages actual residue-field reciprocity as one law on all of `K×`.  W196 supplies the
parallel statement on the abstract tame side.

`AbstractTameLocalReciprocityLaw T` says that any lift of `rec_K(x)` has full unramified tame
coordinate `qSigmaQ ^ (-dyadicValuation FF x)`.  The minus sign is the repository's geometric
Frobenius convention.  The theorem `abstractTameLocalReciprocityLaw_iff_rows` proves that this
law is exactly the conjunction of:

- reciprocity units landing in the full tame-inertia subgroup; and
- the reciprocity uniformizer mapping to `qSigmaQ⁻¹`.

The reverse implication uses `K× = O_K× · π^ℤ`, so the result controls every element rather
than only the two generating rows.  The theorem
`orientedAbsoluteResidueFrobeniusCompatibility_of_reciprocityLaws` then combines W195's actual
law and W196's abstract law directly.  No separate unit-refinement, full-inertia, or coordinate
normalization premise remains in that consumer.

The odd ramified-data field boundary is therefore two classical comparison statements: local
reciprocity acts on the absolute residue field by arithmetic Frobenius to the valuation, and the
oriented tame quotient records the same reciprocity class by geometric Frobenius to the negative
valuation.  AX3/AX4 currently expose only their maximal pro-`2` shadows.

All three public declarations in `RamifiedCertificateAbstractTameReciprocityLaw.lean` depend
only on `propext`, `Classical.choice`, and `Quot.sound`.

Verification on 2026-08-17:

- `lake build GQ2`: 4,543 jobs completed successfully;
- `GQ2_LEDGER_GATE=1 bash scripts/check_dyadic.sh`: 45,244 tracked declarations, no `sorryAx`
  dependencies, no unknown non-standard axioms, and no terminal-certificate violations;
- `bash scripts/scoreboard.sh --raw`: 1,131 imported modules and no stale umbrella imports.

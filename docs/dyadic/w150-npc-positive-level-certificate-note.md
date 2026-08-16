# W150: positive-level Npc marked-core certificate

The missing field-side Npc realization from W147 now has a constructive certificate and adapter.
It is not assumed as a classification fact.

`NpcMarkedData` is the exact finite generator-row input.  Relative to an oriented equivalence, it
requires:

- the sigma and `x2` values to share the factor `2^r`, with a primitive quotient pair;
- the `x1` value to be congruent to `eta` modulo `2^r`; and
- all handle rows to vanish.

`npcPlane_normalize` uses an `SL2` plane correction to make sigma exactly `2^r`.
`npcMarkedMatching` then uses the existing N2 and N5 corrections to clear `x2` and correct `x1`
while preserving the cyclotomic character.  The result is equality with `npcNuPadic` on every
generator and hence on the whole group.

`MarkedCoreCertificateNpc` packages the oriented equivalence and correction.  The field-side
adapter `npcCert_realization` constructs the common `MarkedCoreRealization`, including the exact
`nu_equiv` that was missing in W147.  The headline
`npcMarkedCoreRealization_of_oriented` produces that realization from an oriented equivalence and
`NpcMarkedData`.

All public declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The remaining selector-side arithmetic is now explicit rather than structural: produce the
finite row data from the selected field marking.  In particular, weakening zero handle rows to a
divisibility statement needs a positive-level handle-clearing lemma; the existing handle clearer
uses a unit pivot and does not apply directly for `r > 0`.

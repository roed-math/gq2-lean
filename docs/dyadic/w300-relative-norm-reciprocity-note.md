# W300: relative finite-abelian norm reciprocity

W299 reduced the compatible odd-degree residue calculation to the conventional statement that
the reciprocity image of the units in every finite abelian layer `L/K` has cardinality
`e(L/K)`.  W300 proves that statement from the full finite-layer norm-reciprocity theorem.

The new module
`GQ2.Dyadic.Instances.RamifiedCertificateRelativeNormReciprocity` defines
`RelativeFiniteAbelianNormReciprocity`.  For each finite abelian Galois layer inside `Qbar_2`,
this supplies its relative Artin map, surjectivity, the norm-subgroup kernel, and compatibility
with restriction of lifts of `MarkedRecip.recip`.

The proof is uniform over `K` and `L`.  Its analytic core is

```text
e(L/K) * v_K(N_{L/K}(pi_L)) = [L:K].
```

It then proves that the valuations of the relative norm subgroup are exactly the multiples of
`v_K(N pi_L)`.  The decomposition `Kx = O_Kx * pi_K^Z` reduces the quotient by the unit image to
one cyclic generator, giving

```text
# image(O_Kx) = e(L/K).
```

Consequently
`relativeUnitIndexReciprocity_of_relativeFiniteAbelianNormReciprocity` discharges W299's unit
index premise.  The endpoint
`gammaR_lSq_equiv_galK_oddDegree_of_baseAndRelativeNormReciprocity` now exposes only three
standard local-CFT inputs: the absolute residue law at `Q_2`, the full tame reciprocity law at
`K`, and full finite-abelian norm reciprocity over `K`.

All new analytic and reduction declarations use only `propext`, `Classical.choice`, and
`Quot.sound`.  The final endpoint inherits only the campaign's existing Hilbert, duality, and
general assembly axioms.  No class, presentation family, or handle count appears in this wave.

What remains on this lane is no longer a unit-count argument.  It is the construction or
adoption of the standard relative finite-layer Artin/norm-reciprocity theorem itself; the
current `MarkedRecip` interface deliberately omits that theorem and its pro-2 kernel API is too
narrow for the odd-primary unramified part of the compatible anchored fields.

# W185: local cyclotomic conjugacy and residue-action surjectivity

W185 closes the finite local-cyclotomic theorem isolated by W183.  The valuation ring of the
absolute `2`-adic algebraic closure is Henselian: a monic polynomial splits in the algebraic
closure, its roots are integral, and a product whose norm is less than one has a factor whose
norm is less than one.

Let `zeta` be a primitive odd-order root.  Reduce its integral minimal polynomial to the residue
field.  Square Frobenius preserves the reduced polynomial, and oddness makes that polynomial
separable.  Hensel lifting at the squared residue produces a root close to `zeta ^ 2`; separation
of distinct odd roots forces the lift to equal `zeta ^ 2`.  Hence

```text
IsConjRoot Q_2 zeta (zeta ^ 2).
```

The W182--W183 compactness equivalences now produce one absolute Galois element squaring every
odd-order root of unity.  W181 identifies this with surjectivity of the canonical absolute
residue action.  The new public endpoints are:

- `absoluteNormInteger_henselianLocalRing`;
- `primitiveOddRoot_isConjRoot_square`;
- `exists_squaresOddRootsOfUnity`;
- `absoluteResidueAlgAction_surjective`.

All four declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The Odd-L residue front has therefore moved past finite lifts and action surjectivity.  The next
residue theorem is the normalized continuous identification of the absolute unramified quotient
with `Zhat`, followed by its commuting comparison with the oriented tame quotient.  The anchored
involution norm side remains the separate unit-spectral reciprocity problem.

Verification passes the 4,532-job build, fresh 1,120-module scoreboard, and full ledger gate over
45,120 tracked declarations.

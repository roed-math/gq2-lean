# W182: finite odd cyclotomic lifts assemble automatically

W181 reduced surjectivity of the canonical absolute residue action to one absolute Galois
element that squares every odd-order root of unity. W182 removes compatibility between the
finite cyclotomic approximations to that element.

The new module
`GQ2/Dyadic/Instances/RamifiedCertificateOddRootFrobeniusCompactness.lean` defines the closed
locus `oddRootFrobeniusSet m` of absolute Galois elements squaring every `m`-th root of unity.
These loci are antitone under divisibility. The odd levels form a directed system under
multiplication, so compactness gives

```text
one element squares every odd-order root
  iff for each odd m, some element squares every m-th root.
```

The finite choices need not be compatible. This isolates the remaining arithmetic theorem as
finite-level existence for each odd `m`: the local cyclotomic Frobenius at `2`. Mathlib contains
finite-field Frobenius and normal-extension lifting, but the repository has no theorem showing
that the square permutation of odd roots is a `Q_2`-automorphism of the finite cyclotomic layer,
or equivalently that it lifts through the local residue exact sequence.

All declarations use only `propext`, `Classical.choice`, and `Quot.sound`; no finite or global
Frobenius existence statement is assumed.

Verification passes the 4,527-job build, fresh 1,116-module scoreboard, and full ledger gate over
45,071 tracked declarations.

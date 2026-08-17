# W183: finite odd-root Frobenius is local conjugacy

W182 reduced the global odd-root Frobenius element to independent finite lifts at every odd
cyclotomic level. W183 identifies each finite lift with one local minimal-polynomial equality.

For a primitive `m`-th root `zeta`, every `m`-th root is a power of `zeta`. Therefore an absolute
Galois element belongs to `oddRootFrobeniusSet m` exactly when it sends `zeta` to `zeta ^ 2`.
Normality of the algebraic closure then gives

```text
oddRootFrobeniusSet m is nonempty
  iff zeta and zeta^2 are conjugate over Q_2
  iff minpoly Q_2 zeta = minpoly Q_2 (zeta^2).
```

It is enough to prove this equality for one primitive root at each odd order. Combined with W182,
the global residue Frobenius exists exactly when these independent local equalities hold.

All declarations use only `propext`, `Classical.choice`, and `Quot.sound`. The remaining theorem is
the classical local cyclotomic fact that square Frobenius preserves the `Q_2`-conjugacy class of a
primitive odd-order root; no version of that fact is assumed here.

Verification passes the 4,528-job build, fresh 1,117-module scoreboard, and full ledger gate over
45,080 tracked declarations.

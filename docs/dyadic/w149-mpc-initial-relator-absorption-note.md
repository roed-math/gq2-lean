# W149: all-degree Mpc initial-relator absorption

The five marked-cost tower families isolated in W143 are now absorbed at every depth and every
`Z2` coefficient.  The final theorem is

```lean
MpcMk.mpcMk_initialRelatorAbsorption (r : Nat) (hr : 2 <= r) :
  MpcMkInitialRelatorAbsorption r hr
```

The proof is fully kernel checked.  A cutoff-four reflected checker verifies five sparse base
identities.  Those equalities are bridged to concrete marked-cost range witnesses, propagated by
an exact square theorem, extended to the canonical B/C/D towers, and finally assembled for an
arbitrary `Z2` coefficient using row divisibility and congruence modulo the next filtration rung.

The implementation is split into seven modules to stay under the default 200,000-heartbeat
budget:

- `MpcInitialRelatorBaseChecker`
- `MpcInitialRelatorBaseTrace`
- `MpcInitialRelatorBase`
- `MpcInitialRelatorTower`
- `MpcInitialRelatorRange`
- `MpcInitialRelatorAbsorptionCore`
- `MpcInitialRelatorAbsorption`

No option override, opaque computation, external axiom, or unchecked finite quotient is used.
The final theorem and all semantic bridge theorems depend only on `propext`, `Classical.choice`,
and `Quot.sound`.

This discharges the last open premise of `MpcMkHeadCompletion`.  The next composition wave must
feed it through head reflection/source exactness and the secondary marked-cost range argument to
obtain uniform `MpcMkGood` propagation, `MpcPivShift 2`, and the unconditional sqrt(-10) endpoint.

# W221: the finite linear CABD cokernel

W221 quotients W220's finite `ZMod 4` target by the range of the combined CABD linear map.
The result is the finite module `OneHandleBalancedCABDZModFourCokernel`.  The prescribed
relative `C` class determines one canonical element
`oneHandleBalancedCABDZModFourObstruction` in that module.

The theorem `neutralityObstruction_eq_one_iff_CABDZModFourObstruction_eq_zero` identifies
vanishing of this element with vanishing of the original one-handle neutrality obstruction.
Thus the remaining selector boundary no longer contains an existential range witness: it is
the computation of one explicit element in a finite `ZMod 4`-module cokernel.

No cokernel-vanishing, rank, invariant-factor, or dimension assertion is made.  Every public
declaration has exactly the standard axiom set `propext`, `Classical.choice`, and `Quot.sound`.

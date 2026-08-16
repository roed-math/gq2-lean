# W140: ramified Npc full-offset Hessian

The honest ramified procyclic-N Hessian is now evaluated at its nonzero twisted offset.

- The omega2 block is computed exactly as the existing `powCharge` rather than discarded.
- Delta, D, E, boundary, and handle blocks are evaluated for arbitrary offsets.
- On the honest two-entry normal cochain, the boundary and corrected cross terms combine to
  `polar(c1, A^-1 c0)`.
- The complete `hessRelZ` formula consists of an explicit powCharge-bearing diagonal, that cross
  term, and the standard hyperbolic handle tail.

All twenty-four exported declarations use only the standard axioms or a subset.  The remaining
analytic task is one-dimensional: prove the displayed `npcRamifiedDiagonal` quadratic and feed it
to the W138 comparison base.

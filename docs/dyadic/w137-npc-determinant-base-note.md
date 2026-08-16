# W137: generic Npc determinant consumer

The arbitrary-unit procyclic-N determinant record now has a final analytic consumer.

- Any branch-free word-phase supply discharges both affine determinant clauses.
- A complete `wPnpcPhaseModel` therefore yields the affine determinant certificate directly.
- The varying head quadratic and its Gauss evaluation remain internal to the phase model; no
  diagonal-specific Gauss premise appears in either theorem.

Both exported declarations use exactly the standard three axioms.  Once the ramified
twisted-offset comparison is proved, it can be combined with W136 and fed directly to this
module.

# W126: unrestricted reflection for the marked Mpc successor

The existing even-family derivation theorem now has an exact Mpc cost interpretation.  Membership
in the three crossed-derivation kernels produces four unrestricted depth-r corrections whose
`mpcBldIncr` realizes the given top-layer class.

Consequently, every class in `mpcMkFiveNecessaryKernel` has an explicit unrestricted four-slot
cost witness.  The `nu` and `chi` hypotheses are intentionally unused at this stage.  Their role
is the remaining carrier refinement: replace the arbitrary depth corrections by the marked
carriers without changing the top cost class.

All eight exported declarations use exactly the standard three axioms.  No common-kernel equals
marked-range theorem is asserted.

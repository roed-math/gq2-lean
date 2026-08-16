# W158: arbitrary-h compact-M phase data

The compact-M Hessian and graph phase calculations now include every handle plane.

On the honest ramified branch, `evalFin_mCompact_ramified_handles` extends the landed core
cancellation by the hyperbolic handle sum from `evalFin_handlesW`.  Its `hessRelZ` wrapper needs
only the usual odd-order, fixed-point-free tau action and resolver lift.

The phase layer records both arbitrary-h branches:

- the existing unramified P1 calculation is exactly `wPhCompactWallHandlePhase`;
- the ramified calculation is `wPcMRamifiedHandlePhase`, which becomes the same compact
  wall-handle phase after swapping the two head coordinates.

`wPcM_QZero_eq_ramifiedHandlePhase_of_headMark` carries the honest ramified calculation through
the graph-Hessian trace seam.  No new quadratic or Gauss premise is introduced.  All public
declarations use only the standard three axioms or a subset.

The remaining arbitrary-h work is projected-head comparison and the boundary/supply assembler.

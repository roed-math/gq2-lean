# W161: arbitrary-h compact-M branch-free supply

The compact-M analytic lane is now branch-free at every handle count.

`wPcMComparison_boundary_handles` divides the honest boundary into its unramified and ramified
head actions and applies the two common-phase comparisons from W160.  All projected-head,
resolver, odd-order, and fixed-point-free facts are derived inside the boundary proof.

`wPcM_compactWallHandlePhase_gaussSum` evaluates the shared wall-handle phase as the standard
ramified Gauss value in degree `2h+2`.  Consequently `wPcM_branchFreeSupply_handles` exports
`wPhBranchFreeSupply (2*h+2)` from the concrete tame/pro-2 compatibility and generator values.

No branch, quadratic, resolver, or Gauss premise survives in the public supply.  All four public
declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The remaining compact-M analytic work is routine consumption into the affine determinant and
corrected word certificate.  The independent field-side canonical `C0` pivot premise remains.

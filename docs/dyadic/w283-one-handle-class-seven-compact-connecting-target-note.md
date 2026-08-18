# W283: dual criterion for the compact connecting target

W282 proved that every compact connecting value is realized and reduced ordinary relative
solvability to membership of a reference obstruction in the connecting image.  W283 turns that
membership problem into an exact finite dual test.

`oneHandleCompactConnectingImageTranspose` sends an F2-character of the ordinary relative
cokernel to its evaluations on all compact-kernel corrections.
`oneHandleCompactConnectingTargetEvaluation` evaluates the same character on a reference
obstruction.  The predicate `OneHandleCompactConnectingTargetTransposeVanishing` says that
every character annihilating the image also annihilates the target.

Finite F2 dual separation proves that this predicate is equivalent to image membership.
Appending target evaluation gives `oneHandleCompactConnectingTargetAugmentedTranspose`, and
`ordinaryRelativeSolvable_iff_connectingTarget_ker_eq` states the final criterion: solvability
is equivalent to equality of the augmented and unaugmented transpose kernels.  The remaining
work is therefore a concrete finite kernel or rank computation, not a lift-realization issue.

# W207: the finite four-core correction equation

W206 converts two-central depth plus exact handle-forgetting into a finite relative layer.
W207 packages the complete W205 correction problem at level `k+1`.

`OneHandleBalancedCoreLevelCorrection k` has four finite coordinates. The `A`, `B`, and `D`
coordinates lie in `oneHandleRelativeLambdaImage (k-1) (k+1)`. The `C` coordinate lies in
`oneHandleNeutralRelativeLambdaImage`, defined as the image of exact relative elements killed
by every continuous `Z_2`-valued character. This retains the original condition without
claiming that it is intrinsically visible on an arbitrary finite quotient class.

`nonempty_coreShiftCorrection_iff_exists_levelCorrection` proves that a W205 group-level
correction exists exactly when these four finite coordinates solve the level-`k+1` stage-shift
equation. The reverse direction chooses exact representatives independently using W206 and
the neutral image definition; the finite correction marking then agrees coordinate by
coordinate with the projected group marking.

Consequently `OneHandleBalancedCoreLevelSupply` is equivalent to the previous group-level
supply, and `mpcPivShiftH_two_one_of_balancedCoreLevel` is its final pivot consumer. The
remaining boundary is now a finite constrained image problem for the four-coordinate shift
map, not an inverse-limit or representative-selection problem.

Every declaration has exactly the standard axiom set `propext`, `Classical.choice`, and
`Quot.sound`.

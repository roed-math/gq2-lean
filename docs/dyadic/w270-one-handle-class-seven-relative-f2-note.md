# W270 — the class-seven ordinary-relative transpose

W269 isolates ordinary relative coverage as the first of two finite obstructions.  The
ordinary quotient is elementary abelian: every element has square one.  Finite elementary
duality therefore turns target membership into a `ZMod 2` test on the relative central layer.

At the standard marking, span annihilation is exactly the conjunction of four row equations.
For every relative depth-five class `x`, a functional must kill

* `x^2 [x,A] [x,B]` in the `A` row;
* `[x,A]` in the `B` row;
* `[x,D]` in the relaxed `C` row; and
* `[x,C]` in the `D` row.

`oneHandleC7StandardRelativeCoordinateTranspose` packages these four pullbacks into one finite
linear map.  The theorem
`standardRelativeTargetTransposeVanishing_iff_target_mem_relaxed` says that ordinary relative
coverage holds exactly when every functional in its kernel kills the selected W268 target.
Combining this with W269 gives an exact two-part endpoint: the transpose-kernel target value
must vanish, and the smaller neutral-`C` obstruction must vanish.

No rank equality or target vanishing is asserted.  The next task is to compute the transpose
kernel (or its augmented rank) at the standard class-seven marking; the separate neutrality
quotient is only needed after that first calculation closes.

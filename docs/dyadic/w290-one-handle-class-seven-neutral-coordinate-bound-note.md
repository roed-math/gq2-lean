# W290: class-seven neutral coordinate bound

W289 reduced full one-handle class-seven correctability to a one-bit rank-jump test on the
neutral connecting target.  W290 identifies the ambient neutral target explicitly enough to
bound that calculation.

The standard neutral cokernel is first transported to the generic balanced neutral cokernel
at `oneHandleStandardBalancedPoint`.  The generic coordinate theorem presents it as a quotient
of `(ZMod 4)^2`.  W288 already proved that every target element has square one, so the two
coordinate squares lie in the interaction range.  Consequently the coordinate quotient
factors through the parity plane `(ZMod 2)^2`.

The public conclusions are:

- `oneHandleC7StandardNeutralityParityFactor_surjective`: the two-bit parity plane surjects
  onto the standard neutral target;
- `natCard_oneHandleC7StandardNeutralityCokernel_le_four`: the target has at most four
  elements;
- `oneHandleC7StandardNeutralityFinrank_le_two`: its `F₂`-dimension is at most two.

Thus the remaining W6 computation is no longer an abstract finite search.  It is a rank test
on a target with at most two parity coordinates.  This wave does not evaluate the neutral
connecting image in those coordinates.

# W280 — the compact connecting transpose

W279 reduced the remaining ordinary class-seven statement to containment of the compact-kernel
shift range in the relaxed four-row span.  W280 dualizes that finite inclusion.

`oneHandleCompactKernelTranspose` evaluates each ambient `F₂` character on every compact-kernel
shift.  Pairing it with the existing four-row coordinate transpose gives
`oneHandleCompactAugmentedTranspose`.  The compact connecting homomorphism is trivial exactly
when the augmented transpose and the original coordinate transpose have the same kernel.  It is
also equivalent to equality of their finite `F₂` ranks.

This is the finite linear-algebra form of the frontier: a checker may establish one kernel or
rank equality without choosing legal compact-lift representatives.  The theorem does not
assert that equality, nor does it settle the reference obstruction or neutral-C constraint.

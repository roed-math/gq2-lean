# W291: class-seven neutral rank bound

W290 proved that the standard neutral target is an `F₂`-space of dimension at most two.
W291 transfers that bound to the two transpose maps from the W289 rank criterion.

Both `oneHandleCompactNeutralImageTransposeRank` and every augmented target rank are at most
two.  Hence the neutral-image rank is one of `0`, `1`, or `2`.  The rank-two case is decisive:
the augmented rank cannot increase, so W289 immediately gives full `OneHandleW6Correctable`.

The exact remaining positive target is therefore the finite statement
`oneHandleCompactNeutralImageTransposeRank = 2`.  If that fails, only ranks zero and one remain
and the obstruction is still the one-bit augmentation jump isolated in W289.

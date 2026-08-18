# W288: dual test for the class-seven neutral target

W287 reduced the remaining neutral-C condition to membership in the finite image of
`oneHandleCompactNeutralConnectingHom`. W288 dualizes that image-membership question over
`F₂`.

`oneHandleCompactNeutralImageTranspose` evaluates every character of the neutral-C cokernel
on the compact connecting kernel. The augmented transpose adds evaluation at a chosen neutral
obstruction. That obstruction lies in the image exactly when every character annihilating the
image also annihilates the target, equivalently when the augmented and unaugmented transpose
kernels agree.

Applied to any ordinary correction, this gives
`oneHandleW6Correctable_iff_neutralTarget_ker_eq`: full W6 correctability is now one exact
finite kernel-equality test. The kernel is not computed in this wave.

The module also defines the unaugmented and augmented `F₂` ranks used by the next rank-jump
criterion; it does not determine either value.

# W308: characteristic orientation rules out the transitivity shortcut

W308 tests W307's uniform transitivity proposal against the expected intrinsic nature of the
cyclotomic orientation.  `MCoreOrientationCharacteristic alpha h` says every automorphism of
`DM alpha h` preserves `chiM`.  Given one oriented field equivalence, this is equivalent to
`MFieldOrientationRigidityAt alpha h`: every abstract equivalence from the core to the field's
maximal pro-2 quotient is oriented.

These conditions have two sharp consequences.

First, characteristic orientation is incompatible with transitivity of all surjective
`Ztwo` markings whenever a handle exists.  W307's handle character and canonical compact-M
marking are separated by the oriented `C`-pivot invariant, so an automorphism joining them
would have to change the canonical orientation.

Second, under field orientation rigidity, W305's canonical marked-core realization already
forces W303's exact distinguished-`C` pivot.  This is proved uniformly for compact M and
procyclic M, then assembled as
`evenCanonicalMarkingBoundary_of_realization_of_orientationRigidity`.

Accordingly, unrestricted marking transitivity is not the right general theorem if the
cyclotomic character is indeed the characteristic dualizing orientation.  The honest general
front is now the invariant-stratified M normal-form problem: prove the arithmetic pivot within
the canonical oriented stratum, or construct an alternate word/certificate normal form around
the mobile exact-level kernel value already supplied in every selected M row.

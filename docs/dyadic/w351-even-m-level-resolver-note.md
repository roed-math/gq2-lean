# W351: coefficient-independent level resolution for general even M

W351 removes the coefficient dependence left in W350's finite-target resolver.  At every
nonzero killing level `N`, the cyclic test group `Z/N` detects the residue class of an arbitrary
profinite exponent.  Mapping its generator to any target element whose order divides `N`
transports the chosen integer representative to that target.  The parity detector from W350 is
retained at the same time.

The resulting `levelStokesZhatResolver` and `levelStokesZtwoResolver` depend only on `N`.  They
resolve every profinite word in every finite group killed by `N`, independently of the eventual
coefficient module.  The prime-to-two corrected, all-rank normalized even-M word therefore
supplies the generic `RowActionImage.LevelResolver` required by fixed-word action-image
devissage.

This is not a class-seven or finite-rank argument.  It is uniform in the word, rank, handle
count, field, and coefficient.  The remaining analytic seam is now exactly
`SimpleActionImageStokes` for the corrected normalized word.  Resolver correctness and the
Stokes endpoint no longer occur among its premises; the next proof should transport or compare
the simple action-image complex under the two Nielsen changes and the tame correction.

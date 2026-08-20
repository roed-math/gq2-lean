# W332: flexible even-M certificates

W332 removes the canonical-pivot marking from the analytic side of both even-M families.

For compact M, `mCompactWordCertificateRN_flexible` constructs the complete corrected
certificate from any `FlexibleCoreLeavesRN` for the compact word.  For procyclic M,
`mpcWordCertificateRN_flexible` does the same at every positive level, honest display, and
handle count.  Their determinant and intermediate-leaf constructors are also public.

The input is exactly a presented pro-2 core whose `Z₂` marking is normalized on sigma and the
wild letters.  Exact lifting, Stokes duality, scalar counts, both word-phase branches, Gauss
sums, and affine determinants are then theorems.  No distinguished-C field pivot appears.

This is the general-case analytic endpoint sought after the odd-residue counterexample to the
old canonical compact-M target.  What remains is a single group-theoretic normal-form problem:
construct a normalized `CorePresentation` from the field's coordinate-free mobile pivot.  It
is not another nilpotency-class calculation.

All six public declarations print exactly the standard trust base
`[propext, Classical.choice, Quot.sound]`.

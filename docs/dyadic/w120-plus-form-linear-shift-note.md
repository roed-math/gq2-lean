# W120: remove the procyclic-M linear phase charge

An additive first-slot shift of `plusFormD q q` is absorbed by translating the second slot.  If
`ell(v) = polar q v y`, then

`plusFormD q q (v, w) + ell(v) = plusFormD q q (v, w + y)`.

Nonsingularity supplies `y`, so the translation is an equivalence.  It preserves the Gauss sum
and transports `SourceWordPhaseComparison` back to the unshifted plus form without a constant or
sign correction.

For the `pp = 1` procyclic-M phase, the charge is `dat.m g`.  The new specialization keeps the
essential hypothesis explicit: `g` must act trivially, which makes this charge additive by
factor-set equivariance.  Thus the honest `pp = 1` linear refinement needs no new Gauss-sum
calculation.

# W349: all-rank tame correction for the normalized even-M source

W349 closes the source-structural seam left by W348 without returning to a class-by-class
calculation.  It first proves generically that the closed tame-inertia subgroup of `Tq q` is
exactly the profinite line

```text
{ (tqTau q)^z : z in Zhat }.
```

Consequently any word whose tame defect lies in inertia can be corrected by appending the
inverse corresponding profinite `tau`-power.  This correction specializes to the ordinary tame
quotient and is invisible in every pro-`2` evaluation, so it preserves a complete
`CorePresentation`.

For the W348 normalized strict-handle word, the membership proof uses the full unramified
coordinate `tqToZhat`, not merely its maximal pro-`2` projection `nuTq`.  Quotientwise, every
new shear value is `omega2`-fixed, the compact-M factors cancel in the commutative full
unramified quotient, and the core-zero shear coefficient is identically zero.  Therefore the
whole tame defect lies in actual tame inertia in every rank and handle count.

The final outputs are `headHandlePairTameCorrectedW_specializes` and
`headHandlePairTameCorrectedFlexibleCore`.  Together they give one changed word with ordinary
tame specialization and complete normalized pro-`2` core leaves.  The remaining work is now
analytic certificate supply for this genuinely changed word; no source-normalization or tame
specialization premise remains.

All public theorem pins use exactly `propext`, `Classical.choice`, and `Quot.sound`.

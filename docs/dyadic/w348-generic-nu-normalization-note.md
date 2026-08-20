# W348: rank-generic normalization of the unramified rows

W348 replaces W347's remaining all-wild hypothesis by one general Nielsen argument.  For an
arbitrary finite-rank `CorePresentation`, suppose only that the distinguished `sigma` row has
value `1` in `Ztwo`.  Write `k_i` for the additive `Z_2` coordinate of the `i`-th wild row and
simultaneously substitute

```text
x_i  |->  x_i * sigma^(-k_i).
```

The inverse substitutes `x_i * sigma^(k_i)`.  These substitutions form one syntactic Nielsen
pair, fix `sigma` and `tau`, and kill every wild row.  Transport of the core presentation
therefore produces complete `FlexibleCoreLeavesRN` in every rank.  No branch, degree, handle
count, field, or nilpotency-class hypothesis occurs.

The only semantic input in the row computation is the new generic theorem that the profinite
exponent `padicOmega2 u` acts on every pro-`2` group by ordinary `Z_2`-powering by `u`.  Its
proof is quotientwise and is now located outside the branch modules.

Applying the theorem to W347 gives `headHandlePairNormalizedFlexibleCore`.  The former
`HeadHandlePairWildNormalized` premise disappears: the promoted handle row alone is enough.
The next general seam is analytic transport for this uniformly sheared word, not another
class-by-class core calculation.

All public theorem pins use exactly `propext`, `Classical.choice`, and `Quot.sound`.

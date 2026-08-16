# W169: filtered Mpc pivot and compatible ramified atoms

Wave 169 identifies the positive-level Mpc pivot exactly and removes the
structural part of both remaining compatible odd-L ramified inputs.

## The Mpc pivot is one divided digit

`MpcFieldPivotFiltered` defines the canonical coefficient obtained after
dividing the distinguished C value by `2^r` and its mod-two digit.  Under the
selector's level condition, the exact C-pivot is equivalent to this digit
being `1`.  The family-facing theorem separates the two facts cleanly:
selection supplies exact kernel attainment, while the pivot is precisely the
additional divided digit.

This separation is necessary.  The module gives a concrete core example on
`DM 2 0` whose kernel image is exactly `2 Z_2`, with `nu(B) = 1` and
`nu(C) = 4`.  It satisfies the full level-one kernel condition but not the
exact C-pivot.  Hence exact level, `lambdaAt`, and the ordinary mod-two cup
cannot determine the distinguished pivot.  A field producer needs a genuinely
filtered placement statement.

## Residue-trivial compatible tame lifts

`RamifiedCertificateResidueLift` proves that any source commutator detected as
the target tame involution is automatically a residue-trivial anchored lift.
This gives both an instancewise theorem and a uniform
`CompatibleResidueLiftAt` producer from detected commutators.

For the standard tame relation, a source commutator maps to
`tau^q * tau^-1 = tau^(q-1)`, not generally to `tau`.  The module therefore
closes the full open-subgroup producer when `qK = 2`, but deliberately retains
a detection premise at general `q`.  Odd order of the finite target involution
does not imply coprimality with `q-1`, so the general gap is group-theoretic and
cannot be removed by surjectivity alone.

## Canonical anchored involution field

`AnchoredInvolutionFieldNorm` constructs the fixed field of the canonical
index-two subgroup inside the anchored splitting field.  Openness, Krull
recovery, finite dimensionality, inclusion, index two, square-root generation,
and coordinates are all proved automatically.

Consequently `InvolutionFieldPackage` and
`AnchoredInvolutionFieldDataAt` reduce exactly to equality of the two norm
value groups for compatible ramified uses.  The module exposes both a direct
norm-data predicate and the repository's `HasEqualNormValueGroups` spelling.
No separate tower-existence or square-root premise remains.

## Verification

Every new declaration elaborates at the default heartbeat limit and depends
only on `propext`, `Classical.choice`, and `Quot.sound`.  No option override,
new axiom, `sorry`, or native decision procedure is used.

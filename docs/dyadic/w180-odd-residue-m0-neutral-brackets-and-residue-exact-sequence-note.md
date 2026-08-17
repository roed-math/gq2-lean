# W180: odd-residue M0, neutral brackets, and the residue exact sequence

W180 closes the compact-M unramified-character arithmetic in odd residue degree, corrects an
overstrong W179 graded premise, and constructs the topological exact sequence for the absolute
residue action.  Every new arithmetic and structural theorem is fully proved; no new axiom,
placeholder, or resource-limit override is introduced.

## Compact-M0: odd residue degree is the sharp descent premise

`M0FieldNuOddResidue` proves that the mod-two descent identity only needs
`Odd FF.f`.  The older odd-total-degree theorem first derived this fact and then used exactly
the same computation.  Consequently, once `K(sqrt(-3))/K` preserves the value group, `-3`
represents the marked mod-two unramified character in every odd-residue-degree field.

`M0FieldNuOddResidueSpectral` proves the remaining value-group statement rather than retaining
it as a premise.  The residue field has cardinality `2 ^ FF.f`; for odd `FF.f`, its unit group
has no element of order three.  Reduction therefore gives

```text
norm (c^2 + c + 1) = 1
```

for every unit `c`.  This is the exact atom used in the explicit norm calculation for
`K(sqrt(-3))`.  The resulting theorem
`hasEqualNormValueGroups_of_sq_eq_neg_three_of_odd_residueDegree` is standard-three, including
the harmless split case in which the chosen root already belongs to `K`.

The selected endpoint
`m0RowResidualRN_of_familySelection_of_oddResidueDegree` now needs only:

- odd residue degree; and
- the intrinsic distinguished-D placement `M0UniformizerDPlacement`.

It has no unramified-Kummer, Artin-value, pivot, determinant, or analytic premise.  The live M0
field problem is therefore the distinguished-D placement (and the complementary even-residue
cases), not the marked unramified character.

## Compact-Mpc: W179's full fixed-C premise was false

`MpcFixedCRelativeBracketObstruction` formally supersedes W179's proposed
`FixedCRelativeBracketSurjective`.  For every fixed `c` and every rung, a fixed-C bracket
`[c, epsilon]` has zero first-handle abelian digit, whereas `U_0 ^ (2 ^ j)` survives with a
nonzero digit modulo the next two-central-series rung.  In particular,

```text
not_fixedCRelativeBracketSurjective c
```

holds for every `c`; `U_0^2` already witnesses the failure at the base rung.

The correction is `FixedCRelativeNeutralBracketSurjective`, whose target is restricted to
abelian-neutral defects.  That is the honest target produced by balanced relation rows.  The
module proves that this restricted premise still gives the corrected-D rung climb and the exact
absorber `oneHandleDAbsorbable_of_balanced_fixedC_neutral`.

Thus W179's compactness and generation work remains valid.  What is retracted is only the
overlarge graded target.  The remaining one-handle theorem is abelian-neutral fixed-C
reachability, or an equivalent multi-slot square-plus-bracket span.

## Odd L: the absolute residue action exact sequence

`RamifiedCertificateAbsoluteResidueExactSequence` upgrades W179's algebraic-closure theorem to
the actual topological residue action.  It constructs the base-linear action, proves its kernel
is exactly `absoluteInertiaSubgroup`, proves Krull continuity using finite residue lifts to
integral representatives, and proves the image is closed.  Hence it obtains the continuous
multiplicative equivalence

```text
G_Q2 / absoluteInertiaSubgroup ~=top action.range.
```

The remaining surjectivity theorem is characterized exactly by
`absoluteResidueAlgAction_surjective_iff_finite_lifts`: every automorphism of every finite normal
residue subfield must lift, on that subfield, to an element of the absolute Galois group.  This
finite residue/Frobenius lifting statement is both sufficient and necessary.  Existing
reciprocity interfaces do not provide the required residue-action compatibility.

After finite lifting, the remaining odd-L comparison is to normalize the resulting full residue
Galois group by square Frobenius and connect it to the oriented tame quotient.  The anchored
involution lane still separately retains its finite-layer norm/unit reciprocity boundary.

## Exact frontier after W180

1. Prove abelian-neutral fixed-C reachability for the one-handle Mpc balanced defects, or replace
   it by a provably sufficient multi-slot graded span.
2. Prove intrinsic distinguished-D placement for the selected M0 family; odd-residue
   unramified-character arithmetic is now closed.
3. Prove finite normal residue-automorphism lifting for the absolute residue action, then finish
   the normalized Frobenius comparison used by the compatible odd-L ramified packet.
4. Continue the independent anchored finite-layer norm/unit reciprocity front.

# Completed Fox injectivity: Labute/strong-freeness audit

Date: 2026-08-04

## Result

The current repository does not contain a theorem from which
`SqCompletedFoxRefinementDetection h` follows from nonsquareness of `sqRelator h`.
The missing result is not another finite-quotient Fox calculation.  It is the pro-2
one-relator identity theorem (or an associated-graded Magnus--Labute proof of that theorem):
for a one-relator free pro-2 quotient whose relator is not a square, the completed relation
module is free of rank one, equivalently the completed Fox row has zero common left
annihilator.

## Dependency map

```text
explicit order-32 witness
  GQ2.Dyadic.SqCore.sqRelator_maxProTwo_not_square
                         │
                         │  AVAILABLE
                         ▼
relator is not a proper 2-power in the free pro-2 group
                         │
                         │  MISSING CLASSICAL IDENTITY THEOREM
                         ▼
completed relation module is free of rank one
  ⇔ actual completed Fox row has zero common left annihilator
                         │
                         │  algebraic identification/adapter
                         ▼
injectivity of sqCompletedModTwoFoxBoundary
  ⇔ SqCompletedFoxRefinementDetection
                         │
                         │  bar--Fox comparison (separate remaining lane)
                         ▼
ModTwoHThreeExact (DSq h)
```

There is now a second, strictly lower-level route to the missing middle arrow:

```text
separation of powers of the augmentation ideal of F₂[[DSq h]]
                         +
zero common kernel of the initial Fox row on every augmentation layer
                         │
                         │  H3AugmentationFiltration.lean (PROVED)
                         ▼
completed Fox row has zero common left annihilator
```

The two premises in the latter route are genuine Magnus/associated-graded statements.  They do
not mention global injectivity or compatible-family detection, so using them would not rename
the desired conclusion as a hypothesis.

## Why the existing Roe/Labute stack does not close the arrow

`GQ2/Roe/Labute` proves a specialized rank-three classification/isomorphism by successive
approximation in the lower 2-central tower.  Its graded-Lie and Magnus files provide coefficient
functionals and spanning results for the two concrete Roe normal forms.  They do not construct:

1. the relation module of an arbitrary one-relator pro-2 quotient;
2. the completed group-ring Fox row of `sqRelator h` for arbitrary handle count;
3. an augmentation-associated-graded resolution or a no-common-annihilator theorem;
4. an implication from “not a square” to any of those objects.

In particular, the `MagnusA` development is fixed to three letters and is used to control lower
2-central layers in the Roe classification.  Its filtration estimates are one-sided membership
bounds; they are not a Magnus embedding plus leading-term cancellation theorem for the completed
relation module.

## Why finite `StronglyFreeModTwoRelatorSummand` cannot be used

The existing strongly-free object is deliberately finite-discrete.  Demanding it at every
quotient would in particular demand it at the trivial quotient.  For the improved relator:

* its entire mod-two Fox matrix at `Q = Unit` is zero;
* its class in `R/(R²[R,R])` at `Q = Unit` is zero, because this quotient is commutative of
  exponent two and the relator abelianizes to `x⁻⁴y²`;
* therefore the finite Fox matrix has no left retraction and the displayed relator cannot span a
  split strongly-free regular summand.

These are formalized in `H3FiniteStronglyFreeNoGo.lean`.  This does not conflict with completed
injectivity: a compatible coefficient may vanish at a coarse quotient and be detected only after
passing to a finer quotient.

## Minimal honest next theorem

After the actual completed Fox row is exposed as elements
`d_i ∈ F₂[[DSq h]]`, the minimal non-tautological theorem can be stated in either of two forms:

1. **Identity-theorem form:** nonsquareness of the free pro-2 relator implies that the `d_i`
   have zero common left annihilator.
2. **Initial-form form:** powers of the completed augmentation ideal are separated, and the
   initial forms of the `d_i` have zero common left annihilator on every successive layer.

The second form feeds
`completedRowCommonLeftAnnihilatorFree_of_augmentationInitialRegular` directly.  Proving only
finite-level injectivity is neither necessary nor possible.

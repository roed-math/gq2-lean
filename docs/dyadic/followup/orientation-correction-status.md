# Orientation correction after abstract Labute classification

Date: 2026-08-02

## Result

An unoriented equivalence returned by the present `MLabHypothesis` or `NLabHypothesis` cannot
in general be repaired using the automorphisms already constructed for marked correction.
Those automorphisms are deliberately in the stabilizer of the canonical character:

```lean
forall x, chiM alpha h (u x) = chiM alpha h x
forall x, chiN alpha h (u x) = chiN alpha h x.
```

`GQ2/Dyadic/OrientationCorrection.lean` proves the generic equivalence
`orientationMatches_trans_iff`: precomposition by such an automorphism preserves, in both
directions, whether an abstract equivalence is orientation-compatible.  The same automorphisms
remain exactly the right tool for normalizing the independent unramified marking after
orientation is known.

This is a mathematical obstruction, not only a missing Lean API.  The new continuous
characters `inverseChiM` and `inverseChiN` have pointwise inverse values.  The file proves

```lean
range inverseChiM = imChiM alpha
range inverseChiN = imChiN alpha
```

but, for the valid range `2 <= alpha`, each inverse character differs from the canonical
character.  The theorems `inverseChiM_not_correctable` and `inverseChiN_not_correctable` show
that no character-preserving core automorphism can repair even these same-image examples.
Consequently exact image equality cannot replace canonical-orientation naturality.

## New proved interface

The file also closes two previously implicit image calculations:

```lean
range_chiM : range chiM = imChiM alpha
range_chiN : range chiN = imChiN alpha
```

The proof uses topological generation of `DM`/`DN`, compactness of the character image, and the
displayed generator values.  These equalities make the image antecedents of the existing Labute
hypotheses auditable against the actual standard cores.

The positive orientation boundary is packaged by

```lean
OrientedContinuousMulEquiv chiCore chiG
orientedEquivM_of_datum
orientedEquivN_of_datum
orientedEquivSq_of_values
```

For `M` and `N`, the pulled character must satisfy the already-proved four-generator Labute
datum and be trivial on all appended handles.  `isLabuteOrientationDatumM_unique` and
`isLabuteOrientationDatumN_unique`, followed by `chiM_matching`/`chiN_matching`, then prove
the full pointwise orientation equation.  These are actual recognition theorems, not new
classification hypotheses.

## What theorem is still needed

For an arbitrary equivalence

```lean
f : ContinuousMulEquiv (DM alpha h) (maxProPQuotient 2 (GalK K))
```

obtained from `MLabHypothesis`, it is enough to prove that the pullback
`chiCycKTwo.comp f` satisfies `IsLabuteOrientationDatumM` on the four core letters and is `1`
on every handle.  The `N` signature is identical with `IsLabuteOrientationDatumN`.  A more
intrinsic and reusable theorem would be naturality of a canonical-orientation predicate:

```lean
theorem canonicalOrientation_comp_equiv
    (e : ContinuousMulEquiv G H)
    (hcanonical : IsCanonicalOrientation H chiH) :
  IsCanonicalOrientation G (chiH.comp e)

theorem canonicalOrientation_unique_M
    (hcanonical : IsCanonicalOrientation (DM alpha h) chi) :
  chi = chiM alpha h

theorem canonicalOrientation_unique_N
    (hcanonical : IsCanonicalOrientation (DN alpha h) chi) :
  chi = chiN alpha h
```

No abstract `IsCanonicalOrientation` is presently defined.  Formalizing it through the
dualizing module, or proving the concrete pullback Labute-data statements directly, is the
remaining orientation step.  The existing `mIsCanonical` parameter cannot supply this on its
own: `MLabHypothesis` accepts the predicate in its antecedent but returns an equivalence without
any theorem relating the predicate across that equivalence.

## Odd `L` audit

The odd square-commutator family is separate.

* At arbitrary `h`, `chiSq_matching` recognizes the canonical character from the three Hensel
  values on `sigma`, `x0`, `x1` and value `1` on all handles.  The new
  `orientedEquivSq_of_values` packages exactly this theorem.
* At `h = 0`, `DSq 0` is identified with `DR`, and the proved rank-three path transports the
  descent predicate and invokes `bLab`.
* There is no general odd-rank theorem transporting the rank-three `IsLabuteOrientation`
  predicate to `DSq h`, nor an odd-rank abstract classification theorem.  Nothing in this
  audit extrapolates `BLabHypothesis` beyond rank three.

Thus the next orientation work is not another shear or scaling construction.  It is either the
abstract naturality/uniqueness theorem for the dualizing orientation, or the three concrete
pullback-value calculations required by `orientedEquivM_of_datum`,
`orientedEquivN_of_datum`, and `orientedEquivSq_of_values`.

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
CharacterizesCharacter P chiCore
PullbackNatural PC PG
orientedEquiv_of_natural_unique
orientedEquivM_of_datum
orientedEquivN_of_datum
orientedEquivSq_of_values
```

For `M` and `N`, the pulled character must satisfy the already-proved four-generator Labute
datum and be trivial on all appended handles.  `isLabuteOrientationDatumM_unique` and
`isLabuteOrientationDatumN_unique`, followed by `chiM_matching`/`chiN_matching`, then prove
the full pointwise orientation equation.  These are actual recognition theorems, not new
classification hypotheses.

The complete recognition predicates are now named:

```lean
IsPresentedOrientationM alpha h chi
IsPresentedOrientationN alpha h chi
```

They use the improved four-letter presentations actually formalized in `MarkedCore/Cores.lean`:

* `M`: `A^2 [A,B] C^(2^alpha) [C,D]`, with values
  `(1, -1, 1, (1 - 2^alpha)^(-1))`;
* `N`: `A^(2 + 2^alpha) [A,B] [C,D]`, with values
  `(1, -(1 + 2^alpha)^(-1), 1, 1)`;
* every appended symplectic handle has character value `1`.

Theorems `isPresentedOrientationM_iff` and `isPresentedOrientationN_iff` prove, for
`1 <= alpha`, that these predicates are respectively equivalent to equality with `chiM` and
`chiN`.  Thus the uniqueness half of canonical-orientation transport is now fully proved for
the presentations selected by the new plan.  This is not a regression to the draft's retired
relative-norm word: `Main.lean`'s constructor-table regressions identify every frozen row with
the improved `N0`, `M0`, or `Mpc` word, including both procyclic `M` rows.

The generic theorem `orientedEquiv_of_natural_unique` proves the categorical step: if a
target-side character predicate pulls back along continuous equivalences to a predicate that
uniquely characterizes the standard core character, then the supplied abstract equivalence is
an `OrientedContinuousMulEquiv`.  Its two specializations are
`orientedEquivM_of_pullback_natural` and `orientedEquivN_of_pullback_natural`.

Finally, `orientedAbstractEquiv_KTwoM` and `orientedAbstractEquiv_KTwoN` feed actual abstract
equivalences returned by `MLabHypothesis` and `NLabHypothesis` into that transport theorem.
They do not alter either hypothesis: all new input is the separately named pullback-naturality
premise described below.

## What theorem is still needed

The exact remaining input is no longer an informal prose obligation.  For the `M` output it is
the following premise of `orientedAbstractEquiv_KTwoM`:

```lean
PullbackNatural (IsPresentedOrientationM alpha h)
  (fun chi => mIsCanonical (maxProPQuotient 2 (GalK K)) chi.toMonoidHom)
```

For `N`, whose current classification hypothesis records only the character image, the minimal
signature additionally names a target predicate and requires:

```lean
nIsCanonical (chiCycKTwo (K := K))
PullbackNatural (IsPresentedOrientationN alpha h) nIsCanonical
```

Either an intrinsic dualizing-orientation construction can prove these premises uniformly, or
the concrete four-letter and handle values can prove them for the cyclotomic character at the
particular `K`.  Once either statement is available, the new wrapper returns the oriented
equivalence with no further group-theoretic correction.

The existing `mIsCanonical` parameter still cannot supply naturality on its own:
`MLabHypothesis` accepts it in its antecedent but returns an equivalence without any theorem
relating the predicate across that equivalence.  The new wrapper exposes precisely that missing
law rather than silently strengthening `MLabHypothesis`.

## Duality and cup--Bockstein audit

There is currently no abstract dualizing orientation to instantiate the new transport theorem.

* `TateDualityG G n` contains an unnormalized isomorphism
  `H2 G (MuN n) ≃+ ZMod n` and perfect finite-`n` cup pairings.  It does not define an integral
  dualizing module, its `G`-action character, or transport of such a character along a
  `ContinuousMulEquiv`.
* `IsLocalDualizingGroup` records an open finite-index embedding into `AbsGalQ2`, compatible
  with the finite `MuN n` action.  It likewise produces no `Z_2^×`-valued character.
* `DyadicOrientation` is the deliberately composite B3c interface at `AbsGalQ2`; its own
  documentation says the abstract dualizing-module characterization is deferred.
* The field-side cup form, Bockstein diagonal, and Tate perfectness are all presently used at
  mod `2`.  The new theorem `character_toZModPow_one` proves that every value of every
  `Z_2^×`-valued character reduces to `1` mod `2`, and `inverseCharacter_modTwo_eq` proves the
  entire mod-2 scalar functions of `chi` and `chi⁻¹` are equal.  Thus the current
  cup--Bockstein data cannot distinguish the same-image inverse-character counterexamples.
  An integral dualizing-module action could still distinguish them; it simply is not yet an
  object in the repository.
* Rank three has a genuine theorem, `isLabuteOrientation_comp_iso`, but its proof is specific to
  `DR ≃ D0`: it constructs `D0`-side WordLift master derivations, proves their evaluation matrix
  invertible mod `2`, and solves for arbitrary derivation values.  No current API transports
  that argument from an arbitrary `G_K(2)` to the improved even-rank cores.

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

# W361 independent marked-endpoint audit

## Verdict and scope

No logical loophole, change of source word, or circular marking construction
was found in `SelectedWord`, `SelectedWordFinal`, `MarkedFinal`,
`MarkedCanonical`, and `GeneralMain`. The supported conclusion is **existence
of a certified selected source with an existentially calibrated realization**,
not preservation of an arbitrary previously prescribed core realization.

The bare public inputs are a finite intermediate field `K/Q₂` and
`RI : RamifiedIData K`. There are no hidden topology, selected-pivot, Stokes,
determinant, or reconstruction-premise arguments. Literally, RI supplies a
square root of `-1` and negates `HasEqualNormValueGroups K deltaI`; it is the
standing ramified-i scope, not a theorem for all finite K without qualification.
Odd degree supplies RI through the existing uniform norm obstruction.

## Quantifiers and simultaneous markings

The strongest fixed-source lemma is `nonempty_alignedMarkedFieldEquiv`:
for an already supplied branch G, its actual word certificate W, compatible
field inputs, finite parameters, and RI, it produces **one** equivalence e.
That same e satisfies tame and full two-adic unramified compatibility, the
maximal-pro-two square using the induced realization, and the cyclotomic
equation using **G's original realization**. The statement is not a conjunction
of unrelated existential equivalences.

The bare endpoint then has order `exists G, exists cert, exists e, all equations`.
Its G is the calibrated branch. This is valid existential packaging, not a
proof of `forall prescribed realization, exists e preserving it pointwise`.
The stronger full-fixed-realization reconstruction problem remains distinct.

The selected endpoint carries exact source-constructor provenance:

- L/N: the selected canonical word and core, including the selected display.
- M0: the selected canonical word/core or the actual pair-splice constructor
  with its selected handle and exact transported nu, plus the unit-head row.
- Mpc: the actual mobile splice at `p epsilon r`, exact transported nu, and
  actual unit etaD; the equality with the D-coordinate and etaD's congruence
  to the selected eta modulo `2^r` are recorded explicitly.

No old frozen-M word equality is asserted. The `HEq` fields do not weaken
syntax equality: explicit degree/core equalities accompany them. Canonical
profile fields do not prescribe an additional fixed formula for nu; full
nu-compatibility remains in the branch realization and certificate.

## What calibration changes

`alignedBranch` is exactly `{ G with realization := alignedRealization ... }`.
A default-limit scratch probe checked by `rfl` that degree, word, core, nuP,
and the **whole same certificate W** are unchanged. Hence the `GammaR` carrier,
its relations, and the certificate's actual pro-two map are unchanged too.
The selected profile survives by `Iff.rfl`; there is no index transport that
drops its word or nu equality.

The induced field-to-core map is `W.pro2 ∘ e.symm`. Surjectivity and the exact
maximal-pro-two kernel are transported from W, so this yields a genuine
continuous equivalence with the field's maximal-pro-two quotient. Its nu law
uses the already proved full unramified equation and W's surjectivity.
The argument does not reconstruct e a second time after changing realization.

The dependency order is:

`original realization → arithmetic source → tame-compatible e and nu law →
induced realization → old/new cyclotomic equality`.

The last step uses characteristicness of the **actual field** character
`chiCycKTwo`, not a character newly defined by pulling back along e.
Characteristicness is proved independently from an existing oriented
pro-two field classification and uniform core-orientation rigidity. Its
axiom footprint is smaller than the final endpoint's; it does not consume
the final marked-equivalence conclusion.

## Important record-packaging distinction

`AlignedMarkedFieldEquiv G W T`, and therefore
`HasSelectedFullyMarkedFlexibleAssemblyRN`, retain the original G explicitly;
their cyclotomic field is literally against `G.realization` before calibration.

`SelectedWordMarkedFieldData` instead stores the calibrated branch. Its
cyclotomic field is literally against that new realization. The producer
genuinely proves it through the original-character equation and then the
characteristic old/new equality, but the original G is not itself a field of
this final selected record. Documentation should not conflate those two APIs.

A scratch theorem combined exact `SelectedWordProfile` with an existential
original G, its certificate, and `AlignedMarkedFieldEquiv G cert.cand T` using
the existing producers with no new premise or axiom. At the parent's request,
this has now been promoted in the additive module
`Instances/FieldFamilySpliceOriginalMarked.lean`. Its
`HasSelectedOriginalMarkedWordPresentationRN` and supplied/canonical/bare
producers make original-character provenance visible without changing the
marking proof or claiming preservation of an arbitrary fixed realization.
The selected handle remains a source-producer witness, not an arbitrarily
preassigned handle. This addition changes no existing proof module or API.

## Independent checks and baseline

`/private/tmp/W361MarkedEndpointIndependentAudit.lean` compiled at default
settings. It checked the definitional preservation above, extracted the new
maximal-pro-two and original cyclotomic equations from the same record, proved
the combined selected/original witness, and printed the public theorem types.

The canonical bare selected and bare existential endpoints each print exactly
std3 plus nine inherited axioms: Hilbert norm criterion, local reciprocity,
marked reciprocity, oriented tame quotient, peripheral cyclotomic action,
relative Stiefel–Whitney, Tate duality, absolute-Q₂ finite generation, and
absolute-Q₂ local Euler characteristic. The supplied-bundle endpoint and the
combined scratch witness use std3 plus six (omitting the three canonical
reciprocity/tame bundle constructors). No new axiom or placeholder is hidden
by the packaging. These remain foundationally conditional theorems, not a
claim to have discharged the inherited arithmetic axiom baseline.

`GeneralMain` is an additive export surface and leaves the historical frozen
quadratic entrypoint untouched. The word-display migration and ten-item
acceptance appendix are separate deliverables, not consequences of this audit.

The four inspected endpoint source modules and `GeneralMain.lean` also passed
fresh default-limit checks. The new original-witness packaging has six public
axiom pins: its predicate is std3, the three supplied-bundle producers are
std3 plus six, and its bare ramified-i/odd-degree producers are std3 plus nine,
exactly matching the existing endpoints. No additional marking hypothesis or
axiom was introduced by retaining the witness.

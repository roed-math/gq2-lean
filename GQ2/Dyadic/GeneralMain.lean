/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.FieldFamilySpliceMarkedCanonical
import GQ2.Dyadic.Instances.FieldFamilySpliceSelectedWordFinal
import GQ2.Dyadic.Instances.FieldFamilySpliceOriginalMarked

/-!
# General marked presentations of ramified-i dyadic fields

This is the public entry point for the general finite `K / ℚ₂` theorem. The historical
`GQ2.Dyadic.Main` continues to expose the frozen quadratic table; it is not replaced.

`exists_certifiedFullyMarkedFlexiblePresentation_ramifiedI K RI` takes a finite intermediate
field and `RI : RamifiedIData K`. It returns an actual profinite source word at the exact
field degree, its corrected word certificate, a marked pro-two core realization, and ONE
continuous group isomorphism to `GalK K` satisfying the tame, maximal-pro-two, cyclotomic,
and full unramified compatibility equations.

The source families are the completed flexible families. In the M cases the construction
may use the new tame-shadow splice; this theorem does NOT assert that the old frozen M word
presents the field group. The realization is existentially calibrated, retaining the exact
word, core, full nu and certificate. It does NOT assert that every previously prescribed
core realization is pointwise preserved. `AlignedMarkedFieldEquiv` retains the ORIGINAL
core character explicitly before calibration; the selected record below carries the new
calibrated realization. Its proof preserves the original character, but the original source
is not a separate field of that record.

`nonempty_selectedWordMarkedFieldData_ramifiedI K RI` further retains exact word/core
constructor provenance and the selected parameters, not merely a family tag. The Mpc unit
is the actual normalized D-coordinate, with its congruence to the selected unit recorded.
This is the preferred endpoint when linking an explicit word display to the presentation.

`hasSelectedOriginalMarkedWordPresentationRN_ramifiedI K RI` packages the strongest
provenance statement: it retains the PRE-calibration source G, its exact selected-word
profile and certificate, and `AlignedMarkedFieldEquiv G ...` in one existential. Its
cyclotomic equation is literally against G's original realization, while its pro-two
equations use the induced realization. Prefer this endpoint when both original-character
and exact-word provenance must be visible in the statement itself.

The canonical endpoint inherits std3 plus nine established arithmetic/foundation axioms:
`hilbertSymbol_normCriterion_finiteDyadic`, `localReciprocity`, `markedRecipAt`,
`orientedTameQuotientAt`, `peripheralCyclotomicAction`, `relativeStiefelWhitney_dyadic`,
`tateDualityAt`, `Foundations.absGalQ2_isTopologicallyFinitelyGenerated`, and
`Foundations.absGalQ2_localEulerCharacteristic`. No new axiom or residual proof obligation
is introduced. The supplied-bundle endpoint uses std3 plus six of these inputs.

The unramified-i case remains outside the campaign's stated scope. The odd-degree corollary
uses the proved ramified-i norm obstruction and is not a separate class-by-class argument.
-/

namespace GQ2.Dyadic

export Instances.FieldFamilySpliceMarkedCanonical
  (exists_certifiedFullyMarkedFlexiblePresentation_ramifiedI
   hasSelectedFullyMarkedFlexibleAssemblyRN_canonicalParameters
   hasSelectedFullyMarkedFlexibleAssemblyRN_ramifiedI
   hasSelectedFullyMarkedFlexibleAssemblyRN_oddDegree)

export Instances.FieldFamilySpliceSelectedWordFinal
  (SelectedWordMarkedFieldData
   nonempty_selectedWordMarkedFieldData_ramifiedI
   nonempty_selectedWordMarkedFieldData_oddDegree)

export Instances.FieldFamilySpliceOriginalMarked
  (HasSelectedOriginalMarkedWordPresentationRN
   hasSelectedOriginalMarkedWordPresentationRN_of_matchesRange
   hasSelectedOriginalMarkedWordPresentationRN_fieldSelectionFromRange
   hasSelectedOriginalMarkedWordPresentationRN_canonicalParameters
   hasSelectedOriginalMarkedWordPresentationRN_ramifiedI
   hasSelectedOriginalMarkedWordPresentationRN_oddDegree)

#print axioms exists_certifiedFullyMarkedFlexiblePresentation_ramifiedI
#print axioms hasSelectedFullyMarkedFlexibleAssemblyRN_canonicalParameters
#print axioms hasSelectedFullyMarkedFlexibleAssemblyRN_oddDegree
#print axioms nonempty_selectedWordMarkedFieldData_ramifiedI
#print axioms hasSelectedOriginalMarkedWordPresentationRN_ramifiedI

end GQ2.Dyadic

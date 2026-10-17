/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5.5
-/
module

public import GQ2.TauCeti.B1
public import GQ2.TauCeti.B3c
public import GQ2.TauCeti.B5
public import GQ2.TauCeti.B6
public import GQ2.TauCeti.B7
public import GQ2.TauCeti.B8
public import GQ2.TauCeti.B9
public import GQ2.TauCeti.B10
public import GQ2.TauCeti.B11a
public import GQ2.Foundations.LiteratureInputs

@[expose] public section

/-!
# The literature bundle, proved from Tau Ceti

`tauCetiInputs : GQ2.LiteratureInputs` assembles the nine Tau Ceti adapters
(`GQ2/TauCeti/B*.lean`) into the typeclass the generic capstones consume. Every field is a
theorem or construction proved from Tau Ceti `706344c35` (`GQ2/TauCetiAxiomAudit.lean` checks
that the import closure carries none of the nine legacy names and that the capstones built on it
use only the standard three axioms).

It is a `def`; the instance is `GQ2.tauCetiLiteratureInputs := tauCetiInputs` in
`GQ2/Foundations/TauCetiInstance.lean` (ticket C2, which replaced the axiom-backed instance and
deleted `GQ2/Foundations/Axioms.lean`). The capstones of `GQ2/TauCeti/Main.lean` pass it
explicitly.
-/

namespace GQ2.TauCetiBridge

/-- **The nine literature inputs, proved from Tau Ceti.** Each field is the corresponding adapter:
B1 `absGalQ2_isTopologicallyFinitelyGenerated_tauceti`, B7 `absGalQ2_localEulerCharacteristic_tauceti`,
B3c `dyadicOrientation_tauceti`, B5 `localReciprocity_tauceti`, B6 `tateDualityAt_tauceti`,
B8 `peripheralCyclotomicAction_tauceti`, B9 `relativeStiefelWhitney_dyadic_tauceti`,
B10 `tameQuotient_tauceti` (oriented against B5's reciprocity datum) and
B11a `hilbertSymbol_normCriterion_finiteDyadic_tauceti`. -/
@[instance_reducible] noncomputable def tauCetiInputs : LiteratureInputs where
  absGalQ2_isTopologicallyFinitelyGenerated := absGalQ2_isTopologicallyFinitelyGenerated_tauceti
  absGalQ2_localEulerCharacteristic := @absGalQ2_localEulerCharacteristic_tauceti
  dyadicOrientation := @dyadicOrientation_tauceti
  localReciprocity := localReciprocity_tauceti
  tateDualityAt := @tateDualityAt_tauceti
  peripheralCyclotomicAction := peripheralCyclotomicAction_tauceti
  relativeStiefelWhitney_dyadic := @relativeStiefelWhitney_dyadic_tauceti
  tameQuotient := tameQuotient_tauceti
  hilbertSymbol_normCriterion_finiteDyadic := @hilbertSymbol_normCriterion_finiteDyadic_tauceti

end GQ2.TauCetiBridge

/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.TameTwoQuotient
import GQ2.BoundaryMapsWitness

/-!
# The orientation-clause witness discharge

`TameUnitOrientation LiteratureInputs.localReciprocity` (`GQ2/TameTwoQuotient.lean`) holds for the tame
coordinate of the axiom witness `boundaryMapsWitness` (`GQ2/BoundaryMapsWitness.lean`).

The witness's `tameF` is `SectionThree.tameFHom = locTame.equiv ∘ quotientMk locTame.W`, and
`locTame` repackages the **B10′ bundle** `LiteratureInputs.tameQuotient` itself — so the orientation clause is
verbatim the bundle's `nuT_recip_unit` (the `tame_recip_unitNeg3` pattern of
`BoundaryMapsWitness.lean`, at an arbitrary unit).  This is the discharge promised where the moved
`lemma_6_17_vanish` threads `TameUnitOrientation LiteratureInputs.localReciprocity B.tameF` as a hypothesis
(the `hc`/`hV2` amendment precedent): at `B := boundaryMapsWitness` it is this theorem.

Kept as a leaf file separate from `TameTwoQuotient.lean` so that c2c4's `UnramifiedBridge` can
import the `TameUnitOrientation` definition without pulling in the marked pro-2 isomorphisms witness machinery, and
because `TameTwoQuotient.lean` (namespace `GQ2`) and `BoundaryMapsWitness.lean` (namespace
`GQ2.SectionThree`) declare same-named bricks (`maxProPMk_tameTau`, `ker_nuT_le_proPKernel`) —
importing one into the other would put both in scope of the other's `open`.

Literature-input dependencies: B10′ (`LiteratureInputs.tameQuotient`) + B5
(`LiteratureInputs.localReciprocity`, via the statement); the
`boundaryMapsWitness`-shaped corollary additionally carries the witness's own bundle axioms.
No new axiom, no `sorryAx`.
-/

namespace GQ2

variable [lit : LiteratureInputs]
omit lit

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

include lit in
/-- **The orientation clause at the witness's tame coordinate** (the Lemma 6.17 vanishing proof(iii), the witness
discharge): `SectionThree.tameFHom` satisfies `TameUnitOrientation LiteratureInputs.localReciprocity`.  Since
`tameFHom = LiteratureInputs.tameQuotient.equiv ∘ mk` by construction (`locTame` repackages the B10′ bundle), the
clause is verbatim `LiteratureInputs.tameQuotient.nuT_recip_unit`. -/
theorem tameUnitOrientation_tameFHom :
    TameUnitOrientation LiteratureInputs.localReciprocity SectionThree.tameFHom :=
  LiteratureInputs.tameQuotient.nuT_recip_unit

include lit in
/-- **The witness discharge in the consumer's verbatim shape** (`B := boundaryMapsWitness`):
`boundaryMapsWitness.tameF` satisfies `TameUnitOrientation LiteratureInputs.localReciprocity`.  This is the
instantiation the literal-presentation proof/the architecture review assembly uses to discharge the orientation hypothesis of the moved
`lemma_6_17_vanish` at the axiom witness (`boundaryMapsWitness.tameF ≡ tameFHom` by the
structure-literal projection). -/
theorem tameUnitOrientation_witness :
    TameUnitOrientation LiteratureInputs.localReciprocity (SectionThree.boundaryMapsWitness).tameF :=
  tameUnitOrientation_tameFHom

end GQ2

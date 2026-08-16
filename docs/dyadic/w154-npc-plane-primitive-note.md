# W154: primitive Npc plane from exact level

Exact positive level now produces a chi-preserving frame whose divided sigma/x2 row is primitive.

The proof first identifies the cyclotomic character with the `x1` abelian coordinate.  For an
element in `ker chi` whose marking has exact value `2^r`, the abelian coordinate expansion and
level divisibility force a unit quotient among sigma, `x2`, or the handle coordinates.

The original sigma/x2 plane need not be primitive when handles are present: a character supported
on one handle is a genuine counterexample.  `exists_dnPlanePrimitive_of_level_exact` therefore
changes the frame.  If the unit occurs on a handle, an exact chi-preserving Eichler move transfers
it into `x2`; parity shows the new x2 quotient is a unit.  Sigma and `x1` are preserved.

The result is an automorphism `Psi` preserving `chiN` together with
`NpcPlanePrimitiveAtLevel` for the corrected marking.  The theorem and its primitive-coordinate
lemma depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The remaining work is the routine field wrapper: apply this theorem to the transported field
marking using the exact level element, precompose the oriented equivalence by `Psi`, and feed the
result to W152/W153.
